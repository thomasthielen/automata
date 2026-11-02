//! Runs the command-line tools of [Spot](https://spot.lre.epita.fr/) on automata of this crate,
//! for example to cross-check results or to compute minimal deterministic automata.
//!
//! Spot is not linked, but called as an external program: automata are passed in the HOA format
//! (see [`WriteHoa`]) through stdin, and results are read back from stdout. Spot has to be
//! installed separately; on Windows, it runs inside WSL (see [`Spot::wsl`]). Only available on
//! crate feature `spot`.
//!
//! The tests of this module need Spot and are therefore ignored by default. Run them with
//! `cargo test --features spot spot:: -- --ignored`.
use std::io::Write;
use std::process::{Command, Stdio};

use thiserror::Error;
use tracing::trace;

use crate::TransitionSystem;
use crate::alphabet::CharAlphabet;
use crate::automaton::DCW;
use crate::hoa::{HoaError, WriteHoa, dcw_from_hoa};

/// Errors that can occur when running Spot.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum SpotError {
    /// The program could not be started, for example because it is not installed.
    #[error("could not run {program}: {message}")]
    Launch {
        /// The program that was to be started (the first word of the launcher, if any).
        program: String,
        /// The kind of the underlying I/O error.
        kind: std::io::ErrorKind,
        /// The message of the underlying I/O error.
        message: String,
    },
    /// Spot exited with an error.
    #[error("Spot failed (exit status {status:?}): {stderr}")]
    Failed {
        /// The exit status, or `None` if the process was terminated by a signal.
        status: Option<i32>,
        /// What Spot wrote to stderr.
        stderr: String,
    },
    /// Spot's output could not be interpreted.
    #[error("unexpected output from Spot: {0}")]
    UnexpectedOutput(String),
    /// Spot's output could not be read as an automaton.
    #[error(transparent)]
    Hoa(#[from] HoaError),
}

/// What a finished Spot process returned.
struct Output {
    status: Option<i32>,
    stdout: String,
    stderr: String,
}

impl Output {
    /// The exit status of `autfilt` is 0 if it printed an automaton, 1 if it printed none
    /// (because every input was filtered out), and 2 on errors.
    fn autfilt_result(self) -> Result<Option<String>, SpotError> {
        match self.status {
            Some(0) => Ok(Some(self.stdout)),
            Some(1) => Ok(None),
            status => Err(SpotError::Failed {
                status,
                stderr: self.stderr.trim().to_string(),
            }),
        }
    }
}

/// Splits the automata on stdin into the files `$d/0.hoa`, `$d/1.hoa`, ... of a temporary
/// directory `$d`, which is removed on exit. Used by scripts that need several automata, since
/// Spot reads all but one of them from files.
const SPLIT_STDIN: &str = r#"d=$(mktemp -d) || exit 2
trap 'rm -rf "$d"' EXIT
awk -v d="$d" '{ print > (d "/" (n + 0) ".hoa") } /--END--/ { n++ }'
"#;

/// Determinizes the automaton `0.hoa` into a parity automaton, and then minimizes it with the
/// acceptance condition `$1`, since `--sat-minimize` only accepts deterministic input.
const SAT_MINIMIZE: &str = r#"autfilt -D -p "$d/0.hoa" > "$d/deterministic.hoa" || exit 2
autfilt --sat-minimize="$1" "$d/deterministic.hoa"
"#;

/// Prints `1` if the automata `0.hoa` and `1.hoa` are equivalent, and `0` otherwise.
const EQUIVALENT: &str = r#"autfilt -c --equivalent-to="$d/1.hoa" "$d/0.hoa"
"#;

/// Runs the command-line tools of [Spot](https://spot.lre.epita.fr/), see the
/// [module documentation](self).
///
/// A `Spot` consists of a *launcher*: the words that are put in front of each command, such as
/// `wsl -e` to run it in WSL. Besides `autfilt` itself, some methods run small POSIX `sh`
/// scripts (with `mktemp` and `awk`) through the launcher.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spot {
    launcher: Vec<String>,
}

impl Default for Spot {
    /// See [`Spot::from_env`].
    fn default() -> Self {
        Self::from_env()
    }
}

impl Spot {
    /// The environment variable read by [`Spot::from_env`].
    pub const ENV: &str = "AUTOMATA_SPOT";

    /// Runs Spot directly, expecting `autfilt` on the `PATH`.
    pub fn native() -> Self {
        Self::with_launcher(Vec::<String>::new())
    }

    /// Runs Spot inside the default distribution of WSL, through `wsl -e`. The `-e` makes WSL
    /// execute the command without a shell, so that arguments are passed on unchanged.
    pub fn wsl() -> Self {
        Self::with_launcher(["wsl", "-e"])
    }

    /// Runs Spot with the given launcher, for example `["wsl", "-d", "Ubuntu", "-e"]`.
    pub fn with_launcher<I>(launcher: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<String>,
    {
        Self {
            launcher: launcher.into_iter().map(Into::into).collect(),
        }
    }

    /// Reads the launcher from the environment variable [`Spot::ENV`] (`AUTOMATA_SPOT`), split
    /// at whitespace, where an empty value means [`Spot::native`]. If it is not set, this is
    /// [`Spot::wsl`] on Windows and [`Spot::native`] elsewhere.
    pub fn from_env() -> Self {
        match std::env::var(Self::ENV) {
            Ok(launcher) => Self::with_launcher(launcher.split_whitespace()),
            Err(_) if cfg!(windows) => Self::wsl(),
            Err(_) => Self::native(),
        }
    }

    /// Returns the version line of `autfilt`, such as `autfilt (spot) 2.16.1`.
    ///
    /// # Errors
    /// Returns a [`SpotError`] if Spot cannot be run.
    pub fn version(&self) -> Result<String, SpotError> {
        let version = self
            .autfilt(&["--version"], "")?
            .ok_or_else(|| SpotError::UnexpectedOutput("no version".to_string()))?;
        Ok(version.lines().next().unwrap_or_default().to_string())
    }

    /// Returns whether Spot can be run, see [`Spot::version`].
    pub fn is_available(&self) -> bool {
        self.version().is_ok()
    }

    /// Runs `autfilt` with the given arguments and `input` on stdin. Returns its stdout, or
    /// `None` if it printed no automaton, because every input automaton was filtered out.
    ///
    /// # Errors
    /// Returns a [`SpotError`] if `autfilt` cannot be run or fails.
    pub fn autfilt(&self, args: &[&str], input: &str) -> Result<Option<String>, SpotError> {
        self.run("autfilt", args, input)?.autfilt_result()
    }

    /// Computes a minimal transition-based deterministic co-Büchi automaton (tDCW) that is
    /// equivalent to `aut`, or returns `None` if no tDCW recognizes the language of `aut`.
    ///
    /// This determinizes `aut` with `autfilt -D -p` and minimizes the result with
    /// `autfilt --sat-minimize='acc="Fin(0)"'`, which searches for the least number of states
    /// with a SAT solver; this can take long for large automata.
    ///
    /// The result may be incomplete, where a missing transition rejects. Since it has no state
    /// with an empty language, it is incomplete if and only if the language has a residual that
    /// is empty, and then a minimal *complete* tDCW needs one more state, a rejecting sink.
    ///
    /// # Errors
    /// Returns a [`SpotError`] if Spot cannot be run, fails, or its result cannot be read.
    ///
    /// # Example
    /// ```no_run
    /// use automata::automaton::DCW;
    /// use automata::TransitionSystem;
    /// use automata::spot::Spot;
    ///
    /// // "finitely many b", with a redundant state
    /// let dcw = DCW::builder()
    ///     .with_edges([(0, 'a', false, 0), (0, 'b', true, 1), (1, 'a', false, 1), (1, 'b', true, 0)])
    ///     .into_dcw(0);
    /// let minimal = Spot::default().min_dcw(&dcw).unwrap().unwrap();
    /// assert_eq!(minimal.size(), 1);
    /// ```
    pub fn min_dcw<T>(&self, aut: &T) -> Result<Option<DCW>, SpotError>
    where
        T: WriteHoa + TransitionSystem<Alphabet = CharAlphabet>,
    {
        let script = [SPLIT_STDIN, SAT_MINIMIZE].concat();
        let output = self.sh(&script, &[r#"acc="Fin(0)""#], &aut.to_hoa())?;
        match output.autfilt_result()? {
            Some(hoa) => Ok(Some(dcw_from_hoa(&hoa)?)),
            None => Ok(None),
        }
    }

    /// Returns whether `a` and `b` recognize the same language, according to
    /// `autfilt --equivalent-to`. Both should be over the same alphabet, since Spot identifies
    /// atomic propositions by their names.
    ///
    /// # Errors
    /// Returns a [`SpotError`] if Spot cannot be run or fails.
    pub fn equivalent<S, T>(&self, a: &S, b: &T) -> Result<bool, SpotError>
    where
        S: WriteHoa,
        T: WriteHoa,
    {
        let input = [a.to_hoa(), b.to_hoa()].concat();
        let output = self.sh(&[SPLIT_STDIN, EQUIVALENT].concat(), &[], &input)?;
        // with `-c`, autfilt prints the number of automata that passed the filter, also when it
        // exits with 1 because none did
        match (output.status, output.stdout.trim()) {
            (Some(0), "1") => Ok(true),
            (Some(1), "0") => Ok(false),
            (Some(0 | 1), other) => Err(SpotError::UnexpectedOutput(other.to_string())),
            (status, _) => Err(SpotError::Failed {
                status,
                stderr: output.stderr.trim().to_string(),
            }),
        }
    }

    /// Runs the POSIX `sh` script `script` with the positional parameters `args`.
    fn sh(&self, script: &str, args: &[&str], input: &str) -> Result<Output, SpotError> {
        let mut sh_args = vec!["-c", script, "sh"];
        sh_args.extend_from_slice(args);
        self.run("sh", &sh_args, input)
    }

    /// Runs `program` with `args` through the launcher, writing `input` to its stdin.
    fn run(&self, program: &str, args: &[&str], input: &str) -> Result<Output, SpotError> {
        let (executable, launcher_args) = match self.launcher.split_first() {
            Some((executable, rest)) => (executable.as_str(), rest),
            None => (program, &[][..]),
        };
        let mut command = Command::new(executable);
        command.args(launcher_args);
        if !self.launcher.is_empty() {
            command.arg(program);
        }
        command
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        trace!("running {command:?}");

        let launch_error = |error: std::io::Error| SpotError::Launch {
            program: executable.to_string(),
            kind: error.kind(),
            message: error.to_string(),
        };
        let mut child = command.spawn().map_err(launch_error)?;
        // write stdin from a separate thread, so that a full stdout pipe cannot block it
        let writer = child.stdin.take().map(|mut stdin| {
            let input = input.to_string();
            std::thread::spawn(move || stdin.write_all(input.as_bytes()))
        });
        let output = child.wait_with_output().map_err(launch_error)?;
        if let Some(writer) = writer {
            // a failed write means that the program exited early, which its status reports
            let _ = writer.join();
        }

        Ok(Output {
            status: output.status.code(),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Spot, SpotError};
    use crate::TransitionSystem;
    use crate::automaton::{DCW, NCW};
    use crate::ts::TSBuilder;

    /// \[AK22\], Figure 2: a nice tDCW with three states, all of them equivalent.
    fn ak22_figure_2() -> DCW {
        DCW::builder()
            .with_edges([
                (0, 'a', false, 0),
                (0, 'b', false, 1),
                (0, 'c', true, 2),
                (1, 'a', true, 2),
                (1, 'b', true, 2),
                (1, 'c', false, 0),
                (2, 'a', false, 2),
                (2, 'b', true, 1),
                (2, 'c', true, 0),
            ])
            .into_dcw(0)
    }

    #[test]
    fn missing_program_is_a_launch_error() {
        let spot = Spot::with_launcher(["automata-no-such-program"]);
        assert!(matches!(
            spot.version(),
            Err(SpotError::Launch {
                kind: std::io::ErrorKind::NotFound,
                ..
            })
        ));
        assert!(!spot.is_available());
    }

    #[test]
    #[ignore = "requires Spot"]
    fn version() {
        let version = Spot::default().version().unwrap();
        assert!(version.contains("spot"), "{version}");
    }

    #[test]
    #[ignore = "requires Spot"]
    fn min_dcw_of_a_dcw() {
        let spot = Spot::default();
        let dcw = ak22_figure_2();
        let minimal = spot.min_dcw(&dcw).unwrap().expect("a tDCW recognizes it");
        assert_eq!(minimal.size(), 2);
        assert!(spot.equivalent(&dcw, &minimal).unwrap());
    }

    /// "Eventually only `a`", by guessing when the last `b` was read.
    #[test]
    #[ignore = "requires Spot"]
    fn min_dcw_of_a_nondeterministic_ncw() {
        let spot = Spot::default();
        let ncw: NCW = NCW::builder()
            .with_edges([
                (0, 'a', true, 0),
                (0, 'b', true, 0),
                (0, 'a', false, 1),
                (1, 'a', false, 1),
            ])
            .into_ncw(0);
        let minimal = spot.min_dcw(&ncw).unwrap().expect("a tDCW recognizes it");
        assert_eq!(minimal.size(), 1);
        assert!(spot.equivalent(&ncw, &minimal).unwrap());
    }

    /// "Infinitely many `a`" is not recognized by any tDCW.
    #[test]
    #[ignore = "requires Spot"]
    fn min_dcw_of_a_language_without_dcw() {
        let dba = TSBuilder::without_state_colors()
            .with_edges([(0, 'a', true, 0), (0, 'b', false, 0)])
            .into_dba(0);
        assert_eq!(Spot::default().min_dcw(&dba).unwrap(), None);
    }

    #[test]
    #[ignore = "requires Spot"]
    fn equivalent() {
        let spot = Spot::default();
        let finitely_many_b = DCW::builder()
            .with_edges([(0, 'a', false, 0), (0, 'b', true, 0)])
            .into_dcw(0);
        let finitely_many_a = DCW::builder()
            .with_edges([(0, 'a', true, 0), (0, 'b', false, 0)])
            .into_dcw(0);
        assert!(spot.equivalent(&finitely_many_b, &finitely_many_b).unwrap());
        assert!(!spot.equivalent(&finitely_many_b, &finitely_many_a).unwrap());
    }
}
