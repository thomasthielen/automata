//! Draws random two-layer HD-tNCWs (or, as a baseline, uniformly random tDCWs), minimizes them
//! and checks the sufficient criteria for d-size = hd-size against an exact DBP search. Writes one CSV row per sample (UTF-8) to stdout
//! or to the file given by `out`, and a summary to stderr.
//!
//! ```shell
//! cargo run --release --features random --example hd_criteria -- samples=1500 out=hd.csv
//! cargo run --release --features spot,random --example hd_criteria -- spot   # also asks Spot
//! cargo run --release --features random --example hd_criteria -- generator=uniform size=8 alpha=0.4
//! ```
//!
//! Arguments (all optional, as `key=value`): `generator` (`layered` (default) for
//! [`LayeredNcw::random`], `uniform` for [`generate_random_dcw`]), `samples` (default 1000),
//! `seed` (0; sample `i` uses seed `seed + i`), `symbols` (2), `max_prunings` (3000), `out`
//! (stdout). For `layered`: `layer1` (4; the Layer-1 size of each sample is drawn from
//! `1..=layer1`), `children` (3), `safe` (0.75). For `uniform`: `size` (5; states before
//! removing unreachable ones), `alpha` (0.3; probability of an `α`-transition),
//! `spot_timeout` (600; seconds per SAT minimization, see below; `0` skips it, so that `spot`
//! only checks equivalence). Flags: `spot` cross-checks
//! every sample with Spot's `autfilt` (needs the feature `spot`, see [`automata::spot`]) and adds
//! the columns `spot_minimal`, `spot_prunings` and `spot_d`; `automata` adds the columns
//! `minimal_hd_tncw` and `minimal_tdcw`.
//!
//! Columns:
//! - `seed`: the seed of the sample; `layer1_size`, `ncw_size`: Layer-1 size (empty for
//!   `uniform`) and number of states of the generated tNCW.
//! - `hd`: number of states of the canonical minimal HD-tNCW `C`, without the implicit rejecting
//!   sink (see [`NCW::minimize`]); `classes`, `safe_components`,
//!   `cells`: its language classes, safe components and nonempty cells; `max_maximal_states`:
//!   the largest number of maximal states of a cell (a cell has a maximum iff this is 1).
//! - `residual`, `cell`, `successor`: whether the criterion holds (`1`/`0`).
//! - `d_eq_hd`: `1` if `C` is DBP (d = hd), `0` if not (d > hd), empty if the search was skipped
//!   as there are more than `max_prunings` candidate prunings (`candidate_prunings`).
//! - `witness`: what certifies d = hd: the cyclic pruning (`cell`), the successor pruning
//!   (`successor`) or the search (`search`); empty if d > hd or undecided.
//! - `spot_minimal`: whether Spot finds `C` equivalent to the generated tNCW (`equivalent`,
//!   `DIFFERENT` or `error`). This checks [`NCW::minimize`] independently of the containment
//!   game that it and all checks of this crate use.
//! - `spot_prunings`: the same for every pruning that was constructed and verified (cyclic,
//!   successor, search); `equivalent` only if Spot confirms all of them, empty if there is none.
//! - `spot_d`: unless a pruning certifies d = hd, the size of a minimal tDCW computed by Spot
//!   ([`Spot::min_dcw`](automata::spot::Spot::min_dcw), SAT-based), without a rejecting sink as
//!   for `hd`; empty if `spot_timeout=0`; `timeout` if it took longer than `spot_timeout` seconds (via coreutils `timeout`
//!   appended to the launcher), `error` if Spot failed. Spot's tDCW is checked to be
//!   equivalent to the generated tNCW.
//! - `minimal_hd_tncw` is `C`, and `minimal_tdcw` the witness (same state numbering), written as
//!   `init q` followed by the transitions `q-σ->p` (safe) and `q-σ=>p` (`α`).
//!
//! Anomalies, i.e. a pruning that is not equivalent or not `α`-saturated, or a criterion that
//! holds although d > hd, would contradict the thesis; they are reported on stderr. With
//! `spot`, so are disagreements with Spot: `C` or a pruning that Spot finds not equivalent, a
//! tDCW from Spot that is not equivalent, or `spot_d` < hd, or `spot_d` = hd for a `C` that the
//! search found not DBP.

use automata::alphabet::CharAlphabet;
use automata::automaton::NCW;
use automata::automaton::{Criterion, CyclicPruning, HdCharacteristics, Pruning, SuccessorPruning};
use automata::random::{LayeredNcw, LayeredParameters, generate_random_dcw};
use automata::{Pointed, TransitionSystem};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::collections::BTreeMap;
use std::error::Error;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::process::ExitCode;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut args: BTreeMap<String, String> = BTreeMap::new();
    for arg in std::env::args().skip(1) {
        let (key, value) = arg.split_once('=').unwrap_or((&arg, ""));
        args.insert(key.to_string(), value.to_string());
    }
    let number = |key: &str, default: f64| -> f64 {
        args.get(key)
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    };
    let samples = number("samples", 1000.0) as u64;
    let seed = number("seed", 0.0) as u64;
    let layer1 = number("layer1", 4.0) as usize;
    let max_prunings = number("max_prunings", 3000.0) as u128;
    let parameters = LayeredParameters {
        symbols: number("symbols", 2.0) as usize,
        layer1_size: layer1,
        max_children: number("children", 3.0) as usize,
        safe_probability: number("safe", 0.75),
    };
    let uniform = match args.get("generator").map(String::as_str) {
        None | Some("layered") => false,
        Some("uniform") => true,
        Some(other) => return Err(format!("unknown generator `{other}`").into()),
    };
    let size = number("size", 5.0) as usize;
    let alpha = number("alpha", 0.3);
    if uniform && (size == 0 || !(0.0..=1.0).contains(&alpha)) {
        return Err("`uniform` needs size >= 1 and alpha in [0, 1]".into());
    }
    let spot = args.contains_key("spot");
    if spot && !cfg!(feature = "spot") {
        return Err("the flag `spot` needs the feature `spot`".into());
    }
    let spot_timeout = number("spot_timeout", 600.0) as u64;
    let automata = args.contains_key("automata");
    let mut out: Box<dyn Write> = match args.get("out") {
        Some(path) if !path.is_empty() => Box::new(BufWriter::new(File::create(path)?)),
        _ => Box::new(BufWriter::new(std::io::stdout().lock())),
    };

    let mut header = vec![
        "seed",
        "layer1_size",
        "ncw_size",
        "hd",
        "classes",
        "safe_components",
        "cells",
        "max_maximal_states",
    ];
    header.extend(Criterion::ALL.map(|c| c.name()));
    header.extend(["d_eq_hd", "witness", "candidate_prunings"]);
    if spot {
        header.extend(["spot_minimal", "spot_prunings", "spot_d"]);
    }
    if automata {
        header.extend(["minimal_hd_tncw", "minimal_tdcw"]);
    }
    writeln!(out, "{}", header.join(","))?;

    let mut summary = Summary::default();
    for sample in 0..samples {
        let seed = seed + sample;
        let rng = &mut StdRng::seed_from_u64(seed);
        let (layer1_size, ncw): (String, NCW) = if uniform {
            let dcw = generate_random_dcw(parameters.symbols, size, alpha, rng);
            (String::new(), dcw.into_ncw())
        } else {
            let parameters = LayeredParameters {
                layer1_size: rng.gen_range(1..=layer1.max(1)),
                ..parameters
            };
            let layered = LayeredNcw::random(parameters, rng)
                .map_err(|e| format!("invalid parameters: {e}"))?;
            (layered.layer1_size().to_string(), layered.to_ncw())
        };
        let hd = ncw
            .hd_characteristics(max_prunings)
            .map_err(|e| format!("seed {seed}: {e}"))?;
        for anomaly in anomalies(&hd) {
            eprintln!("seed {seed}: {anomaly}");
            summary.anomalies += 1;
        }
        let spot_checks = if spot {
            let checks = spot_checks(&ncw, &hd, spot_timeout);
            for anomaly in checks.anomalies(&hd) {
                eprintln!("seed {seed}: {anomaly}");
                summary.anomalies += 1;
            }
            checks
        } else {
            SpotChecks::default()
        };
        summary.add(&hd, &spot_checks);

        let mut row = vec![
            seed.to_string(),
            layer1_size,
            ncw.size().to_string(),
            hd.hd().to_string(),
            hd.classes.len().to_string(),
            hd.components.len().to_string(),
            hd.cells.len().to_string(),
            hd.cells
                .iter()
                .map(|c| c.maxima.len())
                .max()
                .unwrap_or(0)
                .to_string(),
        ];
        row.extend(Criterion::ALL.map(|c| (hd.holds(c) as u8).to_string()));
        row.push(match hd.d_equals_hd() {
            Some(d_eq_hd) => (d_eq_hd as u8).to_string(),
            None => String::new(),
        });
        row.push(witness(&hd).to_string());
        row.push(hd.prunings.to_string());
        if spot {
            row.push(spot_checks.minimal.to_string());
            row.push(spot_checks.prunings.to_string());
            row.push(spot_checks.d.clone());
        }
        if automata {
            row.push(transitions(&hd.minimal));
            row.push(match &hd.pruning {
                Pruning::Found(dcw) => transitions(dcw),
                _ => String::new(),
            });
        }
        writeln!(out, "{}", row.join(","))?;
    }
    out.flush()?;
    summary.print(samples);
    Ok(())
}

/// What certifies d = hd: `cell` (the cyclic pruning), `successor` (the successor pruning),
/// `search`, or `""` if d > hd or the search was skipped.
fn witness(hd: &HdCharacteristics) -> &'static str {
    if hd.cyclic.verified().is_some() {
        "cell"
    } else if hd.successor.verified().is_some() {
        "successor"
    } else if let Pruning::Found(_) = hd.pruning {
        "search"
    } else {
        ""
    }
}

/// Outcomes that contradict the thesis (or indicate a bug).
fn anomalies(hd: &HdCharacteristics) -> Vec<String> {
    let mut anomalies = vec![];
    match &hd.cyclic {
        CyclicPruning::NotSaturated {
            state,
            symbol,
            target,
        } => anomalies.push(format!(
            "C is not α-saturated: {state} -{symbol}=> {target} is missing (cyclic pruning)"
        )),
        CyclicPruning::NotEquivalent(_) => {
            anomalies.push("the cyclic pruning is not equivalent to C".into())
        }
        _ => {}
    }
    match &hd.successor {
        SuccessorPruning::NotSaturated {
            state,
            symbol,
            target,
        } => anomalies.push(format!(
            "C is not α-saturated: {state} -{symbol}=> {target} is missing (successor pruning)"
        )),
        SuccessorPruning::NotEquivalent(_) => {
            anomalies.push("the successor pruning is not equivalent to C".into())
        }
        _ => {}
    }
    for c in hd.refuted() {
        anomalies.push(format!("the {} criterion holds although d > hd", c.name()));
    }
    anomalies
}

/// The transitions of an automaton as `q-σ->p` (safe) and `q-σ=>p` (`α`), initial state first.
/// Used for the minimal automaton and for the deterministic witness.
fn transitions<T>(c: &T) -> String
where
    T: TransitionSystem<StateIndex = u32, EdgeColor = bool, Alphabet = CharAlphabet> + Pointed,
{
    let mut edges: Vec<String> = vec![format!("init {}", c.initial())];
    for q in c.state_indices() {
        for (_, sym, alpha, p) in c.transitions_from(q) {
            edges.push(format!("{q}-{sym}{}{p}", if alpha { "=>" } else { "->" }));
        }
    }
    edges.join(" ")
}

/// The results of the Spot cross-checks of one sample, see the columns `spot_*`.
#[derive(Default)]
struct SpotChecks {
    minimal: &'static str,
    prunings: &'static str,
    /// the number of prunings that Spot found equivalent and the number of the others
    pruning_counts: (usize, usize),
    d: String,
    /// whether Spot's minimal tDCW is equivalent to the input, if it computed one
    d_equivalent: Option<&'static str>,
}

impl SpotChecks {
    fn anomalies(&self, hd: &HdCharacteristics) -> Vec<String> {
        let mut anomalies = vec![];
        if self.minimal == "DIFFERENT" {
            anomalies.push("Spot: C is not equivalent to the generated tNCW".to_string());
        }
        if self.prunings == "DIFFERENT" {
            anomalies.push("Spot: a verified pruning is not equivalent".to_string());
        }
        if self.d_equivalent == Some("DIFFERENT") {
            anomalies.push("Spot: its minimal tDCW is not equivalent".to_string());
        }
        if let Ok(d) = self.d.parse::<usize>() {
            if d < hd.hd() {
                anomalies.push(format!("Spot: d = {d} < hd = {}", hd.hd()));
            }
            if d == hd.hd() && hd.d_equals_hd() == Some(false) {
                anomalies.push(format!("Spot: d = hd = {d}, but C is not DBP"));
            }
        }
        anomalies
    }
}

#[cfg(feature = "spot")]
fn spot_checks(ncw: &NCW, hd: &HdCharacteristics, timeout: u64) -> SpotChecks {
    use automata::spot::{Spot, SpotError};

    let spot = Spot::from_env();
    let verdict = |result: Result<bool, SpotError>| match result {
        Ok(true) => "equivalent",
        Ok(false) => "DIFFERENT",
        Err(e) => {
            eprintln!("Spot failed: {e}");
            "error"
        }
    };
    let mut checks = SpotChecks {
        minimal: verdict(spot.equivalent(ncw, &hd.minimal)),
        ..SpotChecks::default()
    };

    // every verified pruning, each distinct one only once
    let mut prunings: Vec<&automata::automaton::DCW> = vec![];
    let found = match &hd.pruning {
        Pruning::Found(dcw) => Some(dcw),
        _ => None,
    };
    for dcw in [hd.cyclic.verified(), hd.successor.verified(), found]
        .into_iter()
        .flatten()
    {
        if !prunings.iter().any(|p| transitions(*p) == transitions(dcw)) {
            prunings.push(dcw);
        }
    }
    for dcw in &prunings {
        match verdict(spot.equivalent(ncw, *dcw)) {
            "equivalent" => checks.pruning_counts.0 += 1,
            other => {
                checks.pruning_counts.1 += 1;
                if checks.prunings != "DIFFERENT" {
                    checks.prunings = other;
                }
            }
        }
    }
    if checks.prunings.is_empty() && !prunings.is_empty() {
        checks.prunings = "equivalent";
    }

    // `spot_timeout=0` skips the SAT minimization (coreutils `timeout 0` would mean no limit)
    if hd.d_equals_hd() != Some(true) && timeout > 0 {
        // the launcher of `Spot::from_env`, followed by coreutils `timeout`
        let mut launcher: Vec<String> = match std::env::var(Spot::ENV) {
            Ok(launcher) => launcher.split_whitespace().map(String::from).collect(),
            Err(_) if cfg!(windows) => vec!["wsl".into(), "-e".into()],
            Err(_) => vec![],
        };
        launcher.extend(["timeout".to_string(), timeout.to_string()]);
        checks.d = match Spot::with_launcher(launcher).min_dcw(ncw) {
            Ok(Some(dcw)) => {
                checks.d_equivalent = Some(verdict(spot.equivalent(ncw, &dcw)));
                // without states of empty language, i.e. without a rejecting sink, as for `hd`
                let mut without_sink = dcw.into_ncw();
                without_sink.remove_empty_states();
                without_sink.size().to_string()
            }
            Ok(None) => "none".to_string(),
            Err(SpotError::Failed {
                status: Some(124), ..
            }) => "timeout".to_string(),
            Err(e) => {
                eprintln!("Spot failed: {e}");
                "error".to_string()
            }
        };
    }
    checks
}

#[cfg(not(feature = "spot"))]
fn spot_checks(_: &NCW, _: &HdCharacteristics, _: u64) -> SpotChecks {
    SpotChecks::default()
}

#[derive(Default)]
struct Summary {
    dbp: usize,
    not_dbp: usize,
    unknown: usize,
    /// per criterion: (holds, fails although d = hd)
    criteria: BTreeMap<Criterion, (usize, usize)>,
    /// samples with d = hd per witness
    witnesses: BTreeMap<&'static str, usize>,
    anomalies: usize,
    /// samples whose `C` Spot found equivalent, and the others
    spot_minimal: (usize, usize),
    /// prunings that Spot found equivalent, and the others
    spot_prunings: (usize, usize),
    /// `(hd, d_eq_hd, spot_d)` of the samples for which Spot computed d
    spot_d: Vec<(usize, Option<bool>, String)>,
}

impl Summary {
    fn add(&mut self, hd: &HdCharacteristics, spot: &SpotChecks) {
        match hd.d_equals_hd() {
            Some(true) => self.dbp += 1,
            Some(false) => self.not_dbp += 1,
            None => self.unknown += 1,
        }
        let only_sufficient = hd.only_sufficient();
        for c in Criterion::ALL {
            let entry = self.criteria.entry(c).or_default();
            entry.0 += hd.holds(c) as usize;
            entry.1 += only_sufficient.contains(&c) as usize;
        }
        let witness = witness(hd);
        if !witness.is_empty() {
            *self.witnesses.entry(witness).or_default() += 1;
        }
        match spot.minimal {
            "" => {}
            "equivalent" => self.spot_minimal.0 += 1,
            _ => self.spot_minimal.1 += 1,
        }
        self.spot_prunings.0 += spot.pruning_counts.0;
        self.spot_prunings.1 += spot.pruning_counts.1;
        if !spot.d.is_empty() {
            self.spot_d
                .push((hd.hd(), hd.d_equals_hd(), spot.d.clone()));
        }
    }

    fn print(&self, samples: u64) {
        eprintln!(
            "{samples} samples: d = hd {}, d > hd {}, undecided {}",
            self.dbp, self.not_dbp, self.unknown
        );
        for (c, (holds, only_sufficient)) in &self.criteria {
            eprintln!(
                "  {:<10} holds {holds:>6} | fails although d = hd {only_sufficient:>6}",
                c.name()
            );
        }
        let witnesses: Vec<String> = self
            .witnesses
            .iter()
            .map(|(name, count)| format!("{name} {count}"))
            .collect();
        eprintln!("  witness for d = hd: {}", witnesses.join(", "));
        if self.anomalies > 0 {
            eprintln!("  ANOMALIES: {}", self.anomalies);
        }
        if self.spot_minimal.0 + self.spot_minimal.1 > 0 {
            eprintln!(
                "  Spot: C equivalent for {} samples, different or failed for {}",
                self.spot_minimal.0, self.spot_minimal.1
            );
            eprintln!(
                "  Spot: {} prunings equivalent, {} different or failed",
                self.spot_prunings.0, self.spot_prunings.1
            );
            for (hd, d_eq_hd, d) in &self.spot_d {
                let search = match d_eq_hd {
                    Some(false) => "not DBP",
                    _ => "undecided",
                };
                eprintln!("  Spot: hd = {hd} ({search}), d = {d}");
            }
        }
    }
}
