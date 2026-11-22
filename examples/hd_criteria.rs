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
//! removing unreachable ones), `alpha` (0.3; probability of an `α`-transition). Flags:
//! `spot` checks every witness for d = hd with Spot's `autfilt` whenever some criterion fails
//! although d = hd (adds the column `spot`); `automata` adds the columns `minimal_hd_tncw` and
//! `minimal_tdcw`.
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
//! - `minimal_hd_tncw` is `C`, and `minimal_tdcw` the witness (same state numbering), written as
//!   `init q` followed by the transitions `q-σ->p` (safe) and `q-σ=>p` (`α`).
//!
//! Anomalies, i.e. a pruning that is not equivalent or not `α`-saturated, or a criterion that
//! holds although d > hd, would contradict the thesis; they are reported on stderr.

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
        header.push("spot");
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
        let spot_check = if spot && !hd.only_sufficient().is_empty() {
            spot_equivalent(&ncw, &hd.pruning)
        } else {
            ""
        };
        summary.add(&hd, spot_check);

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
            row.push(spot_check.to_string());
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

#[cfg(feature = "spot")]
fn spot_equivalent(ncw: &automata::automaton::NCW, pruning: &Pruning) -> &'static str {
    let Pruning::Found(dcw) = pruning else {
        return "";
    };
    match automata::spot::Spot::from_env().equivalent(ncw, dcw) {
        Ok(true) => "equivalent",
        Ok(false) => "DIFFERENT",
        Err(e) => {
            eprintln!("Spot failed: {e}");
            "error"
        }
    }
}

#[cfg(not(feature = "spot"))]
fn spot_equivalent(_: &automata::automaton::NCW, _: &Pruning) -> &'static str {
    ""
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
    spot_confirmed: usize,
    spot_disagrees: usize,
}

impl Summary {
    fn add(&mut self, hd: &HdCharacteristics, spot: &str) {
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
        self.spot_confirmed += (spot == "equivalent") as usize;
        self.spot_disagrees += (spot == "DIFFERENT" || spot == "error") as usize;
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
        if self.spot_confirmed + self.spot_disagrees > 0 {
            eprintln!(
                "  Spot: {} witnesses equivalent, {} different or failed",
                self.spot_confirmed, self.spot_disagrees
            );
        }
    }
}
