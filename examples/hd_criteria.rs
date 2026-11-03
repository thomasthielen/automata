//! Draws random two-layer GFG-tNCWs, minimizes them and checks the sufficient criteria for
//! d-size = hd-size against an exact DBP search. Writes one CSV row per sample to stdout and a
//! summary to stderr.
//!
//! ```shell
//! cargo run --release --features random --example hd_criteria -- samples=1500 layer1=4
//! cargo run --release --features spot,random --example hd_criteria -- spot   # also asks Spot
//! ```
//!
//! Arguments (all optional, as `key=value`): `samples` (default 1000), `seed` (0; sample `i` uses
//! seed `seed + i`), `symbols` (2), `layer1` (4; the Layer-1 size of each sample is drawn from
//! `1..=layer1`), `children` (3), `safe` (0.75), `max_prunings` (3000). The flag `spot` checks
//! every pruning that shows a criterion to be only sufficient with Spot's `autfilt`.

use automata::automaton::{Criterion, HdCharacteristics, Pruning};
use automata::random::{LayeredNcw, LayeredParameters};
use automata::{Pointed, TransitionSystem};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::collections::BTreeMap;
use std::process::ExitCode;

fn main() -> ExitCode {
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
    let spot = args.contains_key("spot");
    if spot && !cfg!(feature = "spot") {
        eprintln!("the flag `spot` needs the feature `spot`");
        return ExitCode::FAILURE;
    }

    println!(
        "sample,seed,layer1,size,hd,classes,components,cells,max_maxima,{},prunings,d_eq_hd,only_sufficient,spot,minimal",
        Criterion::ALL.map(|c| c.name()).join(",")
    );
    let mut summary = Summary::default();
    for sample in 0..samples {
        let rng = &mut StdRng::seed_from_u64(seed + sample);
        let parameters = LayeredParameters {
            layer1_size: rng.gen_range(1..=layer1.max(1)),
            ..parameters
        };
        let layered = match LayeredNcw::random(parameters, rng) {
            Ok(layered) => layered,
            Err(e) => {
                eprintln!("invalid parameters: {e}");
                return ExitCode::FAILURE;
            }
        };
        let ncw = layered.to_ncw();
        let hd = match ncw.hd_characteristics(max_prunings) {
            Ok(hd) => hd,
            Err(e) => {
                eprintln!("sample {sample}: {e}");
                return ExitCode::FAILURE;
            }
        };
        let only_sufficient = hd.only_sufficient();
        let spot_check = if spot && !only_sufficient.is_empty() {
            spot_equivalent(&ncw, &hd.pruning)
        } else {
            String::new()
        };
        summary.add(&hd, &spot_check);
        println!(
            "{sample},{},{},{},{},{},{},{},{},{},{},{},{},{spot_check},{}",
            seed + sample,
            layered.layer1_size(),
            layered.size(),
            hd.hd(),
            hd.classes.len(),
            hd.components.len(),
            hd.cells.len(),
            hd.cells.iter().map(|c| c.maxima.len()).max().unwrap_or(0),
            Criterion::ALL
                .map(|c| hd.holds(c))
                .map(|b| b as u8)
                .map(|b| b.to_string())
                .join(","),
            hd.prunings,
            match hd.d_equals_hd() {
                Some(true) => "yes",
                Some(false) => "no",
                None => "unknown",
            },
            only_sufficient
                .iter()
                .map(|c| c.name())
                .collect::<Vec<_>>()
                .join(" "),
            transitions(&hd),
        );
    }
    summary.print(samples);
    ExitCode::SUCCESS
}

/// The transitions of the minimal automaton as `q-σ->p` (safe) and `q-σ=>p` (`α`), initial
/// state first.
fn transitions(hd: &HdCharacteristics) -> String {
    let c = &hd.minimal;
    let mut edges: Vec<String> = vec![format!("init {}", c.initial())];
    for q in c.state_indices() {
        for (_, sym, alpha, p) in c.transitions_from(q) {
            edges.push(format!("{q}-{sym}{}{p}", if alpha { "=>" } else { "->" }));
        }
    }
    edges.join(" ")
}

#[cfg(feature = "spot")]
fn spot_equivalent(ncw: &automata::automaton::NCW, pruning: &Pruning) -> String {
    let Pruning::Found(dcw) = pruning else {
        return String::new();
    };
    match automata::spot::Spot::from_env().equivalent(ncw, dcw) {
        Ok(true) => "equivalent".into(),
        Ok(false) => "DIFFERENT".into(),
        Err(e) => {
            eprintln!("Spot failed: {e}");
            "error".into()
        }
    }
}

#[cfg(not(feature = "spot"))]
fn spot_equivalent(_: &automata::automaton::NCW, _: &Pruning) -> String {
    String::new()
}

#[derive(Default)]
struct Summary {
    dbp: usize,
    not_dbp: usize,
    unknown: usize,
    /// per criterion: (holds, fails although d = hd, holds although d > hd)
    criteria: BTreeMap<Criterion, (usize, usize, usize)>,
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
        for c in Criterion::ALL {
            let entry = self.criteria.entry(c).or_default();
            entry.0 += hd.holds(c) as usize;
            entry.1 += hd.only_sufficient().contains(&c) as usize;
            entry.2 += hd.refuted().contains(&c) as usize;
        }
        self.spot_confirmed += (spot == "equivalent") as usize;
        self.spot_disagrees += (spot == "DIFFERENT" || spot == "error") as usize;
    }

    fn print(&self, samples: u64) {
        eprintln!(
            "{samples} samples: d = hd {}, d > hd {}, undecided {}",
            self.dbp, self.not_dbp, self.unknown
        );
        for (c, (holds, only_sufficient, refuted)) in &self.criteria {
            eprintln!(
                "  {:<18} holds {holds:>5} | fails although d = hd {only_sufficient:>5} | holds although d > hd {refuted:>3}",
                c.name()
            );
        }
        if self.spot_confirmed + self.spot_disagrees > 0 {
            eprintln!(
                "  Spot: {} witnesses equivalent, {} different or failed",
                self.spot_confirmed, self.spot_disagrees
            );
        }
    }
}
