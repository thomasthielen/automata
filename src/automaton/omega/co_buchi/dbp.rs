//! Determinizability by pruning (DBP) of minimal GFG-tNCWs, and the sufficient criteria for
//! d-size = hd-size that are checked on the canonical minimal GFG-tNCW `C` of a language.
//!
//! A tDCW with `|C|` states exists iff `C` is DBP, i.e. iff removing `α`-transitions turns `C`
//! into an equivalent deterministic automaton (the initial state may be moved to any state of
//! its class). A pruning found by [`NCW::hd_characteristics`] is a certificate for d = hd by
//! itself: it is a tDCW with hd states whose equivalence is checked by the search. The converse,
//! "not DBP ⇒ d > hd", relies on the thesis result that every minimal tDCW, once normalized,
//! embeds into `C` via the safe isomorphism of \[AK22, Theorem 4.2\].

use super::{DCW, NCW};
use crate::alphabet::CharAlphabet;
use crate::error::{Error, Result};
use crate::ts::{ForAlphabet, Sproutable};
use crate::{DTS, NTS, Pointed, TransitionSystem, Void};
use std::collections::{BTreeMap, BTreeSet};
use tracing::debug;

/// A sufficient criterion for d-size = hd-size, checked on the canonical minimal GFG-tNCW `C`.
/// Each criterion implies the next one in [`Criterion::ALL`], so [`Criterion::AlphaTargetCell`]
/// holds most often.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Criterion {
    /// hd equals the number of language classes, so `C` is deterministic already.
    Trivial,
    /// Every cell (see [`Cell`]) has exactly one maximum with respect to safe language
    /// inclusion (Löding). Then the cyclic pruning yields a tDCW with hd states.
    Cell,
    /// Like [`Criterion::Cell`], but only for cells whose class is the target of some
    /// `α`-transition, as the cyclic pruning never jumps into any other class. Only sketched.
    AlphaTargetCell,
}

impl Criterion {
    /// All criteria, from the strongest to the weakest.
    pub const ALL: [Criterion; 3] = [Self::Trivial, Self::Cell, Self::AlphaTargetCell];

    /// A short name, e.g. for column headers.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Trivial => "trivial",
            Self::Cell => "cell",
            Self::AlphaTargetCell => "alpha_target_cell",
        }
    }
}

/// A cell of a nice GFG-tNCW: the states of one language class that lie in one safe component.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cell {
    /// The states of the cell, in increasing order.
    pub states: Vec<u32>,
    /// The states of the cell whose safe language is not strictly contained in the safe language
    /// of another state of the cell, in increasing order.
    pub maxima: Vec<u32>,
    /// Whether some `α`-transition leads into the class of the cell.
    pub alpha_target: bool,
}

/// Outcome of the search for a deterministic pruning, see [`NCW::hd_characteristics`].
#[derive(Debug, Clone)]
pub enum Pruning {
    /// An equivalent tDCW obtained by removing `α`-transitions (and possibly moving the initial
    /// state within its class). Its states are numbered as in [`HdCharacteristics::minimal`].
    Found(DCW),
    /// No pruning is equivalent, so the automaton is not DBP.
    NotDbp,
    /// The search was skipped, as there are more prunings than allowed.
    TooLarge,
}

/// Characteristics of the canonical minimal GFG-tNCW of a language concerning d-size = hd-size,
/// as computed by [`NCW::hd_characteristics`].
#[derive(Debug, Clone)]
pub struct HdCharacteristics {
    /// The canonical minimal GFG-tNCW `C`, i.e. the result of [`NCW::minimize`], with its states
    /// renumbered to `0..hd`.
    pub minimal: NCW,
    /// The language classes of `C`.
    pub classes: Vec<Vec<u32>>,
    /// The safe components (SCCs of the safe transitions) of `C`, including trivial ones.
    pub components: Vec<Vec<u32>>,
    /// The nonempty cells of `C`.
    pub cells: Vec<Cell>,
    /// The number of candidate prunings (initial states times choices), saturating.
    pub prunings: u128,
    /// The outcome of the pruning search.
    pub pruning: Pruning,
}

impl HdCharacteristics {
    /// The size of a minimal GFG-tNCW for the language, the number of states of `C`.
    pub fn hd(&self) -> usize {
        self.minimal.size()
    }

    /// Returns `true` iff the given criterion holds.
    pub fn holds(&self, criterion: Criterion) -> bool {
        match criterion {
            Criterion::Trivial => self.classes.len() == self.hd(),
            Criterion::Cell => self.cells.iter().all(|c| c.maxima.len() == 1),
            Criterion::AlphaTargetCell => self
                .cells
                .iter()
                .filter(|c| c.alpha_target)
                .all(|c| c.maxima.len() == 1),
        }
    }

    /// Returns `Some(true)` if a pruning certifies d = hd, `Some(false)` if `C` is not DBP (so
    /// d > hd), and `None` if the search was skipped.
    pub fn d_equals_hd(&self) -> Option<bool> {
        match self.pruning {
            Pruning::Found(_) => Some(true),
            Pruning::NotDbp => Some(false),
            Pruning::TooLarge => None,
        }
    }

    /// The criteria that fail although d = hd is certified by a pruning. Each of them is shown
    /// to be only sufficient, not necessary.
    pub fn only_sufficient(&self) -> Vec<Criterion> {
        if self.d_equals_hd() != Some(true) {
            return vec![];
        }
        Criterion::ALL
            .into_iter()
            .filter(|&c| !self.holds(c))
            .collect()
    }

    /// The criteria that hold although `C` is not DBP. As [`Criterion::Trivial`] and
    /// [`Criterion::Cell`] are proved sufficient, this can only contain
    /// [`Criterion::AlphaTargetCell`], whose sufficiency is only sketched.
    pub fn refuted(&self) -> Vec<Criterion> {
        if self.d_equals_hd() != Some(false) {
            return vec![];
        }
        Criterion::ALL
            .into_iter()
            .filter(|&c| self.holds(c))
            .collect()
    }
}

impl NCW {
    /// Minimizes a copy of `self` (see [`NCW::minimize`]) and computes the characteristics of
    /// the resulting canonical minimal GFG-tNCW `C` that concern d-size = hd-size: its classes,
    /// safe components and cells, the [`Criterion`]s, and whether `C` is DBP.
    ///
    /// The DBP search tries every initial state of the class of the initial state together with
    /// every choice of one `α`-successor per state and letter, and checks the language
    /// containment of `C` in the pruned automaton with [`NCW::gfg_containment_relation`], which
    /// is exact here as the pruned automaton is deterministic. It is skipped if there are more
    /// than `max_prunings` candidates.
    ///
    /// # Errors
    /// [`Error::InvalidInput`] if `self` is not safe deterministic, which [`NCW::minimize`]
    /// requires. Like [`NCW::minimize`], this assumes that all states of `self` are GFG.
    pub fn hd_characteristics(&self, max_prunings: u128) -> Result<HdCharacteristics> {
        if !self.is_safe_deterministic() {
            return Err(Error::InvalidInput(
                "minimization requires a safe deterministic tNCW",
            ));
        }
        let mut minimized = self.clone();
        minimized.minimize();
        let minimal = Indexed::of(&minimized).ncw();
        let c = Indexed::of(&minimal);
        let n = c.n;

        let contained = minimal.gfg_containment_relation();
        let equivalent =
            |q: u32, s: u32| contained.contains(&(q, s)) && contained.contains(&(s, q));
        let classes = partition(n, equivalent);
        let safe_reach = c.safe_reachability();
        let components = partition(n, |q, s| {
            safe_reach[q as usize][s as usize] && safe_reach[s as usize][q as usize]
        });

        let subsafe = minimal.subsafe_equivalence_relation();
        let alpha_targets: BTreeSet<u32> = c.edges.iter().filter(|e| e.2).map(|e| e.3).collect();
        let mut cells = vec![];
        for class in &classes {
            let alpha_target = class.iter().any(|q| alpha_targets.contains(q));
            for component in &components {
                let states: Vec<u32> = class
                    .iter()
                    .copied()
                    .filter(|q| component.contains(q))
                    .collect();
                let strictly_below =
                    |q: u32, t: u32| subsafe.contains(&(q, t)) && !subsafe.contains(&(t, q));
                let maxima = states
                    .iter()
                    .copied()
                    .filter(|&q| !states.iter().any(|&t| strictly_below(q, t)))
                    .collect();
                if !states.is_empty() {
                    cells.push(Cell {
                        states,
                        maxima,
                        alpha_target,
                    });
                }
            }
        }

        let initials: Vec<u32> = (0..n as u32)
            .filter(|&q| equivalent(c.initial, q))
            .collect();
        let choices = c.choice_points();
        let prunings = choices
            .iter()
            .fold(initials.len() as u128, |acc, (_, targets)| {
                acc.saturating_mul(targets.len() as u128)
            });
        let pruning = if prunings > max_prunings {
            debug!("skipping DBP search over {prunings} prunings");
            Pruning::TooLarge
        } else {
            c.search_pruning(&initials, &choices)
        };

        Ok(HdCharacteristics {
            minimal,
            classes,
            components,
            cells,
            prunings,
            pruning,
        })
    }
}

/// Partitions `0..n` into the classes of the equivalence relation `equivalent`, each in
/// increasing order, ordered by their smallest element.
fn partition(n: usize, equivalent: impl Fn(u32, u32) -> bool) -> Vec<Vec<u32>> {
    let mut classes: Vec<Vec<u32>> = vec![];
    for q in 0..n as u32 {
        match classes.iter_mut().find(|k| equivalent(k[0], q)) {
            Some(k) => k.push(q),
            None => classes.push(vec![q]),
        }
    }
    classes
}

/// An NCW over a [`CharAlphabet`] with states `0..n`, as a list of transitions.
struct Indexed {
    alphabet: CharAlphabet,
    n: usize,
    initial: u32,
    edges: Vec<(u32, char, bool, u32)>,
}

impl Indexed {
    /// Renumbers the states of `ncw` to `0..n`, in increasing order of their indices.
    fn of(ncw: &NCW) -> Self {
        let index: BTreeMap<u32, u32> = ncw
            .state_indices()
            .enumerate()
            .map(|(i, q)| (q, i as u32))
            .collect();
        let mut edges: Vec<_> = ncw
            .state_indices()
            .flat_map(|q| ncw.transitions_from(q).collect::<Vec<_>>())
            .map(|(q, sym, color, p)| (index[&q], sym, color, index[&p]))
            .collect();
        edges.sort();
        Self {
            alphabet: ncw.alphabet().clone(),
            n: index.len(),
            initial: index[&ncw.initial()],
            edges,
        }
    }

    fn ncw(&self) -> NCW {
        let mut ts = NTS::for_alphabet(self.alphabet.clone());
        for _ in 0..self.n {
            ts.add_state(Void);
        }
        for &edge in &self.edges {
            ts.add_edge(edge);
        }
        NCW::from_parts(ts, self.initial)
    }

    /// `reach[q][s]` iff `s` is reachable from `q` via safe transitions (reflexively).
    fn safe_reachability(&self) -> Vec<Vec<bool>> {
        (0..self.n as u32)
            .map(|source| {
                let mut seen = vec![false; self.n];
                seen[source as usize] = true;
                let mut stack = vec![source];
                while let Some(q) = stack.pop() {
                    for &(_, _, _, p) in self.edges.iter().filter(|e| e.0 == q && !e.2) {
                        if !seen[p as usize] {
                            seen[p as usize] = true;
                            stack.push(p);
                        }
                    }
                }
                seen
            })
            .collect()
    }

    /// The pairs `(q, σ)` without a safe `σ`-transition but with several `α`-transitions on
    /// `σ`, together with their targets.
    fn choice_points(&self) -> Vec<((u32, char), Vec<u32>)> {
        let mut alpha: BTreeMap<(u32, char), Vec<u32>> = BTreeMap::new();
        let mut safe = BTreeSet::new();
        for &(q, sym, color, p) in &self.edges {
            if color {
                alpha.entry((q, sym)).or_default().push(p);
            } else {
                safe.insert((q, sym));
            }
        }
        alpha
            .into_iter()
            .filter(|(key, targets)| targets.len() > 1 && !safe.contains(key))
            .collect()
    }

    /// The deterministic automaton with initial state `initial` that keeps every transition
    /// except at the choice points, where it keeps the transition to `picked[i]`.
    fn pruned(&self, initial: u32, choices: &[((u32, char), Vec<u32>)], picked: &[u32]) -> Self {
        let chosen: BTreeMap<(u32, char), u32> = choices
            .iter()
            .zip(picked)
            .map(|((key, _), &p)| (*key, p))
            .collect();
        let edges = self
            .edges
            .iter()
            .copied()
            .filter(|&(q, sym, _, p)| chosen.get(&(q, sym)).is_none_or(|&c| c == p))
            .collect();
        Self {
            alphabet: self.alphabet.clone(),
            n: self.n,
            initial,
            edges,
        }
    }

    /// Returns `true` iff `L(self) ⊆ L(other)`, assuming that `other` is deterministic and all
    /// states of `self` are GFG, so that the containment game is exact.
    fn contained_in(&self, other: &Self) -> bool {
        let mut union = Self {
            alphabet: self.alphabet.clone(),
            n: self.n + other.n,
            initial: self.initial,
            edges: self.edges.clone(),
        };
        let offset = self.n as u32;
        union.edges.extend(
            other
                .edges
                .iter()
                .map(|&(q, sym, color, p)| (q + offset, sym, color, p + offset)),
        );
        union
            .ncw()
            .gfg_containment_relation()
            .contains(&(self.initial, other.initial + offset))
    }

    /// Searches all prunings and returns the first one that is equivalent to `self`.
    fn search_pruning(&self, initials: &[u32], choices: &[((u32, char), Vec<u32>)]) -> Pruning {
        for &initial in initials {
            // a mixed-radix counter over the choices
            let mut counter = vec![0usize; choices.len()];
            loop {
                let picked: Vec<u32> = choices
                    .iter()
                    .zip(&counter)
                    .map(|((_, targets), &i)| targets[i])
                    .collect();
                let pruned = self.pruned(initial, choices, &picked);
                // the pruning is a sub-automaton of `self` started in an equivalent state, so
                // its language is contained in that of `self`
                if self.contained_in(&pruned) {
                    return Pruning::Found(pruned.dcw());
                }
                let Some(digit) = (0..counter.len()).find(|&i| counter[i] + 1 < choices[i].1.len())
                else {
                    break;
                };
                counter[digit] += 1;
                counter[..digit].fill(0);
            }
        }
        Pruning::NotDbp
    }

    /// Turns a deterministic `self` into a [`DCW`].
    fn dcw(&self) -> DCW {
        let mut ts: DTS<CharAlphabet, Void, bool> = DTS::for_alphabet(self.alphabet.clone());
        for _ in 0..self.n {
            ts.add_state(Void);
        }
        for &edge in &self.edges {
            ts.add_edge(edge);
        }
        DCW::from_parts(ts, self.initial)
    }
}

#[cfg(test)]
mod tests {
    use super::{Criterion, Pruning};
    use crate::automaton::NCW;
    use crate::{Pointed, TransitionSystem};

    /// The canonical minimal GFG-tNCW of `L₁ = Σ*(Σa + Σbb)^ω`: three equivalent states, one
    /// safe component, and `α`-transitions to all of them.
    fn l1() -> NCW {
        let alpha = |q, sym| [0, 1, 2].map(|p| (q, sym, true, p));
        NCW::builder()
            .with_edges([(0, 'a', false, 2), (0, 'b', false, 2), (1, 'b', false, 0)])
            .with_edges([(2, 'a', false, 0), (2, 'b', false, 1)])
            .with_edges(alpha(1, 'a'))
            .into_ncw(0)
    }

    #[test]
    fn l1_is_not_dbp() {
        let hd = l1().hd_characteristics(1000).unwrap();
        assert_eq!(hd.hd(), 3);
        assert_eq!(hd.classes, vec![vec![0, 1, 2]]);
        assert_eq!(hd.components, vec![vec![0, 1, 2]]);
        assert_eq!(hd.cells[0].maxima, vec![0, 1, 2]);
        assert_eq!(hd.prunings, 9);
        assert!(matches!(hd.pruning, Pruning::NotDbp));
        assert!(Criterion::ALL.iter().all(|&c| !hd.holds(c)));
        assert!(hd.only_sufficient().is_empty() && hd.refuted().is_empty());
    }

    #[test]
    fn smallest_instance_failing_all_criteria_is_dbp() {
        // found by the `hd_criteria` example (seed 1007): one class and one safe component with
        // the two incomparable maxima 0 and 1, but pruning `1 -a=> 1` leaves an equivalent tDCW
        let ncw = NCW::builder()
            .with_edges([(0, 'a', false, 0), (0, 'b', false, 1), (1, 'b', false, 0)])
            .with_edges([(1, 'a', true, 0), (1, 'a', true, 1)])
            .into_ncw(0);
        let hd = ncw.hd_characteristics(1000).unwrap();
        assert_eq!(hd.hd(), 2);
        assert_eq!(hd.cells.len(), 1);
        assert_eq!(hd.cells[0].maxima, vec![0, 1]);
        assert_eq!(hd.only_sufficient(), Criterion::ALL.to_vec());
        let Pruning::Found(dcw) = hd.pruning else {
            panic!("expected a pruning");
        };
        assert_eq!(dcw.size(), 2);
    }

    #[test]
    fn deterministic_language_is_trivially_dbp() {
        // "finitely many `b`s": one class, already deterministic
        let ncw = NCW::builder()
            .with_edges([(0, 'a', false, 0), (0, 'b', true, 0)])
            .into_ncw(0);
        let hd = ncw.hd_characteristics(1000).unwrap();
        assert!(Criterion::ALL.iter().all(|&c| hd.holds(c)));
        let Pruning::Found(dcw) = hd.pruning else {
            panic!("expected a pruning");
        };
        assert_eq!(dcw.size(), 1);
        assert_eq!(dcw.initial(), 0);
    }

    #[test]
    fn search_is_skipped_above_the_limit() {
        let hd = l1().hd_characteristics(8).unwrap();
        assert!(matches!(hd.pruning, Pruning::TooLarge));
        assert_eq!(hd.d_equals_hd(), None);
    }

    #[test]
    fn rejects_input_that_is_not_safe_deterministic() {
        let ncw = NCW::builder()
            .with_edges([(0, 'a', false, 0), (0, 'a', false, 1), (1, 'a', false, 1)])
            .into_ncw(0);
        assert!(ncw.hd_characteristics(1000).is_err());
    }
}
