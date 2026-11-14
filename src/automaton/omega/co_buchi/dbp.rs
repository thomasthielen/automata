//! Determinizability by pruning (DBP) of minimal HD-tNCWs, and the sufficient criteria for
//! d-size = hd-size that are checked on the canonical minimal HD-tNCW `C` of a language.
//!
//! A tDCW with `|C|` states exists iff `C` is DBP, i.e. iff removing `α`-transitions turns `C`
//! into an equivalent deterministic automaton (the initial state may be moved to any state of
//! its class). A pruning found by [`NCW::hd_characteristics`] is a certificate for d = hd by
//! itself: it is a tDCW with hd states whose equivalence is checked by the search. The converse,
//! "not DBP ⇒ d > hd", relies on the thesis result that every minimal tDCW, once normalized,
//! embeds into `C` via the safe isomorphism of \[AK22, Theorem 4.2\].
//!
//! Before searching, [`NCW::hd_characteristics`] builds the *cyclic pruning* (see
//! [`CyclicPruning`]), which needs no search and is equivalent to `C` whenever the cell criterion
//! holds. It is checked for equivalence like every other pruning, so it is a certificate for
//! d = hd by itself, also for automata that are too large for the search.

use super::{DCW, NCW};
use crate::alphabet::CharAlphabet;
use crate::error::{Error, Result};
use crate::ts::{ForAlphabet, Sproutable};
use crate::{DTS, NTS, Pointed, TransitionSystem, Void};
use std::collections::{BTreeMap, BTreeSet};
use tracing::{debug, warn};

/// A sufficient criterion for d-size = hd-size, checked on the canonical minimal HD-tNCW `C`.
/// Each criterion implies the next one in [`Criterion::ALL`], so [`Criterion::AlphaTargetCell`]
/// holds most often.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Criterion {
    /// hd equals the number of language classes, so `C` is deterministic already.
    Trivial,
    /// Every cell (see [`Cell`]) has a maximum, i.e. a state whose safe language contains the
    /// safe language of every other state of the cell (Löding). Then the cyclic pruning (see
    /// [`CyclicPruning`]) yields a tDCW with hd states.
    Cell,
    /// Like [`Criterion::Cell`], but only for cells whose class is the target of some
    /// `α`-transition, as the cyclic pruning never jumps into any other class. Also sufficient.
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

/// A cell of a nice HD-tNCW: the states of one language class that lie in one safe component.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cell {
    /// The index of the class of the cell in [`HdCharacteristics::classes`].
    pub class: usize,
    /// The index of the safe component of the cell in [`HdCharacteristics::components`].
    pub component: usize,
    /// The states of the cell, in increasing order.
    pub states: Vec<u32>,
    /// The states of the cell whose safe language is not strictly contained in the safe language
    /// of another state of the cell, in increasing order.
    pub maxima: Vec<u32>,
    /// The smallest maximum of the cell, i.e. the smallest state `m` with `x ≾ m` (the safe
    /// language of `x` is contained in that of `m`) for every state `x` of the cell, if there is
    /// one. As `C` is safe-minimal, a maximum is unique, and it exists iff `maxima` has exactly
    /// one element.
    pub maximum: Option<u32>,
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

/// The cyclic pruning of the canonical minimal HD-tNCW `C` (Löding's cell criterion).
///
/// The safe components of `C` are ordered cyclically as in [`HdCharacteristics::components`].
/// The pruning keeps every safe transition and the initial state of `C`. Where a state `q` has no
/// safe `σ`-transition, it keeps only the `α`-transition to the maximum of the cell `(C′, S_j)`
/// (see [`Cell::maximum`]),
/// where `C′` is the class of the `σ`-successors of `q` and `S_j` is the first component after
/// the one of `q` (cyclically, ending with the one of `q` itself) that contains states of `C′`.
/// If the cell criterion holds, the pruning is equivalent to `C`: on an accepted word, from some
/// point on a safe component `S*` contains, at every step, a state of the current class that
/// reads the rest of the word safely. The cyclic order never skips `S*`, and once the run lands in
/// `S*` on the maximum of a cell, it reads the rest of the word safely as well.
///
/// Only the cells that the pruning jumps into need a maximum, and these are cells of
/// `α`-target classes. So the pruning can be built whenever [`Criterion::AlphaTargetCell`] holds,
/// and sometimes even if it fails.
#[derive(Debug, Clone)]
pub enum CyclicPruning {
    /// The cyclic pruning, checked to be equivalent to `C`. Its states are numbered as in
    /// [`HdCharacteristics::minimal`].
    Verified(DCW),
    /// The cell `cells[cell]` (see [`HdCharacteristics::cells`]) that the pruning jumps into when
    /// `state` reads `symbol` has no maximum. This is the first such jump found.
    NoMaximum {
        /// The state without a safe `symbol`-transition.
        state: u32,
        /// The letter.
        symbol: char,
        /// The index of the cell in [`HdCharacteristics::cells`].
        cell: usize,
    },
    /// `C` has no `α`-transition from `state` on `symbol` to `target`, the maximum of the cell
    /// that the pruning jumps into. This cannot happen if `C` is `α`-saturated, as the canonical
    /// form of \[AK22, Theorem 4.6\] is.
    NotSaturated {
        /// The state without a safe `symbol`-transition.
        state: u32,
        /// The letter.
        symbol: char,
        /// The missing target.
        target: u32,
    },
    /// The cyclic pruning could be built, but it is not equivalent to `C`. This would contradict
    /// the sufficiency of the cell criterion, unless `C` is not normal.
    NotEquivalent(DCW),
}

impl CyclicPruning {
    /// The tDCW if the cyclic pruning is verified.
    pub fn verified(&self) -> Option<&DCW> {
        match self {
            Self::Verified(dcw) => Some(dcw),
            _ => None,
        }
    }

    /// A short name, e.g. for CSV columns.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Verified(_) => "verified",
            Self::NoMaximum { .. } => "no_maximum",
            Self::NotSaturated { .. } => "not_saturated",
            Self::NotEquivalent(_) => "NOT_EQUIVALENT",
        }
    }
}

/// Characteristics of the canonical minimal HD-tNCW of a language concerning d-size = hd-size,
/// as computed by [`NCW::hd_characteristics`].
#[derive(Debug, Clone)]
pub struct HdCharacteristics {
    /// The canonical minimal HD-tNCW `C`, i.e. the result of [`NCW::minimize`], with its states
    /// renumbered to `0..hd`.
    pub minimal: NCW,
    /// The language classes of `C`.
    pub classes: Vec<Vec<u32>>,
    /// The safe components (SCCs of the safe transitions) of `C`, including trivial ones.
    pub components: Vec<Vec<u32>>,
    /// The nonempty cells of `C`, ordered by class and then by component.
    pub cells: Vec<Cell>,
    /// The cyclic pruning of `C`.
    pub cyclic: CyclicPruning,
    /// The number of candidate prunings (initial states times choices), saturating.
    pub prunings: u128,
    /// The verified cyclic pruning if there is one, otherwise the outcome of the pruning search.
    pub pruning: Pruning,
}

impl HdCharacteristics {
    /// The size of a minimal HD-tNCW for the language, the number of states of `C`.
    pub fn hd(&self) -> usize {
        self.minimal.size()
    }

    /// Returns `true` iff the given criterion holds.
    pub fn holds(&self, criterion: Criterion) -> bool {
        match criterion {
            Criterion::Trivial => self.classes.len() == self.hd(),
            Criterion::Cell => self.cells.iter().all(|c| c.maximum.is_some()),
            Criterion::AlphaTargetCell => self
                .cells
                .iter()
                .filter(|c| c.alpha_target)
                .all(|c| c.maximum.is_some()),
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

    /// The criteria that hold although `C` is not DBP. As all criteria are proved sufficient,
    /// this is empty unless the minimization or the DBP search is wrong.
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
    /// the resulting canonical minimal HD-tNCW `C` that concern d-size = hd-size: its classes,
    /// safe components and cells, the [`Criterion`]s, the [`CyclicPruning`], and whether `C` is
    /// DBP.
    ///
    /// If the cyclic pruning is verified, it is the result and there is no search. Otherwise the
    /// DBP search tries every initial state of the class of the initial state together with
    /// every choice of one `α`-successor per state and letter, and checks the language
    /// containment of `C` in the pruned automaton with [`NCW::gfg_containment_relation`], which
    /// is exact here as the pruned automaton is deterministic. It is skipped if there are more
    /// than `max_prunings` candidates.
    ///
    /// # Errors
    /// [`Error::InvalidInput`] if `self` is not safe deterministic, which [`NCW::minimize`]
    /// requires. Like [`NCW::minimize`], this assumes that all states of `self` are HD.
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
        for (class_index, class) in classes.iter().enumerate() {
            let alpha_target = class.iter().any(|q| alpha_targets.contains(q));
            for (component_index, component) in components.iter().enumerate() {
                let states: Vec<u32> = class
                    .iter()
                    .copied()
                    .filter(|q| component.contains(q))
                    .collect();
                let below = |q: u32, t: u32| q == t || subsafe.contains(&(q, t));
                let strictly_below = |q: u32, t: u32| below(q, t) && !below(t, q);
                let maxima = states
                    .iter()
                    .copied()
                    .filter(|&q| !states.iter().any(|&t| strictly_below(q, t)))
                    .collect();
                let maximum = states
                    .iter()
                    .copied()
                    .find(|&m| states.iter().all(|&x| below(x, m)));
                if !states.is_empty() {
                    cells.push(Cell {
                        class: class_index,
                        component: component_index,
                        states,
                        maxima,
                        maximum,
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
        let cyclic = c.cyclic_pruning(&classes, &components, &cells);
        match &cyclic {
            CyclicPruning::NotSaturated {
                state,
                symbol,
                target,
            } => warn!("C is not α-saturated: {state} -{symbol}=> {target} is missing"),
            CyclicPruning::NotEquivalent(_) => warn!("the cyclic pruning is not equivalent to C"),
            _ => {}
        }
        let pruning = if let Some(dcw) = cyclic.verified() {
            Pruning::Found(dcw.clone())
        } else if prunings > max_prunings {
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
            cyclic,
            prunings,
            pruning,
        })
    }
}

/// For each of `0..n`, the index of the block of `partition` that contains it.
fn block_of(n: usize, partition: &[Vec<u32>]) -> Vec<usize> {
    let mut block = vec![0; n];
    for (i, states) in partition.iter().enumerate() {
        for &q in states {
            block[q as usize] = i;
        }
    }
    block
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
        self.dead_points()
            .into_iter()
            .filter(|(_, targets)| targets.len() > 1)
            .collect()
    }

    /// The pairs `(q, σ)` without a safe `σ`-transition but with some `α`-transition on `σ`,
    /// together with the targets of these `α`-transitions.
    fn dead_points(&self) -> Vec<((u32, char), Vec<u32>)> {
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
            .filter(|(key, _)| !safe.contains(key))
            .collect()
    }

    /// Builds the cyclic pruning (see [`CyclicPruning`]) from the classes, the safe components in
    /// their cyclic order, and the cells, and checks it for equivalence.
    fn cyclic_pruning(
        &self,
        classes: &[Vec<u32>],
        components: &[Vec<u32>],
        cells: &[Cell],
    ) -> CyclicPruning {
        let class_of = block_of(self.n, classes);
        let component_of = block_of(self.n, components);
        let cell_of: BTreeMap<(usize, usize), usize> = cells
            .iter()
            .enumerate()
            .map(|(i, cell)| ((cell.class, cell.component), i))
            .collect();
        let k = components.len();
        let mut chosen: BTreeMap<(u32, char), u32> = BTreeMap::new();
        for ((q, symbol), targets) in self.dead_points() {
            let class = class_of[targets[0] as usize];
            let own = component_of[q as usize];
            // the cell of the first component after the one of `q` that meets the class; it
            // exists, as the component of `targets[0]` meets the class
            let Some(&cell) = (1..=k).find_map(|i| cell_of.get(&(class, (own + i) % k))) else {
                continue;
            };
            let Some(target) = cells[cell].maximum else {
                return CyclicPruning::NoMaximum {
                    state: q,
                    symbol,
                    cell,
                };
            };
            if !targets.contains(&target) {
                return CyclicPruning::NotSaturated {
                    state: q,
                    symbol,
                    target,
                };
            }
            chosen.insert((q, symbol), target);
        }
        let pruned = Self {
            alphabet: self.alphabet.clone(),
            n: self.n,
            initial: self.initial,
            edges: self
                .edges
                .iter()
                .copied()
                .filter(|&(q, sym, alpha, p)| !alpha || chosen.get(&(q, sym)) == Some(&p))
                .collect(),
        };
        // the pruning is a sub-automaton of `self` with the same initial state
        if self.contained_in(&pruned) {
            CyclicPruning::Verified(pruned.dcw())
        } else {
            CyclicPruning::NotEquivalent(pruned.dcw())
        }
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
    /// states of `self` are HD, so that the containment game is exact.
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
    use super::{Criterion, CyclicPruning, Pruning};
    use crate::automaton::NCW;
    use crate::{Pointed, TransitionSystem};

    /// The canonical minimal HD-tNCW of `L₁ = Σ*(Σa + Σbb)^ω`: three equivalent states, one
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
        assert_eq!(hd.cells[0].maximum, None);
        assert_eq!(hd.prunings, 9);
        assert!(matches!(hd.pruning, Pruning::NotDbp));
        assert!(matches!(
            hd.cyclic,
            CyclicPruning::NoMaximum {
                state: 1,
                symbol: 'a',
                cell: 0
            }
        ));
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
        assert_eq!(hd.cells[0].maximum, None);
        assert_eq!(hd.only_sufficient(), Criterion::ALL.to_vec());
        assert!(matches!(hd.cyclic, CyclicPruning::NoMaximum { .. }));
        let Pruning::Found(dcw) = hd.pruning else {
            panic!("expected a pruning");
        };
        assert_eq!(dcw.size(), 2);
    }

    /// The example of the cyclic-pruning figure: Layer 1 is `p0 -b-> p0, p0 -a,c-> p1,
    /// p1 -a-> p0, p1 -b,c-> p1`; `q0, q1, q3, q4` are children of `p0`, and `q2, q5` of `p1`.
    /// The safe components `{q0, q1, q2}`, `{q3}`, `{q4, q5}`: every cell has a maximum, and
    /// every missing safe transition has `α`-transitions to all children of the Layer-1
    /// successor.
    fn cyclic_example() -> NCW {
        let p0 = [0, 1, 3, 4];
        let p1 = [2, 5];
        let mut alpha = vec![];
        for (q, sym, children) in [
            (0, 'c', &p1[..]),
            (1, 'b', &p0[..]),
            (1, 'c', &p1[..]),
            (2, 'b', &p1[..]),
            (2, 'c', &p1[..]),
            (3, 'a', &p1[..]),
            (3, 'c', &p1[..]),
            (4, 'a', &p1[..]),
            (4, 'b', &p0[..]),
            (5, 'b', &p1[..]),
            (5, 'c', &p1[..]),
        ] {
            alpha.extend(children.iter().map(|&p| (q, sym, true, p)));
        }
        NCW::builder()
            .with_edges([(0, 'b', false, 1), (0, 'a', false, 2), (2, 'a', false, 0)])
            .with_edges([(1, 'a', false, 2), (3, 'b', false, 3)])
            .with_edges([(4, 'c', false, 5), (5, 'a', false, 4)])
            .with_edges(alpha)
            .into_ncw(0)
    }

    #[test]
    fn cyclic_pruning_certifies_d_equals_hd_without_search() {
        // 4 initial states times 2^9 * 4^2 choices; the search is disabled
        let hd = cyclic_example().hd_characteristics(0).unwrap();
        assert_eq!(hd.hd(), 6);
        assert_eq!(hd.classes, vec![vec![0, 1, 3, 4], vec![2, 5]]);
        assert_eq!(hd.components, vec![vec![0, 1, 2], vec![3], vec![4, 5]]);
        assert_eq!(hd.prunings, 32768);
        assert!(hd.holds(Criterion::Cell));
        // the only cell with several states is `{q0, q1}`, with maximum `q0`
        let cell = hd.cells.iter().find(|c| c.states == [0, 1]).unwrap();
        assert_eq!(cell.maximum, Some(0));
        assert_eq!(hd.d_equals_hd(), Some(true));
        let Some(dcw) = hd.cyclic.verified() else {
            panic!("expected a verified cyclic pruning, got {:?}", hd.cyclic);
        };
        assert_eq!(dcw.size(), 6);
        assert_eq!(dcw.initial(), 0);
        let mut alpha: Vec<_> = dcw
            .state_indices()
            .flat_map(|q| dcw.transitions_from(q).collect::<Vec<_>>())
            .filter(|t| t.2)
            .map(|(q, sym, _, p)| (q, sym, p))
            .collect();
        alpha.sort();
        // the jumps of the table in the figure: e.g. `q2` skips `{q3}` (no child of `p1`), and
        // `q4 -b->` wraps around to the maximum `q0` of its cell, not to `q1`
        assert_eq!(
            alpha,
            vec![
                (0, 'c', 5),
                (1, 'b', 3),
                (1, 'c', 5),
                (2, 'b', 5),
                (2, 'c', 5),
                (3, 'a', 5),
                (3, 'c', 5),
                (4, 'a', 2),
                (4, 'b', 0),
                (5, 'b', 2),
                (5, 'c', 2),
            ]
        );
    }

    #[test]
    fn deterministic_language_is_trivially_dbp() {
        // "finitely many `b`s": one class, already deterministic
        let ncw = NCW::builder()
            .with_edges([(0, 'a', false, 0), (0, 'b', true, 0)])
            .into_ncw(0);
        let hd = ncw.hd_characteristics(1000).unwrap();
        assert!(Criterion::ALL.iter().all(|&c| hd.holds(c)));
        assert!(hd.cyclic.verified().is_some());
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
