//! Random two-layer GFG-tNCWs, see [`LayeredNcw`].

use crate::alphabet::CharAlphabet;
use crate::automaton::NCW;
use crate::error::{Error, Result};
use crate::ts::{ForAlphabet, Sproutable};
use crate::{NTS, Void};
use rand::Rng;

/// Parameters of [`LayeredNcw::random`].
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LayeredParameters {
    /// The number of letters, between 1 and 25.
    pub symbols: usize,
    /// The number of Layer-1 states, at least 1. With a single one, the language is
    /// prefix-independent.
    pub layer1_size: usize,
    /// Each Layer-1 state gets between 1 and `max_children` children, uniformly.
    pub max_children: usize,
    /// The probability that a state has a safe transition on a letter, between 0 and 1. Safe
    /// transitions that would leave their safe component are dropped afterwards (R4), so the
    /// actual share is lower.
    pub safe_probability: f64,
}

impl Default for LayeredParameters {
    /// The parameters of the first experiments: two letters, three Layer-1 states, up to three
    /// children each, and safe transitions with probability 0.75.
    fn default() -> Self {
        Self {
            symbols: 2,
            layer1_size: 3,
            max_children: 3,
            safe_probability: 0.75,
        }
    }
}

/// A two-layer GFG-tNCW, generalizing the canonical automaton `A≡L` of \[LW25, Definition 3.7\].
///
/// Layer 1 is a complete deterministic transition system `τ` over the Layer-1 states `P`.
/// Layer 2 consists of the states of the automaton, each with a parent in `P`, and is subject to
/// - R1 (morphism): a safe transition `q -σ-> q'` has `parent(q') = τ(parent(q), σ)`,
/// - R2 (children rule): if `q` has no safe `σ`-transition, it has `α`-transitions on `σ` to
///   all children of `τ(parent(q), σ)`,
/// - R3: every Layer-1 state has a child,
/// - R4 (normal): safe transitions do not leave their safe component.
///
/// In `A≡L`, Layer 1 is the right congruence `∼L`, the states are the pointed classes `[u, v]`
/// with parent `[uv]`, and R1, R3 and R4 hold by definition, \[LW25, Lemma 3.15\] and
/// \[LW25, Lemma 3.19\]. Unlike R2, `A≡L` is unsafe-saturated: it has the `α`-transitions to all
/// children of `τ(parent(q), σ)` even if `q` has a safe `σ`-transition. Dropping them keeps the
/// automaton `α`-homogeneous, as in \[AK22\], and does not affect GFGness: the proof of
/// \[LW25, Lemma 2.2\] uses unsafe-saturation only for a state without a safe transition on the
/// letter, which is exactly where R2 adds `α`-transitions, and the state it needs is among
/// these targets, since all transitions are level by R1 and R2. Here, Layer 1 may be finer than
/// `∼L`, and the states need not be pointed classes, i.e. the automaton need not be safe-minimal
/// or safe-centralized.
///
/// States with the same parent have the same language, and every state is GFG, so the result is
/// a valid input for [`NCW::minimize`] and [`NCW::hd_characteristics`]. Every language of a
/// GFG-tNCW has such a representation, as the canonical minimal GFG-tNCW is two-layered itself.
///
/// The initial state is state 0, whose parent is the initial Layer-1 state 0.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LayeredNcw {
    tau: Vec<Vec<usize>>,
    parent: Vec<usize>,
    safe: Vec<Vec<Option<usize>>>,
}

impl LayeredNcw {
    /// Creates a two-layer tNCW from the Layer-1 transitions `tau[p][i]` (Layer-1 state reached
    /// from `p` on the `i`-th letter), the parents `parent[q]` of the states, and the safe
    /// transitions `safe[q][i]`. Safe transitions that leave their safe component are dropped
    /// (R4); all other transitions follow from the children rule (R2).
    ///
    /// # Errors
    /// [`Error::InvalidInput`] if the dimensions do not match, a letter or state is out of range,
    /// `parent[0] != 0`, a Layer-1 state has no child (R3), or a safe transition violates the
    /// morphism rule (R1).
    pub fn new(
        tau: Vec<Vec<usize>>,
        parent: Vec<usize>,
        safe: Vec<Vec<Option<usize>>>,
    ) -> Result<Self> {
        let symbols = tau.first().map_or(0, Vec::len);
        if !(1..=25).contains(&symbols) || tau.iter().any(|row| row.len() != symbols) {
            return Err(Error::InvalidInput(
                "Layer 1 needs between 1 and 25 letters on every state",
            ));
        }
        if tau.iter().flatten().any(|&p| p >= tau.len()) {
            return Err(Error::InvalidInput("Layer-1 transition to a missing state"));
        }
        if parent.first() != Some(&0) || parent.iter().any(|&p| p >= tau.len()) {
            return Err(Error::InvalidInput(
                "state 0 must have parent 0, and every parent must be a Layer-1 state",
            ));
        }
        if (0..tau.len()).any(|p| !parent.contains(&p)) {
            return Err(Error::InvalidInput("a Layer-1 state has no child (R3)"));
        }
        if safe.len() != parent.len() || safe.iter().any(|row| row.len() != symbols) {
            return Err(Error::InvalidInput(
                "safe transitions need one entry per state and letter",
            ));
        }
        for (q, row) in safe.iter().enumerate() {
            for (i, target) in row.iter().enumerate() {
                if let Some(t) = *target
                    && parent.get(t) != Some(&tau[parent[q]][i])
                {
                    return Err(Error::InvalidInput(
                        "a safe transition violates the morphism rule (R1)",
                    ));
                }
            }
        }
        let mut layered = Self { tau, parent, safe };
        layered.normalize();
        Ok(layered)
    }

    /// Draws a random two-layer tNCW:
    /// 1. Layer 1 gets `layer1_size` states with uniformly drawn transitions, redrawn until all
    ///    states are reachable from state 0.
    /// 2. Each Layer-1 state gets between 1 and `max_children` children.
    /// 3. With probability `safe_probability`, a state gets a safe transition on a letter, to a
    ///    uniformly drawn child of the Layer-1 successor (R1).
    /// 4. Safe transitions that leave their safe component are dropped (R4).
    ///
    /// All randomness is drawn from `rng`, so the result is reproducible for a seeded `rng`.
    ///
    /// # Errors
    /// [`Error::InvalidInput`] if a parameter is out of the range given in
    /// [`LayeredParameters`].
    pub fn random(parameters: LayeredParameters, rng: &mut impl Rng) -> Result<Self> {
        let LayeredParameters {
            symbols,
            layer1_size: m,
            max_children,
            safe_probability,
        } = parameters;
        if !(1..=25).contains(&symbols) || m == 0 || max_children == 0 {
            return Err(Error::InvalidInput(
                "a layered tNCW needs 1 to 25 letters, a Layer-1 state and a child per state",
            ));
        }
        if !(0.0..=1.0).contains(&safe_probability) {
            return Err(Error::InvalidInput("safe_probability must lie in [0, 1]"));
        }
        let tau = loop {
            let tau: Vec<Vec<usize>> = (0..m)
                .map(|_| (0..symbols).map(|_| rng.gen_range(0..m)).collect())
                .collect();
            if reachable(m, 0, |p| tau[p].clone()).iter().all(|&r| r) {
                break tau;
            }
        };
        let parent: Vec<usize> = (0..m)
            .flat_map(|p| std::iter::repeat_n(p, rng.gen_range(1..=max_children)))
            .collect();
        let children: Vec<Vec<usize>> = (0..m)
            .map(|p| (0..parent.len()).filter(|&q| parent[q] == p).collect())
            .collect();
        let safe = (0..parent.len())
            .map(|q| {
                (0..symbols)
                    .map(|i| {
                        let targets = &children[tau[parent[q]][i]];
                        rng.gen_bool(safe_probability)
                            .then(|| targets[rng.gen_range(0..targets.len())])
                    })
                    .collect()
            })
            .collect();
        let mut layered = Self { tau, parent, safe };
        layered.normalize();
        Ok(layered)
    }

    /// The number of letters.
    pub fn symbols(&self) -> usize {
        self.tau[0].len()
    }

    /// The number of Layer-1 states.
    pub fn layer1_size(&self) -> usize {
        self.tau.len()
    }

    /// The number of (Layer-2) states of the automaton.
    pub fn size(&self) -> usize {
        self.parent.len()
    }

    /// The parent of each state.
    pub fn parents(&self) -> &[usize] {
        &self.parent
    }

    /// The children of the Layer-1 state `p`, in increasing order.
    pub fn children(&self, p: usize) -> Vec<usize> {
        (0..self.size()).filter(|&q| self.parent[q] == p).collect()
    }

    /// The tNCW: the safe transitions, and `α`-transitions by the children rule (R2). The
    /// letters are those of [`CharAlphabet::of_size`], the states keep their indices, and state
    /// 0 is initial.
    pub fn to_ncw(&self) -> NCW {
        let alphabet = CharAlphabet::of_size(self.symbols());
        let mut ts = NTS::for_alphabet(alphabet.clone());
        for _ in 0..self.size() {
            ts.add_state(Void);
        }
        for q in 0..self.size() {
            for i in 0..self.symbols() {
                match self.safe[q][i] {
                    Some(t) => {
                        ts.add_edge((q as u32, alphabet[i], false, t as u32));
                    }
                    None => {
                        for t in self.children(self.tau[self.parent[q]][i]) {
                            ts.add_edge((q as u32, alphabet[i], true, t as u32));
                        }
                    }
                }
            }
        }
        NCW::from_parts(ts, 0)
    }

    /// Drops the safe transitions that leave their safe component (R4); by the children rule
    /// (R2), they become `α`-transitions to the children of the Layer-1 successor.
    fn normalize(&mut self) {
        let n = self.size();
        let reach: Vec<Vec<bool>> = (0..n)
            .map(|q| reachable(n, q, |s| self.safe[s].iter().flatten().copied().collect()))
            .collect();
        for (q, row) in self.safe.iter_mut().enumerate() {
            for target in row.iter_mut() {
                if target.is_some_and(|t| !reach[t][q]) {
                    *target = None;
                }
            }
        }
    }
}

/// The states among `0..n` that are reachable from `source` via `successors`.
fn reachable(n: usize, source: usize, successors: impl Fn(usize) -> Vec<usize>) -> Vec<bool> {
    let mut seen = vec![false; n];
    seen[source] = true;
    let mut stack = vec![source];
    while let Some(q) = stack.pop() {
        for t in successors(q) {
            if !seen[t] {
                seen[t] = true;
                stack.push(t);
            }
        }
    }
    seen
}

#[cfg(test)]
mod tests {
    use super::{LayeredNcw, LayeredParameters};
    use crate::TransitionSystem;
    use crate::automaton::{Criterion, CyclicPruning, Pruning};
    use rand::{SeedableRng, rngs::StdRng};

    /// The completed sketch of the 09-08 meeting: Layer 1 is `p0 -a-> p0, p0 -b-> p1,
    /// p1 -a-> p0, p1 -b-> p2, p2 -a-> p1, p2 -b-> p0`, and the states are
    /// `q3, q4, q5, q6, q7, q8, q9, q10` with parents `0, 0, 1, 2, 2, 1, 1, 0`.
    fn completed_sketch() -> LayeredNcw {
        LayeredNcw::new(
            vec![vec![0, 1], vec![0, 2], vec![1, 0]],
            vec![0, 0, 1, 2, 2, 1, 1, 0],
            vec![
                vec![Some(1), Some(2)],
                vec![None, Some(2)],
                vec![Some(0), None],
                vec![Some(6), None],
                vec![Some(5), Some(7)],
                vec![None, Some(3)],
                vec![None, Some(4)],
                vec![None, Some(5)],
            ],
        )
        .unwrap()
    }

    #[test]
    fn completed_sketch_shows_that_the_criteria_are_only_sufficient() {
        let hd = completed_sketch()
            .to_ncw()
            .hd_characteristics(100_000)
            .unwrap();
        assert_eq!(hd.hd(), 8);
        assert_eq!(hd.classes.len(), 3);
        assert_eq!(hd.only_sufficient(), Criterion::ALL.to_vec());
        let Pruning::Found(dcw) = &hd.pruning else {
            panic!("the completed sketch is DBP");
        };
        assert_eq!(dcw.size(), 8);
    }

    #[test]
    fn new_checks_the_rules() {
        // q1 has parent 1, but the safe a-transition of q0 must lead to a child of p0 (R1)
        let r1 = LayeredNcw::new(
            vec![vec![0], vec![1]],
            vec![0, 1],
            vec![vec![Some(1)], vec![None]],
        );
        assert!(r1.is_err());
        // p1 has no child (R3)
        let r3 = LayeredNcw::new(vec![vec![1], vec![0]], vec![0], vec![vec![None]]);
        assert!(r3.is_err());
    }

    #[test]
    fn new_normalizes() {
        // the safe a-transition from q0 to q1 cannot be taken back, so it is dropped
        let layered = LayeredNcw::new(
            vec![vec![0]],
            vec![0, 0],
            vec![vec![Some(1)], vec![Some(1)]],
        )
        .unwrap();
        let ncw = layered.to_ncw();
        let mut transitions: Vec<_> = ncw.transitions_from(0).collect();
        transitions.sort();
        assert_eq!(transitions, vec![(0, 'a', true, 0), (0, 'a', true, 1)]);
    }

    #[test]
    fn random_rejects_invalid_parameters() {
        let rng = &mut StdRng::seed_from_u64(0);
        for parameters in [
            LayeredParameters {
                symbols: 0,
                ..Default::default()
            },
            LayeredParameters {
                layer1_size: 0,
                ..Default::default()
            },
            LayeredParameters {
                safe_probability: 1.5,
                ..Default::default()
            },
        ] {
            assert!(LayeredNcw::random(parameters, rng).is_err());
        }
    }

    #[test]
    fn random_layered_ncws_are_valid_and_find_insufficient_criteria() {
        let mut only_sufficient = 0;
        for seed in 0..60 {
            let rng = &mut StdRng::seed_from_u64(seed);
            let layered = LayeredNcw::random(LayeredParameters::default(), rng).unwrap();
            let ncw = layered.to_ncw();
            assert!(ncw.is_safe_deterministic());
            assert!(ncw.is_semantically_deterministic());
            let hd = ncw.hd_characteristics(2000).unwrap();
            assert!(hd.hd() <= layered.size());
            // the cell criterion is proved sufficient, and the cyclic pruning is the witness; it
            // can be built as soon as the cells of `α`-target classes have unique maxima
            if hd.holds(Criterion::Cell) {
                assert_eq!(hd.d_equals_hd(), Some(true), "seed {seed}");
            }
            if hd.holds(Criterion::AlphaTargetCell) {
                assert!(
                    hd.cyclic.verified().is_some(),
                    "seed {seed}: {:?}",
                    hd.cyclic
                );
            }
            assert!(
                !matches!(
                    hd.cyclic,
                    CyclicPruning::NotSaturated { .. } | CyclicPruning::NotEquivalent(_)
                ),
                "seed {seed}"
            );
            if hd.only_sufficient().contains(&Criterion::AlphaTargetCell) {
                only_sufficient += 1;
            }
        }
        assert!(only_sufficient > 0);
    }

    #[test]
    fn random_is_reproducible() {
        let draw = |seed| {
            LayeredNcw::random(
                LayeredParameters::default(),
                &mut StdRng::seed_from_u64(seed),
            )
            .unwrap()
        };
        assert_eq!(draw(3), draw(3));
    }
}
