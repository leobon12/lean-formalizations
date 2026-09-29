import ReflectedWalk.Step1
import ReflectedWalk.HoldingDivergence

/-!
# Theorem 1.6, closed (Gwynne–Sung, arXiv:2506.18827, p. 5)

This file discharges the last hypothesis of `theorem16` and states Theorem 1.6 with no
hypotheses beyond the data `G` and the energy minimizer bundle.

The chain is:

* `HoldingDivergence.ae_tsum_stepHolding_eq_top` — for an arbitrary reflected walk, the
  embedded holding times at every level sum to `∞` almost surely (property (v) plus the
  embedded pair law, through Borel–Cantelli);
* `Step1.step1` — hence Step 1 of §3.4: a single transition function `q` approximating
  every reflected walk at fixed times;
* `Theorem16.uniqueness_half` and `Existence.existence_half` — the two halves;
* `theorem16` — the assembly.

**Scope.** `IsReflectedWalk` carries the `∞`-side of property (ii)
(`Theorem16.RightContinuousAtInfty`), a user-approved completion of the printed statement.
It is *necessary*: `Lemma311.not_hR` proves the printed property list (i)–(vi) admits
single-time kills, for which right continuity at `∞` fails, and the paper's own Lemma 3.11
and uniqueness Step 1 both require it. See `STATEMENT_SPEC.md`.
-/

namespace ReflectedWalk

variable {V : Type*}

/-- **Theorem 1.6** (Gwynne–Sung, p. 5), with no remaining hypotheses.

For a countably infinite connected conductance graph `G` with `π(x) < ∞` there is a rate
function `w* : VG → (0,∞)` such that for every `w : VG → (0,∞)` with `w ≥ w*` and every
starting point `z`, there is a process `X : [0,∞) → VG ∪ {∞}` with `X₀ = z` satisfying
properties (i)–(vi) — with (ii) read in the compactified state space — and it is unique in
law among such processes. -/
theorem theorem16_closed (G : ConductanceGraph V) (hmin : G.EnergyMinimizer) :
    Theorem16Statement G hmin := by
  refine theorem16_of_holdingTimesDiverge G hmin ?_
  intro hV hinf hG E w hw 𝓨 h𝓨 x n
  let _ : MeasurableSpace V := ⊤
  have _ : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  have : Countable V := hV
  exact Theorem16.ae_tsum_stepHolding_eq_top h𝓨 hG hw (fun v => (h𝓨 v).2.2.2.1) E x n

end ReflectedWalk
