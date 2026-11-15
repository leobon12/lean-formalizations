/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRDeltaConst
import InteractingSLE.Spec.Supplement.R6RefPhase

/-!
# GW4: local reflected transition logarithms give the RepD phase property

Local witnesses suffice; no globally selected logarithm or common chart
across all times is required. Positive reflection gives quantization, and
local agreement with a continuous inherited logarithm gives continuity.
The actual source construction of these witnesses remains explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PhaseSel

/-- **Open geometric branch input.** Near each live positive time the phase
agrees with the inherited argument of a continuous transition logarithm.
At that time it exponentiates to the derivative of a positively reflected
real-boundary conformal map. Neither lattice values nor time constancy are
fields of this predicate. -/
def HasLocalReflectedPhase (k : ℝ) (V : ℝ≥0∞) (d : ℝ≥0 → ℝ) : Prop :=
  ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V → ∃ L : ℝ≥0 → ℂ,
    ContinuousWithinAt L {p : ℝ≥0 | 0 < p ∧ (p : ℝ≥0∞) < V} q ∧
    (d =ᶠ[𝓝[{p : ℝ≥0 | 0 < p ∧ (p : ℝ≥0∞) < V}] q] fun p => chiC k * (L p).im) ∧
    ∃ (φ : ℂ → ℂ) (x r : ℝ), 0 < r ∧ R16.IsRealBoundaryConformal φ x r ∧
      Complex.exp (L q) = deriv (QuantumZipper.CA.schwarzReflect φ) x

/-- Local reflected logarithms prove continuity of the actual phase on its
positive lifetime, without choosing compatible logarithms between patches. -/
theorem HasLocalReflectedPhase.continuousOn {k : ℝ} {V : ℝ≥0∞} {d : ℝ≥0 → ℝ}
    (h : HasLocalReflectedPhase k V d) :
    ContinuousOn d {q : ℝ≥0 | 0 < q ∧ (q : ℝ≥0∞) < V} := by
  intro q hq
  obtain ⟨L, hL, heq, -⟩ := h q hq.1 hq.2
  have hc : ContinuousWithinAt (fun p => chiC k * (L p).im)
      {p : ℝ≥0 | 0 < p ∧ (p : ℝ≥0∞) < V} q :=
    (Complex.continuous_im.continuousAt.comp_continuousWithinAt hL).const_mul (chiC k)
  exact hc.congr_of_eventuallyEq_of_mem heq hq

/-- Positive reflection proves the exact project lattice. Its `phaseStep`
uses `-chiC`, so the integer is the negative of the logarithm's winding integer. -/
theorem HasLocalReflectedPhase.lattice {k : ℝ} {V : ℝ≥0∞} {d : ℝ≥0 → ℝ}
    (h : HasLocalReflectedPhase k V d) {q : ℝ≥0} (hq : 0 < q)
    (hqV : (q : ℝ≥0∞) < V) : ∃ j : ℤ, d q = j * phaseStep k := by
  obtain ⟨L, -, heq, φ, x, r, hr, hφ, hexp⟩ := h q hq hqV
  have hpos := hφ.deriv_schwarzReflect_pos (mem_ball_self hr)
  have hre : 0 < (Complex.exp (L q)).re := by rw [hexp]; exact hpos.2
  have him : (Complex.exp (L q)).im = 0 := by rw [hexp]; exact hpos.1
  obtain ⟨j, hj⟩ := R16.exists_int_im_eq_of_exp_pos hre him
  refine ⟨-j, ?_⟩
  rw [heq.eq_of_nhdsWithin ⟨hq, hqV⟩, hj, phaseStep, Int.cast_neg]
  ring

/-- The exact simultaneous phase clause consumed by MART's RepD follows
from the local reflected branch construction. Empty positive lifetimes and
the arbitrary phase value at zero are included. -/
theorem ae_exists_lattice_const_of_localReflectedPhase {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {k : ℝ} (hk : 4 < k) {V : Ω → ℝ≥0∞} {d : ℝ≥0 → Ω → ℝ}
    (h : ∀ᵐ ω ∂ν, HasLocalReflectedPhase k (V ω) (d · ω)) :
    ∀ᵐ ω ∂ν, ∃ c : ℝ, (∃ j : ℤ, c = j * phaseStep k) ∧
      ∀ q : ℝ≥0, 0 < q → (q : ℝ≥0∞) < V ω → d q ω = c := by
  apply ae_exists_lattice_const_of_continuousOn (phaseStep_ne_zero hk)
    (h.mono fun _ hω => hω.continuousOn)
  intro q hq
  exact h.mono fun _ hω hqV => hω.lattice hq hqV

end InteractingSLE.Theorem14.GW4Fix
