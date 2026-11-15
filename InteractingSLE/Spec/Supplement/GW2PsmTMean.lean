/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmConv

/-!
# GW2's open lines: the typed data of a raised word extend to the word's mean

Packet PROVE-GW2-STAGEMEAN, R121 round (Claim(k) step, word side at the current record). **`eqOn_typed_upW_mean`**:
every bounded harmonic extension of the typed force data of `upW k c` at its own word type is `c`'s mean plus `k` on
`ℍ` (the typed data are the angle-`0` flow-line data of `upW k c`, whose force data are `c.fn + k` off finitely many
points).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist.StagedLaw Supp8.Q3Stop

/-- **The typed data of a raised word extend to the word's mean raised.** -/
theorem eqOn_typed_upW_mean {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (hc : c.IsSorted) (k : ℝ) {w : WordType}
    (hw : wordType κ (GW2Rd.upW k c) = w) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (typedRhoL w) (typedRhoR w) (typedXL κ w (GW2Rd.upW k c)) (typedXR κ w (GW2Rd.upW k c)))
      (forceJumpSet (typedXL κ w (GW2Rd.upW k c)) (typedXR κ w (GW2Rd.upW k c))) u) :
    ∀ z ∈ H, u z = c.mean z + k := by
  have hft := isFlowType_typed hw
  have hS : ({0} ∪ ((GW2Rd.upW k c).jumps : Set ℝ)).Finite :=
    (finite_singleton 0).union (GW2Rd.upW k c).jumps.finite_toSet
  refine RetAux79.eqOn_mean_add_of_forceBoundaryData hu hc k hS fun y hy => ?_
  have h0 : y ≠ 0 := fun h => hy (Or.inl h)
  have hJ : y ∉ (GW2Rd.upW k c).jumps := fun h => hy (Or.inr h)
  rw [RetAux79.forceBoundaryData_zero_of_isFlowType hft,
    Sec4.forceBoundaryData_flowLine hκ (GW2Rd.upW k c).isPiecewiseConstantBoundaryData h0 hJ]
  rfl

end InteractingSLE.Theorem14.GW2Psm
