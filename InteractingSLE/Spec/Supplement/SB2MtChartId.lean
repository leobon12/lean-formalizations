/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MoPhys
import InteractingSLE.Spec.Supplement.WalkIntCanonRun

/-!
# The relative run chart in physical coordinates is the canonical hull chart up to a translation

Packet PROVE-SB2-LCMEAN, round 12 (identification step of the kernel half). `Mq.StageChainAtP` says that at a launched
relative stage of positive lifetime `Mo.physRelChart c c₁ m` is a domain chart of `ℍ ∖ fill X` (`X` the retained
union). The upper chart `c` and the relative run chart `c₁` are run charts, normalized when their launched pieces are
regular (`WalkIntCanon.isNormalized_runChart`; LIFTSET's bundle carries this for `EL` as `RegLaunches`). Normalized
charts have inverses within bounded distance of the identity, so the physical relative chart is the canonical hull
chart of `fill X` up to a real translation:

* **`exists_hullChart_eq_physRelChart`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mt

/-- **The physical relative chart of normalized run charts is a canonical hull chart up to a real translation**: if
`Mo.physRelChart c c₁ m` is a domain chart of `ℍ ∖ X` for a compact `ℍ`-hull `X` and `c`, `c₁` are normalized, then
it agrees on `ℍ ∖ X` with `Mo.hullChart X x₀` for some real `x₀`. -/
theorem exists_hullChart_eq_physRelChart {X : Set ℂ} (hX : IsHPHull X) {c c₁ : Chart}
    (hcN : WalkIntCanon.IsNormalized c) (hc₁N : WalkIntCanon.IsNormalized c₁) (m : ℝ)
    (hD : IsDomainChart (H \ X) (Mo.physRelChart c c₁ m)) :
    ∃ x₀ : ℝ, ∀ z ∈ H \ X, (Mo.physRelChart c c₁ m).1 z = (Mo.hullChart X x₀).1 z := by
  obtain ⟨M, hM⟩ := hcN.inverse_bound
  obtain ⟨M₁, hM₁⟩ := hc₁N.inverse_bound
  exact Mo.exists_hullChart_translate hX hD (Mo.physRelChart_inv_bounded hc₁N.conformal hM hM₁ m)

end InteractingSLE.Theorem14.SB.Mt
