/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MtChartId
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun

/-!
# The relative run chart in physical coordinates is the canonical hull chart, lift included

Packet PROVE-SB2-LCMEAN, round 12 (identification step of the kernel half). `Mt.exists_hullChart_eq_physRelChart`
identifies the forward maps of the physical relative chart `Φ = Mo.physRelChart c c₁ m` and of a canonical hull chart
`Mo.hullChart X x₀` on `ℍ ∖ X`. Chart transports read the lift too, so the lifts must agree as well. Both are continuous
arguments of the same derivative; the normalization at `i∞` fixes the integer between them:

* `isMapOut_congr`: a map-out is determined by its values off the hull;
* **`isNormalized_physRelChart`**: `Φ` is normalized when `c`, `c₁` are and `Φ` is a domain chart (the derivative lift
  comes with the domain chart; the lift limit at `i∞` is the sum of those of `c₁` and `c`);
* **`physRelChart_eq_hullChart`**: `Φ` and `Mo.hullChart X x₀` agree on `ℍ ∖ X`, forward map and lift
  (`WalkIntCanon.HullModel.lift_eq_canonDerivLog`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mt

open WalkIntCanon

/-- **A map-out is determined by its values off the hull.** -/
theorem isMapOut_congr {A : Set ℂ} {g g' : ℂ → ℂ} (hg : IsMapOut A g) (he : EqOn g' g (H \ A)) :
    IsMapOut A g' := by
  refine ⟨⟨hg.1.1.congr he, hg.1.2.congr he.symm⟩, ?_⟩
  refine hg.2.congr' ?_
  exact eventually_inf_principal.2 (Eventually.of_forall fun z hz => by simp only [he hz])

/-- **The physical relative chart of normalized run charts is normalized** when it is a domain chart. -/
theorem isNormalized_physRelChart {X : Set ℂ} {c c₁ : Chart} (hcN : IsNormalized c) (hc₁N : IsNormalized c₁)
    (m : ℝ) (hD : IsDomainChart (H \ X) (Mo.physRelChart c c₁ m)) : IsNormalized (Mo.physRelChart c c₁ m) := by
  obtain ⟨M, hM⟩ := hcN.inverse_bound
  obtain ⟨M₁, hM₁⟩ := hc₁N.inverse_bound
  have hdom : ((Mo.physRelChart c c₁ m).dom : Set ℂ) = H \ X := by rw [hD.1.coe_dom, hD.2.1]
  obtain ⟨L, hL, hlift⟩ := hD.2.2
  refine ⟨hD.1, ⟨L, by rw [hdom]; exact hL, fun z hz => hlift (hdom ▸ hz)⟩,
    ⟨M + M₁ + |m|, Mo.physRelChart_inv_bounded hc₁N.conformal hM hM₁ m⟩, ?_⟩
  have hmapsH : MapsTo (fun y => c₁.2.1 y - (m : ℂ)) H H := fun y hy =>
    Mo.sub_ofReal_mem_H (hc₁N.conformal.2.1 hy) m
  have hbd : ∀ y ∈ H, ‖(fun y => c₁.2.1 y - (m : ℂ)) y - y‖ ≤ M₁ + |m| := by
    intro y hy
    have e : c₁.2.1 y - (m : ℂ) - y = (c₁.2.1 y - y) - (m : ℂ) := by ring
    calc ‖c₁.2.1 y - (m : ℂ) - y‖ = ‖(c₁.2.1 y - y) - (m : ℂ)‖ := by rw [e]
      _ ≤ ‖c₁.2.1 y - y‖ + ‖((m : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ M₁ + |m| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          linarith [hM₁ y hy]
  have hhigh := tendsto_highHalfPlane_of_bound hmapsH hbd
  have hsum := hc₁N.lift_limit.add (hcN.lift_limit.comp hhigh)
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_mem_highHalfPlane] with y hy
  show c₁.2.2 (c₁.2.1 y) + c.2.2 (c.2.1 (c₁.2.1 y - (m : ℂ))) =
    c₁.2.2 (c.1 (c.2.1 (c₁.2.1 y - (m : ℂ))) + (m : ℂ)) + c.2.2 (c.2.1 (c₁.2.1 y - (m : ℂ)))
  rw [hcN.conformal.2.2 _ (hmapsH hy), sub_add_cancel]

/-- **The physical relative chart of normalized run charts is a canonical hull chart**: if it is a domain chart of
`ℍ ∖ X` for a compact `ℍ`-hull `X`, it agrees on `ℍ ∖ X` with `Mo.hullChart X x₀` for some real `x₀`, both in the
forward map and in the lift. -/
theorem physRelChart_eq_hullChart {X : Set ℂ} (hX : IsHPHull X) {c c₁ : Chart} (hcN : IsNormalized c)
    (hc₁N : IsNormalized c₁) (m : ℝ) (hD : IsDomainChart (H \ X) (Mo.physRelChart c c₁ m)) :
    ∃ x₀ : ℝ, EqOn (Mo.physRelChart c c₁ m).1 (Mo.hullChart X x₀).1 (H \ X) ∧
      EqOn (Mo.physRelChart c c₁ m).2.2 (Mo.hullChart X x₀).2.2 (H \ X) := by
  obtain ⟨x₀, hx₀⟩ := exists_hullChart_eq_physRelChart hX hcN hc₁N m hD
  have hdom : ((Mo.physRelChart c c₁ m).dom : Set ℂ) = H \ X := by rw [hD.1.coe_dom, hD.2.1]
  have hmo : IsMapOut X (fun z => (Mo.physRelChart c c₁ m).1 z + (x₀ : ℂ)) := by
    refine isMapOut_congr (ConformalImage.isMapOut_mapOut hX) fun z hz => ?_
    show (Mo.physRelChart c c₁ m).1 z + (x₀ : ℂ) = ConformalImage.mapOut X z
    rw [hx₀ z hz, Mo.hullChart_fwd, sub_add_cancel]
  let Mod : HullModel (Mo.physRelChart c c₁ m) := ⟨X, x₀, hX, hdom, hmo⟩
  have hl := Mod.lift_eq_canonDerivLog (isNormalized_physRelChart hcN hc₁N m hD)
  refine ⟨x₀, hx₀, fun z hz => ?_⟩
  rw [hl hz, Mo.hullChart_lift]

end InteractingSLE.Theorem14.SB.Mt
