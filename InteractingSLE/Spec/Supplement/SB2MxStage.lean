/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MxCanon
import InteractingSLE.Spec.Supplement.SB2MtLift
import InteractingSLE.Spec.Supplement.SB4RChart

/-!
# The canonical chart in B's stage coordinates

Packet PROVE-SB2-LCMEAN, round 14 (item 4: identification with `EL`). SB2LIFT's chain for `EL`'s stage
(`Mn.StageChainAtR2`) lives in B's stage coordinates, in the chart `Mn.stageRelChart cℓ c c₁ m`. That chart is the
physical relative chart `Mo.physRelChart c c₁ m` read through B's stage chart `cℓ` (`stageRelChart_eq_stageChartOf`).
The canonical chart `Φ` of the matched stage, read the same way (`stageChartOf cℓ Φ`), is then a domain chart of the
same domain and differs from it by a real translation. Here `Φ` is the hull chart of the retained fill with the
canonical offset, and the physical relative chart is that hull chart with another offset
(`Mt.physRelChart_eq_hullChart`).
These are the chart inputs of `Mx.eqOn_of_chains`:

* `stageChartOf`, `stageRelChart_eq_stageChartOf`;
* `isDomainChart_congr`, **`isDomainChart_of_translate`**;
* **`stageChartOf_translate`**: from charts `Φ`, `Ψ` of `ℍ ∖ X` with `Φ = Ψ + d` there, the stage charts are domain
  charts of `ℍ ∖ stageRetained cℓ X` (given the one of `Ψ`) and differ by `d`;
* `mem_diff_of_notMem_stageRetained`: B's inverse stage chart maps the complement of the stage-coordinate retained
  set into the complement of the retained fill;
* **`hullChart_eq_add_of_physRelChart`**: the canonical hull chart is the physical relative chart plus a real constant
  on the retained complement (forward map), with the same lift.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mx

/-- **A chart read in B's stage coordinates** through B's stage chart `cℓ` (as `Mn.stageRelChart`). -/
def stageChartOf (cℓ Φ : Chart) : Chart :=
  (fun w => Φ.1 (cℓ.2.1 w), fun y => cℓ.1 (Φ.2.1 y), fun w => Φ.2.2 (cℓ.2.1 w) - cℓ.2.2 (cℓ.2.1 w))

/-- SB2LIFT's stage-coordinate relative chart is the physical relative chart read in B's stage coordinates. -/
theorem stageRelChart_eq_stageChartOf (cℓ c c₁ : Chart) (m : ℝ) :
    Mn.stageRelChart cℓ c c₁ m = stageChartOf cℓ (Mo.physRelChart c c₁ m) := rfl

/-- **A domain chart only matters on its domain** (forward map and lift) and on `ℍ` (inverse). -/
theorem isDomainChart_congr {D : Set ℂ} {c c' : Chart} (hc : IsDomainChart D c) (h1 : EqOn c'.1 c.1 D)
    (h2 : EqOn c'.2.1 c.2.1 H) (h3 : EqOn c'.2.2 c.2.2 D) : IsDomainChart D c' := by
  obtain ⟨⟨hdiff, hmaps, hinv⟩, himg, L, ⟨hLd, hLe⟩, hlift⟩ := hc
  have hDo : IsOpen D := IsDomainChart.isOpen ⟨⟨hdiff, hmaps, hinv⟩, himg, L, ⟨hLd, hLe⟩, hlift⟩
  have hmem : ∀ w ∈ H, c.2.1 w ∈ D := fun w hw => himg ▸ mem_image_of_mem _ hw
  refine ⟨⟨hdiff.congr fun w hw => h2 hw, fun w hw => (h2 hw).symm ▸ hmaps hw, fun w hw => ?_⟩, ?_, L,
    ⟨hLd, fun z hz => ?_⟩, fun z hz => (h3 hz).trans (hlift hz)⟩
  · rw [h2 hw, h1 (hmem w hw), hinv w hw]
  · rw [image_congr fun w hw => h2 hw, himg]
  · have hev : c'.1 =ᶠ[𝓝 z] c.1 := Filter.eventuallyEq_of_mem (hDo.mem_nhds hz) h1
    rw [hev.deriv_eq]
    exact hLe z hz

/-- **A translate of a domain chart is a domain chart of the same domain.** -/
theorem isDomainChart_of_translate {D : Set ℂ} {cR cC : Chart} (hR : IsDomainChart D cR) {d : ℝ}
    (h1 : ∀ z ∈ D, cC.1 z = cR.1 z + d) (h2 : ∀ y ∈ H, cC.2.1 y = cR.2.1 (y - d))
    (h3 : EqOn cC.2.2 cR.2.2 D) : IsDomainChart D cC := by
  refine isDomainChart_congr (Lf.isDomainChart_recenter hR (-d)) (fun z hz => ?_) (fun y hy => ?_) h3
  · show cC.1 z = cR.1 z - ((-d : ℝ) : ℂ)
    rw [h1 z hz, Complex.ofReal_neg, sub_neg_eq_add]
  · show cC.2.1 y = cR.2.1 (y + ((-d : ℝ) : ℂ))
    rw [h2 y hy, Complex.ofReal_neg, ← sub_eq_add_neg]

/-- **The canonical chart and the physical relative chart read in B's stage coordinates**: if `Φ = Ψ + d` on
`ℍ ∖ X` (both domain charts there, same lift) and `cℓ⁻¹` maps the complement of the stage-coordinate retained set into
`ℍ ∖ X`, the stage charts differ by `d` and the canonical one is a domain chart whenever the other is. -/
theorem stageChartOf_translate {cℓ Φ Ψ : Chart} {X A' : Set ℂ} (hΦ : IsDomainChart (H \ X) Φ)
    (hΨ : IsDomainChart (H \ X) Ψ) {d : ℝ} (hfwd : ∀ z ∈ H \ X, Φ.1 z = Ψ.1 z + d)
    (hlift : EqOn Φ.2.2 Ψ.2.2 (H \ X)) (hcℓ : ∀ w ∈ H \ A', cℓ.2.1 w ∈ H \ X)
    (hS : IsDomainChart (H \ A') (stageChartOf cℓ Ψ)) :
    IsDomainChart (H \ A') (stageChartOf cℓ Φ) ∧
      ∀ w ∈ H \ A', (stageChartOf cℓ Φ).1 w = (stageChartOf cℓ Ψ).1 w + d := by
  have hinv : ∀ y ∈ H, Φ.2.1 y = Ψ.2.1 (y - d) := by
    intro y hy
    have hm := hΦ.inv_mem hy
    have e : Ψ.1 (Φ.2.1 y) = y - d := by
      have h := hfwd _ hm
      rw [hΦ.fwd_inv hy] at h
      rw [eq_sub_iff_add_eq]
      exact h.symm
    rw [← e, hΨ.inv_fwd hm]
  have h1 : ∀ w ∈ H \ A', (stageChartOf cℓ Φ).1 w = (stageChartOf cℓ Ψ).1 w + d := fun w hw =>
    hfwd _ (hcℓ w hw)
  refine ⟨isDomainChart_of_translate hS h1 (fun y hy => ?_) (fun w hw => ?_), h1⟩
  · show cℓ.1 (Φ.2.1 y) = cℓ.1 (Ψ.2.1 (y - d))
    rw [hinv y hy]
  · show Φ.2.2 (cℓ.2.1 w) - cℓ.2.2 (cℓ.2.1 w) = Ψ.2.2 (cℓ.2.1 w) - cℓ.2.2 (cℓ.2.1 w)
    rw [hlift (hcℓ w hw)]

/-- **The canonical hull chart is the physical relative chart plus a real constant** on the retained complement, with
the same lift (`Mt.physRelChart_eq_hullChart`). -/
theorem hullChart_eq_add_of_physRelChart {X : Set ℂ} (hX : IsHPHull X) {c c₁ : Chart}
    (hcN : WalkIntCanon.IsNormalized c) (hc₁N : WalkIntCanon.IsNormalized c₁) (m : ℝ)
    (hD : IsDomainChart (H \ X) (Mo.physRelChart c c₁ m)) (x₀ : ℝ) :
    ∃ d : ℝ, (∀ z ∈ H \ X, (Mo.hullChart X x₀).1 z = (Mo.physRelChart c c₁ m).1 z + d) ∧
      EqOn (Mo.hullChart X x₀).2.2 (Mo.physRelChart c c₁ m).2.2 (H \ X) := by
  obtain ⟨x₀', hf, hl⟩ := Mt.physRelChart_eq_hullChart hX hcN hc₁N m hD
  refine ⟨x₀' - x₀, fun z hz => ?_, fun z hz => ?_⟩
  · rw [hf hz, Mo.hullChart_fwd, Mo.hullChart_fwd]
    push_cast
    ring
  · rw [hl hz, Mo.hullChart_lift, Mo.hullChart_lift]

/-- B's inverse stage chart maps the complement of the stage-coordinate retained set into the complement of the
retained fill. -/
theorem mem_diff_of_notMem_stageRetained {cℓ : Chart} (hcℓ : cℓ.IsConformal) {X : Set ℂ} {w : ℂ}
    (hw : w ∈ H \ Mn.stageRetained cℓ X) : cℓ.2.1 w ∈ H \ fillH X :=
  ⟨hcℓ.2.1 hw.1, fun h => hw.2 ⟨hw.1, h⟩⟩

end InteractingSLE.Theorem14.SB.Mx
