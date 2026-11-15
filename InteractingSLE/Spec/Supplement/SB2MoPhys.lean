/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MoNorm
import InteractingSLE.Spec.Supplement.SB2MnIface
import InteractingSLE.Spec.Supplement.SB4RTrStaged
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart

/-!
# The relative chart in physical coordinates

Packet PROVE-SB2-LCMEAN, round 11 (item F2). `EL`'s stage-`j` chart acts on the relative field `affField m h'`, i.e. on
the field read in the upper launch chart `c` and shifted by `m`. Read on the physical field `h`, it is the composite
`physRelChart c c₁ m`: the upper chart, the shift, then the relative run chart `c₁`. This file proves its chart facts
and its relation with R116's stage-coordinate chart `Mn.stageRelChart`:

* `physRelChart`, **`isConformal_physRelChart`** (conformal whenever the two charts are),
  **`physRelChart_inv_bounded`** (inverse within bounded distance of the identity when both inverses are);
* `stageRelChart_inv`, `physRelChart_inv_eq_of_mem_dom`: the stage-coordinate chart is the physical one read through
  B's stage chart;
* **`exists_hullChart_translate`**: a domain chart of `ℍ \ A` (`A` a compact `ℍ`-hull) whose inverse stays within
  bounded distance of the identity is, on `ℍ \ A`, the canonical hull chart up to a real shift of the forward map;
* `physRelChart_eq_trans`, **`isChartTransport_physRelChart`**: reading the field in the upper chart, shifting by `m`
  (`affField m`) and reading the result in the relative run chart is reading the physical field in `physRelChart`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mo

/-- **The relative chart in physical coordinates**: the upper chart `c`, the shift by `m`, then the relative run chart
`c₁` (the lift is the chain-rule sum). -/
def physRelChart (c c₁ : Chart) (m : ℝ) : Chart :=
  (fun z => c₁.1 (c.1 z + (m : ℂ)), fun y => c.2.1 (c₁.2.1 y - (m : ℂ)),
    fun z => c₁.2.2 (c.1 z + (m : ℂ)) + c.2.2 z)

@[simp] theorem physRelChart_fwd (c c₁ : Chart) (m : ℝ) (z : ℂ) :
    (physRelChart c c₁ m).1 z = c₁.1 (c.1 z + (m : ℂ)) := rfl

@[simp] theorem physRelChart_inv (c c₁ : Chart) (m : ℝ) (y : ℂ) :
    (physRelChart c c₁ m).2.1 y = c.2.1 (c₁.2.1 y - (m : ℂ)) := rfl

/-- **The physical relative chart is conformal** whenever the upper and relative charts are. -/
theorem isConformal_physRelChart {c c₁ : Chart} (hc : c.IsConformal) (hc₁ : c₁.IsConformal) (m : ℝ) :
    (physRelChart c c₁ m).IsConformal := by
  refine ⟨?_, fun y hy => ?_, fun y hy => ?_⟩
  · exact hc.1.comp (hc₁.1.sub_const (m : ℂ)) fun y hy => sub_ofReal_mem_H (hc₁.2.1 hy) m
  · exact hc.2.1 (sub_ofReal_mem_H (hc₁.2.1 hy) m)
  · show c₁.1 (c.1 (c.2.1 (c₁.2.1 y - (m : ℂ))) + (m : ℂ)) = y
    rw [hc.2.2 _ (sub_ofReal_mem_H (hc₁.2.1 hy) m), sub_add_cancel, hc₁.2.2 y hy]

/-- **The physical relative chart's inverse stays within bounded distance of the identity** when the inverses of the
upper and relative charts do. -/
theorem physRelChart_inv_bounded {c c₁ : Chart} (hc₁ : c₁.IsConformal) {M M₁ : ℝ}
    (hb : ∀ y ∈ H, ‖c.2.1 y - y‖ ≤ M) (hb₁ : ∀ y ∈ H, ‖c₁.2.1 y - y‖ ≤ M₁) (m : ℝ) :
    ∀ y ∈ H, ‖(physRelChart c c₁ m).2.1 y - y‖ ≤ M + M₁ + |m| := by
  intro y hy
  have hw := sub_ofReal_mem_H (hc₁.2.1 hy) m
  have e : (physRelChart c c₁ m).2.1 y - y =
      (c.2.1 (c₁.2.1 y - (m : ℂ)) - (c₁.2.1 y - (m : ℂ))) + (c₁.2.1 y - y) - (m : ℂ) := by
    simp only [physRelChart_inv]
    ring
  rw [e]
  calc _ ≤ ‖(c.2.1 (c₁.2.1 y - (m : ℂ)) - (c₁.2.1 y - (m : ℂ))) + (c₁.2.1 y - y)‖ + ‖((m : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ (‖c.2.1 (c₁.2.1 y - (m : ℂ)) - (c₁.2.1 y - (m : ℂ))‖ + ‖c₁.2.1 y - y‖) + ‖((m : ℝ) : ℂ)‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ M + M₁ + |m| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith [hb _ hw, hb₁ y hy]

/-- The stage-coordinate relative chart's inverse is B's stage chart applied to the physical one. -/
theorem stageRelChart_inv (cℓ c c₁ : Chart) (m : ℝ) (y : ℂ) :
    (Mn.stageRelChart cℓ c c₁ m).2.1 y = cℓ.1 ((physRelChart c c₁ m).2.1 y) := rfl

/-- Where the physical inverse lands in B's stage-chart domain, it is B's inverse stage chart applied to the
stage-coordinate one. -/
theorem physRelChart_inv_eq_of_mem_dom {cℓ c c₁ : Chart} (hcℓ : cℓ.IsConformal) (m : ℝ) {y : ℂ}
    (hy : (physRelChart c c₁ m).2.1 y ∈ (cℓ.dom : Set ℂ)) :
    (physRelChart c c₁ m).2.1 y = cℓ.2.1 ((Mn.stageRelChart cℓ c c₁ m).2.1 y) := by
  rw [stageRelChart_inv, hcℓ.inv_fwd hy]

/-- **A normalized domain chart of a hull complement is the canonical hull chart up to a real shift.** -/
theorem exists_hullChart_translate {A : Set ℂ} (hA : IsHPHull A) {c : Chart} (hc : IsDomainChart (H \ A) c)
    {M : ℝ} (hb : ∀ y ∈ H, ‖c.2.1 y - y‖ ≤ M) :
    ∃ x₀ : ℝ, ∀ z ∈ H \ A, c.1 z = (hullChart A x₀).1 z := by
  obtain ⟨M₀, hM₀⟩ := hullChart_inv_bounded hA 0
  obtain ⟨t, ht⟩ := exists_translate_of_isDomainChart (isDomainChart_hullChart hA 0) hc hM₀ hb
  refine ⟨-t, fun z hz => ?_⟩
  rw [ht z hz]
  simp only [hullChart_fwd, ofReal_zero, sub_zero, ofReal_neg, sub_neg_eq_add]

theorem physRelChart_eq_trans (c c₁ : Chart) (m : ℝ) : physRelChart c c₁ m = c.trans (Lf.trChart m c₁) := rfl

/-- A translated chart of a conformal chart is conformal. -/
theorem isConformal_trChart {c₁ : Chart} (hc₁ : c₁.IsConformal) (m : ℝ) : (Lf.trChart m c₁).IsConformal := by
  refine ⟨hc₁.1.sub_const (m : ℂ), fun w hw => sub_ofReal_mem_H (hc₁.2.1 hw) m, fun w hw => ?_⟩
  show c₁.1 (c₁.2.1 w - (m : ℂ) + (m : ℂ)) = w
  rw [sub_add_cancel, hc₁.2.2 w hw]

/-- **Chart transport through the physical relative chart**: the field read in the upper chart `c`, shifted by `m`
(`affField m`) and read in the relative run chart `c₁`, is the physical field read in `physRelChart c c₁ m`. -/
theorem isChartTransport_physRelChart {c c₁ : Chart} (hc : c.IsConformal) (hc₁ : c₁.IsConformal)
    (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) (hℓ₁ : ContinuousOn (fun w => c₁.2.2 (c₁.2.1 w)) H)
    {χ m : ℝ} {h h' h'' : LQGMetric.DistOn upperHalfPlaneOpens} (ht : IsChartTransport c 1 0 χ h h')
    (ht₁ : IsChartTransport c₁ 1 0 χ (FlowDilate.affField m one_pos h') h'') :
    IsChartTransport (physRelChart c c₁ m) 1 0 χ h h'' := by
  have h1 := Lf.isChartTransport_trChart ht₁ m
  have e : FlowDilate.affField (-m) one_pos (FlowDilate.affField m one_pos h') = h' := by
    have := FlowDilate.affField_inv_affField (m := m) (one_pos : (0 : ℝ) < 1) h'
    simpa using this
  rw [e] at h1
  have hconf : (Lf.trChart m c₁).IsConformal := isConformal_trChart hc₁ m
  have hℓtr : ContinuousOn (fun w => (Lf.trChart m c₁).2.2 ((Lf.trChart m c₁).2.1 w)) H := by
    refine hℓ₁.congr fun w _ => ?_
    show c₁.2.2 (c₁.2.1 w - (m : ℂ) + (m : ℂ)) = c₁.2.2 (c₁.2.1 w)
    rw [sub_add_cancel]
  have h1' : IsChartTransport (Lf.trChart m c₁) 1 0 (1 * χ) h' h'' := by rw [one_mul]; exact h1
  have h2 := GW2JointKernel.isChartTransport_trans_sign (σ₂ := 1) (a₂ := 0) hc hconf hℓ hℓtr ht h1'
  rw [physRelChart_eq_trans]
  simpa using h2

end InteractingSLE.Theorem14.SB.Mo
