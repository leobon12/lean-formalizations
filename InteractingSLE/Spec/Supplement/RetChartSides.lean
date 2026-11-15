/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetChartAsm

/-!
# The individual chart boundary functions at a touching pair: `RetTouchSidesStatement` PROVED

Packet PROVE-T15-RET5 (Aux. lemma 85's sides read in the individual charts). The touching analogue of
`Sec7.Lemma76G.IsSetting.side₁`/`side₂`, from the outer boundary (OF2) of the touching zone data:

* right of the junction `J = R₂`, the retained chart inverse `ψ` lands on the first prefix (on `(J, R₁]`) or on a real
  point (right of `R₁`), never in the first path's own domain `ℍ ∖ fill(α[0,a])` (`notMem_U₁`); left of `J`, it lands
  on the second prefix or on a real point (`notMem_U₂`);
* hence the composite of the individual chart with `ψ` has real limits there (`exists_real_tendsto_comp`), strictly
  increasing (`strictMonoOn_Ioi_of_tendsto_comp`, `…Iio…`);
* at the tips: `ψ(M₁) = α(a)` and `ψ(0) = β(b)`, both interior (ordinary pair), so the individual chart value is the
  unique preimage `0` of the tip (`IsPhysChart.tip_fibre`) — at an ordinary pair the first tip is interior, so the
  disjoint case's trapping argument for the first tip is not needed.

Main result: **`retTouchSidesStatement : RetTouchSidesStatement`**. Deterministic.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace RetChart

open Restart Supp7 Sec7 Sec7.Lemma76G Sec7.SideHeightBox RetTouch

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {z : ZW}

/-- Right of the junction, the chart inverse avoids the first path's own domain. -/
theorem notMem_U₁ (ht : IsTouchZones α a β b ψ z) {w : ℝ} (hw : z.R₂ < w) :
    ψ w ∉ H \ fillH (α '' Icc 0 a) := by
  have hz := ht.good
  have hα : ∀ p ∈ α '' Icc 0 a, p ∉ H \ fillH (α '' Icc 0 a) := fun p hp h =>
    h.2 (mem_fillH_of_mem_closure h.1 (subset_closure hp))
  rcases lt_trichotomy w z.M₁ with h | rfl | h
  · exact hα _ (ht.side₃ w (ht.junction ▸ hw) h).1
  · rw [ht.tip₁]; exact hα _ ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩
  · rcases lt_trichotomy w z.R₁ with h' | rfl | h'
    · exact hα _ (ht.side₄ w h h')
    · exact hα _ ht.R₁_mem
    · intro hU
      exact (ne_of_gt (show (0 : ℝ) < (ψ w).im from hU.1)) (ht.zone₂ w h').1

/-- Left of the junction, the chart inverse avoids the second path's own domain. -/
theorem notMem_U₂ (ht : IsTouchZones α a β b ψ z) {w : ℝ} (hw : w < z.R₂) :
    ψ w ∉ H \ fillH (β '' Icc 0 b) := by
  have hβ : ∀ p ∈ β '' Icc 0 b, p ∉ H \ fillH (β '' Icc 0 b) := fun p hp h =>
    h.2 (mem_fillH_of_mem_closure h.1 (subset_closure hp))
  rcases lt_trichotomy w z.L₂ with h | rfl | h
  · intro hU
    exact (ne_of_gt (show (0 : ℝ) < (ψ w).im from hU.1)) (ht.zone₀ w h).1
  · exact hβ _ ht.L₂_mem
  · exact hβ _ (ht.side₂ w h hw)

variable {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {φ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- The chart inverse moves points by a bounded amount, composed with a single-path chart of bounded displacement. -/
theorem comp_disp_of_retChart (hC : IsRetChart α a β b φ ψ lift) {f : ℂ → ℂ} {U : Set ℂ} (hψU : MapsTo ψ H U)
    {C : ℝ} (hCf : ∀ z ∈ U, ‖f z - z‖ ≤ C) : ∃ M : ℝ, ∀ z ∈ H, ‖f (ψ z) - z‖ ≤ M := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M := hC.2.2.2.2.2.2.2.2.2.1
  refine ⟨C + M, fun z hz => ?_⟩
  calc ‖f (ψ z) - z‖ = ‖(f (ψ z) - ψ z) + (ψ z - z)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖f (ψ z) - ψ z‖ + ‖ψ z - z‖ := norm_add_le _ _
    _ ≤ C + M := add_le_add (hCf _ (hψU hz)) (hM z (H_subset_Hbar hz))

/-- **`RetTouchSidesStatement` is proved** (see the module docstring). -/
theorem retTouchSidesStatement : RetTouchSidesStatement := by
  intro α β ζ₁ ζ₂ x₁ x₂ a b φ ψ lift W₁ W₂ hp₁ hp₂ _ hp _ hC ht hg₁ hWc₁ hW0₁ hg₂ hWc₂ hW0₂
  set z := zoneDataT φ (activeDomain α a β b) ψ α a β b with hzdef
  have h0₁ : (α 0).im = 0 := by rw [Sec7.IsPathGood.zero hp₁]; simp
  have h0₂ : (β 0).im = 0 := by rw [Sec7.IsPathGood.zero hp₂]; simp
  have ha0 : 0 < a := by
    refine pos_iff_ne_zero.2 fun h => ?_
    have h1 : (0 : ℝ) < (α a).im := hp.2.2.1
    rw [h, h0₁] at h1
    exact lt_irrefl 0 h1
  have hb0 : 0 < b := by
    refine pos_iff_ne_zero.2 fun h => ?_
    have h1 : (0 : ℝ) < (β b).im := hp.2.2.2.1
    rw [h, h0₂] at h1
    exact lt_irrefl 0 h1
  have hK : IsCompact (prefixSet α a β b) :=
    (Sec7.IsPathGood.isCompact_image hp₁ hp.1.le).union (Sec7.IsPathGood.isCompact_image hp₂ hp.2.1.le)
  have hbij : BijOn ψ H (H \ fillH (prefixSet α a β b)) := by
    rw [← activeDomain_eq hK.isClosed]; exact hC.bijOn h0₂
  have hψc : ContinuousOn ψ Hbar := hC.continuousOn_inv
  have hψd : DifferentiableOn ℂ ψ H := hC.differentiableOn_inv
  have hψi : InjOn ψ H := hbij.injOn
  have hψU₁ : MapsTo ψ H (H \ fillH (α '' Icc 0 a)) := fun _ hw =>
    IsSetting.fill₁_subset (hbij.mapsTo hw)
  have hψU₂ : MapsTo ψ H (H \ fillH (β '' Icc 0 b)) := fun _ hw =>
    IsSetting.fill₂_subset (hbij.mapsTo hw)
  refine ⟨?_, ?_⟩
  · -- the first path
    have hch : IsPhysChart α a (physF W₁ a x₁)
        (fun w => extendFrom H (QuantumZipper.fwdMapInv (fun r : ℝ => W₁ r.toNNReal) a) w + x₁) :=
      isPhysChart hg₁ hWc₁ hW0₁ hp₁.1 hp.1 ha0
    obtain ⟨C, hCd⟩ := physF_disp hp₁ hg₁ hWc₁ hW0₁ hp.1 ha0
    obtain ⟨M, hM⟩ := comp_disp_of_retChart hC hψU₁ hCd
    have hlim : ∀ w : ℝ, z.R₂ < w → Tendsto (fun y => physF W₁ a x₁ (ψ y)) (𝓝[H] ((w : ℝ) : ℂ))
        (𝓝 ((bdryVal (physF W₁ a x₁) ψ w : ℝ) : ℂ)) := fun w hw => by
      obtain ⟨y, -, hy⟩ := exists_real_tendsto_comp hch hψc hψU₁ hM (notMem_U₁ ht hw)
      exact tendsto_bdryVal ⟨y, hy⟩
    have hmono := strictMonoOn_Ioi_of_tendsto_comp hψc hψd hψU₁ (isOpen_U hp₁ hp.1.le)
      (differentiableOn_physF hg₁ hWc₁ hW0₁ hp.1) hch.maps hψi hch.injOn (fun w hw => hlim w hw) hM
    refine ⟨hlim, hmono, ?_⟩
    obtain ⟨y, hΦy, hy⟩ := exists_real_tendsto_comp hch hψc hψU₁ hM (notMem_U₁ ht ht.R₂_lt_M₁)
    rw [ht.tip₁] at hΦy
    have hy0 := hch.tip_fibre hp.2.2.1 y hΦy
    rw [hy0] at hy
    exact bdryVal_eq hy
  · -- the second path
    have hch : IsPhysChart β b (physF W₂ b x₂)
        (fun w => extendFrom H (QuantumZipper.fwdMapInv (fun r : ℝ => W₂ r.toNNReal) b) w + x₂) :=
      isPhysChart hg₂ hWc₂ hW0₂ hp₂.1 hp.2.1 hb0
    obtain ⟨C, hCd⟩ := physF_disp hp₂ hg₂ hWc₂ hW0₂ hp.2.1 hb0
    obtain ⟨M, hM⟩ := comp_disp_of_retChart hC hψU₂ hCd
    have hlim : ∀ w : ℝ, w < z.R₂ → Tendsto (fun y => physF W₂ b x₂ (ψ y)) (𝓝[H] ((w : ℝ) : ℂ))
        (𝓝 ((bdryVal (physF W₂ b x₂) ψ w : ℝ) : ℂ)) := fun w hw => by
      obtain ⟨y, -, hy⟩ := exists_real_tendsto_comp hch hψc hψU₂ hM (notMem_U₂ ht hw)
      exact tendsto_bdryVal ⟨y, hy⟩
    have hmono := strictMonoOn_Iio_of_tendsto_comp hψc hψd hψU₂ (isOpen_U hp₂ hp.2.1.le)
      (differentiableOn_physF hg₂ hWc₂ hW0₂ hp.2.1) hch.maps hψi hch.injOn (fun w hw => hlim w hw) hM
    refine ⟨hlim, hmono, ?_⟩
    obtain ⟨y, hΦy, hy⟩ := exists_real_tendsto_comp hch hψc hψU₂ hM (notMem_U₂ ht ht.zero_lt_R₂)
    rw [ofReal_zero, ht.tip₂] at hΦy
    have hy0 := hch.tip_fibre hp.2.2.2.1 y hΦy
    rw [hy0] at hy
    exact bdryVal_eq hy

end RetChart

end RLC

end InteractingSLE
