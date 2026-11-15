/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11Gate

/-!
# GB11: the old real filled base is an interval

Apply the existing boundary-interval theorem for arbitrary continuous filled paths.
The input translation removes the centering of `trMap`, so the mapping-out function
has the hydrodynamic normalization required by `IsBdryExt`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- Removing the input centering gives the boundary extension of the normalized
mapping-out inverse, including its real frontier values and bounded displacement. -/
theorem isBdryExt_uncentered_trMap {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    YuanCharacterisation.IsBdryExt (fwdHull W t)
      (fun z => fwdMap W t z + W t)
      (fun w => trMap W 0 t (w - W t)) := by
  have hshiftH : ∀ w ∈ H, w - (W t : ℂ) ∈ H := by
    intro w hw
    simpa only [QuantumZipper.H, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im,
      sub_zero] using hw
  have hshiftbar : ∀ w ∈ Hbar, w - (W t : ℂ) ∈ Hbar := by
    intro w hw
    simpa only [QuantumZipper.Hbar, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im,
      sub_zero] using hw
  have hFc := YuanSimpleApprox.trMap_continuousOn hη hW hW0 (a := 0) le_rfl ht
  refine ⟨isHPHull_fwdHull hW ht, isMapOut_fwdMap hW hW0 ht, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨Sec6.trMap_zero_mem_domain hW hW0 ht (hshiftH w hw), ?_⟩
    rw [Sec6.fwdMap_trMap_zero hW hW0 ht (hshiftH w hw), sub_add_cancel]
  · exact (YuanSimpleApprox.trMap_differentiableOn hη hW hW0 le_rfl ht).comp
      (differentiableOn_id.sub_const _) hshiftH
  · exact hFc.comp (continuous_id.sub continuous_const).continuousOn hshiftbar
  · intro x
    have hx : ((x : ℂ) - W t).im = 0 := by simp
    have hxbar : (x : ℂ) - W t ∈ Hbar := hx.ge
    refine ⟨Sec6.trMap_zero_mem_closure hη hW hW0 ht hxbar, ?_⟩
    rw [(isHPHull_fwdHull hW ht).isOpen.interior_eq]
    intro hD
    have hnot := (YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 le_rfl ht).2.2.2
      ((x : ℂ) - W t) hx
    rw [Sec6.trMap_zero_image_H hW hW0 ht] at hnot
    exact hnot hD
  · obtain ⟨M, hM⟩ := hη.exists_norm_extendFrom_sub_le hW hW0 ht
    refine ⟨M + ‖(W t : ℂ)‖, fun w hw => ?_⟩
    have hdis := hM (w - W t) (hshiftbar w hw)
    rw [← YuanSimpleApprox.trMap_zero_left hW0 t] at hdis
    have he : trMap W 0 t (w - W t) - w =
        (trMap W 0 t (w - W t) - (w - W t)) - W t := by ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hdis le_rfl)

/-- The real preimage of the explored trace is an interval, for every ambient
generating trace. No simple-trace or no-real-contact assumption is needed. -/
theorem gb11OldRealBaseStatement : GB11OldRealBaseStatement := by
  intro W' γ hW' hW'0 hγ t
  let W : ℝ → ℝ := fun r => W' r.toNNReal
  let η : ℝ → ℂ := fun r => γ r.toNNReal
  have hW : Continuous W := hW'.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simpa only [W, Real.toNNReal_zero] using hW'0
  have hη : IsLoewnerTrace W η := isLoewnerTrace_of_isGeneratingTrace hγ
  have himg : η '' Icc 0 (t : ℝ) = γ '' Icc 0 t := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r.toNNReal, ⟨zero_le, (Real.toNNReal_le_iff_le_coe).2 hr.2⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(r : ℝ), ⟨r.2, NNReal.coe_le_coe.2 hr.2⟩, by simp [η]⟩
  have hF : YuanCharacterisation.IsBdryExt (fillH (η '' Icc 0 (t : ℝ)))
      (fun z => fwdMap W t z + W t) (fun w => trMap W 0 t (w - W t)) := by
    exact (hη.2.2 (t : ℝ) t.2) ▸ isBdryExt_uncentered_trMap hη hW hW0 t.2
  have hηH : MapsTo η (Icc 0 (t : ℝ)) Hbar := by
    intro r hr
    exact (Sec6.trMap_zero_eq_trace hη hW hW0 hr.1) ▸
      YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 le_rfl hr.1
  have hne : (YuanCharacterisation.pathSet (η '' Icc 0 (t : ℝ))
      (fun w => trMap W 0 t (w - W t))).Nonempty := by
    refine ⟨W t, ?_⟩
    change trMap W 0 t ((W t : ℂ) - W t) ∈ η '' Icc 0 (t : ℝ)
    rw [sub_self]
    exact (Sec6.trMap_zero_eq_trace hη hW hW0 t.2).symm ▸
      mem_image_of_mem η ⟨t.2, le_rfl⟩
  have heq := hF.pathSet_eq_Icc (hη.2.1.mono Icc_subset_Ici_self) hηH hne
  have hX : OrdConnected (YuanCharacterisation.pathSet (η '' Icc 0 (t : ℝ))
      (fun w => trMap W 0 t (w - W t))) := by
    rw [heq]
    exact ordConnected_Icc
  constructor
  intro a ha b hb x hx
  have hxa : a + W t ∈ YuanCharacterisation.pathSet (η '' Icc 0 (t : ℝ))
      (fun w => trMap W 0 t (w - W t)) := by
    simpa only [YuanCharacterisation.pathSet, oldRealBase, mem_ofPred_eq,
      Complex.ofReal_add, add_sub_cancel_right, himg, W] using ha
  have hxb : b + W t ∈ YuanCharacterisation.pathSet (η '' Icc 0 (t : ℝ))
      (fun w => trMap W 0 t (w - W t)) := by
    simpa only [YuanCharacterisation.pathSet, oldRealBase, mem_ofPred_eq,
      Complex.ofReal_add, add_sub_cancel_right, himg, W] using hb
  have hm := hX.out hxa hxb ⟨add_le_add hx.1 le_rfl, add_le_add hx.2 le_rfl⟩
  simpa only [YuanCharacterisation.pathSet, oldRealBase, mem_ofPred_eq,
    Complex.ofReal_add, add_sub_cancel_right, himg, W] using hm

end InteractingSLE.Theorem14.GB11Chart
