import QuantumZipper.Proofs.Thm18.ASep4All
import QuantumZipper.Proofs.Thm18.ASep2Sing

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP4 (step 9): assembling the conclusion; the profile singular at `0` for rescaled fields

* `concl0_of_good` (deterministic): conjuncts 1 and 2 at every good parameter of every dyadic
  folded circle give `G4SepConcl0` (as `ae_conj2_add_sep`, `parGood_of_backSep`);
* `concl0_rescale_cutoff` (deterministic): for a scale `s > 0` and a profile `g` continuous off
  `0`, the conclusion for `rescale (ofFun g + x₀) Q s` follows from the conclusions for
  `rescale (ofFun g' + x₀) Q s` with `g'` continuous: take `g' = cutoffProf g (s m / 4)`, where the
  pushed circles near the separated image stay at distance `≥ m / 2` from `0` (`ae_nuT_far`), so
  after the dilation by `s` the two fields read the same raw values
  (`evalReg_rescale_map_eq_of_loc`, `evalReg_map_eq_of_loc`). This is the argument of
  `ae_concl0_prof` (ASep2Sing) with the scale inserted; it needs no probabilistic input.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core RegCont TwoPoint CoordReg GenUC

/-- **The conclusion from conjuncts 1 and 2 at good parameters** (deterministic). -/
theorem concl0_of_good (γ : ℝ) {W : ℝ → ℝ} (hWg : DrvGood W) {y : FieldSample}
    (h1 : ∀ i : ℕ, ∀ p ∈ GoodSet W (foldH (CoordsFull.fullIndex i).1) (CoordsFull.fullIndex i).2,
      evalReg (rescale (coordChange y (fwdMapInv W (p 0)) (Qc γ)) (Qc γ) (p 1))
          ((foldedCircle (foldH (CoordsFull.fullIndex i).1) (CoordsFull.fullIndex i).2).map
            (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) =
        rescale (coordChange y (fwdMapInv W (p 0)) (Qc γ)) (Qc γ) (p 1)
          ((foldedCircle (foldH (CoordsFull.fullIndex i).1) (CoordsFull.fullIndex i).2).map
            (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)))
    (h2 : ∀ i : ℕ, ∀ p ∈ GoodSet W (foldH (CoordsFull.fullIndex i).1) (CoordsFull.fullIndex i).2,
      evalReg (coordChange y (fwdMapInv W (p 0)) (Qc γ))
          (nuA0 W (foldH (CoordsFull.fullIndex i).1) (CoordsFull.fullIndex i).2 p) =
        coordChange y (fwdMapInv W (p 0)) (Qc γ)
          (nuA0 W (foldH (CoordsFull.fullIndex i).1) (CoordsFull.fullIndex i).2 p)) :
    G4SepConcl0 γ (y, W) := by
  have hW := hWg.1
  have hW0 := hWg.2.1
  have hreal := hWg.2.2.2
  intro τ a hτ ha i hsup hsep
  obtain ⟨p, hp0, hp1⟩ : ∃ p : Fin 2 → ℝ, p 0 = τ ∧ p 1 = a := ⟨![τ, a], rfl, rfl⟩
  subst hp0 hp1
  have hfc : fcI i = foldedCircle (foldH (CoordsFull.fullIndex i).1)
      (CoordsFull.fullIndex i).2 := by
    rw [WedgeTK.fc_foldH_eq]
  have hsep' : ∃ δ : ℝ, 0 < δ ∧ foldedCircle (foldH (CoordsFull.fullIndex i).1)
      (CoordsFull.fullIndex i).2
      (Metric.thickening δ (revHull (backDrv W (p 0) 0 (p 1)).2
        (backDrv W (p 0) 0 (p 1)).1)) = 0 := by
    obtain ⟨δ, hδ, h⟩ := hsep
    exact ⟨δ, hδ, by rw [← hfc]; exact h⟩
  have hgood : p ∈ GoodSet W (foldH (CoordsFull.fullIndex i).1) (CoordsFull.fullIndex i).2 :=
    parGood_of_backSep hW hW0 hreal (UnzipFull.fullIndex_radius_pos i) hτ ha hsep'
  have hgd : ∀ᵐ w ∂foldedCircle (foldH (CoordsFull.fullIndex i).1)
      (CoordsFull.fullIndex i).2, 0 < w.im ∧
      w ∈ revMap (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 '' H := by
    have h1 : ∀ᵐ w ∂fcI i,
        w ∈ revMap (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 '' H :=
      mem_ae_iff.2 hsup
    rw [hfc] at h1
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H _ (UnzipFull.fullIndex_radius_pos i), h1]
      with w hw1 hw2
    exact ⟨hw1, hw2⟩
  have he := nuA0_eq_map_psi hW hW0 (p := p) hτ.le ha hgd
  have hc2 := h2 i p hgood
  rw [he] at hc2
  have hc1 := h1 i p hgood
  rw [hfc]
  exact ⟨hc1, hc2⟩

/-- The separation hypotheses only see the driver. -/
theorem backSupportI_fst (y y' : FieldSample) (W : ℝ → ℝ) (τ τ' a : ℝ) (i : ℕ) :
    BackSupportI (y, W) τ τ' a i → BackSupportI (y', W) τ τ' a i := id

theorem backSepI_fst (y y' : FieldSample) (W : ℝ → ℝ) (τ τ' a : ℝ) (i : ℕ) :
    BackSepI (y, W) τ τ' a i → BackSepI (y', W) τ τ' a i := id

/-- **The singular profile for rescaled fields** (deterministic). -/
theorem concl0_rescale_cutoff (γ : ℝ) {W : ℝ → ℝ} (hWg : DrvGood W) (x₀ : FieldSample) {s : ℝ}
    (hs : 0 < s)
    (hcont : ∀ g' : ℂ → ℝ, Continuous g' → G4SepConcl0 γ (rescale (ofFun g' + x₀) (Qc γ) s, W))
    {g : ℂ → ℝ} (hg : ContinuousOn g {0}ᶜ) :
    G4SepConcl0 γ (rescale (ofFun g + x₀) (Qc γ) s, W) := by
  have hW := hWg.1
  have hW0 := hWg.2.1
  have hreal := hWg.2.2.2
  intro τ a hτ ha i hsup hsep
  obtain ⟨p, hp0, hp1⟩ : ∃ p : Fin 2 → ℝ, p 0 = τ ∧ p 1 = a := ⟨![τ, a], rfl, rfl⟩
  subst hp0 hp1
  set d := foldH (CoordsFull.fullIndex i).1 with hd_def
  set r := (CoordsFull.fullIndex i).2 with hr_def
  have hr : 0 < r := UnzipFull.fullIndex_radius_pos i
  have hfc : fcI i = foldedCircle d r := by rw [WedgeTK.fc_foldH_eq]
  have hsep' : ∃ δ : ℝ, 0 < δ ∧ foldedCircle d r
      (Metric.thickening δ (revHull (backDrv W (p 0) 0 (p 1)).2
        (backDrv W (p 0) 0 (p 1)).1)) = 0 := by
    obtain ⟨δ, hδ, h⟩ := hsep
    exact ⟨δ, hδ, by rw [← hfc]; exact h⟩
  have hgood : p ∈ GoodSet W d r := parGood_of_backSep hW hW0 hreal hr hτ ha hsep'
  have hR : (0 : ℝ) ≤ ‖d‖ + r := by positivity
  have hK : foldSph d r ⊆ closedBall 0 (‖d‖ + r) := fun x hx => by
    rw [mem_closedBall, dist_zero_right]; exact norm_le_of_mem_foldSph hx
  have hU : IsOpen (GoodSet W d r) := isOpen_parGood hR hK
  obtain ⟨lo, hi, hpab, hsub⟩ := exists_ratBox_subset hU hgood
  obtain ⟨T, a₀, a₁, δ, hT, ha₀, hδ, -, hSb, hgoodB, hsepB⟩ := boxData_A0 hr hsub ⟨p, hpab⟩
  have hgood0 := hgood0_of_hgood hgoodB
  obtain ⟨m, -, -, -, hm, -, hlow, -⟩ := exists_geo_A0 hW hW0 hT.le ha₀ hgood0
  obtain ⟨-, hgd, -, hsupp, hI2, -, -⟩ :=
    pfacts_A0 hW hW0 hr ha₀ hm hδ hgood0 hlow (hSb p hpab).1 (hSb p hpab).2.2 (hSb p hpab).2.1
      (hsepB p hpab) 0 (continuous_const (y := (0 : ℝ)))
  have hτT : p 0 ∈ Icc (0 : ℝ) T := (hSb p hpab).1
  have haI : p 1 ∈ Icc a₀ a₁ := (hSb p hpab).2.1
  have hSm : ∀ z ∈ scaledSph d r a₀ a₁, m ≤ ‖z‖ := by
    rintro _ ⟨⟨a', w⟩, ⟨ha', hw⟩, rfl⟩
    obtain ⟨u, hu⟩ := hgood0 a' ha' w hw
    have := hlow _ ⟨⟨a', w⟩, ⟨ha', hw⟩, rfl⟩ 0 ⟨le_rfl, hT.le⟩
    rwa [fwdMap_eq_any hu ⟨le_rfl, hT.le⟩, FwdHolo.sol_zero hu hT.le, hW0, Complex.ofReal_zero,
      sub_zero] at this
  have hKH : scaledSph d r a₀ a₁ ⊆ Hbar := by
    rintro _ ⟨⟨a', w⟩, ⟨ha', hw⟩, rfl⟩
    obtain ⟨y, -, rfl⟩ := hw
    show 0 ≤ ((a' : ℂ) * foldH y).im
    have h1 : 0 ≤ (foldH y).im := by rw [TwoPoint.im_foldH]; exact abs_nonneg _
    simpa using mul_nonneg (ha₀.le.trans ha'.1) h1
  set ε : ℝ := m / 2 * Real.exp (-(8 * T / m ^ 2)) with hεdef
  have hε : 0 < ε := by positivity
  set Z₀ : Set ℂ := fwdMap W (p 0) '' {z | z ∈ scaledSph d r a₀ a₁ ∧ 0 < z.im} with hZ₀
  set η : ℝ := s * m / 4 with hηdef
  have hη : 0 < η := by positivity
  set g' : ℂ → ℝ := cutoffProf g η with hg'def
  have hg'c : Continuous g' := continuous_cutoffProf hg hη
  have hgg : ∀ v : ℂ, η ≤ ‖v‖ → g v = g' v := fun v hv => (cutoffProf_eq hη hv).symm
  set Z₁ : Set ℂ := {v | s * m / 2 ≤ ‖v‖} with hZ₁
  -- raw locality of the base fields
  have hlocRaw : ∀ c ∈ RegUnif.Dy, ∀ k : ℕ, (∃ z₀ ∈ Z₁, ‖c - z₀‖ + radius k ≤ η) →
      (ofFun g + x₀) (foldedCircle c (radius k)) =
        (ofFun g' + x₀) (foldedCircle c (radius k)) := by
    rintro c hcD k ⟨z₀, hz₀, hnear⟩
    have hcH : c ∈ Hbar := RegUnif.Dy_subset_Hbar hcD
    show ofFun g (foldedCircle c (radius k)) + x₀ (foldedCircle c (radius k)) =
      ofFun g' (foldedCircle c (radius k)) + x₀ (foldedCircle c (radius k))
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [FrostmanReg.foldedCircle_ae_near_frostman (c := c) hcH (radius_pos k).le]
      with w hw
    refine hgg w ?_
    have h1 : ‖w - c‖ ≤ radius k := by simpa using hw.2
    have h2 := norm_sub_norm_le z₀ w
    have h3 := norm_sub_le_norm_sub_add_norm_sub z₀ c w
    have hz : s * m / 2 ≤ ‖z₀‖ := hz₀
    rw [norm_sub_rev z₀ c, norm_sub_rev c w] at h3
    linarith
  -- locality of the unzipped fields
  have hloc : ∀ c ∈ RegUnif.Dy, ∀ k : ℕ, (∃ z₀ ∈ Z₀, ‖c - z₀‖ + radius k ≤ ε) →
      coordChange (rescale (ofFun g + x₀) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ)
          (foldedCircle c (radius k)) =
        coordChange (rescale (ofFun g' + x₀) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ)
          (foldedCircle c (radius k)) := by
    rintro c hcD k ⟨_, ⟨z₀, ⟨hz₀S, hz₀im⟩, rfl⟩, hnear⟩
    have hcH : c ∈ Hbar := RegUnif.Dy_subset_Hbar hcD
    have hsol : ∃ u, IsForwardSol W z₀ T u := by
      obtain ⟨⟨a', w⟩, ⟨ha', hw⟩, rfl⟩ := hz₀S
      exact hgood0 a' ha' w hw
    have hfar := ae_nuT_far hW hW0 hT.le hm hz₀im hsol (hlow z₀ hz₀S) hτT hcH (radius_pos k) hnear
    obtain ⟨C, B, -, -, hf⟩ := νT_facts hW hW0 (p 0) c (radius_pos k)
    obtain ⟨-, -, hae⟩ := hf (p 0) ⟨hτT.1, le_rfl⟩
    have hmeas := aemeasurable_fwdMapInv hW hW0 hτT.1 c (radius_pos k)
    have hS : MeasurableSet {v : ℂ | v ∈ Hbar ∧ (s : ℂ) * v ∈ Z₁} :=
      isClosed_Hbar.measurableSet.inter
        (measurableSet_le measurable_const (measurable_const_mul (s : ℂ)).norm)
    have hσ : ∀ᵐ w ∂foldedCircle c (radius k),
        fwdMapInv W (p 0) w ∈ Hbar ∧ (s : ℂ) * fwdMapInv W (p 0) w ∈ Z₁ := by
      refine (ae_map_iff hmeas hS).1 ?_
      filter_upwards [hae, hfar] with v hv1 hv2
      refine ⟨(show (0 : ℝ) < v.im from hv1.1).le, ?_⟩
      show s * m / 2 ≤ ‖(s : ℂ) * v‖
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
      nlinarith
    show evalReg (rescale (ofFun g + x₀) (Qc γ) s)
        ((foldedCircle c (radius k)).map (fwdMapInv W (p 0))) + _ =
      evalReg (rescale (ofFun g' + x₀) (Qc γ) s)
        ((foldedCircle c (radius k)).map (fwdMapInv W (p 0))) + _
    rw [evalReg_rescale_map_eq_of_loc hη hlocRaw (Qc γ) hs hmeas hσ]
  -- the conclusion measures
  have hψm : Measurable (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1) :=
    Cor15Group.measurable_revMapInv (continuous_backDrv hW (p 0) 0 (p 1))
      (show 0 ≤ (p 0 - 0) / p 1 ^ 2 from div_nonneg (by linarith) (sq_nonneg _))
  have hσ : ∀ᵐ w ∂foldedCircle d r,
      (p 1 : ℂ) * revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w ∈ Hbar ∧
      (p 1 : ℂ) * revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w ∈ Z₀ ∧
      revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w ∈ Hbar := by
    filter_upwards [hgd, ae_mem_foldSph d hr.le] with w hw hwS
    have e := mul_revMapInv_revDrv0_eq hW hW0 hτ.le ha hw.2.1 hw.1
    have hawH : (p 1 : ℂ) * w ∈ H := by
      show 0 < ((p 1 : ℂ) * w).im
      simpa using mul_pos ha hw.1
    have hf : 0 < (fwdMap W (p 0) ((p 1 : ℂ) * w)).im :=
      FwdHolo.mapsTo_fwdMap hW hτ.le ⟨hawH, hw.2.2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; exact hf.le
    · rw [e]; exact ⟨_, ⟨mem_scaledSph haI hwS, hawH⟩, rfl⟩
    · rw [← e] at hf
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hf
      exact le_of_lt (pos_of_mul_pos_right hf ha.le)
  have hφm : AEMeasurable (fun w => (p 1 : ℂ) *
      revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w) (foldedCircle d r) :=
    ((measurable_const_mul _).comp hψm).aemeasurable
  have hE2 := evalReg_map_eq_of_loc hε hloc hφm (hσ.mono fun w hw => ⟨hw.1, hw.2.1⟩)
  have hE1 := evalReg_rescale_map_eq_of_loc hε hloc (Qc γ) ha hψm.aemeasurable
    (hσ.mono fun w hw => ⟨hw.2.2, hw.2.1⟩)
  -- raw values at the conclusion measure
  have hraw : ∀ y y' : FieldSample, evalReg y ((foldedCircle d r).map fun w => (p 1 : ℂ) * w) =
      evalReg y' ((foldedCircle d r).map fun w => (p 1 : ℂ) * w) →
      unzippedField γ (y, W) (p 0) ((foldedCircle d r).map fun w => (p 1 : ℂ) *
        revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w) =
      unzippedField γ (y', W) (p 0) ((foldedCircle d r).map fun w => (p 1 : ℂ) *
        revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w) := by
    intro y y' hyy
    rw [unzippedField_raw0 γ y hW hW0 hτ.le ha (TwoPoint.foldedCircle_ae_mem_H d hr) hsupp hI2,
      unzippedField_raw0 γ y' hW hW0 hτ.le ha (TwoPoint.foldedCircle_ae_mem_H d hr) hsupp hI2, hyy]
  have hσ'' : ∀ᵐ w ∂foldedCircle d r, (p 1 : ℂ) * w ∈ Hbar ∧ (s : ℂ) * ((p 1 : ℂ) * w) ∈ Z₁ := by
    filter_upwards [ae_mem_foldSph d hr.le] with w hw
    have hmem := mem_scaledSph haI hw
    refine ⟨hKH hmem, ?_⟩
    show s * m / 2 ≤ ‖(s : ℂ) * ((p 1 : ℂ) * w)‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
    have := hSm _ hmem
    nlinarith
  have hR2 := hraw _ _ (evalReg_rescale_map_eq_of_loc hη hlocRaw (Qc γ) hs
    (measurable_const_mul _).aemeasurable hσ'')
  -- the continuous profile `g'`
  obtain ⟨hC1u, hC2u⟩ := hcont g' hg'c (p 0) (p 1) hτ ha i (backSupportI_fst _ _ _ _ _ _ _ hsup)
    (backSepI_fst _ _ _ _ _ _ _ hsep)
  rw [hfc] at hC1u hC2u
  have hC1 : evalReg (rescale (coordChange (rescale (ofFun g' + x₀) (Qc γ) s) (fwdMapInv W (p 0))
      (Qc γ)) (Qc γ) (p 1)) ((foldedCircle d r).map
        (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) =
      rescale (coordChange (rescale (ofFun g' + x₀) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ)) (Qc γ)
        (p 1) ((foldedCircle d r).map
          (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) := hC1u
  have hC2 : evalReg (coordChange (rescale (ofFun g' + x₀) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ))
      ((foldedCircle d r).map fun w => (p 1 : ℂ) *
        revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w) =
      coordChange (rescale (ofFun g' + x₀) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ)
        ((foldedCircle d r).map fun w => (p 1 : ℂ) *
          revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w) := hC2u
  rw [hfc]
  refine ⟨?_, ?_⟩
  · have hRs : ∀ U : FieldSample, rescale U (Qc γ) (p 1) ((foldedCircle d r).map
        (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) =
        evalReg U ((foldedCircle d r).map fun w => (p 1 : ℂ) *
          revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w) +
        Qc γ * ∫ z, Real.log ‖deriv (fun z : ℂ => (p 1 : ℂ) * z) z‖ ∂((foldedCircle d r).map
          (revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1)) := by
      intro U
      unfold rescale coordChange
      rw [Measure.map_map (measurable_const_mul _) hψm]
      rfl
    have hC1' := hC1
    rw [hRs] at hC1'
    have key := hE1.trans hC1'
    rw [hRs]
    rw [← hE2] at key
    exact key
  · show evalReg (coordChange (rescale (ofFun g + x₀) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ)) _ =
      coordChange (rescale (ofFun g + x₀) (Qc γ) s) (fwdMapInv W (p 0)) (Qc γ) _
    rw [hE2]
    exact hC2.trans hR2.symm

end ASep
end QuantumZipper
