import QuantumZipper.Proofs.Thm18.G3RTail2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the region-1 tail node, conclusion

`g3TRegion1TailStmt_holds` (sources and argument in `G3RTail`), and the `R(x)`-side transfer
`g3TCutToProfRStmt_holds`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

theorem tψ_unit (i : G3Idx) (z : ℂ) (hz : ‖z‖ = 1) : tψ i z = 0 := by
  refine tψ_eq_zero i ?_
  have h1 := i.inUnit₁
  have h2 : ‖z‖ ≤ ‖z - i.t₁‖ + ‖(i.t₁ : ℂ)‖ := by
    calc ‖z‖ = ‖(z - i.t₁) + i.t₁‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at h2
  have := i.r₁_pos
  unfold ta; linarith

/-- The field functional read through the balanced increments agrees with the scheme field. -/
theorem sν₁_recon_eq (γ : ℝ) (i : G3Idx) (Y : Ω₀ → FieldSample) (ω : Ω₀) (g : ℂ → ℝ) :
    sν₁ γ i (g3recon γ (CMTV.incr (Y ω)) + ofFun g) = sν₁ γ i (normField γ Y ω + ofFun g) := by
  have hfc : FcEq (g3recon γ (CMTV.incr (Y ω)) + ofFun g) (normField γ Y ω + ofFun g) :=
    fun c ρ hρ => by simp only [Pi.add_apply, fcEq_normField_recon γ Y ω c ρ hρ]
  exact (sν_fc hfc γ i).1

/-- **Cameron–Martin transfer of a null event to the bump-shifted field.** -/
theorem null_shift_of_null {γ : ℝ} (i : G3Idx) (v : ℝ)
    {O₀ : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ)} (hO₀ : MeasurableSet O₀)
    (hnull : gffBase.P {ω | oInc i (CMTV.incr (X₀ ω)) ∈ O₀ ∧
      ENNReal.ofReal v ≤ g3pν₁ γ (g3wProf γ) i ω (Icc (-i.δ) 0)} = 0) (M : ℝ) :
    gffBase.P {ω | oInc i (CMTV.incr (X₀ ω)) ∈ O₀ ∧ ENNReal.ofReal v ≤
      bdryM γ (restrictField (circIn i.t₁ i.r₁) (g3pField γ (g3wProf γ) ω + ofFun (M • tψ i)))
        (Icc (-i.δ) 0)} = 0 := by
  set φ : ℂ → ℝ := M • tψ i with hφdef
  have hφ : ContDiff ℝ 2 φ := (contDiff_tψ i).const_smul M
  have hc : HasCompactSupport φ := (hasCompactSupport_tψ i).smul_left
  have heven : ∀ z, φ (conj z) = φ z := fun z => by simp [hφdef, tψ_conj]
  have hS : ∀ z : ℂ, ‖z‖ = 1 → φ z = 0 := fun z hz => by simp [hφdef, tψ_unit i z hz]
  set T : Set (K3.BalIdx → ℝ) := {y | oInc i y ∈ O₀ ∧ ENNReal.ofReal v ≤
    sν₁ γ i (g3recon γ y + ofFun (g3wProf γ)) (Icc (-i.δ) 0)} with hTdef
  have hrec : Measurable fun y : K3.BalIdx → ℝ => g3recon γ y + ofFun (g3wProf γ) :=
    measurable_pi_iff.2 fun μ => ((measurable_pi_apply μ).comp (measurable_g3recon γ)).add_const _
  have hT : MeasurableSet T :=
    ((measurable_oInc i) hO₀).inter (measurableSet_le measurable_const
      ((Measure.measurable_coe measurableSet_Icc).comp ((measurable_sν₁ γ i).comp hrec)))
  have hmX : Measurable fun ω => CMTV.incr (X₀ ω) :=
    measurable_pi_iff.2 fun j =>
      (gffBase.gff.measurable_coord _).sub (gffBase.gff.measurable_coord _)
  have hmX' : Measurable fun ω => CMTV.incr (X₀ ω + ofFun φ) :=
    measurable_pi_iff.2 fun j => ((gffBase.gff.measurable_coord _).add_const _).sub
      ((gffBase.gff.measurable_coord _).add_const _)
  have e := lintegral_incr_shift_eq gffBase.gff hφ hc heven
    (G := T.indicator (1 : (K3.BalIdx → ℝ) → ℝ≥0∞)) (measurable_const.indicator hT)
  -- the unshifted side vanishes
  have hpre : (fun ω => CMTV.incr (X₀ ω)) ⁻¹' T = {ω | oInc i (CMTV.incr (X₀ ω)) ∈ O₀ ∧
      ENNReal.ofReal v ≤ g3pν₁ γ (g3wProf γ) i ω (Icc (-i.δ) 0)} := by
    ext ω
    simp only [mem_preimage, hTdef, mem_ofPred_eq, sν₁_recon_eq]
    rfl
  have hR : ∫⁻ ω, T.indicator 1 (CMTV.incr (X₀ ω)) * ENNReal.ofReal (cmTilt X₀ φ ω)
      ∂gffBase.P = 0 := by
    have hae := measure_eq_zero_iff_ae_notMem.1 hnull
    rw [← hpre] at hae
    refine (lintegral_congr_ae (hae.mono fun ω hω => ?_)).trans lintegral_zero
    rw [indicator_of_notMem (show CMTV.incr (X₀ ω) ∉ T from hω), zero_mul]
  -- the shifted side
  have hpre' : (fun ω => CMTV.incr (X₀ ω + ofFun φ)) ⁻¹' T = {ω | oInc i (CMTV.incr (X₀ ω)) ∈ O₀ ∧
      ENNReal.ofReal v ≤ bdryM γ (restrictField (circIn i.t₁ i.r₁)
        (g3pField γ (g3wProf γ) ω + ofFun φ)) (Icc (-i.δ) 0)} := by
    ext ω
    have hoff : oInc i (CMTV.incr (X₀ ω + ofFun φ)) = oInc i (CMTV.incr (X₀ ω)) := by
      funext q
      simp only [oInc, CMTV.incr_add_ofFun]
      rw [hφdef, integral_tψ_eq_zero i q.2.2.2.2.1 M, integral_tψ_eq_zero i q.2.2.2.2.2 M]
      ring
    have hfield : normField γ (fun ω => X₀ ω + ofFun φ) ω + ofFun (g3wProf γ) =
        g3pField γ (g3wProf γ) ω + ofFun φ := by
      rw [← g3pField_eq_normField_shift γ hS ω]
      simp only [g3pField]
      abel
    simp only [mem_preimage, hTdef, mem_ofPred_eq, hoff]
    rw [sν₁_recon_eq γ i (fun ω => X₀ ω + ofFun φ) ω, hfield]
    rfl
  have hL : ∫⁻ ω, T.indicator 1 (CMTV.incr (X₀ ω + ofFun φ)) ∂gffBase.P =
      gffBase.P ((fun ω => CMTV.incr (X₀ ω + ofFun φ)) ⁻¹' T) := by
    rw [← lintegral_indicator_one (hmX' hT)]
    rfl
  rw [← hpre', ← hL, e, hR]

set_option maxHeartbeats 800000 in
/-- **The region-1 tail node** (`G3TRegion1TailStmt`). -/
theorem g3TRegion1TailStmt_holds : G3TRegion1TailStmt := by
  intro γ hγ hγ2 i v
  have h𝓞 := outsideSigma2_le gffBase.gff i.t₁ i.r₁ i.t₂ i.r₂
  set A : Set Ω₀ := {ω' | ENNReal.ofReal v ≤ g3pν₁ γ (g3wProf γ) i ω' (Icc (-i.δ) 0)} with hAdef
  set c := gffBase.P[A.indicator (fun _ => (1 : ℝ)) | outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂]
    with hcdef
  have hAm : MeasurableSet A :=
    measurableSet_le measurable_const ((Measure.measurable_coe measurableSet_Icc).comp
      (((measurable_bdryM γ).comp (measurable_g3pReg₁ γ (g3wProf γ) i)).mono
        (sup_le (localSigma_le gffBase.gff _ _) h𝓞) le_rfl))
  set O : Set Ω₀ := {ω | c ω ≤ 0} with hOdef
  have hOm : MeasurableSet[outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂] O :=
    measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
  have hAO : gffBase.P (A ∩ O) = 0 := by
    have hint : Integrable (A.indicator (fun _ => (1 : ℝ))) gffBase.P :=
      (integrable_const (1 : ℝ)).indicator hAm
    have h1 : ∫ x in O, A.indicator (fun _ => (1 : ℝ)) x ∂gffBase.P = ∫ x in O, c x ∂gffBase.P :=
      (setIntegral_condExp h𝓞 hint hOm).symm
    have h2 : ∫ x in O, c x ∂gffBase.P ≤ 0 := setIntegral_nonpos (h𝓞 _ hOm) fun x hx => hx
    have h3 : ∫ x in O, A.indicator (fun _ => (1 : ℝ)) x ∂gffBase.P = gffBase.P.real (A ∩ O) := by
      rw [integral_indicator_const _ hAm, measureReal_restrict_apply hAm, smul_eq_mul, mul_one]
    have : gffBase.P.real (A ∩ O) = 0 := le_antisymm (by linarith) measureReal_nonneg
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
  -- `O` through the outside increments
  have hOP : MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] (O ×ˢ (univ : Set ℝ)) := by
    rw [prod_univ]
    have hfst : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂,
        outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂] (Prod.fst : Ω₀ × ℝ → Ω₀) := by
      unfold outsideSigmaPalm; exact Measurable.of_comap_le le_sup_left
    exact hfst hOm
  obtain ⟨G₀, hG₀, hrep⟩ := outside_repr i hOP
  set O₀ : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) := (fun y => (y, (0 : ℝ))) ⁻¹' G₀ with hO₀def
  have hO₀ : MeasurableSet O₀ := hG₀.preimage (measurable_id.prodMk measurable_const)
  have hOiff : ∀ ω, ω ∈ O ↔ oInc i (CMTV.incr (X₀ ω)) ∈ O₀ := fun ω => by
    have h := Set.ext_iff.1 hrep (ω, 0)
    simpa [hO₀def] using h
  have hnull : gffBase.P {ω | oInc i (CMTV.incr (X₀ ω)) ∈ O₀ ∧
      ENNReal.ofReal v ≤ g3pν₁ γ (g3wProf γ) i ω (Icc (-i.δ) 0)} = 0 := by
    refine measure_mono_null (fun ω (hω : oInc i (CMTV.incr (X₀ ω)) ∈ O₀ ∧
      ENNReal.ofReal v ≤ g3pν₁ γ (g3wProf γ) i ω (Icc (-i.δ) 0)) =>
        (⟨hω.2, (hOiff ω).2 hω.1⟩ : ω ∈ A ∩ O)) hAO
  have hM : ∀ᵐ ω ∂gffBase.P, ∀ M : ℕ, ω ∉ {ω | oInc i (CMTV.incr (X₀ ω)) ∈ O₀ ∧
      ENNReal.ofReal v ≤ bdryM γ (restrictField (circIn i.t₁ i.r₁)
        (g3pField γ (g3wProf γ) ω + ofFun ((M : ℝ) • tψ i))) (Icc (-i.δ) 0)} :=
    ae_all_iff.2 fun M => measure_eq_zero_iff_ae_notMem.1 (null_shift_of_null i v hO₀ hnull M)
  filter_upwards [hM, ae_g3pShift_good hγ hγ2, ae_g3pField_pos hγ hγ2] with ω hMω hsh hpos
  by_contra hcω
  have hO : oInc i (CMTV.incr (X₀ ω)) ∈ O₀ := (hOiff ω).1 (not_lt.1 hcω)
  have hρ := tρ_pos i
  have hJ1 : i.t₁ + tρ i < 0 := by have := i.hη; have := i.hηδ; unfold tρ G3Idx.t₁; linarith
  have hJ2 : -i.δ ≤ i.t₁ - tρ i := by have := i.hη; have := i.hηδ; unfold tρ G3Idx.t₁; linarith
  have hJ3 : i.t₁ - i.r₁ ≤ i.t₁ - tρ i := by
    have := tρ_lt_ta i; have := i.r₁_pos; unfold ta at *; linarith
  have hJ4 : i.t₁ + tρ i ≤ i.t₁ + i.r₁ := by
    have := tρ_lt_ta i; have := i.r₁_pos; unfold ta at *; linarith
  set J : Set ℝ := Ioo (i.t₁ - tρ i) (i.t₁ + tρ i) with hJdef
  set q := qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) J with hqdef
  have hq : 0 < q := hpos _ _ (by linarith) hJ1
  set qr : ℝ := (min q 1).toReal with hqrdef
  have hqr : 0 < qr := ENNReal.toReal_pos (lt_min hq one_pos).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  have hqle : ENNReal.ofReal qr ≤ q := by
    rw [hqrdef, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _
  obtain ⟨M, hMge⟩ := exists_nat_ge (2 * v / (qr * γ))
  apply hMω M
  refine ⟨hO, ?_⟩
  have hcont : Continuous ((M : ℝ) • tψ i) := (contDiff_tψ i).continuous.const_smul _
  obtain ⟨hv', hfin', hat', hdens⟩ := hsh _ hcont
  obtain ⟨hB1, e1⟩ := G3Fid.regionCut hγ hv' hfin' hat' (t := i.t₁) i.r₁_pos
  rw [bdryM, if_pos hB1, e1]
  have hdJ : ∀ t ∈ J, ENNReal.ofReal (Real.exp (γ / 2 * M)) ≤
      ENNReal.ofReal (Real.exp (γ / 2 * ((M : ℝ) • tψ i) t)) := fun t ht => by
    have h1 : tψ i (t : ℂ) = 1 := by
      refine tψ_eq_one i ?_
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_lt.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩).le
    simp [h1]
  have hlow := pos_of_withDensity_ge measurableSet_Ioo hdens
    (ENNReal.ofReal_ne_zero_iff.2 (Real.exp_pos _)) hdJ
  have hv : v ≤ Real.exp (γ / 2 * M) * qr := by
    have hx : v / qr ≤ γ / 2 * M := by
      rw [div_le_iff₀ hqr]
      have := (div_le_iff₀ (by positivity : 0 < qr * γ)).1 hMge
      nlinarith
    have hexp := Real.add_one_le_exp (γ / 2 * M)
    have : v / qr * qr = v := div_mul_cancel₀ v hqr.ne'
    nlinarith
  calc ENNReal.ofReal v ≤ ENNReal.ofReal (Real.exp (γ / 2 * M)) * ENNReal.ofReal qr := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; exact ENNReal.ofReal_le_ofReal hv
    _ ≤ ENNReal.ofReal (Real.exp (γ / 2 * M)) * q := mul_le_mul' le_rfl hqle
    _ ≤ qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω + ofFun ((M : ℝ) • tψ i)) J := hlow
    _ = ((qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω + ofFun ((M : ℝ) • tψ i))).restrict
          (Ioo (i.t₁ - i.r₁) (i.t₁ + i.r₁))) J := by
        rw [Measure.restrict_apply measurableSet_Ioo,
          inter_eq_left.2 (Ioo_subset_Ioo hJ3 hJ4)]
    _ ≤ _ := measure_mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc hJ2 hJ1.le))

end R18
end QuantumZipper
