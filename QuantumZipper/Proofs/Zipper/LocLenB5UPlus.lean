import QuantumZipper.Proofs.Zipper.LocLenB5UArc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R3b: the plus side and `b5UniformArcStmt_holds`

The plus side of `B5UniformArcStmt` is the minus side (`ae_b5MinusArc_of_extAll`) for the
reflected `Γ⁰` pair `(−B, X ∘ refl)` (Sheffield arXiv:1012.4797 §5.4 p. 72, "by symmetry";
the same route as `F2.b5PlusUniform_of_refl`, F2S3B5Plus.lean). The reflection is applied to the
off-tip local limit at time `s` (`isVagueLimitOnR_neg`, own elementary: the reflected dyadic
approximations are the image measures, `RegUnif.integral_bdryApprox_neg`) and to the global
limit at the fixed time `T` (`F1.qBoundaryMeasure_of_avgReg_neg` with `RegUnif.ae_global_fixed`).
No tip input and no flow regularity (`CfgFlowRegStmt`) is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 B5 RegUnif

/-- **Reflection of a local vague limit** (own elementary): if the regularized averages of `x'` at
`t` are those of `x` at `−t`, a local limit `ν` of `x` on the open `U` gives the local limit
`(−·)_* ν` of `x'` on `−U`. -/
theorem isVagueLimitOnR_neg {γ : ℝ} {x x' : FieldSample}
    (havg : ∀ (k : ℕ) (t : ℝ), avgReg x' k (t : ℂ) = avgReg x k ((-t : ℝ) : ℂ))
    {U : Set ℝ} (hU : IsOpen U) {ν : Measure ℝ} (h : IsVagueLimitOnR U (bdryApprox γ x) ν) :
    IsVagueLimitOnR ((fun t : ℝ => -t) ⁻¹' U) (bdryApprox γ x') (ν.map fun t : ℝ => -t) := by
  obtain ⟨h0, hK, ht⟩ := h
  refine ⟨?_, fun K hKc hKU => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.map_apply measurable_neg (hU.preimage continuous_neg).measurableSet.compl]
    have e : (fun t : ℝ => -t) ⁻¹' ((fun t : ℝ => -t) ⁻¹' U)ᶜ = Uᶜ := by ext t; simp
    rw [e]; exact h0
  · rw [Measure.map_apply measurable_neg hKc.measurableSet]
    exact hK _ ((Homeomorph.neg ℝ).isCompact_preimage.2 hKc) fun t ht => by
      have := hKU ht
      simpa using this
  · have hg : tsupport (fun t => f (-t)) ⊆ U := fun t htt => by
      have h1 := tsupport_comp_subset_preimage f continuous_neg htt
      have h2 := hfU h1
      simpa using h2
    have h1 := ht (fun t => f (-t)) (hf.comp continuous_neg)
      (hfc.comp_homeomorph (Homeomorph.neg ℝ)) hg
    rw [integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]
    refine h1.congr' (Eventually.of_forall fun k => ?_)
    have h' : ∀ t : ℝ, avgReg x k (t : ℂ) = avgReg x' k ((-t : ℝ) : ℂ) := fun t => by
      rw [havg k (-t), neg_neg]
    exact (RegUnif.integral_bdryApprox_neg k h' f hf).symm

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Plus side of `B5UniformArcStmt`** (reflection of the minus side). -/
theorem ae_b5PlusArc (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ s ∈ Icc (0 : ℝ) T,
      (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) s).2 =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω)
          (Ioo (zeroPlus (Vr κ T B ω) (T - s)) (zeroPlus (Vr κ T B ω) T)) := by
  have hB' : IsBrownianReal (negB B) P := hB.neg
  have hX' : IsFreeGFFModConstH (reflX X) P := isFreeGFFModConstH_reflRaw hX
  have hind' := indepFun_neg_reflRaw hind
  filter_upwards [ae_b5MinusArc_of_extAll hκ hκ4 hT hB' hX' hind'
      (E5.extAllInput_holds κ P _ _ hκ hκ4 hB' hX' hind'),
    unifLocalStmt_holds hκ hκ4 hT hB hX hind,
    ae_forall_isRegularSample (γ := Real.sqrt κ) hB hX hind,
    ae_global_fixed hκ hκ4 hT hB hX hind,
    ae_isRegularSample_ofFun_h0rev hX κ, ae_drive_good hB κ,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB,
    RS.ae_real_alive hB hκ hκ4.le] with ω hm hloc hreg hG hx hdr hK halive s hs
  obtain ⟨hWc, hW0⟩ := hdr
  obtain ⟨Fx, hFx⟩ := hx
  have hcfg : cfg κ (negB B) (reflX X) ω =
      (reflRaw (ofFun (h0rev κ) + X ω), -drive κ B ω) :=
    Prod.ext (reflRaw_add_ofFun_h0rev κ (X ω)).symm (drive_negB κ B ω)
  -- the fixed chart `T`
  obtain ⟨FT, hFT⟩ := (hreg T hT.le).1
  rw [h0f_eq_unzippedField] at hG
  have hνT : qBoundaryMeasure (Real.sqrt κ) (h0f κ T (negB B) (reflX X) ω) =
      (qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω)).map fun t : ℝ => -t := by
    rw [h0f_eq_unzippedField, hcfg, h0f_eq_unzippedField]
    exact F1.qBoundaryMeasure_of_avgReg_neg
      (fun k u => avgReg_unzippedField_reflRaw_neg_real (x := ofFun (h0rev κ) + X ω)
        (W := drive κ B ω) hWc hW0 hT.le hFx hFT k u) hG
  have hVneg : Vr κ T (negB B) ω = -Vr κ T B ω := by
    funext u
    simp only [Vr, vrev, drive_negB, Pi.neg_apply]
    ring
  have hVc : Continuous (Vr κ T B ω) := continuous_vrev hWc T
  have hV0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
  -- the chart `s`
  obtain ⟨l, m, hl, hm'⟩ := F1.exists_tendsto_sideImages_of_alive (W := drive κ B ω) hs.1
    fun x hx => halive x hx s hs.1
  obtain ⟨Fs, hFs⟩ := (hreg s hs.1).1
  obtain ⟨ν, hν, -⟩ := hloc s hs
  rw [h0f_eq_unzippedField] at hν
  have hν' := isVagueLimitOnR_neg (fun k u => avgReg_unzippedField_reflRaw_neg_real
    (x := ofFun (h0rev κ) + X ω) (W := drive κ B ω) hWc hW0 hs.1 hFx hFs k u)
    isOpen_compl_singleton hν
  have hLHS : (unzipLengthsArc (Real.sqrt κ) (cfg κ (negB B) (reflX X) ω) s).1 =
      (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) s).2 := by
    rw [hcfg]
    show arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ)
          (reflRaw (ofFun (h0rev κ) + X ω), -drive κ B ω) s) (sideImages (-drive κ B ω) s).1 0 =
        arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (cfg κ B X ω) s)
          0 (sideImages (drive κ B ω) s).2
    rw [F1.sideImages_reflect_swap hs.1 hl hm']
    dsimp only
    rw [arcLen_eq_of_isVagueLimitOnR hν' (fun z hz hz0 => by
        simp only [mem_singleton_iff, neg_eq_zero] at hz0
        linarith [hz.2]),
      arcLen_eq_of_isVagueLimitOnR hν (fun z hz hz0 => by
        rw [mem_singleton_iff] at hz0; linarith [hz.1]),
      Measure.map_apply measurable_neg measurableSet_Ioo]
    congr 1
    ext t; simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have h1 := hm s hs
  rw [hLHS, hνT, hVneg,
    F2.zeroMinus_neg_of_simpleHull hVc hV0 hT hK hT.le le_rfl,
    F2.zeroMinus_neg_of_simpleHull hVc hV0 hT hK (by linarith [hs.2]) (by linarith [hs.1]),
    Measure.map_apply measurable_neg measurableSet_Ioo] at h1
  have hpre : (fun t : ℝ => -t) ⁻¹' Ioo (-zeroPlus (Vr κ T B ω) T)
      (-zeroPlus (Vr κ T B ω) (T - s)) =
      Ioo (zeroPlus (Vr κ T B ω) (T - s)) (zeroPlus (Vr κ T B ω) T) := by
    ext t; simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at h1
  exact h1

/-- **`B5UniformArcStmt` holds** (no tip input). -/
theorem b5UniformArcStmt_holds : B5UniformArcStmt := by
  intro κ hκ hκ4 T hT Ω _ P _ B X hB hX hind
  filter_upwards [ae_b5MinusArc_of_extAll hκ hκ4 hT hB hX hind
      (E5.extAllInput_holds κ P B X hκ hκ4 hB hX hind),
    ae_b5PlusArc hκ hκ4 hT hB hX hind] with ω h1 h2 s hs
  exact ⟨h1 s hs, h2 s hs⟩

end LocLen
end QuantumZipper
