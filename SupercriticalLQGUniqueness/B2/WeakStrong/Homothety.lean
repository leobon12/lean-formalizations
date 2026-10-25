import SupercriticalLQGUniqueness.Frozen.WeylScale
import SupercriticalLQGUniqueness.Frozen.LSCMetricInstMeasurableSpace
import SLUMetricAPI

 













set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 

theorem eVariationOn_comp_isometry {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {ψ : X → Y} (hψ : Isometry ψ) (f : ℝ → X) (s : Set ℝ) :
    eVariationOn (ψ ∘ f) s = eVariationOn f s := by
  simp only [eVariationOn, Function.comp_apply, hψ.edist_eq]

theorem hasUnitSpeedOn_comp_isometry_iff {X Y : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] {ψ : X → Y} (hψ : Isometry ψ) (f : ℝ → X) (s : Set ℝ) :
    HasUnitSpeedOn (ψ ∘ f) s ↔ HasUnitSpeedOn f s := by
  simp only [HasUnitSpeedOn, HasConstantSpeedOnWith, eVariationOn_comp_isometry hψ]

 

 
def dilateM (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) : LSCMetric :=
  ⟨fun p => M (c • p.1, c • p.2),
    ⟨fun x => M.isExtMetric.1 _,
      fun x y h => smul_right_injective ℂ hc (M.isExtMetric.2.1 _ _ h),
      fun x y => M.isExtMetric.2.2.1 _ _,
      fun x y z => M.isExtMetric.2.2.2 _ _ _⟩,
    M.lowerSemicontinuous.comp
      (show Continuous fun p : ℂ × ℂ => (c • p.1, c • p.2) by fun_prop)⟩

theorem dilateM_apply (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (p : ℂ × ℂ) :
    dilateM M c hc p = M (c • p.1, c • p.2) := rfl

theorem dilateM_dilateM (M : LSCMetric) {c₁ c₂ : ℝ} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    dilateM (dilateM M c₁ h₁) c₂ h₂ = dilateM M (c₁ * c₂) (mul_ne_zero h₁ h₂) :=
  LSCMetric.ext fun p => by simp only [dilateM_apply, mul_smul]

theorem dilateM_one (M : LSCMetric) : dilateM M 1 one_ne_zero = M :=
  LSCMetric.ext fun p => by simp only [dilateM_apply, one_smul]

 
def homPt (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) : (dilateM M c hc).Space → M.Space :=
  fun z => M.pt (c • (show ℂ from z))

theorem isometry_homPt (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) : Isometry (homPt M c hc) :=
  fun _ _ => rfl

theorem homPt_comp (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (P : ℝ → ℂ) :
    homPt M c hc ∘ ((dilateM M c hc).pt ∘ P) = M.pt ∘ fun t => c • P t := rfl

theorem isCurve_dilateM_iff (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (P : ℝ → ℂ) (a b : ℝ) :
    (dilateM M c hc).IsCurve P a b ↔ M.IsCurve (fun t => c • P t) a b := by
  refine and_congr_right fun _ => ?_
  rw [(isometry_homPt M c hc).isEmbedding.continuousOn_iff, homPt_comp]

theorem len_dilateM (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (P : ℝ → ℂ) (a b : ℝ) :
    (dilateM M c hc).len P a b = M.len (fun t => c • P t) a b := by
  change eVariationOn _ _ = eVariationOn _ _
  rw [← homPt_comp, eVariationOn_comp_isometry (isometry_homPt M c hc)]

theorem hasUnitSpeedOn_dilateM_iff (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (P : ℝ → ℂ)
    (s : Set ℝ) :
    HasUnitSpeedOn ((dilateM M c hc).pt ∘ P) s ↔ HasUnitSpeedOn (M.pt ∘ fun t => c • P t) s := by
  rw [← homPt_comp, hasUnitSpeedOn_comp_isometry_iff (isometry_homPt M c hc)]

theorem smul_inv_smul_fun {c : ℝ} (hc : c ≠ 0) (Q : ℝ → ℂ) :
    (fun t => c • (fun t => c⁻¹ • Q t) t) = Q :=
  funext fun t => smul_inv_smul₀ hc (Q t)

 
theorem isLengthSpace_dilateM {M : LSCMetric} (hM : M.IsLengthSpace) (c : ℝ) (hc : c ≠ 0) :
    (dilateM M c hc).IsLengthSpace := by
  intro x y hxy ε hε
  obtain ⟨Q, a, b, hQ, hQa, hQb, hlen⟩ := hM (c • x) (c • y) hxy ε hε
  refine ⟨fun t => c⁻¹ • Q t, a, b, ?_, ?_, ?_, ?_⟩
  · rw [isCurve_dilateM_iff, smul_inv_smul_fun hc]; exact hQ
  · simp only [hQa, inv_smul_smul₀ hc]
  · simp only [hQb, inv_smul_smul₀ hc]
  · rw [len_dilateM, smul_inv_smul_fun hc]; exact hlen

 
theorem internal_dilateM (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) (Y Y' : Set ℂ)
    (hY : ∀ z, c • z ∈ Y' ↔ z ∈ Y) (p : Y × Y) :
    (dilateM M c hc).internal Y p =
      M.internal Y' (⟨c • p.1.1, (hY _).2 p.1.2⟩, ⟨c • p.2.1, (hY _).2 p.2.2⟩) := by
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hQ =>
      le_iInf fun hQY => le_iInf fun hQa => le_iInf fun hQb => ?_
    have h1 : (dilateM M c hc).IsCurve (fun t => c⁻¹ • Q t) a b := by
      rw [isCurve_dilateM_iff, smul_inv_smul_fun hc]; exact hQ
    have h2 : ∀ t ∈ Icc a b, (fun t => c⁻¹ • Q t) t ∈ Y := by
      intro t ht
      rw [← hY, smul_inv_smul₀ hc]
      exact hQY t ht
    have h3 : (fun t => c⁻¹ • Q t) a = (p.1 : ℂ) := by simp only [hQa, inv_smul_smul₀ hc]
    have h4 : (fun t => c⁻¹ • Q t) b = (p.2 : ℂ) := by simp only [hQb, inv_smul_smul₀ hc]
    calc (dilateM M c hc).internal Y p ≤ (dilateM M c hc).len (fun t => c⁻¹ • Q t) a b :=
          iInf_le_of_le (fun t => c⁻¹ • Q t) <| iInf_le_of_le a <| iInf_le_of_le b <|
            iInf_le_of_le h1 <| iInf_le_of_le h2 <| iInf_le_of_le h3 <| iInf_le_of_le h4 le_rfl
      _ = M.len Q a b := by rw [len_dilateM, smul_inv_smul_fun hc]
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPY => le_iInf fun hPa => le_iInf fun hPb => ?_
    have h1 : M.IsCurve (fun t => c • P t) a b := (isCurve_dilateM_iff M c hc P a b).1 hP
    have h2 : ∀ t ∈ Icc a b, (fun t => c • P t) t ∈ Y' := fun t ht => (hY _).2 (hPY t ht)
    have h3 : (fun t => c • P t) a = c • (p.1 : ℂ) := by simp only [hPa]
    have h4 : (fun t => c • P t) b = c • (p.2 : ℂ) := by simp only [hPb]
    calc M.internal Y' (⟨c • p.1.1, (hY _).2 p.1.2⟩, ⟨c • p.2.1, (hY _).2 p.2.2⟩)
          ≤ M.len (fun t => c • P t) a b :=
          iInf_le_of_le (fun t => c • P t) <| iInf_le_of_le a <| iInf_le_of_le b <|
            iInf_le_of_le h1 <| iInf_le_of_le h2 <| iInf_le_of_le h3 <| iInf_le_of_le h4 le_rfl
      _ = (dilateM M c hc).len P a b := by rw [len_dilateM]

 

theorem weylScale_dilateM (ξ : ℝ) {f g : C(ℂ, ℝ)} (M : LSCMetric) (c : ℝ) (hc : c ≠ 0)
    (hfg : ∀ z, g (c • z) = f z) (p : ℂ × ℂ) :
    weylScale ξ f (dilateM M c hc) p = weylScale ξ g M (c • p.1, c • p.2) := by
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun L => le_iInf fun hQ => le_iInf fun hu =>
      le_iInf fun hQa => le_iInf fun hQb => ?_
    have h1 : (dilateM M c hc).IsCurve (fun t => c⁻¹ • Q t) 0 L := by
      rw [isCurve_dilateM_iff, smul_inv_smul_fun hc]; exact hQ
    have h2 : HasUnitSpeedOn ((dilateM M c hc).pt ∘ fun t => c⁻¹ • Q t) (Icc 0 L) := by
      rw [hasUnitSpeedOn_dilateM_iff, smul_inv_smul_fun hc]; exact hu
    have h3 : (fun t => c⁻¹ • Q t) 0 = p.1 := by simp only [hQa, inv_smul_smul₀ hc]
    have h4 : (fun t => c⁻¹ • Q t) L = p.2 := by simp only [hQb, inv_smul_smul₀ hc]
    calc weylScale ξ f (dilateM M c hc) p
          ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f ((fun t => c⁻¹ • Q t) t))) :=
          iInf_le_of_le (fun t => c⁻¹ • Q t) <| iInf_le_of_le L <| iInf_le_of_le h1 <|
            iInf_le_of_le h2 <| iInf_le_of_le h3 <| iInf_le_of_le h4 le_rfl
      _ = ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (Q t))) := by
          refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
          rw [← hfg, smul_inv_smul₀ hc]
  · refine le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hu =>
      le_iInf fun hPa => le_iInf fun hPb => ?_
    have h1 : M.IsCurve (fun t => c • P t) 0 L := (isCurve_dilateM_iff M c hc P 0 L).1 hP
    have h2 : HasUnitSpeedOn (M.pt ∘ fun t => c • P t) (Icc 0 L) :=
      (hasUnitSpeedOn_dilateM_iff M c hc P _).1 hu
    have h3 : (fun t => c • P t) 0 = (c • p.1, c • p.2).1 := by simp only [hPa]
    have h4 : (fun t => c • P t) L = (c • p.1, c • p.2).2 := by simp only [hPb]
    calc weylScale ξ g M (c • p.1, c • p.2)
          ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g ((fun t => c • P t) t))) :=
          iInf_le_of_le (fun t => c • P t) <| iInf_le_of_le L <| iInf_le_of_le h1 <|
            iInf_le_of_le h2 <| iInf_le_of_le h3 <| iInf_le_of_le h4 le_rfl
      _ = ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
          refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
          rw [hfg]

 

 
def lscPull (e : (ℂ × ℂ) ≃ₜ (ℂ × ℂ)) (f : LSCFun) : LSCFun :=
  ⟨f.1 ∘ e, f.2.comp e.continuous⟩

theorem lscTendsto_comp_homeomorph (e : (ℂ × ℂ) ≃ₜ (ℂ × ℂ)) {F : ℕ → ℂ × ℂ → EReal}
    {f : ℂ × ℂ → EReal} (h : LSCTendsto F f) :
    LSCTendsto (fun n => F n ∘ e) (f ∘ e) := by
  refine ⟨fun p q hpq => h.1 (fun n => e (p n)) (e q) ((e.continuous.tendsto q).comp hpq),
    fun q => ?_⟩
  obtain ⟨p, hp, hF⟩ := h.2 (e q)
  refine ⟨fun n => e.symm (p n), ?_, ?_⟩
  · simpa [Function.comp_def] using (e.symm.continuous.tendsto (e q)).comp hp
  · simpa [Function.comp_def] using hF

theorem continuous_lscPull (e : (ℂ × ℂ) ≃ₜ (ℂ × ℂ)) : Continuous (lscPull e) := by
  rw [continuous_iff_seqContinuous]
  intro F f hF
  rw [LSCFun.tendsto_iff_lscTendsto] at hF ⊢
  exact lscTendsto_comp_homeomorph e hF

 
def pairSmulHomeomorph (c : ℝ) (hc : c ≠ 0) : (ℂ × ℂ) ≃ₜ (ℂ × ℂ) :=
  (Homeomorph.smulOfNeZero c hc).prodCongr (Homeomorph.smulOfNeZero c hc)

theorem toLSCFun_dilateM (M : LSCMetric) (c : ℝ) (hc : c ≠ 0) :
    (dilateM M c hc).toLSCFun = lscPull (pairSmulHomeomorph c hc) M.toLSCFun := rfl

 
theorem continuous_dilateM (c : ℝ) (hc : c ≠ 0) : Continuous fun M : LSCMetric => dilateM M c hc := by
  rw [LSCMetric.isInducing_toLSCFun.continuous_iff]
  have e : (LSCMetric.toLSCFun ∘ fun M : LSCMetric => dilateM M c hc) =
      lscPull (pairSmulHomeomorph c hc) ∘ LSCMetric.toLSCFun := rfl
  rw [e]
  exact (continuous_lscPull _).comp LSCMetric.isInducing_toLSCFun.continuous

instance instBorelSpaceLSCMetric : BorelSpace LSCMetric := ⟨rfl⟩

 
theorem measurable_dilateM (c : ℝ) (hc : c ≠ 0) : Measurable fun M : LSCMetric => dilateM M c hc :=
  (continuous_dilateM c hc).measurable

end SupercriticalLQGUniqueness.B2.WeakStrong
