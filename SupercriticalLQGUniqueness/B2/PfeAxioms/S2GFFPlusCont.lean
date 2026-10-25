import SupercriticalLQGUniqueness.B2.PfeAxioms.S2SubseqLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2WeylAlgebra
import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationLimitSkC
import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationTopology
import SupercriticalLQGUniqueness.B2.WeakStrong.Homothety
import SupercriticalLQGUniqueness.B2.WeakStrong.Field
import SupercriticalLQGUniqueness.B2.PfeLocal.OpenInternalBridge
import LQGMetric.Papers.DFGPS.T12P6B
import LQGMetric.Field.Measurable

 















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

 
theorem translateDist_addFun (z : ℂ) (u : DistC) (f : C(ℂ, ℝ)) :
    translateDist z (addFun u f) =
      addFun (translateDist z u) (f.comp (ContinuousMap.addRight z)) := by
  refine DFunLike.ext _ _ fun φ => ?_
  change u (testTranslate z φ) + ofCont f (testTranslate z φ) =
    translateDist z u φ + ofCont (f.comp (ContinuousMap.addRight z)) φ
  rw [ofCont_apply, ofCont_apply]
  congr 1
  rw [← integral_add_right_eq_self (fun x => testTranslate z φ x * f x) z]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show φ (x + z - z) * f (x + z) = φ x * f (x + z)
  rw [add_sub_cancel_right]

 
def trPt (M : LSCMetric) (w : ℂ) : (translateMetric w M).Space → M.Space :=
  fun x => M.pt ((show ℂ from x) + w)

theorem isometry_trPt (M : LSCMetric) (w : ℂ) : Isometry (trPt M w) :=
  fun _ _ => rfl

theorem trPt_comp (M : LSCMetric) (w : ℂ) (P : ℝ → ℂ) :
    trPt M w ∘ ((translateMetric w M).pt ∘ P) = M.pt ∘ fun t => P t + w := rfl

theorem isCurve_translateMetric_iff' (M : LSCMetric) (w : ℂ) (P : ℝ → ℂ) (a b : ℝ) :
    (translateMetric w M).IsCurve P a b ↔ M.IsCurve (fun t => P t + w) a b := by
  refine and_congr_right fun _ => ?_
  rw [(isometry_trPt M w).isEmbedding.continuousOn_iff, trPt_comp]

theorem hasUnitSpeedOn_translateMetric_iff (M : LSCMetric) (w : ℂ) (P : ℝ → ℂ)
    (s : Set ℝ) :
    HasUnitSpeedOn ((translateMetric w M).pt ∘ P) s ↔
      HasUnitSpeedOn (M.pt ∘ fun t => P t + w) s := by
  rw [← trPt_comp, WeakStrong.hasUnitSpeedOn_comp_isometry_iff (isometry_trPt M w)]

theorem sub_add_fun (w : ℂ) (Q : ℝ → ℂ) : (fun t => (fun t => Q t - w) t + w) = Q :=
  funext fun t => sub_add_cancel (Q t) w

 


theorem weylScale_translateMetric (ξ : ℝ) {f g : C(ℂ, ℝ)} (M : LSCMetric) (w : ℂ)
    (hfg : ∀ z, g (z + w) = f z) (p : ℂ × ℂ) :
    weylScale ξ f (translateMetric w M) p = weylScale ξ g M (p.1 + w, p.2 + w) := by
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun L => le_iInf fun hQ => le_iInf fun hu =>
      le_iInf fun hQa => le_iInf fun hQb => ?_
    have h1 : (translateMetric w M).IsCurve (fun t => Q t - w) 0 L := by
      rw [isCurve_translateMetric_iff', sub_add_fun]; exact hQ
    have h2 : HasUnitSpeedOn ((translateMetric w M).pt ∘ fun t => Q t - w) (Icc 0 L) := by
      rw [hasUnitSpeedOn_translateMetric_iff, sub_add_fun]; exact hu
    have h3 : (fun t => Q t - w) 0 = p.1 := by simp only [hQa, add_sub_cancel_right]
    have h4 : (fun t => Q t - w) L = p.2 := by simp only [hQb, add_sub_cancel_right]
    calc weylScale ξ f (translateMetric w M) p
          ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f ((fun t => Q t - w) t))) :=
          iInf_le_of_le (fun t => Q t - w) <| iInf_le_of_le L <| iInf_le_of_le h1 <|
            iInf_le_of_le h2 <| iInf_le_of_le h3 <| iInf_le_of_le h4 le_rfl
      _ = ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (Q t))) := by
          refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
          rw [← hfg, sub_add_cancel]
  · refine le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hu =>
      le_iInf fun hPa => le_iInf fun hPb => ?_
    have h1 : M.IsCurve (fun t => P t + w) 0 L :=
      (isCurve_translateMetric_iff' M w P 0 L).1 hP
    have h2 : HasUnitSpeedOn (M.pt ∘ fun t => P t + w) (Icc 0 L) :=
      (hasUnitSpeedOn_translateMetric_iff M w P _).1 hu
    have h3 : (fun t => P t + w) 0 = (p.1 + w, p.2 + w).1 := by simp only [hPa]
    have h4 : (fun t => P t + w) L = (p.1 + w, p.2 + w).2 := by simp only [hPb]
    calc weylScale ξ g M (p.1 + w, p.2 + w)
          ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g ((fun t => P t + w) t))) :=
          iInf_le_of_le (fun t => P t + w) <| iInf_le_of_le L <| iInf_le_of_le h1 <|
            iInf_le_of_le h2 <| iInf_le_of_le h3 <| iInf_le_of_le h4 le_rfl
      _ = ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
          refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
          rw [hfg]

 
theorem isGFFPlusCont_of_normalized {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) : IsGFFPlusCont h P := by
  obtain ⟨hm, f, hf, -, hW⟩ := LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1
  exact ⟨hm, f, hf, hW⟩

 

variable (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
  (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
  (Φ : DistC → LSCMetric)
  (hlsc : PfeWeyl.NormalizedLscLimit ξ m ε Φ)
  (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
  (htail : PfeWeyl.NormalizedAcrossTails Φ)
  (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε Φ)

include hε hlsc hgeo htail hsmall in
 

theorem exists_decomp_patchWitness_of_gffPlusCont
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∃ (h₀ : Ω → DistC) (g : Ω → C(ℂ, ℝ)), IsNormalizedWholePlaneGFF h₀ P ∧ Measurable g ∧
      (∀ ω, h ω = addFun (h₀ ω) (g ω)) ∧
      ∀ᵐ ω ∂P, Continuous (PfeWeyl.euclidForget (Φ (h₀ ω))) ∧
        ∀ F : C(ℂ, ℝ), ∀ p,
          patchWitness ξ m ε (addFun (h₀ ω) F) p = weylScale (ξ : ℝ) F (Φ (h₀ ω)) p := by
  obtain ⟨h₀, g, hh₀, hg, hdec⟩ := LQGMetric.DFGPS.T12.isGFFPlusCont_decomp hh
  have hh₀' : IsNormalizedWholePlaneGFF h₀ P := isNormalizedWholePlaneGFF_iff_old.mpr hh₀
  refine ⟨h₀, g, hh₀', hg, hdec, ?_⟩
  filter_upwards [ae_patchWitness_weyl_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h₀ hh₀',
    (hgeo P h₀ hh₀').2] with ω hω hctrl
  exact ⟨B2.PfeLocal.continuous_euclidForget_of_small_metric _ hctrl, fun F p => (hω F).2 p⟩

include hε hlsc hgeo htail hsmall in
 
theorem ae_isLengthSpace_patchWitness_of_gffPlusCont
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, (patchWitness ξ m ε (h ω)).IsLengthSpace := by
  obtain ⟨h₀, g, -, -, hdec, hae⟩ :=
    exists_decomp_patchWitness_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  filter_upwards [hae] with ω hω
  rw [hdec ω]
  exact isLengthSpace_weylScale (Φ (h₀ ω)) hω.1 ξ ξ.property.le (g ω) _ (hω.2 (g ω))

include hε hlsc hgeo htail hsmall in
 

theorem ae_weyl_patchWitness_of_gffPlusCont
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), weylScale (ξ : ℝ) f (patchWitness ξ m ε (h ω)) =
      (patchWitness ξ m ε (addFun (h ω) f)).1 := by
  obtain ⟨h₀, g, -, -, hdec, hae⟩ :=
    exists_decomp_patchWitness_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  filter_upwards [hae] with ω hω
  intro f
  funext p
  have h1 := hω.2 (g ω + f) p
  have h2 := weylScale_comp (Φ (h₀ ω)) _ hω.1 ξ ξ.property.le (g ω) (hω.2 (g ω)) f p
  rw [hdec ω, DFGPS.T12.addFun_addFun', h2, add_comm f (g ω)]
  exact h1.symm

include hε hlsc hgeo htail hsmall in
 

theorem ae_translate_patchWitness_of_gffPlusCont
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (hpts : PfeWeyl.NormalizedPointCircles ξ m ε Φ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (patchWitness ξ m ε (translateDist z (h ω))).1 (u, v) =
        (patchWitness ξ m ε (h ω)).1 (u + z, v + z) := by
  obtain ⟨h₀, g, hh₀, -, hdec, -⟩ :=
    exists_decomp_patchWitness_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  let X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun δ =>
    (exists_heatVersion hh₀ (δ : ℝ) δ.property).choose
  have hX : ∀ δ, IsHeatSmoothing P h₀ δ (X δ) := fun δ =>
    (exists_heatVersion hh₀ (δ : ℝ) δ.property).choose_spec.2
  have htr := ae_translation_of_dg20LimitSkC_w3 hSkC ξ Q hQ m hm ε hε (patchWitness ξ m ε)
    (subseqLimit_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall hpts) P h₀ hh₀ X hX
    (normalizedAcrossTails_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall)
    (normalizedSmallAnnuli_patchWitness ξ m ε hε Φ hlsc hgeo htail hsmall) z
  have hk : IsGFFPlusCont (fun ω => translateDist z (h₀ ω)) P :=
    WeakStrong.isGFFPlusCont_translate (isGFFPlusCont_of_normalized hh₀) z
  have hWk := ae_weyl_patchWitness_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall P _ hk
  have hW0 := ae_weyl_patchWitness_of_gffPlusCont ξ m ε hε Φ hlsc hgeo htail hsmall P h₀
    (isGFFPlusCont_of_normalized hh₀)
  filter_upwards [htr, hWk, hW0] with ω htrω hWkω hW0ω
  intro u v
  have hEq : patchWitness ξ m ε (translateDist z (h₀ ω)) =
      translateMetric z (patchWitness ξ m ε (h₀ ω)) :=
    LSCMetric.ext fun p => htrω p.1 p.2
  rw [hdec ω, translateDist_addFun, ← hWkω, ← hW0ω, hEq]
  exact weylScale_translateMetric (ξ : ℝ) _ z (fun _ => rfl) (u, v)

end SupercriticalLQGUniqueness.B2.PfeAxioms
