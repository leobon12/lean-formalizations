import SupercriticalConformalCovariance.Rotation.Field
import SupercriticalLQGUniqueness.B2.WeakStrong.Homothety
import SupercriticalLQGUniqueness.B2.Strong.Bridge

/-! Transport of an LSC metric under a complex rotation. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open LQGMetric
open SupercriticalLQGUniqueness

namespace SupercriticalConformalCovariance.Rotation

/-- The metric obtained by evaluating `M` at inverse-rotated endpoints. -/
def rotMetric (a : ℂ) (ha : a ≠ 0) (M : LSCMetric) : LSCMetric :=
  let e := GaussianLQG.mulCLE a⁻¹ (inv_ne_zero ha)
  ⟨fun p => M (e p.1, e p.2),
    ⟨fun x => M.isExtMetric.1 _,
      fun x y h => e.injective (M.isExtMetric.2.1 _ _ h),
      fun x y => M.isExtMetric.2.2.1 _ _,
      fun x y z => M.isExtMetric.2.2.2 _ _ _⟩,
    M.lowerSemicontinuous.comp
      (show Continuous fun p : ℂ × ℂ => (e p.1, e p.2) by fun_prop)⟩

@[simp] theorem rotMetric_apply (a : ℂ) (ha : a ≠ 0) (M : LSCMetric)
    (p : ℂ × ℂ) :
    rotMetric a ha M p = M (a⁻¹ * p.1, a⁻¹ * p.2) := rfl

private def rotPt (a : ℂ) (ha : a ≠ 0) (M : LSCMetric) :
    (rotMetric a ha M).Space → M.Space :=
  fun z => M.pt (a⁻¹ * (show ℂ from z))

private theorem isometry_rotPt (a : ℂ) (ha : a ≠ 0) (M : LSCMetric) :
    Isometry (rotPt a ha M) :=
  fun _ _ => rfl

private theorem rotPt_comp (a : ℂ) (ha : a ≠ 0) (M : LSCMetric)
    (P : ℝ → ℂ) :
    rotPt a ha M ∘ ((rotMetric a ha M).pt ∘ P) =
      M.pt ∘ fun t => a⁻¹ * P t := rfl

theorem isCurve_rotMetric_iff (a : ℂ) (ha : a ≠ 0) (M : LSCMetric)
    (P : ℝ → ℂ) (s t : ℝ) :
    (rotMetric a ha M).IsCurve P s t ↔
      M.IsCurve (fun v => a⁻¹ * P v) s t := by
  refine and_congr_right fun _ => ?_
  rw [(isometry_rotPt a ha M).isEmbedding.continuousOn_iff, rotPt_comp]

theorem len_rotMetric (a : ℂ) (ha : a ≠ 0) (M : LSCMetric)
    (P : ℝ → ℂ) (s t : ℝ) :
    (rotMetric a ha M).len P s t =
      M.len (fun v => a⁻¹ * P v) s t := by
  change eVariationOn _ _ = eVariationOn _ _
  rw [← rotPt_comp, SupercriticalLQGUniqueness.B2.WeakStrong.eVariationOn_comp_isometry
    (isometry_rotPt a ha M)]

theorem hasUnitSpeedOn_rotMetric_iff (a : ℂ) (ha : a ≠ 0)
    (M : LSCMetric) (P : ℝ → ℂ) (s : Set ℝ) :
    HasUnitSpeedOn ((rotMetric a ha M).pt ∘ P) s ↔
      HasUnitSpeedOn (M.pt ∘ fun v => a⁻¹ * P v) s := by
  rw [← rotPt_comp, SupercriticalLQGUniqueness.B2.WeakStrong.hasUnitSpeedOn_comp_isometry_iff
    (isometry_rotPt a ha M)]

theorem isLengthSpace_rotMetric {M : LSCMetric} (hM : M.IsLengthSpace)
    (a : ℂ) (ha : a ≠ 0) :
    (rotMetric a ha M).IsLengthSpace := by
  intro x y hxy ε hε
  obtain ⟨Q, s, t, hQ, hQs, hQt, hlen⟩ :=
    hM (a⁻¹ * x) (a⁻¹ * y) hxy ε hε
  refine ⟨fun v => a * Q v, s, t, ?_, ?_, ?_, ?_⟩
  · rw [isCurve_rotMetric_iff]
    simpa only [inv_mul_cancel_left₀ ha] using hQ
  · simp only [hQs, mul_inv_cancel_left₀ ha]
  · simp only [hQt, mul_inv_cancel_left₀ ha]
  · rw [len_rotMetric]
    simpa only [inv_mul_cancel_left₀ ha, rotMetric_apply] using hlen

/-- Internal distances transport under the inverse rotation. -/
theorem internal_rotMetric (M : LSCMetric) (a : ℂ) (ha : a ≠ 0)
    (Y Y' : Set ℂ)
    (hY : ∀ z, a⁻¹ * z ∈ Y' ↔ z ∈ Y) (p : Y × Y) :
    (rotMetric a ha M).internal Y p =
      M.internal Y'
        (⟨a⁻¹ * p.1.1, (hY _).2 p.1.2⟩,
         ⟨a⁻¹ * p.2.1, (hY _).2 p.2.2⟩) := by
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun s => le_iInf fun t => le_iInf fun hQ =>
      le_iInf fun hQY => le_iInf fun hQs => le_iInf fun hQt => ?_
    have h1 : (rotMetric a ha M).IsCurve (fun v => a * Q v) s t := by
      rw [isCurve_rotMetric_iff]
      simpa only [inv_mul_cancel_left₀ ha] using hQ
    have h2 : ∀ v ∈ Set.Icc s t, (fun v => a * Q v) v ∈ Y := by
      intro v hv
      apply (hY _).1
      simpa only [inv_mul_cancel_left₀ ha] using hQY v hv
    have h3 : (fun v => a * Q v) s = (p.1 : ℂ) := by
      simp only [hQs, mul_inv_cancel_left₀ ha]
    have h4 : (fun v => a * Q v) t = (p.2 : ℂ) := by
      simp only [hQt, mul_inv_cancel_left₀ ha]
    calc (rotMetric a ha M).internal Y p
        ≤ (rotMetric a ha M).len (fun v => a * Q v) s t :=
          iInf_le_of_le (fun v => a * Q v) <| iInf_le_of_le s <| iInf_le_of_le t <|
            iInf_le_of_le h1 <| iInf_le_of_le h2 <| iInf_le_of_le h3 <|
              iInf_le_of_le h4 le_rfl
      _ = M.len Q s t := by
          rw [len_rotMetric]
          simp only [inv_mul_cancel_left₀ ha]
  · refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP =>
      le_iInf fun hPY => le_iInf fun hPs => le_iInf fun hPt => ?_
    have h1 : M.IsCurve (fun v => a⁻¹ * P v) s t :=
      (isCurve_rotMetric_iff a ha M P s t).1 hP
    have h2 : ∀ v ∈ Set.Icc s t, (fun v => a⁻¹ * P v) v ∈ Y' :=
      fun v hv => (hY _).2 (hPY v hv)
    have h3 : (fun v => a⁻¹ * P v) s = a⁻¹ * (p.1 : ℂ) := by simp only [hPs]
    have h4 : (fun v => a⁻¹ * P v) t = a⁻¹ * (p.2 : ℂ) := by simp only [hPt]
    calc (M.internal Y'
        (⟨a⁻¹ * p.1.1, (hY _).2 p.1.2⟩,
         ⟨a⁻¹ * p.2.1, (hY _).2 p.2.2⟩))
        ≤ M.len (fun v => a⁻¹ * P v) s t :=
          iInf_le_of_le (fun v => a⁻¹ * P v) <| iInf_le_of_le s <| iInf_le_of_le t <|
            iInf_le_of_le h1 <| iInf_le_of_le h2 <| iInf_le_of_le h3 <|
              iInf_le_of_le h4 le_rfl
      _ = (rotMetric a ha M).len P s t := by rw [len_rotMetric]

/-- Weyl scaling commutes with transport by a rotation. -/
theorem weylScale_rotMetric (ξ : ℝ) (M : LSCMetric)
    (a : ℂ) (ha : a ≠ 0) {f g : C(ℂ, ℝ)}
    (hfg : ∀ z, g (a⁻¹ * z) = f z) (p : ℂ × ℂ) :
    weylScale ξ f (rotMetric a ha M) p =
      weylScale ξ g M (a⁻¹ * p.1, a⁻¹ * p.2) := by
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun L => le_iInf fun hQ => le_iInf fun hu =>
      le_iInf fun hQs => le_iInf fun hQt => ?_
    have h1 : (rotMetric a ha M).IsCurve (fun t => a * Q t) 0 L := by
      rw [isCurve_rotMetric_iff]
      simpa only [inv_mul_cancel_left₀ ha] using hQ
    have h2 : HasUnitSpeedOn ((rotMetric a ha M).pt ∘ fun t => a * Q t)
        (Set.Icc 0 L) := by
      rw [hasUnitSpeedOn_rotMetric_iff]
      simpa only [inv_mul_cancel_left₀ ha] using hu
    have h3 : (fun t => a * Q t) 0 = p.1 := by
      simp only [hQs, mul_inv_cancel_left₀ ha]
    have h4 : (fun t => a * Q t) L = p.2 := by
      simp only [hQt, mul_inv_cancel_left₀ ha]
    calc weylScale ξ f (rotMetric a ha M) p
        ≤ ∫⁻ t in Set.Icc 0 L,
            ENNReal.ofReal (Real.exp (ξ * f ((fun t => a * Q t) t))) :=
          iInf_le_of_le (fun t => a * Q t) <| iInf_le_of_le L <|
            iInf_le_of_le h1 <| iInf_le_of_le h2 <| iInf_le_of_le h3 <|
              iInf_le_of_le h4 le_rfl
      _ = ∫⁻ t in Set.Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (Q t))) := by
          refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
          rw [← hfg, inv_mul_cancel_left₀ ha]
  · refine le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hu =>
      le_iInf fun hPs => le_iInf fun hPt => ?_
    have h1 : M.IsCurve (fun t => a⁻¹ * P t) 0 L :=
      (isCurve_rotMetric_iff a ha M P 0 L).1 hP
    have h2 : HasUnitSpeedOn (M.pt ∘ fun t => a⁻¹ * P t) (Set.Icc 0 L) :=
      (hasUnitSpeedOn_rotMetric_iff a ha M P _).1 hu
    have h3 : (fun t => a⁻¹ * P t) 0 = a⁻¹ * p.1 := by simp only [hPs]
    have h4 : (fun t => a⁻¹ * P t) L = a⁻¹ * p.2 := by simp only [hPt]
    calc weylScale ξ g M (a⁻¹ * p.1, a⁻¹ * p.2)
        ≤ ∫⁻ t in Set.Icc 0 L,
            ENNReal.ofReal (Real.exp (ξ * g ((fun t => a⁻¹ * P t) t))) :=
          iInf_le_of_le (fun t => a⁻¹ * P t) <| iInf_le_of_le L <|
            iInf_le_of_le h1 <| iInf_le_of_le h2 <| iInf_le_of_le h3 <|
              iInf_le_of_le h4 le_rfl
      _ = ∫⁻ t in Set.Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
          refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
          rw [hfg]

private def pairRotHomeomorph (a : ℂ) (ha : a ≠ 0) :
    (ℂ × ℂ) ≃ₜ (ℂ × ℂ) :=
  (GaussianLQG.mulCLE a⁻¹ (inv_ne_zero ha)).toHomeomorph.prodCongr
    (GaussianLQG.mulCLE a⁻¹ (inv_ne_zero ha)).toHomeomorph

theorem continuous_rotMetric (a : ℂ) (ha : a ≠ 0) :
    Continuous (rotMetric a ha) := by
  rw [LSCMetric.isInducing_toLSCFun.continuous_iff]
  have e : (LSCMetric.toLSCFun ∘ rotMetric a ha) =
      SupercriticalLQGUniqueness.B2.WeakStrong.lscPull (pairRotHomeomorph a ha) ∘
        LSCMetric.toLSCFun := rfl
  rw [e]
  exact (SupercriticalLQGUniqueness.B2.WeakStrong.continuous_lscPull _).comp
    LSCMetric.isInducing_toLSCFun.continuous

theorem measurable_rotMetric (a : ℂ) (ha : a ≠ 0) :
    Measurable (rotMetric a ha) :=
  (continuous_rotMetric a ha).measurable

/-- The rotated metric assignment from DG Proposition 1.9. -/
def rotatedAssignment (a : ℂ) (ha : a ≠ 0)
    (D : DistC → LSCMetric) : DistC → LSCMetric :=
  fun h => rotMetric a ha (D (GaussianLQG.rotDist a h))

theorem measurable_rotatedAssignment (a : ℂ) (ha : a ≠ 0)
    {D : DistC → LSCMetric} (hD : Measurable D) :
    Measurable (rotatedAssignment a ha D) :=
  (measurable_rotMetric a ha).comp
    (hD.comp (GaussianLQG.measurable_rotDist a))

theorem ae_rotatedAssignment_isLengthSpace
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusCont h P) {a : ℂ} (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D
      (h ω)).IsLengthSpace := by
  have hg := isGFFPlusCont_rotDist hh ha
  filter_upwards [hD.2.1 P (fun ω => GaussianLQG.rotDist a (h ω)) hg] with ω hω
  exact isLengthSpace_rotMetric hω a (GaussianLQG.ne_zero_of_norm_eq_one ha)

theorem ae_rotatedAssignment_weyl
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusCont h P) {a : ℂ} (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ),
      weylScale (ξ : ℝ) f
        (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D (h ω)) =
      (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D
        (addFun (h ω) f)).1 := by
  let ha0 := GaussianLQG.ne_zero_of_norm_eq_one ha
  have hg := isGFFPlusCont_rotDist hh ha
  filter_upwards [hD.2.2.2.1 P (fun ω => GaussianLQG.rotDist a (h ω)) hg]
    with ω hω f
  let g : C(ℂ, ℝ) := f.comp (GaussianLQG.mulCM a)
  have hfg : ∀ z : ℂ, g (a⁻¹ * z) = f z := by
    intro z
    simp only [g, ContinuousMap.comp_apply, GaussianLQG.mulCM_apply,
      mul_inv_cancel_left₀ ha0]
  funext p
  change weylScale (ξ : ℝ) f (rotMetric a ha0 (D (GaussianLQG.rotDist a (h ω)))) p =
    rotMetric a ha0 (D (GaussianLQG.rotDist a (addFun (h ω) f))) p
  rw [weylScale_rotMetric (ξ : ℝ) _ a ha0 hfg,
    rotMetric_apply, rotDist_addFun ha]
  exact congrFun (hω g) (a⁻¹ * p.1, a⁻¹ * p.2)

theorem ae_rotatedAssignment_coord
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsGFFPlusCont h P) {a : ℂ} (ha : ‖a‖ = 1)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D (h ω)).1
        ((r : ℝ) • u + z, (r : ℝ) • v + z) =
      (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D
        (addConst (scaleTranslateDist r z (h ω)) (Q * Real.log (r : ℝ)))).1
        (u, v) := by
  let ha0 := GaussianLQG.ne_zero_of_norm_eq_one ha
  have hg := isGFFPlusCont_rotDist hh ha
  filter_upwards [hD.2.2.2.2.1 P (fun ω => GaussianLQG.rotDist a (h ω)) hg
    r (a⁻¹ * z)] with ω hω u v
  have hf : GaussianLQG.rotDist a
      (addConst (scaleTranslateDist r z (h ω)) (Q * Real.log (r : ℝ))) =
      addConst (scaleTranslateDist r (a⁻¹ * z)
        (GaussianLQG.rotDist a (h ω))) (Q * Real.log (r : ℝ)) := by
    rw [rotDist_addConst ha,
      B2.Strong.scaleTranslateDist_eq_affineComp,
      B2.Strong.scaleTranslateDist_eq_affineComp,
      rotDist_affineComp ha r.2]
  change (D (GaussianLQG.rotDist a (h ω))).1
      (a⁻¹ * ((r : ℝ) • u + z), a⁻¹ * ((r : ℝ) • v + z)) =
    (D (GaussianLQG.rotDist a
      (addConst (scaleTranslateDist r z (h ω)) (Q * Real.log (r : ℝ))))).1
      (a⁻¹ * u, a⁻¹ * v)
  rw [hf]
  have he : ∀ x : ℂ, a⁻¹ * ((r : ℝ) • x + z) =
      (r : ℝ) • (a⁻¹ * x) + a⁻¹ * z := by
    intro x
    rw [Complex.real_smul, Complex.real_smul, mul_add]
    congr 1
    ring
  rw [he u, he v]
  exact hω (a⁻¹ * u) (a⁻¹ * v)


end SupercriticalConformalCovariance.Rotation
