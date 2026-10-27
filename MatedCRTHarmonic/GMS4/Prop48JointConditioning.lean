import MatedCRTHarmonic.GMSAppA.LemmaA1A2
import MatedCRTHarmonic.GMSAppA.TupleIndep
import MatedCRTHarmonic.GMSAppA.Freeze
import MatedCRTHarmonic.GMSAppA.LemmaA3Tuple
import LQGMetric.Field.CircleAvgAffine

/-!
# Joint local conditioning for [18] Proposition 4.8

The local observable in (4.22) depends on two independent whole-plane GFFs, `h` and `hIG`, and
on the two circle averages at the same radius. This file combines the two one-field versions of
[18] Lemma A.2 to condition jointly on that pair. The residual pair is independent of
the pair of circle averages, and the conditional expectation of every integrable measurable
local functional is its average over fresh residual samples with the observed averages frozen.

Source: [18, Proposition 4.8, especially (4.22), and Lemma 4.9]. Lemma A.2 is formalized in
`MatedCRTHarmonic.GMSAppA.LemmaA1A2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open LQGMetric LQGMetric.Blueprint

namespace MatedCRTHarmonic.GMS4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The joint observation of the two circle averages used in [18] (4.22). -/
def prop48JointCircleAverages (h hIG : Ω → DistC) (δ : ℝ) (z : ℂ) (ω : Ω) : ℝ × ℝ :=
  (circleAvg (h ω) δ z, circleAvg (hIG ω) δ z)

/-- The pair of local fields with their respective circle averages subtracted. -/
def prop48JointLocalResidual (h hIG : Ω → DistC) (δ : ℝ) (z : ℂ) (ω : Ω) :
    DistOn (ballO z δ) × DistOn (ballO z δ) :=
  (restrictTo (ballO z δ) (addConst (h ω) (-circleAvg (h ω) δ z)),
    restrictTo (ballO z δ) (addConst (hIG ω) (-circleAvg (hIG ω) δ z)))

/-- The two independent fields, indexed for direct use with `GMSAppA.lemmaA3N`. -/
def prop48FieldFamily (h hIG : Ω → DistC) (i : Fin 2) : Ω → DistC :=
  if i = 0 then h else hIG

/-- The two fields in coordinates `w ↦ r w + z`, retaining their circle averages. -/
def prop48AffineFieldFamily (h hIG : Ω → DistC) (r : ℝ) (z : ℂ)
    (i : Fin 2) (ω : Ω) : DistC :=
  affineComp r z (prop48FieldFamily h hIG i ω)

/-- A whole-plane field seen in coordinates `w ↦ r w + z`, normalized at the unit circle. -/
def prop48AffineNormalizedField (r : ℝ) (z : ℂ) (g : DistC) : DistC :=
  addConst (affineComp r z g) (-circleAvg g r z)

theorem measurable_prop48AffineNormalizedField (r : ℝ) (z : ℂ) :
    Measurable (prop48AffineNormalizedField r z) := by
  refine GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [prop48AffineNormalizedField, GFFInv.addConst_apply]
  exact ((measurable_distOn_apply φ).comp (measurable_affineComp r z)).add
    (((measurable_circleAvg_left r z).neg).const_mul _)

/-- Affine-normalizing a normalized whole-plane GFF preserves its law and normalization. -/
theorem prop48_affineNormalized_isNormalizedWPGFF
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {h : Ω₀ → DistC} (hh : IsNormalizedWPGFF h P₀)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    IsNormalizedWPGFF (fun ω => prop48AffineNormalizedField r z (h ω)) P₀ := by
  have hm : Measurable (fun ω => prop48AffineNormalizedField r z (h ω)) :=
    (measurable_prop48AffineNormalizedField r z).comp hh.1.measurable
  have he : P₀.map (fun ω => prop48AffineNormalizedField r z (h ω)) = P₀.map h :=
    CircleAvg.map_affine_sub_circleAvg hh hr z
  have hG := LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq hm hh.1 he
  refine ⟨hG, ?_⟩
  have hS : MeasurableSet {g : DistC | circleAvg g 1 0 = 0} :=
    measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const
  have hmap : ∀ᵐ g ∂(P₀.map h), circleAvg g 1 0 = 0 :=
    (ae_map_iff hh.1.measurable.aemeasurable hS).2 hh.2
  rw [← he] at hmap
  exact (ae_map_iff hm.aemeasurable hS).1 hmap

/-- The circle in affine coordinates corresponding to the original unit circle still has
zero average. Its center is `-z/r` and its radius is `1/r`. -/
theorem prop48_affine_circle_normalized
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {h : Ω₀ → DistC} (hh : IsNormalizedWPGFF h P₀)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P₀,
      circleAvg (affineComp r z (h ω)) r⁻¹ (-(r⁻¹ : ℂ) * z) = 0 := by
  have hc := CircleAvg.ae_circleAvg_affineComp (hh.1.affineComp hr z)
    (inv_pos.mpr hr) (-(r⁻¹ : ℂ) * z)
  filter_upwards [hc, hh.2] with ω hω hn
  rw [← hω]
  have hcenter : (r : ℂ) * (-(r⁻¹ : ℂ) * z) + z = 0 := by
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    calc
      (r : ℂ) * (-(r⁻¹ : ℂ) * z) + z =
          z - z * ((r : ℂ) * (r : ℂ)⁻¹) := by ring
      _ = 0 := by rw [mul_inv_cancel₀ hrC]; ring
  rw [GM.affineComp_comp (inv_ne_zero hr.ne') hr.ne'
    (-(r⁻¹ : ℂ) * z) z (h ω)]
  simp only [mul_inv_cancel₀ hr.ne', hcenter, GM.affineComp_one_zero]
  exact hn

/-- If the rescaling radius stays inside the unit disk around `z`, the A.3 unit disk
in the rescaled coordinates lies inside the circle corresponding to the original unit circle. -/
theorem prop48_affine_unitBall_subset
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hsmall : r + ‖z‖ < 1) :
    Metric.ball (0 : ℂ) 1 ⊆ Metric.ball (-(r⁻¹ : ℂ) * z) r⁻¹ := by
  apply Metric.ball_subset_ball'
  rw [dist_zero_left, norm_mul, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  change 1 + r⁻¹ * ‖z‖ ≤ r⁻¹
  rw [← one_div, le_div_iff₀ hr]
  calc
    (1 + 1 / r * ‖z‖) * r = r + ‖z‖ := by field_simp [hr.ne']
    _ ≤ 1 := hsmall.le

/-- Applying the same affine coordinate map to independent fields preserves independence. -/
theorem prop48_affine_fields_independent
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {h hIG : Ω₀ → DistC} (hind : IndepFun h hIG P₀)
    (r : ℝ) (z : ℂ) :
    IndepFun (fun ω => affineComp r z (h ω))
      (fun ω => affineComp r z (hIG ω)) P₀ :=
  hind.comp (measurable_affineComp r z) (measurable_affineComp r z)

private def prop48AverageFamily (h hIG : Ω → DistC) (δ : ℝ) (z : ℂ) (i : Fin 2) : Ω → ℝ :=
  fun ω => circleAvg (prop48FieldFamily h hIG i ω) δ z

private def prop48ResidualFamily (h hIG : Ω → DistC) (δ : ℝ) (z : ℂ) (i : Fin 2) :
    Ω → DistOn (ballO z δ) :=
  fun ω => restrictTo (ballO z δ)
    (addConst (prop48FieldFamily h hIG i ω) (-prop48AverageFamily h hIG δ z i ω))

/-- Two independent fields form a two-element independent family. -/
private theorem prop48_fieldFamily_iIndepFun
    {h hIG : Ω → DistC} [IsProbabilityMeasure P] (hind : IndepFun h hIG P) :
    iIndepFun (prop48FieldFamily h hIG) P := by
  classical
  rw [iIndepFun_iff]
  intro s E hE
  by_cases h0 : (0 : Fin 2) ∈ s
  · by_cases h1 : (1 : Fin 2) ∈ s
    · have hs : s = Finset.univ := Finset.eq_univ_iff_forall.mpr fun i => by
        fin_cases i <;> assumption
      subst s
      have hI : (⋂ i ∈ (Finset.univ : Finset (Fin 2)), E i) = E 0 ∩ E 1 := by
        ext ω
        simp
      have hprod : (∏ i ∈ (Finset.univ : Finset (Fin 2)), P (E i)) = P (E 0) * P (E 1) := by
        simp [Fin.prod_univ_succ]
      obtain ⟨A, hA, hAE⟩ := hE 0 (by simp)
      obtain ⟨B, hB, hBE⟩ := hE 1 (by simp)
      rw [hI, hprod]
      have hE0 : MeasurableSet[MeasurableSpace.comap h inferInstance] (E 0) := ⟨A, hA, hAE⟩
      have hE1 : MeasurableSet[MeasurableSpace.comap hIG inferInstance] (E 1) := by
        exact ⟨B, hB, hBE⟩
      have hdep := (IndepFun_iff h hIG P).1 hind (E 0) (E 1) hE0 hE1
      simpa [prop48FieldFamily] using hdep
    · have hs : s = {0} := by
        ext i
        fin_cases i <;> simp_all
      subst s
      simp

  · by_cases h1 : (1 : Fin 2) ∈ s
    · have hs : s = {1} := by
        ext i
        fin_cases i <;> simp_all
      subst s
      simp
    · have hs : s = ∅ := by
        ext i
        fin_cases i <;> simp_all
      subst s
      simp

/-- Appendix A.3 specialized to the independent pair `(h,hIG)` at the unit circle. This is the
two-field estimate used before translating and rescaling the observations in [18, (4.35)].
The exterior and circle-average sigma algebras still refer to the displayed pair of fields. -/
theorem prop48_twoField_lemmaA3
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {h hIG : Ω₀ → DistC}
    (hh : IsNormalizedWPGFF h P₀) (hhIG : IsNormalizedWPGFF hIG P₀)
    (hind : IndepFun h hIG P₀)
    {p p₀ s δ : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs : 0 < s)
    (hδ : 0 < δ) (hδa : δ ≤ GMSAppA.a3aN p p₀ 2)
    {X : Ω₀ → ℝ}
    {F : ((Fin 2 → DistOn (ballO 0 δ)) × (Fin 2 → ℝ)) → ℝ}
    (hF : Measurable F)
    (hX : X =ᵐ[P₀] fun ω => F (GMSAppA.obsN δ (prop48FieldFamily h hIG) ω))
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P₀ ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal
      |P₀[X | GMSAppA.extSigmaN (prop48FieldFamily h hIG)] ω -
        P₀[X | GMSAppA.cSigmaN (prop48FieldFamily h hIG)] ω| ^ p ∂P₀ ≤
      ENNReal.ofReal (GMSAppA.a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) *
            ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P₀ +
          ENNReal.ofReal
              (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P₀) ^ (p / p₀)) := by
  have hfields : ∀ k : Fin 2, IsWholePlaneGFF (prop48FieldFamily h hIG k) P₀ := by
    intro k
    fin_cases k
    · simpa [prop48FieldFamily] using hh.1
    · simpa [prop48FieldFamily] using hhIG.1
  have hnorm : ∀ k : Fin 2, ∀ᵐ ω ∂P₀,
      circleAvg (prop48FieldFamily h hIG k ω) 1 0 = 0 := by
    intro k
    fin_cases k
    · simpa [prop48FieldFamily] using hh.2
    · simpa [prop48FieldFamily] using hhIG.2
  exact GMSAppA.lemmaA3N hp hpp₀ hs hfields (prop48_fieldFamily_iIndepFun hind)
    (Set.Subset.rfl) hnorm hδ (by simpa using hδa) hF hX hXp₀

/-- Appendix A.3 transported to the disk centered at `z` with radius `r`. The circle-average
sigma algebra in these coordinates is the pair of original averages at radius `r`; the exterior
sigma algebra is that of the original fields outside `B_r(z)`. The latter identifications are
proved separately, so this theorem retains the transformed-field notation explicitly. -/
theorem prop48_twoField_lemmaA3_affine
    {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {h hIG : Ω₀ → DistC}
    (hh : IsNormalizedWPGFF h P₀) (hhIG : IsNormalizedWPGFF hIG P₀)
    (hind : IndepFun h hIG P₀)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (hsmall : r + ‖z‖ < 1)
    {p p₀ s δ : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs : 0 < s)
    (hδ : 0 < δ) (hδa : δ ≤ GMSAppA.a3aN p p₀ 2)
    {X : Ω₀ → ℝ}
    {F : ((Fin 2 → DistOn (ballO 0 δ)) × (Fin 2 → ℝ)) → ℝ}
    (hF : Measurable F)
    (hX : X =ᵐ[P₀] fun ω => F (GMSAppA.obsN δ (prop48AffineFieldFamily h hIG r z) ω))
    (hXp₀ : ∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P₀ ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal
      |P₀[X | GMSAppA.extSigmaN (prop48AffineFieldFamily h hIG r z)] ω -
        P₀[X | GMSAppA.cSigmaN (prop48AffineFieldFamily h hIG r z)] ω| ^ p ∂P₀ ≤
      ENNReal.ofReal (GMSAppA.a3C p p₀) *
        (ENNReal.ofReal (δ ^ (s * p)) *
            ∫⁻ ω, ENNReal.ofReal |X ω| ^ p ∂P₀ +
          ENNReal.ofReal
              (Real.exp (-(GMSAppA.a3bN p p₀ 2 / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal |X ω| ^ p₀ ∂P₀) ^ (p / p₀)) := by
  have hfields : ∀ i : Fin 2,
      IsWholePlaneGFF (prop48AffineFieldFamily h hIG r z i) P₀ := by
    intro i
    fin_cases i
    · change IsWholePlaneGFF (fun ω => affineComp r z (h ω)) P₀
      exact hh.1.affineComp hr z
    · change IsWholePlaneGFF (fun ω => affineComp r z (hIG ω)) P₀
      exact hhIG.1.affineComp hr z
  have hind' : iIndepFun (prop48AffineFieldFamily h hIG r z) P₀ := by
    convert prop48_fieldFamily_iIndepFun (prop48_affine_fields_independent hind r z) using 1
    funext i ω
    fin_cases i <;> simp [prop48AffineFieldFamily, prop48FieldFamily]
  have hnorm : ∀ i : Fin 2, ∀ᵐ ω ∂P₀,
      circleAvg (prop48AffineFieldFamily h hIG r z i ω) r⁻¹ (-(r⁻¹ : ℂ) * z) = 0 := by
    intro i
    fin_cases i
    · simpa [prop48AffineFieldFamily, prop48FieldFamily] using
        prop48_affine_circle_normalized hh hr z
    · simpa [prop48AffineFieldFamily, prop48FieldFamily] using
        prop48_affine_circle_normalized hhIG hr z
  exact GMSAppA.lemmaA3N hp hpp₀ hs hfields hind'
    (prop48_affine_unitBall_subset hr z hsmall) hnorm hδ
    (by simpa using hδa) hF hX hXp₀

/-- The joint local residual of two independent normalized whole-plane GFFs is independent of
their two circle averages. This is the reusable joint version of the analytic construction Lemma A.2 needed for
[18] Proposition 4.8. -/
theorem prop48_joint_residual_indep
    {h hIG : Ω → DistC} (hh : IsNormalizedWPGFF h P) (hhIG : IsNormalizedWPGFF hIG P)
    (hind : IndepFun h hIG P) {δ : ℝ} {z : ℂ} (hδ : 0 < δ)
    (hnest : closedBall z δ ⊆ closedBall (0 : ℂ) 1) :
    IndepFun (prop48JointCircleAverages h hIG δ z)
      (prop48JointLocalResidual h hIG δ z) P := by
  let A : Fin 2 → MeasurableSpace Ω := fun i =>
    MeasurableSpace.comap (prop48FieldFamily h hIG i) inferInstance
  let B : Fin 2 → MeasurableSpace Ω := fun i =>
    MeasurableSpace.comap (prop48AverageFamily h hIG δ z i) inferInstance
  let D : Fin 2 → MeasurableSpace Ω := fun i =>
    MeasurableSpace.comap (prop48ResidualFamily h hIG δ z i) inferInstance
  have hP : IsProbabilityMeasure P := hh.1.gaussian.isProbabilityMeasure
  have hAind : iIndep A P := by
    rw [← iIndepFun_iff_iIndep]
    exact prop48_fieldFamily_iIndepFun hind
  have hAle : ∀ i, A i ≤ ‹MeasurableSpace Ω› := fun i =>
    by
      fin_cases i
      · exact hh.1.measurable.comap_le
      · exact hhIG.1.measurable.comap_le
  have hBle : ∀ i, B i ≤ A i := by
    intro i
    fin_cases i
    · have hf : Measurable[MeasurableSpace.comap h inferInstance] h := comap_measurable h
      exact ((measurable_circleAvg_left δ z).comp hf).comap_le
    · have hf : Measurable[MeasurableSpace.comap hIG inferInstance] hIG := comap_measurable hIG
      exact ((measurable_circleAvg_left δ z).comp hf).comap_le
  have hDle : ∀ i, D i ≤ A i := by
    intro i
    fin_cases i
    · have hf : Measurable[MeasurableSpace.comap h inferInstance] h := comap_measurable h
      have ha : Measurable[MeasurableSpace.comap h inferInstance]
          (fun ω => circleAvg (h ω) δ z) := (measurable_circleAvg_left δ z).comp hf
      have hadd : Measurable[MeasurableSpace.comap h inferInstance]
          (fun ω => addConst (h ω) (-circleAvg (h ω) δ z)) :=
        GFFInv.measurable_distC_iff.2 fun φ => by
          simp only [GFFInv.addConst_apply]
          exact ((measurable_distOn_apply φ).comp hf).add (ha.neg.const_mul _)
      have hm : Measurable[MeasurableSpace.comap h inferInstance]
          (prop48ResidualFamily h hIG δ z 0) := by
        change Measurable[MeasurableSpace.comap h inferInstance]
          (fun ω => restrictTo (ballO z δ) (addConst (h ω) (-circleAvg (h ω) δ z)))
        exact (measurable_restrictTo (ballO z δ)).comp hadd
      exact hm.comap_le
    · have hf : Measurable[MeasurableSpace.comap hIG inferInstance] hIG := comap_measurable hIG
      have ha : Measurable[MeasurableSpace.comap hIG inferInstance]
          (fun ω => circleAvg (hIG ω) δ z) := (measurable_circleAvg_left δ z).comp hf
      have hadd : Measurable[MeasurableSpace.comap hIG inferInstance]
          (fun ω => addConst (hIG ω) (-circleAvg (hIG ω) δ z)) :=
        GFFInv.measurable_distC_iff.2 fun φ => by
          simp only [GFFInv.addConst_apply]
          exact ((measurable_distOn_apply φ).comp hf).add (ha.neg.const_mul _)
      have hm : Measurable[MeasurableSpace.comap hIG inferInstance]
          (prop48ResidualFamily h hIG δ z 1) := by
        change Measurable[MeasurableSpace.comap hIG inferInstance]
          (fun ω => restrictTo (ballO z δ) (addConst (hIG ω) (-circleAvg (hIG ω) δ z)))
        exact (measurable_restrictTo (ballO z δ)).comp hadd
      exact hm.comap_le
  have hBD : ∀ i, Indep (B i) (D i) P := by
    intro i
    fin_cases i
    · have hsingle := GMSAppA.lemmaA2_indepFun hh hδ hnest
      have hsingle' : IndepFun (prop48AverageFamily h hIG δ z 0)
          (prop48ResidualFamily h hIG δ z 0) P := by
        change IndepFun (fun ω => circleAvg (h ω) δ z)
          (fun ω => restrictTo (ballO z δ) (addConst (h ω) (-circleAvg (h ω) δ z))) P
        exact hsingle
      exact (IndepFun_iff_Indep _ _ _).1 hsingle'
    · have hsingle := GMSAppA.lemmaA2_indepFun hhIG hδ hnest
      have hsingle' : IndepFun (prop48AverageFamily h hIG δ z 1)
          (prop48ResidualFamily h hIG δ z 1) P := by
        change IndepFun (fun ω => circleAvg (hIG ω) δ z)
          (fun ω => restrictTo (ballO z δ) (addConst (hIG ω) (-circleAvg (hIG ω) δ z))) P
        exact hsingle
      exact (IndepFun_iff_Indep _ _ _).1 hsingle'
  have H := GMSAppA.indep_iSup_iSup_of_iIndep hAind hBle hDle hAle hBD
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left H ?_) ?_
  · refine Measurable.comap_le (Measurable.prodMk ?_ ?_)
    · exact (comap_measurable (prop48AverageFamily h hIG δ z 0)).mono
        (le_iSup B 0) le_rfl
    · exact (comap_measurable (prop48AverageFamily h hIG δ z 1)).mono
        (le_iSup B 1) le_rfl
  · refine Measurable.comap_le (Measurable.prodMk ?_ ?_)
    · exact (comap_measurable (prop48ResidualFamily h hIG δ z 0)).mono
        (le_iSup D 0) le_rfl
    · exact (comap_measurable (prop48ResidualFamily h hIG δ z 1)).mono
        (le_iSup D 1) le_rfl

/-! ### Joint the analytic construction output

The named producer contract below records the joint form of Lemma A.2. It is proved by applying
`GMSAppA.condExp_comp_indep_of_integrable` to the pair of circle averages and the independent pair
of centered local fields, then pushing the residual-pair law through `Measure.map`. This is the
conditional input used in [18] Proposition 4.8 at and Lemma 4.9 at. -/

/-- **the analytic construction joint Lemma A.2 output required by Proposition 4.8.** The residual-independence part
is proved in `prop48_joint_residual_indep`. This record names the remaining conditional-law output:
for each measurable integrable functional of the two local fields, its conditional expectation
given both circle averages is the expectation over a fresh residual pair, with each observed
average added back to its matching field. -/
structure Prop48JointConditioningOutput
    {h hIG : Ω → DistC} [IsProbabilityMeasure P]
    (hh : IsNormalizedWPGFF h P) (hhIG : IsNormalizedWPGFF hIG P)
    (hind : IndepFun h hIG P) {δ : ℝ} {z : ℂ} (hδ : 0 < δ)
    (hnest : closedBall z δ ⊆ closedBall (0 : ℂ) 1) : Prop where
  condExp_integrable : ∀ {F : DistOn (ballO z δ) × DistOn (ballO z δ) → ℝ},
    Measurable F →
    Integrable (fun ω => F
      (restrictTo (ballO z δ) (h ω), restrictTo (ballO z δ) (hIG ω))) P →
      P[(fun ω => F (restrictTo (ballO z δ) (h ω), restrictTo (ballO z δ) (hIG ω))) |
        MeasurableSpace.comap (prop48JointCircleAverages h hIG δ z) inferInstance] =ᵐ[P]
        fun ω => ∫ ω', F
          (GMSAppA.addConstOn (ballO z δ)
            (prop48JointLocalResidual h hIG δ z ω').1
            (prop48JointCircleAverages h hIG δ z ω).1,
            GMSAppA.addConstOn (ballO z δ)
            (prop48JointLocalResidual h hIG δ z ω').2
            (prop48JointCircleAverages h hIG δ z ω).2) ∂P

/-- The joint conditional-law output follows by applying the integrable freezing lemma to the
pair of circle averages and the independent pair of centered local fields. -/
theorem prop48_joint_conditioning_output
    {h hIG : Ω → DistC} [IsProbabilityMeasure P]
    (hh : IsNormalizedWPGFF h P) (hhIG : IsNormalizedWPGFF hIG P)
    (hind : IndepFun h hIG P) {δ : ℝ} {z : ℂ} (hδ : 0 < δ)
    (hnest : closedBall z δ ⊆ closedBall (0 : ℂ) 1) :
    Prop48JointConditioningOutput hh hhIG hind hδ hnest := by
  let S : Ω → ℝ × ℝ := prop48JointCircleAverages h hIG δ z
  let R : Ω → DistOn (ballO z δ) × DistOn (ballO z δ) :=
    prop48JointLocalResidual h hIG δ z
  have hSh : Measurable fun ω => circleAvg (h ω) δ z :=
    (measurable_circleAvg_left δ z).comp hh.1.measurable
  have hShIG : Measurable fun ω => circleAvg (hIG ω) δ z :=
    (measurable_circleAvg_left δ z).comp hhIG.1.measurable
  have hS : Measurable S := hSh.prodMk hShIG
  have hRh : Measurable fun ω =>
      restrictTo (ballO z δ) (addConst (h ω) (-circleAvg (h ω) δ z)) :=
    (measurable_restrictTo (ballO z δ)).comp (hh.1.addConst hSh.neg).measurable
  have hRhIG : Measurable fun ω =>
      restrictTo (ballO z δ) (addConst (hIG ω) (-circleAvg (hIG ω) δ z)) :=
    (measurable_restrictTo (ballO z δ)).comp (hhIG.1.addConst hShIG.neg).measurable
  have hR : Measurable R := hRh.prodMk hRhIG
  have hSR : Indep (MeasurableSpace.comap S inferInstance)
      (MeasurableSpace.comap R inferInstance) P := by
    rw [← IndepFun_iff_Indep]
    exact prop48_joint_residual_indep hh hhIG hind hδ hnest
  constructor
  intro F hF hFi
  let G : (ℝ × ℝ) × (DistOn (ballO z δ) × DistOn (ballO z δ)) → ℝ := fun p =>
    F (GMSAppA.addConstOn (ballO z δ) p.2.1 p.1.1,
      GMSAppA.addConstOn (ballO z δ) p.2.2 p.1.2)
  have hG : Measurable G := by
    apply hF.comp
    apply Measurable.prodMk
    · exact (GMSAppA.measurable_addConstOn (ballO z δ)).comp
        ((measurable_fst.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_snd))
    · exact (GMSAppA.measurable_addConstOn (ballO z δ)).comp
        ((measurable_snd.comp measurable_fst).prodMk
          (measurable_snd.comp measurable_snd))
  have hdec : (fun ω => F
      (restrictTo (ballO z δ) (h ω), restrictTo (ballO z δ) (hIG ω))) =
      fun ω => G (S ω, R ω) := by
    funext ω
    apply congrArg F
    apply Prod.ext
    · simp only [S, R, prop48JointCircleAverages, prop48JointLocalResidual]
      rw [← GMSAppA.restrictTo_addConst_eq_addConstOn, GFFLaw.addConst_addConst,
        neg_add_cancel, GFFLaw.addConst_zero']
    · simp only [S, R, prop48JointCircleAverages, prop48JointLocalResidual]
      rw [← GMSAppA.restrictTo_addConst_eq_addConstOn, GFFLaw.addConst_addConst,
        neg_add_cancel, GFFLaw.addConst_zero']
  rw [hdec]
  have key := GMSAppA.condExp_comp_indep_of_integrable
    (𝓖 := MeasurableSpace.comap S inferInstance) (S := S) (R := R) (f := G)
    hS.comap_le (comap_measurable S) hR hSR hG (hdec ▸ hFi)
  refine key.trans (ae_of_all _ fun ω => ?_)
  change (∫ r, G (S ω, r) ∂(P.map R)) = _
  rw [integral_map (f := fun r => G (S ω, r)) hR.aemeasurable
    (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]

/-- The nonnegative integrable specialization of the named joint conditioning output, used for
The localized density functionals in [18] (4.22)--(4.25). -/
theorem Prop48JointConditioningOutput.condExp_nonneg
    {h hIG : Ω → DistC} [IsProbabilityMeasure P]
    {hh : IsNormalizedWPGFF h P} {hhIG : IsNormalizedWPGFF hIG P}
    {hind : IndepFun h hIG P} {δ : ℝ} {z : ℂ} {hδ : 0 < δ}
    {hnest : closedBall z δ ⊆ closedBall (0 : ℂ) 1}
    (O : Prop48JointConditioningOutput hh hhIG hind hδ hnest)
    {F : DistOn (ballO z δ) × DistOn (ballO z δ) → ℝ} (hF : Measurable F)
    (_hFnonneg : ∀ x, 0 ≤ F x)
    (hFi : Integrable (fun ω => F
      (restrictTo (ballO z δ) (h ω), restrictTo (ballO z δ) (hIG ω))) P) :
    P[(fun ω => F (restrictTo (ballO z δ) (h ω), restrictTo (ballO z δ) (hIG ω))) |
      MeasurableSpace.comap (prop48JointCircleAverages h hIG δ z) inferInstance] =ᵐ[P]
      fun ω => ∫ ω', F
        (GMSAppA.addConstOn (ballO z δ)
          (prop48JointLocalResidual h hIG δ z ω').1
          (prop48JointCircleAverages h hIG δ z ω).1,
          GMSAppA.addConstOn (ballO z δ)
          (prop48JointLocalResidual h hIG δ z ω').2
          (prop48JointCircleAverages h hIG δ z ω).2) ∂P :=
  O.condExp_integrable hF hFi

end MatedCRTHarmonic.GMS4
