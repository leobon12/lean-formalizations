import HigherDimLQGMetric.Sec10.Cor102Field
import HigherDimLQGMetric.Sec10.Cor102Tight
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric
import HigherDimLQGMetric.Sharp.ScaledMetric
import HigherDimLQGMetric.Metric.WeylBasic
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Sphere.Scaling
import HigherDimLQGMetric.Field.Measurable

/-!
# Fixed dilation of a sharp weak metric assignment

For a fixed positive `r`, the transformed assignment is
`r^(-ξQ) D_(g(·/r))(r·,r·)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set TopologicalSpace
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem s8c_pow_pos {r ξ Q : ℝ} (hr : 0 < r) :
    0 < (r ^ (ξ * Q))⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hr _)

/-- The fixed dilation of an assignment. -/
def s8c_transform (ξ Q : ℝ) (r : ℝ) (hr : 0 < r)
    (D : DistRd d → ContMetric d) : DistRd d → ContMetric d :=
  fun g => ((D (affineComp r⁻¹ 0 g)).affine r hr.ne' 0).smul
    (r ^ (ξ * Q))⁻¹ (s8c_pow_pos hr)

theorem s8c_transform_apply (ξ Q : ℝ) {r : ℝ} (hr : 0 < r)
    (D : DistRd d → ContMetric d) (g : DistRd d) (u v : Rd d) :
    (s8c_transform ξ Q r hr D g).1 (u,v) =
      (r ^ (ξ * Q))⁻¹ * (D (affineComp r⁻¹ 0 g)).1 (r • u, r • v) := by
  simp only [s8c_transform, ContMetric.smul_apply, ContMetric.affine_apply, add_zero]

theorem s8c_transform_measurable (ξ Q : ℝ) {r : ℝ} (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : Measurable D) :
    Measurable (s8c_transform ξ Q r hr D) := by
  apply Measurable.subtype_mk
  exact (continuous_const_smul _).measurable.comp
    ((ContinuousMap.continuous_precomp _).measurable.comp
      (measurable_subtype_coe.comp
        (hD.comp (measurable_affineComp r⁻¹ 0))))

theorem s8c_transform_length {ξ Q r : ℝ} (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, (s8c_transform ξ Q r hr D (h ω)).IsLength := by
  have hg := s8c_lgfPlusCont_affine hh (inv_pos.mpr hr) 0
  filter_upwards [hD.length P (fun ω => affineComp r⁻¹ 0 (h ω)) hg] with ω hω
  exact ContMetric.isLength_smul (s8c_pow_pos hr)
    (ContMetric.isLength_affine hr.ne' 0 hω)

private theorem s8c_image_set {r : ℝ} (hr : r ≠ 0) (U : Set (Rd d)) :
    (fun x : Rd d => r • x + 0) '' U =
      {y : Rd d | r⁻¹ • y + 0 ∈ U} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change r⁻¹ • (r • x + 0) + 0 ∈ U
    simpa only [add_zero, inv_smul_smul₀ hr] using hx
  · intro hy
    change r⁻¹ • y + 0 ∈ U at hy
    refine ⟨r⁻¹ • y, (by simpa only [add_zero] using hy), ?_⟩
    simp only [add_zero, smul_inv_smul₀ hr]

theorem s8c_transform_locality {ξ Q r : ℝ} (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P)
    (U : TopologicalSpace.Opens (Rd d)) :
    ∃ F : DistOn U → (Rd d → Rd d → ℝ≥0∞), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
        (s8c_transform ξ Q r hr D (h ω)).internal U z w =
          F (restrictTo U (h ω)) z w := by
  let V : Opens (Rd d) := preOpens r⁻¹ 0 U
  have hg := s8c_lgfPlusCont_affine hh (inv_pos.mpr hr) 0
  obtain ⟨G, hGm, hG⟩ := hD.locality P
    (fun ω => affineComp r⁻¹ 0 (h ω)) hg V
  refine ⟨fun k z w => ENNReal.ofReal (r ^ (ξ * Q))⁻¹ *
    G (distAffine (inv_ne_zero hr.ne') 0 k) (r • z) (r • w), ?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro z
    apply measurable_pi_iff.mpr
    intro w
    exact measurable_const.mul
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        (hGm.comp (measurable_distAffine (inv_ne_zero hr.ne') 0 U))))
  · filter_upwards [hG] with ω hω z hz w hw
    rw [s8c_transform, ContMetric.internal_smul,
      ContMetric.internal_affine hr.ne' 0,
      s8c_image_set hr.ne', show
        ({y : Rd d | r⁻¹ • y + 0 ∈ (U : Set (Rd d))} : Set (Rd d)) = V from rfl]
    have hzV : r • z + 0 ∈ V := by
      simp only [V, mem_preOpens, add_zero, inv_smul_smul₀ hr.ne']
      exact hz
    have hwV : r • w + 0 ∈ V := by
      simp only [V, mem_preOpens, add_zero, inv_smul_smul₀ hr.ne']
      exact hw
    rw [hω (r • z + 0) hzV (r • w + 0) hwV]
    rw [restrictTo_affineComp (inv_ne_zero hr.ne') 0 U]
    simp only [add_zero]

theorem s8c_transform_weyl {ξ Q r : ℝ} (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ z w : Rd d,
      weylScale ξ f (s8c_transform ξ Q r hr D (h ω)) z w =
        ENNReal.ofReal ((s8c_transform ξ Q r hr D (addFun (h ω) f)).1 (z, w)) := by
  have hg := s8c_lgfPlusCont_affine hh (inv_pos.mpr hr) 0
  filter_upwards [hD.weyl P (fun ω => affineComp r⁻¹ 0 (h ω)) hg] with ω hω f z w
  let f' : C(Rd d, ℝ) := f.comp (affinePt r⁻¹ 0)
  have hf : f'.comp (ContMetric.affineMap r 0) = f := by
    ext x
    simp only [f', ContinuousMap.comp_apply, affinePt_apply,
      ContMetric.affineMap_apply, add_zero, inv_smul_smul₀ hr.ne']
  calc
    weylScale ξ f (s8c_transform ξ Q r hr D (h ω)) z w =
        ENNReal.ofReal (r ^ (ξ * Q))⁻¹ *
          weylScale ξ f' (D (affineComp r⁻¹ 0 (h ω))) (r • z) (r • w) := by
            rw [← hf]
            simp only [s8c_transform, weylScale_smul,
              weylScale_affine hr.ne' 0, ContMetric.affineMap_apply, add_zero]
    _ = ENNReal.ofReal (r ^ (ξ * Q))⁻¹ *
          ENNReal.ofReal ((D (addFun (affineComp r⁻¹ 0 (h ω)) f')).1 (r • z, r • w)) := by
            rw [hω f' (r • z) (r • w)]
    _ = ENNReal.ofReal ((s8c_transform ξ Q r hr D (addFun (h ω) f)).1 (z, w)) := by
          rw [s8c_transform_apply, affineComp_addFun (inv_pos.mpr hr)]
          exact (ENNReal.ofReal_mul (s8c_pow_pos hr).le).symm

theorem s8c_transform_translation {ξ Q r : ℝ} (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P) (z : Rd d) :
    ∀ᵐ ω ∂P, ∀ u v : Rd d,
      (s8c_transform ξ Q r hr D (affineComp 1 z (h ω))).1 (u, v) =
        (s8c_transform ξ Q r hr D (h ω)).1 (u + z, v + z) := by
  have hg := s8c_lgfPlusCont_affine hh (inv_pos.mpr hr) 0
  filter_upwards [hD.translation P (fun ω => affineComp r⁻¹ 0 (h ω)) hg (r • z)]
    with ω hω u v
  have he : affineComp r⁻¹ 0 (affineComp 1 z (h ω)) =
      affineComp 1 (r • z) (affineComp r⁻¹ 0 (h ω)) := by
    rw [affineComp_affineComp, affineComp_affineComp]
    simp only [one_mul, mul_one, smul_zero, zero_add,
      inv_smul_smul₀ hr.ne', add_zero]
  rw [s8c_transform_apply, s8c_transform_apply, he,
    hω (r • u) (r • v)]
  simp only [smul_add]

/-- The transformed sharp normalized metric is the original one at scale `r*s`. -/
theorem s8c_normalized_transform {ξ Q r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hd : 2 ≤ d) {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P,
      normalizedAtScale ξ (s8c_transform ξ Q r hr D)
        (fun t => t ^ (ξ * Q)) (h ω) s =
      normalizedAtScale ξ D (fun t => t ^ (ξ * Q))
        (affineComp r⁻¹ 0 (h ω)) (r * s) := by
  filter_upwards [hh.ae_sphereAvg_affineComp hd (inv_pos.mpr hr) 0
    (mul_pos hr hs) 0] with ω hω
  have hrpow : (r * s) ^ (ξ * Q) = r ^ (ξ * Q) * s ^ (ξ * Q) :=
    Real.mul_rpow hr.le hs.le
  have hmul : r⁻¹ * (r * s) = s := by field_simp
  ext p
  simp only [normalizedAtScale, ContinuousMap.smul_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul,
    s8c_transform_apply]
  rw [hω, hmul, smul_zero, zero_add, hrpow]
  simp only [smul_smul, mul_inv_rev]
  ring

/-- Fixed dilation preserves the sharp weak class. -/
theorem s8c_transform_sharp (hd : 2 ≤ d) {ξ Q r : ℝ} (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D) :
    IsSharpWeakExpMetric d ξ Q (s8c_transform ξ Q r hr D) := by
  let hD' : IsWeakExpMetric d ξ D (fun s => s ^ (ξ * Q)) := hD
  refine ⟨s8c_transform_measurable ξ Q hr hD'.measurable,
    s8c_transform_length hr hD, s8c_transform_locality hr hD,
    s8c_transform_weyl hr hD, s8c_transform_translation hr hD,
    ?_, ?_, ?_⟩
  · exact fun s hs => Real.rpow_pos_of_pos hs _
  · intro Ω _ P _ h hh R hR
    let g : Ω → DistRd d := fun ω => affineComp r⁻¹ 0 (h ω)
    have hg : IsLGFPlusCont g P := s8c_lgfPlusCont_affine hh (inv_pos.mpr hr) 0
    have hT := hD'.tight P g hg (r * R) (mul_pos hr hR)
    apply s8c_tightOver_reindex (b := fun s => r * s) hT
    · intro s hs
      exact ⟨mul_pos hr hs.1, mul_lt_mul_of_pos_left hs.2 hr⟩
    · intro s hs
      exact s8c_normalized_transform hr hs.1 hd h hh
  · intro Ω _ P _ h hh
    let g : Ω → DistRd d := fun ω => affineComp r⁻¹ 0 (h ω)
    have hg : IsLGFPlusBddCont g P := s8c_lgfPlusBdd_affine hh (inv_pos.mpr hr) 0
    have hT := hD'.tight_bdd P g hg
    apply s8c_tightOver_reindex (b := fun s => r * s) hT
    · intro s hs
      exact mul_pos hr hs
    · intro s hs
      exact s8c_normalized_transform hr hs hd h hh.isLGFPlusCont

end HigherDimLQGMetric
