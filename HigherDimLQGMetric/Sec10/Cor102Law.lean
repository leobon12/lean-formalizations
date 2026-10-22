import HigherDimLQGMetric.Sec10.Cor102Transform
import HigherDimLQGMetric.Core.MainInputs
import HigherDimLQGMetric.Sec10.Pure
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Thm16.CompactPath
import HigherDimLQGMetric.Sharp.TightLower
import HigherDimLQGMetric.Sharp.TightUpper

/-!
# The dilation factor and the normalized metric law

Sharp weak uniqueness makes each fixed dilation a deterministic multiple of the original
assignment. The normalized metric law identifies the multiple at every scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology
open HigherDimLFPP (Rd e₁)
open scoped ENNReal

variable {d : ℕ}

/-- Sharp weak uniqueness applied to a fixed dilation. -/
theorem s8c_transform_proportional (h14s : Theorem14SharpStmt)
    (hd : 3 ≤ d) {ξ Q r : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q) (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D) :
    ∃ a : ℝ, 0 < a ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
          (s8c_transform ξ Q r hr D (addFun (h ω) f)).1 (u, v) =
            a * (D (addFun (h ω) f)).1 (u, v) :=
  h14s d ξ Q hd hξ hQ D (s8c_transform ξ Q r hr D)
    hD (s8c_transform_sharp (by omega : 2 ≤ d) hr hD)

/-- The transformed metric of the recentered rescaled LGF equals its original sharp normalized
metric. Only constant Weyl scaling is used here. -/
theorem s8c_ae_normalized_eq_transform {ξ Q r : ℝ} (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r =
      (s8c_transform ξ Q r hr D (s8a_pureRescaled h r ω)).1 := by
  filter_upwards [hD.ae_apply_addFun_const hh.isLGFPlusCont] with ω hw
  ext p
  have he : affineComp r⁻¹ 0 (s8a_pureRescaled h r ω) =
      addConst (h ω) (-sphereAvg (h ω) r 0) := by
    unfold s8a_pureRescaled
    rw [affineComp_addConst (inv_pos.mpr hr)]
    have hcancel := affineComp_inv_affineComp hr.ne' (0 : Rd d) (h ω)
    simp only [smul_zero, neg_zero] at hcancel
    rw [hcancel]
  have hc := hw (-sphereAvg (h ω) r 0) (r • p.1) (r • p.2)
  rcases p with ⟨u,v⟩
  rw [s8c_transform_apply, he]
  simp only [normalizedAtScale, ContinuousMap.smul_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul,
    addConst, hc]
  ring_nf

/-- For a normalized LGF, recentering after dilation preserves the law of the field. -/
theorem s8c_map_pureRescaled_eq_self (hd : 2 ≤ d)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {r : ℝ} (hr : 0 < r) :
    P.map (s8a_pureRescaled h r) = P.map h := by
  rw [s8a_map_pureRescaled_eq hd hh.1 hr]
  apply Measure.map_congr
  filter_upwards [hh.2] with ω hω
  simp only [hω, neg_zero, addConst_zero]

/-- The normalized metric at scale `r` has the law of `a` times the unit metric. -/
theorem s8c_normalized_law (hd : 2 ≤ d) {ξ Q r a : ℝ} (hr : 0 < r)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    (ha : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
        (s8c_transform ξ Q r hr D (addFun (h ω) f)).1 (u, v) =
          a * (D (addFun (h ω) f)).1 (u, v))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    P.map (fun ω => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r) =
      P.map (fun ω => a • (D (h ω)).1) := by
  have hg : IsWholeSpaceLGF (s8a_pureRescaled h r) P :=
    s8a_pureRescaled_isLGF hh.1 hr
  have hae : ∀ᵐ ω ∂P,
      normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r =
        a • (D (s8a_pureRescaled h r ω)).1 := by
    filter_upwards [s8c_ae_normalized_eq_transform hr hD P h hh.1,
      ha P (s8a_pureRescaled h r) hg.isLGFPlusCont] with ω hnorm hfactor
    rw [hnorm]
    apply ContinuousMap.ext
    rintro ⟨u,v⟩
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, addFun_zero] using
      hfactor 0 u v
  rw [Measure.map_congr hae]
  let M : DistRd d → C(Rd d × Rd d, ℝ) := fun g => a • (D g).1
  have hMm : Measurable M :=
    (continuous_const_smul a).measurable.comp (measurable_subtype_coe.comp hD.measurable)
  change P.map (M ∘ s8a_pureRescaled h r) = P.map (M ∘ h)
  rw [← Measure.map_map hMm hg.measurable,
    s8c_map_pureRescaled_eq_self hd h hh hr,
    Measure.map_map hMm hh.1.measurable]

end HigherDimLQGMetric
