import HigherDimLQGMetric.Sec10.Basic
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Sphere.Scaling
import HigherDimLQGMetric.Events.TightLaw
import HigherDimLQGMetric.Select.MetricBorel

/-!
# Normalized scaling of a strong assignment on an LGF

The exact covariance and constant Weyl rule reduce the normalized metric at any scale to the
metric of a normalized rescaled field. This is the pure-field part of Lemma 10.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- The field obtained by dilation and subtraction of its scale-average. -/
def s8a_pureRescaled (h : Ω → DistRd d) (r : ℝ) (ω : Ω) : DistRd d :=
  addConst (affineComp r 0 (h ω)) (-sphereAvg (h ω) r 0)

/-- An LGF stays an LGF after dilation and random additive recentering. -/
theorem s8a_pureRescaled_isLGF (hh : IsWholeSpaceLGF h P) {r : ℝ} (hr : 0 < r) :
    IsWholeSpaceLGF (s8a_pureRescaled h r) P := by
  unfold s8a_pureRescaled
  exact (hh.affineComp hr 0).addConst
    (((measurable_sphereAvg_left r 0).comp hh.measurable).neg)

/-- Exact covariance removes the sharp normalizer and the scale sphere-average. -/
theorem IsStrongExpMetric.ae_normalizedAtScale_pure
    [IsProbabilityMeasure P] (hD : IsStrongExpMetric d ξ Q D) (hh : IsWholeSpaceLGF h P)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r =
      (D (s8a_pureRescaled h r ω)).1 := by
  let g := s8a_pureRescaled h r
  have hg : IsWholeSpaceLGF g P := s8a_pureRescaled_isLGF hh hr
  filter_upwards [hD.coord P h hh.isLGFPlusCont r hr 0,
    hD.ae_apply_addFun_const hg.isLGFPlusCont] with ω hc hw
  ext ⟨u, v⟩
  have hc' := hc u v
  have hw' := hw (sphereAvg (h ω) r 0 + Q * Real.log r) u v
  have he : addConst (g ω) (sphereAvg (h ω) r 0 + Q * Real.log r) =
      addConst (affineComp r 0 (h ω)) (Q * Real.log r) := by
    unfold g s8a_pureRescaled
    rw [addConst_addConst]
    congr 1
    ring
  rw [addFun_const, he] at hw'
  simp only [normalizedAtScale, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, smul_eq_mul, add_zero] at *
  rw [hc', hw']
  have he' : (r ^ (ξ * Q))⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r 0) *
      Real.exp (ξ * (sphereAvg (h ω) r 0 + Q * Real.log r)) = 1 := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    rw [show -(Real.log r * (ξ * Q)) + -ξ * sphereAvg (h ω) r 0 +
      ξ * (sphereAvg (h ω) r 0 + Q * Real.log r) = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, he', one_mul]

/-- Every recentered rescaling of an LGF has the same law. -/
theorem s8a_map_pureRescaled_eq (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r : ℝ} (hr : 0 < r) :
    P.map (s8a_pureRescaled h r) =
      P.map (fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)) := by
  have ha := hh.ae_sphereAvg_affineComp hd hr 0 one_pos 0
  have hm : P.map (s8a_pureRescaled h r) =
      P.map (fun ω => addConst (affineComp r 0 (h ω))
        (-sphereAvg (affineComp r 0 (h ω)) 1 0)) := by
    apply Measure.map_congr
    filter_upwards [ha] with ω hω
    simp only [s8a_pureRescaled, hω, mul_one, smul_zero, zero_add]
  rw [hm]
  exact map_normalizedLGF_eq hd (hh.affineComp hr 0) hh

/-- For a pure LGF, the normalized metrics at all positive scales have one common law. -/
theorem IsStrongExpMetric.map_normalizedAtScale_pure_eq (hd : 2 ≤ d)
    [IsProbabilityMeasure P] (hD : IsStrongExpMetric d ξ Q D) (hh : IsWholeSpaceLGF h P)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    P.map (fun ω => normalizedAtScale ξ D (fun t => t ^ (ξ * Q)) (h ω) r) =
      P.map (fun ω => normalizedAtScale ξ D (fun t => t ^ (ξ * Q)) (h ω) s) := by
  rw [Measure.map_congr (hD.ae_normalizedAtScale_pure hh hr),
    Measure.map_congr (hD.ae_normalizedAtScale_pure hh hs)]
  have hDm : Measurable fun g : DistRd d => (D g).1 :=
    measurable_subtype_coe.comp hD.measurable
  change P.map ((fun g : DistRd d => (D g).1) ∘ s8a_pureRescaled h r) =
    P.map ((fun g : DistRd d => (D g).1) ∘ s8a_pureRescaled h s)
  rw [← Measure.map_map hDm (s8a_pureRescaled_isLGF hh hr).measurable,
    ← Measure.map_map hDm (s8a_pureRescaled_isLGF hh hs).measurable,
    s8a_map_pureRescaled_eq hd hh hr, s8a_map_pureRescaled_eq hd hh hs]

/-- For a pure LGF, the sharp normalized metrics form a constant-law tight family. -/
theorem IsStrongExpMetric.tightOver_pure (hd : 2 ≤ d)
    [IsProbabilityMeasure P] (hD : IsStrongExpMetric d ξ Q D)
    (hh : IsWholeSpaceLGF h P) :
    TightOver P (fun r ω => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r)
      (Set.Ioi 0) := by
  let X : ℝ → Ω → C(Rd d × Rd d, ℝ) :=
    fun r ω => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) r
  have hm : ∀ r, Measurable (X r) := by
    intro r
    have hsc := (measurable_scaledField (ξ := ξ) hD.measurable (fun s => s ^ (ξ * Q)) r 0).comp
      hh.measurable
    have he : X r = scaledField ξ D (fun s => s ^ (ξ * Q)) r 0 ∘ h := by
      funext ω
      exact (scaledField_zero ξ D (fun s => s ^ (ξ * Q)) r (h ω)).symm
    rw [he]
    exact hsc
  let μ₀ : Measure C(Rd d × Rd d, ℝ) := P.map (X 1)
  have hlaw : ∀ r ∈ Set.Ioi (0 : ℝ), P.map (X r) = μ₀ := by
    intro r hr
    exact hD.map_normalizedAtScale_pure_eq hd hh hr one_pos
  have hset : {μ : Measure C(Rd d × Rd d, ℝ) |
      ∃ r ∈ Set.Ioi (0 : ℝ), μ = P.map (X r)} = {μ₀} := by
    ext μ
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hlaw r hr
    · rintro rfl
      exact ⟨1, by simp, (hlaw 1 (by simp)).symm⟩
  refine ⟨fun r _ => (hm r).aemeasurable, ?_, ?_⟩
  · rw [hset]
    exact isTightMeasureSet_singleton
  · intro μ hμ
    have hsub : {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ r ∈ Set.Ioi (0 : ℝ),
          (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (X r)} ⊆
        {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
          (ν : Measure C(Rd d × Rd d, ℝ)) = μ₀} := by
      rintro ν ⟨r, hr, hν⟩
      exact hν.trans (hlaw r hr)
    have hcl : IsClosed {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        (ν : Measure C(Rd d × Rd d, ℝ)) = μ₀} :=
      Set.Subsingleton.isClosed fun ν₁ h₁ ν₂ h₂ =>
        ProbabilityMeasure.toMeasure_injective (h₁.trans h₂.symm)
    have hμ' : (μ : Measure C(Rd d × Rd d, ℝ)) = μ₀ :=
      closure_minimal hsub hcl hμ
    rw [hμ', show μ₀ = P.map ((fun g : DistRd d => (D g).1) ∘ s8a_pureRescaled h 1) by
      change P.map (fun ω => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) 1) = _
      rw [Measure.map_congr (hD.ae_normalizedAtScale_pure hh one_pos)]
      rfl]
    exact (ae_map_iff (μ := P) (f := fun ω => (D (s8a_pureRescaled h 1 ω)).1)
      ((measurable_subtype_coe.comp hD.measurable).comp
        (s8a_pureRescaled_isLGF hh one_pos).measurable).aemeasurable
      (measurableSet_isContinuousMetric_select d)).2 (ae_of_all _ fun ω => (D _).2)

end HigherDimLQGMetric
