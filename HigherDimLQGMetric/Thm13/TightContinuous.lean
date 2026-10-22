import HigherDimLQGMetric.Thm13.PureCompact

/-! Weak Axiom V for arbitrary continuous perturbations on bounded scale intervals. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 600000

noncomputable section

open MeasureTheory Set Topology Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_pure_compact_of_normalized
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ)
    (D : DistRd d → ContMetric d) (hDm : Measurable D)
    (hN : L8NormalizedWeyl ξ D)
    (c : ℝ → ℝ) (hc : ∀ r, 0 < r → 0 < c r)
    (hcan : TightFamily (normLGFLaw d)
      (fun r g => normalizedAtScale ξ D c g r) (Ioi 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set C(Rd d × Rd d, ℝ), IsCompact K ∧
      K ⊆ {M | IsContinuousMetric M} ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d),
        IsNormalizedLGF h P → ∀ r ∈ Ioi (0 : ℝ),
          (P.map (fun ω => normalizedAtScale ξ D c (h ω) r)) Kᶜ ≤ ε := by
  let P₀ : Measure (DistRd d) := normLGFLaw d
  letI : IsProbabilityMeasure P₀ := (normLGFLaw_spec_holds d hd).1
  have hh₀ : IsNormalizedLGF id P₀ := (normLGFLaw_spec_holds d hd).2.1
  have hlen₀ : ∀ᵐ g ∂P₀, (D g).IsLength :=
    (hN P₀ id hh₀).mono fun g ⟨hD, _⟩ => hD
  have hLen : ∀ r ∈ Ioi (0 : ℝ), ∀ᵐ g ∂P₀,
      ∃ M : ContMetric d, M.IsLength ∧
        M.1 = normalizedAtScale ξ D c g r := by
    intro r hr
    filter_upwards [hlen₀] with g hDg
    let a : ℝ := (c r)⁻¹ * Real.exp (-ξ * sphereAvg g r 0)
    have ha : 0 < a := mul_pos (inv_pos.mpr (hc r hr)) (Real.exp_pos _)
    let M : ContMetric d := ((D g).affine r hr.ne' 0).smul a ha
    refine ⟨M, ContMetric.isLength_smul ha
      (ContMetric.isLength_affine hr.ne' 0 hDg), ?_⟩
    ext p
    simp only [M, a, ContMetric.smul_apply, ContMetric.affine_apply,
      normalizedAtScale, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, smul_eq_mul, add_zero]
  obtain ⟨K, hKc, hKm, hKmass⟩ :=
    l8_tightFamily_compact_metrics hd P₀
      (fun r g => normalizedAtScale ξ D c g r) (Ioi 0)
      hcan hLen hε
  refine ⟨K, hKc, hKm, ?_⟩
  intro Ω _ P _ h hh r hr
  have hmap : P.map h = normLGFLaw d :=
    (normLGFLaw_spec_holds d hd).2.2 _ inferInstance hh.map_id
  let F : DistRd d → C(Rd d × Rd d, ℝ) :=
    fun g => normalizedAtScale ξ D c g r
  have hF : Measurable F := by
    simpa only [F, ← scaledField_zero] using
      (measurable_scaledField hDm c r 0)
  have hlaw : P.map (fun ω => normalizedAtScale ξ D c (h ω) r) =
      (normLGFLaw d).map F := by
    change P.map (F ∘ h) = (normLGFLaw d).map F
    calc
      P.map (F ∘ h) = (P.map h).map F :=
        (Measure.map_map hF hh.1.measurable).symm
      _ = _ := by rw [hmap]
  rw [hlaw]
  exact hKmass r hr

theorem l8_tight_cont_of_normalized
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (D : DistRd d → ContMetric d) (hDm : Measurable D)
    (hN : L8NormalizedWeyl ξ D)
    (c : ℝ → ℝ) (hc : ∀ r, 0 < r → 0 < c r)
    (hcan : TightFamily (normLGFLaw d)
      (fun r g => normalizedAtScale ξ D c g r) (Ioi 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsLGFPlusCont h P) (R : ℝ) (hR : 0 < R) :
    TightOver P (fun r ω => normalizedAtScale ξ D c (h ω) r)
      (Ioo 0 R) := by
  apply l8_tight_cont_of_pure_compact hd ξ hξ D hDm hN c hc P h hh R hR
  intro ε hε
  obtain ⟨K, hKc, hKm, hKmass⟩ :=
    l8_pure_compact_of_normalized hd ξ D hDm hN c hc hcan hε
  exact ⟨K, hKc, hKm, fun h₀ hh₀ r hr =>
    hKmass P h₀ hh₀ r hr.1⟩

end HigherDimLQGMetric
