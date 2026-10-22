import HigherDimLQGMetric.Limits.ScalePrelimit
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Continuous scalar multiplication of metric laws

The scalar and law vary together.  Express the result as a continuous image
of a product of a Dirac law with the metric law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Joint continuity of positive or arbitrary real scalar multiplication and
weak convergence of laws on the metric-function space. -/
theorem l6c_continuous_law_smul {d : ℕ} :
    Continuous (fun p : ℝ × ProbabilityMeasure C(Rd d × Rd d, ℝ) =>
      p.2.map (fun D => p.1 • D)) := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let S : ℝ × C(Rd d × Rd d, ℝ) → C(Rd d × Rd d, ℝ) :=
    fun p => p.1 • p.2
  have hS : Continuous S := continuous_fst.smul continuous_snd
  have hprod : Continuous (fun p : ℝ × ProbabilityMeasure C(Rd d × Rd d, ℝ) =>
      (diracProba p.1).prod p.2) :=
    ProbabilityMeasure.continuous_prod.comp
      ((continuous_diracProba.comp continuous_fst).prodMk continuous_snd)
  have hm := (ProbabilityMeasure.continuous_map hS).comp hprod
  have heq (p : ℝ × ProbabilityMeasure C(Rd d × Rd d, ℝ)) :
      ((diracProba p.1).prod p.2).map S =
        p.2.map (fun D => p.1 • D) := by
    apply Subtype.ext
    change ((Measure.dirac p.1).prod (p.2 : Measure C(Rd d × Rd d, ℝ))).map S =
      (p.2 : Measure C(Rd d × Rd d, ℝ)).map (fun D => p.1 • D)
    rw [Measure.dirac_prod, Measure.map_map]
    · rfl
    · exact hS.measurable
    · exact measurable_prodMk_left
  exact hm.congr fun p => heq p

/-- A compact family of laws remains compact when each law is multiplied by a
scalar from a fixed closed interval. -/
theorem l6c_isCompact_scaled_laws {d : ℕ}
    (K : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ))) (hK : IsCompact K)
    (a b : ℝ) :
    IsCompact {ρ : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ s ∈ Set.Icc a b, ∃ ν ∈ K, ρ = ν.map (fun D => s • D)} := by
  let F : ℝ × ProbabilityMeasure C(Rd d × Rd d, ℝ) →
      ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    fun p => p.2.map (fun D => p.1 • D)
  have hF : Continuous F := l6c_continuous_law_smul
  have hC : IsCompact (Set.Icc a b ×ˢ K) := isCompact_Icc.prod hK
  have heq : F '' (Set.Icc a b ×ˢ K) =
      {ρ : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ s ∈ Set.Icc a b, ∃ ν ∈ K, ρ = ν.map (fun D => s • D)} := by
    ext ρ
    constructor
    · rintro ⟨⟨s, ν⟩, ⟨hs, hν⟩, rfl⟩
      exact ⟨s, hs, ν, hν, rfl⟩
    · rintro ⟨s, hs, ν, hν, rfl⟩
      exact ⟨(s, ν), ⟨hs, hν⟩, rfl⟩
  rw [←heq]
  exact hC.image hF

/-- The lower median of the unit distance scales with the metric law. -/
theorem l6c_lowerMedian_law_smul {d : ℕ}
    (η : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    {s : ℝ} (hs : 0 < s) :
    lowerMedian ((η.map (fun D => s • D)) : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, HigherDimLFPP.e₁ d)) =
      s * lowerMedian (η : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, HigherDimLFPP.e₁ d)) := by
  let e : C(Rd d × Rd d, ℝ) → ℝ :=
    fun D => D (0, HigherDimLFPP.e₁ d)
  have hsm : AEMeasurable (fun D : C(Rd d × Rd d, ℝ) => s • D)
      (η : Measure C(Rd d × Rd d, ℝ)) :=
    (show Continuous (fun D : C(Rd d × Rd d, ℝ) => s • D) from
      by fun_prop).measurable.aemeasurable
  have he : Measurable e := (continuous_eval_const _).measurable
  have hmap : ∀ t : ℝ,
      ((η.map (fun D => s • D)) : Measure C(Rd d × Rd d, ℝ))
        {D | e D ≤ t} =
        (η : Measure C(Rd d × Rd d, ℝ)) {D | s * e D ≤ t} := by
    intro t
    rw [ProbabilityMeasure.toMeasure_map]
    change ((η : Measure C(Rd d × Rd d, ℝ)).map (fun D => s • D))
      (e ⁻¹' Iic t) = _
    rw [Measure.map_apply_of_aemeasurable hsm (he measurableSet_Iic)]
    rfl
  have hmed : lowerMedian ((η.map (fun D => s • D)) : Measure C(Rd d × Rd d, ℝ)) e =
      lowerMedian (η : Measure C(Rd d × Rd d, ℝ)) (fun D => s * e D) := by
    unfold lowerMedian
    congr 1
    ext t
    change ((2 : ℝ≥0∞)⁻¹ ≤
      ((η.map (fun D => s • D)) : Measure C(Rd d × Rd d, ℝ)) {D | e D ≤ t}) ↔
      ((2 : ℝ≥0∞)⁻¹ ≤ (η : Measure C(Rd d × Rd d, ℝ)) {D | s * e D ≤ t})
    rw [hmap]
  rw [hmed]
  exact l6c_lowerMedian_const_mul he.aemeasurable hs

end HigherDimLQGMetric
