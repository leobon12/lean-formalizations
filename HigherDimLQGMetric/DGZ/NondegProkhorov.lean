import HigherDimLQGMetric.DGZ.NondegJointTight

/-!
# Prokhorov subsequences for the DGZ joint laws

This is the compactness step `μ0` of the corrected DGZ Lemma 6.9. The state carries every
internal-metric coordinate needed later; no Skorokhod representation is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- A pointwise measurable joint state has a probability law. -/
def nd_jointLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hP : IsProbabilityMeasure P) (H : ℕ → Rd d → Ω → ℝ)
    (ξ : ℝ) (q : ℝ≥0∞) (r : ℝ) (n : ℕ) :
    ProbabilityMeasure (nd_Joint d r) := by
  letI := hP
  exact ⟨P.map (nd_jointSample P H ξ q r n), inferInstance⟩

/-- Every sequence of dyadic levels admits a weakly convergent subsequence of joint laws. -/
theorem nd_exists_joint_limit {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₀ : ℝ≥0∞, 0 < q₀ ∧ q₀ < 1 ∧ ∀ q : ℝ≥0∞, q₀ ≤ q → q < 1 →
      ∀ (r : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        ∀ hH : IsDyadicRealization κ P W H, ∀ ns : ℕ → ℕ,
          ∃ μ : ProbabilityMeasure (nd_Joint d r), ∃ ψ : ℕ → ℕ,
            StrictMono ψ ∧ Tendsto
              (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns (ψ k)))
              atTop (𝓝 μ) := by
  obtain ⟨q₀, hq₀0, hq₀1, htight⟩ := nd_isTightMeasureSet_joint h
  refine ⟨q₀, hq₀0, hq₀1, ?_⟩
  intro q hq hq1 r Ω _ P W H hH ns
  let law : ℕ → ProbabilityMeasure (nd_Joint d r) :=
    fun n => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns n)
  have hT : IsTightMeasureSet
      {((μ : ProbabilityMeasure (nd_Joint d r)) : Measure (nd_Joint d r)) |
        μ ∈ range law} := by
    refine (htight q hq hq1 r Ω P W H hH).subset ?_
    rintro ν ⟨μ, ⟨n, rfl⟩, rfl⟩
    exact ⟨ns n, rfl⟩
  obtain ⟨μ, -, ψ, hψ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet hT).tendsto_subseq
      (x := law) (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨μ, ψ, hψ, hlim⟩

end HigherDimLQGMetric.DGZ
