import HigherDimLQGMetric.LfppTight.MedianBasics
import HigherDimLQGMetric.Main.LFPPMedian

/-!
# Positivity of the LFPP lower median

The point-distance measurability lemma is reused from the final LFPP assembly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- Positivity of the fixed normalization, including its exact convention as a
lower median rather than an arbitrary median. -/
theorem l6a_aEps_pos {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < aEps κ ξ ε := by
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd).2.1
  let X : DistRd d → ℝ := fun h => lfppDist κ ξ ε h (0, e₁ d)
  have hXm : AEMeasurable X (normLGFLaw d) :=
    l10a_aemeasurable_lfppPoint hd κ hκ ξ (normLGFLaw d) id hn hε
  have hc := l10a_ae_continuous_convMollify hd κ hκ (normLGFLaw d) id hn hε
  have hXp : ∀ᵐ h ∂(normLGFLaw d), 0 < X h := by
    filter_upwards [hc] with h hh
    exact HigherDimLFPP.lfppDistOn_pos hh
      (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
      (HigherDimLFPP.PcwJoined.of_convex convex_univ (Set.mem_univ 0)
        (Set.mem_univ (e₁ d)))
  rw [l6a_aEps_eq_lowerMedian]
  exact l6a_lowerMedian_pos (normLGFLaw d) X hXm hXp

/-- Every normalized LGF realization has the same lower median `aEps` for its
whole-space LFPP point distance. -/
theorem l6a_aEps_eq_sample_lowerMedian {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    aEps κ ξ ε = lowerMedian P
      (fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)) := by
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  let F : DistRd d → ℝ := fun g => lfppDist κ ξ ε g (0, e₁ d)
  have hFm : AEMeasurable F (normLGFLaw d) :=
    l10a_aemeasurable_lfppPoint hd κ hκ ξ (normLGFLaw d) id
      (normLGFLaw_spec_holds d hd).2.1 hε
  have hXFm : AEMeasurable (F ∘ h) P := by
    simpa only [Function.comp_def] using
      l10a_aemeasurable_lfppPoint hd κ hκ ξ P h hh hε
  have hhlaw : P.map h = normLGFLaw d :=
    (normLGFLaw_spec_holds d hd).2.2 (P.map h) inferInstance hh.map_id
  rw [l6a_aEps_eq_lowerMedian,
    l6a_lowerMedian_eq_lowerQuantile_map (normLGFLaw d) F hFm]
  change LQGMetric.lowerQuantile ((normLGFLaw d).map F) 2⁻¹ =
    lowerMedian P (F ∘ h)
  rw [l6a_lowerMedian_eq_lowerQuantile_map P (F ∘ h) hXFm]
  rw [← hhlaw]
  exact congrArg (fun ν : Measure ℝ => LQGMetric.lowerQuantile ν 2⁻¹)
    (AEMeasurable.map_map_of_aemeasurable
      (by rw [hhlaw]; exact hFm) hh.1.measurable.aemeasurable)

end HigherDimLQGMetric
