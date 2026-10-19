import GaussianLQG.Assembly.Provider
import GaussianLQG.Uniform.Limit
import GaussianLQG.Core.InterfacesS6

/-!
# The current proof frontier of the unconditional main theorem (orchestrator integration)

The frozen keystone's statement (`GaussianLQG/Frozen/MainTheorem.lean`), proved from the
LFPP-level uniform moment bounds (★) = `LFPPUniformMoments c` for some positive normalization `c`
(Route U15). It composes the conditional provider `main_theorem_provider` with the passage to the
limit `uniformMomentInput_of_lfppUniformMoments` (Route U16). What remains is to prove (★): Route
U3–U15.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG

/-- The frozen main theorem, assuming only (★) for some positive normalization `c`. -/
theorem main_theorem_of_lfppUniformMoments (c : ℝ → ℕ → ℝ) (hc : ∀ γ n, 0 < c γ n)
    (hstar : LFPPUniformMoments c)
    (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsNormalizedWPGFF h P) :
    (LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) qConst ∧
      ∀ m, LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) m → m = qConst) ∧
    qConst < 0 ∧
    TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) ∧
    P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) =
      gaussianReal (-qConst / 2) (3 / 8 : NNReal) ∧
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((D γ (h ω)).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal (-qConst / 2) (3 / 8 : NNReal)) ∧
    ∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (P.map fun ω => (D γ (h ω)).1 (0, 1)) (m γ)) →
      Tendsto (fun γ => (m γ - (1 - qConst / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) :=
  main_theorem_provider D hD (uniformMomentInput_of_lfppUniformMoments c hc hstar D hD) P h hh

end GaussianLQG
