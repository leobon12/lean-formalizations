import GaussianLQG.Assembly.FrontierS6
import GaussianLQG.Uniform.Star

/-!
# The proof frontier: only the LFPP Hölder moments (U12) remain (orchestrator integration)

The frozen keystone's statement (`GaussianLQG/Frozen/MainTheorem.lean`, anchor `main_theorem_v2`),
proved from `Uniform.IfaceHolderMomentU` (ledger U12) alone: (★) comes from
`StarBound.exists_lfppUniformMoments` (U15, with U13 and U14 proved) and the passage to the limit
from `main_theorem_of_lfppUniformMoments` (U16 and the conditional provider).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG

/-- The frozen main theorem, assuming only ledger U12 (uniform LFPP Hölder moments). -/
theorem main_theorem_of_holderMoment (hU12 : Uniform.IfaceHolderMomentU) :
    ∀ (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (_hh : LQGMetric.IsNormalizedWPGFF h P),
    -- `q` is the unique median of `M`, and `q < 0`
    (LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) qConst ∧
      ∀ m, LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) m → m = qConst) ∧
    qConst < 0 ∧
    -- (1.7): convergence in probability
    TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) ∧
    -- the limit has law `N(-q/2, 3/8)`
    P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) =
      gaussianReal (-qConst / 2) (3 / 8 : NNReal) ∧
    -- (1.8): convergence in law to `N(-q/2, 3/8)` (indexed by `γ ∈ (0,2)`)
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((D γ (h ω)).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal (-qConst / 2) (3 / 8 : NNReal)) ∧
    -- (1.9) for every choice of medians `m_γ` of `D^γ(0,1)`
    ∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (P.map fun ω => (D γ (h ω)).1 (0, 1)) (m γ)) →
      Tendsto (fun γ => (m γ - (1 - qConst / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) :=
  fun D hD _ _ P _ h hh =>
    let ⟨c, hc, hstar⟩ := StarBound.exists_lfppUniformMoments hU12
    main_theorem_of_lfppUniformMoments c hc hstar D hD P h hh

end GaussianLQG
