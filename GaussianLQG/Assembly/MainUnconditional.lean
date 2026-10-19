import GaussianLQG.Assembly.FrontierU12
import GaussianLQG.Uniform.Holder.Done

/-!
# Provider of the frozen main theorem

The registered implementation of the keystone anchor `main_theorem_v2`
(`GaussianLQG/Frozen/MainTheorem.lean`, manifest `GaussianLQG/Frozen/frozen-anchors.json`).
`main_theorem_impl` has exactly the frozen statement. It is `main_theorem_of_holderMoment` (the main
theorem from the uniform LFPP Hölder moments, ledger U12) applied to `Uniform.ifaceHolderMomentU_holds`
(U12, proved). The chain behind it: (★) `StarBound.exists_lfppUniformMoments` (U15, from U12–U14), the
passage to the limit `uniformMomentInput_of_lfppUniformMoments` (U16), which gives (S6) for the
canonical metric, and the conditional provider `main_theorem_provider` (Sections 1–7 of the blueprint).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG

/-- Provider of the frozen main theorem (source Theorem 1.1, blueprint Theorem `thm:main`). -/
theorem main_theorem_impl :
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
  main_theorem_of_holderMoment Uniform.ifaceHolderMomentU_holds

end GaussianLQG
