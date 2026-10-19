import GaussianLQG.Assembly.Main
import GaussianLQG.Assembly.Discharge
import GaussianLQG.LQG.Crossing
import GaussianLQG.LQG.EnergyApprox

/-!
# Provider of the main theorem

`main_theorem_provider` has exactly the statement of the draft main theorem
(`planning/main-theorem-draft.lean.txt`, source Theorem 1.1, blueprint Theorem `thm:main`):
the same binders, hypotheses and conclusions; only the name differs. Its only hypotheses are those of
the draft: `hD` (each `D γ` is the canonical γ-LQG metric) and `hS6` (the source's Lemma 2.1, the
single trust input, ruling R7). Once the author approves and the statement is frozen, the frozen
anchor's body will be this provider.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG

/-- **Main theorem** (source Theorem 1.1, blueprint Theorem `thm:main`), relative to the single input
(S6) (source Lemma 2.1, unproved; taken as a hypothesis under ruling R7). -/
theorem main_theorem_provider (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ))
    (hS6 : UniformMomentInput D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : LQGMetric.IsNormalizedWPGFF h P) :
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
  main_theorem_of_interfaces D hD hS6 P h hh (fun S =>
    ⟨S.crossingConv S.energyApprox, S.fixedPairConv S.energyApprox, S.lawM_holds, S.h00Law⟩)

end GaussianLQG
