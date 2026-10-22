import HigherDimLQGMetric.Assembly.Theorem14Sharp
import HigherDimLQGMetric.Main.Inputs
import HigherDimLQGMetric.Main.Theorem12
import HigherDimLQGMetric.Sec10.Cor102
import HigherDimLQGMetric.ShellDec.Bridge

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.theorem12`

`theorem12_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/Theorem12.lean` verbatim ([S] Theorem 1.2: existence of a
strong assignment at `Q(ξ)`, convergence of the normalized LFPP, uniqueness up to a constant). Proof: L10a's
`theorem12_of_inputs` (`Main/Theorem12.lean`, via Cor 10.4) with the unconditional inputs of `Main/Inputs.lean` (L8's
[1] Theorem 1.3 from L6a, L6c, L7a, L7b, L7c; L9c's [1] Theorem 1.6; S8b's Lemma 10.3), L5b's `realEpsAdapterShape`,
`theorem14Sharp_impl`, S8c's `cor102Sharp_of` and G3b's `shellDecouplingFun_rd`. This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `theorem12`, proved. -/
theorem theorem12_impl :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    (∃ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D ∧
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P →
        TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
          (fun ω => (D (h ω)).1)) ∧
    ∀ D D' : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d ξ (distExp d ξ) D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) := by
  exact theorem12_of_inputs b3Goal' DGZ.realEpsAdapterShape theorem16Shape' theorem14Sharp_impl
    (cor102Sharp_of theorem14Sharp_impl) lemma103Shape' shellDecouplingFun_rd

end HigherDimLQGMetric
