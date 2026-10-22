-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Frozen.TendstoInProbLU
import HigherDimLQGMetric.Frozen.AEps
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont
import HigherDimLQGMetric.Frozen.AddFun
import HigherDimLQGMetric.Assembly.Theorem12

/-!
# Frozen theorem: `theorem12`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M5, M6, M7, M12, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] Theorem 1.2 (l. 82–88) with the standing hypotheses of l. 50 and Corollary 10.4 (l. 1572–1577):
existence of an assignment satisfying the four strong axioms at `Q = Q(ξ)` (ruling M12), convergence in
probability, locally uniformly, of `𝔞_ε⁻¹ D^ε_h` to it for every nonnegative admissible kernel of
[1, Remark 1.1] (ruling M6) and every LGF plus a bounded continuous function, and uniqueness up to a
deterministic positive constant (all endpoint pairs, all continuous perturbations). The limit `D` is the
same for all kernels (the unique median-one assignment, l. 1574–1575). Phase B anchor (rulings M1, M5).

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.theorem12_impl` (provider `HigherDimLQGMetric.Assembly.Theorem12`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- **Theorem 1.2** (target statement) at `Q = Q(ξ)`: existence of a strong assignment, convergence of the
normalized convolution LFPP of [1, Remark 1.1] to it (every nonnegative admissible kernel, every LGF plus
a bounded continuous function), and uniqueness up to a deterministic positive constant. -/
theorem theorem12 :
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
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.theorem12_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
