import GaussianLQG.LQG.Bridge.Defs
import LQGMetric.Assembly.MainFinal

/-!
# Existence of the canonical γ-LQG metric

For `γ ∈ (0,2)` a canonical γ-LQG metric exists (`exists_isCanonicalLQGMetric`): this is the
existence part of GM Theorem 1.2, `LQGMetric.theorem12_proved`, whose existence clause is
`GaussianLQG.IsCanonicalLQGMetric` verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace GaussianLQG

/-- **Existence of the canonical γ-LQG metric** (GM Theorem 1.2, existence part): for
`γ ∈ (0,2)` there is a canonical γ-LQG metric. -/
theorem exists_isCanonicalLQGMetric {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ D : LQGMetric.DistC → LQGMetric.ContMetric, IsCanonicalLQGMetric γ D :=
  (LQGMetric.theorem12_proved γ hγ hγ2).1

end GaussianLQG
