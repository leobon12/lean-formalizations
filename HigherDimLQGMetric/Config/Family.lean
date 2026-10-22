import HigherDimLQGMetric.Config.Bounds

/-!
# Original configurations and compact families

`C(β)` is the closure of the original length-metric configurations which
obey the bounds.  Taking the closure of all bounded quadruples would lose
the path-length relations needed later.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The configurations of two comparable length metrics, in normalized unit coordinates. -/
def configOriginal (hd : 2 ≤ d) (c C : ℝ) : Set (ConfigC d) :=
  {q | ∃ (D Dt : ContMetric d) (hD : D.IsLength) (hDt : Dt.IsLength),
    (∀ u v : Rd d, c * D.1 (u, v) ≤ Dt.1 (u, v) ∧
      Dt.1 (u, v) ≤ C * D.1 (u, v)) ∧
    q = configC hd D Dt hD hDt (s := 1) (r := 1)
      (by norm_num) (by norm_num) 0}

/-- `C(β) = closure(Orig ∩ B(β))`. -/
def configCompactFamily (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) :
    Set (ConfigC d) :=
  closure (configOriginal hd c C ∩ configBoundSet β)

theorem configCompactFamily_subset_bound (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) :
    configCompactFamily hd c C β ⊆ configBoundSet β := by
  unfold configCompactFamily
  exact closure_minimal (inter_subset_right) (configBoundSet_isClosed β)

theorem configCompactFamily_isCompact (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) :
    IsCompact (configCompactFamily hd c C β) := by
  exact (configBoundSet_isCompact β).of_isClosed_subset isClosed_closure
    (configCompactFamily_subset_bound hd c C β)

end HigherDimLQGMetric
