import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Basic constants of the LQG-metric project

`Q γ = 2/γ + γ/2` (GM (1.3)). The LQG dimension `d_γ` and `ξ = γ/d_γ` are defined in the
statement layer (`LQGMetric/Statement/`), following Ding–Gwynne Thm 1.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LQGMetric

/-- `Q = 2/γ + γ/2` (Gwynne–Miller, eq. (1.3)). -/
noncomputable def Q (γ : ℝ) : ℝ := 2 / γ + γ / 2

lemma Q_pos {γ : ℝ} (hγ : 0 < γ) : 0 < Q γ := by
  unfold Q; positivity

end LQGMetric
