import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Radial retraction onto a closed disk, and the induced extension of continuous functions

For `R > 0` the map
`z ↦ c + (R / max R ‖z - c‖) • (z - c)` retracts `ℂ` onto `closedBall c R`. Precomposition gives an
explicit (choice-free) extension operator `diskExt : C(closedBall c R, ℝ) → C(ℂ, ℝ)`, continuous for
the compact-open topologies, hence Borel measurable. It turns random continuous corrections on the
disk into random continuous corrections on `ℂ` (needed to apply Weyl scaling and locality to
whole-plane fields).
-/

set_option autoImplicit false

noncomputable section

open Metric Set

namespace SupercriticalConformalCovariance.Lemma31

/-- The radial retraction of `ℂ` onto `closedBall c R` (`R > 0`). -/
def diskRetract (c : ℂ) {R : ℝ} (hR : 0 < R) : C(ℂ, closedBall c R) where
  toFun z := ⟨c + (R / max R ‖z - c‖ : ℝ) • (z - c), by
    have hm : 0 < max R ‖z - c‖ := lt_max_of_lt_left hR
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hR.le hm.le), div_mul_eq_mul_div, div_le_iff₀ hm]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR.le⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_const.add (Continuous.smul (f := fun z : ℂ => (R / max R ‖z - c‖ : ℝ))
      (g := fun z : ℂ => z - c) ?_ (continuous_id.sub continuous_const))
    exact continuous_const.div (continuous_const.max (continuous_norm.comp
      (continuous_id.sub continuous_const))) fun z => (lt_max_of_lt_left hR).ne'

theorem diskRetract_of_mem (c : ℂ) {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ closedBall c R) :
    (diskRetract c hR z : ℂ) = z := by
  have hz' : ‖z - c‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hz
  show c + (R / max R ‖z - c‖ : ℝ) • (z - c) = z
  rw [max_eq_left hz', div_self hR.ne', one_smul, add_sub_cancel]

/-- Extension of a continuous function on `closedBall c R` to `ℂ`, by the radial retraction. -/
def diskExt (c : ℂ) {R : ℝ} (hR : 0 < R) (f : C(closedBall c R, ℝ)) : C(ℂ, ℝ) :=
  f.comp (diskRetract c hR)

theorem diskExt_eq (c : ℂ) {R : ℝ} (hR : 0 < R) (f : C(closedBall c R, ℝ)) (z : ℂ)
    (hz : z ∈ closedBall c R) : diskExt c hR f z = f ⟨z, hz⟩ := by
  show f (diskRetract c hR z) = f ⟨z, hz⟩
  congr 1
  exact Subtype.ext (diskRetract_of_mem c hR hz)

theorem continuous_diskExt (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Continuous (diskExt c hR) :=
  ContinuousMap.continuous_precomp _

theorem measurable_diskExt (c : ℂ) {R : ℝ} (hR : 0 < R) :
    Measurable (diskExt c hR) :=
  (continuous_diskExt c hR).measurable

end SupercriticalConformalCovariance.Lemma31
