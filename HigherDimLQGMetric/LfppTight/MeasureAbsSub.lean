import HigherDimLQGMetric.LfppTight.LogCovDominated

/-! Positive density domination for a difference and a scalar multiple. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_posM_abs_sub_le {d : ℕ} (f g : Rd d → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    posM (fun x => |f x - g x|) ≤
      posM (fun x => |f x|) + posM (fun x => |g x|) := by
  unfold posM
  have hfm : Measurable (fun x : Rd d => ENNReal.ofReal |f x|) :=
    (continuous_abs.measurable.comp hf).ennreal_ofReal
  have hgm : Measurable (fun x : Rd d => ENNReal.ofReal |g x|) :=
    (continuous_abs.measurable.comp hg).ennreal_ofReal
  have hpoint : (fun x : Rd d => ENNReal.ofReal |f x - g x|) ≤ᵐ[volume]
      (fun x => ENNReal.ofReal |f x| + ENNReal.ofReal |g x|) := by
    apply ae_of_all
    intro x
    dsimp
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f x) (-(g x)))
  calc
    volume.withDensity (fun x : Rd d => ENNReal.ofReal |f x - g x|) ≤
        volume.withDensity (fun x => ENNReal.ofReal |f x| + ENNReal.ofReal |g x|) :=
      withDensity_mono hpoint
    _ = volume.withDensity (fun x : Rd d => ENNReal.ofReal |f x|) +
        volume.withDensity (fun x : Rd d => ENNReal.ofReal |g x|) :=
      withDensity_add_left hfm _

theorem l6a_posM_abs_const_mul {d : ℕ} (g : Rd d → ℝ)
    (_hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (c : ℝ) :
    posM (fun x => |c * g x|) = ENNReal.ofReal |c| • posM g := by
  unfold posM
  have heq : (fun x : Rd d => ENNReal.ofReal |c * g x|) =
      ENNReal.ofReal |c| • (fun x => ENNReal.ofReal (g x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (hg0 x),
      ENNReal.ofReal_mul (abs_nonneg c)]
  rw [heq, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

end HigherDimLQGMetric
