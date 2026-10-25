import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareGlue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

 

theorem laneB_in_square_cutoff_le_of_split
    {ξ M : ℝ} {f g h : ℂ → ℝ}
    (hfg : Continuous (fun x => f x + g x))
    (hfield : ∀ x ∈ (rectAB 1 1).toSet,
      |h x - (f x + g x)| ≤ M) :
    (rectLen ξ h (rectAB 1 1)).toReal ≤
      Real.exp (|ξ| * M) *
        (rectLen ξ (fun x => f x + g x) (rectAB 1 1)).toReal := by
  have hcmp : rectLen ξ h (rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) *
        rectLen ξ (fun x => f x + g x) (rectAB 1 1) :=
    crossLenIn_le_of_abs_sub_le hfield
  have hfin : rectLen ξ (fun x => f x + g x) (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) hfg
  have hrhs : ENNReal.ofReal (Real.exp (|ξ| * M)) *
      rectLen ξ (fun x => f x + g x) (rectAB 1 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hreal := ENNReal.toReal_mono hrhs hcmp
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal

end SupercriticalLQGUniqueness.B2.DG20Conc
