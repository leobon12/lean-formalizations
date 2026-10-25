import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPrimeAround

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 
def laneCPrimeLongRect (side : Fin 4) (i : Fin 5) : MarkedRect :=
  let t : ℝ := -3 / 16 + (i.val : ℝ) / 4
  match side.val with
  | 0 => ⟨t, 17 / 16, 3 / 8, 1 / 8, true⟩
  | 1 => ⟨t, -3 / 16, 3 / 8, 1 / 8, true⟩
  | 2 => ⟨-3 / 16, t, 1 / 8, 3 / 8, false⟩
  | _ => ⟨17 / 16, t, 1 / 8, 3 / 8, false⟩

 
def laneCPrimeJoinRect (side : Fin 4) (i : Fin 4) : MarkedRect :=
  let t : ℝ := -3 / 16 + ((i.val : ℝ) + 1) / 4
  match side.val with
  | 0 => ⟨t, 1, 1 / 8, 3 / 8, false⟩
  | 1 => ⟨t, -1 / 4, 1 / 8, 3 / 8, false⟩
  | 2 => ⟨-1 / 4, t, 3 / 8, 1 / 8, true⟩
  | _ => ⟨1, t, 3 / 8, 1 / 8, true⟩

theorem laneC_prime_long_subset_wide (side : Fin 4) (i : Fin 5) :
    (laneCPrimeLongRect side i).toSet ⊆
      (laneCPrimeWideRect side).toSet := by
  fin_cases side <;> fin_cases i <;> intro z hz <;>
    norm_num [laneCPrimeLongRect, laneCPrimeWideRect,
      MarkedRect.toSet, Complex.mem_reProdIm] at hz ⊢ <;>
    rcases hz with ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ <;>
    exact ⟨⟨by linarith, by linarith⟩,⟨by linarith, by linarith⟩⟩

theorem laneC_prime_long_subset_open (side : Fin 4) (i : Fin 5) :
    (laneCPrimeLongRect side i).toSet ⊆ laneCPrimeAround :=
  (laneC_prime_long_subset_wide side i).trans (laneC_prime_wide_subset side)

end SupercriticalLQGUniqueness.B2.DG20Conc
