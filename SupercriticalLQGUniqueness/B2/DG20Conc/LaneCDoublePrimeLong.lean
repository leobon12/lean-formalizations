import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAnnuli
import LQGMetric.Papers.DDDF.P18S1Geom

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 
def laneCDoublePrimeLongRect (j : Fin 8) : MarkedRect :=
  match j.val with
  | 0 => ⟨-2, 2, 3, 1, true⟩
  | 1 => ⟨0, 2, 3, 1, true⟩
  | 2 => ⟨-2, -2, 3, 1, true⟩
  | 3 => ⟨0, -2, 3, 1, true⟩
  | 4 => ⟨-2, -2, 1, 3, false⟩
  | 5 => ⟨-2, 0, 1, 3, false⟩
  | 6 => ⟨2, -2, 1, 3, false⟩
  | _ => ⟨2, 0, 1, 3, false⟩

 
theorem laneC_double_prime_long_rect_subset (j : Fin 8) :
    (laneCDoublePrimeLongRect j).toSet ⊆ laneCDoublePrimeCross := by
  have hinner : interior laneCInnerCluster =
      Ioo (-1 : ℝ) 2 ×ℂ Ioo (-1 : ℝ) 2 := by
    simp [laneCInnerCluster, Complex.interior_reProdIm, interior_Icc]
  intro z hz
  fin_cases j <;>
    simp only [laneCDoublePrimeLongRect, MarkedRect.toSet, laneCDoublePrimeCross,
      laneCOuterCluster, hinner, Complex.mem_reProdIm, mem_sdiff, mem_Icc,
      mem_Ioo] at hz ⊢ <;>
    rcases hz with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
  all_goals
    constructor
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · intro h
      rcases h with ⟨⟨_, _⟩, ⟨_, _⟩⟩
      linarith

 


def laneCDoublePrimeCornerVertical (k : Fin 4) : Fin 8 :=
  match k.val with
  | 0 => ⟨5, by decide⟩
  | 1 => ⟨7, by decide⟩
  | 2 => ⟨4, by decide⟩
  | _ => ⟨6, by decide⟩

theorem laneC_double_prime_corner_meet (k : Fin 4)
    {γ δ : ℝ → ℂ}
    (hγ : AdmPath (laneCDoublePrimeLongRect ⟨k.val, by omega⟩).toSet
      (laneCDoublePrimeLongRect ⟨k.val, by omega⟩).side₁
      (laneCDoublePrimeLongRect ⟨k.val, by omega⟩).side₂ γ)
    (hδ : AdmPath (laneCDoublePrimeLongRect (laneCDoublePrimeCornerVertical k)).toSet
      (laneCDoublePrimeLongRect (laneCDoublePrimeCornerVertical k)).side₁
      (laneCDoublePrimeLongRect (laneCDoublePrimeCornerVertical k)).side₂ δ) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, γ s = δ t := by
  fin_cases k <;>
    exact hv_meet rfl rfl (by norm_num [laneCDoublePrimeLongRect,
      laneCDoublePrimeCornerVertical])
      (by norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeCornerVertical])
      (by norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeCornerVertical])
      (by norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeCornerVertical])
      (by norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeCornerVertical])
      (by norm_num [laneCDoublePrimeLongRect, laneCDoublePrimeCornerVertical]) hγ hδ

end SupercriticalLQGUniqueness.B2.DG20Conc
