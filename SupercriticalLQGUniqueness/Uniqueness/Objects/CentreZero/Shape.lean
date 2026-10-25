import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero.RN
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Object




 






set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero

open SupercriticalLQGUniqueness
open Set Metric

variable (P : Objects.Tube.TubeParams) (hP : P.Good) (r Asup Amax : ℝ)
  (hr : 0 < r) (hAsup : 0 < Asup) (hSmall : 100 * Asup ≤ P.sp * P.ρ)

 
def uZero : TopologicalSpace.Opens ℂ :=
  ⟨P.tubeAt r 0, (Objects.Tube.TubeParams.tubeAt_annular hP hr hAsup hSmall 0).1⟩

 
def vZero : TopologicalSpace.Opens ℂ :=
  ⟨P.nbhdAt r Asup 0, (Objects.Tube.TubeParams.nbhdAt_annular hP hr hAsup hSmall 0).1⟩

 
def fZero : LQGMetric.TestC :=
  P.bumpAtTest r Amax ⟨Asup, hAsup⟩ 0 hP hr hSmall

theorem uZero_annular :
    EndSaving.InterfaceV2.IsOpenAnnularTubeV2 0 ⟨r, hr⟩ (uZero P hP r Asup hr hAsup hSmall) := by
  exact (Objects.Tube.TubeParams.tubeAt_annular hP hr hAsup hSmall 0).2

theorem vZero_annular :
    EndSaving.InterfaceV2.IsOpenAnnularTubeV2 0 ⟨r, hr⟩ (vZero P hP r Asup hr hAsup hSmall) := by
  exact (Objects.Tube.TubeParams.nbhdAt_annular hP hr hAsup hSmall 0).2

theorem closure_uZero_vZero :
    closure (uZero P hP r Asup hr hAsup hSmall : Set ℂ) ⊆
      (vZero P hP r Asup hr hAsup hSmall : Set ℂ) := by
  exact Objects.Tube.TubeParams.closure_tubeAt_subset hr hAsup 0

theorem closure_vZero_annulus :
    closure (vZero P hP r Asup hr hAsup hSmall : Set ℂ) ⊆
      {x : ℂ | r < dist x 0 ∧ dist x 0 < 3 * r} := by
  exact Objects.Tube.TubeParams.closure_nbhdAt_subset hP hr hSmall 0

theorem vZero_middle :
    (vZero P hP r Asup hr hAsup hSmall : Set ℂ) ⊆
      {x : ℂ | 1.5 * r < dist x 0 ∧ dist x 0 < 2.5 * r} := by
  intro x hx
  change x ∈ P.nbhdAt r Asup 0 at hx
  have hx' : x ∈ P.nbhd r Asup := by
    simpa only [Objects.Tube.TubeParams.mem_nbhdAt, sub_zero] using hx
  have h := (Objects.Tube.TubeParams.nbhd_and_thickening_subset_annulus hP hr hSmall).1 hx'
  change (3 / 2 : ℝ) * r < ‖x‖ ∧ ‖x‖ < (5 / 2 : ℝ) * r at h
  change 1.5 * r < dist x 0 ∧ dist x 0 < 2.5 * r
  rw [dist_zero_right]
  constructor <;> nlinarith [h.1, h.2]

theorem fZero_nonneg (hAmax : 0 ≤ Amax) (x : ℂ) :
    0 ≤ fZero P hP r Asup Amax hr hAsup hSmall x := by
  exact Objects.Tube.TubeParams.bump_nonneg hAmax ⟨Asup, hAsup⟩ (x - 0)

theorem fZero_le (hAmax : 0 ≤ Amax) (x : ℂ) :
    fZero P hP r Asup Amax hr hAsup hSmall x ≤ Amax := by
  exact Objects.Tube.TubeParams.bump_le hAmax ⟨Asup, hAsup⟩ (x - 0)

theorem fZero_on_uZero {x : ℂ}
    (hx : x ∈ (uZero P hP r Asup hr hAsup hSmall : Set ℂ)) :
    fZero P hP r Asup Amax hr hAsup hSmall x = Amax := by
  exact Objects.Tube.TubeParams.bumpAt_eq_on_tube Amax ⟨Asup, hAsup⟩ 0 (subset_closure hx)

theorem fZero_off_vZero {x : ℂ}
    (hx : x ∉ (vZero P hP r Asup hr hAsup hSmall : Set ℂ)) :
    fZero P hP r Asup Amax hr hAsup hSmall x = 0 := by
  exact Objects.Tube.TubeParams.bumpAt_eq_zero hr Amax ⟨Asup, hAsup⟩ 0 hx

end SupercriticalLQGUniqueness.Uniqueness.Objects.CentreZero
