import Mathlib




 







set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

variable {X : Type*} [TopologicalSpace X]

 
def glue (a : ℤ → X) (p : ∀ k : ℤ, Path (a k) (a (k + 1))) (x : ℝ) : X :=
  (p ⌊x⌋).extend (x - ⌊x⌋)

theorem glue_eq_of_mem (a : ℤ → X) (p : ∀ k : ℤ, Path (a k) (a (k + 1))) {k : ℤ} {x : ℝ}
    (hx : x ∈ Ico (k : ℝ) (k + 1)) : glue a p x = (p k).extend (x - k) := by
  have : ⌊x⌋ = k := Int.floor_eq_iff.mpr hx
  unfold glue; rw [this]

theorem glue_int (a : ℤ → X) (p : ∀ k : ℤ, Path (a k) (a (k + 1))) (k : ℤ) :
    glue a p k = a k := by
  rw [glue_eq_of_mem a p (k := k) ⟨le_rfl, by linarith⟩, sub_self, Path.extend_zero]

 
theorem glue_eq_prev (a : ℤ → X) (p : ∀ k : ℤ, Path (a k) (a (k + 1))) {k : ℤ} {x : ℝ}
    (hx : x ∈ Ioc ((k : ℝ) - 1) k) : glue a p x = (p (k - 1)).extend (x - (k - 1 : ℤ)) := by
  rcases hx.2.lt_or_eq with h | h
  · rw [glue_eq_of_mem a p (k := k - 1) ⟨by push_cast; linarith [hx.1], by push_cast; linarith⟩]
  · rw [h, glue_int, show (k : ℝ) - ((k - 1 : ℤ) : ℝ) = 1 by push_cast; ring, Path.extend_one]
    exact congrArg a (by ring)

theorem continuous_glue (a : ℤ → X) (p : ∀ k : ℤ, Path (a k) (a (k + 1))) :
    Continuous (glue a p) := by
  have hg : ∀ k : ℤ, Continuous (fun x : ℝ => (p k).extend (x - k)) :=
    fun k => (p k).continuous_extend.comp (continuous_id.sub continuous_const)
  rw [continuous_iff_continuousAt]
  intro x
  set k := ⌊x⌋ with hk
  have hxk : x ∈ Ico (k : ℝ) (k + 1) := Int.floor_eq_iff.mp hk.symm
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · rcases hxk.1.lt_or_eq with hlt | heq
    · 
      apply (hg k).continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [Ioc_mem_nhdsLE_of_mem ⟨hlt, le_rfl⟩] with y hy
        exact glue_eq_of_mem a p ⟨hy.1.le, by linarith [hy.2, hxk.2]⟩
      · exact glue_eq_of_mem a p hxk
    · 
      apply (hg (k - 1)).continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [Ioc_mem_nhdsLE_of_mem (show x ∈ Ioc ((k : ℝ) - 1) k from
          ⟨by linarith, heq.symm.le⟩)] with y hy
        exact glue_eq_prev a p hy
      · exact glue_eq_prev a p ⟨by linarith, heq.symm.le⟩
  · apply (hg k).continuousWithinAt.congr_of_eventuallyEq
    · filter_upwards [Ico_mem_nhdsGE_of_mem hxk] with y hy
      exact glue_eq_of_mem a p hy
    · exact glue_eq_of_mem a p hxk

theorem glue_mem_range (a : ℤ → X) (p : ∀ k : ℤ, Path (a k) (a (k + 1))) (x : ℝ) :
    glue a p x ∈ range (p ⌊x⌋) := by
  unfold glue
  rw [Path.extend]
  exact ⟨projIcc 0 1 zero_le_one (x - ⌊x⌋), rfl⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
