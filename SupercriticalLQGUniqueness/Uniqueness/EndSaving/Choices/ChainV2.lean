import Mathlib




 










set_option autoImplicit false

noncomputable section

open Finset
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

 



theorem chain_bound {ι : Type*} [DecidableEq ι] (S : Finset ι) (s t : ι → ℝ)
    (d g : ℝ → ℝ → ℝ≥0∞)
    (htri : ∀ x y z : ℝ, x ≤ y → y ≤ z → d x z ≤ d x y + d y z)
    (hadd : ∀ x y z : ℝ, x ≤ y → y ≤ z → g x z = g x y + g y z)
    (a b : ℝ) (hab : a ≤ b)
    (hst : ∀ i ∈ S, s i < t i)
    (hin : ∀ i ∈ S, a ≤ s i ∧ t i ≤ b)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (hgap : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      (∀ i ∈ S, t i ≤ x ∨ y ≤ s i) → d x y ≤ g x y) :
    d a b + ∑ i ∈ S, g (s i) (t i) ≤ g a b + ∑ i ∈ S, d (s i) (t i) := by
  induction S using Finset.strongInduction generalizing a with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      simp only [sum_empty, add_zero]
      exact hgap a b le_rfl hab le_rfl (by simp)
    · obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image s hS
      set S' := S.erase i₀ with hS'
      have hS'sub : S' ⊂ S := Finset.erase_ssubset hi₀
      have hafter : ∀ j ∈ S', t i₀ ≤ s j := by
        intro j hj
        have hjS : j ∈ S := Finset.mem_of_mem_erase hj
        have hji : j ≠ i₀ := Finset.ne_of_mem_erase hj
        rcases hdisj i₀ hi₀ j hjS (Ne.symm hji) with h | h
        · exact h
        · have h1 := hmin j hjS
          have h2 := hst j hjS
          exact absurd (lt_of_lt_of_le h2 (h.trans h1)) (lt_irrefl _)
      have hs₀ := (hin i₀ hi₀).1
      have ht₀ := (hin i₀ hi₀).2
      have hst₀ := hst i₀ hi₀
      have hIH := ih S' hS'sub (t i₀) ht₀
        (fun j hj => hst j (Finset.mem_of_mem_erase hj))
        (fun j hj => ⟨hafter j hj, (hin j (Finset.mem_of_mem_erase hj)).2⟩)
        (fun j hj k hk hjk => hdisj j (Finset.mem_of_mem_erase hj) k
          (Finset.mem_of_mem_erase hk) hjk)
        (by
          intro x y hx hxy hy hgapS'
          apply hgap x y (hs₀.trans (hst₀.le.trans hx)) hxy hy
          intro i hi
          by_cases hii : i = i₀
          · subst hii
            exact Or.inl hx
          · exact hgapS' i (Finset.mem_erase.mpr ⟨hii, hi⟩))
      have hfirst : d a (s i₀) ≤ g a (s i₀) := by
        apply hgap a (s i₀) le_rfl hs₀ (hst₀.le.trans ht₀)
        intro i hi
        exact Or.inr (hmin i hi)
      have hsplit : d a b ≤ d a (s i₀) + d (s i₀) (t i₀) + d (t i₀) b := by
        calc d a b ≤ d a (s i₀) + d (s i₀) b := htri a (s i₀) b hs₀ (hst₀.le.trans ht₀)
          _ ≤ d a (s i₀) + (d (s i₀) (t i₀) + d (t i₀) b) := by
              gcongr
              exact htri (s i₀) (t i₀) b hst₀.le ht₀
          _ = d a (s i₀) + d (s i₀) (t i₀) + d (t i₀) b := by ring
      have hgsplit : g a b = g a (s i₀) + g (s i₀) (t i₀) + g (t i₀) b := by
        rw [hadd a (s i₀) b hs₀ (hst₀.le.trans ht₀), hadd (s i₀) (t i₀) b hst₀.le ht₀]
        ring
      have hsumg : ∑ i ∈ S, g (s i) (t i) = g (s i₀) (t i₀) + ∑ i ∈ S', g (s i) (t i) :=
        (Finset.add_sum_erase S _ hi₀).symm
      have hsumd : ∑ i ∈ S, d (s i) (t i) = d (s i₀) (t i₀) + ∑ i ∈ S', d (s i) (t i) :=
        (Finset.add_sum_erase S _ hi₀).symm
      rw [hsumg, hsumd, hgsplit]
      calc d a b + (g (s i₀) (t i₀) + ∑ i ∈ S', g (s i) (t i))
          ≤ d a (s i₀) + d (s i₀) (t i₀) + d (t i₀) b +
              (g (s i₀) (t i₀) + ∑ i ∈ S', g (s i) (t i)) := by gcongr
        _ = d a (s i₀) + d (s i₀) (t i₀) + g (s i₀) (t i₀) +
              (d (t i₀) b + ∑ i ∈ S', g (s i) (t i)) := by ring
        _ ≤ g a (s i₀) + d (s i₀) (t i₀) + g (s i₀) (t i₀) +
              (g (t i₀) b + ∑ i ∈ S', d (s i) (t i)) := by gcongr
        _ = g a (s i₀) + g (s i₀) (t i₀) + g (t i₀) b +
              (d (s i₀) (t i₀) + ∑ i ∈ S', d (s i) (t i)) := by ring

 

theorem disjoint_intervals_total_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (s t : ι → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hst : ∀ i ∈ S, s i < t i)
    (hin : ∀ i ∈ S, a ≤ s i ∧ t i ≤ b)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i) :
    ∑ i ∈ S, (t i - s i) ≤ b - a := by
  have h := chain_bound S s t (fun _ _ => 0) (fun x y => ENNReal.ofReal (y - x))
    (by intro x y z _ _; simp)
    (by
      intro x y z hxy hyz
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hxy) (sub_nonneg.mpr hyz)]
      congr 1
      ring)
    a b hab hst hin hdisj (by intro x y _ _ _ _; exact bot_le)
  simp only [zero_add, sum_const_zero, add_zero] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => (sub_nonneg.mpr (hst i hi).le))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hab)).mp h


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
