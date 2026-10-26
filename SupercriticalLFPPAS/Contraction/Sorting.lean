import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-!
# Ordering the selected intervals (Lemma 4.1, SB2 D6 step 6)

The greedy selection of Lemma 4.1 (paper l. 422–428) returns a finite family of pairwise disjoint nondegenerate open
time intervals. The joining step needs them in increasing order `I₁ < ⋯ < I_k` (SB2 D6 step 6), so that the
complementary segments `H₀ = [a, s₁]`, `H_i = [t_i, s_{i+1}]`, `H_k = [t_k, b]` are defined. `l41_sort_intervals`
enumerates the family as `e 0, …, e (k−1)` with `(e i).2 ≤ (e j).1` for `i < j`.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLFPPAS.Contraction

/-- Two disjoint open intervals, the second nondegenerate and starting no earlier than the first: the first ends
before the second starts. -/
theorem l41_disjoint_intervals_le {I J : ℝ × ℝ} (hJ : J.1 < J.2)
    (hdisj : Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)) (hle : I.1 ≤ J.1) : I.2 ≤ J.1 := by
  by_contra h
  have h1 : J.1 < min I.2 J.2 := lt_min (lt_of_not_ge h) hJ
  have hx1 : J.1 < (J.1 + min I.2 J.2) / 2 := by linarith
  have hx2 : (J.1 + min I.2 J.2) / 2 < min I.2 J.2 := by linarith
  exact Set.disjoint_left.mp hdisj ⟨hle.trans_lt hx1, hx2.trans_le (min_le_left _ _)⟩
    ⟨hx1, hx2.trans_le (min_le_right _ _)⟩

/-- **Increasing enumeration of disjoint intervals.** A finite family of pairwise disjoint nondegenerate open
intervals is `{e 0, …, e (k−1)}` with `e` injective on `[0, k)` and `(e i).2 ≤ (e j).1` for `i < j < k`. -/
theorem l41_sort_intervals (Sel : Finset (ℝ × ℝ)) :
    (∀ I ∈ Sel, ∀ J ∈ Sel, I ≠ J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)) →
    (∀ I ∈ Sel, I.1 < I.2) →
    ∃ (k : ℕ) (e : ℕ → ℝ × ℝ), (Finset.range k).image e = Sel ∧
      Set.InjOn e (Finset.range k : Set ℕ) ∧ ∀ i j, i < j → j < k → (e i).2 ≤ (e j).1 := by
  classical
  induction Sel using Finset.strongInduction with
  | H Sel ih =>
    intro hdisj hpos
    by_cases hne : Sel.Nonempty
    · obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image Sel (fun J => J.1) hne
      obtain ⟨k, e, himg, hinj, hord⟩ := ih (Sel.erase I) (Finset.erase_ssubset hI)
        (fun J hJ J' hJ' hJJ' => hdisj J (Finset.mem_of_mem_erase hJ) J'
          (Finset.mem_of_mem_erase hJ') hJJ')
        (fun J hJ => hpos J (Finset.mem_of_mem_erase hJ))
      have hmem : ∀ i < k, e i ∈ Sel.erase I := fun i hi => by
        rw [← himg]
        exact Finset.mem_image_of_mem e (Finset.mem_range.mpr hi)
      refine ⟨k + 1, fun i => if i < k then e i else I, ?_, ?_, ?_⟩
      · rw [Finset.range_add_one, Finset.image_insert]
        have hcongr : (Finset.range k).image (fun i => if i < k then e i else I) =
            (Finset.range k).image e :=
          Finset.image_congr (fun i hi => by
            simp only [Finset.coe_range, Set.mem_Iio] at hi
            simp only [hi, ↓reduceIte])
        rw [hcongr, himg]
        simp only [lt_irrefl, ↓reduceIte]
        exact Finset.insert_erase hI
      · intro i hi j hj hij
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        by_cases hik : i < k
        · by_cases hjk : j < k
          · simp only [hik, hjk, ↓reduceIte] at hij
            exact hinj (by simpa using hik) (by simpa using hjk) hij
          · simp only [hik, hjk, ↓reduceIte] at hij
            exact absurd hij (Finset.ne_of_mem_erase (hmem i hik))
        · by_cases hjk : j < k
          · simp only [hik, hjk, ↓reduceIte] at hij
            exact absurd hij.symm (Finset.ne_of_mem_erase (hmem j hjk))
          · omega
      · intro i j hij hjk
        by_cases hj : j < k
        · have hi : i < k := hij.trans hj
          simp only [hi, hj, ↓reduceIte]
          exact hord i j hij hj
        · have hi : i < k := by omega
          simp only [hi, hj, ↓reduceIte]
          have hei := hmem i hi
          exact l41_disjoint_intervals_le (hpos I hI)
            (hdisj _ (Finset.mem_of_mem_erase hei) I hI (Finset.ne_of_mem_erase hei))
            (hmax _ (Finset.mem_of_mem_erase hei))
    · refine ⟨0, fun _ => (0, 0), ?_, ?_, ?_⟩
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
      · simp
      · intro i j _ hj
        omega

end SupercriticalLFPPAS.Contraction
