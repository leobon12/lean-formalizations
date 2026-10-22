import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
Finite pruning argument for Section 8 of the higher-dimensional LQG metric proof.
-/

set_option autoImplicit false

namespace HigherDimLQGMetric

/-- The abstract form of Lemma 8.3: repeatedly remove a bad site. -/
theorem pruning {α : Type*} [DecidableEq α] (Z : Finset α) (s : α → ℝ) {q S g b H : ℝ}
    (hqS : 0 < q * S) (hs : ∀ i ∈ Z, q * S ≤ s i ∧ s i ≤ 2 * (q * S)) (hg : 0 < g)
    (hb0 : 0 ≤ b) (hb : 2 * b < g / 2) (hH : 0 < H) (Δ : Finset α → ℝ)
    (good : Finset α → α → Prop) (hstart : g * ∑ i ∈ Z, s i ≤ Δ Z)
    (hundo : ∀ Z' ⊆ Z, ∀ i ∈ Z', ¬ good Z' i → Δ Z' - b * s i ≤ Δ (Z'.erase i))
    (hocc : ∀ Z' ⊆ Z, Δ Z' ≤ H * ∑ i ∈ Z', s i) :
    ∃ Z' ⊆ Z, (∀ i ∈ Z', good Z' i) ∧ g / (4 * H) * Z.card ≤ Z'.card := by
  classical
  have step : ∀ t : Finset α, t ⊆ Z →
      g * ∑ i ∈ Z, s i - b * ∑ i ∈ Z \ t, s i ≤ Δ t →
      ∃ u ⊆ t, (∀ i ∈ u, good u i) ∧
        g * ∑ i ∈ Z, s i - b * ∑ i ∈ Z \ u, s i ≤ Δ u := by
    intro t
    induction t using Finset.strongInductionOn with
    | _ t ih =>
      intro htZ htΔ
      by_cases hgood : ∀ i ∈ t, good t i
      · exact ⟨t, Finset.Subset.refl t, hgood, htΔ⟩
      · push Not at hgood
        obtain ⟨i, hit, hbad⟩ := hgood
        have hsi : i ∈ Z := htZ hit
        have herase : t.erase i ⊂ t := Finset.erase_ssubset hit
        have hdiff : Z \ (t.erase i) = insert i (Z \ t) := Finset.sdiff_erase hsi
        have hnot : i ∉ Z \ t := by simp [hit]
        have hsum : (∑ j ∈ Z \ (t.erase i), s j) =
            s i + ∑ j ∈ Z \ t, s j := by rw [hdiff, Finset.sum_insert hnot]
        have hnext : g * ∑ j ∈ Z, s j -
            b * ∑ j ∈ Z \ (t.erase i), s j ≤ Δ (t.erase i) := by
          rw [hsum]
          have hu := hundo t htZ i hit hbad
          nlinarith
        obtain ⟨u, hut, hgu, hΔu⟩ :=
          ih (t.erase i) herase (Finset.Subset.trans (Finset.erase_subset _ _) htZ) hnext
        exact ⟨u, Finset.Subset.trans hut (Finset.erase_subset _ _), hgu, hΔu⟩
  obtain ⟨u, huZ, hgood, hΔu⟩ := step Z (Finset.Subset.refl Z) (by simpa using hstart)
  refine ⟨u, huZ, hgood, ?_⟩
  have hsumZlo : (q * S) * Z.card ≤ ∑ i ∈ Z, s i := by
    calc
      (q * S) * Z.card = ∑ _i ∈ Z, q * S := by simp [mul_comm]
      _ ≤ ∑ i ∈ Z, s i := Finset.sum_le_sum (fun i hi => (hs i hi).1)
  have hsumUhi : (∑ i ∈ u, s i) ≤ 2 * (q * S) * u.card := by
    calc
      (∑ i ∈ u, s i) ≤ ∑ _i ∈ u, 2 * (q * S) :=
        Finset.sum_le_sum (fun i hi => (hs i (huZ hi)).2)
      _ = 2 * (q * S) * u.card := by simp [mul_comm]
  have hsumDiffhi : (∑ i ∈ Z \ u, s i) ≤ 2 * (q * S) * Z.card := by
    calc
      (∑ i ∈ Z \ u, s i) ≤ ∑ _i ∈ Z \ u, 2 * (q * S) :=
        Finset.sum_le_sum (fun i hi => (hs i (Finset.mem_sdiff.mp hi).1).2)
      _ = 2 * (q * S) * (Z \ u).card := by simp [mul_comm]
      _ ≤ 2 * (q * S) * Z.card := by
        gcongr
        exact Finset.sdiff_subset
  have hΔhi := hocc u huZ
  have hg_half : g / 2 ≤ g - 2 * b := by linarith
  have hq : 0 ≤ q * S := le_of_lt hqS
  have hcard : (g / 2) * (q * S) * Z.card ≤ 2 * H * (q * S) * u.card := by
    have hmul : 0 ≤ (q * S) * Z.card := mul_nonneg hq (Nat.cast_nonneg _)
    have h1 : g * ((q * S) * Z.card) - b * (2 * (q * S) * Z.card) ≤ Δ u := by
      have hgl := mul_le_mul_of_nonneg_left hsumZlo (le_of_lt hg)
      have hbr := mul_le_mul_of_nonneg_left hsumDiffhi hb0
      linarith
    have h2 := mul_le_mul_of_nonneg_left hsumUhi (le_of_lt hH)
    nlinarith
  have hscaled : (g / 2 * (Z.card : ℝ)) * (q * S) ≤
      (2 * H * (u.card : ℝ)) * (q * S) := by nlinarith [hcard]
  have hunscaled := (mul_le_mul_iff_of_pos_right hqS).mp hscaled
  calc
    g / (4 * H) * (Z.card : ℝ) = (g * (Z.card : ℝ)) / (4 * H) := by ring
    _ ≤ (u.card : ℝ) := (div_le_iff₀ (by positivity : 0 < 4 * H)).2 (by
      nlinarith [hunscaled])

end HigherDimLQGMetric
