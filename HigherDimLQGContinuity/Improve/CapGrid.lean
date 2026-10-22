import HigherDimLQGContinuity.Caps.Lemma22

/-!
# Primary-site cap on the finite inspection grid
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The standard grid cap specializes to every possible full-scale primary
site, with a depth index at most `3V+4`. -/
theorem q11_primary_cap_grid {d : ℕ} (hd : 3 ≤ d) :
    ∃ Ccap C c : ℝ, 0 < Ccap ∧ 0 < C ∧ 0 < c ∧
      ∀ V : ℝ, 1 ≤ V →
        let n := ⌈3 * V⌉₊ + 3
        2 * V ≤ (n : ℝ) ∧ (n : ℝ) ≤ 3 * V + 4 ∧
        pinLaw d 10 {g | ∃ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) n 4,
          Ccap * n < |sphereAvg g p.1 p.2|} ≤
          ENNReal.ofReal (C * Real.exp (-c * n)) ∧
        (∀ g : DistRd d,
          (∀ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) n 4,
            |sphereAvg g p.1 p.2| ≤ Ccap * n) →
          ∀ ξ η : ℝ, 0 ≤ ξ → 0 ≤ η →
          ∀ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) n 4,
            |Real.log (scaleS d η 1 p.1 p.2 g /
              scaleS d ξ 1 p.1 p.2 g)| ≤
              (Real.sqrt (2 * d) + Ccap) * |η - ξ| * n) := by
  have hd0 : (0 : ℝ) < d := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (by omega : 1 ≤ d))
  have hκ : 0 < 1 / (20 * Real.sqrt d) := by positivity
  obtain ⟨Ccap, C, c, hcap, hC, hc, hgrid⟩ :=
    lemma22 (by omega : 2 ≤ d)
      (lam := 2) (κ := 1 / (20 * Real.sqrt d)) (c₀ := 1)
      (s := 1) (s₀ := 10)
      (by norm_num) hκ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  refine ⟨Ccap, C, c, hcap, hC, hc, fun V hV => ?_⟩
  let n : ℕ := ⌈3 * V⌉₊ + 3
  have hV0 : 0 ≤ 3 * V := by linarith
  have hnlo : 3 * V + 3 ≤ (n : ℝ) := by
    dsimp [n]
    have hceil : 3 * V ≤ (⌈3 * V⌉₊ : ℝ) := Nat.le_ceil (3 * V)
    push_cast
    linarith
  have hnhi : (n : ℝ) ≤ 3 * V + 4 := by
    dsimp [n]
    have := (Nat.ceil_lt_add_one hV0).le
    push_cast
    linarith
  have hn1 : 1 ≤ n := by dsimp [n]; omega
  have hlog : Real.log (1 + (4 : ℝ)) ≤ (n : ℝ) := by
    have hh : Real.log (5 : ℝ) ≤ 5 := Real.log_le_self (by norm_num)
    have hn : (6 : ℝ) ≤ n := by linarith [hnlo, hV]
    norm_num at ⊢
    linarith
  have hmain := hgrid (n := n) (W := 4) hn1 (by norm_num) (by simpa using hlog)
  simp only [one_mul] at hmain
  exact ⟨by linarith, hnhi, hmain.1, hmain.2⟩

end HigherDimLQGContinuity
