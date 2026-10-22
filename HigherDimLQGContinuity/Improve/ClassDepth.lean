import HigherDimLQGContinuity.Improve.ClassCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# An exponential depth absorbs the polynomial class count
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- A quadratic number of classes, multiplied by the requested square-root
number of sites per class, is eventually smaller than the available linear
number of sites. This is the quantitative pigeonhole margin in Step 1. -/
theorem q11_class_depth_eventually {C w : ℝ} (hC : 0 ≤ C) (hw : 0 < w) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ V : ℝ, L ≤ V →
      C * (1 + V) ^ (2 : ℕ) * (Real.exp (V / 2) + 1) + 1 ≤
        (w / 80) * Real.exp V := by
  have hpow : Filter.Tendsto
      (fun V : ℝ => V ^ (2 : ℕ) * Real.exp (-(1 / 2) * V))
      Filter.atTop (nhds 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) (1 / 2)
      (by norm_num)) using 1
    ext V
    norm_num [Real.rpow_natCast]
  have hexp : Filter.Tendsto
      (fun V : ℝ => Real.exp (-(1 / 2) * V)) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (1 / 2) (by norm_num))
  have hmul : Filter.Tendsto
      (fun V : ℝ => (8 * C) * (V ^ (2 : ℕ) * Real.exp (-(1 / 2) * V)))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hpow) using 1
    ring_nf
  have hlim : Filter.Tendsto
      (fun V : ℝ => (8 * C * V ^ (2 : ℕ) + 1) * Real.exp (-(1 / 2) * V))
      Filter.atTop (nhds 0) := by
    convert (hmul.add hexp) using 1 <;> ring_nf
  have hsmall : ∀ᶠ V : ℝ in Filter.atTop,
      (8 * C * V ^ (2 : ℕ) + 1) * Real.exp (-(1 / 2) * V) ≤ w / 80 := by
    exact hlim.eventually (eventually_le_nhds (by linarith : (0 : ℝ) < w / 80))
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨max 1 L₀, le_max_left _ _, fun V hV => ?_⟩
  have hV1 : 1 ≤ V := (le_max_left _ _).trans hV
  have hsm := hL₀ V ((le_max_right _ _).trans hV)
  have he : 1 ≤ Real.exp (V / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpoly : (1 + V) ^ (2 : ℕ) ≤ 4 * V ^ (2 : ℕ) := by nlinarith
  have hleft : C * (1 + V) ^ (2 : ℕ) * (Real.exp (V / 2) + 1) + 1 ≤
      (8 * C * V ^ (2 : ℕ) + 1) * Real.exp (V / 2) := by
    have hCpoly : C * (1 + V) ^ (2 : ℕ) ≤ C * (4 * V ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hpoly hC
    have hsum : Real.exp (V / 2) + 1 ≤ 2 * Real.exp (V / 2) := by linarith
    have hnonneg : 0 ≤ C * (1 + V) ^ (2 : ℕ) := by positivity
    have hmult := mul_le_mul_of_nonneg_left hsum hnonneg
    have hmult2 := mul_le_mul_of_nonneg_right hCpoly (by positivity : 0 ≤ 2 * Real.exp (V / 2))
    nlinarith
  have hright : (8 * C * V ^ (2 : ℕ) + 1) * Real.exp (V / 2) ≤
      (w / 80) * Real.exp V := by
    have hm := mul_le_mul_of_nonneg_right hsm (le_of_lt (Real.exp_pos V))
    have hexpeq : Real.exp (-(1 / 2) * V) * Real.exp V = Real.exp (V / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexpeq] at hm
    exact hm
  exact hleft.trans hright

/-- The actual natural-number inequality used by the finite pigeonhole
principle, including rounding up the required fibre size and down the site
count. -/
theorem q11_class_count_depth {d : ℕ} {K0 w : ℝ}
    (hK0 : 0 ≤ K0) (hw : 0 < w) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ V : ℝ, L ≤ V →
      (q11ClassSet d V (Real.exp (-V)) K0).card *
          ⌈Real.exp (V / 2)⌉₊ ≤
        ⌊(w / 80) * Real.exp V⌋₊ := by
  let C : ℝ := ((1000 * d) ^ d : ℕ) *
    (2 / Real.log 2 + 1) * (2 * K0 / Real.log 2 + 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨L, hL, hdepth⟩ := q11_class_depth_eventually hC hw
  refine ⟨L, hL, fun V hV => ?_⟩
  have hV0 : 0 ≤ V := by linarith
  have hclass : ((q11ClassSet d V (Real.exp (-V)) K0).card : ℝ) ≤
      C * (1 + V) ^ (2 : ℕ) := by
    simpa only [C] using q11_classSet_card_exp_le (d := d) hV0 hK0
  have hn : (⌈Real.exp (V / 2)⌉₊ : ℝ) ≤ Real.exp (V / 2) + 1 :=
    (Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos _))).le
  have hp : (↑((q11ClassSet d V (Real.exp (-V)) K0).card *
      ⌈Real.exp (V / 2)⌉₊) : ℝ) ≤
      C * (1 + V) ^ (2 : ℕ) * (Real.exp (V / 2) + 1) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hclass hn (Nat.cast_nonneg _) (by positivity)
  have hf : (w / 80) * Real.exp V - 1 ≤
      (⌊(w / 80) * Real.exp V⌋₊ : ℝ) :=
    (Nat.sub_one_lt_floor _).le
  have htotal : (↑((q11ClassSet d V (Real.exp (-V)) K0).card *
      ⌈Real.exp (V / 2)⌉₊) : ℝ) ≤
      (⌊(w / 80) * Real.exp V⌋₊ : ℝ) := by
    linarith only [hp, hf, hdepth V hV]
  exact_mod_cast htotal

/-- At the same depth, the number of catalogues is at most one inverse mesh
power. This is the catalogue factor in the final probability sum. -/
theorem q11_class_count_exp_le {d : ℕ} {K0 w : ℝ}
    (hK0 : 0 ≤ K0) (hw : 0 < w) (hw1 : w ≤ 1) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ V : ℝ, L ≤ V →
      ((q11ClassSet d V (Real.exp (-V)) K0).card : ℝ) ≤ Real.exp V := by
  obtain ⟨L, hL, hcount⟩ := q11_class_count_depth (d := d) hK0 hw
  refine ⟨L, hL, fun V hV => ?_⟩
  have hn : 1 ≤ ⌈Real.exp (V / 2)⌉₊ := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hc : (q11ClassSet d V (Real.exp (-V)) K0).card ≤
      ⌊(w / 80) * Real.exp V⌋₊ := by
    calc
      (q11ClassSet d V (Real.exp (-V)) K0).card
          = (q11ClassSet d V (Real.exp (-V)) K0).card * 1 := by omega
      _ ≤ (q11ClassSet d V (Real.exp (-V)) K0).card *
            ⌈Real.exp (V / 2)⌉₊ := Nat.mul_le_mul_left _ hn
      _ ≤ _ := hcount V hV
  have hfloor : (⌊(w / 80) * Real.exp V⌋₊ : ℝ) ≤
      (w / 80) * Real.exp V := Nat.floor_le (by positivity)
  have hw80 : w / 80 ≤ 1 := by linarith
  calc
    ((q11ClassSet d V (Real.exp (-V)) K0).card : ℝ)
        ≤ (⌊(w / 80) * Real.exp V⌋₊ : ℝ) := by exact_mod_cast hc
    _ ≤ (w / 80) * Real.exp V := hfloor
    _ ≤ Real.exp V := by nlinarith [Real.exp_pos V]

end HigherDimLQGContinuity
