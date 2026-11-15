/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Bernstein drivers: continuous drivers read from finitely many values of a path (near facts, piece 1)

Packet PROVE-GW2-BUF (round 7). Path functionals on `ℝ≥0 → ℝ` with the product σ-algebra are measurable only through
countably many coordinates. The real Loewner images are continuous functionals of a continuous driver in the uniform
norm on `[0, T]`. They become measurable through drivers that read finitely many values of the path: Bernstein
polynomials of the grid values `w (T k / n)`.

* `bsum T n v s`: the Bernstein sum of grid values `v : Fin (n+1) → ℝ` at the clamped time `s / T`;
  **`continuous_bsum`**, **`abs_bsum_sub_le`** (`|bsum v − bsum v'| ≤ ‖v − v'‖`);
* `gridVals T n w`, `measurable_gridVals`; `bdrv T n w := bsum T n (gridVals T n w)` (causal: reads `w` on `[0, T]`);
* **`tendsto_bdrv`**: for a path continuous on `[0, T]` (`T > 0`), the Bernstein drivers converge to it uniformly on
  `[0, T]`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal unitInterval

namespace InteractingSLE.Theorem14.GW2Bh

/-- The clamped unit time `s / T` of a real time. -/
def unitTime (T : ℝ≥0) (s : ℝ) : unitInterval := projIcc 0 1 zero_le_one (s / T)

theorem continuous_unitTime (T : ℝ≥0) : Continuous (unitTime T) :=
  continuous_projIcc.comp (continuous_id.div_const _)

/-- The grid time `T z_k` of the `k`-th Bernstein node. -/
def gridTime (T : ℝ≥0) {n : ℕ} (k : Fin (n + 1)) : ℝ≥0 := T * ⟨(bernstein.z k : ℝ), (bernstein.z k).2.1⟩

theorem gridTime_le (T : ℝ≥0) {n : ℕ} (k : Fin (n + 1)) : gridTime T k ≤ T := by
  unfold gridTime
  calc T * ⟨(bernstein.z k : ℝ), (bernstein.z k).2.1⟩ ≤ T * 1 :=
        mul_le_mul_of_nonneg_left (show (⟨(bernstein.z k : ℝ), (bernstein.z k).2.1⟩ : ℝ≥0) ≤ 1 from
          (bernstein.z k).2.2) zero_le
    _ = T := mul_one T

/-- **The Bernstein sum of grid values** at the clamped time. -/
def bsum (T : ℝ≥0) (n : ℕ) (v : Fin (n + 1) → ℝ) (s : ℝ) : ℝ :=
  ∑ k : Fin (n + 1), bernstein n k (unitTime T s) * v k

theorem continuous_bsum (T : ℝ≥0) (n : ℕ) (v : Fin (n + 1) → ℝ) : Continuous (bsum T n v) :=
  continuous_finsetSum _ fun k _ => ((bernstein n k).continuous.comp (continuous_unitTime T)).mul continuous_const

/-- **The Bernstein sum is `1`-Lipschitz in the grid values** (sup norm). -/
theorem abs_bsum_sub_le (T : ℝ≥0) (n : ℕ) (v v' : Fin (n + 1) → ℝ) (s : ℝ) :
    |bsum T n v s - bsum T n v' s| ≤ ‖v - v'‖ := by
  have he : bsum T n v s - bsum T n v' s = ∑ k : Fin (n + 1), bernstein n k (unitTime T s) * (v k - v' k) := by
    unfold bsum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [he]
  calc |∑ k : Fin (n + 1), bernstein n k (unitTime T s) * (v k - v' k)|
      ≤ ∑ k : Fin (n + 1), |bernstein n k (unitTime T s) * (v k - v' k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin (n + 1), bernstein n k (unitTime T s) * ‖v - v'‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg bernstein_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ bernstein_nonneg
        have h := norm_le_pi_norm (v - v') k
        rwa [Pi.sub_apply, Real.norm_eq_abs] at h
    _ = ‖v - v'‖ := by
        rw [← Finset.sum_mul, bernstein.probability, one_mul]

/-- The grid values of a path. -/
def gridVals (T : ℝ≥0) (n : ℕ) (w : ℝ≥0 → ℝ) : Fin (n + 1) → ℝ := fun k => w (gridTime T k)

theorem measurable_gridVals (T : ℝ≥0) (n : ℕ) : Measurable (gridVals T n) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- **The `n`-th Bernstein driver of a path on `[0, T]`.** -/
def bdrv (T : ℝ≥0) (n : ℕ) (w : ℝ≥0 → ℝ) : ℝ → ℝ := bsum T n (gridVals T n w)

theorem continuous_bdrv (T : ℝ≥0) (n : ℕ) (w : ℝ≥0 → ℝ) : Continuous (bdrv T n w) := continuous_bsum T n _

/-- The Bernstein driver reads the path on `[0, T]` only. -/
theorem bdrv_congr (T : ℝ≥0) (n : ℕ) {w w' : ℝ≥0 → ℝ} (h : ∀ u ≤ T, w u = w' u) : bdrv T n w = bdrv T n w' := by
  unfold bdrv gridVals
  congr 1
  funext k
  exact h _ (gridTime_le T k)

/-- **Bernstein drivers converge uniformly on `[0, T]`** to a path continuous on `[0, T]`. -/
theorem tendsto_bdrv {T : ℝ≥0} (hT : 0 < T) {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ s ∈ Icc (0 : ℝ) T, |bdrv T n w s - w s.toNNReal| ≤ δ := by
  -- the path on the unit interval
  have hcont : Continuous fun x : unitInterval => w (T * ⟨(x : ℝ), x.2.1⟩) := by
    refine hw.comp_continuous (continuous_const.mul (continuous_induced_rng.2 continuous_subtype_val)) fun x => ?_
    show T * ⟨(x : ℝ), x.2.1⟩ ≤ T
    calc T * ⟨(x : ℝ), x.2.1⟩ ≤ T * 1 :=
          mul_le_mul_of_nonneg_left (show (⟨(x : ℝ), x.2.1⟩ : ℝ≥0) ≤ 1 from x.2.2) zero_le
      _ = T := mul_one T
  set f : C(unitInterval, ℝ) := ⟨fun x => w (T * ⟨(x : ℝ), x.2.1⟩), hcont⟩ with hf
  have hlim := ContinuousMap.tendsto_iff_tendstoUniformly.1 (bernsteinApproximation_uniform f)
  have hball := Metric.tendstoUniformly_iff.1 hlim δ hδ
  filter_upwards [hball] with n hn s hs
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : s / T ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hs.1 hTr.le, (div_le_one hTr).2 hs.2⟩
  have hunit : (unitTime T s : ℝ) = s / T := by
    unfold unitTime
    rw [projIcc_of_mem _ hsT]
  have hb : bdrv T n w s = bernsteinApproximation n f (unitTime T s) := by
    rw [bernsteinApproximation.apply]
    unfold bdrv bsum gridVals gridTime
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul]
    rfl
  have hfv : f (unitTime T s) = w s.toNNReal := by
    rw [hf]
    change w (T * ⟨(unitTime T s : ℝ), (unitTime T s).2.1⟩) = w s.toNNReal
    congr 1
    apply NNReal.eq
    change (T : ℝ) * (unitTime T s : ℝ) = (s.toNNReal : ℝ)
    rw [hunit, Real.coe_toNNReal _ hs.1, mul_div_cancel₀ _ hTr.ne']
  rw [hb, ← hfv]
  have h1 := hn (unitTime T s)
  rw [Real.dist_eq, abs_sub_comm] at h1
  exact h1.le

end InteractingSLE.Theorem14.GW2Bh
