/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import MathFin.Probability.Brownian.Girsanov.GirsanovSimpleTheta
import MathFin.Probability.Brownian.Girsanov.GirsanovSimpleDoleansMoments
import MathFin.Probability.Brownian.Ito.ItoIsometryAdapted
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dyadic Riemann sums against a Brownian motion of a general filtration

Packet PROVE-SEC2-GIR (specification §2.2, proof of Theorem 2.2, `source/spec/p001-048.md` L486–L488 and
the Girsanov densities of Aux. lemma 4, L694–L706).

The vendored Itô integral of `formal-mathfin` is built over the natural filtration of `B`, while the
driving Brownian motion of an evolution (Definition 2.1) is a Brownian motion of an arbitrary filtration
`𝓕` in which the drifts are adapted. The simple-integrand layer of `formal-mathfin` (the simple Doléans
exponential, the simple Girsanov theorem, the discrete Itô isometry) is stated for an arbitrary filtration;
this file builds the passage to the limit along dyadic partitions for a bounded adapted integrand `θ` whose
paths are left-continuous at almost every time.

* `grid n i = i / 2 ^ n`, `cells n = n * 2 ^ n` (the cells of level `n` cover `[0, n]`);
* `riemannSum B θ n t = ∑_{i < n 2^n} θ(i/2^n) (B(min ((i+1)/2^n) t) - B(min (i/2^n) t))`;
* `stepFun θ n u ω = θ(⌊u 2^n⌋/2^n) ω`, the left-point step approximation;
* `integral_step_eq_sum`: `∫₀ᵗ g ⌊u 2^m⌋ du = ∑_j g j (min s_{j+1} t - min s_j t)`;
* `sum_refine`: the refinement identity for increment sums;
* `integral_sq_sum_clamp`: the discrete Itô isometry for a clamped partition.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Girsanov

/-! ### The dyadic grid -/

/-- The dyadic grid point `i / 2 ^ n`. -/
def grid (n i : ℕ) : ℝ≥0 := (i : ℝ≥0) / 2 ^ n

/-- The number of cells of level `n`: `n * 2 ^ n`, so that `grid n (cells n) = n`. -/
def cells (n : ℕ) : ℕ := n * 2 ^ n

theorem coe_grid (n i : ℕ) : ((grid n i : ℝ≥0) : ℝ) = (i : ℝ) / 2 ^ n := by
  simp [grid]

theorem grid_zero (n : ℕ) : grid n 0 = 0 := by simp [grid]

theorem grid_mono (n : ℕ) : Monotone (grid n) := by
  intro i j hij
  unfold grid
  gcongr

theorem grid_cells (n : ℕ) : grid n (cells n) = n := by
  unfold grid cells
  have h : (2 : ℝ≥0) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  field_simp

theorem grid_mul_pow (n m i : ℕ) (hnm : n ≤ m) : grid m (i * 2 ^ (m - n)) = grid n i := by
  apply NNReal.coe_injective
  rw [coe_grid, coe_grid]
  have h2 : (2 : ℝ) ^ m = 2 ^ n * 2 ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnm]
  rw [h2]
  push_cast
  field_simp

theorem grid_le_of_le {n m j : ℕ} (hnm : n ≤ m) : grid n (j / 2 ^ (m - n)) ≤ grid m j := by
  rw [← grid_mul_pow n m _ hnm]
  exact grid_mono m (Nat.div_mul_le_self j _)

/-- The left grid point below `u`: `⌊u 2^n⌋ / 2^n`. -/
def stepIdx (n : ℕ) (u : ℝ) : ℕ := ⌊u * 2 ^ n⌋₊

theorem measurable_stepIdx (n : ℕ) : Measurable (stepIdx n) :=
  Nat.measurable_floor.comp (measurable_id.mul_const _)

theorem coe_grid_stepIdx_le {n : ℕ} {u : ℝ} (hu : 0 ≤ u) : ((grid n (stepIdx n u) : ℝ≥0) : ℝ) ≤ u := by
  rw [coe_grid, stepIdx, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem lt_coe_grid_stepIdx_add {n : ℕ} (u : ℝ) : u < ((grid n (stepIdx n u) : ℝ≥0) : ℝ) + 1 / 2 ^ n := by
  rw [coe_grid, stepIdx, ← add_div, lt_div_iff₀ (by positivity)]
  exact Nat.lt_floor_add_one _

theorem tendsto_coe_grid_stepIdx {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun n => ((grid n (stepIdx n u) : ℝ≥0) : ℝ)) atTop (𝓝 u) := by
  have hlim : Tendsto (fun n : ℕ => u - 1 / 2 ^ n) atTop (𝓝 u) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds (fun n => ?_)
    (fun n => coe_grid_stepIdx_le hu)
  have := lt_coe_grid_stepIdx_add (n := n) u
  linarith

theorem stepIdx_div_pow {n m : ℕ} (hnm : n ≤ m) {u : ℝ} :
    stepIdx m u / 2 ^ (m - n) = stepIdx n u := by
  rw [stepIdx, stepIdx, show ((2 : ℕ) ^ (m - n) : ℕ) = (((2 : ℕ) ^ (m - n) : ℕ) : ℕ) from rfl,
    ← Nat.floor_div_natCast]
  congr 1
  have h2 : (2 : ℝ) ^ m = 2 ^ n * 2 ^ (m - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnm]
  rw [h2]
  push_cast
  field_simp

theorem stepIdx_eq_of_mem {m N : ℕ} {u : ℝ} (h1 : ((grid m N : ℝ≥0) : ℝ) < u)
    (h2 : u < ((grid m (N + 1) : ℝ≥0) : ℝ)) : stepIdx m u = N := by
  rw [coe_grid] at h1 h2
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_iff₀ hp] at h1
  rw [lt_div_iff₀ hp] at h2
  rw [stepIdx, Nat.floor_eq_iff (by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
  push_cast at h2
  exact ⟨h1.le, h2⟩

/-! ### Integrals of dyadic step functions -/

theorem intervalIntegrable_step (g : ℕ → ℝ) (m : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u => g (stepIdx m u)) volume a b := by
  have hmeas : Measurable fun u => g (stepIdx m u) :=
    (measurable_from_nat (f := g)).comp (measurable_stepIdx m)
  set K : ℕ := stepIdx m (max |a| |b|)
  refine (intervalIntegrable_const (c := ∑ j ∈ Finset.range (K + 1), |g j|)).mono_fun'
    hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun u hu => ?_))
  show ‖g (stepIdx m u)‖ ≤ _
  rw [Real.norm_eq_abs]
  have hk : stepIdx m u ≤ K := by
    apply Nat.floor_le_floor
    have hu' : u ≤ max |a| |b| :=
      hu.2.trans (max_le_max (le_abs_self a) (le_abs_self b))
    gcongr
  exact Finset.single_le_sum (f := fun j => |g j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- **The integral of a dyadic step function.** For `t ≤ grid m N`,
`∫₀ᵗ g ⌊u 2^m⌋ du = ∑_{j < N} g j (min s_{j+1} t - min s_j t)` with `s_j = j / 2^m`. -/
theorem integral_step_eq_sum (g : ℕ → ℝ) (m N : ℕ) (t : ℝ≥0) :
    ∫ u in (0 : ℝ)..((min t (grid m N) : ℝ≥0) : ℝ), g (stepIdx m u)
      = ∑ j ∈ Finset.range N,
          g j * (((min (grid m (j + 1)) t : ℝ≥0) : ℝ) - ((min (grid m j) t : ℝ≥0) : ℝ)) := by
  induction N with
  | zero => simp [grid_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih,
      ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_step g m _ _)
        (intervalIntegrable_step g m _ _)]
    congr 1
    set a : ℝ := ((min t (grid m N) : ℝ≥0) : ℝ)
    set b : ℝ := ((min t (grid m (N + 1)) : ℝ≥0) : ℝ)
    have hab : a ≤ b := by
      simp only [a, b, NNReal.coe_le_coe]
      exact min_le_min le_rfl (grid_mono m (Nat.le_succ N))
    have hlen : b - a = ((min (grid m (N + 1)) t : ℝ≥0) : ℝ) - ((min (grid m N) t : ℝ≥0) : ℝ) := by
      simp only [a, b, min_comm t]
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (g := fun _ => g N) (fun u hu => ?_),
      setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul, hlen, mul_comm]
    have h1 : ((grid m N : ℝ≥0) : ℝ) < u := by
      have : a < u := hu.1
      by_cases htN : grid m N ≤ t
      · have ha : a = ((grid m N : ℝ≥0) : ℝ) := by simp only [a]; rw [min_eq_right htN]
        rwa [ha] at this
      · push Not at htN
        have hb : b = t := by
          simp only [b]
          rw [min_eq_left (htN.le.trans (grid_mono m (Nat.le_succ N)))]
        have ha : a = t := by simp only [a]; rw [min_eq_left htN.le]
        exact absurd hu.2 (by rw [hb]; exact not_lt.2 (by rw [← ha]; exact hu.1.le))
    have h2 : u < ((grid m (N + 1) : ℝ≥0) : ℝ) :=
      hu.2.trans_le (by simp only [b, NNReal.coe_le_coe]; exact min_le_right _ _)
    simp only [stepIdx_eq_of_mem h1 h2]

theorem integral_step_eq_sum' (g : ℕ → ℝ) {m N : ℕ} {t : ℝ≥0} (ht : t ≤ grid m N) :
    ∫ u in (0 : ℝ)..(t : ℝ), g (stepIdx m u)
      = ∑ j ∈ Finset.range N,
          g j * (((min (grid m (j + 1)) t : ℝ≥0) : ℝ) - ((min (grid m j) t : ℝ≥0) : ℝ)) := by
  rw [← integral_step_eq_sum, min_eq_left ht]

/-! ### Increment sums: number of cells, refinement -/

/-- Cells beyond the time `t` contribute nothing to a clamped sum. -/
theorem sum_clamp_cells_eq {s : ℕ → ℝ≥0} (hs : Monotone s) (c : ℕ → ℝ) (F : ℝ≥0 → ℝ)
    {N N' : ℕ} (hN : N ≤ N') {t : ℝ≥0} (ht : t ≤ s N) :
    ∑ i ∈ Finset.range N', c i * (F (min (s (i + 1)) t) - F (min (s i) t))
      = ∑ i ∈ Finset.range N, c i * (F (min (s (i + 1)) t) - F (min (s i) t)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Finset.sum_range_add, add_eq_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : t ≤ s (N + i) := ht.trans (hs (Nat.le_add_right _ _))
  have h2 : t ≤ s (N + i + 1) := h1.trans (hs (Nat.le_succ _))
  rw [min_eq_right h1, min_eq_right h2, sub_self, mul_zero]

/-- **Refinement of an increment sum.** Splitting each cell into `K` subcells. -/
theorem sum_refine (c : ℕ → ℝ) (F : ℕ → ℝ) (N K : ℕ) (hK : 0 < K) :
    ∑ i ∈ Finset.range N, c i * (F ((i + 1) * K) - F (i * K))
      = ∑ j ∈ Finset.range (N * K), c (j / K) * (F (j + 1) - F j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]
    congr 1
    have hdiv : ∀ r ∈ Finset.range K, (N * K + r) / K = N := fun r hr => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt (Finset.mem_range.1 hr),
        zero_add]
    rw [Finset.sum_congr rfl fun r hr => by rw [hdiv r hr], ← Finset.mul_sum]
    congr 1
    exact (Finset.sum_range_sub (fun r => F (N * K + r)) K).symm

theorem grid_mul_two_pow (n m : ℕ) : grid m (n * 2 ^ m) = n := by
  unfold grid
  have h : (2 : ℝ≥0) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  field_simp

/-! ### The clamped discrete Itô isometry -/

/-- The clamp of `x` to `[a, b]`. -/
def clamp (a b x : ℝ≥0) : ℝ≥0 := min (max x a) b

theorem clamp_mono (a b : ℝ≥0) : Monotone (clamp a b) := fun _ _ h =>
  min_le_min (max_le_max h le_rfl) le_rfl

theorem clamp_zero_left (b x : ℝ≥0) : clamp 0 b x = min x b := by
  simp [clamp]

theorem le_clamp {a b x : ℝ≥0} (hx : x ≤ b) : x ≤ clamp a b x :=
  le_min (le_max_left _ _) hx

theorem clamp_of_lt {a b x : ℝ≥0} (hx : b < x) : clamp a b x = b :=
  min_eq_right ((hx.le).trans (le_max_left _ _))

section Isometry

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- The cut multiplier `v j` (set to `0` for cells beyond `b`), adapted to the clamped points. -/
private def cutMult (s : ℕ → ℝ≥0) (b : ℝ≥0) (v : ℕ → Ω → ℝ) (j : ℕ) : Ω → ℝ :=
  if s j ≤ b then v j else 0

private theorem cutMult_measurable {s : ℕ → ℝ≥0} {v : ℕ → Ω → ℝ}
    (hv : ∀ j, Measurable[𝓕 (s j)] (v j)) (a b : ℝ≥0) (j : ℕ) :
    Measurable[𝓕 (clamp a b (s j))] (cutMult s b v j) := by
  unfold cutMult
  split_ifs with h
  · exact (hv j).mono (𝓕.mono (le_clamp h)) le_rfl
  · exact measurable_const

private theorem cutMult_memLp {s : ℕ → ℝ≥0} {v : ℕ → Ω → ℝ} (hvL2 : ∀ j, MemLp (v j) 2 P)
    (b : ℝ≥0) (j : ℕ) : MemLp (cutMult s b v j) 2 P := by
  unfold cutMult
  split_ifs
  · exact hvL2 j
  · exact MemLp.zero

private theorem cutMult_term {s : ℕ → ℝ≥0} (hs : Monotone s) (v : ℕ → Ω → ℝ) (a b : ℝ≥0)
    (j : ℕ) (ω : Ω) :
    cutMult s b v j ω * (B (clamp a b (s (j + 1))) ω - B (clamp a b (s j)) ω)
      = v j ω * (B (clamp a b (s (j + 1))) ω - B (clamp a b (s j)) ω) := by
  unfold cutMult
  split_ifs with h
  · rfl
  · push Not at h
    rw [clamp_of_lt h, clamp_of_lt (h.trans_le (hs (Nat.le_succ j)))]
    simp

/-- **The discrete Itô isometry on a clamped partition** (`clamp a b` of a monotone partition), for
multipliers `v j` that are `𝓕 (s j)`-measurable (not necessarily `𝓕 (clamp a b (s j))`-measurable). -/
theorem integral_sq_sum_clamp (hB : IsFilteredPreBrownian B 𝓕 P) {s : ℕ → ℝ≥0}
    (hs : Monotone s) {v : ℕ → Ω → ℝ} (hv : ∀ j, Measurable[𝓕 (s j)] (v j))
    (hvL2 : ∀ j, MemLp (v j) 2 P) (a b : ℝ≥0) (N : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range N,
        v j ω * (B (clamp a b (s (j + 1))) ω - B (clamp a b (s j)) ω)) ^ 2 ∂P
      = ∑ j ∈ Finset.range N,
          (∫ ω, v j ω ^ 2 ∂P) * (((clamp a b (s (j + 1)) : ℝ≥0) : ℝ) - clamp a b (s j)) := by
  have h := MathFin.ItoIsometryAdapted.ito_isometry_discrete hB (N := N)
    (t := fun j => clamp a b (s j)) (fun i j hij => clamp_mono a b (hs hij))
    (cutMult_measurable hv a b) (cutMult_memLp hvL2 b)
  simp only [cutMult_term hs] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold cutMult
  split_ifs with hj
  · rfl
  · push Not at hj
    rw [clamp_of_lt hj, clamp_of_lt (hj.trans_le (hs (Nat.le_succ j)))]
    simp

theorem memLp_sum_clamp (hB : IsFilteredPreBrownian B 𝓕 P) {s : ℕ → ℝ≥0}
    (hs : Monotone s) {v : ℕ → Ω → ℝ} (hv : ∀ j, Measurable[𝓕 (s j)] (v j))
    (hvL2 : ∀ j, MemLp (v j) 2 P) (a b : ℝ≥0) (N : ℕ) :
    MemLp (fun ω => ∑ j ∈ Finset.range N,
        v j ω * (B (clamp a b (s (j + 1))) ω - B (clamp a b (s j)) ω)) 2 P := by
  have : (fun ω => ∑ j ∈ Finset.range N,
        v j ω * (B (clamp a b (s (j + 1))) ω - B (clamp a b (s j)) ω))
      = ∑ j ∈ Finset.range N, fun ω =>
        cutMult s b v j ω * (B (clamp a b (s (j + 1))) ω - B (clamp a b (s j)) ω) := by
    ext ω
    simp only [Finset.sum_apply, cutMult_term hs]
  rw [this]
  exact memLp_finsetSum' _ fun j _ =>
    MathFin.ItoIsometryAdapted.memLp_adapted_mul_increment hB
      (clamp_mono a b (hs (Nat.le_succ j))) (cutMult_measurable hv a b j) (cutMult_memLp hvL2 b j)

end Isometry

/-! ### Riemann sums and step approximations -/

section Riemann

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-- The dyadic left-point Riemann sum of level `n` at time `t`:
`∑_{i < n 2^n} θ(i/2^n) (B(min ((i+1)/2^n) t) - B(min (i/2^n) t))` (the `formal-mathfin`
`simpleStochSum` of the dyadic partition with left-point multipliers). -/
def riemannSum (B θ : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (cells n),
    θ (grid n i) ω * (B (min (grid n (i + 1)) t) ω - B (min (grid n i) t) ω)

theorem riemannSum_eq_simpleStochSum (n : ℕ) (t : ℝ≥0) :
    riemannSum B θ n t
      = MathFin.SimpleDoleansMoments.simpleStochSum (X := B) (grid n) (fun i => θ (grid n i))
        (cells n) t := rfl

/-- The left-point step approximation `θ(⌊u 2^n⌋ / 2^n)` of `θ`, indexed by real time `u`. -/
def stepFun (θ : ℝ≥0 → Ω → ℝ) (n : ℕ) (u : ℝ) (ω : Ω) : ℝ := θ (grid n (stepIdx n u)) ω

theorem measurable_stepFun_time (θ : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Measurable fun u => stepFun θ n u ω :=
  (measurable_from_nat (f := fun j => θ (grid n j) ω)).comp (measurable_stepIdx n)

/-- The two increment sums of levels `n ≤ m`, written on the partition of level `m`. -/
theorem riemannSum_sub_eq {n m : ℕ} (hnm : n ≤ m) {t : ℝ≥0} (htn : t ≤ n) (ω : Ω) :
    riemannSum B θ n t ω - riemannSum B θ m t ω
      = ∑ j ∈ Finset.range (n * 2 ^ m),
          (θ (grid n (j / 2 ^ (m - n))) ω - θ (grid m j) ω) *
            (B (clamp 0 t (grid m (j + 1))) ω - B (clamp 0 t (grid m j)) ω) := by
  have hK : 0 < 2 ^ (m - n) := pow_pos two_pos _
  have hcells : cells n * 2 ^ (m - n) = n * 2 ^ m := by
    rw [cells, Nat.mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]
  have h1 : riemannSum B θ n t ω
      = ∑ j ∈ Finset.range (n * 2 ^ m), θ (grid n (j / 2 ^ (m - n))) ω *
          (B (min (grid m (j + 1)) t) ω - B (min (grid m j) t) ω) := by
    rw [← hcells, ← sum_refine (fun i => θ (grid n i) ω)
      (fun j => B (min (grid m j) t) ω) (cells n) _ hK, riemannSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [grid_mul_pow n m _ hnm, grid_mul_pow n m _ hnm]
  have h2 : riemannSum B θ m t ω
      = ∑ j ∈ Finset.range (n * 2 ^ m), θ (grid m j) ω *
          (B (min (grid m (j + 1)) t) ω - B (min (grid m j) t) ω) := by
    rw [riemannSum]
    exact sum_clamp_cells_eq (grid_mono m) (fun j => θ (grid m j) ω) (fun x => B x ω)
      (Nat.mul_le_mul_right _ hnm) (by rw [grid_mul_two_pow]; exact htn)
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [clamp_zero_left, clamp_zero_left]
  ring

theorem memLp_two_of_bdd [IsFiniteMeasure P] {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {C : ℝ}
    (hfC : ∀ ω, |f ω| ≤ C) : MemLp f 2 P :=
  MemLp.of_bound hf C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfC ω)

variable [IsProbabilityMeasure P]

/-- **The Itô isometry for the difference of two Riemann sums**, `t ≤ n ≤ m`:
`E[(S_n(t) - S_m(t))²] = E ∫₀ᵗ (θⁿ - θᵐ)² du` with the left-point step approximations. -/
theorem integral_sq_riemannSum_sub (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) {n m : ℕ} (hnm : n ≤ m)
    {t : ℝ≥0} (htn : t ≤ n) :
    ∫ ω, (riemannSum B θ n t ω - riemannSum B θ m t ω) ^ 2 ∂P
      = ∫ ω, (∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ n u ω - stepFun θ m u ω) ^ 2) ∂P := by
  set v : ℕ → Ω → ℝ := fun j ω => θ (grid n (j / 2 ^ (m - n))) ω - θ (grid m j) ω with hv_def
  have hvm : ∀ j, Measurable[𝓕 (grid m j)] (v j) := fun j =>
    (((hθm _).mono (𝓕.mono (grid_le_of_le hnm))).measurable).sub (hθm _).measurable
  have hvb : ∀ j ω, |v j ω| ≤ 2 * C := fun j ω => by
    simp only [hv_def]
    exact (abs_sub _ _).trans (by linarith [hθb (grid n (j / 2 ^ (m - n))) ω, hθb (grid m j) ω])
  have hvL2 : ∀ j, MemLp (v j) 2 P := fun j =>
    memLp_two_of_bdd ((hvm j).mono (𝓕.le _) le_rfl).aestronglyMeasurable (hvb j)
  have hsum := integral_sq_sum_clamp hB (grid_mono m) hvm hvL2 0 t (n * 2 ^ m)
  simp_rw [riemannSum_sub_eq hnm htn]
  rw [hsum]
  have hint : ∀ j ∈ Finset.range (n * 2 ^ m), Integrable (fun ω => v j ω ^ 2 *
      (((clamp 0 t (grid m (j + 1)) : ℝ≥0) : ℝ) - clamp 0 t (grid m j))) P := fun j _ =>
    ((hvL2 j).integrable_sq).mul_const _
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ hint]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have hstep := integral_step_eq_sum' (fun j => v j ω ^ 2) (m := m) (N := n * 2 ^ m)
    (t := t) (by rw [grid_mul_two_pow]; exact htn)
  simp only [clamp_zero_left] at hstep ⊢
  rw [← hstep]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [hv_def, stepFun, stepIdx_div_pow hnm]

end Riemann

/-! ### Convergence of the step approximations -/

section Convergence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-- The pathwise regularity used for Riemann approximation: for almost every `ω`, the path
`θ(·, ω)` is left-continuous at Lebesgue-almost every time. -/
def IsRiemannRegular (P : Measure Ω) (θ : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ u ∂(volume : Measure ℝ),
    ContinuousWithinAt (fun s => θ s ω) (Set.Iic u.toNNReal) u.toNNReal

theorem tendsto_stepFun {ω : Ω} {u : ℝ}
    (hu : ContinuousWithinAt (fun s => θ s ω) (Set.Iic u.toNNReal) u.toNNReal) :
    Tendsto (fun n => stepFun θ n u ω) atTop (𝓝 (θ u.toNNReal ω)) := by
  rcases le_or_gt u 0 with h0 | h0
  · have hidx : ∀ n, stepIdx n u = 0 := fun n => by
      rw [stepIdx, Nat.floor_eq_zero]
      exact (mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)).trans_lt one_pos
    simp only [stepFun, hidx, grid_zero, Real.toNNReal_of_nonpos h0]
    exact tendsto_const_nhds
  · refine hu.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩)
    · rw [← NNReal.tendsto_coe, Real.coe_toNNReal _ h0.le]
      exact tendsto_coe_grid_stepIdx h0.le
    · change grid n (stepIdx n u) ≤ u.toNNReal
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h0.le]
      exact coe_grid_stepIdx_le h0.le

theorem abs_stepFun_le {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (n : ℕ) (u : ℝ) (ω : Ω) :
    |stepFun θ n u ω| ≤ C := hθb _ _

theorem measurable_stepFun_uncurry (hθm : ∀ t, Measurable (θ t)) (n : ℕ) :
    Measurable fun p : Ω × ℝ => stepFun θ n p.2 p.1 := by
  have hG : Measurable fun q : Ω × ℕ => θ (grid n q.2) q.1 :=
    measurable_from_prod_countable_left fun k => hθm (grid n k)
  exact hG.comp (measurable_fst.prodMk ((measurable_stepIdx n).comp measurable_snd))

theorem sq_sub_le_of_abs_le {x y C : ℝ} (hx : |x| ≤ C) (hy : |y| ≤ C) : (x - y) ^ 2 ≤ (2 * C) ^ 2 := by
  have h : |x - y| ≤ 2 * C := (abs_sub _ _).trans (by linarith)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Pathwise: `∫₀ᵗ (θⁿ - θᵐ)² → 0` as `n, m → ∞`. -/
theorem tendsto_integral_sq_stepFun_sub {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) {ω : Ω}
    (hω : ∀ᵐ u ∂(volume : Measure ℝ),
      ContinuousWithinAt (fun s => θ s ω) (Set.Iic u.toNNReal) u.toNNReal) (t : ℝ) :
    Tendsto (fun p : ℕ × ℕ => ∫ u in (0 : ℝ)..t, (stepFun θ p.1 u ω - stepFun θ p.2 u ω) ^ 2)
      (atTop ×ˢ atTop) (𝓝 0) := by
  have key : Tendsto
      (fun p : ℕ × ℕ => ∫ u in (0 : ℝ)..t, (stepFun θ p.1 u ω - stepFun θ p.2 u ω) ^ 2)
      (atTop ×ˢ atTop) (𝓝 (∫ u in (0 : ℝ)..t, (0 : ℝ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2 * C) ^ 2)
      (Eventually.of_forall fun p => (((measurable_stepFun_time θ p.1 ω).sub
        (measurable_stepFun_time θ p.2 ω)).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun p => ae_of_all _ fun u _ => ?_) intervalIntegrable_const
      (hω.mono fun u hu _ => ?_)
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sq_sub_le_of_abs_le (abs_stepFun_le hθb p.1 u ω) (abs_stepFun_le hθb p.2 u ω)
    · have h := tendsto_stepFun hu
      have h2 : Tendsto (fun p : ℕ × ℕ => stepFun θ p.1 u ω - stepFun θ p.2 u ω)
          (atTop ×ˢ atTop) (𝓝 (θ u.toNNReal ω - θ u.toNNReal ω)) :=
        (h.comp tendsto_fst).sub (h.comp tendsto_snd)
      rw [sub_self] at h2
      simpa using h2.pow 2
  simpa using key

end Convergence

/-! ### The `L²` limit of the Riemann sums -/

section Limit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

theorem eLpNorm_two_eq_sqrt {f : Ω → ℝ} (hf : MemLp f 2 P) :
    eLpNorm f 2 P = ENNReal.ofReal (√(∫ ω, f ω ^ 2 ∂P)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, Real.sqrt_eq_rpow]
  congr 2
  · refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp [Real.norm_eq_abs]
  · norm_num

theorem riemannSum_eq_sum_clamp (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    riemannSum B θ n t ω = ∑ j ∈ Finset.range (cells n),
      θ (grid n j) ω * (B (clamp 0 t (grid n (j + 1))) ω - B (clamp 0 t (grid n j)) ω) := by
  simp only [riemannSum, clamp_zero_left]

theorem stronglyMeasurable_riemannSum (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) (n : ℕ) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] (riemannSum B θ n t) := by
  have heq : riemannSum B θ n t = ∑ j ∈ Finset.range (cells n), fun ω =>
      cutMult (grid n) t (fun j => θ (grid n j)) j ω *
        (B (clamp 0 t (grid n (j + 1))) ω - B (clamp 0 t (grid n j)) ω) := by
    ext ω
    rw [riemannSum_eq_sum_clamp, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ =>
      (cutMult_term (B := B) (grid_mono n) (fun j => θ (grid n j)) 0 t j ω).symm
  rw [heq]
  refine Finset.stronglyMeasurable_sum _ fun j _ => ?_
  have hc := cutMult_measurable (𝓕 := 𝓕) (s := grid n) (v := fun j => θ (grid n j))
    (fun j => (hθm _).measurable) 0 t j
  have hle : ∀ x, clamp 0 t x ≤ t := fun x => min_le_right _ _
  have h1 : Measurable[𝓕 t] (B (clamp 0 t (grid n (j + 1)))) :=
    hB.measurable_eval_of_le (hle _)
  have h2 : Measurable[𝓕 t] (B (clamp 0 t (grid n j))) := hB.measurable_eval_of_le (hle _)
  exact ((hc.mono (𝓕.mono (hle _)) le_rfl).mul (h1.sub h2)).stronglyMeasurable

theorem memLp_riemannSum (hB : IsFilteredPreBrownian B 𝓕 P) [IsFiniteMeasure P]
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (n : ℕ) (t : ℝ≥0) :
    MemLp (riemannSum B θ n t) 2 P := by
  have h := memLp_sum_clamp hB (grid_mono n) (v := fun j => θ (grid n j))
    (fun j => (hθm _).measurable)
    (fun j => memLp_two_of_bdd ((hθm _).mono (𝓕.le _)).aestronglyMeasurable (hθb _))
    0 t (cells n)
  refine h.ae_eq (ae_of_all _ fun ω => ?_)
  rw [riemannSum_eq_sum_clamp]

variable [IsProbabilityMeasure P]

theorem measurable_integral_sq_stepFun_sub (hθm : ∀ t, Measurable (θ t)) (n m : ℕ) (t : ℝ≥0) :
    StronglyMeasurable fun ω =>
      ∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ n u ω - stepFun θ m u ω) ^ 2 := by
  have hF : StronglyMeasurable fun p : Ω × ℝ =>
      (stepFun θ n p.2 p.1 - stepFun θ m p.2 p.1) ^ 2 :=
    (((measurable_stepFun_uncurry hθm n).sub (measurable_stepFun_uncurry hθm m)).pow_const
      2).stronglyMeasurable
  have h := hF.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ)))
  convert h using 1
  funext ω
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]

/-- `E ∫₀ᵗ (θⁿ - θᵐ)² → 0` as `n, m → ∞`. -/
theorem tendsto_integral_integral_sq_stepFun_sub (hθm : ∀ t, Measurable (θ t)) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    Tendsto (fun p : ℕ × ℕ =>
        ∫ ω, (∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ p.1 u ω - stepFun θ p.2 u ω) ^ 2) ∂P)
      (atTop ×ˢ atTop) (𝓝 0) := by
  have key : Tendsto (fun p : ℕ × ℕ =>
        ∫ ω, (∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ p.1 u ω - stepFun θ p.2 u ω) ^ 2) ∂P)
      (atTop ×ˢ atTop) (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * C) ^ 2 * t)
      (Eventually.of_forall fun p =>
        (measurable_integral_sq_stepFun_sub hθm p.1 p.2 t).aestronglyMeasurable)
      (Eventually.of_forall fun p => ae_of_all _ fun ω => ?_) (integrable_const _)
      (hθreg.mono fun ω hω => tendsto_integral_sq_stepFun_sub hθb hω t)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
      (f := fun u => (stepFun θ p.1 u ω - stepFun θ p.2 u ω) ^ 2) (C := (2 * C) ^ 2)
      (fun u _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact sq_sub_le_of_abs_le (abs_stepFun_le hθb p.1 u ω) (abs_stepFun_le hθb p.2 u ω))
    rwa [sub_zero, NNReal.abs_eq] at h
  simpa using key

/-- `I` is an `𝓕 t`-measurable `L²(P)` limit of the dyadic Riemann sums at time `t`. -/
def IsRiemannLimit (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B θ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (I : Ω → ℝ) : Prop :=
  StronglyMeasurable[𝓕 t] I ∧
    Tendsto (fun n => eLpNorm (riemannSum B θ n t - I) 2 P) atTop (𝓝 0)

/-- **Existence of the Itô integral as an `L²` limit of dyadic Riemann sums** in an arbitrary
filtration, for a bounded adapted integrand that is left-continuous at almost every time. -/
theorem exists_isRiemannLimit (hB : IsFilteredPreBrownian B 𝓕 P) (hθm : StronglyAdapted 𝓕 θ)
    {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    ∃ I, IsRiemannLimit P 𝓕 B θ t I := by
  have hθm' : ∀ s, Measurable (θ s) := fun s => ((hθm s).mono (𝓕.le s)).measurable
  have hL2 := memLp_riemannSum hB hθm hθb (t := t)
  set F : ℕ → Lp ℝ 2 P := fun n => (hL2 n).toLp _ with hF
  have hdist : ∀ N n : ℕ, t ≤ (N : ℝ≥0) → N ≤ n → dist (F n) (F N)
      = √(∫ ω, (∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ N u ω - stepFun θ n u ω) ^ 2) ∂P) := by
    intro N n htN hNn
    rw [dist_comm, Lp.dist_def, eLpNorm_congr_ae
      ((MemLp.coeFn_toLp (hL2 N)).sub (MemLp.coeFn_toLp (hL2 n))),
      eLpNorm_two_eq_sqrt ((hL2 N).sub (hL2 n)), ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    congr 1
    exact integral_sq_riemannSum_sub hB hθm hθb hNn htN
  have hcau : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have h := tendsto_integral_integral_sq_stepFun_sub hθm' hθb hθreg t
    have hev := h.eventually (gt_mem_nhds (pow_pos hε 2))
    rw [Filter.eventually_prod_iff] at hev
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := hev
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hpa
    obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 hpb
    obtain ⟨c, hc⟩ := exists_nat_ge (t : ℝ)
    refine ⟨max (max a b) c, fun n hn => ?_⟩
    have hN : t ≤ (max (max a b) c : ℕ) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hc.trans (by exact_mod_cast le_max_right _ _)
    rw [hdist _ _ hN hn, Real.sqrt_lt' hε]
    exact hab (ha _ ((le_max_left _ _).trans (le_max_left _ _)))
      (hb _ (((le_max_right _ _).trans (le_max_left _ _)).trans hn))
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have hLm : AEStronglyMeasurable[𝓕 t] (⇑L) P := by
    have hclosed := isClosed_aestronglyMeasurable (F := ℝ) (p := 2) (μ := P) (𝓕.le t)
    refine hclosed.mem_of_tendsto hL (Eventually.of_forall fun n => ?_)
    exact ⟨riemannSum B θ n t, stronglyMeasurable_riemannSum hB hθm n t,
      MemLp.coeFn_toLp (hL2 n)⟩
  refine ⟨hLm.mk _, hLm.stronglyMeasurable_mk, ?_⟩
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F L).1 hL
  refine h.congr fun n => eLpNorm_congr_ae ?_
  exact (MemLp.coeFn_toLp (hL2 n)).sub hLm.ae_eq_mk

end Limit

/-! ### The Itô integral as a chosen `L²` limit -/

section StochIntegral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-- **The Itô integral** `∫₀ᵗ θ dB`, defined as an `𝓕 t`-measurable `L²(P)`-limit of the dyadic
left-point Riemann sums (a limit chosen by `Classical.epsilon`, exactly as `limUnder` chooses a limit;
`isRiemannLimit_stochIntegral` shows that it is such a limit for every bounded adapted integrand that
is left-continuous at almost every time, `exists_isRiemannLimit`). It is unique up to `P`-null
sets (`stochIntegral_ae_eq_of_isRiemannLimit`). -/
def stochIntegral (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B θ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    Ω → ℝ :=
  Classical.epsilon (IsRiemannLimit P 𝓕 B θ t)

variable [IsProbabilityMeasure P]

theorem isRiemannLimit_stochIntegral (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    IsRiemannLimit P 𝓕 B θ t (stochIntegral P 𝓕 B θ t) :=
  Classical.epsilon_spec (exists_isRiemannLimit hB hθm hθb hθreg t)

theorem tendstoInMeasure_riemannSum (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    TendstoInMeasure P (fun n => riemannSum B θ n t) atTop (stochIntegral P 𝓕 B θ t) := by
  have h := isRiemannLimit_stochIntegral hB hθm hθb hθreg t
  exact tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    (fun n => (memLp_riemannSum hB hθm hθb n t).aestronglyMeasurable)
    ((h.1.mono (𝓕.le t)).aestronglyMeasurable) h.2

theorem stochIntegral_ae_eq_of_isRiemannLimit (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {t : ℝ≥0} {I : Ω → ℝ} (hI : IsRiemannLimit P 𝓕 B θ t I) :
    stochIntegral P 𝓕 B θ t =ᵐ[P] I := by
  have h1 := tendstoInMeasure_riemannSum hB hθm hθb hθreg t
  have h2 : TendstoInMeasure P (fun n => riemannSum B θ n t) atTop I :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
      (fun n => (memLp_riemannSum hB hθm hθb n t).aestronglyMeasurable)
      ((hI.1.mono (𝓕.le t)).aestronglyMeasurable) hI.2
  exact tendstoInMeasure_ae_unique h1 h2

theorem memLp_stochIntegral (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) : MemLp (stochIntegral P 𝓕 B θ t) 2 P := by
  have h := isRiemannLimit_stochIntegral hB hθm hθb hθreg t
  obtain ⟨n, hn⟩ := (h.2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))).exists
  have hdiff : MemLp (riemannSum B θ n t - stochIntegral P 𝓕 B θ t) 2 P :=
    ⟨((memLp_riemannSum hB hθm hθb n t).aestronglyMeasurable).sub
      (h.1.mono (𝓕.le t)).aestronglyMeasurable, hn.trans ENNReal.one_lt_top⟩
  have := (memLp_riemannSum hB hθm hθb n t).sub hdiff
  simpa using this

end StochIntegral

/-! ### The drift and quadratic sums as integrals of step functions -/

section Drift

variable {Ω : Type*} {θ : ℝ≥0 → Ω → ℝ}

theorem simpleDrift_eq_integral {n : ℕ} {t : ℝ≥0} (htn : t ≤ n) (ω : Ω) :
    MathFin.simpleDrift (grid n) (fun i => θ (grid n i)) (cells n) t ω
      = ∫ u in (0 : ℝ)..(t : ℝ), stepFun θ n u ω := by
  rw [show (∫ u in (0 : ℝ)..(t : ℝ), stepFun θ n u ω)
      = ∫ u in (0 : ℝ)..(t : ℝ), (fun j => θ (grid n j) ω) (stepIdx n u) from rfl,
    integral_step_eq_sum' (fun j => θ (grid n j) ω) (by rw [grid_cells]; exact htn),
    MathFin.simpleDrift]

theorem simpleQuadVar_eq_integral {n : ℕ} {t : ℝ≥0} (htn : t ≤ n) (ω : Ω) :
    MathFin.SimpleDoleansMoments.simpleQuadVar (grid n) (fun i => θ (grid n i)) (cells n) t ω
      = ∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ n u ω) ^ 2 := by
  rw [show (∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ n u ω) ^ 2)
      = ∫ u in (0 : ℝ)..(t : ℝ), (fun j => θ (grid n j) ω ^ 2) (stepIdx n u) from rfl,
    integral_step_eq_sum' (fun j => θ (grid n j) ω ^ 2) (by rw [grid_cells]; exact htn),
    MathFin.SimpleDoleansMoments.simpleQuadVar]

theorem tendsto_integral_stepFun {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) {ω : Ω}
    (hω : ∀ᵐ u ∂(volume : Measure ℝ),
      ContinuousWithinAt (fun s => θ s ω) (Set.Iic u.toNNReal) u.toNNReal) (t : ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun n => ∫ u in (0 : ℝ)..t, g (stepFun θ n u ω)) atTop
      (𝓝 (∫ u in (0 : ℝ)..t, g (θ u.toNNReal ω))) := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Set.Icc (-C) C, ‖g x‖ ≤ M :=
    (isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    (Eventually.of_forall fun n =>
      (hg.measurable.comp (measurable_stepFun_time θ n ω)).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ fun u _ => hM _ (abs_le.1 (hθb _ _)))
    intervalIntegrable_const (hω.mono fun u hu _ => (hg.tendsto _).comp (tendsto_stepFun hu))

end Drift

end Girsanov

end InteractingSLE
