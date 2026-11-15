/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovDensity

/-!
# A martingale with the bracket of `∫ θ dB` is `∫ θ dB`

Packet PROVE-LOCEXT-A, step 3 (the second line of (HL4): `(M_t − m, v) = ∫₀ᵗ a_s dB_s`). Source: Aux. lemma 55,
proof (`source/spec/p241-288.md` L163–L182, p. 248).

Let `B` be a Brownian motion of an arbitrary filtration `𝓕` and `θ` a bounded progressive integrand that is
left-continuous at almost every time (the hypotheses of the landed Itô integral `Girsanov.stochIntegral`, the `L²`
limit of the dyadic left-point Riemann sums). If `X` is a square-integrable `𝓕`-martingale such that
`X B − ∫₀^· θ` is a martingale and `E[X_t²] = E ∫₀ᵗ θ²`, then `X_t = ∫₀ᵗ θ dB` almost surely
(`ae_eq_stochIntegral_of_brackets`). This is Revuz–Yor IV.(1.8)/(2.?) in the elementary form needed here:
`E[(X_t − R_n)²] = E ∫₀ᵗ (θ − θ_n)²` for the Riemann sums `R_n` with step integrands `θ_n`, by the discrete
Itô isometry, the cross bracket `E[θ_j (B_{t_{j+1}} − B_{t_j}) X_t] = E[θ_j ∫_{t_j}^{t_{j+1}} θ]`, and the
variance; the right side tends to `0` by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-! ### Products with martingales -/

/-- For a martingale `X`, `s ≤ t`, and `Y ∈ L²(𝓕_s)` with `X_t ∈ L²`: `E[Y X_t] = E[Y X_s]`. -/
theorem integral_mul_martingale_eq [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P)
    (hXL2 : ∀ t, MemLp (X t) 2 P) {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ}
    (hYm : StronglyMeasurable[𝓕 s] Y) (hYL2 : MemLp Y 2 P) :
    ∫ ω, Y ω * X t ω ∂P = ∫ ω, Y ω * X s ω ∂P := by
  have hint : Integrable (fun ω => Y ω * X t ω) P := hYL2.integrable_mul (hXL2 t)
  have hc := condExp_mul_of_stronglyMeasurable_left hYm hint ((hXL2 t).integrable one_le_two)
  rw [← integral_condExp (𝓕.le s) (f := fun ω => Y ω * X t ω)]
  refine integral_congr_ae ?_
  filter_upwards [hc, hX.condExp_ae_eq hst] with ω h1 h2
  have e : (fun ω => Y ω * X t ω) = Y * X t := rfl
  rw [e, h1, Pi.mul_apply, h2]

/-- For a martingale `X`, `s ≤ t`, and an `𝓕_s`-measurable `Y` with `Y X_t`, `Y X_s` integrable:
`E[Y X_t] = E[Y X_s]`. -/
theorem integral_mul_martingale_eq_of_integrable [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓕 P) {s t : ℝ≥0} (hst : s ≤ t) {Y : Ω → ℝ} (hYm : StronglyMeasurable[𝓕 s] Y)
    (hint : Integrable (fun ω => Y ω * X t ω) P) :
    ∫ ω, Y ω * X t ω ∂P = ∫ ω, Y ω * X s ω ∂P := by
  have hc := condExp_mul_of_stronglyMeasurable_left hYm hint (hX.integrable t)
  rw [← integral_condExp (𝓕.le s) (f := fun ω => Y ω * X t ω)]
  refine integral_congr_ae ?_
  filter_upwards [hc, hX.condExp_ae_eq hst] with ω h1 h2
  have e : (fun ω => Y ω * X t ω) = Y * X t := rfl
  rw [e, h1, Pi.mul_apply, h2]

theorem memLp_two_B (hB : IsFilteredPreBrownian B 𝓕 P) (t : ℝ≥0) : MemLp (B t) 2 P :=
  (hB.toIsPreBrownianReal.hasLaw_eval t).memLp (memLp_id_gaussianReal' 2 (by simp))

theorem memLp_top_of_bdd {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C) :
    MemLp Y ∞ P :=
  memLp_top_of_bound hY C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hYb ω)

theorem abs_drift_le {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (t : ℝ≥0) (ω : Ω) : |drift θ t ω| ≤ C * t := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
    (f := fun u : ℝ => θ u.toNNReal ω) (C := C) fun u _ => by rw [Real.norm_eq_abs]; exact hθb _ _
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.coe_nonneg] at this

/-- **The cross bracket on one cell**: for `a ≤ b ≤ t` and a bounded `𝓕_a`-measurable `Y`,
`E[Y (B_b − B_a) X_t] = E[Y ∫_a^b θ]`, from the martingales `X` and `X B − ∫₀^· θ`. -/
theorem integral_cell_cross [IsProbabilityMeasure P] (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓕 P) (hXL2 : ∀ t, MemLp (X t) 2 P)
    (hXB : Martingale (fun t ω => X t ω * B t ω - drift θ t ω) 𝓕 P) {a b t : ℝ≥0} (hab : a ≤ b) (hbt : b ≤ t)
    {Y : Ω → ℝ} (hYm : StronglyMeasurable[𝓕 a] Y) {C' : ℝ} (hYb : ∀ ω, |Y ω| ≤ C') :
    ∫ ω, Y ω * (B b ω - B a ω) * X t ω ∂P = ∫ ω, Y ω * (drift θ b ω - drift θ a ω) ∂P := by
  have hBm : ∀ s, StronglyMeasurable[𝓕 s] (B s) := hB.stronglyAdapted
  have hDm : ∀ s, StronglyMeasurable[𝓕 s] (drift θ s) := fun s =>
    stronglyMeasurable_integral_comp hθ measurable_id s
  have hYinf : MemLp Y ∞ P := memLp_top_of_bdd ((hYm.mono (𝓕.le a)).aestronglyMeasurable) hYb
  have hDint : ∀ s, Integrable (drift θ s) P := fun s =>
    (memLp_top_of_bdd ((hDm s).mono (𝓕.le s)).aestronglyMeasurable (abs_drift_le hθb s)).integrable le_top
  have hYB : ∀ s, MemLp (fun ω => Y ω * B s ω) 2 P := fun s => (memLp_two_B hB s).mul' hYinf
  have hYBX : ∀ s s', Integrable (fun ω => Y ω * B s ω * X s' ω) P := fun s s' =>
    (hYB s).integrable_mul (hXL2 s')
  have hYD : ∀ s, Integrable (fun ω => Y ω * drift θ s ω) P := fun s => (hDint s).mul_of_top_right hYinf
  -- Step 1: move `X_t` to `X_b`
  have h1 : ∫ ω, Y ω * (B b ω - B a ω) * X t ω ∂P = ∫ ω, Y ω * (B b ω - B a ω) * X b ω ∂P :=
    integral_mul_martingale_eq hX hXL2 hbt
      (((hYm.mono (𝓕.mono hab)).mul ((hBm b).sub ((hBm a).mono (𝓕.mono hab)))))
      ((memLp_two_B hB b).sub (memLp_two_B hB a) |>.mul' hYinf |>.congr_norm
        (((hYm.mono (𝓕.mono hab)).mul ((hBm b).sub ((hBm a).mono (𝓕.mono hab)))).mono
          (𝓕.le b)).aestronglyMeasurable (ae_of_all _ fun ω => by simp))
  -- Step 2: `E[Y B_a X_b] = E[Y B_a X_a]`
  have h2 : ∫ ω, Y ω * B a ω * X b ω ∂P = ∫ ω, Y ω * B a ω * X a ω ∂P :=
    integral_mul_martingale_eq hX hXL2 hab (hYm.mul (hBm a)) (hYB a)
  -- Step 3: `E[Y M_b] = E[Y M_a]`
  have hMint : ∀ s, Integrable (fun ω => Y ω * (X s ω * B s ω - drift θ s ω)) P := fun s => by
    have := (hYBX s s).sub (hYD s)
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.sub_apply]; ring
  have h3 := integral_mul_martingale_eq_of_integrable hXB hab hYm (hMint b)
  -- Step 4: algebra
  have e1 : ∀ ω, Y ω * (B b ω - B a ω) * X b ω = Y ω * (X b ω * B b ω - drift θ b ω) +
      Y ω * drift θ b ω - Y ω * B a ω * X b ω := fun ω => by ring
  have e2 : ∀ ω, Y ω * B a ω * X a ω = Y ω * (X a ω * B a ω - drift θ a ω) + Y ω * drift θ a ω :=
    fun ω => by ring
  have hsum : Integrable (fun ω => Y ω * (X b ω * B b ω - drift θ b ω) + Y ω * drift θ b ω) P :=
    (hMint b).add (hYD b)
  rw [h1, integral_congr_ae (ae_of_all _ e1), integral_sub hsum (hYBX a b),
    integral_add (hMint b) (hYD b), h2, integral_congr_ae (ae_of_all _ e2),
    integral_add (hMint a) (hYD a), h3]
  have e3 : ∀ ω, Y ω * (drift θ b ω - drift θ a ω) = Y ω * drift θ b ω - Y ω * drift θ a ω :=
    fun ω => by ring
  rw [integral_congr_ae (ae_of_all _ e3), integral_sub (hYD b) (hYD a)]
  ring

/-! ### Step integrands against a second function -/

theorem intervalIntegrable_step_mul (g : ℕ → ℝ) {φ : ℝ → ℝ} (hφ : ∀ a b, IntervalIntegrable φ volume a b)
    (m : ℕ) (a b : ℝ) : IntervalIntegrable (fun u => g (stepIdx m u) * φ u) volume a b := by
  have hmeas : Measurable fun u => g (stepIdx m u) :=
    (measurable_from_nat (f := g)).comp (measurable_stepIdx m)
  set K : ℕ := stepIdx m (max |a| |b|)
  rw [intervalIntegrable_iff]
  refine ((intervalIntegrable_iff.1 (hφ a b))).bdd_mul (c := ∑ j ∈ Finset.range (K + 1), |g j|)
    hmeas.aestronglyMeasurable ((ae_restrict_iff' measurableSet_uIoc).2 (ae_of_all _ fun u hu => ?_))
  rw [Real.norm_eq_abs]
  have hk : stepIdx m u ≤ K := by
    apply Nat.floor_le_floor
    have hu' : u ≤ max |a| |b| :=
      hu.2.trans (max_le_max (le_abs_self a) (le_abs_self b))
    gcongr
  exact Finset.single_le_sum (f := fun j => |g j|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- `∫₀^{t ∧ s_N} g⌊u 2^m⌋ φ(u) du = ∑_{j<N} g j ∫_{s_j ∧ t}^{s_{j+1} ∧ t} φ`, `s_j = j/2^m`. -/
theorem integral_step_mul_eq_sum (g : ℕ → ℝ) {φ : ℝ → ℝ} (hφ : ∀ a b, IntervalIntegrable φ volume a b)
    (m N : ℕ) (t : ℝ≥0) :
    ∫ u in (0 : ℝ)..((min t (grid m N) : ℝ≥0) : ℝ), g (stepIdx m u) * φ u
      = ∑ j ∈ Finset.range N, g j * ∫ u in ((min (grid m j) t : ℝ≥0) : ℝ)..((min (grid m (j + 1)) t : ℝ≥0) : ℝ),
          φ u := by
  induction N with
  | zero => simp [grid_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih,
      ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_step_mul g hφ m _ _)
        (intervalIntegrable_step_mul g hφ m _ _)]
    congr 1
    set a : ℝ := ((min t (grid m N) : ℝ≥0) : ℝ)
    set b : ℝ := ((min t (grid m (N + 1)) : ℝ≥0) : ℝ)
    have hab : a ≤ b := by
      simp only [a, b, NNReal.coe_le_coe]
      exact min_le_min le_rfl (grid_mono m (Nat.le_succ N))
    have ha' : ((min (grid m N) t : ℝ≥0) : ℝ) = a := by simp only [a, min_comm]
    have hb' : ((min (grid m (N + 1)) t : ℝ≥0) : ℝ) = b := by simp only [b, min_comm]
    rw [ha', hb', intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      ← integral_const_mul, integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
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

/-! ### The moments of the Riemann sums -/

section Moments

variable [IsProbabilityMeasure P] {C : ℝ}

/-- The increment weights `Δ_j = s_{j+1} ∧ t − s_j ∧ t` of level `n`. -/
def cellLen (n j : ℕ) (t : ℝ≥0) : ℝ :=
  ((min (grid n (j + 1)) t : ℝ≥0) : ℝ) - ((min (grid n j) t : ℝ≥0) : ℝ)

/-- **The discrete Itô isometry for the Riemann sums**: `E[R_n²] = E ∑_j θ_j² Δ_j`. -/
theorem integral_riemannSum_sq (hB : IsFilteredPreBrownian B 𝓕 P) (hθm : StronglyAdapted 𝓕 θ)
    (hθb : ∀ t ω, |θ t ω| ≤ C) (n : ℕ) (t : ℝ≥0) :
    ∫ ω, riemannSum B θ n t ω ^ 2 ∂P =
      ∫ ω, ∑ j ∈ Finset.range (cells n), θ (grid n j) ω ^ 2 * cellLen n j t ∂P := by
  have hvL2 : ∀ j, MemLp (θ (grid n j)) 2 P := fun j =>
    memLp_two_of_bdd ((hθm _).mono (𝓕.le _)).aestronglyMeasurable (hθb _)
  have h := integral_sq_sum_clamp hB (grid_mono n) (v := fun j => θ (grid n j))
    (fun j => (hθm _).measurable) hvL2 0 t (cells n)
  simp only [clamp_zero_left] at h
  simp only [riemannSum]
  rw [h, integral_finsetSum _ fun j _ => ((hvL2 j).integrable_sq).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, cellLen]

/-- **The cross bracket of the Riemann sums with `X`**: `E[R_n X_t] = E ∑_j θ_j (∫_{t_j}^{t_{j+1}} θ)`. -/
theorem integral_riemannSum_mul (hB : IsFilteredPreBrownian B 𝓕 P) (hθ : IsStronglyProgressive 𝓕 θ)
    (hθb : ∀ t ω, |θ t ω| ≤ C) {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P) (hXL2 : ∀ t, MemLp (X t) 2 P)
    (hXB : Martingale (fun t ω => X t ω * B t ω - drift θ t ω) 𝓕 P) (n : ℕ) (t : ℝ≥0) :
    ∫ ω, riemannSum B θ n t ω * X t ω ∂P =
      ∫ ω, ∑ j ∈ Finset.range (cells n), θ (grid n j) ω *
        (drift θ (min (grid n (j + 1)) t) ω - drift θ (min (grid n j) t) ω) ∂P := by
  have hθm : StronglyAdapted 𝓕 θ := hθ.stronglyAdapted
  have hDm : ∀ s, StronglyMeasurable[𝓕 s] (drift θ s) := fun s =>
    stronglyMeasurable_integral_comp hθ measurable_id s
  have hθinf : ∀ j, MemLp (θ (grid n j)) ∞ P := fun j =>
    memLp_top_of_bdd ((hθm _).mono (𝓕.le _)).aestronglyMeasurable (hθb _)
  have hDint : ∀ s, Integrable (drift θ s) P := fun s =>
    (memLp_top_of_bdd ((hDm s).mono (𝓕.le s)).aestronglyMeasurable (abs_drift_le hθb s)).integrable le_top
  have hterm : ∀ j, Integrable (fun ω => θ (grid n j) ω *
      (B (min (grid n (j + 1)) t) ω - B (min (grid n j) t) ω) * X t ω) P := fun j => by
    have hY2 : MemLp (fun ω => θ (grid n j) ω *
        (B (min (grid n (j + 1)) t) ω - B (min (grid n j) t) ω)) 2 P :=
      ((memLp_two_B hB (min (grid n (j + 1)) t)).sub (memLp_two_B hB (min (grid n j) t))).mul' (hθinf j)
    exact hY2.integrable_mul (hXL2 t)
  have hterm2 : ∀ j, Integrable (fun ω => θ (grid n j) ω *
      (drift θ (min (grid n (j + 1)) t) ω - drift θ (min (grid n j) t) ω)) P := fun j =>
    ((hDint _).sub (hDint _)).mul_of_top_right (hθinf j)
  have hsplit : (fun ω => riemannSum B θ n t ω * X t ω) = fun ω => ∑ j ∈ Finset.range (cells n),
      θ (grid n j) ω * (B (min (grid n (j + 1)) t) ω - B (min (grid n j) t) ω) * X t ω := by
    funext ω; simp only [riemannSum, Finset.sum_mul]
  rw [hsplit, integral_finsetSum _ fun j _ => hterm j, integral_finsetSum _ fun j _ => hterm2 j]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjt : grid n j ≤ t
  · have ha : min (grid n j) t = grid n j := min_eq_left hjt
    have hY : StronglyMeasurable[𝓕 (min (grid n j) t)] (θ (grid n j)) := by rw [ha]; exact hθm _
    exact integral_cell_cross hB hθ hθb hX hXL2 hXB (min_le_min (grid_mono n (Nat.le_succ j)) le_rfl)
      (min_le_right _ _) hY (hθb _)
  · push Not at hjt
    have h1 : min (grid n j) t = t := min_eq_right hjt.le
    have h2 : min (grid n (j + 1)) t = t := min_eq_right (hjt.le.trans (grid_mono n (Nat.le_succ j)))
    simp [h1, h2]

/-- **The pointwise identity**: for `t ≤ n`, `∫₀ᵗ (θ_n − θ)² = ∑ θ_j² Δ_j − 2 ∑ θ_j ∫_{t_j}^{t_{j+1}} θ + ∫₀ᵗ θ²`. -/
theorem integral_sq_stepFun_sub_eq (hθ : IsStronglyProgressive 𝓕 θ) (hθb : ∀ t ω, |θ t ω| ≤ C) {n : ℕ}
    {t : ℝ≥0} (htn : t ≤ n) (ω : Ω) :
    ∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ n u ω - θ u.toNNReal ω) ^ 2 =
      (∑ j ∈ Finset.range (cells n), θ (grid n j) ω ^ 2 * cellLen n j t) -
        2 * (∑ j ∈ Finset.range (cells n), θ (grid n j) ω *
          (drift θ (min (grid n (j + 1)) t) ω - drift θ (min (grid n j) t) ω)) + quadInt θ t ω := by
  have htc : t ≤ grid n (cells n) := by rw [grid_cells]; exact htn
  have hφ : ∀ a b, IntervalIntegrable (fun u : ℝ => θ u.toNNReal ω) volume a b :=
    intervalIntegrable_time hθ hθb ω
  have hs := intervalIntegrable_step (fun j => θ (grid n j) ω) n 0 t
  have hs2 := intervalIntegrable_step (fun j => θ (grid n j) ω ^ 2) n 0 t
  have hsθ := intervalIntegrable_step_mul (fun j => θ (grid n j) ω) hφ n 0 t
  have hθ2 : IntervalIntegrable (fun u : ℝ => θ u.toNNReal ω ^ 2) volume 0 t :=
    (intervalIntegrable_const (c := C ^ 2)).mono_fun'
      ((measurable_time_of_progressive hθ ω).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun u => by
        beta_reduce
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hθb _ _) 2)
  have e : ∀ u, (stepFun θ n u ω - θ u.toNNReal ω) ^ 2 = θ (grid n (stepIdx n u)) ω ^ 2 -
      2 * (θ (grid n (stepIdx n u)) ω * θ u.toNNReal ω) + θ u.toNNReal ω ^ 2 := fun u => by
    simp only [stepFun]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (hs2.sub (hsθ.const_mul 2)) hθ2,
    intervalIntegral.integral_sub hs2 (hsθ.const_mul 2), intervalIntegral.integral_const_mul]
  have h1 := integral_step_eq_sum' (fun j => θ (grid n j) ω ^ 2) htc
  have h2 := integral_step_mul_eq_sum (fun j => θ (grid n j) ω) hφ n (cells n) t
  rw [min_eq_left htc] at h2
  have hsum : ∑ j ∈ Finset.range (cells n), θ (grid n j) ω *
      (∫ u in ((min (grid n j) t : ℝ≥0) : ℝ)..((min (grid n (j + 1)) t : ℝ≥0) : ℝ), θ u.toNNReal ω) =
      ∑ j ∈ Finset.range (cells n), θ (grid n j) ω *
        (drift θ (min (grid n (j + 1)) t) ω - drift θ (min (grid n j) t) ω) :=
    Finset.sum_congr rfl fun j _ => by
      rw [drift, drift, intervalIntegral.integral_interval_sub_left (hφ _ _) (hφ _ _)]
  rw [h1, h2, hsum, quadInt]
  rfl

/-- **A martingale with the bracket of `∫ θ dB` is `∫ θ dB`**: if `X` is a square-integrable `𝓕`-martingale,
`X B − ∫₀^· θ` is a martingale and `E[X_t²] = E ∫₀ᵗ θ²`, then `X_t = ∫₀ᵗ θ dB` almost surely. -/
theorem stochIntegral_ae_eq_of_brackets (hB : IsFilteredPreBrownian B 𝓕 P) (hθ : IsStronglyProgressive 𝓕 θ)
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P)
    (hXL2 : ∀ t, MemLp (X t) 2 P) (hXB : Martingale (fun t ω => X t ω * B t ω - drift θ t ω) 𝓕 P)
    (hX2 : ∀ t, ∫ ω, X t ω ^ 2 ∂P = ∫ ω, quadInt θ t ω ∂P) (t : ℝ≥0) :
    stochIntegral P 𝓕 B θ t =ᵐ[P] X t := by
  have hθm : StronglyAdapted 𝓕 θ := hθ.stronglyAdapted
  refine stochIntegral_ae_eq_of_isRiemannLimit hB hθm hθb hθreg ⟨hX.1 t, ?_⟩
  -- the measurable pieces
  have hDm : ∀ s, StronglyMeasurable[𝓕 s] (drift θ s) := fun s =>
    stronglyMeasurable_integral_comp hθ measurable_id s
  have hQm : StronglyMeasurable[𝓕 t] (quadInt θ t) :=
    stronglyMeasurable_integral_comp hθ (measurable_id.pow_const 2) t
  set F : ℕ → Ω → ℝ := fun n ω => ∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ n u ω - θ u.toNNReal ω) ^ 2 with hF
  have hFbd : ∀ n ω, |F n ω| ≤ (2 * C) ^ 2 * t := fun n ω => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
      (f := fun u => (stepFun θ n u ω - θ u.toNNReal ω) ^ 2) (C := (2 * C) ^ 2) fun u _ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by
          linarith [abs_stepFun_le hθb n u ω, hθb u.toNNReal ω])) 2
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.coe_nonneg] at this
  have hFform : ∀ n : ℕ, t ≤ (n : ℝ≥0) → F n = fun ω => (∑ j ∈ Finset.range (cells n), θ (grid n j) ω ^ 2 * cellLen n j t) -
      2 * (∑ j ∈ Finset.range (cells n), θ (grid n j) ω *
        (drift θ (min (grid n (j + 1)) t) ω - drift θ (min (grid n j) t) ω)) + quadInt θ t ω :=
    fun n htn => funext fun ω => integral_sq_stepFun_sub_eq hθ hθb htn ω
  have hFmeas : ∀ n : ℕ, t ≤ (n : ℝ≥0) → StronglyMeasurable (F n) := fun n htn => by
    rw [hFform n htn]
    have hθj : ∀ j, Measurable (θ (grid n j)) := fun j => (hθm _).measurable.mono (𝓕.le _) le_rfl
    have hDj : ∀ s, Measurable (drift θ s) := fun s => (hDm s).measurable.mono (𝓕.le s) le_rfl
    have m1 : Measurable fun ω => ∑ j ∈ Finset.range (cells n), θ (grid n j) ω ^ 2 * cellLen n j t :=
      Finset.measurable_fun_sum _ fun j _ => ((hθj j).pow_const 2).mul_const _
    have m2 : Measurable fun ω => ∑ j ∈ Finset.range (cells n), θ (grid n j) ω *
        (drift θ (min (grid n (j + 1)) t) ω - drift θ (min (grid n j) t) ω) :=
      Finset.measurable_fun_sum _ fun j _ => (hθj j).mul ((hDj _).sub (hDj _))
    exact ((m1.sub (m2.const_mul 2)).add (hQm.measurable.mono (𝓕.le t) le_rfl)).stronglyMeasurable
  -- `F n → 0` in expectation
  have hlim : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
    have key : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 (∫ _ω, (0 : ℝ) ∂P)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * C) ^ 2 * t)
        ((eventually_ge_atTop ⌈(t : ℝ)⌉₊).mono fun n hn => (hFmeas n (by
          have : (t : ℝ) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
          exact_mod_cast this)).aestronglyMeasurable)
        (Eventually.of_forall fun n => ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hFbd n ω)
        (integrable_const _) ?_
      filter_upwards [hθreg] with ω hω
      have hinner : Tendsto (fun n => ∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ n u ω - θ u.toNNReal ω) ^ 2)
          atTop (𝓝 (∫ u in (0 : ℝ)..(t : ℝ), (0 : ℝ))) := by
        refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * C) ^ 2)
          (Eventually.of_forall fun n => (((measurable_stepFun_time θ n ω).sub
            (measurable_time_of_progressive hθ ω)).pow_const 2).aestronglyMeasurable)
          (Eventually.of_forall fun n => ae_of_all _ fun u _ => by
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by
              linarith [abs_stepFun_le hθb n u ω, hθb u.toNNReal ω])) 2)
          intervalIntegrable_const ?_
        filter_upwards [hω] with u hu _
        have := ((tendsto_stepFun hu).sub_const (θ u.toNNReal ω)).pow 2
        simpa using this
      simpa using hinner
    simpa using key
  -- the `L²` distance of the Riemann sums from `X_t`
  have hdist : ∀ n : ℕ, t ≤ (n : ℝ≥0) → ∫ ω, (riemannSum B θ n t ω - X t ω) ^ 2 ∂P = ∫ ω, F n ω ∂P := by
    intro n htn
    have hR := memLp_riemannSum hB hθm hθb n t
    have hRX : Integrable (fun ω => riemannSum B θ n t ω * X t ω) P := hR.integrable_mul (hXL2 t)
    have hR2 : Integrable (fun ω => riemannSum B θ n t ω ^ 2) P := hR.integrable_sq
    have hX2i : Integrable (fun ω => X t ω ^ 2) P := (hXL2 t).integrable_sq
    have hθinf : ∀ j, MemLp (θ (grid n j)) ∞ P := fun j =>
      memLp_top_of_bdd ((hθm _).mono (𝓕.le _)).aestronglyMeasurable (hθb _)
    have hDint : ∀ s, Integrable (drift θ s) P := fun s =>
      (memLp_top_of_bdd ((hDm s).mono (𝓕.le s)).aestronglyMeasurable (abs_drift_le hθb s)).integrable le_top
    have hS1 : Integrable (fun ω => ∑ j ∈ Finset.range (cells n), θ (grid n j) ω ^ 2 * cellLen n j t) P :=
      integrable_finsetSum _ fun j _ => ((memLp_two_of_bdd ((hθm _).mono (𝓕.le _)).aestronglyMeasurable
        (hθb _)).integrable_sq).mul_const _
    have hS2 : Integrable (fun ω => ∑ j ∈ Finset.range (cells n), θ (grid n j) ω *
        (drift θ (min (grid n (j + 1)) t) ω - drift θ (min (grid n j) t) ω)) P :=
      integrable_finsetSum _ fun j _ => ((hDint _).sub (hDint _)).mul_of_top_right (hθinf j)
    have hQi : Integrable (quadInt θ t) P :=
      (memLp_top_of_bdd (hQm.mono (𝓕.le t)).aestronglyMeasurable (C := C ^ 2 * t) fun ω => by
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
          (f := fun u : ℝ => θ u.toNNReal ω ^ 2) (C := C ^ 2) fun u _ => by
            rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hθb _ _) 2
        rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.coe_nonneg] at this).integrable le_top
    have e : ∀ ω, (riemannSum B θ n t ω - X t ω) ^ 2 =
        riemannSum B θ n t ω ^ 2 - 2 * (riemannSum B θ n t ω * X t ω) + X t ω ^ 2 := fun ω => by ring
    have hA1 : Integrable (fun ω => riemannSum B θ n t ω ^ 2 - 2 * (riemannSum B θ n t ω * X t ω)) P :=
      hR2.sub (hRX.const_mul 2)
    have hA2 : Integrable (fun ω => (∑ j ∈ Finset.range (cells n), θ (grid n j) ω ^ 2 * cellLen n j t) -
        2 * (∑ j ∈ Finset.range (cells n), θ (grid n j) ω *
          (drift θ (min (grid n (j + 1)) t) ω - drift θ (min (grid n j) t) ω))) P :=
      hS1.sub (hS2.const_mul 2)
    rw [integral_congr_ae (ae_of_all _ e), integral_add hA1 hX2i,
      integral_sub hR2 (hRX.const_mul 2), integral_const_mul, integral_riemannSum_sq hB hθm hθb,
      integral_riemannSum_mul hB hθ hθb hX hXL2 hXB, hX2, hFform n htn,
      integral_add hA2 hQi, integral_sub hS1 (hS2.const_mul 2), integral_const_mul]
  -- conclusion
  have hL2 : ∀ n, MemLp (riemannSum B θ n t - X t) 2 P := fun n =>
    (memLp_riemannSum hB hθm hθb n t).sub (hXL2 t)
  have hev : ∀ᶠ n in atTop, eLpNorm (riemannSum B θ n t - X t) 2 P =
      ENNReal.ofReal (√(∫ ω, F n ω ∂P)) := by
    filter_upwards [eventually_ge_atTop ⌈(t : ℝ)⌉₊] with n hn
    have htn : t ≤ n := by
      have : (t : ℝ) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      exact_mod_cast this
    rw [eLpNorm_two_eq_sqrt (hL2 n)]
    simp only [Pi.sub_apply]
    rw [hdist n htn]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have h1 : Tendsto (fun n => √(∫ ω, F n ω ∂P)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    simpa [Function.comp_def] using this
  have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
  simpa [Function.comp_def] using h2

end Moments

end LocalExt

end InteractingSLE
