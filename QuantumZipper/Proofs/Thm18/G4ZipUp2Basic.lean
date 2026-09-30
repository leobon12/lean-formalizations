import QuantumZipper.Proofs.Zipper.Cor15RezipRegMeas
import QuantumZipper.Proofs.Zipper.E6UpBasic
import QuantumZipper.Proofs.Zipper.WedgeLawRef
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: a measurable *continuous* surrogate driver

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (3). Task
G4-ZIPUP2.

The measurable zip-up `G4ZipUpReadStmt` (`G4ReadDrv.lean`) needs the inverse reverse map
`revMapInv W' T` of a *measurably read* driver `(T, W') = F d` to be a measurable function of
the data `d`. Every device in the repository (`Cor15Group.measurable_revMapInv_param`,
`PushTameAS.measurable_fwdMap_alive`, `tamedUnc`, `revMap` itself) is gated on the driver being
*continuous* in the time variable: `revMap W T` is junk `0` when no solution of the reverse
Loewner equation exists, and existence forces `t ↦ W t` continuous on `[0,T]`. Continuity of a
driver is not a measurable condition for the product σ-algebra on `ℝ≥0 → ℝ`
(`G4ZipUpReadMeas.lean`, docstring), so one must build a driver that is continuous *by
construction* and measurable in the parameter.

This file provides that device: `surDrv N n e` is the dyadic piecewise-linear interpolation of
the values of the driver `e` at the grid points `k/2^n` (`k ≤ N·2^n`), *read through the
measurable dyadic extension* `WedgeLaw.extP` (which agrees with `e` when `e` is continuous,
`extP_of_continuous`). It is

* continuous in `r` for every `e` (`continuous_surDrv`) — so it may be fed to
  `measurable_revMapInv_param` / `PushTameAS.measurable_fwdMap_alive`;
* measurable as a `C(ℝ, ℝ)`-valued function of `e` (`measurable_surDrv`), i.e. jointly
  measurable in `(e, r)`;
* uniformly close to a continuous driver: `|surDrv N n W r − W r| ≤ ε` on `[0,N]` for
  `n` large, uniformly in the grid length `M ≥ N` (`tendsto_surDrv_uniform`).

The limit of the surrogates is taken in `G4ZipUp2Path.lean` (in `C([0,1], ℝ)`), which yields
a measurable path that is continuous for every parameter and equals the rescaled driver when
the driver is continuous; no stability of the Loewner flow is needed.

**Own elementary argument** (measurable dyadic interpolation device).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## 1. The clamping ramp -/

/-- Clamp to `[0,1]`. -/
def ramp (x : ℝ) : ℝ := min (max x 0) 1

theorem continuous_ramp : Continuous ramp := by
  unfold ramp
  exact (continuous_id.max (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))).min
    (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))

theorem ramp_of_nonpos {x : ℝ} (hx : x ≤ 0) : ramp x = 0 := by
  rw [ramp, max_eq_right hx, min_eq_left (zero_le_one : (0 : ℝ) ≤ 1)]

theorem ramp_of_one_le {x : ℝ} (hx : 1 ≤ x) : ramp x = 1 := by
  rw [ramp, max_eq_left (le_trans zero_le_one hx), min_eq_right hx]

theorem ramp_mem (x : ℝ) : ramp x ∈ Icc (0 : ℝ) 1 := by
  simp only [ramp, mem_Icc]
  exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

/-! ## 2. The piecewise-linear dyadic surrogate driver -/

/-- The `n`-th dyadic piecewise-linear surrogate driver on `[0,N]` of the driver `e`: the
interpolant of the values `WedgeLaw.extP e (k/2^n)` at the grid points `k/2^n`, `k ≤ N·2^n`,
based at `WedgeLaw.extP e 0` and extended constantly to the right of `N·2^n`. Continuous in
`r` for every `e` (each term is a clamped ramp times a constant), and measurable in `e`. -/
def surDrv (N n : ℕ) (e : ℝ → ℝ) (r : ℝ) : ℝ :=
  WedgeLaw.extP e 0 + ∑ k ∈ Finset.range (N * 2 ^ n + 1),
    ramp ((2 : ℝ) ^ n * r - k) *
      (WedgeLaw.extP e (((k : ℝ) + 1) / 2 ^ n) - WedgeLaw.extP e ((k : ℝ) / 2 ^ n))

theorem continuous_surDrv (N n : ℕ) (e : ℝ → ℝ) :
    Continuous fun r => surDrv N n e r := by
  unfold surDrv
  refine continuous_const.add (continuous_finsetSum _ fun k _ => ?_)
  exact (continuous_ramp.comp ((continuous_const.mul continuous_id).sub continuous_const)).mul
    continuous_const

/-! ## 3. Telescoping of ramped increments -/

/-- Telescoping of ramped increments: if the ramps are `1` below the index `j` and `0` above it,
only the term at `j` is fractional. -/
theorem sum_ramp_mul_sub {M : ℕ} (f θ : ℕ → ℝ) {j : ℕ} (hj : j + 1 ≤ M)
    (h1 : ∀ k < j, θ k = 1) (h2 : ∀ k, j < k → k < M → θ k = 0) :
    ∑ k ∈ Finset.range M, θ k * (f (k + 1) - f k) =
      (f j - f 0) + θ j * (f (j + 1) - f j) := by
  have hM : M = (j + 1) + (M - (j + 1)) := (Nat.add_sub_cancel' hj).symm
  rw [hM, Finset.sum_range_add]
  have hzero : ∑ i ∈ Finset.range (M - (j + 1)),
      θ (j + 1 + i) * (f (j + 1 + i + 1) - f (j + 1 + i)) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have hi' : i < M - (j + 1) := Finset.mem_range.1 hi
      rw [h2 (j + 1 + i) (by omega) (by omega), zero_mul]
  rw [hzero, add_zero, Finset.sum_range_succ]
  have hcongr : ∑ k ∈ Finset.range j, θ k * (f (k + 1) - f k) =
      ∑ k ∈ Finset.range j, (f (k + 1) - f k) :=
    Finset.sum_congr rfl fun k hk => by rw [h1 k (Finset.mem_range.1 hk), one_mul]
  rw [hcongr, Finset.sum_range_sub]

/-- Value of the surrogate at a point where the ramps are pinned: only the grid point `j/2^n`
and its successor enter. -/
theorem surDrv_eq_grid {N n : ℕ} {e : ℝ → ℝ} {r : ℝ} {j : ℕ} (hj : j + 1 ≤ N * 2 ^ n + 1)
    (h1 : ∀ k < j, 1 ≤ (2 : ℝ) ^ n * r - k)
    (h2 : ∀ k, j < k → k < N * 2 ^ n + 1 → (2 : ℝ) ^ n * r - k ≤ 0) :
    surDrv N n e r = WedgeLaw.extP e 0 +
      (WedgeLaw.extP e ((j : ℝ) / 2 ^ n) - WedgeLaw.extP e 0) +
      ramp ((2 : ℝ) ^ n * r - j) *
        (WedgeLaw.extP e (((j : ℝ) + 1) / 2 ^ n) - WedgeLaw.extP e ((j : ℝ) / 2 ^ n)) := by
  have h := sum_ramp_mul_sub (f := fun k : ℕ => WedgeLaw.extP e ((k : ℝ) / 2 ^ n))
    (θ := fun k : ℕ => ramp ((2 : ℝ) ^ n * r - k)) hj
    (fun k hk => ramp_of_one_le (h1 k hk)) (fun k hk hkM => ramp_of_nonpos (h2 k hk hkM))
  have h' : ∑ k ∈ Finset.range (N * 2 ^ n + 1),
      ramp ((2 : ℝ) ^ n * r - k) *
        (WedgeLaw.extP e (((k : ℝ) + 1) / 2 ^ n) - WedgeLaw.extP e ((k : ℝ) / 2 ^ n)) =
      (WedgeLaw.extP e ((j : ℝ) / 2 ^ n) - WedgeLaw.extP e ((0 : ℕ) / 2 ^ n)) +
        ramp ((2 : ℝ) ^ n * r - j) *
          (WedgeLaw.extP e (((j : ℝ) + 1) / 2 ^ n) - WedgeLaw.extP e ((j : ℝ) / 2 ^ n)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using h
  rw [surDrv, h', Nat.cast_zero, zero_div]
  ring

/-! ## 4. Uniform convergence to a continuous driver -/

/-- **The surrogate converges uniformly to a continuous driver on `[0,N]`**, uniformly in
the grid length `M ≥ N` (Heine–Cantor on `[0, N+1]`). -/
theorem tendsto_surDrv_uniform {W : ℝ → ℝ} (hW : Continuous W) (N : ℕ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ M : ℕ, N ≤ M → ∀ r ∈ Icc (0 : ℝ) N,
      |surDrv M n W r - W r| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff_le.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := (N : ℝ) + 1)).uniformContinuousOn_of_continuous
      hW.continuousOn) ε hε
  have htend : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n < δ :=
    htend.eventually (eventually_lt_nhds hδ)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine eventually_atTop.2 ⟨n₀, fun n hn M hNM r hr => ?_⟩
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2nn : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n
  have hδn : (1 : ℝ) / 2 ^ n ≤ δ := by
    have h := hn₀ n hn
    rw [one_div_pow] at h
    exact h.le
  have hr0 : 0 ≤ r := hr.1
  have hrN : r ≤ N := hr.2
  set j : ℕ := ⌊(2 : ℝ) ^ n * r⌋₊ with hjdef
  have hjx : (j : ℝ) ≤ (2 : ℝ) ^ n * r := by
    rw [hjdef]; exact Nat.floor_le (by positivity)
  have hxj : (2 : ℝ) ^ n * r < (j : ℝ) + 1 := by
    rw [hjdef]; exact Nat.lt_floor_add_one _
  have hNMr : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hjN : j ≤ M * 2 ^ n := by
    have hxN : (2 : ℝ) ^ n * r ≤ (M : ℝ) * 2 ^ n := by nlinarith [h2n, hrN, hNMr]
    have hcast : (j : ℝ) ≤ ((M * 2 ^ n : ℕ) : ℝ) := by
      push_cast
      linarith [hjx, hxN]
    exact_mod_cast hcast
  -- the grid formula
  have hgrid := surDrv_eq_grid (N := M) (n := n) (e := W) (r := r) (j := j) (by omega)
    (fun k hk => by
      have hk1 : (k : ℝ) + 1 ≤ (j : ℝ) := by
        have : k + 1 ≤ j := by omega
        exact_mod_cast this
      linarith)
    (fun k hk hkM => by
      have hk1 : (j : ℝ) + 1 ≤ (k : ℝ) := by
        have : j + 1 ≤ k := by omega
        exact_mod_cast this
      linarith)
  rw [WedgeLaw.extP_of_continuous hW] at hgrid
  -- the two grid points are within the mesh of `r`
  have key : ∀ a b : ℝ, (a - b) * 2 ^ n ≤ 1 → a - b ≤ 1 / 2 ^ n := by
    intro a b hab
    have h : (a - b) * 2 ^ n ≤ (1 / 2 ^ n) * 2 ^ n := by
      rw [one_div, inv_mul_cancel₀ h2nn]; exact hab
    exact le_of_mul_le_mul_right h h2n
  have ha_le : (j : ℝ) / 2 ^ n - r ≤ 1 / 2 ^ n := by
    refine key _ _ ?_
    rw [sub_mul, div_mul_cancel₀ _ h2nn]
    linarith [hjx]
  have hle_a : r - (j : ℝ) / 2 ^ n ≤ 1 / 2 ^ n := by
    refine key _ _ ?_
    rw [sub_mul, div_mul_cancel₀ _ h2nn]
    linarith [hxj]
  have hb_ge : r - ((j : ℝ) + 1) / 2 ^ n ≤ 1 / 2 ^ n := by
    refine key _ _ ?_
    rw [sub_mul, div_mul_cancel₀ _ h2nn]
    linarith [hxj]
  have hle_b : ((j : ℝ) + 1) / 2 ^ n - r ≤ 1 / 2 ^ n := by
    refine key _ _ ?_
    rw [sub_mul, div_mul_cancel₀ _ h2nn]
    linarith [hjx]
  -- membership in the compact set on which `W` is uniformly continuous
  have h1div : (1 : ℝ) / 2 ^ n ≤ 1 :=
    (div_le_one h2n).2 (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have ha_mem : (j : ℝ) / 2 ^ n ∈ Icc (0 : ℝ) (N + 1) := by
    refine ⟨by positivity, ?_⟩
    have : (j : ℝ) / 2 ^ n ≤ r := by
      rw [div_le_iff₀ h2n]; linarith [hjx]
    linarith
  have hb_mem : ((j : ℝ) + 1) / 2 ^ n ∈ Icc (0 : ℝ) (N + 1) := by
    refine ⟨by positivity, ?_⟩
    have : ((j : ℝ) + 1) / 2 ^ n ≤ r + 1 := by linarith [hle_b, h1div]
    linarith
  have hrmem : r ∈ Icc (0 : ℝ) (N + 1) := ⟨hr0, by linarith⟩
  have hWa : dist (W ((j : ℝ) / 2 ^ n)) (W r) ≤ ε :=
    hδc _ ha_mem _ hrmem (by rw [Real.dist_eq]; exact (abs_sub_le_iff.2 ⟨ha_le, hle_a⟩).trans hδn)
  have hWb : dist (W (((j : ℝ) + 1) / 2 ^ n)) (W r) ≤ ε :=
    hδc _ hb_mem _ hrmem (by rw [Real.dist_eq]; exact (abs_sub_le_iff.2 ⟨hle_b, hb_ge⟩).trans hδn)
  have h1 : |W ((j : ℝ) / 2 ^ n) - W r| ≤ ε := by rw [← Real.dist_eq]; exact hWa
  have h2 : |W (((j : ℝ) + 1) / 2 ^ n) - W r| ≤ ε := by rw [← Real.dist_eq]; exact hWb
  -- the convex-combination form of the surrogate
  have hsplit : W 0 + (W ((j : ℝ) / 2 ^ n) - W 0) +
      ramp ((2 : ℝ) ^ n * r - j) * (W (((j : ℝ) + 1) / 2 ^ n) - W ((j : ℝ) / 2 ^ n)) - W r =
      (1 - ramp ((2 : ℝ) ^ n * r - j)) * (W ((j : ℝ) / 2 ^ n) - W r) +
        ramp ((2 : ℝ) ^ n * r - j) * (W (((j : ℝ) + 1) / 2 ^ n) - W r) := by ring
  rw [hgrid, hsplit]
  have hθ := ramp_mem ((2 : ℝ) ^ n * r - j)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hθ.2] : (0 : ℝ) ≤ 1 - ramp ((2 : ℝ) ^ n * r - j)),
    abs_of_nonneg hθ.1]
  refine (add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith [hθ.2]))
    (mul_le_mul_of_nonneg_left h2 hθ.1)).trans (le_of_eq ?_)
  ring

/-! ## 5. The surrogate as a measurable family of continuous drivers at time `1` -/

/-- The surrogate driver of the pair `(T, W')` rescaled to time `1`:
`s ↦ (surDrv N n W' (T·s) − extP W' 0)/√T`. Continuous in `s`, `0` at `s = 0`, and equal to
`(W'(T·s) − W'(0))/√T` when `W'` is continuous — so it is a legitimate (continuous) driver for
every parameter, which `revMapInv` is not. -/
def surScaled (N n : ℕ) (T : ℝ) (W' : ℝ → ℝ) (s : ℝ) : ℝ :=
  (surDrv N n W' (T * s) - WedgeLaw.extP W' 0) / Real.sqrt T

theorem continuous_surScaled (N n : ℕ) (T : ℝ) (W' : ℝ → ℝ) :
    Continuous fun s => surScaled N n T W' s :=
  (((continuous_surDrv N n W').comp (continuous_const.mul continuous_id)).sub
    continuous_const).div_const _

/-- The driver part of a measurable `(T, W')`-reading is measurable as a function-valued map. -/
theorem measurable_drv_of_joint {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hF2 : Measurable fun q : E6.FullData × ℝ => (F q.1).2 q.2) :
    Measurable fun d => (F d).2 :=
  measurable_pi_iff.2 fun r => hF2.comp (measurable_id.prodMk measurable_const)

theorem measurable_surScaled {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hF1 : Measurable fun d => (F d).1)
    (hF2 : Measurable fun q : E6.FullData × ℝ => (F q.1).2 q.2) (N n : ℕ) (s : ℝ) :
    Measurable fun d => surScaled N n (F d).1 (F d).2 s := by
  have hW : Measurable fun d : E6.FullData => (F d).2 := measurable_drv_of_joint hF2
  have hT : Measurable fun d : E6.FullData => WedgeLaw.extP (F d).2 0 :=
    WedgeLaw.measurable_extP.comp (hW.prodMk measurable_const)
  have hsum : Measurable fun d : E6.FullData =>
      ∑ k ∈ Finset.range (N * 2 ^ n + 1),
        ramp ((2 : ℝ) ^ n * ((F d).1 * s) - k) *
          (WedgeLaw.extP (F d).2 (((k : ℝ) + 1) / 2 ^ n) - WedgeLaw.extP (F d).2 ((k : ℝ) / 2 ^ n)) := by
    refine Finset.measurable_sum _ fun k _ => ?_
    have hc : Measurable fun d : E6.FullData => WedgeLaw.extP (F d).2 (((k : ℝ) + 1) / 2 ^ n) :=
      WedgeLaw.measurable_extP.comp (hW.prodMk measurable_const)
    have hc' : Measurable fun d : E6.FullData => WedgeLaw.extP (F d).2 ((k : ℝ) / 2 ^ n) :=
      WedgeLaw.measurable_extP.comp (hW.prodMk measurable_const)
    have hr : Measurable fun d : E6.FullData => ramp ((2 : ℝ) ^ n * ((F d).1 * s) - k) :=
      continuous_ramp.measurable.comp
        ((measurable_const.mul (hF1.mul_const s)).sub measurable_const)
    exact hr.mul (hc.sub hc')
  have hval : Measurable fun d : E6.FullData => surDrv N n (F d).2 ((F d).1 * s) := hT.add hsum
  exact (hval.sub hT).div (Real.continuous_sqrt.measurable.comp hF1)

end Thm18Asm
end QuantumZipper

