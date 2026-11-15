/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessClock
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.Zipper.JointModDet
import QuantumZipper.Proofs.Zipper.ESMLMeas

/-!
# The height functional on the canonical path space

Packet PROVE-ZHAN-A7. Astra, *Formalization proofs and dependency audit* (ruling R35), "Eliminate all other terminal
cluster points" (`source/external/AstraIG1/ig1_formalization_proofs.txt` L1471–L1499): the source compares the minimal
height `M` of the terminal cluster set with the same quantity for a restarted prefix, which has the same law. A law
needs a measurable functional of the Brownian path. This file builds it on QuantumZipper's canonical path space
`CPath` (continuous paths `ℝ≥0 → ℝ`, product σ-algebra), with no reference to any particular strip path:

* for a path `f`, the constant-drift strip driver `ξ_t = √κ (f_t − f_0) + σ t` (`drv`), and in strip time the explicit
  chordal data of the strip chain (Astra L1503–L1505, Lemma 1.10 of the additional note):
  `q_t = e^{ξ_t − t}` (`qq`, the gap `W − V`), `A_t = 1 + 2∫₀ᵗ q` (`aa`, minus the end mark), the chordal driver
  `q_t − A_t` (`ww`), and the chordal time `s(t) = ∫₀ᵗ q²` (`ss`, the clock `Retarget.clk` with rate `q²`);
* the chordal driver in chordal time, frozen after the chordal time of the strip time `N` (`cdrv`, through the inverse
  clock `Retarget.invClk`);
* the radial values `F_{s(t)}(iy)` of the inverse Loewner map at the chordal time of the strip time `t` (`rad`), the
  strip height `liminf_{y ↓ 0} arg(1 + F_{s(t)}(iy))` (`hgt`), and its `liminf` over rational strip times (`mm`).

Every evaluation is measurable in `f` (`measurable_cdrv`, `measurable_rad`, `measurable_hgt`, `measurable_mm`): joint
measurability of functions continuous in time and measurable in `f` (`measurable_uncurry_of_continuous_of_measurable`),
measurable parametric integrals (`StronglyMeasurable.integral_prod_right`), the inverse clock through its sublevel
sets, and QuantumZipper's measurability of the inverse map in the driving path (`RS.measurable_fwdMapInv_drive`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H fwdMapInv)
open QuantumZipper.RS (CPath)

namespace InteractingSLE

namespace Zhan

namespace HeightLaw

open Retarget

variable (κ σ : ℝ)

/-! ### The explicit strip-time data of a path -/

/-- The constant-drift strip driver `ξ_t = √κ (f_t − f_0) + σ t` of a path, read on `ℝ`. -/
def drv (f : CPath) (u : ℝ) : ℝ := Real.sqrt κ * (f.1 u.toNNReal - f.1 0) + σ * u

/-- The chordal gap `q_t = e^{ξ_t − t}` in strip time. -/
def qq (f : CPath) (u : ℝ) : ℝ := Real.exp (drv κ σ f u - u)

/-- The clock rate `q_t²` of the chordal time. -/
def rate (f : CPath) (u : ℝ) : ℝ := qq κ σ f u ^ 2

/-- `A_t = 1 + 2∫₀ᵗ q`, minus the end mark in strip time. -/
def aa (f : CPath) (u : ℝ) : ℝ := 1 + 2 * ∫ r in (0 : ℝ)..u, qq κ σ f r

/-- The chordal driver in strip time, `q_t − A_t`. -/
def ww (f : CPath) (u : ℝ) : ℝ := qq κ σ f u - aa κ σ f u

/-- The chordal time `s(t) = ∫₀ᵗ q²` of the strip time `t`. -/
def ss (f : CPath) (u : ℝ) : ℝ := clk (rate κ σ f) u

/-- The chordal time clamped to `[0, s(N)]`. -/
def clampS (f : CPath) (N : ℝ) (s : ℝ) : ℝ := max 0 (min s (ss κ σ f N))

/-- The strip time of the chordal time `s`, frozen after the strip time `N`. -/
def tt (f : CPath) (N : ℝ) (s : ℝ) : ℝ := invClk (rate κ σ f) (clampS κ σ f N s)

/-- **The chordal driver in chordal time**, frozen after the chordal time of the strip time `N`. -/
def cdrv (f : CPath) (N : ℝ) (s : ℝ) : ℝ := ww κ σ f (tt κ σ f N s)

/-! ### Elementary properties -/

variable {κ σ}

theorem continuous_drv (f : CPath) : Continuous (drv κ σ f) := by
  have h : Continuous fun u : ℝ => f.1 u.toNNReal := f.2.comp continuous_real_toNNReal
  exact (continuous_const.mul (h.sub continuous_const)).add (continuous_const.mul continuous_id)

@[simp] theorem drv_zero (f : CPath) : drv κ σ f 0 = 0 := by simp [drv]

theorem continuous_qq (f : CPath) : Continuous (qq κ σ f) := by
  unfold qq
  have := continuous_drv (κ := κ) (σ := σ) f
  fun_prop

theorem qq_pos (f : CPath) (u : ℝ) : 0 < qq κ σ f u := Real.exp_pos _

@[simp] theorem qq_zero (f : CPath) : qq κ σ f 0 = 1 := by simp [qq]

theorem continuous_rate (f : CPath) : Continuous (rate κ σ f) := (continuous_qq f).pow 2

theorem rate_pos (f : CPath) (u : ℝ) : 0 < rate κ σ f u := pow_pos (qq_pos f u) 2

/-- The rate is a clock rate on every `[0, N]`. -/
theorem isRate (f : CPath) {N : ℝ} (hN : 0 ≤ N) : IsRate (rate κ σ f) N :=
  ⟨hN, (continuous_rate f).continuousOn, fun u _ => rate_pos f u⟩

theorem continuous_aa (f : CPath) : Continuous (aa κ σ f) := by
  have h : Continuous fun u => ∫ r in (0 : ℝ)..u, qq κ σ f r :=
    continuous_iff_continuousAt.2 fun x => (((continuous_qq f).integral_hasStrictDerivAt 0 x).hasDerivAt).continuousAt
  exact continuous_const.add (continuous_const.mul h)

@[simp] theorem aa_zero (f : CPath) : aa κ σ f 0 = 1 := by simp [aa]

theorem continuous_ww (f : CPath) : Continuous (ww κ σ f) := (continuous_qq f).sub (continuous_aa f)

@[simp] theorem ww_zero (f : CPath) : ww κ σ f 0 = 0 := by simp [ww]

@[simp] theorem ss_zero (f : CPath) : ss κ σ f 0 = 0 := clk_zero _

theorem ss_nonneg (f : CPath) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ ss κ σ f u :=
  (isRate f hu).clk_nonneg ⟨hu, le_rfl⟩

theorem clampS_mem (f : CPath) {N : ℝ} (hN : 0 ≤ N) (s : ℝ) :
    clampS κ σ f N s ∈ Icc 0 (ss κ σ f N) :=
  ⟨le_max_left _ _, max_le (ss_nonneg f hN) (min_le_right _ _)⟩

theorem clampS_of_mem (f : CPath) {N s : ℝ} (hs : s ∈ Icc 0 (ss κ σ f N)) : clampS κ σ f N s = s := by
  rw [clampS, min_eq_left hs.2, max_eq_right hs.1]

theorem continuous_clampS (f : CPath) (N : ℝ) : Continuous (clampS κ σ f N) := by
  unfold clampS; fun_prop

theorem tt_mem (f : CPath) {N : ℝ} (hN : 0 ≤ N) (s : ℝ) : tt κ σ f N s ∈ Icc 0 N :=
  (isRate f hN).invClk_mem (clampS_mem f hN s)

theorem continuous_tt (f : CPath) {N : ℝ} (hN : 0 ≤ N) : Continuous (tt κ σ f N) :=
  (isRate f hN).continuousOn_invClk.comp_continuous (continuous_clampS f N) (clampS_mem f hN)

theorem tt_ss (f : CPath) {N u : ℝ} (hu : u ∈ Icc 0 N) : tt κ σ f N (ss κ σ f u) = u := by
  have hN : 0 ≤ N := hu.1.trans hu.2
  have hm : ss κ σ f u ∈ Icc 0 (ss κ σ f N) :=
    ⟨ss_nonneg f hu.1, (isRate f hN).clk_le_clk hu ⟨hN, le_rfl⟩ |>.2 hu.2⟩
  rw [tt, clampS_of_mem f hm]
  exact (isRate f hN).invClk_clk hu

theorem continuous_cdrv (f : CPath) {N : ℝ} (hN : 0 ≤ N) : Continuous (cdrv κ σ f N) :=
  (continuous_ww f).comp (continuous_tt f hN)

theorem cdrv_zero (f : CPath) {N : ℝ} (hN : 0 ≤ N) : cdrv κ σ f N 0 = 0 := by
  have h0 : tt κ σ f N 0 = 0 := by
    have := tt_ss (κ := κ) (σ := σ) f (N := N) (u := 0) ⟨le_rfl, hN⟩
    rwa [ss_zero] at this
  rw [cdrv, h0, ww_zero]

theorem cdrv_ss (f : CPath) {N u : ℝ} (hu : u ∈ Icc 0 N) : cdrv κ σ f N (ss κ σ f u) = ww κ σ f u := by
  rw [cdrv, tt_ss f hu]

theorem cdrv_of_nonpos (f : CPath) {N s : ℝ} (hN : 0 ≤ N) (hs : s ≤ 0) : cdrv κ σ f N s = 0 := by
  have hc : clampS κ σ f N s = 0 := by
    rw [clampS, min_eq_left (hs.trans (ss_nonneg f hN)), max_eq_left hs]
  rw [cdrv, tt, hc, (isRate f hN).invClk_zero, ww_zero]

/-! ### Measurability in the path -/

theorem measurable_eval (u : ℝ≥0) : Measurable fun f : CPath => f.1 u :=
  (measurable_pi_apply u).comp measurable_subtype_coe

theorem measurable_drv (u : ℝ) : Measurable fun f : CPath => drv κ σ f u :=
  (measurable_const.mul ((measurable_eval _).sub (measurable_eval 0))).add measurable_const

theorem measurable_qq (u : ℝ) : Measurable fun f : CPath => qq κ σ f u :=
  Real.measurable_exp.comp ((measurable_drv u).sub measurable_const)

theorem measurable_uncurry_qq : Measurable (Function.uncurry fun u (f : CPath) => qq κ σ f u) :=
  measurable_uncurry_of_continuous_of_measurable (fun f => continuous_qq f) fun u => measurable_qq u

/-- A parametric interval integral of a jointly measurable integrand is measurable in the path. -/
theorem measurable_intervalIntegral_of_uncurry {g : ℝ → CPath → ℝ}
    (hg : Measurable (Function.uncurry g)) (a b : ℝ) : Measurable fun f => ∫ r in a..b, g r f := by
  have hs : StronglyMeasurable (Function.uncurry fun (f : CPath) (r : ℝ) => g r f) :=
    (hg.comp measurable_swap).stronglyMeasurable
  simp only [intervalIntegral]
  exact (hs.integral_prod_right (ν := volume.restrict (Ioc a b))).measurable.sub
    (hs.integral_prod_right (ν := volume.restrict (Ioc b a))).measurable

theorem measurable_aa (u : ℝ) : Measurable fun f : CPath => aa κ σ f u :=
  measurable_const.add (measurable_const.mul (measurable_intervalIntegral_of_uncurry measurable_uncurry_qq 0 u))

theorem measurable_ww (u : ℝ) : Measurable fun f : CPath => ww κ σ f u :=
  (measurable_qq u).sub (measurable_aa u)

theorem measurable_uncurry_ww : Measurable (Function.uncurry fun u (f : CPath) => ww κ σ f u) :=
  measurable_uncurry_of_continuous_of_measurable (fun f => continuous_ww f) fun u => measurable_ww u

theorem measurable_ss (u : ℝ) : Measurable fun f : CPath => ss κ σ f u := by
  have h : Measurable (Function.uncurry fun r (f : CPath) => rate κ σ f r) :=
    measurable_uncurry_of_continuous_of_measurable (fun f => continuous_rate f)
      fun r => (measurable_qq r).pow_const 2
  exact measurable_intervalIntegral_of_uncurry h 0 u

theorem measurable_clampS (N s : ℝ) : Measurable fun f : CPath => clampS κ σ f N s :=
  measurable_const.max (measurable_const.min (measurable_ss N))

/-- The frozen inverse clock is measurable in the path (through its sublevel sets). -/
theorem measurable_tt {N : ℝ} (hN : 0 ≤ N) (s : ℝ) : Measurable fun f : CPath => tt κ σ f N s := by
  refine measurable_of_Iic fun a => ?_
  rcases lt_or_ge a 0 with ha | ha
  · convert MeasurableSet.empty
    ext f
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
    exact ha.trans_le (tt_mem f hN s).1
  rcases le_or_gt a N with haN | haN
  · have : (fun f : CPath => tt κ σ f N s) ⁻¹' Iic a = {f | clampS κ σ f N s ≤ ss κ σ f a} := by
      ext f
      simp only [mem_preimage, mem_Iic]
      have hr := isRate (κ := κ) (σ := σ) f hN
      have hm := clampS_mem (κ := κ) (σ := σ) f hN s
      show invClk (rate κ σ f) (clampS κ σ f N s) ≤ a ↔ clampS κ σ f N s ≤ clk (rate κ σ f) a
      rw [← hr.clk_le_clk (hr.invClk_mem hm) ⟨ha, haN⟩, hr.clk_invClk hm]
    rw [this]
    exact measurableSet_le (measurable_clampS N s) (measurable_ss a)
  · convert MeasurableSet.univ
    ext f
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    exact (tt_mem f hN s).2.trans haN.le

theorem measurable_cdrv {N : ℝ} (hN : 0 ≤ N) (s : ℝ) : Measurable fun f : CPath => cdrv κ σ f N s :=
  measurable_uncurry_ww.comp ((measurable_tt hN s).prodMk measurable_id)

/-! ### The inverse Loewner map of the frozen chordal driver -/

/-- For `z ∈ ℍ`, `t ↦ F_t(z)` is continuous on `ℝ≥0` (as `Sec7.continuous_fwdMapInv_time`). -/
theorem continuous_fwdMapInv_time {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {z : ℂ}
    (hz : z ∈ H) : Continuous fun t : ℝ≥0 => fwdMapInv V t z := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hT : (0 : ℝ) ≤ (t₀ : ℝ) + 1 := by positivity
  have hcont := QuantumZipper.RegUnif.continuousOn_fwdMapInv_joint hV hV0 ((t₀ : ℝ) + 1)
  have h1 : Continuous fun t : ℝ≥0 => fwdMapInv V (min (t : ℝ) ((t₀ : ℝ) + 1)) z := by
    have hf : Continuous fun t : ℝ≥0 => ((min (t : ℝ) ((t₀ : ℝ) + 1)), z) :=
      (NNReal.continuous_coe.min continuous_const).prodMk continuous_const
    exact hcont.comp_continuous hf fun t =>
      ⟨⟨le_min t.coe_nonneg hT, min_le_right _ _⟩, hz⟩
  refine h1.continuousAt.congr ?_
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝 t₀, (t : ℝ) < (t₀ : ℝ) + 1 :=
    (NNReal.continuous_coe.tendsto t₀).eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hev] with t ht
  rw [min_eq_left ht.le]

/-- `f ↦ F_t(z)` for the frozen chordal driver is measurable. -/
theorem measurable_fwdMapInv_cdrv {N : ℝ} (hN : 0 ≤ N) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.im) :
    Measurable fun f : CPath => fwdMapInv (cdrv κ σ f N) t z := by
  set B : ℝ≥0 → CPath → ℝ := fun r f => cdrv κ σ f N r with hB
  have heq : (fun f : CPath => fwdMapInv (cdrv κ σ f N) t z) =
      fun f => fwdMapInv (QuantumZipper.drive 1 B f) t z := by
    funext f
    congr 1
    funext r
    simp only [QuantumZipper.drive, Real.sqrt_one, one_mul, hB]
    rcases le_total 0 r with hr | hr
    · rw [Real.coe_toNNReal _ hr]
    · rw [Real.toNNReal_of_nonpos hr, NNReal.coe_zero, cdrv_zero f hN, cdrv_of_nonpos f hN hr]
  rw [heq]
  refine QuantumZipper.RS.measurable_fwdMapInv_drive (fun r => measurable_cdrv hN r)
    (fun f => (continuous_cdrv f hN).comp NNReal.continuous_coe) (fun f => ?_) 1 ht hz
  simp only [NNReal.coe_zero, cdrv_zero f hN]

/-- Joint measurability of `(t, f) ↦ F_t(z)`. -/
theorem measurable_uncurry_fwdMapInv_cdrv {N : ℝ} (hN : 0 ≤ N) {z : ℂ} (hz : 0 < z.im) :
    Measurable (Function.uncurry fun (t : ℝ≥0) (f : CPath) => fwdMapInv (cdrv κ σ f N) t z) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun f => continuous_fwdMapInv_time (continuous_cdrv f hN) (cdrv_zero f hN) hz)
    fun t => measurable_fwdMapInv_cdrv hN t.coe_nonneg hz


/-! ### `liminf` along rationals, at `0⁺` and at `∞` -/

/-- `liminf_{y ↓ 0} φ(y)` along rational `y`: `sup_m inf_{y ∈ ℚ ∩ (0, 1/(m+1))} φ(y)`. -/
def limInfQ (φ : ℝ → ℝ) : ℝ := ⨆ m : ℕ, ⨅ y : {y : ℚ // 0 < y ∧ (y : ℝ) < 1 / ((m : ℝ) + 1)}, φ y

/-- `liminf_{q → ∞} h(q)` along rational `q`: `sup_n inf_{q ∈ ℚ, q ≥ n} h(q)`. -/
def limInfTopQ (h : ℝ → ℝ) : ℝ := ⨆ n : ℕ, ⨅ q : {q : ℚ // (n : ℚ) ≤ q}, h q

section LimInf

variable {φ ψ : ℝ → ℝ} {lo hi : ℝ}

theorem nonempty_ratIoo (m : ℕ) : Nonempty {y : ℚ // 0 < y ∧ (y : ℝ) < 1 / ((m : ℝ) + 1)} := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity)
  exact ⟨⟨q, by exact_mod_cast hq1, hq2⟩⟩

theorem bddBelow_ratIoo (hφ : ∀ y, 0 < y → φ y ∈ Icc lo hi) (m : ℕ) :
    BddBelow (range fun y : {y : ℚ // 0 < y ∧ (y : ℝ) < 1 / ((m : ℝ) + 1)} => φ y) :=
  ⟨lo, by rintro _ ⟨y, rfl⟩; exact (hφ _ (by exact_mod_cast y.2.1)).1⟩

theorem infQ_mem (hφ : ∀ y, 0 < y → φ y ∈ Icc lo hi) (m : ℕ) :
    (⨅ y : {y : ℚ // 0 < y ∧ (y : ℝ) < 1 / ((m : ℝ) + 1)}, φ y) ∈ Icc lo hi := by
  have := nonempty_ratIoo m
  obtain ⟨y⟩ := nonempty_ratIoo m
  exact ⟨le_ciInf fun y => (hφ _ (by exact_mod_cast y.2.1)).1,
    (ciInf_le (bddBelow_ratIoo hφ m) y).trans (hφ _ (by exact_mod_cast y.2.1)).2⟩

theorem bddAbove_infQ (hφ : ∀ y, 0 < y → φ y ∈ Icc lo hi) :
    BddAbove (range fun m : ℕ => ⨅ y : {y : ℚ // 0 < y ∧ (y : ℝ) < 1 / ((m : ℝ) + 1)}, φ y) :=
  ⟨hi, by rintro _ ⟨m, rfl⟩; exact (infQ_mem hφ m).2⟩

theorem limInfQ_mem (hφ : ∀ y, 0 < y → φ y ∈ Icc lo hi) : limInfQ φ ∈ Icc lo hi :=
  ⟨(infQ_mem hφ 0).1.trans (le_ciSup (bddAbove_infQ hφ) 0), ciSup_le fun m => (infQ_mem hφ m).2⟩

/-- The rational infimum on `(0, 1/(k+1))` is below every real value there (continuity). -/
theorem infQ_le_of_continuousOn (hc : ContinuousOn ψ (Ioi 0)) (hψ : ∀ y, 0 < y → ψ y ∈ Icc lo hi)
    (k : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1 / ((k : ℝ) + 1)) :
    (⨅ y : {y : ℚ // 0 < y ∧ (y : ℝ) < 1 / ((k : ℝ) + 1)}, ψ y) ≤ ψ r := by
  by_contra hlt
  push Not at hlt
  set I := ⨅ y : {y : ℚ // 0 < y ∧ (y : ℝ) < 1 / ((k : ℝ) + 1)}, ψ y
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hc r hr0) (I - ψ r) (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r < min (r + δ) (1 / ((k : ℝ) + 1)) from
    lt_min (by linarith) hr)
  have hq0 : (0 : ℝ) < q := hr0.trans hq1
  have hd : dist (q : ℝ) r < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left (r + δ) (1 / ((k : ℝ) + 1))]
  have h1 := hball (show (q : ℝ) ∈ Ioi 0 from hq0) hd
  have h2 : I ≤ ψ q := ciInf_le (bddBelow_ratIoo hψ k)
    ⟨q, by exact_mod_cast hq0, hq2.trans_le (min_le_right _ _)⟩
  rw [Real.dist_eq, abs_lt] at h1
  linarith [h1.2]

/-- **Comparison under scaling**: if `ψ(y) ≤ φ(g y)` for all `y > 0` and `ψ` is continuous, then
`liminf ψ ≤ liminf φ`. -/
theorem limInfQ_le_of_scale (hc : ContinuousOn ψ (Ioi 0)) (hψ : ∀ y, 0 < y → ψ y ∈ Icc lo hi)
    (hφ : ∀ y, 0 < y → φ y ∈ Icc lo hi) {g : ℝ} (hg : 0 < g) (h : ∀ y, 0 < y → ψ y ≤ φ (g * y)) :
    limInfQ ψ ≤ limInfQ φ := by
  refine ciSup_le fun k => ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < g / ((k : ℝ) + 1) by positivity)
  have := nonempty_ratIoo m
  refine le_trans ?_ (le_ciSup (bddAbove_infQ hφ) m)
  refine le_ciInf fun q => ?_
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.2.1
  have hqg : (q : ℝ) / g < 1 / ((k : ℝ) + 1) := by
    rw [div_lt_iff₀ hg]
    have h1 : (q : ℝ) < g / ((k : ℝ) + 1) := q.2.2.trans hm
    calc (q : ℝ) < g / ((k : ℝ) + 1) := h1
      _ = 1 / ((k : ℝ) + 1) * g := by ring
  have h1 := infQ_le_of_continuousOn hc hψ k (div_pos hq0 hg) hqg
  have h2 := h ((q : ℝ) / g) (div_pos hq0 hg)
  rw [mul_div_cancel₀ _ hg.ne'] at h2
  exact h1.trans h2

/-- **The rational `liminf` of a convergent function is its limit.** -/
theorem limInfQ_eq_of_tendsto (hφ : ∀ y, 0 < y → φ y ∈ Icc lo hi) {L : ℝ}
    (hL : Tendsto φ (𝓝[>] 0) (𝓝 L)) : limInfQ φ = L := by
  have key : ∀ ε > 0, ∃ δ > 0, ∀ y, 0 < y → y < δ → |φ y - L| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hL (Metric.ball_mem_nhds L hε))
    exact ⟨δ, hδ, fun y hy hyδ => by
      have := hball ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hy]; exact hyδ, hy⟩
      rwa [mem_preimage, Metric.mem_ball, Real.dist_eq] at this⟩
  refine le_antisymm (ciSup_le fun k => le_of_forall_pos_lt_add fun ε hε => ?_)
    (le_of_forall_pos_le_add fun ε hε => ?_)
  · obtain ⟨δ, hδ, hδφ⟩ := key ε hε
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (0 : ℝ) < min δ (1 / ((k : ℝ) + 1)) by positivity)
    have hq : (q : ℝ) < 1 / ((k : ℝ) + 1) := hq2.trans_le (min_le_right _ _)
    have h1 := ciInf_le (bddBelow_ratIoo hφ k) ⟨q, by exact_mod_cast hq1, hq⟩
    have h2 := hδφ q hq1 (hq2.trans_le (min_le_left _ _))
    rw [abs_lt] at h2
    simp only at h1
    linarith [h2.2]
  · obtain ⟨δ, hδ, hδφ⟩ := key ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    have := nonempty_ratIoo k
    have h1 : L - ε ≤ ⨅ y : {y : ℚ // 0 < y ∧ (y : ℝ) < 1 / ((k : ℝ) + 1)}, φ y :=
      le_ciInf fun y => by
        have := hδφ y (by exact_mod_cast y.2.1) (y.2.2.trans hk)
        rw [abs_lt] at this
        linarith [this.1]
    have h2 := le_ciSup (bddAbove_infQ hφ) k
    unfold limInfQ
    linarith

variable {h₁ h₂ : ℝ → ℝ}

theorem bddBelow_ratIci (hh : ∀ t, 0 ≤ t → h₁ t ∈ Icc lo hi) (n : ℕ) :
    BddBelow (range fun q : {q : ℚ // (n : ℚ) ≤ q} => h₁ q) :=
  ⟨lo, by rintro _ ⟨q, rfl⟩; exact (hh _ (by exact_mod_cast (Nat.cast_nonneg n).trans q.2)).1⟩

theorem infTop_mem (hh : ∀ t, 0 ≤ t → h₁ t ∈ Icc lo hi) (n : ℕ) :
    (⨅ q : {q : ℚ // (n : ℚ) ≤ q}, h₁ q) ∈ Icc lo hi := by
  have hn : ((n : ℚ) : ℝ) = (n : ℝ) := by push_cast; rfl
  have : Nonempty {q : ℚ // (n : ℚ) ≤ q} := ⟨⟨n, le_rfl⟩⟩
  exact ⟨le_ciInf fun q => (hh _ (by exact_mod_cast (Nat.cast_nonneg n).trans q.2)).1,
    (ciInf_le (bddBelow_ratIci hh n) ⟨n, le_rfl⟩).trans (hh _ (by positivity)).2⟩

theorem bddAbove_infTop (hh : ∀ t, 0 ≤ t → h₁ t ∈ Icc lo hi) :
    BddAbove (range fun n : ℕ => ⨅ q : {q : ℚ // (n : ℚ) ≤ q}, h₁ q) :=
  ⟨hi, by rintro _ ⟨n, rfl⟩; exact (infTop_mem hh n).2⟩

theorem limInfTopQ_mem (hh : ∀ t, 0 ≤ t → h₁ t ∈ Icc lo hi) : limInfTopQ h₁ ∈ Icc lo hi :=
  ⟨(infTop_mem hh 0).1.trans (le_ciSup (bddAbove_infTop hh) 0), ciSup_le fun n => (infTop_mem hh n).2⟩

/-- **Comparison under a time shift**: if `h₁(q) ≤ h₂(n + q)` at nonnegative rationals, then
`liminf h₁ ≤ liminf h₂`. -/
theorem limInfTopQ_le_of_shift (hh₁ : ∀ t, 0 ≤ t → h₁ t ∈ Icc lo hi) (hh₂ : ∀ t, 0 ≤ t → h₂ t ∈ Icc lo hi)
    (n : ℕ) (h : ∀ q : ℚ, 0 ≤ q → h₁ q ≤ h₂ ((n : ℝ) + q)) : limInfTopQ h₁ ≤ limInfTopQ h₂ := by
  refine ciSup_le fun N => ?_
  have : Nonempty {q : ℚ // ((N + n : ℕ) : ℚ) ≤ q} := ⟨⟨(N + n : ℕ), le_rfl⟩⟩
  refine le_trans ?_ (le_ciSup (bddAbove_infTop hh₂) (N + n))
  refine le_ciInf fun q => ?_
  have hq : ((N : ℚ)) ≤ (q : ℚ) - n := by
    have := q.2; push_cast at this; linarith
  have h1 := ciInf_le (bddBelow_ratIci hh₁ N) ⟨(q : ℚ) - n, hq⟩
  have h2 := h ((q : ℚ) - n) ((Nat.cast_nonneg N).trans hq)
  simp only at h1
  have h3 : ((n : ℝ) + (((q : ℚ) - n : ℚ) : ℝ)) = ((q : ℚ) : ℝ) := by push_cast; ring
  rw [h3] at h2
  exact h1.trans h2

/-- Below the `liminf`: eventually above. -/
theorem eventually_lt_of_lt_limInfTopQ (hh : ∀ t, 0 ≤ t → h₁ t ∈ Icc lo hi) {c : ℝ}
    (hc : c < limInfTopQ h₁) : ∃ N : ℕ, ∀ q : ℚ, (N : ℚ) ≤ q → c < h₁ q := by
  obtain ⟨N, hN⟩ := exists_lt_of_lt_ciSup hc
  exact ⟨N, fun q hq => hN.trans_le (ciInf_le (bddBelow_ratIci hh N) ⟨q, hq⟩)⟩

/-- Above the `liminf`: frequently below. -/
theorem frequently_lt_of_limInfTopQ_lt (hh : ∀ t, 0 ≤ t → h₁ t ∈ Icc lo hi) {c : ℝ}
    (hc : limInfTopQ h₁ < c) (N : ℕ) : ∃ q : ℚ, (N : ℚ) ≤ q ∧ h₁ q < c := by
  have : Nonempty {q : ℚ // (N : ℚ) ≤ q} := ⟨⟨N, le_rfl⟩⟩
  have h1 : (⨅ q : {q : ℚ // (N : ℚ) ≤ q}, h₁ q) < c :=
    (le_ciSup (bddAbove_infTop hh) N).trans_lt hc
  obtain ⟨q, hq⟩ := exists_lt_of_ciInf_lt h1
  exact ⟨q, q.2, hq⟩

end LimInf

/-! ### Radial values, strip heights and their `liminf` -/

variable (κ σ) in
/-- The radial value `F_{s(t)}(iy)` of the inverse map at the chordal time of the strip time `t` (driver frozen after
the strip time `⌈t⌉`). -/
def rad (f : CPath) (t y : ℝ) : ℂ := fwdMapInv (cdrv κ σ f ⌈t⌉₊) (ss κ σ f t) ((y : ℂ) * I)

variable (κ σ) in
/-- The strip height at the strip time `t`: `liminf_{y ↓ 0} arg(1 + F_{s(t)}(iy))` (over rational `y`). -/
def hgt (f : CPath) (t : ℝ) : ℝ := limInfQ fun y => arg (1 + rad κ σ f t y)

variable (κ σ) in
/-- **The terminal minimal height**: the `liminf` of the strip heights over rational strip times. -/
def mm (f : CPath) : ℝ := limInfTopQ (hgt κ σ f)

theorem measurable_rad {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy : 0 < y) :
    Measurable fun f : CPath => rad κ σ f t y := by
  have hz : 0 < ((y : ℂ) * I).im := by simpa using hy
  have h := (measurable_uncurry_fwdMapInv_cdrv (κ := κ) (σ := σ) (Nat.cast_nonneg ⌈t⌉₊) hz).comp
    (((measurable_ss (κ := κ) (σ := σ) t).real_toNNReal).prodMk measurable_id)
  convert h using 1
  funext f
  simp only [Function.comp_apply, Function.uncurry_apply_pair, rad, id,
    Real.coe_toNNReal _ (ss_nonneg f ht)]

theorem measurable_hgt {t : ℝ} (ht : 0 ≤ t) : Measurable fun f : CPath => hgt κ σ f t :=
  Measurable.iSup fun _ => Measurable.iInf fun y =>
    measurable_arg.comp (measurable_const.add (measurable_rad ht (by exact_mod_cast y.2.1)))

theorem measurable_mm : Measurable fun f : CPath => mm κ σ f :=
  Measurable.iSup fun n => Measurable.iInf fun q =>
    measurable_hgt (by exact_mod_cast (Nat.cast_nonneg n).trans q.2)

/-! ### The sublinearity constant -/

variable (κ σ) in
/-- The sublinearity constant of the strip driver at slope `a`: `sup_{q ∈ ℚ, q ≥ 0} (|ξ_q| − a q)`. -/
def csub (a : ℝ) (f : CPath) : ℝ := ⨆ q : {q : ℚ // 0 ≤ q}, (|drv κ σ f ((q : ℚ) : ℝ)| - a * (q : ℚ))

theorem measurable_csub (a : ℝ) : Measurable fun f : CPath => csub κ σ a f :=
  Measurable.iSup fun _ => (continuous_abs.measurable.comp (measurable_drv (κ := κ) (σ := σ) _)).sub measurable_const

/-- If the sup is finite, it bounds `|ξ_t| − a t` at every time (continuity). -/
theorem abs_drv_le_csub {a : ℝ} {f : CPath}
    (hb : BddAbove (range fun q : {q : ℚ // 0 ≤ q} => |drv κ σ f ((q : ℚ) : ℝ)| - a * (q : ℚ)))
    {t : ℝ} (ht : 0 ≤ t) : |drv κ σ f t| ≤ csub κ σ a f + a * t := by
  have hc : Continuous fun u : ℝ => |drv κ σ f u| - a * u :=
    (continuous_drv f).abs.sub (continuous_const.mul continuous_id)
  by_contra hlt
  push Not at hlt
  have hlt' : csub κ σ a f < |drv κ σ f t| - a * t := by linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hc.continuousAt
    (|drv κ σ f t| - a * t - csub κ σ a f) (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + δ by linarith)
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast ht.trans hq1.le
  have hd : dist (q : ℝ) t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have h1 := hball hd
  have h2 : |drv κ σ f (q : ℝ)| - a * q ≤ csub κ σ a f := le_ciSup hb ⟨q, hq0⟩
  rw [Real.dist_eq, abs_lt] at h1
  linarith [h1.1]

end HeightLaw

end Zhan

end InteractingSLE
