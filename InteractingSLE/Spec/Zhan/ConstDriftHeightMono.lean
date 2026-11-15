/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftHeightPath
import QuantumZipper.Proofs.RS.KoebeLoewnerTime

/-!
# The restart lowers the strip height: `mm (θ_n f) ≤ mm f` for every path

Packet PROVE-ZHAN-A7. Astra L1491–L1493: "The inverse-flow height inequality gives `Im F_h(z) > Im z`
(`z ∈ S_π`)". Here the inequality is proved for the explicit chordal data of `ConstDriftHeightMeas.lean`, for
**every** continuous path `f` (no trace is needed), and transported to the height functional:

* `shiftPath n f = f(n + ·) − f(n)` is the path of the restart at the strip time `n`; its explicit data are the
  rescaled shifted data of `f` (`qq_shiftPath`, `ss_shiftPath`, `ww_shiftPath`, `cdrv_shiftPath`);
* `rad_add_eq`: the radial values compose, `F^f_{s(n+t)}(i g y) = F^f_{s(n)}(g F^{θf}_{s'(t)}(iy))`, `g = q_n`
  (QuantumZipper's flow property `RS.fwdMapInv_add_shift` and scaling `RS.fwdMapInv_scale`);
* `explicit end mark`: `V = −A ∘ (inverse clock)` solves `V_s = −1 + ∫₀ˢ 2/(V − W)` (change of variables
  `Retarget.IsRate.integral_clk_eq`);
* `arg_sub_lt_arg_add_one` (**the height inequality**): along a forward flow `u` from `z ∈ ℍ` and a left mark `V`
  solving the end-mark equation, `D = u − (V − W) = z + 1 + ∫ (2/u − 2/(V − W))` has `(log D)' = −2/(u (V − W))`, whose
  imaginary part is negative, so `arg D` strictly decreases;
* `hgt_shiftPath_le`, `mm_shiftPath_le`: `hgt (θ_n f) t ≤ hgt f (n + t)` and `mm (θ_n f) ≤ mm f`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H fwdMapInv fwdMap fwdHull IsForwardSol)
open QuantumZipper.RS (CPath)

namespace InteractingSLE

namespace Zhan

namespace HeightLaw

open Strip Retarget

variable {κ σ : ℝ}

/-! ### The restarted path and its explicit data -/

/-- The path of the restart at time `n`: `u ↦ f(n + u) − f(n)`. -/
def shiftPath (n : ℝ≥0) (f : CPath) : CPath :=
  ⟨fun u => f.1 (n + u) - f.1 n, (f.2.comp (continuous_const.add continuous_id)).sub continuous_const⟩

theorem measurable_shiftPath (n : ℝ≥0) : Measurable (shiftPath n) :=
  Measurable.subtype_mk (measurable_pi_iff.2 fun _ => (measurable_eval _).sub (measurable_eval _))

theorem drv_shiftPath (n : ℝ≥0) (f : CPath) {u : ℝ} (hu : 0 ≤ u) :
    drv κ σ (shiftPath n f) u = drv κ σ f (n + u) - drv κ σ f n := by
  simp only [drv, shiftPath, add_zero, sub_self, sub_zero]
  rw [Real.toNNReal_add n.coe_nonneg hu, Real.toNNReal_coe]
  ring

theorem qq_shiftPath (n : ℝ≥0) (f : CPath) {u : ℝ} (hu : 0 ≤ u) :
    qq κ σ (shiftPath n f) u = qq κ σ f (n + u) / qq κ σ f n := by
  rw [qq, qq, qq, drv_shiftPath n f hu, ← Real.exp_sub]
  ring_nf

/-- `∫₀ᵗ φ(n + u) du = ∫ₙⁿ⁺ᵗ φ` along the restart. -/
theorem integral_shift (n : ℝ≥0) (φ : ℝ → ℝ) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, φ (n + u) = ∫ u in (n : ℝ)..(n + t), φ u := by
  rw [intervalIntegral.integral_comp_add_left φ (n : ℝ), add_zero]

theorem ss_shiftPath (n : ℝ≥0) (f : CPath) {t : ℝ} (ht : 0 ≤ t) :
    ss κ σ (shiftPath n f) t = (ss κ σ f (n + t) - ss κ σ f n) / qq κ σ f n ^ 2 := by
  have hg := qq_pos (κ := κ) (σ := σ) f n
  have h1 : ss κ σ (shiftPath n f) t = ∫ u in (0 : ℝ)..t, rate κ σ f (n + u) / qq κ σ f n ^ 2 := by
    rw [ss, Retarget.clk]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht] at hu
    simp only [rate, qq_shiftPath n f hu.1, div_pow]
  rw [h1, intervalIntegral.integral_div, integral_shift, ss, ss, Retarget.clk, Retarget.clk,
    intervalIntegral.integral_interval_sub_left ((continuous_rate f).intervalIntegrable _ _)
      ((continuous_rate f).intervalIntegrable _ _)]

theorem ww_shiftPath (n : ℝ≥0) (f : CPath) {t : ℝ} (ht : 0 ≤ t) :
    ww κ σ (shiftPath n f) t = (ww κ σ f (n + t) - ww κ σ f n) / qq κ σ f n := by
  have hg := qq_pos (κ := κ) (σ := σ) f n
  have h1 : ∫ u in (0 : ℝ)..t, qq κ σ (shiftPath n f) u = (∫ u in (n : ℝ)..(n + t), qq κ σ f u) / qq κ σ f n := by
    have : ∫ u in (0 : ℝ)..t, qq κ σ (shiftPath n f) u = ∫ u in (0 : ℝ)..t, qq κ σ f (n + u) / qq κ σ f n := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le ht] at hu
      simp only [qq_shiftPath n f hu.1]
    rw [this, intervalIntegral.integral_div, integral_shift]
  have h2 := intervalIntegral.integral_interval_sub_left (μ := volume)
    ((continuous_qq (κ := κ) (σ := σ) f).intervalIntegrable 0 (n + t))
    ((continuous_qq (κ := κ) (σ := σ) f).intervalIntegrable 0 n)
  rw [ww, aa, h1, qq_shiftPath n f ht, ww, ww, aa, aa]
  rw [← h2]
  field_simp
  ring

/-- **The frozen driver of the restart** is the rescaled shifted frozen driver of `f`. -/
theorem cdrv_shiftPath (n : ℝ≥0) (f : CPath) {N' N : ℝ} (hN' : 0 ≤ N') (hN : (n : ℝ) + N' ≤ N) {r : ℝ}
    (hr : r ∈ Icc 0 (ss κ σ (shiftPath n f) N')) :
    cdrv κ σ (shiftPath n f) N' r =
      (cdrv κ σ f N (ss κ σ f n + qq κ σ f n ^ 2 * r) - cdrv κ σ f N (ss κ σ f n)) / qq κ σ f n := by
  have hg := qq_pos (κ := κ) (σ := σ) f n
  set t' := tt κ σ (shiftPath n f) N' r with ht'
  have ht'm := tt_mem (κ := κ) (σ := σ) (shiftPath n f) hN' r
  have hss : ss κ σ (shiftPath n f) t' = r := by
    rw [ht', tt, ss, clampS_of_mem _ hr]
    exact (isRate _ hN').clk_invClk hr
  have hss' : ss κ σ f n + qq κ σ f n ^ 2 * r = ss κ σ f (n + t') := by
    rw [← hss, ss_shiftPath n f ht'm.1]
    field_simp
    ring
  have hnN : (n : ℝ) ∈ Icc 0 N := ⟨n.coe_nonneg, by linarith [ht'm.1]⟩
  have hntN : (n : ℝ) + t' ∈ Icc 0 N := ⟨by linarith [ht'm.1, n.coe_nonneg], by linarith [ht'm.2]⟩
  rw [hss', cdrv_ss f hntN, cdrv_ss f hnN, cdrv, ← ht', ww_shiftPath n f ht'm.1]

/-! ### The flow property of the radial values -/

theorem mul_I_mem_H {y : ℝ} (hy : 0 < y) : (y : ℂ) * I ∈ H := by
  show 0 < ((y : ℂ) * I).im
  simpa using hy

theorem ss_le_ss (f : CPath) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : ss κ σ f a ≤ ss κ σ f b :=
  ((isRate (κ := κ) (σ := σ) f (ha.trans hab)).clk_le_clk ⟨ha, hab⟩ ⟨ha.trans hab, le_rfl⟩).2 hab

/-- **The radial values compose**: `F^f_{s(n+t)}(i g y) = F^f_{s(n)}(g · F^{θ_n f}_{s'(t)}(iy))` with `g = q_n`. -/
theorem rad_add_eq (n : ℕ) (f : CPath) {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy : 0 < y) :
    rad κ σ f ((n : ℝ) + t) (qq κ σ f n * y) =
      fwdMapInv (cdrv κ σ f ⌈(n : ℝ) + t⌉₊) (ss κ σ f n)
        ((qq κ σ f n : ℂ) * rad κ σ (shiftPath n f) t y) := by
  set g := qq κ σ f n with hgdef
  set N := ⌈(n : ℝ) + t⌉₊ with hNdef
  set W := cdrv κ σ f N with hWdef
  set a := ss κ σ f n with ha_def
  set s' := ss κ σ (shiftPath n f) t with hs'def
  have hg : 0 < g := qq_pos f n
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hW : Continuous W := continuous_cdrv f hN0
  have hW0 : W 0 = 0 := cdrv_zero f hN0
  have ha : 0 ≤ a := ss_nonneg f (Nat.cast_nonneg n)
  have hs' : 0 ≤ s' := ss_nonneg _ ht
  have hn : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by simp
  have hsum : ss κ σ f ((n : ℝ) + t) = a + g ^ 2 * s' := by
    rw [hs'def, ss_shiftPath (n : ℝ≥0) f ht, hn, ← hgdef, ← ha_def]
    field_simp
    ring
  have hw : (y : ℂ) * I ∈ H := mul_I_mem_H hy
  have hgw : (g : ℂ) * ((y : ℂ) * I) ∈ H := by
    rw [show (g : ℂ) * ((y : ℂ) * I) = ((g * y : ℝ) : ℂ) * I by push_cast; ring]
    exact mul_I_mem_H (mul_pos hg hy)
  rw [rad, hsum, show (((g * y : ℝ)) : ℂ) * I = (g : ℂ) * ((y : ℂ) * I) by push_cast; ring,
    QuantumZipper.RS.fwdMapInv_add_shift hW hW0 ha (by positivity) hgw]
  congr 1
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 := QuantumZipper.RS.shiftDrive_zero W a
  have hsc := QuantumZipper.RS.fwdMapInv_scale hV hV0 hg hs' hw
  have hceil : (n : ℝ) + (⌈t⌉₊ : ℝ) ≤ (N : ℝ) := by
    rw [hNdef, add_comm (n : ℝ) t, Nat.ceil_add_natCast ht]
    push_cast
    linarith
  have heq : fwdMapInv (fun r => QuantumZipper.RS.shiftDrive W a (g ^ 2 * r) / g) s' ((y : ℂ) * I) =
      rad κ σ (shiftPath n f) t y := by
    rw [rad]
    refine LP.fwdMapInv_eq_of_eqOn_Icc (by fun_prop) (continuous_cdrv _ (Nat.cast_nonneg _))
      (by simp [hV0]) (cdrv_zero _ (Nat.cast_nonneg _)) hs' (fun r hr => ?_) hw
    have hr' : r ∈ Icc 0 (ss κ σ (shiftPath n f) (⌈t⌉₊ : ℝ)) :=
      ⟨hr.1, hr.2.trans (ss_le_ss _ ht (Nat.le_ceil t))⟩
    rw [cdrv_shiftPath (N := (N : ℝ)) (n : ℝ≥0) f (Nat.cast_nonneg _) (by rw [hn]; exact hceil) hr', hn]
    simp only [QuantumZipper.RS.shiftDrive, hWdef, ha_def, hgdef]
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  rw [← heq, hsc]
  field_simp

/-! ### The explicit end mark -/

variable (κ σ) in
/-- The explicit end mark in chordal time: `V = −A ∘ (inverse clock)`. -/
def vmark (f : CPath) (N : ℝ) (s : ℝ) : ℝ := -aa κ σ f (tt κ σ f N s)

theorem vmark_sub_cdrv (f : CPath) (N s : ℝ) : vmark κ σ f N s - cdrv κ σ f N s = -qq κ σ f (tt κ σ f N s) := by
  simp only [vmark, cdrv, ww]
  ring

theorem continuous_vmark (f : CPath) {N : ℝ} (hN : 0 ≤ N) : Continuous (vmark κ σ f N) :=
  ((continuous_aa f).comp (continuous_tt f hN)).neg

/-- **The explicit end mark solves the end-mark equation** `V_s = −1 + ∫₀ˢ 2/(V − W)` on `[0, s(N)]`. -/
theorem vmark_eq (f : CPath) {N : ℝ} (hN : 0 ≤ N) {s : ℝ} (hs : s ∈ Icc 0 (ss κ σ f N)) :
    vmark κ σ f N s = -1 + ∫ r in (0 : ℝ)..s, 2 / (vmark κ σ f N r - cdrv κ σ f N r) := by
  have hr := isRate (κ := κ) (σ := σ) f hN
  set S := tt κ σ f N s with hS
  have hSm : S ∈ Icc 0 N := tt_mem f hN s
  have hsS : Retarget.clk (rate κ σ f) S = s := by
    rw [hS, tt, clampS_of_mem f hs]
    exact hr.clk_invClk hs
  have hrS : IsRate (rate κ σ f) S := isRate f hSm.1
  have hcv := hrS.integral_clk_eq (fun r => 2 / (vmark κ σ f N r - cdrv κ σ f N r))
  rw [hsS] at hcv
  rw [hcv]
  have hcongr : ∫ u in (0 : ℝ)..S, rate κ σ f u * (2 / (vmark κ σ f N (Retarget.clk (rate κ σ f) u) -
      cdrv κ σ f N (Retarget.clk (rate κ σ f) u))) = ∫ u in (0 : ℝ)..S, -2 * qq κ σ f u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hSm.1] at hu
    have hu' : u ∈ Icc 0 N := ⟨hu.1, hu.2.trans hSm.2⟩
    have htt : tt κ σ f N (Retarget.clk (rate κ σ f) u) = u := tt_ss f hu'
    simp only [vmark_sub_cdrv, htt, rate]
    have := qq_pos (κ := κ) (σ := σ) f u
    field_simp
  rw [hcongr, intervalIntegral.integral_const_mul, vmark, aa]
  ring

/-! ### The height inequality -/

/-- **The height inequality along a forward flow.** Let `u` be the centred forward flow of `z ∈ ℍ` on `[0, a]`, `a > 0`,
and `V < W` a left mark solving the end-mark equation `V_s = −1 + ∫₀ˢ 2/(V − W)`. Then
`D = u − (V − W) = z + 1 + ∫ (2/u − 2/(V − W))` has `(log D)' = −2/(u (V − W))` with negative imaginary part, so
`arg D(a) < arg D(0) = arg(z + 1)`. -/
theorem arg_sub_lt_arg_add_one {W V : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hW : ContinuousOn W (Icc 0 a)) (hV : ContinuousOn V (Icc 0 a))
    (hVW : ∀ s ∈ Icc 0 a, V s < W s)
    (hVeq : ∀ s ∈ Icc 0 a, V s = -1 + ∫ r in (0 : ℝ)..s, 2 / (V r - W r))
    {z : ℂ} {u : ℝ → ℂ} (hu : IsForwardSol W z a u) (huim : ∀ s ∈ Icc 0 a, 0 < (u s).im) :
    arg (u a - ((V a - W a : ℝ) : ℂ)) < arg (z + 1) := by
  set k : ℝ → ℂ := fun r => 2 / u r - 2 / ((V r - W r : ℝ) : ℂ) with hk
  have huc : ContinuousOn u (Icc 0 a) := hu.1
  have hu0 : ∀ s ∈ Icc 0 a, u s ≠ 0 := fun s hs => (hu.2 s hs).1
  have hB : ∀ s ∈ Icc 0 a, ((V s - W s : ℝ) : ℂ) ≠ 0 := fun s hs => by
    exact_mod_cast (sub_neg.2 (hVW s hs)).ne
  have hBc : ContinuousOn (fun r => ((V r - W r : ℝ) : ℂ)) (Icc 0 a) :=
    Complex.continuous_ofReal.comp_continuousOn (hV.sub hW)
  have h1c : ContinuousOn (fun r => (2 : ℂ) / u r) (Icc 0 a) := continuousOn_const.div huc hu0
  have h2c : ContinuousOn (fun r => (2 : ℂ) / ((V r - W r : ℝ) : ℂ)) (Icc 0 a) :=
    continuousOn_const.div hBc hB
  have hkc : ContinuousOn k (Icc 0 a) := h1c.sub h2c
  set D : ℝ → ℂ := fun s => u s - ((V s - W s : ℝ) : ℂ) with hD
  have hDeq : ∀ s ∈ Icc 0 a, D s = z + 1 + ∫ r in (0 : ℝ)..s, k r := by
    intro s hs
    have hsub : Icc 0 s ⊆ Icc 0 a := Icc_subset_Icc_right hs.2
    have hi1 : IntervalIntegrable (fun r => (2 : ℂ) / u r) volume 0 s :=
      (h1c.mono hsub).intervalIntegrable_of_Icc hs.1
    have hi2 : IntervalIntegrable (fun r => (2 : ℂ) / ((V r - W r : ℝ) : ℂ)) volume 0 s :=
      (h2c.mono hsub).intervalIntegrable_of_Icc hs.1
    have hcast : ∫ r in (0 : ℝ)..s, (2 : ℂ) / ((V r - W r : ℝ) : ℂ) =
        ((∫ r in (0 : ℝ)..s, 2 / (V r - W r) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r _ => ?_
      push_cast
      rfl
    simp only [hD, hk]
    rw [intervalIntegral.integral_sub hi1 hi2, hcast, (hu.2 s hs).2, hVeq s hs]
    push_cast
    ring
  have hDd : ∀ s ∈ Ioo 0 a, HasDerivAt D (k s) s := by
    intro s hs
    have hkc' : ContinuousOn k (Ioo 0 a) := hkc.mono Ioo_subset_Icc_self
    have hI := intervalIntegral.integral_hasDerivAt_right
      ((hkc.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc hs.1.le)
      (hkc'.stronglyMeasurableAtFilter isOpen_Ioo s hs) (hkc'.continuousAt (isOpen_Ioo.mem_nhds hs))
    refine (hI.const_add (z + 1)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr using hDeq r (Ioo_subset_Icc_self hr)
  have hDim : ∀ s ∈ Icc 0 a, (D s).im = (u s).im := fun s _ => by simp [hD]
  have hDslit : ∀ s ∈ Icc 0 a, D s ∈ slitPlane := fun s hs =>
    mem_slitPlane_iff.2 (Or.inr (by rw [hDim s hs]; exact (huim s hs).ne'))
  -- the argument of `D` is strictly decreasing
  set φ : ℝ → ℝ := fun s => (Complex.log (D s)).im with hφ
  have hDc : ContinuousOn D (Icc 0 a) := huc.sub hBc
  have hφc : ContinuousOn φ (Icc 0 a) :=
    Complex.continuous_im.comp_continuousOn (hDc.clog hDslit)
  have hφd : ∀ s ∈ Ioo 0 a, HasDerivAt φ (k s / D s).im s := fun s hs =>
    Strip.hasDerivAt_im ((hDd s hs).clog_real (hDslit s (Ioo_subset_Icc_self hs)))
  have hneg : ∀ s ∈ Ioo 0 a, (k s / D s).im < 0 := by
    intro s hs
    have hs' := Ioo_subset_Icc_self hs
    set b : ℝ := V s - W s with hb
    have hb0 : b < 0 := sub_neg.2 (hVW s hs')
    have hus := hu0 s hs'
    have hD0 : D s ≠ 0 := fun h0 => by
      have := hDim s hs'; rw [h0, zero_im] at this; linarith [huim s hs']
    have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne
    have hkD : k s / D s = ((-2 / b : ℝ) : ℂ) * (u s)⁻¹ := by
      have hDs : D s = u s - (b : ℂ) := rfl
      have hks : k s = 2 / u s - 2 / (b : ℂ) := rfl
      rw [hDs, hks]
      have hub : u s - (b : ℂ) ≠ 0 := by rw [← hDs]; exact hD0
      push_cast
      field_simp
      ring
    rw [hkD, Complex.im_ofReal_mul, Complex.inv_im]
    have hns : 0 < Complex.normSq (u s) := Complex.normSq_pos.2 hus
    have h1 : 0 < -2 / b := div_pos_of_neg_of_neg (by norm_num) hb0
    have h2 : -(u s).im / Complex.normSq (u s) < 0 := div_neg_of_neg_of_pos (by linarith [huim s hs']) hns
    nlinarith
  have hanti : StrictAntiOn φ (Icc 0 a) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 a) hφc fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hφd x hx).deriv]
    exact hneg x hx
  have hlt := hanti ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩ ha
  have hD0 : D 0 = z + 1 := by
    rw [hDeq 0 ⟨le_rfl, ha.le⟩, intervalIntegral.integral_same, add_zero]
  simp only [hφ, Complex.log_im, hD0] at hlt
  exact hlt

/-- **The height inequality for the explicit chain**: for `p ∈ ℍ` and a strip time `n ≥ 1`,
`arg(1 + p) < arg(1 + F_{s(n)}(q_n p))`. -/
theorem arg_one_add_lt (f : CPath) {n : ℕ} (hn : 0 < n) {N : ℝ} (hnN : (n : ℝ) ≤ N) {p : ℂ} (hp : p ∈ H) :
    arg (1 + p) < arg (1 + fwdMapInv (cdrv κ σ f N) (ss κ σ f n) ((qq κ σ f n : ℂ) * p)) := by
  set g := qq κ σ f n with hgdef
  set W := cdrv κ σ f N with hWdef
  set a := ss κ σ f n with ha_def
  have hN : 0 ≤ N := (Nat.cast_nonneg n).trans hnN
  have hW : Continuous W := continuous_cdrv f hN
  have hW0 : W 0 = 0 := cdrv_zero f hN
  have hg : 0 < g := qq_pos f n
  have ha : 0 < a := by
    have := (isRate (κ := κ) (σ := σ) f hN).clk_lt ⟨le_rfl, hN⟩ ⟨Nat.cast_nonneg n, hnN⟩
      (by exact_mod_cast hn)
    rwa [clk_zero] at this
  have hw : (g : ℂ) * p ∈ H := by
    show 0 < ((g : ℂ) * p).im
    rw [Complex.im_ofReal_mul]
    exact mul_pos hg hp
  set z := fwdMapInv W a ((g : ℂ) * p) with hz_def
  have hz := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ha.le hw
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ha.le hz.1 hz.2
  have hua : u a = (g : ℂ) * p := by
    rw [← QuantumZipper.fwdMap_eq hW hz.1 hu ⟨ha.le, le_rfl⟩,
      QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ha.le hw]
  have huim : ∀ s ∈ Icc 0 a, 0 < (u s).im := fun s hs => by
    rw [← QuantumZipper.fwdMap_eq hW hz.1 hu hs]
    exact Ito.im_fwdMap_pos_of_continuousOn ha.le hW.continuousOn hz.1 ⟨u, hu⟩ hs
  have haN : a ≤ ss κ σ f N := ss_le_ss f (Nat.cast_nonneg n) hnN
  have hkey := arg_sub_lt_arg_add_one ha hW.continuousOn (continuous_vmark f hN).continuousOn
    (fun s _ => by
      have h1 := vmark_sub_cdrv (κ := κ) (σ := σ) f N s
      have h2 := qq_pos (κ := κ) (σ := σ) f (tt κ σ f N s)
      linarith)
    (fun s hs => vmark_eq f hN ⟨hs.1, hs.2.trans haN⟩) hu huim
  have hVa : vmark κ σ f N a - W a = -g := by
    rw [hWdef, vmark_sub_cdrv, ha_def, tt_ss f ⟨Nat.cast_nonneg n, hnN⟩]
  rw [hua, hVa] at hkey
  have h1 : (g : ℂ) * p - ((-g : ℝ) : ℂ) = ((g : ℝ) : ℂ) * (1 + p) := by push_cast; ring
  rw [h1, Complex.arg_real_mul _ hg, add_comm z 1] at hkey
  exact hkey

/-! ### Comparison of the heights -/

theorem arg_mem_Icc (z : ℂ) : arg z ∈ Icc (-Real.pi) Real.pi :=
  ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩

theorem rad_mem_H (f : CPath) {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy : 0 < y) : rad κ σ f t y ∈ H :=
  QuantumZipper.RS.fwdMapInv_mem_H (continuous_cdrv f (Nat.cast_nonneg _)) (cdrv_zero f (Nat.cast_nonneg _))
    (ss_nonneg f ht) (mul_I_mem_H hy)

theorem continuousOn_arg_rad (f : CPath) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun y => arg (1 + rad κ σ f t y)) (Ioi 0) := by
  have hN : (0 : ℝ) ≤ (⌈t⌉₊ : ℝ) := Nat.cast_nonneg _
  have hd := QuantumZipper.RS.differentiableOn_fwdMapInv (continuous_cdrv (κ := κ) (σ := σ) f hN)
    (cdrv_zero f hN) (ss_nonneg (κ := κ) (σ := σ) f ht)
  intro y hy
  have hyH := mul_I_mem_H hy
  have hc : ContinuousAt (fun y : ℝ => (y : ℂ) * I) y := by fun_prop
  have h1 : ContinuousAt (fun y : ℝ => rad κ σ f t y) y :=
    ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) * I)
      (g := fwdMapInv (cdrv κ σ f ⌈t⌉₊) (ss κ σ f t))
      (hd.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hyH)) hc
  have hmem : 1 + rad κ σ f t y ∈ slitPlane := by
    refine mem_slitPlane_iff.2 (Or.inr ?_)
    have := rad_mem_H (κ := κ) (σ := σ) f ht hy
    simp only [add_im, one_im, zero_add]
    exact this.ne'
  have h2 : ContinuousAt (fun y : ℝ => 1 + rad κ σ f t y) y := continuousAt_const.add h1
  have h3 : ContinuousAt (fun y : ℝ => arg (1 + rad κ σ f t y)) y :=
    (continuousAt_arg hmem).tendsto.comp h2
  exact h3.continuousWithinAt

theorem hgt_mem (f : CPath) (t : ℝ) : hgt κ σ f t ∈ Icc (-Real.pi) Real.pi :=
  limInfQ_mem fun _ _ => arg_mem_Icc _

/-- **The restart lowers the strip height**: `hgt (θ_n f) t ≤ hgt f (n + t)`, `n ≥ 1`. -/
theorem hgt_shiftPath_le (f : CPath) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    hgt κ σ (shiftPath n f) t ≤ hgt κ σ f ((n : ℝ) + t) := by
  refine limInfQ_le_of_scale (continuousOn_arg_rad _ ht) (fun y _ => arg_mem_Icc _)
    (fun y _ => arg_mem_Icc _) (qq_pos (κ := κ) (σ := σ) f n) fun y hy => ?_
  rw [rad_add_eq n f ht hy]
  have hnN : (n : ℝ) ≤ (⌈(n : ℝ) + t⌉₊ : ℝ) := by
    have := Nat.le_ceil ((n : ℝ) + t)
    linarith
  exact (arg_one_add_lt f hn hnN (rad_mem_H _ ht hy)).le

/-- **The terminal minimal height does not increase under the restart**: `mm (θ_n f) ≤ mm f`, `n ≥ 1`. -/
theorem mm_shiftPath_le (f : CPath) {n : ℕ} (hn : 0 < n) : mm κ σ (shiftPath n f) ≤ mm κ σ f :=
  limInfTopQ_le_of_shift (fun t _ => hgt_mem _ t) (fun t _ => hgt_mem _ t) n fun q hq =>
    hgt_shiftPath_le f hn (by exact_mod_cast hq)

end HeightLaw

end Zhan

end InteractingSLE
