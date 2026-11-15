import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# Deterministic Loewner calculus behind (3.15)–(3.17)

Packet PROVE-T11-ITO (Specification §3.3, `source/spec/p049-096.md` L496–L527). For the centred forward
Loewner map `f_t = QuantumZipper.fwdMap W t` (`f_t = g_t − W_t`) and a point `z` not yet swallowed:

* `fwdMap_congr_of_eqOn`, `logDerivFwd_congr_of_eqOn`: the flow at times `≤ T` depends on the driver
  only through its values on `[0, T]` (no continuity needed);
* `fwdMap_eq_sub_add_integral`: the integrated Loewner equation `f_t(z) = z − W_t + ∫₀ᵗ 2/f_s(z) ds`;
  `hasDerivWithinAt_fwdMap_add`: `∂ₜ g_t(z) = ∂ₜ (f_t(z) + W_t) = 2/f_t(z)`;
* `hasDerivWithinAt_logDerivFwd`: `d log f_t'(z) = −2/f_t(z)² dt` for the branch
  `logDerivFwd W t z = −∫₀ᵗ 2/f_s(z)² ds` of `log f_t'(z)`; `deriv_fwdMap_eq_exp`:
  `f_t'(z) = exp (logDerivFwd W t z)`; `deriv_fwdMap_eq_one_add_integral`:
  `d f_t'(z) = −2 f_t'(z)/f_t(z)² dt` in integrated form;
* `greenH_fwdMap_eq_sub_integral` (**(3.16)**, integrated): for `y ≠ z` not swallowed by time `t`,
  `G(f_t y, f_t z) = G(y, z) − ∫₀ᵗ Im(2/f_s y) Im(2/f_s z) ds`, `G = QuantumZipper.greenH`.

The differential form of (3.16) is QuantumZipper's `FwdClock.hasDerivWithinAt_greenH_fwdMap`
(re-exported here as `hasDerivWithinAt_greenH_fwdMap`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open QuantumZipper

namespace InteractingSLE

namespace Ito

variable {W : ℝ → ℝ} {y z : ℂ} {T t s : ℝ}

/-! ### Locality in the driver -/

/-- The forward-flow predicate on `[0, T]` only reads the driver on `[0, T]`. -/
theorem isForwardSol_iff_of_eqOn {W W' : ℝ → ℝ} (h : EqOn W W' (Icc 0 T)) (u : ℝ → ℂ) :
    IsForwardSol W z T u ↔ IsForwardSol W' z T u := by
  unfold IsForwardSol
  refine and_congr Iff.rfl (forall₂_congr fun _ hs => ?_)
  rw [h hs]

/-- The forward map at time `T` only depends on the driver on `[0, T]`. -/
theorem fwdMap_congr_of_eqOn {W W' : ℝ → ℝ} (h : EqOn W W' (Icc 0 T)) :
    fwdMap W T z = fwdMap W' T z := by
  have hP : IsForwardSol W z T = IsForwardSol W' z T :=
    funext fun u => propext (isForwardSol_iff_of_eqOn h u)
  unfold fwdMap
  rw [hP]

/-- The forward map at times `t ∈ [0, T]` only depends on the driver on `[0, T]`. -/
theorem fwdMap_congr_of_eqOn_of_le {W W' : ℝ → ℝ} (h : EqOn W W' (Icc 0 T)) (htT : t ≤ T) :
    fwdMap W t z = fwdMap W' t z :=
  fwdMap_congr_of_eqOn fun _ hs => h ⟨hs.1, hs.2.trans htT⟩

/-- The branch `logDerivFwd` of `log f_t'` at times `t ∈ [0, T]` only depends on the driver on
`[0, T]`. -/
theorem logDerivFwd_congr_of_eqOn {W W' : ℝ → ℝ} (h : EqOn W W' (Icc 0 T)) (ht : 0 ≤ t)
    (htT : t ≤ T) : logDerivFwd W t z = logDerivFwd W' t z := by
  unfold logDerivFwd
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  rw [fwdMap_congr_of_eqOn_of_le h (hs.2.trans htT)]

/-- The driver clamped to `[0, T]`: `W (min (max s 0) T)`. It agrees with `W` on `[0, T]` and is
continuous as soon as `W` is continuous on `[0, T]`. -/
def clampDrv (W : ℝ → ℝ) (T : ℝ) (s : ℝ) : ℝ := W (min (max s 0) T)

theorem clampDrv_eqOn : EqOn (clampDrv W T) W (Icc 0 T) := fun s hs => by
  simp only [clampDrv, max_eq_left hs.1, min_eq_left hs.2]

theorem continuous_clampDrv (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T)) :
    Continuous (clampDrv W T) := by
  have hm : Continuous fun s : ℝ => min (max s 0) T := (continuous_id.max continuous_const).min
    continuous_const
  refine hW.comp_continuous hm fun s => ⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩

/-! ### Integrated forms of the Loewner equation -/

/-- A point not swallowed by time `T` has a forward solution on `[0, T]`. -/
theorem exists_isForwardSol_of_mem (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    ∃ u, IsForwardSol W z T u :=
  exists_isForwardSol_of_not_mem_fwdHull hT hz.1 hz.2

/-- A point not swallowed by time `T` is not swallowed by any earlier time. -/
theorem mem_diff_fwdHull_of_le (hz : z ∈ H \ fwdHull W T) (htT : t ≤ T) :
    z ∈ H \ fwdHull W t :=
  ⟨hz.1, fun h => hz.2 ((fwdHull_mono (W := W)).1 htT h)⟩

/-- **The integrated Loewner equation** for `f_t = g_t − W_t`:
`f_s(z) = z − W_s + ∫₀ˢ 2/f_r(z) dr` for `s ∈ [0, T]`, `z` not swallowed by time `T`. -/
theorem fwdMap_eq_sub_add_integral (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    fwdMap W s z = z - W s + ∫ r in (0 : ℝ)..s, 2 / fwdMap W r z := by
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem hT hz
  exact ((FwdClock.isForwardSol_fwdMap hW hz.1 hu).2 s hs).2

/-- The forward map is a solution of the forward flow on `[0, T]`. -/
theorem isForwardSol_fwdMap_of_mem (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    IsForwardSol W z T (fun s => fwdMap W s z) := by
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem hT hz
  exact FwdClock.isForwardSol_fwdMap hW hz.1 hu

/-- `Im f_s(z) > 0` for `s ∈ [0, T]`, `z` not swallowed by time `T`. -/
theorem im_fwdMap_pos (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) {s : ℝ}
    (hs : s ∈ Icc 0 T) : 0 < (fwdMap W s z).im :=
  (im_isForwardSol_le hW hz.1 (isForwardSol_fwdMap_of_mem hW hT hz)).2 s hs

theorem fwdMap_ne_zero (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) {s : ℝ}
    (hs : s ∈ Icc 0 T) : fwdMap W s z ≠ 0 := fun h => by
  have := im_fwdMap_pos hW hT hz hs
  rw [h, Complex.zero_im] at this
  exact lt_irrefl 0 this

/-- `s ↦ f_s(z)` is continuous on `[0, T]`. -/
theorem continuousOn_fwdMap_time' (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    ContinuousOn (fun s => fwdMap W s z) (Icc 0 T) :=
  (isForwardSol_fwdMap_of_mem hW hT hz).1

/-- **`∂ₜ g_t(z) = 2/f_t(z)`**: the uncentred map `g_t(z) = f_t(z) + W_t` has time derivative
`2/f_t(z)` on `[0, T]`. -/
theorem hasDerivWithinAt_fwdMap_add (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => fwdMap W r z + W r) (2 / fwdMap W s z) (Icc 0 T) s :=
  FwdHolo.hasDerivWithinAt_shift (isForwardSol_fwdMap_of_mem hW hT hz) hs

/-! ### The spatial derivative `f_t'(z)` -/

/-- `f_t'(z) = exp (logDerivFwd W t z)` (QuantumZipper's `FwdHolo.hasDerivAt_fwdMap`). -/
theorem deriv_fwdMap_eq_exp (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    deriv (fwdMap W T) z = Complex.exp (logDerivFwd W T z) :=
  (FwdHolo.hasDerivAt_fwdMap hW hT hz).deriv

theorem continuousOn_two_div_fwdMap_sq (hW : Continuous W) (hT : 0 ≤ T)
    (hz : z ∈ H \ fwdHull W T) : ContinuousOn (fun s => 2 / fwdMap W s z ^ 2) (Icc 0 T) :=
  continuousOn_const.div ((continuousOn_fwdMap_time' hW hT hz).pow 2) fun _ hs =>
    pow_ne_zero 2 (fwdMap_ne_zero hW hT hz hs)

/-- **`d log f_t'(z) = −2/f_t(z)² dt`** for the branch `logDerivFwd W t z = −∫₀ᵗ 2/f_s(z)² ds`
of `log f_t'(z)` (which vanishes at `t = 0`). -/
theorem hasDerivWithinAt_logDerivFwd (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => logDerivFwd W r z) (-(2 / fwdMap W s z ^ 2)) (Icc 0 T) s := by
  unfold logDerivFwd
  exact (FwdClock.hasDerivWithinAt_integral_Icc (continuousOn_two_div_fwdMap_sq hW hT hz) hs).neg

theorem continuousOn_logDerivFwd (hW : Continuous W) (hT : 0 ≤ T) (hz : z ∈ H \ fwdHull W T) :
    ContinuousOn (fun s => logDerivFwd W s z) (Icc 0 T) := fun _ hs =>
  (hasDerivWithinAt_logDerivFwd hW hT hz hs).continuousWithinAt

/-- The fundamental theorem of calculus on `[0, t]` for a function with a derivative within
`[0, T]` at every point, `t ≤ T`. -/
theorem integral_eq_sub_of_hasDerivWithinAt_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f f' : ℝ → E}
    (hf : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (f' s) (Icc 0 T) s)
    (hf' : ContinuousOn f' (Icc 0 T)) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ s in (0 : ℝ)..t, f' s = f t - f 0 := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (fun s hs => (hf s ⟨hs.1, hs.2.trans htT⟩).continuousWithinAt.mono
      (Icc_subset_Icc_right htT)) (fun s hs => ?_) ?_
  · have hs' : s ∈ Ioo (0 : ℝ) T := ⟨hs.1, hs.2.trans_le htT⟩
    exact ((hf s (Ioo_subset_Icc_self hs')).hasDerivAt
      (Icc_mem_nhds hs'.1 hs'.2)).hasDerivWithinAt
  · exact (hf'.mono (Icc_subset_Icc_right htT)).intervalIntegrable_of_Icc ht

/-- **`d f_t'(z) = −2 f_t'(z)/f_t(z)² dt`**, integrated: for `z` not swallowed by time `t`,
`f_t'(z) = 1 + ∫₀ᵗ (−2 f_s'(z)/f_s(z)²) ds`. -/
theorem deriv_fwdMap_eq_one_add_integral (hW : Continuous W) (ht : 0 ≤ t)
    (hz : z ∈ H \ fwdHull W t) :
    deriv (fwdMap W t) z =
      1 + ∫ s in (0 : ℝ)..t, -2 * deriv (fwdMap W s) z / fwdMap W s z ^ 2 := by
  have hE : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun r => Complex.exp (logDerivFwd W r z))
      (Complex.exp (logDerivFwd W s z) * -(2 / fwdMap W s z ^ 2)) (Icc 0 t) s := fun s hs =>
    (hasDerivWithinAt_logDerivFwd hW ht hz hs).cexp
  have hcont : ContinuousOn (fun s => Complex.exp (logDerivFwd W s z) * -(2 / fwdMap W s z ^ 2))
      (Icc 0 t) :=
    ((continuousOn_logDerivFwd hW ht hz).cexp).mul (continuousOn_two_div_fwdMap_sq hW ht hz).neg
  have hFTC := integral_eq_sub_of_hasDerivWithinAt_Icc hE hcont ht le_rfl
  have h0 : logDerivFwd W 0 z = 0 := by simp [logDerivFwd]
  rw [h0, Complex.exp_zero] at hFTC
  have hint : ∫ s in (0 : ℝ)..t, -2 * deriv (fwdMap W s) z / fwdMap W s z ^ 2 =
      ∫ s in (0 : ℝ)..t, Complex.exp (logDerivFwd W s z) * -(2 / fwdMap W s z ^ 2) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    rw [deriv_fwdMap_eq_exp hW hs.1 (mem_diff_fwdHull_of_le hz hs.2)]
    ring
  rw [hint, hFTC, deriv_fwdMap_eq_exp hW ht hz]
  ring

/-! ### (3.16): the Green function along the flow -/

/-- **(3.16)**, differential form (QuantumZipper `FwdClock.hasDerivWithinAt_greenH_fwdMap`):
`∂ₜ G(f_t y, f_t z) = −Im(2/f_t y) Im(2/f_t z)` on `[0, T]` for `y ≠ z` not swallowed by `T`. -/
theorem hasDerivWithinAt_greenH_fwdMap (hW : Continuous W) (hT : 0 ≤ T)
    (hy : y ∈ H \ fwdHull W T) (hz : z ∈ H \ fwdHull W T) (hyz : y ≠ z) {s : ℝ}
    (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (fun r => greenH (fwdMap W r y) (fwdMap W r z))
      (-((2 / fwdMap W s y).im * (2 / fwdMap W s z).im)) (Icc 0 T) s :=
  FwdClock.hasDerivWithinAt_greenH_fwdMap hW hy.1 hz.1 hyz (exists_isForwardSol_of_mem hT hy)
    (exists_isForwardSol_of_mem hT hz) hs

theorem continuousOn_im_two_div_mul (hW : Continuous W) (hT : 0 ≤ T)
    (hy : y ∈ H \ fwdHull W T) (hz : z ∈ H \ fwdHull W T) :
    ContinuousOn (fun s => (2 / fwdMap W s y).im * (2 / fwdMap W s z).im) (Icc 0 T) := by
  have h1 : ∀ x ∈ H \ fwdHull W T, ContinuousOn (fun s => (2 / fwdMap W s x).im) (Icc 0 T) :=
    fun x hx => Complex.continuous_im.comp_continuousOn
      (continuousOn_const.div (continuousOn_fwdMap_time' hW hT hx) fun _ hs =>
        fwdMap_ne_zero hW hT hx hs)
  exact (h1 y hy).mul (h1 z hz)

/-- **(3.16)**, integrated: for `y ≠ z` in `ℍ` not swallowed by time `t`,
`G(f_t y, f_t z) = G(y, z) − ∫₀ᵗ Im(2/f_s y) Im(2/f_s z) ds`. -/
theorem greenH_fwdMap_eq_sub_integral (hW : Continuous W) (ht : 0 ≤ t)
    (hy : y ∈ H \ fwdHull W t) (hz : z ∈ H \ fwdHull W t) (hyz : y ≠ z) :
    greenH (fwdMap W t y) (fwdMap W t z) =
      greenH y z - ∫ s in (0 : ℝ)..t, (2 / fwdMap W s y).im * (2 / fwdMap W s z).im := by
  have hFTC := integral_eq_sub_of_hasDerivWithinAt_Icc
    (fun s hs => hasDerivWithinAt_greenH_fwdMap hW ht hy hz hyz hs)
    (continuousOn_im_two_div_mul hW ht hy hz).neg ht le_rfl
  rw [intervalIntegral.integral_neg, FwdClock.greenH_fwdMap_zero hW hy.1 hz.1 ht
    (exists_isForwardSol_of_mem ht hy) (exists_isForwardSol_of_mem ht hz)] at hFTC
  linear_combination (exp := 1) -hFTC

/-! ### Drivers that are only continuous on `[0, T]` -/

/-- A solution on the closed interval `[0, T]` of a continuous driver means `z` is not swallowed by `T`
(QuantumZipper `Thm18Asm.LWFar.lwc_notMem_fwdHull_of_sol`, restated). -/
theorem notMem_fwdHull_of_isForwardSol (hW : Continuous W) (hz : 0 < z.im) (hT : 0 ≤ T)
    {u : ℝ → ℂ} (hu : IsForwardSol W z T u) : z ∉ fwdHull W T := by
  intro hK
  obtain ⟨-, σ, hσT, -, hc⟩ := (FwdClock.mem_fwdHull_iff_inf_im hW).1 hK
  have hanti := im_isForwardSol_le hW hz hu
  have hTT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  obtain ⟨t, ht0, htσ, hlt⟩ := hc (u T).im (hanti.2 T hTT)
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht0, by linarith⟩
  rw [fwdMap_eq hW hz hu htT] at hlt
  have := hanti.1 htT hTT htT.2
  linarith

/-- For a driver continuous on `[0, T]` with a forward solution on `[0, T]`, the clamped driver is
continuous and does not swallow `z` by time `T`. -/
theorem mem_diff_fwdHull_clampDrv (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T)) (hz : 0 < z.im)
    (hsol : ∃ u, IsForwardSol W z T u) : z ∈ H \ fwdHull (clampDrv W T) T := by
  obtain ⟨u, hu⟩ := hsol
  have hu' : IsForwardSol (clampDrv W T) z T u :=
    (isForwardSol_iff_of_eqOn (clampDrv_eqOn (W := W)) u).2 hu
  exact ⟨hz, notMem_fwdHull_of_isForwardSol (continuous_clampDrv hT hW) hz hT hu'⟩

theorem fwdMap_clampDrv_of_le (hs : s ≤ T) : fwdMap (clampDrv W T) s z = fwdMap W s z :=
  fwdMap_congr_of_eqOn_of_le (clampDrv_eqOn (W := W)) hs

/-- The integrated Loewner equation for a driver continuous on `[0, T]`. -/
theorem fwdMap_eq_sub_add_integral_of_continuousOn (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T))
    (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol W z T u) {s : ℝ} (hs : s ∈ Icc 0 T) :
    fwdMap W s z = z - W s + ∫ r in (0 : ℝ)..s, 2 / fwdMap W r z := by
  have h := fwdMap_eq_sub_add_integral (continuous_clampDrv hT hW) hT
    (mem_diff_fwdHull_clampDrv hT hW hz hsol) hs
  rw [fwdMap_clampDrv_of_le hs.2, clampDrv_eqOn hs] at h
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs.1] at hr
  simp only [fwdMap_clampDrv_of_le (hr.2.trans hs.2)]

theorem im_fwdMap_pos_of_continuousOn (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T))
    (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol W z T u) {s : ℝ} (hs : s ∈ Icc 0 T) :
    0 < (fwdMap W s z).im := by
  rw [← fwdMap_clampDrv_of_le hs.2]
  exact im_fwdMap_pos (continuous_clampDrv hT hW) hT (mem_diff_fwdHull_clampDrv hT hW hz hsol) hs

theorem continuousOn_fwdMap_of_continuousOn (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T))
    (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol W z T u) :
    ContinuousOn (fun s => fwdMap W s z) (Icc 0 T) :=
  (continuousOn_fwdMap_time' (continuous_clampDrv hT hW) hT
    (mem_diff_fwdHull_clampDrv hT hW hz hsol)).congr fun _ hs =>
      (fwdMap_clampDrv_of_le hs.2).symm

theorem antitoneOn_im_fwdMap_of_continuousOn (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T))
    (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol W z T u) :
    AntitoneOn (fun s => (fwdMap W s z).im) (Icc 0 T) := by
  have h := (im_isForwardSol_le (continuous_clampDrv hT hW) hz
    (isForwardSol_fwdMap_of_mem (continuous_clampDrv hT hW) hT
      (mem_diff_fwdHull_clampDrv hT hW hz hsol))).1
  intro a ha b hb hab
  have := h ha hb hab
  simp only [fwdMap_clampDrv_of_le ha.2, fwdMap_clampDrv_of_le hb.2] at this
  exact this

theorem logDerivFwd_clampDrv_of_le (hs : 0 ≤ s) (hsT : s ≤ T) :
    logDerivFwd (clampDrv W T) s z = logDerivFwd W s z :=
  logDerivFwd_congr_of_eqOn (clampDrv_eqOn (W := W)) hs hsT

theorem continuousOn_logDerivFwd_of_continuousOn (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T))
    (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol W z T u) :
    ContinuousOn (fun s => logDerivFwd W s z) (Icc 0 T) :=
  (continuousOn_logDerivFwd (continuous_clampDrv hT hW) hT
    (mem_diff_fwdHull_clampDrv hT hW hz hsol)).congr fun _ hs =>
      (logDerivFwd_clampDrv_of_le hs.1 hs.2).symm

theorem isForwardSol_of_le {u : ℝ → ℂ} (hu : IsForwardSol W z T u) (hs : 0 ≤ s) (hsT : s ≤ T) :
    IsForwardSol W z s u :=
  isForwardSol_restrict hu hs hsT

end Ito

end InteractingSLE
