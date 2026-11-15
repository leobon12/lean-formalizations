/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtAFlow
import InteractingSLE.Spec.Coupling.Fubini

/-!
# The local comparison of Aux. lemma 55: (HL6)–(HL7), the source drift is the distant-force drift

Packet PROVE-LOCEXT-A, deterministic parts of step 4. Source: Aux. lemma 55, proof (`source/spec/p241-288.md`
L184–L212, pp. 248–249): "(HL4) `a_s = ∫_ℍ k_s(z) v(z) d²z` […] Let `P_t` be Dirichlet projection onto
`H¹₀(ℍ ∖ K_t)` […] `f − P_t f = q − q_t` on `ℍ ∖ K_t`, `P_t f = q_t` near the new hull (HL6). […] The Green
representation `P_t f = G_{ℍ∖K_t} v` now identifies its inward normal derivative in the half-plane coordinate at
`W_t` as `−a_t` […] `a_t = κ^{-1/2} ∑_{j∈J} ρ_j/(W_t − V^j_t)` (HL7)."

## Route (no Sobolev projection, no boundary normal derivative)

Fix a time `s` in the local regime. Write `A(u) = ∫ Im(2/f_u(z)) v(z) dz` (the source drift `a_u`) and
`E(u) = κ^{-1/2} ∑_J ρ_j/(W_u − V^j_u)` (the distant drift). Two representations of one function on `ℍ ∖ K_s`:

1. `D_s(y) = ∫₀ˢ Im(2/f_u(y)) (E(u) − A(u)) du` (harmonic: the imaginary part of a holomorphic function);
2. `D_s(y) = G_{ℍ∖K_s} v (y) − f(y) + q(y) − q_s(y)`, by the integrated Loewner–Green identity (3.16) against `v`
   with `G_ℍ v = f` (Green inversion, `LocalExtACutoff`), and the dynamics of (HL5) (`LocalExtAFlow`).

The second form shows `D_s → 0` at the hull and at the real points near it (there `f = q`, and both
`G_{ℍ∖K_s} v` and `q_s` vanish on the boundary in the half-plane coordinate), the first form shows `D_s → 0` at the
real points away from the hull and at `∞`. Hence `D_s = 0` (bounded harmonic uniqueness in the half-plane
coordinate), which is (HL6); then `∫₀ˢ Im(2/f_u(y)) (E − A) du = 0` for all `s` gives `A = E`, which is (HL7).

This file: the local regime and its elementary bounds (separation of the source from the hulls).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull IsForwardSol greenH)

/-! ### The local regime -/

/-- **The local regime of Aux. 55** for a continuous driver `W : ℝ → ℝ` up to time `T`: `W 0 = 0`, `T ≤ r²/64`
and `|W| ≤ r/4` on `[0, T]`. -/
structure IsLocalRegime (W : ℝ → ℝ) (r T : ℝ) : Prop where
  cont : Continuous W
  zero : W 0 = 0
  r_pos : 0 < r
  T_nonneg : 0 ≤ T
  T_le : T ≤ r ^ 2 / 64
  bound : ∀ u ∈ Icc (0 : ℝ) T, |W u| ≤ r / 4

namespace IsLocalRegime

variable {W : ℝ → ℝ} {r T : ℝ}

theorem mono (h : IsLocalRegime W r T) {s : ℝ} (hs : s ∈ Icc 0 T) : IsLocalRegime W r s :=
  ⟨h.cont, h.zero, h.r_pos, hs.1, hs.2.trans h.T_le, fun u hu => h.bound u ⟨hu.1, hu.2.trans hs.2⟩⟩

/-- **The hull lies in `B̄(0, 5r/8)`.** -/
theorem fwdHull_subset (h : IsLocalRegime W r T) : fwdHull W T ⊆ closedBall 0 (5 * r / 8) := by
  rcases eq_or_lt_of_le h.T_nonneg with hT0 | hTpos
  · intro z hz
    exfalso
    have hpos := QuantumZipper.swallowTime_pos h.cont hz.1
    have hle : QuantumZipper.swallowTime W z ≤ ENNReal.ofReal T := hz.2
    rw [← hT0, ENNReal.ofReal_zero] at hle
    exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)
  · have hsq : Real.sqrt T ≤ r / 8 := by
      rw [Real.sqrt_le_left (by linarith [h.r_pos])]
      nlinarith [h.T_le]
    exact (QuantumZipper.CaraR.fwdHull_subset_closedBall h.cont hTpos h.bound).trans
      (closedBall_subset_closedBall (by linarith))

/-- A point of `ℍ` outside `B̄(0, 5r/8)` is alive through the regime. -/
theorem mem_of_lt_norm (h : IsLocalRegime W r T) {z : ℂ} (hz : 0 < z.im) (hzn : 5 * r / 8 < ‖z‖) :
    z ∈ H \ fwdHull W T :=
  ⟨hz, fun hK => by
    have := h.fwdHull_subset hK
    rw [mem_closedBall, dist_zero_right] at this
    linarith⟩

/-- **The source is far from the driver**: for `z ∈ ℍ` with `6r ≤ |z| ≤ 7r`, `|f_u(z)| ≥ 11r/4`. -/
theorem le_norm_fwdMap_src (h : IsLocalRegime W r T) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖)
    {u : ℝ} (hu : u ∈ Icc 0 T) : 11 * r / 4 ≤ ‖fwdMap W u z‖ := by
  have hr := h.r_pos
  have halive := h.mem_of_lt_norm hz (by linarith)
  rcases le_or_gt (3 * r) |z.re| with hre | hre
  · rcases le_or_gt 0 z.re with h0 | h0
    · rw [abs_of_nonneg h0] at hre
      have := le_re_fwdMap_of_le_re h.cont h.T_nonneg halive h.bound (δ := 11 * r / 4) (by linarith)
        (by linarith) hu
      exact this.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    · rw [abs_of_neg h0] at hre
      have := re_fwdMap_le_of_re_le h.cont h.T_nonneg halive h.bound (δ := 11 * r / 4) (by linarith)
        (by linarith) hu
      exact (by linarith : 11 * r / 4 ≤ -(fwdMap W u z).re).trans ((neg_le_abs _).trans
        (Complex.abs_re_le_norm _))
  · -- the point is high: `Im z ≥ √27 r ≥ 5r`
    have hnsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have him5 : 5 * r ≤ z.im := by
      have h36 : 36 * r ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hre9 : z.re ^ 2 < 9 * r ^ 2 := by
        have := abs_lt.1 hre; nlinarith
      nlinarith
    have hbar := sq_im_le_sq_im_fwdMap h.cont h.T_nonneg halive hu
    have hu5 : 5 * u ≤ 5 * (r ^ 2 / 64) := by linarith [hu.2, h.T_le]
    have him : 11 * r / 4 ≤ (fwdMap W u z).im := by
      have hpos := Ito.im_fwdMap_pos h.cont h.T_nonneg halive hu
      nlinarith
    exact him.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))

/-- **Points near the seed stay near the driver**: for `y` alive at `s` with `|y| ≤ r`, `|f_s(y)| ≤ 7r/4`. -/
theorem norm_fwdMap_le_of_norm_le (h : IsLocalRegime W r T) {y : ℂ} (hy : y ∈ H \ fwdHull W T)
    (hyn : ‖y‖ ≤ r) {u : ℝ} (hu : u ∈ Icc 0 T) : ‖fwdMap W u y‖ ≤ 7 * r / 4 := by
  have hr := h.r_pos
  have hu8 : 8 / r * u ≤ r / 8 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hr]; nlinarith [hu.2, h.T_le]
  have hyre : |y.re| ≤ r := (Complex.abs_re_le_norm y).trans hyn
  have hWu := h.bound u hu
  have hup := re_g_le h.cont h.T_nonneg hy h.bound (R₀ := r / 2) (by linarith) hu
  have hlo := le_re_g h.cont h.T_nonneg hy h.bound (R₀ := r / 2) (by linarith) hu
  rw [show 4 / (r / 2) = 8 / r by field_simp; ring] at hup hlo
  have hmax : max y.re (r / 4 + r / 2) ≤ r := max_le (abs_le.1 hyre).2 (by linarith)
  have hmin : -r ≤ min y.re (-(r / 4) - r / 2) := le_min (abs_le.1 hyre).1 (by linarith)
  have hre : |(fwdMap W u y).re| ≤ 11 * r / 8 := by
    rw [abs_le]; constructor <;> linarith [(abs_le.1 hWu).1, (abs_le.1 hWu).2]
  have him : (fwdMap W u y).im ≤ r := by
    have hanti := (QuantumZipper.im_isForwardSol_le h.cont hy.1
      (Ito.isForwardSol_fwdMap_of_mem h.cont h.T_nonneg hy)).1 ⟨le_rfl, h.T_nonneg⟩ hu hu.1
    have h0 : (fwdMap W 0 y).im = y.im := by
      rw [Ito.fwdMap_eq_sub_add_integral h.cont h.T_nonneg hy ⟨le_rfl, h.T_nonneg⟩]
      simp
    beta_reduce at hanti
    rw [h0] at hanti
    exact hanti.trans ((le_abs_self _).trans ((Complex.abs_im_le_norm y).trans hyn))
  have him0 := (Ito.im_fwdMap_pos h.cont h.T_nonneg hy hu).le
  have hsq : ‖fwdMap W u y‖ ^ 2 ≤ (7 * r / 4) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [abs_le.1 hre, sq_abs (fwdMap W u y).re]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith) two_ne_zero).1 hsq

end IsLocalRegime

/-! ### The source drift and the Green potential -/

section Source

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

/-- The open set carrying the source: `{Im z > 0, |z| > 5r/8}` (outside every hull of the regime). -/
def srcSet (r : ℝ) : Set ℂ := {z : ℂ | 0 < z.im ∧ 5 * r / 8 < ‖z‖}

theorem isOpen_srcSet (r : ℝ) : IsOpen (srcSet r) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt continuous_const continuous_norm)

theorem mem_srcSet_of_vSrc_ne_zero (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {z : ℂ}
    (hz : vSrc κ xL xR ρL ρR r z ≠ 0) : z ∈ srcSet r ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r := by
  by_contra hn
  refine hz (vSrc_eq_zero_of_not hF hr fun h => hn ⟨⟨h.1, ?_⟩, h.2⟩)
  linarith [h.2.1, hr.1]

theorem exists_abs_vSrc_le (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    ∃ C, 0 ≤ C ∧ ∀ z, |vSrc κ xL xR ρL ρR r z| ≤ C := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_vDens (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hr.1
    ).exists_bound_of_continuous (continuous_vDens hF hr)
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ QuantumZipper.H
  · rw [vSrc, Set.indicator_of_mem hz, ← Real.norm_eq_abs]; exact (hC z).trans (le_max_left _ _)
  · rw [vSrc, Set.indicator_of_notMem hz, abs_zero]; exact le_max_right _ _

theorem integrable_vSrc (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Integrable (vSrc κ xL xR ρL ρR r) :=
  ((continuous_vDens hF hr).integrable_of_hasCompactSupport (hasCompactSupport_vDens hr.1)).indicator
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet

variable (κ xL xR ρL ρR r)

/-- **The source drift** `A(u) = ∫ Im(2/f_u(z)) v(z) dz` (the coefficient `a_u` of (HL4)). -/
def srcDrift (W : ℝ → ℝ) (u : ℝ) : ℝ := ∫ z, (2 / fwdMap W u z).im * vSrc κ xL xR ρL ρR r z

/-- **The Green potential of the source in `ℍ ∖ K_s`**: `G_{ℍ∖K_s} v (y) = ∫ G_ℍ(f_s y, f_s z) v(z) dz`. -/
def greenPot (W : ℝ → ℝ) (s : ℝ) (y : ℂ) : ℝ :=
  ∫ z, greenH (fwdMap W s y) (fwdMap W s z) * vSrc κ xL xR ρL ρR r z

variable {κ xL xR ρL ρR r}

open Classical in
/-- `Im(2/f_u)` on the source set, `0` elsewhere (a measurable version of the kernel). -/
def srcKer (r : ℝ) (W : ℝ → ℝ) (u : ℝ) (z : ℂ) : ℝ :=
  (srcSet r).piecewise (fun z => (2 / fwdMap W u z).im) (fun _ => 0) z

theorem continuousOn_fwdMap_srcSet {W : ℝ → ℝ} {T : ℝ} (h : IsLocalRegime W r T) {u : ℝ}
    (hu : u ∈ Icc 0 T) : ContinuousOn (fwdMap W u) (srcSet r) := by
  have hsub : srcSet r ⊆ H \ fwdHull W u := fun z hz => (h.mono hu).mem_of_lt_norm hz.1 hz.2
  exact ((QuantumZipper.FwdHolo.differentiableOn_fwdMap h.cont hu.1).continuousOn).mono hsub

theorem measurable_srcKer {W : ℝ → ℝ} {T : ℝ} (h : IsLocalRegime W r T) {u : ℝ} (hu : u ∈ Icc 0 T) :
    Measurable (srcKer r W u) := by
  classical
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const (isOpen_srcSet r).measurableSet
  have hsub : srcSet r ⊆ H \ fwdHull W u := fun z hz => (h.mono hu).mem_of_lt_norm hz.1 hz.2
  exact Complex.continuous_im.comp_continuousOn (continuousOn_const.div (continuousOn_fwdMap_srcSet h hu)
    fun z hz => Ito.fwdMap_ne_zero h.cont hu.1 (hsub hz) ⟨hu.1, le_rfl⟩)

theorem srcKer_mul_vSrc (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (W : ℝ → ℝ) (u : ℝ)
    (z : ℂ) : srcKer r W u z * vSrc κ xL xR ρL ρR r z = (2 / fwdMap W u z).im * vSrc κ xL xR ρL ρR r z := by
  classical
  by_cases hz : vSrc κ xL xR ρL ρR r z = 0
  · simp [hz]
  · rw [srcKer, Set.piecewise_eq_of_mem _ _ _ (mem_srcSet_of_vSrc_ne_zero hF hr hz).1]

/-- `|Im(2/f_u(z))| ≤ 8/(11r)` on the source. -/
theorem abs_im_two_div_src_le {W : ℝ → ℝ} {T : ℝ} (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {u : ℝ} (hu : u ∈ Icc 0 T) {z : ℂ}
    (hz : vSrc κ xL xR ρL ρR r z ≠ 0) : |(2 / fwdMap W u z).im| ≤ 8 / (11 * r) := by
  obtain ⟨hzS, hz6, -⟩ := mem_srcSet_of_vSrc_ne_zero hF hr hz
  have hn := h.le_norm_fwdMap_src hzS.1 hz6 hu
  have hpos : 0 < ‖fwdMap W u z‖ := lt_of_lt_of_le (by linarith [h.r_pos]) hn
  calc |(2 / fwdMap W u z).im| ≤ ‖2 / fwdMap W u z‖ := Complex.abs_im_le_norm _
    _ = 2 / ‖fwdMap W u z‖ := by rw [norm_div]; simp
    _ ≤ 2 / (11 * r / 4) := div_le_div_of_nonneg_left zero_le_two (by linarith [h.r_pos]) hn
    _ = 8 / (11 * r) := by field_simp; ring

/-- The clamp of a time to `[0, s]`. -/
def clampS (s u : ℝ) : ℝ := max 0 (min u s)

theorem clampS_mem {s : ℝ} (hs : 0 ≤ s) (u : ℝ) : clampS s u ∈ Icc 0 s :=
  ⟨le_max_left _ _, max_le hs (min_le_right _ _)⟩

theorem clampS_of_mem {s u : ℝ} (hu : u ∈ Icc 0 s) : clampS s u = u := by
  simp [clampS, max_eq_right hu.1, min_eq_left hu.2]

theorem continuous_clampS (s : ℝ) : Continuous (clampS s) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem integrable_greenH_mul_vSrc (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (w : ℂ) :
    Integrable fun z => greenH w z * vSrc κ xL xR ρL ρR r z := by
  have hHm : MeasurableSet QuantumZipper.H := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have h := (integrable_greenH_mul_vDens (κ := κ) (ρL := ρL) (ρR := ρR) hF hr w).indicator hHm
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [vSrc, Set.indicator_mul_right]

/-- **The integrated Loewner–Green identity against the source** ((3.16) integrated against `v`, with Green
inversion `G_ℍ v = f`): for `y` alive at `s`,
`G_{ℍ∖K_s} v (y) = f(y) − ∫₀ˢ Im(2/f_u(y)) A(u) du`. -/
theorem greenPot_eq {W : ℝ → ℝ} {T : ℝ} (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {s : ℝ} (hs : s ∈ Icc 0 T) {y : ℂ} (hy : y ∈ H \ fwdHull W s) :
    greenPot κ xL xR ρL ρR r W s y =
      fCut κ xL xR ρL ρR r y - ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * srcDrift κ xL xR ρL ρR r W u := by
  classical
  have hsr := h.mono hs
  have hs0 := hs.1
  have hr0 : 0 < r := hr.1
  obtain ⟨Cv, hCv0, hCv⟩ := exists_abs_vSrc_le (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
  set v := vSrc κ xL xR ρL ρR r with hv
  -- the kernel at `y` is bounded on `[0, s]`
  set δ := (fwdMap W s y).im with hδ
  have hδpos : 0 < δ := Ito.im_fwdMap_pos h.cont hs0 hy ⟨hs0, le_rfl⟩
  have hanti := (QuantumZipper.im_isForwardSol_le h.cont hy.1 (Ito.isForwardSol_fwdMap_of_mem h.cont hs0 hy)).1
  have hky : ∀ u ∈ Icc (0 : ℝ) s, |(2 / fwdMap W u y).im| ≤ 2 / δ := fun u hu => by
    have hle : δ ≤ (fwdMap W u y).im := hanti hu ⟨hs0, le_rfl⟩ hu.2
    have hpos : 0 < ‖fwdMap W u y‖ := norm_pos_iff.2 (Ito.fwdMap_ne_zero h.cont hs0 hy hu)
    calc |(2 / fwdMap W u y).im| ≤ ‖2 / fwdMap W u y‖ := Complex.abs_im_le_norm _
      _ = 2 / ‖fwdMap W u y‖ := by rw [norm_div]; simp
      _ ≤ 2 / δ := div_le_div_of_nonneg_left zero_le_two hδpos
          (hle.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _)))
  -- the integrand on `ℝ × ℂ`
  set F : ℝ → ℂ → ℝ := fun u z => (2 / fwdMap W (clampS s u) y).im * (srcKer r W (clampS s u) z * v z)
    with hF_def
  have hcy : Continuous fun u => (2 / fwdMap W (clampS s u) y).im := by
    refine Complex.continuous_im.comp ?_
    have hc := (Ito.continuousOn_fwdMap_time' h.cont hs0 hy).comp_continuous (continuous_clampS s)
      (clampS_mem hs0)
    exact continuous_const.div hc fun u => Ito.fwdMap_ne_zero h.cont hs0 hy (clampS_mem hs0 u)
  have hFm : Measurable fun p : ℝ × ℂ => F p.1 p.2 := by
    refine Coupling.measurable_uncurry_of_continuousOn isClosed_univ (0 : ℝ) (fun z => ?_) (fun u _ => ?_)
      (fun u hu => absurd (mem_univ u) hu)
    · refine Continuous.continuousOn ?_
      by_cases hz : z ∈ srcSet r
      · have hzs : z ∈ H \ fwdHull W s := hsr.mem_of_lt_norm hz.1 hz.2
        have hc := (Ito.continuousOn_fwdMap_time' h.cont hs0 hzs).comp_continuous (continuous_clampS s)
          (clampS_mem hs0)
        have hk : Continuous fun u => srcKer r W (clampS s u) z := by
          simp only [srcKer, Set.piecewise_eq_of_mem _ _ _ hz]
          exact Complex.continuous_im.comp (continuous_const.div hc fun u =>
            Ito.fwdMap_ne_zero h.cont hs0 hzs (clampS_mem hs0 u))
        exact hcy.mul (hk.mul continuous_const)
      · simp only [hF_def, srcKer, Set.piecewise_eq_of_notMem _ _ _ hz, zero_mul, mul_zero]
        exact continuous_const
    · exact measurable_const.mul ((measurable_srcKer h ⟨(clampS_mem hs0 u).1,
        (clampS_mem hs0 u).2.trans hs.2⟩).mul (measurable_vSrc hF hr))
  -- the bound
  set K := 2 / δ * (8 / (11 * r)) * Cv with hK
  have hFb : ∀ u z, |F u z| ≤ K * (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) z := by
    intro u z
    by_cases hz : v z = 0
    · simp only [hF_def, hz, mul_zero, abs_zero]
      exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · obtain ⟨hzS, hz6, hz7⟩ := mem_srcSet_of_vSrc_ne_zero hF hr hz
      have hcu := clampS_mem hs0 u
      rw [Set.indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; exact hz7), mul_one]
      simp only [hF_def, srcKer, Set.piecewise_eq_of_mem _ _ _ hzS, abs_mul]
      have h1 := hky _ hcu
      have h2 := abs_im_two_div_src_le h hF hr ⟨hcu.1, hcu.2.trans hs.2⟩ hz
      have h3 := hCv z
      calc |(2 / fwdMap W (clampS s u) y).im| * (|(2 / fwdMap W (clampS s u) z).im| * |v z|)
          ≤ 2 / δ * (8 / (11 * r) * Cv) := by gcongr
        _ = K := by rw [hK]; ring
  have hint : Integrable (Function.uncurry F) ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℂ => (fun _ : ℝ => (1 : ℝ)) p.1 *
        (fun z => K * (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) z) p.2)
        ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
      have hball : Integrable fun z : ℂ => (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) z :=
        (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
      have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) s)) := by
        rw [uIoc_of_le hs0]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      exact Integrable.mul_prod (L := ℝ) (integrable_const _) (hball.const_mul K)
    refine hg.mono' hFm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, one_mul, Real.norm_eq_abs]
    exact hFb p.1 p.2
  -- the swap
  have hswap := intervalIntegral_integral_swap hint
  have hleft : ∫ u in (0 : ℝ)..s, ∫ z, F u z = ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im *
      srcDrift κ xL xR ρL ρR r W u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs0] at hu
    simp only [hF_def, clampS_of_mem hu, integral_const_mul, srcDrift]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => srcKer_mul_vSrc hF hr W u z)
  have hright : ∀ z, z ≠ y → greenH (fwdMap W s y) (fwdMap W s z) * v z =
      greenH y z * v z - ∫ u in (0 : ℝ)..s, F u z := by
    intro z hzy
    by_cases hz : v z = 0
    · simp [hF_def, hz]
    · have hzS := (mem_srcSet_of_vSrc_ne_zero hF hr hz).1
      have hzs : z ∈ H \ fwdHull W s := hsr.mem_of_lt_norm hzS.1 hzS.2
      rw [Ito.greenH_fwdMap_eq_sub_integral h.cont hs0 hy hzs hzy.symm, sub_mul]
      congr 1
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hs0] at hu
      simp only [hF_def, clampS_of_mem hu, srcKer, Set.piecewise_eq_of_mem _ _ _ hzS]
      ring
  have hFi : Integrable fun z => ∫ u in (0 : ℝ)..s, F u z := by
    have := hint.integral_prod_right
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, intervalIntegral.integral_of_le hs0, uIoc_of_le hs0]
  have hae : (fun z => greenH (fwdMap W s y) (fwdMap W s z) * v z) =ᵐ[volume]
      fun z => greenH y z * v z - ∫ u in (0 : ℝ)..s, F u z := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton y)] with z hz
    exact hright z hz
  rw [greenPot, ← hv, integral_congr_ae hae, integral_sub (integrable_greenH_mul_vSrc hF hr y) hFi,
    integral_greenH_mul_vSrc hF hr, ← hswap, hleft]

/-- **The source drift is continuous** on the regime (dominated convergence). -/
theorem continuousOn_srcDrift {W : ℝ → ℝ} {T : ℝ} (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) : ContinuousOn (srcDrift κ xL xR ρL ρR r W) (Icc 0 T) := by
  classical
  have hr0 : 0 < r := hr.1
  have he : srcDrift κ xL xR ρL ρR r W = fun u => ∫ z, srcKer r W u z * vSrc κ xL xR ρL ρR r z := by
    funext u; exact integral_congr_ae (ae_of_all _ fun z => (srcKer_mul_vSrc hF hr W u z).symm)
  rw [he]
  refine continuousOn_of_dominated (bound := fun z => 8 / (11 * r) * |vSrc κ xL xR ρL ρR r z|)
    (fun u hu => ((measurable_srcKer h hu).mul (measurable_vSrc hF hr)).aestronglyMeasurable)
    (fun u hu => ae_of_all _ fun z => ?_) ((integrable_vSrc hF hr).abs.const_mul _) (ae_of_all _ fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : vSrc κ xL xR ρL ρR r z = 0
    · simp [hz]
    · rw [srcKer, Set.piecewise_eq_of_mem _ _ _ (mem_srcSet_of_vSrc_ne_zero hF hr hz).1]
      exact mul_le_mul_of_nonneg_right (abs_im_two_div_src_le h hF hr hu hz) (abs_nonneg _)
  · by_cases hz : z ∈ srcSet r
    · have hzT : z ∈ H \ fwdHull W T := h.mem_of_lt_norm hz.1 hz.2
      simp only [srcKer, Set.piecewise_eq_of_mem _ _ _ hz]
      exact (Complex.continuous_im.comp_continuousOn (continuousOn_const.div
        (Ito.continuousOn_fwdMap_time' h.cont h.T_nonneg hzT)
          fun u hu => Ito.fwdMap_ne_zero h.cont h.T_nonneg hzT hu)).mul continuousOn_const
    · simp only [srcKer, Set.piecewise_eq_of_notMem _ _ _ hz, zero_mul]
      exact continuousOn_const

theorem abs_srcDrift_le {W : ℝ → ℝ} {T : ℝ} (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {u : ℝ} (hu : u ∈ Icc 0 T) :
    |srcDrift κ xL xR ρL ρR r W u| ≤ 8 / (11 * r) * ∫ z, |vSrc κ xL xR ρL ρR r z| := by
  rw [srcDrift, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    ((integrable_vSrc hF hr).abs.const_mul _) (ae_of_all _ fun z => ?_))
  beta_reduce
  rw [abs_mul]
  by_cases hz : vSrc κ xL xR ρL ρR r z = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (abs_im_two_div_src_le h hF hr hu hz) (abs_nonneg _)

end Source

end LocalExt

end InteractingSLE
