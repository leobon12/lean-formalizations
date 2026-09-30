import QuantumZipper.Proofs.Loewner.CoreArc3b
import QuantumZipper.Proofs.Thm11.MainMart
import QuantumZipper.Proofs.Thm18.LWExcMaxPrin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SLE step (0): a hull inside the half disk of radius `R` has capacity time `≤ R²/2`

Task TIPX-DRIVE, TX-SLE route of `handoff/TIPX-ROUTE.md` §6, step (0). For a continuous driver
`A` with `A 0 = 0`, if the forward hull `K_s` lies in the closed disk `B̄(0, R)` then
`hcap K_s = 2s ≤ R² = hcap (B̄(0,R) ∩ ℍ)` (**`two_mul_le_sq_of_fwdHull_subset`**). Consequently the
curve leaves `B(0, R)` before capacity time `R²/2`; with `R = 1/4` the first exit time of
`B(0,1/4)` is `≤ 1/32 < 1/16`, the start of the window of `SLEBaseReturnStmt`.

Source: monotonicity of half-plane capacity and `hcap (B̄(0,R) ∩ ℍ) = R²` (Lawler, *Conformally
invariant processes in the plane*, 2005, §3.4, Prop. 3.41 and Example 3.39). Proof here (own
elementary argument, Nevanlinna-type comparison; no Brownian motion): on
`U = {Im z > 0, |z| > R} ⊆ ℍ \ K_s` the function `F = Im (z + R²/z) − Im f_s(z)` is harmonic,
`F ≤ Im(z + R²/z) → 0` at `∂U` (as `Im f_s > 0`), and `F ≤ Im z − Im f_s(z) → 0` at `∞` (clock
formula `Im f_s = Im z · e^{−2S}`, `S = ∫₀ˢ |f_u|^{−2}`, and `|f_u(z) − z| ≤ C`,
`CoreArc.norm_fwdMap_sub_le_uniform`); the maximum principle (`LWFar.lwExc_harm_le_zero`) gives
`F ≤ 0`, i.e. `1 − e^{−2S(it)} ≤ R²/t²`, and `S(it) ≥ s/(t + C)²` forces `2s ≤ R²`.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace TipXE

variable {A : ℝ → ℝ}

/-- `f_0 = id` for a driver with `A 0 = 0`, at points off the hull. -/
theorem fwdMap_zero_eq {z : ℂ} (hA : Continuous A) (hA0 : A 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    (hz : z ∈ H \ fwdHull A s) : fwdMap A 0 z = z := by
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hs hz.1 hz.2
  rw [fwdMap_eq hA hz.1 hu ⟨le_rfl, hs⟩, (hu.2 0 ⟨le_rfl, hs⟩).2, hA0]
  simp

/-- Uniform displacement bound `‖f_u(z) − z‖ ≤ C` for `u ∈ [0, s]`, `z ∉ K_s`. -/
theorem exists_fwdMap_disp_le (hA : Continuous A) (hA0 : A 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ H \ fwdHull A s, ∀ u ∈ Icc (0 : ℝ) s, ‖fwdMap A u z - z‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn (s := Icc 0 s))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, hs⟩)
  refine ⟨24 * M + 8 * Real.sqrt s, by positivity, fun z hz u hu => ?_⟩
  rcases hu.1.eq_or_lt with h0 | hpos
  · rw [← h0, fwdMap_zero_eq hA hA0 hs hz, sub_self, norm_zero]; positivity
  have hzu : z ∈ H \ fwdHull A u := ⟨hz.1, fun h => hz.2 (fwdHull_mono.1 hu.2 h)⟩
  have hb := CoreArc.norm_fwdMap_sub_le_uniform hA hA0 hpos
    (M := M) (fun t ht => by
      have := hM t ⟨ht.1, ht.2.trans hu.2⟩
      rwa [Real.norm_eq_abs] at this) hzu
  have : Real.sqrt u ≤ Real.sqrt s := Real.sqrt_le_sqrt hu.2
  linarith

/-- The comparison function `Im (z + R²/z) − Im f_s(z)`. -/
def hcapCmp (A : ℝ → ℝ) (s R : ℝ) (z : ℂ) : ℝ :=
  (z + (R : ℂ) ^ 2 / z).im - (fwdMap A s z).im

theorem im_add_sq_div_le (R : ℝ) {z : ℂ} (hz : 0 < z.im) (hR : R < ‖z‖) (hR0 : 0 < R) :
    (z + (R : ℂ) ^ 2 / z).im ≤ min z.im (2 * (‖z‖ - R)) := by
  have hn : 0 < ‖z‖ := hR0.trans hR
  have hns : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  have hkey : (z + (R : ℂ) ^ 2 / z).im = z.im * (1 - R ^ 2 / ‖z‖ ^ 2) := by
    rw [Complex.add_im, Complex.div_im, ← hns]
    have h1 : ((R : ℂ) ^ 2).re = R ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have h2 : ((R : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    rw [h1, h2]
    have : Complex.normSq z ≠ 0 := by rw [hns]; positivity
    field_simp
    ring
  rw [hkey]
  have hq : 0 ≤ 1 - R ^ 2 / ‖z‖ ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hq1 : 1 - R ^ 2 / ‖z‖ ^ 2 ≤ 1 := by
    have : 0 ≤ R ^ 2 / ‖z‖ ^ 2 := by positivity
    linarith
  have him : z.im ≤ ‖z‖ := Complex.im_le_norm z
  refine le_min (by nlinarith) ?_
  have e : z.im * (1 - R ^ 2 / ‖z‖ ^ 2) ≤ ‖z‖ * (1 - R ^ 2 / ‖z‖ ^ 2) :=
    mul_le_mul_of_nonneg_right him hq
  have e2 : ‖z‖ * (1 - R ^ 2 / ‖z‖ ^ 2) = (‖z‖ - R) * (‖z‖ + R) / ‖z‖ := by
    field_simp
    ring
  have e3 : (‖z‖ - R) * (‖z‖ + R) / ‖z‖ ≤ 2 * (‖z‖ - R) := by
    rw [div_le_iff₀ hn]
    nlinarith
  linarith

/-- `1 − e^{−x} ≥ x/(1+x)` for `x ≥ 0`. -/
theorem one_sub_exp_neg_ge {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hpos : 0 < 1 + x := by linarith
  have he : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hpos h1
  have : 1 / (1 + x) = 1 - x / (1 + x) := by field_simp; ring
  linarith

theorem im_add_sq_div_eq (R : ℝ) {z : ℂ} (hz : z ≠ 0) :
    (z + (R : ℂ) ^ 2 / z).im = z.im * (1 - R ^ 2 / ‖z‖ ^ 2) := by
  have hns : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  rw [Complex.add_im, Complex.div_im, ← hns]
  have h1 : ((R : ℂ) ^ 2).re = R ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h2 : ((R : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  rw [h1, h2]
  have : Complex.normSq z ≠ 0 := (Complex.normSq_pos.2 hz).ne'
  field_simp
  ring

/-- Clock bounds: if `‖f_u(z) − z‖ ≤ C` on `[0, s]` then
`s/(‖z‖ + C)² ≤ S_s(z) ≤ s/(‖z‖ − C)²` (the latter for `‖z‖ > C`). -/
theorem clock_bounds (hA : Continuous A) {s C : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ H \ fwdHull A s) (hC : ∀ u ∈ Icc (0 : ℝ) s, ‖fwdMap A u z - z‖ ≤ C)
    (hCz : C < ‖z‖) :
    s / (‖z‖ + C) ^ 2 ≤ FwdClock.fwdClock A s z ∧ FwdClock.fwdClock A s z ≤ s / (‖z‖ - C) ^ 2 := by
  have hI := MainMart.intervalIntegrable_clock hA hs hz
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, hs⟩)
  have hlo : ∀ u ∈ Icc (0 : ℝ) s, ‖z‖ - C ≤ ‖fwdMap A u z‖ := fun u hu => by
    have := norm_sub_norm_le z (fwdMap A u z)
    rw [norm_sub_rev] at this
    linarith [hC u hu]
  have hhi : ∀ u ∈ Icc (0 : ℝ) s, ‖fwdMap A u z‖ ≤ ‖z‖ + C := fun u hu => by
    have := norm_le_norm_add_norm_sub' (fwdMap A u z) z
    linarith [hC u hu]
  have hpos : 0 < ‖z‖ - C := by linarith
  unfold FwdClock.fwdClock
  constructor
  · have h := intervalIntegral.integral_mono_on hs intervalIntegrable_const hI
      (f := fun _ => 1 / (‖z‖ + C) ^ 2) fun u hu => by
        have h1 := hhi u hu
        have h2 : 0 < ‖fwdMap A u z‖ := hpos.trans_le (hlo u hu)
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h2.le h1 2)
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    calc s / (‖z‖ + C) ^ 2 = s * (1 / (‖z‖ + C) ^ 2) := by ring
      _ ≤ _ := h
  · have h := intervalIntegral.integral_mono_on hs hI intervalIntegrable_const
      (g := fun _ => 1 / (‖z‖ - C) ^ 2) fun u hu =>
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le (hlo u hu) 2)
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
    calc _ ≤ s * (1 / (‖z‖ - C) ^ 2) := h
      _ = s / (‖z‖ - C) ^ 2 := by ring

/-- **TX-SLE step (0).** If `K_s ⊆ B̄(0, R)` then `2s ≤ R²`. -/
theorem two_mul_le_sq_of_fwdHull_subset (hA : Continuous A) (hA0 : A 0 = 0) {s R : ℝ}
    (hs : 0 ≤ s) (hR : 0 < R) (hK : fwdHull A s ⊆ closedBall (0 : ℂ) R) : 2 * s ≤ R ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_fwdMap_disp_le hA hA0 hs
  set U : Set ℂ := {z | 0 < z.im ∧ R < ‖z‖} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt continuous_const continuous_norm)
  have hUsub : U ⊆ H \ fwdHull A s := fun z hz => ⟨hz.1, fun hk => by
    have := hK hk
    rw [mem_closedBall, dist_zero_right] at this
    linarith [hz.2]⟩
  have hz0 : ∀ z ∈ U, z ≠ 0 := fun z hz h => by
    have := hz.2; rw [h, norm_zero] at this; linarith
  have himf : ∀ z ∈ U, 0 < (fwdMap A s z).im := fun z hz =>
    (MainMart.im_fwdMap_pos_and_clock hA hs (hUsub hz)).1
  -- the clock formula
  have hclock : ∀ z ∈ U, (fwdMap A s z).im = z.im * Real.exp (-2 * FwdClock.fwdClock A s z) :=
    fun z hz => FwdClock.im_fwdMap_eq_clock hA hz.1
      (exists_isForwardSol_of_not_mem_fwdHull hs (hUsub hz).1 (hUsub hz).2) ⟨hs, le_rfl⟩
  -- maximum principle
  have hharm : InnerProductSpace.HarmonicOnNhd (hcapCmp A s R) U := by
    intro z hz
    have hn : U ∈ 𝓝 z := hUo.mem_nhds hz
    have ha1 : AnalyticAt ℂ (fun w : ℂ => w + (R : ℂ) ^ 2 / w) z := by
      have : DifferentiableOn ℂ (fun w : ℂ => w + (R : ℂ) ^ 2 / w) U := fun w hw =>
        (differentiableAt_id.add ((differentiableAt_const _).div differentiableAt_id
          (hz0 w hw))).differentiableWithinAt
      exact this.analyticAt hn
    have ha2 : AnalyticAt ℂ (fwdMap A s) z :=
      ((FwdHolo.differentiableOn_fwdMap hA hs).mono hUsub).analyticAt hn
    exact ha1.harmonicAt_im.sub ha2.harmonicAt_im
  have hle : ∀ z ∈ U, hcapCmp A s R z ≤ (z + (R : ℂ) ^ 2 / z).im := fun z hz => by
    unfold hcapCmp; linarith [himf z hz]
  have hbd : ∀ x₀ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ U, dist y x₀ < δ → hcapCmp A s R y ≤ ε := by
    intro x₀ hx₀ ε hε
    have hcl : x₀ ∈ closure U := frontier_subset_closure hx₀
    have hnot : x₀ ∉ U := fun h => (hUo.frontier_eq ▸ hx₀).2 h
    have hclsub : closure U ⊆ {z : ℂ | 0 ≤ z.im ∧ R ≤ ‖z‖} :=
      closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩)
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le continuous_const continuous_norm))
    have hx₁ := hclsub hcl
    refine ⟨ε / 2, by positivity, fun y hy hdist => ?_⟩
    have hm := im_add_sq_div_le R hy.1 hy.2 hR
    have hyx : ‖y - x₀‖ < ε / 2 := by rwa [← dist_eq_norm]
    refine (hle y hy).trans (hm.trans ?_)
    by_cases him : 0 < x₀.im
    · have hxR : ‖x₀‖ ≤ R := by
        by_contra h; exact hnot ⟨him, lt_of_not_ge h⟩
      have : ‖y‖ ≤ ‖x₀‖ + ‖y - x₀‖ := norm_le_norm_add_norm_sub' y x₀
      exact (min_le_right _ _).trans (by linarith)
    · have hx0 : x₀.im = 0 := le_antisymm (not_lt.1 him) hx₁.1
      have : y.im - x₀.im ≤ ‖y - x₀‖ := by
        rw [← Complex.sub_im]; exact Complex.im_le_norm _
      exact (min_le_left _ _).trans (by linarith)
  have hinf : ∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, ∀ y ∈ U, R' ≤ ‖y‖ → hcapCmp A s R y ≤ ε := by
    intro ε hε
    refine ⟨max (2 * C + 1) (8 * s / ε + 1), fun y hy hyR => ?_⟩
    have h1 : 2 * C + 1 ≤ ‖y‖ := (le_max_left _ _).trans hyR
    have h2 : 8 * s / ε + 1 ≤ ‖y‖ := (le_max_right _ _).trans hyR
    have hCy : C < ‖y‖ := by linarith
    obtain ⟨-, hSup⟩ := clock_bounds hA hs (hUsub hy) (hC y (hUsub hy)) hCy
    set S := FwdClock.fwdClock A s y
    have hS0 : 0 ≤ S := intervalIntegral.integral_nonneg hs fun u _ => by positivity
    have hyn : 0 < ‖y‖ := by linarith
    -- `F y ≤ Im y (1 − e^{−2S}) ≤ ‖y‖ · 2S`
    have hF : hcapCmp A s R y ≤ y.im * (1 - Real.exp (-2 * S)) := by
      have hm := (im_add_sq_div_le R hy.1 hy.2 hR).trans (min_le_left _ _)
      unfold hcapCmp
      rw [hclock y hy]
      nlinarith
    have hexp : 1 - Real.exp (-2 * S) ≤ 2 * S := by
      linarith [Real.add_one_le_exp (-2 * S)]
    have him : y.im ≤ ‖y‖ := Complex.im_le_norm y
    have hhalf : ‖y‖ / 2 ≤ ‖y‖ - C := by linarith
    have hS : S ≤ 4 * s / ‖y‖ ^ 2 := by
      refine hSup.trans ?_
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith [sq_nonneg (‖y‖ - C), mul_le_mul hhalf hhalf (by positivity) (by linarith)]
    have hq : 0 ≤ 1 - Real.exp (-2 * S) := by
      have : Real.exp (-2 * S) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      linarith
    calc hcapCmp A s R y ≤ y.im * (1 - Real.exp (-2 * S)) := hF
      _ ≤ ‖y‖ * (2 * S) := mul_le_mul him hexp hq hyn.le
      _ ≤ ‖y‖ * (2 * (4 * s / ‖y‖ ^ 2)) := by gcongr
      _ = 8 * s / ‖y‖ := by field_simp; ring
      _ ≤ ε := by
        rw [div_le_iff₀ hyn]
        have : 8 * s / ε * ε = 8 * s := div_mul_cancel₀ _ hε.ne'
        nlinarith
  have hF0 := Thm18Asm.LWFar.lwExc_harm_le_zero hUo hharm hbd hinf
  -- evaluate at `z = t i`, `t` large
  by_contra hcon
  push Not at hcon
  set d : ℝ := 2 * s - R ^ 2 with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set t : ℝ := max (R + C + 1) (R ^ 2 * (2 * C + C ^ 2 + 2 * s) / d + 1) with ht
  have ht1 : R + C + 1 ≤ t := le_max_left _ _
  have ht2 : R ^ 2 * (2 * C + C ^ 2 + 2 * s) / d + 1 ≤ t := le_max_right _ _
  have htpos : 0 < t := by linarith
  set z : ℂ := (t : ℂ) * Complex.I with hzdef
  have hzn : ‖z‖ = t := by
    rw [hzdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
  have hzim : z.im = t := by simp [hzdef]
  have hzU : z ∈ U := ⟨by rw [hzim]; exact htpos, by rw [hzn]; linarith⟩
  have hFz := hF0 z hzU
  obtain ⟨hSlo, -⟩ := clock_bounds hA hs (hUsub hzU) (hC z (hUsub hzU)) (by rw [hzn]; linarith)
  rw [hzn] at hSlo
  set S := FwdClock.fwdClock A s z
  -- `F z ≤ 0` means `t e^{−2S} ≥ t (1 − R²/t²)`
  have hineq : 1 - Real.exp (-2 * S) ≤ R ^ 2 / t ^ 2 := by
    have e := hFz
    unfold hcapCmp at e
    rw [im_add_sq_div_eq R (hz0 z hzU), hclock z hzU, hzn, hzim] at e
    have : t * (1 - Real.exp (-2 * S)) ≤ t * (R ^ 2 / t ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this htpos
  have hS0 : 0 ≤ 2 * S := by
    have : 0 ≤ s / (t + C) ^ 2 := by positivity
    linarith
  have hlow := one_sub_exp_neg_ge hS0
  have ha : 2 * s / (t + C) ^ 2 ≤ 2 * S := by
    have := mul_le_mul_of_nonneg_left hSlo (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * s / (t + C) ^ 2 = 2 * (s / (t + C) ^ 2) := by ring
      _ ≤ 2 * S := this
  -- `x ↦ x/(1+x)` is monotone
  have hmono : 2 * s / (t + C) ^ 2 / (1 + 2 * s / (t + C) ^ 2) ≤ 2 * S / (1 + 2 * S) := by
    have hp : 0 ≤ 2 * s / (t + C) ^ 2 := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hkey : 2 * s / (t + C) ^ 2 / (1 + 2 * s / (t + C) ^ 2) ≤ R ^ 2 / t ^ 2 :=
    hmono.trans (hlow.trans (by simpa [neg_mul] using hineq))
  have htc : 0 < (t + C) ^ 2 := by positivity
  have hrew : 2 * s / (t + C) ^ 2 / (1 + 2 * s / (t + C) ^ 2) = 2 * s / ((t + C) ^ 2 + 2 * s) := by
    field_simp
  rw [hrew, div_le_div_iff₀ (by positivity) (by positivity)] at hkey
  -- `2 s t² ≤ R² ((t + C)² + 2s)` contradicts the choice of `t`
  have hbig : R ^ 2 * (2 * C + C ^ 2 + 2 * s) < d * t := by
    have := (div_lt_iff₀ hdpos).1 (show R ^ 2 * (2 * C + C ^ 2 + 2 * s) / d < t by linarith)
    linarith
  have ht1' : 1 ≤ t := by linarith
  nlinarith [mul_le_mul_of_nonneg_left ht1' (sq_nonneg R), mul_le_mul_of_nonneg_left ht1'
    (show 0 ≤ R ^ 2 * (C ^ 2 + 2 * s) by positivity)]

end TipXE
end QuantumZipper
