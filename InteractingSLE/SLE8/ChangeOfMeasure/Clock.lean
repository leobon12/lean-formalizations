import InteractingSLE.SLE8.ReverseFlow
import QuantumZipper.Proofs.Loewner.Algebra
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The height parameter of the reverse flow (SLE₈ note, (3.1), (3.5), (3.10), (3.3))

SLE₈ note `source/sle8-continuity.pdf`, §3.1, pp. 4–5 (transcription `source/sle8/sle8-continuity.md`,
anchors `lem-3.1`, `lem-3.1-proof`).

Everything here is deterministic. Fix a continuous driver `W` and `y > 0`, and let
`Z_s = revMap W s (iy) = X_s + i Y_s` be QuantumZipper's centred reverse flow from `iy` (the note's
`Z_s(iy)` of (2.6)), with `Φ_s = |Z_s'(iy)|`. The height `Y_s` is continuous and strictly increasing,
`log Y_s = log y + ∫₀ˢ 2/|Z_r|² dr`, so `u = log Y_s` is the note's increasing height parameter.

* `hitTime W y c`: the first time at which `Y` reaches the level `c` (`sInf` over `ℝ≥0`); the
  height-parameter clock is `u ↦ hitTime W y (exp u)` (`𝔰⁻¹` of (3.6)).
* `logIm_sub_logPhi`: (3.5) in the capacity parameter,
  `log Y_s − log y − log Φ_s = 4 ∫₀ˢ Y_r² / |Z_r|⁴ dr` (the note's `2 ∫ sech² J du`).
* `im_ge_of_cone`: growth of the height while `|X| ≤ k Y` and `Y ≤ √5`.
* `volume_occupation_le`: the occupation bound (3.3) from (3.10), via the change of variables
  `u = log Y_s` (`du = 2/|Z_s|² ds`).
-/

noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal

namespace InteractingSLE.SLE8.ChangeOfMeasure

open QuantumZipper

/-! ### The height process -/

/-- The reverse flow from `iy`: `Z_s = revMap W s (iy)`. -/
def htZ (W : ℝ → ℝ) (y s : ℝ) : ℂ := revMap W s ((y : ℂ) * I)

theorem mem_H_mul_I {y : ℝ} (hy : 0 < y) : ((y : ℂ) * I) ∈ H := by
  show 0 < ((y : ℂ) * I).im
  simpa using hy

theorem im_mul_I (y : ℝ) : ((y : ℂ) * I).im = y := by simp

variable {W : ℝ → ℝ} {y : ℝ}

theorem le_im_htZ (hW : Continuous W) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) : y ≤ (htZ W y s).im := by
  have := im_le_im_revMap W hW ((y : ℂ) * I) (by simpa using hy) hs
  rwa [im_mul_I] at this

theorem im_htZ_pos (hW : Continuous W) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) : 0 < (htZ W y s).im :=
  hy.trans_le (le_im_htZ hW hy hs)

theorem htZ_ne_zero (hW : Continuous W) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) : htZ W y s ≠ 0 := by
  intro h
  have := im_htZ_pos hW hy hs
  rw [h] at this
  simp at this

theorem htZ_zero (hW : Continuous W) (hy : 0 < y) (hW0 : W 0 = 0) : htZ W y 0 = (y : ℂ) * I := by
  rw [htZ, revMap_zero hW (mem_H_mul_I hy), hW0]
  simp

theorem im_htZ_zero (hW : Continuous W) (hy : 0 < y) : (htZ W y 0).im = y := by
  rw [htZ, revMap_zero hW (mem_H_mul_I hy)]
  simp

theorem continuousOn_htZ (hW : Continuous W) (hy : 0 < y) :
    ContinuousOn (htZ W y) (Ici 0) :=
  ReverseFlow.continuousOn_revMap_time W hW _ (by simpa using hy)

theorem strictMonoOn_im_htZ (hW : Continuous W) (hy : 0 < y) :
    StrictMonoOn (fun s => (htZ W y s).im) (Ici 0) :=
  LoewnerAlgebra.strictMonoOn_im_revMap W hW _ (by simpa using hy)

/-- `log Y_s = log y + ∫₀ˢ 2/|Z_r|² dr`. -/
theorem log_im_htZ (hW : Continuous W) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) :
    Real.log (htZ W y s).im = Real.log y + ∫ r in (0 : ℝ)..s, 2 / ‖htZ W y r‖ ^ 2 := by
  have := TwoPoint.log_im_revMap hW (mem_H_mul_I hy) hs
  rw [im_mul_I] at this
  exact this

/-- `log Φ_s = Re ∫₀ˢ 2/Z_r² dr`. -/
theorem log_phi_htZ (hW : Continuous W) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) :
    Real.log ‖deriv (revMap W s) ((y : ℂ) * I)‖ = (∫ r in (0 : ℝ)..s, 2 / (htZ W y r) ^ 2).re :=
  log_norm_deriv_revMap W hW hs (mem_H_mul_I hy)

/-- `Φ_s ≤ Y_s / y` (Lemma 2.2). -/
theorem phi_le_im_div (hW : Continuous W) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) :
    ‖deriv (revMap W s) ((y : ℂ) * I)‖ ≤ (htZ W y s).im / y := by
  have := TwoPoint.norm_deriv_revMap_le hW (mem_H_mul_I hy) hs
  rwa [im_mul_I] at this

/-- `Y_s² ≤ y² + 4 s` (Lemma 2.2). -/
theorem im_htZ_sq_le (hW : Continuous W) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) :
    (htZ W y s).im ^ 2 ≤ y ^ 2 + 4 * s := by
  have := TwoPoint.im_revMap_sq_le hW (mem_H_mul_I hy) hs
  rwa [im_mul_I] at this

theorem continuousOn_gain (hW : Continuous W) (hy : 0 < y) :
    ContinuousOn (fun r => 2 / ‖htZ W y r‖ ^ 2) (Ici 0) :=
  continuousOn_const.div ((continuousOn_htZ hW hy).norm.pow 2) fun _ hr =>
    pow_ne_zero 2 (norm_ne_zero_iff.2 (htZ_ne_zero hW hy hr))

theorem continuousOn_two_div_sq (hW : Continuous W) (hy : 0 < y) :
    ContinuousOn (fun r => 2 / (htZ W y r) ^ 2) (Ici 0) :=
  continuousOn_const.div ((continuousOn_htZ hW hy).pow 2) fun _ hr =>
    pow_ne_zero 2 (htZ_ne_zero hW hy hr)

theorem re_two_div_sq_eq (u : ℂ) :
    (2 / u ^ 2).re = 2 * (u.re ^ 2 - u.im ^ 2) / (u.re ^ 2 + u.im ^ 2) ^ 2 := by
  rw [Complex.div_re, map_pow, Complex.normSq_apply]
  simp [pow_two, Complex.mul_re, Complex.mul_im]

theorem norm_sq_eq (u : ℂ) : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- **(3.5)** in the capacity parameter: `log Y_s − log y − log Φ_s = 4 ∫₀ˢ Y_r²/|Z_r|⁴ dr`. -/
theorem logIm_sub_logPhi (hW : Continuous W) (hy : 0 < y) {s : ℝ} (hs : 0 ≤ s) :
    Real.log (htZ W y s).im - Real.log y - Real.log ‖deriv (revMap W s) ((y : ℂ) * I)‖ =
      ∫ r in (0 : ℝ)..s, 4 * (htZ W y r).im ^ 2 / ‖htZ W y r‖ ^ 4 := by
  rw [log_im_htZ hW hy hs, log_phi_htZ hW hy hs]
  have hsub : uIcc 0 s ⊆ Ici (0 : ℝ) := by rw [uIcc_of_le hs]; exact Icc_subset_Ici_self
  have hi1 : IntervalIntegrable (fun r => 2 / ‖htZ W y r‖ ^ 2) volume 0 s :=
    ((continuousOn_gain hW hy).mono hsub).intervalIntegrable
  have hi2 : IntervalIntegrable (fun r => 2 / (htZ W y r) ^ 2) volume 0 s :=
    ((continuousOn_two_div_sq hW hy).mono hsub).intervalIntegrable
  have hi3 : IntervalIntegrable (fun r => (2 / (htZ W y r) ^ 2).re) volume 0 s :=
    ((Complex.continuous_re.comp_continuousOn (continuousOn_two_div_sq hW hy)).mono
      hsub).intervalIntegrable
  rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hi2]
  simp only [Complex.reCLM_apply]
  rw [add_sub_cancel_left, ← intervalIntegral.integral_sub hi1 hi3]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [re_two_div_sq_eq, show ‖htZ W y r‖ ^ 4 = (‖htZ W y r‖ ^ 2) ^ 2 by ring, norm_sq_eq]
  have hr0 : 0 ≤ r := by
    rw [uIcc_of_le hs] at hr; exact hr.1
  have hN : 0 < (htZ W y r).re ^ 2 + (htZ W y r).im ^ 2 := by
    have := im_htZ_pos hW hy hr0
    positivity
  field_simp
  ring

/-- **Growth of the height in a cone.** If `|X_r| ≤ k Y_r` and `Y_r ≤ √5` for `r ∈ [0,s]`, then
`Y_s ≥ y e^{2s / (5(1+k²))}`. -/
theorem im_ge_of_cone (hW : Continuous W) (hy : 0 < y) {s k : ℝ} (hs : 0 ≤ s)
    (hcone : ∀ r ∈ Icc 0 s, |(htZ W y r).re| ≤ k * (htZ W y r).im ∧ (htZ W y r).im ≤ √5) :
    y * Real.exp (2 * s / (5 * (1 + k ^ 2))) ≤ (htZ W y s).im := by
  have hY := im_htZ_pos hW hy hs
  have hc : 2 * s / (5 * (1 + k ^ 2)) ≤ ∫ r in (0 : ℝ)..s, 2 / ‖htZ W y r‖ ^ 2 := by
    have hsub : uIcc 0 s ⊆ Ici (0 : ℝ) := by rw [uIcc_of_le hs]; exact Icc_subset_Ici_self
    have hint := ((continuousOn_gain hW hy).mono hsub).intervalIntegrable (μ := volume)
    have h := intervalIntegral.integral_mono_on hs (intervalIntegrable_const (c := 2 / (5 * (1 + k ^ 2))))
      hint (fun r hr => ?_)
    · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
      calc 2 * s / (5 * (1 + k ^ 2)) = s * (2 / (5 * (1 + k ^ 2))) := by ring
        _ ≤ _ := h
    · obtain ⟨h1, h2⟩ := hcone r hr
      have hYr := im_htZ_pos hW hy hr.1
      rw [norm_sq_eq]
      have hX2 : (htZ W y r).re ^ 2 ≤ k ^ 2 * (htZ W y r).im ^ 2 := by
        have := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
        calc (htZ W y r).re ^ 2 ≤ (k * (htZ W y r).im) ^ 2 := this
          _ = k ^ 2 * (htZ W y r).im ^ 2 := by ring
      have hY2 : (htZ W y r).im ^ 2 ≤ 5 := by
        have := pow_le_pow_left₀ hYr.le h2 2
        rwa [Real.sq_sqrt (by norm_num)] at this
      have hN : 0 < (htZ W y r).re ^ 2 + (htZ W y r).im ^ 2 := by positivity
      rw [div_le_div_iff₀ (by positivity) hN]
      nlinarith
  have := log_im_htZ hW hy hs
  calc y * Real.exp (2 * s / (5 * (1 + k ^ 2)))
      ≤ y * Real.exp (∫ r in (0 : ℝ)..s, 2 / ‖htZ W y r‖ ^ 2) := by gcongr
    _ = (htZ W y s).im := by
      rw [← Real.exp_log hY, this, Real.exp_add, Real.exp_log hy]

/-! ### The hitting-time clock -/

/-- The first time `s ≥ 0` at which the height `Y_s` reaches the level `c` (`0` if it never does). The
height-parameter clock of the note is `u ↦ hitTime W y (e^u)`. -/
def hitTime (W : ℝ → ℝ) (y c : ℝ) : ℝ≥0 := sInf {s : ℝ≥0 | c ≤ (htZ W y s).im}

theorem continuous_im_htZ_nnreal (hW : Continuous W) (hy : 0 < y) :
    Continuous fun s : ℝ≥0 => (htZ W y s).im := by
  refine Complex.continuous_im.comp ?_
  exact (continuousOn_htZ hW hy).comp_continuous NNReal.continuous_coe fun s => s.coe_nonneg

theorem monotone_im_htZ_nnreal (hW : Continuous W) (hy : 0 < y) :
    Monotone fun s : ℝ≥0 => (htZ W y s).im := fun s t hst =>
  (strictMonoOn_im_htZ hW hy).monotoneOn s.coe_nonneg t.coe_nonneg (by exact_mod_cast hst)

theorem strictMono_im_htZ_nnreal (hW : Continuous W) (hy : 0 < y) :
    StrictMono fun s : ℝ≥0 => (htZ W y s).im := fun s t hst =>
  strictMonoOn_im_htZ hW hy s.coe_nonneg t.coe_nonneg (by exact_mod_cast hst)

theorem isClosed_level (hW : Continuous W) (hy : 0 < y) (c : ℝ) :
    IsClosed {s : ℝ≥0 | c ≤ (htZ W y s).im} :=
  isClosed_le continuous_const (continuous_im_htZ_nnreal hW hy)

theorem hitTime_le (s : ℝ≥0) {c : ℝ} (hs : c ≤ (htZ W y s).im) : hitTime W y c ≤ s :=
  csInf_le (OrderBot.bddBelow _) hs

theorem le_im_hitTime (hW : Continuous W) (hy : 0 < y) {c : ℝ}
    (hreach : ∃ s : ℝ≥0, c ≤ (htZ W y s).im) : c ≤ (htZ W y (hitTime W y c)).im :=
  (isClosed_level hW hy c).csInf_mem hreach (OrderBot.bddBelow _)

theorem hitTime_eq_zero (hW : Continuous W) (hy : 0 < y) {c : ℝ} (hc : c ≤ y) :
    hitTime W y c = 0 :=
  le_antisymm (hitTime_le 0 (by rw [NNReal.coe_zero, im_htZ_zero hW hy]; exact hc)) bot_le

/-- At the hitting time the height equals the level. -/
theorem im_hitTime (hW : Continuous W) (hy : 0 < y) {c : ℝ} (hc : y ≤ c)
    (hreach : ∃ s : ℝ≥0, c ≤ (htZ W y s).im) : (htZ W y (hitTime W y c)).im = c := by
  refine le_antisymm ?_ (le_im_hitTime hW hy hreach)
  obtain ⟨s₁, hs₁⟩ := hreach
  have hY0 : (htZ W y ((0 : ℝ≥0) : ℝ)).im ≤ c := by
    rw [NNReal.coe_zero, im_htZ_zero hW hy]; exact hc
  obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ s₁)
    (continuous_im_htZ_nnreal hW hy).continuousOn ⟨hY0, hs₁⟩
  calc (htZ W y (hitTime W y c)).im ≤ (htZ W y s).im :=
        monotone_im_htZ_nnreal hW hy (hitTime_le s hsc.ge)
    _ = c := hsc

theorem hitTime_le_iff (hW : Continuous W) (hy : 0 < y) {c : ℝ}
    (hreach : ∃ s : ℝ≥0, c ≤ (htZ W y s).im) (t : ℝ≥0) :
    hitTime W y c ≤ t ↔ c ≤ (htZ W y t).im :=
  ⟨fun h => (le_im_hitTime hW hy hreach).trans (monotone_im_htZ_nnreal hW hy h),
    hitTime_le t⟩

theorem hitTime_im (hW : Continuous W) (hy : 0 < y) (s : ℝ≥0) :
    hitTime W y (htZ W y s).im = s := by
  refine le_antisymm (hitTime_le s le_rfl) ?_
  by_contra h
  have h1 := strictMono_im_htZ_nnreal hW hy (lt_of_not_ge h)
  have h2 := le_im_hitTime hW hy ⟨s, le_rfl⟩
  exact absurd h2 (not_le.2 h1)

theorem hitTime_mono (hW : Continuous W) (hy : 0 < y) {c d : ℝ} (hcd : c ≤ d)
    (hreach : ∃ s : ℝ≥0, d ≤ (htZ W y s).im) : hitTime W y c ≤ hitTime W y d :=
  hitTime_le _ (hcd.trans (le_im_hitTime hW hy hreach))

/-- The hitting-time clock is continuous on the levels below a reached level `cmax`. -/
theorem continuousOn_hitTime (hW : Continuous W) (hy : 0 < y) {cmax : ℝ} (hyc : y ≤ cmax)
    (hreach : ∃ s : ℝ≥0, cmax ≤ (htZ W y s).im) :
    ContinuousOn (fun c => (hitTime W y c : ℝ)) (Iic cmax) := by
  set cl : ℝ → ℝ := fun c => max y (min c cmax) with hcl
  have hcl_le : ∀ c, cl c ≤ cmax := fun c => max_le hyc (min_le_right _ _)
  have hcl_ge : ∀ c, y ≤ cl c := fun c => le_max_left _ _
  have hreach' : ∀ c, ∃ s : ℝ≥0, cl c ≤ (htZ W y s).im := fun c =>
    let ⟨s, hs⟩ := hreach; ⟨s, (hcl_le c).trans hs⟩
  set G : ℝ → ℝ := fun c => (hitTime W y (cl c) : ℝ) + max 0 (c - cmax) + min 0 (c - y) with hG
  have hclm : Monotone cl := fun a b hab => max_le_max le_rfl (min_le_min hab le_rfl)
  have hGm : Monotone G := by
    intro a b hab
    have h1 : (hitTime W y (cl a) : ℝ) ≤ hitTime W y (cl b) := by
      exact_mod_cast hitTime_mono hW hy (hclm hab) (hreach' b)
    have h2 : max 0 (a - cmax) ≤ max 0 (b - cmax) := max_le_max le_rfl (by linarith)
    have h3 : min 0 (a - y) ≤ min 0 (b - y) := min_le_min le_rfl (by linarith)
    simp only [hG]
    linarith
  set S : ℝ≥0 := hitTime W y cmax with hS
  have hGs : Function.Surjective G := by
    intro w
    rcases lt_or_ge w 0 with hw | hw
    · refine ⟨y + w, ?_⟩
      have : cl (y + w) = y := by simp only [hcl]; rw [max_eq_left]; exact min_le_of_left_le (by linarith)
      simp only [hG, this, hitTime_eq_zero hW hy le_rfl, NNReal.coe_zero]
      rw [max_eq_left (by linarith), min_eq_right (by linarith)]
      ring
    rcases le_or_gt w S with hwS | hwS
    · set w' : ℝ≥0 := w.toNNReal
      have hw' : (w' : ℝ) = w := Real.coe_toNNReal w hw
      have hw'S : w' ≤ S := by rw [← NNReal.coe_le_coe, hw']; exact hwS
      have hYw : (htZ W y w').im ≤ cmax := by
        calc (htZ W y w').im ≤ (htZ W y S).im := monotone_im_htZ_nnreal hW hy hw'S
          _ = cmax := im_hitTime hW hy hyc hreach
      have hYy : y ≤ (htZ W y w').im := le_im_htZ hW hy w'.coe_nonneg
      refine ⟨(htZ W y w').im, ?_⟩
      have : cl (htZ W y w').im = (htZ W y w').im := by
        simp only [hcl]; rw [min_eq_left hYw, max_eq_right hYy]
      simp only [hG]
      rw [this, max_eq_left (by linarith), min_eq_left (by linarith), hitTime_im hW hy w', hw']
      ring
    · refine ⟨cmax + (w - S), ?_⟩
      have : cl (cmax + (w - S)) = cmax := by
        simp only [hcl]; rw [min_eq_right (by linarith), max_eq_right hyc]
      simp only [hG, this, ← hS]
      rw [max_eq_right (by linarith), min_eq_left (by linarith)]
      ring
  have hGc : Continuous G := hGm.continuous_of_surjective hGs
  have hcont : Continuous fun c => (hitTime W y (cl c) : ℝ) := by
    have : (fun c => (hitTime W y (cl c) : ℝ)) =
        fun c => G c - max 0 (c - cmax) - min 0 (c - y) := by
      funext c; simp only [hG]; ring
    rw [this]
    fun_prop
  refine hcont.continuousOn.congr fun c hc => ?_
  simp only
  rcases le_or_gt c y with h | h
  · have hcl' : cl c = y := by simp only [hcl]; exact max_eq_left (min_le_of_left_le h)
    rw [hcl', hitTime_eq_zero hW hy h, hitTime_eq_zero hW hy le_rfl]
  · congr 2
    simp only [hcl]
    rw [min_eq_left (show c ≤ cmax from hc), max_eq_right h.le]

/-! ### The height-parameter path and the occupation bound -/

/-- `J = arsinh (X / Y)` of a point `Z = X + iY`. -/
def jFun (z : ℂ) : ℝ := Real.arsinh (z.re / z.im)

/-- The height-parameter path `u ↦ J_u = arsinh(X/Y)` at the time `hitTime W y (e^{min u U})` at which
`log Y` reaches `min u U` (constant `J_{u₀} = 0` before `u₀ = log y`, frozen after `U`). -/
def htJ (W : ℝ → ℝ) (y U u : ℝ) : ℝ := jFun (htZ W y (hitTime W y (Real.exp (min u U))))

theorem hitTime_exp_log_im (hW : Continuous W) (hy : 0 < y) {r : ℝ} (hr : 0 ≤ r) :
    (hitTime W y (Real.exp (Real.log (htZ W y r).im)) : ℝ) = r := by
  rw [Real.exp_log (im_htZ_pos hW hy hr)]
  have := hitTime_im hW hy r.toNNReal
  rw [Real.coe_toNNReal r hr] at this
  rw [this, Real.coe_toNNReal r hr]

theorem htJ_log_im (hW : Continuous W) (hy : 0 < y) {U r : ℝ} (hr : 0 ≤ r)
    (hU : Real.log (htZ W y r).im ≤ U) :
    htJ W y U (Real.log (htZ W y r).im) = jFun (htZ W y r) := by
  rw [htJ, min_eq_left hU, hitTime_exp_log_im hW hy hr]

theorem hasDerivWithinAt_log_im (hW : Continuous W) (hy : 0 < y) {T r : ℝ} (hr : r ∈ Icc 0 T) :
    HasDerivWithinAt (fun t => Real.log (htZ W y t).im) (2 / ‖htZ W y r‖ ^ 2) (Icc 0 T) r := by
  have : Fact (r ∈ Icc 0 T) := ⟨hr⟩
  have hT : 0 ≤ T := hr.1.trans hr.2
  have hc : ContinuousOn (fun r => 2 / ‖htZ W y r‖ ^ 2) (Icc 0 T) :=
    (continuousOn_gain hW hy).mono Icc_subset_Ici_self
  have hint : IntervalIntegrable (fun r => 2 / ‖htZ W y r‖ ^ 2) volume 0 r :=
    (hc.mono (by rw [uIcc_of_le hr.1]; exact Icc_subset_Icc_right hr.2)).intervalIntegrable
  have h := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 T) (t := Icc 0 T) hint
    (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc r) (hc r hr)
  refine (h.const_add (Real.log y)).congr (fun t ht => log_im_htZ hW hy ht.1) (log_im_htZ hW hy hr.1)

/-- The occupation constant `C_occ = cosh² 1 / 2` of (3.3). -/
def occConst : ℝ := Real.cosh 1 ^ 2 / 2

theorem occConst_pos : 0 < occConst := by unfold occConst; positivity

/-- **The occupation bound (3.3)**, from (3.10): if `Y_T ≤ √5 ≤ e^U` and `a ≤ y Φ_T`, then the
height-parameter time spent by `J` in `[-1, 1]` before `τ_T = log Y_T` is at most
`C_occ (log √5 − log a)`. -/
theorem volume_occupation_le (hW : Continuous W) (hy : 0 < y) {T U a : ℝ} (hT : 0 ≤ T)
    (hTU : Real.log (htZ W y T).im ≤ U) (hY5 : (htZ W y T).im ≤ √5) (ha : 0 < a)
    (hphi : a ≤ y * ‖deriv (revMap W T) ((y : ℂ) * I)‖) :
    volume {u | u ∈ Icc (Real.log y) (Real.log (htZ W y T).im) ∧ |htJ W y U u| ≤ 1} ≤
      ENNReal.ofReal (occConst * (Real.log (√5) - Real.log a)) := by
  set f : ℝ → ℝ := fun t => Real.log (htZ W y t).im with hf
  set S : Set ℝ := {r | r ∈ Icc 0 T ∧ |jFun (htZ W y r)| ≤ 1} with hS
  have hjc : ContinuousOn (fun r => |jFun (htZ W y r)|) (Icc 0 T) := by
    refine (Real.continuous_arsinh.comp_continuousOn ?_).abs
    have hZ := (continuousOn_htZ hW hy).mono (Icc_subset_Ici_self : Icc (0 : ℝ) T ⊆ Ici 0)
    exact (Complex.continuous_re.comp_continuousOn hZ).div
      (Complex.continuous_im.comp_continuousOn hZ) fun r hr => (im_htZ_pos hW hy hr.1).ne'
  have hSc : IsClosed S := hjc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSm : MeasurableSet S := hSc.measurableSet
  have hSsub : S ⊆ Icc 0 T := fun r hr => hr.1
  have hderiv : ∀ r ∈ S, HasDerivWithinAt f (2 / ‖htZ W y r‖ ^ 2) S r := fun r hr =>
    (hasDerivWithinAt_log_im hW hy hr.1).mono hSsub
  have hmono : MonotoneOn f S := fun r hr t ht hrt =>
    Real.log_le_log (im_htZ_pos hW hy hr.1.1)
      ((strictMonoOn_im_htZ hW hy).monotoneOn hr.1.1 ht.1.1 hrt)
  -- the image of `S` is the occupation set
  have himage : f '' S = {u | u ∈ Icc (Real.log y) (Real.log (htZ W y T).im) ∧
      |htJ W y U u| ≤ 1} := by
    ext u
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hYr := im_htZ_pos hW hy hr.1.1
      have hle : (htZ W y r).im ≤ (htZ W y T).im :=
        (strictMonoOn_im_htZ hW hy).monotoneOn hr.1.1 hT hr.1.2
      have hfr : f r ≤ Real.log (htZ W y T).im := Real.log_le_log hYr hle
      refine ⟨⟨Real.log_le_log hy (le_im_htZ hW hy hr.1.1), hfr⟩, ?_⟩
      simp only [hf]
      rw [htJ_log_im hW hy hr.1.1 (hfr.trans hTU)]
      exact hr.2
    · rintro ⟨⟨hu1, hu2⟩, hu3⟩
      have hYT := im_htZ_pos hW hy hT
      have h1 : (htZ W y 0).im ≤ Real.exp u := by
        rw [im_htZ_zero hW hy, ← Real.exp_log hy]; exact Real.exp_le_exp.2 hu1
      have h2 : Real.exp u ≤ (htZ W y T).im := by
        rw [← Real.exp_log hYT]; exact Real.exp_le_exp.2 hu2
      have hcont : ContinuousOn (fun r => (htZ W y r).im) (Icc 0 T) :=
        Complex.continuous_im.comp_continuousOn
          ((continuousOn_htZ hW hy).mono Icc_subset_Ici_self)
      obtain ⟨r, hr, hre⟩ := intermediate_value_Icc hT hcont ⟨h1, h2⟩
      simp only at hre
      have hfr : f r = u := by simp only [hf]; rw [hre, Real.log_exp]
      refine ⟨r, ⟨hr, ?_⟩, hfr⟩
      have := htJ_log_im hW hy (U := U) hr.1 (by rw [hre, Real.log_exp]; exact hu2.trans hTU)
      rw [hre, Real.log_exp] at this
      rw [← this]
      exact hu3
  rw [← himage, ← setLIntegral_one, lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn hSm hderiv
    hmono]
  simp only [mul_one]
  -- pointwise bound on `S`
  set g : ℝ → ℝ := fun r => occConst * (4 * (htZ W y r).im ^ 2 / ‖htZ W y r‖ ^ 4) with hg
  have hpt : ∀ r ∈ S, ENNReal.ofReal (2 / ‖htZ W y r‖ ^ 2) ≤ ENNReal.ofReal (g r) := by
    intro r hr
    refine ENNReal.ofReal_le_ofReal ?_
    have hYr := im_htZ_pos hW hy hr.1.1
    have hJ := hr.2
    have hsinh : |(htZ W y r).re / (htZ W y r).im| ≤ Real.sinh 1 := by
      have h := Real.sinh_arsinh ((htZ W y r).re / (htZ W y r).im)
      rw [← h, Real.abs_sinh]
      exact Real.sinh_le_sinh.2 hJ
    have hX : (htZ W y r).re ^ 2 ≤ Real.sinh 1 ^ 2 * (htZ W y r).im ^ 2 := by
      have h := sq_le_sq' (neg_le_of_abs_le hsinh) (le_of_abs_le hsinh)
      rw [div_pow, div_le_iff₀ (by positivity)] at h
      linarith
    have hN : ‖htZ W y r‖ ^ 2 ≤ Real.cosh 1 ^ 2 * (htZ W y r).im ^ 2 := by
      rw [norm_sq_eq, Real.cosh_sq]
      nlinarith
    have hN0 : 0 < ‖htZ W y r‖ ^ 2 := by
      rw [norm_sq_eq]; positivity
    simp only [hg, occConst]
    rw [show ‖htZ W y r‖ ^ 4 = (‖htZ W y r‖ ^ 2) ^ 2 by ring]
    set N := ‖htZ W y r‖ ^ 2
    calc 2 / N = 2 * N / N ^ 2 := by field_simp
      _ ≤ 2 * (Real.cosh 1 ^ 2 * (htZ W y r).im ^ 2) / N ^ 2 := by gcongr
      _ = Real.cosh 1 ^ 2 / 2 * (4 * (htZ W y r).im ^ 2 / N ^ 2) := by ring
  have hgc : ContinuousOn g (Icc 0 T) := by
    have hZ := (continuousOn_htZ hW hy).mono (Icc_subset_Ici_self : Icc (0 : ℝ) T ⊆ Ici 0)
    refine continuousOn_const.mul (((continuousOn_const.mul
      ((Complex.continuous_im.comp_continuousOn hZ).pow 2)).div (hZ.norm.pow 4)) fun r hr => ?_)
    exact pow_ne_zero 4 (norm_ne_zero_iff.2 (htZ_ne_zero hW hy hr.1))
  have hg0 : ∀ r, 0 ≤ g r := fun r => by
    simp only [hg]; have := occConst_pos; positivity
  have hgi : IntegrableOn g (Icc 0 T) := hgc.integrableOn_Icc
  calc ∫⁻ r in S, ENNReal.ofReal (2 / ‖htZ W y r‖ ^ 2)
      ≤ ∫⁻ r in S, ENNReal.ofReal (g r) := setLIntegral_mono' hSm hpt
    _ ≤ ∫⁻ r in Icc 0 T, ENNReal.ofReal (g r) := lintegral_mono_set hSsub
    _ = ENNReal.ofReal (∫ r in Icc 0 T, g r) :=
        (ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0)).symm
    _ = ENNReal.ofReal (occConst * (Real.log (htZ W y T).im - Real.log y -
          Real.log ‖deriv (revMap W T) ((y : ℂ) * I)‖)) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
          logIm_sub_logPhi hW hy hT]
        simp only [hg]
        rw [intervalIntegral.integral_const_mul]
    _ ≤ ENNReal.ofReal (occConst * (Real.log (√5) - Real.log a)) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ occConst_pos.le)
        have hYT := im_htZ_pos hW hy hT
        have hphi0 : 0 < ‖deriv (revMap W T) ((y : ℂ) * I)‖ := by
          rcases (norm_nonneg (deriv (revMap W T) ((y : ℂ) * I))).lt_or_eq with h | h
          · exact h
          · rw [← h, mul_zero] at hphi; linarith
        have h1 : Real.log a ≤ Real.log y + Real.log ‖deriv (revMap W T) ((y : ℂ) * I)‖ := by
          rw [← Real.log_mul hy.ne' hphi0.ne']; exact Real.log_le_log ha hphi
        have h2 : Real.log (htZ W y T).im ≤ Real.log (√5) := Real.log_le_log hYT hY5
        linarith

end InteractingSLE.SLE8.ChangeOfMeasure
