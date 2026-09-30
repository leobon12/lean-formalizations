import QuantumZipper.Proofs.Thm18.G1RestUnifDefs
import QuantumZipper.Proofs.Zipper.RegContEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST-UNIF-AVG: regularized circle averages of the rescaled wedge field along `ψ`

Proof of `G1RC.AvgRegPsiStmt` (G1RestUnifDefs.lean): for a good sample, `S > 0`, `ψ` as in
`PsiGood` and every folded circle `fc(d, r)`, `r > 0`, for `fc`-a.e. `z`

  `avgReg y k (ψ z) = F(S ψ z, S 2^{-k}) + smoothFun (rp g) (S ψ z) (S 2^{-k}) + Q log S`.

Off the circle `‖w‖ = 2^{-k}` this is `G1RC.avgReg_rescale_wedge`. On that circle, the dyadic
approximants `c_n = dyadicRoundC n w = (a + b i)/2^n` still avoid the circle eventually unless
`w` lies on a coordinate axis: `‖c_n‖ = 2^{-k}` means `4^k (a² + b²) = 4^n`, which forces
`a = 0` or `b = 0` (squares are `0, 1 mod 4`; `int_four_pow_mul_sq_add_sq_ne`). In `H` the only
such point of the circle is `i 2^{-k}`, and `ψ_* fc` does not charge it (`ψ` is injective on `H`,
folded circles have no atoms). At the other points the raw values converge by continuity of `F`
and of the smoothed profile in the centre (`F1.RC3Two.continuous_smoothFun_rp`).

Own elementary argument (circle-average bookkeeping and a parity argument); no published
source needed (cost rule of AGENT_GUIDE.md).
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open F1.RC3Two WedgeTK CircleFubini

/-- A folded circle of positive radius has no atoms (as `G4TraceNull.foldedCircle_singleton`). -/
theorem foldedCircle_singleton_restAvg (y p : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    foldedCircle y ρ {p} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun e he _ => ?_) bot_le
  have ht : (0 : ℝ) ≤ (e : ℝ) * ρ / 6 := by positivity
  calc foldedCircle y ρ {p} ≤ foldedCircle y ρ (closedBall p ((e : ℝ) * ρ / 6)) :=
        measure_mono (by simpa using ht)
    _ ≤ ENNReal.ofReal (6 * ((e : ℝ) * ρ / 6) / ρ) :=
        RegCont.foldedCircle_closedBall_le_arc y p hρ ht
    _ = (e : ℝ≥0∞) := by
        rw [show 6 * ((e : ℝ) * ρ / 6) / ρ = (e : ℝ) by field_simp, ENNReal.ofReal_coe_nnreal]
    _ ≤ 0 + (e : ℝ≥0∞) := by rw [zero_add]

/-- If `4 ∣ a² + b²` then `a` and `b` are even. -/
theorem int_even_of_four_dvd_sq_add_sq {a b : ℤ} (h : 4 ∣ a ^ 2 + b ^ 2) :
    2 ∣ a ∧ 2 ∣ b := by
  have h0 : (a ^ 2 + b ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  have ha : a ^ 2 % 4 = (a % 4) * (a % 4) % 4 := by rw [pow_two, Int.mul_emod]
  have hb : b ^ 2 % 4 = (b % 4) * (b % 4) % 4 := by rw [pow_two, Int.mul_emod]
  have hab : (a ^ 2 + b ^ 2) % 4 = (a ^ 2 % 4 + b ^ 2 % 4) % 4 := Int.add_emod _ _ _
  generalize a ^ 2 = A at *
  generalize b ^ 2 = B at *
  have ra : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have rb : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
  rcases ra with ra | ra | ra | ra <;> rcases rb with rb | rb | rb | rb <;>
    rw [ra] at ha <;> rw [rb] at hb <;> norm_num at ha hb <;> omega

/-- `4^k (a² + b²) ≠ 4^n` for nonzero integers `a, b`. -/
theorem int_four_pow_mul_sq_add_sq_ne (n : ℕ) :
    ∀ (a b : ℤ) (k : ℕ), a ≠ 0 → b ≠ 0 → (4 : ℤ) ^ k * (a ^ 2 + b ^ 2) ≠ 4 ^ n := by
  induction n with
  | zero =>
    intro a b k ha hb h
    have h1 : 0 < a ^ 2 := by positivity
    have h2 : 0 < b ^ 2 := by positivity
    have h3 : (1 : ℤ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    rw [pow_zero] at h
    nlinarith
  | succ n ih =>
    intro a b k ha hb h
    cases k with
    | zero =>
      rw [pow_zero, one_mul] at h
      have hd : (4 : ℤ) ∣ a ^ 2 + b ^ 2 := h ▸ dvd_pow_self 4 (Nat.succ_ne_zero n)
      obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := int_even_of_four_dvd_sq_add_sq hd
      refine ih a' b' 0 (by rintro rfl; simp at ha) (by rintro rfl; simp at hb) ?_
      have e : (2 * a') ^ 2 + (2 * b') ^ 2 = 4 * (a' ^ 2 + b' ^ 2) := by ring
      rw [e] at h
      have h' : 4 * (a' ^ 2 + b' ^ 2) = 4 * 4 ^ n := by rw [h, pow_succ, mul_comm]
      rw [pow_zero, one_mul]
      exact (mul_right_inj' (by norm_num : (4 : ℤ) ≠ 0)).1 h'
    | succ k =>
      refine ih a b k ha hb ?_
      have e : (4 : ℤ) ^ k * (a ^ 2 + b ^ 2) * 4 = 4 ^ n * 4 := by
        rw [← pow_succ, ← h, pow_succ]; ring
      exact mul_right_cancel₀ (by norm_num) e

/-- A dyadic point off both coordinate axes is not on a dyadic circle through `0`. -/
theorem norm_dyadicRoundC_ne_radius {n k : ℕ} {w : ℂ} (hre : (dyadicRoundC n w).re ≠ 0)
    (him : (dyadicRoundC n w).im ≠ 0) : ‖dyadicRoundC n w‖ ≠ radius k := by
  intro h
  set a : ℤ := ⌊(2 : ℝ) ^ n * w.re⌋ with ha_def
  set b : ℤ := ⌊(2 : ℝ) ^ n * w.im⌋ with hb_def
  have hre' : (dyadicRoundC n w).re = a / 2 ^ n := rfl
  have him' : (dyadicRoundC n w).im = b / 2 ^ n := rfl
  have ha : a ≠ 0 := by intro h0; apply hre; rw [hre', h0]; simp
  have hb : b ≠ 0 := by intro h0; apply him; rw [him', h0]; simp
  refine int_four_pow_mul_sq_add_sq_ne n a b k ha hb ?_
  have hsq : ‖dyadicRoundC n w‖ ^ 2 = radius k ^ 2 := by rw [h]
  rw [Complex.sq_norm, Complex.normSq_apply, hre', him'] at hsq
  have e1 : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = ((2 : ℝ) ^ n) ^ 2 * radius k ^ 2 := by
    rw [← hsq]; field_simp
  have e2 : (4 : ℝ) ^ k * radius k ^ 2 = 1 := by
    rw [radius, ← pow_mul, mul_comm k 2, pow_mul, ← mul_pow]
    norm_num
  have e3 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have : (4 : ℝ) ^ k * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) = 4 ^ n := by
    rw [e3, e1]; linear_combination ((2 : ℝ) ^ n) ^ 2 * e2
  exact_mod_cast this

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}

/-- The regularized average of the rescaled wedge field, when the dyadic approximants of `w`
eventually avoid the circle `‖·‖ = 2^{-k}`. -/
theorem avgReg_rescale_wedge_of_ev (h : WedgeGood x F A) (Q C : ℝ)
    (hbd : ∀ t, 0 < t → t ≤ 1 → |wg x A Q t| ≤ C * (1 - Real.log t)) {S : ℝ} (hS : 0 < S)
    {k : ℕ} {w : ℂ} (hw : w ∈ Hbar) (hev : ∀ᶠ n in atTop, ‖dyadicRoundC n w‖ ≠ radius k) :
    avgReg (rescale (wedgeField (lateralPart x) A Q) Q S) k w =
      F ((S : ℂ) * w, S * radius k) +
        GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * w) (S * radius k) +
        Q * Real.log S := by
  have hSρ : 0 < S * radius k := mul_pos hS (radius_pos k)
  have hc := RegClosure.tendsto_dyadicRoundC w
  unfold avgReg
  refine Tendsto.limUnder_eq ?_
  have hcongr : (fun n => F (foldH ((S : ℂ) * dyadicRoundC n w), S * radius k) +
      GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * dyadicRoundC n w) (S * radius k) +
      Q * Real.log S) =ᶠ[atTop]
      fun n => rescale (wedgeField (lateralPart x) A Q) Q S
        (foldedCircle (dyadicRoundC n w) (radius k)) := by
    filter_upwards [hev] with n hn
    rw [rescale_wedge_fc_eq h Q hS _ (radius_pos k) hn]
    rfl
  refine Tendsto.congr' hcongr ?_
  have hSw : (S : ℂ) * w ∈ Hbar := by
    show 0 ≤ ((S : ℂ) * w).im
    rw [Complex.im_ofReal_mul]; exact mul_nonneg hS.le hw
  have hmul : Tendsto (fun n => (S : ℂ) * dyadicRoundC n w) atTop (𝓝 ((S : ℂ) * w)) :=
    hc.const_mul _
  have h1 : Tendsto (fun n => F (foldH ((S : ℂ) * dyadicRoundC n w), S * radius k)) atTop
      (𝓝 (F ((S : ℂ) * w, S * radius k))) := by
    have hin : Tendsto (fun n => (foldH ((S : ℂ) * dyadicRoundC n w), S * radius k)) atTop
        (𝓝[Hbar ×ˢ Ioi 0] ((S : ℂ) * w, S * radius k)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        mk_mem_prod (foldH_mem_Hbar' _) (show S * radius k ∈ Ioi 0 from hSρ)⟩
      have := ((continuous_foldH'.tendsto _).comp hmul).prodMk_nhds
        (tendsto_const_nhds (x := S * radius k))
      rwa [foldH_of_mem' hSw] at this
    exact (h.good.1.1 ((S : ℂ) * w, S * radius k)
      (mk_mem_prod hSw (show S * radius k ∈ Ioi 0 from hSρ))).tendsto.comp hin
  have h2 : Tendsto (fun n => GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * dyadicRoundC n w)
      (S * radius k)) atTop
      (𝓝 (GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * w) (S * radius k))) :=
    ((continuous_smoothFun_rp (measurable_wg h.cont) (continuousOn_wg h.good h.cont) hbd
      hSρ).tendsto _).comp hmul
  exact (h1.add h2).add tendsto_const_nhds

/-- **`AvgRegPsiStmt` holds.** -/
theorem avgRegPsiStmt_holds : AvgRegPsiStmt := by
  intro x F A h Q C hbd S hS ψ hψ d r hr k
  have hsing : ∀ᵐ z ∂foldedCircle d r, z ∈ H → ψ z ≠ Complex.I * (radius k : ℂ) := by
    by_cases hp : ∃ p ∈ H, ψ p = Complex.I * (radius k : ℂ)
    · obtain ⟨p, hpH, hpψ⟩ := hp
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (foldedCircle_singleton_restAvg d p hr)]
        with z hz hzH hzψ
      exact hz (hψ.2.2.1 hzH hpH (hzψ.trans hpψ.symm))
    · push Not at hp
      exact Eventually.of_forall fun z hz => hp z hz
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr, hsing] with z hzH hz
  have hwH : ψ z ∈ H := hψ.2.2.2.1 hzH
  have hwH' : 0 < (ψ z).im := hwH
  have hwHb : ψ z ∈ Hbar := show 0 ≤ (ψ z).im from hwH'.le
  by_cases hn : ‖ψ z‖ = radius k
  · refine avgReg_rescale_wedge_of_ev h Q C hbd hS hwHb ?_
    have hre : (ψ z).re ≠ 0 := by
      intro h0
      apply hz hzH
      apply Complex.ext
      · rw [h0]; simp
      · have e := Complex.sq_norm_sub_sq_re (ψ z)
        rw [hn, h0] at e
        have hρ := radius_pos k
        simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, one_mul, zero_add]
        nlinarith
    have hre_ev : ∀ᶠ n in atTop, (dyadicRoundC n (ψ z)).re ≠ 0 :=
      ((Complex.continuous_re.tendsto _).comp
        (RegClosure.tendsto_dyadicRoundC (ψ z))).eventually_ne hre
    have him_ev : ∀ᶠ n in atTop, (dyadicRoundC n (ψ z)).im ≠ 0 :=
      ((Complex.continuous_im.tendsto _).comp
        (RegClosure.tendsto_dyadicRoundC (ψ z))).eventually_ne hwH'.ne'
    filter_upwards [hre_ev, him_ev] with n h1 h2 using norm_dyadicRoundC_ne_radius h1 h2
  · exact avgReg_rescale_wedge h Q hS hwHb hn

end G1RC
end Thm18Asm
end QuantumZipper
