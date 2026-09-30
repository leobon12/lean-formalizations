import QuantumZipper.Proofs.Zipper.CfgFMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE: Hölder-`1/3` displacement of the unzipping maps in time (`TDisp`)

`‖ψ_{t+h}(u) − ψ_t(u)‖ ≤ (ε + 2h/Im u) e^{2t/(Im u)²}` with `ε` the oscillation of the driver on
`[t, t+h]` (`RegCont.norm_fwdMapInv_add_sub_le`); for a `1/3`-Hölder driver `ε ≤ C h^{1/3}` and
`h ≤ h^{1/3} (1 + T)`, which gives `TDisp` (`CfgFM.tDisp_of_holder`), in particular for the
drivers `Wof κ T f` of good paths (`CfgFM.tDisp_of_good`). Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set

namespace QuantumZipper.E6
namespace CfgFM

open RegCont CharFun

variable {W : ℝ → ℝ}

theorem rpow_two_thirds_le {h : ℝ} (hh : 0 ≤ h) : h ^ ((2 : ℝ) / 3) ≤ 1 + h := by
  rcases le_total h 1 with h1 | h1
  · have := Real.rpow_le_one hh h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num : (2 : ℝ) / 3 ≤ 1)
    rw [Real.rpow_one] at this
    linarith

theorem self_le_rpow_third_mul {h : ℝ} (hh : 0 ≤ h) : h ≤ h ^ ((1 : ℝ) / 3) * (1 + h) := by
  have e : h = h ^ ((1 : ℝ) / 3) * h ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add' hh (by norm_num)]; norm_num
  calc h = h ^ ((1 : ℝ) / 3) * h ^ ((2 : ℝ) / 3) := e
    _ ≤ h ^ ((1 : ℝ) / 3) * (1 + h) :=
      mul_le_mul_of_nonneg_left (rpow_two_thirds_le hh) (Real.rpow_nonneg hh _)

/-- One-sided displacement bound. -/
theorem disp_le (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} {CH M : ℝ} (hCH : 0 ≤ CH)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ ((1 : ℝ) / 3))
    {i : ℝ} (hi : 0 < i) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (ht' : t' ∈ Icc (0 : ℝ) T)
    (htt : t ≤ t') {x : ℂ} (hx : i ≤ x.im) :
    ‖tpsi W t' x - tpsi W t x‖ ≤
      ((CH + 4 * M) + 2 * (1 + T) / i) * Real.exp (2 / i ^ 2 * T) *
        |t' - t| ^ ((1 : ℝ) / 3) := by
  have hxH : x ∈ H := show 0 < x.im by linarith
  set h := t' - t with hhdef
  have hh : 0 ≤ h := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t ht)
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hhT : h ≤ T := by linarith [ht.1, ht'.2]
  have hc : 0 ≤ h ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hh _
  have hε : ∀ q ∈ Icc (0 : ℝ) h, |W (t + h - q) - W (t + h)| ≤ (CH + 4 * M) * h ^ ((1 : ℝ) / 3) := by
    intro q hq
    have e : t + h = t' := by rw [hhdef]; ring
    rw [e]
    have hq1 : t' - q ∈ Icc (0 : ℝ) T := ⟨by linarith [hq.2, ht.1], by linarith [hq.1, ht'.2]⟩
    rcases le_total q (1 / 2) with hq2 | hq2
    · have hq3 : |t' - q - t'| ≤ 1 / 2 := by
        rw [show t' - q - t' = -q by ring, abs_neg, abs_of_nonneg hq.1]; exact hq2
      have := hH _ hq1 _ ht' hq3
      rw [show t' - q - t' = -q by ring, abs_neg, abs_of_nonneg hq.1] at this
      have hqh : q ^ ((1 : ℝ) / 3) ≤ h ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow hq.1 hq.2 (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hqh hCH]
    · have h1 : |W (t' - q) - W t'| ≤ 2 * M := by
        have a := abs_sub (W (t' - q)) (W t')
        linarith [hM _ hq1, hM _ ht']
      have h2 : 1 ≤ 2 * h ^ ((1 : ℝ) / 3) := by
        have : (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) ≤ h ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by norm_num) (hq2.trans hq.2) (by norm_num)
        have h3 : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ ((1 : ℝ) / 3) :=
          Real.self_le_rpow_of_le_one (by norm_num) (by norm_num) (by norm_num)
        linarith
      nlinarith
  have hd := norm_fwdMapInv_add_sub_le hW hW0 ht.1 hh hε hxH
  have e2 : t + h = t' := by rw [hhdef]; ring
  rw [e2] at hd
  rw [tpsi_eq hW hW0 ht'.1 hxH, tpsi_eq hW hW0 ht.1 hxH, abs_of_nonneg hh]
  refine hd.trans ?_
  have hxi : 0 < x.im := hxH
  have hA : 2 * h / x.im ≤ 2 * (1 + T) / i * h ^ ((1 : ℝ) / 3) := by
    have k1 : 2 * h / x.im ≤ 2 * h / i := div_le_div_of_nonneg_left (by positivity) hi hx
    have k2 : h ≤ h ^ ((1 : ℝ) / 3) * (1 + T) :=
      (self_le_rpow_third_mul hh).trans (mul_le_mul_of_nonneg_left (by linarith) hc)
    have k3 : 2 * h / i ≤ 2 * (h ^ ((1 : ℝ) / 3) * (1 + T)) / i :=
      div_le_div_of_nonneg_right (by linarith) hi.le
    calc 2 * h / x.im ≤ 2 * (h ^ ((1 : ℝ) / 3) * (1 + T)) / i := k1.trans k3
      _ = 2 * (1 + T) / i * h ^ ((1 : ℝ) / 3) := by ring
  have hB : Real.exp (2 / x.im ^ 2 * t) ≤ Real.exp (2 / i ^ 2 * T) := by
    apply Real.exp_le_exp.2
    have k1 : 2 / x.im ^ 2 ≤ 2 / i ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hi.le hx 2)
    exact mul_le_mul k1 ht.2 ht.1 (by positivity)
  calc ((CH + 4 * M) * h ^ ((1 : ℝ) / 3) + 2 * h / x.im) * Real.exp (2 / x.im ^ 2 * t)
      ≤ ((CH + 4 * M) * h ^ ((1 : ℝ) / 3) + 2 * (1 + T) / i * h ^ ((1 : ℝ) / 3)) *
          Real.exp (2 / i ^ 2 * T) :=
        mul_le_mul (by linarith) hB (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- **`TDisp` for a `1/3`-Hölder driver.** -/
theorem tDisp_of_holder (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} {CH : ℝ} (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ ((1 : ℝ) / 3)) : TDisp W T := by
  intro m
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set i : ℝ := 1 / (2 * ((m : ℝ) + 1)) with hidef
  have hi : 0 < i := by positivity
  have hM0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ M := fun t ht => (abs_nonneg _).trans (hM t ht)
  refine ⟨|((CH + 4 * |M|) + 2 * (1 + |T|) / i) * Real.exp (2 / i ^ 2 * |T|)|, abs_nonneg _,
    fun t ht t' ht' x _ hx => ?_⟩
  have hM' : ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ |M| := fun s hs => (hM s hs).trans (le_abs_self _)
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  have key : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) T → b ∈ Icc (0 : ℝ) T → a ≤ b →
      ‖tpsi W b x - tpsi W a x‖ ≤
        |((CH + 4 * |M|) + 2 * (1 + |T|) / i) * Real.exp (2 / i ^ 2 * |T|)| *
          |b - a| ^ ((1 : ℝ) / 3) := by
    intro a b ha hb hab
    have := disp_le hW hW0 hCH hM' hH hi ha hb hab hx
    rw [abs_of_nonneg hT0] at *
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (abs_nonneg _) _))
  rcases le_total t t' with h1 | h1
  · rw [norm_sub_rev, abs_sub_comm]; exact key t t' ht ht' h1
  · exact key t' t ht' ht h1

/-- **`TDisp` for the drivers of good paths.** -/
theorem tDisp_of_good (κ : ℝ) {T : ℝ} (hT : 0 < T) {f : C(Icc (0 : ℝ) T, ℝ)}
    (hf : f ∈ GoodP hT.le (1 / 3)) : TDisp (Wof κ T hT.le f) T := by
  obtain ⟨C, hC⟩ := hf.2
  exact tDisp_of_holder (continuous_Wof κ T hT.le f) (Wof_zero_of_GoodP hT.le κ hf)
    (by positivity) (Wof_holder hT.le κ hC)

end CfgFM
end QuantumZipper.E6
