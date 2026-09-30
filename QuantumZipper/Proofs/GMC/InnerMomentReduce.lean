import QuantumZipper.Proofs.GMC.BdryMomentsScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GMC-INNERMOM: the uniform `q`-th moment of the inner masses (`1 < q ≤ 2`, `q < 4/γ²`),
# reduced to a Palm (rooted-measure) inequality and a sub-window fractional moment bound

Target: `InnerMomentStmt γ q` (`BdryMomentsScale`), i.e. `E[W^q] ≤ A δ^q` uniformly in
`t, δ, k` (`2·2^{-k} < δ`), where `W = innerMass γ X t δ k` is the total mass of the random
measure `W(du) = (2^{-k}/δ)^{γ²/4} e^{(γ/2) Y_k(u)} du` on `S = [t − δ/2, t + δ/2]`
(`innerMeasure`, `Y = X − X(fc(t,δ))` the inner field).

Route (the "rooted measure" / Girsanov argument for positive moments of GMC; Kahane 1985;
Rhodes–Vargas, *Gaussian multiplicative chaos and applications: a review*, arXiv:1305.6221,
§2.3 (existence of moments); Berestycki–Powell, *Gaussian free field and Liouville quantum
gravity*, arXiv:2004.04720, ch. 3 (Girsanov/rooted measure); the route was fixed in the
`BdryMomentsScale` docstring):

1. **Palm inequality** (`PalmRootedStmt`, open input). Write `E W^q = E[W · W^{q−1}]` and apply
   Cameron–Martin at level `k` to the density `e^{(γ/2) Y_k(x)}` (`PalmFormula.palm_levelK`):
   the field is shifted by `(γ/2) Cov(Y_k(x), Y_k(·))`, and the exact kernel identities
   (`kernelCov_fc_real_*`: `Var Y_k(x) = 2 log(δ/2^{-k})`, `Cov(Y_k(x), Y_k(u)) ≤
   2 log(δ / max(|x−u|, 2^{-k})) + 2 log 2`) give
   `E W^q ≤ C₁ ∫_S E[(∫ (δ/max(|x−u|, 2·2^{-k}))^{γ²/2} W(du))^{q−1}] dx`.
2. **Sub-window fractional moments** (`SubFracStmt`, open input). For `p ∈ (0,1]` and an interval
   `J` of length `ℓ ∈ (2·2^{-k}, δ]`: `E W(J)^p ≤ C₂ (ℓ/δ)^{ζ(p)} δ^p`,
   `ζ(p) = p(1+γ²/4) − p²γ²/4` (the inner field on the sub-window is a Gaussian constant of
   variance `2 log(δ/ℓ)`, independent of the sub-window's inner field, plus Jensen — the same
   argument as `FracMom.fracMoment_dyadic`).
3. **Bookkeeping (proved here).** Dyadic annuli around `x`: `palmKer_le` bounds the kernel by
   `4^{γ²/2}(1 + Σ_j 2^{jγ²/2} 1_{B_j})`, `B_j` the interval of length `δ 2^{-j}` around `x`;
   subadditivity of `y ↦ y^p` (`p = q − 1 ≤ 1`) and step 2 give a geometric series with ratio
   `2^{-(ζ(p) − pγ²/2)} = 2^{-p(1 − qγ²/4)} < 1` exactly when `q < 4/γ²`
   (`lintegral_palmKer_rpow_le`, `innerMomentBound_of_palm_subFrac`,
   `innerMomentStmt_of_palm_subFrac`).

The annulus bookkeeping is an own elementary write-up of the standard computation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace GMCMoments

open FracMom BdryExist

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The rescaled inner random measure `W(du) = (2^{-k}/δ)^{γ²/4} e^{(γ/2) Y_k(u)} du` on
`S = bI t δ`; its total mass is `innerMass γ X t δ k ω`. -/
def innerMeasure (γ : ℝ) (X : Ω → FieldSample) (t δ : ℝ) (k : ℕ) (ω : Ω) : Measure ℝ :=
  (volume.restrict (bI t δ)).withDensity fun s =>
    ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) s)

theorem innerMeasure_univ (γ : ℝ) (X : Ω → FieldSample) (t δ : ℝ) (k : ℕ) (ω : Ω) :
    innerMeasure γ X t δ k ω univ = innerMass γ X t δ k ω := by
  rw [innerMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rfl

theorem innerMeasure_bI (γ : ℝ) (X : Ω → FieldSample) (t δ : ℝ) (k : ℕ) (ω : Ω) :
    innerMeasure γ X t δ k ω (bI t δ) = innerMass γ X t δ k ω := by
  rw [innerMeasure, withDensity_apply _ (measurableSet_bI t δ), Measure.restrict_restrict
    (measurableSet_bI t δ), inter_self]
  rfl

theorem measurable_innerMeasure_apply (hX : IsFreeGFFModConstH X P) (γ t δ : ℝ) (k : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable fun ω => innerMeasure γ X t δ k ω B := by
  have e : (fun ω => innerMeasure γ X t δ k ω B) = fun ω =>
      ∫⁻ s, ENNReal.ofReal (wDens γ δ k (innerSample X t δ ω) s) ∂(volume.restrict (B ∩ bI t δ)) := by
    funext ω
    rw [innerMeasure, withDensity_apply _ hB, Measure.restrict_restrict hB]
  rw [e]
  exact ((ENNReal.measurable_ofReal.comp (measurable_wDens₂ γ δ k)).lintegral_prod_right'
    (ν := volume.restrict (B ∩ bI t δ))).comp (measurable_innerSample hX t δ)

/-- The Palm kernel `(δ / max(|x − u|, 2·2^{-k}))^{γ²/2}`. -/
def palmKer (γ δ : ℝ) (k : ℕ) (x u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((δ / max |x - u| (2 * radius k)) ^ (γ ^ 2 / 2))

/-- The boundary multifractal exponent `ζ(p) = p(1 + γ²/4) − p²γ²/4`. -/
def zeta (γ p : ℝ) : ℝ := p * (1 + γ ^ 2 / 4) - p ^ 2 * γ ^ 2 / 4

/-- **Open input 1 (Palm / rooted-measure inequality).** -/
def PalmRootedBound (γ q : ℝ) (X : Ω → FieldSample) (P : Measure Ω) (C : ℝ≥0∞) : Prop :=
  ∀ (t δ : ℝ) (k : ℕ), 0 < δ → 2 * radius k < δ →
    ∫⁻ ω, innerMass γ X t δ k ω ^ q ∂P ≤
      C * ∫⁻ x in bI t δ, ∫⁻ ω, (∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω) ^ (q - 1) ∂P

/-- Law-level form of `PalmRootedBound`. -/
def PalmRootedStmt (γ q : ℝ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → PalmRootedBound γ q X P C

/-- **Open input 2 (sub-window fractional moments).** -/
def SubFracBound (γ p : ℝ) (X : Ω → FieldSample) (P : Measure Ω) (C : ℝ≥0∞) : Prop :=
  ∀ (t δ : ℝ) (k : ℕ) (a ℓ : ℝ), 0 < δ → 2 * radius k < δ → 2 * radius k < ℓ → ℓ ≤ δ →
    ∫⁻ ω, innerMeasure γ X t δ k ω (Icc (a - ℓ / 2) (a + ℓ / 2)) ^ p ∂P ≤
      C * ENNReal.ofReal ((ℓ / δ) ^ zeta γ p) * ENNReal.ofReal δ ^ p

/-- Law-level form of `SubFracBound`. -/
def SubFracStmt (γ p : ℝ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → SubFracBound γ p X P C

/-! ### Dyadic annuli -/

/-- Weight of the `j`-th ball: `2^{ja}` if its length `δ 2^{-j}` exceeds `2·2^{-k}`. -/
def annW (δ : ℝ) (k j : ℕ) (a : ℝ) : ℝ≥0∞ :=
  if 2 * radius k < δ * radius j then ENNReal.ofReal ((radius j)⁻¹ ^ a) else 0

/-- The `j`-th ball around `x`: the interval of length `δ 2^{-j}` centred at `x`. -/
def annB (x δ : ℝ) (j : ℕ) : Set ℝ := Icc (x - δ * radius j / 2) (x + δ * radius j / 2)

theorem palmKer_le (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (x u : ℝ) :
    palmKer γ δ k x u ≤ ENNReal.ofReal (4 ^ (γ ^ 2 / 2)) *
      (1 + ∑' j, annW δ k j (γ ^ 2 / 2) * (annB x δ j).indicator 1 u) := by
  set a := γ ^ 2 / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  set d := max |x - u| (2 * radius k) with hd
  have hr := radius_pos k
  have hd2 : 2 * radius k ≤ d := le_max_right _ _
  have hdu : |x - u| ≤ d := le_max_left _ _
  have hd0 : 0 < d := lt_of_lt_of_le (by linarith) hd2
  by_cases hsmall : δ < 4 * d
  · calc palmKer γ δ k x u ≤ ENNReal.ofReal (4 ^ a) := by
          apply ENNReal.ofReal_le_ofReal
          apply rpow_le_rpow (div_pos hδ hd0).le _ ha0
          rw [div_le_iff₀ hd0]; linarith
      _ ≤ _ := by
          conv_lhs => rw [← mul_one (ENNReal.ofReal (4 ^ a))]
          gcongr
          exact le_self_add
  · push_neg at hsmall
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := δ / (4 * d)) (y := (2 : ℝ))
      (by rw [le_div_iff₀ (by positivity)]; linarith) one_lt_two
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    rw [le_div_iff₀ (by positivity)] at hn1
    rw [div_lt_iff₀ (by positivity), pow_succ] at hn2
    have hrj : radius (n + 1) = (2 ^ n * 2)⁻¹ := by
      simp only [radius, inv_pow, pow_succ, mul_inv]
    have hℓ1 : 2 * d ≤ δ * radius (n + 1) := by
      rw [hrj, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]; nlinarith
    have hℓ2 : δ * radius (n + 1) < 4 * d := by
      rw [hrj, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]; nlinarith
    have hrj0 : 0 < radius (n + 1) := radius_pos _
    have hW : annW δ k (n + 1) a = ENNReal.ofReal ((radius (n + 1))⁻¹ ^ a) := by
      rw [annW, if_pos (show 2 * radius k < δ * radius (n + 1) by linarith)]
    have hu : u ∈ annB x δ (n + 1) := by
      have h := abs_le.1 (show |x - u| ≤ δ * radius (n + 1) / 2 by linarith)
      rw [annB, mem_Icc]
      constructor <;> linarith [h.1, h.2]
    have hk : palmKer γ δ k x u ≤
        ENNReal.ofReal (4 ^ a) * ENNReal.ofReal ((radius (n + 1))⁻¹ ^ a) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_rpow (by norm_num) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      apply rpow_le_rpow (div_pos hδ hd0).le _ ha0
      rw [div_le_iff₀ hd0, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hrj0]
      nlinarith
    refine hk.trans ?_
    gcongr
    refine le_trans ?_ le_add_self
    refine le_trans ?_ (ENNReal.le_tsum (n + 1))
    rw [hW, indicator_of_mem hu, Pi.one_apply, mul_one]

theorem measurableSet_annB (x δ : ℝ) (j : ℕ) : MeasurableSet (annB x δ j) := measurableSet_Icc

theorem radius_le_one_im (j : ℕ) : radius j ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

/-! ### The annulus sum in expectation -/

/-- Ratio `2^{-(ζ(p) − pγ²/2)}` of the geometric series. -/
def annRatio (γ p : ℝ) : ℝ≥0∞ := ENNReal.ofReal (2⁻¹ ^ (zeta γ p - γ ^ 2 / 2 * p))

theorem annW_rpow_mul_le (γ : ℝ) {p δ : ℝ} (hp0 : 0 < p) (hδ : 0 < δ) (k j : ℕ) :
    annW δ k j (γ ^ 2 / 2) ^ p * ENNReal.ofReal ((δ * radius j / δ) ^ zeta γ p) ≤
      annRatio γ p ^ j := by
  unfold annW
  split_ifs with h
  · have hr := radius_pos j
    have h0 : 0 ≤ (radius j)⁻¹ ^ (γ ^ 2 / 2) := rpow_nonneg (inv_nonneg.2 hr.le) _
    rw [mul_div_cancel_left₀ _ hδ.ne', ENNReal.ofReal_rpow_of_nonneg h0 hp0.le,
      ← ENNReal.ofReal_mul (rpow_nonneg h0 _), annRatio,
      ← ENNReal.ofReal_pow (rpow_nonneg (by norm_num) _)]
    apply le_of_eq
    congr 1
    rw [← rpow_mul (inv_nonneg.2 hr.le), inv_rpow hr.le, ← rpow_neg hr.le, ← rpow_add hr,
      radius, ← rpow_pow_comm (by norm_num),
      show -(γ ^ 2 / 2 * p) + zeta γ p = zeta γ p - γ ^ 2 / 2 * p by ring]
  · rw [ENNReal.zero_rpow_of_pos hp0, zero_mul]
    exact zero_le

/-- **Annulus bookkeeping.** From the sub-window bound (`p ∈ (0,1]`), the `p`-th moment of the
Palm-weighted mass around any `x` is at most `4^{pγ²/2} C δ^p (1 + Σ_j θ^j)`. -/
theorem lintegral_palmKer_rpow_le (hX : IsFreeGFFModConstH X P)
    {γ p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {C : ℝ≥0∞} (hH : SubFracBound γ p X P C)
    {t δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 2 * radius k < δ) (x : ℝ) :
    ∫⁻ ω, (∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω) ^ p ∂P ≤
      ENNReal.ofReal (4 ^ (γ ^ 2 / 2)) ^ p * (C * ENNReal.ofReal δ ^ p) *
        (1 + ∑' j, annRatio γ p ^ j) := by
  set c4 := ENNReal.ofReal (4 ^ (γ ^ 2 / 2)) with hc4
  set M : Ω → ℝ≥0∞ := fun ω => innerMeasure γ X t δ k ω univ with hM
  set Mj : ℕ → Ω → ℝ≥0∞ := fun j ω => innerMeasure γ X t δ k ω (annB x δ j) with hMj
  have hpt : ∀ ω, (∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω) ^ p ≤
      c4 ^ p * (M ω ^ p + ∑' j, annW δ k j (γ ^ 2 / 2) ^ p * Mj j ω ^ p) := by
    intro ω
    have h1 : ∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω ≤
        c4 * (M ω + ∑' j, annW δ k j (γ ^ 2 / 2) * Mj j ω) := by
      calc _ ≤ ∫⁻ u, c4 * (1 + ∑' j, annW δ k j (γ ^ 2 / 2) * (annB x δ j).indicator 1 u)
              ∂innerMeasure γ X t δ k ω := lintegral_mono fun u => palmKer_le γ hδ k x u
        _ = _ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_add_left measurable_const, lintegral_one,
              lintegral_tsum fun j =>
                ((measurable_one.indicator (measurableSet_annB x δ j)).const_mul _).aemeasurable]
            congr 2
            refine tsum_congr fun j => ?_
            rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_annB x δ j)),
              lintegral_indicator_one (measurableSet_annB x δ j)]
    calc _ ≤ (c4 * (M ω + ∑' j, annW δ k j (γ ^ 2 / 2) * Mj j ω)) ^ p :=
          ENNReal.rpow_le_rpow h1 hp0.le
      _ = c4 ^ p * (M ω + ∑' j, annW δ k j (γ ^ 2 / 2) * Mj j ω) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ c4 ^ p * (M ω ^ p + (∑' j, annW δ k j (γ ^ 2 / 2) * Mj j ω) ^ p) :=
          mul_le_mul_right (ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1) _
      _ ≤ _ := by
          refine mul_le_mul_right (add_le_add le_rfl ?_) _
          refine (rpow_tsum_le_tsum_rpow _ hp0 hp1).trans (le_of_eq (tsum_congr fun j => ?_))
          exact ENNReal.mul_rpow_of_nonneg _ _ hp0.le
  have hMm : Measurable M := measurable_innerMeasure_apply hX γ t δ k MeasurableSet.univ
  have hMjm : ∀ j, Measurable (Mj j) := fun j =>
    measurable_innerMeasure_apply hX γ t δ k (measurableSet_annB x δ j)
  have hS : ∫⁻ ω, M ω ^ p ∂P ≤ C * ENNReal.ofReal δ ^ p := by
    have hb := hH t δ k t δ hδ hk hk le_rfl
    rw [div_self hδ.ne', one_rpow, ENNReal.ofReal_one, mul_one] at hb
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hb
    simp only [hM]
    rw [innerMeasure_univ, ← innerMeasure_bI]
    rfl
  have hj : ∀ j, annW δ k j (γ ^ 2 / 2) ^ p * ∫⁻ ω, Mj j ω ^ p ∂P ≤
      C * ENNReal.ofReal δ ^ p * annRatio γ p ^ j := by
    intro j
    by_cases h : 2 * radius k < δ * radius j
    · have hb := hH t δ k x (δ * radius j) hδ hk h
        (mul_le_of_le_one_right hδ.le (radius_le_one_im j))
      calc annW δ k j (γ ^ 2 / 2) ^ p * ∫⁻ ω, Mj j ω ^ p ∂P
          ≤ annW δ k j (γ ^ 2 / 2) ^ p * (C * ENNReal.ofReal ((δ * radius j / δ) ^ zeta γ p) *
              ENNReal.ofReal δ ^ p) := mul_le_mul_right hb _
        _ = C * ENNReal.ofReal δ ^ p * (annW δ k j (γ ^ 2 / 2) ^ p *
              ENNReal.ofReal ((δ * radius j / δ) ^ zeta γ p)) := by ring
        _ ≤ _ := mul_le_mul_right (annW_rpow_mul_le γ hp0 hδ k j) _
    · rw [annW, if_neg h, ENNReal.zero_rpow_of_pos hp0, zero_mul]
      exact zero_le
  calc ∫⁻ ω, (∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω) ^ p ∂P
      ≤ ∫⁻ ω, c4 ^ p * (M ω ^ p + ∑' j, annW δ k j (γ ^ 2 / 2) ^ p * Mj j ω ^ p) ∂P :=
        lintegral_mono hpt
    _ = c4 ^ p * (∫⁻ ω, M ω ^ p ∂P +
          ∑' j, annW δ k j (γ ^ 2 / 2) ^ p * ∫⁻ ω, Mj j ω ^ p ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
          lintegral_add_left (hMm.pow_const p),
          lintegral_tsum fun j => (((hMjm j).pow_const p).const_mul _).aemeasurable]
        congr 2
        exact tsum_congr fun j => lintegral_const_mul _ ((hMjm j).pow_const p)
    _ ≤ c4 ^ p * (C * ENNReal.ofReal δ ^ p + ∑' j, C * ENNReal.ofReal δ ^ p * annRatio γ p ^ j) :=
        mul_le_mul_right (add_le_add hS (ENNReal.tsum_le_tsum hj)) _
    _ = _ := by rw [ENNReal.tsum_mul_left]; ring

theorem annRatio_lt_one {γ q : ℝ} (hγ : 0 < γ) (hq : 1 < q) (hqγ : q < 4 / γ ^ 2) :
    annRatio γ (q - 1) < 1 := by
  rw [annRatio, ENNReal.ofReal_lt_one]
  apply rpow_lt_one (by norm_num) (by norm_num)
  have h : q * γ ^ 2 < 4 := by rwa [lt_div_iff₀ (by positivity)] at hqγ
  unfold zeta
  nlinarith [mul_pos (sub_pos.2 hq) (sub_pos.2 h)]

/-- **Reduction (`1 < q ≤ 2`).** Palm inequality + sub-window fractional moments of order
`q − 1` give the uniform `q`-th moment of the inner masses. -/
theorem innerMomentBound_of_palm_subFrac (hX : IsFreeGFFModConstH X P)
    {γ q : ℝ} (hq : 1 < q) (hq2 : q ≤ 2) {C₁ C₂ : ℝ≥0∞}
    (h1 : PalmRootedBound γ q X P C₁) (h2 : SubFracBound γ (q - 1) X P C₂) :
    InnerMomentBound γ q X P (C₁ * (ENNReal.ofReal (4 ^ (γ ^ 2 / 2)) ^ (q - 1) * C₂ *
      (1 + ∑' j, annRatio γ (q - 1) ^ j))) := by
  intro t δ k hδ hk
  have hp0 : 0 < q - 1 := by linarith
  have hp1 : q - 1 ≤ 1 := by linarith
  refine (h1 t δ k hδ hk).trans ?_
  calc C₁ * ∫⁻ x in bI t δ, ∫⁻ ω, (∫⁻ u, palmKer γ δ k x u ∂innerMeasure γ X t δ k ω) ^ (q - 1) ∂P
      ≤ C₁ * ∫⁻ x in bI t δ, ENNReal.ofReal (4 ^ (γ ^ 2 / 2)) ^ (q - 1) *
          (C₂ * ENNReal.ofReal δ ^ (q - 1)) * (1 + ∑' j, annRatio γ (q - 1) ^ j) :=
        mul_le_mul_right (lintegral_mono fun x => lintegral_palmKer_rpow_le hX hp0 hp1 h2 hδ hk x) _
    _ = _ := by
        rw [setLIntegral_const, volume_bI hδ.le]
        have hq' : ENNReal.ofReal δ ^ q = ENNReal.ofReal δ ^ (q - 1) * ENNReal.ofReal δ := by
          conv_lhs => rw [show q = (q - 1) + 1 by ring]
          rw [ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 hδ).ne' ENNReal.ofReal_ne_top,
            ENNReal.rpow_one]
        rw [hq']
        ring

/-- **Law-level reduction.** For `0 < γ`, `1 < q ≤ 2`, `q < 4/γ²`:
`PalmRootedStmt γ q → SubFracStmt γ (q − 1) → InnerMomentStmt γ q`. -/
theorem innerMomentStmt_of_palm_subFrac {γ q : ℝ} (hγ : 0 < γ) (hq : 1 < q) (hq2 : q ≤ 2)
    (hqγ : q < 4 / γ ^ 2) (h1 : PalmRootedStmt γ q) (h2 : SubFracStmt γ (q - 1)) :
    InnerMomentStmt γ q := by
  obtain ⟨C₁, hC₁, hA1⟩ := h1
  obtain ⟨C₂, hC₂, hA2⟩ := h2
  refine ⟨C₁ * (ENNReal.ofReal (4 ^ (γ ^ 2 / 2)) ^ (q - 1) * C₂ *
    (1 + ∑' j, annRatio γ (q - 1) ^ j)), ?_, ?_⟩
  · have hr := annRatio_lt_one hγ hq hqγ
    rw [ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top hC₁ (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top) hC₂)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'⟩))
  · intro Ω _ P _ X hX
    exact innerMomentBound_of_palm_subFrac hX hq hq2 (hA1 P X hX) (hA2 P X hX)

end GMCMoments
end QuantumZipper
