import MatedCRTHarmonic.GMSMain.T13Layer
import MatedCRTHarmonic.GMSMain.T13Theorem14
import MatedCRTHarmonic.BundleSec4.MesoModelFinal
import MatedCRTHarmonic.GMSMain.EpsASource
import MatedCRTHarmonic.GMSMain.EpsALemma27

/-!
# Real meshes `ε ∈ (0, 1)`: asymptotics, admissibility, the rate helper and (1.8)

The [18] results are stated for every real `ε ∈ (0, 1)`. The real-mesh inputs hold
for the mated-CRT map `MatedCRT.graph ε (bm ω)` of every frozen coupling with the curve cells `η ω([ε(x−1), εx])`:
[18] Proposition 2.10 (`GMSMain.epsA_prop210Source`, bad event `GMSMain.EpsAProp210Bad`) and Lemma 2.7
(`GMSMain.epsA_lemma27Bad_coupling`, bad event `GMSMain.EpsALemma27Bad`). Both bad events are the failure of "an
embedding with the curve cells exists, and EVERY such embedding satisfies the bound". This file:

* `t13r_tendsto_rpow`, `t13r_tendsto_rpow_div_pow`, `t13r_tendsto_log_div_rpow`, **`t13r_tendsto_lemma34Bound_mul_log`**
  — the asymptotics of `T13Theorem14` along `ε → 0+` (`𝓝[>] 0`) instead of dyadic sequences;
* `t13r_threeAdmissible` — the three tests of Lemma 3.4 are admissible for Proposition 2.10 at a real mesh;
* **`t13r_rate_of_eventually`** — a failure bound `≤ K ε^α` for all small `ε`, uniform in a parameter, gives
  `≤ C ε^α` for every `ε ∈ (0, 1)` (coarse meshes absorbed into `C`);
* `T13RealGreenGood ε ρ A b c` — the event (1.8) for the mated-CRT map of `b` with the cells of `c`;
* **`t13r_green_of_inputs`** — (1.8) at every real mesh from the two named real-mesh inputs (Lemma 2.7 on `B_{ρ₁}`,
  Proposition 2.10 at `(ρ₁, 100, β_G)`) in their stated forms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic GMS3

/-! ### Asymptotics along `ε → 0+` -/

theorem t13r_tendsto_rpow {a : ℝ} (ha : 0 < a) : Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem t13r_tendsto_rpow_div_pow {a b : ℝ} {n : ℕ} (h : n * b < a) :
    Tendsto (fun ε : ℝ => ε ^ a / (ε ^ b) ^ n) (𝓝[>] 0) (𝓝 0) := by
  refine (t13r_tendsto_rpow (show 0 < a - b * n by linarith)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Real.rpow_sub hε, Real.rpow_mul_natCast (le_of_lt hε)]

theorem t13r_tendsto_log_div_rpow {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) :
    Tendsto (fun ε : ℝ => Real.log (ρ / ε ^ β)) (𝓝[>] 0) atTop := by
  have heq : (fun ε : ℝ => Real.log ρ + (-β) * Real.log ε) =ᶠ[𝓝[>] 0] fun ε => Real.log (ρ / ε ^ β) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.log_div hρ.ne' (Real.rpow_pos_of_pos hε β).ne', Real.log_rpow hε]
    ring
  exact (tendsto_atTop_add_const_left _ _
    (Tendsto.const_mul_atBot_of_neg (neg_neg_of_pos hβ) Real.tendsto_log_nhdsGT_zero)).congr' heq

/-- **The Lemma 3.4 error term is `≈ 6πA / log(ρ/ε^β)` as `ε → 0+`** (the real-mesh form of
`t13_tendsto_lemma34Bound_mul_log`). -/
theorem t13r_tendsto_lemma34Bound_mul_log {ρ β q β' α A : ℝ} (hρ : 0 < ρ) (hβ : 0 < β) (hq : 3 * β < q)
    (hβ' : 2 * β < β') (hα : 2 * β < α) :
    Tendsto (fun ε : ℝ => lemma34Bound (ε ^ β) ρ (ε ^ q) (ε ^ β') A (ε ^ α) * Real.log (ρ / ε ^ β))
      (𝓝[>] 0) (𝓝 (3 * A * (2 * π))) := by
  have hL := t13r_tendsto_log_div_rpow hρ hβ
  have hX : Tendsto (fun ε : ℝ => (Real.log (ρ / ε ^ β))⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have hα0 : 0 < α := by linarith
  have hlogmul : Tendsto (fun ε : ℝ => Real.log ε * ε ^ α) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero hα0
  have hη := t13r_tendsto_rpow hα0
  have hηL : Tendsto (fun ε : ℝ => ε ^ α * Real.log (ρ / ε ^ β)) (𝓝[>] 0) (𝓝 0) := by
    have heq : (fun ε : ℝ => Real.log ρ * ε ^ α + (-β) * (Real.log ε * ε ^ α)) =ᶠ[𝓝[>] 0]
        fun ε => ε ^ α * Real.log (ρ / ε ^ β) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Real.log_div hρ.ne' (Real.rpow_pos_of_pos hε β).ne', Real.log_rpow hε]
      ring
    refine Tendsto.congr' heq ?_
    simpa using (hη.const_mul (Real.log ρ)).add (hlogmul.const_mul (-β))
  have hw := t13r_tendsto_rpow (show 0 < β' by linarith)
  have hs := t13r_tendsto_rpow hβ
  have r4 := t13r_tendsto_rpow_div_pow (a := q) (b := β) (n := 3) (by push_cast; linarith)
  have r1 := t13r_tendsto_rpow_div_pow (a := β') (b := β) (n := 1) (by push_cast; linarith)
  have r2 := t13r_tendsto_rpow_div_pow (a := β') (b := β) (n := 2) (by push_cast; linarith)
  have r3 := t13r_tendsto_rpow_div_pow (a := α) (b := β) (n := 2) (by push_cast; linarith)
  have r5 := t13r_tendsto_rpow_div_pow (a := q) (b := β) (n := 2) (by push_cast; linarith)
  simp only [pow_one] at r1
  set S : ℝ → ℝ := fun ε => 6 * (ε ^ q / (ε ^ β) ^ 3) * (A * (π * ρ ^ 2) + ε ^ α) +
      12 * (A * (8 * π) * (ε ^ β' / ε ^ β + 4 * (ε ^ β' / ε ^ β) ^ 2 +
        ρ * (ε ^ β' / (ε ^ β) ^ 2)) + ε ^ α / (ε ^ β) ^ 2) +
      384 * (ε ^ q / (ε ^ β) ^ 2) ^ 2 * ((A * (π * ρ ^ 2) + ε ^ α) +
        (A * (8 * π * ε ^ β' * (ε ^ β + 2 * ε ^ β') + 8 * π * ε ^ β' * (ρ + 2 * ε ^ β')) +
          ε ^ α)) with hS
  obtain ⟨S₀, hSlim⟩ : ∃ S₀, Tendsto S (𝓝[>] 0) (𝓝 S₀) :=
    ⟨_, (((r4.const_mul 6).mul (hη.const_add _)).add
      (((((r1.add ((r1.pow 2).const_mul 4)).add (r2.const_mul ρ)).const_mul (A * (8 * π))).add
        r3).const_mul 12)).add
      (((r5.pow 2).const_mul 384).mul ((hη.const_add _).add
        (((((hw.const_mul (8 * π)).mul (hs.add (hw.const_mul 2))).add
          ((hw.const_mul (8 * π)).mul ((hw.const_mul 2).const_add ρ))).const_mul A).add hη)))⟩
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      lemma34Bound (ε ^ β) ρ (ε ^ q) (ε ^ β') A (ε ^ α) * Real.log (ρ / ε ^ β) =
        3 * A * (2 * π) + 3 * (ε ^ α * Real.log (ρ / ε ^ β)) + (Real.log (ρ / ε ^ β))⁻¹ * S ε := by
    filter_upwards [self_mem_nhdsWithin, hL.eventually_ne_atTop 0] with ε hε hk
    have hsk : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
    rw [lemma34Bound_eq hsk hk]
    simp only [hS]
    field_simp
    ring
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  have hlim := ((tendsto_const_nhds (x := 3 * A * (2 * π))).add (hηL.const_mul 3)).add (hX.mul hSlim)
  simpa using hlim

/-! ### Admissibility of the Lemma 3.4 tests at a real mesh -/

/-- **The three tests of Lemma 3.4 at a real mesh `ε ∈ (0, 1)`** (`bundle_recThreeAdmissible_of_small` with
`ε` in place of `2^{-k}`). -/
theorem t13r_threeAdmissible {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {ρ ρ₁ β β' rho C betaG4 : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ < ρ₁) (hρ₁rho : ρ₁ ≤ rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C)
    (hbetaG4 : 0 < betaG4) (hβ : 0 < β) (hbeta3 : 3 * β ≤ betaG4) (hbetaPrime : β' ≤ betaG4)
    (hsmall : ε ^ β ≤ ρ * Real.exp (-2)) :
    GMS4.Prop210Admissible ε rho C betaG4 (GMS3.annulusSet 0 (ε ^ β) ρ)
        (fun u => ‖fderiv ℝ (GMS3.logRad 0 ρ (ε ^ β)) u‖ ^ 2) ∧
      GMS4.Prop210Admissible ε rho C betaG4 (GMS3.annulusSet 0 (ε ^ β) ρ) (fun _ => 1) ∧
      GMS4.Prop210Admissible ε rho C betaG4 (ball 0 ρ₁) (GMS3.lemma34Layer (ε ^ β) ρ (ε ^ β')) := by
  have hs := Real.rpow_pos_of_pos hε β
  have hw := Real.rpow_pos_of_pos hε β'
  have hexp : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hsρ : ε ^ β < ρ := by
    calc ε ^ β ≤ ρ * Real.exp (-2) := hsmall
      _ < ρ * 1 := mul_lt_mul_of_pos_left hexp hρ
      _ = ρ := mul_one ρ
  have hratio : 0 < ε ^ β / ρ := div_pos hs hρ
  have hratio_le : ε ^ β / ρ ≤ Real.exp (-2) := by
    rw [div_le_iff₀ hρ]
    linarith [mul_comm ρ (Real.exp (-2))]
  have hlog : Real.log (ε ^ β / ρ) ≤ -2 := by
    calc Real.log (ε ^ β / ρ) ≤ Real.log (Real.exp (-2)) := Real.log_le_log hratio hratio_le
      _ = -2 := Real.log_exp (-2)
  have hsq : 4 ≤ (Real.log (ε ^ β / ρ)) ^ 2 := by nlinarith
  have hlinv : ((Real.log (ε ^ β / ρ)) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hsq
  have hC1 : 1 ≤ C := by nlinarith [Real.pi_gt_three]
  have hpowpos : 0 < ε ^ (-betaG4) := Real.rpow_pos_of_pos hε _
  have hOne : 1 ≤ C * ε ^ (-betaG4) := by
    have h1 : 1 ≤ ε ^ (-betaG4) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1.le (by linarith)
    nlinarith
  have hLayer : (ε ^ β')⁻¹ ≤ C * ε ^ (-betaG4) := by
    rw [← Real.rpow_neg hε.le]
    exact (Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)).trans
      (le_mul_of_one_le_left hpowpos.le hC1)
  have hM : ((Real.log (ε ^ β / ρ)) ^ 2 * (ε ^ β) ^ 2)⁻¹ ≤ C * ε ^ (-betaG4) := by
    have hp2 : ((ε ^ β) ^ 2)⁻¹ ≤ ε ^ (-betaG4) :=
      BundleSec4.bundle_invPower_le hε hε1.le 2 (by norm_num; linarith)
    calc ((Real.log (ε ^ β / ρ)) ^ 2 * (ε ^ β) ^ 2)⁻¹ =
          ((Real.log (ε ^ β / ρ)) ^ 2)⁻¹ * ((ε ^ β) ^ 2)⁻¹ := by rw [mul_inv_rev]; ring
      _ ≤ (1 / 4) * ε ^ (-betaG4) := mul_le_mul hlinv hp2 (by positivity) (by norm_num)
      _ ≤ C * ε ^ (-betaG4) := mul_le_mul_of_nonneg_right (by linarith) hpowpos.le
  have hL : 2 * ((Real.log (ε ^ β / ρ)) ^ 2 * (ε ^ β) ^ 3)⁻¹ ≤ C * ε ^ (-betaG4) := by
    have hp3 : ((ε ^ β) ^ 3)⁻¹ ≤ ε ^ (-betaG4) :=
      BundleSec4.bundle_invPower_le hε hε1.le 3 (by norm_num; linarith)
    calc 2 * ((Real.log (ε ^ β / ρ)) ^ 2 * (ε ^ β) ^ 3)⁻¹ =
          2 * (((Real.log (ε ^ β / ρ)) ^ 2)⁻¹ * ((ε ^ β) ^ 3)⁻¹) := by rw [mul_inv_rev]; ring
      _ ≤ 2 * ((1 / 4) * ε ^ (-betaG4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hlinv hp3 (by positivity) (by norm_num)) (by norm_num)
      _ ≤ C * ε ^ (-betaG4) := by nlinarith
  exact ⟨MesoModel.recAnnulusSqGrad_admissible hε hε1 hs hsρ (le_trans hρ₁.le hρ₁rho) hrho1 hC
      hbetaG4 hM hL,
    MesoModel.recAnnulusOne_admissible hε hε1 hs hsρ (le_trans hρ₁.le hρ₁rho) hrho1 hC hbetaG4 hOne,
    MesoModel.recBallLayer_admissible hε hε1 (hρ.trans hρ₁) hρ₁rho hrho1 hC hbetaG4 hw hOne hLayer⟩

/-! ### The rate helper -/

/-- **Coarse meshes absorbed into the rate**: if, for all small real `ε > 0`, the failure probabilities of a family of
events indexed by `i` with `Q ε i` are `≤ K ε^α`, then for some `C ≥ 0` they are `≤ C ε^α` for every `ε ∈ (0, 1)`.
`C` depends only on `K`, `α` and the threshold, not on `i`. -/
theorem t13r_rate_of_eventually {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} {Q : ℝ → ι → Prop} {Bad : ℝ → ι → Set Ω} {K α : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, Q ε i → P (Bad ε i) ≤ ENNReal.ofReal (K * ε ^ α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ i, Q ε i → P (Bad ε i) ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  set ε₁ := min u 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hu one_pos
  have hpos : 0 < ε₁ ^ α := Real.rpow_pos_of_pos hε₁0 α
  refine ⟨K + (ε₁ ^ α)⁻¹, by positivity, fun ε hε i hi => ?_⟩
  have hεα : 0 ≤ ε ^ α := Real.rpow_nonneg hε.1.le α
  rcases lt_or_ge ε u with h | h
  · refine (hsub ⟨hε.1, h⟩ i hi).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ (ε₁ ^ α)⁻¹ * ε ^ α := by positivity
    nlinarith
  · have hge : ε₁ ^ α ≤ ε ^ α :=
      Real.rpow_le_rpow hε₁0.le ((min_le_left _ _).trans h) hα.le
    have hone : (1 : ℝ) ≤ (K + (ε₁ ^ α)⁻¹) * ε ^ α := by
      have h1 : 1 ≤ (ε₁ ^ α)⁻¹ * ε ^ α := by
        calc (1 : ℝ) = (ε₁ ^ α)⁻¹ * ε₁ ^ α := (inv_mul_cancel₀ hpos.ne').symm
          _ ≤ (ε₁ ^ α)⁻¹ * ε ^ α := mul_le_mul_of_nonneg_left hge (inv_pos.2 hpos).le
      have h2 : 0 ≤ K * ε ^ α := mul_nonneg hK hεα
      nlinarith
    calc P (Bad ε i) ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((K + (ε₁ ^ α)⁻¹) * ε ^ α) := ENNReal.ofReal_le_ofReal hone

/-! ### (1.8) at every real mesh -/

/-- **The event (1.8) at mesh `ε`** for the mated-CRT map of a Brownian path `b` with the cells of a curve `c`: an
embedding with the curve cells exists, and for EVERY such embedding `H`,
`Gr_{τ}(0, 0) ≥ (1/A) log(ε⁻¹) deg(0)`, `τ` the exit time from `V(B_ρ(0))` (`GMS3.green`). -/
def T13RealGreenGood (ε ρ A : ℝ) (b : MatedCRT.Path2) (c : C(ℝ, ℂ)) : Prop :=
  (∃ (h : MatedCRT.IsLocallyFinite ε b) (H : CellularEmbedding (MatedCRT.graph ε b h) 0),
      ∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∧
    ∀ (h : MatedCRT.IsLocallyFinite ε b) (H : CellularEmbedding (MatedCRT.graph ε b h) 0),
      (∀ x : ℤ, H.cell x = c '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) →
        ENNReal.ofReal (Real.log ε⁻¹ / A * (MatedCRT.graph ε b h).deg 0) ≤
          green (MatedCRT.graph ε b h) 0 (vFin H (ball 0 ρ))

/-- **[18] (1.8) at every real mesh from the two named real-mesh inputs**: Lemma 2.7 on `B_{ρ₁}(0)` (exponent `q`,
rate `C₂₇ ε^α`) and Proposition 2.10 at `(ρ₁, 100, β_G)` (threshold `A₂`, tolerance and rate exponent `α`), both in
their stated forms, with `0 < ρ < ρ₁ < 1`, `3β < q`, `2β < β' ≤ q`, `2β < α`, `3β ≤ β_G`, `β' ≤ β_G`. -/
theorem t13r_green_of_inputs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (bm : Ω → MatedCRT.Path2) (η : Ω → C(ℝ, ℂ))
    {ρ ρ₁ q β β' α βG A₂ CP C27 : ℝ} (hρ : 0 < ρ) (hρρ₁ : ρ < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hβ : 0 < β) (hq : 3 * β < q) (hβ' : 2 * β < β') (hβ'q : β' ≤ q) (hα : 2 * β < α)
    (hβG : 0 < βG) (h3βG : 3 * β ≤ βG) (hβ'G : β' ≤ βG) (hA₂ : 0 ≤ A₂) (hCP : 0 ≤ CP) (hC27 : 0 ≤ C27)
    (h27 : ∀ ε ∈ Ioo (0 : ℝ) 1, P (EpsALemma27Bad bm η ε q ρ₁) ≤ ENNReal.ofReal (C27 * ε ^ α))
    (h210 : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ (V : Set ℂ) (g : ℂ → ℝ), GMS4.Prop210Admissible ε ρ₁ 100 βG V g →
      P (EpsAProp210Bad bm η ε V g A₂ (ε ^ α)) ≤ ENNReal.ofReal (CP * ε ^ α)) :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | ¬ T13RealGreenGood ε ρ A (bm ω) (η ω)} ≤ ENNReal.ofReal (C * ε ^ α) := by
  have hα0 : 0 < α := by linarith
  set M : ℝ := 3 * A₂ * (2 * π) + 1 with hMdef
  have hM : 0 < M := by positivity
  set A : ℝ := 2 * M / β with hAdef
  have hA : 0 < A := by positivity
  have hT := t13r_tendsto_lemma34Bound_mul_log (A := A₂) hρ hβ hq hβ' hα
  have hlogi : Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] 0) atTop := by
    have : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop :=
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
    refine this.congr' ?_
    filter_upwards with ε
    rw [Real.log_inv]
  have hs := t13r_tendsto_rpow hβ
  have hδ := t13r_tendsto_rpow (show 0 < q by linarith)
  have hqβ := t13r_tendsto_rpow_div_pow (a := q) (b := β) (n := 1) (by push_cast; linarith)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ _i : Unit, True →
      P {ω | ¬ T13RealGreenGood ε ρ A (bm ω) (η ω)} ≤ ENNReal.ofReal ((C27 + 3 * CP) * ε ^ α) := by
    filter_upwards [self_mem_nhdsWithin, hT.eventually (ge_mem_nhds (by linarith : 3 * A₂ * (2 * π) < M)),
      (hlogi.const_mul_atTop (by positivity : 0 < β / 2)).eventually_ge_atTop (-Real.log ρ),
      hlogi.eventually_gt_atTop 0, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
      hs.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ρ / 2)),
      hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ρ / 2)),
      hδ.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ρ₁ - ρ)),
      hqβ.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6)),
      hs.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ρ * Real.exp (-2)))]
      with ε hε0 hTk hlog1 hlog0 hε01 h2 h3 h4 h5 hsmall _ _
    have hε0' : (0 : ℝ) < ε := hε0
    have hε1 : ε < 1 := hε01.2
    have hsk : 0 < ε ^ β := Real.rpow_pos_of_pos hε0' β
    have hsρ : ε ^ β < ρ := by linarith
    have h6 : 6 * ε ^ q ≤ ε ^ β := by
      rw [pow_one, div_lt_iff₀ hsk] at h5
      linarith
    have hδρ : ε ^ q < ρ - ε ^ β := by linarith
    have hρ₁' : ρ + ε ^ q < ρ₁ := by linarith
    have hεI : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0', hε1⟩
    have hAdm := t13r_threeAdmissible hε0' hε1 hρ hρρ₁ le_rfl hρ₁1 BundleSec4.bundle_sixteen_pi_le_hundred hβG hβ
      h3βG hβ'G hsmall (β' := β')
    set Bk := lemma34Bound (ε ^ β) ρ (ε ^ q) (ε ^ β') A₂ (ε ^ α) with hBk
    have hB : 0 < Bk := t13_lemma34Bound_pos hsk hsρ (Real.rpow_pos_of_pos hε0' q).le
      (Real.rpow_pos_of_pos hε0' β').le hA₂ (Real.rpow_pos_of_pos hε0' α)
    set Λ := Real.log ε⁻¹ with hΛ
    have hℓ : Real.log (ρ / ε ^ β) = Real.log ρ + β * Λ := by
      rw [Real.log_div hρ.ne' hsk.ne', Real.log_rpow hε0', hΛ, Real.log_inv]
      ring
    have hℓlow : β / 2 * Λ ≤ Real.log (ρ / ε ^ β) := by rw [hℓ]; nlinarith
    have hBΛ : Bk * Λ ≤ A := by
      have h1 : Bk * (β / 2 * Λ) ≤ M := (mul_le_mul_of_nonneg_left hℓlow hB.le).trans hTk
      rw [hAdef, le_div_iff₀ hβ]
      nlinarith
    -- the failure event
    set B27 := EpsALemma27Bad bm η ε q ρ₁
    set Bf := EpsAProp210Bad bm η ε (annulusSet 0 (ε ^ β) ρ)
      (fun u => ‖fderiv ℝ (logRad 0 ρ (ε ^ β)) u‖ ^ 2) A₂ (ε ^ α)
    set B1 := EpsAProp210Bad bm η ε (annulusSet 0 (ε ^ β) ρ) (fun _ => 1) A₂ (ε ^ α)
    set Bg := EpsAProp210Bad bm η ε (ball 0 ρ₁) (lemma34Layer (ε ^ β) ρ (ε ^ β')) A₂ (ε ^ α)
    have hsub : {ω | ¬ T13RealGreenGood ε ρ A (bm ω) (η ω)} ⊆ B27 ∪ Bf ∪ B1 ∪ Bg := by
      intro ω hω
      by_contra hcon
      have h27ω : ω ∉ B27 := fun h => hcon (Or.inl (Or.inl (Or.inl h)))
      have hFω : ω ∉ Bf := fun h => hcon (Or.inl (Or.inl (Or.inr h)))
      have h1ω : ω ∉ B1 := fun h => hcon (Or.inl (Or.inr h))
      have hgω : ω ∉ Bg := fun h => hcon (Or.inr h)
      have h27' : _ := not_not.1 h27ω
      apply hω
      refine ⟨h27'.1, fun hlf H hcell => ?_⟩
      have hgreen := theorem14_green (matedCRT_connected ε (bm ω) hlf) H hsk hsρ
        (Real.rpow_pos_of_pos hε0' q).le h6 hδρ hρ₁' (Real.rpow_pos_of_pos hε0' β')
        (Real.rpow_le_rpow_of_exponent_ge hε0' hε1.le hβ'q) hA₂ (Real.rpow_pos_of_pos hε0' α).le
        (h27'.2 hlf H hcell) (epsA_prop210Bound_of_not_mem_bad hFω hlf H hcell)
        (epsA_prop210Bound_of_not_mem_bad h1ω hlf H hcell) (epsA_prop210Bound_of_not_mem_bad hgω hlf H hcell)
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hgreen
      have hdeg : (0 : ℝ) ≤ (MatedCRT.graph ε (bm ω) hlf).deg 0 := Nat.cast_nonneg _
      rw [div_mul_eq_mul_div, le_div_iff₀ hB, div_mul_eq_mul_div, div_le_iff₀ hA]
      nlinarith [mul_le_mul_of_nonneg_left hBΛ hdeg]
    calc P {ω | ¬ T13RealGreenGood ε ρ A (bm ω) (η ω)} ≤ P (B27 ∪ Bf ∪ B1 ∪ Bg) := measure_mono hsub
      _ ≤ ((P B27 + P Bf) + P B1) + P Bg :=
          (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
      _ ≤ ((ENNReal.ofReal (C27 * ε ^ α) + ENNReal.ofReal (CP * ε ^ α)) + ENNReal.ofReal (CP * ε ^ α)) +
            ENNReal.ofReal (CP * ε ^ α) :=
          add_le_add (add_le_add (add_le_add (h27 ε hεI) (h210 ε hεI _ _ hAdm.1)) (h210 ε hεI _ _ hAdm.2.1))
            (h210 ε hεI _ _ hAdm.2.2)
      _ = ENNReal.ofReal ((C27 + 3 * CP) * ε ^ α) := by
          have hm : 0 ≤ ε ^ α := Real.rpow_nonneg hε0'.le α
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  obtain ⟨C, hC, hrate⟩ := t13r_rate_of_eventually (Q := fun _ (_ : Unit) => True) hα0 (by positivity) hev
  exact ⟨A, hA, C, hC, fun ε hε => hrate ε hε () trivial⟩

end MatedCRTHarmonic.GMSMain
