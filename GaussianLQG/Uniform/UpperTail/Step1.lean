import GaussianLQG.Uniform.UpperTail.Defs
import GaussianLQG.Uniform.UpperTail.Leaves
import GaussianLQG.Uniform.RSW.Psi
import LQGMetric.Papers.DDDF.P18S2

/-!
# DDDF Proposition 18, Step 1, uniform in `ξ` (Route U, item U6)

Phase B, packet B-3 (worker PB-U6). Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`,
U6 and §5 (rows `dddf_p18_step1_psi`, `p18_step1_of_psi`). Templates (not edited):
`dddf_p18_step1_psi` (`LQGMetric/Papers/DDDF/P18S2.lean`) and `p18_step1_of_psi`
(`P18S1Conv.lean`); DDDF20 `tightness.tex` l. 900–910.

* `p18_step1_psi_of_consts`: the percolation argument of `dddf_p18_step1_psi` with the RSW
  constant `C_R` (form (3.39) at `(A, B) = (1/2, 4)`, used for `(1,1) → (3,1)`) and the output
  constant `C` as parameters: `p ≤ min(1/4, θ_r^{C_R})`, `θ_r = (1/16)^{25}/12`,
  `C ≥ max(64 K_p, 24/log 2)`, `K_p = C_R e^{C_R √|log(p/C_R)|}`, `c = log 2/2`.
* `p18_step1_psi_unif : P18Step1PsiU ξs`: `C_R` from `psi_rsw_high_quantile_unif_all`, which is
  chosen before the probability space and before `ξ`, so all constants are.
* `p18_step1_of_psi_of_consts`: the `ψ → φ` conversion of `p18_step1_of_psi` with its constants
  as parameters: `C ≥ A`, `C ≥ 4 + C_ψ`, `C ≥ C_ψ e^{ξM}`, `M = √(max(1, log(C'/(p/2)))/c')`.
* `p18_step1_unif : P18Step1U ξs` (ledger U6): `(A, c_A)` from `prop5_X3k_tail_W`, `(C', c')` from
  `exists_tail_XAB_unif_W` (both before the probability space, `ξ`-free), and
  `C = max(A, C_ψ e^{ξs M}, 4 + C_ψ)` (Recipe M: `e^{ξM} ≤ e^{ξs M}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- **DDDF Prop 18, Step 1 for `ψ`, with its constants as parameters** (template
`dddf_p18_step1_psi`, same proof): given the RSW bound (3.39) with constant `C_R` for the shapes
`(1,1) → (3,1)`, for `p ≤ min(1/4, θ_r^{C_R})` and `C ≥ max(64 K_p, 24/log 2)`,
`P(L^{(n)}_{3k,k}(ψ) ≥ C k² ℓ̄_n(ψ,p)) ≤ C e^{-(log 2/2) k}`. -/
theorem p18_step1_psi_of_consts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ CR : ℝ} (hCR : 0 < CR)
    (hrsw : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 → 3 * ε ^ (1 / CR) < 1 →
      ellBarQ ξ P (psiMN psiQ₀ W P 0 n) (rectAB 3 1) (ENNReal.ofReal (3 * ε ^ (1 / CR))) ≤
        CR * ellBarQ ξ P (psiMN psiQ₀ W P 0 n) (rectAB 1 1) (ENNReal.ofReal ε) *
          Real.exp (CR * Real.sqrt |Real.log (ε / CR)|))
    {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) (hpθ : p ≤ ((1 / 16 : ℝ) ^ 25 / 12) ^ CR)
    {C : ℝ} (hC64 : 64 * (CR * Real.exp (CR * Real.sqrt |Real.log (p / CR)|)) ≤ C)
    (hC24 : 24 / Real.log 2 ≤ C) (n k : ℕ) (hk : 1 ≤ k) :
    P {ω | C * k ^ 2 * ellBarQ ξ P (psiMN psiQ₀ W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
        lenObs ξ (psiMN psiQ₀ W P 0 n) (rectAB (3 * k) k) ω} ≤
      ENNReal.ofReal (C * Real.exp (-(Real.log 2 / 2 * k))) := by
  have := hW.isProbabilityMeasure
  set Q := psiQ₀
  set θr : ℝ := (1 / 16 : ℝ) ^ 25 / 12
  have hθr : 0 < θr := by positivity
  set p'' : ℝ := 3 * p ^ (1 / CR)
  have hp''0 : 0 < p'' := by have := Real.rpow_pos_of_pos hp (1 / CR); positivity
  have hp''θ : p'' ≤ 3 * θr := by
    have h : p ^ (1 / CR) ≤ θr :=
      calc p ^ (1 / CR) ≤ (θr ^ CR) ^ (1 / CR) := Real.rpow_le_rpow hp.le hpθ (by positivity)
        _ = θr := by rw [one_div, Real.rpow_rpow_inv hθr.le hCR.ne']
    show 3 * p ^ (1 / CR) ≤ 3 * θr
    linarith
  have hp''1 : p'' < 1 := by
    have : 3 * θr < 1 := by norm_num [θr]
    linarith
  have h4p : 4 * p'' ≤ (1 / 16 : ℝ) ^ 25 := by
    calc 4 * p'' ≤ 4 * (3 * θr) := mul_le_mul_of_nonneg_left hp''θ (by norm_num)
      _ = (1 / 16 : ℝ) ^ 25 := by simp only [θr]; ring
  set Kp : ℝ := CR * Real.exp (CR * Real.sqrt |Real.log (p / CR)|)
  have hKp : 0 < Kp := by positivity
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log 2 / 2
  set f := psiMN Q W P 0 n
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  set ℓ := ellBarQ ξ P f (rectAB 3 1) (ENNReal.ofReal p'')
  set ℓ1 := ellBarQ ξ P f (rectAB 1 1) (ENNReal.ofReal p)
  have hrs : ℓ ≤ Kp * ℓ1 := by
    have h := hrsw n p hp (by linarith) hp''1
    calc ℓ ≤ CR * ℓ1 * Real.exp (CR * Real.sqrt |Real.log (p / CR)|) := h
      _ = Kp * ℓ1 := by simp only [Kp]; ring
  have hq0 : 0 < ENNReal.ofReal p'' := ENNReal.ofReal_pos.2 hp''0
  have hq1 : ENNReal.ofReal p'' < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hp''1
  have hℓ0 : 0 ≤ ℓ := ellQ_nonneg hψ.cont hψ.meas _ (tsub_pos_of_lt hq1)
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0.ne')
  by_cases hk3 : k < 3
  · calc _ ≤ (1 : ℝ≥0∞) := prob_le_one
      _ ≤ ENNReal.ofReal (C * Real.exp (-(c * k))) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have h1 := Real.add_one_le_exp (-(c * k))
        have hc : c * k ≤ Real.log 2 := by simp only [c]; nlinarith
        have hl2 := Real.log_two_lt_d9
        have h24 : 24 ≤ 24 / Real.log 2 := by
          rw [le_div_iff₀ hl]; norm_num at hl2 ⊢; linarith
        have hE : (3 / 10 : ℝ) ≤ Real.exp (-(c * k)) := by norm_num at hl2; linarith
        nlinarith [mul_le_mul (h24.trans hC24) hE (by norm_num) (by linarith [h24.trans hC24])]
  push Not at hk3
  set B : ℤ × ℤ → Set Ω := fun x => siteBad (ξ := ξ) f ℓ (sh x)
  have hθ : (8 : ℝ≥0∞) * ENNReal.ofReal (1 / 16) ≤ 2⁻¹ := by
    rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    apply ENNReal.ofReal_le_ofReal; norm_num
  have hεθ : ENNReal.ofReal (4 * p'') ≤ ENNReal.ofReal (1 / 16) ^ ((4 + 1) ^ 2) := by
    rw [← ENNReal.ofReal_pow (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by norm_num at h4p ⊢; linarith)
  have hper := perc_peierls P (3 * k - 2) (k - 2) (by omega) (by omega) B 4 hθ hεθ
    (fun x _ => by
      refine (prob_siteBad_le hW Q n ℓ (sh x)).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
      exact prob_gt_ellBarQ hψ.cont hψ.meas _ hq0 hq1)
    (fun F _ hF => by
      choose T hT hTe using fun x => siteBad_eq_preimage (ξ := ξ) hψ.cont ℓ x
      have e : ∀ x, B x = {ω | (fun y => psiMN Q W P 0 n (sbox x y) ω) ∈ T x} := hTe
      simp only [e]
      exact (prob_iInter_sbox hW Q psiSmall_psiQ₀ n T hT F hF).le)
  have hsub : {ω | C * k ^ 2 * ℓ1 ≤ lenObs ξ f (rectAB (3 * k) k) ω} ⊆
      {ω | ¬ PercGoodLR ((3 * k - 2 : ℕ) : ℤ) ((k - 2 : ℕ) : ℤ) (fun x => ω ∉ B x)} := by
    intro ω hω hLR
    have eK : ((3 * k - 2 : ℕ) : ℤ) = 3 * (k : ℤ) - 2 := by omega
    have eL : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
    rw [eK, eL] at hLR
    have conv : ∀ R : MarkedRect, 0 ≤ R.w → 0 ≤ R.h → lenObs ξ f R ω ≤ ℓ →
        rectLen ξ (fun x => f x ω) R ≤ ENNReal.ofReal ℓ := fun R hw hh h => by
      rw [← ofReal_lenObs hψ.cont R hw hh ω]; exact ENNReal.ofReal_le_ofReal h
    have hR := rectLen_le_of_percGoodLR (ξ := ξ) (g := fun x => f x ω) (k := k)
      ENNReal.ofReal_ne_top (good := fun x => ω ∉ B x) (fun x hx _ => by
        simp only [B, siteBad, mem_union, mem_ofPred_eq, not_or, not_lt] at hx
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
        exact ⟨conv _ (by norm_num [sB]) (by norm_num [sB]) h1,
          conv _ (by norm_num [sT]) (by norm_num [sT]) h2,
          conv _ (by norm_num [sL]) (by norm_num [sL]) h3,
          conv _ (by norm_num [sR]) (by norm_num [sR]) h4⟩) hLR
    have e : (2 * ((3 * k * k : ℕ) : ℝ≥0∞) + 2) * (4 * ENNReal.ofReal ℓ) =
        ENNReal.ofReal (((8 * (3 * k * k) + 8 : ℕ) : ℝ) * ℓ) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]; push_cast; ring
    rw [e] at hR
    have hL : lenObs ξ f (rectAB (3 * k) k) ω ≤ ((8 * (3 * k * k) + 8 : ℕ) : ℝ) * ℓ :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hR
    have hpos : 0 < lenObs ξ f (rectAB (3 * k) k) ω :=
      lenObs_pos hψ.cont _ (by simp [rectAB]) (by simp [rectAB])
        (by simp [MarkedRect.crossWidth, rectAB]; omega) ω
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hN : ((8 * (3 * k * k) + 8 : ℕ) : ℝ) ≤ 32 * (k : ℝ) ^ 2 := by push_cast; nlinarith
    have h32 : lenObs ξ f (rectAB (3 * k) k) ω ≤ 32 * (k : ℝ) ^ 2 * (Kp * ℓ1) :=
      hL.trans ((mul_le_mul_of_nonneg_right hN hℓ0).trans
        (mul_le_mul_of_nonneg_left hrs (by positivity)))
    have hℓ1 : 0 < ℓ1 := by
      by_contra h
      push Not at h
      have : 32 * (k : ℝ) ^ 2 * (Kp * ℓ1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos hKp.le h)
      linarith
    have hkl : 0 < (k : ℝ) ^ 2 * ℓ1 := by positivity
    have h64 : 64 * Kp * ((k : ℝ) ^ 2 * ℓ1) ≤ C * ((k : ℝ) ^ 2 * ℓ1) :=
      mul_le_mul_of_nonneg_right hC64 hkl.le
    have hω' : C * (k : ℝ) ^ 2 * ℓ1 ≤ lenObs ξ f (rectAB (3 * k) k) ω := hω
    nlinarith [mul_pos hKp hkl]
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := hper
    _ ≤ ((3 * k - 2 : ℕ) : ℝ≥0∞) * 2⁻¹ ^ (k - 2) := by gcongr
    _ = ENNReal.ofReal (((3 * k - 2 : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ (k - 2)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (C * Real.exp (-(c * k))) :=
      ENNReal.ofReal_le_ofReal ((p18_perc_tail k hk3).trans
        (mul_le_mul_of_nonneg_right hC24 (Real.exp_pos _).le))

/-- **DDDF Prop 18, Step 1 for `ψ`, uniform in `ξ ∈ (0, ξs]` and in the white noise** (ledger U6;
template `dddf_p18_step1_psi`): with `C_R ≥ 1` of `psi_rsw_high_quantile_unif_all` at
`(A, B) = (1/2, 4)`, `p₀ = min(1/4, θ_r^{C_R})`, `C = max(64 K_p, 24/log 2)`, `c = log 2/2`. -/
theorem p18_step1_psi_unif (ξs : ℝ) (hξs : 0 < ξs) : P18Step1PsiU ξs := by
  obtain ⟨CR, hCR1, hrsw⟩ := psi_rsw_high_quantile_unif_all.{0} hξs psiQ₀ (A := 1 / 2) (B := 4)
    (by norm_num) (by norm_num)
  have hCR : 0 < CR := by linarith
  have hθr : (0 : ℝ) < (1 / 16 : ℝ) ^ 25 / 12 := by positivity
  refine ⟨min (1 / 4) (((1 / 16 : ℝ) ^ 25 / 12) ^ CR),
    lt_min (by norm_num) (Real.rpow_pos_of_pos hθr _), fun p hp hpp => ?_⟩
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max (64 * (CR * Real.exp (CR * Real.sqrt |Real.log (p / CR)|))) (24 / Real.log 2),
    Real.log 2 / 2, lt_of_lt_of_le (by positivity) (le_max_right _ _), by positivity,
    fun {Ω} _ {P} {W} hW ξ hξ n k hk => ?_⟩
  exact p18_step1_psi_of_consts hW hCR
    (fun n ε hε hε2 h3 => hrsw hW ξ hξ 1 1 3 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) n ε hε hε2 h3)
    hp (hpp.trans (min_le_left _ _)) (hpp.trans (min_le_right _ _)) (le_max_left _ _)
    (le_max_right _ _) n k hk

/-- **DDDF Prop 18, Step 1, the `ψ → φ` conversion with its constants as parameters** (template
`p18_step1_of_psi`, same proof): from Step 1 for `ψ` with `(C_ψ, c_ψ)`, the `X_{3k,k}` tail with
`(A, c_A)` and the Prop 5 tail of `X_{1,1}` at level `p/2` with `(C', c')`, every
`C ≥ max(A, C_ψ e^{ξM}, 4 + C_ψ)` gives
`P(L^{(n)}_{3k,k}(φ) ≥ e^{ξC√k} C k² ℓ̄_n(φ,p/2)) ≤ C e^{-min(c_A, c_ψ) k}`. -/
theorem p18_step1_of_psi_of_consts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {ξ : ℝ} (hξ : 0 < ξ) {p : ℝ} (hp : 0 < p)
    (hp1 : p ≤ 1 / 2) {Cψ cψ : ℝ} (hCψ : 0 < Cψ)
    (h1 : ∀ (n k : ℕ), 1 ≤ k →
      P {ω | Cψ * k ^ 2 * ellBarQ ξ P (psiMN psiQ₀ W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
          lenObs ξ (psiMN psiQ₀ W P 0 n) (rectAB (3 * k) k) ω} ≤
        ENNReal.ofReal (Cψ * Real.exp (-(cψ * k))))
    {A cA : ℝ} (hA : 0 < A)
    (hX : ∀ k : ℕ, 1 ≤ k → P {ω | ENNReal.ofReal (A * √k) ≤
        XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN psiQ₀ W P 0 n y ω) (3 * k) k} ≤
      ENNReal.ofReal (4 * Real.exp (-(cA * k))))
    {C' c' : ℝ}
    (htail : P {ω | ENNReal.ofReal (√(max 1 (Real.log (C' / (p / 2))) / c')) <
        XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN psiQ₀ W P 0 n y ω) 1 1} ≤
      ENNReal.ofReal (p / 2))
    {C : ℝ} (hAC : A ≤ C)
    (hψC : Cψ * Real.exp (ξ * √(max 1 (Real.log (C' / (p / 2))) / c')) ≤ C)
    (h4C : 4 + Cψ ≤ C) (n k : ℕ) (hk : 1 ≤ k) :
    P {ω | Real.exp (ξ * C * √k) * C * k ^ 2 * ellBarN ξ W P n (ENNReal.ofReal (p / 2)) ≤
        lenObs ξ (phiMN W P 0 n) (rectAB (3 * k) k) ω} ≤
      ENNReal.ofReal (C * Real.exp (-(min cA cψ * k))) := by
  have := hW.isProbabilityMeasure
  set Q := psiQ₀
  set M : ℝ := √(max 1 (Real.log (C' / (p / 2))) / c')
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hC0 : 0 < C := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hψv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  -- (2.27): `ℓ̄_n(ψ,p) ≤ e^{ξM} ℓ̄_n(φ,p/2)`
  have hlev : (1 - ENNReal.ofReal p) + ENNReal.ofReal (p / 2) = 1 - ENNReal.ofReal (p / 2) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp.le, ← ENNReal.ofReal_sub _ (by positivity),
      ← ENNReal.ofReal_add (by linarith) (by positivity)]
    congr 1; ring
  have hcmp := ellQ_psi_le_of_tail (ξ := ξ) hW Q zero_le_one zero_le_one hM htail
    (p := 1 - ENNReal.ofReal p)
    (by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp.le, ENNReal.ofReal_pos]; linarith)
    (by rw [hlev]; exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
          (ENNReal.ofReal_pos.2 (by positivity)).ne') n
  rw [hlev, abs_of_pos hξ] at hcmp
  set lφ := ellBarN ξ W P n (ENNReal.ofReal (p / 2))
  have hlφ : 0 ≤ lφ := ellQ_nonneg hφ.cont hφ.meas _
    (by rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_pos]
        linarith)
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne')
  have hcmp' : ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
      Real.exp (ξ * M) * lφ := hcmp
  set E₁ := {ω | ENNReal.ofReal (A * √k) ≤
    XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) (3 * k) k}
  set E₂ := {ω | Cψ * k ^ 2 * ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p) ≤
    lenObs ξ (psiMN Q W P 0 n) (rectAB (3 * k) k) ω}
  have hsub : {ω | Real.exp (ξ * C * √k) * C * k ^ 2 * lφ ≤
      lenObs ξ (phiMN W P 0 n) (rectAB (3 * k) k) ω} ⊆ E₁ ∪ E₂ := by
    intro ω hω
    by_cases h1 : ω ∈ E₁
    · exact Or.inl h1
    right
    have hXle : XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) (3 * k) k ≤
        ENNReal.ofReal (A * √k) := (not_le.1 h1).le
    have hL := lenObs_le_of_XAB_le (ξ := ξ) (φ := fun n => phiMN W P 0 n)
      (ψ := fun n => psiMN Q W P 0 n)
      (fun k _ => (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le k)).cont _) (by positivity)
      hk0 (by positivity) hXle n
    rw [abs_of_pos hξ] at hL
    have hω' : Real.exp (ξ * C * √k) * C * k ^ 2 * lφ ≤ _ := hω
    have hexp : Real.exp (ξ * (A * √k)) ≤ Real.exp (ξ * C * √k) := by
      refine Real.exp_le_exp.2 ?_
      have := mul_le_mul_of_nonneg_left hAC hξ.le
      nlinarith [Real.sqrt_nonneg (k : ℝ)]
    have hkey : C * k ^ 2 * lφ ≤ lenObs ξ (psiMN Q W P 0 n) (rectAB (3 * k) k) ω := by
      have h0 : 0 ≤ C * k ^ 2 * lφ := by positivity
      have h2 : Real.exp (ξ * (A * √k)) * (C * k ^ 2 * lφ) ≤
          Real.exp (ξ * (A * √k)) * lenObs ξ (psiMN Q W P 0 n) (rectAB (3 * k) k) ω := by
        calc _ ≤ Real.exp (ξ * C * √k) * (C * k ^ 2 * lφ) := mul_le_mul_of_nonneg_right hexp h0
          _ = Real.exp (ξ * C * √k) * C * k ^ 2 * lφ := by ring
          _ ≤ _ := hω'.trans hL
      exact le_of_mul_le_mul_left h2 (Real.exp_pos _)
    show Cψ * k ^ 2 * _ ≤ _
    calc Cψ * k ^ 2 * ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)
        ≤ Cψ * k ^ 2 * (Real.exp (ξ * M) * lφ) :=
          mul_le_mul_of_nonneg_left hcmp' (by positivity)
      _ = (Cψ * Real.exp (ξ * M)) * k ^ 2 * lφ := by ring
      _ ≤ C * k ^ 2 * lφ := by gcongr
      _ ≤ _ := hkey
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (hX k hk) (h1 n k hk)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : Real.exp (-(cA * k)) ≤ Real.exp (-(min cA cψ * k)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left cA cψ])
  have e2 : Real.exp (-(cψ * k)) ≤ Real.exp (-(min cA cψ * k)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right cA cψ])
  have he := Real.exp_pos (-(min cA cψ * k))
  nlinarith

/-- **DDDF Prop 18, Step 1, uniform in `ξ ∈ (0, ξs]` and in the white noise** (ledger U6
`p18_step1_unif`; template `p18_step1_of_psi`): `p₀ = min(p₀^ψ, 1/2)`, `c = min(c_A, c_ψ)` and
`C = max(A, C_ψ e^{ξs M}, 4 + C_ψ)`, all chosen before the probability space and before `ξ`. -/
theorem p18_step1_unif (ξs : ℝ) (hξs : 0 < ξs) : P18Step1U ξs := by
  obtain ⟨p₀, hp₀, hstep⟩ := p18_step1_psi_unif ξs hξs
  obtain ⟨A, cA, hA, hcA, hX⟩ := prop5_X3k_tail_W.{0} psiQ₀
  obtain ⟨C', c', hC', hc', htail⟩ := exists_tail_XAB_unif_W.{0} psiQ₀ 1
  refine ⟨min p₀ (1 / 2), lt_min hp₀ (by norm_num), fun p hp hpp => ?_⟩
  have hp1 : p ≤ 1 / 2 := hpp.trans (min_le_right _ _)
  obtain ⟨Cψ, cψ, hCψ, hcψ, h1⟩ := hstep p hp (hpp.trans (min_le_left _ _))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = √(max 1 (Real.log (C' / (p / 2))) / c') := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMdef]; exact Real.sqrt_nonneg _
  refine ⟨max (max A (Cψ * Real.exp (ξs * M))) (4 + Cψ), min cA cψ,
    lt_of_lt_of_le (by linarith) (le_max_right _ _), lt_min hcA hcψ,
    fun {Ω} _ {P} {W} hW ξ hξ n k hk => ?_⟩
  refine p18_step1_of_psi_of_consts hW hξ.1 hp hp1 hCψ (h1 hW ξ hξ) hA (hX hW)
    (htail hW 1 1 le_rfl le_rfl (p / 2) (by positivity))
    ((le_max_left _ _).trans (le_max_left _ _)) ?_ (le_max_right _ _) n k hk
  rw [← hMdef]
  refine le_trans ?_ ((le_max_right _ _).trans (le_max_left _ _))
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hξ.2 hM))
    hCψ.le

end Uniform
end GaussianLQG
