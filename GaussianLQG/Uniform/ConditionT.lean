import GaussianLQG.Uniform.RSW.Law
import LQGMetric.Papers.DDDF.S6P21Ratio
import LQGMetric.Papers.DDDF.S6P21Max
import LQGMetric.Papers.DDDF.T20CMain

/-!
# Condition (T) of DDDF Theorem 20 for small `ξ`, with uniform constants (Route U, item U8)

Phase B, packet PB-RSW. Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`, U8;
feasibility study `planning/audits/B1-S6-feasibility.md`, §4 U8; argument of the source's
(A.8)–(A.9) and of audit A4, V6.

DDDF's Condition (T) (`ConditionT`, `LQGMetric/Papers/DDDF/D5T.lean`) asks for `α > 1`, `c > 0`
and `K₀` such that, for `K₀ ≤ K ≤ n`, the ratio
`R = Σ_{π^K} e^{2ξψ_{0,K}} / (Σ_{π^K} e^{ξψ_{0,K}})²` along a measurable near-geodesic selection
satisfies `E[R^α]^{1/α} ≤ e^{-cK}`. In `LQGMetric` it is verified only for `ξ = γ/d_γ`
(`S6.s6_conditionT_psiQ₁`, which needs DDDF (5.54), `ξ < 2` and `Q > 2`). For small `ξ` no
exponent input is needed:

* `S6.ratio_pathwise` (DDDF Prop 21, Steps 1–3, valid for every `ξ > 0`) gives
  `R · L_K ≤ 4·2^{-K} e^{ξM} e^{2ξX} e^{6ξO}` with `M = sup_{[0,1]²}|φ_{0,K}|`, `X = Xbig`,
  `O = Obig`, and `L_K = L^{(K)}_{1,1}(φ) ≥ e^{-ξM}` (`L23.toReal_rectLen_bounds`); hence, for
  `ξ ≤ 1/8`, `R ≤ 4·2^{-K} e^{M/4} e^{X/4} e^{3O/4}`, a bound by one random variable that does
  not depend on `ξ` (`ratio_sq_le`; ledger Recipe D);
* with `α = 2` and Hölder's inequality with exponents `(3,3,3)`, the moments
  `E e^{3M/2} ≤ 4^{3K/2 + K₁√K}` (`prop2_expMoment_int`, `γ' = 3/2 < 2`),
  `E e^{3X/2} ≤ M_X` (`expMoment_XAB_shift_W`) and `E e^{9O/2} ≤ 25 e^{c_O K^{5/8} + K_O K^{1/4}}`
  (`obig_expMoment`, a copy of `S6.obig_moment`; `T20C.prop3_expMoment_shift`) give
  `E[R²]^{1/2} ≤ e^{-(K log 2)/2 + o(K)} ≤ e^{-(log 2/4) K}` for `K ≥ K₀` (`final_real_T`).

All constants (`α = 2`, `c = log 2 / 4`, `K₀`) are chosen before the probability space and
before `ξ` (`conditionTU_small_all : ConditionTUAll (1/8) Q`); the ledger's per-noise form
`conditionTU_small hW Q : ConditionTU (1/8) Q W P` is its corollary. The near-geodesic selections
are those of `S6.exists_nearGeodSel`. The `γ`-specific file `S6P21.lean` is not imported.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

universe u

/-- **Condition (T), uniform in `ξ ∈ (0, ξs]` and in the white noise** (strong form of the
ledger's `ConditionTU`; per-`ξ` template `ConditionT`, `LQGMetric/Papers/DDDF/D5T.lean`): `α`, `c`
and `K₀` are chosen before the probability space and before `ξ`. -/
def ConditionTUAll (ξs : ℝ) (Q : PsiParams) : Prop :=
  ∃ α : ℝ, 1 < α ∧ ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
    ∀ η : ℝ, 0 < η → ∃ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ ∧
      ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
        (∫⁻ ω, ENNReal.ofReal
            (T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) (γ n ω) ^ α) ∂P) ^ (1 / α) ≤
          ENNReal.ofReal (Real.exp (-(c * K)))

/-- **Condition (T), uniform in `ξ ∈ (0, ξs]`** (ledger U0, U8, `ConditionTU ξs Q W P`; per-`ξ`
template `ConditionT`): for a fixed white noise, `α`, `c` and `K₀` are chosen before `ξ`. -/
def ConditionTU {Ω : Type*} [MeasurableSpace Ω] (ξs : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ)
    (P : Measure Ω) : Prop :=
  ∃ α : ℝ, 1 < α ∧ ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, ∀ ξ ∈ Ioc (0 : ℝ) ξs,
    ∀ η : ℝ, 0 < η → ∃ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ ∧
      ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
        (∫⁻ ω, ENNReal.ofReal
            (T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) (γ n ω) ^ α) ∂P) ^ (1 / α) ≤
          ENNReal.ofReal (Real.exp (-(c * K)))

/-- the strong form gives the ledger's per-noise form -/
theorem ConditionTUAll.conditionTU {ξs : ℝ} {Q : PsiParams} (h : ConditionTUAll.{u} ξs Q)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) : ConditionTU ξs Q W P := by
  obtain ⟨α, hα, c, hc, K₀, hT⟩ := h
  exact ⟨α, hα, c, hc, K₀, hT hW⟩

/-- the uniform condition gives DDDF's Condition (T) at every `ξ ∈ (0, ξs]` -/
theorem ConditionTU.conditionT {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξs : ℝ} {Q : PsiParams} (h : ConditionTU ξs Q W P) {ξ : ℝ}
    (hξ : ξ ∈ Ioc (0 : ℝ) ξs) : ConditionT ξ Q W P := by
  obtain ⟨α, hα, c, hc, K₀, hT⟩ := h
  exact ⟨α, hα, c, hc, K₀, fun η hη => hT ξ hξ η hη⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ} in
/-- the moment of `Obig` (copy of `S6.obig_moment`, `LQGMetric/Papers/DDDF/S6P21.lean`, which
sits in a file with `γ`-specific imports; ledger Finding fd:docs (iv)):
`E e^{b O_K} ≤ 25 e^{c K^{5/8} + C K^{1/4}}` from (2.17) on the 25 translated unit boxes -/
lemma obig_expMoment {b cO KO : ℝ} (hb : 0 < b)
    (hO : ∀ (n : ℕ) (Y : ℂ → Ω → ℝ),
      (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
      (∀ ω, ContDiff ℝ 1 fun x => Y x ω) → ∀ c₁ : ℂ,
      AEMeasurable (fun ω => ((2 : ℝ) ^ n)⁻¹ *
        ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖) P ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (b * (n : ℝ) ^ (1 / 8 : ℝ) * (((2 : ℝ) ^ n)⁻¹ *
        ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖))) ∂P ≤
        ENNReal.ofReal (Real.exp (cO * (n : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) +
          KO * (n : ℝ) ^ (2 * (1 / 8 : ℝ)))))
    {K : ℕ} (hK : 1 ≤ K) (Y : ℂ → Ω → ℝ)
    (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x)
    (hYc : ∀ ω, ContDiff ℝ 1 fun x => Y x ω) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (b * T20C.Obig K Y ω)) ∂P ≤
      ENNReal.ofReal (25 * Real.exp (cO * (K : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) +
        KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)))) := by
  set E := Real.exp (cO * (K : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) + KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)))
  set Oc : ℂ → Ω → ℝ := fun c₁ ω => ((2 : ℝ) ^ K)⁻¹ *
    ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖ with hOc
  have hKe : (1 : ℝ) ≤ (K : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hK) (by norm_num)
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (b * T20C.Obig K Y ω)) ≤
      ∑ c₁ ∈ T20C.offs, ENNReal.ofReal (Real.exp (b * (K : ℝ) ^ (1 / 8 : ℝ) * Oc c₁ ω)) := by
    intro ω
    obtain ⟨c₁, hc₁, he⟩ := Finset.exists_mem_eq_sup' T20C.offs_nonempty (fun c₁ => Oc c₁ ω)
    have e : T20C.Obig K Y ω = Oc c₁ ω := he
    have hO0 : 0 ≤ Oc c₁ ω := mul_nonneg (by positivity)
      (Real.iSup_nonneg fun _ => norm_nonneg _)
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) (Finset.single_le_sum
      (f := fun c₁ => ENNReal.ofReal (Real.exp (b * (K : ℝ) ^ (1 / 8 : ℝ) * Oc c₁ ω)))
      (fun _ _ => zero_le) hc₁)
    rw [e]
    have := mul_le_mul_of_nonneg_right hKe (mul_nonneg hb.le hO0)
    nlinarith
  calc _ ≤ ∫⁻ ω, ∑ c₁ ∈ T20C.offs, ENNReal.ofReal (Real.exp (b * (K : ℝ) ^ (1 / 8 : ℝ) *
        Oc c₁ ω)) ∂P := lintegral_mono hpt
    _ = ∑ c₁ ∈ T20C.offs, ∫⁻ ω, ENNReal.ofReal (Real.exp (b * (K : ℝ) ^ (1 / 8 : ℝ) *
        Oc c₁ ω)) ∂P := lintegral_finsetSum' _ fun c₁ _ =>
          (Real.measurable_exp.comp_aemeasurable
            ((hO K Y hY hYc c₁).1.const_mul _)).ennreal_ofReal
    _ ≤ ∑ c₁ ∈ T20C.offs, ENNReal.ofReal E :=
        Finset.sum_le_sum fun c₁ _ => (hO K Y hY hYc c₁).2
    _ = (T20C.offs.card : ℝ≥0∞) * ENNReal.ofReal E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 25 * ENNReal.ofReal E := by gcongr; exact_mod_cast T20C.card_offs_le
    _ = ENNReal.ofReal (25 * E) := by rw [ENNReal.ofReal_mul (by norm_num)]; simp

/-- the pointwise real inequality behind Condition (T) for `ξ ≤ 1/8`: from
`R L ≤ 4h e^{ξM} e^{2ξX} e^{6ξO}` and `L ≥ e^{-ξM}`,
`R² ≤ 16 h² (e^{3M/2})^{1/3} (e^{3X/2})^{1/3} (e^{9O/2})^{1/3}` -/
lemma ratio_sq_le {R L h M X O ξ : ℝ} (hR : 0 ≤ R) (hh : 0 < h) (hξ : ξ ≤ 1 / 8) (hM : 0 ≤ M) (hX : 0 ≤ X) (hO : 0 ≤ O) (hL : Real.exp (-(ξ * M)) ≤ L)
    (hRL : R * L ≤ 4 * h * Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O)) :
    R ^ (2 : ℝ) ≤ 16 * h ^ 2 * (Real.exp (3 / 2 * M) ^ (1 / 3 : ℝ) *
      Real.exp (3 / 2 * X) ^ (1 / 3 : ℝ) * Real.exp (9 / 2 * O) ^ (1 / 3 : ℝ)) := by
  have hL0 : 0 < L := (Real.exp_pos _).trans_le hL
  set s := 2 * ξ * M + 2 * ξ * X + 6 * ξ * O with hs
  have hB : 0 ≤ 4 * h * Real.exp s := by positivity
  have e1 : 4 * h * Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O) =
      4 * h * Real.exp s * Real.exp (-(ξ * M)) := by
    have e : Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O) =
        Real.exp s * Real.exp (-(ξ * M)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hs]; ring
    calc 4 * h * Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O)
        = 4 * h * (Real.exp (ξ * M) * Real.exp (2 * ξ * X) * Real.exp (6 * ξ * O)) := by ring
      _ = 4 * h * (Real.exp s * Real.exp (-(ξ * M))) := by rw [e]
      _ = 4 * h * Real.exp s * Real.exp (-(ξ * M)) := by ring
  have h1 : R ≤ 4 * h * Real.exp s := by
    have : R * L ≤ 4 * h * Real.exp s * L :=
      (hRL.trans_eq e1).trans (mul_le_mul_of_nonneg_left hL hB)
    exact le_of_mul_le_mul_right this hL0
  have h2 : s ≤ M / 4 + X / 4 + 3 * O / 4 := by
    rw [hs]
    have hM' : ξ * M ≤ 1 / 8 * M := mul_le_mul_of_nonneg_right hξ hM
    have hX' : ξ * X ≤ 1 / 8 * X := mul_le_mul_of_nonneg_right hξ hX
    have hO' : ξ * O ≤ 1 / 8 * O := mul_le_mul_of_nonneg_right hξ hO
    linarith
  have h3 : R ≤ 4 * h * Real.exp (M / 4 + X / 4 + 3 * O / 4) :=
    h1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (by positivity))
  rw [Real.rpow_two, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add,
    ← Real.exp_add]
  calc R ^ 2 ≤ (4 * h * Real.exp (M / 4 + X / 4 + 3 * O / 4)) ^ 2 := pow_le_pow_left₀ hR h3 2
    _ = 16 * h ^ 2 * (Real.exp (M / 4 + X / 4 + 3 * O / 4) *
          Real.exp (M / 4 + X / 4 + 3 * O / 4)) := by ring
    _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring

/-- the real asymptotics of Condition (T) for `ξ ≤ 1/8`:
`(16·4^{-K} (4^{3K/2 + K₁√K})^{1/3} M_X^{1/3} (25 e^{c_O K^{5/8} + K_O K^{1/4}})^{1/3})^{1/2}
≤ e^{-(log 2/4) K}` once the sub-linear terms are below `(log 2/4) K` -/
lemma final_real_T {K : ℕ} {K₁ MX cO KO : ℝ} (hK1 : (1 : ℝ) ≤ K) (hMX : 0 < MX)
    (hasy : Real.log 4 + (Real.log MX + Real.log 25) / 6 + ((0 : ℕ) : ℝ) * Real.log (K + 1) +
      (|K₁ * Real.log 4 / 6| + |cO| / 6) * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) +
      |KO| / 6 * (K : ℝ) ^ (2 * (1 / 8 : ℝ)) + 0 * (K : ℝ) ^ ((2 : ℝ) / 3) ≤
        Real.log 2 / 2 / 2 * K) :
    (16 * ((2 : ℝ)⁻¹ ^ K) ^ 2 * (((4 : ℝ) ^ (3 / 2 * (K : ℝ) + K₁ * √(K : ℝ))) ^ (1 / 3 : ℝ) *
      MX ^ (1 / 3 : ℝ) * (25 * Real.exp (cO * (K : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) +
        KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)))) ^ (1 / 3 : ℝ))) ^ (1 / 2 : ℝ) ≤
      Real.exp (-(Real.log 2 / 4 * K)) := by
  set L2 := Real.log 2 with hL2
  have hL20 : 0 < L2 := Real.log_pos (by norm_num)
  have hL4 : Real.log 4 = 2 * L2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hL16 : Real.log 16 = 4 * L2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  set x := 3 / 2 * (K : ℝ) + K₁ * √(K : ℝ) with hx
  set y := cO * (K : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) + KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)) with hy
  set Z := 16 * ((2 : ℝ)⁻¹ ^ K) ^ 2 * (((4 : ℝ) ^ x) ^ (1 / 3 : ℝ) * MX ^ (1 / 3 : ℝ) *
    (25 * Real.exp y) ^ (1 / 3 : ℝ)) with hZ
  have h4x : 0 < (4 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have h25 : 0 < 25 * Real.exp y := by positivity
  have hZ0 : 0 < Z := by positivity
  rw [Real.rpow_def_of_pos hZ0, Real.exp_le_exp]
  -- the logarithm of `Z`
  have hlogZ : Real.log Z = 4 * L2 - 2 * K * L2 + 1 / 3 * (x * (2 * L2)) +
      1 / 3 * Real.log MX + 1 / 3 * (Real.log 25 + y) := by
    have a1 : Real.log (16 * ((2 : ℝ)⁻¹ ^ K) ^ 2) = 4 * L2 - 2 * K * L2 := by
      rw [Real.log_mul (by norm_num) (by positivity), hL16, ← pow_mul, Real.log_pow,
        Real.log_inv]
      push_cast; ring
    have a2 : Real.log (((4 : ℝ) ^ x) ^ (1 / 3 : ℝ)) = 1 / 3 * (x * (2 * L2)) := by
      rw [Real.log_rpow h4x, Real.log_rpow (by norm_num), hL4]
    have a3 : Real.log (MX ^ (1 / 3 : ℝ)) = 1 / 3 * Real.log MX := Real.log_rpow hMX _
    have a4 : Real.log ((25 * Real.exp y) ^ (1 / 3 : ℝ)) = 1 / 3 * (Real.log 25 + y) := by
      rw [Real.log_rpow h25, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    have b1 : (16 * ((2 : ℝ)⁻¹ ^ K) ^ 2) ≠ 0 := by positivity
    have b2 : ((4 : ℝ) ^ x) ^ (1 / 3 : ℝ) ≠ 0 := by positivity
    have b3 : MX ^ (1 / 3 : ℝ) ≠ 0 := by positivity
    have b4 : (25 * Real.exp y) ^ (1 / 3 : ℝ) ≠ 0 := by positivity
    rw [hZ, Real.log_mul b1 (mul_ne_zero (mul_ne_zero b2 b3) b4), a1,
      Real.log_mul (mul_ne_zero b2 b3) b4, Real.log_mul b2 b3, a2, a3, a4]
    ring
  rw [hlogZ]
  -- the sub-linear terms
  have hp58 : 0 ≤ (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) := by positivity
  have hp14 : 0 ≤ (K : ℝ) ^ (2 * (1 / 8 : ℝ)) := by positivity
  have hsq : √(K : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  have t1 : K₁ * Real.log 4 / 6 * √(K : ℝ) ≤
      |K₁ * Real.log 4 / 6| * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg _))
  have t2 : cO / 6 * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) ≤ |cO| / 6 * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) :=
    mul_le_mul_of_nonneg_right (by have := le_abs_self cO; linarith) hp58
  have t3 : KO / 6 * (K : ℝ) ^ (2 * (1 / 8 : ℝ)) ≤ |KO| / 6 * (K : ℝ) ^ (2 * (1 / 8 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by have := le_abs_self KO; linarith) hp14
  have ey : y = cO * (K : ℝ) ^ ((1 : ℝ) / 2 + 1 / 8) + KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)) := by
    rw [hy]
  rw [hx, ey]
  simp only [Nat.cast_zero, zero_mul, add_zero] at hasy
  rw [hL4] at hasy t1
  nlinarith [t1, t2, t3, hasy]

/-- **Condition (T) for `ξ ∈ (0, 1/8]`, uniform in `ξ` and in the white noise** (strong form of
ledger U8; source (A.8)–(A.9), audit A4 V6): `α = 2`, `c = log 2 / 4` and `K₀` are chosen before
the probability space and before `ξ`, for every choice of the parameters `Q` of `ψ`. -/
theorem conditionTU_small_all (Q : PsiParams) : ConditionTUAll.{u} (1 / 8) Q := by
  -- the constants, before `Ω` and `ξ`
  obtain ⟨K₁, hK₁⟩ := prop2_expMoment_int (γ := 3 / 2) (by norm_num) (by norm_num)
  obtain ⟨MX, hMX⟩ := expMoment_XAB_shift_W Q T20C.cBig 5 5 (l := 3 / 2) (by norm_num)
  obtain ⟨cO, KO, hO⟩ := T20C.prop3_expMoment_shift (by norm_num : (0 : ℝ) < 1 / 8)
    (a := 9 / 2) (by norm_num)
  set MX' : ℝ := max MX 1 with hMX'
  have hMX'0 : 0 < MX' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K₃, hK₃⟩ := T20C.asymp (c := Real.log 2 / 2) (ε := 1 / 8) (by positivity)
    (by norm_num) (by norm_num) (Real.log 4 + (Real.log MX' + Real.log 25) / 6)
    (|K₁ * Real.log 4 / 6| + |cO| / 6) (|KO| / 6) 0 0 (by positivity) (by positivity) le_rfl
  refine ⟨2, by norm_num, Real.log 2 / 4, by positivity, max K₃ 2,
    fun {Ω} _ {P} {W} hW ξ hξ η hη => ?_⟩
  have := hW.isProbabilityMeasure
  obtain ⟨hξ0, hξ8⟩ := hξ
  obtain ⟨Γ, hΓ⟩ := S6.exists_nearGeodSel hW Q ξ hη
  refine ⟨Γ, hΓ, fun K hK n hn => ?_⟩
  have hK3 : K₃ ≤ K := (le_max_left _ _).trans hK
  have hK2 : 2 ≤ K := (le_max_right _ _).trans hK
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  -- a `C¹` version of `φ_{0,K}`
  obtain ⟨Y, -, hY, -, hYc, -⟩ := exists_C1_modification_phi hW (a := ((2 : ℝ) ^ K)⁻¹) (b := 1)
    (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 K x ω := by
    refine T20C.ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ K)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  set h := (2 : ℝ)⁻¹ ^ K with hh
  have hh0 : 0 < h := by positivity
  set F0 : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (3 / 2 * ⨆ z : ferniqueBox 0 1, |Y z ω|))
  set F1 : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (3 / 2 * T20C.Xbig Q W P ω))
  set F2 : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (9 / 2 * T20C.Obig K Y ω))
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x ω)
      (Γ n ω) ^ (2 : ℝ)) ≤ ENNReal.ofReal (16 * h ^ 2) *
        (F0 ω ^ (1 / 3 : ℝ) * F1 ω ^ (1 / 3 : ℝ) * F2 ω ^ (1 / 3 : ℝ)) := by
    filter_upwards [hYeq, T20D.ae_XAB_shift_ne_top hW Q T20C.cBig 5 5] with ω hω hfin
    have hRL := S6.ratio_pathwise Q hξ0 hK2 (hYc ω) hω hfin (hΓ.adm n ω)
    -- `L^{(K)}_{1,1}(φ) ≥ e^{-ξM}`
    have hcpt : IsCompact (ferniqueBox (0 : ℂ) 1) := by
      rw [← rectAB_one_toSet]; exact (rectAB 1 1).isCompact_toSet
    have hbdd : BddAbove (range fun z : ferniqueBox (0 : ℂ) 1 => |Y z ω|) := by
      have := isCompact_iff_compactSpace.1 hcpt
      exact (isCompact_range (continuous_abs.comp
        ((hYc ω).continuous.comp continuous_subtype_val))).bddAbove
    have hMb : ∀ x ∈ L23.sq01, |phiMN W P 0 K x ω| ≤ ⨆ z : ferniqueBox 0 1, |Y z ω| := by
      intro x hx
      have hxF : x ∈ ferniqueBox (0 : ℂ) 1 := by rw [← rectAB_one_toSet]; exact hx
      rw [← hω x]
      exact le_ciSup hbdd (⟨x, hxF⟩ : ferniqueBox (0 : ℂ) 1)
    have hLb := (L23.toReal_rectLen_bounds (ξ := ξ) hMb).2.1
    rw [abs_of_pos hξ0] at hLb
    have hb := ratio_sq_le (T20C.condTRatio_nonneg _ _ _ _) hh0 hξ8
      (Real.iSup_nonneg fun _ => abs_nonneg _) ENNReal.toReal_nonneg (T20C.Obig_nonneg K Y ω)
      hLb hRL
    simp only [F0, F1, F2]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hb
  -- measurability
  have hF0m : AEMeasurable F0 P :=
    ((aemeasurable_sup_abs hW (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
      hY fun ω => (hYc ω).continuous).const_mul _).exp.ennreal_ofReal
  have hF1m : AEMeasurable F1 P := (((hMX hW).1).const_mul _).exp.ennreal_ofReal
  have hF2m : AEMeasurable F2 P :=
    ((T20C.aemeasurable_sup'_fun T20C.offs_nonempty fun c₁ _ =>
      (hO hW K Y hY hYc c₁).1).const_mul _).exp.ennreal_ofReal
  -- Hölder's inequality with exponents `(3, 3, 3)`
  have hH : ∫⁻ ω, F0 ω ^ (1 / 3 : ℝ) * F1 ω ^ (1 / 3 : ℝ) * F2 ω ^ (1 / 3 : ℝ) ∂P ≤
      (∫⁻ ω, F0 ω ∂P) ^ (1 / 3 : ℝ) * (∫⁻ ω, F1 ω ∂P) ^ (1 / 3 : ℝ) *
        (∫⁻ ω, F2 ω ∂P) ^ (1 / 3 : ℝ) := by
    have h := ENNReal.lintegral_prod_norm_pow_le (μ := P) Finset.univ
      (f := ![F0, F1, F2]) (fun i _ => by
        fin_cases i
        · exact hF0m
        · exact hF1m
        · exact hF2m) (p := ![1 / 3, 1 / 3, 1 / 3])
      (by simp only [Fin.sum_univ_three, Matrix.cons_val]; norm_num)
      (fun i _ => by fin_cases i <;> simp)
    simpa [Fin.prod_univ_three] using h
  -- the moments
  have m0 : ∫⁻ ω, F0 ω ∂P ≤
      ENNReal.ofReal ((4 : ℝ) ^ (3 / 2 * (K : ℝ) + K₁ * √(K : ℝ))) := by
    obtain ⟨hint, hle⟩ := hK₁ hW K Y hY fun ω => (hYc ω).continuous
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hle
  have m1 : ∫⁻ ω, F1 ω ∂P ≤ ENNReal.ofReal MX' :=
    ((hMX hW).2).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have m2 := obig_expMoment (b := 9 / 2) (cO := cO) (KO := KO) (by norm_num)
    (fun n Y hY hYc c₁ => hO hW n Y hY hYc c₁) (by omega : 1 ≤ K) Y hY hYc
  have hfinal := final_real_T (K := K) (K₁ := K₁) (cO := cO) (KO := KO) hK1r hMX'0
    (hK₃ K hK3)
  -- assembling
  have hI : ∫⁻ ω, ENNReal.ofReal (T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x ω)
      (Γ n ω) ^ (2 : ℝ)) ∂P ≤ ENNReal.ofReal (16 * h ^ 2 *
        (((4 : ℝ) ^ (3 / 2 * (K : ℝ) + K₁ * √(K : ℝ))) ^ (1 / 3 : ℝ) * MX' ^ (1 / 3 : ℝ) *
          (25 * Real.exp (cO * (K : ℝ) ^ (1 / 2 + 1 / 8 : ℝ) +
            KO * (K : ℝ) ^ (2 * (1 / 8 : ℝ)))) ^ (1 / 3 : ℝ))) := by
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul' le_rfl hH).trans ?_
    have e0 := ENNReal.rpow_le_rpow m0 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have e1 := ENNReal.rpow_le_rpow m1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have e2 := ENNReal.rpow_le_rpow m2 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    refine (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' e0 e1) e2)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.rpow_le_rpow hI (by norm_num)).trans ?_
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (hfinal.trans_eq (by ring_nf))

/-- **Condition (T) for `ξ ∈ (0, 1/8]`, with uniform constants** (ledger U8,
`conditionTU_small`; source (A.8)–(A.9), audit A4 V6): for a white noise `W` and every choice of
the parameters `Q` of `ψ` (the ledger's instance is `Q = S6.psiQ₁`), `α = 2`, `c = log 2 / 4` and
`K₀` are chosen before `ξ` (in fact before the noise, `conditionTU_small_all`). -/
theorem conditionTU_small {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) :
    ConditionTU (1 / 8) Q W P :=
  (conditionTU_small_all.{u} Q).conditionTU hW

end Uniform
end GaussianLQG
