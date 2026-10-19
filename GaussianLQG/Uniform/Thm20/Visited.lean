import GaussianLQG.Uniform.Thm20.Pathwise
import GaussianLQG.Uniform.Thm20.Ratio
import GaussianLQG.Uniform.Thm20.Apriori
import GaussianLQG.Uniform.ConditionT

/-!
# DDDF Theorem 20, Step 4 for the visited blocks, uniform in `ξ`

Phase B, packet PB-U9 (ledger U9, rows `dddf_t20_step4_visited_of_pathwise` and
`dddf_t20_step4_of_visited` of §`subsec:ledger-T20`; DDDF (5.65)–(5.67), `tightness.tex`
l. 1156–1172).

The template `dddf_t20_step4_visited_of_pathwise` (`LQGMetric/Papers/DDDF/T20CMain.lean`) takes
expectations in the pathwise bound: Hölder with Condition (T), the moments of `X` and of the
oscillation, the ratio moment (5.66) and the comparison `Λ_{n−K}(φ,p) ≤ C_Λ Λ_{n−K}(ψ,p/2)`; the
sub-exponential factors are absorbed by the non-quantitative threshold `T20C.asymp`. Its inputs
are obtained after `ξ` and the noise. Here:

* `t20Step4VisitedAt_of`: the template proof with every input constant as a parameter
  (`α, c, K₁` of (T); `C₀, d, K₂` of the pathwise bound; `Cr, cr` of (5.66); `C_Λ`; `M_X`;
  `c_O, K_O`; and the threshold `K₃` of `asymp` at `A₀ = visA0 …`, `B₃ = visB3 …`); the output
  constants are the template's `C₂ = c/2`, `K₀ = max (max K₁ K₂) (max K₃ 1)`;
* `t20_step4_visited_of_pathwise_unif`: the uniform version (ledger Recipe E: `asymp` is called
  once, before the probability space and before `ξ`, at the uniform inputs: `α, c, K₁` of the
  uniform Condition (T) (U8), the uniform pathwise constants, `Cr, cr` of
  `t20_ratio_moment_unif` (from U5, U6), `C_Λ = e^{2ξs M}` of `LambdaN_le_LambdaNPsi_unif`, `M_X`
  of `expMoment_XAB_shift_W` and `c_O, K_O` of `prop3_expMoment_shift`, both at
  `l = a = 3βC₀`);
* `t20Step4At_of_visitedAt`, `t20Step4U_of_visitedU`: the proof of `dddf_t20_step4_of_visited`
  (`LQGMetric/Papers/DDDF/T20BStep4.lean`; `η → 0` removes the unvisited blocks, no new
  constants).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

/-- the constant `A₀ = log(2D) + 1 + 4(3 + (4(l+1)/c_r)²)` of the asymptotic step of
`dddf_t20_step4_visited_of_pathwise` (`LQGMetric/Papers/DDDF/T20CMain.lean`), with
`D = 26 C₀ (max(M_X, 0) + 1) C_Λ²` and `l = 12β` -/
def visA0 (β C₀ MX CΛ cr : ℝ) : ℝ :=
  Real.log (2 * (C₀ * (max MX 0 + 1) * 26 * CΛ ^ 2)) + 1 +
    4 * (3 + (4 * (2 * (6 * β) + 1) / cr) ^ 2)

/-- the constant `B₃ = 4 (4(log(l C₀ C_r + 1) + log 4)/c_r)^{2/3}`, `l = 12β`, of the
asymptotic step of `dddf_t20_step4_visited_of_pathwise` -/
def visB3 (β C₀ Cr cr : ℝ) : ℝ :=
  4 * (4 * (Real.log (2 * (6 * β) * C₀ * Cr + 1) + Real.log 4) / cr) ^ ((2 : ℝ) / 3)

lemma visB3_nonneg {β C₀ Cr cr : ℝ} (hβ : 0 < β) (hC₀ : 0 < C₀) (hCr : 0 < Cr)
    (hcr : 0 < cr) : 0 ≤ visB3 β C₀ Cr cr := by
  unfold visB3
  have hl0 : 0 < 2 * (6 * β) := by positivity
  have ha₁ : 0 ≤ Real.log (2 * (6 * β) * C₀ * Cr + 1) :=
    Real.log_nonneg (by nlinarith [mul_pos (mul_pos hl0 hC₀) hCr])
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num)
    (add_nonneg ha₁ (Real.log_nonneg (by norm_num)))) hcr.le) _)

section Visited

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

open T20C in
/-- **DDDF (5.65)–(5.67), visited blocks, with explicit constants** (the proof of
`dddf_t20_step4_visited_of_pathwise`, `LQGMetric/Papers/DDDF/T20CMain.lean`,
`tightness.tex` l. 1156–1172, with every input constant as a parameter). -/
theorem t20Step4VisitedAt_of (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ : ℝ}
    {α c : ℝ} (hα : 1 < α) {K₁ : ℕ}
    (hTη : ∀ η : ℝ, 0 < η → ∃ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ ∧
      ∀ K : ℕ, K₁ ≤ K → ∀ n : ℕ, K ≤ n →
        (∫⁻ ω, ENNReal.ofReal
            (T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) (γ n ω) ^ α) ∂P) ^ (1 / α) ≤
          ENNReal.ofReal (Real.exp (-(c * K))))
    {C₀ : ℝ} (hC₀ : 0 < C₀) {d K₂ : ℕ} (hpath : T20Step4PathwiseAt ξ Q W P C₀ d K₂)
    {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4) {Cr cr : ℝ} (hCr : 0 < Cr) (hcr : 0 < cr)
    (hRp : ∀ q : ℝ, 0 < q → ∀ (K n : ℕ), K ≤ n → ∀ (J J' : Finset (Circle × ℂ))
      (hJ : J.Nonempty) (hJ' : J'.Nonempty),
      ∫⁻ ω, ENNReal.ofReal (lsRatio ξ W P K n J J' hJ hJ' ω ^ q) ∂P ≤
        ENNReal.ofReal (LambdaN ξ W P (n - K) (ENNReal.ofReal p) ^ q *
          (Real.exp (2 * q * T20B.tailX0 (2 * q) (J.card + J'.card) Cr cr) + 1)))
    {CΛ : ℝ} (hCΛ : 0 < CΛ)
    (hΛ : ∀ n : ℕ, LambdaN ξ W P n (ENNReal.ofReal p) ≤
      CΛ * LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)))
    {MX : ℝ} (hXm : AEMeasurable (Xbig Q W P) P)
    (hMX : ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * (α / (α - 1)) * C₀ * Xbig Q W P ω)) ∂P ≤
      ENNReal.ofReal MX)
    {cO KO : ℝ}
    (hO : ∀ (n : ℕ) (Y : ℂ → Ω → ℝ), (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ n)⁻¹ 1 x) →
      (∀ ω, ContDiff ℝ 1 fun x => Y x ω) → ∀ c₁ : ℂ,
      AEMeasurable (fun ω => ((2 : ℝ) ^ n)⁻¹ *
        ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖) P ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * (α / (α - 1)) * C₀ * (n : ℝ) ^ Q.ε₀ *
        (((2 : ℝ) ^ n)⁻¹ * ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖))) ∂P ≤
        ENNReal.ofReal (Real.exp (cO * (n : ℝ) ^ (1 / 2 + Q.ε₀) + KO * (n : ℝ) ^ (2 * Q.ε₀))))
    {K₃ : ℕ} (hK₃ : ∀ K : ℕ, K₃ ≤ K → visA0 (α / (α - 1)) C₀ MX CΛ cr + d * Real.log (K + 1) +
      |cO| * (K : ℝ) ^ (1 / 2 + Q.ε₀) + |KO| * (K : ℝ) ^ (2 * Q.ε₀) +
      visB3 (α / (α - 1)) C₀ Cr cr * (K : ℝ) ^ ((2 : ℝ) / 3) ≤ c / 2 * K) :
    T20Step4VisitedAt ξ Q W P p (c / 2) (max (max K₁ K₂) (max K₃ 1)) := by
  have := hW.isProbabilityMeasure
  set β : ℝ := α / (α - 1) with hβ
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := div_pos hα0 (by linarith)
  have hβ1 : 1 ≤ β := by rw [hβ, le_div_iff₀ (by linarith)]; linarith
  set t : ℝ := (3 * β)⁻¹ with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  set MX' : ℝ := max MX 0 with hMX'
  have hMX'0 : 0 ≤ MX' := le_max_right _ _
  set l : ℝ := 2 * (6 * β) with hl
  set a₁ : ℝ := Real.log (l * C₀ * Cr + 1)
  set D : ℝ := C₀ * (MX' + 1) * 26 * CΛ ^ 2 with hD
  have hD0 : 0 < D := by positivity
  set A0 : ℝ := Real.log (2 * D) + 1 + 4 * (3 + (4 * (l + 1) / cr) ^ 2)
  have hl0 : 0 < l := by positivity
  have ha₁ : 0 ≤ a₁ := Real.log_nonneg (by nlinarith [mul_pos (mul_pos hl0 hC₀) hCr])
  set B3 : ℝ := 4 * (4 * (a₁ + Real.log 4) / cr) ^ ((2 : ℝ) / 3)
  replace hK₃ : ∀ K : ℕ, K₃ ≤ K → A0 + d * Real.log (K + 1) + |cO| * (K : ℝ) ^ (1 / 2 + Q.ε₀) +
      |KO| * (K : ℝ) ^ (2 * Q.ε₀) + B3 * (K : ℝ) ^ ((2 : ℝ) / 3) ≤ c / 2 * K := hK₃
  intro K hK n hn
  have hK1' : K₁ ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hK2' : K₂ ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hK3' : K₃ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hK1 : 1 ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  obtain ⟨s, hσ, J, J', hJ, hJ', hcard, hP⟩ := hpath K hK2' n hn
  refine ⟨s, hσ, ?_⟩
  -- the target `B = e^{-cK/2} Λ_{n-K}(ψ,p/2)²`
  set Λψ : ℝ := LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2))
  set Λφ : ℝ := LambdaN ξ W P (n - K) (ENNReal.ofReal p)
  have hQ2 : ENNReal.ofReal p ≤ 2⁻¹ := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hΛφ : 0 < Λφ := T20B.LambdaN_pos hW (ENNReal.ofReal_pos.2 hp) hQ2 _
  have hΛφψ : Λφ ≤ CΛ * Λψ := hΛ (n - K)
  have hΛψ : 0 < Λψ := by
    by_contra h; have := not_lt.1 h; nlinarith
  set B : ℝ := Real.exp (-(c / 2 * K)) * Λψ ^ 2 with hB
  have hB0 : 0 < B := by positivity
  set η₀ : ℝ := min 1 (B / (2 * C₀ * 4 ^ K))
  refine ⟨η₀, lt_min one_pos (by positivity), fun η hη hηη => ?_⟩
  obtain ⟨γ, hγ, hTK⟩ := hTη η hη
  refine ⟨γ, hγ, ?_⟩
  obtain ⟨Y, -, hY, -, hYc, -⟩ := exists_C1_modification_phi hW
    (a := ((2 : ℝ) ^ K)⁻¹) (b := 1) (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hPz := hP η hη ((hηη.trans (min_le_left _ _))) γ hγ Y hY hYc
  have hKn : K ≤ n := hn
  -- measurability of the four factors
  have hRm := measurable_condTRatio hW Q hγ K n
  have hSm := measurable_lsRatio hW ξ hKn J J' hJ hJ'
  have hOm : AEMeasurable (fun ω => C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω) P :=
    (aemeasurable_sup'_fun offs_nonempty fun c₁ _ => (hO K Y hY hYc c₁).1).const_mul _
  have hXm' : AEMeasurable (Xbig Q W P) P := hXm
  set F : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x ω)
    (γ n ω) * Real.exp (C₀ * Xbig Q W P ω) * Real.exp (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω) *
      lsRatio ξ W P K n J J' hJ hJ' ω ^ 2) with hF
  have hFm : AEMeasurable F P :=
    ((((hRm.aemeasurable.mul ((hXm'.const_mul C₀).exp)).mul hOm.exp).mul
      (hSm.aemeasurable.pow_const 2))).ennreal_ofReal
  set AK : ℝ := C₀ * ((K : ℝ) + 1) ^ d with hAK
  have hAK0 : 0 ≤ AK := by positivity
  have hpt : ∀ z : Ω × Ω, ENNReal.ofReal (C₀ * ((K : ℝ) + 1) ^ d * Real.exp (C₀ * Xbig Q W P z.1) *
      Real.exp (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y z.1) * lsRatio ξ W P K n J J' hJ hJ' z.1 ^ 2 *
      T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x z.1) (γ n z.1)) =
      ENNReal.ofReal AK * F z.1 := fun z => by
    rw [hF, ← ENNReal.ofReal_mul hAK0]; congr 1; ring
  have hmp := measurePreserving_fst (μ := P) (ν := P)
  have hFP : ∫⁻ z, F z.1 ∂(P.prod P) = ∫⁻ ω, F ω ∂P := by
    conv_rhs => rw [← hmp.map_eq]
    rw [lintegral_map' (by rw [hmp.map_eq]; exact hFm) measurable_fst.aemeasurable]
  -- Hölder
  have hH := holder_step (P := P) hα hβ (R := fun ω => T20.condTRatio ξ K
      (fun x => psiMN Q W P 0 K x ω) (γ n ω)) (X := Xbig Q W P)
    (O := fun ω => C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω) (S := lsRatio ξ W P K n J J' hJ hJ')
    (fun ω => condTRatio_nonneg _ _ _ _) (fun ω => lsRatio_nonneg _ _ _ _ _ _ _ _)
    hRm.aemeasurable hXm' hOm hSm.aemeasurable (C₀ := C₀)
  -- the four moments
  have h1 := hTK K hK1' n hn
  have h2 : (∫⁻ ω, ENNReal.ofReal (Real.exp (3 * β * C₀ * Xbig Q W P ω)) ∂P) ^ t ≤
      ENNReal.ofReal MX' ^ t :=
    ENNReal.rpow_le_rpow (hMX.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) ht0
  set E : ℝ := Real.exp (cO * (K : ℝ) ^ (1 / 2 + Q.ε₀) + KO * (K : ℝ) ^ (2 * Q.ε₀)) with hE
  have hI3 : ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * β * (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω))) ∂P ≤
      ENNReal.ofReal (25 * E) := by
    set Oc : ℂ → Ω → ℝ := fun c₁ ω => ((2 : ℝ) ^ K)⁻¹ *
      ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun x => Y (x + c₁) ω) z‖ with hOc
    have hpt3 : ∀ ω, ENNReal.ofReal (Real.exp (3 * β * (C₀ * (K : ℝ) ^ Q.ε₀ * Obig K Y ω))) ≤
        ∑ c₁ ∈ offs, ENNReal.ofReal (Real.exp (3 * β * C₀ * (K : ℝ) ^ Q.ε₀ * Oc c₁ ω)) := by
      intro ω
      obtain ⟨c₁, hc₁, he⟩ := Finset.exists_mem_eq_sup' offs_nonempty (fun c₁ => Oc c₁ ω)
      have e : Obig K Y ω = Oc c₁ ω := he
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun c₁ =>
        ENNReal.ofReal (Real.exp (3 * β * C₀ * (K : ℝ) ^ Q.ε₀ * Oc c₁ ω)))
        (fun _ _ => zero_le) hc₁)
      rw [e]; congr 2; ring
    calc _ ≤ ∫⁻ ω, ∑ c₁ ∈ offs, ENNReal.ofReal (Real.exp (3 * β * C₀ * (K : ℝ) ^ Q.ε₀ *
          Oc c₁ ω)) ∂P := lintegral_mono hpt3
      _ = ∑ c₁ ∈ offs, ∫⁻ ω, ENNReal.ofReal (Real.exp (3 * β * C₀ * (K : ℝ) ^ Q.ε₀ *
          Oc c₁ ω)) ∂P := lintegral_finsetSum' _ fun c₁ _ =>
            (Real.measurable_exp.comp_aemeasurable
              ((hO K Y hY hYc c₁).1.const_mul _)).ennreal_ofReal
      _ ≤ ∑ c₁ ∈ offs, ENNReal.ofReal E := Finset.sum_le_sum fun c₁ _ => (hO K Y hY hYc c₁).2
      _ = (offs.card : ℝ≥0∞) * ENNReal.ofReal E := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 25 * ENNReal.ofReal E := by
          gcongr; exact_mod_cast card_offs_le
      _ = ENNReal.ofReal (25 * E) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have h3 := ENNReal.rpow_le_rpow hI3 ht0
  set x₀ : ℝ := T20B.tailX0 (2 * (6 * β)) (J.card + J'.card) Cr cr with hx₀
  set MS : ℝ := Λφ ^ (6 * β) * (Real.exp (2 * (6 * β) * x₀) + 1) with hMS
  have h4 := ENNReal.rpow_le_rpow (z := t) (hRp (6 * β) (by positivity) K n hKn J J' hJ hJ') ht0
  have hMS0 : 0 ≤ MS := by positivity
  have hE0 : 0 ≤ 25 * E := by positivity
  have hZ : ∫⁻ ω, F ω ∂P ≤ ENNReal.ofReal (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t *
      MS ^ t) := by
    refine hH.trans ((mul_le_mul' (mul_le_mul' (mul_le_mul' h1 h2) h3) h4).trans (le_of_eq ?_))
    rw [ENNReal.ofReal_rpow_of_nonneg hMX'0 ht0, ENNReal.ofReal_rpow_of_nonneg hE0 ht0,
      ENNReal.ofReal_rpow_of_nonneg hMS0 ht0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  -- the real inequality (absorbing the sub-exponential factors)
  have hreal : AK * (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t * MS ^ t) ≤ B / 2 := by
    set E' : ℝ := Real.exp (|cO| * (K : ℝ) ^ (1 / 2 + Q.ε₀) + |KO| * (K : ℝ) ^ (2 * Q.ε₀))
      with hE'
    have hEE' : E ≤ E' := Real.exp_le_exp.2 (add_le_add
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
    have hE'1 : 1 ≤ E' := Real.one_le_exp (by positivity)
    have hx0 : 0 ≤ x₀ := le_trans (by norm_num) (le_max_left _ _)
    have hx : x₀ ≤ 3 + (4 * (l + 1) / cr) ^ 2 +
        (4 * (a₁ + Real.log 4) / cr) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((2 : ℝ) / 3) :=
      tailX0_le (l := 2 * (6 * β)) (C := Cr) (c := cr) (C₀ := C₀) (N := (J.card : ℝ) + J'.card)
        (by positivity) hCr hcr hC₀ (by positivity) hK1 hcard
    have hasy := hK₃ K hK3'
    have hA0 : A0 = Real.log (2 * D) + 1 + 4 * (3 + (4 * (l + 1) / cr) ^ 2) := rfl
    have hB3' : B3 * (K : ℝ) ^ ((2 : ℝ) / 3) =
        4 * ((4 * (a₁ + Real.log 4) / cr) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((2 : ℝ) / 3)) := by
      show 4 * (4 * (a₁ + Real.log 4) / cr) ^ ((2 : ℝ) / 3) * (K : ℝ) ^ ((2 : ℝ) / 3) = _
      ring
    have hlE : Real.log E' = |cO| * (K : ℝ) ^ (1 / 2 + Q.ε₀) + |KO| * (K : ℝ) ^ (2 * Q.ε₀) :=
      Real.log_exp _
    have hkey : Real.log (2 * D) + d * Real.log (K + 1) + 1 + 4 * x₀ + Real.log E' ≤
        c / 2 * K := by
      rw [hlE]; linarith
    have := final_real (β := β) (d := d) hβ1 hMX'0 hE0 hEE' hE'1 hΛφ hΛψ hCΛ hΛφψ hx0 hC₀
      (Nat.cast_nonneg K) hD hkey
    exact this
  have hηt : C₀ * 4 ^ K * η ^ 2 ≤ B / 2 := by
    have hηB : η ≤ B / (2 * C₀ * 4 ^ K) := hηη.trans (min_le_right _ _)
    have hη1 : η ≤ 1 := hηη.trans (min_le_left _ _)
    have hsq : η ^ 2 ≤ η := by nlinarith
    have h4K : (0 : ℝ) < C₀ * 4 ^ K := by positivity
    calc C₀ * 4 ^ K * η ^ 2 ≤ C₀ * 4 ^ K * (B / (2 * C₀ * 4 ^ K)) :=
          mul_le_mul_of_nonneg_left (hsq.trans hηB) h4K.le
      _ = B / 2 := by field_simp
  calc _ ≤ ∫⁻ z, ∑ b ∈ T20B.nearIdx K, (visSet γ n K b s).indicator
        (fun z => ENNReal.ofReal (incr ξ Q W P K n b z ^ 2)) z ∂(P.prod P) :=
        sum_lintegral_le _ _
    _ ≤ ∫⁻ z, (ENNReal.ofReal (C₀ * 4 ^ K * η ^ 2) + ENNReal.ofReal AK * F z.1) ∂(P.prod P) :=
        lintegral_mono_ae (hPz.mono fun z hz => hz.trans (le_of_eq (by rw [hpt z])))
    _ = ENNReal.ofReal (C₀ * 4 ^ K * η ^ 2) + ENNReal.ofReal AK * ∫⁻ ω, F ω ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hFP]
    _ ≤ ENNReal.ofReal (B / 2) + ENNReal.ofReal AK * ENNReal.ofReal
        (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t * MS ^ t) :=
        add_le_add (ENNReal.ofReal_le_ofReal hηt) (mul_le_mul_of_nonneg_left hZ zero_le)
    _ = ENNReal.ofReal (B / 2) + ENNReal.ofReal
        (AK * (Real.exp (-(c * K)) * MX' ^ t * (25 * E) ^ t * MS ^ t)) := by
        rw [ENNReal.ofReal_mul hAK0]
    _ ≤ ENNReal.ofReal (B / 2) + ENNReal.ofReal (B / 2) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hreal)
    _ = ENNReal.ofReal B := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

open T20B in
/-- **Step 4 reduced to the visited blocks, with explicit constants** (the proof of
`dddf_t20_step4_of_visited`, `LQGMetric/Papers/DDDF/T20BStep4.lean`): the constants pass through
unchanged. -/
theorem t20Step4At_of_visitedAt (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ p C₂ : ℝ} {K₀ : ℕ}
    (hV : T20Step4VisitedAt ξ Q W P p C₂ K₀) : T20Step4At ξ Q W P p C₂ K₀ := by
  have := hW.isProbabilityMeasure
  intro K hK0 n hn
  obtain ⟨s, hσ, η₀, hη₀, hη⟩ := hV K hK0 n hn
  set N : ℝ := ((nearIdx K).card : ℝ)
  set B : ℝ := Real.exp (-(C₂ * K)) * LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2
  have hB0 : 0 ≤ B := by positivity
  set f : ℤ × ℤ → Ω × Ω → ℝ := fun b z => max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 -
    blkKn Q W P K n b x z.1 + blkKn Q W P K n b x z.2) -
      L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 ^ 2
  have hf0 : ∀ b z, 0 ≤ f b z := fun b z => sq_nonneg _
  -- for every admissible `η`
  have key : ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∑ b ∈ nearIdx K, ∫ z, f b z ∂(P.prod P) ≤ B + N * Real.log (1 + η) ^ 2 := by
    intro η hη0 hηη
    obtain ⟨γ, hγ, hsum⟩ := hη η hη0 hηη
    have hl0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
    have hb : ∀ b ∈ nearIdx K, ∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P) ≤
        ∫⁻ z, {z : Ω × Ω | ∃ t ∈ Icc (0 : ℝ) 1, γ n z.1 t ∉ farSet (hoBlock K b) s}.indicator
          (fun z => ENNReal.ofReal (f b z)) z ∂(P.prod P) +
          ENNReal.ofReal (Real.log (1 + η) ^ 2) := by
      intro b _
      have hc : ENNReal.ofReal (Real.log (1 + η) ^ 2) =
          ∫⁻ _z, ENNReal.ofReal (Real.log (1 + η) ^ 2) ∂(P.prod P) := by
        rw [lintegral_const, measure_univ, mul_one]
      rw [hc, ← lintegral_add_right _ measurable_const]
      refine lintegral_mono_ae ?_
      filter_upwards [dddf_t20_step4_far hW Q ξ hn hσ b hη0.le hγ] with z hz
      by_cases hv : z ∈ {z : Ω × Ω | ∃ t ∈ Icc (0 : ℝ) 1, γ n z.1 t ∉ farSet (hoBlock K b) s}
      · rw [indicator_of_mem hv]; exact le_self_add
      · rw [indicator_of_notMem hv, zero_add]
        simp only [mem_ofPred_eq, not_exists, not_and, not_not] at hv
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hz hv
        have h2 : 0 ≤ max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          blkKn Q W P K n b x z.1 + blkKn Q W P K n b x z.2) -
            L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 := le_max_right _ _
        exact pow_le_pow_left₀ h2 h1 2
    have hfin : ∑ b ∈ nearIdx K, ∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P) ≤
        ENNReal.ofReal B + ENNReal.ofReal (N * Real.log (1 + η) ^ 2) := by
      calc _ ≤ ∑ b ∈ nearIdx K, (∫⁻ z, {z : Ω × Ω | ∃ t ∈ Icc (0 : ℝ) 1,
              γ n z.1 t ∉ farSet (hoBlock K b) s}.indicator
              (fun z => ENNReal.ofReal (f b z)) z ∂(P.prod P) +
              ENNReal.ofReal (Real.log (1 + η) ^ 2)) := Finset.sum_le_sum hb
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          congr 1
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ ≤ _ := add_le_add_left hsum _
    have hne : ENNReal.ofReal B + ENNReal.ofReal (N * Real.log (1 + η) ^ 2) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    calc ∑ b ∈ nearIdx K, ∫ z, f b z ∂(P.prod P)
        ≤ ∑ b ∈ nearIdx K, (∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P)).toReal :=
          Finset.sum_le_sum fun b _ => integral_le_toReal_lintegral (hf0 b)
      _ = (∑ b ∈ nearIdx K, ∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P)).toReal := by
          rw [ENNReal.toReal_sum fun b _ => ne_top_of_le_ne_top hne
            ((Finset.single_le_sum (f := fun b => ∫⁻ z, ENNReal.ofReal (f b z) ∂(P.prod P))
              (fun _ _ => bot_le) ‹_›).trans hfin)]
      _ ≤ (ENNReal.ofReal B + ENNReal.ofReal (N * Real.log (1 + η) ^ 2)).toReal :=
          ENNReal.toReal_mono hne hfin
      _ = B + N * Real.log (1 + η) ^ 2 := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hB0, ENNReal.toReal_ofReal (by positivity)]
  -- `η → 0`
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set η : ℝ := min η₀ (min 1 (ε / (N + 1)))
  have hη0 : 0 < η := lt_min hη₀ (lt_min one_pos (by positivity))
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε / (N + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hl : Real.log (1 + η) ≤ η := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + η by linarith); linarith
  have hl0 : 0 ≤ Real.log (1 + η) := Real.log_nonneg (by linarith)
  have hsq : Real.log (1 + η) ^ 2 ≤ η := by nlinarith
  have hNe : N * η < ε := by
    have h1 : N * η ≤ N * (ε / (N + 1)) := mul_le_mul_of_nonneg_left hηε hN
    have h2 : N * (ε / (N + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  calc _ ≤ B + N * Real.log (1 + η) ^ 2 := key η hη0 (min_le_left _ _)
    _ < B + ε := by nlinarith [mul_le_mul_of_nonneg_left hsq hN]

end Visited

/-- **DDDF Theorem 20, Step 4 for the visited blocks, uniform in `ξ ∈ (0, ξs]` and in the white
noise** (ledger U9, uniform `dddf_t20_step4_visited_of_pathwise`): from the uniform Condition (T)
(U8), the uniform pathwise bound (U0) and the uniform Cor 17 and Prop 18 (U5, U6). All constants
are chosen before the probability space and before `ξ`; the threshold of `T20C.asymp` is
evaluated once at the uniform inputs (Recipe E). -/
theorem t20_step4_visited_of_pathwise_unif (Q : PsiParams) (hε : Q.ε₀ < 1 / 2) {ξs : ℝ}
    (hT : ConditionTUAll.{0} ξs Q) (hA : T20Step4PathwiseU.{0} ξs Q) (h17 : IfaceCor17U ξs)
    (h18 : IfaceProp18U ξs) : T20Step4VisitedU ξs Q := by
  obtain ⟨α, hα, c, hc, K₁, hT⟩ := hT
  obtain ⟨C₀, hC₀, d, K₂, hpath⟩ := hA
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < α / (α - 1) := div_pos hα0 (by linarith)
  obtain ⟨p₀, hp₀, hR⟩ := t20_ratio_moment_unif h17 h18
  obtain ⟨MX, hMX⟩ := expMoment_XAB_shift_W Q T20C.cBig 5 5 (l := 3 * (α / (α - 1)) * C₀)
    (by positivity)
  obtain ⟨cO, KO, hO⟩ := T20C.prop3_expMoment_shift Q.ε₀_pos (a := 3 * (α / (α - 1)) * C₀)
    (by positivity)
  refine ⟨min p₀ (1 / 4), lt_min hp₀ (by norm_num), fun p hp hpp => ?_⟩
  have hp4 : p ≤ 1 / 4 := hpp.trans (min_le_right _ _)
  obtain ⟨Cr, cr, hCr, hcr, hRp⟩ := hR p hp (hpp.trans (min_le_left _ _))
  obtain ⟨CΛ, hCΛ, hΛ⟩ := LambdaN_le_LambdaNPsi_unif Q ξs hp (by linarith)
  obtain ⟨K₃, hK₃⟩ := T20C.asymp hc Q.ε₀_pos hε (visA0 (α / (α - 1)) C₀ MX CΛ cr) |cO| |KO|
    (visB3 (α / (α - 1)) C₀ Cr cr) d (abs_nonneg _) (abs_nonneg _)
    (visB3_nonneg hβ0 hC₀ hCr hcr)
  refine ⟨c / 2, by positivity, max (max K₁ K₂) (max K₃ 1), fun {Ω} _ {P} {W} hW ξ hξ => ?_⟩
  exact t20Step4VisitedAt_of hW Q hα (hT hW ξ hξ) hC₀ (hpath hW ξ hξ) hp hp4 hCr hcr
    (fun q hq K n hKn J J' hJ hJ' => hRp hW ξ hξ q hq K n hKn J J' hJ hJ' Prod.fst Prod.fst
      Prod.snd Prod.snd) hCΛ (hΛ hW ξ hξ) (hMX hW).1 (hMX hW).2 (hO hW) hK₃

/-- **Step 4 of DDDF Theorem 20, uniform** (ledger U0, `T20Step4U`): from the uniform visited-block
bound; the constants pass through unchanged. -/
theorem t20Step4U_of_visitedU {ξs : ℝ} {Q : PsiParams} (hV : T20Step4VisitedU ξs Q) :
    T20Step4U ξs Q := by
  obtain ⟨p₀, hp₀, hV⟩ := hV
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C₂, hC₂, K₀, hV⟩ := hV p hp hpp
  exact ⟨C₂, hC₂, K₀, fun {Ω} _ {P} {W} hW ξ hξ => t20Step4At_of_visitedAt hW Q (hV hW ξ hξ)⟩

end Uniform
end GaussianLQG
