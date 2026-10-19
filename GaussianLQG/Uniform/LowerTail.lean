import GaussianLQG.Uniform.RSW.Psi
import GaussianLQG.Uniform.Interfaces
import LQGMetric.Papers.DDDF.C17

/-!
# Lower tails with constants uniform in `ξ`: DDDF Prop 16 and Cor 17 (Route U, item U5)

Phase B, packet PB-U5 (ledger packets B-1a, part, and B-2). Mathematical source: the
uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`, statements U0 and U5, constant
ledger §`subsec:ledger-lower`, Recipes M, R, X and §OP-3. Templates (not edited):
`p16_generic`, `dddf_prop16` (`LQGMetric/Papers/DDDF/P16.lean`) and `dddf_cor17` (`C17.lean`):
DDDF20 (arXiv:1904.08021 v2) Proposition 16, (4.42), and Corollary 17, (4.48).

Every statement is in the ledger's U-form: the constants come before the probability space
`(Ω, P, W)` and before `ξ ∈ (0, ξs]`.

* `c8At_mono`: Cor 8 in the form `C8At` is monotone in its constant `C₀ ≥ 1` (Recipe M; ledger
  B-1a). `C8AtU ξs Q` (ledger U0) is `C8At` for the fields `ψ_{0,n}` with one constant `C₀ ≥ 1`
  chosen before `Ω` and `ξ`; `c8AtU` proves it from the uniform (3.38),
  `psi_rsw_low_quantile_unif_all` at `(A, B) = (1, 3)`.
* `p16_generic_unif`: `p16_generic` with its existential moved in front of `Ω`, `P` and `ξ`
  (Recipe X). Its witnesses `p₀ = q₀/C₀`, `(C, c)` of `tail_of_levels` depend on `C₀` only; the
  proof is the template's (`tail_of_levels` and `p16_level`, which takes `C₀` as a parameter).
* `prop16_unif` (ledger U5, first statement): `p16_generic_unif` at the uniform constant of
  `C8AtU`, with (4.44) from `prob_33_le_sq` (no constants).
* `cor17_core`: the proof of `dddf_cor17` at one noise, one `ξ` and one level `p`, with every
  constant a parameter. It uses exactly the four facts of the ledger: `c ≤ c₅/(4ξ²)`,
  `c ≤ c₁/16`, `C₅ + C₁ ≤ C` and `e^{c(4ξM)²} ≤ C`.
* `cor17_unif` (ledger U5, second statement): `cor17_core` with `(p₁, C₁, c₁)` from
  `prop16_unif` at `psiQ₀`, `(C₅, c₅)` from `dddf_prop5_XAB_W`, `(C', c')` from
  `exists_tail_XAB_unif_W` (both before `Ω`), and the ledger's witnesses
  `p₀ = min(p₁/2, 1/4)`, `M = √(max 1 (log(C'/p))/c')`, `c* = min(c₅/(4ξs²), c₁/16)`,
  `C* = (C₅ + C₁ + 1) e^{4c₅M²}`. Since `c*(4ξM)² ≤ 4c₅M²` for `ξ ≤ ξs`, the four facts hold
  for every `ξ ∈ (0, ξs]` (Recipe R).
* `ifaceCor17U`: the interface `IfaceCor17U ξs` of `GaussianLQG/Uniform/Interfaces.lean`.

Aliases with the names of the ledger's packet plan and §OP-3 (`prop16_unif_all`,
`cor17_unif_all`) and per-noise corollaries (`prop16_unif_noise`, `cor17_unif_noise`) are
included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

/-! ### Cor 8 in the form `C8At`: monotonicity in the constant and the uniform predicate -/

/-- **`C8At` is monotone in its constant `C₀ ≥ 1`** (ledger B-1a, Recipe M, Finding fd:C1): the
level `ε/C₀` decreases and the factor `C₀ e^{C₀ √|log(ε/C₀)|}` increases with `C₀`. -/
theorem c8At_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℝ} {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) {C₀ C₁ : ℝ} (hC₀ : 1 ≤ C₀) (hC : C₀ ≤ C₁)
    (h : C8At ξ P Y C₀) : C8At ξ P Y C₁ := by
  intro a b a' b' ha hb ha' hb' ε hε hε2
  have hC₀0 : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le hC₀0 hC
  have hdiv : ε / C₁ ≤ ε / C₀ := div_le_div_of_nonneg_left hε.le hC₀0 hC
  have hlt : ε / C₀ < 1 := by rw [div_lt_one hC₀0]; linarith
  have hlev : ellQ ξ P Y (rectAB a' b') (ENNReal.ofReal (ε / C₁)) ≤
      ellQ ξ P Y (rectAB a' b') (ENNReal.ofReal (ε / C₀)) :=
    ellQ_mono _ (ENNReal.ofReal_pos.2 (div_pos hε hC₁0))
      (by rw [ENNReal.ofReal_lt_one]; exact hlt) (ENNReal.ofReal_le_ofReal hdiv)
  have hℓ : 0 ≤ ellQ ξ P Y (rectAB a b) (ENNReal.ofReal ε) :=
    ellQ_nonneg hYc hYm _ (ENNReal.ofReal_pos.2 hε) (by rw [ENNReal.ofReal_lt_one]; linarith)
  have hlog : |Real.log (ε / C₀)| ≤ |Real.log (ε / C₁)| := by
    have hn0 : Real.log (ε / C₀) < 0 := Real.log_neg (div_pos hε hC₀0) hlt
    have hn1 : Real.log (ε / C₁) ≤ Real.log (ε / C₀) := Real.log_le_log (div_pos hε hC₁0) hdiv
    rw [abs_of_neg hn0, abs_of_neg (hn1.trans_lt hn0)]
    linarith
  have hexp : Real.exp (C₀ * √|Real.log (ε / C₀)|) ≤ Real.exp (C₁ * √|Real.log (ε / C₁)|) :=
    Real.exp_le_exp.2 (mul_le_mul hC (Real.sqrt_le_sqrt hlog) (Real.sqrt_nonneg _) hC₁0.le)
  calc _ ≤ _ := hlev
    _ ≤ _ := h a b a' b' ha hb ha' hb' ε hε hε2
    _ ≤ C₁ * ellQ ξ P Y (rectAB a b) (ENNReal.ofReal ε) * Real.exp (C₁ * √|Real.log (ε / C₁)|) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hC hℓ) hexp (Real.exp_pos _).le
          (mul_nonneg hC₁0.le hℓ)

/-- **Ledger U0 `C8AtU`**: DDDF Corollary 8, (3.38), in the form `C8At` (shapes in `[1,3]²`) for
the fields `ψ_{0,n}` with parameters `Q`, with one constant `C₀ ≥ 1` chosen before the
probability space, the white noise and `ξ ∈ (0, ξs]`. -/
def C8AtU (ξs : ℝ) (Q : PsiParams) : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
    IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ n : ℕ, C8At ξ P (psiMN Q W P 0 n) C₀

/-- the uniform predicate `C8AtU` holds for every `ξs > 0` and every `Q`: the uniform (3.38),
`psi_rsw_low_quantile_unif_all`, at `(A, B) = (1, 3)` -/
theorem c8AtU {ξs : ℝ} (hξs : 0 < ξs) (Q : PsiParams) : C8AtU.{u} ξs Q := by
  obtain ⟨C₀, hC₀1, hC8⟩ := psi_rsw_low_quantile_unif_all.{u} hξs Q (A := 1) (B := 3) one_pos
    (by norm_num)
  exact ⟨C₀, hC₀1, fun hW ξ hξ n a b a' b' ha hb ha' hb' ε hε hε2 =>
    hC8 hW ξ hξ a b a' b' ha hb ha' hb' n ε hε hε2⟩

/-! ### Proposition 16 -/

/-- **`p16_generic` with its constants before the probability space and before `ξ`** (ledger
U5, Recipe X; template `p16_generic`, whose existential sits after `Ω`, `P` and `ξ`): the
witnesses `p₀ = q₀/C₀` and `(C, c)` of `tail_of_levels` depend on `C₀` only. Same proof. -/
theorem p16_generic_unif {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ p₀ C c : ℝ, 0 < p₀ ∧ 0 < C ∧ 0 < c ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      [IsProbabilityMeasure P] (ξ : ℝ) (Y : ℂ → Ω → ℝ),
      (∀ ω, Continuous fun x => Y x ω) → (∀ x, Measurable (Y x)) → C8At ξ P Y C₀ →
      (∀ m : ℝ, P {ω | lenObs ξ Y (rectAB 3 3) ω ≤ m} ≤
        P {ω | lenObs ξ Y (rectAB 1 3) ω ≤ m} ^ 2) →
      ∀ p s : ℝ, 0 < p → p ≤ p₀ → 0 < s →
      P {ω | lenObs ξ Y (rectAB 1 3) ω ≤
          Real.exp (-s) * ellQ ξ P Y (rectAB 1 1) (ENNReal.ofReal p)} ≤
        ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  obtain ⟨hθ0, hθ4, -⟩ := p16Theta_facts hC₀
  obtain ⟨C, c, hC, hc, ht⟩ := tail_of_levels (L := Real.log (p16K C₀)) (B := C₀⁻¹)
    (p16M_pos hC₀) (inv_nonneg.2 hC₀.le) hθ0.le hθ4
  exact ⟨p16Q C₀ 0 / C₀, C, c, div_pos (p16Q_facts hC₀ 0).1 hC₀, hC, hc,
    fun ξ Y hYc hYm hC8 hsq p s hp hpp hs => ht s _ hs prob_le_one fun i hi =>
      p16_level hYc hYm hC₀ hC8 hsq hp hpp hi⟩

/-- **DDDF Proposition 16, uniform in `ξ` and in the white noise** (ledger U5, first statement;
template `dddf_prop16`): for `r₀` small (`PsiSmall Q`) there are `p₀, C, c > 0`, chosen before
the probability space and before `ξ`, such that for every white noise, every `ξ ∈ (0, ξs]`,
`n ≥ 0`, `p ∈ (0, p₀]` and `s > 0`,
`P(L^{(n)}_{1,3}(ψ) ≤ e^{-s} ℓ_n(ψ, p)) ≤ C e^{-cs²}`. -/
theorem prop16_unif (ξs : ℝ) (hξs : 0 < ξs) (Q : PsiParams) (hQ : PsiSmall Q) :
    ∃ p₀ C c : ℝ, 0 < p₀ ∧ 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (p s : ℝ), 0 < p → p ≤ p₀ → 0 < s →
        P {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
            Real.exp (-s) * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  obtain ⟨C₀, hC₀1, hC8⟩ := c8AtU.{u} hξs Q
  obtain ⟨p₀, C, c, hp₀, hC, hc, h⟩ := p16_generic_unif.{u} (lt_of_lt_of_le one_pos hC₀1)
  refine ⟨p₀, C, c, hp₀, hC, hc, fun {Ω} _ {P} {W} hW ξ hξ n p s hp hpp hs => ?_⟩
  have := hW.isProbabilityMeasure
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  exact h ξ (psiMN Q W P 0 n) hψ.cont hψ.meas (hC8 hW ξ hξ n) (prob_33_le_sq hW Q hQ n) p s hp
    hpp hs

/-! ### Corollary 17 -/

/-- **The proof of DDDF Corollary 17 with its constants as parameters** (template `dddf_cor17`,
same argument): at one white noise, one `ξ > 0` and one level `p ≤ 1/4` with `2p ≤ p₁`, the
Prop 16 tail `(C₁, c₁)` at levels `≤ p₁`, the Prop 5 tail `(C₅, c₅)` of `X_{1,3}` and the
bound `P(X_{1,1} > M) ≤ p` give `P(L^{(n)}_{1,3}(φ) ≤ e^{-s} ℓ_n(φ, p)) ≤ C e^{-cs²}` for every
`(C, c)` with `c ≤ c₅/(4ξ²)`, `c ≤ c₁/16`, `C₅ + C₁ ≤ C` and `e^{c(4ξM)²} ≤ C`. -/
theorem cor17_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ p p₁ C₁ c₁ C₅ c₅ M C c : ℝ} (hξ : 0 < ξ)
    (hp : 0 < p) (hp4 : p ≤ 1 / 4) (hp2 : 2 * p ≤ p₁) (hC₁ : 0 < C₁) (hc₁ : 0 < c₁)
    (hC₅ : 0 < C₅) (hM : 0 ≤ M) (hc : 0 < c) (hcc₅ : c ≤ c₅ / (4 * ξ ^ 2))
    (hcc₁ : c ≤ c₁ / 16) (hCsum : C₅ + C₁ ≤ C) (hCexp : Real.exp (c * (4 * ξ * M) ^ 2) ≤ C)
    (h16 : ∀ (n : ℕ) (q s : ℝ), 0 < q → q ≤ p₁ → 0 < s →
      P {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
          Real.exp (-s) * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal q)} ≤
        ENNReal.ofReal (C₁ * Real.exp (-c₁ * s ^ 2)))
    (h5 : ∀ x : ℝ, 0 < x → P {ω | ENNReal.ofReal x ≤
        XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) 1 3} ≤
      ENNReal.ofReal (C₅ * Real.exp (-(c₅ * x ^ 2))))
    (htail : P {ω | ENNReal.ofReal M <
        XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) 1 1} ≤
      ENNReal.ofReal p)
    (n : ℕ) {s : ℝ} (hs : 0 < s) :
    P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
        Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)} ≤
      ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  have := hW.isProbabilityMeasure
  by_cases hsM : s < 4 * ξ * M
  · -- small `s`: the bound exceeds `1`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 ≤ Real.exp (c * (4 * ξ * M) ^ 2) * Real.exp (-c * s ^ 2) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hsM.le 2) hc.le]
    exact h1.trans (mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le)
  push Not at hsM
  -- (2.27): `ℓ_n(φ, p) ≤ e^{ξM} ℓ_n(ψ, 2p)`
  have hcmp := ellQ_phi_le_of_tail (ξ := ξ) hW Q zero_le_one zero_le_one hM htail
    (p := ENNReal.ofReal p) (ENNReal.ofReal_pos.2 hp)
    (by rw [← ENNReal.ofReal_add hp.le hp.le, ENNReal.ofReal_lt_one]; linarith) n
  rw [← ENNReal.ofReal_add hp.le hp.le, show p + p = 2 * p by ring, abs_of_pos hξ] at hcmp
  set x : ℝ := s / (2 * ξ)
  have hx : 0 < x := by positivity
  set s' : ℝ := s / 2 - ξ * M
  have hs' : s / 4 ≤ s' := by simp only [s']; linarith
  set E₁ := {ω | ENNReal.ofReal x ≤
    XAB (fun n y => phiMN W P 0 n y ω) (fun n y => psiMN Q W P 0 n y ω) 1 3}
  set E₂ := {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
    Real.exp (-s') * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p))}
  -- off `{X_{1,3} ≥ s/(2ξ)}`: `L_{1,3}(ψ) ≤ e^{s/2} L_{1,3}(φ)`
  have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
      Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)} ⊆ E₁ ∪ E₂ := by
    intro ω hω
    by_cases h1 : ω ∈ E₁
    · exact Or.inl h1
    right
    have hX : XAB (fun n y => psiMN Q W P 0 n y ω) (fun n y => phiMN W P 0 n y ω) 1 3 ≤
        ENNReal.ofReal x := by
      rw [XAB_comm]; exact (not_le.1 h1).le
    have hL := lenObs_le_of_XAB_le (ξ := ξ) (φ := fun n => psiMN Q W P 0 n)
      (ψ := fun n => phiMN W P 0 n)
      (fun k _ => (isPhiVersion_phiMN hW (Nat.zero_le k)).cont _) zero_le_one
      (by norm_num) hx.le hX n
    rw [abs_of_pos hξ] at hL
    have hω' : lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤ Real.exp (-s) * (Real.exp (ξ * M) *
        ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p))) :=
      hω.trans (mul_le_mul_of_nonneg_left hcmp (Real.exp_pos _).le)
    show lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
      Real.exp (-s') * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p))
    calc _ ≤ _ := hL
      _ ≤ Real.exp (ξ * x) * (Real.exp (-s) * (Real.exp (ξ * M) *
          ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p)))) :=
          mul_le_mul_of_nonneg_left hω' (Real.exp_pos _).le
      _ = Real.exp (ξ * x + -s + ξ * M) *
          ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (2 * p)) := by
          rw [Real.exp_add, Real.exp_add]; ring
      _ = _ := by
          congr 2
          simp only [x, s']; field_simp; ring
  have hP1 := h5 x hx
  have hP2 := h16 n (2 * p) s' (by positivity) hp2 (by linarith)
  -- `c ≤ c₅/(4ξ²)`
  have hb1 : C₅ * Real.exp (-(c₅ * x ^ 2)) ≤ C₅ * Real.exp (-c * s ^ 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₅.le
    have hx2 : x ^ 2 = s ^ 2 / (4 * ξ ^ 2) := by simp only [x]; rw [div_pow, mul_pow]; norm_num
    rw [hx2]
    have : c * s ^ 2 ≤ c₅ / (4 * ξ ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_right hcc₅ (by positivity)
    rw [div_mul_eq_mul_div] at this
    rw [mul_div_assoc']
    linarith
  -- `c ≤ c₁/16` and `s' ≥ s/4`
  have hb2 : C₁ * Real.exp (-c₁ * s' ^ 2) ≤ C₁ * Real.exp (-c * s ^ 2) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₁.le
    have h1 : s ^ 2 / 16 ≤ s' ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hc₁.le, mul_le_mul_of_nonneg_right hcc₁ (sq_nonneg s)]
  -- `C₅ + C₁ ≤ C`
  have h3 : (C₅ + C₁) * Real.exp (-c * s ^ 2) ≤ C * Real.exp (-c * s ^ 2) :=
    mul_le_mul_of_nonneg_right hCsum (Real.exp_pos _).le
  calc _ ≤ P (E₁ ∪ E₂) := measure_mono hsub
    _ ≤ P E₁ + P E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₅ * Real.exp (-(c₅ * x ^ 2))) +
        ENNReal.ofReal (C₁ * Real.exp (-c₁ * s' ^ 2)) := add_le_add hP1 hP2
    _ = ENNReal.ofReal (C₅ * Real.exp (-(c₅ * x ^ 2)) + C₁ * Real.exp (-c₁ * s' ^ 2)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := ENNReal.ofReal_le_ofReal (by linarith)

/-- **DDDF Corollary 17, uniform in `ξ` and in the white noise** (ledger U5, second statement;
template `dddf_cor17`; source (A.5) at every level `p ≤ p₀`): there is `p₀ > 0` such that for
every `p ∈ (0, p₀]` there are `C, c > 0`, chosen before the probability space and before `ξ`,
with `P(L^{(n)}_{1,3}(φ) ≤ e^{-s} ℓ_n(φ, p)) ≤ C e^{-cs²}` for every white noise, every
`ξ ∈ (0, ξs]`, `n ≥ 0` and `s > 0`. Witnesses (ledger row `dddf_cor17`):
`c = min(c₅/(4ξs²), c₁/16)`, `C = (C₅ + C₁ + 1) e^{4c₅M²}`. -/
theorem cor17_unif (ξs : ℝ) (hξs : 0 < ξs) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (s : ℝ), 0 < s →
        P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
            Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  obtain ⟨p₁, C₁, c₁, hp₁, hC₁, hc₁, h16⟩ := prop16_unif.{u} ξs hξs psiQ₀ psiSmall_psiQ₀
  obtain ⟨C', c', hC', hc', htail⟩ := exists_tail_XAB_unif_W.{u} psiQ₀ 3
  obtain ⟨C₅, c₅, hC₅, hc₅, h5⟩ := dddf_prop5_XAB_W.{u} psiQ₀ 1 3
  refine ⟨min (p₁ / 2) (1 / 4), lt_min (by positivity) (by norm_num), fun p hp hpp => ?_⟩
  have hp2 : 2 * p ≤ p₁ := by linarith [min_le_left (p₁ / 2) (1 / 4)]
  have hp4 : p ≤ 1 / 4 := hpp.trans (min_le_right _ _)
  set M : ℝ := √(max 1 (Real.log (C' / p)) / c')
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  set c : ℝ := min (c₅ / (4 * ξs ^ 2)) (c₁ / 16)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  set C : ℝ := (C₅ + C₁ + 1) * Real.exp (4 * c₅ * M ^ 2)
  have he : 1 ≤ Real.exp (4 * c₅ * M ^ 2) := Real.one_le_exp (by positivity)
  have hCe : Real.exp (4 * c₅ * M ^ 2) ≤ C := le_mul_of_one_le_left (Real.exp_pos _).le
    (by linarith)
  have hCsum : C₅ + C₁ ≤ C := by
    have : (C₅ + C₁) * 1 ≤ C := mul_le_mul (by linarith) he zero_le_one (by positivity)
    linarith
  refine ⟨C, c, by positivity, hc, fun {Ω} _ {P} {W} hW ξ hξ n s hs => ?_⟩
  obtain ⟨hξ0, hξs'⟩ := hξ
  -- `c ≤ c₅/(4ξs²) ≤ c₅/(4ξ²)`
  have hcc₅ : c ≤ c₅ / (4 * ξ ^ 2) :=
    (min_le_left _ _).trans (div_le_div_of_nonneg_left hc₅.le (by positivity)
      (by nlinarith))
  -- `c (4ξM)² = (4ξ²c) 4M² ≤ 4c₅M²`
  have hCexp : Real.exp (c * (4 * ξ * M) ^ 2) ≤ C := by
    refine (Real.exp_le_exp.2 ?_).trans hCe
    have h4 : c * (4 * ξ ^ 2) ≤ c₅ := by
      rwa [le_div_iff₀ (by positivity)] at hcc₅
    have e : c * (4 * ξ * M) ^ 2 = c * (4 * ξ ^ 2) * (4 * M ^ 2) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ 4 * M ^ 2)]
  exact cor17_core hW psiQ₀ hξ0 hp hp4 hp2 hC₁ hc₁ hC₅ hM hc hcc₅ (min_le_right _ _) hCsum
    hCexp (fun n q s hq hq₁ hs => h16 hW ξ ⟨hξ0, hξs'⟩ n q s hq hq₁ hs) (h5 hW)
    (htail hW 1 1 (by norm_num) (by norm_num) p hp) n hs

/-- **The interface `IfaceCor17U`** (`GaussianLQG/Uniform/Interfaces.lean`, ledger U5) holds for
every `ξs > 0`. -/
theorem ifaceCor17U (ξs : ℝ) (hξs : 0 < ξs) : IfaceCor17U ξs :=
  cor17_unif.{0} ξs hξs

/-! ### Aliases and per-noise forms -/

/-- `prop16_unif` under the name of the ledger's packet plan (B-2) -/
theorem prop16_unif_all {ξs : ℝ} (hξs : 0 < ξs) (Q : PsiParams) (hQ : PsiSmall Q) :
    ∃ p₀ C c : ℝ, 0 < p₀ ∧ 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (p s : ℝ), 0 < p → p ≤ p₀ → 0 < s →
        P {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
            Real.exp (-s) * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) :=
  prop16_unif.{u} ξs hξs Q hQ

/-- `cor17_unif` under the name of the ledger's packet plan (B-2) and §OP-3 -/
theorem cor17_unif_all {ξs : ℝ} (hξs : 0 < ξs) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (s : ℝ), 0 < s →
        P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
            Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) :=
  cor17_unif.{u} ξs hξs

section PerNoise

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- per-noise form of `prop16_unif` (white noise first, constants before `ξ`) -/
theorem prop16_unif_noise (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) (Q : PsiParams)
    (hQ : PsiSmall Q) :
    ∃ p₀ C c : ℝ, 0 < p₀ ∧ 0 < C ∧ 0 < c ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ (n : ℕ) (p s : ℝ), 0 < p → p ≤ p₀ → 0 < s →
        P {ω | lenObs ξ (psiMN Q W P 0 n) (rectAB 1 3) ω ≤
            Real.exp (-s) * ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  obtain ⟨p₀, C, c, hp₀, hC, hc, h⟩ := prop16_unif.{u} ξs hξs Q hQ
  exact ⟨p₀, C, c, hp₀, hC, hc, h hW⟩

/-- per-noise form of `cor17_unif` (white noise first, constants before `ξ`) -/
theorem cor17_unif_noise (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (s : ℝ), 0 < s →
        P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
            Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  obtain ⟨p₀, hp₀, h⟩ := cor17_unif.{u} ξs hξs
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨C, c, hC, hc, hb⟩ := h p hp hpp
  exact ⟨C, c, hC, hc, hb hW⟩

end PerNoise

end Uniform
end GaussianLQG
