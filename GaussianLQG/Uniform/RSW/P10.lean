import GaussianLQG.Uniform.RSW.Law
import LQGMetric.Papers.DDDF.P10Main

/-!
# DDDF Proposition 10 with constants uniform in `ξ` (Route U, item U3)

Phase B, packet PB-RSW. Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`, U3;
feasibility study `planning/audits/B1-S6-feasibility.md`, §3b row 14 and §4 U3. Templates (not
edited): `p10_core` (`LQGMetric/Papers/DDDF/P10Core.lean`), `prop10` and `p10_exponent_le`
(`P10Main.lean`), the predicate `Prop10` (`P10Node.lean`).

* `p10_core_unif`: `p10_core` with its binder moved: the constants `C₆, c₆, σ` come from
  DDDF Lemma 6 (`lemma6`), which does not involve `ξ`, so they are chosen before `ξ`. The proof
  is that of `p10_core`.
* `Prop10U ξs P W` (ledger U0, U3): Prop 10 for a fixed white noise with one constant `C ≥ 1`
  for all `ξ ∈ (0, ξs]`; `Prop10UAll ξs`: the stronger form with one `C` for all white noises on
  all probability spaces.
* `prop10_unif_all`: `Prop10UAll ξs` for every `ξs > 0`; `prop10_unif` (ledger U3): its per-noise
  corollary `Prop10U ξs P W`. The proof is that of `prop10`, with two
  changes: (i) the coupling is built once, on a reference space `(ℕ → ℝ)²` with
  `stdP ⊗ stdP` (`exists_isWhiteNoise`), and the crossing-length probabilities are transferred to
  the given white noise by `measure_crossLenIn_le_eq` (the template builds it on `Ω × Ω`, which
  makes `C` depend on `W`); (ii) the Lemma 9 level is `ε₁ = min (ε/4) (e^{-(ξs σ)²/2}/2)`, which
  is admissible for every `ξ ≤ ξs`, and the exponent `ξ x + √(2(ξσ)² log ε₁⁻¹)` is nondecreasing
  in `ξ`, so `p10_exponent_le` at `ξs` gives `C` (the ledger's bound `K₀(ξ) ≤ K₀(ξs)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.WNPush

universe u

/-- **DDDF Proposition 10, uniform in `ξ ∈ (0, ξs]` and in the white noise** (strong form of the
ledger's `Prop10U`; template `Prop10`, `LQGMetric/Papers/DDDF/P10Node.lean`): for the data
`(K, A, B, U, F)` of Prop 10 there is one `C ≥ 1`, chosen before the probability space and
before `ξ`. -/
def Prop10UAll (ξs : ℝ) : Prop :=
  ∀ (K A B U : Set ℂ) (F : ℂ → ℂ), IsCompact K → IsCompact A → IsCompact B → A ⊆ K → B ⊆ K →
    P10Map K U F →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ (n : ℕ) (l ε : ℝ), 0 < l → 0 < ε → ε < 1 / 2 →
      (ENNReal.ofReal ε ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ ENNReal.ofReal l} →
        ENNReal.ofReal (ε / 4) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (F '' K) (F '' A) (F '' B) ≤
            ENNReal.ofReal (p10Len C l ε (derivSup F K))}) ∧
      (ENNReal.ofReal (1 - ε) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ ENNReal.ofReal l} →
        ENNReal.ofReal (1 - 3 * ε) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (F '' K) (F '' A) (F '' B) ≤
            ENNReal.ofReal (p10Len C l ε (derivSup F K))})

/-- **DDDF Proposition 10, uniform in `ξ ∈ (0, ξs]`** (ledger U0, U3, `Prop10U ξs P W`; template
`Prop10`): for a fixed white noise and the data `(K, A, B, U, F)` of Prop 10 there is one `C ≥ 1`,
chosen before `ξ`. -/
def Prop10U {Ω : Type*} [MeasurableSpace Ω] (ξs : ℝ) (P : Measure Ω) (W : WNSpace → Ω → ℝ) :
    Prop :=
  ∀ (K A B U : Set ℂ) (F : ℂ → ℂ), IsCompact K → IsCompact A → IsCompact B → A ⊆ K → B ⊆ K →
    P10Map K U F →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (l ε : ℝ), 0 < l → 0 < ε → ε < 1 / 2 →
      (ENNReal.ofReal ε ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ ENNReal.ofReal l} →
        ENNReal.ofReal (ε / 4) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (F '' K) (F '' A) (F '' B) ≤
            ENNReal.ofReal (p10Len C l ε (derivSup F K))}) ∧
      (ENNReal.ofReal (1 - ε) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ ENNReal.ofReal l} →
        ENNReal.ofReal (1 - 3 * ε) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (F '' K) (F '' A) (F '' B) ≤
            ENNReal.ofReal (p10Len C l ε (derivSup F K))})

/-- the strong form gives the ledger's per-noise form -/
theorem Prop10UAll.prop10U {ξs : ℝ} (h : Prop10UAll.{u} ξs) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) : Prop10U ξs P W := by
  intro K A B U F hK hA hB hAK hBK hF
  obtain ⟨C, hC1, hC⟩ := h K A B U F hK hA hB hAK hBK hF
  exact ⟨C, hC1, fun ξ hξ n l ε hl hε0 hε => hC hW ξ hξ n l ε hl hε0 hε⟩

/-- the uniform predicate gives DDDF's Prop 10 at every `ξ ∈ (0, ξs]` -/
theorem Prop10U.prop10 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    {ξs : ℝ} (h : Prop10U ξs P W) {ξ : ℝ} (hξ : ξ ∈ Ioc (0 : ℝ) ξs) : Prop10 ξ P W := by
  intro K A B U F hK hA hB hAK hBK hF
  obtain ⟨C, hC1, hC⟩ := h K A B U F hK hA hB hAK hBK hF
  exact ⟨C, by linarith, fun n l ε hl hε0 hε => hC ξ hξ n l ε hl hε0 hε⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Core of DDDF Prop 10 with the Lemma 6 constants before `ξ`** (template `p10_core`,
binder moved; same proof). -/
theorem p10_core_unif {K A B U : Set ℂ} {F : ℂ → ℂ} (hK : IsCompact K)
    (hF : P10Map K U F) {W₁ W₂ : WNSpace → Ω → ℝ} (hW₁ : IsWhiteNoise P W₁)
    (hW₂ : IsWhiteNoise P W₂) (hind : IndepFun (fun ω f => W₁ f ω) (fun ω f => W₂ f ω) P) :
    ∃ C₆ c₆ σ : ℝ, 0 < C₆ ∧ 0 < c₆ ∧ 0 < σ ∧ ∀ ξ : ℝ, 0 < ξ → ∀ (n : ℕ) (l x ε₁ : ℝ),
      0 < x → 0 < ε₁ → ε₁ < Real.exp (-(ξ * σ) ^ 2 / 2) →
      P {ω | crossLenIn ξ (fun y => phiMN W₁ P 0 n y ω) K A B ≤ ENNReal.ofReal l} ≤
        P {ω | crossLenIn ξ (fun y => phiMN (coupledNoise hF.confHyp W₁ W₂) P 0 n y ω)
            (F '' K) (F '' A) (F '' B) ≤ ENNReal.ofReal (derivSup F K * Real.exp (ξ * x) *
              Real.exp (Real.sqrt (2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)) * l)} +
          ENNReal.ofReal (C₆ * Real.exp (-c₆ * x ^ 2)) + ENNReal.ofReal ε₁ := by
  classical
  have hP := hW₁.isProbabilityMeasure
  obtain ⟨M, hMb⟩ := hF.deriv_bd
  set h := hF.confHyp
  obtain ⟨C₆, c₆, σH, hC₆, hc₆, h6⟩ := lemma6 h hF.bdd (fun y hy => (hMb y hy).1)
    (fun y hy => (hMb y hy).2.1) (fun y hy => (hMb y hy).2.2) hK hF.sub hW₁ hW₂ hind
  set σ := Real.sqrt (max σH 1)
  have hσ : 0 < σ := Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hσ2 : σ ^ 2 = max σH 1 := Real.sq_sqrt (le_trans zero_le_one (le_max_right _ _))
  refine ⟨C₆, c₆, σ, hC₆, hc₆, hσ, fun ξ hξ n l x ε₁ hx hε₁ hε₁' => ?_⟩
  set δ : ℝ := (2 : ℝ)⁻¹ ^ n
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨YL, YH, hdec, hLc, hHc, hLm, hHm, hLae, hHae, htail, hvar, hindH⟩ := h6 δ hδ hδ1
  set Wt := coupledNoise h W₁ W₂
  have e1 : phiMN W₁ P 0 n = phiVer W₁ P δ 1 := by simp only [phiMN, pow_zero, δ]
  have e2 : phiMN Wt P 0 n = phiVer Wt P δ 1 := by simp only [phiMN, pow_zero, δ]
  rw [e1, e2]
  set φ := phiVer W₁ P δ 1
  set φt := phiVer Wt P δ 1
  have hv := isPhiVersion_phiVer hW₁ hδ hδ1
  -- the high-frequency field, extended off `K` by `φ_H`
  set Ψ : ℂ → Ω → ℝ := fun y ω => if y ∈ K then YH y ω else phiH F U W₁ δ y ω
  have hΨK : ∀ y ∈ K, ∀ ω, Ψ y ω = YH y ω := fun y hy ω => by simp [Ψ, hy]
  have hΨc : ∀ ω, ContinuousOn (fun y => Ψ y ω) K := fun ω =>
    (hHc ω).congr fun y hy => hΨK y hy ω
  have hphiHm : ∀ y, Measurable (phiH F U W₁ δ y) := fun y =>
    (hW₁.measurable _).const_mul _
  have hΨm : ∀ y, Measurable (Ψ y) := fun y => by
    by_cases hy : y ∈ K
    · have : Ψ y = YH y := funext fun ω => by simp [Ψ, hy]
      rw [this]; exact hHm y
    · have : Ψ y = phiH F U W₁ δ y := funext fun ω => by simp [Ψ, hy]
      rw [this]; exact hphiHm y
  have hind0 : IndepFun (fun ω y => phi W₁ δ 1 y ω) (fun ω y => phiH F U W₁ δ y ω) P :=
    (hindH.symm.comp (φ := fun (z : ℂ → ℝ × ℝ) y => (z y).1) (ψ := id)
      (measurable_pi_iff.2 fun y => measurable_fst.comp (measurable_pi_apply y)) measurable_id)
  have hindΨ : IndepFun (fun ω y => φ y ω) (fun ω y => Ψ y ω) P :=
    indepFun_modification (fun y => measurable_phi hW₁ δ 1 y) hv.meas hphiHm hΨm hv.ae_eq
      (fun y => by
        by_cases hy : y ∈ K
        · have : Ψ y = YH y := funext fun ω => by simp [Ψ, hy]
          rw [this]; exact hHae y hy
        · have : Ψ y = phiH F U W₁ δ y := funext fun ω => by simp [Ψ, hy]
          rw [this]) hind0
  have hgauss : ∀ y ∈ K, ∃ v : ℝ≥0, (v : ℝ) ≤ σ ^ 2 ∧ HasLaw (Ψ y) (gaussianReal 0 v) P := by
    intro y hy
    refine ⟨(‖Real.sqrt Real.pi • hKer F U δ y‖ ^ 2).toNNReal, ?_, ?_⟩
    · rw [Real.coe_toNNReal _ (sq_nonneg _), hσ2, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, Real.sq_sqrt Real.pi_pos.le, ← variance_phiH hW₁ δ y]
      exact (hvar y).trans (le_max_left _ _)
    · have : Ψ y = YH y := funext fun ω => by simp [Ψ, hy]
      rw [this]
      exact (hasLaw_phiH hW₁ δ y).congr (hHae y hy)
  have hT := tail_cross (A := A) (B := B) hξ hσ hε₁ hε₁' hK hv.cont hv.meas hΨc hΨm hindΨ hgauss
  have hT2 := htail x hx.le
  set s := Real.sqrt (2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp s)
  set S := derivSup F K
  have hsub : {ω | crossLenIn ξ (fun y => φ y ω) K A B ≤ ENNReal.ofReal l} ⊆
      ({ω | crossLenIn ξ (fun y => φt y ω) (F '' K) (F '' A) (F '' B) ≤
          ENNReal.ofReal (S * Real.exp (ξ * x) * Real.exp s * l)} ∪
        {ω | ENNReal.ofReal x ≤ ⨆ y ∈ K, ENNReal.ofReal |YL y ω|}) ∪
        {ω | c * crossLenIn ξ (fun y => φ y ω) K A B <
          crossLenIn ξ (fun y => φ y ω + Ψ y ω) K A B} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, not_lt] at hn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hn
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · have htop : crossLenIn ξ (fun y => φ y ω) K A B = ⊤ := by
        rw [crossLenIn_eq_biInf]
        refine iInf₂_eq_top.2 fun Q hQ => ?_
        obtain ⟨z, -, w, -, -, hU⟩ := hQ
        have := hU 0 ⟨le_rfl, zero_le_one⟩
        rw [hKe] at this; exact absurd this (Set.notMem_empty _)
      rw [htop] at hω
      exact absurd hω (not_le.2 ENNReal.ofReal_lt_top)
    obtain ⟨y₀, hy₀⟩ := hKne
    have hbdd : BddAbove ((fun z => ‖deriv F z‖) '' K) :=
      ⟨M, by rintro _ ⟨z, hz, rfl⟩; exact (hMb z (hF.sub hz)).2.1⟩
    have hSb : ∀ y ∈ K, ‖deriv F y‖ ≤ S := fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
    have hS1 : 1 ≤ S := ((hMb y₀ (hF.sub hy₀)).1).trans (hSb y₀ hy₀)
    have hsup : ∀ y ∈ K, |YL y ω| ≤ x := fun y hy =>
      ((ENNReal.ofReal_lt_ofReal_iff hx).1 ((le_iSup₂ (f := fun y (_ : y ∈ K) =>
        ENNReal.ofReal |YL y ω|) y hy).trans_lt h2)).le
    have hcong : crossLenIn ξ (fun y => φ y ω + YH y ω) K A B =
        crossLenIn ξ (fun y => φ y ω + Ψ y ω) K A B :=
      crossLenIn_congr_on fun y hy => by rw [hΨK y hy ω]
    have hstep1 : crossLenIn ξ (fun y => φt (F y) ω) K A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * x)) * crossLenIn ξ (fun y => φ y ω + YH y ω) K A B := by
      refine crossLenIn_le_of_abs_sub_le fun y hy => ?_
      rw [hdec y ω]
      have : φ y ω + YL y ω + YH y ω - (φ y ω + YH y ω) = YL y ω := by ring
      rw [this]; exact hsup y hy
    have hstep2 : crossLenIn ξ (fun z => φt z ω) (F '' K) (F '' A) (F '' B) ≤
        ENNReal.ofReal S * crossLenIn ξ ((fun z => φt z ω) ∘ F) K A B :=
      crossLenIn_image_le hF.isOpen hF.sub hF.diff (by linarith) hSb
    have hfin : crossLenIn ξ (fun z => φt z ω) (F '' K) (F '' A) (F '' B) ≤
        ENNReal.ofReal (S * Real.exp (ξ * x) * Real.exp s * l) := by
      calc _ ≤ ENNReal.ofReal S * crossLenIn ξ ((fun z => φt z ω) ∘ F) K A B := hstep2
        _ ≤ ENNReal.ofReal S * (ENNReal.ofReal (Real.exp (|ξ| * x)) *
            crossLenIn ξ (fun y => φ y ω + YH y ω) K A B) := mul_le_mul_right hstep1 _
        _ ≤ ENNReal.ofReal S * (ENNReal.ofReal (Real.exp (|ξ| * x)) *
            (c * ENNReal.ofReal l)) := by
          rw [hcong]
          exact mul_le_mul_right (mul_le_mul_right (h3.trans (mul_le_mul_right hω c)) _) _
        _ = ENNReal.ofReal (S * Real.exp (ξ * x) * Real.exp s * l) := by
          rw [abs_of_pos hξ, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          ring
    exact (not_lt.2 hfin) h1
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add le_rfl hT2) hT

/-- **DDDF Proposition 10, uniform in `ξ` and in the white noise** (strong form of ledger U3;
template `prop10`). For every `ξs > 0`, `Prop10UAll ξs`: the constant `C ≥ 1` depends only on
`(K, A, B, U, F)` and `ξs`. -/
theorem prop10_unif_all {ξs : ℝ} (hξs : 0 < ξs) : Prop10UAll.{u} ξs := by
  intro K A B U F hK hA hB hAK hBK hF
  -- the reference space `(ℕ → ℝ)²` with two independent white noises
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise
  have hW₁ := isWhiteNoise_fst hW₀
  have hW₂ := isWhiteNoise_snd hW₀
  have hind := indepFun_fst_snd_noise hW₀
  obtain ⟨C₆, c₆, σ, hC₆, hc₆, hσ, hcore⟩ := p10_core_unif hK hF hW₁ hW₂ hind
  set C₆' := max C₆ 1
  obtain ⟨C, hC1, hCexp⟩ := p10_exponent_le (σ := σ) hξs hc₆ (le_max_right C₆ 1)
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ n l ε hl hε0 hε => ?_⟩
  have hP := hW.isProbabilityMeasure
  obtain ⟨hξ0, hξs'⟩ := hξ
  have hℓ : 0 < Real.log ε⁻¹ := Real.log_pos (by rw [lt_inv_comm₀ one_pos hε0]; linarith)
  have ha₁ : 0 ≤ Real.log (4 * C₆') := Real.log_nonneg (by
    have := le_max_right C₆ 1; linarith)
  set x := √((Real.log (4 * C₆') + Real.log ε⁻¹) / c₆)
  have hx : 0 < x := Real.sqrt_pos.2 (by positivity)
  -- the Lemma 9 level, chosen with `ξs`: admissible for every `ξ ≤ ξs`
  set ε' := Real.exp (-(ξs * σ) ^ 2 / 2)
  set ε₁ := min (ε / 4) (ε' / 2)
  have hε₁ : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hξσ : (ξ * σ) ^ 2 ≤ (ξs * σ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hξs' hσ.le) 2
  have hε'ξ : ε' ≤ Real.exp (-(ξ * σ) ^ 2 / 2) := Real.exp_le_exp.2 (by linarith)
  have hε₁' : ε₁ < Real.exp (-(ξ * σ) ^ 2 / 2) :=
    (min_le_right _ _).trans_lt (by have := Real.exp_pos (-(ξs * σ) ^ 2 / 2); linarith)
  have key := hcore ξ hξ0 n l x ε₁ hx hε₁ hε₁'
  have htail : C₆ * Real.exp (-c₆ * x ^ 2) ≤ ε / 4 := by
    have hx2 : c₆ * x ^ 2 = Real.log (4 * C₆') + Real.log ε⁻¹ := by
      rw [Real.sq_sqrt (by positivity)]; field_simp
    have e : Real.exp (-c₆ * x ^ 2) = ε / (4 * C₆') := by
      rw [neg_mul, hx2, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
        Real.exp_log (by have := le_max_right C₆ 1; positivity), Real.exp_log (by positivity)]
      field_simp
    rw [e]
    have h1 : C₆ ≤ C₆' := le_max_left _ _
    have h2 : 0 < C₆' := lt_of_lt_of_le one_pos (le_max_right _ _)
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set S := derivSup F K
  have hS : 0 ≤ S := Real.sSup_nonneg (by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg _)
  have hlen : S * Real.exp (ξ * x) * Real.exp (√(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)) * l ≤
      p10Len C l ε S := by
    have hE := hCexp ε hε0 hε
    -- the exponent is nondecreasing in `ξ`
    have hlog0 : 0 ≤ Real.log ε₁⁻¹ := by
      rw [Real.log_inv, neg_nonneg]
      exact Real.log_nonpos hε₁.le ((min_le_left _ _).trans (by linarith))
    have hm : ξ * x + √(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹) ≤
        ξs * x + √(2 * (ξs * σ) ^ 2 * Real.log ε₁⁻¹) := by
      have h1 : ξ * x ≤ ξs * x := mul_le_mul_of_nonneg_right hξs' hx.le
      have h2 : √(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹) ≤ √(2 * (ξs * σ) ^ 2 * Real.log ε₁⁻¹) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hξσ (by norm_num)) hlog0)
      linarith
    have h1 : Real.exp (ξ * x) * Real.exp (√(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)) ≤
        C * Real.exp (C * √|Real.log (ε / (2 * C))|) := by
      rw [← Real.exp_add]
      calc Real.exp (ξ * x + √(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹))
          ≤ Real.exp (C * √|Real.log (ε / (2 * C))|) := Real.exp_le_exp.2 (hm.trans hE)
        _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le hC1
    unfold p10Len
    calc S * Real.exp (ξ * x) * Real.exp (√(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹)) * l
        = (S * l) * (Real.exp (ξ * x) * Real.exp (√(2 * (ξ * σ) ^ 2 * Real.log ε₁⁻¹))) := by
          ring
      _ ≤ (S * l) * (C * Real.exp (C * √|Real.log (ε / (2 * C))|)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hK' : IsCompact (F '' K) := hK.image_of_continuousOn (hF.diff.continuousOn.mono hF.sub)
  -- the probabilities of the statement are those on the reference space
  have hT1 := measure_crossLenIn_le_eq (ξ := ξ) (A := A) (B := B) hK hW hW₁ n (ENNReal.ofReal l)
  have hT2 := measure_crossLenIn_le_eq (ξ := ξ) (A := F '' A) (B := F '' B) hK' hW
    (isWhiteNoise_coupledNoise hF.confHyp hW₁ hW₂ hind) n (ENNReal.ofReal (p10Len C l ε S))
  have hmain : P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ ENNReal.ofReal l} ≤
      P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (F '' K) (F '' A) (F '' B) ≤
        ENNReal.ofReal (p10Len C l ε S)} + ENNReal.ofReal (ε / 2) := by
    rw [hT1, hT2]
    refine key.trans ?_
    have e : ENNReal.ofReal (ε / 2) = ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    rw [e, ← add_assoc]
    refine add_le_add (add_le_add (measure_mono fun ω hω => ?_) (ENNReal.ofReal_le_ofReal htail))
      (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    exact hω.trans (ENNReal.ofReal_le_ofReal hlen)
  constructor
  · intro h1
    have h2 := tsub_le_iff_right.2 (h1.trans hmain)
    rw [← ENNReal.ofReal_sub _ (by positivity)] at h2
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans h2
  · intro h1
    have h2 := tsub_le_iff_right.2 (h1.trans hmain)
    rw [← ENNReal.ofReal_sub _ (by positivity)] at h2
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans h2

/-- **DDDF Proposition 10, uniform in `ξ`** (ledger U3, `prop10_unif`; template `prop10`): for a
white noise `W` and `ξs > 0`, `Prop10U ξs P W`. -/
theorem prop10_unif {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) : Prop10U ξs P W :=
  (prop10_unif_all.{u} hξs).prop10U hW

end Uniform
end GaussianLQG
