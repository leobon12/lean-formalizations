import LQGMetric.Papers.DDDF.T20EMain
import GaussianLQG.Uniform.Interfaces

/-!
# Uniform-in-`ξ` predicates for DDDF Theorem 20 (Route U, ledger U0 and U9)

Phase B, packet PB-U9 (ledger packets B-6). Uniform-constants ledger
`blueprint/phaseB/uniform-ledger.tex`, statement U0 (table of uniform predicates), U9 and
Finding `fd:predicates`.

The per-`ξ` predicates of DDDF Theorem 20, Step 4 in `LQGMetric/Papers/DDDF/`
(`T20CircuitGlue`, `T20Step4Num`, `T20Step4Den`, `T20Step4Pathwise`, `T20Step4Visited`,
`T20Step4`) are `Prop`s of `(ξ, Q, W, P)` with their existential constants inside. Here:

* `…At ξ Q W P (constants)` is the body of each template with the constants as explicit
  parameters (`t20Step4Num_iff` etc. check by `Iff.rfl` that the bodies are verbatim);
* `…U ξs Q` is the uniform copy of the ledger: the existential block is moved in front of
  `∀ {Ω} [MeasurableSpace Ω] {P} {W}, IsWhiteNoise P W → ∀ ξ ∈ Ioc 0 ξs`, so the constants are
  chosen before the probability space and before `ξ`.

The pathwise predicates (`Glue`, `Num`, `Den`, `Pathwise`) are universe polymorphic in the
probability space; `T20Step4VisitedU` and `T20Step4U` are stated for `Ω : Type`, the universe of
the interfaces `IfaceCor17U`, `IfaceProp18U` (`GaussianLQG/Uniform/Interfaces.lean`) from which
they are proved.
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

/-! ### The template bodies with explicit constants -/

section At

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the body of `T20CircuitGlue` (`LQGMetric/Papers/DDDF/T20DNum.lean`, DDDF (5.61)–(5.62),
the circuit gluing) with the constants `C₁, d₁, K₀` as parameters -/
def T20CircuitGlueAt (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (C₁ : ℝ)
    (d₁ K₀ : ℕ) : Prop :=
  ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → ∃ s : ℝ,
    (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
    ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ →
      ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K, z ∈ T20C.visSet γ n K b s →
        ∃ P' ∈ T20.coarseBlocks K (γ n z.1),
          |((b.1 - P'.1 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
          |((b.2 - P'.2 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
          ∃ R : Finset (Circle × ℂ), R ⊆ T20D.longFam K ∧ (R.card : ℝ) ≤ C₁ * ((K : ℝ) + 1) ^ d₁ ∧
            (∀ j ∈ R, ∀ x ∈ T20D.RL K j, x ∈ T20D.bigBox ∧
              ‖x - T20.dyCenter K P'‖ ≤ C₁ * (K : ℝ) ^ Q.ε₀ * (2 : ℝ)⁻¹ ^ K) ∧
            (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
                T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
              (1 + η) * T20C.lenPsi ξ Q W P n z.1 +
                ∑ j ∈ R, T20B.mrectLen ξ (fun x => psiMN Q W P 0 n x z.1) K j.1 j.2 3 1

/-- the body of `T20Step4Num` (`LQGMetric/Papers/DDDF/T20CGather.lean`, DDDF (5.61)–(5.62))
with the constants `C₁, d₁, K₀` as parameters -/
def T20Step4NumAt (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (C₁ : ℝ)
    (d₁ K₀ : ℕ) : Prop :=
  ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → ∃ s : ℝ,
    (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
    ∃ (J : Finset (Circle × ℂ)) (hJ : J.Nonempty), ((J.card : ℝ) ≤ C₁ * 4 ^ K) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ →
      ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x) →
        (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
        ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K, z ∈ T20C.visSet γ n K b s →
          ∃ P' ∈ T20.coarseBlocks K (γ n z.1),
            |((b.1 - P'.1 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
            |((b.2 - P'.2 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
            T20C.incr ξ Q W P K n b z ≤ η + C₁ * ((K : ℝ) + 1) ^ d₁ *
              Real.exp (C₁ * T20C.Xbig Q W P z.1) *
              Real.exp (C₁ * (K : ℝ) ^ Q.ε₀ * T20C.Obig K Y z.1) *
              Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') z.1) *
              T20C.maxLong ξ W P K n J hJ z.1 / T20C.lenPsi ξ Q W P n z.1

/-- the body of `T20Step4Den` (`LQGMetric/Papers/DDDF/T20CGather.lean`, DDDF (5.63)–(5.64))
with the constants `C₁, K₀` as parameters -/
def T20Step4DenAt (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (C₁ : ℝ)
    (K₀ : ℕ) : Prop :=
  ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
    ∃ (J' : Finset (Circle × ℂ)) (hJ' : J'.Nonempty), ((J'.card : ℝ) ≤ C₁ * 4 ^ K) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ →
      ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x) →
        (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
        ∀ᵐ ω ∂P, Real.exp (-(C₁ * T20C.Xbig Q W P ω)) *
          Real.exp (-(C₁ * (K : ℝ) ^ Q.ε₀ * T20C.Obig K Y ω)) *
          T20C.minShort ξ W P K n J' hJ' ω *
          ∑ P' ∈ T20.coarseBlocks K (γ n ω), Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') ω) ≤
          C₁ * T20C.lenPsi ξ Q W P n ω

/-- the body of `T20Step4Pathwise` (`LQGMetric/Papers/DDDF/T20CDefs.lean`, DDDF (5.61)–(5.64)
summed over the visited blocks) with the constants `C₀, d, K₀` as parameters -/
def T20Step4PathwiseAt (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (C₀ : ℝ)
    (d K₀ : ℕ) : Prop :=
  ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → ∃ s : ℝ,
    (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
    ∃ (J J' : Finset (Circle × ℂ)) (hJ : J.Nonempty) (hJ' : J'.Nonempty),
      ((J.card : ℝ) + J'.card ≤ C₀ * 4 ^ K) ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ γ : ℕ → Ω → ℝ → ℂ, T20.IsNearGeodSel ξ Q W P η γ →
      ∀ Y : ℂ → Ω → ℝ, (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x) →
        (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
        ∀ᵐ z ∂(P.prod P), ∑ b ∈ T20B.nearIdx K, (T20C.visSet γ n K b s).indicator
            (fun z => ENNReal.ofReal (T20C.incr ξ Q W P K n b z ^ 2)) z ≤
          ENNReal.ofReal (C₀ * 4 ^ K * η ^ 2) +
          ENNReal.ofReal (C₀ * ((K : ℝ) + 1) ^ d * Real.exp (C₀ * T20C.Xbig Q W P z.1) *
            Real.exp (C₀ * (K : ℝ) ^ Q.ε₀ * T20C.Obig K Y z.1) *
            T20C.lsRatio ξ W P K n J J' hJ hJ' z.1 ^ 2 *
            T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x z.1) (γ n z.1))

/-- the body of `T20Step4Visited` (`LQGMetric/Papers/DDDF/T20BStep4.lean`, DDDF (5.65)–(5.67)) at
the level `p`, with the constants `C₂, K₀` as parameters -/
def T20Step4VisitedAt (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (p C₂ : ℝ)
    (K₀ : ℕ) : Prop :=
  ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n → ∃ s : ℝ,
    (∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s) ∧
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ γ : ℕ → Ω → ℝ → ℂ,
      T20.IsNearGeodSel ξ Q W P η γ ∧
      ∑ b ∈ T20B.nearIdx K, ∫⁻ z, {z : Ω × Ω | ∃ t ∈ Icc (0 : ℝ) 1,
          γ n z.1 t ∉ T20B.farSet (T20B.hoBlock K b) s}.indicator (fun z => ENNReal.ofReal
        (max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2) - L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 ^ 2))
          z ∂(P.prod P) ≤
        ENNReal.ofReal (Real.exp (-(C₂ * K)) *
          LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2)

/-- the body of `T20Step4` (`LQGMetric/Papers/DDDF/T20BRec.lean`, the bound of Step 4 used in
(5.68)) at the level `p`, with the constants `C₂, K₀` as parameters -/
def T20Step4At (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (p C₂ : ℝ)
    (K₀ : ℕ) : Prop :=
  ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
    ∑ b ∈ T20B.nearIdx K, ∫ z, max (L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 -
        T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2) -
      L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1)) 0 ^ 2 ∂(P.prod P) ≤
      Real.exp (-(C₂ * K)) * LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2

variable {ξ : ℝ} {Q : PsiParams} {W : WNSpace → Ω → ℝ} {P : Measure Ω}

/-- the template `T20CircuitGlue` is `∃ constants, T20CircuitGlueAt` -/
theorem t20CircuitGlue_iff : T20CircuitGlue ξ Q W P ↔
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ d₁ K₀ : ℕ, T20CircuitGlueAt ξ Q W P C₁ d₁ K₀ := Iff.rfl

/-- the template `T20Step4Num` is `∃ constants, T20Step4NumAt` -/
theorem t20Step4Num_iff : T20Step4Num ξ Q W P ↔
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ d₁ K₀ : ℕ, T20Step4NumAt ξ Q W P C₁ d₁ K₀ := Iff.rfl

/-- the template `T20Step4Den` is `∃ constants, T20Step4DenAt` -/
theorem t20Step4Den_iff : T20Step4Den ξ Q W P ↔
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ K₀ : ℕ, T20Step4DenAt ξ Q W P C₁ K₀ := Iff.rfl

/-- the template `T20Step4Pathwise` is `∃ constants, T20Step4PathwiseAt` -/
theorem t20Step4Pathwise_iff : T20Step4Pathwise ξ Q W P ↔
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d K₀ : ℕ, T20Step4PathwiseAt ξ Q W P C₀ d K₀ := Iff.rfl

/-- the template `T20Step4Visited` is `∃ p₀, ∀ p ≤ p₀, ∃ constants, T20Step4VisitedAt` -/
theorem t20Step4Visited_iff : T20Step4Visited ξ Q W P ↔
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ K₀ : ℕ,
      T20Step4VisitedAt ξ Q W P p C₂ K₀ := Iff.rfl

/-- the template `T20Step4` is `∃ p₀, ∀ p ≤ p₀, ∃ constants, T20Step4At` -/
theorem t20Step4_iff : T20Step4 ξ Q W P ↔
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ K₀ : ℕ,
      T20Step4At ξ Q W P p C₂ K₀ := Iff.rfl

end At

/-! ### The uniform predicates (ledger U0) -/

/-- **The circuit gluing, uniform in `ξ ∈ (0, ξs]` and in the white noise** (uniform copy of
`T20CircuitGlue`): the constants are chosen before the probability space and before `ξ`. -/
def T20CircuitGlueU (ξs : ℝ) (Q : PsiParams) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ d₁ K₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      T20CircuitGlueAt ξ Q W P C₁ d₁ K₀

/-- **DDDF (5.61)–(5.62), uniform** (ledger U0, `T20Step4NumU`; template `T20Step4Num`). -/
def T20Step4NumU (ξs : ℝ) (Q : PsiParams) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ d₁ K₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      T20Step4NumAt ξ Q W P C₁ d₁ K₀

/-- **DDDF (5.63)–(5.64), uniform** (ledger U0, `T20Step4DenU`; template `T20Step4Den`). -/
def T20Step4DenU (ξs : ℝ) (Q : PsiParams) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ K₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      T20Step4DenAt ξ Q W P C₁ K₀

/-- **The pathwise bound of Step 4, uniform** (ledger U0, `T20Step4PathwiseU`; template
`T20Step4Pathwise`). -/
def T20Step4PathwiseU (ξs : ℝ) (Q : PsiParams) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ d K₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      T20Step4PathwiseAt ξ Q W P C₀ d K₀

/-- **Step 4 for the visited blocks, uniform** (ledger U0, `T20Step4VisitedU`; template
`T20Step4Visited`): `p₀`, and for `p ≤ p₀` the constants `C₂, K₀`, are chosen before the
probability space and before `ξ`. -/
def T20Step4VisitedU (ξs : ℝ) (Q : PsiParams) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ K₀ : ℕ,
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, T20Step4VisitedAt ξ Q W P p C₂ K₀

/-- **Step 4 of Theorem 20, uniform** (ledger U0, `T20Step4U`; template `T20Step4`). -/
def T20Step4U (ξs : ℝ) (Q : PsiParams) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ K₀ : ℕ,
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, T20Step4At ξ Q W P p C₂ K₀

end Uniform
end GaussianLQG
