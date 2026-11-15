/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Covariance exhaustion: the abstract steps of Aux. lemma 50

Packet PROVE-SEC7-A3 (specification §7.1, Aux. lemma 50, `source/spec/p193-240.md` L819–L912 and
`p241-288.md` L1–L28, pp. 235–242). Aux. lemma 50 identifies the conditional law of the whole field given
the recorded driving history: the conditional-mean martingale `N_t(φ) = E[(h, φ) | 𝒢_t]` is exhausted by
its Brownian part `I_t(φ)` and the fresh Gaussian jumps `J_t(φ)` at pocket births, because the Green
identity accounts for the entire variance. The probabilistic steps that do not involve the Loewner
geometry are proved here, in the generality in which the source uses them:

* `integral_sq_condExp_sub_condExp` (passage to the usual augmentation, p. 237): for nested
  `σ`-algebras the squared `L²` distance between the conditional means is the difference of the expected
  conditional variances; `tendsto_integral_sq_condExp_sub` (the means converge when the variances do);
  `condExp_ae_eq_integral_of_integral_sq_eq` ("`Var(N₀(φ)) = 0` and `N₀(φ) = (m, φ)`");
* `condExp_exp_jump_eq` (HGV10): Gaussian conditional characteristic functions before and at a birth give
  the centred Gaussian conditional law of the jump `ΔN_τ(φ)`, with variance the lost conditional variance;
* `ae_eq_add_of_integral_mul_eq` (HGV11)–(HGV12): `N_t − N₀ = I_t + J_t` from the `L²` identities
  `E[(N − N₀) I] = E[I²]`, `E[(N − N₀) J] = E[J²]`, `E[IJ] = 0` and the variance identity
  `E[(N − N₀)²] = E[I²] + E[J²]` ("this variance identity rules out every additional component");
* `condExp_exp_eq_of_tendsto` ("Forgetting the germs"): `L¹` limits of conditionally centred Gaussian
  variables with converging conditional variances are conditionally centred Gaussian.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace InteractingSLE

namespace Sec7

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **(HGV11)–(HGV12): the variance identity rules out every further component.** If `X, I, J` are
square integrable with `E[XI] = E[I²]`, `E[XJ] = E[J²]`, `E[IJ] = 0` and `E[X²] = E[I²] + E[J²]`, then
`X = I + J` almost surely: the squared `L²` norm of `X − I − J` expands to zero. -/
theorem ae_eq_add_of_integral_mul_eq {X I J : Ω → ℝ} (hX : MemLp X 2 P) (hI : MemLp I 2 P)
    (hJ : MemLp J 2 P) (hXI : ∫ ω, X ω * I ω ∂P = ∫ ω, I ω ^ 2 ∂P)
    (hXJ : ∫ ω, X ω * J ω ∂P = ∫ ω, J ω ^ 2 ∂P) (hIJ : ∫ ω, I ω * J ω ∂P = 0)
    (hXX : ∫ ω, X ω ^ 2 ∂P = ∫ ω, I ω ^ 2 ∂P + ∫ ω, J ω ^ 2 ∂P) :
    X =ᵐ[P] I + J := by
  have i1 := hX.integrable_mul hI
  have i2 := hX.integrable_mul hJ
  have i3 := hI.integrable_mul hJ
  have iX := hX.integrable_sq
  have iI := hI.integrable_sq
  have iJ := hJ.integrable_sq
  have hexp : ∀ ω, (X ω - I ω - J ω) ^ 2 = X ω ^ 2 + I ω ^ 2 + J ω ^ 2
      - 2 * (X ω * I ω) - 2 * (X ω * J ω) + 2 * (I ω * J ω) := fun ω => by ring
  have hint : ∫ ω, (X ω - I ω - J ω) ^ 2 ∂P = 0 := by
    simp_rw [hexp]
    rw [integral_add, integral_sub, integral_sub, integral_add, integral_add, integral_const_mul,
      integral_const_mul, integral_const_mul, hXI, hXJ, hIJ, hXX]
    · ring
    all_goals first
      | exact iX | exact iI | exact iJ | exact i1.const_mul 2 | exact i2.const_mul 2
      | exact i3.const_mul 2 | exact iX.add iI | exact (iX.add iI).add iJ
      | exact ((iX.add iI).add iJ).sub (i1.const_mul 2)
      | exact (((iX.add iI).add iJ).sub (i1.const_mul 2)).sub (i2.const_mul 2)
  have hsqi : Integrable (fun ω => (X ω - I ω - J ω) ^ 2) P := ((hX.sub hI).sub hJ).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X ω - I ω - J ω)) hsqi).1 hint
  filter_upwards [h0] with ω hω
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at hω
  simp only [Pi.add_apply]
  linarith

/-- **Nested conditional means: the squared `L²` distance is the difference of the conditional
variances** (Aux. lemma 50, passage from raw germs to their usual augmentation, p. 237: "For nested raw
marked sigma-algebras the squared `L²` distance between the two conditional means is the expectation of
the difference of these conditional variances"). For `m ≤ m'` and square-integrable `X`,
`E[(E[X|m'] − E[X|m])²] = E[(X − E[X|m])²] − E[(X − E[X|m'])²]`. -/
theorem integral_sq_condExp_sub_condExp [IsFiniteMeasure P] {m m' : MeasurableSpace Ω}
    (hmm' : m ≤ m') (hm' : m' ≤ mΩ) {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, (P[X | m'] ω - P[X | m] ω) ^ 2 ∂P
      = ∫ ω, (X ω - P[X | m] ω) ^ 2 ∂P - ∫ ω, (X ω - P[X | m'] ω) ^ 2 ∂P := by
  have h1 : MemLp (P[X | m']) 2 P := hX.condExp (by norm_num)
  have h0 : MemLp (P[X | m]) 2 P := hX.condExp (by norm_num)
  set A : Ω → ℝ := fun ω => X ω - P[X | m'] ω with hA
  set D : Ω → ℝ := fun ω => P[X | m'] ω - P[X | m] ω with hD
  have hAm : MemLp A 2 P := hX.sub h1
  have hDm : MemLp D 2 P := h1.sub h0
  -- the cross term vanishes
  have hDs : StronglyMeasurable[m'] D :=
    stronglyMeasurable_condExp.sub (stronglyMeasurable_condExp.mono hmm')
  have hcA : P[A | m'] =ᵐ[P] 0 := by
    have := condExp_sub (m := m') (hX.integrable one_le_two) (h1.integrable one_le_two) (μ := P)
    refine this.trans ?_
    rw [condExp_of_stronglyMeasurable hm' stronglyMeasurable_condExp integrable_condExp, sub_self]
  have hcross : ∫ ω, D ω * A ω ∂P = 0 := by
    have e : (fun ω => D ω * A ω) = D * A := rfl
    rw [e, ← integral_condExp hm']
    have := condExp_mul_of_stronglyMeasurable_left hDs (hDm.integrable_mul hAm)
      (hAm.integrable one_le_two)
    rw [integral_congr_ae this]
    rw [integral_congr_ae (hcA.mono fun ω hω => by simp only [Pi.mul_apply, hω, Pi.zero_apply,
      mul_zero] : D * P[A | m'] =ᵐ[P] fun _ => (0 : ℝ))]
    simp
  have key : ∫ ω, (X ω - P[X | m] ω) ^ 2 ∂P = ∫ ω, A ω ^ 2 ∂P + ∫ ω, D ω ^ 2 ∂P := by
    have e : (fun ω => (X ω - P[X | m] ω) ^ 2)
        = fun ω => (A ω ^ 2 + D ω ^ 2) + 2 * (D ω * A ω) := by
      funext ω; simp only [hA, hD]; ring
    rw [e, integral_add (f := fun ω => A ω ^ 2 + D ω ^ 2) (g := fun ω => 2 * (D ω * A ω))
      (hAm.integrable_sq.add hDm.integrable_sq) ((hDm.integrable_mul hAm).const_mul 2),
      integral_add (f := fun ω => A ω ^ 2) (g := fun ω => D ω ^ 2) hAm.integrable_sq
      hDm.integrable_sq, integral_const_mul, hcross, mul_zero, add_zero]
  show ∫ ω, D ω ^ 2 ∂P = _ - ∫ ω, A ω ^ 2 ∂P
  rw [key]
  ring

/-- **Conditional means converge when the conditional variances do** (Aux. lemma 50, p. 237, right
augmentation; also the announced births (HGV9)): for `m ≤ mₙ` and square-integrable `X`, if
`E[(X − E[X|mₙ])²] → E[(X − E[X|m])²]`, then `E[X|mₙ] → E[X|m]` in `L²`. -/
theorem tendsto_integral_sq_condExp_sub [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    {mn : ℕ → MeasurableSpace Ω} (hmn : ∀ n, m ≤ mn n) (hmn' : ∀ n, mn n ≤ mΩ) {X : Ω → ℝ}
    (hX : MemLp X 2 P)
    (hvar : Tendsto (fun n => ∫ ω, (X ω - P[X | mn n] ω) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (X ω - P[X | m] ω) ^ 2 ∂P))) :
    Tendsto (fun n => ∫ ω, (P[X | mn n] ω - P[X | m] ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have := (tendsto_const_nhds (x := ∫ ω, (X ω - P[X | m] ω) ^ 2 ∂P)).sub hvar
  rw [sub_self] at this
  exact this.congr fun n => (integral_sq_condExp_sub_condExp (hmn n) (hmn' n) hX).symm

/-- **No variance is lost at time zero** (Aux. lemma 50, p. 237: "At time zero the conditional
covariance is the full `G_ℍ`, so the variance identity gives `Var(N₀(φ)) = 0` and `N₀(φ) = (m, φ)`"):
if conditioning on `m'` does not reduce the variance of a square-integrable `X`, then `E[X|m']` is the
constant `E[X]`. -/
theorem condExp_ae_eq_integral_of_integral_sq_eq [IsProbabilityMeasure P] {m' : MeasurableSpace Ω}
    (hm' : m' ≤ mΩ) {X : Ω → ℝ} (hX : MemLp X 2 P)
    (hvar : ∫ ω, (X ω - P[X | m'] ω) ^ 2 ∂P = ∫ ω, (X ω - ∫ ω', X ω' ∂P) ^ 2 ∂P) :
    P[X | m'] =ᵐ[P] fun _ => ∫ ω, X ω ∂P := by
  have key := integral_sq_condExp_sub_condExp (m := ⊥) bot_le hm' hX
  rw [condExp_bot] at key
  rw [hvar, sub_self] at key
  have hi : Integrable (fun ω => (P[X | m'] ω - ∫ ω', X ω' ∂P) ^ 2) P :=
    ((hX.condExp (by norm_num)).sub (memLp_const _)).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hi).1 key
  filter_upwards [h0] with ω hω
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at hω
  linarith

lemma norm_exp_mul_I_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

lemma integrable_exp_mul_I_ofReal [IsFiniteMeasure P] {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) :
    Integrable (fun ω => Complex.exp (Complex.I * (Y ω : ℂ))) P := by
  refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω => (norm_exp_mul_I_ofReal _).le)
  exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    |>.comp_aestronglyMeasurable hY

/-- **(HGV10): the conditional law of the mean jump at a birth.** Let `m ≤ m'` (the announced
pre-birth information and the information at the birth). If, for a real observable `X`, the
conditional characteristic function given each is Gaussian,
`E[e^{iX} | m] = e^{i N₁ − v₁/2}` and `E[e^{iX} | m'] = e^{i N₂ − v₂/2}`, with `N₁` `m`-measurable,
`N₂` `m'`-measurable and the later variance `v₂ ≥ 0` already `m`-measurable, then the jump of the
conditional mean has the Gaussian conditional characteristic function
`E[e^{i(N₂ − N₁)} | m] = e^{−(v₁ − v₂)/2}` ("by the tower property and division by the nonzero
Gaussian characteristic factor", p. 240). Applied to `uX` for every real `u` this identifies the jump
as a centred Gaussian with conditional variance `v₁ − v₂`. -/
theorem condExp_exp_jump_eq [IsFiniteMeasure P] {m m' : MeasurableSpace Ω} (hmm' : m ≤ m')
    (hm' : m' ≤ mΩ) {X N₁ N₂ v₁ v₂ : Ω → ℝ}
    (hN₁ : StronglyMeasurable[m] N₁) (hN₂ : StronglyMeasurable[m'] N₂)
    (hv₂ : StronglyMeasurable[m] v₂) (hv₂0 : ∀ ω, 0 ≤ v₂ ω)
    (h₁ : P[fun ω => Complex.exp (Complex.I * (X ω : ℂ)) | m] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * (N₁ ω : ℂ) - (v₁ ω : ℂ) / 2))
    (h₂ : P[fun ω => Complex.exp (Complex.I * (X ω : ℂ)) | m'] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * (N₂ ω : ℂ) - (v₂ ω : ℂ) / 2)) :
    P[fun ω => Complex.exp (Complex.I * ((N₂ ω - N₁ ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => Complex.exp (-(((v₁ ω - v₂ ω : ℝ) : ℂ)) / 2) := by
  have hm : m ≤ mΩ := hmm'.trans hm'
  -- measurability and bounds of the factors
  have hcI : Continuous fun x : ℝ => Complex.exp (Complex.I * (x : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hcV : Continuous fun x : ℝ => Complex.exp (-(x : ℂ) / 2) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.neg).div_const 2)
  set F₂ : Ω → ℂ := fun ω => Complex.exp (Complex.I * (N₂ ω : ℂ)) with hF₂
  set G₂ : Ω → ℂ := fun ω => Complex.exp (-(v₂ ω : ℂ) / 2) with hG₂
  set E₁ : Ω → ℂ := fun ω => Complex.exp (-(Complex.I * (N₁ ω : ℂ))) with hE₁
  have hF₂s : StronglyMeasurable[m'] F₂ := hcI.comp_stronglyMeasurable hN₂
  have hG₂s : StronglyMeasurable[m] G₂ := hcV.comp_stronglyMeasurable hv₂
  have hE₁s : StronglyMeasurable[m] E₁ :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)
      |>.comp_stronglyMeasurable hN₁
  have hF₂b : ∀ ω, ‖F₂ ω‖ ≤ 1 := fun ω => (norm_exp_mul_I_ofReal _).le
  have hG₂b : ∀ ω, ‖G₂ ω‖ ≤ 1 := fun ω => by
    simp only [hG₂, Complex.norm_exp]
    have : (-(v₂ ω : ℂ) / 2).re = -(v₂ ω) / 2 := by simp
    rw [this, Real.exp_le_one_iff]; linarith [hv₂0 ω]
  have hE₁b : ∀ ω, ‖E₁ ω‖ ≤ 1 := fun ω => by
    simp only [hE₁, Complex.norm_exp]; simp
  have hF₂i : Integrable F₂ P :=
    Integrable.of_bound (hF₂s.mono hm').aestronglyMeasurable 1 (Eventually.of_forall hF₂b)
  have hGFi : Integrable (G₂ * F₂) P :=
    Integrable.of_bound ((hG₂s.mono hm).mul (hF₂s.mono hm')).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Pi.mul_apply, norm_mul]
        nlinarith [hF₂b ω, hG₂b ω, norm_nonneg (F₂ ω), norm_nonneg (G₂ ω)])
  have hEFi : Integrable (E₁ * F₂) P :=
    Integrable.of_bound ((hE₁s.mono hm).mul (hF₂s.mono hm')).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Pi.mul_apply, norm_mul]
        nlinarith [hF₂b ω, hE₁b ω, norm_nonneg (F₂ ω), norm_nonneg (E₁ ω)])
  -- the tower identity: `e^{iN₁ − v₁/2} = e^{−v₂/2} E[e^{iN₂} | m]`
  have htower : (fun ω => Complex.exp (Complex.I * (N₁ ω : ℂ) - (v₁ ω : ℂ) / 2)) =ᵐ[P]
      G₂ * P[F₂ | m] := by
    refine h₁.symm.trans ?_
    refine (condExp_condExp_of_le hmm' hm').symm.trans ?_
    have hfac : (fun ω => Complex.exp (Complex.I * (N₂ ω : ℂ) - (v₂ ω : ℂ) / 2)) = G₂ * F₂ := by
      funext ω
      simp only [hG₂, hF₂, Pi.mul_apply, ← Complex.exp_add]
      congr 1; ring
    refine (condExp_congr_ae (g := G₂ * F₂) (h₂.trans (Eventually.of_forall fun ω => ?_))).trans
      ?_
    · rw [hfac]
    · exact condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
        hG₂s.aestronglyMeasurable hGFi hF₂i
  -- pull out `e^{−iN₁}` and divide
  have hpull : P[E₁ * F₂ | m] =ᵐ[P] E₁ * P[F₂ | m] :=
    condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
      hE₁s.aestronglyMeasurable hEFi hF₂i
  have heq : (fun ω => Complex.exp (Complex.I * ((N₂ ω - N₁ ω : ℝ) : ℂ))) = E₁ * F₂ := by
    funext ω
    simp only [hE₁, hF₂, Pi.mul_apply, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [heq]
  filter_upwards [hpull, htower] with ω h1 h2
  rw [h1, Pi.mul_apply]
  have hG₂ne : G₂ ω ≠ 0 := Complex.exp_ne_zero _
  have hF : P[F₂ | m] ω = Complex.exp (Complex.I * (N₁ ω : ℂ) - (v₁ ω : ℂ) / 2) / G₂ ω := by
    rw [h2, Pi.mul_apply]; field_simp
  rw [hF, hE₁, hG₂]
  simp only
  rw [mul_div_assoc', ← Complex.exp_add, ← Complex.exp_sub]
  congr 1; push_cast; ring

lemma norm_exp_mul_I_sub_exp_mul_I_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))‖ ≤ |a - b| := by
  have e : Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ))
      = Complex.exp (Complex.I * (b : ℂ)) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e, norm_mul, norm_exp_mul_I_ofReal, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- **Conditionally Gaussian limits** (Aux. lemma 50, "Forgetting the germs", p. 241: "Pass to the
`L²` limit of the finite sums. Bounded characteristic functions converge in `L¹`, and their covariance
sums increase to the finite total. Thus `J_t`, conditionally on the recorded driving history, is
centered Gaussian"). If `Jₙ → J` in `L¹` and `E[e^{iJₙ} | m] = e^{−qₙ/2}` with `m`-measurable
`qₙ ≥ 0` converging almost surely to an `m`-measurable `q`, then `E[e^{iJ} | m] = e^{−q/2}`. -/
theorem condExp_exp_eq_of_tendsto [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {J : Ω → ℝ} {Jn : ℕ → Ω → ℝ} {q : Ω → ℝ} {qn : ℕ → Ω → ℝ}
    (hJ : AEStronglyMeasurable[mΩ] J P) (hJn : ∀ n, AEStronglyMeasurable[mΩ] (Jn n) P)
    (hJint : ∀ n, Integrable (fun ω => Jn n ω - J ω) P)
    (hL1 : Tendsto (fun n => ∫ ω, |Jn n ω - J ω| ∂P) atTop (𝓝 0))
    (hq : StronglyMeasurable[m] q) (hqn : ∀ n, StronglyMeasurable[m] (qn n))
    (hqn0 : ∀ n ω, 0 ≤ qn n ω) (hqlim : ∀ᵐ ω ∂P, Tendsto (fun n => qn n ω) atTop (𝓝 (q ω)))
    (hcf : ∀ n, P[fun ω => Complex.exp (Complex.I * (Jn n ω : ℂ)) | m] =ᵐ[P]
      fun ω => Complex.exp (-(qn n ω : ℂ) / 2)) :
    P[fun ω => Complex.exp (Complex.I * (J ω : ℂ)) | m] =ᵐ[P]
      fun ω => Complex.exp (-(q ω : ℂ) / 2) := by
  have hcV : Continuous fun x : ℝ => Complex.exp (-(x : ℂ) / 2) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.neg).div_const 2)
  have hVb : ∀ x : ℝ, 0 ≤ x → ‖Complex.exp (-(x : ℂ) / 2)‖ ≤ 1 := fun x hx => by
    rw [Complex.norm_exp]
    have : (-(x : ℂ) / 2).re = -x / 2 := by simp
    rw [this, Real.exp_le_one_iff]; linarith
  have hEi := integrable_exp_mul_I_ofReal (P := P) hJ
  have hEni : ∀ n, Integrable (fun ω => Complex.exp (Complex.I * (Jn n ω : ℂ))) P := fun n =>
    integrable_exp_mul_I_ofReal (hJn n)
  have hgs : StronglyMeasurable[m] fun ω => Complex.exp (-(q ω : ℂ) / 2) :=
    hcV.comp_stronglyMeasurable hq
  have hq0 : ∀ᵐ ω ∂P, 0 ≤ q ω := hqlim.mono fun ω hω =>
    ge_of_tendsto' hω fun n => hqn0 n ω
  have hgi : Integrable (fun ω => Complex.exp (-(q ω : ℂ) / 2)) P :=
    Integrable.of_bound (hgs.mono hm).aestronglyMeasurable 1 (hq0.mono fun ω hω => hVb _ hω)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hEi (fun A _ _ => hgi.integrableOn)
    (fun A hA _ => ?_) hgs.aestronglyMeasurable).symm
  have hA' : MeasurableSet[mΩ] A := hm A hA
  -- the left side along the sequence
  have hL : Tendsto (fun n => ∫ ω in A, Complex.exp (Complex.I * (Jn n ω : ℂ)) ∂P) atTop
      (𝓝 (∫ ω in A, Complex.exp (Complex.I * (J ω : ℂ)) ∂P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hL1
    rw [← integral_sub (hEni n).integrableOn hEi.integrableOn]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (setIntegral_mono_set ((hEni n).sub hEi).norm.integrableOn
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall (subset_univ A))).trans ?_
    rw [setIntegral_univ]
    exact integral_mono ((hEni n).sub hEi).norm (hJint n).abs fun ω =>
      norm_exp_mul_I_sub_exp_mul_I_le _ _
  -- the right side along the sequence
  have hR : Tendsto (fun n => ∫ ω in A, Complex.exp (-(qn n ω : ℂ) / 2) ∂P) atTop
      (𝓝 (∫ ω in A, Complex.exp (-(q ω : ℂ) / 2) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => ((hcV.comp_stronglyMeasurable (hqn n)).mono hm).aestronglyMeasurable.restrict)
      (integrable_const _) (fun n => Eventually.of_forall fun ω => hVb _ (hqn0 n ω)) ?_
    exact ae_restrict_of_ae (hqlim.mono fun ω hω => (hcV.tendsto _).comp hω)
  have heq : ∀ n, ∫ ω in A, Complex.exp (Complex.I * (Jn n ω : ℂ)) ∂P
      = ∫ ω in A, Complex.exp (-(qn n ω : ℂ) / 2) ∂P := fun n => by
    rw [← setIntegral_condExp hm (hEni n) hA]
    exact setIntegral_congr_ae hA' ((hcf n).mono fun ω hω _ => hω)
  exact tendsto_nhds_unique hR (hL.congr heq)

end Sec7

end InteractingSLE
