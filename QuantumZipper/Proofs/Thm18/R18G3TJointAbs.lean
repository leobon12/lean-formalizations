import QuantumZipper.Proofs.Thm18.G3Core
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T-J: abstract lemmas (weighted decorrelation from conditional independence)

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71: conditionally on the field outside the
two half-discs, the two zoomed-in figures are independent (GFF Markov property) and each has
conditional law close to the wedge law (conditional Proposition 5.5). This file is the abstract
probabilistic bookkeeping turning these two facts into a weighted product formula:

* `integral_abs_condExp_sub_le`: if `|P(A ∩ G) − a P(E ∩ G)| ≤ e` for all `G ∈ 𝒢`, then
  `E|P[A|𝒢] − a P[E|𝒢]| ≤ 2e`;
* `integral_indicator_eq_condExp`: pull-out of a bounded `𝒢`-measurable weight;
* `abs_integral_inter_sub_le`: for events `A₁`, `A₂`, `E₁`, `E₂` with
  `P[A₁ ∩ A₂|𝒢] = P[A₁|𝒢] P[A₂|𝒢]` and `P[E₁ ∩ E₂|𝒢] = P[E₁|𝒢] P[E₂|𝒢]`, and a `𝒢`-measurable
  weight `w ∈ [0, M]`: `|∫_{A₁∩A₂} w − a b ∫_{E₁∩E₂} w| ≤ M (2e₁ + 2e₂)`.

Own elementary proofs (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal symmDiff

namespace QuantumZipper
namespace R18

variable {Ω : Type*} {𝒢 mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

theorem setIntegral_condExp_indicator_one (h𝒢 : 𝒢 ≤ mΩ) {A G : Set Ω} (hA : MeasurableSet A)
    (hG : MeasurableSet[𝒢] G) :
    ∫ ω in G, P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω ∂P = P.real (A ∩ G) := by
  rw [setIntegral_condExp h𝒢 ((integrable_const (1 : ℝ)).indicator hA) hG]
  exact (integral_indicator_one (μ := P.restrict G) hA).trans (measureReal_restrict_apply hA)

/-- **Sup over `𝒢` to `L¹`.** -/
theorem integral_abs_condExp_sub_le (h𝒢 : 𝒢 ≤ mΩ) {A E : Set Ω} (hA : MeasurableSet A)
    (hE : MeasurableSet E) (a e : ℝ)
    (H : ∀ G, MeasurableSet[𝒢] G → |P.real (A ∩ G) - a * P.real (E ∩ G)| ≤ e) :
    ∫ ω, |P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω - a * P[E.indicator (fun _ => (1 : ℝ)) | 𝒢] ω|
      ∂P ≤ 2 * e := by
  set f := P[A.indicator (fun _ => (1 : ℝ)) | 𝒢]
  set k := P[E.indicator (fun _ => (1 : ℝ)) | 𝒢]
  set h : Ω → ℝ := fun ω => f ω - a * k ω with hh
  have hsm : StronglyMeasurable[𝒢] h :=
    stronglyMeasurable_condExp.sub (stronglyMeasurable_condExp.const_mul a)
  have hint : Integrable h P := integrable_condExp.sub (integrable_condExp.const_mul a)
  have key : ∀ G, MeasurableSet[𝒢] G → ∫ ω in G, h ω ∂P = P.real (A ∩ G) - a * P.real (E ∩ G) :=
    fun G hG => by
      rw [hh, integral_sub integrable_condExp.integrableOn
        (integrable_condExp.const_mul a).integrableOn, integral_const_mul,
        setIntegral_condExp_indicator_one h𝒢 hA hG, setIntegral_condExp_indicator_one h𝒢 hE hG]
  set S : Set Ω := {ω | 0 ≤ h ω}
  have hS : MeasurableSet[𝒢] S := measurableSet_le measurable_const hsm.measurable
  have h1 : ∫ ω in S, |h ω| ∂P = ∫ ω in S, h ω ∂P :=
    setIntegral_congr_fun (h𝒢 _ hS) fun ω hω => abs_of_nonneg hω
  have h2 : ∫ ω in Sᶜ, |h ω| ∂P = -∫ ω in Sᶜ, h ω ∂P := by
    rw [← integral_neg]
    exact setIntegral_congr_fun (h𝒢 _ hS.compl) fun ω hω => abs_of_neg (not_le.1 hω)
  rw [← integral_add_compl (h𝒢 _ hS) hint.abs, h1, h2, key S hS, key Sᶜ hS.compl]
  have e1 := (abs_le.1 (H S hS)).2
  have e2 := (abs_le.1 (H Sᶜ hS.compl)).1
  linarith

/-- **Pull-out** of a bounded `𝒢`-measurable weight. -/
theorem integral_indicator_eq_condExp (h𝒢 : 𝒢 ≤ mΩ) {B : Set Ω} (hB : MeasurableSet B)
    {w : Ω → ℝ} (hw : Measurable[𝒢] w) {M : ℝ} (hwM : ∀ ω, 0 ≤ w ω ∧ w ω ≤ M) :
    ∫ ω, B.indicator w ω ∂P = ∫ ω, w ω * P[B.indicator (fun _ => (1 : ℝ)) | 𝒢] ω ∂P := by
  have hws : StronglyMeasurable[𝒢] w := hw.stronglyMeasurable
  have hwb : ∀ᵐ ω ∂P, ‖w ω‖ ≤ M := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hwM ω).1]; exact (hwM ω).2
  have hB1 : Integrable (B.indicator (fun _ => (1 : ℝ))) P := (integrable_const _).indicator hB
  have hwB : Integrable (w * B.indicator (fun _ => (1 : ℝ))) P :=
    hB1.bdd_mul (hws.mono h𝒢).aestronglyMeasurable hwb
  have e : B.indicator w = w * B.indicator (fun _ => (1 : ℝ)) := by
    funext ω; by_cases h : ω ∈ B <;> simp [indicator, h]
  rw [e, ← integral_condExp h𝒢]
  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hws hwB hB1)

/-- **Weighted decorrelation.** -/
theorem abs_integral_inter_sub_le (h𝒢 : 𝒢 ≤ mΩ) {A₁ A₂ E₁ E₂ : Set Ω} (hA₁ : MeasurableSet A₁)
    (hA₂ : MeasurableSet A₂) (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂)
    (hCA : P[(A₁ ∩ A₂).indicator (fun _ => (1 : ℝ)) | 𝒢] =ᵐ[P]
      P[A₁.indicator (fun _ => (1 : ℝ)) | 𝒢] * P[A₂.indicator (fun _ => (1 : ℝ)) | 𝒢])
    (hCE : P[(E₁ ∩ E₂).indicator (fun _ => (1 : ℝ)) | 𝒢] =ᵐ[P]
      P[E₁.indicator (fun _ => (1 : ℝ)) | 𝒢] * P[E₂.indicator (fun _ => (1 : ℝ)) | 𝒢])
    {a b e₁ e₂ : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (H₁ : ∀ G, MeasurableSet[𝒢] G → |P.real (A₁ ∩ G) - a * P.real (E₁ ∩ G)| ≤ e₁)
    (H₂ : ∀ G, MeasurableSet[𝒢] G → |P.real (A₂ ∩ G) - b * P.real (E₂ ∩ G)| ≤ e₂)
    {w : Ω → ℝ} (hw : Measurable[𝒢] w) {M : ℝ} (hwM : ∀ ω, 0 ≤ w ω ∧ w ω ≤ M) :
    |∫ ω, (A₁ ∩ A₂).indicator w ω ∂P - a * b * ∫ ω, (E₁ ∩ E₂).indicator w ω ∂P| ≤
      M * (2 * e₁ + 2 * e₂) := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure P
  have hM0 : 0 ≤ M := (hwM ω₀).1.trans (hwM ω₀).2
  set f₁ := P[A₁.indicator (fun _ => (1 : ℝ)) | 𝒢]
  set f₂ := P[A₂.indicator (fun _ => (1 : ℝ)) | 𝒢]
  set k₁ := P[E₁.indicator (fun _ => (1 : ℝ)) | 𝒢]
  set k₂ := P[E₂.indicator (fun _ => (1 : ℝ)) | 𝒢]
  have hws : StronglyMeasurable[𝒢] w := hw.stronglyMeasurable
  have hwb : ∀ᵐ ω ∂P, ‖w ω‖ ≤ M := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hwM ω).1]; exact (hwM ω).2
  have hwa := (hws.mono h𝒢).aestronglyMeasurable (μ := P)
  have iA : Integrable (fun ω => w ω * P[(A₁ ∩ A₂).indicator (fun _ => (1 : ℝ)) | 𝒢] ω) P :=
    integrable_condExp.bdd_mul hwa hwb
  have iE : Integrable (fun ω => w ω * P[(E₁ ∩ E₂).indicator (fun _ => (1 : ℝ)) | 𝒢] ω) P :=
    integrable_condExp.bdd_mul hwa hwb
  have i₁ : Integrable (fun ω => |f₁ ω - a * k₁ ω|) P :=
    (integrable_condExp.sub (integrable_condExp.const_mul a)).abs
  have i₂ : Integrable (fun ω => |f₂ ω - b * k₂ ω|) P :=
    (integrable_condExp.sub (integrable_condExp.const_mul b)).abs
  rw [integral_indicator_eq_condExp h𝒢 (hA₁.inter hA₂) hw hwM,
    integral_indicator_eq_condExp h𝒢 (hE₁.inter hE₂) hw hwM, ← integral_const_mul,
    ← integral_sub iA (iE.const_mul _)]
  have hf₂ := Thm18Asm.condExp_indicator_one_mem_Icc (P := P) h𝒢 hA₂
  have hk₁ := Thm18Asm.condExp_indicator_one_mem_Icc (P := P) h𝒢 hE₁
  have hpt : ∀ᵐ ω ∂P, |w ω * P[(A₁ ∩ A₂).indicator (fun _ => (1 : ℝ)) | 𝒢] ω -
      a * b * (w ω * P[(E₁ ∩ E₂).indicator (fun _ => (1 : ℝ)) | 𝒢] ω)| ≤
      M * (|f₁ ω - a * k₁ ω| + |f₂ ω - b * k₂ ω|) := by
    filter_upwards [hCA, hCE, hf₂, hk₁] with ω c1 c2 j2 j1
    rw [c1, c2]
    simp only [Pi.mul_apply]
    have e : w ω * (f₁ ω * f₂ ω) - a * b * (w ω * (k₁ ω * k₂ ω)) =
        w ω * ((f₁ ω - a * k₁ ω) * f₂ ω + (a * k₁ ω) * (f₂ ω - b * k₂ ω)) := by ring
    rw [e, abs_mul, abs_of_nonneg (hwM ω).1]
    refine mul_le_mul (hwM ω).2 ?_ (abs_nonneg _) hM0
    have hak : |a * k₁ ω| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg ha.1 j1.1)]
      exact mul_le_one₀ ha.2 j1.1 j1.2
    calc |(f₁ ω - a * k₁ ω) * f₂ ω + (a * k₁ ω) * (f₂ ω - b * k₂ ω)|
        ≤ |(f₁ ω - a * k₁ ω) * f₂ ω| + |(a * k₁ ω) * (f₂ ω - b * k₂ ω)| := abs_add_le _ _
      _ = |f₁ ω - a * k₁ ω| * |f₂ ω| + |a * k₁ ω| * |f₂ ω - b * k₂ ω| := by
          rw [abs_mul, abs_mul]
      _ ≤ |f₁ ω - a * k₁ ω| * 1 + 1 * |f₂ ω - b * k₂ ω| := by
          gcongr
          rw [abs_le]; constructor <;> linarith [j2.1, j2.2]
      _ = _ := by ring
  refine (abs_integral_le_integral_abs).trans ((integral_mono_ae
    (iA.sub (iE.const_mul _)).abs ((i₁.add i₂).const_mul M) hpt).trans ?_)
  rw [integral_const_mul, Pi.add_def, integral_add i₁ i₂]
  have := integral_abs_condExp_sub_le h𝒢 hA₁ hE₁ a e₁ H₁
  have := integral_abs_condExp_sub_le h𝒢 hA₂ hE₂ b e₂ H₂
  gcongr

/-- Replacing the event of a weighted integral costs at most `M` times the symmetric
difference. -/
theorem abs_integral_indicator_sub_le {S S' : Set Ω} (hS : MeasurableSet S)
    (hS' : MeasurableSet S') {w : Ω → ℝ} (hw : Measurable w) {M : ℝ}
    (hwM : ∀ ω, 0 ≤ w ω ∧ w ω ≤ M) :
    |∫ ω, S.indicator w ω ∂P - ∫ ω, S'.indicator w ω ∂P| ≤ M * P.real (S ∆ S') := by
  have hwb : ∀ᵐ ω ∂P, ‖w ω‖ ≤ M := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hwM ω).1]; exact (hwM ω).2
  have iw : Integrable w P := Integrable.of_bound hw.aestronglyMeasurable M hwb
  rw [← integral_sub (iw.indicator hS) (iw.indicator hS'), mul_comm M, ← smul_eq_mul,
    ← integral_indicator_const _ (hS.symmDiff hS')]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    ((integrable_const M).indicator (hS.symmDiff hS')) (Filter.Eventually.of_forall fun ω => ?_))
  have h0 := hwM ω
  by_cases h1 : ω ∈ S <;> by_cases h2 : ω ∈ S' <;>
    simp [indicator, h1, h2, mem_symmDiff, abs_of_nonneg h0.1, h0.2]

end R18
end QuantumZipper
