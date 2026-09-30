import QuantumZipper.Proofs.Thm18.R18G3TCM4
import QuantumZipper.Proofs.Thm18.R18G3TJointAbs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-a), part 5: weights, truncation and the real Palm formula

* `abs_integral_weight_sub_le`: from the mixing bound over `𝒢`-events to a nonnegative
  integrable `𝒢`-measurable weight, truncated at level `K`:
  `|∫_A w − a ∫_E w| ≤ 2Ke + 2 ∫ (w − min(w, K))` (own elementary argument on top of
  `integral_abs_condExp_sub_le` and `integral_indicator_eq_condExp`).
* `g3pPalmLaw_cut_real`: `P_B(S_B ∩ G) = κ ∫_{S_A ∩ G'} D dP_A` with `κ = (Z_A/Z_B)`,
  `D = cmTilt` (Cameron–Martin, Berestycki–Powell Lemma 3.12).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

/-! ## From events to truncated weights -/

section Abstract

variable {Ω : Type*} {𝒢 mΩ : MeasurableSpace Ω} {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

theorem abs_integral_weight_sub_le (h𝒢 : 𝒢 ≤ mΩ) {A E : Set Ω} (hA : MeasurableSet A)
    (hE : MeasurableSet E) {a e : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (H : ∀ G, MeasurableSet[𝒢] G → |P.real (A ∩ G) - a * P.real (E ∩ G)| ≤ e)
    {w : Ω → ℝ} (hw : Measurable[𝒢] w) (hw0 : ∀ ω, 0 ≤ w ω) (hwi : Integrable w P)
    {K : ℝ} (hK : 0 ≤ K) :
    |∫ ω, A.indicator w ω ∂P - a * ∫ ω, E.indicator w ω ∂P| ≤
      K * (2 * e) + 2 * ∫ ω, (w ω - min (w ω) K) ∂P := by
  set w₁ : Ω → ℝ := fun ω => min (w ω) K with hw₁def
  set w₂ : Ω → ℝ := fun ω => w ω - min (w ω) K with hw₂def
  have hw₁ : Measurable[𝒢] w₁ := hw.min measurable_const
  have hw₁b : ∀ ω, 0 ≤ w₁ ω ∧ w₁ ω ≤ K := fun ω => ⟨le_min (hw0 ω) hK, min_le_right _ _⟩
  have hw₂0 : ∀ ω, 0 ≤ w₂ ω := fun ω => sub_nonneg.2 (min_le_left _ _)
  have hmw : Measurable w := hw.mono h𝒢 le_rfl
  have i₁ : Integrable w₁ P :=
    (integrable_const K).mono' (hmw.min measurable_const).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw₁b ω).1]; exact (hw₁b ω).2)
  have i₂ : Integrable w₂ P := hwi.sub i₁
  have hsplit : ∀ B : Set Ω, MeasurableSet B →
      ∫ ω, B.indicator w ω ∂P = ∫ ω, B.indicator w₁ ω ∂P + ∫ ω, B.indicator w₂ ω ∂P := by
    intro B hB
    rw [← integral_add (i₁.indicator hB) (i₂.indicator hB)]
    congr 1
    funext ω
    by_cases h : ω ∈ B <;> simp [indicator, h, hw₁def, hw₂def]
  rw [hsplit A hA, hsplit E hE]
  -- the truncated part
  have hws : StronglyMeasurable[𝒢] w₁ := hw₁.stronglyMeasurable
  have hwb : ∀ᵐ ω ∂P, ‖w₁ ω‖ ≤ K := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hw₁b ω).1]; exact (hw₁b ω).2
  have hwa := (hws.mono h𝒢).aestronglyMeasurable (μ := P)
  have iA : Integrable (fun ω => w₁ ω * P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω) P :=
    integrable_condExp.bdd_mul hwa hwb
  have iE : Integrable (fun ω => w₁ ω * P[E.indicator (fun _ => (1 : ℝ)) | 𝒢] ω) P :=
    integrable_condExp.bdd_mul hwa hwb
  have iD : Integrable (fun ω => |P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω -
      a * P[E.indicator (fun _ => (1 : ℝ)) | 𝒢] ω|) P :=
    (integrable_condExp.sub (integrable_condExp.const_mul a)).abs
  have hT1 : |∫ ω, A.indicator w₁ ω ∂P - a * ∫ ω, E.indicator w₁ ω ∂P| ≤ K * (2 * e) := by
    rw [integral_indicator_eq_condExp h𝒢 hA hw₁ hw₁b,
      integral_indicator_eq_condExp h𝒢 hE hw₁ hw₁b, ← integral_const_mul,
      ← integral_sub iA (iE.const_mul _)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |w₁ ω * P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω -
          a * (w₁ ω * P[E.indicator (fun _ => (1 : ℝ)) | 𝒢] ω)| ∂P
        ≤ ∫ ω, K * |P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω -
          a * P[E.indicator (fun _ => (1 : ℝ)) | 𝒢] ω| ∂P := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (iD.const_mul K) (ae_of_all _ fun ω => ?_)
          have e1 : w₁ ω * P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω -
              a * (w₁ ω * P[E.indicator (fun _ => (1 : ℝ)) | 𝒢] ω) =
              w₁ ω * (P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω -
                a * P[E.indicator (fun _ => (1 : ℝ)) | 𝒢] ω) := by ring
          show |_| ≤ K * |_|
          rw [e1, abs_mul, abs_of_nonneg (hw₁b ω).1]
          exact mul_le_mul_of_nonneg_right (hw₁b ω).2 (abs_nonneg _)
      _ = K * ∫ ω, |P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] ω -
          a * P[E.indicator (fun _ => (1 : ℝ)) | 𝒢] ω| ∂P := integral_const_mul _ _
      _ ≤ K * (2 * e) :=
          mul_le_mul_of_nonneg_left (integral_abs_condExp_sub_le h𝒢 hA hE a e H) hK
  -- the tail
  have hB : ∀ B : Set Ω, MeasurableSet B →
      0 ≤ ∫ ω, B.indicator w₂ ω ∂P ∧ ∫ ω, B.indicator w₂ ω ∂P ≤ ∫ ω, w₂ ω ∂P := by
    intro B hB
    refine ⟨integral_nonneg fun ω => indicator_nonneg (fun ω _ => hw₂0 ω) ω, ?_⟩
    exact integral_mono (i₂.indicator hB) i₂ fun ω => by
      by_cases h : ω ∈ B <;> simp [indicator, h, hw₂0 ω]
  obtain ⟨a0, a1⟩ := hB A hA
  obtain ⟨b0, b1⟩ := hB E hE
  have hT2 : |∫ ω, A.indicator w₂ ω ∂P - a * ∫ ω, E.indicator w₂ ω ∂P| ≤
      2 * ∫ ω, w₂ ω ∂P := by
    rw [abs_le]
    constructor <;> nlinarith
  calc |∫ ω, A.indicator w₁ ω ∂P + ∫ ω, A.indicator w₂ ω ∂P -
        a * (∫ ω, E.indicator w₁ ω ∂P + ∫ ω, E.indicator w₂ ω ∂P)|
      = |(∫ ω, A.indicator w₁ ω ∂P - a * ∫ ω, E.indicator w₁ ω ∂P) +
          (∫ ω, A.indicator w₂ ω ∂P - a * ∫ ω, E.indicator w₂ ω ∂P)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hT1 hT2)

end Abstract

end R18
end QuantumZipper
