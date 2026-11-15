import InteractingSLE.Spec.Sec2.T24BrInit
import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Spec.Supplement.LPTrace
import MathFin.Probability.Martingales.BoundedLocalMartingale

/-!
# Theorem 2.4: transferring from driver information to curve information

`LP.traceAt` reads only the driver up to the evaluation time. Its landed tip identity
therefore makes the generating curve adapted to the usual augmentation of any filtration
in which the driver is adapted. The final lemma reuses the smaller-filtration martingale
theorem. These lemmas concern an everywhere-adapted driver; localization before a lifetime
is a separate obligation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Ambient-measurable modifications are measurable in the usual augmentation. -/
theorem measurable_usualAugmentation_of_ae_eq {f g : Ω → ℂ} (hf : Measurable f)
    {t : ℝ≥0} (hg : Measurable[𝓕 t] g) (heq : f =ᵐ[P] g) :
    Measurable[usualAugmentation 𝓕 P t] f := by
  have hgm := hg.mono (𝓕.le t) le_rfl
  let D : Set Ω := {ω | f ω ≠ g ω}
  have hDm : MeasurableSet D := (measurableSet_eq_fun hf hgm).compl
  have hD0 : P D = 0 := ae_iff.1 heq
  have hD : MeasurableSet[usualAugmentation 𝓕 P t] D :=
    Ito.measurableSet_usualAugmentation_of_null hDm hD0 t
  intro A hA
  have hbadm : MeasurableSet (D ∩ f ⁻¹' A) := hDm.inter (hf hA)
  have hbad0 : P (D ∩ f ⁻¹' A) = 0 := measure_mono_null inter_subset_left hD0
  have he : f ⁻¹' A = (Dᶜ ∩ g ⁻¹' A) ∪ (D ∩ f ⁻¹' A) := by
    ext ω
    by_cases hω : f ω = g ω <;> simp [D, hω]
  rw [he]
  exact (hD.compl.inter (Ito.le_usualAugmentation 𝓕 P t _ (hg hA))).union
    (Ito.measurableSet_usualAugmentation_of_null hbadm hbad0 t)

/-- The trace selector at time `t` is measurable using only driver evaluations before `t`. -/
theorem measurable_traceAt_of_adapted {W : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    (hW : ∀ s ≤ t, Measurable[𝓕 t] (W s)) :
    Measurable[𝓕 t] fun ω => LP.traceAt t (fun s => W s ω) := by
  let : MeasurableSpace Ω := 𝓕 t
  have hm : Measurable[𝓕 t] fun ω => fun s => W (min s t) ω :=
    measurable_pi_iff.2 fun s => hW _ (min_le_right s t)
  have he : (fun ω => LP.traceAt t (fun s => W s ω)) =
      fun ω => LP.traceAt t (fun s => W (min s t) ω) := by
    funext ω
    exact LP.traceAt_congr fun s hs => by rw [min_eq_left hs]
  rw [he]
  exact (LP.measurable_traceAt t).comp hm

/-- An a.s. generating curve is adapted to the augmented driver filtration. -/
theorem stronglyAdapted_curve_usualAugmentation {W : ℝ≥0 → Ω → ℝ}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hW : StronglyAdapted 𝓕 W)
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧
      IsGeneratingTrace (W · ω) ⊤ (η · ω)) :
    StronglyAdapted (usualAugmentation 𝓕 P) η := by
  intro t
  have hm : Measurable[𝓕 t] fun ω => LP.traceAt t (W · ω) :=
    measurable_traceAt_of_adapted fun s hs =>
      (hW s).measurable.mono (𝓕.mono hs) le_rfl
  have heq : η t =ᵐ[P] fun ω => LP.traceAt t (W · ω) := by
    filter_upwards [hgen] with ω hω
    exact (LP.traceAt_eq_of_isGeneratingTrace hω.2 hω.1.continuousOn
      (Sec7.SideHeight.w_zero_of_isGeneratingTrace hω.2 ENNReal.zero_lt_top) ENNReal.coe_lt_top).symm
  exact (measurable_usualAugmentation_of_ae_eq (hη t).measurable hm heq).stronglyMeasurable

/-- The usual augmentation is idempotent. -/
theorem usualAugmentation_idempotent :
    usualAugmentation (usualAugmentation 𝓕 P) P = usualAugmentation 𝓕 P := by
  rw [Ito.usualAugmentation_eq_rightCont, Ito.nullAugmented_usualAugmentation]
  exact Filtration.IsRightContinuous.eq

/-- The augmented curve filtration lies in the augmented filtration of an adapted driver. -/
theorem curveFiltration_le_usualAugmentation {W : ℝ≥0 → Ω → ℝ}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hW : StronglyAdapted 𝓕 W)
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧
      IsGeneratingTrace (W · ω) ⊤ (η · ω)) :
    usualAugmentation (Filtration.natural η hη) P ≤ usualAugmentation 𝓕 P := by
  have ha := stronglyAdapted_curve_usualAugmentation hη hW hgen
  have hn : Filtration.natural η hη ≤ usualAugmentation 𝓕 P := by
    intro t
    change (⨆ s ≤ t, MeasurableSpace.comap (η s) inferInstance) ≤ _
    exact iSup₂_le fun s hs =>
      (ha s).measurable.comap_le.trans ((usualAugmentation 𝓕 P).mono hs)
  have h := Ito.usualAugmentation_mono hn P
  rwa [usualAugmentation_idempotent] at h

/-- A driver-filtration martingale adapted to the curve filtration transfers to that filtration. -/
theorem martingale_curveFiltration [IsFiniteMeasure P] {W : ℝ≥0 → Ω → ℝ}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hW : StronglyAdapted 𝓕 W)
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧
      IsGeneratingTrace (W · ω) ⊤ (η · ω)) {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X (usualAugmentation 𝓕 P) P)
    (hXa : StronglyAdapted (usualAugmentation (Filtration.natural η hη) P) X) :
    Martingale X (usualAugmentation (Filtration.natural η hη) P) P :=
  MathFin.martingale_smaller_filtration (curveFiltration_le_usualAugmentation hη hW hgen)
    hX hXa

end InteractingSLE.Sec2.T24Bridge
