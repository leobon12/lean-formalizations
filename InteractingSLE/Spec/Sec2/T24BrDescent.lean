import InteractingSLE.Spec.Sec2.T24BrBefore
import MathFin.Probability.Martingales.MartingaleSetIntegral
import InteractingSLE.Spec.Sec2.MartingaleExtract

/-!
# Descent of stopped martingales to the curve filtration

Right continuity makes a curve event supported on survival measurable at the same
time in the evolution filtration. Testing increments on that event gives descent;
after the stopping time both increments vanish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {Q : Measure Ω'} {π : Ω' → Ω} {𝓕' : Filtration ℝ≥0 mΩ'}

/-- A martingale version of a stopped process on an extension descends to the curve space. -/
theorem martingale_curveFiltration_of_stopped_pullback [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω' → ℝ≥0∞} {η : ℝ≥0 → Ω → ℂ}
    (hη : ∀ t, StronglyMeasurable (η t)) (hπ : MeasurePreserving π Q P)
    (hW : AdaptedBefore 𝓕' ζ (fun t ω => W t (π ω)))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation (Filtration.natural η hη) P) σ)
    (hσζ : ∀ᵐ ω ∂Q, σ (π ω) ≤ ζ ω)
    {X : ℝ≥0 → Ω → ℝ}
    (hXa : StronglyAdapted (usualAugmentation (Filtration.natural η hη) P) X)
    (hstop : ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
      σ ω ≤ (s : WithTop ℝ≥0) → σ ω ≤ (t : WithTop ℝ≥0) → X s ω = X t ω)
    {M : ℝ≥0 → Ω' → ℝ} (hM : Martingale M (usualAugmentation 𝓕' Q) Q)
    (he : ∀ t, (fun ω => X t (π ω)) =ᵐ[Q] M t) :
    Martingale X (usualAugmentation (Filtration.natural η hη) P) P := by
  let 𝓖 := usualAugmentation (Filtration.natural η hη) P
  have hXm (t : ℝ≥0) : StronglyMeasurable (X t) := (hXa t).mono (𝓖.le t)
  have hXi (t : ℝ≥0) : Integrable (X t) P :=
    (hπ.integrable_comp (hXm t).aestronglyMeasurable).1 ((hM.integrable t).congr (he t).symm)
  refine martingale_iff_setIntegral_eq.2 ⟨hXa, hXi, ?_⟩
  intro s t hst A hA
  have hAm : MeasurableSet A := 𝓖.le s _ hA
  let D : Set Ω' := π ⁻¹' A ∩ {ω | (s : WithTop ℝ≥0) < σ (π ω)}
  have hD : MeasurableSet[usualAugmentation 𝓕' Q s] D :=
    curve_event_before_stop_measurable hη hπ hW hgen hσ hσζ le_rfl hA
  have hDm : MeasurableSet D := (usualAugmentation 𝓕' Q).le s _ hD
  have hzero : (∫ ω in D, (X s (π ω) - X t (π ω)) ∂Q) = 0 := by
    calc
      _ = ∫ ω in D, (M s ω - M t ω) ∂Q := integral_congr_ae
        (ae_restrict_of_ae ((he s).sub (he t)))
      _ = (∫ ω in D, M s ω ∂Q) - ∫ ω in D, M t ω ∂Q :=
        integral_sub (hM.integrable s).integrableOn (hM.integrable t).integrableOn
      _ = 0 := sub_eq_zero.2 (hM.setIntegral_eq hst hD)
  have hsub : (∫ ω in π ⁻¹' A, (X s (π ω) - X t (π ω)) ∂Q) = 0 := by
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      (hπ.measurable hAm).nullMeasurableSet (inter_subset_left : D ⊆ π ⁻¹' A)]
    · exact hzero
    · filter_upwards [hπ.quasiMeasurePreserving.ae hstop] with ω hω hmem
      have hle : σ (π ω) ≤ (s : WithTop ℝ≥0) := by
        by_contra hh
        exact hmem.2 ⟨hmem.1, lt_of_not_ge hh⟩
      exact sub_eq_zero.2 (hω s t hle (hle.trans (by exact_mod_cast hst)))
  have hmap := setIntegral_map (μ := Q) (g := π) hAm
    ((hXm s).sub (hXm t)).aestronglyMeasurable
    hπ.measurable.aemeasurable
  rw [hπ.map_eq] at hmap
  have hz : (∫ ω in A, (X s ω - X t ω) ∂P) = 0 := hmap.trans hsub
  rw [integral_sub (hXi s).integrableOn (hXi t).integrableOn] at hz
  exact sub_eq_zero.1 hz

/-- Descent for a supplied curve-localizing sequence, independently of the observable. -/
theorem isLocalMartingaleBefore_curveFiltration_of_stopped_pullback
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → WithTop ℝ≥0} {η : ℝ≥0 → Ω → ℂ}
    (hη : ∀ t, StronglyMeasurable (η t)) (hπ : MeasurePreserving π Q P)
    (hW : AdaptedBefore 𝓕' (ζ ∘ π) (fun t ω => W t (π ω)))
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    {X : ℝ≥0 → Ω → ℝ} {σ : ℕ → Ω → WithTop ℝ≥0}
    (hσ : ∀ n, IsStoppingTime (usualAugmentation (Filtration.natural η hη) P) (σ n))
    (hle : ∀ n ω, σ n ω ≤ ζ ω)
    (hex : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < ζ ω →
      ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω)
    (ha : ∀ n, StronglyAdapted (usualAugmentation (Filtration.natural η hη) P)
      (stoppedProcess X (σ n)))
    (hm : ∀ n, ∃ M : ℝ≥0 → Ω' → ℝ, Martingale M (usualAugmentation 𝓕' Q) Q ∧
      ∀ t, (fun ω => stoppedProcess X (σ n) t (π ω)) =ᵐ[Q] M t) :
    MartChar.IsLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P ζ X := by
  refine ⟨σ, hσ, hle, hex, fun n => ?_⟩
  obtain ⟨M, hM, he⟩ := hm n
  apply martingale_curveFiltration_of_stopped_pullback hη hπ hW hgen (hσ n)
    (Eventually.of_forall fun ω => hle n (π ω)) (ha n)
    (Eventually.of_forall fun ω s t hs ht => ?_) hM he
  simp only [stoppedProcess, min_eq_right hs, min_eq_right ht]

end InteractingSLE.Sec2.T24Bridge
