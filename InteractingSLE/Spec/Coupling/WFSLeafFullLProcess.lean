/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafFullLCompare

/-!
# Transferring closed processes from the full evolution to its cutoff

Continuous full-history cylinder means extend by the proved L¹ density and
closure theorems. For an observable of a stopping cutoff, the full closed
process is already adapted and closed in the cutoff-driving filtration.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction

namespace InteractingSLE.WFS

open LawUnique

/-- Full-filtration closing identities for a cutoff observable imply both
adaptedness and closing in the cutoff filtration, for the same process. -/
theorem stronglyAdapted_closed_cutoff_of_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞}
    (hXζ : IsMeasurableKilledDriving W VL VR ζ)
    (hXV : IsMeasurableKilledDriving W VL VR V) (hle : ∀ ω, V ω ≤ ζ ω)
    (hV : IsStoppingTime (drivingFiltration P hXζ) fun ω => (V ω : WithTop ℝ≥0))
    {f : ℝ≥0∞ → ℝ} (hf : Measurable f) (hi : Integrable (fun ω => f (V ω)) P)
    {X : ℝ≥0 → Ω → ℝ} (hXa : StronglyAdapted (drivingFiltration P hXζ) X)
    (hclosed : ∀ t, X t =ᵐ[P] P[fun ω => f (V ω) | drivingFiltration P hXζ t]) :
    StronglyAdapted (drivingFiltration P hXV) X ∧
      ∀ t, X t =ᵐ[P] P[fun ω => f (V ω) | drivingFiltration P hXV t] := by
  have he (t : ℝ≥0) : X t =ᵐ[P] P[fun ω => f (V ω) | drivingFiltration P hXV t] :=
    (hclosed t).trans (condExp_cutoff_observable_eq_full hXζ hXV hle hV hf hi t).symm
  refine ⟨fun t => Measurable.stronglyMeasurable ?_, he⟩
  exact Sec2.Restart.measurable_of_ae_eq_of_null ((drivingFiltration P hXV).le t)
    (fun A hA hA0 => Ito.nullSets_le_usualAugmentation _ P t A
      (MeasurableSpace.measurableSet_generateFrom ⟨hA, hA0⟩))
    stronglyMeasurable_condExp.measurable
    ((hXa t).measurable.mono ((drivingFiltration P hXζ).le t) le_rfl) (he t).symm

/-- Continuous versions of finite-history cylinder means suffice for every
integrable Borel function of that history in the same filtration. Density and
L¹ closure are the already proved results, rather than additional inputs. -/
theorem exists_continuous_closed_of_history_cylinders
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (𝓓 : Filtration ℝ≥0 mΩ) (hn : ∀ t, nullSigma P ≤ 𝓓 t)
    {nL nR : ℕ} {Y : Ω → HistorySpace nL nR} (hY : Measurable Y)
    {F : HistorySpace nL nR → ℝ} (hFm : Measurable F) (hFi : Integrable F (P.map Y))
    (hcyl : ∀ n : ℕ, ∀ g : HistoryWindow nL nR n →ᵇ ℝ,
      ∃ M : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 M ∧
        (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
        ∀ t, M t =ᵐ[P] P[fun ω => g (historyWindow n (Y ω)) | 𝓓 t]) :
    ∃ X : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 X ∧
      (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) ∧
      ∀ t, X t =ᵐ[P] P[fun ω => F (Y ω) | 𝓓 t] := by
  have hZ : Integrable (fun ω => F (Y ω)) P := hFi.comp_measurable hY
  apply exists_continuous_closed_process_of_L1_approx 𝓓 hn hZ
  intro ε hε
  obtain ⟨n, g, hg⟩ := exists_historyWindow_comp_L1_approx (P := P) hY hFm hFi hε
  refine ⟨fun ω => g (historyWindow n (Y ω)), integrable_historyWindow_comp hY g,
    ?_, hcyl n g⟩
  calc
    _ = ∫ ω, ‖F (Y ω) - g (historyWindow n (Y ω))‖ ∂P :=
      integral_congr_ae (ae_of_all _ fun _ => norm_sub_rev _ _)
    _ < ε := hg

end InteractingSLE.WFS
