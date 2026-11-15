/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedWire

/-!
# The null-completed σ-algebra of a fixed pair of incoming walls

Packet PROVE-STRIPSYS-PERQ. The rational-history record is the existing `PocketStopWalls.fullHist`.
Continuous walls are measurable at every real time from this record. Null sets lie in the counterflow's
initial driving σ-algebra, so this choice meets the marked-stop bound without recording any other wall.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketWordPerQ

open Sec6 PocketStopWalls PocketStopMarked

variable {Ω : Type*}

/-- The σ-algebra of the two full incoming histories, together with measurable null sets. -/
abbrev wallsSigma [mΩ : MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ Ito.nullSets P

/-- Every time evaluation of a continuous wall is measurable from the full rational histories. -/
theorem measurable_eval_fullHist {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ}
    (hc : ∀ i ω, Continuous (η i ω)) (i : Fin k) (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (fullHist η) inferInstance] (fun ω => η i ω t) := by
  let : MeasurableSpace Ω := MeasurableSpace.comap (fullHist η) inferInstance
  have hrat : ∀ q : ℚ≥0,
      Measurable[MeasurableSpace.comap (fullHist η) inferInstance] (fun ω => η i ω q) := fun q => by
    have h := (measurable_pi_apply q).comp
      (measurable_snd.comp ((measurable_pi_apply i).comp (comap_measurable (fullHist η))))
    change Measurable[MeasurableSpace.comap (fullHist η) inferInstance]
      (fun ω => (fullHist η ω i).2 q) at h
    simpa only [fullHist, histOf, stopCoord, le_top, ↓reduceIte, pathCoord] using h
  obtain ⟨s, -, hs, hst⟩ := Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)
  let q : ℕ → ℚ≥0 := fun n => ⟨s n, Rat.cast_nonneg.1 (t.coe_nonneg.trans (hs n).le)⟩
  have hq : Tendsto (fun n => (q n : ℝ≥0)) atTop (𝓝 t) :=
    NNReal.tendsto_coe.1 hst
  exact measurable_of_tendsto_metrizable (fun n => hrat (q n))
    (tendsto_pi_nhds.2 fun ω => ((hc i ω).tendsto t).comp hq)

/-- The first wall's evaluations are events of the fixed-pair σ-algebra. -/
theorem measurable_right_wallsSigma [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (t : ℝ≥0) :
    Measurable[wallsSigma P R L] (fun ω => R ω t) := by
  have hc : ∀ i : Fin 2, ∀ ω, Continuous (![R, L] i ω) := by
    intro i ω
    fin_cases i
    · exact hRc ω
    · exact hLc ω
  exact (measurable_eval_fullHist hc 0 t).mono le_sup_left le_rfl

/-- The second wall's evaluations are events of the same fixed-pair σ-algebra. -/
theorem measurable_left_wallsSigma [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (t : ℝ≥0) :
    Measurable[wallsSigma P R L] (fun ω => L ω t) := by
  have hc : ∀ i : Fin 2, ∀ ω, Continuous (![R, L] i ω) := by
    intro i ω
    fin_cases i
    · exact hRc ω
    · exact hLc ω
  exact (measurable_eval_fullHist hc 1 t).mono le_sup_left le_rfl

/-- Measurable walls give a sub-σ-algebra of the ambient measurable space. -/
theorem wallsSigma_le [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R L : Ω → ℝ≥0 → ℂ}
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t) :
    wallsSigma P R L ≤ mΩ := by
  refine sup_le (measurable_fullHist ?_).comap_le (Ito.nullSets_le P)
  intro i t
  fin_cases i
  · exact hRm t
  · exact hLm t

/-- The fixed-pair σ-algebra satisfies the marked-stop initial-information bound. -/
theorem wallsSigma_le_drivingFiltration [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ)
    (R L : Ω → ℝ≥0 → ℂ) :
    wallsSigma P R L ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0 :=
  le_drivingFiltration_zero_of_le hX le_rfl

end InteractingSLE.Sec7.PocketWordPerQ
