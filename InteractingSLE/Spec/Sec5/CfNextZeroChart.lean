/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfNextSource

/-!
# The infinity-source clause in the literal zero-prefix record chart

Packet PROVE-CFCHART2. At zero capacity the record's forward map and lift agree
everywhere with the identity chart, and its inverse agrees on the upper half-plane.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfNext

open CfGiven CfChart Exist Exist.Staged Exist.StagedLaw

/-- The forward map of a zero-prefix image chart is exactly inversion. -/
theorem cfChart_zero_fwd (e : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (cfChart (recOf 0 e)).1 = infinitySourceChart.1 := by
  funext z
  change infinitySourceChart.1 ((recChart (recOf 0 e)).1 z) = infinitySourceChart.1 z
  rw [recChart_eq, CfResume.rtime_recOf_zero,
    Theorem14.GW2aCont.loewner_zero_fwd (rdrv_zero (recOf 0 e))]
  rfl

/-- The lift of a zero-prefix image chart is exactly the inversion lift. -/
theorem cfChart_zero_lift (e : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (cfChart (recOf 0 e)).2.2 = infinitySourceChart.2.2 := by
  funext z
  change infinitySourceChart.2.2 ((recChart (recOf 0 e)).1 z) + (recChart (recOf 0 e)).2.2 z = _
  rw [recChart_eq, CfResume.rtime_recOf_zero,
    Theorem14.GW2aCont.loewner_zero_fwd (rdrv_zero (recOf 0 e)),
    Theorem14.GW2aCont.loewner_zero_lift]
  exact add_zero _

/-- On the upper half-plane the zero-prefix image inverse is inversion. -/
theorem cfChart_zero_inv (e : (ℝ≥0 → ℝ) × ℝ≥0∞) {z : ℂ} (hz : z ∈ H) :
    (cfChart (recOf 0 e)).2.1 z = infinitySourceChart.2.1 z :=
  CfResume.recChart_recOf_zero_inv e (WangWu.negInv_mem_H hz)

/-- The source-chart clause is the clause in the literal random zero-prefix chart. -/
theorem isChartCanon_zero_record {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {nL nR : ℕ} {α a k : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hcan : IsChartCanon α ρL ρR P 𝓐 W VL VR ζ (fun _ => infinitySourceChart) a k h) :
    IsChartCanon α ρL ρR P 𝓐 W VL VR ζ (fun ω => cfChart (recOf 0 (D ω))) a k h := by
  apply CfChart.IsChartCanon.congr_ae hcan
  intro t φ
  exact ae_of_all _ fun ω hE => by
    have hI : (cfChart (recOf 0 (D ω))).2.1 ''
        (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) t) =
        infinitySourceChart.2.1 '' (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) t) :=
      Set.image_congr fun z hz => cfChart_zero_inv (D ω) hz.1
    constructor
    · exact ⟨hE.1, hI ▸ hE.2⟩
    · simp only [chartRhs, cfChart_zero_fwd, cfChart_zero_lift, hI]

end InteractingSLE.Sec5.CfNext
