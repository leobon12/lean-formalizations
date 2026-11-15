/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfNextPositive
import InteractingSLE.Spec.Supplement.HullDetGenLaw

/-!
# Physical member locality for an original infinite-lifetime coupling

Packet PROVE-CFCHART2. Specialize the existing fixed-chart time-change locality
theorem to the identity chart and clock. This supplies the zero-prefix locality input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfNext

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 LawUnique GlueCond

/-- Every infinite-lifetime optional hull coupling has the physical member identities
in its own driving filtration, with lifetime replaced by infinity. -/
theorem hasSafeMembers_optional_top {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    HasSafeMembers P (drivingFiltration P hX) univ (fun _ => ⊤) W h := by
  have hg := Aux50Hit.ae_isGoodPath hC.1 hζ
  have hℓ : ∀ q : ℝ≥0, IsStoppingTime (drivingFiltration P hX)
      (fun _ : Ω => (q : WithTop ℝ≥0)) := fun q => isStoppingTime_const _ q
  have hℓζ : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ((q : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω :=
    fun q => hζ.mono fun ω hω => hω ▸ ENNReal.coe_lt_top
  have hreg : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → Mean.IsDrvReg W (fun _ => ⊤) ω :=
    hg.mono fun ω hω _ => ⟨hω.continuous.continuousOn, hω.2.1⟩
  have hK : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → (q : ℝ≥0∞) < ⊤ →
      Chart.id.2.1 '' (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) q) =
        H \ fwdHull (fun r : ℝ => W r.toNNReal ω) (((q : WithTop ℝ≥0)).untopD 0 : ℝ≥0) :=
    fun q => ae_of_all _ fun ω _ _ => by rw [WithTop.untopD_coe]; exact image_id' _
  have hBK : ∀ q : ℝ≥0, ∀ᵐ ω ∂P,
      hullAt q (killedHistory W VL VR ζ ω) =
        fwdHull (fun r : ℝ => W r.toNNReal ω) (((q : WithTop ℝ≥0)).untopD 0 : ℝ≥0) :=
    fun q => hg.mono fun ω hω => by
      rw [WithTop.untopD_coe]
      exact Aux50Hit.regHull_stopHistory_cstop hω q
  have hmem := Supp8.HullDetGen.hasSafeMembers_of_timeChange hκ hC hX hℓ hℓζ
    (𝓗 := drivingFiltration P hX) (fun q => by rw [IsStoppingTime.measurableSpace_const])
    Chart.isConformal_id continuousOn_const
    (fun z _ => InnerProductSpace.harmonicAt_const (0 : ℝ)) 0 0 hreg hK
    (fun q ω => hullAt q (killedHistory W VL VR ζ ω))
    (fun q => (measurable_hullAt q).comp (measurable_killedHistory hX))
    (fun q ω => hullAt_relClosed q _) hBK
  have he : (fun ω => Chart.chartTransport Chart.isConformal_id 1 0 0 (h ω)) = h := by
    funext ω
    exact ((isChartTransport_id 0 (h ω)).eq_chartTransport Chart.isConformal_id
      (Chart.locallyIntegrableOn_of_continuousOn continuousOn_const)).symm
  rwa [he] at hmem

end InteractingSLE.Sec5.CfNext
