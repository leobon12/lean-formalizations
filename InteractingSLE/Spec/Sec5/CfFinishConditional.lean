/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishSeparated

/-!
# The record-kernel law from separated raw marks and physical locality

Packet PROVE-CFCHART2. Inverse classification discharges the word-type premise and
the earlier bounded-mean theorem discharges integrability. The remaining geometric
premises are explicit, and this conditional helper does not replace the source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfFinish

open CfGiven Exist.StagedLaw Restart Restart.DomainMarkov.K2 Sec7.PocketTraversal

/-- With the raw chart converted, physical member identities and strict separation
of the initial marks suffice for the conditional counterflow. The boundary-word
classification, deterministic erasure and field integrability are proved. -/
theorem ae_counterflow_of_separated_chart {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {R : Ω → RecData} (hR : Measurable R) {𝓐 : Filtration ℝ≥0 mΩ}
    (h𝒢 : MeasurableSpace.comap R inferInstance ≤ 𝓐 0)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : Measurable[MeasurableSpace.comap R inferInstance] xL)
    (hxR : Measurable[MeasurableSpace.comap R inferInstance] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω))
    {V : ℝ≥0 → Ω → ℝ} (hV0 : ∀ ω, V 0 ω = 0)
    (hVc : ∀ ω, Continuous fun t => V t ω) (hVa : StronglyAdapted 𝓐 V)
    (hthr : ∀ᵐ ω ∂P, FCDet.thr ρL ρR V xL xR ω = ⊤)
    (hchart : Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 V
      (geomLW V xL) (geomRW V xR) (fun _ => ⊤) (fun ω => cfChart (R ω))
      (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω))
    (hsep : ∀ᵐ ω ∂P,
      StrictAnti (xL ω) ∧ StrictMono (xR ω) ∧ xL ω 0 = 0 ∧ xR ω 0 = 0)
    (hlocal : HasSafeMembers P 𝓐 univ (fun _ => ⊤) V
      (fun ω => imgField κ (R ω) (h ω))) :
    ∀ᵐ ω₀ ∂P,
      IsCenteredCounterflowDriver κ (condExpKernel P (MeasurableSpace.comap R inferInstance) ω₀)
        (fun ω => recField κ (R ω₀) (h ω)) V (fun _ => ⊤) := by
  have hdual : 0 < 16 / κ := div_pos (by norm_num) hκ
  obtain ⟨_, _, eL, eR, _, _, heL, heR, htype⟩ := exists_erasure_flowType_ae hdual ρL ρR hsep
  exact CfResume.ae_counterflow_of_erased_chart hκ eL eR heL heR hh hR h𝒢
    hxL hxR hxL0 hxR0 hxLa hxRm hV0 hVc hVa hthr hchart htype hlocal

end InteractingSLE.Sec5.CfFinish
