/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfCarryJoint

/-!
# The positive (4.4) construction from its raw physical member identities

Packet PROVE-CFCHART2. Combine the chart, reduction and physical members BEFORE
choosing chart data. The remaining input is explicitly the raw physical locality
assertion, rather than reduction or locality of an unrelated selected base.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfCarry

open CfConv CfGiven CfChart Exist Exist.Staged Exist.StagedLaw Restart LawUnique Lemma47Angle
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Restart.DomainMarkov.K2
open Sec7.StripHeights44 (IsHeightBounded44)

/-- The source's positive-prefix base, reduction and members in one joint witness,
conditional only on the explicitly stated physical locality assertion for raw data. -/
theorem exists_chartBase_reduction_members44_of_raw {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hθh : IsHeightBounded44 κ b J θ) (hπh : IsHeightBounded44 κ b J (π / 2))
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D)
    (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    {s : ℝ≥0} (hs : 0 < s) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω))
    (hraw :
      let W := fun t ω => (D ω).1 t
      let ζ := fun ω => (D ω).2
      let x := qxLT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        (flowLineXL b J 0) (flowLineXR b J 0)
      let y := qxRT κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        (flowLineXL b J 0) (flowLineXR b J 0)
      ∀ (h' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
        (VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ)
        (VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (N : Set Ω)
        (E : Set (Coarse (coarseSigma h' W VL VR ζ N) × HistorySpace 0 0))
        (hι : Measurable fun ω => (toCoarse (coarseSigma h' W VL VR ζ N) ω,
          Cond44Ref.cfHistory W' ζ' ω)),
        (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h' ω)) →
        IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0)
          (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) P 𝓕 W VL VR B ζ h' →
        P N = 0 → coarseSigma h' W VL VR ζ N ≤ mΩ → MeasurableSet E →
        (∀ p ∈ E, IsGood47 W VL VR ζ p) →
        (∀ p ∈ E, qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E p = ⊤) →
        (∀ᵐ ω ∂P, (toCoarse (coarseSigma h' W VL VR ζ N) ω, Cond44Ref.cfHistory W' ζ' ω) ∈ E) →
        HasSafeMembers P
          (Coupling.filtrationComap
            (qRaw (Ω := Coarse (coarseSigma h' W VL VR ζ N)) x y W VL VR ζ s E) hι)
          univ (fun ω => qT (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E
            (toCoarse (coarseSigma h' W VL VR ζ N) ω, Cond44Ref.cfHistory W' ζ' ω))
          (fun t ω => qW (Ω := Coarse (coarseSigma h' W VL VR ζ N)) W VL VR ζ s E t
            (toCoarse (coarseSigma h' W VL VR ζ N) ω, Cond44Ref.cfHistory W' ζ' ω))
          (fun ω => imgField κ (recOf (s : ℝ≥0∞) (D ω)) (h ω))) :
    ∃ d : Wire.Night.ChartData Ω,
      Wire.Night.ChartBase κ P h (fun ω => recOf (s : ℝ≥0∞) (D ω)) η d ∧
      Wire.Night.ChartReduction κ P d ∧
      HasSafeMembers P d.filtration univ (fun _ => ⊤) d.driver
        (fun ω => imgField κ (recOf (s : ℝ≥0∞) (D ω)) (h ω)) := by
  obtain ⟨h', 𝓕, VL, VR, B, N, E, hι, htr, hC, hN0, hm, hE, hEg, hEtop, hEae, hcan⟩ :=
    QSched.exists_chartCanon_omega44 hA href hκ hκ4 hb hcf hθh hπh hθ hD hs
  have hθb := RestartGen.cfThetaBounds_of_heights hκ hκ4 hb hπh θ
  obtain ⟨d, hbase, hred, hmem⟩ := exists_chartBase_reduction_members_of_raw hι
    isMeasurableKilledDriving_coarse hE hEg hEtop hEae hs
    (measurable_recOf hDm hDreg (s : ℝ≥0∞)) (fun _ => rfl) hDreg hC.2.1 htr hcan hκ
    (fun i => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.1 i)
    (fun j => (isOrderedForceWord_qx_angle κ θ _ _ _ _).2.2.2 j)
    (strictAnti_qxL_angle κ θ _ _ _ _) (strictMono_qxR_angle κ θ _ _ _ _) rfl rfl
    (prefix_iwL_angle hκ hκ4 hθ.2 hθb) (prefix_iwR_angle hκ hκ4 hθ.1 hθb)
    (hraw h' 𝓕 VL VR B N E hι htr hC hN0 hm hE hEg hEtop hEae)
  obtain ⟨h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, hpath⟩ := hbase
  refine ⟨d, ⟨h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hV0, hVc, hVa, hthr, hchart, ?_⟩, hred, hmem⟩
  filter_upwards [hpath, ae_histLine_cfHistory_eq hcf hζ' hη] with ω hp heq
  obtain ⟨hg, ℓ, hc, hmono, h0, hl⟩ := hp
  refine ⟨hg, ℓ, hc, hmono, h0, fun u hu => ?_⟩
  simpa only [heq, Real.toNNReal_coe, toCoarse, Coarse] using hl u hu

end InteractingSLE.Sec5.CfCarry
