/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmKer

/-!
# GW2's open lines: the current piece under the conditional kernel, with announcing stops

Packet PROVE-GW2-STAGEMEAN, R119 round. The current piece is, under the conditional kernel of the earlier pieces, a
flow line of the launch field (`IsStagedHistory`). `GW2Stl.exists_chart_mean_stop_random` reads it at stopping times
strictly before its lifetime; on an admissible seed these come from an announcing sequence of the lifetime:

* **`kernel_chart_mean_stop`**: the union mean of the conditional counterflow stopped at `σ_k` (the own time at which
  the original counterflow reaches `s`, `GW2Sgk.exists_stop_of_datum`) and the current piece stopped at
  `min t (T n)`, in the conditional counterflow's relative chart (`GW2Stl.exists_chart_mean_stop_random`), from the
  launch datum's clauses under any probability measure;
* **`flowLine_pack`**: from `IsFlowLineDriver` with an admissible seed under any probability measure, the unpacked
  coupling (translate, optional hull coupling, killed driving) together with an announcing sequence of the lifetime
  for the coupling's driving filtration (`WholeField.exists_isAnnouncingSeq_of_adapted`, as in
  `GW2Sf.GW2SfUnionMean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Olm

open Restart Exist Exist.StagedLaw WholeField LocalSets Sec7.PocketTraversal Supp8 Supp8.GB6 Supp8.GB6LineL
  Supp8.GB6LMean Supp8.Q3Chain RelSafeS GW2JointKernel GW2TipSystem GW2Fb GW2JDetR8
open Supp8.Q3Rel (invHull relLog)
open QuantumZipper (fwdHull)

/-- **A flow line with an admissible seed, unpacked, with an announcing sequence of its lifetime.** -/
theorem flowLine_pack {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b J θ μ X Wα ζα)
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
      (flowLineXL b J 0) (flowLineXR b J 0)) :
    ∃ (Xθ : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (hX : IsMeasurableKilledDriving Wα VL VR ζα) (T : ℕ → Ω → ℝ≥0),
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (X ω) (Xθ ω)) ∧
      IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
        (flowLineRhoR κ b J 0 θ) μ 𝓕 Wα VL VR B ζα Xθ ∧
      Coupling.IsAnnouncingSeq (drivingFiltration μ hX) μ ζα T := by
  obtain ⟨Xθ, 𝓕, VL, VR, B, htr, hC⟩ := hfl
  have hX : IsMeasurableKilledDriving Wα VL VR ζα := hC.2.2.2.1
  have : (drivingFiltration μ hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨T, hT, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration μ hX) (B := B) (κ := κ)
    (xL := flowLineXL b J 0) (xR := flowLineXR b J 0)
    (fun N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hC.1.2.2.2.2 (hC.1.ae_tendsto_threshold hκ) hseed
  exact ⟨Xθ, 𝓕, VL, VR, B, hX, T, htr, hC, hT⟩

/-- **The kernel union mean at the current piece.** Under any probability measure: the launch field `X` (a GFF of
`(b, J)`), its centred counterflow `W_k` with the launch datum's clock `ℓ` and tip relation through the launch chart
`cL` (with a proper boundary extension), the original counterflow `W'` (regular), and the current piece (a flow line of
`X` at angle `θ` with an admissible seed and generating trace `α`). There are the stop `σ` (`= t₀` where `ℓ t₀ = s`,
`t₀ < N`), the angle-`θ` field `Xθ`, an announcing sequence `T` of the piece's lifetime, the counterflow's word `c'`
and trace `γ`, such that for every `n` and `t` the conclusion of `GW2Stl.exists_chart_mean_stop_random` holds at
`σ` and `τ = min t (T n)`. -/
theorem kernel_chart_mean_stop (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hG : IsGFFWithBoundaryData μ X b J) {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ μ X Wk ζk) {W' : ℝ≥0 → Ω → ℝ}
    (hW' : ∀ᵐ ω ∂μ, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ')
    {cL : Chart} (hpb : GW1P.HasProperBdryExt cL) {ℓ : Ω → ℝ≥0 → ℝ≥0} {Aset : Set ℂ}
    (hd : ∀ᵐ ω ∂μ, ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
      range (ℓ ω) = {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) Aset} ∧
      ∀ (r : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z ↔
        infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z)
    (s N : ℝ≥0) {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b J θ μ X Wα ζα)
    {α : Ω → ℝ≥0 → ℂ} (hα : ∀ᵐ ω ∂μ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
      (flowLineXL b J 0) (flowLineXR b J 0)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    ∃ (σ : Ω → WithTop ℝ≥0) (Xθ : Ω → DistOn upperHalfPlaneOpens) (T : ℕ → Ω → ℝ≥0) (c' : BoundaryWord)
      (γ : Ω → ℝ≥0 → ℂ), (∀ ω, σ ω ≤ (N : WithTop ℝ≥0)) ∧
      (∀ᵐ ω ∂μ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < N → σ ω = (t₀ : WithTop ℝ≥0)) ∧
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (X ω) (Xθ ω)) ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → ∃ n, t ≤ T n ω) ∧
      (∀ᵐ ω ∂μ, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
      ∀ (n : ℕ) (t : ℝ≥0),
    ∃ A K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ Measurable[mΩ, hittingSigma] K ∧
      (∀ᵐ ω ∂μ, A ω = invHull (fun r : ℝ => Wk r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
      (∀ᵐ ω ∂μ, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω)
        ((min (t : WithTop ℝ≥0) (T n ω)).untopD 0 : ℝ≥0)) ∧
      IsLocalSet (fun ω => A ω ∪ K ω) (centredField Xθ u₀) μ ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (fun ω => A ω ∪ K ω) (centredField Xθ u₀) μ g →
        ∀ᵐ ω ∂μ, γ ω ((σ ω).untopD 0 : ℝ≥0) ∈ H → 0 < (min (t : WithTop ℝ≥0) (T n ω)).untopD 0 →
          ((((min (t : WithTop ℝ≥0) (T n ω)).untopD 0 : ℝ≥0)) : ℝ≥0∞) <
            firstContactTime (fun u => (α ω u : OnePoint ℂ))
            ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ ω).untopD 0 : ℝ≥0)) →
          let sω : ℝ≥0 := (σ ω).untopD 0
          let c := jointWordOfRec (specOffset κ) κ c' (cfRec sω Wk ζk ω)
          let Tt := (min (t : WithTop ℝ≥0) (T n ω)).untopD 0
          let q := (relClock (fun r : ℝ => Wk r.toNNReal ω) sω (fun r : ℝ => Wα r.toNNReal ω) Tt).toNNReal
          ∃ p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ),
            IsRelChainStop κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
              (flowLineXL b J 0) (flowLineXR b J 0)
              (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
              (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
              (fun r : ℝ => Wk r.toNNReal ω) sω (Wα · ω) Tt p ∧
            ∀ (nL nR : ℕ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
              FCDet.IsFlowType κ θ c xL xR ρL ρR →
              ∀ ψ : TestOn upperHalfPlaneOpens,
                Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => p.2.2.1 r.toNNReal) q) →
                Chart.chartTransport (isConformal_relChart (cfRec sω Wk ζk ω)) 1 (specOffset κ) (chiC κ)
                    (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
                  ∫ y, couplingMean κ (fun r : ℝ => p.2.2.1 r.toNNReal) q
                    (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => p.2.2.1 t)
                      (geomLW (fun t (_ : Unit) => p.2.2.1 t) (fun _ => xL))
                      (geomRW (fun t (_ : Unit) => p.2.2.1 t) (fun _ => xR)) () q) y * ψ y := by
  obtain ⟨h', h₁, c', 𝓕', VL', VR', B', γ, hX', hT, htr', hC', hcomp, hNR⟩ :=
    counterflow_pack h13 hκ hκ4 hb hG hcf (hd.mono fun _ h => h.1)
  obtain ⟨σ, hσ, hσt, hσN, hσeq⟩ := GW2Sgk.exists_stop_of_datum h13 hκ μ hcf hX' hW' hpb hd s N
  obtain ⟨Xθ, 𝓕, VL, VR, B, hX, T, htr, hC, hTa⟩ := flowLine_pack hκ hfl hseed
  refine ⟨σ, Xθ, T, c', γ, hσN, hσeq, htr, hTa.2.2.2, hcomp, fun n t => ?_⟩
  have hτ : IsStoppingTime (drivingFiltration μ hX) (fun ω => min (t : WithTop ℝ≥0) (T n ω)) :=
    (isStoppingTime_const _ t).min (hTa.1 n)
  have hτζ : ∀ᵐ ω ∂μ, ((min (t : WithTop ℝ≥0) (T n ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζα ω :=
    (hTa.2.2.1 n).mono fun _ hω => (min_le_right _ _).trans_lt hω
  have hτt : ∀ ω, min (t : WithTop ℝ≥0) (T n ω) ≠ ⊤ :=
    fun _ => ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  exact GW2Stl.exists_chart_mean_stop_random h12 h13 hκ hb hG hT htr' hC' hX' hcomp hNR hσ hσt htr hC hα hX
    hτ hτζ hτt hu₀

end InteractingSLE.Theorem14.GW2Olm
