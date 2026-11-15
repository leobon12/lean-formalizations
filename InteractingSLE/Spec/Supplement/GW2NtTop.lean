/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NtKer
import InteractingSLE.Spec.Supplement.GW2NtXfer
import InteractingSLE.Spec.Supplement.GW2StmThr
import InteractingSLE.Spec.Supplement.GW2OmxKerF

/-!
# GW2's `noThreshold` by route (M): assembly from STAGEMEAN's stage-start export

Packet PROVE-GW2-NOTHR (round 2, decision D38). Route (M): under the launch kernel `ν = condExpKernel P pastG ω₀` of
the earlier pieces, the candidate and the conditional counterflow are a configuration of PROVE-GW2-SAFE's collision
exclusion `GW2Stm.ae_no_threshold_gw2_random`: the joint word `gw2Word κ θ c′ (gb6Rec t₀ W ζ)` has no continuation
threshold along the relative driver `R` before `V`. STAGEMEAN's stage-start identity (Claim(j)) identifies, per sample,
the stage word with that joint word through the dilation `λ` (data equal off a finite set) and the stage driver with
`R` (Brownian rescaling) on the pre-cap window; the data-level transfer (`GW2Nt.not_threshold_of_dil`) then gives no
stage threshold there. Past the clock of `T + cap` the after-cap part (`GW2Nt.ae_not_threshold_afterCapX`) applies,
and the kernel-to-`P` transfer (`GW2Nt.ae_noThr_of_kernel`) concludes.

* **`StageKernelExportX`**: D38's export — at the launch kernel, SAFE's configuration (the launch field's data, the
  candidate's flow-line driver and traces, the conditional counterflow, the relative version with its good-sample,
  version and cofinality facts at the counterflow's own time `t₀`) and, per sample of the record event, the stage-start
  data identity and the driver relation on the pre-cap window. Owner: PROVE-GW2-STAGEMEAN (root-`x` kernel port:
  PROVE-GW2-GEOM2). It is consumed as STAGEMEAN's statement (decision D38).
* **`noThresholdX_of_export`**: `GW2Rz.NoThresholdX` of ROOTX's corrected root-`x` instance `schedInstSX` from the
  export.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Nt

open Restart Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 GW2Rd GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sde GW2Sdh GW2Sdi GW2Schedule GW2Tip MartChar.RealFlow
  Sec5.CrossCond.StagedRepLater Sec5.Prop513Schedule Supp8.GB6.RelDrv Supp8.RelSafe

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **D38's export** (PROVE-GW2-STAGEMEAN; root-`x` kernel port PROVE-GW2-GEOM2): for `P`-almost every `ω₀`, at a launch
`(cL, θ)` of the candidate, under the launch kernel `ν` of the earlier pieces: SAFE's configuration of a flow line of
the launch field and the conditional counterflow, with a relative version `(R, V)` at the counterflow's own time `t₀`;
and, `ν`-almost surely on the instance's record event, the stage-start data identity of the stage word with the joint
word through a dilation `λ` (off a finite set) and, at every stage time of the pre-cap window below the stage cap, the
relative driver is the dilated stage driver up to `λ²` times that time, which is before `V`. -/
def StageKernelExportX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (I : StageInst Ω) (x₀ : ℝ) : Prop :=
  ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
    ∃ (b : ℝ → ℝ) (J : Finset ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞)
      (α : Ω → ℝ≥0 → ℂ) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (cw : BoundaryWord)
      (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) (t₀ : Ω → ℝ≥0) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
      (lam : Ω → ℝ) (F : Ω → Set ℝ),
      IsPiecewiseConstantBoundaryData b J ∧ IsPiecewiseConstantBoundaryData b' J' ∧
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC c.κ)) (chiC (16 / c.κ)) (h ω) (h' ω)) ∧
      IsFlowLineDriver c.κ b J θ (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h Wα ζα ∧
      (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) ∧
      IsFlowLineDriver (16 / c.κ) b' J' 0 (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h' W ζ ∧
      cw.jumps = J' ∧ (∀ y ∉ J', cw.fn y = b' y) ∧
      (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), γ ω (t₀ ω) ∈ H →
        RelSafe.PhysGood (t₀ ω) (regW (t₀ ω) Wα ζα) W ζ (extTr (t₀ ω) Wα ζα α) γ ω ∧
        RelSafe.VersionAt (t₀ ω) (regW (t₀ ω) Wα ζα) W (extTr (t₀ ω) Wα ζα α) γ R V ω ∧
        ∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω →
          ∃ t : ℝ≥0, (t : ℝ≥0∞) < gw2End (t₀ ω) ζα γ α ω ∧ (u : ℝ) < gw2Clock (t₀ ω) W Wα ω t) ∧
      ∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), I.srecX c r l x₀ ω ∈ I.E →
        γ ω (t₀ ω) ∈ H ∧ 0 < lam ω ∧ (F ω).Finite ∧
        (∀ y, y ∉ F ω → (I.β (I.srecX c r l x₀ ω)).fn y = (gw2Word c.κ θ cw (gb6Rec (t₀ ω) W ζ ω)).fn (lam ω * y)) ∧
        ∀ u : ℝ≥0, (u : ℝ≥0∞) < I.capX c x₀ ω →
          (((I.T + candidateCap c r a : ℝ≥0) : ℝ≥0∞) < contactX x₀ c.s I.γ c.α ω →
            ((stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0) : ℝ) + u ≤
              clockX x₀ c.s c.W c.ζ I.W (I.T + candidateCap c r a) ω) →
          ((((lam ω) ^ 2 * u).toNNReal : ℝ≥0) : ℝ≥0∞) < V ω ∧
            ∀ v ∈ Icc (0 : ℝ) ((lam ω) ^ 2 * u),
              R v.toNNReal ω = scD (lam ω) (fun q : ℝ => I.drvX c x₀ q.toNNReal ω) v

/-- **One kernel sample of the pre-cap window** (deterministic): SAFE's conclusion for the joint word along `R` at
`λ² u`, the data identity and the driver relation give no stage threshold at `u`. -/
theorem not_threshold_stage_of_joint {κ : ℝ} (hκ : 0 < κ) {β K : BoundaryWord} {lam : ℝ} (hlam : 0 < lam)
    {F : Set ℝ} (hF : F.Finite) (hdata : ∀ y, y ∉ F → β.fn y = K.fn (lam * y)) {D : ℝ → ℝ} (hD : Continuous D)
    {Rr : ℝ≥0 → ℝ} {u : ℝ≥0} (hW : ∀ v ∈ Icc (0 : ℝ) (lam ^ 2 * u), Rr v.toNNReal = scD lam D v)
    (hn : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ K.fn K.jumps 0 0) (flowLineRhoR κ K.fn K.jumps 0 0)
      (Rr (lam ^ 2 * u).toNNReal)
      (fun i => -rightImg (fun v : ℝ => -Rr v.toNNReal) (-flowLineXL K.fn K.jumps 0 i) (lam ^ 2 * u).toNNReal)
      (fun j => rightImg (fun v : ℝ => Rr v.toNNReal) (flowLineXR K.fn K.jumps 0 j) (lam ^ 2 * u).toNNReal)) :
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D u)
      (fun i => -rightImg (fun v => -D v) (-flowLineXL β.fn β.jumps 0 i) u)
      (fun j => rightImg D (flowLineXR β.fn β.jumps 0 j) u) := by
  have hpos : (0 : ℝ) ≤ lam ^ 2 * u := mul_nonneg (sq_nonneg _) u.coe_nonneg
  have hcoe : (((lam ^ 2 * u).toNNReal : ℝ≥0) : ℝ) = lam ^ 2 * u := Real.coe_toNNReal _ hpos
  refine not_threshold_of_dil (c₁ := K) (c₂ := β) (θ₁ := 0) (θ₂ := 0) hκ hlam hF (fun y hy => by
    simp only [zero_mul, add_zero]; exact hdata y hy) hD u.coe_nonneg
    (WL := fun v : ℝ => Rr v.toNNReal) hW ?_
  rw [hcoe] at hn
  exact hn

/-- **`noThreshold` of the corrected root-`x` instance from D38's export** (route (M)): SAFE's collision exclusion
under the launch kernel, the stage-start identity and the data-level transfer on the pre-cap window, the after-cap
part beyond it, and the kernel-to-`P` transfer. -/
theorem noThresholdX_of_export (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (hord : TimeOrdered 0 (historyProgram c r l)) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (ch : SchedChoice Ω)
    (hβ : Measurable ch.β ∧ (range fun y => Supp8.Q3Stop.wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀)
    (hexp : StageKernelExportX c r l a (schedInstSX c r l a GT hA ch) (rootPt r.1)) :
    NoThresholdX (schedInstSX c r l a GT hA ch) c r l (rootPt r.1) := by
  set I := schedInstSX c r l a GT hA ch with hI
  set x := rootPt r.1 with hxdef
  have hWm : ∀ t, Measurable (I.W t) := measurable_schedW c r l a
  have hver : IsRelVersionXR x c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1
  have hv : IsRelVersionX x c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  have hpre : Measurable (stgPreRecX x c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
    (measurable_stgPreRecX hGT.1 hs hx (measurable_gb6Rec_src c) hWm
      (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2) hver I.T).mono
      ((physFilt (measurable_gb6Rec_src c) hWm c.P).le I.T) le_rfl
  have hE : MeasurableSet I.E :=
    (hE₀.inter (measurableSet_succRec c r l)).inter (measurableSet_aliveRecX _ _ c.s hρ.1)
  have hrec : Measurable (I.srecX c r l x) := measurable_augRec (measurable_stageEncRec c r l) hpre
  have hDm : ∀ t, Measurable (I.drvX c x t) := measurable_stgRX hv.1 hv.2.1 hpre
  have hDc : ∀ ω, Continuous fun t => I.drvX c x t ω := fun ω => continuous_stgDrv (hv.2.1 ω) _
  have hcap : Measurable (I.capX c x) := measurable_stgVX hv.2.2.2.2.1 hpre
  -- the staged history of the future program and the past σ-algebra
  set L := futureProgram c r l a with hL
  set spec := GW2Olm.futSpec c r l a with hspec
  set E := GW2Olm.futFam c r l a with hEdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := hS.2.1 k
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hLS : MeasurableSet[GW2Olm.pastG c r l a] {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    measurableSet_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl (isFlowProg_spec x true L)
      (specDelta_ne_top _) E (by rw [hlen]; omega)
  have hcov : ∀ᵐ ω ∂c.P, I.srecX c r l x ω ∈ I.E → ω ∈ {ω | AllSucc (specDelta spec) (fun j => E j ω) k} :=
    Eventually.of_forall fun ω hEω =>
      Gm.allSucc_future_of_oldSuccess c r l a ω ((augRec_mem_succRec_iff c r l _ ω).1 hEω.1.2)
  have hACk := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (ae_not_threshold_afterCapX c r l a hx hs hord hGT hA hV ch)
  refine ae_noThr_of_kernel h𝒢 hrec hE hβ.1 hβ.2.1 hDm hDc hcap hLS hcov ?_
  filter_upwards [hexp, hACk] with ω₀ hX hAC₀ hL₀
  have hlaunch := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _) (fun j => E j ω₀) (show k < spec.2.2.length by omega)).1 hL₀
  obtain ⟨b, J, h, Wα, ζα, α, b', J', h', cw, W, ζ, γ, t₀, Rk, Vk, lam, F, hb, hb', hT, hfl, hα, hcf, hcwJ, hcwb,
    hpt, hid⟩ := hX _ _ hlaunch
  have hG := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver c.hκ hb hfl
  have hsafe := GW2Stm.ae_no_threshold_gw2_random c.hκ c.hκ4 hb hG hb' hT hfl hα hcf cw hcwJ hcwb t₀ hpt
  filter_upwards [hsafe, hid, hAC₀] with ω hs1 hid1 hac hEω u hu
  by_cases hwin : ((I.T + candidateCap c r a : ℝ≥0) : ℝ≥0∞) < contactX x c.s I.γ c.α ω ∧
      clockX x c.s c.W c.ζ I.W (I.T + candidateCap c r a) ω <
        ((stgStartX x c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0) : ℝ) + u
  · exact hac hEω u hu hwin.1 hwin.2 (Restart.FlowStopIdentCMI.flowLineXL_nonpos' _ _ 0)
      (Restart.FlowStopIdentCMI.flowLineXR_nonneg' _ _ 0)
  · obtain ⟨hγH, hlam, hFfin, hdata, hw⟩ := hid1 hEω
    obtain ⟨hlamV, hdrv⟩ := hw u hu fun hc => le_of_not_gt fun hlt => hwin ⟨hc, hlt⟩
    have hn := hs1 hγH _ hlamV
    have h1 := not_threshold_stage_of_joint c.hκ hlam hFfin hdata (D := fun q : ℝ => I.drvX c x q.toNNReal ω)
      ((hDc ω).comp continuous_real_toNNReal) (Rr := fun t => Rk t ω) hdrv hn
    simp only [Real.toNNReal_coe] at h1
    exact h1

end InteractingSLE.Theorem14.GW2Nt
