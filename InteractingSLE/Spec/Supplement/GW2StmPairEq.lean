/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StmClock
import InteractingSLE.Spec.Supplement.GW2StmTip
import InteractingSLE.Spec.Supplement.BRLeafGB6
import InteractingSLE.Spec.Supplement.GW2RootZ21Clock
import InteractingSLE.Spec.Supplement.GW2FbDual
import InteractingSLE.Spec.Supplement.GW2RdExt

/-!
# GW2's stage step, part 6: Proposition GB6 conditioned on the prefix, equality form

Packet PROVE-GW2-STAGEMEAN, round 2. `GW2Later.GB6PrefixPairStatement` (proved:
`BRLeaf.gb6PrefixPairStatement_of_hullDet`) records only that the conditional counterflow's tips lie in the original
completed counterflow range. GW2's launch datum (`GW2TipSystem.HasLaunchPairEq`) needs **equality**: the conditional
counterflow is the original one before its first contact with the prefix, up to a time change measurable in the sample
(Proposition GB6, supplement p. 518: "the portion of `η` before its first contact with `α[0, σ]` … is the complete
canonical counterflow of the conditional component field").

* **`exists_prefixPairEq`**: in the setting of `GB6PrefixPairStatement` (verbatim binders; `γ`, `α` the chosen
  traces of the counterflow and the flow), almost surely on `{s < ζα}` with an interior tip, for every field `h₂` read
  in the flow's own Loewner chart, under the conditional law given the prefix record there are a centred counterflow
  `W₂` of `h₂` with infinite lifetime and the explicit time change
  `ℓ ω' u = ellQ (q ↦ RootZ21.forwardCapacity s q (g ω', cfRec q W ζ ω')) u` (measurable at every `u`), almost surely
  continuous and strictly increasing onto the times before the first contact `T_c` of the counterflow with the prefix,
  with the tips of `W₂`, read through the prefix's own Loewner chart and the inversion, EXACTLY the tips of the
  counterflow `W` at the changed times (the tip clause of `GW2TipSystem.HasLaunchPairEq`).

The proof is `BRLeaf.gb6PrefixPairStatement_of_hullDet`'s, keeping the time change: GB6's pathwise clause
(`gb6_pathwise`) feeds `GW2Stm.chartContinuation_explicit`; the record reader `RootZ21.forwardCapacity` is the relative
clock before contact (`RootZ21.forwardCapacity_eq_relClock_before_contact`), so `ellQ` of it is the clock's inverse
(`GW2Stm.ellQ_eq_clockInv`). Inputs: GB6's hull identity and Theorems 1.2–1.3 (R48: Theorem 1.4 may use them).
Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar fwdMapInv chiC)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Stm

open Exist.StagedLaw Supp8.GB6 Restart Sec2.Assembly GW2Later BRLeaf Sec5.CrossRestart GW2TipSystem

/-- **The record reader is the relative clock before the first contact** (at one sample; the flow record is the
retained record, the complete counterflow is the explored driver). -/
theorem forwardCapacity_agree {Ω : Type*} {Wα W : ℝ≥0 → Ω → ℝ} {ζα ζ : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ} {s : ℝ≥0}
    {g : Ω → RecData} {ω : Ω} (hW0α : Wα 0 ω = 0) (hWcα : ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω})
    (hα : IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (hs : (s : ℝ≥0∞) < ζα ω) (hsH : α ω s ∈ H)
    (hζ : ζ ω = ⊤) (hW0 : W 0 ω = 0) (hWc : Continuous fun t => W t ω)
    (hγ : IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) (hg : g ω = cfRec s Wα ζα ω) :
    ∀ q : ℝ≥0, (q : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
        ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
      RootZ21.forwardCapacity s q (g ω, cfRec q W ζ ω) =
        relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) q := by
  intro q hq
  have hcfE : cfRec q W ζ ω = recOf (q : ℝ≥0∞) ((fun t => W t ω), ⊤) := by
    unfold cfRec
    rw [GW2JointKernel.cfE_eq q hζ hW0 hWc]
  have hreg : Exist.Staged.IsRegularDriver ((fun t => W t ω), ⊤) :=
    ⟨hWc.continuousOn, hW0, fun t ht => absurd ht (not_le.2 ENNReal.coe_lt_top), fun h => absurd rfl h⟩
  have hlt : (q : ℝ≥0∞) < min (firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
      ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s)) ((fun t => W t ω), (⊤ : ℝ≥0∞)).2 :=
    lt_min hq ENNReal.coe_lt_top
  rw [hg, hcfE, RootZ21.forwardCapacity_eq_relClock_before_contact Wα ζα ω hα hWcα hW0α hs hsH hreg hγ hlt]
  refine congrFun (relClock_eq_of_eqOn s.coe_nonneg (fun r hr => ?_) _) q
  show regW s Wα ζα r.toNNReal ω = Wα r.toNNReal ω
  exact GW2Rd.regW_eq_of_lt s hW0α hWcα (lt_of_le_of_lt
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hs)

/-- **GB6's equality at one sample with an explicit time change** (deterministic; `tips_mem_range_of_sample` with the
time change kept). At a sample with an interior flow tip before the lifetime, if the GB6 canonical-space point `x` of
the chart field is good and its decoded driver satisfies GB6's hull identity, and `b` is any clock equal to the relative
clock before the first contact `T_c`, then `ellQ b` is continuous, strictly increasing onto the times before `T_c`, and
the tips of the relative driver read through the prefix's Loewner chart and the inversion are the physical counterflow's
tips at the changed times (`tipAt_loewner_iff_of_interior`). -/
theorem sample_chartEq {κ : ℝ} {hω Hω : DistOn upperHalfPlaneOpens} {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞}
    {α γ : ℝ≥0 → ℂ} {s : ℝ≥0} {x : GB6Space} (hα : IsGeneratingTrace wα Tα α)
    (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    (htrγ : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (htr : IsChartTransport (ownComponentChart (fun r : ℝ => wα r.toNNReal) s) (-1)
      (-(Real.pi * chiC κ)) (chiC (16 / κ)) hω Hω) (hHx : gb6Field x = Hω)
    (hgood : IsGB6KernelGood x) (hcode : IsGoodDrvCode (gb6Code x))
    (hjL : gb6JL x = junctionL (fun r : ℝ => wα r.toNNReal) s)
    (hjR : gb6JR x = junctionR (fun r : ℝ => wα r.toNNReal) s)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => drvDec (gb6Code x) r.toNNReal)
          (relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t) =
        relMap (fun r : ℝ => wα r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t)
    {b : ℝ≥0 → ℝ} (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      b t = relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
    {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hB : HasBdryLimits (fwdMapInv U T))
    (hch : ownComponentChart (fun r : ℝ => wα r.toNNReal) s = ownComponentChart U T) :
    Continuous (ellQ b) ∧ StrictMono (ellQ b) ∧
      range (ellQ b) = {t : ℝ≥0 | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} ∧
      ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner U T).trans infinitySourceChart).tipAt (fun t => gb6WC t x) r z ↔
        infinitySourceChart.tipAt w (ellQ b r) z := by
  obtain ⟨-, hWCc, hWC0, hΓgen, hunb, hKWC⟩ := gb6_pathwise (x := x) gb6EndpointStatement hα hwα hwα0 hs hsH
    hγ hw hw0 htrγ htr hHx hgood hcode hjL hjR hK
  obtain ⟨hexh, hid⟩ := chartContinuation_explicit hα hwα hwα0 hs hsH hγ hw hw0 hΓgen hWCc hWC0 hunb hKWC
  have hℓ : ellQ b = clockInv (fun t : ℝ≥0 => relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
      (firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :=
    funext fun u => ellQ_eq_clockInv hexh hb u
  have htrΓ := (isGeneratingTrace_gb6Γ hgood.2.2.1).2
  have hdense := BRLeaf.mem_closure_setOf_mem_H (transientDenseQ_of_isGeneratingTrace hΓgen hWCc hWC0 htrΓ)
  rw [hℓ]
  refine ⟨hexh.continuous_clockInv, hexh.strictMono_clockInv, ?_, tipAt_loewner_iff_of_interior hU hU0 hT hB hΓgen
    hWCc hWC0 hγ hw hw0 hdense hexh.continuous_clockInv fun u hu => ?_⟩
  · rw [← image_univ]
    exact hexh.image_clockInv
  · have h1 := hid u hu
    rw [hch] at h1
    exact h1

/-- **Proposition GB6 conditioned on the prefix record, equality form, from GB6's hull identity.** -/
theorem exists_prefixPairEq (hD : GB6HullDetStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (κ : ℝ) (hκ : 0 < κ) (hκ4 : κ < 4) (θ : ℝ)
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [mΩ : MeasurableSpace Ω] [hSB : StandardBorelSpace Ω]
    (Q : Measure Ω) [hQ : IsProbabilityMeasure Q] (h : Ω → DistOn upperHalfPlaneOpens)
    (hG : IsGFFWithBoundaryData Q h b jumps) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ Q h W ζ) (hζ : ∀ᵐ ω ∂Q, ζ ω = ⊤) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞)
    (hfl : IsFlowLineDriver κ b jumps θ Q h Wα ζα) (s : ℝ≥0∞) (hs : s ≠ ⊤) (g : Ω → RecData)
    (hgm : Measurable g) (hgeq : ∀ᵐ ω ∂Q, g ω = recOf s ((fun t => Wα t ω), ζα ω)) :
    ∀ᵐ ω ∂Q, s < ζα ω → IsInteriorStop (fun t => Wα t ω) s →
      ∀ h₂ : Ω → DistOn upperHalfPlaneOpens,
        (∀ ω', IsChartTransport (Chart.id.loewner (stopDrv s ((fun t => Wα t ω), ζα ω))
          (stopTime s ((fun t => Wα t ω), ζα ω))) 1 0 (QuantumZipper.chiC κ) (h ω') (h₂ ω')) →
        ∃ (W₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
          IsCenteredCounterflowDriver κ (condExpKernel Q (MeasurableSpace.comap g inferInstance) ω) h₂ W₂ ζ₂ ∧
          (∀ u, Measurable fun ω' => ℓ ω' u) ∧
          ∀ᵐ ω' ∂(condExpKernel Q (MeasurableSpace.comap g inferInstance) ω), ζ₂ ω' = ⊤ ∧
            Continuous (ℓ ω') ∧ StrictMono (ℓ ω') ∧
            range (ℓ ω') = {t : ℝ≥0 | (t : ℝ≥0∞) < firstContactTime
              (fun t => sphereInv (GW2aSingle.chosenTrace W ζ ω' t : OnePoint ℂ))
              ((fun t => (GW2aSingle.chosenTrace Wα ζα ω' t : OnePoint ℂ)) '' Icc 0 s.toNNReal)} ∧
            ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner (stopDrv s ((fun t => Wα t ω), ζα ω))
                (stopTime s ((fun t => Wα t ω), ζα ω))).trans infinitySourceChart).tipAt (fun t => W₂ t ω') r z ↔
              infinitySourceChart.tipAt (fun t => W t ω') (ℓ ω' r) z := by
  have hκ' : 0 < 16 / κ := by positivity
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  obtain ⟨F, hF⟩ := Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀ (16 / κ) 0 hκ'
  have hC : CompleteSixteenDivStatement := fun κ₁ hκ₁ _ nL nR xL xR ρL ρR hFw => by
    intro Ω₁ mΩ₁ P₁ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hE₁
    exact (h13₀ (div_pos (by norm_num) hκ₁) hFw hE₁).mono fun _ hω => hω.2
  set s' : ℝ≥0 := s.toNNReal with hs'def
  have hss : (s' : ℝ≥0∞) = s := ENNReal.coe_toNNReal hs
  obtain ⟨b', J', h', hb', hT, hcfl⟩ := hcf
  obtain ⟨hadmL, hadmR⟩ :=
    GW0.counterflow_admissible (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hcfl hζ
  set γ := GW2aSingle.chosenTrace W ζ with hγdef
  have hcomp : ∀ᵐ ω ∂Q, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop := by
    filter_upwards [GW2aSingle.ae_chosenTrace h13 hκ' hcfl, hζ] with ω hω hζω
    rw [hζω] at hω
    exact ⟨hζω, hω.1, hω.2 rfl⟩
  set α := GW2aSingle.chosenTrace Wα ζα with hαdef
  have hα : ∀ᵐ ω ∂Q, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω) :=
    (GW2aSingle.ae_chosenTrace h13 hκ hfl).mono fun _ hω => hω.1
  obtain ⟨c, hcJ, hcb⟩ := BoundaryWord.exists_fn_eq hb
  have hflc : IsFlowLineDriver κ c.fn c.jumps θ Q h Wα ζα :=
    (isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData jumps hcb).2 hfl
  obtain ⟨Hc, hHcm, hHc⟩ := exists_measurable_chartField hfl hG.1 s' (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ))
  have hHc' : ∀ᵐ ω ∂Q, (s' : ℝ≥0∞) < ζα ω → α ω s' ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s') (-1) (-(Real.pi * chiC κ))
        (chiC (16 / κ)) (h ω) (Hc ω) := by
    filter_upwards [hHc] with ω hω hs₁ _ using hω hs₁
  have hHull := hD κ θ hκ hκ4 hθ.1 hθ.2 Ω mΩ Q hQ h b jumps W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcfl hadmL hadmR
    hcomp hfl hα s' Hc hHcm hHc' F hF c hcJ hcb
  have hgeq' : ∀ᵐ ω ∂Q, g ω = recOf (s' : ℝ≥0∞) ((fun t => Wα t ω), ζα ω) := by rw [hss]; exact hgeq
  have hGFFk := ae_isGFF_condExpKernel_prefix hκ hG hflc hα s' hHcm hHc' hgm hgeq'
  have hG' : IsGFFWithBoundaryData Q h' b' J' :=
    GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ' hb' hcfl
  have hcL := gb6_admL hκ hb hG hb' hG' hT hadmR hcJ hcb
  have hcR := gb6_admR hκ hb hG hb' hG' hT hadmL hcJ hcb
  -- all almost-sure facts at one sample
  have hAll : ∀ᵐ ω ∂Q, (((s' : ℝ≥0∞) < ζα ω → g ω = gb6Rec s' Wα ζα ω) ∧
        (g ω ∈ gb6TS s' ↔ gb6Rec s' Wα ζα ω ∈ gb6TS s')) ∧
      ((s' : ℝ≥0∞) < ζα ω → GB6RecGood s' Wα ζα α ω) ∧
      (Wα 0 ω = 0 ∧ ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω}) ∧
      IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω) ∧
      (ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop) ∧
      (W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ((s' : ℝ≥0∞) < ζα ω → α ω s' ∈ H →
        IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s') (-1) (-(Real.pi * chiC κ))
          (chiC (16 / κ)) (h ω) (Hc ω)) ∧
      ((s' : ℝ≥0∞) < ζα ω → α ω s' ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s') →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (gb6Word κ θ c s' (fun t => Wα t ω), Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => Wα r.toNNReal ω) s' (fun r : ℝ => W r.toNNReal ω) t) =
            relMap (fun r : ℝ => Wα r.toNNReal ω) s' '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t) := by
    filter_upwards [ae_rec_facts hflc hα s' hgeq', ae_gb6RecGood hflc hα s', ae_driver_zero_continuousOn hfl, hα,
      hcomp, ae_driver_zero_continuousOn hcfl, hHc', hHull] with ω h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hm : MeasurableSpace.comap g inferInstance ≤ mΩ := hgm.comap_le
  have hK := KernelTower.ae_ae_condExpKernel_of_ae hm hAll
  have hconc := Exist.Staged.ae_ae_eq_of_comap (P := Q) hgm
  filter_upwards [hconc, hK, hGFFk, hAll] with ω₀ hc₀ hK₀ hGFF₀ hA₀ hsζ hint h₂ htr₂
  obtain ⟨hrec₀, hgood₀, hdrv₀, hα₀, -, -, -, -⟩ := hA₀
  have hs'ζ : (s' : ℝ≥0∞) < ζα ω₀ := by rw [hss]; exact hsζ
  have hαH : α ω₀ s' ∈ H := mem_H_of_isInteriorStop hα₀ hdrv₀.2 hdrv₀.1 hsζ hint
  have hg₀ : g ω₀ = gb6Rec s' Wα ζα ω₀ := hrec₀.1 hs'ζ
  have hg₀T : g ω₀ ∈ gb6TS s' := by rw [hg₀]; exact (mem_gb6TS_iff hgood₀).1 ⟨hs'ζ, hαH⟩
  have hβs := isSorted_gb6WordOfRec κ θ c (g ω₀)
  obtain ⟨-, hadm₀, htail₀⟩ := gb6_word_of_mem hκ hκ4 hθ.1 hθ.2 c hg₀T (J'.image fun w => -w⁻¹) hcL hcR
  have hGFFν := hGFF₀ hg₀T
  -- the flow piece at `ω₀` and its own chart
  have hregm : GW1P.PieceRegular (fun t => Wα t ω₀) (min s (ζα ω₀)) := by
    rw [min_eq_left hsζ.le]; exact pieceRegular_of_lt hα₀ hdrv₀.2 hdrv₀.1 hsζ
  obtain ⟨hUc, hU0⟩ := GW2Later.continuous_stopDrv (e := ((fun t => Wα t ω₀), ζα ω₀)) hregm
  have hT0 : (0 : ℝ) ≤ stopTime s ((fun t => Wα t ω₀), ζα ω₀) := NNReal.coe_nonneg _
  have hB : HasBdryLimits (fwdMapInv (stopDrv s ((fun t => Wα t ω₀), ζα ω₀))
      (stopTime s ((fun t => Wα t ω₀), ζα ω₀))) :=
    hregm.hasBdryLimits (lt_of_le_of_lt (min_le_left _ _) (lt_top_iff_ne_top.2 hs)).ne
  have hconf := GW2JointKernel.isConformal_loewner hUc hU0 hT0
  have hlift := GW2JointKernel.continuousOn_loewner_lift hUc hU0 hT0
  have hh₂ : h₂ = fun ω' => Chart.chartTransport hconf 1 0 (chiC κ) (h ω') := funext fun ω' =>
    (htr₂ ω').unique hconf (Chart.isChartTransport_chartTransport hconf
      (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω'))
  have hh₂m : Measurable h₂ := by rw [hh₂]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hG.1
  have hRm : Measurable fun ω' => Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω') :=
    (Sec7.StripSysField.measurable_returnField _ _).comp hh₂m
  have hconfO := isConformal_ownComponentChart hUc hU0 hT0
  have hchart₀ : ownComponentChart (stopDrv s ((fun t => Wα t ω₀), ζα ω₀))
      (stopTime s ((fun t => Wα t ω₀), ζα ω₀)) = ownComponentChart (fun r : ℝ => Wα r.toNNReal ω₀) s' := by
    unfold ownComponentChart
    rw [loewner_stopDrv_eq hα₀ hdrv₀.2 hdrv₀.1 hsζ]
  -- the record, the chart and the chart field under the conditional law
  have hrecν : ∀ᵐ ω' ∂(condExpKernel Q (MeasurableSpace.comap g inferInstance) ω₀),
      gb6Rec s' Wα ζα ω' = g ω₀ ∧
      ownComponentChart (fun r : ℝ => Wα r.toNNReal ω') s' = ownComponentChart (stopDrv s ((fun t => Wα t ω₀),
        ζα ω₀)) (stopTime s ((fun t => Wα t ω₀), ζα ω₀)) ∧
      Hc ω' = Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω') ∧
      (s' : ℝ≥0∞) < ζα ω' ∧ α ω' s' ∈ H := by
    filter_upwards [hc₀, hK₀] with ω' hgω' hA'
    obtain ⟨hrec', hgood', -, -, -, -, hHc'', -⟩ := hA'
    have hT' : gb6Rec s' Wα ζα ω' ∈ gb6TS s' := hrec'.2.1 (hgω' ▸ hg₀T)
    obtain ⟨hs', hαH'⟩ := (mem_gb6TS_iff hgood').2 hT'
    have hrec'' : gb6Rec s' Wα ζα ω' = g ω₀ := (hrec'.1 hs').symm.trans hgω'
    have hch : ownComponentChart (fun r : ℝ => Wα r.toNNReal ω') s' = ownComponentChart (stopDrv s
        ((fun t => Wα t ω₀), ζα ω₀)) (stopTime s ((fun t => Wα t ω₀), ζα ω₀)) := by
      rw [hchart₀, ← (hgood' hs').1.2.1, ← (hgood₀ hs'ζ).1.2.1, hrec'', hg₀]
    refine ⟨hrec'', hch, ?_, hs', hαH'⟩
    have h4 := hHc'' hs' hαH'
    rw [hch] at h4
    exact h4.unique hconfO (isChartTransport_ownComponentChart_returnField hκ hUc hU0 hT0 (htr₂ ω'))
  have hGFF'' := isGFFWithBoundaryData_congr_ae hGFFν hRm (hrecν.mono fun ω' h => h.2.2.1)
  -- the canonical code under the conditional law
  obtain ⟨u₀, hu₀, -⟩ :=
    PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
      (gb6WordOfRec κ θ c (g ω₀)).isPiecewiseConstantBoundaryData
  have hmap : (condExpKernel Q (MeasurableSpace.comap g inferInstance) ω₀).map
      (fun ω' => Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω')) =
      (gb6WordOfRec κ θ c (g ω₀)).gffLaw := by
    have h5 := Exist.map_eq_of_isGFFWithBoundaryData hGFF''
      ((gb6WordOfRec κ θ c (g ω₀)).isGFFWithBoundaryData_gffLaw hβs) hu₀
    rwa [Measure.map_id] at h5
  have hcmp0 := ae_drvOf_eq_drvDec h12p h13 hκ' hF hβs
  have hkg0 := ae_isGB6KernelGood_gffLaw hκ hκ4 hC hF hβs hadm₀ htail₀
  have hgc0 := ae_isGoodDrvCode_gffLaw hκ' hF hβs
  rw [← hmap] at hcmp0 hkg0 hgc0
  have hcmp := ae_of_ae_map hRm.aemeasurable hcmp0
  have hkg := ae_of_ae_map hRm.aemeasurable hkg0
  have hgc := ae_of_ae_map hRm.aemeasurable hgc0
  refine ⟨_, _, fun ω' => ellQ (fun q => RootZ21.forwardCapacity s' q (g ω', cfRec q W ζ ω')),
    isCenteredCounterflowDriver_cfDrv h12p h13 hκ hκ' hh₂m hGFF'', fun u => ?_, ?_⟩
  · exact measurable_ellQ (fun q => (RootZ21.measurable_forwardCapacity s' q).comp
      (hgm.prodMk (Supp8.GB6.measurable_recOf_cfE hcfl q).2)) u
  filter_upwards [hcmp, hkg, hgc, hrecν, hK₀, hc₀] with ω' hc' hk' hgc' hr' hA' hgω'
  obtain ⟨hrec'', hch, hHceq, hs', hαH'⟩ := hr'
  obtain ⟨-, hgood', hdrv', hα', hcomp', hcfd', hHc'', hHull'⟩ := hA'
  have hWc' : Continuous fun t => W t ω' := by
    have h6 := hcfd'.2
    rw [hcomp'.1] at h6
    simp only [ENNReal.coe_lt_top, ofPred_true] at h6
    exact continuousOn_univ.1 h6
  have hβeq : gb6Word κ θ c s' (fun t => Wα t ω') = gb6WordOfRec κ θ c (g ω₀) := by
    rw [← hrec'', gb6Word, (hgood' hs').2.1]
  have hLtop := hk'.1
  have hW₂eq : (fun t => (cfDrv h12p hκ' (gb6WordOfRec κ θ c (g ω₀))
      (Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω'))).1 t) =
      fun t => gb6WC t (Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω'),
        F (gb6WordOfRec κ θ c (g ω₀), Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω')),
        (jLOfRec (g ω₀), jROfRec (g ω₀))) := by
    funext t
    refine (hc'.2 t (lt_of_lt_of_le ENNReal.coe_lt_top (top_le_iff.2 hLtop))).trans ?_
    exact (congrFun (drvDecTop_eq_drvDec hgc' hLtop) t).symm
  have hgrec : g ω' = cfRec s' Wα ζα ω' := by
    rw [GW2Fb.cfRec_eq_gb6Rec, hrec'']; exact hgω'
  have hagree := forwardCapacity_agree hdrv'.1 hdrv'.2 hα' hs' hαH' hcomp'.1 hcfd'.1 hWc' hcomp'.2.1 hgrec
  have hjL : jLOfRec (g ω₀) = junctionL (fun r : ℝ => Wα r.toNNReal ω') s' := by
    rw [← hrec'']; exact (hgood' hs').1.2.2.1
  have hjR : jROfRec (g ω₀) = junctionR (fun r : ℝ => Wα r.toNNReal ω') s' := by
    rw [← hrec'']; exact (hgood' hs').1.2.2.2.1
  have h7 := hHull' hs' hαH'
  rw [hβeq, hHceq] at h7
  obtain ⟨h1, h2, h3, h4⟩ := sample_chartEq
    (x := (Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω'),
      F (gb6WordOfRec κ θ c (g ω₀), Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω')),
      (jLOfRec (g ω₀), jROfRec (g ω₀)))) hα' hdrv'.2 hdrv'.1 hs' hαH' hcomp'.2.1 hWc' hcfd'.1 hcomp'.2.2
    (hHc'' hs' hαH') hHceq.symm hk' hgc' hjL hjR h7 hagree hUc hU0 hT0 hB hch
  exact ⟨hc'.1.trans hk'.1, h1, h2, h3, by rw [hW₂eq]; exact h4⟩

end InteractingSLE.Theorem14.GW2Stm
