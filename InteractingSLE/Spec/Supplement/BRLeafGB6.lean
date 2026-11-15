/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BRLeafGB6Aux
import InteractingSLE.Spec.Supplement.GB6RelDet
import InteractingSLE.Spec.Supplement.GB6LawMain
import InteractingSLE.Spec.Supplement.GB6LawFinal
import InteractingSLE.Spec.Supplement.GW2aSingle
import InteractingSLE.Spec.Supplement.BR3Ref
import InteractingSLE.Spec.Sec5.GlueCond
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Restart.FlowCodeMain

/-!
# Proposition GB6 conditioned on the flow's own marked prefix, from GB6's hull identity

Packet PROVE-T14-BR. **`gb6PrefixPairStatement_of_hullDet`**: Theorem 1.4's leaf
`Theorem14.GW2Later.GB6PrefixPairStatement` (Proposition GB6's conditional-law half conditioned on the prefix record,
supplement §8.6, pp. 518–520) follows from GB6's hull identity `Supp8.GB6.GB6HullDetStatement` (the leaf behind the
existing `Supp8.GB6.GB6CondDetStatement`, which it implies: `gb6CondDetStatement_of_hullDet`) and Theorems 1.2–1.3 at
universes `u` and `0` (R48: Theorem 1.4 may use them).

Proof, at a sample `ω₀` with `s < ζα` and an interior tip, `ν = condExpKernel Q σ(g) ω₀`, `β₀` the conditional word of
the record `g ω₀`:
1. (R1) under `ν`: the chart field `Hc` (the field read in `ownComponentChart`) is a GFF with the word `β₀`
   (`ae_isGFF_condExpKernel_prefix`); under `ν` the record is `g ω₀`, so `Hc` is `ν`-a.s. the return field `h₂''` of the
   given flow-chart field `h₂` (charts of equal records agree, `GB6RecGood`).
2. The pair: the field-determined driver of Theorem 1.2 at universe `u` for the counterflow word of `β₀` is an optional
   hull coupling with `h₂''` under `ν` (`Exist.Staged.isOptionalHullCoupling_drv`), so it is a centred counterflow
   driver of `h₂`.
3. It is `ν`-a.s. the decoded canonical driver code `drvDec (F (β₀, h₂''))` (`ae_drvOf_eq_drvDec`), whose GB6 point is
   good (`ae_isGB6KernelGood_gffLaw`): infinite lifetime and a complete transient trace `Γ`.
4. GB6's hull identity at `ω'` (`ν`-a.s.) and `gb6_pathwise` give the unbounded relative clock;
   `isGB6ChartContinuation_of_relHulls` identifies `Γ(u)` read in the chart with the physical counterflow; the tips at
   interior and boundary trace points follow (`mem_of_tipAt_loewner_inf`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar fwdMapInv chiC)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace BRLeaf

open Exist.StagedLaw Supp8.GB6 Restart Sec2.Assembly GW2Later

/-- The raw record of the prefix and GB6's regularized record agree before the lifetime and lie in `gb6TS`
together. -/
theorem ae_rec_facts {κ θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    {α : Ω → ℝ≥0 → ℂ} (hfl : IsFlowLineDriver κ b J θ Q h Wα ζα)
    (hα : ∀ᵐ ω ∂Q, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0) {g : Ω → RecData}
    (hgeq : ∀ᵐ ω ∂Q, g ω = recOf (s : ℝ≥0∞) ((fun t => Wα t ω), ζα ω)) :
    ∀ᵐ ω ∂Q, ((s : ℝ≥0∞) < ζα ω → g ω = gb6Rec s Wα ζα ω) ∧
      (g ω ∈ gb6TS s ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) := by
  filter_upwards [hgeq, ae_gb6RecGood hfl hα s] with ω hgω hrec
  have he : (s : ℝ≥0∞) < ζα ω → g ω = gb6Rec s Wα ζα ω := fun hs => by
    rw [hgω, recOf_eq_recOf_top ENNReal.coe_ne_top hs, (hrec hs).2.1]
  refine ⟨he, ?_⟩
  by_cases hs : (s : ℝ≥0∞) < ζα ω
  · rw [he hs]
  · have h1 : g ω ∉ gb6TS s := fun hm => by
      have hf := hm.1
      rw [hgω, recOf_flag_of_le (not_lt.1 hs)] at hf
      exact Bool.noConfusion hf
    have h2 : gb6Rec s Wα ζα ω ∉ gb6TS s := fun hm => hs ((flag_recOf_cfE s).1 hm.1)
    exact ⟨fun hm => absurd hm h1, fun hm => absurd hm h2⟩

/-! ### The pair under the conditional law -/

/-- **The field-determined driver of Theorem 1.2 at universe `u`** for the angle-`0` flow line of the word `β` at
parameter `k`, read off a field sample. -/
def cfDrv (h12p : Exist.Staged.Theorem12ParamStatement.{u}) {k : ℝ} (hk : 0 < k) (β : BoundaryWord)
    (f : DistOn upperHalfPlaneOpens) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  Exist.Staged.drvOf (Exist.Staged.detCode
    (Exist.Staged.paramΦ h12p hk (flowLineNL β.fn β.jumps 0) (flowLineNR β.fn β.jumps 0))
      (((flowLineXL β.fn β.jumps 0, flowLineXR β.fn β.jumps 0),
        (flowLineRhoL k β.fn β.jumps 0 0, flowLineRhoR k β.fn β.jumps 0 0)), f))

theorem measurable_cfDrv (h12p : Exist.Staged.Theorem12ParamStatement.{u}) {k : ℝ} (hk : 0 < k)
    (β : BoundaryWord) : Measurable (cfDrv h12p hk β) :=
  Exist.Staged.measurable_drvOf.comp ((Exist.Staged.measurable_detCode
    (Exist.Staged.measurable_paramΦ h12p hk _ _)).comp (measurable_const.prodMk measurable_id))

/-- **The centred counterflow pair of a field whose return field is a GFF** (any probability on a space in `Type u`):
the field-determined driver of the return field drives the centred counterflow. -/
theorem isCenteredCounterflowDriver_cfDrv (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hk : 0 < 16 / κ) {Ω : Type u} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {h₂ : Ω → DistOn upperHalfPlaneOpens} (hh₂m : Measurable h₂)
    {β : BoundaryWord}
    (hβ : IsGFFWithBoundaryData ν (fun ω => Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω))
      β.fn β.jumps) :
    IsCenteredCounterflowDriver κ ν h₂
      (fun t ω => (cfDrv h12p hk β (Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω))).1 t)
      (fun ω => (cfDrv h12p hk β (Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω))).2) := by
  have hm : Measurable fun ω => Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω) :=
    (Sec7.StripSysField.measurable_returnField _ _).comp hh₂m
  have htrinf : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h₂ ω)
      (Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω)) := fun ω => by
    have h3 := GW2JointKernel.isChartTransport_infinitySourceChart_returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω)
    have e1 : Real.pi * chiC κ - 2 * Real.pi * chiC κ = -(Real.pi * chiC κ) := by ring
    have e2 : -chiC κ = chiC (16 / κ) := (chiC_sixteen_div hκ).symm
    rw [e1, e2] at h3
    exact h3
  have hFw := Theorem15.isOrderedForceWord_flowLine β.fn β.jumps 0
  have hgffF := Exist.isGFFWithBoundaryData_flowField hk β.isPiecewiseConstantBoundaryData 0 0 hβ
  have hff : (fun ω => Exist.flowField 0 (0 * chiC (16 / κ))
      (Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω))) =
      fun ω => Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω) := funext fun ω => by
    rw [zero_mul]; exact Sec5.GlueCond.flowField_zero_zero _
  rw [hff] at hgffF
  obtain ⟨𝓕, VL, VR, B, hCpl⟩ := Exist.Staged.isOptionalHullCoupling_drv h12p h13 hk hFw hgffF
    ((measurable_cfDrv h12p hk β).comp hm) (Eventually.of_forall fun _ => rfl)
  exact ⟨β.fn, β.jumps, _, β.isPiecewiseConstantBoundaryData, htrinf,
    _, 𝓕, VL, VR, B, fun ω => Sec7.StripSysField.isTranslateAddConst_zero_self _ _, hCpl⟩

/-! ### The tips at one sample -/

/-- **GB6's pathwise clause at one sample gives the tips** (deterministic). At a sample with an interior flow tip
before the lifetime, if the GB6 canonical-space point `x` of the chart field is good and its decoded driver satisfies
GB6's hull identity, then every tip of that driver, read through the chart `(Chart.id.loewner U T).trans
infinitySourceChart` of the flow's own component, lies in the completed counterflow range. -/
theorem tips_mem_range_of_sample {κ : ℝ} {hω Hω : DistOn upperHalfPlaneOpens} {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞}
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
    {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hB : HasBdryLimits (fwdMapInv U T))
    (hch : ownComponentChart (fun r : ℝ => wα r.toNNReal) s = ownComponentChart U T) :
    ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner U T).trans infinitySourceChart).tipAt (fun t => gb6WC t x) r z →
      z ∈ counterflowCompletedRange w := by
  obtain ⟨-, hWCc, hWC0, hΓgen, hunb, hKWC⟩ := gb6_pathwise (x := x) gb6EndpointStatement hα hwα hwα0 hs hsH
    hγ hw hw0 htrγ htr hHx hgood hcode hjL hjR hK
  obtain ⟨-, ℓ, -, -, -, hid⟩ := isGB6ChartContinuation_of_relHulls htr hα hwα hwα0 hs hsH hγ hw hw0 hΓgen
    hWCc hWC0 hunb hKWC
  have htrΓ := (isGeneratingTrace_gb6Γ hgood.2.2.1).2
  have hdense := mem_closure_setOf_mem_H (transientDenseQ_of_isGeneratingTrace hΓgen hWCc hWC0 htrΓ)
  have hR := CounterflowRange.isClosed_counterflowCompletedRange hγ hw hw0 htrγ
  refine mem_of_tipAt_loewner_inf hU hU0 hT hB hΓgen hWCc hWC0 hdense hR fun u hu => ?_
  have hidu := hid u hu
  rw [hch] at hidu
  exact mem_counterflowCompletedRange_of_sphereInv hγ hw hw0 hidu


/-- **Theorem 1.4's leaf `GB6PrefixPairStatement` from GB6's hull identity** (conditional helper with a distinct name;
Theorems 1.2–1.3 at universes `u` and `0` are the permitted roots of Theorem 1.4's wiring). -/
theorem gb6PrefixPairStatement_of_hullDet (hD : GB6HullDetStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : GB6PrefixPairStatement.{u} := by
  intro κ hκ hκ4 θ hθ b jumps hb Ω mΩ hSB Q hQ h hG W ζ hcf hζ Wα ζα hfl s hs g hgm hgeq
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
  refine ⟨_, _, isCenteredCounterflowDriver_cfDrv h12p h13 hκ hκ' hh₂m hGFF'', ?_, ?_⟩
  · filter_upwards [hcmp, hkg] with ω' hc' hk'
    exact hc'.1.trans hk'.1
  filter_upwards [hcmp, hkg, hgc, hrecν, hK₀] with ω' hc' hk' hgc' hr' hA'
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
  rw [hW₂eq]
  refine tips_mem_range_of_sample (x := (Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω'),
      F (gb6WordOfRec κ θ c (g ω₀), Sec7.StripSysField.returnField (Real.pi * chiC κ) (chiC κ) (h₂ ω')),
      (jLOfRec (g ω₀), jROfRec (g ω₀)))) hα' hdrv'.2 hdrv'.1 hs' hαH' hcomp'.2.1 hWc' hcfd'.1 hcomp'.2.2
    (hHc'' hs' hαH') hHceq.symm hk' hgc' ?_ ?_ ?_ hUc hU0 hT0 hB hch
  · show jLOfRec (g ω₀) = _
    rw [← hrec'']; exact (hgood' hs').1.2.2.1
  · show jROfRec (g ω₀) = _
    rw [← hrec'']; exact (hgood' hs').1.2.2.2.1
  · have h7 := hHull' hs' hαH'
    rw [hβeq, hHceq] at h7
    exact h7

/-- **GB6's two Theorem 1.4 leaves from its hull identity**: `GB6CondDetStatement` (the leaf of the expanded wiring,
`gb6CondDetStatement_of_hullDet`) and `GB6PrefixPairStatement` both follow from `GB6HullDetStatement` and Theorems
1.2–1.3. -/
theorem gb6CondDet_and_prefixPair_of_hullDet (hD : GB6HullDetStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) :
    GB6CondDetStatement.{u} ∧ GB6PrefixPairStatement.{u} :=
  ⟨gb6CondDetStatement_of_hullDet hD, gb6PrefixPairStatement_of_hullDet hD h12 h13 h12₀ h13₀⟩

end BRLeaf

end Theorem14

end InteractingSLE
