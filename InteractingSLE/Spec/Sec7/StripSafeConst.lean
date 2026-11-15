/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7Aux131Walls
import InteractingSLE.Spec.Sec7.Aux37GermFlowStrip
import InteractingSLE.Spec.Sec5.Prop59SchedReal

/-!
# The constant-angle strip system, constructed without Theorem 1.2/1.3 (R48)

Packet PROVE-STRIPSYS-SAFE. Theorem 1.2's R.7 input `hstrip` (`R7Leaves.R7StripOnConfig`: a strip system
`StripSys.IsStripSystem` on every R.7 configuration) is used only through the strip system's field, counterflow and
its **constant-angle** incoming paths `η_θ` (the one-instruction programs `R7Aux131.constSpec θ`, `θ ∈ [−π/2, π/2]`):
PROVE-AUX37-WALLS' witness exclusions (`Aux37Walls.hwit_r7`, `hwitI_r7`) and everything they call read `hS.staged`
only at `constSpec θ`.

**Why not the whole strip system.** `IsStripSystem` asks for every boundary-continued program. With the R.7 heights
(`b + aχ ≤ −λ` on `ℝ₋`, `≥ λ` on `ℝ₊` for every `a ∈ [−π/2, π/2]`), a piece launched after non-hitting pieces of
angles `θ₁, …, θ_{k−1}` sees the exposed sides of all of them, at heights `−λ − θᵢχ` (left) and `λ − θᵢχ` (right).
Its flow-line word satisfies (4.4) (`Sec4.Cond44`: right partial sums `≥ 0`) directly iff `θ_k ≥ max θᵢ`, and after
the reflection `z ↦ −z̄` iff `θ_k ≤ min θᵢ`. For the program `π/2, −π/2, 0` (own times `1, 1, ∞`) the third piece's
word is admissible on both sides but satisfies (4.4) in neither orientation (the first piece's right side has height
`λ − πχ/2 < λ` at angle `0`, the second piece's left side height `−λ + πχ/2 > −λ`), so determining it needs Theorem 1.2
outside §4.2's regime — exactly what R48 forbids here (`Theorem12ParamCond44Statement`, R74, covers only (4.4) words).

So this file isolates what the R.7 chain uses:

* **`IsConstStripSystem`**: `IsStripSystem` with `staged` restricted to the constant-angle programs;
  `StripSys.IsStripSystem.toConst` (every strip system is one);
* `constFam`: the drivers `admDrv θ` (field-determined, `h44`) of the field for every program, regular at every sample;
* **`isStagedHistory_constFam`**: they realize `constSpec θ` as a staged history when the flow-line word at `θ`
  satisfies (4.4) (sealed Theorem 1.1 + `h44` + Remark 2.3, PROVE-PROP59-SCHED's `isFlowLineDriver_admDrv`);
* **`exists_isConstStripSystem`**: a constant-angle strip system on every field and centred counterflow whose data
  have the strip heights at every angle of `[−π/2, π/2]`, with drivers regular at every sample;
* the ports to `IsConstStripSystem` (same proofs) of `R7Aux131.isStagedHistory_const`, `…ae_isSimpleProper_const`,
  `StripPocketPath.ae_counterflow_trace`, `…ae_isLoewnerTrace_counterflow`, `Aux37Germ.isLocalSet_cfHull`.

R48: no Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param`; the only named input is
`h44` (R74).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.StripSafe

open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open Exist.Staged (IsRegularDriver)
open R7Aux131 (constSpec)

/-! ### The constant-angle strip system -/

/-- **The constant-angle strip system**: `StripSys.IsStripSystem` with its staged histories required only for the
constant-angle programs `constSpec θ`, `θ ∈ [−π/2, π/2]` (the incoming paths `η_θ` of Aux. lemmas 130–131). The field
names are those of `IsStripSystem`. -/
structure IsConstStripSystem (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop where
  kappa_pos : 0 < κ
  kappa_lt_four : κ < 4
  boundaryData : IsPiecewiseConstantBoundaryData b jumps
  gff : IsGFFWithBoundaryData P h b jumps
  counterflow : IsCenteredCounterflowDriver κ P h W' ζ'
  lifetime : ∀ᵐ ω ∂P, ζ' ω = ⊤
  staged : ∀ θ : ℝ, θ ∈ Icc (-(π / 2)) (π / 2) → IsStagedHistory κ b jumps P h (constSpec θ) (E (constSpec θ))

section System

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- Every strip system is a constant-angle strip system. -/
theorem _root_.InteractingSLE.Sec7.StripSys.IsStripSystem.toConst
    (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es) : IsConstStripSystem κ b jumps P h W' ζ' Es :=
  ⟨hS.kappa_pos, hS.kappa_lt_four, hS.boundaryData, hS.gff, hS.counterflow, hS.lifetime,
    fun _ hθ => R7Aux131.isStagedHistory_const hS hθ⟩

/-- The drivers of `η_θ` form a staged history of the strip field (port of `R7Aux131.isStagedHistory_const`). -/
theorem isStagedHistory_const (hS : IsConstStripSystem κ b jumps P h W' ζ' Es) {θ : ℝ}
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) : IsStagedHistory κ b jumps P h (constSpec θ) (Es (constSpec θ)) :=
  hS.staged θ hθ

/-- **Every version of `η_θ` is almost surely a simple proper curve** (port of `R7Aux131.ae_isSimpleProper_const`). -/
theorem ae_isSimpleProper_const (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hreg : ∀ ω, IsRegularDriver (Es (constSpec θ) 0 ω))
    {γ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (constSpec θ) 0 ω).1 ⊤ (γ ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (γ ω) := by
  obtain ⟨hL0, hR0⟩ := R7Aux131.heights_const hS.kappa_pos hS.kappa_lt_four hcumL hcumR hθ
  exact StripPocketPath.ae_isSimpleProper_of_simple_trace hreg (R7Aux131.ae_simple_trace_const hS.kappa_pos
    hS.kappa_lt_four hS.boundaryData hS.gff (isStagedHistory_const hS hθ) hL0 hR0) hγc hγ0 hγtr

/-- **The counterflow has a continuous trace** (port of `StripPocketPath.ae_counterflow_trace`). -/
theorem ae_counterflow_trace (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η := by
  have hκ := hS.kappa_pos
  have hb := hS.boundaryData
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hS.gff hS.counterflow
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hbd := StripPocketPath.counterflowData_bounds_off hκ (g := b) (J := jumps)
    (fun x hx hxJ => by have := hcumL _ hm x hx hxJ; linarith)
    (fun x hx hxJ => by have := hcumR _ hp x hx hxJ; linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk'
    (StripSysField.isPiecewiseConstant_counterflowData κ hb) hbd.1 hbd.2
  have hF' := Theorem15.isOrderedForceWord_flowLine (StripSysField.counterflowData κ b)
    (StripSysField.counterflowJumps jumps) 0
  have hE := hC'.1
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE,
    hE.2.2.2.2] with ω ⟨hζ, _, η, hη⟩ hpth
  have hw : Continuous fun t => W' t ω := by
    have := hpth.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  exact ⟨hζ, hw, hpth.1, η, hη⟩

/-- **Every version of the counterflow's trace is a Loewner trace** (port of
`StripPocketPath.ae_isLoewnerTrace_counterflow`). -/
theorem ae_isLoewnerTrace_counterflow (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (fun s : ℝ => W' s.toNNReal ω) (η ω) ∧ Continuous (fun s : ℝ => W' s.toNNReal ω) ∧
      W' (0 : ℝ).toNNReal ω = 0 := by
  filter_upwards [ae_counterflow_trace hS hcumL hcumR, hηtr] with ω hω hη
  obtain ⟨-, hc, h0, -⟩ := hω
  refine ⟨StripPocketPath.isLoewnerTrace_congr (fun s hs => ?_) (isLoewnerTrace_of_isGeneratingTrace hη),
    hc.comp continuous_real_toNNReal, by rw [Real.toNNReal_zero]; exact h0⟩
  simp only [Real.coe_toNNReal _ (mem_Ici.1 hs)]

/-- **The counterflow hull at a fixed time is a local set of the centred field** (port of
`Aux37Germ.isLocalSet_cfHull`). -/
theorem isLocalSet_cfHull (hS : IsConstStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    (u₀ : ℂ → ℝ) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (t : ℝ≥0) :
    IsLocalSet (Aux37Germ.cfHull W' ζ' t) (WholeField.centredField h u₀) P := by
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [ae_counterflow_trace hS hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  exact WholeField.IsLocalSet.sub_dist (Sec5.GlueCond.isLocalSet_cfHullQ hS.counterflow hreg t)
    (WholeField.isHarmonicDistOn_smoothDist hu₀)

end System

/-! ### The R48-safe construction -/

section Construction

open Sec7.AdmCode Exist.StagedLaw
open Exist.Staged (instrAngle)

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- **The constant-angle drivers**: for every program, the field-determined angle-`θ` flow-line driver `admDrv θ` of
the field (`θ` the angle of the program's first instruction), for a boundary word `c₀` of the data. -/
def constFam {Ω : Type*} (c₀ : Restart.BoundaryWord) (h : Ω → DistOn upperHalfPlaneOpens) :
    ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  fun spec _ ω => admDrv h44 hκ hκ4 (instrAngle spec 0) (c₀, h ω)

theorem constFam_constSpec {Ω : Type*} (c₀ : Restart.BoundaryWord) (h : Ω → DistOn upperHalfPlaneOpens) (θ : ℝ)
    (k : ℕ) (ω : Ω) : constFam h44 hκ hκ4 c₀ h (constSpec θ) k ω = admDrv h44 hκ hκ4 θ (c₀, h ω) :=
  rfl

theorem constFam_regular {Ω : Type*} (c₀ : Restart.BoundaryWord) (h : Ω → DistOn upperHalfPlaneOpens)
    (spec : ExplSpec) (k : ℕ) (ω : Ω) : IsRegularDriver (constFam h44 hκ hκ4 c₀ h spec k ω) :=
  admDrv_regular h44 hκ hκ4 _ _

theorem measurable_constFam {Ω : Type*} [MeasurableSpace Ω] (c₀ : Restart.BoundaryWord)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (spec : ExplSpec) (k : ℕ) :
    Measurable (constFam h44 hκ hκ4 c₀ h spec k) :=
  (measurable_admDrv h44 hκ hκ4 _).comp (measurable_const.prodMk hh)

/-- No instruction after the first of `constSpec θ` launches a piece. -/
theorem launches_constSpec_succ {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (θ : ℝ)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) {c : Chart} {θ' : ℝ} :
    (ExplState.run κ b jumps (constSpec θ) D (k + 1 + 1)).2.2.2.1 (k + 1) ≠ some (c, θ') := by
  intro hl
  have h1 := (eq_launch_of_launches (constSpec θ) D hl).1
  simp [constSpec] at h1

/-- **The constant-angle drivers realize `constSpec θ`** as a staged history of a GFF with data `b`, when the angle-`θ`
flow-line word of `b` satisfies (4.4) (heights `hL`, `hR`). -/
theorem isStagedHistory_constFam {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {c₀ : Restart.BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {θ : ℝ}
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + π * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) :
    IsStagedHistory κ b jumps P h (constSpec θ) (constFam h44 hκ hκ4 c₀ h (constSpec θ)) := by
  set E := constFam h44 hκ hκ4 c₀ h (constSpec θ) with hEdef
  have hEm : ∀ k, Measurable (E k) := measurable_constFam h44 hκ hκ4 c₀ hh.1 _
  have hreg : ∀ k ω, IsRegularDriver (E k ω) := constFam_regular h44 hκ hκ4 c₀ h _
  -- the data of `c₀`
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  have h44θ : Sec4.Cond44 κ (flowLineRhoL κ c₀.fn c₀.jumps 0 θ) (flowLineRhoR κ c₀.fn c₀.jumps 0 θ) := by
    refine StripDet.cond44_flowLine_of_heights hκ c₀.isPiecewiseConstantBoundaryData θ (fun y hy hyJ => ?_)
      (fun y hy hyJ => ?_)
    · rw [hc₀J] at hyJ
      rw [hc₀ y hyJ]
      exact hL y hy hyJ
    · rw [hc₀J] at hyJ
      rw [hc₀ y hyJ]
      exact hR y hy hyJ
  obtain ⟨-, hfl⟩ := Sec5.Prop59Sched.isFlowLineDriver_admDrv h44 hκ hκ4 θ c₀ h44θ hh₀ (hEm 0)
    (Eventually.of_forall fun ω => rfl)
  refine ⟨hEm, fun k => ?_, fun k => Eventually.of_forall fun ω => (hreg k ω).2.2.2, fun k => ?_⟩
  · rw [Exist.Staged.pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb _ (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl).comap_le
  · rcases k with _ | k
    · refine Eventually.of_forall fun ω₀ c θ' hl => ?_
      rw [R7Aux131.launches_run_one_constSpec θ] at hl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl)
      refine ⟨c₀.fn, c₀.jumps, h, c₀.isPiecewiseConstantBoundaryData, fun ω => ?_, ?_⟩
      · have h2 := isChartTransport_shiftChart 0 (chiC κ) (h ω)
        rwa [Prop74B.flowField_zero_zero] at h2
      · rw [Theorem14.GW1.pastSigma_zero_eq_bot, Theorem14.GW1.condExpKernel_bot_apply]
        exact hfl
    · exact Eventually.of_forall fun ω₀ c θ' hl => absurd hl (launches_constSpec_succ θ _ k)

include h44 hκ hκ4 in
/-- **A constant-angle strip system exists, R48-safely,** on every standard Borel probability space carrying a GFF `h`
with data `b` (strip heights `hcumL`, `hcumR` at every angle of `[−π/2, π/2]`) and a centred counterflow of `h` with
infinite lifetime: the drivers `constFam` (field-determined, from `h44`), regular at every sample. -/
theorem exists_isConstStripSystem {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) :
    ∃ Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, IsConstStripSystem κ b jumps P h W' ζ' Es ∧
      ∀ spec k ω, IsRegularDriver (Es spec k ω) := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  refine ⟨constFam h44 hκ hκ4 c₀ h, ⟨hκ, hκ4, hb, hh, hcf, hζ', fun θ hθ => ?_⟩, constFam_regular h44 hκ hκ4 c₀ h⟩
  obtain ⟨hL, hR⟩ := R7Aux131.heights_const hκ hκ4 hcumL hcumR hθ
  exact isStagedHistory_constFam h44 hκ hκ4 hb hc₀J hc₀ hh hL hR

end Construction

end InteractingSLE.Sec7.StripSafe
