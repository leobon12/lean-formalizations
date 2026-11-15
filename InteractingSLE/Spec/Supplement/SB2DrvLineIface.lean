/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEntrK2
import InteractingSLE.Spec.Supplement.SB2DrvLine
import InteractingSLE.Spec.Supplement.SB2DrvLineAbs
import InteractingSLE.Spec.Supplement.SB2FinConfig
import InteractingSLE.Spec.Supplement.SB2GLift
import InteractingSLE.Spec.Supplement.SBLwShift

/-!
# The interface between SB2(1)'s two line halves

Packet PROVE-T14-SB2DRV (round 4). `SB2EntranceLinesStatement` (K2's line data in the entrance σ-algebra `D.marks`) is
split between two workers:

* the **version half** (PROVE-AUX61-NOJUMP): the physical-to-relative time change, the relative driver `W` with its
  trace `Γ` and the remainder link (E3/E5), the lifetime reconstruction (E7), the clock and safe-event measurability
  for the physical line filtration, and the per-sample S2 chain record `IsSB2LineChain` — packaged as the data
  **`SB2LineVersion`** and the named input **`SB2LineVersionStatement`**;
* the **kernel half** (PROVE-T14-SB2DRV): K2's (S) and (L) on the type cells of the entrance event from these data —
  the line kernels at `T_L + t` given `D.lineMarks t`, the line means read in the launch chart (the flow-line chart
  law of the remainder, through the relative configuration of the chain record), the line locality — the named input
  **`SB2LineKernelStatement`**.

**`sb2EntranceLinesStatement_of_halves`**: the two halves give `SB2EntranceLinesStatement`, hence (with
`sb2DriverLinkAmbStatement_of_lineData`) SB2(1)'s driver link. `EntranceUnion.lineFilt` is the physical line
filtration `T ↦ D.absMarks T`, indexed by the **absolute** physical time `T` of the upper flow (the union
`A ∪ η([0, max(T, T_L)])`, history-marked local, nested, containing the entrance σ-algebra: `SB2DrvLineAbs`); the clock
`a T` is the relative time reached at absolute physical time `T` (`0` up to `T_L`). Absolute times are needed by FIN's
union mean (the flow hull at a deterministic time is a local set by itself; at `T_L + t` it is not).

The chain record is stated in the coordinates shifted by the upper seed `u` (prefix path from `0`, the shifted launch
chart `shiftChart c u m`, `m` the entry point read in the chart), exactly as consumed by FIN's
`FinRel.isRelConfigJK_of_s2_liftOn` and produced by `Lv.exists_relConfig_of_path_of_finite`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal

/-! ### The physical line filtration -/

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The physical line filtration**: `T ↦ D.absMarks T` (retained past and the killed histories of the capped upper
flows through `max(T, T_n)`), absolute physical time `T`. -/
def lineFilt (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    Filtration ℝ≥0 mΩ :=
  ⟨fun t => D.absMarks (t : ℝ≥0∞), fun _ _ hst => D.absMarks_mono (ENNReal.coe_le_coe.2 hst),
    fun t => D.absMarks_le HP (t : ℝ≥0∞)⟩

theorem marks_le_lineFilt (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (t : ℝ≥0) : D.marks ≤ D.lineFilt HP t :=
  D.marks_le_absMarks (t : ℝ≥0∞)

end EntranceUnion

/-! ### The per-sample chain record -/

/-- **The S2 chain record of the upper flow after its entrance** at one sample, in coordinates shifted by the seed `u`
(supplement pp. 631–633; Lemma S2's lift and the relative chain, `FinRel.IsSB2RelChain`): the retained prefix `A`
shifted by `−u` is a path `p` from `0`; the shifted launch chart `shiftChart c u m` is a left entry chart of it with a
finite-fibre continuous boundary map `g` and real-vanishing lift; the shifted upper flow has a proper S1 witness `β'`
with the prefix on its closed right side, visiting `L − u` at its first visit time `t_L = T_L` and equal to the shifted
flow before the physical horizon `t_L + S`; the post-`t_L` portion
has the proper S2 lift `γ` (`g ∘ γ = β'(t_L + ·)`), with relative chains `(Wr, ηr)` on every physical horizon below
`S > 0`, no real arc after the entrance, and the physical Loewner driver `w` of the shifted flow, whose hulls are the
fills of the witness; K2's relative driver is the chain driver, the relative clock at the absolute physical time `T`
is `0` up to `t_L` and the capacity clock of `γ` at `T − t_L` after it, and the relative lifetime `V` is reached only
below the horizon `t_L + S`. -/
def IsSB2LineChain (A : Set ℂ) (u m : ℝ) (c : Chart) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (W : ℝ≥0 → ℝ)
    (a : ℝ≥0 → ℝ≥0∞) (V : ℝ≥0∞) : Prop :=
  ∃ (p : ℝ → ℂ) (g : ℂ → ℂ) (β' γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (S : ℝ) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (w : ℝ → ℝ)
    (ηw : ℝ → ℂ),
    -- the retained prefix, shifted
    (ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
      (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧ p '' Icc 0 1 = (fun z => z - (u : ℂ)) '' A) ∧
    -- the shifted launch chart
    (IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) (Lw.shiftChart c u m) ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g (Lw.shiftChart c u m).2.1 H ∧
      (∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧ FinRel.LiftRealOn (Lw.shiftChart c u m)) ∧
    -- the S1 witness of the shifted upper flow and its S2 lift
    (Supp9B.IsProperCurve β' ∧ β' 0 = 0 ∧ p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' ∧
      β' tL = realMin (p '' Icc 0 1) ∧ ((tL : ℝ≥0) : ℝ≥0∞) = firstVisit η ζ (realMin A) ∧
      Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s, g (γ s) = β' (tL + s)) ∧
    -- the witness is the shifted flow before the physical horizon
    (∀ t : ℝ≥0, (t : ℝ) < (tL : ℝ) + S → β' t = η t - u) ∧
    -- the relative chains below the physical horizon
    (0 < S ∧ (∀ S₀ : ℝ, 0 ≤ S₀ → S₀ < S → FinRel.IsSB2RelChain (p '' Icc 0 1) (Lw.shiftChart c u m) β' γ tL S₀ Wr ηr) ∧
      interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) ∧
    -- the physical Loewner driver of the shifted flow
    (Continuous w ∧ w 0 = 0 ∧ IsLoewnerTrace w ηw ∧
      (∀ s : ℝ, 0 < s → s < S → fwdHull w ((tL : ℝ) + s) = fillH (β' '' Icc 0 (tL + s.toNNReal))) ∧
      ∀ r : ℝ, 0 ≤ r → r < (tL : ℝ) + S → ηw r = β' r.toNNReal) ∧
    -- K2's driver, clock and lifetime
    ((∀ q : ℝ≥0, (q : ℝ≥0∞) < V → W q = Wr q) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ tL → a t = 0) ∧
      (∀ t : ℝ≥0, (tL : ℝ) ≤ t → (t : ℝ) < tL + S →
        a t = ((Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (t - tL)).toNNReal : ℝ≥0∞)) ∧
      ∀ t : ℝ≥0, a t < V → (t : ℝ) < tL + S)

/-! ### The version half's data -/

/-- **The version half's data** for one SB2(1) problem, chart record and entrance construction: the relative filtration
`𝓗 ⊇ D.marks`, the relative driver `W` (adapted, continuous from `0`) with its relative trace `Γ`, generating up to `Vg`
and linked to the actual remainder, the lifetime reconstruction `Vg = thr_w` on every type cell; the relative clock `a`
(absolute physical time `T` of the upper flow ↦ relative time, `0` up to `T_L`), continuous, monotone, from `0`, adapted
to the physical line filtration, with the time-change compatibility of `𝓗`; on every type cell the reach of the
lifetime, the force regularity, the measurability of the safe events in the line filtration, and almost surely the
chain record. -/
structure SB2LineVersion {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) where
  𝓗 : Filtration ℝ≥0 mΩ
  W : ℝ≥0 → Ω → ℝ
  Γ : Ω → ℝ≥0 → ℂ
  Vg : Ω → ℝ≥0∞
  a : ℝ≥0 → Ω → ℝ≥0∞
  marks_le : D.marks ≤ 𝓗 0
  W_zero : ∀ ω, W 0 ω = 0
  W_cont : ∀ ω, Continuous fun t => W t ω
  W_adapted : StronglyAdapted 𝓗 W
  link : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
    firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
    IsGeneratingTrace (fun t => W t ω) (Vg ω) (Γ ω) ∧
      IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
        (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
        (fun t => Γ ω t + launchEntry κ b jumps E (k + 1) u ω) (Vg ω)
  life : ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
    firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
    ω ∈ wordTypeCell κ ψ I.word D.event w →
    Vg ω = FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω
  clock_cont : ∀ ω, Continuous fun t => a t ω
  clock_mono : ∀ ω, Monotone fun t => a t ω
  clock_zero : ∀ ω, a 0 ω = 0
  clock_meas : ∀ t, Measurable[D.lineFilt HP t] (a t)
  timeChange : ∀ (q : ℝ≥0) (D' : Set Ω), MeasurableSet[𝓗 q] D' → ∀ t,
    MeasurableSet[D.lineFilt HP t] (D' ∩ {ω | (q : ℝ≥0∞) ≤ a t ω})
  reach : ∀ w ∈ I.types, ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    (q : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
    ∃ t, (q : ℝ≥0∞) ≤ a t ω
  reg : ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    Aux79.IsForceReg W (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
      (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) ω
  safeS : ∀ w ∈ I.types, ∀ (φ : TestOn upperHalfPlaneOpens) t, MeasurableSet[D.lineFilt HP t]
    {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  safeL : ∀ w ∈ I.types, ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[D.lineFilt HP t]
    {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
      Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  chain : ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    IsSB2LineChain (lowerPrefix κ b jumps E (k + 1) u ω) u (launchEntry κ b jumps E (k + 1) u ω)
      (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω) (fun q => W q ω) (fun t => a t ω)
      (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω)

/-! ### The two named inputs -/

/-- **Named input, the version half** (PROVE-AUX61-NOJUMP): the version data exist for every SB2(1) problem, chart
record and entrance construction. -/
def SB2LineVersionStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀),
    Nonempty (SB2LineVersion HP I D)

/-- **Named input, the kernel half** (PROVE-T14-SB2DRV): from the version data, K2's (S) and (L) for the chart field on
every type cell of the entrance event, with the reconstructed lifetime. -/
def SB2LineKernelStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersion HP I D),
    ∀ w ∈ I.types,
      HasSafeLaw κ (typedRhoL w) (typedRhoR w) P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) Vd.W
        (geomLW Vd.W (cellXL κ ψ I.word w)) (geomRW Vd.W (cellXR κ ψ I.word w))
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) Vd.W
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω))

/-- **The two halves give K2's line data in the entrance σ-algebra.** -/
theorem sb2EntranceLinesStatement_of_halves (hV : SB2LineVersionStatement.{u}) (hK : SB2LineKernelStatement.{u}) :
    SB2EntranceLinesStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D
  obtain ⟨Vd⟩ := hV κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D
  exact ⟨Vd.𝓗, Vd.W, Vd.Γ, Vd.marks_le, Vd.W_zero, Vd.W_cont, Vd.W_adapted,
    hK κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd, Vd.Vg, Vd.link, Vd.life⟩

/-- **SB2(1)'s ambient driver link from the two line halves** (Theorems 1.2–1.3 as hypotheses, R48). -/
theorem sb2DriverLinkAmbStatement_of_halves (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hV : SB2LineVersionStatement.{u}) (hK : SB2LineKernelStatement.{u}) :
    SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_lineData h12p h13 (sb2EntranceLinesStatement_of_halves hV hK)

end InteractingSLE.Theorem14.SB.Lv
