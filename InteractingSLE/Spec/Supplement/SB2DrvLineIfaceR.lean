/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2TcChainAt
import InteractingSLE.Spec.Restart.FCLocality

/-!
# The repaired interface between SB2(1)'s two line halves (ruling R108)

Packet PROVE-T14-SB2DRV (round 6). PROVE-AUX61-NOJUMP proved (`Tc.SB2LineVersion.ae_lifetime_ne_top`) that the
version data `SB2LineVersion` of `SB2DrvLineIface` force a finite flow lifetime almost surely (one physical horizon
for the chain record), so `SB2LineVersionStatement` is false. Ruling R108 repairs the interface; the old one stays in
place for its committed consumers. The successor here:

* **`EntranceUnion.lineFiltC`**: the physical line filtration completed by `P`-null sets inside the ambient
  σ-algebra, `T ↦ mΩ ⊓ aeSigma (D.absMarks T) P`; it contains `D.lineFilt` and the entrance σ-algebra, and
  history-marked locality for `D.absMarks T` passes to it (`isHistoryAvoidanceLocal_lineFiltC`);
* **`SB2LineVersionR`**: the version data with every measurability field for `lineFiltC`, the chain record at one
  physical time `t` (`Tc.IsSB2LineChainAt … t`, used when `a t < thr`), and the clause `alive`: the physical time `t`
  is below the flow lifetime `ζ` whenever `a t < thr` (the relative lifetime is reached no later than the physical one;
  needed by the line mean, which reads the flow up to `t`);
* the named inputs **`SB2LineVersionRStatement`** (PROVE-AUX61-NOJUMP) and **`SB2LineKernelRStatement`** (this packet),
  and **`sb2EntranceLinesStatement_of_halvesR`**, **`sb2DriverLinkAmbStatement_of_halvesR`**.
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

/-! ### The completed physical line filtration -/

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The completed physical line filtration**: `T ↦ mΩ ⊓ aeSigma (D.absMarks T) P` (the line filtration with the
`P`-null modifications of its events added, inside the ambient σ-algebra). -/
def lineFiltC (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (_HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    Filtration ℝ≥0 mΩ :=
  ⟨fun t => mΩ ⊓ LocalSets.aeSigma (D.absMarks (t : ℝ≥0∞)) P,
    fun _ _ hst => inf_le_inf_left _ fun _ ⟨G', hG', hGG'⟩ =>
      ⟨G', D.absMarks_mono (ENNReal.coe_le_coe.2 hst) G' hG', hGG'⟩,
    fun _ => inf_le_left⟩

theorem lineFilt_le_lineFiltC (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (t : ℝ≥0) : D.lineFilt HP t ≤ D.lineFiltC HP t :=
  le_inf ((D.lineFilt HP).le t) fun s hs => ⟨s, hs, EventuallyEq.rfl⟩

theorem marks_le_lineFiltC (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (t : ℝ≥0) : D.marks ≤ D.lineFiltC HP t :=
  (D.marks_le_lineFilt HP t).trans (D.lineFilt_le_lineFiltC HP t)

/-- **History-marked locality for the absolute line passes to the completed line filtration.** -/
theorem isHistoryAvoidanceLocal_lineFiltC (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (t : ℝ≥0) {B : Ω → Set ℂ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hloc : WholeField.IsHistoryAvoidanceLocal (D.absMarks (t : ℝ≥0∞)) B h₀ P) :
    WholeField.IsHistoryAvoidanceLocal (D.lineFiltC HP t) B h₀ P :=
  Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma hloc

end EntranceUnion

/-! ### The repaired version data -/

/-- **The version half's data, repaired (R108)**: as `SB2LineVersion`, with the measurability fields (`clock_meas`,
`timeChange`, `safeS`, `safeL`) for the completed line filtration `D.lineFiltC`, the chain record at one physical time
(`chain`: at every `t`, almost surely on the type cell and below the relative lifetime, `Tc.IsSB2LineChainAt … t`),
and `alive`: below the relative lifetime the physical time is below the flow lifetime. -/
structure SB2LineVersionR {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
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
  clock_meas : ∀ t, Measurable[D.lineFiltC HP t] (a t)
  timeChange : ∀ (q : ℝ≥0) (D' : Set Ω), MeasurableSet[𝓗 q] D' → ∀ t,
    MeasurableSet[D.lineFiltC HP t] (D' ∩ {ω | (q : ℝ≥0∞) ≤ a t ω})
  reach : ∀ w ∈ I.types, ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    (q : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
    ∃ t, (q : ℝ≥0∞) ≤ a t ω
  reg : ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    Aux79.IsForceReg W (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
      (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) ω
  safeS : ∀ w ∈ I.types, ∀ (φ : TestOn upperHalfPlaneOpens) t, MeasurableSet[D.lineFiltC HP t]
    {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  safeL : ∀ w ∈ I.types, ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[D.lineFiltC HP t]
    {ω | a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω ∧
      Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  chain : ∀ w ∈ I.types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
    Tc.IsSB2LineChainAt (lowerPrefix κ b jumps E (k + 1) u ω) u (launchEntry κ b jumps E (k + 1) u ω)
      (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω) (fun q => W q ω) (fun t => a t ω)
      (FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω) t
  alive : ∀ w ∈ I.types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
    (t : ℝ≥0∞) < ζ ω

/-! ### The two named inputs, repaired -/

/-- **Named input, the version half, repaired (R108)** (PROVE-AUX61-NOJUMP). -/
def SB2LineVersionRStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀),
    Nonempty (SB2LineVersionR HP I D)

/-- **Named input, the kernel half, repaired (R108)** (PROVE-T14-SB2DRV): from the repaired version data, K2's (S) and
(L) for the chart field on every type cell of the entrance event. -/
def SB2LineKernelRStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionR HP I D),
    ∀ w ∈ I.types,
      HasSafeLaw κ (typedRhoL w) (typedRhoR w) P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) Vd.W
        (geomLW Vd.W (cellXL κ ψ I.word w)) (geomRW Vd.W (cellXR κ ψ I.word w))
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) Vd.W
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω))

/-- **The two repaired halves give K2's line data in the entrance σ-algebra.** -/
theorem sb2EntranceLinesStatement_of_halvesR (hV : SB2LineVersionRStatement.{u})
    (hK : SB2LineKernelRStatement.{u}) : SB2EntranceLinesStatement.{u} := by
  intro κ b jumps Ω mΩ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D
  obtain ⟨Vd⟩ := hV κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D
  exact ⟨Vd.𝓗, Vd.W, Vd.Γ, Vd.marks_le, Vd.W_zero, Vd.W_cont, Vd.W_adapted,
    hK κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd, Vd.Vg, Vd.link, Vd.life⟩

/-- **SB2(1)'s ambient driver link from the two repaired line halves** (Theorems 1.2–1.3 as hypotheses, R48). -/
theorem sb2DriverLinkAmbStatement_of_halvesR (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hV : SB2LineVersionRStatement.{u}) (hK : SB2LineKernelRStatement.{u}) :
    SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_lineData h12p h13 (sb2EntranceLinesStatement_of_halvesR hV hK)

end InteractingSLE.Theorem14.SB.Lv
