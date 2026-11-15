/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineIfaceR

/-!
# SB2ZsIface: `SB2DrvLineIfaceR` for the lifetime-generic line version `SB2LineVersionG`

Packet PROVE-T14-SB2DRV (round 15, decision D4: SB2(1) at announced stops). The declarations of `SB2DrvLineIfaceR` that
depend on the line version, for `SB2LineVersionG` (guards `a t < Λ w` in place of `a t < thr`), with the suffix `G`.
The proofs are the landed ones with the guard replaced. No source theorem is replaced.
-/
/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/

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

end EntranceUnion

/-! ### The repaired version data -/

/-! ### The two named inputs, repaired -/

/-- **The lifetime-generic line version (decision D4)**: `SB2LineVersionR` with a lifetime `Λ w` per word type in
place of the threshold `thr` in every guard, and without the generating trace, the remainder link and the field
`life` (these are asked per stop in the stopped version). At SB2(1)'s stop `m`, `W` is the driver frozen at the stop
and `Λ w = min (V m) thr`; `Λ_le` records `Λ ≤ thr` (for the identification at the stop). -/
structure SB2LineVersionG {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) where
  𝓗 : Filtration ℝ≥0 mΩ
  W : ℝ≥0 → Ω → ℝ
  a : ℝ≥0 → Ω → ℝ≥0∞
  Λ : WordType → Ω → ℝ≥0∞
  marks_le : D.marks ≤ 𝓗 0
  W_zero : ∀ ω, W 0 ω = 0
  W_cont : ∀ ω, Continuous fun t => W t ω
  W_adapted : StronglyAdapted 𝓗 W
  clock_cont : ∀ ω, Continuous fun t => a t ω
  clock_mono : ∀ ω, Monotone fun t => a t ω
  clock_zero : ∀ ω, a 0 ω = 0
  clock_meas : ∀ t, Measurable[D.lineFiltC HP t] (a t)
  timeChange : ∀ (q : ℝ≥0) (D' : Set Ω), MeasurableSet[𝓗 q] D' → ∀ t,
    MeasurableSet[D.lineFiltC HP t] (D' ∩ {ω | (q : ℝ≥0∞) ≤ a t ω})
  reach : ∀ w ∈ I.types, ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    (q : ℝ≥0∞) < Λ w ω →
    ∃ t, (q : ℝ≥0∞) ≤ a t ω
  reg : ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    Aux79.IsForceReg W (geomLW W (cellXL κ ψ I.word w)) (geomRW W (cellXR κ ψ I.word w))
      (Λ w) ω
  safeS : ∀ w ∈ I.types, ∀ (φ : TestOn upperHalfPlaneOpens) t, MeasurableSet[D.lineFiltC HP t]
    {ω | a t ω < Λ w ω ∧
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  safeL : ∀ w ∈ I.types, ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[D.lineFiltC HP t]
    {ω | a t ω < Λ w ω ∧
      Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)}
  chain : ∀ w ∈ I.types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    a t ω < Λ w ω →
    Tc.IsSB2LineChainAt (lowerPrefix κ b jumps E (k + 1) u ω) u (launchEntry κ b jumps E (k + 1) u ω)
      (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω) (fun q => W q ω) (fun t => a t ω)
      (Λ w ω) t
  alive : ∀ w ∈ I.types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    a t ω < Λ w ω →
    (t : ℝ≥0∞) < ζ ω
  Λ_le : ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
    Λ w ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω


/-- **Named input, the kernel half, repaired (R108)** (PROVE-T14-SB2DRV): from the repaired version data, K2's (S) and
(L) for the chart field on every type cell of the entrance event. -/
def SB2LineKernelRStatementG : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionG HP I D),
    ∀ w ∈ I.types,
      HasSafeLaw κ (typedRhoL w) (typedRhoR w) P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (Vd.Λ w) Vd.W
        (geomLW Vd.W (cellXL κ ψ I.word w)) (geomRW Vd.W (cellXR κ ψ I.word w))
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (Vd.Λ w) Vd.W
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω))
end InteractingSLE.Theorem14.SB.Lv

