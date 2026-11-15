/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBFrontier
import InteractingSLE.Spec.Jordan.Coupling
import InteractingSLE.Foundations.Loewner.HullBasic
import InteractingSLE.Spec.Supplement.S9BTransfer

/-!
# The remainder of a history in the conditional field of a random domain (Lemma SB2; shared with BW1, BR4a)

Packet PROVE-T14-SB2. The supplement repeatedly identifies **the remainder of one history** with **a history launched in
the conditional field of a random domain**: Lemma SB2 (p. 630–633, `source/spec/p625-671.md` L113–L124: "the
post-`T_L` relative portion [...] is the canonical upper flow of the conditional field in `D_A`"; "the remaining tail
[...] is again a finite simple proper lower walk of the retained conditional field"), Lemma S4 (p. 579), Proposition
BW1 (p. 615: "Conditional on the marked terminal history `A`, the actual prefix `η[0, T]` is the complete counterflow of
the conditional component field in `U`") and Corollary BR4a. This file supplies the carriers, in exactly the form of the
frozen `IsStagedHistory` launch clause ("conditionally on the retained history, that piece is the angle-`θ` flow line of
the conditional field in the current domain, read in `c` with its inherited lift"), with the conditioning σ-algebra,
the chart and the event made explicit:

* `IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ`: for `P`-a.e. `ω₀ ∈ F`, under `condExpKernel P 𝒢 ω₀` the field
  read in the chart `c ω₀` (flow rule `(1, 0, χ)`) and `(W, ζ)` satisfy the frozen `IsFlowLineDriver` at angle `θ`
  with the piecewise-constant data `bc ω₀` off `jc ω₀`;
* `IsCondCounterflowDriverOn κ 𝒢 P F h c W ζ`: the same for the frozen centred counterflow (BW1, BR4a);
* `IsCondStagedHistoryOn κ 𝒢 P F h c bc jc spec E`: the same for a whole frozen staged history (SB2(2): the lower
  tail is "again a finite simple proper lower walk of the retained conditional field").

The data `bc ω₀` are those of the conditional field (`IsCondChartField` states its Gaussian law when needed).
The frozen staged histories are instances: `IsStagedHistory.isCondFlowLineDriverOn` (each launched piece, given
`pastSigma`, in its launch chart).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### The carriers -/

section Carriers

/- The conditioning σ-algebra `𝒢` is bound before the ambient instance `mΩ` (as in `IsCondChartField`), so
that instance search always finds `mΩ`. -/

/-- **A flow line of the conditional field in a random chart** (the frozen `IsStagedHistory` launch clause with the
σ-algebra, the chart and the event explicit; supplement SB2(1), S4: "the canonical angle-`ϑ` flow of the conditional
field in `D`"): for `P`-almost every `ω₀ ∈ F`, conditionally on `𝒢` (`condExpKernel P 𝒢 ω₀`), the field `h` read in
the chart `c ω₀` with the flow rule (1.4) and the driver `W` with lifetime `ζ` satisfy the frozen angle-`θ`
`IsFlowLineDriver`, with the piecewise-constant data `bc ω₀` off `jc ω₀`. -/
def IsCondFlowLineDriverOn {Ω : Type u} (κ θ : ℝ) (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (F : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (c : Ω → Chart) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsPiecewiseConstantBoundaryData (bc ω₀) (jc ω₀) ∧
    ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
      IsFlowLineDriver κ (bc ω₀) (jc ω₀) θ (condExpKernel P 𝒢 ω₀) h' W ζ

/-- **A centred counterflow of the conditional field in a random chart** (Proposition BW1, p. 615: "the complete
counterflow of the conditional component field in `U`, from `y` to that prime end over `q`"; Corollary BR4a): for
`P`-almost every `ω₀ ∈ F`, conditionally on `𝒢`, the field read in the chart `c ω₀` with the flow rule and `(W, ζ)`
satisfy the frozen `IsCenteredCounterflowDriver` (its data are part of that predicate). -/
def IsCondCounterflowDriverOn {Ω : Type u} (κ : ℝ) (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (F : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (c : Ω → Chart) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
    ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
      IsCenteredCounterflowDriver κ (condExpKernel P 𝒢 ω₀) h' W ζ

/-- **A staged history of the conditional field in a random chart** (Lemma SB2(2), p. 631: "the result is again a
finite simple proper lower walk of the retained conditional field"): for `P`-almost every `ω₀ ∈ F`, conditionally on
`𝒢`, the drivers `E` form a frozen `IsStagedHistory` of the program `spec ω₀` for the field read in the chart `c ω₀`,
with the piecewise-constant data `bc ω₀` off `jc ω₀` (which drive the boundary continuations of the program). -/
def IsCondStagedHistoryOn {Ω : Type u} (κ : ℝ) (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (F : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (c : Ω → Chart) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (spec : Ω → ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsPiecewiseConstantBoundaryData (bc ω₀) (jc ω₀) ∧
    ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport (c ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
      IsStagedHistory κ (bc ω₀) (jc ω₀) (condExpKernel P 𝒢 ω₀) h' (spec ω₀) E

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P] {κ θ : ℝ} {F F' : Set Ω} {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart}
  {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- A conditional flow line on `F` is one on every smaller event. -/
theorem IsCondFlowLineDriverOn.mono (hW : IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ) (hF : F' ⊆ F) :
    IsCondFlowLineDriverOn κ θ 𝒢 P F' h c bc jc W ζ := by
  filter_upwards [hW] with ω₀ hω₀ hF'
  exact hω₀ (hF hF')

/-- A conditional counterflow on `F` is one on every smaller event. -/
theorem IsCondCounterflowDriverOn.mono (hW : IsCondCounterflowDriverOn κ 𝒢 P F h c W ζ) (hF : F' ⊆ F) :
    IsCondCounterflowDriverOn κ 𝒢 P F' h c W ζ := by
  filter_upwards [hW] with ω₀ hω₀ hF'
  exact hω₀ (hF hF')

/-- A conditional staged history on `F` is one on every smaller event. -/
theorem IsCondStagedHistoryOn.mono {spec : Ω → ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsCondStagedHistoryOn κ 𝒢 P F h c bc jc spec E) (hF : F' ⊆ F) :
    IsCondStagedHistoryOn κ 𝒢 P F' h c bc jc spec E := by
  filter_upwards [hE] with ω₀ hω₀ hF'
  exact hω₀ (hF hF')

/-- Modifying the event on a null set does not change a conditional flow line. -/
theorem IsCondFlowLineDriverOn.congr_ae (hW : IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ)
    (hFF : ∀ᵐ ω ∂P, ω ∈ F' → ω ∈ F) : IsCondFlowLineDriverOn κ θ 𝒢 P F' h c bc jc W ζ := by
  filter_upwards [hW, hFF] with ω₀ hω₀ hF hF'
  exact hω₀ (hF hF')

/-- Changing the chart, the data or the event on a null set does not change a conditional flow line. -/
theorem IsCondFlowLineDriverOn.congr_chart {c' : Ω → Chart} {bc' : Ω → ℝ → ℝ} {jc' : Ω → Finset ℝ}
    (hW : IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ)
    (hcc : ∀ᵐ ω ∂P, ω ∈ F → c' ω = c ω ∧ bc' ω = bc ω ∧ jc' ω = jc ω) :
    IsCondFlowLineDriverOn κ θ 𝒢 P F h c' bc' jc' W ζ := by
  filter_upwards [hW, hcc] with ω₀ hω₀ hc hF
  obtain ⟨e1, e2, e3⟩ := hc hF
  rw [e1, e2, e3]
  exact hω₀ hF

/-- **A conditional flow line, together with the conditional field, is a flow line in a domain** (`Jordan`'s
`IsDomainFlowLine`) under almost every kernel measure, when the random chart takes the marked prime ends of the random
domain to `0, ∞`. -/
theorem IsCondFlowLineDriverOn.isDomainFlowLine (hW : IsCondFlowLineDriverOn κ θ 𝒢 P F h c bc jc W ζ)
    (hG : IsCondChartField 𝒢 1 0 (chiC κ) P h c bc jc) {D : Ω → Set ℂ} {x y : ∀ ω, PrimeEnd (D ω)}
    (hc : ∀ᵐ ω ∂P, ω ∈ F → IsDomainChartAt (D ω) (x ω) (y ω) (c ω)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      IsDomainFlowLine κ (D ω₀) (x ω₀) (y ω₀) (c ω₀) (bc ω₀) (jc ω₀) θ (condExpKernel P 𝒢 ω₀) h W ζ := by
  filter_upwards [hW, hG, hc] with ω₀ hW₀ hG₀ hc₀ hF
  obtain ⟨hb, h', ht, hfl⟩ := hW₀ hF
  obtain ⟨-, h'', ht'', hg⟩ := hG₀
  have e : h'' = h' := IsDomainChartAt.chartField_unique (hc₀ hF) ht'' ht
  subst e
  exact ⟨hc₀ hF, hb, h'', ht, hg, hfl⟩

end Carriers

/-! ### The frozen staged histories are instances -/

/-- The chart in which instruction `k` of the history launched its ordinary piece (`Chart.id` if it launched none). -/
def launchChart (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    Chart :=
  ((ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k).elim Chart.id Prod.fst

/-- **Each launched piece of a frozen staged history is a conditional flow line** given the retained history
(`pastSigma`), in its launch chart, on the event that instruction `k` launched it at angle `θ` (the frozen
`IsStagedHistory` launch clause; the data of the conditional field are chosen for each realization). -/
theorem _root_.InteractingSLE.IsStagedHistory.exists_isCondFlowLineDriverOn {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) (k : ℕ) (θ : ℝ) :
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ),
      IsCondFlowLineDriverOn κ θ (pastSigma κ b jumps spec E k) P
        {ω₀ | ∃ c, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ)} h
        (fun ω₀ => launchChart κ b jumps spec (fun j => E j ω₀) k) bc jc
        (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) := by
  classical
  set Q : Ω → Prop := fun ω₀ => ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
      IsPiecewiseConstantBoundaryData b' jumps' ∧
      (∀ ω, IsChartTransport (launchChart κ b jumps spec (fun j => E j ω₀) k) 1 0 (chiC κ) (h ω) (h' ω)) ∧
      IsFlowLineDriver κ b' jumps' θ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h'
        (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2) with hQ
  refine ⟨fun ω₀ => if hq : Q ω₀ then hq.choose else fun _ => 0,
    fun ω₀ => if hq : Q ω₀ then hq.choose_spec.choose else ∅, ?_⟩
  filter_upwards [hS.2.2.2 k] with ω₀ hω₀ hF
  obtain ⟨c, hc⟩ := hF
  have hl : launchChart κ b jumps spec (fun j => E j ω₀) k = c := by
    simp only [launchChart, hc, Option.elim]
  have hq : Q ω₀ := by
    obtain ⟨b', jumps', h', hb', ht, hfl⟩ := hω₀ c θ hc
    exact ⟨b', jumps', h', hb', by rw [hl]; exact ht, hfl⟩
  simp only [hq, ↓reduceDIte]
  obtain ⟨h', hb', ht, hfl⟩ := hq.choose_spec.choose_spec
  exact ⟨hb', h', ht, hfl⟩

/-! ### Geometry of a retained history -/

/-- The smallest original real point of `A` (`L = min(A ∩ ℝ)`, S2, SB2(1)). -/
def realMin (A : Set ℂ) : ℝ := sInf {x : ℝ | (x : ℂ) ∈ A}

/-- The largest original real point of `A` (`R = max(A ∩ ℝ)`, SB2(2)). -/
def realMax (A : Set ℂ) : ℝ := sSup {x : ℝ | (x : ℂ) ∈ A}

/-- The compact filled hull `K_A` of a retained history `A`: its filling in `ℍ` (`fillH`) together with its real base
`[min(A ∩ ℝ), max(A ∩ ℝ)]`. Its complement in `ℍ` is `D_A = ℍ \ fillH A`. -/
def hullK (A : Set ℂ) : Set ℂ := fillH A ∪ ((↑) : ℝ → ℂ) '' Icc (realMin A) (realMax A)

/-- **The chart of `D_A` at the left entry prime end over `L`** (S2: "starting from the left original-real base prime
end `g_A(L⁻)`"; SB2(1): "from the prime end over `L` incident to the untouched original-real interval on its left";
"The far-left original-real interval anchors the derivative logarithm at zero"): `c` is a chart of
`D_A = ℍ \ fillH A`; it extends continuously to the untouched real interval `(−∞, L)` with boundary values tending to
`0` as `x ↑ L`; it takes `∞` to `∞`; and its lift tends to `0` on `(−∞, L)`. -/
def IsLeftEntryChart (A : Set ℂ) (L : ℝ) (c : Chart) : Prop :=
  IsDomainChart (H \ fillH A) c ∧
    (∃ e : ℝ → ℝ, (∀ x < L, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) ∧ Tendsto e (𝓝[<] L) (𝓝 0)) ∧
    Tendsto c.1 (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (Bornology.cobounded ℂ) ∧
    ∀ x < L, Tendsto c.2.2 (𝓝[H] (x : ℂ)) (𝓝 0)

/-- **The chart of `D_A` at the right entry prime end over `R`** (SB2(2): "from the prime end over `R` selected by its
free right collar"; "reflect this construction and anchor on the far-right original-real interval"): the reflection
of `IsLeftEntryChart`, with the untouched real interval `(R, ∞)`. -/
def IsRightEntryChart (A : Set ℂ) (R : ℝ) (c : Chart) : Prop :=
  IsDomainChart (H \ fillH A) c ∧
    (∃ e : ℝ → ℝ, (∀ x > R, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) ∧ Tendsto e (𝓝[>] R) (𝓝 0)) ∧
    Tendsto c.1 (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (Bornology.cobounded ℂ) ∧
    ∀ x > R, Tendsto c.2.2 (𝓝[H] (x : ℂ)) (𝓝 0)

/-- **The surviving original heights in the chart** (SB2(1): "Real connectors of `A` retain their original field
values"; SB2(2): "All inherited [...] real connectors and marks are retained"; S4, "On every surviving original
interval its phase is zero by Aux. 57"): at every original real point `x` off `jumps` whose upper collar is free
(not filled by `A`), and wherever the chart has a real boundary value `e` there (off `jc`), the conditional data are
the original height: `bc e = b x`. -/
def RetainsOriginalHeights (A : Set ℂ) (c : Chart) (b : ℝ → ℝ) (jumps : Finset ℝ) (bc : ℝ → ℝ) (jc : Finset ℝ) :
    Prop :=
  ∀ x : ℝ, x ∉ jumps → (∀ᶠ z in 𝓝[H] (x : ℂ), z ∉ fillH A) → ∀ e : ℝ,
    Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e : ℂ)) → e ∉ jc → bc e = b x

/-- The first time a curve visits the point `z` within its available range (`⊤` if it does not). -/
def firstVisit (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (z : ℂ) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : (s : ℝ≥0∞) ≤ ζ ∧ η s = z), (s : ℝ≥0∞)

/-- The physical points of a history through its first `k` instructions (its root, the ordinary pieces and the
recorded connectors of the state after `k` instructions); `ExplState.physSet` is the case `k = length`. -/
def prefixPhysSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    Set ℂ :=
  let s := ExplState.run κ b jumps spec D k
  {(spec.1 : ℂ)} ∪ (⋃ p ∈ s.1, p.1.tipSet p.2.1 p.2.2) ∪ ⋃ a ∈ s.2.1, ((↑) : ℝ → ℂ) '' a

theorem prefixPhysSet_length (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    prefixPhysSet κ b jumps spec D spec.2.2.length = ExplState.physSet κ b jumps spec D := rfl

/-- The history has stopped at a new right record: at a right continuation threshold, or at the restart mark ending
a rightward connector (SB2(1): "ending at a finite right record or at the end of its next rightward real interval"). -/
def EndsAtRightRecord (s : ExplState) : Prop :=
  s.2.2.2.2.2.1 = (Sum.inr (Sum.inr (Sum.inl (some true))) : ExplStatus) ∨
    s.2.2.2.2.2.1 = (Sum.inr (Sum.inr (Sum.inr (Sum.inl (true, true)))) : ExplStatus)

/-- The physical image through the chart `c` of a set `S` of the chart's coordinate: the limits of `c.inv` at the
points of `S` from `ℍ` (the continuous finite-fiber boundary extension, S2), which for `w ∈ ℍ` is `c.inv w`. -/
def chartBoundaryImage (c : Chart) (S : Set ℂ) : Set ℂ := {z | ∃ w ∈ S, Tendsto c.2.1 (𝓝[H] w) (𝓝 z)}

/-- The physical points, through the chart `c`, of a history run in the coordinate of `c` (data `b'` off `jumps'`):
its root and connectors through the boundary extension of `c.inv`, its ordinary pieces through the composed charts. -/
def relPhysSet (κ : ℝ) (b' : ℝ → ℝ) (jumps' : Finset ℝ) (c : Chart) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Set ℂ :=
  let s := ExplState.run κ b' jumps' spec D spec.2.2.length
  chartBoundaryImage c {(spec.1 : ℂ)} ∪ (⋃ p ∈ s.1, (c.trans p.1).tipSet p.2.1 p.2.2) ∪
    ⋃ a ∈ s.2.1, chartBoundaryImage c (((↑) : ℝ → ℂ) '' a)

/-! ### Convention S1 -/

/-- **Convention S1** (one-sided completion for a possibly noninjective history; supplement p. 577,
`source/spec/p577-624.md` L5–L12): the finite simple prefix `β([0, a])` "has a proper continuous injective extension
`β̂` in `closure ℍ` from `0` to infinity whose full closed right Jordan side contains `A`. The right side is defined
by adjoining the lower vertical ray at `0` and using the orientation from `0` along `β̂` to infinity." -/
def IsOneSided (A : Set ℂ) (β : ℝ≥0 → ℂ) (a : ℝ≥0) : Prop :=
  ∃ β' : ℝ≥0 → ℂ, IsProperCompletion β a β' ∧ A ⊆ Supp9B.closedRightSide β'

/-- S1 is inherited by smaller histories. -/
theorem IsOneSided.mono {A A' : Set ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0} (h : IsOneSided A β a) (hA : A' ⊆ A) :
    IsOneSided A' β a := by
  obtain ⟨β', hβ', hA'⟩ := h
  exact ⟨β', hβ', hA.trans hA'⟩

/-- S1 for a prefix gives S1 for every shorter prefix (the same witness). -/
theorem IsOneSided.of_le {A : Set ℂ} {β : ℝ≥0 → ℂ} {a a' : ℝ≥0} (h : IsOneSided A β a) (ha : a' ≤ a) :
    IsOneSided A β a' := by
  obtain ⟨β', ⟨h1, h2, h3, h4, h5⟩, hA⟩ := h
  exact ⟨β', ⟨h1, h2, h3, h4, fun t ht => h5 t (ht.trans ha)⟩, hA⟩

/-! ### The histories of Section 28 -/

section Histories

variable {Ω : Type u}

/-- The completed lower walk `R` of Theorem 1.4 (angle `−π/2`, continuing right), as a physical set. -/
def lowerWalkSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    Set ℂ :=
  ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)

/-- The state of the lower walk after its first `k` instructions. -/
def lowerWalkState (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (ω : Ω) : ExplState :=
  ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k

/-- The retained lower-walk prefix `A` of SB2(1): the first `k` instructions of the lower walk, with the initial real
bridge `[u, 0]` from the upper seed `u ≤ 0` (retained as original boundary data, not as an ordinary piece). -/
def lowerPrefix (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u : ℝ)
    (ω : Ω) : Set ℂ :=
  prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0

/-- The retained upper history `A` of SB2(2): the first `k` instructions of the schedule `l` from `u ≤ 0`, with the
real bridge `[u, 0]` to the lower seed `0`. -/
def upperPrefix (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω : Ω) : Set ℂ :=
  prefixPhysSet κ b jumps ⟨u, true, scheduleProgram 0 l⟩ (fun j => E ⟨u, true, scheduleProgram 0 l⟩ j ω) k ∪
    ((↑) : ℝ → ℂ) '' Icc u 0

end Histories

/-! ### Lemma SB2 -/

/-- **Lemma SB2(1)** (the upper erasure; supplement pp. 630–631, `source/spec/p625-671.md` L113–L122), in the
setting of Theorem 1.4. Let `A` be the lower-walk prefix through `k` instructions, ending at a right record (a right
threshold or the end of a rightward connector), with the initial real bridge `[u, 0]` from the upper seed `u ≤ 0`
whose heights satisfy SB1's conditions. Let `η` be the constant angle-`ψ` flow from `u` (`−π/2 < ψ ≤ π/2`), and
assume S1 for `A` and every available prefix of `η`. Put `L = min(A ∩ ℝ)`, `T_L` the first visit of `η` to `L`, and
`T = t ∧ ζ` for a deterministic `t` ("one clipped available upper stop", SB3). Then

* `η([0, T ∧ T_L]) ⊆ K_A` (the filled hull with its real base);
* conditionally on the retained lower history (a σ-algebra `𝒢 ⊇ pastSigma`), on `{T_L < T}`: in a left entry chart
  `c` of `D_A` at `L`, a driver `Wr` (lifetime `ζr`) is the angle-`ψ` flow line of the conditional field ("the
  canonical upper flow of the conditional field in `D_A`, from the prime end over `L` incident to the untouched
  original-real interval on its left"), the surviving original real points keep their heights ("Real connectors of
  `A` retain their original field values"), and the post-`T_L` portion `η((T_L, T])` is the physical trace of `Wr`
  through a relative stop `Tr ≤ ζr`, which lies in `η([T_L, T])` ("with its original stop reconstructed"). -/
def SB2UpperStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ → ψ ≤ Real.pi / 2 →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, EndsAtRightRecord (lowerWalkState κ b jumps E k ω) →
        ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
    ∀ t : ℝ≥0∞,
      (∀ᵐ ω ∂P, EndsAtRightRecord (lowerWalkState κ b jumps E k ω) →
        η ω '' {s | (s : ℝ≥0∞) ≤ min (min t (ζ ω))
            (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω)))} ⊆
          hullK (lowerPrefix κ b jumps E k u ω)) ∧
      ∃ (𝒢 : MeasurableSpace Ω) (c : Ω → Chart) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (Wr : ℝ≥0 → Ω → ℝ)
        (ζr Tr : Ω → ℝ≥0∞),
        𝒢 ≤ mΩ ∧
        pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k ≤ 𝒢 ∧
        IsCondFlowLineDriverOn (mΩ := mΩ) κ ψ 𝒢 P
          {ω | EndsAtRightRecord (lowerWalkState κ b jumps E k ω) ∧
            firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω)) < min t (ζ ω)}
          h c bc jc Wr ζr ∧
        ∀ᵐ ω ∂P, EndsAtRightRecord (lowerWalkState κ b jumps E k ω) →
          firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω)) < min t (ζ ω) →
          IsLeftEntryChart (lowerPrefix κ b jumps E k u ω) (realMin (lowerPrefix κ b jumps E k u ω)) (c ω) ∧
          RetainsOriginalHeights (lowerPrefix κ b jumps E k u ω) (c ω) b jumps (bc ω) (jc ω) ∧
          Tr ω ≤ ζr ω ∧
          η ω '' {s | firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω)) < (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) ≤ min t (ζ ω)} ⊆ (c ω).tipSet (fun r => Wr r ω) (Tr ω) ∧
          (c ω).tipSet (fun r => Wr r ω) (Tr ω) ⊆
            η ω '' {s | firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω)) ≤ (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) ≤ min t (ζ ω)}

/-- **Lemma SB2(2)** (the lower erasure; supplement p. 631, `source/spec/p625-671.md` L121), in the setting of
Theorem 1.4. Let `B` be the completed lower walk and `A` the upper history through `k` instructions of a schedule `l`
from `u ≤ 0` with angles `ψ_j ∈ (−π/2, π/2]`, with the real bridge `[u, 0]` adjoined (its lower left groups
admissible). Suppose `A` is almost surely on the closed left of `B`. Put `R = max(A ∩ ℝ)`. Then `B` visits `R`, and
conditionally on the retained upper history (`𝒢 ⊇ pastSigma`), in a right entry chart `c` of `D_A` at `R` (the
conditional field there is a GFF with data `bc`, which keep the surviving original heights), the remaining tail of `B`
is a lower walk `E'` of the conditional field ("again a finite simple proper lower walk of the retained conditional
field, from the prime end over `R` selected by its free right collar"): its physical points (through `c`) lie on `B`
and contain every point of `B` in `D_A` ("the erased initial portion lies in `K_A`"). -/
def SB2LowerStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∃ (𝒢 : MeasurableSpace Ω) (c : Ω → Chart) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ)
        (E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
        𝒢 ≤ mΩ ∧
        pastSigma κ b jumps ⟨u, true, scheduleProgram 0 l⟩ (E ⟨u, true, scheduleProgram 0 l⟩) k ≤ 𝒢 ∧
        IsCondChartField (mΩ := mΩ) 𝒢 1 0 (chiC κ) P h c bc jc ∧
        IsCondStagedHistoryOn (mΩ := mΩ) κ 𝒢 P univ h c bc jc
          (fun ω => boundaryWalkSpec (bc ω) (jc ω) (-(Real.pi / 2)) true) E' ∧
        ∀ᵐ ω ∂P,
          IsRightEntryChart (upperPrefix κ b jumps E u l k ω) (realMax (upperPrefix κ b jumps E u l k ω)) (c ω) ∧
          RetainsOriginalHeights (upperPrefix κ b jumps E u l k ω) (c ω) b jumps (bc ω) (jc ω) ∧
          ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈ lowerWalkSet κ b jumps E ω ∧
          lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E u l k ω)) ⊆
            relPhysSet κ (bc ω) (jc ω) (c ω) (boundaryWalkSpec (bc ω) (jc ω) (-(Real.pi / 2)) true)
              (fun j => E' j ω) ∧
          relPhysSet κ (bc ω) (jc ω) (c ω) (boundaryWalkSpec (bc ω) (jc ω) (-(Real.pi / 2)) true)
              (fun j => E' j ω) ⊆ lowerWalkSet κ b jumps E ω

end SB

end Theorem14

end InteractingSLE
