/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PieceSimpleMeas
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.GW1LaterR51
import InteractingSLE.Spec.Supplement.GW2LaterPass

/-!
# Lemma GW1: each new piece of a boundary walk is simple and meets the old union only at its seed

Packet PROVE-T14-GW1Z. Lemma GW1, proof (`source/spec/p577-624.md` L957, p. 619), "The next ordinary piece and the full
old union". GW1's induction keeps, at the launch of each ordinary piece `β_j` of the right walk (from the seed `w_j`,
in the unbounded component `U_j` of the complement of the old union `A_j`):

* item 2: "Given this retained datum, `η[0, T_{w_j}]` has the complete conditional counterflow kernel in `U_j` from
  `y` to `w_j`";
* item 3: "Every point of `A_j \ {w_j}` has first counterflow visit strictly after `T_{w_j}`."

`IsLaunchClock` is this datum at the launch of instruction `k`, in the clock form in which BW1 and BR4a state their
conditional pairs (`BW1.BW1Statement`, `BR4a.BR4aStatement`): a process `Wk` which, under the regular conditional law
given the retained past, drives the centred counterflow of the field read in the launch chart, with infinite lifetime;
and almost surely a continuous strictly increasing clock `ℓ` onto `[0, T)`, `T` the first time the original physical
counterflow tip lies in the old union (`T = T_{w_j}` by item 3), under which the relative physical tips are the
original ones. `WalkLaunchClockStatement` asks for it at every launch of the right walk and of its left mirror.

## Main results

* `GW1PieceSimpleStatement` (**the per-piece statement**): almost surely, every ordinary piece launched by the right
  walk is a simple curve (continuous injective parametrization of its physical points, proper when infinite) that
  meets the old union (`SB.prefixPhysSet` before its instruction) only at its first point, the tip at time `0`.
* `ae_mem_pieceVisitEvent`: GB6 under the conditional law of a launch gives the measurable piece event
  (`PieceVisitEvent`: the piece is injective, and each of its points after time `0` is a point of the conditional
  counterflow) almost surely under that law.
* **`gw1PieceSimpleStatement_of_clock`**: the per-piece statement from GB6's restart law, GW0's forward implication,
  Theorem 1.3, the walk datum (`WalkLaunchClockStatement`) and the deterministic fibre statement for staged charts
  (`ChartFiberStatement`: "The continuous inverse chart is injective away from those old boundary fibers").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1Z

open Supp8.GB6 (IsFirstContactAtTip sphereInv)
open Exist.StagedLaw (instrTime)

/-! ### The statements -/

/-- The boundary walk programs of Lemma GW1: the right walk (`right = true`, angle `−π/2`, continuing right) and its
left mirror (`right = false`, angle `π/2`, continuing left). -/
abbrev walkSpec (b : ℝ → ℝ) (jumps : Finset ℝ) (right : Bool) : ExplSpec :=
  boundaryWalkSpec b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right

theorem walkAngle_mem_Icc (right : Bool) :
    (if right then -(Real.pi / 2) else Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hpi := Real.pi_pos
  cases right
  · exact ⟨by simp only [Bool.false_eq_true, ↓reduceIte]; linarith, by simp⟩
  · exact ⟨by simp, by simp only [↓reduceIte]; linarith⟩

/-- **A simple piece meeting `A` only after its first point**: for the piece driven by `W` up to its stop `S` and read
in the chart `c`, there are a boundary-limit map `f` of `c⁻¹` (moving points by at most `C`) and a continuous
generating trace `α` of `W` up to `S` (transient when `S = ∞`), such that the physical piece `f ∘ α` (whose image of
`[0, S]` is `c.tipSet`, `CounterflowRange.tipSet_stopped_eq_of_tendsto`) is injective on `[0, S]` and `f(α(t)) ∉ A`
for `0 < t ≤ S`. -/
def IsSimplePiece (c : Chart) (W : ℝ≥0 → ℝ) (S : ℝ≥0∞) (A : Set ℂ) : Prop :=
  ∃ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ) (C : ℝ), (∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) ∧
    (∀ p ∈ Hbar, ‖f p - p‖ ≤ C) ∧ W 0 = 0 ∧ ContinuousOn W {t | (t : ℝ≥0∞) ≤ S} ∧ IsGeneratingTrace W S α ∧
    (S = ⊤ → Tendsto (fun t => ‖α t‖) atTop atTop) ∧ InjOn (fun t => f (α t)) {t | (t : ℝ≥0∞) ≤ S} ∧
    ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → f (α t) ∉ A

/-- **A simple piece as a parametrized curve**: its physical points are the image of `[0, S]` under a continuous
injective map `g` starting at the piece's tip at time `0`, with `g(t) ∉ A` for `t > 0`, proper when `S = ∞`. -/
theorem IsSimplePiece.exists_param {c : Chart} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {A : Set ℂ} (hP : IsSimplePiece c W S A) :
    ∃ g : ℝ≥0 → ℂ, ContinuousOn g {t | (t : ℝ≥0∞) ≤ S} ∧ InjOn g {t | (t : ℝ≥0∞) ≤ S} ∧
      g '' {t | (t : ℝ≥0∞) ≤ S} = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ∧
      c.tipAt (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) 0 (g 0) ∧
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → g t ∉ A) ∧ (S = ⊤ → Tendsto (fun t => ‖g t‖) atTop atTop) := by
  obtain ⟨f, α, C, hf, hC, hW0, hW, hα, htr, hinj, havoid⟩ := hP
  exact exists_param_of_injOn hf hC hα hW hW0 htr hinj havoid

/-- **GW1, per piece** (p. 619: "The physical new piece is consequently simple and joins `A_j` only at `w_j`"), for
the staged families of Theorem 1.4 (drivers regular at every sample, launched pieces regular almost surely, ruling
R51): for the right walk and its left mirror, almost surely, every piece launched by the walk is a simple piece of
its launch chart meeting the old union before its instruction (`SB.prefixPhysSet`) only at its first point. -/
def GW1PieceSimpleStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ right : Bool, ∀ᵐ ω ∂P, ∀ (k : ℕ) (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (walkSpec b jumps right) (fun j => E (walkSpec b jumps right) j ω) (k + 1)).2.2.2.1
          k = some (c, θ) →
        IsSimplePiece c (E (walkSpec b jumps right) k ω).1
          (min (instrTime (walkSpec b jumps right) k) (E (walkSpec b jumps right) k ω).2)
          (SB.prefixPhysSet κ b jumps (walkSpec b jumps right) (fun j => E (walkSpec b jumps right) j ω) k)

/-- **GW1's induction data 2–3 at the launch of instruction `k`, in the clock form of BW1 and BR4a.** `Wk` (measurable
at each time) drives, under the regular conditional law given the retained past at almost every launch sample, the
centred counterflow of every field read in the launch chart, with infinite lifetime ("`η[0, T_{w_j}]` has the
complete conditional counterflow kernel in `U_j`"). Almost surely at a launch: `Wk` has infinite lifetime, a
continuous path from `0` and a continuous transient generating trace, and a continuous strictly increasing clock `ℓ`
maps `[0, ∞)` onto `[0, T)`, `T` the first time the original physical counterflow tip lies in the old union, so that
the relative physical tips (read through the launch chart and the inversion) are the original tips at the clock times
(item 3: the old points other than the seed are first visited after `T_{w_j}`, so `T = T_{w_j}`). -/
def IsLaunchClock (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (W' : ℝ≥0 → Ω → ℝ) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (Wk : ℝ≥0 → Ω → ℝ)
    (ζk : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0) : Prop :=
  (∀ t, Measurable (Wk t)) ∧
  (∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
    (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
    ∀ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) →
      IsCenteredCounterflowDriver κ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' Wk ζk ∧
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ζk ω = ⊤) ∧
  ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
    (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
    ζk ω = ⊤ ∧ Continuous (fun t => Wk t ω) ∧ Wk 0 ω = 0 ∧
    (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wk t ω) ⊤ γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop) ∧
    Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
    range (ℓ ω) = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart (fun t => W' t ω)
      (SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k)} ∧
    ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z ↔
      infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z

/-- **Named input: GW1's induction data 2–3 at every launch of either walk** (`IsLaunchClock`), for the staged
families of `GW1PieceSimpleStatement`. In the source it is maintained along the walk by BW1 (after a completed piece),
BW2 (the forced real connector) and BR4a (retargeting to the next seed), p. 618–620. -/
def WalkLaunchClockStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ (right : Bool) (k : ℕ), ∃ (Wk : ℝ≥0 → Ω → ℝ) (ζk : Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
        IsLaunchClock κ b jumps P h W' (walkSpec b jumps right) (E (walkSpec b jumps right)) k Wk ζk ℓ

/-- **Named deterministic statement: the boundary fibres of a staged chart lie on the old union** (GW1, p. 619: "The
continuous inverse chart is injective away from those old boundary fibers"). Along any run whose launched pieces are
regular, the chart `c` of a launch has a boundary-limit map `f` from inside `ℍ` moving points by a bounded amount, and
two points of `ℍ̄` with the same image outside the old union `SB.prefixPhysSet` coincide. -/
def ChartFiberStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞),
    (∀ (j : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2)) →
    ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      ∃ (f : ℂ → ℂ) (C : ℝ), (∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) ∧ (∀ p ∈ Hbar, ‖f p - p‖ ≤ C) ∧
        ∀ x ∈ Hbar, ∀ y ∈ Hbar, f x = f y → f x ∉ SB.prefixPhysSet κ b jumps spec D k → x = y

/-! ### The clock keeps the relative tips off the old union -/

/-- **A relative tip is an original tip before the first visit of `A`, hence not in `A`.** -/
theorem notMem_of_clock {c : Chart} {Wk W' : ℝ≥0 → ℝ} {ℓ : ℝ≥0 → ℝ≥0} {A : Set ℂ}
    (hrange : range ℓ = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart W' A})
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z) :
    ∀ (r : ℝ≥0) (z : ℂ), (c.trans infinitySourceChart).tipAt Wk r z → z ∉ A := by
  intro r z hz hzA
  have h1 : ((ℓ r : ℝ≥0) : ℝ≥0∞) < firstTipTime infinitySourceChart W' A := by
    have hmem : ℓ r ∈ range ℓ := ⟨r, rfl⟩
    rw [hrange] at hmem
    exact hmem
  have h2 : firstTipTime infinitySourceChart W' A ≤ ℓ r := iInf₂_le (ℓ r) ⟨z, hzA, (hiff r z).1 hz⟩
  exact absurd h2 (not_le.2 h1)

/-! ### GB6 under the conditional law of a launch -/

/-- **GB6 for the next ordinary piece, in a complete pair** (GW1, p. 619: "Apply GB6, within the independently
established complete conditional pair in item 2, to every available interior-tip prefix of `β_j`"). Under a probability
law `Q` (in the application: the regular conditional law given the retained past at a launch), let `h'` be the field
of an angle-`θ` flow-line coupling (`θ ∈ [−π/2, π/2]`, piecewise-constant data) driven by `e`, whose driver takes its
recorded limit at a finite lifetime, and let `Wk` drive the centred counterflow of `h'` with infinite lifetime. Then
almost surely the piece stopped at `min t₀ ζ` is in the measurable piece event: injective, and each of its points after
time `0` a point of the counterflow. Named inputs: GB6's restart law, GW0's forward implication, Theorem 1.3. -/
theorem ae_mem_pieceVisitEvent (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {θ : ℝ} (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {b' : ℝ → ℝ} {jumps' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' jumps')
    {h' : Ω → DistOn upperHalfPlaneOpens} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hfl : IsFlowLineDriver κ b' jumps' θ Q h' (fun t ω => (e ω).1 t) (fun ω => (e ω).2))
    (hrec : ∀ᵐ ω ∂Q, (e ω).2 ≠ ⊤ → 0 < (e ω).2 → ∀ c : ℝ,
      Tendsto (e ω).1 (𝓝[<] (e ω).2.toNNReal) (𝓝 c) → (e ω).1 (e ω).2.toNNReal = c)
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} (hWk : IsCenteredCounterflowDriver κ Q h' Wk ζk)
    (hζk : ∀ᵐ ω ∂Q, ζk ω = ⊤) (t₀ : ℝ≥0∞) :
    ∀ᵐ ω ∂Q, ω ∈ PieceVisitEvent e (fun ω => min t₀ (e ω).2) Wk := by
  have hh := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  obtain ⟨b'', J'', h'', hb'', htr, hcf⟩ := hWk
  have hκ' : 0 < 16 / κ := by positivity
  obtain ⟨hadmL, hadmR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hcf hζk
  set γ := GW2aSingle.chosenTrace Wk ζk with hγdef
  set α := GW2aSingle.chosenTrace (fun t ω => (e ω).1 t) (fun ω => (e ω).2) with hαdef
  have hγ := GW2aSingle.ae_chosenTrace hT13 hκ' hcf
  have hα := GW2aSingle.ae_chosenTrace hT13 hκ hfl
  have hcomp : ∀ᵐ ω ∂Q, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop := by
    filter_upwards [hγ, hζk] with ω hω hζ
    rw [hζ] at hω
    exact ⟨hζ, hω.1, hω.2 rfl⟩
  have hFC := Supp8.GB6.gb6FirstContactStatement_of_restart hGB6 κ θ hκ hκ4 hθ.1 hθ.2 Ω _ Q
    inferInstance h' b' jumps' Wk (fun t ω => (e ω).1 t) ζk (fun ω => (e ω).2) γ α b'' J'' h'' hb' hh hb''
    htr hcf hadmL hadmR hcomp hfl (hα.mono fun _ hω => hω.1)
  have hall := ae_all_iff.2 fun p : ℕ × ℕ => hFC (Sec2.Assembly.dyad p.1 p.2)
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hcfd := Supp8.GB6.ae_driver_zero_continuousOn hcf
  obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hthr := hC.1.ae_tendsto_threshold hκ
  filter_upwards [hcomp, hα, hall, hdrv, hcfd, hthr, hrec] with ω hcω hαω hqω hdω hcfω hthω hrecω
  have hWc : Continuous fun s => Wk s ω := by
    have hc' := hcfω.2
    rw [hcω.1] at hc'
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc'
    exact continuousOn_univ.1 hc'
  have hγc : Continuous (γ ω) := by
    have hc' := hcω.2.1.2.1
    simp only [le_top, ofPred_true] at hc'
    exact continuousOn_univ.1 hc'
  have hend : (e ω).2 ≠ ⊤ → 0 < (e ω).2 →
      Tendsto (e ω).1 (𝓝[<] (e ω).2.toNNReal) (𝓝 ((e ω).1 (e ω).2.toNNReal)) := by
    intro hne hpos
    have hT : (((e ω).2.toNNReal : ℝ≥0) : ℝ≥0∞) = (e ω).2 := ENNReal.coe_toNNReal hne
    have hTpos : 0 < (e ω).2.toNNReal := ENNReal.toNNReal_pos hpos.ne' hne
    obtain ⟨w₀, vL₀, vR₀, hlim, -⟩ := hthω _ hTpos hT
    have h1 : Tendsto (e ω).1 (𝓝[<] (e ω).2.toNNReal) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
    rw [hrecω hne hpos w₀ h1]
    exact h1
  have hWS : ContinuousOn (e ω).1 {s | (s : ℝ≥0∞) ≤ min t₀ (e ω).2} :=
    CounterflowRange.continuousOn_le_min t₀ hdω.2 hend
  have hαS : IsGeneratingTrace (e ω).1 (min t₀ (e ω).2) (α ω) := hαω.1.mono_horizon (min_le_right _ _)
  obtain ⟨hvis, hinj⟩ := visit_and_injOn_of_firstContact hαS hWS hdω.1 hγc fun s hs hsS hsH => by
    obtain ⟨p, rfl⟩ := hs
    exact hqω p (lt_of_lt_of_le hsS (min_le_right _ _)) hsH
  have hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < min t₀ (e ω).2 → LP.traceAt (rt q) (e ω).1 = α ω (rt q) := fun q hq =>
    LP.traceAt_eq_of_isGeneratingTrace hαω.1 hdω.2 hdω.1 (lt_of_lt_of_le hq (min_le_right _ _))
  have hG : ∀ r : ℚ, LP.traceAt (rt r) (fun s => Wk s ω) = γ ω (rt r) := fun r =>
    LP.traceAt_eq_of_isGeneratingTrace hcω.2.1 hWc.continuousOn hcfω.1 ENNReal.coe_lt_top
  exact ⟨sepAt_of_injOn hαS.2.1 hA hinj, visAt_of_visit hγc hA hG hvis⟩

/-! ### The per-piece statement -/

/-- The flow instructions of a boundary walk have the walk's angle, in `[−π/2, π/2]`. -/
theorem angle_walkSpec_mem {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool} {k : ℕ} {θ : ℝ} {t : ℝ≥0∞}
    (hk : (walkSpec b jumps right).2.2[k]? = some (Sum.inl (θ, t))) : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  rw [GW1Conn.getElem?_boundaryWalkSpec] at hk
  by_cases h1 : k < (walkSpec b jumps right).2.2.length
  · by_cases h2 : k % 2 = 0
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at hk
      rw [← hk.1]
      exact walkAngle_mem_Icc right
    · simp [h1, h2] at hk
  · simp [h1] at hk

/-- **GW1, per piece, for both walks** (p. 619), from GB6's restart law, GW0's forward implication, Theorem 1.3,
GW1's induction data 2–3 at every launch (`WalkLaunchClockStatement`) and the fibre statement for staged charts
(`ChartFiberStatement`). For each instruction `k`: GB6 under the conditional law at the launch gives the measurable
piece event kernel-almost surely (`ae_mem_pieceVisitEvent`); the launch event is in the retained past, so the event
holds `P`-almost surely on it (`GW2Later.ae_of_ae_condExpKernel_on'`); pathwise, the event gives injectivity and
visits (`injOn_of_sepAt`, `visit_of_visAt`), the clock keeps the relative tips off the old union (`notMem_of_clock`),
and `exists_param_of_visit` concludes. -/
theorem gw1PieceSimpleStatement_of_clock (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hD : WalkLaunchClockStatement.{u}) (hF : ChartFiberStatement) : GW1PieceSimpleStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg hR right
  have hwR := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (walkAngle_mem_Icc right) right
  have hS := hE (walkSpec b jumps right) hwR
  have hRs := hR (walkSpec b jumps right) hwR
  refine ae_all_iff.2 fun k => ?_
  obtain ⟨Wk, ζk, ℓ, hWm, hD1, hD2⟩ := hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hR right k
  set spec := walkSpec b jumps right with hspec
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.1 k ≠ none}
    with hLdef
  have hL : MeasurableSet[pastSigma κ b jumps spec (E spec) k] L :=
    GW1W.measurableSet_pastSigma_launch hb spec hS.1 (hreg spec) k
  set M := PieceVisitEvent (E spec k) (fun ω => min (instrTime spec k) (E spec k ω).2) Wk with hMdef
  have hM : MeasurableSet M := measurableSet_pieceVisitEvent (hS.1 k)
    (measurable_const.min (measurable_snd.comp (hS.1 k))) hWm
  have hker : ∀ᵐ ω₀ ∂P, ω₀ ∈ L →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec (E spec) k) ω₀), ω ∈ M := by
    filter_upwards [hS.2.2.2 k, hD1] with ω₀ hst hd1 hω₀
    obtain ⟨⟨c, θ⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω₀
    obtain ⟨b', jumps', h', hb', htr, hfl⟩ := hst c θ hl
    obtain ⟨hWk, hζk⟩ := hd1 c θ hl h' htr
    have hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      angle_walkSpec_mem (Exist.StagedLaw.eq_launch_of_launches spec _ hl).1
    exact ae_mem_pieceVisitEvent hGB6 hGW0 hT13 hκ hκ4 hθ hb' hfl
      (Eventually.of_forall fun ω => (hreg spec k ω).2.2.2) hWk hζk (instrTime spec k)
  have hP := GW2Later.ae_of_ae_condExpKernel_on' (hS.2.1 k) hL hM hker
  filter_upwards [hP, hRs, hD2] with ω hPω hRω hD2ω c θ hl
  have hωM : ω ∈ M := hPω (show _ ≠ none by rw [hl]; exact Option.some_ne_none _)
  have hk := (Exist.StagedLaw.eq_launch_of_launches spec _ hl).1
  obtain ⟨hw0, hwc, η, hη, hηtr⟩ := hRω k θ (instrTime spec k) c hk hl
  obtain ⟨-, hWkc, hWk0, ⟨γ, hγ, hγtr⟩, -, -, hrange, hiff⟩ := hD2ω c θ hl
  have hregω : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps spec (fun j => E spec j ω) (j + 1)).2.2.2.1 j = some (c', θ') →
      GW1P.PieceRegular (E spec j ω).1 (min (instrTime spec j) (E spec j ω).2) := by
    intro j c' θ' hl'
    obtain ⟨a1, a2, a3, a4, a5⟩ :=
      hRω j θ' (instrTime spec j) c' (Exist.StagedLaw.eq_launch_of_launches spec _ hl').1 hl'
    exact ⟨a1, a2, a3, a4, a5⟩
  obtain ⟨f, C, hf, hC, hfib⟩ := hF κ b jumps spec (fun j => E spec j ω) hregω k c θ hl
  have hwlt : ContinuousOn (E spec k ω).1 {s | (s : ℝ≥0∞) < min (instrTime spec k) (E spec k ω).2} :=
    hwc.mono fun s (hs : (s : ℝ≥0∞) < _) => (le_of_lt hs : (s : ℝ≥0∞) ≤ _)
  have hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < min (instrTime spec k) (E spec k ω).2 →
      LP.traceAt (rt q) (E spec k ω).1 = η (rt q) := fun q hq =>
    LP.traceAt_eq_of_isGeneratingTrace hη hwlt hw0 hq
  have hγc : Continuous γ := by
    have hc' := hγ.2.1
    simp only [le_top, ofPred_true] at hc'
    exact continuousOn_univ.1 hc'
  have hG : ∀ r : ℚ, LP.traceAt (rt r) (fun s => Wk s ω) = γ (rt r) := fun r =>
    LP.traceAt_eq_of_isGeneratingTrace hγ hWkc.continuousOn hWk0 ENNReal.coe_lt_top
  have hinj := injOn_of_sepAt hη.2.1 hA hωM.1
  have hvis := visit_of_visAt hη.2.1 hη.1 hinj hγc hγtr hA hG hωM.2
  obtain ⟨hinj', havoid⟩ :=
    piece_simple_of_visit hf hfib hη hwc hw0 hγ hWkc hWk0 hvis hinj (notMem_of_clock hrange hiff)
  exact ⟨f, η, C, hf, hC, hw0, hwc, hη, hηtr, hinj', havoid⟩

end GW1Z

end Theorem14

end InteractingSLE
