/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ParamProof
import InteractingSLE.Spec.Supplement.GW1ActiveRun
import InteractingSLE.Spec.Supplement.GW1Connector
import InteractingSLE.Spec.Supplement.GW1LaterR51
import InteractingSLE.Spec.Supplement.WalkProper

/-!
# Lemma GW1: boundary-walk bookkeeping and the per-piece interface

Packet PROVE-T14-GW1Y. The existing finite-chain constructor is in GW1ParamProof; this module records the
physical-set view of a run and the exact launch/connector transitions needed to feed it. It also declares the
per-piece simplicity and old-union avoidance statement for the following proof packet.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1Bookkeep

open Exist Exist.Staged Exist.StagedLaw GW1X

/-- The physical part of a state, including its original root. -/
def statePhysicalSet (x : ℝ) (s : ExplState) : Set ℂ :=
  {(x : ℂ)} ∪ (⋃ p ∈ s.1, p.1.tipSet p.2.1 p.2.2) ∪
    ⋃ a ∈ s.2.1, ((↑) : ℝ → ℂ) '' a

/-- The frozen completed-walk physical set is the state physical set of its terminal run. -/
theorem physSet_eq_statePhysicalSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b jumps spec D =
      statePhysicalSet spec.1 (ExplState.run κ b jumps spec D spec.2.2.length) := by
  rfl

section Walk

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool}
  {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- At a launched walk instruction, the new ordinary piece is appended in the launch chart, with its driver
stopped at the instruction time and the sampled lifetime. -/
theorem pieces_run_succ_of_launch {k : ℕ}
    (h : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).1 =
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k).1 ++
        [((ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k).2.2.2.2.1,
          fun r : ℝ≥0 => (D k).1 (min (r : ℝ≥0∞) (min ⊤ (D k).2)).toNNReal,
          min ⊤ (D k).2)] := by
  rw [GW1W.launch_walk h, CounterflowRange.pieces_launch]

/-- A real connector recorded by moveAlong is appended after the old connectors, with its endpoints given by the
state's current point and the target mark. -/
theorem arcs_moveAlong_append (s : ExplState) (right : Bool) (x : ℝ) (atMark : Bool) :
    (ExplState.moveAlong s right x atMark).2.1 =
      s.2.1 ++ [if right then Icc (stPt s) x else Icc x (stPt s)] := by
  exact arcs_moveAlong s right x atMark

/-- The terminal boundary ray is appended after the existing connectors, from the current physical point. -/
theorem arcs_moveToEnd_append (s : ExplState) (right : Bool) :
    (ExplState.moveToEnd s right).2.1 =
      s.2.1 ++ [if right then Ici (stPt s) else Iic (stPt s)] := by
  exact arcs_moveToEnd s right

end Walk

/-- A physical ordinary piece in a launch chart is simple and meets the already explored physical set only at its
seed. The trace and boundary extension witnesses also identify the parametrized start and the full tip set. -/
def PieceSimpleAt (c : Chart) (W : ℝ≥0 → ℝ) (S : ℝ≥0∞) (old : Set ℂ)
    (q₀ q₁ : ℝ) : Prop :=
  ∃ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ) (C : ℝ),
    (∀ p ∈ QuantumZipper.Hbar, Tendsto c.2.1 (𝓝[QuantumZipper.H] p) (𝓝 (f p))) ∧
    (∀ p ∈ QuantumZipper.Hbar, ‖f p - p‖ ≤ C) ∧
    (∀ p ∈ QuantumZipper.Hbar, f p ∈ QuantumZipper.Hbar) ∧
    W 0 = 0 ∧
    ContinuousOn W {t | (t : ℝ≥0∞) ≤ S} ∧
    IsGeneratingTrace W S α ∧
    (S = ⊤ → Tendsto (fun t => ‖α t‖) atTop atTop) ∧
    Set.InjOn (fun t : ℝ≥0 => f (α t)) {t | (t : ℝ≥0∞) ≤ S} ∧
    f (α 0) = (q₀ : ℂ) ∧
    (S ≠ ⊤ → f (α S.toNNReal) = (q₁ : ℂ)) ∧
    c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ∩ old = {f (α 0)}

/-- A finite positive piece satisfying `PieceSimpleAt` can be parametrized as an arc on `[0,1]`; its image is the
piece tip set and its only point in the old physical set is its initial endpoint. -/
theorem exists_isArc_of_pieceSimpleAt {c : Chart} {W : ℝ≥0 → ℝ} {T : ℝ≥0} {old : Set ℂ}
    {q₀ q₁ : ℝ} (hT : 0 < T) (h : PieceSimpleAt c W (T : ℝ≥0∞) old q₀ q₁) :
    ∃ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ) (γ : ℝ≥0 → ℂ),
      GW1X.IsArc γ ∧
      γ '' Iic 1 = c.tipSet
        (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) (T : ℝ≥0∞)).toNNReal) (T : ℝ≥0∞) ∧
      (∀ s ∈ Iic 1, γ s ∈ QuantumZipper.Hbar) ∧
      γ 0 = f (α 0) ∧ γ 1 = f (α T) ∧ γ 0 = (q₀ : ℂ) ∧
      γ 1 = (q₁ : ℂ) ∧
      γ 0 ∈ old ∧
      γ '' Iic 1 ∩ old = {γ 0} := by
  obtain ⟨f, α, C, hf, hC, hmaps, hW0, hWc, hgen, htrans, hinj, hStart, hEnd, havoid⟩ := h
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (T : ℝ≥0∞)} = Iic T := by
    ext t
    simp only [mem_setOf_eq, mem_Iic, ENNReal.coe_le_coe]
  have hinj' : Set.InjOn (f ∘ α) (Iic T) := by
    intro s hs t ht hst
    exact hinj (hset ▸ hs) (hset ▸ ht) hst
  obtain ⟨hArc, hImage, h0, h1⟩ :=
    GW1X.exists_isArc_tipSet hf hT hgen hWc hW0 hinj'
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (T : ℝ≥0∞) → α t ∈ QuantumZipper.Hbar := by
    intro t ht
    exact Sec7.IsGeneratingTrace.mem_Hbar hgen
      (hWc.mono fun t hs => Set.mem_setOf_eq.mpr (le_of_lt hs)) hW0 ht
  have hγH : ∀ s ∈ Iic (1 : ℝ≥0), GW1X.rescale (f ∘ α) T s ∈ QuantumZipper.Hbar := by
    intro s hs
    have ht : min s 1 * T ∈ Iic T :=
      Set.mem_Iic.2 (mul_le_of_le_one_left (zero_le (a := T)) (min_le_right s 1))
    change f (α (min s 1 * T)) ∈ QuantumZipper.Hbar
    exact hmaps _ (hαH _ (ENNReal.coe_le_coe.2 ht))
  refine ⟨f, α, GW1X.rescale (f ∘ α) T, hArc, hImage, hγH, h0, h1, ?_, ?_, ?_, ?_⟩
  · exact h0.trans hStart
  · have hEnd' : f (α T) = (q₁ : ℂ) := by simpa using hEnd (by simp)
    exact h1.trans hEnd'
  · have hseed : f (α 0) ∈ old := by
      have hm : f (α 0) ∈
          c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) (T : ℝ≥0∞)).toNNReal)
            (T : ℝ≥0∞) ∩ old := by
        rw [havoid]
        simp
      exact hm.2
    rw [h0]
    exact hseed
  · rw [hImage, havoid, h0]

/-- An infinite piece satisfying `PieceSimpleAt` is itself a proper simple curve; its range is the tip set.
The bounded-displacement clause on the boundary extension transfers transience of the generating trace to the
physical curve. -/
theorem exists_isProperCurve_of_pieceSimpleAt {c : Chart} {W : ℝ≥0 → ℝ} {old : Set ℂ}
    {q₀ q₁ : ℝ} (h : PieceSimpleAt c W ⊤ old q₀ q₁) :
    ∃ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ) (γ : ℝ≥0 → ℂ),
      Supp9B.IsProperCurve γ ∧ γ 0 = f (α 0) ∧ γ 0 = (q₀ : ℂ) ∧ γ 0 ∈ old ∧
      range γ = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) ⊤).toNNReal) ⊤ := by
  obtain ⟨f, α, C, hf, hC, hmaps, hW0, hWc, hgen, htrans, hinj, hStart, -, havoid⟩ := h
  have htime : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (⊤ : ℝ≥0∞)} = univ := by
    ext t
    simp
  have hWc' : ContinuousOn W univ := htime ▸ hWc
  have hαc : Continuous α := continuousOn_univ.1 (htime ▸ hgen.2.1)
  have hαH : ∀ t : ℝ≥0, α t ∈ QuantumZipper.Hbar := fun t =>
    Sec7.IsGeneratingTrace.mem_Hbar hgen
      (hWc.mono fun t hs => Set.mem_setOf_eq.mpr (le_of_lt hs)) hW0 le_top
  have hfcont : ContinuousOn f QuantumZipper.Hbar := GW1P.continuousOn_of_tendsto hf
  let γ : ℝ≥0 → ℂ := fun t => f (α t)
  have hγc : Continuous γ := continuousOn_univ.1
    (hfcont.comp hαc.continuousOn fun t _ => hαH t)
  have hγinj : Function.Injective γ := by
    intro s t hst
    exact hinj (htime.symm ▸ Set.mem_univ s) (htime.symm ▸ Set.mem_univ t) hst
  have hγH : ∀ t, γ t ∈ QuantumZipper.Hbar := fun t => hmaps _ (hαH t)
  have hγtr : Tendsto (fun t : ℝ≥0 => ‖γ t‖) atTop atTop := by
    apply tendsto_atTop.2
    intro R
    obtain ⟨T, hT⟩ := eventually_atTop.1 ((htrans rfl).eventually_ge_atTop (R + C))
    filter_upwards [eventually_atTop.2 ⟨T, fun t ht => hT t ht⟩] with t ht
    have hlarge : R + C ≤ ‖α t‖ := ht
    have hdist : ‖α t‖ - ‖γ t‖ ≤ C := by
      calc
        ‖α t‖ - ‖γ t‖ ≤ ‖α t - γ t‖ := norm_sub_norm_le _ _
        _ = ‖f (α t) - α t‖ := by simp [γ, norm_sub_rev]
        _ ≤ C := hC _ (hαH t)
    change R ≤ ‖γ t‖
    linarith
  have hseedOld : f (α 0) ∈ old := by
    have hm : f (α 0) ∈
        c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) ⊤).toNNReal) ⊤ ∩ old := by
      rw [havoid]
      simp
    exact hm.2
  have htip : c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) ⊤).toNNReal) ⊤ =
      f '' (α '' univ) := by
    calc
      _ = f '' (α '' {t | (t : ℝ≥0∞) ≤ (⊤ : ℝ≥0∞)}) :=
        CounterflowRange.tipSet_stopped_eq_of_tendsto hgen hWc hW0 fun t _ => hf _ (hαH t)
      _ = f '' (α '' univ) := by rw [htime]
  refine ⟨f, α, γ, ⟨hγc, hγinj, hγH, hγtr⟩, rfl, hStart, hseedOld, ?_⟩
  rw [htip]
  change Set.range (fun t : ℝ≥0 => f (α t)) = f '' (α '' univ)
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨α t, ⟨t, Set.mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨t, -, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

/-- Exact terminal-state representation needed to apply the finite-chain constructor to a walk. This records the
remaining bookkeeping goal explicitly: the interleaved finite pieces and connectors must form `L`, and `ρ` must be
the final proper piece or boundary ray. -/
def WalkChainRepresentation (x : ℝ) (s : ExplState) : Prop :=
  ∃ (L : List (ℝ≥0 → ℂ)) (ρ : ℝ≥0 → ℂ),
    Supp9B.IsProperCurve ρ ∧ GW1X.ChainOK L ρ ∧
    GW1X.chainStart L ρ = (x : ℂ) ∧ GW1X.chainSet L ρ = statePhysicalSet x s

/-- The named chain-representation condition supplies the walk's proper parametrization by the existing
finite-chain theorem. -/
theorem exists_isProperCurve_of_walkChainRepresentation {x : ℝ} {s : ExplState}
    (h : WalkChainRepresentation x s) :
    ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = (x : ℂ) ∧
      range γ = statePhysicalSet x s := by
  obtain ⟨L, ρ, hρ, hChain, hStart, hSet⟩ := h
  obtain ⟨γ, hγ, hγ0, hγR⟩ := GW1X.exists_isProperCurve_of_chainOK hρ hChain
  exact ⟨γ, hγ, hγ0.trans hStart, hγR.trans hSet⟩

/-- GW1's per-piece simplicity statement (right walk and its left mirror): for every launched ordinary piece,
its physical trace is simple and intersects the entire old walk only at the seed. The statement includes the
regular trace and its boundary extension so later reducers can use the same witnesses to form finite arcs or the
terminal proper ray. -/
def GW1PieceSimpleStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hfield : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P hfield b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P hfield W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P hfield spec (E spec)) →
      (∀ spec k ω, Staged.IsRegularDriver (E spec k ω)) →
      ∀ right : Bool,
        let θ := if right then -(Real.pi / 2) else Real.pi / 2
        let spec := boundaryWalkSpec b jumps θ right
        ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ c : Chart, ∀ θ' : ℝ,
          (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.1 k = some (c, θ') →
          PieceSimpleAt c (E spec k ω).1 (min (instrTime spec k) (E spec k ω).2)
            (statePhysicalSet spec.1 (ExplState.run κ b jumps spec (fun j => E spec j ω) k))
            (ExplState.run κ b jumps spec (fun j => E spec j ω) k).2.2.2.2.2.2.1
            (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.2.2.2.1

end InteractingSLE.Theorem14.GW1Bookkeep
