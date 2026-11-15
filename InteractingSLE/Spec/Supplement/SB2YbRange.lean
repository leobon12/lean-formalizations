/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LuRange
import InteractingSLE.Spec.Supplement.SB2XzArc

/-!
# The relative physical set as the range of the lift curve, connector form

Packet PROVE-T14-SB2LIFT (round 31; decision D36): `physSet_eq_of_accCorrW`,
`range_eq_physSet_of_accCorrW`, `range_eq_physSet_start_arcW`, `range_eq_physSet_start_pieceW`.
The statements and proofs are those of the landed originals, with `tail` replaced by its connector form
`TailArc` (`SB2XzArc`, read only on connectors of the actual run); the full `tail` is false (handoff
§R29.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ}

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ}

variable {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- `physSet_eq_of_accCorr`, also recording that the connectors `X` of the history are connectors of the actual
run at stage `N + o`. -/
theorem physSet_eq_of_accCorrW {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {N o : ℕ} {L : Pc → Pc → Prop}
    {t₁ t₂ : ExplState} (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hc : AccCorr ι R L t₁ t₂ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N))
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone) :
    ∃ (X : List (Set ℝ)) (Y₁ Y₂ : List Pc), List.Forall₂ L Y₁ Y₂ ∧
      ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ =
        statePhysicalSet 0 t₁ ∪ (⋃ q ∈ Y₁, q.1.tipSet q.2.1 q.2.2) ∪ ⋃ a ∈ X, ((↑) : ℝ → ℂ) '' a ∧
      ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ =
        statePhysicalSet 0 t₂ ∪ (⋃ q ∈ Y₂, q.1.tipSet q.2.1 q.2.2) ∪
          ⋃ a ∈ X, ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) ∧
      ∀ a ∈ X, a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)).2.1 := by
  obtain ⟨hst, ⟨X, hX₁, hX₂⟩, Y₁, Y₂, hY₁, hY₂, hY⟩ := hc
  refine ⟨X, Y₁, Y₂, hY, ?_, ?_, fun a ha => by rw [hX₁]; exact List.mem_append_right _ ha⟩
  · rw [physSet_walk_eq_of_done hN₁ hd, statePhysicalSet_append hY₁ hX₁]
  · rw [physSet_walk_eq_of_done hN₂ (hst.2.1.trans hd), statePhysicalSet_append hY₂ hX₂]
    simp only [List.mem_map, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]

/-- **The relative physical set is the range of the lift curve** (deterministic): the correspondence with history
holds at actual stage `N + o` and relative stage `N`, with pieces paired by the lift relation, the actual walk is
done there, `β₀` is an injective parametrization of the actual walk visiting `R` at `t_L`, and the start parts
correspond (`hQ`, given that the actual start part lies on `β₀`). -/
theorem range_eq_physSet_of_accCorrW (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {N o : ℕ}
    {t₁ t₂ : ExplState} (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hc : AccCorr ι R (LiftRel β₀ tL γ) t₁ t₂ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N))
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : TailArc κ θ b₁ J₁ D₁ R β₀ tL)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hQ : statePhysicalSet 0 t₁ ⊆ range β₀ → liftImage β₀ tL γ (statePhysicalSet 0 t₁) = statePhysicalSet 0 t₂) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  obtain ⟨X, Y₁, Y₂, hY, hP₁, hP₂, hXa⟩ := physSet_eq_of_accCorrW hN₁ hN₂ hc hd
  have hsub : ∀ a ∈ X, ((↑) : ℝ → ℂ) '' a ⊆ range β₀ := fun a ha => by
    rw [hβr, hP₁]
    exact subset_union_of_subset_right (subset_biUnion_of_mem (u := fun a => ((↑) : ℝ → ℂ) '' a) ha) _
  have hQ' := hQ (by rw [hβr, hP₁]; exact subset_union_left.trans subset_union_left)
  refine range_eq_of_decomp hβr hP₁ hP₂ hY hQ' fun a ha => ?_
  exact liftImage_ofRealW hβ hβL hγ0 h.map_base hhead (htail.of_mem (hXa a ha)) hray
    fun x hx _ => hsub a ha ⟨x, hx, rfl⟩

/-- **SB2(2)'s physical sets, starting on an actual connector** (deterministic, one sample). The actual walk moves
right at its connector instruction `o + 1` (`o` even) from `pt ≤ R` across `R` (no restart mark in `(pt, R]`, low
outward height at `R`); the relative first piece has zero lifetime. From relative stage `2` (actual stage `o + 2`)
to `N` the lockstep data hold (`StepOK`, and at each launch the relative piece is the lift of the actual one), and
the actual walk is done at `N + o`. If `β₀` is an injective parametrization of the actual walk visiting `R` at
`t_L`, whose head has real points `≤ R` and tail real points `≥ R`, the actual prefix before the connector lies on
the head, and the lift curve `γ` reads the untouched ray through `ι`, then the relative walk's physical set is
`range γ`. -/
theorem range_eq_physSet_start_arcW (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}
    (ho : o % 2 = 0) (hn : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hmove : ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) none
        true =
      if hC : (restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).Nonempty then
        ExplState.moveAlong (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true
          ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true)
    (hθ : stAngle (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) = θ)
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≤ R)
    (hgap : ∀ x ∈ restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)), R < x)
    (hlow : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ) (hreg : IsRegularDriver (D₂ 0)) (h0 : (D₂ 0).2 = 0)
    (h2N : 2 ≤ N) (hlen : ∀ i, 2 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hstep : ∀ i, 2 ≤ i → i < N →
      StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι R (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : TailArc κ θ b₁ J₁ D₁ R β₀ tL)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ⊆
      β₀ '' Iic tL) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  obtain ⟨a, hRa, hc, hS₁, hS₂, haA⟩ := start_arc_physW h hn (by omega) hmove hθ hpt hrec hgap hlow hreg h0
  have e : 2 + o = o + 1 + 1 := by omega
  have h₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) := by rw [e]; exact hc
  have hacc := accCorr_run_of_steps (L := LiftRel β₀ tL γ) h le_rfl o 2 N ho hlen h₀ hstep N h2N le_rfl
  refine range_eq_physSet_of_accCorrW h hN₁ hN₂ hacc hd hβr hβ hβL hγ0 hhead htail hray fun hsub => ?_
  rw [e] at hsub ⊢
  rw [hS₁, hS₂]
  rw [hS₁] at hsub
  exact liftImage_start_arcW hβ hβL hγ0 h.map_base hhead (htail.of_mem haA) hray hP₀ hRa
    fun x hx _ => hsub (Or.inr ⟨x, hx, rfl⟩)

/-- **SB2(2)'s physical sets, starting on an actual piece** (deterministic, one sample). The actual flow instruction
`o` (even) launches the piece through `R` from a state with point and record `≤ R`; the relative walk launches its
first piece from the root, with the launch observables of `StepOK` and the lift relation (the relative first piece
is the lift of the actual one), and `R` is a physical point of the actual piece. From relative stage `1` (actual
stage `o + 1`) to `N` the lockstep data hold and the actual walk is done at `N + o`. With `β₀`, `γ` as in
`range_eq_physSet_start_arcW` (the actual prefix before the piece on the head), the relative walk's physical set is
`range γ`. -/
theorem range_eq_physSet_start_pieceW (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}
    (ho : o % 2 = 0)
    (hlaunch : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) =
      ExplState.launch (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) o (D₁ o) θ ⊤)
    (htip : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≠ .inr (.inl ()))
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R)
    (hT : (D₂ 0).2 = ⊤ ↔ (D₁ o).2 = ⊤) (h0 : (D₂ 0).2 = 0 ↔ (D₁ o).2 = 0)
    (hR : (∃ x : ℝ, 0 < x ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x) ↔
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) ⊤ (D₁ o) x)
    (hL₁ : ¬ ∃ x : ℝ, x < stRecL (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ∧
      lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) ⊤ (D₁ o) x)
    (hL₂ : ¬ ∃ x : ℝ, x < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x)
    (hrec' : (D₁ o).2 ≠ ⊤ → lRecR (ExplState.init 0) ⊤ (D₂ 0) =
      ι (max (lRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊤ (D₁ o)) R))
    (hlift₀ : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o))
      (newPc (ExplState.init 0) (D₂ 0)))
    (hRmem : (R : ℂ) ∈ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).1.tipSet
      (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.1
      (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.2)
    (h1N : 1 ≤ N) (hlen : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hstep : ∀ i, 1 ≤ i → i < N →
      StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι R (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : TailArc κ θ b₁ J₁ D₁ R β₀ tL)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊆ β₀ '' Iic tL) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  have hc := stCorr_start_piece (b₂ := b₂) (J₂ := J₂) (D₂ := D₂) h hlaunch htip hpt hrec hT h0 hR hL₁ hL₂ hrec'
  obtain ⟨hS₁, hS₂⟩ := start_piece_phys (b₂ := b₂) (J₂ := J₂) (D₂ := D₂) hlaunch
  have e : 1 + o = o + 1 := by omega
  have h₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (1 + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) := by rw [e]; exact hc
  have hacc := accCorr_run_of_steps (L := LiftRel β₀ tL γ) h le_rfl o 1 N ho hlen h₀ hstep N h1N le_rfl
  refine range_eq_physSet_of_accCorrW h hN₁ hN₂ hacc hd hβr hβ hβL hγ0 hhead htail hray fun _ => ?_
  rw [e, hS₁, hS₂]
  exact liftImage_start_piece hβ hγ0 hP₀ hlift₀ (by rw [hβL]; exact Or.inr hRmem)

end InteractingSLE.Theorem14.SB.Lk
