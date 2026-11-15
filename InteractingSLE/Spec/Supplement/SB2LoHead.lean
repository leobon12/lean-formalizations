/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LoFut

/-!
# The actual prefix before the start lies on the head of every parametrization

Packet PROVE-SB2-LIFTSET (round 3). From the future part (`SB2LoFut`) and `subset_head_of_split`:

* **`subset_head_of_futPart`**: at the end of a done run, a preconnected prefix `P` holding `0` and the seed `q`, met
  by the future part only at `q`, lies on `β₀ '' [0, t_L]` as soon as `R = β₀ t_L` is in `P` only if it is the seed;
* **`head_of_arcStart`**: the `head` field of `ArcStart` — the connector at instruction `o + 1` moves right across `R`
  and clears the prefix (`WalkConnectorClearance`), so `R` is in the prefix only if it is the seed;
* **`head_of_pieceStart`**: the `head` field of `PieceStart` — the piece launched at instruction `o` passes through `R`
  and meets the prefix only at its seed (`PieceSimpleAt`).

Inputs: GW1's per-step facts for the actual walk (the hypotheses of `walkChainRepresentation_of_pieceSimpleAt`, a.s.
from `GW1Z.GW1PieceSimpleStatement`, `WalkTipCoordinatesStatement`, `WalkConnectorClearanceStatement`), the walk done
inside its program, and `β₀` a proper parametrization from `0` with `β₀ t_L = R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep GW1W

/-- **The prefix before a split lies on the head through `t_L`** (deterministic): the walk is done at the end with
physical part `P ∪ T` (`FutPart`), `β₀` is a proper parametrization from `0`, `P` is preconnected with the seed `q`,
and `R = β₀ t_L` is in `P` only if it is the seed. -/
theorem subset_head_of_futPart {β₀ : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β₀) (hβ0 : β₀ 0 = 0) {s : ExplState}
    (hβr : range β₀ = statePhysicalSet 0 s) {P : Set ℂ} {q : ℂ} (hF : FutPart P q s) (hd : stStatus s = stDone)
    (hPc : IsPreconnected P) (h0P : (0 : ℂ) ∈ P) (hqP : q ∈ P) {tL : ℝ≥0} {R : ℂ} (hβL : β₀ tL = R)
    (hR : R ∈ P → R = q) : P ⊆ β₀ '' Iic tL := by
  obtain ⟨T, hT, hTc, hqT, hTP, -, hunb⟩ := hF
  have hPr : P ⊆ range β₀ := by rw [hβr, hT]; exact subset_union_left
  have hTr : T ⊆ range β₀ := by rw [hβr, hT]; exact subset_union_right
  obtain ⟨ty, hty⟩ := hTr hqT
  have hsplit := subset_head_of_split hβ hPr hTr hTc (hunb hd) (hty ▸ hqT)
    (fun z hz => by rw [mem_singleton_iff, hty]; exact hTP z hz.2 hz.1)
  rcases le_or_gt ty tL with hle | hlt
  · exact hsplit.trans (image_mono (Iic_subset_Iic.2 hle))
  · exfalso
    have he := isClosedEmbedding_of_isProperCurve hβ
    have hI : IsPreconnected (β₀ ⁻¹' P) := by
      rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hPr]; exact hPc
    have h0I : (0 : ℝ≥0) ∈ β₀ ⁻¹' P := by show β₀ 0 ∈ P; rw [hβ0]; exact h0P
    have htyI : ty ∈ β₀ ⁻¹' P := by show β₀ ty ∈ P; rw [hty]; exact hqP
    have htL : tL ∈ β₀ ⁻¹' P := hI.Icc_subset h0I htyI ⟨zero_le, hlt.le⟩
    have hRq : β₀ tL = β₀ ty := by rw [hty, hβL]; exact hR (hβL ▸ htL)
    exact hlt.ne (hβ.2.1 hRq)


section Starts

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The head inclusion at an arc start**: GW1's per-step facts, the actual walk done inside its program, `β₀` a
proper parametrization from `0` visiting `R` at `t_L`, and the connector at instruction `o + 1` moving right across
`R`: the actual prefix before that connector lies on the head `β₀ '' [0, t_L]`. -/
theorem head_of_arcStart
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ true) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1))))
    (hC : GW1WalkChain.WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ true) D)
    {N o : ℕ} (hN : N ≤ (boundaryWalkSpec b jumps θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D N) = stDone)
    {β₀ : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0} {R : ℝ}
    (hβL : β₀ tL = R) (hoN : o + 1 ≤ N) (hn : o + 1 < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hodd : (o + 1) % 2 = 1)
    (hmove : ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) none
        true =
      if hC : (restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).Nonempty then
        ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true
          ((restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true)
    (hpt : stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) ≤ R)
    (hgap : ∀ x ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)), R < x) :
    statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) ⊆ β₀ '' Iic tL := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1) with hs
  have hstep : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1 + 1) =
      ExplState.contStep κ b jumps s none true := GW1W.run_succ_walk_cont hn hodd
  have hnd : stStatus s ≠ stDone := by
    intro hdn
    have e := GW1WalkChain.contStep_of_done (κ := κ) (b := b) (jumps := jumps) hdn none true
    rw [hmove] at e
    split_ifs at e with hCn
    · have := congrArg (fun t : ExplState => t.2.1.length) e
      simp only [moveAlong_arcs_true, List.length_append, List.length_singleton] at this
      omega
    · have := congrArg (fun t : ExplState => t.2.1.length) e
      simp only [moveToEnd_arcs_true, List.length_append, List.length_singleton] at this
      omega
  obtain ⟨hPc, hqP⟩ := prefix_facts hP hC (o + 1)
  have hF := futPart_run hP hC (futPart_start (hqP hnd) hnd) N hoN
  have hβr' : range β₀ = statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D N) := by
    rw [hβr, physSet_walk_eq_of_done hN hd]
  refine subset_head_of_futPart hβ hβ0 hβr' hF hd hPc (Or.inl (Or.inl rfl)) (hqP hnd) hβL (fun hRP => ?_)
  -- `R` lies on the connector, which meets the prefix only at its start
  by_cases hCn : (restartSet κ b jumps s).Nonempty
  · have he : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1 + 1) =
        ExplState.moveAlong s true ((restartSet κ b jumps s).min' hCn) true := by
      rw [hstep, hmove]; simp only [hCn, ↓reduceDIte]
    have hcl := (hC (o + 1)).1 true _ he
    exact hcl _ ⟨R, ⟨hpt, (hgap _ (Finset.min'_mem _ hCn)).le⟩, rfl⟩ hRP
  · have he : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1 + 1) = ExplState.moveToEnd s true := by
      rw [hstep, hmove]; simp only [hCn, ↓reduceDIte]
    have hcl := (hC (o + 1)).2 true he
    refine hcl _ ?_ hRP
    rw [GW1WalkChain.range_realRay]
    exact ⟨R, hpt, rfl⟩


/-- **The head inclusion at a piece start**: as `head_of_arcStart`, with the piece launched at instruction `o`
passing through `R` (piece simplicity: it meets the prefix only at its seed). -/
theorem head_of_pieceStart
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ true) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1))))
    (hC : GW1WalkChain.WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ true) D)
    {N o : ℕ} (hN : N ≤ (boundaryWalkSpec b jumps θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D N) = stDone)
    {β₀ : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0} {R : ℝ}
    (hβL : β₀ tL = R) (hoN : o ≤ N)
    (hlaunch : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1) =
      ExplState.launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o) o (D o) θ ⊤)
    (hRmem : (R : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o) (D o)).1.tipSet
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o) (D o)).2.1
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o) (D o)).2.2) :
    statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o) ⊆ β₀ '' Iic tL := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D o with hs
  have hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)).2.2.2.1 o = some (stChart s, θ) := by
    rw [hlaunch, launches_launch, Function.update_self]
  have hnd : stStatus s ≠ stDone := by
    intro hdn
    have e := Lx.run_eq_of_done (boundaryWalkSpec b jumps θ true) D hdn (o + 1) (Nat.le_succ o)
    rw [hlaunch] at e
    have h1 := congrArg (fun t : ExplState => t.1.length) e
    rw [launch_pieces, ← hs] at h1
    simp at h1
  obtain ⟨hPc, hqP⟩ := prefix_facts hP hC o
  have hF := futPart_run hP hC (futPart_start (hqP hnd) hnd) N hoN
  have hβr' : range β₀ = statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D N) := by
    rw [hβr, physSet_walk_eq_of_done hN hd]
  refine subset_head_of_futPart hβ hβ0 hβr' hF hd hPc (Or.inl (Or.inl rfl)) (hqP hnd) hβL (fun hRP => ?_)
  have hpiece := hP o (stChart s) θ hl (hqP hnd)
  rw [Lx.instrTime_boundaryWalk_of_launch hl] at hpiece
  have hmeet := GW1WalkChain.tipSet_inter_of_pieceSimpleAt hpiece
  have hR' : (R : ℂ) ∈ (stChart s).tipSet (fun r => (D o).1 (min (r : ℝ≥0∞) (min ⊤ (D o).2)).toNNReal)
      (min ⊤ (D o).2) ∩ statePhysicalSet 0 s := ⟨hRmem, hRP⟩
  rw [hmeet] at hR'
  exact hR'

end Starts

end InteractingSLE.Theorem14.SB.Lk
