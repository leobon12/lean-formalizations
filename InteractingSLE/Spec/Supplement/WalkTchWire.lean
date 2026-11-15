/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkTchMatchL
import InteractingSLE.Spec.Supplement.WalkWdClosedWire
import InteractingSLE.Spec.Supplement.WalkWdActive

/-!
# `WalkTouchMatchStatement` and Theorem 1.4's walk chart `hNL`

Packet PROVE-WALK-TOUCH. **`walkTouchMatchStatement_of_inputs`** proves PROVE-WALK-WORDS2's named input
`WalkWd.WalkTouchMatchStatement` (the controlled prefix matches at the real touch points of the pieces) from Theorem 1.3
(both universes) and the five GW3 inputs `hPR hPL hA hF hNR` — the same inputs as the rest of `hNL`. Consequently
**`walkNormChartLocStatement_of_inputs`** gives the binder `hNL` of `Wire.theorem14Statement_assembled2` from Theorem
1.3 and the five GW3 inputs alone.

Per sample (after PROVE-WALK-WORDS2's `walkFiniteMatchOnLiveStatement_of_inputs`): the walls are proper simple curves
`α`, `β` from `0` (`hPR`, `hPL`), the pocket shape and the landings (`WalkWd.pocket_landing_facts`) give that a
landing on the right walk avoids the left walk and, for a bounded component, precedes the closing contact. The
activeness of the component for every prefix stopped before a fresh point of the walk inside the open set
`α([0, U))` (`exists_dom_window_right`: `WalkWd.subset_H_diff_fillH_raw_of_bounded/_unbounded`, the raw initial
segments of PROVE-T14-WALKINT) is the domain input of `exists_controlledMatch_right_touch`; mirror for the left walk.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkTch

open Exist WalkBdry WalkMean WalkNorm WalkInf WalkWords WalkIntFill WalkIntFiber WalkIntActive WalkWd
open GW1WalkFinish GW1WalkChain

/-! ### The domain windows (deterministic) -/

section Dom

variable {specR specL : ExplSpec} {sR sL : ExplState} {α β : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {p : ℂ}

/-- **The domain window of a right-walk landing**: an open set `U₀ ∋ p` such that the component chart maps `ℍ` into
the domain of every prefix of the right walk stopped before a fresh walk point inside `U₀`. -/
theorem exists_dom_window_right (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (hrR : range α = physOf specR sR) (hrL : range β = physOf specL sL)
    (hco : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hC : C ∈ betweenComponents (physOf specR sR) (physOf specL sL)) (hCo : IsOpen C)
    (hcC : MapsTo c.2.1 H C) (hpα : p ∈ range α)
    (hmk : ∀ (pre post : List Piece) (pc : Piece), sR.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sR, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hraw : ∀ R : WalkPrefix sR, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H)
    (hexit : Bornology.IsBounded C → ∃ U V : ℝ≥0, α U = β V ∧ α U ∈ closure C ∧
      ∀ r : ℝ≥0, α r = p → r < U) :
    ∃ U₀ : Set ℂ, IsOpen U₀ ∧ p ∈ U₀ ∧ ∀ (pre post : List Piece) (pc : Piece) (τ : ℝ≥0),
      sR.1 = pre ++ pc :: post → (τ : ℝ≥0∞) < pc.2.2 →
      (∃ z ∈ U₀, z ∈ wsetOf sR ∧ z ∉ prefixSet pre pc τ) → ∀ w ∈ H, c.2.1 w ∈ (prefixChart pc τ).dom := by
  have hwR : wsetOf sR ⊆ range α := fun z hz => hrR ▸ Or.inl (Or.inr hz.1)
  have hC' : C ∈ betweenComponents (range α) (range β) := by rw [hrR, hrL]; exact hC
  by_cases hb : Bornology.IsBounded C
  · obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
    obtain ⟨rp, hrp⟩ := hpα
    obtain ⟨O, hO, hOe⟩ := exists_isOpen_preimage_Iio hα U
    have hpO : p ∈ O := by
      have : rp ∈ α ⁻¹' O := by rw [hOe]; exact hlt rp hrp
      rw [← hrp]; exact this
    have hU0 : 0 < U := lt_of_le_of_lt zero_le (hlt rp hrp)
    have hV0 : 0 < V := by
      refine pos_iff_ne_zero.2 fun hV => hU0.ne' (hα.2.1 ?_)
      rw [hUV, hV, hβ0, hα0]
    refine ⟨O, hO, hpO, fun pre post pc τ hs hτ hz => ?_⟩
    obtain ⟨z, hzO, hzw, hzn⟩ := hz
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    set R : WalkPrefix sR := ⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩ with hRdef
    obtain ⟨a, ha⟩ := hraw R
    obtain ⟨u, rfl⟩ := hwR hzw
    have huU : u < U := by
      have : u ∈ α ⁻¹' O := hzO
      rw [hOe] at this; exact this
    have hau : a < u := by
      refine lt_of_not_ge fun hle => hzn ?_
      have hmem : α u ∈ α '' Icc 0 a ∩ H := ⟨⟨u, ⟨zero_le, hle⟩, rfl⟩, hzw.2⟩
      rw [← ha] at hmem
      exact hmem
    have hsub : C ⊆ H \ fillH R.raw := subset_H_diff_fillH_raw_of_bounded R hα hβ hco hC'
      (by rw [ha]; exact inter_subset_left) (hau.trans huU) hV0 hUV hUC
    exact mem_prefix_dom_of_subset R hsub hcC
  · refine ⟨univ, isOpen_univ, mem_univ p, fun pre post pc τ hs hτ _ => ?_⟩
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    set R : WalkPrefix sR := ⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩ with hRdef
    refine mem_prefix_dom_of_subset R (subset_H_diff_fillH_raw_of_unbounded R hC hCo hb ?_) hcC
    exact fun z hz => Or.inl (hrR ▸ hwR (R.raw_subset hz))

/-- **The domain window of a left-walk landing** (mirror). -/
theorem exists_dom_window_left (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (hrR : range α = physOf specR sR) (hrL : range β = physOf specL sL)
    (hco : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hC : C ∈ betweenComponents (physOf specR sR) (physOf specL sL)) (hCo : IsOpen C)
    (hcC : MapsTo c.2.1 H C) (hpβ : p ∈ range β)
    (hmk : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sL, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hraw : ∀ R : WalkPrefix sL, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H)
    (hexit : Bornology.IsBounded C → ∃ U V : ℝ≥0, α U = β V ∧ α U ∈ closure C ∧
      ∀ r : ℝ≥0, β r = p → r < V) :
    ∃ U₀ : Set ℂ, IsOpen U₀ ∧ p ∈ U₀ ∧ ∀ (pre post : List Piece) (pc : Piece) (τ : ℝ≥0),
      sL.1 = pre ++ pc :: post → (τ : ℝ≥0∞) < pc.2.2 →
      (∃ z ∈ U₀, z ∈ wsetOf sL ∧ z ∉ prefixSet pre pc τ) → ∀ w ∈ H, c.2.1 w ∈ (prefixChart pc τ).dom := by
  have hwL : wsetOf sL ⊆ range β := fun z hz => hrL ▸ Or.inl (Or.inr hz.1)
  have hC' : C ∈ betweenComponents (range α) (range β) := by rw [hrR, hrL]; exact hC
  by_cases hb : Bornology.IsBounded C
  · obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
    obtain ⟨rp, hrp⟩ := hpβ
    obtain ⟨O, hO, hOe⟩ := exists_isOpen_preimage_Iio hβ V
    have hpO : p ∈ O := by
      have : rp ∈ β ⁻¹' O := by rw [hOe]; exact hlt rp hrp
      rw [← hrp]; exact this
    have hV0 : 0 < V := lt_of_le_of_lt zero_le (hlt rp hrp)
    have hU0 : 0 < U := by
      refine pos_iff_ne_zero.2 fun hU => hV0.ne' (hβ.2.1 ?_)
      rw [← hUV, hU, hα0, hβ0]
    refine ⟨O, hO, hpO, fun pre post pc τ hs hτ hz => ?_⟩
    obtain ⟨z, hzO, hzw, hzn⟩ := hz
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    set R : WalkPrefix sL := ⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩ with hRdef
    obtain ⟨a, ha⟩ := hraw R
    obtain ⟨v, rfl⟩ := hwL hzw
    have hvV : v < V := by
      have : v ∈ β ⁻¹' O := hzO
      rw [hOe] at this; exact this
    have hav : a < v := by
      refine lt_of_not_ge fun hle => hzn ?_
      have hmem : β v ∈ β '' Icc 0 a ∩ H := ⟨⟨v, ⟨zero_le, hle⟩, rfl⟩, hzw.2⟩
      rw [← ha] at hmem
      exact hmem
    have hsub : C ⊆ H \ fillH R.raw := active_of_later_common_contact hα hβ hco hC' (a := 0) (b := a)
      (by rw [ha]; exact inter_subset_left.trans subset_union_right) hU0 (hav.trans hvV) hUV hUC
    exact mem_prefix_dom_of_subset R hsub hcC
  · refine ⟨univ, isOpen_univ, mem_univ p, fun pre post pc τ hs hτ _ => ?_⟩
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    set R : WalkPrefix sL := ⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩ with hRdef
    refine mem_prefix_dom_of_subset R (subset_H_diff_fillH_raw_of_unbounded R hC hCo hb ?_) hcC
    exact fun z hz => Or.inr (hrL ▸ hwL (R.raw_subset hz))

end Dom

/-! ### The almost-sure statement -/

/-- **`WalkTouchMatchStatement`** from Theorem 1.3 and the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks` (see the module docstring). -/
theorem walkTouchMatchStatement_of_inputs (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hA : GW2aContainmentStatement.{u}) (hF : SB.SBFrontierRegStatement.{u})
    (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) : WalkTouchMatchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hpi := Real.pi_pos
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 hT13 hT13₀
  have hTip := walkTipCoordinatesStatement_of_d4 hT13 hD4
  have hClear := walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 hT13₀) hD4
  filter_upwards [hfacts, hRR, hRL, hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true),
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false),
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    walkComponentOrientationStatement_of_theorem13 hT13 hT13₀ hPR hPL hA hF hNR κ hκ hκ4 b jumps hb P h hh W' ζ'
      hcf hζ' E hE hR hreg hfacts,
    hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR]
    with ω hf hωR hωL hS hAR hAL hTipR hTipL hClR hClL hor hαω hβω
  obtain ⟨α, hα, hα0, hrR⟩ := hαω
  obtain ⟨β, hβ, hβ0, hrL⟩ := hβω
  replace hrR : range α = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 := hrR
  replace hrL : range β = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 := hrL
  intro C hC c hc
  have hfα : GB11.IsCompleteSimpleFlow α := ⟨hα.1, hα.2.1, hα0, fun t => hα.2.2.1 t, hα.2.2.2⟩
  have hfβ : GB11.IsCompleteSimpleFlow β := ⟨hβ.1, hβ.2.1, hβ0, fun t => hβ.2.2.1 t, hβ.2.2.2⟩
  have hco := hf.1.2.2 α β hrR hrL hfα hfβ
  -- the pocket shape of the two walls
  have hno : ∀ a b' : ℝ≥0, a < b' → ¬ α '' Icc a b' ⊆ range β := by
    intro a b' hab hsub
    have hS' : α '' Icc a b' ⊆ physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 ∩
        physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 :=
      fun z hz => ⟨hrR ▸ image_subset_range _ _ hz, hrL ▸ hsub hz⟩
    have hsing := hf.2.2.1 _ hS' (isPreconnected_Icc.image _ hfα.1.continuousOn)
    have he := hsing ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩ ⟨b', ⟨hab.le, le_rfl⟩, rfl⟩
    exact absurd (hfα.2.1 he) hab.ne
  have hdL : Disjoint (range β) (rightSideOf (range α)) := by
    rw [hrR, hrL, Set.disjoint_left]
    intro z hzL hzR
    exact eq_empty_iff_forall_notMem.1 hS.1 z ⟨hAL hzL, hzR⟩
  have hdR : Disjoint (range α) (leftSideOf (range β)) := by
    rw [hrR, hrL, Set.disjoint_left]
    intro z hzR hzL
    exact eq_empty_iff_forall_notMem.1 hS.2 z ⟨hAR hzR, hzL⟩
  have hgeo : ∀ C' ∈ betweenComponents (range α) (range β),
      GW3.IsTwoArcJordanComponent (range α) (range β) C' ∨ GW3.HasOrientedUniformizer (range α) (range β) C' := by
    rw [hrR, hrL]; exact hf.2.2.2
  have hW := PocketMirror.pocketShapeDetStatement α β hfα hfβ hco hno hdL hdR hgeo
  have hC' : C ∈ betweenComponents (range α) (range β) := by rw [hrR, hrL]; exact hC
  have hc' : IsComponentChart (range α) (range β) C c := by rw [hrR, hrL]; exact hc
  obtain ⟨hnot, hexit⟩ := pocket_landing_facts hfα hfβ hco hW hC' hc'
  have hαc : IsClosed (range α) := GW4Reg.isClosed_range_of_isCompleteSimpleFlow hfα
  have hβc : IsClosed (range β) := GW4Reg.isClosed_range_of_isCompleteSimpleFlow hfβ
  have hwR : wsetOf (walkRuns κ b jumps E ω).1 ⊆ range α := fun z hz => hrR ▸ Or.inl (Or.inr hz.1)
  have hwL : wsetOf (walkRuns κ b jumps E ω).2 ⊆ range β := fun z hz => hrL ▸ Or.inl (Or.inr hz.1)
  have hoR : ordOf (walkRuns κ b jumps E ω).1 ⊆ range α := fun z hz => hrR ▸ Or.inl (Or.inr hz)
  have hoL : ordOf (walkRuns κ b jumps E ω).2 ⊆ range β := fun z hz => hrL ▸ Or.inl (Or.inr hz)
  -- the component chart
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  have hcc : c.IsConformal := GW3Law.isConformal_of_isComponentChart hc hCoH.1 hCoH.2
  have hcC : MapsTo c.2.1 H C := hc.2.2.1
  have hland := hc.2.2.2.2.1
  obtain ⟨horR, horL⟩ := hor C hC c hc
  -- the runs
  have hregR := fun k c θ hl => pieceRegular_of_event hωR k c θ hl
  have hregL := fun k c θ hl => pieceRegular_of_event hωL k c θ hl
  have hDR : ∀ k, Exist.Staged.IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) :=
    fun k => hreg _ k ω
  have hDL : ∀ k, Exist.Staged.IsRegularDriver (E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) :=
    fun k => hreg _ k ω
  have hdR' := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR
      (fun k c θ hl => hf.2.1 true k c θ hl) hs
  have hdL' := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL
      (fun k c θ hl => hf.2.1 false k c θ hl) hs
  have hfR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (-(Real.pi / 2)) true
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR hDR hs h0
  have hfL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (Real.pi / 2) false
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL hDL hs h0
  have hjR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntBridge.prefixChart_disjoint_prefixSet (-(Real.pi / 2)) true
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR hDR hs h0
  have hjL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntBridge.prefixChart_disjoint_prefixSet (Real.pi / 2) false
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL hDL hs h0
  have ht0R : ∀ pc ∈ (walkRuns κ b jumps E ω).1.1, ∀ z, pc.1.tipAt pc.2.1 0 z → z.im = 0 :=
    fun pc hpc z hz => im_eq_zero_of_tipAt_zero hTipR hpc hz
  have ht0L : ∀ pc ∈ (walkRuns κ b jumps E ω).2.1, ∀ z, pc.1.tipAt pc.2.1 0 z → z.im = 0 :=
    fun pc hpc z hz => im_eq_zero_of_tipAt_zero hTipL hpc hz
  have hmkR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post) (τ : ℝ≥0)
      (hτ : (τ : ℝ≥0∞) < pc.2.2) => exists_walkPrefix (-(Real.pi / 2)) true _ hregR hDR hs hτ
  have hmkL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post) (τ : ℝ≥0)
      (hτ : (τ : ℝ≥0∞) < pc.2.2) => exists_walkPrefix (Real.pi / 2) false _ hregL hDL hs hτ
  have hrawR : ∀ R : WalkPrefix (walkRuns κ b jumps E ω).1, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H := fun R =>
    WalkIntRunChron.exists_raw_initial_segment_of_run
      (fun k c θ' hl hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ (hf.2.1 true) hTipR hl hseed)
      hClR hα hα0 hrR hDR R
  have hrawL : ∀ R : WalkPrefix (walkRuns κ b jumps E ω).2, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H := fun R =>
    WalkIntRunChron.exists_raw_initial_segment_of_run
      (fun k c θ' hl hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ (hf.2.1 false) hTipL hl hseed)
      hClL hβ hβ0 hrL hDL R
  refine ⟨fun x p hx hp him hpo hpE => ?_, fun x p hx hp him hpo hpE => ?_⟩
  · -- the right walk
    have hpα : p ∈ range α := hoR hpo
    have hpL : p ∉ closure (wsetOf (walkRuns κ b jumps E ω).2) := fun h =>
      (hnot x p hp).1 hx (closure_minimal hwL hβc h)
    obtain ⟨U₀, hU₀, hpU₀, hdomR⟩ := exists_dom_window_right hα hβ hα0 hβ0 hrR hrL hco hC hCoH.1 hcC hpα
      hmkR hrawR fun hb => by
        obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
        exact ⟨U, V, hUV, hUC, (hlt x p hp).1⟩
    exact fun U hU hpU => exists_controlledMatch_right_touch hα hoR hdR' hfR hjR ht0R hcc
      (fun x' hx' => by
        obtain ⟨z, hz, hzR, -⟩ := hland x'
        exact ⟨z, hz, hrR ▸ hzR hx'⟩) hx hp him hU hpU hpo hpE hpL horR hU₀ hpU₀ hdomR
  · -- the left walk
    have hpβ : p ∈ range β := hoL hpo
    have hpR : p ∉ closure (wsetOf (walkRuns κ b jumps E ω).1) := fun h =>
      (hnot x p hp).2 hx (closure_minimal hwR hαc h)
    obtain ⟨U₀, hU₀, hpU₀, hdomL⟩ := exists_dom_window_left hα hβ hα0 hβ0 hrR hrL hco hC hCoH.1 hcC hpβ
      hmkL hrawL fun hb => by
        obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
        exact ⟨U, V, hUV, hUC, (hlt x p hp).2⟩
    exact fun U hU hpU => exists_controlledMatch_left_touch hβ hoL hdL' hfL hjL ht0L hcc
      (fun x' hx' => by
        obtain ⟨z, hz, -, hzL⟩ := hland x'
        exact ⟨z, hz, hrL ▸ hzL hx'⟩) hx hp him hU hpU hpo hpE hpR horL hU₀ hpU₀ hdomL

/-- **Theorem 1.4's walk chart `hNL`** (`WalkNorm.WalkNormChartLocStatement`, the binder `hNL` of
`Wire.theorem14Statement_assembled2`) from Theorem 1.3 and the five GW3 inputs alone. -/
theorem walkNormChartLocStatement_of_inputs (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hA : GW2aContainmentStatement.{u}) (hF : SB.SBFrontierRegStatement.{u})
    (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) : WalkNormChartLocStatement.{u} :=
  WalkWd.walkNormChartLocStatement_of_inputs hT13 hT13₀ hPR hPL hA hF hNR
    (walkTouchMatchStatement_of_inputs hT13 hT13₀ hPR hPL hA hF hNR)

end InteractingSLE.Theorem14.WalkTch
