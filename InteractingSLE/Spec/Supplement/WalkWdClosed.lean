/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWdCore
import InteractingSLE.Spec.Supplement.WalkIntClosedRetained
import InteractingSLE.Spec.Supplement.WalkIntEnvelopeRetained
import InteractingSLE.Spec.Supplement.WalkIntBoundCutRun

/-!
# Closed pairs for the finite-word matches (ruling R92: no live piece needed)

Packet PROVE-WALK-WORDS2, round 3. `hMatch` with a `RetainedPair` (a live prefix of **each** walk) fails when one walk
has no live recorded piece (ruling R92). Here the matches are packaged with a `WalkIntClosed.ClosedPair` (closed-time
prefixes, `time ≤ stop`), which always exists:

* `ClosedTailSep J C α β`: the tail-separation exit data of a closed pair (the form PROVE-T14-WALKINT's admissible
  closed family consumes); `IsRealGap`: the real-collar data of a real match, with no reference pair;
* **`exists_closedPrefix_raw_eq_empty`**: every boundary-walk run has a closed prefix with empty raw set — its root
  piece
  (always recorded) at own time `0`, which starts at the real point `0`;
* **`exists_closedPair_right` / `_left`**: a controlled prefix match on one walk and an empty closed prefix of the other
  give a `ClosedPair` with the match and, for a bounded component, `ClosedTailSep`;
* **`finite_matches_closed_of_sample`**: the per-sample matches in the closed form, with no live-piece assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkWd

open WalkBdry WalkMean WalkNorm WalkWords WalkIntFill WalkIntActive WalkIntClosed Exist.StagedLaw

/-- **Tail separation of a closed pair** before a later common contact in the closure of `C`. -/
def ClosedTailSep {sR sL : ExplState} (J : ClosedPair sR sL) (C : Set ℂ) (α β : ℝ≥0 → ℂ) : Prop :=
  ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧ α s = β t ∧ Disjoint (closure J.right.raw) (α '' Ici s) ∧
    Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure C

/-- **The real-collar data of a real match** (no reference pair). -/
def IsRealGap (sR sL : ExplState) (b : ℝ → ℝ) (jumps : Finset ℝ) (c : Chart) (x bx : ℝ) : Prop :=
  ∃ a r : ℝ, a ∉ (jumps : Set ℝ) ∧ 0 < r ∧ Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ)) ∧
    Disjoint (ball (a : ℂ) r) (wsetOf sR ∪ wsetOf sL) ∧ bx = b a

/-- **A closed prefix with empty raw set**: the root piece at own time `0`. -/
theorem exists_closedPrefix_raw_eq_empty {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
      some (c, θ') → GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    (hTip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D) :
    ∃ R : ClosedPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length), R.raw = ∅ := by
  set l := (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
    (boundaryWalkSpec b jumps θ right).2.2.length).1 with hl
  obtain ⟨pc, post, hs⟩ : ∃ pc post, l = [] ++ pc :: post := by
    rcases hcase : l with _ | ⟨pc, post⟩
    · exact absurd hcase (WalkIntBoundCut.boundary_run_pieces_ne_nil θ right D)
    · exact ⟨pc, post, rfl⟩
  obtain ⟨R, hRpre, -, hRpc, hRτ⟩ := exists_closedPrefix θ right D hreg hD hs (τ := 0) (by simp)
  refine ⟨R, Set.eq_empty_iff_forall_notMem.2 fun z hz => ?_⟩
  rw [ClosedPrefix.raw, hRpre, hRpc, hRτ] at hz
  obtain ⟨hz | hz, hzH⟩ := hz
  · simp at hz
  · obtain ⟨t, ht, htip⟩ := hz
    rw [ENNReal.coe_le_coe, nonpos_iff_eq_zero] at ht
    subst ht
    have hmem : pc ∈ l := by rw [hs]; exact List.mem_cons_self
    have h0 := im_eq_zero_of_tipAt_zero hTip hmem htip
    exact absurd hzH (by show ¬ (0 < z.im); rw [h0]; exact lt_irrefl 0)

section Pair

variable {sR sL : ExplState} {α β : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {x : ℝ} {p : ℂ}

/-- **A closed pair for a right-walk match.** -/
theorem exists_closedPair_right (hα : Supp9B.IsProperCurve α) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hpα : p ∈ range α) (hwR : wsetOf sR ⊆ range α) (hctl : IsControlledMatch sR sL true c x p)
    (hmk : ∀ (pre post : List Piece) (pc : Piece), sR.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sR, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hraw : ∀ R : WalkPrefix sR, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H)
    (L₀ : ClosedPrefix sL) (hL₀ : L₀.raw = ∅)
    (hexit : Bornology.IsBounded C → ∃ U V : ℝ≥0, α U = β V ∧ α U ∈ closure C ∧
      ∀ r : ℝ≥0, α r = p → r < U) :
    ∃ J : ClosedPair sR sL, (Bornology.IsBounded C → ClosedTailSep J C α β) ∧
      WalkIntFiber.IsPiecePhysicalMatch sR sL true c J.model x := by
  by_cases hb : Bornology.IsBounded C
  · obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
    obtain ⟨rp, hrp⟩ := hpα
    have hrpU := hlt rp hrp
    obtain ⟨O, hO, hOe⟩ := exists_isOpen_preimage_Iio hα U
    have hpO : p ∈ O := by
      have : rp ∈ α ⁻¹' O := by rw [hOe]; exact hrpU
      rw [← hrp]; exact this
    obtain ⟨pre, post, pc, τ, hs, hτ, ⟨z, hzO, hzw, hzn⟩, hm⟩ := hctl O hO hpO
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    obtain ⟨a, ha⟩ := hraw ⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩
    obtain ⟨u, rfl⟩ := hwR hzw
    have huU : u < U := by
      have : u ∈ α ⁻¹' O := hzO
      rw [hOe] at this; exact this
    have hau : a < u := by
      refine lt_of_not_ge fun hle => hzn ?_
      have hmem : α u ∈ α '' Icc 0 a ∩ H := ⟨⟨u, ⟨zero_le, hle⟩, rfl⟩, hzw.2⟩
      rw [← ha] at hmem
      exact hmem
    obtain ⟨J, hJR, hJL⟩ := exists_closedPair
      (ClosedPrefix.ofWalkPrefix (⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩ : WalkPrefix sR)) L₀
    have hU0 : 0 < U := lt_of_le_of_lt zero_le hrpU
    have hV0 : 0 < V := by
      refine pos_iff_ne_zero.2 fun hV => hU0.ne' (hα.2.1 ?_)
      rw [hUV, hV, hβ0, hα0]
    have hrawsub : J.right.raw ⊆ α '' Icc 0 a := by
      rw [hJR]
      change prefixSet pre' pc' τ ⊆ _
      have : prefixSet pre' pc' τ = α '' Icc 0 a ∩ H := ha
      rw [this]; exact inter_subset_left
    refine ⟨J, fun _ => ⟨U, V, hU0, hV0, hUV,
      WalkIntEnvelope.disjoint_closure_tail_of_cutoff hα hrawsub (hau.trans huU), ?_, hUC⟩, ?_⟩
    · rw [hJL, hL₀, closure_empty]; exact empty_disjoint _
    · have hsub := J.right_subset
      rw [hJR] at hsub
      exact hm J.model M hsub
  · obtain ⟨pre, post, pc, τ, hs, hτ, -, hm⟩ := hctl univ isOpen_univ (mem_univ p)
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    obtain ⟨J, hJR, -⟩ := exists_closedPair
      (ClosedPrefix.ofWalkPrefix (⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩ : WalkPrefix sR)) L₀
    have hsub := J.right_subset
    rw [hJR] at hsub
    exact ⟨J, fun h => absurd h hb, hm J.model M hsub⟩

/-- **A closed pair for a left-walk match** (mirror). -/
theorem exists_closedPair_left (hβ : Supp9B.IsProperCurve β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hpβ : p ∈ range β) (hwL : wsetOf sL ⊆ range β) (hctl : IsControlledMatch sL sR false c x p)
    (hmk : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sL, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hraw : ∀ R : WalkPrefix sL, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H)
    (R₀ : ClosedPrefix sR) (hR₀ : R₀.raw = ∅)
    (hexit : Bornology.IsBounded C → ∃ U V : ℝ≥0, α U = β V ∧ α U ∈ closure C ∧
      ∀ r : ℝ≥0, β r = p → r < V) :
    ∃ J : ClosedPair sR sL, (Bornology.IsBounded C → ClosedTailSep J C α β) ∧
      WalkIntFiber.IsPiecePhysicalMatch sL sR false c J.model x := by
  by_cases hb : Bornology.IsBounded C
  · obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
    obtain ⟨rp, hrp⟩ := hpβ
    have hrpV := hlt rp hrp
    obtain ⟨O, hO, hOe⟩ := exists_isOpen_preimage_Iio hβ V
    have hpO : p ∈ O := by
      have : rp ∈ β ⁻¹' O := by rw [hOe]; exact hrpV
      rw [← hrp]; exact this
    obtain ⟨pre, post, pc, τ, hs, hτ, ⟨z, hzO, hzw, hzn⟩, hm⟩ := hctl O hO hpO
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    obtain ⟨a, ha⟩ := hraw ⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩
    obtain ⟨v, rfl⟩ := hwL hzw
    have hvV : v < V := by
      have : v ∈ β ⁻¹' O := hzO
      rw [hOe] at this; exact this
    have hav : a < v := by
      refine lt_of_not_ge fun hle => hzn ?_
      have hmem : β v ∈ β '' Icc 0 a ∩ H := ⟨⟨v, ⟨zero_le, hle⟩, rfl⟩, hzw.2⟩
      rw [← ha] at hmem
      exact hmem
    obtain ⟨J, hJR, hJL⟩ := exists_closedPair R₀
      (ClosedPrefix.ofWalkPrefix (⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩ : WalkPrefix sL))
    have hV0 : 0 < V := lt_of_le_of_lt zero_le hrpV
    have hU0 : 0 < U := by
      refine pos_iff_ne_zero.2 fun hU => hV0.ne' (hβ.2.1 ?_)
      rw [← hUV, hU, hα0, hβ0]
    have hrawsub : J.left.raw ⊆ β '' Icc 0 a := by
      rw [hJL]
      change prefixSet pre' pc' τ ⊆ _
      have : prefixSet pre' pc' τ = β '' Icc 0 a ∩ H := ha
      rw [this]; exact inter_subset_left
    refine ⟨J, fun _ => ⟨U, V, hU0, hV0, hUV, ?_,
      WalkIntEnvelope.disjoint_closure_tail_of_cutoff hβ hrawsub (hav.trans hvV), hUC⟩, ?_⟩
    · rw [hJR, hR₀, closure_empty]; exact empty_disjoint _
    · have hsub := J.left_subset
      rw [hJL] at hsub
      exact hm J.model M hsub
  · obtain ⟨pre, post, pc, τ, hs, hτ, -, hm⟩ := hctl univ isOpen_univ (mem_univ p)
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    obtain ⟨J, -, hJL⟩ := exists_closedPair R₀
      (ClosedPrefix.ofWalkPrefix (⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩ : WalkPrefix sL))
    have hsub := J.left_subset
    rw [hJL] at hsub
    exact ⟨J, fun h => absurd h hb, hm J.model M hsub⟩

end Pair

section Sample

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {specR specL : ExplSpec} {sR sL : ExplState}
  {α β : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart}

/-- **The finite-word matches of one component chart, closed form** (no live piece needed; cf.
`finite_matches_of_sample`). -/
theorem finite_matches_closed_of_sample (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0) (hrR : range α = physOf specR sR) (hrL : range β = physOf specL sL)
    (hco : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t')) (hW : GW4Reg.WalkPocketShape α β)
    (hC : C ∈ betweenComponents (physOf specR sR) (physOf specL sL))
    (hc : IsComponentChart (physOf specR sR) (physOf specL sL) C c) (hdom : (c.dom : Set ℂ) = C)
    {ℓ : ℝ → ℂ} (hℓi : Function.Injective ℓ) (hℓ : ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (ℓ x)))
    (hclR : IsClosed (ordOf sR)) (hclL : IsClosed (ordOf sL))
    (hctlR : ∀ (x : ℝ) (p : ℂ), 0 < x → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p ∈ ordOf sR →
      p ∉ pieceEnds sR.1 → p ∉ closure (wsetOf sL) → IsControlledMatch sR sL true c x p)
    (hctlL : ∀ (x : ℝ) (p : ℂ), x < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p ∈ ordOf sL →
      p ∉ pieceEnds sL.1 → p ∉ closure (wsetOf sR) → IsControlledMatch sL sR false c x p)
    (hmkR : ∀ (pre post : List Piece) (pc : Piece), sR.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sR, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hmkL : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sL, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hrawR : ∀ R : WalkPrefix sR, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H)
    (hrawL : ∀ R : WalkPrefix sL, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H)
    (R₀ : ClosedPrefix sR) (hR₀ : R₀.raw = ∅) (L₀ : ClosedPrefix sL) (hL₀ : L₀.raw = ∅)
    {jumpsC : Finset ℝ} (hpw : IsPiecewiseConstantBoundaryData (componentWord κ b (ordOf sR) (ordOf sL) c.2.1) jumpsC)
    (hcbd : IsComponentBoundaryData κ b (ordOf sR) (ordOf sL) c.2.1
      (componentWord κ b (ordOf sR) (ordOf sL) c.2.1) jumpsC) :
    ∃ (t : Chart × (ℝ → ℝ) × Finset ℝ) (F : Set ℝ), F.Finite ∧
      IsComponentChart (physOf specR sR) (physOf specL sL) C t.1 ∧
      IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
      IsComponentBoundaryData κ b (ordOf sR) (ordOf sL) t.1.2.1 t.2.1 t.2.2 ∧
      ∀ x : ℝ, x ∉ F →
        (0 < x → (∃ J : ClosedPair sR sL,
            (Bornology.IsBounded (t.1.dom : Set ℂ) → ClosedTailSep J (t.1.dom : Set ℂ) α β) ∧
            WalkIntFiber.IsPiecePhysicalMatch sR sL true t.1 J.model x ∧ t.2.1 x = -bigLambda κ) ∨
          IsRealGap sR sL b jumps t.1 x (t.2.1 x)) ∧
        (x < 0 → (∃ J : ClosedPair sR sL,
            (Bornology.IsBounded (t.1.dom : Set ℂ) → ClosedTailSep J (t.1.dom : Set ℂ) α β) ∧
            WalkIntFiber.IsPiecePhysicalMatch sL sR false t.1 J.model x ∧ t.2.1 x = bigLambda κ) ∨
          IsRealGap sR sL b jumps t.1 x (t.2.1 x)) := by
  have hfα : GB11.IsCompleteSimpleFlow α := ⟨hα.1, hα.2.1, hα0, fun t => hα.2.2.1 t, hα.2.2.2⟩
  have hfβ : GB11.IsCompleteSimpleFlow β := ⟨hβ.1, hβ.2.1, hβ0, fun t => hβ.2.2.1 t, hβ.2.2.2⟩
  have hC' : C ∈ betweenComponents (range α) (range β) := by rw [hrR, hrL]; exact hC
  have hc' : IsComponentChart (range α) (range β) C c := by rw [hrR, hrL]; exact hc
  obtain ⟨hnot, hexit⟩ := pocket_landing_facts hfα hfβ hco hW hC' hc'
  have hαc : IsClosed (range α) := GW4Reg.isClosed_range_of_isCompleteSimpleFlow hfα
  have hβc : IsClosed (range β) := GW4Reg.isClosed_range_of_isCompleteSimpleFlow hfβ
  have hwR : wsetOf sR ⊆ range α := fun z hz => hrR ▸ Or.inl (Or.inr hz.1)
  have hwL : wsetOf sL ⊆ range β := fun z hz => hrL ▸ Or.inl (Or.inr hz.1)
  have hclwR : closure (wsetOf sR) ⊆ ordOf sR := closure_minimal (fun z hz => hz.1) hclR
  have hclwL : closure (wsetOf sL) ⊆ ordOf sL := closure_minimal (fun z hz => hz.1) hclL
  have hclwLβ : closure (wsetOf sL) ⊆ range β := closure_minimal hwL hβc
  have hclwRα : closure (wsetOf sR) ⊆ range α := closure_minimal hwR hαc
  set F : Set ℝ := {0} ∪ ℓ ⁻¹' (pieceEnds sR.1 ∪ pieceEnds sL.1 ∪ ((↑) : ℝ → ℂ) '' (jumps : Set ℝ)) with hFdef
  have hF : F.Finite := (finite_singleton 0).union
    ((((pieceEnds_finite _).union (pieceEnds_finite _)).union (jumps.finite_toSet.image _)).preimage
      hℓi.injOn)
  refine ⟨(c, componentWord κ b (ordOf sR) (ordOf sL) c.2.1, jumpsC), F, hF, hc, hpw, hcbd,
    fun x hxF => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  all_goals
    have hxF' : ℓ x ∉ pieceEnds sR.1 ∧ ℓ x ∉ pieceEnds sL.1 ∧ ℓ x ∉ ((↑) : ℝ → ℂ) '' (jumps : Set ℝ) :=
      ⟨fun h => hxF (Or.inr (Or.inl (Or.inl h))), fun h => hxF (Or.inr (Or.inl (Or.inr h))),
        fun h => hxF (Or.inr (Or.inr h))⟩
    obtain ⟨hpE, hpE', hpJ⟩ := hxF'
    obtain ⟨p₁, hp₁, hp₁R, hp₁L⟩ := hc.2.2.2.2.1 x
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
    have hpp : p₁ = ℓ x := tendsto_nhds_unique hp₁ (hℓ x)
    subst hpp
    obtain ⟨hw1, hw2⟩ := componentWord_of_landing (κ := κ) (b := b) (ordR := ordOf sR) (ordL := ordOf sL) (hℓ x)
    obtain ⟨hn1, hn2⟩ := hnot x (ℓ x) (hℓ x)
  · -- `x > 0`
    have hpR := hp₁R hx
    have hpβ := hn1 hx
    by_cases hpo : ℓ x ∈ ordOf sR
    · have hctl := hctlR x (ℓ x) hx (hℓ x) hpo hpE (fun h => hpβ (hclwLβ h))
      obtain ⟨J, hbe, hm⟩ := exists_closedPair_right hα hα0 hβ0 (hrR ▸ hpR) hwR hctl hmkR hrawR L₀ hL₀
        (fun hb => by
          obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
          exact ⟨U, V, hUV, hUC, (hlt x (ℓ x) (hℓ x)).1⟩)
      refine Or.inl ⟨J, by rw [hdom]; exact hbe, hm, ?_⟩
      show componentWord κ b (ordOf sR) (ordOf sL) c.2.1 x = _
      rw [hw1 hx, ite_eq_left hpo]
    · have him : (ℓ x).im = 0 := (mem_ordOf_or_im_eq_zero hpR).resolve_left hpo
      have hre : ((ℓ x).re : ℂ) = ℓ x := Complex.ext (by simp) (by simp [him])
      obtain ⟨r, hr, hgap⟩ := exists_ball_disjoint_union (S := wsetOf sR) (T := wsetOf sL) (q := ℓ x)
        (fun h => hpo (hclwR h)) (fun h => hpβ (hclwLβ h))
      refine Or.inr ⟨(ℓ x).re, r, fun h => hpJ ⟨_, h, hre⟩, hr, by rw [hre]; exact hℓ x,
        by rw [hre]; exact hgap, ?_⟩
      show componentWord κ b (ordOf sR) (ordOf sL) c.2.1 x = _
      rw [hw1 hx, ite_eq_right hpo]
  · -- `x < 0`
    have hpL := hp₁L hx
    have hpα := hn2 hx
    by_cases hpo : ℓ x ∈ ordOf sL
    · have hctl := hctlL x (ℓ x) hx (hℓ x) hpo hpE' (fun h => hpα (hclwRα h))
      obtain ⟨J, hbe, hm⟩ := exists_closedPair_left hβ hα0 hβ0 (hrL ▸ hpL) hwL hctl hmkL hrawL R₀ hR₀
        (fun hb => by
          obtain ⟨U, V, hUV, hUC, hlt⟩ := hexit hb
          exact ⟨U, V, hUV, hUC, (hlt x (ℓ x) (hℓ x)).2⟩)
      refine Or.inl ⟨J, by rw [hdom]; exact hbe, hm, ?_⟩
      show componentWord κ b (ordOf sR) (ordOf sL) c.2.1 x = _
      rw [hw2 hx, ite_eq_left hpo]
    · have him : (ℓ x).im = 0 := (mem_ordOf_or_im_eq_zero hpL).resolve_left hpo
      have hre : ((ℓ x).re : ℂ) = ℓ x := Complex.ext (by simp) (by simp [him])
      obtain ⟨r, hr, hgap⟩ := exists_ball_disjoint_union (S := wsetOf sR) (T := wsetOf sL) (q := ℓ x)
        (fun h => hpα (hclwRα h)) (fun h => hpo (hclwL h))
      refine Or.inr ⟨(ℓ x).re, r, fun h => hpJ ⟨_, h, hre⟩, hr, by rw [hre]; exact hℓ x,
        by rw [hre]; exact hgap, ?_⟩
      show componentWord κ b (ordOf sR) (ordOf sL) c.2.1 x = _
      rw [hw2 hx, ite_eq_right hpo]

end Sample

end InteractingSLE.Theorem14.WalkWd
