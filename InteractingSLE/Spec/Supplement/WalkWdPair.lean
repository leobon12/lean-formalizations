/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWdShape
import InteractingSLE.Spec.Supplement.WalkWdMatch
import InteractingSLE.Spec.Supplement.WalkIntActiveRetained
import InteractingSLE.Spec.Supplement.GW1WalkChainPiece

/-!
# Retained pairs for the finite-word matches

Packet PROVE-WALK-WORDS2 (`hMatch` of Theorem 1.4's walk leaf). Deterministic packaging of one match:

* `exists_first_split` (lists): the first element with a property;
* **`exists_walkPrefix_raw_eq_empty`**: a boundary-walk run with a live recorded piece has a live recorded prefix with
  empty raw set — the first live piece at its own time `0` (every earlier piece is dead, and every piece starts at a
  real point, `GW1WalkChain.WalkTipCoordinates`);
* **`exists_retainedPair_right` / `_left`**: a controlled prefix match (`WalkWd.exists_controlledMatch_right` /
  `_left`: for every open `U ∋ p` a prefix with the match and a fresh point of the walk in `U` after it), the raw
  initial segments of live prefixes in a full proper parameter `α` (PROVE-T14-WALKINT's
  `exists_raw_initial_segment_of_run`), an empty live prefix of the other walk and, for a bounded component, a closing
  contact `α U = β V ∈ C̄` after the landing give a `RetainedPair` with the match and its `BeforeExit` data: take
  `U ∩ range α = α([0, U))`; the fresh point `α(u)`, `u < U`, is off the prefix set `α([0, a]) ∩ ℍ`, so `a < u < U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkWd

open WalkBdry WalkIntFill WalkIntActive Exist.StagedLaw

/-- The first element of a list with a property. -/
theorem exists_first_split {ι : Type*} (P : ι → Prop) :
    ∀ l : List ι, (∃ x ∈ l, P x) → ∃ (pre : List ι) (x : ι) (post : List ι),
      l = pre ++ x :: post ∧ P x ∧ ∀ y ∈ pre, ¬ P y
  | [], ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, h => by
    by_cases ha : P a
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · obtain ⟨x, hx, hPx⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact absurd hPx ha
      · obtain ⟨pre, y, post, he, hPy, hpre⟩ := exists_first_split P l ⟨x, hx', hPx⟩
        refine ⟨a :: pre, y, post, by rw [he]; rfl, hPy, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ha
        · exact hpre z hz

section Seed

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- Every recorded piece of a run with tip coordinates starts at a real point. -/
theorem im_eq_zero_of_tipAt_zero {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hTip : GW1WalkChain.WalkTipCoordinates κ b jumps spec D) {n : ℕ} {p' : Piece}
    (hp' : p' ∈ (ExplState.run κ b jumps spec D n).1) {z : ℂ} (hz : p'.1.tipAt p'.2.1 0 z) : z.im = 0 := by
  obtain ⟨pre, post, hs⟩ := List.append_of_mem hp'
  obtain ⟨ℓ, -, θ', hl, -, hpc⟩ := WalkSide.exists_launch_of_pieces_eq (κ := κ) (b := b) (jumps := jumps) spec D n hs
  subst hpc
  have h0 := (hTip ℓ _ θ' hl).1
  rw [Chart.tipAt_unique hz h0]
  simp

/-- **A live recorded prefix with empty raw set** (the first live piece at own time `0`). -/
theorem exists_walkPrefix_raw_eq_empty (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
      some (c, θ') → GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    (hTip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D)
    (hlive : ∃ pc ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1, (0 : ℝ≥0∞) < pc.2.2) :
    ∃ R : WalkPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length), R.raw = ∅ := by
  obtain ⟨pre, pc, post, hs, hpos, hpre⟩ := exists_first_split (fun p : Piece => (0 : ℝ≥0∞) < p.2.2) _ hlive
  obtain ⟨R, hRpre, -, hRpc, hRτ⟩ := exists_walkPrefix θ right D hreg hD hs (τ := 0) (by simpa using hpos)
  refine ⟨R, ?_⟩
  rw [WalkPrefix.raw, hRpre, hRpc, hRτ]
  refine Set.eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨hz | hz, hzH⟩ := hz
  · obtain ⟨p', hp', hzp'⟩ := mem_iUnion₂.1 hz
    have hstop : p'.2.2 = 0 := le_antisymm (not_lt.1 (hpre p' hp')) zero_le
    obtain ⟨t, ht, htip⟩ := hzp'
    rw [hstop, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at ht
    subst ht
    have hmem : p' ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (boundaryWalkSpec b jumps θ right).2.2.length).1 := by
      rw [hs]; exact List.mem_append_left _ hp'
    have h0 := im_eq_zero_of_tipAt_zero hTip hmem htip
    exact absurd hzH (by show ¬ (0 < z.im); rw [h0]; exact lt_irrefl 0)
  · obtain ⟨t, ht, htip⟩ := hz
    rw [ENNReal.coe_le_coe, nonpos_iff_eq_zero] at ht
    subst ht
    have hmem : pc ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (boundaryWalkSpec b jumps θ right).2.2.length).1 := by
      rw [hs]; exact List.mem_append_right _ List.mem_cons_self
    have h0 := im_eq_zero_of_tipAt_zero hTip hmem htip
    exact absurd hzH (by show ¬ (0 < z.im); rw [h0]; exact lt_irrefl 0)

end Seed

section Pair

variable {sR sL : ExplState} {α β : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {x : ℝ} {p : ℂ}

/-- The open set of a full parameter's initial segment `α([0, U))`. -/
theorem exists_isOpen_preimage_Iio (hα : Supp9B.IsProperCurve α) (U : ℝ≥0) :
    ∃ O : Set ℂ, IsOpen O ∧ α ⁻¹' O = Iio U :=
  (WalkCont.isClosedEmbedding_of_isProperCurve hα).isInducing.isOpen_iff.1 isOpen_Iio

/-- **A retained pair for a right-walk match** (see the module docstring). -/
theorem exists_retainedPair_right (hα : Supp9B.IsProperCurve α) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hpα : p ∈ range α) (hwR : wsetOf sR ⊆ range α)
    (hctl : ∀ U : Set ℂ, IsOpen U → p ∈ U → ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0),
      sR.1 = pre ++ pc :: post ∧ (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
      (∃ z ∈ U, z ∈ wsetOf sR ∧ z ∉ prefixSet pre pc τ) ∧
      ∀ {d : Chart} (B : WalkIntCanon.HullModel d) (A : WalkIntCanon.HullModel (prefixChart pc τ)),
        A.hull ⊆ B.hull → WalkIntFiber.IsPiecePhysicalMatch sR sL true c B x)
    (hmk : ∀ (pre post : List Piece) (pc : Piece), sR.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sR, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hraw : ∀ R : WalkPrefix sR, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H)
    (L₀ : WalkPrefix sL) (hL₀ : L₀.raw = ∅)
    (hexit : Bornology.IsBounded C → ∃ U V : ℝ≥0, α U = β V ∧ α U ∈ closure C ∧
      ∀ r : ℝ≥0, α r = p → r < U) :
    ∃ J : RetainedPair sR sL, (Bornology.IsBounded C → Nonempty (BeforeExit J C α β)) ∧
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
    obtain ⟨J, hJR, hJL⟩ := exists_retainedPair (⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩ : WalkPrefix sR) L₀
    have hU0 : 0 < U := lt_of_le_of_lt zero_le hrpU
    have hV0 : 0 < V := by
      refine pos_iff_ne_zero.2 fun hV => hU0.ne' (hα.2.1 ?_)
      rw [hUV, hV, hβ0, hα0]
    refine ⟨J, fun _ => ⟨⟨a, 0, U, V, ?_, ?_, hau.trans huU, hV0, hUV, hUC⟩⟩, ?_⟩
    · rw [hJR]
      change prefixSet pre' pc' τ ⊆ _
      have : prefixSet pre' pc' τ = α '' Icc 0 a ∩ H := ha
      rw [this]; exact inter_subset_left
    · rw [hJL, hL₀]; exact empty_subset _
    · have hsub := J.right_subset
      rw [hJR] at hsub
      exact hm J.model M hsub
  · obtain ⟨pre, post, pc, τ, hs, hτ, -, hm⟩ := hctl univ isOpen_univ (mem_univ p)
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    obtain ⟨J, hJR, -⟩ := exists_retainedPair (⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩ : WalkPrefix sR) L₀
    have hsub := J.right_subset
    rw [hJR] at hsub
    exact ⟨J, fun h => absurd h hb, hm J.model M hsub⟩

/-- **A retained pair for a left-walk match** (mirror). -/
theorem exists_retainedPair_left (hβ : Supp9B.IsProperCurve β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hpβ : p ∈ range β) (hwL : wsetOf sL ⊆ range β)
    (hctl : ∀ U : Set ℂ, IsOpen U → p ∈ U → ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0),
      sL.1 = pre ++ pc :: post ∧ (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
      (∃ z ∈ U, z ∈ wsetOf sL ∧ z ∉ prefixSet pre pc τ) ∧
      ∀ {d : Chart} (B : WalkIntCanon.HullModel d) (A : WalkIntCanon.HullModel (prefixChart pc τ)),
        A.hull ⊆ B.hull → WalkIntFiber.IsPiecePhysicalMatch sL sR false c B x)
    (hmk : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post → ∀ τ : ℝ≥0,
      (τ : ℝ≥0∞) < pc.2.2 → ∃ R : WalkPrefix sL, R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ)
    (hraw : ∀ R : WalkPrefix sL, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H)
    (R₀ : WalkPrefix sR) (hR₀ : R₀.raw = ∅)
    (hexit : Bornology.IsBounded C → ∃ U V : ℝ≥0, α U = β V ∧ α U ∈ closure C ∧
      ∀ r : ℝ≥0, β r = p → r < V) :
    ∃ J : RetainedPair sR sL, (Bornology.IsBounded C → Nonempty (BeforeExit J C α β)) ∧
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
    obtain ⟨J, hJR, hJL⟩ := exists_retainedPair R₀ (⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩ : WalkPrefix sL)
    have hV0 : 0 < V := lt_of_le_of_lt zero_le hrpV
    have hU0 : 0 < U := by
      refine pos_iff_ne_zero.2 fun hU => hV0.ne' (hβ.2.1 ?_)
      rw [← hUV, hU, hα0, hβ0]
    refine ⟨J, fun _ => ⟨⟨0, a, U, V, ?_, ?_, hU0, hav.trans hvV, hUV, hUC⟩⟩, ?_⟩
    · rw [hJR, hR₀]; exact empty_subset _
    · rw [hJL]
      change prefixSet pre' pc' τ ⊆ _
      have : prefixSet pre' pc' τ = β '' Icc 0 a ∩ H := ha
      rw [this]; exact inter_subset_left
    · have hsub := J.left_subset
      rw [hJL] at hsub
      exact hm J.model M hsub
  · obtain ⟨pre, post, pc, τ, hs, hτ, -, hm⟩ := hctl univ isOpen_univ (mem_univ p)
    obtain ⟨⟨pre', post', pc', τ', hs', hτ', M, hn, hpr, hf⟩, rfl, rfl, rfl, rfl⟩ := hmk pre post pc hs τ hτ
    obtain ⟨J, -, hJL⟩ := exists_retainedPair R₀ (⟨pre', post', pc', τ, hs', hτ', M, hn, hpr, hf⟩ : WalkPrefix sL)
    have hsub := J.left_subset
    rw [hJL] at hsub
    exact ⟨J, fun h => absurd h hb, hm J.model M hsub⟩

end Pair

end InteractingSLE.Theorem14.WalkWd
