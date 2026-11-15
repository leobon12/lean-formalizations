/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XzArc
import InteractingSLE.Spec.Supplement.SB2XbAE
import InteractingSLE.Spec.Supplement.SB2XbLock
import InteractingSLE.Spec.Supplement.SB2LpStep
import InteractingSLE.Spec.Supplement.SB2McRun
import InteractingSLE.Spec.Supplement.SB2MeInputs
import InteractingSLE.Spec.Supplement.GW2aContArc
import InteractingSLE.Spec.Supplement.SB2LkFree

/-!
# The connector form of `tail` holds at both start kinds

Packet PROVE-T14-SB2LIFT (round 30). **`tailArc_of_arcStart`**, **`tailArc_of_pieceStart`**: for a proper
parametrization `β₀` of the actual lower walk that visits `R` at `t_L` with its head real points `≤ R`, at an arc
start or a piece start at `o` (with their head inclusions), every connector point visited by the tail after `t_L` is
`≥ R` (`TailArc`). Deterministic, from GW1's run facts (regular launches, no left move, no left end-hit) and the
connectors lying in `[0, ∞)`. Steps:
* `mem_arcs_run_mono`, **`arc_origin`**: a connector of the run is old at the start stage or was appended at a
  later stage;
* **`appended_arc`**: an appended connector lies right of the current point, and the walk was neither done nor
  dead there (no left move; a terminal left ray would leave `[0, ∞)`);
* `pt_ge_of_appended`: the current point at such a stage is at least every earlier right record (`PtRec`, the
  record is monotone; every earlier launch was finite since the walk is not done);
* **`not_tail_of_seg`**: the tail cannot reach a real point `x < R` of a real segment `[x, y] ⊆ range β₀` with
  `y > R` (the head has no real point `> R`, and an intermediate-value argument along the segment's preimage);
  this handles the part of the start connector left of `R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The connectors of a run only accumulate. -/
theorem mem_arcs_run_mono {a : Set ℝ} {n m : ℕ} (hnm : n ≤ m)
    (ha : a ∈ (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n).2.1) :
    a ∈ (ExplState.run κ b J (boundaryWalkSpec b J θ true) D m).2.1 := by
  induction m, hnm using Nat.le_induction with
  | base => exact ha
  | succ m _ ih =>
    rcases GW2aCont.arcs_run_succ (κ := κ) (b := b) (jumps := J) (boundaryWalkSpec b J θ true) D m with
      e | ⟨a', e⟩
    · rw [e]; exact ih
    · rw [e]; exact List.mem_append_left _ ih

/-- **The origin of a connector**: it is a connector at stage `j₀`, or it was appended at a stage `j ≥ j₀`. -/
theorem arc_origin {a : Set ℝ} {j₀ n : ℕ} (hj : j₀ ≤ n)
    (ha : a ∈ (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n).2.1) :
    a ∈ (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j₀).2.1 ∨
      ∃ j, j₀ ≤ j ∧ j < n ∧ (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (j + 1)).2.1 =
        (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j).2.1 ++ [a] := by
  induction n, hj using Nat.le_induction with
  | base => exact Or.inl ha
  | succ n hjn ih =>
    rcases GW2aCont.arcs_run_succ (κ := κ) (b := b) (jumps := J) (boundaryWalkSpec b J θ true) D n with
      e | ⟨a', e⟩
    · rw [e] at ha
      rcases ih ha with h | ⟨j, h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, h1, by omega, h3⟩
    · rw [e] at ha
      rcases List.mem_append.1 ha with h | h
      · rcases ih h with h' | ⟨j, h1, h2, h3⟩
        · exact Or.inl h'
        · exact Or.inr ⟨j, h1, by omega, h3⟩
      · rw [List.mem_singleton] at h
        subst h
        exact Or.inr ⟨n, hjn, by omega, e⟩

theorem not_eq_append_singleton {l : List (Set ℝ)} {a : Set ℝ} (h : l = l ++ [a]) : False := by
  have := congrArg List.length h
  simp at this

/-- **An appended connector lies right of the current point**, and the walk was neither done nor dead there. -/
theorem appended_arc {a : Set ℝ} {j : ℕ}
    (he : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (j + 1)).2.1 =
      (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j).2.1 ++ [a])
    (hlm : NoLeftMove κ b J θ D j) (ha0 : a ⊆ Ici 0) :
    a ⊆ Ici (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j)) ∧
      stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j) ≠ stDone ∧
      stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j) ≠ stDead := by
  set s := ExplState.run κ b J (boundaryWalkSpec b J θ true) D j with hs
  have hne : ∀ t : ExplState, t.2.1 = s.2.1 →
      ExplState.run κ b J (boundaryWalkSpec b J θ true) D (j + 1) = t → False := by
    intro t ht e
    rw [e, ht] at he
    exact not_eq_append_singleton he
  refine ⟨?_, fun hd => ?_, fun hd => ?_⟩
  · rcases run_succ_walk_cases (κ := κ) (b := b) (jumps := J) (θ := θ) D j with e | e | e
    · exact (hne s rfl e).elim
    · exact (hne _ (GW2aCont.arcs_flowStep (κ := κ) (b := b) false s j (D j) θ ⊤) e).elim
    · rcases contStep_cases (κ := κ) (b := b) (jumps := J) s none true with e' | e' | ⟨r, x, m, e'⟩ | ⟨r, e'⟩
      · exact (hne s rfl (e.trans e')).elim
      · exact (hne _ (arcs_setDead s) (e.trans e')).elim
      · have h1 := he
        rw [e, e', GW1Bookkeep.arcs_moveAlong_append] at h1
        have h2 : (if r then Icc (stPt s) x else Icc x (stPt s)) = a := by simpa using h1
        cases r
        · exact absurd (e.trans e') (hlm x m)
        · simp only [↓reduceIte] at h2
          rw [← h2]
          exact fun z hz => hz.1
      · have h1 := he
        rw [e, e', GW1Bookkeep.arcs_moveToEnd_append] at h1
        have h2 : (if r then Ici (stPt s) else Iic (stPt s)) = a := by simpa using h1
        cases r
        · exfalso
          simp only [Bool.false_eq_true, ↓reduceIte] at h2
          have hm : min (stPt s) 0 - 1 ∈ a := by
            rw [← h2]
            exact mem_Iic.2 (by linarith [min_le_left (stPt s) 0])
          have h0 := ha0 hm
          simp only [mem_Ici] at h0
          linarith [min_le_right (stPt s) 0]
        · simp only [↓reduceIte] at h2
          rw [← h2]
  · exact not_eq_append_singleton
      ((arcs_run_succ_of_terminal (κ := κ) (b := b) (jumps := J) (θ := θ) D (Or.inl hd)).symm.trans he)
  · exact not_eq_append_singleton
      ((arcs_run_succ_of_terminal (κ := κ) (b := b) (jumps := J) (θ := θ) D (Or.inr hd)).symm.trans he)

/-- **The current point at a live stage is at least every earlier right record**: every earlier launch was finite
(an infinite one ends the walk), so `PtRec` and the record's monotonicity hold up to the stage. -/
theorem pt_ge_of_live (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) (hlm : ∀ j, NoLeftMove κ b J θ D j)
    (hlh : ∀ j, NoLeftHit κ b J θ D j) {j₁ j : ℕ} (hj : j₁ ≤ j)
    (hnd : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j) ≠ stDone)
    (hndd : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j) ≠ stDead) :
    stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j₁) ≤
      stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D j) := by
  have hfin : ∀ i, i < j → (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (i + 1)).2.2.2.1 i ≠ none →
      (D i).2 ≠ ⊤ := by
    intro i hi hl htop
    have hd : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (i + 1)) = stDone := by
      rw [launch_walk hl]
      exact (launch_eq_of_top _ i (D i) θ ⊤ (by rw [htop, min_self])).2.2.2.2.1
    exact hnd (done_of_le hd (by omega))
  have hrp := recInv_ptRec_run_le hP hfin hlm hlh
  have hmono := stRecR_run_mono hP (fun k hk => (hrp k hk.le).1) hj le_rfl
  rcases (hrp j le_rfl).2 with h | h | h
  · exact absurd h hnd
  · exact absurd h hndd
  · rw [h]; exact hmono

/-- **The tail cannot reach the left part of a real segment through `R`**: if `[x, y] ⊆ range β₀` with `x < R < y`,
the head has no real point `> R`, and `β₀` visits `R` at `t_L`, then `β₀` does not visit `x` after `t_L`. -/
theorem not_tail_of_seg {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} (hβp : Supp9B.IsProperCurve β₀) (hβL : β₀ tL = R)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) {x y : ℝ} (hxR : x < R) (hRy : R < y)
    (hseg : ((↑) : ℝ → ℂ) '' Icc x y ⊆ range β₀) {s : ℝ≥0} (hs : β₀ (tL + s) = x) : False := by
  have hemb := isClosedEmbedding_of_isProperCurve hβp
  set K : Set ℂ := ((↑) : ℝ → ℂ) '' Icc x y with hK
  have hKP : β₀ '' (β₀ ⁻¹' K) = K := image_preimage_eq_of_subset hseg
  have hKc : IsPreconnected K := isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hPp : IsPreconnected (β₀ ⁻¹' K) := by
    rw [← hKP] at hKc
    exact hemb.isEmbedding.isInducing.isPreconnected_image.1 hKc
  obtain ⟨ty, hty⟩ := hseg ⟨y, ⟨by linarith, le_rfl⟩, rfl⟩
  have htyL : tL < ty := by
    by_contra h
    push Not at h
    have := hhead ty h y hty
    linarith
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [add_zero, hβL] at hs
    have := Complex.ofReal_injective hs
    linarith
  have hsu : tL < tL + s := lt_add_of_pos_right tL (pos_iff_ne_zero.2 hs0)
  have hyP : ty ∈ β₀ ⁻¹' K := by
    show β₀ ty ∈ K
    rw [hty]
    exact ⟨y, ⟨by linarith, le_rfl⟩, rfl⟩
  have huP : tL + s ∈ β₀ ⁻¹' K := by
    show β₀ (tL + s) ∈ K
    rw [hs]
    exact ⟨x, ⟨le_rfl, by linarith⟩, rfl⟩
  have hsub := hPp.ordConnected.uIcc_subset hyP huP
  have hg : ContinuousOn (fun t => (β₀ t).re) (uIcc ty (tL + s)) :=
    (Complex.continuous_re.comp hβp.1).continuousOn
  have hR : R ∈ uIcc ((β₀ ty).re) ((β₀ (tL + s)).re) := by
    rw [hty, hs, Complex.ofReal_re, Complex.ofReal_re]
    exact mem_uIcc.2 (Or.inr ⟨hxR.le, hRy.le⟩)
  obtain ⟨r, hr, hgr⟩ := intermediate_value_uIcc hg hR
  obtain ⟨z, -, hz⟩ := hsub hr
  have hzR : z = R := by
    have := congrArg Complex.re hz
    simp only [Complex.ofReal_re] at this
    rw [this]
    exact hgr
  have hrL : r = tL := hβp.2.1 (by rw [← hz, hzR, hβL])
  rcases mem_uIcc.1 hr with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd (hrL ▸ h1) (not_le.2 htyL)
  · exact absurd (hrL ▸ h1) (not_le.2 hsu)

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ}

/-- A visit of the head to a tail point `x < R` is impossible (injectivity). -/
theorem not_head_of_tail (hβp : Supp9B.IsProperCurve β₀) (hβL : β₀ tL = R) {s : ℝ≥0} {x : ℝ}
    (hx : β₀ (tL + s) = x) (hxR : x < R) {t : ℝ≥0} (ht : t ≤ tL) (e : β₀ t = x) : False := by
  have h := hβp.2.1 (e.trans hx.symm)
  have hs0 : s = 0 := by
    have h' : tL + s ≤ tL := h ▸ ht
    exact le_antisymm (by simpa using h') bot_le
  rw [hs0, add_zero, hβL] at hx
  have := Complex.ofReal_injective hx
  linarith

/-- **`TailArc` at an arc start.** -/
theorem tailArc_of_arcStart (hβp : Supp9B.IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβL : β₀ tL = R)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R)
    (harc : ∀ n, ∀ a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n).2.1, a ⊆ Ici 0)
    (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hlm : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j)
    (hlh : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j) (hA : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o) :
    TailArc κ θ b₁ J₁ D₁ R β₀ tL := by
  rintro s x hx ⟨n, a, ha, hxa⟩
  by_contra hxR
  push Not at hxR
  have hmem := mem_arcs_run_mono (le_max_left n (o + 1)) ha
  rcases arc_origin (le_max_right n (o + 1)) hmem with h0 | ⟨j, hj₀, -, he⟩
  · obtain ⟨t, ht, e⟩ := hA.head (Or.inr (mem_iUnion₂.2 ⟨a, h0, x, hxa, rfl⟩))
    exact not_head_of_tail hβp hβL hx hxR ht e
  have haj : a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.1 := by
    rw [he]
    exact List.mem_append_right _ (List.mem_singleton_self a)
  obtain ⟨hsub, hnd, hndd⟩ := appended_arc he (hlm j) (harc _ a haj)
  have hrun : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1 + 1) =
      ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) none true :=
    run_succ_walk_cont hA.len (by have := hA.even; omega)
  rw [hA.move] at hrun
  rcases Nat.lt_or_ge j (o + 1 + 1) with hjlt | hjge
  · -- the start connector
    obtain rfl : j = o + 1 := by omega
    have hseg : ∀ y : ℝ, Icc x y ⊆ a → ((↑) : ℝ → ℂ) '' Icc x y ⊆ range β₀ := by
      rintro y hy _ ⟨z, hz, rfl⟩
      rw [hβr]
      refine prefix_subset_physSet D₁ (n := o + 1 + 1) (by have := hA.len; omega) ?_
      show (z : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1 + 1))
      exact Or.inr (mem_iUnion₂.2 ⟨a, haj, z, hy hz, rfl⟩)
    split_ifs at hrun with hC
    · rw [hrun, moveAlong_arcs_true] at he
      have ha' : Icc (stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)))
          ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).min' hC) = a := by
        simpa using he
      have hw := hA.gap _ (Finset.min'_mem _ hC)
      rw [← ha'] at hxa hseg
      exact not_tail_of_seg hβp hβL hhead hxR hw (hseg _ fun z hz => ⟨hxa.1.trans hz.1, hz.2⟩) hx
    · rw [hrun, moveToEnd_arcs_true] at he
      have ha' : Ici (stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))) = a := by
        simpa using he
      rw [← ha'] at hxa hseg
      exact not_tail_of_seg hβp hβL hhead hxR (lt_add_one R)
        (hseg _ fun z hz => mem_Ici.2 ((mem_Ici.1 hxa).trans hz.1)) hx
  · -- a later connector starts beyond `R`
    have hR2 : R < stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1 + 1)) := by
      split_ifs at hrun with hC
      · rw [hrun, stRecR_moveAlong_true]
        exact lt_of_lt_of_le (hA.gap _ (Finset.min'_mem _ hC)) (le_max_right _ _)
      · exfalso
        have hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1 + 1)) = stDone := by
          rw [hrun]
          exact stStatus_moveToEnd'' _ _
        exact hnd (done_of_le hd hjge)
    have h2 := pt_ge_of_live hP hlm hlh hjge hnd hndd
    have h3 : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ j) ≤ x := hsub hxa
    linarith

/-- **`TailArc` at a piece start.** -/
theorem tailArc_of_pieceStart (hβp : Supp9B.IsProperCurve β₀) (hβL : β₀ tL = R)
    (harc : ∀ n, ∀ a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n).2.1, a ⊆ Ici 0)
    (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hlm : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j)
    (hlh : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j) (hV : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    TailArc κ θ b₁ J₁ D₁ R β₀ tL := by
  rintro s x hx ⟨n, a, ha, hxa⟩
  by_contra hxR
  push Not at hxR
  have hmem := mem_arcs_run_mono (le_max_left n (o + 1)) ha
  rcases arc_origin (le_max_right n (o + 1)) hmem with h0 | ⟨j, hj₀, -, he⟩
  · have harcs : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.1 =
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o).2.1 := by
      rw [hV.launch]
      exact GW2aCont.arcs_launch _ _ _ _ _
    rw [harcs] at h0
    obtain ⟨t, ht, e⟩ := hV.head (Or.inr (mem_iUnion₂.2 ⟨a, h0, x, hxa, rfl⟩))
    exact not_head_of_tail hβp hβL hx hxR ht e
  have haj : a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.1 := by
    rw [he]
    exact List.mem_append_right _ (List.mem_singleton_self a)
  obtain ⟨hsub, hnd, hndd⟩ := appended_arc he (hlm j) (harc _ a haj)
  by_cases htop : (D₁ o).2 = ⊤
  · have hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) = stDone := by
      rw [hV.launch]
      exact (launch_eq_of_top _ o (D₁ o) θ ⊤ (by rw [htop, min_self])).2.2.2.2.1
    exact hnd (done_of_le hd hj₀)
  · have h1 := hV.recAfter htop
    have h2 := pt_ge_of_live hP hlm hlh hj₀ hnd hndd
    have h3 : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ j) ≤ x := hsub hxa
    linarith

end InteractingSLE.Theorem14.SB.Lk
