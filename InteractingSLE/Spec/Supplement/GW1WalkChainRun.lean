/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkChainReal

/-!
# GW1: the run induction

This is a conditional deterministic reduction. The hypotheses concerning connector clearance
and successful completion are stated explicitly; they are not consequences of per-piece simplicity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkChain

open GW1X GW1Bookkeep Exist Exist.Staged Exist.StagedLaw

theorem statePhysicalSet_launch (root : ℝ) (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    statePhysicalSet root (ExplState.launch s k D θ t) = statePhysicalSet root s ∪
      (stChart s).tipSet (fun r => D.1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal) (min t D.2) := by
  have harcs : (ExplState.launch s k D θ t).2.1 = s.2.1 := by
    obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
    unfold ExplState.launch
    dsimp only
    split_ifs <;> try rfl
    all_goals (rcases status with _ | _ | _ | _ | _ | _ <;> rfl)
  have hUnion (p : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞) :
      (⋃ q ∈ s.1 ++ [p], q.1.tipSet q.2.1 q.2.2) =
        (⋃ q ∈ s.1, q.1.tipSet q.2.1 q.2.2) ∪ p.1.tipSet p.2.1 p.2.2 := by
    ext z
    simp only [mem_union, mem_iUnion, exists_prop, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨q, hq | hq, hz⟩
      · exact Or.inl ⟨q, hq, hz⟩
      · exact Or.inr (hq ▸ hz)
    · rintro (⟨q, hq, hz⟩ | hz)
      · exact ⟨q, Or.inl hq, hz⟩
      · exact ⟨p, Or.inr rfl, hz⟩
  unfold statePhysicalSet
  rw [CounterflowRange.pieces_launch, harcs, hUnion]
  ac_rfl

theorem tipSet_inter_of_pieceSimpleAt {c : Chart} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    {old : Set ℂ} {q₀ q₁ : ℝ} (h : PieceSimpleAt c W S old q₀ q₁) :
    c.tipSet (fun r => W (min (r : ℝ≥0∞) S).toNNReal) S ∩ old = {(q₀ : ℂ)} := by
  obtain ⟨f, α, C, hf, hC, hmaps, hW0, hW, hα, htr, hi, hs, he, hm⟩ := h
  exact hm.trans (congrArg singleton hs)

theorem tipSet_zero_of_pieceSimpleAt {c : Chart} {W : ℝ≥0 → ℝ}
    {old : Set ℂ} {q₀ q₁ : ℝ} (h : PieceSimpleAt c W 0 old q₀ q₁) :
    c.tipSet (fun r => W (min (r : ℝ≥0∞) 0).toNNReal) 0 = {(q₀ : ℂ)} ∧ q₁ = q₀ := by
  obtain ⟨f, α, C, hf, hC, hmaps, hW0, hW, hα, htr, hi, hs, he, hm⟩ := h
  have htime : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ 0} = {0} := by ext t; simp
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (0 : ℝ≥0∞) → α t ∈ QuantumZipper.Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hW.mono fun _ ht => mem_ofPred.2 (le_of_lt ht)) hW0 ht
  have hset := CounterflowRange.tipSet_stopped_eq_of_tendsto hα hW hW0 fun t ht => hf _ (hαH t ht)
  refine ⟨?_, Complex.ofReal_injective ?_⟩
  · simpa only [htime, image_singleton, hs] using hset
  · have he' : f (α 0) = (q₁ : ℂ) := by simpa only [ENNReal.toNNReal_zero] using he (by simp)
    exact he'.symm.trans hs

/-- A live state has a chronological finite history. A completed state has its terminal chain. -/
def StateRepresented (root : ℝ) (s : ExplState) : Prop :=
  (stStatus s = stDone ∧ WalkChainRepresentation root s) ∨
    (stStatus s ≠ stDone ∧ ArcHistory (root : ℂ) (statePhysicalSet root s) (stPt s : ℂ))

theorem stateRepresented_init (root : ℝ) : StateRepresented root (ExplState.init root) := by
  refine Or.inr ⟨?_, ?_⟩
  · intro heq
    cases heq
  · convert ArcHistory.root (x := (root : ℂ)) using 1 <;>
    simp only [statePhysicalSet, ExplState.init, List.not_mem_nil, iUnion_of_empty, iUnion_empty,
      union_empty, stPt]

theorem stateRepresented_launch {root : ℝ} {s : ExplState}
    (h : ArcHistory (root : ℂ) (statePhysicalSet root s) (stPt s : ℂ))
    (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hP : PieceSimpleAt (stChart s) D.1 D.2 (statePhysicalSet root s) (stPt s)
      (stPt (ExplState.launch s k D θ ⊤))) :
    StateRepresented root (ExplState.launch s k D θ ⊤) := by
  have hset := statePhysicalSet_launch root s k D θ ⊤
  simp only [min_top_left] at hset
  by_cases htop : D.2 = ⊤
  · obtain ⟨f, α, ρ, hρ, hρf, hρ0, hρold, hρset⟩ :=
      exists_isProperCurve_of_pieceSimpleAt (htop ▸ hP)
    have hmeet : ∀ t, ρ t ∈ statePhysicalSet root s → t = 0 := by
      intro t ht
      have hm : ρ t ∈ ({(stPt s : ℂ)} : Set ℂ) := by
        rw [← tipSet_inter_of_pieceSimpleAt (htop ▸ hP), ← hρset]
        exact ⟨⟨t, rfl⟩, ht⟩
      exact hρ.2.1 ((mem_singleton_iff.1 hm).trans hρ0.symm)
    refine Or.inl ⟨(launch_eq_of_top s k D θ ⊤ (by simp only [htop, min_self])).2.2.2.2.1, ?_⟩
    apply h.walkChainRepresentation hρ hρ0 hmeet
    simpa only [htop, hρset] using hset
  · have hnot : stStatus (ExplState.launch s k D θ ⊤) ≠ stDone := by
      obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
      simp only [ExplState.launch, min_top_left, htop, ↓reduceIte, not_top_lt]
      split_ifs <;> try (intro heq; cases heq)
      all_goals (rcases status with _ | _ | _ | _ | _ | _ <;> intro heq <;> cases heq)
    refine Or.inr ⟨hnot, ?_⟩
    by_cases hzero : D.2 = 0
    · obtain ⟨hZ, hq⟩ := tipSet_zero_of_pieceSimpleAt (hzero ▸ hP)
      rw [hzero, hZ] at hset
      have hsingle : statePhysicalSet root s ∪ {(stPt s : ℂ)} = statePhysicalSet root s :=
        union_eq_left.2 (singleton_subset_iff.2 h.endpoint_mem)
      rw [hset, hsingle, hq]
      exact h
    · let T := D.2.toNNReal
      have hT : (T : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal htop
      have hTpos : 0 < T := by
        apply pos_iff_ne_zero.2
        intro h0
        apply hzero
        rw [← hT, h0, ENNReal.coe_zero]
      obtain ⟨f, α, γ, hγ, hγset, hγH, hγf0, hγf1, hγ0, hγ1, hγold, hγmeet⟩ :=
        exists_isArc_of_pieceSimpleAt hTpos (hT.symm ▸ hP)
      have hHist := h.append γ hγ (fun t ht => hγH t ht) hγ0 (by
        intro t ht hmem
        apply hγ.2 ht (mem_Iic.2 (by norm_num))
        have hm : γ t ∈ ({γ 0} : Set ℂ) := by rw [← hγmeet]; exact ⟨⟨t, ht, rfl⟩, hmem⟩
        exact mem_singleton_iff.1 hm)
      rw [hγset, hT, hγ1] at hHist
      rw [hset]
      exact hHist

/-- The new connector meets the entire retained old set only at its starting point. -/
def ConnectorClearance (root : ℝ) (s : ExplState) (B : Set ℂ) : Prop :=
  ∀ z ∈ B, z ∈ statePhysicalSet root s → z = (stPt s : ℂ)

theorem stateRepresented_moveAlong {root : ℝ} {s : ExplState}
    (h : ArcHistory (root : ℂ) (statePhysicalSet root s) (stPt s : ℂ))
    (right : Bool) (x : ℝ) (mark : Bool)
    (hdir : if right then stPt s < x else x < stPt s)
    (hclear : ConnectorClearance root s (((↑) : ℝ → ℂ) ''
      (if right then Icc (stPt s) x else Icc x (stPt s)))) :
    StateRepresented root (ExplState.moveAlong s right x mark) := by
  have hne : stPt s ≠ x := by
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hdir
    · exact hdir.ne'
    · exact hdir.ne
  have himage : realArc (stPt s) x '' Iic 1 = ((↑) : ℝ → ℂ) ''
      (if right then Icc (stPt s) x else Icc x (stPt s)) := by
    rw [image_realArc]
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hdir ⊢
    · rw [min_eq_right hdir.le, max_eq_left hdir.le]
    · rw [min_eq_left hdir.le, max_eq_right hdir.le]
  have hArc := isArc_realArc hne
  have hHist := h.append (realArc (stPt s) x) hArc
    (fun t _ => realArc_upper _ _ t) (realArc_zero _ _) (by
      intro t ht hmem
      apply hArc.2 ht (mem_Iic.2 (by norm_num))
      rw [realArc_zero]
      apply hclear _ _ hmem
      rw [← himage]
      exact ⟨t, ht, rfl⟩)
  rw [himage, realArc_one] at hHist
  refine Or.inr ⟨?_, ?_⟩
  · obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
    intro heq
    cases heq
  · rw [statePhysicalSet_moveAlong]
    simpa only [GW1W.stPt_moveAlong] using hHist

theorem stateRepresented_moveToEnd {root : ℝ} {s : ExplState}
    (h : ArcHistory (root : ℂ) (statePhysicalSet root s) (stPt s : ℂ))
    (right : Bool) (hclear : ConnectorClearance root s (range (realRay right (stPt s)))) :
    StateRepresented root (ExplState.moveToEnd s right) := by
  refine Or.inl ⟨?_, ?_⟩
  · obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
    rfl
  · apply h.walkChainRepresentation (isProperCurve_realRay right (stPt s)) (realRay_zero _ _)
    · intro t ht
      apply (isProperCurve_realRay right (stPt s)).2.1
      rw [realRay_zero]
      exact hclear _ ⟨t, rfl⟩ ht
    · exact statePhysicalSet_moveToEnd root s right

/-- An unrestricted continuation either changes no geometry, traverses a strictly oriented
finite interval to a mark, or appends a terminal boundary ray. -/
theorem contStep_none_cases {κ : ℝ} (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (pref : Bool) :
    ExplState.contStep κ b jumps s none pref = s ∨
      ExplState.contStep κ b jumps s none pref = setDead s ∨
      (∃ (right : Bool) (x : ℝ), (if right then stPt s < x else x < stPt s) ∧
        ExplState.contStep κ b jumps s none pref = ExplState.moveAlong s right x true) ∨
      ∃ right : Bool, ExplState.contStep κ b jumps s none pref = ExplState.moveToEnd s right := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.contStep
  dsimp only
  repeat' first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | solve
      | refine Or.inr (Or.inr (Or.inl ⟨true, _, ?_, rfl⟩))
        rename_i hC
        exact (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
    | solve
      | refine Or.inr (Or.inr (Or.inl ⟨false, _, ?_, rfl⟩))
        rename_i hC
        exact (Finset.mem_filter.1 (Finset.max'_mem _ hC)).2.1
    | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
    | split

theorem contStep_of_done {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {s : ExplState}
    (h : stStatus s = stDone) (v : Option ℝ) (pref : Bool) :
    ExplState.contStep κ b jumps s v pref = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at h
  subst status
  rfl

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool}
  {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- Exact geometric obligations for the real connectors of one run. -/
def WalkConnectorClearance (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ k, let s := ExplState.run κ b jumps spec D k
    (∀ r x, ExplState.run κ b jumps spec D (k + 1) = ExplState.moveAlong s r x true →
      ConnectorClearance spec.1 s (((↑) : ℝ → ℂ) ''
        (if r then Icc (stPt s) x else Icc x (stPt s)))) ∧
    (∀ r, ExplState.run κ b jumps spec D (k + 1) = ExplState.moveToEnd s r →
      ConnectorClearance spec.1 s (range (realRay r (stPt s))))

/-- The complete run reduction. Piece simplicity supplies arcs, including the initial singleton
when the lifetime is zero. Connector clearance supplies the other arcs and the terminal ray.
The completion hypothesis excludes a finite run ending in the machine's `dead` state. -/
theorem walkChainRepresentation_of_pieceSimpleAt
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hC : WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    (hDone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length) = stDone) :
    WalkChainRepresentation 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length) := by
  let spec := boundaryWalkSpec b jumps θ right
  have hI : ∀ n, StateRepresented 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
    intro n
    induction n with
    | zero => exact stateRepresented_init 0
    | succ n ih =>
      by_cases hdone : stStatus
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) = stDone
      · have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) =
            ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
          rw [run_succ]
          cases hk : spec.2.2[n]? with
          | none => rfl
          | some a =>
            change ExplState.step κ b jumps false D
              (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (a, n) =
                ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n
            rcases a with ⟨a, t⟩ | r | ⟨v, r⟩
            · exact isTerminal_flowStep (Or.inl hdone) n (D n) a t
            · exact contStep_of_done hdone none r
            · exact contStep_of_done hdone (some v) r
        rw [heq]
        exact ih
      · have hHist : ArcHistory (0 : ℂ)
            (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n))
            (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) : ℂ) := by
          rcases ih with ⟨hd, _⟩ | ⟨_, hh⟩
          · exact False.elim (hdone hd)
          · exact hh
        cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
            (n + 1)).2.2.2.1 n with
        | some p =>
          obtain ⟨c, θ'⟩ := p
          have hn : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
              (n + 1)).2.2.2.1 n ≠ none := by
            rw [hl]
            exact Option.some_ne_none _
          have heq := GW1W.launch_walk hn
          have hpiece := hP n c θ' hl hHist.endpoint_mem
          obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hn
          have htime : instrTime spec n = ⊤ := by
            simp only [spec, instrTime, GW1Conn.getElem?_boundaryWalkSpec, hlen, hev, ↓reduceIte]
          obtain ⟨_, _, hc⟩ := eq_launch_of_launches spec D hl
          rw [htime, min_top_left, hc, heq] at hpiece
          rw [heq]
          exact stateRepresented_launch hHist n (D n) θ hpiece
        | none =>
          by_cases hlen : n < spec.2.2.length
          · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
            · have heq := GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev
              have hnl := hl
              rw [heq] at hnl
              rw [heq, GW1W.flowStep_eq_self_of_noLaunch _ _ _ _ _ hnl]
              exact ih
            · have heq := GW1W.run_succ_walk_cont (κ := κ) (D := D) hlen hodd
              rcases contStep_none_cases (κ := κ) b jumps
                (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) right
                with hs | hs | ⟨r, x, hd, hs⟩ | ⟨r, hs⟩
              · rw [heq, hs]
                exact ih
              · rw [heq, hs]
                refine Or.inr ⟨?_, hHist⟩
                intro hf
                cases hf
              · rw [heq, hs]
                exact stateRepresented_moveAlong hHist r x true hd ((hC n).1 r x (heq.trans hs))
              · rw [heq, hs]
                exact stateRepresented_moveToEnd hHist r ((hC n).2 r (heq.trans hs))
          · have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) =
            ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
              rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_right hlen]
            rw [heq]
            exact ih
  rcases hI spec.2.2.length with ⟨_, hc⟩ | ⟨hn, _⟩
  · exact hc
  · exact False.elim (hn hDone)

end Run

end InteractingSLE.Theorem14.GW1WalkChain
