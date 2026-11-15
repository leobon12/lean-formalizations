/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LuStart

/-!
# SB2(2)'s lockstep induction with history: connectors as images, pieces paired

Packet PROVE-SB2-LIFTSET (target 2, the run half; handoff PROVE-T14-SB2LIFT §R10.2 item 3). `stCorr_run_of_steps`
propagates the state correspondence `StCorr ι p` of the actual and the relative lower walk. Here it is strengthened
to keep track of what the two runs record ("Genuine real connectors outside the old real base are transported by
positive reflection; if the erasure endpoint lies inside a connector, retain only its remaining part", supplement
p. 631):

* **`AccCorr ι p L t₁ t₂ s₁ s₂`**: `StCorr ι p s₁ s₂`, and since the starting states `t₁, t₂` the relative connectors
  are the `ι`-images of the parts right of `p` of the actual connectors, and the recorded pieces pair up under a
  relation `L` (for SB2(2), `L` is "the relative piece is the lift of the actual one", (L4));
* **`arcs_contStep_thr_gen`**: the connector datum of `stCorr_contStep_thr_gen` (the new relative connector is
  `ι '' (a ∩ Ici p)`);
* **`accCorr_step`**, **`accCorr_run_of_steps`**: every step keeps the correspondence with history, given `StepOK`
  and, at every launch, the piece datum `StepPiece` (the two new pieces are related by `L`);
* **`physSet_eq_of_accCorr`**: once the actual walk is done (hence also the relative one), the two physical sets are
  the physical parts of the starting states, the paired pieces, and the connectors, the relative connectors being
  the `ι`-images of the actual ones.

Supporting lemmas: `contStep_pieces`, `launch_pieces` (bookkeeping of `ExplState`), `statePhysicalSet_append`,
`physSet_walk_eq_of_done`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ}

/-! ### Bookkeeping of the run -/

/-- A connector step records no piece. -/
theorem contStep_pieces (b : ℝ → ℝ) (J : Finset ℝ) (s : ExplState) (v : Option ℝ) (pref : Bool) :
    (ExplState.contStep κ b J s v pref).1 = s.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.contStep
  dsimp only
  repeat' first | rfl | split

/-- A launch records one piece: the current chart, the driver stopped at the stop time, the stop time. -/
theorem launch_pieces (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k d θ t).1 =
      s.1 ++ [(stChart s, fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min t d.2)).toNNReal, min t d.2)] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | p | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
  · simp only [ExplState.launch]
    split_ifs <;> rfl


/-- A rightward move records the connector from the current point. -/
theorem moveAlong_arcs_true (s : ExplState) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s true x m).2.1 = s.2.1 ++ [Icc (stPt s) x] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

/-- A rightward move to the end records the ray from the current point. -/
theorem moveToEnd_arcs_true (s : ExplState) : (ExplState.moveToEnd s true).2.1 = s.2.1 ++ [Ici (stPt s)] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

/-- **A rightward connector step adds one arc right of the current point.** -/
theorem exists_arc_of_move {b : ℝ → ℝ} {J : Finset ℝ} {s t : ExplState}
    (ht : t = if hC : (restartSet κ b J s).Nonempty then
      ExplState.moveAlong s true ((restartSet κ b J s).min' hC) true else ExplState.moveToEnd s true) :
    ∃ a : Set ℝ, a ⊆ Ici (stPt s) ∧ t.2.1 = s.2.1 ++ [a] := by
  split_ifs at ht with hC
  · exact ⟨_, fun z (hz : z ∈ Icc _ _) => hz.1, by rw [ht, moveAlong_arcs_true]⟩
  · exact ⟨_, fun z hz => hz, by rw [ht, moveToEnd_arcs_true]⟩

/-! ### The lockstep correspondence with history -/

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {p : ℝ} {s₁ s₂ : ExplState}

/-- **The connectors of a connector step from a right threshold, for any current point**: the new relative connector
is the `ι`-image of the part of the actual one right of `p` (companion of `stCorr_contStep_thr_gen`). -/
theorem arcs_contStep_thr_gen (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hc : StCorr ι p s₁ s₂) (hRp : R ≤ p)
    (hptrec : stPt s₁ ≤ stRecR s₁) (hgap : ∀ x ∈ restartSet κ b₁ J₁ s₁, p < x)
    (hst : stStatus s₁ = stThr (some true)) :
    ∃ a : Set ℝ, (ExplState.contStep κ b₁ J₁ s₁ none true).2.1 = s₁.2.1 ++ [a] ∧
      (ExplState.contStep κ b₂ J₂ s₂ none true).2.1 = s₂.2.1 ++ [ι '' (a ∩ Ici p)] := by
  set p' := max (stPt s₁) p with hp'
  have hRp' : R ≤ p' := hRp.trans (le_max_right _ _)
  have hc' : StCorr ι p' s₁ s₂ := by
    obtain ⟨hpt, hstat, hθ, hrec⟩ := hc
    refine ⟨by rw [hpt, hp', ← max_assoc, max_self], hstat, hθ, ?_⟩
    rw [hrec, hp', ← max_assoc, max_eq_left hptrec]
  have hgap' : ∀ x ∈ restartSet κ b₁ J₁ s₁, p' < x := fun x hx => by
    have hx' := hx
    simp only [restartSet, Finset.mem_filter] at hx'
    exact max_lt hx'.2.1 (hgap x hx)
  obtain ⟨-, a, ha₁, ha₂⟩ := stCorr_contStep_thr (κ := κ) h hc' hRp' (le_max_left _ _) hgap' hst
  obtain ⟨a', ha'pt, ha'⟩ := exists_arc_of_move (contStep_thr_true' (κ := κ) b₁ J₁ s₁ hst)
  have haa : a = a' := by
    have := ha₁.symm.trans ha'
    simpa using this
  subst haa
  refine ⟨a, ha₁, ?_⟩
  rw [ha₂]
  congr 3
  ext z
  simp only [mem_inter_iff, mem_Ici, hp', max_le_iff]
  exact ⟨fun hz => ⟨hz.1, hz.2.2⟩, fun hz => ⟨hz.1, ha'pt hz.1, hz.2⟩⟩


/-- A recorded ordinary piece: (chart at launch, stopped driver, stop time). -/
abbrev Pc : Type := Chart × (ℝ≥0 → ℝ) × ℝ≥0∞

/-- The piece recorded by a launch at the walk's horizon `⊤` from the state `s` with driver `d`. -/
def newPc (s : ExplState) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : Pc :=
  (stChart s, fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min ⊤ d.2)).toNNReal, min ⊤ d.2)

/-- **The lockstep correspondence with its history**: the state correspondence, and since the starting states
`t₁, t₂` the relative connectors are the `ι`-images (right of `p`) of the actual ones and the recorded pieces pair up
under the relation `L`. -/
def AccCorr (ι : ℝ → ℝ) (p : ℝ) (L : Pc → Pc → Prop) (t₁ t₂ s₁ s₂ : ExplState) : Prop :=
  StCorr ι p s₁ s₂ ∧
    (∃ X : List (Set ℝ), s₁.2.1 = t₁.2.1 ++ X ∧ s₂.2.1 = t₂.2.1 ++ X.map (fun a => ι '' (a ∩ Ici p))) ∧
    ∃ Y₁ Y₂ : List Pc, s₁.1 = t₁.1 ++ Y₁ ∧ s₂.1 = t₂.1 ++ Y₂ ∧ List.Forall₂ L Y₁ Y₂

variable {L : Pc → Pc → Prop} {t₁ t₂ : ExplState}

/-- The correspondence with history starts at any pair of corresponding states. -/
theorem accCorr_refl (hc : StCorr ι p s₁ s₂) : AccCorr ι p L s₁ s₂ s₁ s₂ :=
  ⟨hc, ⟨[], by simp, by simp⟩, [], [], by simp, by simp, List.Forall₂.nil⟩

/-- Two steps that leave both states unchanged (or change neither the connectors nor the pieces) keep the
history. -/
theorem accCorr_of_same {s₁' s₂' : ExplState} (hc : AccCorr ι p L t₁ t₂ s₁ s₂) (hc' : StCorr ι p s₁' s₂')
    (h₁ : s₁'.2.1 = s₁.2.1 ∧ s₁'.1 = s₁.1) (h₂ : s₂'.2.1 = s₂.2.1 ∧ s₂'.1 = s₂.1) :
    AccCorr ι p L t₁ t₂ s₁' s₂' := by
  obtain ⟨-, ⟨X, hX₁, hX₂⟩, Y₁, Y₂, hY₁, hY₂, hY⟩ := hc
  exact ⟨hc', ⟨X, h₁.1.trans hX₁, h₂.1.trans hX₂⟩, Y₁, Y₂, h₁.2.trans hY₁, h₂.2.trans hY₂, hY⟩

/-- **The piece datum at a launch** in the lockstep induction: at an admissible restart mark the two new pieces
are related by `L`. -/
def StepPiece (κ θ : ℝ) (b₁ : ℝ → ℝ) (L : Pc → Pc → Prop) (flow : Bool) (s₁ s₂ : ExplState)
    (D₁ D₂ : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  flow = true → stStatus s₁ = GW1W.stArcM true →
    ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt s₁)) (rightLim b₁ (stPt s₁)) θ → L (newPc s₁ D₁) (newPc s₂ D₂)


/-- **One step of the lockstep induction with history.** -/
theorem accCorr_step (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hRp : R ≤ p) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k₁ k₂ : ℕ}
    (hk₁ : k₁ < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hk₂ : k₂ < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hpar : k₁ % 2 = k₂ % 2)
    (hc : AccCorr ι p L t₁ t₂ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂))
    (hok : StepOK κ θ b₁ J₁ R ι p (k₂ % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂) (D₁ k₁) (D₂ k₂))
    (hpc : StepPiece κ θ b₁ L (k₂ % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂) (D₁ k₁) (D₂ k₂)) :
    AccCorr ι p L t₁ t₂ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k₁ + 1))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k₂ + 1)) := by
  have hnext := stCorr_step h hRp hk₁ hk₂ hpar hc.1 hok
  set s₁ := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁ with hs₁
  set s₂ := ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂ with hs₂
  have hstat := hc.1.2.1
  rcases Nat.mod_two_eq_zero_or_one k₂ with hev | hodd
  · have hev₁ : k₁ % 2 = 0 := hpar.trans hev
    rw [run_succ_walk_flow hk₁ hev₁, run_succ_walk_flow hk₂ hev] at hnext ⊢
    simp only [StepOK, hev, decide_true, ↓reduceIte] at hok
    rcases hok with hd | hd | ⟨hst, hpR, hp₁, -⟩
    · rw [flowStep_of_done hd, flowStep_of_done (hstat.trans hd)]
      exact hc
    · rw [flowStep_of_dead hd, flowStep_of_dead (hstat.trans hd)]
      exact hc
    · have hst₂ : stStatus s₂ = GW1W.stArcM true := hstat.trans hst
      have hpt' : stPt s₂ = ι (stPt s₁) := by rw [hc.1.1, max_eq_left hp₁]
      obtain ⟨-, hseed⟩ := launchReady_corr (κ := κ) (θ := θ) h hst hst₂ hpt' hpR
      by_cases hadm : ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt s₁)) (rightLim b₁ (stPt s₁)) θ
      · have hadm₂ := hseed.2 hadm
        have e₁ := GW1WalkExit.flowStep_of_launchReady (κ := κ) (θ := θ) (b := b₁) (right := true)
          (Or.inr ⟨hst, hadm⟩) k₁ (D₁ k₁)
        have e₂ := GW1WalkExit.flowStep_of_launchReady (κ := κ) (θ := θ) (b := b₂) (right := true)
          (Or.inr ⟨hst₂, hadm₂⟩) k₂ (D₂ k₂)
        rw [e₁, e₂] at hnext ⊢
        have hL : L (newPc s₁ (D₁ k₁)) (newPc s₂ (D₂ k₂)) := hpc (by simp [hev]) hst hadm
        obtain ⟨-, ⟨X, hX₁, hX₂⟩, Y₁, Y₂, hY₁, hY₂, hY⟩ := hc
        refine ⟨hnext, ⟨X, by rw [launch_arcs, hX₁], by rw [launch_arcs, hX₂]⟩, Y₁ ++ [newPc s₁ (D₁ k₁)],
          Y₂ ++ [newPc s₂ (D₂ k₂)], ?_, ?_, List.rel_append hY (List.Forall₂.cons hL List.Forall₂.nil)⟩
        · rw [launch_pieces, hY₁, List.append_assoc]
          rfl
        · rw [launch_pieces, hY₂, List.append_assoc]
          rfl
      · have hadm₂ : ¬ ExplState.IsAdmissibleSeed κ (leftLim b₂ (stPt s₂)) (rightLim b₂ (stPt s₂)) θ :=
          fun h' => hadm (hseed.1 h')
        rw [flowStep_arcM_not hst hadm k₁ (D₁ k₁) ⊤, flowStep_arcM_not hst₂ hadm₂ k₂ (D₂ k₂) ⊤]
        exact hc
  · have hodd₁ : k₁ % 2 = 1 := hpar.trans hodd
    rw [run_succ_walk_cont hk₁ hodd₁, run_succ_walk_cont hk₂ hodd] at hnext ⊢
    simp only [StepOK, hodd, Nat.one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte] at hok
    rcases hok with hd | hd | ⟨r, hr⟩ | ⟨hst, hptrec, hgap⟩
    · rw [contStep_of_done' hd, contStep_of_done' (hstat.trans hd)]
      exact hc
    · exact accCorr_of_same hc hnext ⟨(contStep_of_dead hd true).2.2.2.2, contStep_pieces _ _ _ _ _⟩
        ⟨(contStep_of_dead (hstat.trans hd) true).2.2.2.2, contStep_pieces _ _ _ _ _⟩
    · rw [contStep_of_arcM hr, contStep_of_arcM (hstat.trans hr)]
      exact hc
    · obtain ⟨a, ha₁, ha₂⟩ := arcs_contStep_thr_gen (κ := κ) h hc.1 hRp hptrec hgap hst
      obtain ⟨-, ⟨X, hX₁, hX₂⟩, Y₁, Y₂, hY₁, hY₂, hY⟩ := hc
      refine ⟨hnext, ⟨X ++ [a], by rw [ha₁, hX₁, List.append_assoc], ?_⟩, Y₁, Y₂,
        by rw [contStep_pieces, hY₁], by rw [contStep_pieces, hY₂], hY⟩
      rw [ha₂, hX₂, List.map_append, List.append_assoc]
      rfl

/-- **The lockstep induction with history**: from the state correspondence at stage `i₀` and the step data while
both programs have instructions, the correspondence with history (connectors as images, pieces paired) holds at
every stage up to `N`, counted from the states at `i₀`. -/
theorem accCorr_run_of_steps (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hRp : R ≤ p) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (o i₀ N : ℕ) (hpar : o % 2 = 0)
    (hlen : ∀ i, i₀ ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (h₀ : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i₀))
    (hstep : ∀ i, i₀ ≤ i → i < N →
      StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι p (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ L (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i)) :
    ∀ i, i₀ ≤ i → i ≤ N → AccCorr ι p L (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i₀)
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact fun _ => accCorr_refl h₀
  | succ i hi ih =>
    intro hiN
    have hiN' : i < N := hiN
    have hc := ih hiN'.le
    obtain ⟨hk₁, hk₂⟩ := hlen i hi hiN'
    have hpar' : (i + o) % 2 = i % 2 := by omega
    obtain ⟨hok, hpc⟩ := hstep i hi hiN' hc.1
    have := accCorr_step (κ := κ) (θ := θ) h hRp hk₁ hk₂ hpar' hc hok hpc
    rwa [show i + o + 1 = i + 1 + o by omega] at this


/-! ### The physical sets -/

/-- A union over an appended list. -/
theorem biUnion_list_append {α β : Type*} (l₁ l₂ : List α) (f : α → Set β) :
    (⋃ q ∈ l₁ ++ l₂, f q) = (⋃ q ∈ l₁, f q) ∪ ⋃ q ∈ l₂, f q := by
  ext z
  simp only [mem_iUnion, mem_union, List.mem_append, exists_prop, or_and_right, exists_or]

open GW1Bookkeep in
/-- The physical part of a state that extends another by pieces `Y` and connectors `Z`. -/
theorem statePhysicalSet_append {x : ℝ} {s t : ExplState} {Y : List Pc} {Z : List (Set ℝ)} (hY : s.1 = t.1 ++ Y)
    (hZ : s.2.1 = t.2.1 ++ Z) :
    statePhysicalSet x s = statePhysicalSet x t ∪ (⋃ q ∈ Y, q.1.tipSet q.2.1 q.2.2) ∪
      ⋃ a ∈ Z, ((↑) : ℝ → ℂ) '' a := by
  unfold statePhysicalSet
  rw [hY, hZ, biUnion_list_append, biUnion_list_append]
  ext z
  simp only [mem_union]
  tauto

open GW1Bookkeep in
/-- **The physical set of a walk that is done at a stage inside its program** is the physical part of that stage. -/
theorem physSet_walk_eq_of_done {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hn : n ≤ (boundaryWalkSpec b J θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) = stDone) :
    ExplState.physSet κ b J (boundaryWalkSpec b J θ true) D =
      statePhysicalSet 0 (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) := by
  rw [physSet_eq_statePhysicalSet, Lx.run_eq_of_done _ D hd _ hn]
  rfl

open GW1Bookkeep in
/-- **The two physical sets after the lockstep run**: if the correspondence with history holds at actual stage
`N + o` and relative stage `N`, and the actual walk is done there (hence also the relative one), then both physical
sets are the physical parts of the starting states, the paired pieces, and the connectors — the relative connectors
being the `ι`-images (right of `p`) of the actual ones. -/
theorem physSet_eq_of_accCorr {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {N o : ℕ}
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hc : AccCorr ι p L t₁ t₂ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N))
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone) :
    ∃ (X : List (Set ℝ)) (Y₁ Y₂ : List Pc), List.Forall₂ L Y₁ Y₂ ∧
      ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ =
        statePhysicalSet 0 t₁ ∪ (⋃ q ∈ Y₁, q.1.tipSet q.2.1 q.2.2) ∪ ⋃ a ∈ X, ((↑) : ℝ → ℂ) '' a ∧
      ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ =
        statePhysicalSet 0 t₂ ∪ (⋃ q ∈ Y₂, q.1.tipSet q.2.1 q.2.2) ∪
          ⋃ a ∈ X, ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici p)) := by
  obtain ⟨hst, ⟨X, hX₁, hX₂⟩, Y₁, Y₂, hY₁, hY₂, hY⟩ := hc
  refine ⟨X, Y₁, Y₂, hY, ?_, ?_⟩
  · rw [physSet_walk_eq_of_done hN₁ hd, statePhysicalSet_append hY₁ hX₁]
  · rw [physSet_walk_eq_of_done hN₂ (hst.2.1.trans hd), statePhysicalSet_append hY₂ hX₂]
    simp only [List.mem_map, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right]

end InteractingSLE.Theorem14.SB.Lk
