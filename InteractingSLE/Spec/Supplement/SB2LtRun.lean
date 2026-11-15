/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LtStep

/-!
# The lockstep correspondence of the actual and the relative walk: the induction

Packet PROVE-T14-SB2LIFT (round 10; item 3 of handoff §R9.2). The actual lower walk runs the program
`boundaryWalkSpec b₁ J₁ θ true` with drivers `D₁`, and the relative walk runs `boundaryWalkSpec b₂ J₂ θ true` with
drivers `D₂`. Relative instruction `i` faces actual instruction `i + o`; the offset `o` is even, so flow faces flow
and connector faces connector.

* `stCorr_contStep_thr_gen`: the connector step from a right threshold, for any current point. The effective start
  is `max pt p`, with `pt ≤ recR`.
* **`StepOK`**: the data needed at one step, by the actual status:
  - flow: done, dead, or a restart mark right of `R` and of `p`, with the launch observables (`launch_corr`'s
    hypotheses) in the admissible case;
  - connector: done, dead, a mark, or a right threshold with no actual restart mark in `(pt, p]`.
* **`stCorr_run_of_steps`**: from the correspondence at a starting stage `i₀`, and `StepOK` at every later step while
  both programs still have instructions, the correspondence holds at every stage up to `N`.

The starting stage is the stage after the relative walk's first flow instruction, which launches from its root. It
is SB2(2)'s R-visit case (§R4.2) and enters as the hypothesis `h₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {κ θ : ℝ} {p : ℝ} {s₁ s₂ : ExplState}

theorem stPt_moveToEnd' (s : ExplState) (r : Bool) : stPt (ExplState.moveToEnd s r) = stPt s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem stRecR_moveToEnd' (s : ExplState) (r : Bool) : stRecR (ExplState.moveToEnd s r) = stRecR s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

/-- **A connector step from a right threshold, for any current point** (effective start `max pt p`). -/
theorem stCorr_contStep_thr_gen (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hc : StCorr ι p s₁ s₂) (hRp : R ≤ p)
    (hptrec : stPt s₁ ≤ stRecR s₁) (hgap : ∀ x ∈ restartSet κ b₁ J₁ s₁, p < x)
    (hst : stStatus s₁ = stThr (some true)) :
    StCorr ι p (ExplState.contStep κ b₁ J₁ s₁ none true) (ExplState.contStep κ b₂ J₂ s₂ none true) := by
  set p' := max (stPt s₁) p with hp'
  have hRp' : R ≤ p' := hRp.trans (le_max_right _ _)
  have hp'p : p ≤ p' := le_max_right _ _
  have hc' : StCorr ι p' s₁ s₂ := by
    obtain ⟨hpt, hstat, hθ, hrec⟩ := hc
    refine ⟨by rw [hpt, hp', ← max_assoc, max_self], hstat, hθ, ?_⟩
    rw [hrec, hp', ← max_assoc, max_eq_left hptrec]
  have hgap' : ∀ x ∈ restartSet κ b₁ J₁ s₁, p' < x := fun x hx => by
    have hx' := hx
    simp only [restartSet, Finset.mem_filter] at hx'
    exact max_lt hx'.2.1 (hgap x hx)
  obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := stCorr_contStep_thr (κ := κ) h hc' hRp' (le_max_left _ _) hgap' hst
  -- back from `p'` to `p`: the new point is beyond `p'` or stays at `p'`
  have hthr := contStep_thr_true' (κ := κ) b₁ J₁ s₁ hst
  have hback : ∀ y : ℝ, (y = stPt (ExplState.contStep κ b₁ J₁ s₁ none true) ∨
      y = stRecR (ExplState.contStep κ b₁ J₁ s₁ none true)) → max y p' = max y p := by
    intro y hy
    by_cases hC : (restartSet κ b₁ J₁ s₁).Nonempty
    · simp only [hthr, hC, ↓reduceDIte] at hy
      have hmin := hgap' _ (Finset.min'_mem _ hC)
      rcases hy with rfl | rfl
      · rw [stPt_moveAlong, max_eq_left hmin.le, max_eq_left (hp'p.trans hmin.le)]
      · rw [stRecR_moveAlong_true]
        rw [max_eq_left ((le_max_right _ _).trans' hmin.le), max_eq_left ((le_max_right _ _).trans'
          (hp'p.trans hmin.le))]
    · simp only [hthr, hC, ↓reduceDIte] at hy
      rcases hy with rfl | rfl
      · rw [stPt_moveToEnd', hp', ← max_assoc, max_self]
      · rw [stRecR_moveToEnd', hp', ← max_assoc, max_eq_left hptrec]
  exact ⟨by rw [h1, hback _ (Or.inl rfl)], h2, h3, by rw [h4, hback _ (Or.inr rfl)]⟩

/-- **The data needed at one step of the lockstep induction**, by the actual status (`flow`: a flow instruction). -/
def StepOK (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ) (p : ℝ) (flow : Bool)
    (s₁ s₂ : ExplState) (D₁ D₂ : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  if flow then
    stStatus s₁ = stDone ∨ stStatus s₁ = stDead ∨
      (stStatus s₁ = GW1W.stArcM true ∧ R < stPt s₁ ∧ p ≤ stPt s₁ ∧
        (ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt s₁)) (rightLim b₁ (stPt s₁)) θ →
          (D₂.2 = ⊤ ↔ D₁.2 = ⊤) ∧ (D₂.2 = 0 ↔ D₁.2 = 0) ∧
          ((∃ x : ℝ, stRecR s₂ < x ∧ lHit (stChart s₂) ⊤ D₂ x) ↔
            ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) ⊤ D₁ x) ∧
          (¬ ∃ x : ℝ, x < stRecL s₁ ∧ lHit (stChart s₁) ⊤ D₁ x) ∧
          (¬ ∃ x : ℝ, x < stRecL s₂ ∧ lHit (stChart s₂) ⊤ D₂ x) ∧
          (D₁.2 ≠ ⊤ → lRecR s₂ ⊤ D₂ = ι (max (lRecR s₁ ⊤ D₁) p))))
  else
    stStatus s₁ = stDone ∨ stStatus s₁ = stDead ∨ (∃ r, stStatus s₁ = GW1W.stArcM r) ∨
      (stStatus s₁ = stThr (some true) ∧ stPt s₁ ≤ stRecR s₁ ∧ ∀ x ∈ restartSet κ b₁ J₁ s₁, p < x)

/-- **One step of the lockstep induction.** -/
theorem stCorr_step (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hRp : R ≤ p) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k₁ k₂ : ℕ}
    (hk₁ : k₁ < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hk₂ : k₂ < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hpar : k₁ % 2 = k₂ % 2)
    (hc : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂))
    (hok : StepOK κ θ b₁ J₁ R ι p (k₂ % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₁)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ k₂) (D₁ k₁) (D₂ k₂)) :
    StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k₁ + 1))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k₂ + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one k₂ with hev | hodd
  · have hev₁ : k₁ % 2 = 0 := hpar.trans hev
    rw [run_succ_walk_flow hk₁ hev₁, run_succ_walk_flow hk₂ hev]
    simp only [StepOK, hev, decide_true, ↓reduceIte] at hok
    rcases hok with hd | hd | ⟨hst, hpR, hp₁, hl⟩
    · exact stCorr_flowStep_of_done hc hd _ _ _ _ _
    · exact stCorr_flowStep_of_dead hc hd _ _ _ _ _
    · exact stCorr_flowStep_arcM h hc hst hpR hp₁ k₁ k₂ hl
  · have hodd₁ : k₁ % 2 = 1 := hpar.trans hodd
    rw [run_succ_walk_cont hk₁ hodd₁, run_succ_walk_cont hk₂ hodd]
    simp only [StepOK, hodd, Nat.one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte] at hok
    rcases hok with hd | hd | ⟨r, hr⟩ | ⟨hst, hptrec, hgap⟩
    · exact stCorr_contStep_of_done hc hd true
    · exact stCorr_contStep_of_dead hc hd true
    · exact stCorr_contStep_of_arcM hc hr true
    · exact stCorr_contStep_thr_gen h hc hRp hptrec hgap hst

/-- **The lockstep induction**: from the correspondence at stage `i₀` and the step data while both programs have
instructions, the correspondence holds at every stage up to `N`. -/
theorem stCorr_run_of_steps (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hRp : R ≤ p) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (o i₀ N : ℕ) (hpar : o % 2 = 0)
    (hlen : ∀ i, i₀ ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (h₀ : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i₀))
    (hstep : ∀ i, i₀ ≤ i → i < N →
      StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι p (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i)) :
    ∀ i, i₀ ≤ i → i ≤ N → StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact fun _ => h₀
  | succ i hi ih =>
    intro hiN
    have hiN' : i < N := hiN
    have hc := ih hiN'.le
    obtain ⟨hk₁, hk₂⟩ := hlen i hi hiN'
    have hpar' : (i + o) % 2 = i % 2 := by omega
    have := stCorr_step (κ := κ) (θ := θ) h hRp hk₁ hk₂ hpar' hc (hstep i hi hiN' hc)
    rwa [show i + o + 1 = i + 1 + o by omega] at this

end InteractingSLE.Theorem14.SB.Lk
