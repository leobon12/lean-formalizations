/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LsTr
import InteractingSLE.Spec.Supplement.SB2LkCorr

/-!
# The lockstep correspondence of the actual and the relative walk: one step

Packet PROVE-T14-SB2LIFT (round 10; item 3 of handoff §R9.2, the lockstep induction). The actual lower walk (data
`b₁`, genuine jumps `J₁`) and SB2(2)'s relative walk (data `b₂`, `J₂`) are compared step by step through the
right-ray correspondence `ι` (`RayCorr`, effective start `p ≥ R`). The state correspondence is

  **`StCorr ι p s₁ s₂`**: the relative point and right record are the `ι`-images of the actual ones (after `max · p`),
  and statuses and angles agree.

This file proves that every kind of step of the two walks preserves it:

* **`stCorr_contStep_thr`**: a connector step from a right threshold (`SB2LkCorr.contStep_corr`). The new relative
  connector is the `ι`-image of the part of the actual one right of `p`;
* **`stCorr_flowStep_arcM`**: a flow step at corresponding restart marks right of `R`. The seeds are admissible
  together (`launchReady_corr`). If they are, the hypotheses of `launch_corr` are needed: lifetimes infinite and zero
  together, right hits together, no left hits, and the new records corresponding;
* `stCorr_flowStep_of_done`, `stCorr_flowStep_of_dead`, `stCorr_contStep_of_done`, `stCorr_contStep_of_arcM`,
  `stCorr_contStep_of_dead`: the steps that leave both states unchanged (or only mark them dead).

The per-launch hypotheses are exactly what `lRecR_corr` (records) and `lHit_run_iff` (hits) reduce to the fill
correspondence of the two runs.
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

/-- **The state correspondence** of an actual and a relative walk state. -/
def StCorr (ι : ℝ → ℝ) (p : ℝ) (s₁ s₂ : ExplState) : Prop :=
  stPt s₂ = ι (max (stPt s₁) p) ∧ stStatus s₂ = stStatus s₁ ∧ stAngle s₂ = stAngle s₁ ∧
    stRecR s₂ = ι (max (stRecR s₁) p)

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {κ θ : ℝ} {p : ℝ} {s₁ s₂ : ExplState}

/-- **A connector step from a right threshold preserves the correspondence.** -/
theorem stCorr_contStep_thr (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hc : StCorr ι p s₁ s₂) (hRp : R ≤ p)
    (hp₁ : stPt s₁ ≤ p) (hgap : ∀ x ∈ restartSet κ b₁ J₁ s₁, p < x)
    (hst : stStatus s₁ = stThr (some true)) :
    StCorr ι p (ExplState.contStep κ b₁ J₁ s₁ none true) (ExplState.contStep κ b₂ J₂ s₂ none true) ∧
      ∃ a : Set ℝ, (ExplState.contStep κ b₁ J₁ s₁ none true).2.1 = s₁.2.1 ++ [a] ∧
        (ExplState.contStep κ b₂ J₂ s₂ none true).2.1 = s₂.2.1 ++ [ι '' (a ∩ Ici p)] := by
  obtain ⟨hpt, hstat, hθ, hrec⟩ := hc
  have hst₂ : stStatus s₂ = stThr (some true) := hstat.trans hst
  have hp₂ : stPt s₂ = ι p := by rw [hpt, max_eq_right hp₁]
  obtain ⟨h1, h2, h3, h4, h5⟩ := contStep_corr (κ := κ) h hθ hRp hp₁ hp₂ hgap hrec
    (contStep_thr_true' b₁ J₁ s₁ hst) (contStep_thr_true' b₂ J₂ s₂ hst₂)
  exact ⟨⟨h1, h2, h3, h4⟩, h5⟩

/-- **A flow step at corresponding restart marks right of `R` preserves the correspondence**, given the launch
observables in the admissible case. -/
theorem stCorr_flowStep_arcM (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hc : StCorr ι p s₁ s₂)
    (hst : stStatus s₁ = GW1W.stArcM true) (hpR : R < stPt s₁) (hp₁ : p ≤ stPt s₁) (k₁ k₂ : ℕ)
    {D₁ D₂ : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hlaunch : ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt s₁)) (rightLim b₁ (stPt s₁)) θ →
      (D₂.2 = ⊤ ↔ D₁.2 = ⊤) ∧ (D₂.2 = 0 ↔ D₁.2 = 0) ∧
      ((∃ x : ℝ, stRecR s₂ < x ∧ lHit (stChart s₂) ⊤ D₂ x) ↔ ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) ⊤ D₁ x) ∧
      (¬ ∃ x : ℝ, x < stRecL s₁ ∧ lHit (stChart s₁) ⊤ D₁ x) ∧
      (¬ ∃ x : ℝ, x < stRecL s₂ ∧ lHit (stChart s₂) ⊤ D₂ x) ∧
      (D₁.2 ≠ ⊤ → lRecR s₂ ⊤ D₂ = ι (max (lRecR s₁ ⊤ D₁) p))) :
    StCorr ι p (ExplState.flowStep κ b₁ false s₁ k₁ D₁ θ ⊤) (ExplState.flowStep κ b₂ false s₂ k₂ D₂ θ ⊤) := by
  obtain ⟨hpt, hstat, hθ, hrec⟩ := hc
  have hst₂ : stStatus s₂ = GW1W.stArcM true := hstat.trans hst
  have hpt' : stPt s₂ = ι (stPt s₁) := by rw [hpt, max_eq_left hp₁]
  obtain ⟨-, hseed⟩ := launchReady_corr (κ := κ) (θ := θ) h hst hst₂ hpt' hpR
  by_cases hadm : ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt s₁)) (rightLim b₁ (stPt s₁)) θ
  · have hadm₂ := hseed.2 hadm
    rw [GW1WalkExit.flowStep_of_launchReady (Or.inr ⟨hst, hadm⟩) k₁ D₁,
      GW1WalkExit.flowStep_of_launchReady (Or.inr ⟨hst₂, hadm₂⟩) k₂ D₂]
    obtain ⟨hT, h0, hR, hL₁, hL₂, hrec'⟩ := hlaunch hadm
    have htip₁ : stStatus s₁ ≠ .inr (.inl ()) := by rw [hst]; exact fun e => by cases e
    have htip₂ : stStatus s₂ ≠ .inr (.inl ()) := by rw [hst₂]; exact fun e => by cases e
    obtain ⟨e1, e2, e3, e4⟩ := launch_corr (θ := θ) k₁ k₂ htip₁ htip₂ hT h0 hR hL₁ hL₂ hpt hrec hrec'
    exact ⟨e3, e1, e2, e4⟩
  · have hadm₂ : ¬ ExplState.IsAdmissibleSeed κ (leftLim b₂ (stPt s₂)) (rightLim b₂ (stPt s₂)) θ :=
      fun h' => hadm (hseed.1 h')
    rw [flowStep_arcM_not hst hadm k₁ D₁ ⊤, flowStep_arcM_not hst₂ hadm₂ k₂ D₂ ⊤]
    exact ⟨hpt, hstat, hθ, hrec⟩

/-- A flow step from a finished state changes nothing. -/
theorem flowStep_of_done {b : ℝ → ℝ} {s : ExplState} (hs : stStatus s = stDone) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) : ExplState.flowStep κ b false s k D θ t = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at hs
  subst hs
  rfl

/-- A flow step from a dead state changes nothing. -/
theorem flowStep_of_dead {b : ℝ → ℝ} {s : ExplState} (hs : stStatus s = stDead) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) : ExplState.flowStep κ b false s k D θ t = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at hs
  subst hs
  rfl

/-- A connector step from a finished state changes nothing. -/
theorem contStep_of_done' {b : ℝ → ℝ} {J : Finset ℝ} {s : ExplState} (hs : stStatus s = stDone) (pref : Bool) :
    ExplState.contStep κ b J s none pref = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at hs
  subst hs
  rfl

/-- A connector step at a restart mark changes nothing. -/
theorem contStep_of_arcM {b : ℝ → ℝ} {J : Finset ℝ} {s : ExplState} {r : Bool}
    (hs : stStatus s = GW1W.stArcM r) (pref : Bool) : ExplState.contStep κ b J s none pref = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at hs
  subst hs
  rfl

/-- A connector step from a dead state only marks it dead. -/
theorem contStep_of_dead {b : ℝ → ℝ} {J : Finset ℝ} {s : ExplState} (hs : stStatus s = stDead) (pref : Bool) :
    stPt (ExplState.contStep κ b J s none pref) = stPt s ∧
      stStatus (ExplState.contStep κ b J s none pref) = stDead ∧
      stAngle (ExplState.contStep κ b J s none pref) = stAngle s ∧
      stRecR (ExplState.contStep κ b J s none pref) = stRecR s ∧
      (ExplState.contStep κ b J s none pref).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stCorr_flowStep_of_done (hc : StCorr ι p s₁ s₂) (hs : stStatus s₁ = stDone) (k₁ k₂ : ℕ)
    (D₁ D₂ : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) :
    StCorr ι p (ExplState.flowStep κ b₁ false s₁ k₁ D₁ θ t) (ExplState.flowStep κ b₂ false s₂ k₂ D₂ θ t) := by
  rw [flowStep_of_done hs, flowStep_of_done (hc.2.1.trans hs)]
  exact hc

theorem stCorr_flowStep_of_dead (hc : StCorr ι p s₁ s₂) (hs : stStatus s₁ = stDead) (k₁ k₂ : ℕ)
    (D₁ D₂ : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) :
    StCorr ι p (ExplState.flowStep κ b₁ false s₁ k₁ D₁ θ t) (ExplState.flowStep κ b₂ false s₂ k₂ D₂ θ t) := by
  rw [flowStep_of_dead hs, flowStep_of_dead (hc.2.1.trans hs)]
  exact hc

theorem stCorr_contStep_of_done (hc : StCorr ι p s₁ s₂) (hs : stStatus s₁ = stDone) (pref : Bool) :
    StCorr ι p (ExplState.contStep κ b₁ J₁ s₁ none pref) (ExplState.contStep κ b₂ J₂ s₂ none pref) := by
  rw [contStep_of_done' hs, contStep_of_done' (hc.2.1.trans hs)]
  exact hc

theorem stCorr_contStep_of_arcM {r : Bool} (hc : StCorr ι p s₁ s₂) (hs : stStatus s₁ = GW1W.stArcM r)
    (pref : Bool) :
    StCorr ι p (ExplState.contStep κ b₁ J₁ s₁ none pref) (ExplState.contStep κ b₂ J₂ s₂ none pref) := by
  rw [contStep_of_arcM hs, contStep_of_arcM (hc.2.1.trans hs)]
  exact hc

theorem stCorr_contStep_of_dead (hc : StCorr ι p s₁ s₂) (hs : stStatus s₁ = stDead) (pref : Bool) :
    StCorr ι p (ExplState.contStep κ b₁ J₁ s₁ none pref) (ExplState.contStep κ b₂ J₂ s₂ none pref) := by
  obtain ⟨a1, a2, a3, a4, -⟩ := contStep_of_dead (κ := κ) (b := b₁) (J := J₁) hs pref
  obtain ⟨c1, c2, c3, c4, -⟩ := contStep_of_dead (κ := κ) (b := b₂) (J := J₂) (hc.2.1.trans hs) pref
  obtain ⟨hpt, -, hθ, hrec⟩ := hc
  exact ⟨by rw [c1, a1, hpt], by rw [c2, a2], by rw [c3, a3, hθ], by rw [c4, a4, hrec]⟩

end InteractingSLE.Theorem14.SB.Lk
