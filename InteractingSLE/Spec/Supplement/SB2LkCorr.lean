/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveChart
import InteractingSLE.Spec.Supplement.GW1WalkExitRestart

/-!
# SB2(2)'s lifted walk: the connector step under the boundary correspondence of the right rays

Packet PROVE-T14-SB2LIFT (round 5, step P3 of the geometric half `Lk.SB2LowerRelWalkStatement`; handoff §R4.2).
The frozen run keeps its current point, its records and its connectors in its own original frame, and a connector
from a right threshold (or from a zero-lifetime root with a low right height) runs right to the least genuine jump
`x > pt` with `−λ < b(x+) + θχ` (`GW1W.restartSet`). The relative lower walk of SB2(2) runs on the relative data
`affData 1 m b'`. Right of `0` that data is the actual data `b` right of `R = max(A ∩ ℝ)`, read through the chart's
real boundary map. That map is SB2LOW's `ROrig`; here it is an increasing `ι : [R, ∞) → [0, ∞)` with `ι R = 0`. This
file proves the deterministic connector correspondence:

* **`RayCorr`**: the correspondence: `ι` is strictly increasing on `[R, ∞)`, `ι R = 0`, onto `[0, ∞)`, carries the
  one-sided limits, and carries the genuine jumps right of `R`. Also `RayCorr.image_Icc`, `RayCorr.image_Ici`;
* **`mem_restartSet_corr`**, **`restartSet_corr_nonempty_iff`**, **`restartSet_corr_min'`**: the restart marks
  correspond. Their hypotheses are a relative point `ι p` at an effective actual start `p ≥ R`, no actual restart mark
  in `(pt, p]`, and equal angles;
* **`contStep_corr`**: one connector step of both runs. The new points (after `max · p`), statuses, angles and right
  records (after `max · p`) correspond, and the relative connector is the `ι`-image of the part of the actual connector
  right of `p`.

* **`launchReady_corr`**, `flowStep_arcM_not`: at corresponding restart marks right of `R` both runs launch, or
  neither does and the flow instruction changes nothing;
* **`launch_corr`** (bookkeeping of `ExplState.launch` at the walk's horizon `⊤`): if the two lifetimes are infinite
  together and zero together, the right and left hits beyond the records occur together, and the new right records
  correspond, then the post-launch statuses, angles, points and right records correspond.

With `p = pt` this is every later stage; with `p = R` it is the first relative connector when `R` lies inside an actual
connector (the part of `B` before `R` is erased).
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

/-- **The boundary correspondence of the right rays** `[R, ∞)` of the actual data `b₁` (genuine jumps of `J₁`) and
`[0, ∞)` of the relative data `b₂` (genuine jumps of `J₂`): an increasing bijection carrying the right limits and the
genuine jumps. -/
structure RayCorr (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ) : Prop where
  mono : StrictMonoOn ι (Ici R)
  map_base : ι R = 0
  surj : ∀ y, 0 ≤ y → ∃ x, R ≤ x ∧ ι x = y
  rightLim_eq : ∀ x, R ≤ x → rightLim b₂ (ι x) = rightLim b₁ x
  leftLim_eq : ∀ x, R < x → leftLim b₂ (ι x) = leftLim b₁ x
  mem_jumpSet_iff : ∀ x, R < x → (ι x ∈ jumpSet b₂ J₂ ↔ x ∈ jumpSet b₁ J₁)

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ}

namespace RayCorr

theorem nonneg (h : RayCorr b₁ J₁ b₂ J₂ R ι) {x : ℝ} (hx : R ≤ x) : 0 ≤ ι x :=
  h.map_base ▸ h.mono.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx

theorem pos (h : RayCorr b₁ J₁ b₂ J₂ R ι) {x : ℝ} (hx : R < x) : 0 < ι x :=
  h.map_base ▸ h.mono (mem_Ici.2 le_rfl) (mem_Ici.2 hx.le) hx

theorem lt_iff (h : RayCorr b₁ J₁ b₂ J₂ R ι) {x y : ℝ} (hx : R ≤ x) (hy : R ≤ y) : ι x < ι y ↔ x < y :=
  h.mono.lt_iff_lt (mem_Ici.2 hx) (mem_Ici.2 hy)

theorem le_iff (h : RayCorr b₁ J₁ b₂ J₂ R ι) {x y : ℝ} (hx : R ≤ x) (hy : R ≤ y) : ι x ≤ ι y ↔ x ≤ y :=
  h.mono.le_iff_le (mem_Ici.2 hx) (mem_Ici.2 hy)

/-- Every relative point `y ≥ ι a` (with `a ≥ R`) is the image of an actual point `≥ a`. -/
theorem exists_ge (h : RayCorr b₁ J₁ b₂ J₂ R ι) {a y : ℝ} (ha : R ≤ a) (hy : ι a ≤ y) :
    ∃ x, a ≤ x ∧ ι x = y := by
  obtain ⟨x, hx, rfl⟩ := h.surj y ((h.nonneg ha).trans hy)
  exact ⟨x, (h.le_iff ha hx).1 hy, rfl⟩

theorem image_Icc (h : RayCorr b₁ J₁ b₂ J₂ R ι) {a x : ℝ} (ha : R ≤ a) (hax : a ≤ x) :
    ι '' Icc a x = Icc (ι a) (ι x) := by
  ext y
  constructor
  · rintro ⟨z, ⟨hz₁, hz₂⟩, rfl⟩
    exact ⟨(h.le_iff ha (ha.trans hz₁)).2 hz₁, (h.le_iff (ha.trans hz₁) (ha.trans hax)).2 hz₂⟩
  · rintro ⟨hy₁, hy₂⟩
    obtain ⟨z, hz, rfl⟩ := h.exists_ge ha hy₁
    exact ⟨z, ⟨hz, (h.le_iff (ha.trans hz) (ha.trans hax)).1 hy₂⟩, rfl⟩

theorem image_Ici (h : RayCorr b₁ J₁ b₂ J₂ R ι) {a : ℝ} (ha : R ≤ a) : ι '' Ici a = Ici (ι a) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (h.le_iff ha (ha.trans hz)).2 hz
  · intro hy
    obtain ⟨z, hz, rfl⟩ := h.exists_ge ha hy
    exact ⟨z, hz, rfl⟩

end RayCorr

/-! ### The restart marks -/

section Restart

variable {κ : ℝ} {s₁ s₂ : ExplState} {p : ℝ}

/-- **The relative restart marks are the images of the actual ones** (relative point `ι p` at an effective actual
start `p ≥ R` not left of the actual point, no actual restart mark in `(pt, p]`, equal angles). -/
theorem mem_restartSet_corr (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hθ : stAngle s₂ = stAngle s₁) (hRp : R ≤ p)
    (hp₁ : stPt s₁ ≤ p) (hp₂ : stPt s₂ = ι p) (hgap : ∀ x ∈ restartSet κ b₁ J₁ s₁, p < x) {y : ℝ} :
    y ∈ restartSet κ b₂ J₂ s₂ ↔ ∃ x ∈ restartSet κ b₁ J₁ s₁, ι x = y := by
  simp only [restartSet, Finset.mem_filter]
  constructor
  · rintro ⟨hyJ, hpy, hyb⟩
    rw [hp₂] at hpy
    obtain ⟨x, hpx, rfl⟩ := h.exists_ge hRp hpy.le
    have hpx' : p < x := (h.lt_iff hRp (hRp.trans hpx)).1 hpy
    have hRx : R < x := lt_of_le_of_lt hRp hpx'
    refine ⟨x, ⟨(h.mem_jumpSet_iff x hRx).1 hyJ, lt_of_le_of_lt hp₁ hpx', ?_⟩, rfl⟩
    rwa [h.rightLim_eq x hRx.le, hθ] at hyb
  · rintro ⟨x, hx, rfl⟩
    have hpx := hgap x (by simp only [restartSet, Finset.mem_filter]; exact hx)
    obtain ⟨hxJ, -, hxb⟩ := hx
    have hRx : R < x := lt_of_le_of_lt hRp hpx
    refine ⟨(h.mem_jumpSet_iff x hRx).2 hxJ, ?_, ?_⟩
    · rw [hp₂]
      exact (h.lt_iff hRp hRx.le).2 hpx
    · rw [h.rightLim_eq x hRx.le, hθ]
      exact hxb

theorem restartSet_corr_nonempty_iff (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hθ : stAngle s₂ = stAngle s₁) (hRp : R ≤ p)
    (hp₁ : stPt s₁ ≤ p) (hp₂ : stPt s₂ = ι p) (hgap : ∀ x ∈ restartSet κ b₁ J₁ s₁, p < x) :
    (restartSet κ b₂ J₂ s₂).Nonempty ↔ (restartSet κ b₁ J₁ s₁).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, -⟩ := (mem_restartSet_corr h hθ hRp hp₁ hp₂ hgap).1 hy
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨ι x, (mem_restartSet_corr h hθ hRp hp₁ hp₂ hgap).2 ⟨x, hx, rfl⟩⟩

/-- **The relative restart mark is the image of the actual one.** -/
theorem restartSet_corr_min' (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hθ : stAngle s₂ = stAngle s₁) (hRp : R ≤ p)
    (hp₁ : stPt s₁ ≤ p) (hp₂ : stPt s₂ = ι p) (hgap : ∀ x ∈ restartSet κ b₁ J₁ s₁, p < x)
    (hC₁ : (restartSet κ b₁ J₁ s₁).Nonempty) (hC₂ : (restartSet κ b₂ J₂ s₂).Nonempty) :
    (restartSet κ b₂ J₂ s₂).min' hC₂ = ι ((restartSet κ b₁ J₁ s₁).min' hC₁) := by
  have hiff := fun y => mem_restartSet_corr (y := y) h hθ hRp hp₁ hp₂ hgap
  have hx₁ := Finset.min'_mem _ hC₁
  have hR₁ : R ≤ (restartSet κ b₁ J₁ s₁).min' hC₁ := hRp.trans (hgap _ hx₁).le
  refine le_antisymm (Finset.min'_le _ _ ((hiff _).2 ⟨_, hx₁, rfl⟩)) (Finset.le_min' _ _ _ fun y hy => ?_)
  obtain ⟨x, hx, rfl⟩ := (hiff y).1 hy
  exact (h.le_iff hR₁ (hRp.trans (hgap x hx).le)).2 (Finset.min'_le _ _ hx)

/-- **One connector step of both runs** (each in the form "move right to the least restart mark, or to the end"):
the new points and right records correspond after `max · p`, the statuses and angles agree, and the relative
connector is the `ι`-image of the part of the actual connector right of `p`. -/
theorem contStep_corr (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hθ : stAngle s₂ = stAngle s₁) (hRp : R ≤ p)
    (hp₁ : stPt s₁ ≤ p) (hp₂ : stPt s₂ = ι p) (hgap : ∀ x ∈ restartSet κ b₁ J₁ s₁, p < x)
    (hrec : stRecR s₂ = ι (max (stRecR s₁) p)) {t₁ t₂ : ExplState}
    (ht₁ : t₁ = if hC : (restartSet κ b₁ J₁ s₁).Nonempty then
      ExplState.moveAlong s₁ true ((restartSet κ b₁ J₁ s₁).min' hC) true else ExplState.moveToEnd s₁ true)
    (ht₂ : t₂ = if hC : (restartSet κ b₂ J₂ s₂).Nonempty then
      ExplState.moveAlong s₂ true ((restartSet κ b₂ J₂ s₂).min' hC) true else ExplState.moveToEnd s₂ true) :
    stPt t₂ = ι (max (stPt t₁) p) ∧ stStatus t₂ = stStatus t₁ ∧ stAngle t₂ = stAngle t₁ ∧
      stRecR t₂ = ι (max (stRecR t₁) p) ∧
      ∃ a : Set ℝ, t₁.2.1 = s₁.2.1 ++ [a] ∧ t₂.2.1 = s₂.2.1 ++ [ι '' (a ∩ Ici p)] := by
  by_cases hC₁ : (restartSet κ b₁ J₁ s₁).Nonempty
  · have hC₂ := (restartSet_corr_nonempty_iff h hθ hRp hp₁ hp₂ hgap).2 hC₁
    have hmin := restartSet_corr_min' h hθ hRp hp₁ hp₂ hgap hC₁ hC₂
    have hpx : p < (restartSet κ b₁ J₁ s₁).min' hC₁ := hgap _ (Finset.min'_mem _ hC₁)
    simp only [hC₁, ↓reduceDIte] at ht₁
    simp only [hC₂, ↓reduceDIte, hmin] at ht₂
    subst ht₁ ht₂
    generalize (restartSet κ b₁ J₁ s₁).min' hC₁ = x at hpx ⊢
    have hRx : R ≤ x := hRp.trans hpx.le
    obtain ⟨pc₁, ac₁, rt₁, la₁, ch₁, st₁, pt₁, an₁, rR₁, rL₁⟩ := s₁
    obtain ⟨pc₂, ac₂, rt₂, la₂, ch₂, st₂, pt₂, an₂, rR₂, rL₂⟩ := s₂
    change an₂ = an₁ at hθ
    change pt₁ ≤ p at hp₁
    change pt₂ = ι p at hp₂
    change rR₂ = ι (max rR₁ p) at hrec
    refine ⟨?_, rfl, hθ, ?_, Icc pt₁ x, rfl, ?_⟩
    · show ι x = ι (max x p)
      rw [max_eq_left hpx.le]
    · show max rR₂ (ι x) = ι (max (max rR₁ x) p)
      rw [hrec]
      have hm1 : R ≤ max rR₁ p := hRp.trans (le_max_right _ _)
      have hmax : max (ι (max rR₁ p)) (ι x) = ι (max (max rR₁ p) x) := by
        rcases le_total (max rR₁ p) x with hle | hle
        · rw [max_eq_right hle, max_eq_right ((h.le_iff hm1 hRx).2 hle)]
        · rw [max_eq_left hle, max_eq_left ((h.le_iff hRx hm1).2 hle)]
      have e1 : max (max rR₁ p) x = max rR₁ x := by rw [max_assoc, max_eq_right hpx.le]
      have e2 : max (max rR₁ x) p = max rR₁ x := max_eq_left (hpx.le.trans (le_max_right _ _))
      rw [hmax, e1, e2]
    · show ac₂ ++ [Icc pt₂ (ι x)] = ac₂ ++ [ι '' (Icc pt₁ x ∩ Ici p)]
      have e : Icc pt₁ x ∩ Ici p = Icc p x := by
        ext z
        simp only [mem_inter_iff, mem_Icc, mem_Ici]
        exact ⟨fun hz => ⟨hz.2, hz.1.2⟩, fun hz => ⟨⟨hp₁.trans hz.1, hz.2⟩, hz.1⟩⟩
      rw [e, h.image_Icc hRp hpx.le, hp₂]
  · have hC₂ : ¬ (restartSet κ b₂ J₂ s₂).Nonempty :=
      fun h2 => hC₁ ((restartSet_corr_nonempty_iff h hθ hRp hp₁ hp₂ hgap).1 h2)
    simp only [hC₁, ↓reduceDIte] at ht₁
    simp only [hC₂, ↓reduceDIte] at ht₂
    subst ht₁ ht₂
    obtain ⟨pc₁, ac₁, rt₁, la₁, ch₁, st₁, pt₁, an₁, rR₁, rL₁⟩ := s₁
    obtain ⟨pc₂, ac₂, rt₂, la₂, ch₂, st₂, pt₂, an₂, rR₂, rL₂⟩ := s₂
    change an₂ = an₁ at hθ
    change pt₁ ≤ p at hp₁
    change pt₂ = ι p at hp₂
    change rR₂ = ι (max rR₁ p) at hrec
    refine ⟨?_, rfl, hθ, hrec, Ici pt₁, rfl, ?_⟩
    · show pt₂ = ι (max pt₁ p)
      rw [max_eq_right hp₁, hp₂]
    · show ac₂ ++ [Ici pt₂] = ac₂ ++ [ι '' (Ici pt₁ ∩ Ici p)]
      have e : Ici pt₁ ∩ Ici p = Ici p := by
        ext z
        simp only [mem_inter_iff, mem_Ici]
        exact ⟨fun hz => hz.2, fun hz => ⟨hp₁.trans hz, hz⟩⟩
      rw [e, h.image_Ici hRp, hp₂]

end Restart

/-! ### The flow instruction at a restart mark -/

section Mark

open GW1WalkExit

variable {κ θ : ℝ} {s₁ s₂ : ExplState}

/-- **At a restart mark with an inadmissible seed the flow instruction changes nothing.** -/
theorem flowStep_arcM_not {b : ℝ → ℝ} {s : ExplState} (hst : stStatus s = GW1W.stArcM true)
    (hn : ¬ ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) : ExplState.flowStep κ b false s k D θ t = s := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  change status = _ at hst
  subst hst
  simp only [ExplState.flowStep, Bool.false_eq_true, ↓reduceIte]
  split_ifs with h
  · exact absurd h hn
  · rfl

/-- **At corresponding restart marks right of `R` the seeds are admissible together.** -/
theorem launchReady_corr (h : RayCorr b₁ J₁ b₂ J₂ R ι) (hst₁ : stStatus s₁ = GW1W.stArcM true)
    (hst₂ : stStatus s₂ = GW1W.stArcM true) (hpt : stPt s₂ = ι (stPt s₁)) (hR : R < stPt s₁) :
    (LaunchReady κ b₂ θ true s₂ ↔ LaunchReady κ b₁ θ true s₁) ∧
      (ExplState.IsAdmissibleSeed κ (leftLim b₂ (stPt s₂)) (rightLim b₂ (stPt s₂)) θ ↔
        ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt s₁)) (rightLim b₁ (stPt s₁)) θ) := by
  have hseed : ExplState.IsAdmissibleSeed κ (leftLim b₂ (stPt s₂)) (rightLim b₂ (stPt s₂)) θ ↔
      ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt s₁)) (rightLim b₁ (stPt s₁)) θ := by
    rw [hpt, h.leftLim_eq _ hR, h.rightLim_eq _ hR.le]
  refine ⟨?_, hseed⟩
  have hroot₁ : stStatus s₁ ≠ .inl () := by rw [hst₁]; exact fun e => by cases e
  have hroot₂ : stStatus s₂ ≠ .inl () := by rw [hst₂]; exact fun e => by cases e
  unfold LaunchReady
  simp only [hst₁, hst₂, true_and]
  constructor
  · rintro (e | hs)
    · exact absurd (hst₂ ▸ e) hroot₂
    · exact Or.inr (hseed.1 hs)
  · rintro (e | hs)
    · exact absurd (hst₁ ▸ e) hroot₁
    · exact Or.inr (hseed.2 hs)

end Mark

/-! ### The launch step -/

section Launch

variable {s₁ s₂ : ExplState} {p θ : ℝ}

/-- **The bookkeeping of a launch at the walk's horizon** for two runs whose launch observables correspond. -/
theorem launch_corr (k₁ k₂ : ℕ) {D₁ D₂ : (ℝ≥0 → ℝ) × ℝ≥0∞} (htip₁ : stStatus s₁ ≠ .inr (.inl ()))
    (htip₂ : stStatus s₂ ≠ .inr (.inl ())) (hT : D₂.2 = ⊤ ↔ D₁.2 = ⊤) (h0 : D₂.2 = 0 ↔ D₁.2 = 0)
    (hR : (∃ x : ℝ, stRecR s₂ < x ∧ lHit (stChart s₂) ⊤ D₂ x) ↔ ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) ⊤ D₁ x)
    (hL₁ : ¬ ∃ x : ℝ, x < stRecL s₁ ∧ lHit (stChart s₁) ⊤ D₁ x)
    (hL₂ : ¬ ∃ x : ℝ, x < stRecL s₂ ∧ lHit (stChart s₂) ⊤ D₂ x)
    (hpt : stPt s₂ = ι (max (stPt s₁) p)) (hrec : stRecR s₂ = ι (max (stRecR s₁) p))
    (hrec' : D₁.2 ≠ ⊤ → lRecR s₂ ⊤ D₂ = ι (max (lRecR s₁ ⊤ D₁) p)) :
    stStatus (ExplState.launch s₂ k₂ D₂ θ ⊤) = stStatus (ExplState.launch s₁ k₁ D₁ θ ⊤) ∧
      stAngle (ExplState.launch s₂ k₂ D₂ θ ⊤) = stAngle (ExplState.launch s₁ k₁ D₁ θ ⊤) ∧
      stPt (ExplState.launch s₂ k₂ D₂ θ ⊤) = ι (max (stPt (ExplState.launch s₁ k₁ D₁ θ ⊤)) p) ∧
      stRecR (ExplState.launch s₂ k₂ D₂ θ ⊤) = ι (max (stRecR (ExplState.launch s₁ k₁ D₁ θ ⊤)) p) := by
  by_cases hT₁ : D₁.2 = ⊤
  · have hT₂ : D₂.2 = ⊤ := hT.2 hT₁
    have e₁ := launch_eq_of_top s₁ k₁ D₁ θ ⊤ (by rw [hT₁, min_self])
    have e₂ := launch_eq_of_top s₂ k₂ D₂ θ ⊤ (by rw [hT₂, min_self])
    rw [e₁.2.2.2.2.1, e₂.2.2.2.2.1, e₁.2.1, e₂.2.1, e₁.2.2.2.2.2, e₂.2.2.2.2.2, e₁.2.2.1, e₂.2.2.1]
    exact ⟨rfl, rfl, hpt, hrec⟩
  · have hT₂ : D₂.2 ≠ ⊤ := fun h => hT₁ (hT.1 h)
    have e₁ := launch_eq_of_ne_top s₁ k₁ D₁ θ ⊤ (by rwa [min_eq_right le_top])
    have e₂ := launch_eq_of_ne_top s₂ k₂ D₂ θ ⊤ (by rwa [min_eq_right le_top])
    rw [e₁.2.2.2.2.1, e₂.2.2.2.2.1, e₁.2.1, e₂.2.1, e₁.2.2.2.2.2, e₂.2.2.2.2.2, e₁.2.2.1, e₂.2.2.1]
    have hnlt₁ : ¬ (⊤ : ℝ≥0∞) < D₁.2 := not_lt.2 le_top
    have hnlt₂ : ¬ (⊤ : ℝ≥0∞) < D₂.2 := not_lt.2 le_top
    refine ⟨?_, rfl, ?_, hrec' hT₁⟩
    · unfold lStatus
      simp only [hnlt₁, hnlt₂, ↓reduceIte]
      by_cases h0₁ : D₁.2 = 0
      · have h0₂ : D₂.2 = 0 := h0.2 h0₁
        simp only [h0₁, h0₂, ↓reduceIte]
      · have h0₂ : D₂.2 ≠ 0 := fun h => h0₁ (h0.1 h)
        simp only [h0₁, h0₂, ↓reduceIte, hL₁, hL₂]
        by_cases hR₁ : ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) ⊤ D₁ x
        · simp only [hR₁, hR.2 hR₁, ↓reduceIte]
        · have hR₂ : ¬ ∃ x : ℝ, stRecR s₂ < x ∧ lHit (stChart s₂) ⊤ D₂ x := fun h => hR₁ (hR.1 h)
          simp only [hR₁, hR₂, ↓reduceIte]
    · unfold lPt
      simp only [hnlt₁, hnlt₂, ↓reduceIte]
      by_cases h0₁ : D₁.2 = 0
      · simp only [h0₁, h0.2 h0₁, ↓reduceIte]
        exact hpt
      · have h0₂ : D₂.2 ≠ 0 := fun h => h0₁ (h0.1 h)
        simp only [h0₁, h0₂, ↓reduceIte, hL₁, hL₂]
        by_cases hR₁ : ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) ⊤ D₁ x
        · simp only [hR₁, hR.2 hR₁, ↓reduceIte]
          exact hrec' hT₁
        · have hR₂ : ¬ ∃ x : ℝ, stRecR s₂ < x ∧ lHit (stChart s₂) ⊤ D₂ x := fun h => hR₁ (hR.1 h)
          simp only [hR₁, hR₂, ↓reduceIte]
          exact hpt

end Launch

end InteractingSLE.Theorem14.SB.Lk
