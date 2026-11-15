/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KWord
import InteractingSLE.Spec.Supplement.GW1ActiveChartL
import InteractingSLE.Spec.Supplement.GW1ActiveLaw

/-!
# The lower walk's left side: the inward left profile and the original word on the untouched left ray

Packet PROVE-T14-SB2FIN5, step (b) of the plan for SB2(1)'s active word. GW1's invariant `GW1W.RInv` for the right
(lower) walk controls the word right of the right record. SB2(1)'s active word needs the left side: left of the left
record the physical ray is untouched, its chart image is increasing and negative (`LLeft`, the inward mirror of
`GW1W.RRight`), and there the staged word is the original word (`GW1W.LOrig`).

* `LLeft`; **`lLeft_launch`**: every launch of a regular piece with a good record keeps `LLeft`, and left of the new
  left record the new profile is the real flow of the old one at alive points (the relation `GW1W.lOrig_of_rel` uses);
* **`lOrig_of_rel'`**: `GW1W.lOrig_of_rel` from `LLeft` (it only uses the profile's monotonicity and sign).

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

namespace InteractingSLE.Theorem14.GW1W

open Exist Exist.StagedLaw Exist.Staged Restart

/-- **The inward left profile of a state** (the mirror of `RRight`): left of the left record the chart is increasing,
continuous and unbounded below on the real line, with negative values (read through the reflected profile `lProf`). -/
def LLeft (s : ExplState) : Prop :=
  RightGood (lProf (stChart s)) (-stRecL s) ∧ ∀ x, -stRecL s < x → 0 < lProf (stChart s) x

theorem LLeft.strictMonoOn {s : ExplState} (hs : LLeft s) : StrictMonoOn (rProf (stChart s)) (Iio (stRecL s)) := by
  intro x hx y hy hxy
  have h := hs.1.1 (show -stRecL s < -y by have : y < stRecL s := hy; linarith)
    (show -stRecL s < -x by have : x < stRecL s := hx; linarith) (by linarith : -y < -x)
  simp only [lProf_eq, neg_neg] at h
  linarith

theorem LLeft.neg {s : ExplState} (hs : LLeft s) {x : ℝ} (hx : x < stRecL s) : rProf (stChart s) x < 0 := by
  have h := hs.2 (-x) (by linarith)
  simp only [lProf_eq, neg_neg] at h
  linarith

theorem LProf.lLeft {s : ExplState} (hs : LProf s) : LLeft s := ⟨hs.2.1, hs.2.2.1⟩

variable {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The inward left profile after a launch** with a good record at a finite stop (the mirror of `rRight_launch`,
with the relation of `lProf_launch`): it stays good and negative left of the new left record, and there the new profile
is the real flow of the old one at alive points. -/
theorem lLeft_launch (hc : IsRealChart (stChart s)) (hs : LLeft s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    IsRealChart (stChart (ExplState.launch s k D θ ⊤)) ∧ LLeft (ExplState.launch s k D θ ⊤) ∧
      ∀ x, x < stRecL (ExplState.launch s k D θ ⊤) →
        x < stRecL s ∧ (∃ u, IsForwardSol (rdrv (recOf ⊤ D)) (rProf (stChart s) x : ℂ) (rtime (recOf ⊤ D)) u) ∧
        rProf (stChart (ExplState.launch s k D θ ⊤)) x =
          (fwdMap (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) (rProf (stChart s) x)).re := by
  obtain ⟨hm, hpos⟩ := hs
  obtain ⟨hch, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  have hWr : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  rw [hWr, rtime_recOf]
  set W := stopDrv ⊤ D with hWdef
  set T := stopTime ⊤ D with hTdef
  have hT0 : 0 ≤ T := stopTime_nonneg ⊤ D
  have hH := (isRealFlow_stop hreg hgood).2
  set A' : ℝ → Prop := fun y : ℝ => ∃ u, IsForwardSol W ((-y : ℝ) : ℂ) T u with hA'def
  set f' : ℝ → ℝ := fun y => -(fwdMap W T ((-y : ℝ) : ℂ)).re with hf'def
  set m := lProf (stChart s) with hmdef
  have hrecL' : -stRecL (ExplState.launch s k D θ ⊤) = newRec m (-stRecL s) A' := by
    rw [hrecL, lRecL_eq_newRec hc, neg_neg]
  have hprofR : ∀ x, rProf (stChart (ExplState.launch s k D θ ⊤)) x = (fwdMap W T (rProf (stChart s) x)).re := by
    intro x
    rw [hch]
    change (fwdMap W T ((stChart s).1 x)).re = _
    rw [hc.eq_ofReal x]
  have hprofL : lProf (stChart (ExplState.launch s k D θ ⊤)) = fun u => f' (m u) := by
    funext u
    rw [lProf_eq, hprofR]
    change -(fwdMap W T (rProf (stChart s) (-u) : ℂ)).re = -(fwdMap W T ((-(lProf (stChart s) u) : ℝ) : ℂ)).re
    rw [lProf_eq, neg_neg]
  have hle := le_newRec hm hH
  refine ⟨fun x => ?_, ⟨?_, fun u hu => ?_⟩, fun x hx => ?_⟩
  · rw [hch]
    change (fwdMap W T ((stChart s).1 x)).im = 0
    rw [hc.eq_ofReal x]
    exact im_fwdMap_ofReal W hT0 _
  · rw [hprofL, hrecL']
    exact rightGood_comp hm hH
  · rw [hrecL'] at hu
    obtain ⟨h0, hA⟩ := pos_alive_of_newRec_lt hm hH hu
    rw [hprofL]
    exact hH.2.2.2.1 _ h0 hA
  · have hu : newRec m (-stRecL s) A' < -x := by rw [← hrecL']; linarith
    obtain ⟨-, hA⟩ := pos_alive_of_newRec_lt hm hH hu
    refine ⟨by linarith [hle.trans_lt hu], ?_, hprofR x⟩
    have e : ((-(m (-x)) : ℝ) : ℂ) = (rProf (stChart s) x : ℂ) := by rw [hmdef, lProf_eq, neg_neg, neg_neg]
    rw [← e]
    exact hA

/-- **The original word survives on the new left ray** (`lOrig_of_rel` from the inward profile `LLeft`). -/
theorem lOrig_of_rel' {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} (hs : LLeft s) (hO : LOrig b jumps β s)
    {s₁ : ExplState} {r : RecData} (θ : ℝ)
    (hrel : LLeft s₁ ∧ ∀ x, x < stRecL s₁ → x < stRecL s ∧
      (∃ u, IsForwardSol (rdrv r) (rProf (stChart s) x : ℂ) (rtime r) u) ∧
      rProf (stChart s₁) x = (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x)).re) :
    LOrig b jumps (stopWord κ (β, θ, r)) s₁ := by
  obtain ⟨hs₁, hrel⟩ := hrel
  set γ := stopWord κ (β, θ, r) with hγ
  set m₁ := rProf (stChart s₁) with hm₁
  intro x hx hxJ hzJ
  have hc₁ : ContinuousAt m₁ x := by
    have hcl : ContinuousAt (lProf (stChart s₁)) (-x) :=
      hs₁.1.2.1.continuousAt (Ioi_mem_nhds (by linarith))
    have : m₁ = fun y => -lProf (stChart s₁) (-y) := by
      funext y; rw [hm₁, lProf_eq, neg_neg, neg_neg]
    rw [this]
    exact (hcl.comp (by simpa using continuous_neg.continuousAt (x := x))).neg
  have hP : ∀ᶠ x' in 𝓝 x, x' < stRecL s₁ ∧ b x' = b x ∧ m₁ x' ∉ γ.jumps ∧ γ.fn (m₁ x') = γ.fn (m₁ x) := by
    have h1 := hc₁.eventually (γ.isPiecewiseConstantBoundaryData (m₁ x) hzJ)
    have h2 := hc₁.eventually ((γ.jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds hzJ)
    filter_upwards [Iio_mem_nhds hx, hb x hxJ, h1, h2] with x' h0 h3 h4 h5
    exact ⟨h0, h3, h5, h4⟩
  obtain ⟨x', hx'R, hx'J, hmx'J, hx'R₁, hbx', hm₁J, hfn⟩ :=
    exists_near_avoid_left hs.strictMonoOn (hrel x hx).1 jumps β.jumps hP
  obtain ⟨-, hal, heq⟩ := hrel x' hx'R₁
  have hneg : rProf (stChart s) x' < 0 := hs.neg hx'R
  calc γ.fn (m₁ x) = γ.fn (m₁ x') := hfn.symm
    _ = γ.fn (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x')).re := by rw [heq]
    _ = β.fn (rProf (stChart s) x') :=
        stopWord_fn_fwdMap_neg hκ β θ r hneg hal hmx'J (by rw [← heq]; exact hm₁J)
    _ = b x' := hO x' hx'R hx'J hmx'J
    _ = b x := hbx'

theorem stRecL_moveAlong_true' (s : ExplState) (w : ℝ) (m : Bool) :
    stRecL (ExplState.moveAlong s true w m) = stRecL s := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

/-- **The inward left profile after a rightward move** (the chart is recentred at the image `a ≥ 0` of the new
point; the left record does not change). -/
theorem lLeft_moveAlong_true (hs : LLeft s) {w : ℝ} (m : Bool) (ha : 0 ≤ rProf (stChart s) w) :
    LLeft (ExplState.moveAlong s true w m) := by
  have hprof : lProf (stChart (ExplState.moveAlong s true w m)) =
      fun x => lProf (stChart s) x + rProf (stChart s) w := by
    funext x
    rw [stChart_moveAlong, lProf_eq, rProf_recenter, lProf_eq]
    simp only [rProf]
    ring
  unfold LLeft
  rw [hprof, stRecL_moveAlong_true']
  obtain ⟨⟨hmono, hcont, hunb⟩, hpos⟩ := hs
  refine ⟨⟨fun x hx y hy hxy => by simp only; linarith [hmono hx hy hxy], hcont.add continuousOn_const,
    fun M => ?_⟩, fun x hx => add_pos_of_pos_of_nonneg (hpos x hx) ha⟩
  obtain ⟨x, hx, hMx⟩ := hunb (M - rProf (stChart s) w)
  exact ⟨x, hx, by linarith⟩

/-- **The original word on the left ray after a rightward move** (the word recentred by the same amount). -/
theorem lOrig_moveAlong_true {b : ℝ → ℝ} {jumps : Finset ℝ} {γ : BoundaryWord} (hO : LOrig b jumps γ s) {w : ℝ}
    (m : Bool) :
    LOrig b jumps (BoundaryWord.shiftW (rProf (stChart s) w) γ) (ExplState.moveAlong s true w m) := by
  intro x hx hxJ hzJ
  rw [stRecL_moveAlong_true'] at hx
  rw [stChart_moveAlong] at hzJ ⊢
  change rProf ((stChart s).recenter (rProf (stChart s) w)) x ∉ _ at hzJ
  change (BoundaryWord.shiftW (rProf (stChart s) w) γ).fn (rProf ((stChart s).recenter (rProf (stChart s) w)) x) = _
  rw [rProf_recenter] at hzJ ⊢
  rw [BoundaryWord.fn_shiftW, sub_add_cancel]
  rw [BoundaryWord.jumps_shiftW] at hzJ
  refine hO x hx hxJ fun h => hzJ (Finset.mem_image.2 ⟨_, h, rfl⟩)

/-- **The first left interval of a force word**: right of every left position (and left of the seed), off the jumps,
the word's height is `−λ − s`. -/
theorem fn_forceWord_first {κ : ℝ} {nL nR : ℕ} {pL pR ρL ρR : ℕ → ℝ} {s y : ℝ} (h : IsMarkOrder nL nR pL pR)
    (hy0 : y < 0) (hy : y ∉ (forceWord κ nL nR pL pR ρL ρR s).jumps) (hL : ∀ i < nL, pL i < y) :
    (forceWord κ nL nR pL pR ρL ρR s).fn y = -sleLambda κ - s := by
  rw [fn_forceWord κ ρL ρR s h hy hy0.ne]
  unfold forceBoundaryData
  rw [ite_eq_left_of_eq_true _ _ (eq_true hy0)]
  have he : Finset.univ.filter (fun i : Fin nL => y < pL i) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun i _ => not_lt.2 (hL i i.2).le
  rw [he, Finset.sum_empty, add_zero, mul_one, sleLambda]

/-- **The stop word on its first left interval**: right of every new left mark (and left of the tip), off the jumps,
the stop word after an angle-`θ` piece has height `−λ − θχ` (the left side of the piece). -/
theorem stopWord_fn_first {κ : ℝ} (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy0 : y < 0)
    (hy : y ∉ (stopWord κ (c, θ, r)).jumps)
    (hL : ∀ i < flowLineNL c.fn c.jumps 0, markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) < y) :
    (stopWord κ (c, θ, r)).fn y = -sleLambda κ - θ * chiC κ :=
  fn_forceWord_first (isMarkOrder_stopWord c r) hy0 hy hL

end InteractingSLE.Theorem14.GW1W
