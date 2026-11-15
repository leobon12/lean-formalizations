/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LzExit
import InteractingSLE.Spec.Supplement.GW1ActiveChartL
import InteractingSLE.Spec.Supplement.GW2aConnMove
import InteractingSLE.Spec.ZhanGT4.FirstSwallowSide

/-!
# The left profile of the right walk and the strong exclusion of left hits

Packet PROVE-T14-SB2LIFT (round 15; item 1 of handoff §R14.2). GW1's stage data excludes left thresholds
(`NoLeftThr`) but not a left hit alongside a right hit. Two real points on opposite sides of the driver are never
swallowed at the same time (`ZhanGT4.not_realSwallowAt_both`). So the strong `NoLeftHit` follows once the points left
of the left record have negative chart points. This file proves that part of GW1's left profile:

* **`LProf3 s`**: the chart is real, and the reflected left profile `lProf` is increasing, continuous, unbounded and
  positive beyond `−recL` (GW1's `LProf` without its smallness clause at the record);
* `lProf3_init`: at the root;
* **`lProf3_launch`**: it survives every launch with a finite lifetime and a good driver record. The proof is GW1's
  `lProf_launch`, which uses its left hit only for the dropped clause: `rightGood_comp`, `pos_alive_of_newRec_lt`;
* **`lProf3_moveAlong_true`**: it survives a move to the right to a point with positive chart value (a shift of the
  profile by that value);
* **`not_leftHit_of_lProf3`**: at a launch from a state with `LProf3` and `RProf`, if the walk does not end at a left
  threshold, then no point left of the left record is hit. A zero stop hits nothing with a nonzero
  chart point. Otherwise the status is a right threshold, so a right point (positive chart point, `RProf`) and the
  left point (negative chart point) would be swallowed at the same time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol fwdMap)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Restart GW1W

/-- **The left profile of a state** (GW1's `LProf` without the smallness clause at the record). -/
def LProf3 (s : ExplState) : Prop :=
  IsRealChart (stChart s) ∧ RightGood (lProf (stChart s)) (-stRecL s) ∧
    ∀ x, -stRecL s < x → 0 < lProf (stChart s) x

theorem lProf3_init (x₀ : ℝ) : LProf3 (ExplState.init x₀) := by
  have hl : lProf (stChart (ExplState.init x₀)) = fun x => x + x₀ := by
    funext x
    simp [lProf, ExplState.init, Chart.id, Chart.recenter]
    ring
  have hr : stRecL (ExplState.init x₀) = x₀ := rfl
  refine ⟨fun x => by simp [ExplState.init, Chart.id, Chart.recenter], ?_, fun x hx => ?_⟩
  · rw [hl, hr]
    refine ⟨fun a _ b _ hab => by simp only; linarith, (continuous_id.add continuous_const).continuousOn,
      fun M => ⟨max (-x₀) (M - x₀) + 1, by linarith [le_max_left (-x₀) (M - x₀)], by
        simp only; linarith [le_max_right (-x₀) (M - x₀)]⟩⟩
  · rw [hl]
    rw [hr] at hx
    simp only
    linarith

variable {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The left profile survives a launch with a finite lifetime and a good driver record.** -/
theorem lProf3_launch (hs : LProf3 s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    LProf3 (ExplState.launch s k D θ ⊤) := by
  obtain ⟨hc, hm, hpos⟩ := hs
  obtain ⟨hch, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  have hWr : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
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
  refine ⟨fun x => ?_, ?_, fun u hu => ?_⟩
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

/-- **The left profile survives a move to the right** to a point with positive chart value. -/
theorem lProf3_moveAlong_true (hs : LProf3 s) {w : ℝ} (ha : 0 < rProf (stChart s) w) (m : Bool) :
    LProf3 (ExplState.moveAlong s true w m) := by
  obtain ⟨hc, hm, hpos⟩ := hs
  set a := rProf (stChart s) w with hadef
  have hch : stChart (ExplState.moveAlong s true w m) = (stChart s).recenter a := GW1W.stChart_moveAlong s true w m
  have hrec : stRecL (ExplState.moveAlong s true w m) = stRecL s := GW2aConn.stRecL_moveAlong_true s w m
  have hl : lProf (stChart (ExplState.moveAlong s true w m)) = fun x => lProf (stChart s) x + a := by
    funext x
    rw [hch]
    simp only [lProf, Chart.recenter, Complex.sub_re, Complex.ofReal_re]
    ring
  unfold LProf3
  rw [hrec]
  refine ⟨fun x => ?_, ?_, fun x hx => ?_⟩
  · rw [hch]
    show ((stChart s).1 x - (a : ℂ)).im = 0
    simp [hc x]
  · rw [hl]
    obtain ⟨h1, h2, h3⟩ := hm
    refine ⟨fun x hx y hy hxy => by simp only; linarith [h1 hx hy hxy], h2.add continuousOn_const,
      fun M => ?_⟩
    obtain ⟨x, hx, hMx⟩ := h3 (M - a)
    exact ⟨x, hx, by simp only; linarith⟩
  · rw [hl]
    simp only
    linarith [hpos x hx]

/-- **No left hit at a launch** from a state with the left and the right profile, when the walk does not end at a left
threshold. -/
theorem not_leftHit_of_lProf3 (hl : LProf3 s) (hr : RProf s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hthr : stStatus (ExplState.launch s k D θ ⊤) ≠ stThr (some false)) :
    ¬ ∃ y : ℝ, y < stRecL s ∧ lHit (stChart s) ⊤ D y := by
  rintro ⟨y, hy, hbefore, hna⟩
  obtain ⟨hc, -, hpos⟩ := hl
  have hv : (stChart s).1 y = (((-lProf (stChart s) (-y)) : ℝ) : ℂ) := by
    rw [hc.eq_ofReal y, lProf_eq, neg_neg, neg_neg]
  have hvneg : -lProf (stChart s) (-y) < 0 := by
    have := hpos (-y) (by linarith)
    linarith
  have hd0 : D.1 0 = 0 := hreg.2.1
  by_cases hT : stopTime ⊤ D = 0
  · exact hna (lAlive_of_stopTime_zero hd0 hT (by rw [hv]; exact_mod_cast hvneg.ne))
  · -- a positive stop: the lifetime is finite and positive, and the status is a right threshold
    have hfin : D.2 ≠ ⊤ := fun h => hT (by simp [stopTime, h])
    have h0 : D.2 ≠ 0 := fun h => hT (by simp [stopTime, h])
    have hTpos : 0 < stopTime ⊤ D := lt_of_le_of_ne (stopTime_nonneg ⊤ D) (Ne.symm hT)
    obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
    have hnlt : ¬ (⊤ : ℝ≥0∞) < D.2 := not_lt.2 le_top
    have hR : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ D x := by
      by_contra hR
      have hL : ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) ⊤ D x := ⟨y, hy, hbefore, hna⟩
      apply hthr
      rw [hst]
      simp only [lStatus, hnlt, h0, hR, hL, ↓reduceIte]
    obtain ⟨x, hx, hxbefore, hxna⟩ := hR
    have hu : (stChart s).1 x = ((rProf (stChart s) x : ℝ) : ℂ) := hc.eq_ofReal x
    have hupos : 0 < rProf (stChart s) x := hr.2.2.1 x hx
    have hWr : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg (hgood hfin)
    have hW : Continuous (stopDrv ⊤ D) := by rw [← hWr]; exact continuous_rdrv _
    have hW0 : stopDrv ⊤ D 0 = 0 := stopDrv_zero hreg ⊤
    have hswv : InteractingSLE.RealSwallowAt (stopDrv ⊤ D) (-lProf (stChart s) (-y)) (stopTime ⊤ D) := by
      refine ⟨hTpos, fun r hr => ?_, fun h => hna ?_⟩
      · have := hbefore r hr.2
        rw [hv] at this
        exact this
      · show ∃ u, IsForwardSol (stopDrv ⊤ D) ((stChart s).1 y) (stopTime ⊤ D) u
        rw [hv]; exact h
    have hswu : InteractingSLE.RealSwallowAt (stopDrv ⊤ D) (rProf (stChart s) x) (stopTime ⊤ D) := by
      refine ⟨hTpos, fun r hr => ?_, fun h => hxna ?_⟩
      · have := hxbefore r hr.2
        rw [hu] at this
        exact this
      · show ∃ u, IsForwardSol (stopDrv ⊤ D) ((stChart s).1 x) (stopTime ⊤ D) u
        rw [hu]; exact h
    exact ZhanGT4.not_realSwallowAt_both hW hW0 hvneg hupos hswv hswu

end InteractingSLE.Theorem14.SB.Lk
