/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BmDeath
import InteractingSLE.Spec.Supplement.SB2VqEnd

/-!
# The converse of SAFE's collision exclusion in the relative chart: a real bad tip gives a threshold

Packet PROVE-GW2-NOTHR (round 3, D35 (D-a), the threshold at the candidate's death). SAFE's collision exclusion reads
"no threshold ⇐ the tip avoids the bad set". At the death the converse is needed: the tip is at a bad real point, and
the relative driver has a continuation threshold there. Earlier boundary bounces matter: the zero mark collides at the
death only if the relative trace has no earlier real visit at or beyond the tip (BUF's
`GW2Bh.rightImg_eq_of_real_tip_off`).

* **`alive_of_le_point`**: a point right of an alive point is alive (`regFlow_lt_regFlow`);
* **`rightImg_eq_of_not_alive_of_le`**: below a dead point the right image is the dead point's (the right image is
  an infimum over alive points);
* **`rightSum_le_of_real_bad_tip_off`**, **`leftSum_le_of_real_bad_tip_off`**: in the relative chart, a real tip at a
  bad right (left) point beyond the earlier real visits of the relative trace gives the right (left) threshold sum of
  the relative driver at the tip's relative time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Nu

open MartChar.RealFlow Supp8.GB6.CoordB Restart GW2Bh

section Flow

variable {w : ℝ → ℝ}

/-- **A point right of an alive point is alive.** -/
theorem alive_of_le_point (hw : Continuous w) {y y' t : ℝ} (ht : 0 ≤ t) (h : Alive w y t) (hyy : y ≤ y') :
    Alive w y' t := by
  rcases hyy.eq_or_lt with rfl | hlt
  · exact h
  obtain ⟨n, hn⟩ := (alive_iff_regFlow hw ht).1 h
  exact (alive_iff_regFlow hw ht).2 ⟨n, fun s hs =>
    (hn s hs).trans (regFlow_lt_regFlow hw (by positivity) hlt hs.1).le⟩

/-- **Below a dead point the right image is the dead point's** (no alive point lies between). -/
theorem rightImg_eq_of_not_alive_of_le (hw : Continuous w) {x y t : ℝ} (ht : 0 ≤ t) (hxy : x ≤ y)
    (hy : ¬ Alive w y t) : rightImg w x t = rightImg w y t := by
  unfold rightImg
  congr 1
  ext g
  constructor
  · rintro ⟨z, hxz, hz, rfl⟩
    refine ⟨z, ?_, hz, rfl⟩
    by_contra hle
    exact hy (alive_of_le_point hw ht hz (not_lt.1 hle))
  · rintro ⟨z, hyz, hz, rfl⟩
    exact ⟨z, lt_of_le_of_lt hxy hyz, hz, rfl⟩

end Flow

section Rel

variable {U : ℝ → ℝ} {s : ℝ} {γ : ℝ≥0 → ℂ} {a : ℝ≥0 → ℝ} {τ : ℝ≥0}

/-- **The right threshold at a real bad tip beyond the earlier visits, in the relative chart.** The physical tip at
`τ` is real, its chart image `p` has `Re p > 0`, the relative trace has no real visit `≥ Re p` before `a τ`, and the
right cumulative weight at `Re p` is `≤ −2`: the collided right marks of the relative driver at `a τ` carry weight
`≤ −2`. -/
theorem rightSum_le_of_real_bad_tip_off (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ)
    (hγc : ContinuousOn γ (Iic τ)) (hγ0 : γ 0 = 0) (hsafe : MapsTo γ (Iic τ) (relSafe U s)) {R : ℝ → ℝ}
    (hRc : Continuous R) (hR0 : R 0 = 0) (hK : ∀ t ≤ τ, fwdHull R (a t) = fillH (relBdry U s '' (γ '' Icc 0 t)))
    (hσ : 0 < a τ) (him : (γ τ).im = 0) (hpos : 0 < (relBdry U s (γ τ)).re)
    (hoff : ∀ u ∈ Ico 0 (a τ), ∀ r : ℝ, (relBdry U s (γ τ)).re ≤ r → relTrace U s γ a τ u ≠ r)
    {nR : ℕ} (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ)
    (hbad : SB.Vq.wR xR ρR (relBdry U s (γ τ)).re ≤ -2) :
    ∑ j ∈ univ.filter (fun j => rightImg R (xR j) (a τ) = R (a τ)), ρR j ≤ -2 := by
  have hzero : rightImg R 0 (a τ) = R (a τ) :=
    rightImg_eq_of_real_tip_off hU hU0 hs ha hγc hγ0 hsafe hRc hR0 hK hσ him hpos le_rfl hoff hpos.le
  have hη := isLoewnerTraceLT_relTrace hU hU0 hs ha hγc hγ0 hsafe hK
  have hc := continuousOn_relTrace hU hU0 hs ha hγc hsafe
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hRc hR0 hσ hc
  have htip := TraceClose.extendFrom_zero_eq hη hRc hR0 hσ hc
  rw [relTrace_end ha] at htip
  rw [SB.Vq.filter_eq_of_zero_collision hRc hR0 hσ.le hB htip hzero xR]
  exact hbad

/-- **The left threshold at a real bad tip beyond the earlier visits, in the relative chart** (the mirror form; left
marks `x ≤ 0` are read as right marks `−x` of the negated driver). -/
theorem leftSum_le_of_real_bad_tip_off (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ)
    (hγc : ContinuousOn γ (Iic τ)) (hγ0 : γ 0 = 0) (hsafe : MapsTo γ (Iic τ) (relSafe U s)) {R : ℝ → ℝ}
    (hRc : Continuous R) (hR0 : R 0 = 0) (hK : ∀ t ≤ τ, fwdHull R (a t) = fillH (relBdry U s '' (γ '' Icc 0 t)))
    (hσ : 0 < a τ) (him : (γ τ).im = 0) (hneg : (relBdry U s (γ τ)).re < 0)
    (hoff : ∀ u ∈ Ico 0 (a τ), ∀ r : ℝ, r ≤ (relBdry U s (γ τ)).re → relTrace U s γ a τ u ≠ r)
    {nL : ℕ} (xL : Fin nL → ℝ) (ρL : Fin nL → ℝ)
    (hbad : SB.Vq.wL xL ρL (relBdry U s (γ τ)).re ≤ -2) :
    ∑ i ∈ univ.filter (fun i => -rightImg (fun v => -R v) (-xL i) (a τ) = R (a τ)), ρL i ≤ -2 := by
  have hzero : rightImg (-R) 0 (a τ) = (-R) (a τ) := by
    have h := rightImg_neg_eq_of_real_tip_off hU hU0 hs ha hγc hγ0 hsafe hRc hR0 hK hσ him hneg le_rfl hoff
      (x := 0) hneg.le
    simpa only [neg_zero] using h
  have hη := SB.Vo.isLoewnerTraceLT_reflect (isLoewnerTraceLT_relTrace hU hU0 hs ha hγc hγ0 hsafe hK)
  have hc : ContinuousOn (fun u => LP.reflectC (relTrace U s γ a τ u)) (Icc 0 (a τ)) :=
    LP.continuous_reflectC.comp_continuousOn (continuousOn_relTrace hU hU0 hs ha hγc hsafe)
  have hnR : Continuous (-R) := hRc.neg
  have hnR0 : (-R) 0 = 0 := by simp [hR0]
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hnR hnR0 hσ hc
  have htip := TraceClose.extendFrom_zero_eq hη hnR hnR0 hσ hc
  rw [relTrace_end ha] at htip
  have hfilt : univ.filter (fun i => -rightImg (fun v => -R v) (-xL i) (a τ) = R (a τ)) =
      univ.filter (fun i => rightImg (-R) ((fun i => -xL i) i) (a τ) = (-R) (a τ)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
    change -rightImg (-R) (-xL i) (a τ) = R (a τ) ↔ rightImg (-R) (-xL i) (a τ) = -R (a τ)
    constructor <;> intro h <;> linarith
  rw [hfilt, SB.Vq.filter_eq_of_zero_collision hnR hnR0 hσ.le hB htip hzero (fun i => -xL i)]
  have hre : (LP.reflectC (relBdry U s (γ τ))).re = -(relBdry U s (γ τ)).re := by simp [LP.reflectC]
  have hw : SB.Vq.wR (fun i => -xL i) ρL (LP.reflectC (relBdry U s (γ τ))).re =
      SB.Vq.wL xL ρL (relBdry U s (γ τ)).re := by
    unfold SB.Vq.wR SB.Vq.wL
    rw [hre]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_le_neg_iff]
  change SB.Vq.wR (fun i => -xL i) ρL (LP.reflectC (relBdry U s (γ τ))).re ≤ -2
  rw [hw]
  exact hbad

end Rel

end InteractingSLE.Theorem14.GW2Nu
