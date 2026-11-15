/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdtExpl
import InteractingSLE.Spec.Supplement.GW2SdsTip
import InteractingSLE.Spec.Supplement.GW2TmZero
import InteractingSLE.Spec.Sec4.ZeroMarksAvoid
import InteractingSLE.Spec.Supplement.GW2LaterInt

/-!
# A candidate launched at an interior switching tip is not at a threshold (deterministic)

Packet PROVE-GW2-SDE (round 19, decision D45 item 2). The candidate's lifetime is `0` exactly when its launch point is a
bad point of the launch word (RELDET's `GW2Rd.ae_life_zero_iff`, `badDist_zero_eq_zero_iff`). The seed's outward
cumulative weights at `0` are the first flow-line weights only (every other label is strictly off `0`), so they read
only the launch word's one-sided limits at `0`:

* `wR_flowLine_zero`, `wL_flowLine_zero`;
* **`badDist_ne_zero_of_lims`**: if the word's one-sided limits at `0` are the sides `−λ − θ′χ`, `λ − θ′χ` of a piece
  at an angle `θ′ ∈ [−π/2, π/2]`, then no angle `θ ∈ [−π/2, π/2]` puts the seed at a threshold (`|θ − θ′|χ ≤ πχ =
  (2 − κ/2)λ < 2λ`);
* **`lims_stopWord_zero`**: the explicit stop word of a piece whose junctions are strictly off the tip has exactly
  these one-sided limits at `0`;
* **`junctions_strict_of_interiorStop`**: a piece stopped at an interior point (frozen `IsInteriorStop`) whose decoded
  record driver generates a trace has both junctions strictly off the tip.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Sdt

open Restart Exist.Staged Exist.StagedLaw Supp8.GB6 PiecewiseConstantBoundaryData

/-- The right outward weight of a flow-line word at `0` is its first right weight. -/
theorem wR_flowLine_zero (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) :
    SB.Vq.wR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ) 0 = (rightLim b 0 + θ * chiC κ) / sleLambda κ - 1 := by
  classical
  unfold SB.Vq.wR flowLineXR flowLineRhoR flowLineNR
  have hfilt : Finset.univ.filter (fun j : Fin (((jumpSet b J).filter (fun y => 0 < y)).card + 1) =>
      (Fin.cons (0 : ℝ) (fun i => ((jumpSet b J).filter (fun y => 0 < y)).orderEmbOfFin rfl i - 0) :
        Fin (((jumpSet b J).filter (fun y => 0 < y)).card + 1) → ℝ) j ≤ 0) = {0} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · rw [Fin.cons_succ, sub_zero]
      have hm := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (fun y => 0 < y)) rfl i
      have hpos := (Finset.mem_filter.1 hm).2
      constructor
      · intro h; linarith
      · intro h; exact absurd h (Fin.succ_ne_zero i)
  rw [hfilt, Finset.sum_singleton, Fin.cons_zero]

/-- The left outward weight of a flow-line word at `0` is its first left weight. -/
theorem wL_flowLine_zero (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) :
    SB.Vq.wL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ) 0 = -(leftLim b 0 + θ * chiC κ) / sleLambda κ - 1 := by
  classical
  unfold SB.Vq.wL flowLineXL flowLineRhoL flowLineNL
  have hfilt : Finset.univ.filter (fun j : Fin (((jumpSet b J).filter (fun y => y < 0)).card + 1) =>
      0 ≤ (Fin.cons (0 : ℝ) (fun i => ((jumpSet b J).filter (fun y => y < 0)).orderEmbOfFin rfl (Fin.rev i) - 0) :
        Fin (((jumpSet b J).filter (fun y => y < 0)).card + 1) → ℝ) j) = {0} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · rw [Fin.cons_succ, sub_zero]
      have hm := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (fun y => y < 0)) rfl (Fin.rev i)
      have hneg := (Finset.mem_filter.1 hm).2
      constructor
      · intro h; linarith
      · intro h; exact absurd h (Fin.succ_ne_zero i)
  rw [hfilt, Finset.sum_singleton, Fin.cons_zero]

/-- **No threshold at a seed with the sides of a piece**: if the word's one-sided limits at `0` are `−λ − θ′χ` and
`λ − θ′χ`, the launch point `0` is not bad at any angle `θ`, for angles in `[−π/2, π/2]`. -/
theorem badDist_ne_zero_of_lims {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (w : BoundaryWord) {θ θp : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hθp : θp ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hL : leftLim w.fn 0 = -sleLambda κ - θp * chiC κ) (hR : rightLim w.fn 0 = sleLambda κ - θp * chiC κ) :
    GW2Rd.badDist κ θ w 0 ≠ 0 := by
  rw [Ne, GW2Rd.badDist_zero_eq_zero_iff hκ θ w, GW2Rd.threshold_seed_iff_isBadPoint]
  have hl := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  have hpi := Sec4.pi_mul_chiC hκ
  rintro ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩
  · rw [Complex.zero_re, wR_flowLine_zero, hR] at h
    have h' : sleLambda κ - θp * chiC κ + θ * chiC κ ≤ -sleLambda κ := by
      have := (div_le_iff₀ hl).1 (by linarith : (sleLambda κ - θp * chiC κ + θ * chiC κ) / sleLambda κ ≤ -1)
      linarith
    have hd : -Real.pi ≤ θ - θp := by linarith [hθ.1, hθp.2]
    nlinarith
  · rw [Complex.zero_re, wL_flowLine_zero, hL] at h
    have h' : -(-sleLambda κ - θp * chiC κ + θ * chiC κ) ≤ -sleLambda κ := by
      have := (div_le_iff₀ hl).1 (by linarith : -(-sleLambda κ - θp * chiC κ + θ * chiC κ) / sleLambda κ ≤ -1)
      linarith
    have hd : -Real.pi ≤ θp - θ := by linarith [hθ.2, hθp.1]
    nlinarith

/-- **The explicit stop word's one-sided limits at the tip** are the piece's sides, when the piece's junctions are
strictly off the tip. -/
theorem lims_stopWord_zero {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData)
    (hL : markPosL (rdrv r) (rtime r) 0 < 0) (hR : 0 < markPos (rdrv r) (rtime r) 0) :
    leftLim (stopWord κ (c, θ, r)).fn 0 = -sleLambda κ - θ * chiC κ ∧
      rightLim (stopWord κ (c, θ, r)).fn 0 = sleLambda κ - θ * chiC κ := by
  refine ⟨Sec4.leftLim_eq_of_forall_notMem (stopWord κ (c, θ, r)).jumps hL fun t ht htJ => ?_,
    Sec4.rightLim_eq_of_forall_notMem (stopWord κ (c, θ, r)).jumps hR fun t ht htJ => ?_⟩
  · rcases (GW2Sdp.fn_stopWord_left hκ c θ r (le_refl 0) ht.2 htJ).1 ht.1 with h | ⟨y, hy1, hy2, -⟩
    · exact h
    · exact absurd (hy1.trans hy2) (lt_irrefl 0)
  · rcases (GW2Sdp.fn_stopWord_right hκ c θ r (le_refl 0) ht.1 htJ).1 ht.2 with h | ⟨y, hy1, hy2, -⟩
    · exact h
    · exact absurd (hy1.trans hy2) (lt_irrefl 0)

/-- **A piece stopped at an interior point has both junctions strictly off the tip**, when the decoded driver of its
record generates a trace. -/
theorem junctions_strict_of_interiorStop {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {Δ : ℝ≥0}
    (hΔ : (Δ : ℝ≥0∞) < e.2) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t : ℝ≥0 => rdrv (recOf (Δ : ℝ≥0∞) e) t) ⊤ η)
    (hint : GW2Later.IsInteriorStop e.1 (Δ : ℝ≥0∞)) :
    markPosL (rdrv (recOf (Δ : ℝ≥0∞) e)) (rtime (recOf (Δ : ℝ≥0∞) e)) 0 < 0 ∧
      0 < markPos (rdrv (recOf (Δ : ℝ≥0∞) e)) (rtime (recOf (Δ : ℝ≥0∞) e)) 0 := by
  set p := recOf (Δ : ℝ≥0∞) e with hp
  have hmin : min (Δ : ℝ≥0∞) e.2 = Δ := min_eq_left hΔ.le
  have hfin : min (Δ : ℝ≥0∞) e.2 ≠ ⊤ := by rw [hmin]; exact ENNReal.coe_ne_top
  have hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min (Δ : ℝ≥0∞) e.2} :=
    he.1.mono fun s hs => lt_of_le_of_lt (hmin ▸ hs) hΔ
  have hL := isLoewnerTrace_of_isGeneratingTrace hη
  rw [GW2Sds.rdrv_toNNReal p] at hL
  have hW := continuous_rdrv p
  have hW0 := rdrv_zero p
  have ht : rtime p = (Δ : ℝ) := by rw [hp, rtime_recOf_coe, hmin, ENNReal.toNNReal_coe]
  -- the record driver is the stopped piece driver
  have hstop : (fun r : ℝ => e.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (Δ : ℝ≥0∞)).toNNReal) = rdrv p := by
    funext r
    rw [← GW2Sds.rdrv_toNNReal p]
    show e.1 _ = rdrv p ((r.toNNReal : ℝ≥0) : ℝ)
    rw [GW2TipSystem.Gm.rdrv_recOf_eq he hfin hc r.toNNReal, hmin, ENNReal.toNNReal_coe, ← ENNReal.coe_min,
      ENNReal.toNNReal_coe]
  obtain ⟨q, hqH, hq⟩ := hint
  have hLT : IsLoewnerTraceLT (rdrv p) ((Δ : ℝ) + 1) (fun s => η s.toNNReal) :=
    ⟨hL.1, hL.2.1.mono Ico_subset_Ici_self, fun t ht _ => hL.2.2 t ht⟩
  have htip := hLT.tendsto_fwdMapInv_mul_I hW hW0 Δ.coe_nonneg (lt_add_one _)
  have hq' : Tendsto (fun y : ℝ => fwdMapInv (rdrv p) Δ (y * Complex.I)) (𝓝[>] 0) (𝓝 q) := by
    refine hq.congr fun y => ?_
    show fwdMapInv (fun r : ℝ => e.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (Δ : ℝ≥0∞)).toNNReal)
      (((Δ : ℝ≥0∞).toNNReal : ℝ≥0) : ℝ) (y * Complex.I) = _
    rw [ENNReal.toNNReal_coe, hstop]
  have hηq : η (((Δ : ℝ)).toNNReal) = q := tendsto_nhds_unique htip hq'
  rw [ht]
  refine GW2Sds.junctions_strict_of_trace hW hW0 hL Δ.coe_nonneg ?_
  show η ((Δ : ℝ).toNNReal) ∈ H
  rw [hηq]
  exact hqH

end InteractingSLE.Theorem14.GW2Sdt
