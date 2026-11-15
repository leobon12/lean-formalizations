/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39Chart

/-!
# Fresh-tip uniqueness (Lemma 1.1 of the ZTip-elimination note)

Ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` L37–L61):

> **Lemma 1.1** (Fresh-tip uniqueness, with no stopping-time hypothesis). Let `T > 0` be any time
> of a realized continuous chordal Loewner trace. If `p = η(T) ∈ ℍ` and `p ∉ η([0, T))`, then
> `f_T⁻¹({p}) ∩ ∂ℍ = {W_T}`.

In the centred chart of PROVE-YUAN-M1B (`f̄_T = trMap W 0 T`, the driver `W_T` at `0`) this reads:
a real `x` with `f̄_T(x) = η(T)` is `0` (`trMap_zero_eq_trace` gives `f̄_T(0) = η(T)`).

## Proof (a variant of the source's)

The source runs a backward real characteristic from `x` on `[s, T]`. Instead we use that the
increment inverse map `f̄_{s,T} = trMap W s T` moves points by at most `24 M + 8 √(T − s)`, where
`M = sup_{[s, T]} |W − W_s|` (QuantumZipper's reverse-flow bound, through `norm_fwdMapInv_sub_le`),
and that its hull `A` (the filling of the shifted trace on `[0, T − s]`) lies in the ball of the
same radius about `0`. For `s` close to `T` this radius `ε` is `< |x| / 3`. Then `w = f̄_{s,T}(x)`
satisfies `|w| > 2ε`, so `w ∉ A`; since `w` is a boundary value at a real point it is not in
`f̄_{s,T}(ℍ) = ℍ \ A`, hence `w` is real. Then `η(T) = f̄_T(x) = f̄_s(w)` is a boundary value of
`f̄_s`
at a real point: it lies in `K_s` and is adherent to `ℍ \ K_s`, hence in `η([0, s])` with `s < T`,
contradicting freshness. The two ingredients are the same as the source's (the increment map is
analytic across the real line away from its small hull, and the composition
`f̄_T = f̄_s ∘ f̄_{s,T}`).

## Main results

* `norm_trMap_sub_le`: `‖f̄_{s,T}(w) − w‖ ≤ 24 M + 8 √(T − s)` on `ℍ̄`;
* `trMap_zero_eq_trace`: `f̄_T(0) = η(T)`;
* `fresh_tip_fibre`: **Lemma 1.1**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

theorem shiftDrive_apply' (W : ℝ → ℝ) (s r : ℝ) : shiftDrive W s r = W (s + r) - W s := rfl

/-- The tip in the centred chart: `f̄_T(0) = η(T)`. -/
theorem trMap_zero_eq_trace (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) : trMap W 0 T 0 = η T := by
  rw [YuanSimpleApprox.trMap_zero, YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero,
    hη.loewnerTip_eq hW hW0 hT]

/-- **The increment inverse map moves points by a small amount**: if `|W r − W s| ≤ M` on
`[s, T]`, then `‖f̄_{s,T}(w) − w‖ ≤ 24 M + 8 √(T − s)` for `w ∈ ℍ̄`. -/
theorem norm_trMap_sub_le (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s T M : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hM : ∀ r ∈ Icc s T, |W r - W s| ≤ M) {w : ℂ}
    (hw : w ∈ Hbar) : ‖trMap W s T w - w‖ ≤ 24 * M + 8 * Real.sqrt (T - s) := by
  have hV := QuantumZipper.RS.continuous_shiftDrive hW s
  have hV0 : shiftDrive W s 0 = 0 := InteractingSLE.shiftDrive_zero W s
  have hTs : 0 ≤ T - s := sub_nonneg.2 hsT
  have hMV : ∀ r ∈ Icc (0 : ℝ) (T - s), |shiftDrive W s r| ≤ M := by
    intro r hr
    rw [shiftDrive_apply']
    exact hM (s + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hbound : ∀ v ∈ H, ‖fwdMapInv (shiftDrive W s) (T - s) v - v‖ ≤
      24 * M + 8 * Real.sqrt (T - s) := fun v hv => norm_fwdMapInv_sub_le hV hV0 hTs hMV hv
  have hcl : w ∈ closure H := by rw [closure_H]; exact hw
  have : (𝓝[H] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hlim := (hη.hasBdryLimits_shift hW hW0 hs hTs).tendsto hw
  have ht := (hlim.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).norm
  refine le_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact hbound v hv

/-- For `0 < T` and `ε > 0` there is `s ∈ [0, T)` with `24 M + 8 √(T − s) < ε` for
`M = sup_{[s, T]} |W − W_s|`. -/
theorem exists_close_time (hW : Continuous W) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ s ∈ Ico 0 T, ∃ M, (∀ r ∈ Icc s T, |W r - W s| ≤ M) ∧ 24 * M + 8 * Real.sqrt (T - s) < ε := by
  obtain ⟨δ, hδ, hδW⟩ := Metric.continuous_iff.1 hW T (ε / 200) (by positivity)
  set η' := min T (min (δ / 2) ((ε / 200) ^ 2)) with hη'
  have hη'pos : 0 < η' := lt_min hT (lt_min (half_pos hδ) (by positivity))
  refine ⟨T - η', ⟨by linarith [min_le_left T (min (δ / 2) ((ε / 200) ^ 2))], by linarith⟩,
    ε / 100, fun r hr => ?_, ?_⟩
  · have h1 : dist (W r) (W T) < ε / 200 := hδW r (by
      rw [Real.dist_eq, abs_lt]
      have := min_le_right T (min (δ / 2) ((ε / 200) ^ 2))
      have := min_le_left (δ / 2) ((ε / 200) ^ 2)
      constructor <;> linarith [hr.1, hr.2])
    have h2 : dist (W (T - η')) (W T) < ε / 200 := hδW (T - η') (by
      rw [Real.dist_eq, abs_lt]
      have := min_le_right T (min (δ / 2) ((ε / 200) ^ 2))
      have := min_le_left (δ / 2) ((ε / 200) ^ 2)
      constructor <;> linarith)
    rw [Real.dist_eq] at h1 h2
    have := abs_sub_le (W r) (W T) (W (T - η'))
    rw [abs_sub_comm (W T)] at this
    linarith
  · have hsq : Real.sqrt (T - (T - η')) ≤ ε / 200 := by
      rw [sub_sub_cancel]
      rw [Real.sqrt_le_left (by positivity)]
      exact (min_le_right T _).trans (min_le_right _ _)
    nlinarith

/-- A boundary value of `f̄_s` at a real point which lies in `ℍ` was visited by time `s`. -/
theorem mem_trace_of_trMap_real (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {w : ℂ} (hw : w.im = 0) (hH : trMap W 0 s w ∈ H) :
    trMap W 0 s w ∈ η '' Icc 0 s := by
  obtain ⟨-, hc, -, hR⟩ := YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 le_rfl hs
  have himg : trMap W 0 s '' H = H \ fwdHull W s := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 hs]
    refine image_congr fun v hv => ?_
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hs hv, YuanSimpleApprox.shiftDrive_zero_eq hW0,
      sub_zero]
  have hnot := hR w hw
  rw [himg] at hnot
  have hK : trMap W 0 s w ∈ fwdHull W s := by
    by_contra h; exact hnot ⟨hH, h⟩
  have hwH : w ∈ Hbar := mem_Hbar_of_im_eq_zero hw
  have hcl : trMap W 0 s w ∈ closure (H \ fwdHull W s) := by
    rw [← himg]
    have hwcl : w ∈ closure H := by rw [closure_H]; exact hwH
    have := (hc.mono (closure_H ▸ (subset_refl _) : closure H ⊆ Hbar)).image_closure
      (s := H) ⟨w, hwcl, rfl⟩
    exact this
  rw [hη.2.2 s hs] at hK hcl
  have := mem_closure_of_mem_fillH_of_mem_closure hK hcl
  have hcpt : IsCompact (η '' Icc 0 s) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun t ht => ht.1)
  rwa [hcpt.isClosed.closure_eq] at this

/-- **Lemma 1.1** (fresh-tip uniqueness). If `T > 0`, `η(T) ∈ ℍ` and `η(T) ∉ η([0, T))`, then the
only real point `x` with `f̄_T(x) = η(T)` is the driver `0` (centred chart). -/
theorem fresh_tip_fibre (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 < T) (hpH : η T ∈ H) (hfresh : η T ∉ η '' Ico 0 T) {x : ℝ}
    (hx : trMap W 0 T x = η T) : x = 0 := by
  by_contra hx0
  have hxpos : 0 < |x| := abs_pos.2 hx0
  obtain ⟨s, hs, M, hM, hB⟩ := exists_close_time hW hT (ε := |x| / 3) (by positivity)
  set B := 24 * M + 8 * Real.sqrt (T - s) with hBdef
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  set w := trMap W s T x with hw
  have hwx : ‖w - x‖ ≤ B := norm_trMap_sub_le hη hW hW0 hs.1 hs.2.le hM hxH
  -- `w` is real
  have hwreal : w.im = 0 := by
    by_contra hwim
    have hwHbar : w ∈ Hbar := YuanSimpleApprox.trMap_mapsTo_Hbar hη hW hW0 hs.1 hs.2.le hxH
    have hwH : w ∈ H := lt_of_le_of_ne hwHbar (Ne.symm hwim)
    obtain ⟨-, -, -, hR⟩ := YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 hs.1 hs.2.le
    have hnot := hR (x : ℂ) (by simp)
    have himg : trMap W s T '' H = H \ fwdHull (shiftDrive W s) (T - s) := by
      have hV := QuantumZipper.RS.continuous_shiftDrive hW s
      rw [← QuantumZipper.RS.image_fwdMapInv_H hV (InteractingSLE.shiftDrive_zero W s)
        (sub_nonneg.2 hs.2.le)]
      exact image_congr fun v hv => YuanSimpleApprox.trMap_eq_fwdMapInv hW hs.2.le hv
    rw [himg] at hnot
    have hwA : w ∈ fwdHull (shiftDrive W s) (T - s) := by
      by_contra h; exact hnot ⟨hwH, h⟩
    -- the increment hull lies in the ball of radius `B`
    have hγ := YuanSimpleApprox.isLoewnerTrace_shift' hη hW hW0 hs.1
    rw [hγ.2.2 (T - s) (sub_nonneg.2 hs.2.le)] at hwA
    have htipB : ∀ r ∈ Icc (0 : ℝ) (T - s), ‖loewnerTip (shiftDrive W s) r‖ ≤ B := by
      intro r hr
      have h1 := norm_trMap_sub_le hη hW hW0 hs.1 (show s ≤ s + r by linarith [hr.1])
        (M := M) (fun q hq => hM q ⟨hq.1, hq.2.trans (by linarith [hr.2])⟩)
        (w := 0) zero_mem_Hbar
      rw [sub_zero, YuanSimpleApprox.trMap_zero, add_sub_cancel_left] at h1
      refine h1.trans ?_
      have : Real.sqrt r ≤ Real.sqrt (T - s) := Real.sqrt_le_sqrt hr.2
      linarith
    have hB0 : 0 ≤ B := (norm_nonneg _).trans hwx
    have hwB : ‖w‖ ≤ B := by
      refine le_of_forall_pos_lt_add fun δ hδ => ?_
      have hcl : closure (loewnerTip (shiftDrive W s) '' Icc 0 (T - s)) ⊆ ball 0 (B + δ) := by
        refine (closure_minimal ?_ isClosed_closedBall).trans
          (closedBall_subset_ball (show B < B + δ by linarith))
        rintro _ ⟨r, hr, rfl⟩
        exact mem_closedBall_zero_iff.2 (htipB r hr)
      exact mem_ball_zero_iff.1 (fillH_subset_ball (by linarith) hcl hwA)
    have h1 : |x| ≤ ‖w‖ + B := by
      have := norm_sub_norm_le (x : ℂ) w
      rw [norm_real, Real.norm_eq_abs, norm_sub_rev] at this
      linarith
    linarith
  -- `η T` is a boundary value of `f̄_s` at the real point `w`
  have hcomp : trMap W 0 s w = η T := by
    rw [hw, YuanSimpleApprox.trMap_trMap hη hW hW0 le_rfl hs.1 hs.2.le hxH, hx]
  have hmem := mem_trace_of_trMap_real hη hW hW0 hs.1 hwreal (by rw [hcomp]; exact hpH)
  rw [hcomp] at hmem
  obtain ⟨r, hr, hrT⟩ := hmem
  exact hfresh ⟨r, ⟨hr.1, hr.2.trans_lt hs.2⟩, hrT⟩

end InteractingSLE.Sec6
