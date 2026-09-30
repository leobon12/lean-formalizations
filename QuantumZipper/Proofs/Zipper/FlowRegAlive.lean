import QuantumZipper.Proofs.Zipper.FlowRegAliveDet
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Zipper.JointModAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, F1/F2 flow regularity: no real point is swallowed by any restarted SLE flow

`ae_shift_alive_all`: for `0 < κ < 4` (indeed `κ ≤ 4`), almost surely, for **every** restart time
`u ≥ 0`, every real `x ≠ 0` and every horizon `T ≥ 0`, the forward flow driven by the restarted
driver `s ↦ W (u + max s 0) − W u` (`W = √κ B`) exists from `x` on `[0,T]`. This is the body of
`Thm18Asm.G4ShiftAliveStmt` and the aliveness behind the side images along the capacity flow.

Proof.
1. Fixed rational restart times `q ≥ 0`: the restarted driver is the driver of the Brownian motion
   `B(q + ·) − B(q)` (weak Markov property, `RS.isBrownianReal_shift_indep`, `RS.drive_shift`), so
   `RS.ae_real_alive` applies (Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005),
   Lemma 6.2, pp. 23–24; Kemppainen, *Schramm–Loewner Evolution* (2017), Prop. 5.1–5.2,
   pp. 78–80). Countably many `q` at once.
2. All real `u` (deterministic, `shift_alive_pos_of_rat`): for `x > 0` choose a rational
   `q ≤ u` so close to `u` that, with `a = u − q`, `sup_{[0,a]} |W(q+·) − W q| ≤ x/8` and
   `a < x²/32`. Then `x = f^{(q)}_a(y)` for some `y > 0` (`F1.exists_fwdMap_eq`: small starts stay
   below `3x/4`, large starts exceed `x`, and the real flow is `1`-Lipschitz), and the solution from
   `y` for the `q`-restarted driver on `[0, a + T]`, restarted at time `a`
   (`F1.isForwardSol_shift`, Loewner semigroup property), is a solution from `x` for the
   `u`-restarted driver on `[0,T]`. Negative `x` by the reflection `W ↦ −W` (`RS.isForwardSol_neg`).

The passage from rational to all restart times is an own elementary argument (the literature
states the simple-curve property of the whole trace, Rohde–Schramm Thm 6.1, from which the
restarted statement follows via the conformal-map picture; we avoid that machinery).
-/

noncomputable section

open Complex Filter MeasureTheory Set ProbabilityTheory
open scoped Topology NNReal

namespace QuantumZipper
namespace F1

/-- **All restart times, positive start** (deterministic). -/
theorem shift_alive_pos_of_rat {W : ℝ → ℝ} (hW : Continuous W)
    (hq : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ y : ℝ, 0 < y → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s => W (q + max s 0) - W q) (y : ℂ) T v)
    {u : ℝ} (hu : 0 ≤ u) {x : ℝ} (hx : 0 < x) {T : ℝ} (hT : 0 ≤ T) :
    ∃ v, IsForwardSol (fun s => W (u + max s 0) - W u) (x : ℂ) T v := by
  obtain ⟨δ, hδ, hδW⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := u + 1)).uniformContinuousOn_of_continuous
      hW.continuousOn) (x / 8) (by positivity)
  set δ' := min (min δ 1) (x ^ 2 / 32) with hδ'
  have hδ'0 : 0 < δ' := lt_min (lt_min hδ one_pos) (by positivity)
  have hδ'δ : δ' ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hδ'1 : δ' ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ'x : δ' ≤ x ^ 2 / 32 := min_le_right _ _
  obtain ⟨q, hq0, hqu, hqδ⟩ : ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ u ∧ u - q < δ' := by
    rcases eq_or_lt_of_le hu with h | h
    · exact ⟨0, by simp, by simp [← h], by simp [← h, hδ'0]⟩
    · obtain ⟨q, h1, h2⟩ := exists_rat_btwn
        (max_lt h (sub_lt_self u hδ'0) : max 0 (u - δ') < u)
      exact ⟨q, (le_max_left _ _).trans h1.le, h2.le, by linarith [le_max_right 0 (u - δ')]⟩
  set a := u - (q : ℝ) with ha_def
  have ha : 0 ≤ a := by linarith
  have hqa : (q : ℝ) + a = u := by rw [ha_def]; ring
  set V : ℝ → ℝ := fun s => W (q + max s 0) - W q with hVdef
  have hVc : Continuous V :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hVdef]
  have hM : ∀ s ∈ Icc (0 : ℝ) a, |V s| ≤ x / 8 := fun s hs => by
    have h := hδW (q + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩ q ⟨hq0, by linarith⟩
      (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs.1]; linarith [hs.2])
    rw [Real.dist_eq] at h
    simp only [hVdef, max_eq_left hs.1]
    exact h.le
  have hbound : x / 4 + 2 * (x / 8) + 2 * a / (x / 4) < x := by
    have h8 : 2 * a / (x / 4) < x / 4 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  obtain ⟨y, hy, hfy⟩ := exists_fwdMap_eq hVc hV0 ha (by positivity : (0 : ℝ) < x / 4) hM hbound
    (fun y hy => hq q hq0 y hy a ha)
  obtain ⟨w, hw⟩ := hq q hq0 y hy (a + T) (by linarith)
  have hwa : w a = x := by
    rw [← fwdMap_eq_of_isForwardSol hw ⟨ha, by linarith⟩, hfy]
  have h := isForwardSol_shift ha hT hw
  rw [hwa] at h
  have hdrv : (fun s => V (a + max s 0) - V a) = fun s => W (u + max s 0) - W u := by
    funext s
    simp only [hVdef, max_eq_left (add_nonneg ha (le_max_right s 0)), max_eq_left ha]
    rw [← add_assoc, hqa]
    ring
  exact ⟨_, hdrv ▸ h⟩

/-- **All restart times, all real starts `x ≠ 0`** (deterministic). -/
theorem shift_alive_of_rat {W : ℝ → ℝ} (hW : Continuous W)
    (hq : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ y : ℝ, y ≠ 0 → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s => W (q + max s 0) - W q) (y : ℂ) T v)
    {u : ℝ} (hu : 0 ≤ u) {x : ℝ} (hx : x ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ∃ v, IsForwardSol (fun s => W (u + max s 0) - W u) (x : ℂ) T v := by
  rcases hx.lt_or_gt with hneg | hpos
  · have hq' : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ y : ℝ, 0 < y → ∀ T : ℝ, 0 ≤ T →
        ∃ v, IsForwardSol (fun s => (-W) (q + max s 0) - (-W) q) (y : ℂ) T v := by
      intro q hq0 y hy T hT
      obtain ⟨v, hv⟩ := hq q hq0 (-y) (by linarith) T hT
      refine ⟨fun t => -v t, ?_⟩
      convert RS.isForwardSol_neg hv using 1
      · funext t; simp only [Pi.neg_apply]; ring
      · push_cast; ring
    obtain ⟨v, hv⟩ := shift_alive_pos_of_rat hW.neg hq' hu (neg_pos.2 hneg) hT
    refine ⟨fun t => -v t, ?_⟩
    convert RS.isForwardSol_neg hv using 1
    · funext t; simp only [Pi.neg_apply]; ring
    · push_cast; ring
  · exact shift_alive_pos_of_rat hW (fun q hq0 y hy T hT => hq q hq0 y hy.ne' T hT) hu hpos hT

/-- `toNNReal` does not see the negative part. -/
private lemma toNNReal_max_zero' (t : ℝ) : (max t 0).toNNReal = t.toNNReal := by
  rcases le_total t 0 with h | h
  · rw [max_eq_right h, Real.toNNReal_zero, Real.toNNReal_of_nonpos h]
  · rw [max_eq_left h]

/-- **No real point is swallowed by any restarted SLE_κ flow** (`κ ≤ 4`), all restart times at
once. -/
theorem ae_shift_alive_all (κ : ℝ) (hκ : 0 < κ) (hκ4 : κ ≤ 4) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ u : ℝ, 0 ≤ u → ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s => drive κ B ω (u + max s 0) - drive κ B ω u) (x : ℂ) T v := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 ≤ (q : ℝ) → ∀ y : ℝ, y ≠ 0 → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s => drive κ B ω (q + max s 0) - drive κ B ω q) (y : ℂ) T v := by
    intro q
    set s : ℝ≥0 := (q : ℝ).toNNReal
    have hB' := (RS.isBrownianReal_shift_indep hB κ s).1
    filter_upwards [RS.ae_real_alive hB' hκ hκ4] with ω hω hq0 y hy T hT
    have hsq : ((s : ℝ)) = q := Real.coe_toNNReal _ hq0
    have hdrv : drive κ (fun r ω => B (s + r) ω - B s ω) ω =
        fun t => drive κ B ω (q + max t 0) - drive κ B ω q := by
      funext t
      have h1 : drive κ (fun r ω => B (s + r) ω - B s ω) ω t =
          drive κ (fun r ω => B (s + r) ω - B s ω) ω (max t 0) := by
        simp only [drive, toNNReal_max_zero']
      rw [h1, RS.drive_shift κ B s ω (le_max_right t 0), hsq]
    rw [← hdrv]
    exact hω y hy T hT
  filter_upwards [ae_all_iff.2 hq, RegUnif.ae_drive_good hB κ] with ω hω hdr u hu x hx T hT
  exact shift_alive_of_rat hdr.1 (fun q hq0 => hω q hq0) hu hx hT

end F1
end QuantumZipper
