/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailPullback
import InteractingSLE.Spec.Zhan.UpperPoint

/-!
# The strip driver as a constant drift plus an error: `ξ_t = √κ B̃_t + σ t + ∫₀ᵗ e`

Packet PROVE-ZHAN-A4. Astra, *Formalization proofs* L1556–L1558 (the strip endpoint theorem): "The driver is
`ξ_t = √κ B_t + σ t + ∫₀ᵗ e_s ds`, `σ = (q₋ − q₊)/2 ∈ (−1, 1)`, where `|e_t| ≤ C e^{−ct}` eventually."

For an R36 strip path with lower left marks `pᴸᵢ` and lower right marks `pᴿⱼ` (strip coordinates
`stripPoint … t`) put `Xᵢ = ξ − pᴸᵢ > 0`, `Yⱼ = pᴿⱼ − ξ > 0` and `C(x) = coth(x/2)`. A lower point solves
`p' = C(p − ξ)` (`IsSepMark.stripPoint_eq_add_integral_of_lt`), so

* `Xᵢ(t) − Xᵢ(s) = (ξ_t − ξ_s) + ∫ₛᵗ C(Xᵢ)` and `Yⱼ(t) − Yⱼ(s) = −(ξ_t − ξ_s) + ∫ₛᵗ C(Yⱼ)`;
* with PROVE-ZHAN-A2's driving identity `ξ_t = √κ B̃_t − Σᵢ (ρᴸᵢ/2)(pᴸᵢ(t) − pᴸᵢ) − Σⱼ (ρᴿⱼ/2)(pᴿⱼ(t) − pᴿⱼ) +
  ((τ₋ − τ₊)/2) t` this is `ξ_t = √κ B̃_t + σ t + ∫₀ᵗ e` with
  `e = Σᵢ (ρᴸᵢ/2)(C(Xᵢ) − 1) − Σⱼ (ρᴿⱼ/2)(C(Yⱼ) − 1)` (`stripErr`).

## Main results

* `IsSepMark.stripPoint_eq_add_integral_of_lt`: the integrated lower-point equation;
* `StripGood`: the pathwise data of a strip evolution used below (path, unbounded clock, noncollision on the strip
  life);
* `StripGood.gapL_sub`, `StripGood.gapR_sub`: the gap equations; `StripGood.gapL_pos`, `StripGood.gapR_pos`;
* `StripGood.stripDriver_eq`: `ξ_t = √κ B̃_t + σ t + ∫₀ᵗ e` from the driving identity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec4

theorem cothHalf_neg (x : ℝ) : cothHalf (-x) = -cothHalf x := by
  unfold cothHalf
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · have hE : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    have h1 : Real.exp x - 1 ≠ 0 := sub_ne_zero.2 (fun h' => h ((Real.exp_eq_one_iff x).1 h'))
    have h2 : (Real.exp x)⁻¹ - 1 ≠ 0 := by
      intro h'
      apply h1
      have : (Real.exp x)⁻¹ = 1 := by linarith
      rw [inv_eq_one] at this
      rw [this]; ring
    rw [Real.exp_neg, eq_neg_iff_add_eq_zero, div_add_div _ _ h2 h1, div_eq_zero_iff]
    left
    field_simp
    ring

theorem cothHalf_sub_one_eq {x : ℝ} (hx : x ≠ 0) : cothHalf x - 1 = 2 / (Real.exp x - 1) := by
  unfold cothHalf
  have h : Real.exp x - 1 ≠ 0 := sub_ne_zero.2 (fun h' => hx ((Real.exp_eq_one_iff x).1 h'))
  field_simp
  ring

theorem continuousOn_cothHalf : ContinuousOn cothHalf {x | x ≠ 0} := by
  unfold cothHalf
  refine (Real.continuous_exp.continuousOn.add continuousOn_const).div
    (Real.continuous_exp.continuousOn.sub continuousOn_const) fun x hx => ?_
  exact sub_ne_zero.2 fun h' => hx ((Real.exp_eq_one_iff x).1 h')

theorem measurable_cothHalf : Measurable cothHalf := by
  unfold cothHalf; fun_prop

end Sec4

namespace Strip

namespace IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

/-- A lower point path off the driver has a continuous `coth((p − ξ)/2)` on `[0, t(S)]`. -/
theorem continuousOn_cothHalf_lower (h : IsSepMark w v S) {y : ℝ → ℝ} (hy : ContinuousOn y (Icc 0 S))
    (hyw : ∀ s ∈ Icc 0 S, y s ≠ w s) (hvy : ∀ s ∈ Icc 0 S, v s < y s) :
    ContinuousOn (fun u => Sec4.cothHalf (stripPoint w v y u - stripDriver w v u))
      (Icc 0 (stripClock w v S)) := by
  have hp := h.continuousOn_stripPoint hy fun s hs => (hvy s hs).ne'
  have hne : ∀ u ∈ Icc 0 (stripClock w v S), stripPoint w v y u - stripDriver w v u ≠ 0 := by
    intro u hu
    have hs := h.chordalTime_mem hu
    have hpos : 0 < w (chordalTime w v u) - v (chordalTime w v u) := sub_pos.2 (h.lt _ hs)
    have hpos' : 0 < |y (chordalTime w v u) - v (chordalTime w v u)| :=
      abs_pos.2 (sub_ne_zero.2 (hvy _ hs).ne')
    rw [stripPoint, stripDriver, show u + Real.log |y (chordalTime w v u) - v (chordalTime w v u)| -
      (u + Real.log (w (chordalTime w v u) - v (chordalTime w v u))) =
      Real.log |y (chordalTime w v u) - v (chordalTime w v u)| -
        Real.log (w (chordalTime w v u) - v (chordalTime w v u)) by ring, sub_ne_zero]
    intro hlog
    have := Real.log_injOn_pos hpos' hpos hlog
    rw [abs_of_pos (sub_pos.2 (hvy _ hs))] at this
    exact hyw _ hs (by linarith)
  exact Sec4.continuousOn_cothHalf.comp (hp.sub h.continuousOn_stripDriver) fun u hu => hne u hu

/-- **The integrated lower-point equation**: a chordal real point path `y > v` that never meets the driver on
`[0, S]` has strip coordinate `p_t = p_0 + ∫₀ᵗ coth((p_u − ξ_u)/2) du` on `[0, t(S)]`. -/
theorem stripPoint_eq_add_integral_of_lt (h : IsSepMark w v S) {y : ℝ → ℝ}
    (hy : ContinuousOn y (Icc 0 S)) (hint : IntervalIntegrable (fun u => 2 / (y u - w u)) volume 0 S)
    (heq : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ u in (0 : ℝ)..s, 2 / (y u - w u))
    (hyw : ∀ s ∈ Icc 0 S, y s ≠ w s) (hvy : ∀ s ∈ Icc 0 S, v s < y s) {t : ℝ}
    (ht : t ∈ Icc 0 (stripClock w v S)) :
    stripPoint w v y t = stripPoint w v y 0 +
      ∫ u in (0 : ℝ)..t, Sec4.cothHalf (stripPoint w v y u - stripDriver w v u) := by
  have hsub : Icc 0 t ⊆ Icc 0 (stripClock w v S) := Icc_subset_Icc le_rfl ht.2
  have hp := h.continuousOn_stripPoint hy fun s hs => (hvy s hs).ne'
  have hne : ∀ u ∈ Icc 0 (stripClock w v S), stripPoint w v y u - stripDriver w v u ≠ 0 := by
    intro u hu
    have hs := h.chordalTime_mem hu
    have hpos : 0 < w (chordalTime w v u) - v (chordalTime w v u) := sub_pos.2 (h.lt _ hs)
    have hpos' : 0 < |y (chordalTime w v u) - v (chordalTime w v u)| :=
      abs_pos.2 (sub_ne_zero.2 (hvy _ hs).ne')
    rw [stripPoint, stripDriver, show u + Real.log |y (chordalTime w v u) - v (chordalTime w v u)| -
      (u + Real.log (w (chordalTime w v u) - v (chordalTime w v u))) =
      Real.log |y (chordalTime w v u) - v (chordalTime w v u)| -
        Real.log (w (chordalTime w v u) - v (chordalTime w v u)) by ring, sub_ne_zero]
    intro hlog
    have := Real.log_injOn_pos hpos' hpos hlog
    rw [abs_of_pos (sub_pos.2 (hvy _ hs))] at this
    exact hyw _ hs (by linarith)
  have hcont : ContinuousOn (fun u => Sec4.cothHalf (stripPoint w v y u - stripDriver w v u)) (Icc 0 t) :=
    Sec4.continuousOn_cothHalf.comp ((hp.sub h.continuousOn_stripDriver).mono hsub)
      fun u hu => hne u (hsub hu)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hp.mono hsub)
    (fun u hu => h.hasDerivAt_stripPoint_of_lt hy hint heq ⟨hu.1, hu.2.trans_le ht.2⟩
      (hyw _ (h.chordalTime_mem ⟨hu.1.le, hu.2.le.trans ht.2⟩))
      (hvy _ (h.chordalTime_mem ⟨hu.1.le, hu.2.le.trans ht.2⟩)))
    (hcont.intervalIntegrable_of_Icc ht.1)]
  ring

end IsSepMark

end Strip

namespace Zhan

open Strip

variable {nL nR : ℕ}

/-! ### Strip gaps and the drift error along a path -/

/-- The strip gap `Xᵢ = ξ − pᴸᵢ` of the lower left mark `i`. -/
def gapL (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (i : Fin nL) (t : ℝ) : ℝ :=
  stripDriver (extPath w) (extPath (vL (Fin.last nL))) t -
    stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vL i.castSucc)) t

/-- The strip gap `Yⱼ = pᴿⱼ − ξ` of the lower right mark `j`. -/
def gapR (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (j : Fin nR) (t : ℝ) : ℝ :=
  stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vR j)) t -
    stripDriver (extPath w) (extPath (vL (Fin.last nL))) t

/-- **The drift error** `e = Σᵢ (ρᴸᵢ/2)(C(Xᵢ) − 1) − Σⱼ (ρᴿⱼ/2)(C(Yⱼ) − 1)`, `C(x) = coth(x/2)`. -/
def stripErr (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  (∑ i, ρL i / 2 * (Sec4.cothHalf (gapL w vL i t) - 1)) -
    ∑ j, ρR j / 2 * (Sec4.cothHalf (gapR w vL vR j t) - 1)

/-- The pathwise data of a strip evolution used for the whole-tail step: the integrated path, the unbounded
strip clock (clause (1), PROVE-ZHAN-A3) and noncollision of the lower marks on the strip life (PROVE-ZHAN-A3). -/
structure StripGood (a : ℝ) (pL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    Prop where
  path : IsIntegratedSLEPath a (wordXL pL) xR ρL ρR w vL vR b ζ
  clock : HasUnboundedStripClock w (vL (Fin.last nL)) ζ
  noncoll : ∀ s : ℝ≥0, IsStripLife w (vL (Fin.last nL)) ζ s →
    (∀ i : Fin nL, vL i.castSucc s < w s) ∧ ∀ j : Fin nR, w s < vR j s

namespace StripGood

variable {a : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem isStripPath (h : StripGood a pL xR ρL ρR w vL vR b ζ) : IsStripPath w (vL (Fin.last nL)) ζ :=
  h.path.isStripPath h.clock

theorem exists_life (h : StripGood a pL xR ρL ρR w vL vR b ζ) (t : ℝ) :
    ∃ S : ℝ≥0, IsStripLife w (vL (Fin.last nL)) ζ S ∧
      t ≤ stripClock (extPath w) (extPath (vL (Fin.last nL))) S :=
  h.clock t

theorem isSepMark (h : StripGood a pL xR ρL ρR w vL vR b ζ) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) :
    IsSepMark (extPath w) (extPath (vL (Fin.last nL))) S :=
  isSepMark_of_isIntegratedSLEPath h.path hS

/-- A real time of `[0, S]` read through `toNNReal` lies in the strip life. -/
theorem life_toNNReal {S : ℝ≥0} (hS : IsStripLife w (vL (Fin.last nL)) ζ S) {s : ℝ} (hs : s ∈ Icc 0 (S : ℝ)) :
    IsStripLife w (vL (Fin.last nL)) ζ s.toNNReal :=
  hS.mono (Real.toNNReal_le_iff_le_coe.2 hs.2)

/-- The data of the lower-point equation for a lower mark path `y` with `v < y`, `y ≠ w` on the strip life,
solving `y = y₀ + ∫ 2/(y − w)` with integrable reciprocal gap. -/
theorem stripPoint_eq_of_lowerMark (h : StripGood a pL xR ρL ρR w vL vR b ζ) {y : ℝ≥0 → ℝ}
    (hyc : ContinuousOn y {t | (t : ℝ≥0∞) < ζ})
    (hyi : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - y s.toNNReal)⁻¹) volume 0 t)
    (hyeq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → y t = y 0 + ∫ s in (0 : ℝ)..t, 2 / (y s.toNNReal - w s.toNNReal))
    (hyw : ∀ s : ℝ≥0, IsStripLife w (vL (Fin.last nL)) ζ s → y s ≠ w s)
    (hvy : ∀ s : ℝ≥0, IsStripLife w (vL (Fin.last nL)) ζ s → vL (Fin.last nL) s < y s)
    {S : ℝ≥0} (hS : IsStripLife w (vL (Fin.last nL)) ζ S) {t : ℝ}
    (ht : t ∈ Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :
    stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath y) t =
      stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath y) 0 +
      ∫ u in (0 : ℝ)..t, Sec4.cothHalf (stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath y) u -
        stripDriver (extPath w) (extPath (vL (Fin.last nL))) u) := by
  have hm := h.isSepMark hS
  refine hm.stripPoint_eq_add_integral_of_lt (continuousOn_extPath hyc hS.1) ?_ (fun s hs => ?_)
    (fun s hs => hyw _ (life_toNNReal hS hs)) (fun s hs => hvy _ (life_toNNReal hS hs)) ht
  · have e : (fun u => 2 / (extPath y u - extPath w u)) =
        fun u => (-2) * (w u.toNNReal - y u.toNNReal)⁻¹ := by
      funext u
      simp only [extPath]
      rw [div_eq_mul_inv, ← neg_sub, inv_neg]; ring
    rw [e]
    exact (hyi S hS.1).const_mul (-2)
  · have hlt := (life_toNNReal hS hs).1
    simp only [extPath]
    rw [hyeq _ hlt, Real.coe_toNNReal _ hs.1, Real.toNNReal_zero]

/-- The lower-point equation for the lower left mark `i`. -/
theorem stripPoint_eq_left (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) {t : ℝ}
    (ht : t ∈ Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :
    stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vL i.castSucc)) t =
      stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vL i.castSucc)) 0 +
      ∫ u in (0 : ℝ)..t, Sec4.cothHalf (stripPoint (extPath w) (extPath (vL (Fin.last nL)))
        (extPath (vL i.castSucc)) u - stripDriver (extPath w) (extPath (vL (Fin.last nL))) u) := by
  have hF := h.path.isForcePath
  refine h.stripPoint_eq_of_lowerMark (hF.continuousOn_vL _) (fun t ht => hF.integrable_gapL ht _)
    (fun t ht => ?_) (fun s hs => ((h.noncoll s hs).1 i).ne)
    (fun s hs => vL_last_lt_vL_castSucc h.path hs i) hS ht
  rw [hF.vL_eq ht, hF.vL_zero]

/-- The lower-point equation for the lower right mark `j`. -/
theorem stripPoint_eq_right (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j : Fin nR) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) {t : ℝ}
    (ht : t ∈ Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :
    stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vR j)) t =
      stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vR j)) 0 +
      ∫ u in (0 : ℝ)..t, Sec4.cothHalf (stripPoint (extPath w) (extPath (vL (Fin.last nL)))
        (extPath (vR j)) u - stripDriver (extPath w) (extPath (vL (Fin.last nL))) u) := by
  have hF := h.path.isForcePath
  refine h.stripPoint_eq_of_lowerMark (hF.continuousOn_vR _) (fun t ht => hF.integrable_gapR ht _)
    (fun t ht => ?_) (fun s hs => ((h.noncoll s hs).2 j).ne')
    (fun s hs => (hs.2 s le_rfl).trans ((h.noncoll s hs).2 j)) hS ht
  rw [hF.vR_eq ht, hF.vR_zero]

theorem continuousOn_left (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) :
    ContinuousOn (fun u => Sec4.cothHalf (stripPoint (extPath w) (extPath (vL (Fin.last nL)))
      (extPath (vL i.castSucc)) u - stripDriver (extPath w) (extPath (vL (Fin.last nL))) u))
      (Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :=
  (h.isSepMark hS).continuousOn_cothHalf_lower (continuousOn_extPath (h.path.isForcePath.continuousOn_vL _) hS.1)
    (fun _ hs => ((h.noncoll _ (life_toNNReal hS hs)).1 i).ne)
    (fun _ hs => vL_last_lt_vL_castSucc h.path (life_toNNReal hS hs) i)

theorem continuousOn_right (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j : Fin nR) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) :
    ContinuousOn (fun u => Sec4.cothHalf (stripPoint (extPath w) (extPath (vL (Fin.last nL)))
      (extPath (vR j)) u - stripDriver (extPath w) (extPath (vL (Fin.last nL))) u))
      (Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :=
  (h.isSepMark hS).continuousOn_cothHalf_lower (continuousOn_extPath (h.path.isForcePath.continuousOn_vR _) hS.1)
    (fun _ hs => ((h.noncoll _ (life_toNNReal hS hs)).2 j).ne')
    (fun _ hs => ((life_toNNReal hS hs).2 _ le_rfl).trans ((h.noncoll _ (life_toNNReal hS hs)).2 j))

/-- **The left gap equation**: `Xᵢ(t) − Xᵢ(s) = (ξ_t − ξ_s) + ∫ₛᵗ C(Xᵢ)`. -/
theorem gapL_sub (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    gapL w vL i t - gapL w vL i s =
      (stripDriver (extPath w) (extPath (vL (Fin.last nL))) t -
        stripDriver (extPath w) (extPath (vL (Fin.last nL))) s) +
      ∫ u in s..t, Sec4.cothHalf (gapL w vL i u) := by
  obtain ⟨S, hS, htS⟩ := h.exists_life t
  have ht : t ∈ Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S) := ⟨hs.trans hst, htS⟩
  have hs' : s ∈ Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S) := ⟨hs, hst.trans htS⟩
  have hc := h.continuousOn_left i hS
  have h1 := h.stripPoint_eq_left i hS ht
  have h2 := h.stripPoint_eq_left i hS hs'
  have hsub := intervalIntegral.integral_interval_sub_left (μ := volume)
    ((hc.mono (uIcc_subset_Icc ⟨le_rfl, hs.trans (hst.trans htS)⟩ ht)).intervalIntegrable)
    ((hc.mono (uIcc_subset_Icc ⟨le_rfl, hs.trans (hst.trans htS)⟩ hs')).intervalIntegrable)
  have hneg : ∫ u in s..t, Sec4.cothHalf (gapL w vL i u) =
      -∫ u in s..t, Sec4.cothHalf (stripPoint (extPath w) (extPath (vL (Fin.last nL)))
        (extPath (vL i.castSucc)) u - stripDriver (extPath w) (extPath (vL (Fin.last nL))) u) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [gapL]
    rw [← Sec4.cothHalf_neg, neg_sub]
  rw [hneg]
  simp only [gapL]
  linarith

/-- **The right gap equation**: `Yⱼ(t) − Yⱼ(s) = −(ξ_t − ξ_s) + ∫ₛᵗ C(Yⱼ)`. -/
theorem gapR_sub (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j : Fin nR) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    gapR w vL vR j t - gapR w vL vR j s =
      -(stripDriver (extPath w) (extPath (vL (Fin.last nL))) t -
        stripDriver (extPath w) (extPath (vL (Fin.last nL))) s) +
      ∫ u in s..t, Sec4.cothHalf (gapR w vL vR j u) := by
  obtain ⟨S, hS, htS⟩ := h.exists_life t
  have ht : t ∈ Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S) := ⟨hs.trans hst, htS⟩
  have hs' : s ∈ Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S) := ⟨hs, hst.trans htS⟩
  have hc := h.continuousOn_right j hS
  have h1 := h.stripPoint_eq_right j hS ht
  have h2 := h.stripPoint_eq_right j hS hs'
  have hsub := intervalIntegral.integral_interval_sub_left (μ := volume)
    ((hc.mono (uIcc_subset_Icc ⟨le_rfl, hs.trans (hst.trans htS)⟩ ht)).intervalIntegrable)
    ((hc.mono (uIcc_subset_Icc ⟨le_rfl, hs.trans (hst.trans htS)⟩ hs')).intervalIntegrable)
  have heq : ∫ u in s..t, Sec4.cothHalf (gapR w vL vR j u) =
      ∫ u in s..t, Sec4.cothHalf (stripPoint (extPath w) (extPath (vL (Fin.last nL)))
        (extPath (vR j)) u - stripDriver (extPath w) (extPath (vL (Fin.last nL))) u) := rfl
  rw [heq]
  simp only [gapR]
  linarith

theorem continuousOn_cothHalf_gapL (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) :
    ContinuousOn (fun u => Sec4.cothHalf (gapL w vL i u))
      (Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :=
  (h.continuousOn_left i hS).neg.congr fun u _ => by
    simp only [gapL, Pi.neg_apply]; rw [← Sec4.cothHalf_neg, neg_sub]

theorem continuousOn_cothHalf_gapR (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j : Fin nR) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) :
    ContinuousOn (fun u => Sec4.cothHalf (gapR w vL vR j u))
      (Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :=
  h.continuousOn_right j hS

theorem continuousOn_gapL (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) :
    ContinuousOn (gapL w vL i) (Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :=
  (h.isSepMark hS).continuousOn_stripDriver.sub ((h.isSepMark hS).continuousOn_stripPoint
    (continuousOn_extPath (h.path.isForcePath.continuousOn_vL _) hS.1)
    fun _ hs => (vL_last_lt_vL_castSucc h.path (life_toNNReal hS hs) i).ne')

theorem continuousOn_gapR (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j : Fin nR) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) :
    ContinuousOn (gapR w vL vR j) (Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :=
  ((h.isSepMark hS).continuousOn_stripPoint
    (continuousOn_extPath (h.path.isForcePath.continuousOn_vR _) hS.1)
    fun _ hs => (((life_toNNReal hS hs).2 _ le_rfl).trans
      ((h.noncoll _ (life_toNNReal hS hs)).2 j)).ne').sub (h.isSepMark hS).continuousOn_stripDriver

theorem continuousOn_stripDriver' (h : StripGood a pL xR ρL ρR w vL vR b ζ) {S : ℝ≥0}
    (hS : IsStripLife w (vL (Fin.last nL)) ζ S) :
    ContinuousOn (stripDriver (extPath w) (extPath (vL (Fin.last nL))))
      (Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S)) :=
  (h.isSepMark hS).continuousOn_stripDriver

/-- The strip gaps are positive. -/
theorem gapL_pos (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) {t : ℝ} (ht : 0 ≤ t) :
    0 < gapL w vL i t := by
  obtain ⟨S, hS, htS⟩ := h.exists_life t
  have hm := h.isSepMark hS
  have hs := hm.chordalTime_mem ⟨ht, htS⟩
  have hl := life_toNNReal hS hs
  have h1 := vL_last_lt_vL_castSucc h.path hl i
  have h2 := (h.noncoll _ hl).1 i
  simp only [gapL, stripDriver, stripPoint, extPath]
  rw [abs_of_pos (sub_pos.2 h1)]
  have := Real.log_lt_log (sub_pos.2 h1) (show vL i.castSucc _ - vL (Fin.last nL) _ <
    w _ - vL (Fin.last nL) _ by linarith)
  linarith

theorem gapR_pos (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j : Fin nR) {t : ℝ} (ht : 0 ≤ t) :
    0 < gapR w vL vR j t := by
  obtain ⟨S, hS, htS⟩ := h.exists_life t
  have hm := h.isSepMark hS
  have hs := hm.chordalTime_mem ⟨ht, htS⟩
  have hl := life_toNNReal hS hs
  have h1 := hl.2 _ le_rfl
  have h2 := (h.noncoll _ hl).2 j
  simp only [gapR, stripDriver, stripPoint, extPath]
  rw [abs_of_pos (by linarith)]
  have := Real.log_lt_log (sub_pos.2 h1) (show w _ - vL (Fin.last nL) _ <
    vR j _ - vL (Fin.last nL) _ by linarith)
  linarith

theorem stripPoint_zero_left (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) :
    stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vL i.castSucc)) 0 = pL i := by
  obtain ⟨S, hS, -⟩ := h.exists_life 0
  have hF := h.path.isForcePath
  simp only [stripPoint, (h.isSepMark hS).chordalTime_zero, extPath, Real.toNNReal_zero, hF.vL_zero,
    wordXL_castSucc, wordXL_last, zero_add, sub_neg_eq_add, sub_add_cancel]
  rw [abs_of_pos (Real.exp_pos _), Real.log_exp]

theorem stripPoint_zero_right {pR : Fin nR → ℝ} (h : StripGood a pL (wordXR pR) ρL ρR w vL vR b ζ)
    (j : Fin nR) :
    stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vR j)) 0 = pR j := by
  obtain ⟨S, hS, -⟩ := h.exists_life 0
  have hF := h.path.isForcePath
  simp only [stripPoint, (h.isSepMark hS).chordalTime_zero, extPath, Real.toNNReal_zero, hF.vR_zero,
    hF.vL_zero, wordXL_last, wordXR, zero_add, sub_neg_eq_add, sub_add_cancel]
  rw [abs_of_pos (Real.exp_pos _), Real.log_exp]

/-- **The strip driver is a constant drift plus the integrated error**: from the driving identity of
PROVE-ZHAN-A2 (`exists_stripBrownian`), `ξ_t = N_t + (d + sᴸ/2 − sᴿ/2) t + ∫₀ᵗ e`. -/
theorem stripDriver_eq {pR : Fin nR → ℝ} (h : StripGood a pL (wordXR pR) ρL ρR w vL vR b ζ)
    {ρl : Fin nL → ℝ} {ρr : Fin nR → ℝ} {N : ℝ≥0 → ℝ} {d : ℝ}
    (hd : ∀ t : ℝ≥0, stripDriver (extPath w) (extPath (vL (Fin.last nL))) t = N t
      - (∑ i : Fin nL, ρl i / 2 * (stripPoint (extPath w) (extPath (vL (Fin.last nL)))
          (extPath (vL i.castSucc)) t - pL i))
      - (∑ j, ρr j / 2 * (stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vR j)) t - pR j))
      + d * t) (t : ℝ≥0) :
    stripDriver (extPath w) (extPath (vL (Fin.last nL))) t =
      N t + (d + (∑ i, ρl i) / 2 - (∑ j, ρr j) / 2) * t + ∫ u in (0 : ℝ)..t, stripErr ρl ρr w vL vR u := by
  obtain ⟨S, hS, htS⟩ := h.exists_life t
  have hsub : uIcc (0 : ℝ) t ⊆ Icc 0 (stripClock (extPath w) (extPath (vL (Fin.last nL))) S) :=
    uIcc_subset_Icc ⟨le_rfl, (NNReal.coe_nonneg t).trans htS⟩ ⟨NNReal.coe_nonneg t, htS⟩
  have hiL : ∀ i, IntervalIntegrable (fun u => Sec4.cothHalf (gapL w vL i u)) volume 0 t := fun i =>
    ((h.continuousOn_cothHalf_gapL i hS).mono hsub).intervalIntegrable
  have hiR : ∀ j, IntervalIntegrable (fun u => Sec4.cothHalf (gapR w vL vR j u)) volume 0 t := fun j =>
    ((h.continuousOn_cothHalf_gapR j hS).mono hsub).intervalIntegrable
  have hξ0 : stripDriver (extPath w) (extPath (vL (Fin.last nL))) 0 = 0 :=
    (h.isSepMark hS).stripDriver_zero (by simp [extPath, h.path.1])
  -- the lower points through the gap equations
  have hpL : ∀ i, stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vL i.castSucc)) t - pL i =
      -∫ u in (0 : ℝ)..t, Sec4.cothHalf (gapL w vL i u) := fun i => by
    have h1 := h.gapL_sub i le_rfl (NNReal.coe_nonneg t)
    have h0 := h.stripPoint_zero_left i
    have h2 : gapL w vL i t = stripDriver (extPath w) (extPath (vL (Fin.last nL))) t -
      stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vL i.castSucc)) t := rfl
    have h3 : gapL w vL i 0 = stripDriver (extPath w) (extPath (vL (Fin.last nL))) 0 -
      stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vL i.castSucc)) 0 := rfl
    linarith
  have hpR : ∀ j, stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vR j)) t - pR j =
      ∫ u in (0 : ℝ)..t, Sec4.cothHalf (gapR w vL vR j u) := fun j => by
    have h1 := h.gapR_sub j le_rfl (NNReal.coe_nonneg t)
    have h0 := h.stripPoint_zero_right j
    have h2 : gapR w vL vR j t = stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vR j)) t -
      stripDriver (extPath w) (extPath (vL (Fin.last nL))) t := rfl
    have h3 : gapR w vL vR j 0 = stripPoint (extPath w) (extPath (vL (Fin.last nL))) (extPath (vR j)) 0 -
      stripDriver (extPath w) (extPath (vL (Fin.last nL))) 0 := rfl
    linarith
  have hI : ∫ u in (0 : ℝ)..t, stripErr ρl ρr w vL vR u =
      (∑ i, ρl i / 2 * ((∫ u in (0 : ℝ)..t, Sec4.cothHalf (gapL w vL i u)) - t)) -
        ∑ j, ρr j / 2 * ((∫ u in (0 : ℝ)..t, Sec4.cothHalf (gapR w vL vR j u)) - t) := by
    unfold stripErr
    have hA : IntervalIntegrable (fun u => ∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i u) - 1)) volume 0 t :=
      (continuousOn_finsetSum _ fun i _ =>
        (((h.continuousOn_cothHalf_gapL i hS).mono hsub).sub continuousOn_const).const_mul (ρl i / 2)
        ).intervalIntegrable
    have hB : IntervalIntegrable (fun u => ∑ j, ρr j / 2 * (Sec4.cothHalf (gapR w vL vR j u) - 1))
        volume 0 t :=
      (continuousOn_finsetSum _ fun j _ =>
        (((h.continuousOn_cothHalf_gapR j hS).mono hsub).sub continuousOn_const).const_mul (ρr j / 2)
        ).intervalIntegrable
    rw [intervalIntegral.integral_sub hA hB]
    · rw [intervalIntegral.integral_finsetSum fun i _ => ((hiL i).sub intervalIntegrable_const).const_mul _,
        intervalIntegral.integral_finsetSum fun j _ => ((hiR j).sub intervalIntegrable_const).const_mul _]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hiL i) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hiR j) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  rw [hd t, hI]
  simp only [hpL, hpR]
  rw [Finset.sum_div, Finset.sum_div]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

end StripGood

end Zhan

end InteractingSLE
