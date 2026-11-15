/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VnEnd
import InteractingSLE.Spec.Restart.FlowStopIdentLLTerminal
import InteractingSLE.WangWu.SeedTailLandingGap
import InteractingSLE.Foundations.Loewner.TraceClose
import InteractingSLE.Spec.Supplement.SB2LkS2
import InteractingSLE.Spec.Sec5.KillArcSwallow
import InteractingSLE.Spec.Sec5.Prop59NodeTreeFlow
import InteractingSLE.Spec.Supplement.GW2RdLand

/-!
# SB2(1)'s step 3, deterministic core: force-point collisions are real visits of the trace

Packet PROVE-AUX61-NOJUMP (decision D4, option B, step 3: `relLife = ζc`). The relative and the original thresholds
are both "a first visit to a real boundary point with outward cumulative weight `≤ −2`". This file proves the
Loewner half: at a time `σ` before which the zero right gap stays open, a right force image collides with the driver
exactly when the trace is at a real point at or right of the mark.

* **`rightImg_eq_iff_real_tip`**: for a continuous driver `U` from `0` with a Loewner trace `η` continuous on
  `[0, σ]`, if `U t < rightImg U 0 t` for `0 < t < σ` and `η σ ≠ 0`, then for every mark `x ≥ 0`
  `rightImg U x σ = U σ ↔ (η σ).im = 0 ∧ x ≤ (η σ).re`.
* Ingredients:
  * `TraceClose.hasBdryLimits_of_isLoewnerTraceLT` and `TraceClose.extendFrom_zero_eq` (the boundary extension at
    the horizon and its tip);
  * `FlowStopIdentLL.real_tip_of_rightImg_eq` (a collision puts the tip on `ℝ` right of the mark);
  * `WangWu.SeedTail.rightImg_zero_eq_of_real_terminal` (a positive-real tip forces the zero collision);
  * `FlowStopIdentLL.rightImg_eq_iff_of_zero_collision` (the colliding marks form the interval up to the tip).
* **`no_rightImg_eq_before_first_visit`**: before the trace's first visit to `(0, ∞)` (and with no return to `0`)
  no right mark `x ≥ 0` collides. **`rightImg_eq_iff_at_first_visit`**: at that first visit the colliding right
  marks are exactly those at or left of the tip.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Vo

open MartChar.RealFlow

variable {U : ℝ → ℝ} {η : ℝ → ℂ} {σ : ℝ}

/-- **Right collisions at a horizon with an open zero gap are real visits of the tip.** -/
theorem rightImg_eq_iff_real_tip (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 < σ) (hη : IsLoewnerTraceLT U σ η)
    (hc : ContinuousOn η (Icc 0 σ)) (hsep : ∀ t ∈ Ioo 0 σ, U t < rightImg U 0 t) (hne : η σ ≠ 0) {x : ℝ}
    (hx : 0 ≤ x) : rightImg U x σ = U σ ↔ (η σ).im = 0 ∧ x ≤ (η σ).re := by
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 hσ hc
  have htip := TraceClose.extendFrom_zero_eq hη hU hU0 hσ hc
  constructor
  · exact Restart.FlowStopIdentLL.real_tip_of_rightImg_eq hU hU0 hσ.le hB htip
  · rintro ⟨him, hxr⟩
    have hend : η σ = (((η σ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hpos : 0 < (η σ).re := by
      rcases (hx.trans hxr).lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by simp [← h]) (by simp [him])) hne
    have hzero := WangWu.SeedTail.rightImg_zero_eq_of_real_terminal hU hU0 hσ hpos hη hc hend hsep
    exact (Restart.FlowStopIdentLL.rightImg_eq_iff_of_zero_collision hU hU0 hσ.le hB htip hzero x).2 hxr

/-- A Loewner trace before a horizon is one before every earlier horizon. -/
theorem isLoewnerTraceLT_mono {T T' : ℝ} (hη : IsLoewnerTraceLT U T η) (hT : T' ≤ T) :
    IsLoewnerTraceLT U T' η :=
  ⟨hη.1, hη.2.1.mono fun _ ht => ⟨ht.1, lt_of_lt_of_le ht.2 hT⟩,
    fun t ht htT => hη.2.2 t ht (lt_of_lt_of_le htT hT)⟩

/-- **No right collision before the trace's first visit to `(0, ∞)`** (with no return to `0`). -/
theorem no_rightImg_eq_before_first_visit (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ}
    (hη : IsLoewnerTraceLT U T η) (hc : ContinuousOn η (Ico 0 T)) (hne : ∀ t ∈ Ioo 0 T, η t ≠ 0) {σ : ℝ}
    (hσT : σ < T) (hvis : ∀ t ∈ Ioc 0 σ, ¬ ((η t).im = 0 ∧ 0 < (η t).re)) {x : ℝ} (hx : 0 ≤ x)
    {t : ℝ} (ht : t ∈ Ioc 0 σ) : rightImg U x t ≠ U t := by
  intro hcoll
  have ht0 : 0 < t := ht.1
  have htT : t < T := lt_of_le_of_lt ht.2 hσT
  have hη' : IsLoewnerTraceLT U t η := isLoewnerTraceLT_mono hη htT.le
  have hc' : ContinuousOn η (Icc 0 t) := hc.mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη' hU hU0 ht0 hc'
  have htip := TraceClose.extendFrom_zero_eq hη' hU hU0 ht0 hc'
  obtain ⟨him, hxr⟩ := Restart.FlowStopIdentLL.real_tip_of_rightImg_eq hU hU0 ht0.le hB htip hcoll
  have hne' : η t ≠ 0 := hne t ⟨ht0, htT⟩
  have hpos : 0 < (η t).re := by
    rcases (hx.trans hxr).lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext (by simp [← h]) (by simp [him])) hne'
  exact hvis t ht ⟨him, hpos⟩

/-- **At the first visit to `(0, ∞)` the colliding right marks are those at or left of the tip.** -/
theorem rightImg_eq_iff_at_first_visit (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ}
    (hη : IsLoewnerTraceLT U T η) (hc : ContinuousOn η (Ico 0 T)) (hne : ∀ t ∈ Ioo 0 T, η t ≠ 0) {σ : ℝ}
    (hσ : 0 < σ) (hσT : σ < T) (hvis : ∀ t ∈ Ioo 0 σ, ¬ ((η t).im = 0 ∧ 0 < (η t).re)) {x : ℝ} (hx : 0 ≤ x) :
    rightImg U x σ = U σ ↔ (η σ).im = 0 ∧ x ≤ (η σ).re := by
  have hsep : ∀ t ∈ Ioo 0 σ, U t < rightImg U 0 t := fun t ht => by
    refine lt_of_le_of_ne (le_rightImg hU 0 ht.1.le) fun h => ?_
    have hvis' : ∀ s ∈ Ioc 0 t, ¬ ((η s).im = 0 ∧ 0 < (η s).re) := fun s hs =>
      hvis s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    exact no_rightImg_eq_before_first_visit hU hU0 hη hc hne (ht.2.trans hσT) hvis' le_rfl
      ⟨ht.1, le_rfl⟩ h.symm
  exact rightImg_eq_iff_real_tip hU hU0 hσ (isLoewnerTraceLT_mono hη hσT.le)
    (hc.mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hσT⟩) hsep (hne σ ⟨hσ, hσT⟩) hx

/-! ### Left marks, by reflection -/

/-- **The reflected trace** `t ↦ −conj (η t)` is a Loewner trace of the negated driver. -/
theorem isLoewnerTraceLT_reflect (hη : IsLoewnerTraceLT U σ η) :
    IsLoewnerTraceLT (-U) σ (fun t => LP.reflectC (η t)) := by
  refine ⟨by show LP.reflectC (η 0) = 0; rw [hη.1, LP.reflectC_zero],
    LP.continuous_reflectC.comp_continuousOn hη.2.1, fun t ht htσ => ?_⟩
  rw [LP.fwdHull_neg, hη.2.2 t ht htσ, ← LP.fillH_image_reflectC, image_image]

/-- **Left collisions at a horizon with an open zero gap are real visits of the tip** (left marks `x ≤ 0`, read as
right marks `−x` of the negated driver). -/
theorem rightImg_neg_eq_iff_real_tip (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 < σ)
    (hη : IsLoewnerTraceLT U σ η) (hc : ContinuousOn η (Icc 0 σ))
    (hsep : ∀ t ∈ Ioo 0 σ, -U t < rightImg (-U) 0 t) (hne : η σ ≠ 0) {x : ℝ} (hx : x ≤ 0) :
    rightImg (-U) (-x) σ = -U σ ↔ (η σ).im = 0 ∧ (η σ).re ≤ x := by
  have hU' : Continuous (-U) := hU.neg
  have hU0' : (-U) 0 = 0 := by simp [hU0]
  have hne' : LP.reflectC (η σ) ≠ 0 := fun h => hne (by
    rw [← LP.reflectC_reflectC (η σ), h, LP.reflectC_zero])
  have hc' : ContinuousOn (fun t => LP.reflectC (η t)) (Icc 0 σ) := LP.continuous_reflectC.comp_continuousOn hc
  have key := rightImg_eq_iff_real_tip hU' hU0' hσ (isLoewnerTraceLT_reflect hη) hc' hsep hne' (neg_nonneg.2 hx)
  have key' : rightImg (-U) (-x) σ = -U σ ↔
      (LP.reflectC (η σ)).im = 0 ∧ -x ≤ (LP.reflectC (η σ)).re := key
  rw [key']
  simp only [LP.reflectC, Complex.neg_im, Complex.conj_im, neg_neg, Complex.neg_re, Complex.conj_re, neg_le_neg_iff]

/-! ### Later contacts: restarting the real flow at the last collision -/

/-- **A later collision**: if the image of a right mark `a` collides with the driver at `S`, the gap stays open on
`(S, T)`, and a real point `x` alive at `S` dies by `T`, then the image of `a` collides again at `T`. This is
`KillArc.rightImg_eq_of_not_alive` for the driver restarted at `S` (the flow property
`Prop59NodeTree.rightImg_shiftDrv` and `Prop59NodeTree.alive_of_shift`). -/
theorem rightImg_eq_of_not_alive_after (hU : Continuous U) {S T a x : ℝ} (hS : 0 ≤ S) (hST : S < T)
    (hcoll : rightImg U a S = U S) (hsep : ∀ t ∈ Ioo S T, U t < rightImg U a t)
    (hxS : Alive U x S) (hxT : ¬ Alive U x T) : rightImg U a T = U T := by
  set U' := Sec5.Prop59NodeTree.shiftDrv U S with hU'def
  have hU' : Continuous U' := Sec5.Prop59NodeTree.continuous_shiftDrv hU S
  have hU'0 : U' 0 = 0 := by simp [hU'def, Sec5.Prop59NodeTree.shiftDrv]
  have hTS : 0 < T - S := sub_pos.2 hST
  -- the flow property at the collision
  have hflow : ∀ r : ℝ, 0 ≤ r → rightImg U' 0 r = rightImg U a (S + r) - U S := fun r hr => by
    have := Sec5.Prop59NodeTree.rightImg_shiftDrv hU hS hr a
    rwa [hcoll, sub_self] at this
  have hU'r : ∀ r, U' r = U (S + r) - U S := fun r => rfl
  have hx'pos : 0 < cflow U x S := by
    have := hxS.lt_gImg hU ⟨hS, le_rfl⟩
    simp only [gImg] at this
    linarith
  have hsep' : ∀ t ∈ Ioo 0 (T - S), U' t < rightImg U' 0 t := fun t ht => by
    rw [hflow t ht.1.le, hU'r]
    have := hsep (S + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith
  have hdead : ¬ Alive U' (cflow U x S) (T - S) := fun h' => hxT (by
    have := Sec5.Prop59NodeTree.alive_of_shift hU hS hTS.le hxS h'
    rwa [add_sub_cancel] at this)
  have key := Sec5.KillArc.rightImg_eq_of_not_alive hU' hU'0 hTS le_rfl hx'pos hsep' hdead
  rw [hflow _ hTS.le, hU'r, add_sub_cancel] at key
  linarith

/-- **A later right contact is a collision**: if the zero right mark collided at `S` and its gap stays open on
`(S, σ)`, and the tip at `σ` is the real point `y > 0` while some real point of `(0, y]` was still alive at `S`,
then the zero mark collides at `σ` (the landing swallows that point, `GW2Rd.not_alive_of_tip_eq_pos`). -/
theorem rightImg_zero_eq_at_later_real_tip (hU : Continuous U) (hU0 : U 0 = 0) {S y x : ℝ} (hS : 0 ≤ S)
    (hSσ : S < σ) (hcoll : rightImg U 0 S = U S) (hsep : ∀ t ∈ Ioo S σ, U t < rightImg U 0 t)
    (htip : Tendsto (fwdMapInv U σ) (𝓝[H] 0) (𝓝 (y : ℂ))) (hx : 0 < x) (hxy : x ≤ y) (hxS : Alive U x S) :
    rightImg U 0 σ = U σ :=
  rightImg_eq_of_not_alive_after hU hS hSσ hcoll hsep hxS fun h =>
    Theorem14.GW2Rd.not_alive_of_tip_eq_pos hU hU0 (hS.trans hSσ.le) htip hx hxy
      ⟨_, WangWu.isForwardSol_of_alive hU h⟩

/-- **The colliding right marks at a later real contact are those at or left of the tip.** -/
theorem rightImg_eq_iff_at_later_real_tip (hU : Continuous U) (hU0 : U 0 = 0) {S y x : ℝ} (hS : 0 ≤ S)
    (hSσ : S < σ) (hcoll : rightImg U 0 S = U S) (hsep : ∀ t ∈ Ioo S σ, U t < rightImg U 0 t)
    (hB : HasBdryLimits (fwdMapInv U σ)) (htip : extendFrom H (fwdMapInv U σ) 0 = (y : ℂ)) (hx : 0 < x)
    (hxy : x ≤ y) (hxS : Alive U x S) (z : ℝ) : rightImg U z σ = U σ ↔ z ≤ y := by
  have hσ : 0 ≤ σ := hS.trans hSσ.le
  have hlim : Tendsto (fwdMapInv U σ) (𝓝[H] 0) (𝓝 (y : ℂ)) := by
    rw [← htip]
    exact hB.tendsto (show (0 : ℂ) ∈ Hbar by simp [Hbar])
  have hzero := rightImg_zero_eq_at_later_real_tip hU hU0 hS hSσ hcoll hsep hlim hx hxy hxS
  have := Restart.FlowStopIdentLL.rightImg_eq_iff_of_zero_collision hU hU0 hσ hB htip hzero z
  simpa using this

end InteractingSLE.Theorem14.SB.Vo
