/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BmContact
import InteractingSLE.Spec.Sec7.Lemma76EJunction

/-!
# The contact clause without an open zero gap (decision D17 (B), provisional)

Packet PROVE-GW2-BUF (round 10). `GW2BmContact.gapVanishes_of_canonical` asks the zero gap of the canonical driver
to stay open before the contact time `L`. At the instance it can close earlier: the relative curve may visit the
original real line in the relative chart (the physical curve touching `ℝ`) before it contacts the counterflow. What
holds instead is that the contact point lies beyond every earlier real visit: the counterflow's side `[markPos, ∞)`
is not touched before contact. This file proves the contact clause in that form.

* **`alive_of_traceLT_off`**: a real point `y > 0` that a Loewner trace does not reach from the right on `[0, t]`
  is alive at `t`. This is `Lemma76E.alive_of_trace_off` for real-time traces.
* **`rightImg_zero_eq_of_alive_tip`**: if the trace at `L` is a real point beyond a point `x₀ > 0` alive at every
  time before `L`, the zero right mark collides at `L`. Proof: restart at the last zero collision before `L` (a
  closed set) and apply NOJUMP's `SB.Vo.rightImg_zero_eq_at_later_real_tip`.
* **`rightImg_eq_of_alive_tip`**: then every mark `x` at or left of the tip collides at `L`.
* **`gapVanishes_of_collision`**: the collision of the canonical driver at `L` gives the contact clause for any
  driver agreeing with it before `L`.
* **`gapVanishes_of_canonical_off`**: the contact clause from a canonical trace that reaches a real point `≥ x₀ > 0`
  at `L` without reaching `[x₀, ∞)` before. **`gapVanishes_neg_of_canonical_off`** is its left mirror, for the
  negated driver.
* **`eqOn_trace_of_eqOn`**: two Loewner traces of drivers that agree before `L` agree before `L`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv trace)

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow

/-- **A real point beyond a Loewner trace is alive**: if the trace does not meet `[y, ∞)` on `[0, t]`, `y > 0`,
then `y` is alive at `t`. -/
theorem alive_of_traceLT_off {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTraceLT U T η) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) {y : ℝ} (hy : 0 < y)
    (hoff : ∀ s ∈ Icc 0 t, ∀ r : ℝ, y ≤ r → η s ≠ r) : Alive U y t := by
  set A := η '' Icc 0 t with hA
  have hAc : IsCompact A :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩)
  have hK : fwdHull U t = fillH A := hη.2.2 t ht htT
  obtain ⟨R, hR⟩ := hAc.isBounded.subset_closedBall 0
  set e : ℝ := max R y + 1 with he
  have hyR : y ≤ e := by rw [he]; linarith [le_max_right R y]
  have heR : R < |e| := by
    rw [abs_of_pos (by rw [he]; linarith [le_max_right R y])]
    rw [he]; linarith [le_max_left R y]
  obtain ⟨ρ, hρ, hball⟩ := Sec5.Aux22Strip.exists_ball_notMem_fillH_aux hAc hR (a := y) (b := e) (e := e) (x := y)
    (fun r hr ⟨s, hs, hγ⟩ => hoff s hs r hr.1 hγ) ⟨le_rfl, hyR⟩ ⟨hyR, le_rfl⟩ heR
  obtain ⟨v, hv⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hU hU0 hy.ne' ht hρ (by
    rw [hK, Set.disjoint_left]
    exact fun z hz => hball z hz)
  exact Sec7.Lemma76E.alive_of_isForwardSol hU ht (by rw [hU0]; exact hy) hv

/-- **The zero right mark collides at a real contact beyond an alive point.** If a Loewner trace continuous on
`[0, L]` is at a real point at `L`, and some `x₀ ∈ (0, Re η L]` is alive at every time before `L`, then
`rightImg U 0 L = U L`. No open zero gap is assumed: the flow is restarted at the last zero collision. -/
theorem rightImg_zero_eq_of_alive_tip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {L : ℝ} (hL : 0 < L)
    {η : ℝ → ℂ} (hη : IsLoewnerTraceLT U L η) (hc : ContinuousOn η (Icc 0 L)) (him : (η L).im = 0)
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀L : x₀ ≤ (η L).re) (halive : ∀ t ∈ Ico 0 L, Alive U x₀ t) :
    rightImg U 0 L = U L := by
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 hL hc
  have htip := TraceClose.extendFrom_zero_eq hη hU hU0 hL hc
  have hend : η L = (((η L).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hlim : Tendsto (fwdMapInv U L) (𝓝[H] 0) (𝓝 (((η L).re : ℝ) : ℂ)) := by
    rw [← hend, ← htip]
    exact hB.tendsto (show (0 : ℂ) ∈ Hbar by simp [Hbar])
  set Z : Set ℝ := {t | t ∈ Icc 0 L ∧ rightImg U 0 t = U t} with hZ
  have hG : ContinuousOn (fun t => rightImg U 0 t - U t) (Icc 0 L) :=
    ((continuousOn_rightImg hU 0).mono Icc_subset_Ici_self).sub hU.continuousOn
  have hZc : IsClosed Z := by
    have e : Z = Icc 0 L ∩ (fun t => rightImg U 0 t - U t) ⁻¹' {0} := by
      ext t
      simp only [hZ, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, sub_eq_zero]
    rw [e]
    exact hG.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have h0Z : (0 : ℝ) ∈ Z := ⟨⟨le_rfl, hL.le⟩, by rw [rightImg_zero hU hU0 le_rfl, hU0]⟩
  have hZb : BddAbove Z := ⟨L, fun t ht => ht.1.2⟩
  have hSZ : sSup Z ∈ Z := hZc.csSup_mem ⟨0, h0Z⟩ hZb
  rcases hSZ.1.2.lt_or_eq with hSL | hSL
  · have hsep : ∀ t ∈ Ioo (sSup Z) L, U t < rightImg U 0 t := fun t ht => by
      refine lt_of_le_of_ne (le_rightImg hU 0 (hSZ.1.1.trans ht.1.le)) fun h => ?_
      have htZ : t ∈ Z := ⟨⟨hSZ.1.1.trans ht.1.le, ht.2.le⟩, h.symm⟩
      exact absurd (le_csSup hZb htZ) (not_le.2 ht.1)
    exact SB.Vo.rightImg_zero_eq_at_later_real_tip hU hU0 hSZ.1.1 hSL hSZ.2 hsep hlim hx₀ hx₀L
      (halive _ ⟨hSZ.1.1, hSL⟩)
  · rw [← hSL]
    exact hSZ.2

/-- **Every mark at or left of a real contact beyond an alive point collides there.** -/
theorem rightImg_eq_of_alive_tip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {L : ℝ} (hL : 0 < L)
    {η : ℝ → ℂ} (hη : IsLoewnerTraceLT U L η) (hc : ContinuousOn η (Icc 0 L)) (him : (η L).im = 0)
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀L : x₀ ≤ (η L).re) (halive : ∀ t ∈ Ico 0 L, Alive U x₀ t) {x : ℝ}
    (hx : x ≤ (η L).re) : rightImg U x L = U L :=
  (Restart.FlowStopIdentLL.rightImg_eq_iff_of_zero_collision hU hU0 hL.le
    (TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 hL hc)
    (TraceClose.extendFrom_zero_eq hη hU hU0 hL hc)
    (rightImg_zero_eq_of_alive_tip hU hU0 hL hη hc him hx₀ hx₀L halive) x).2 hx

/-- **The contact clause from a collision of an agreeing continuous driver at `L`.** -/
theorem gapVanishes_of_collision {D Wc : ℝ → ℝ} (hWc : Continuous Wc) {L : ℝ} (hL : 0 < L)
    (hagree : ∀ r ∈ Ico 0 L, D r = Wc r) {x : ℝ} (hcol : rightImg Wc x L = Wc L) : GapVanishes D x L := by
  have hG : ContinuousOn (fun t => rightImg Wc x t - Wc t) (Ici 0) :=
    (continuousOn_rightImg hWc x).sub hWc.continuousOn
  intro ε hε c₀ hc₀
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hG L (show (0 : ℝ) ≤ L from hL.le)) ε hε
  set d := min (min ((L - c₀) / 2) (δ / 2)) (L / 2) with hd
  have hd0 : 0 < d := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hd1 : d ≤ (L - c₀) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : d ≤ δ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : d ≤ L / 2 := min_le_right _ _
  refine ⟨L - d, by linarith, by linarith, ?_⟩
  have hmem : L - d ∈ Ici (0 : ℝ) := show (0 : ℝ) ≤ L - d by linarith
  have hdist : dist (L - d) L < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    linarith
  have h1 := hball hmem hdist
  rw [Real.dist_eq, hcol, sub_self, sub_zero] at h1
  have hcongr : rightImg D x (L - d) = rightImg Wc x (L - d) :=
    Supp8.GB6.rightImg_congr hWc (by linarith) fun r hr => hagree r ⟨hr.1, by linarith [hr.2]⟩
  rw [hcongr, hagree (L - d) ⟨by linarith, by linarith⟩]
  exact lt_of_abs_lt h1

/-- **The contact clause from a canonical trace reaching a real point beyond its earlier real visits.** On
`[0, L)` the driver `D` equals the continuous canonical driver `Wc`, whose Loewner trace `ηc` is continuous on
`[0, L]`, real at `L`, and does not reach `[x₀, ∞)` before `L`, for some `x₀ ∈ (0, Re ηc L]`. Then every mark
`x ≤ Re ηc L` has a vanishing gap along `D` at `L`. -/
theorem gapVanishes_of_canonical_off {D Wc : ℝ → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {L : ℝ} (hL : 0 < L)
    (hagree : ∀ r ∈ Ico 0 L, D r = Wc r) {ηc : ℝ → ℂ} (hη : IsLoewnerTraceLT Wc L ηc)
    (hc : ContinuousOn ηc (Icc 0 L)) (him : (ηc L).im = 0) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀L : x₀ ≤ (ηc L).re)
    (hoff : ∀ s ∈ Ico 0 L, ∀ r : ℝ, x₀ ≤ r → ηc s ≠ r) {x : ℝ} (hx : x ≤ (ηc L).re) : GapVanishes D x L := by
  have halive : ∀ t ∈ Ico 0 L, Alive Wc x₀ t := fun t ht =>
    alive_of_traceLT_off hWc hWc0 hη ht.1 ht.2 hx₀ fun s hs => hoff s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  exact gapVanishes_of_collision hWc hL hagree (rightImg_eq_of_alive_tip hWc hWc0 hL hη hc him hx₀ hx₀L halive hx)

/-- **The left contact clause** (marks `x ≥ Re ηc L` on the left, read as right marks `−x` of the negated driver):
the mirror of `gapVanishes_of_canonical_off`, for a trace reaching a real point `≤ x₀ < 0` without reaching
`(−∞, x₀]` before. -/
theorem gapVanishes_neg_of_canonical_off {D Wc : ℝ → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {L : ℝ}
    (hL : 0 < L) (hagree : ∀ r ∈ Ico 0 L, D r = Wc r) {ηc : ℝ → ℂ} (hη : IsLoewnerTraceLT Wc L ηc)
    (hc : ContinuousOn ηc (Icc 0 L)) (him : (ηc L).im = 0) {x₀ : ℝ} (hx₀ : x₀ < 0) (hx₀L : (ηc L).re ≤ x₀)
    (hoff : ∀ s ∈ Ico 0 L, ∀ r : ℝ, r ≤ x₀ → ηc s ≠ r) {x : ℝ} (hx : (ηc L).re ≤ x) :
    GapVanishes (fun r => -D r) (-x) L := by
  have hWc' : Continuous (fun r => -Wc r) := hWc.neg
  have hη' : IsLoewnerTraceLT (-Wc) L (fun t => LP.reflectC (ηc t)) := SB.Vo.isLoewnerTraceLT_reflect hη
  have hc' : ContinuousOn (fun t => LP.reflectC (ηc t)) (Icc 0 L) := LP.continuous_reflectC.comp_continuousOn hc
  have hre : ∀ z : ℂ, (LP.reflectC z).re = -z.re ∧ (LP.reflectC z).im = z.im := fun z => by
    simp [LP.reflectC]
  refine gapVanishes_of_canonical_off (Wc := fun r => -Wc r) hWc' (by simp [hWc0]) hL
    (fun r hr => by simp only [hagree r hr]) hη' hc' (by rw [(hre _).2, him]) (neg_pos.2 hx₀)
    (by rw [(hre _).1]; linarith) (fun s hs r hr h => ?_) (by rw [(hre _).1]; linarith)
  apply hoff s hs (-r) (by linarith)
  have h2 := congrArg LP.reflectC h
  rw [LP.reflectC_reflectC] at h2
  rw [h2]
  apply Complex.ext <;> simp [LP.reflectC]

/-- **Two Loewner traces of drivers agreeing before `L` agree before `L`** (both are the radial-limit trace). -/
theorem eqOn_trace_of_eqOn {D Wc : ℝ → ℝ} (hD : Continuous D) (hD0 : D 0 = 0) (hWc : Continuous Wc)
    (hWc0 : Wc 0 = 0) {L L' : ℝ} (hagree : ∀ r ∈ Ico 0 L, D r = Wc r) {η ηc : ℝ → ℂ}
    (hη : IsLoewnerTraceLT D L' η) (hηc : IsLoewnerTraceLT Wc L ηc) (hLL' : L ≤ L') :
    EqOn η ηc (Ico 0 L) := by
  intro t ht
  obtain ⟨t₂, ht₂, ht₂L⟩ := exists_between ht.2
  rw [← hη.trace_eq hD hD0 ht.1 (lt_of_lt_of_le ht.2 hLL'), ← hηc.trace_eq hWc hWc0 ht.1 ht.2]
  exact trace_eq_of_eqOn ht.1 ht₂ fun r hr => hagree r ⟨hr.1, lt_of_le_of_lt hr.2 ht₂L⟩

end InteractingSLE.Theorem14.GW2Bh
