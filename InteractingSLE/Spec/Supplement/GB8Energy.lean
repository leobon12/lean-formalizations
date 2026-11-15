/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB8EnergyKoebe
import InteractingSLE.Spec.Supplement.GB8EnergyCode
import InteractingSLE.Spec.Supplement.GB8Inputs
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Sec5.CfAvoidLeftQHit
import InteractingSLE.Spec.Sec7.ContinuityProb6Shift
import InteractingSLE.Spec.Zhan.SeparatedShift
import InteractingSLE.WangWu.SideValues
import InteractingSLE.WangWu.ReverseContactBdry


/-!
# Lemma GB8 by the finite-energy buffer

Packet PROVE-T14-TIP5 (route of `planning/handoffs/PROVE-T14-TIP4.md` §5.2). Specification supplement §8.8,
**Lemma GB8** and its proof (`source/spec/p481-528.md` L1019–L1050, pp. 523–524); the statement is
`Supp8.GB8.GB8Statement` (driver form, `GB8.lean`).

By `gb8Statement_iff_eventualSep` (PROVE-T14-TIP4) GB8 reduces to excluding the event `E` = "infinite lifetime and the
outermost left mark never meets the driver". The source's argument, in driver form:

1. "The complete finite-force theorem makes the trace transient to infinity on that event": Theorem 1.3
   (`Exist.Theorem13Statement`, exactly the frozen anchor's type) gives a continuous trace tending to `∞`.
2. "Every real contact then lies in the fixed compact interval `[x₋, x₊]`, so a sufficiently late rational own time
   `q` is an interior time after the last real contact": the trace never visits `(−∞, x₋] ∪ [x₊, ∞)`
   (`Sec5.CfAvoidLeftQ.trace_ne_of_{gt,lt}_of_sep`, with GB7a/G12's right no-contact `rightNoContactStatement`), so
   after some time it is off the real line (`exists_forall_ne_real`). At a late rational `q` the restarted trace
   (`exists_restart_trace`, [Yua22] Corollary 1.3) satisfies `η(q + s) = F̄_q(η₂(s))`, and `F̄_q` sends the real points
   beyond the marks' images back to the real line (`im_extendFrom_eq_zero_of_le_vL`); so every mark is off the driver
   at `q` and the restarted trace never visits the marks' sides.
3. "On the proposed entirely interior transient future … sufficiently thin crosscuts around that support are never
   hit": the restarted marks never meet the restarted driver (`GB8.w_lt_vR_of_trace_avoid`), and the energy of the
   change to the GB8 reference is finite by Koebe distortion (`GB8EnergyKoebe.lean`). Hence the restarted state lies in
   an energy buffer (`exists_restart_energySep`).
4. "Aux. 108 gives equivalence on the entire stopped history … Countably many rational `q` … exclude the event": the
   restarted energy buffers are null (`measure_restart_energySep_eq_zero`, `GB8EnergyCode.lean`), so `E` is null
   (`ae_noContact_false`), and **`gb8Statement_of_thm13`** follows as in `GB8Proof.gb8Statement_of_inputs`.

The finite-energy buffer replaces the gap buffer of `EventualSepStatement` (which is equivalent to GB8 itself,
PROVE-T14-TIP4 §5.1): it contains the actual interior transient future, whose gaps need not stay bounded below.

## Main results

* `restart_mark_eq`, `exists_forall_ne_real`, `exists_restart_trace`, `im_extendFrom_eq_zero_of_le_vL`,
  `im_extendFrom_eq_zero_of_vR_le`, `pathEnergy_eq`, `minGap_pos_of_lt`;
* **`exists_restart_energySep`** (deterministic): the interior transient future lies in an energy buffer;
* **`ae_noContact_false`**, **`gb8Statement_of_thm13`**: Lemma GB8 given Theorem 1.3;
  `eventualSepStatement_of_thm13`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Supp8.GB8

open QuantumZipper (H Hbar fwdMapInv)
open Zhan Sec2 Girsanov Coupling

variable {nL nR : ℕ}

/-! ### The restarted marks -/

/-- **A restarted mark solves the restarted Loewner equation**: `v(q + t) − w(q)` starts at `v(q) − w(q)` and solves
`ṽ_t = ṽ_0 + ∫₀ᵗ 2/(ṽ − w̃)` with the restarted driver `w̃ = w(q + ·) − w(q)`. -/
theorem restart_mark_eq {w v : ℝ≥0 → ℝ} {x : ℝ}
    (hveq : ∀ t : ℝ≥0, v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hint : ∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 t)
    (q t : ℝ≥0) :
    v (q + t) - w q = (v q - w q) +
      ∫ s in (0 : ℝ)..t, 2 / ((v (q + s.toNNReal) - w q) - (w (q + s.toNNReal) - w q)) := by
  have h1 := hveq (q + t)
  have h2 := hveq q
  have hsplit : ∫ s in (0 : ℝ)..((q + t : ℝ≥0) : ℝ), 2 / (v s.toNNReal - w s.toNNReal) =
      (∫ s in (0 : ℝ)..(q : ℝ), 2 / (v s.toNNReal - w s.toNNReal)) +
        ∫ s in (q : ℝ)..((q + t : ℝ≥0) : ℝ), 2 / (v s.toNNReal - w s.toNNReal) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint q)
      (((hint (q + t)).symm.trans (hint q)).symm)).symm
  have hshift : ∫ s in (q : ℝ)..((q + t : ℝ≥0) : ℝ), 2 / (v s.toNNReal - w s.toNNReal) =
      ∫ s in (0 : ℝ)..(t : ℝ), 2 / ((v (q + s.toNNReal) - w q) - (w (q + s.toNNReal) - w q)) := by
    have e := intervalIntegral.integral_comp_add_right (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal))
      (a := (0 : ℝ)) (b := (t : ℝ)) (q : ℝ)
    rw [zero_add, show (t : ℝ) + q = ((q + t : ℝ≥0) : ℝ) by push_cast; ring] at e
    rw [← e]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hs' : (s + q).toNNReal = q + s.toNNReal := by
      rw [add_comm, Real.toNNReal_add q.coe_nonneg hs.1, Real.toNNReal_coe]
    simp only [hs']
    ring_nf
  rw [h1, h2, hsplit, hshift]
  ring


/-! ### Late times: the transient trace is off the real line -/

section Path

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- **"Every real contact then lies in the fixed compact interval `[x₋, x₊]`"**: on infinite lifetime, if a left mark
`x₋ < 0` and a right mark `x₊ > 0` never meet the driver, the trace never visits `(−∞, x₋] ∪ [x₊, ∞)`; if it is
transient, it is off the real line after some time. -/
theorem exists_forall_ne_real (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) {iL : Fin nL} {iR : Fin nR}
    (hxp : 0 < xR iR) (hLs : ∀ t, vL iL t < w t) (hRs : ∀ t, w t < vR iR t) :
    ∃ t₀ : ℝ≥0, ∀ t, t₀ ≤ t → ∀ x : ℝ, η t ≠ x := by
  obtain ⟨t₀, ht₀⟩ := (htr.eventually_gt_atTop (max (-xL iL) (xR iR))).exists_forall_of_atTop
  refine ⟨t₀, fun t ht x hx => ?_⟩
  have h1 := ht₀ t ht
  rw [hx, Complex.norm_real, Real.norm_eq_abs] at h1
  rcases lt_or_ge x 0 with hneg | hnn
  · rw [abs_of_neg hneg] at h1
    exact Sec5.CfAvoidLeftQ.trace_ne_of_gt_of_sep hp hη (fun s _ => hLs s) t hneg
      (by linarith [le_max_left (-xL iL) (xR iR)]) hx
  · rw [abs_of_nonneg hnn] at h1
    have hx' : xR iR ≤ x := by linarith [le_max_right (-xL iL) (xR iR)]
    exact Sec5.CfAvoidLeftQ.trace_ne_of_lt_of_sep hp hη (fun s _ => hRs s) t (hxp.trans_le hx') hx' hx

end Path

/-! ### The restarted trace and the boundary extension of the inverse map -/

/-- **The restarted trace** ([Yua22] Corollary 1.3,
`Sec7.Positive.exists_isGeneratingTrace_shiftNN_of_isGeneratingTrace`): for a continuous transient generating trace
`η` of `w` on `[0, ∞)` and a time `q`, the restarted driver `w(q + ·) − w(q)` has a continuous transient generating
trace `η₂` with `η(q + s) = F̄_q(η₂(s))` for `s > 0` and `F̄_q(0) = η(q)`, where `F̄_q` is the boundary extension
of the inverse Loewner map at time `q`. -/
theorem exists_restart_trace {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) (q : ℝ≥0) :
    ∃ η₂ : ℝ≥0 → ℂ, IsGeneratingTrace (Sec7.shiftNN w q) ⊤ η₂ ∧ Tendsto (fun t => ‖η₂ t‖) atTop atTop ∧
      (∀ s : ℝ≥0, 0 < s → η (q + s) = extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) (η₂ s)) ∧
      extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) 0 = η q := by
  obtain ⟨η₂, hη₂⟩ := Sec7.Positive.exists_isGeneratingTrace_shiftNN_of_isGeneratingTrace hw hw0 hη q
  have htr₂ := Zhan.tendsto_norm_shiftNN hw hw0 hη hη₂ htr
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤} := hw.continuousOn
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη hwc hw0 (σ := q) ENNReal.coe_lt_top
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < (q : ℝ≥0∞) + ⊤} := by rw [add_top]; exact hwc
  obtain ⟨hJ, -⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hJ
  refine ⟨η₂, hη₂, htr₂, fun s hs => ?_, ?_⟩
  · have ht : q < q + s := lt_add_of_pos_right q hs
    rw [hη.eq_of_le hJ hwc hw0 le_top, Sec7.joinTrace_of_lt ht, add_tsub_cancel_left]
  · have hlim := h₁.2.2
    have hne : (𝓝[H] (0 : ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ (show (0 : ℝ) ≤ (0 : ℂ).im by simp))
    exact hlim.limUnder_eq

section Path

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- **Real points at or beyond a left mark's image are sent back to the real line** by the extended inverse map
(`WangWu.vL_sub_lt_of_extendFrom_mem_H`). -/
theorem im_extendFrom_eq_zero_of_le_vL (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) (hw : Continuous w)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) (q : ℝ≥0) {i : Fin nL} {x : ℝ} (hx : x ≤ vL i q - w q) :
    (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) x).im = 0 := by
  have hηL := isLoewnerTrace_of_isGeneratingTrace hη
  have hW0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simp [hp.isForcePath.w_zero]
  have hmem := WangWu.extendFrom_mem_Hbar hηL (hw.comp continuous_real_toNNReal) hW0 q.coe_nonneg
    (x := (x : ℂ)) (show (0 : ℝ) ≤ (x : ℂ).im by simp)
  refine le_antisymm (not_lt.1 fun hpos => ?_) hmem
  have := WangWu.vL_sub_lt_of_extendFrom_mem_H hp hw hηL (t := q) ENNReal.coe_lt_top hpos i
  linarith

/-- **Real points at or beyond a right mark's image are sent back to the real line.** -/
theorem im_extendFrom_eq_zero_of_vR_le (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) (hw : Continuous w)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) (q : ℝ≥0) {j : Fin nR} {x : ℝ} (hx : vR j q - w q ≤ x) :
    (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) x).im = 0 := by
  have hηL := isLoewnerTrace_of_isGeneratingTrace hη
  have hW0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simp [hp.isForcePath.w_zero]
  have hmem := WangWu.extendFrom_mem_Hbar hηL (hw.comp continuous_real_toNNReal) hW0 q.coe_nonneg
    (x := (x : ℂ)) (show (0 : ℝ) ≤ (x : ℂ).im by simp)
  refine le_antisymm (not_lt.1 fun hpos => ?_) hmem
  have := WangWu.lt_vR_sub_of_extendFrom_mem_H hp hw hηL (t := q) ENNReal.coe_lt_top hpos j
  linarith

end Path

/-! ### The energy of the path, side by side -/

/-- The path energy as the energy of the two side sums. -/
theorem pathEnergy_eq (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (T : ℝ≥0) :
    pathEnergy κ ρL ρL' ρR ρR' w vL vR T = 1 / κ * ∫ s in (0 : ℝ)..T,
      (∑ i, (ρL' i - ρL i) / (w s.toNNReal - vL i s.toNNReal) +
        ∑ j, (ρR' j - ρR j) / (w s.toNNReal - vR j s.toNNReal)) ^ 2 := by
  unfold pathEnergy Zhan.changeEnergy
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [Fin.sum_univ_add]
  simp only [weightDiff, Girsanov.allMarks, Fin.addCases_left, Fin.addCases_right]

/-- Marks strictly off the driver give a positive smallest gap. -/
theorem minGap_pos_of_lt {w : ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (hL : ∀ i, vL i < w) (hR : ∀ j, w < vR j) :
    0 < minGap ((w, vL, vR) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := by
  rw [minGap, Finset.lt_inf'_iff]
  intro k _
  rcases k with _ | i | j
  · exact one_pos
  · exact abs_pos.2 (sub_ne_zero.2 (hL i).ne')
  · exact abs_pos.2 (sub_ne_zero.2 (hR j).ne)

/-! ### The actual interior transient future lies in an energy buffer -/

section Path

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- **The actual interior transient future lies in an energy buffer** (deterministic; GB8 proof, p. 523: "The complete
finite-force theorem makes the trace transient to infinity on that event. Every real contact then lies in the fixed
compact interval `[x₋, x₊]`, so a sufficiently late rational own time `q` is an interior time after the last real
contact"). Along an integrated path of the GB8 word with infinite lifetime whose outermost marks never meet the driver
and with a continuous transient trace, there is a rational time `q > 0` with every mark off the driver at `q` after
which the restarted state stays in the energy buffer of the change to the GB8 reference: the restarted trace never
visits the marks' sides (the extended inverse map sends those real points back to the real line, which the late trace
avoids), so the restarted marks never meet the restarted driver (`w_lt_vR_of_trace_avoid`) and the energy is finite
by Koebe distortion (`exists_energy_bound`). -/
theorem exists_restart_energySep (hκ : 0 < κ) (hnL : 0 < nL) (hnR : 0 < nR)
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ⊤) (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩)
    (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hLs : ∀ t, vL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t < w t) (hRs : ∀ t, w t < vR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ t)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) :
    ∃ p : ℚ≥0, 0 < p ∧
      0 < minGap ((w p, fun i => vL i p, fun j => vR j p) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) ∧
      ∃ m : ℕ, EnergySep κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m (fun t => w ((p : ℝ≥0) + t) - w p)
        (fun i t => vL i ((p : ℝ≥0) + t) - w p) (fun j t => vR j ((p : ℝ≥0) + t) - w p) ⊤ := by
  have hpF := hp.isForcePath
  have hc : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ⊤} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => ENNReal.coe_lt_top)
  have hw : Continuous w := hc hpF.continuousOn_w
  have hvL : ∀ i, Continuous (vL i) := fun i => hc (hpF.continuousOn_vL i)
  have hvR : ∀ j, Continuous (vR j) := fun j => hc (hpF.continuousOn_vR j)
  have hw0 := hpF.w_zero
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ := fun t => ENNReal.coe_lt_top
  obtain ⟨t₀, ht₀⟩ := exists_forall_ne_real hp hη htr hxp hLs hRs
  obtain ⟨p, hp1, -⟩ := Zhan.exists_nnrat_near (t₀ + 1) one_pos
  set q : ℝ≥0 := (p : ℝ≥0) with hq
  have ht₀q : t₀ < q := lt_of_lt_of_le (lt_add_one t₀) hp1
  have hq0 : (0 : ℝ≥0) < q := lt_of_le_of_lt zero_le ht₀q
  obtain ⟨η₂, hη₂, htr₂, hjoin, hzero⟩ := exists_restart_trace hw hw0 hη htr q
  set oL : Fin nL := ⟨0, hnL⟩ with hoL
  set oR : Fin nR := ⟨0, hnR⟩ with hoR
  have hreal : ∀ t, t₀ ≤ t → ∀ z : ℂ, z.im = 0 → η t ≠ z := fun t ht z hz he =>
    ht₀ t ht z.re (by rw [he]; exact Complex.ext (by simp) (by simp [hz]))
  -- every mark is off the driver at `q`
  have hgL : vL oL q < w q := by
    refine lt_of_le_of_ne (hpF.vL_le_w (hlt q) oL) fun he => ?_
    have him := im_extendFrom_eq_zero_of_le_vL hp hw hη q (i := oL) (x := 0) (by rw [he, sub_self])
    rw [Complex.ofReal_zero, hzero] at him
    exact hreal q ht₀q.le _ him rfl
  have hgR : w q < vR oR q := by
    refine lt_of_le_of_ne (hpF.w_le_vR (hlt q) oR) fun he => ?_
    have him := im_extendFrom_eq_zero_of_vR_le hp hw hη q (j := oR) (x := 0) (by rw [he, sub_self])
    rw [Complex.ofReal_zero, hzero] at him
    exact hreal q ht₀q.le _ him rfl
  have hgLi : ∀ i, vL i q < w q := fun i =>
    lt_of_le_of_lt (hpF.antitone_vL (hlt q) (Fin.le_def.2 (Nat.zero_le _))) hgL
  have hgRj : ∀ j, w q < vR j q := fun j =>
    lt_of_lt_of_le hgR (hpF.monotone_vR (hlt q) (Fin.le_def.2 (Nat.zero_le _)))
  -- the restarted trace never visits the marks' sides
  have havL : ∀ s (x : ℝ), x ≤ vL oL q - w q → η₂ s ≠ x := by
    intro s x hx he
    rcases eq_zero_or_pos s with rfl | hs
    · rw [hη₂.1] at he
      have := congrArg Complex.re he
      simp only [Complex.zero_re, Complex.ofReal_re] at this
      linarith [hgL]
    · have h1 := hjoin s hs
      rw [he] at h1
      have him := im_extendFrom_eq_zero_of_le_vL hp hw hη q hx
      rw [← h1] at him
      exact hreal (q + s) (ht₀q.le.trans le_self_add) _ him rfl
  have havR : ∀ s (x : ℝ), vR oR q - w q ≤ x → η₂ s ≠ x := by
    intro s x hx he
    rcases eq_zero_or_pos s with rfl | hs
    · rw [hη₂.1] at he
      have := congrArg Complex.re he
      simp only [Complex.zero_re, Complex.ofReal_re] at this
      linarith [hgR]
    · have h1 := hjoin s hs
      rw [he] at h1
      have him := im_extendFrom_eq_zero_of_vR_le hp hw hη q hx
      rw [← h1] at him
      exact hreal (q + s) (ht₀q.le.trans le_self_add) _ him rfl
  -- the restarted state
  set w' : ℝ≥0 → ℝ := fun t => w (q + t) - w q with hw'
  set vL' : Fin nL → ℝ≥0 → ℝ := fun i t => vL i (q + t) - w q with hvL'
  set vR' : Fin nR → ℝ≥0 → ℝ := fun j t => vR j (q + t) - w q with hvR'
  have hw'c : Continuous w' := (hw.comp (continuous_const.add continuous_id)).sub continuous_const
  have hvL'c : ∀ i, Continuous (vL' i) := fun i =>
    ((hvL i).comp (continuous_const.add continuous_id)).sub continuous_const
  have hvR'c : ∀ j, Continuous (vR' j) := fun j =>
    ((hvR j).comp (continuous_const.add continuous_id)).sub continuous_const
  have hw'0 : w' 0 = 0 := by simp [hw']
  have hη₂' : IsGeneratingTrace w' ⊤ η₂ := hη₂
  have hvLeq : ∀ i (t : ℝ≥0), vL' i t = (vL i q - w q) +
      ∫ s in (0 : ℝ)..t, 2 / (vL' i s.toNNReal - w' s.toNNReal) := fun i t =>
    restart_mark_eq (fun t => hpF.vL_eq (hlt t) i) (fun t => hpF.intervalIntegrable_forceL (hlt t) i) q t
  have hvReq : ∀ j (t : ℝ≥0), vR' j t = (vR j q - w q) +
      ∫ s in (0 : ℝ)..t, 2 / (vR' j s.toNNReal - w' s.toNNReal) := fun j t =>
    restart_mark_eq (fun t => hpF.vR_eq (hlt t) j) (fun t => hpF.intervalIntegrable_forceR (hlt t) j) q t
  -- the restarted marks never meet the restarted driver
  have hR' : ∀ j t, w' t < vR' j t := fun j t =>
    w_lt_vR_of_trace_avoid (ζ := ⊤) (x := vR j q - w q) (by linarith [hgRj j]) hw'c.continuousOn hw'0
      (hvR'c j).continuousOn (fun t _ => hvReq j t)
      (fun t _ => by simp only [hw', hvR']; linarith [hpF.w_le_vR (hlt (q + t)) j]) hη₂'
      (fun t _ y hy => havR t y (le_trans (by linarith [hpF.monotone_vR (hlt q) (Fin.le_def.2
        (Nat.zero_le (j : ℕ)) : oR ≤ j)]) hy)) (hlt t)
  have hL' : ∀ i t, vL' i t < w' t := by
    intro i t
    have h := w_lt_vR_of_trace_avoid (ζ := ⊤) (w := -w') (v := fun t => -vL' i t) (x := -(vL i q - w q))
      (by linarith [hgLi i]) hw'c.neg.continuousOn (by simp [hw'0]) (hvL'c i).neg.continuousOn
      (fun t _ => by
        simp only [Pi.neg_apply]
        rw [hvLeq i t, neg_add, ← intervalIntegral.integral_neg]
        congr 1
        refine intervalIntegral.integral_congr fun s _ => ?_
        rw [show -vL' i s.toNNReal - -w' s.toNNReal = -(vL' i s.toNNReal - w' s.toNNReal) by ring, div_neg])
      (fun t _ => by simp only [Pi.neg_apply, hw', hvL']; linarith [hpF.vL_le_w (hlt (q + t)) i])
      (LP.isGeneratingTrace_reflect hη₂')
      (fun t _ y hy he => havL t (-y) (le_trans (by linarith) (le_trans (neg_le_neg hy) (by
          linarith [hpF.antitone_vL (hlt q) (Fin.le_def.2 (Nat.zero_le (i : ℕ)) : oL ≤ i)])))
        (by
          have := congrArg LP.reflectC he
          rw [LP.reflectC_reflectC] at this
          rw [this]; simp [LP.reflectC]))
      (hlt t)
    simp only [Pi.neg_apply] at h
    linarith
  -- the energy
  have hcL : ∑ i, (refW nL (κ - 4) i - ρL i) = 0 := by rw [Finset.sum_sub_distrib, sum_refW hnL, hsL, sub_self]
  have hcR : ∑ j, (refW nR (κ / 2 - 2) j - ρR j) = 0 := by
    rw [Finset.sum_sub_distrib, sum_refW hnR, hsR, sub_self]
  obtain ⟨m, hm⟩ := exists_energy_bound hw'c hw'0 hη₂' htr₂ hnL hnR (yL := fun i => vL i q - w q)
    (yR := fun j => vR j q - w q) hvL'c hvR'c hvLeq hvReq hL' hR'
    (fun t i i' hii' => by simp only [hvL']; linarith [hpF.antitone_vL (hlt (q + t)) hii'])
    (fun t j j' hjj' => by simp only [hvR']; linarith [hpF.monotone_vR (hlt (q + t)) hjj'])
    havL havR _ _ hcL hcR
  have hpos : (0 : ℚ≥0) < p := by
    have h := hq0
    rw [hq] at h
    exact_mod_cast h
  refine ⟨p, hpos, minGap_pos_of_lt hgLi hgRj, ⌈m / κ⌉₊, rfl, fun N => ?_, fun N => ?_⟩
  · have hf : Continuous fun s => minGap ((w' s, fun i => vL' i s, fun j => vR' j s) :
        ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
      continuous_minGap.comp (hw'c.prodMk ((continuous_pi hvL'c).prodMk (continuous_pi hvR'c)))
    obtain ⟨n, hn⟩ := Zhan.exists_one_div_le_on_Iic hf (fun s => minGap_pos_of_lt (fun i => hL' i s)
      (fun j => hR' j s)) (N : ℝ≥0)
    exact ⟨n, fun p' hp' => hn p' hp'.le⟩
  · rw [pathEnergy_eq]
    have h1 := hm N (N : ℝ≥0).coe_nonneg
    calc 1 / κ * ∫ s in (0 : ℝ)..((N : ℝ≥0) : ℝ), (∑ i, (refW nL (κ - 4) i - ρL i) /
          (w' s.toNNReal - vL' i s.toNNReal) + ∑ j, (refW nR (κ / 2 - 2) j - ρR j) /
          (w' s.toNNReal - vR' j s.toNNReal)) ^ 2 ≤ 1 / κ * m := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = m / κ := by ring
      _ ≤ ⌈m / κ⌉₊ := Nat.le_ceil _

end Path

/-! ### Lemma GB8 -/

/-- **GB8's core: the event of no far-left contact is null** (GB8 proof, pp. 523–524), given Theorem 1.3 ("the
complete finite-force theorem makes the trace transient to infinity on that event"). Almost surely, the lifetime is
finite or the outermost left mark meets the driver. -/
theorem ae_noContact_false (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hnL : 0 < nL) (hnR : 0 < nR) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (hxm : xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0)
    (hxp : 0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩) (hsL : ∑ i, ρL i = κ - 4) (hsR : ∑ j, ρR j = κ / 2 - 2)
    (hpsL : ∀ i : Fin nL, (i : ℕ) < nL - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hpsR : ∀ j : Fin nR, (j : ℕ) < nR - 1 → -2 < ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t : ℝ≥0, VL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ t ω < W t ω) → False := by
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have h13ω := h13 hκ hF hE
  have htr : ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) γ := by
    filter_upwards [h13ω] with ω h using ⟨h.2.choose, h.2.choose_spec.1⟩
  have hR := rightNoContactStatement κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR P 𝓕 W VL VR
    B ζ hE htr
  have hnull : ∀ᵐ ω ∂P, ∀ p : ℚ≥0, ∀ m : ℕ, 0 < p → ¬ (((p : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      0 < minGap (stateAt W VL VR p ω) ∧
      EnergySep κ ρL (refW nL (κ - 4)) ρR (refW nR (κ / 2 - 2)) m (fun t => W ((p : ℝ≥0) + t) ω - W p ω)
        (fun i t => VL i ((p : ℝ≥0) + t) ω - W p ω) (fun j t => VR j ((p : ℝ≥0) + t) ω - W p ω)
        (ζ ω - (p : ℝ≥0))) := by
    rw [ae_all_iff]; intro p; rw [ae_all_iff]; intro m
    by_cases hp : 0 < p
    · have hp' : (0 : ℝ≥0) < (p : ℝ≥0) := by exact_mod_cast hp
      have h0 := measure_restart_energySep_eq_zero referenceSwallowStatement.{0} hκ hκ4 hnL hnR hE (p : ℝ≥0) hp'
        (m : ℝ)
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) h0
      simp only [not_imp, not_not, mem_ofPred_eq] at hω
      exact hω.2
    · exact Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [hE.2.2.2.2, h13ω, hR, hnull] with ω hp h13ω' hRω hnullω
  intro hζ hL
  obtain ⟨-, η, hη, htrη⟩ := h13ω'
  have htr' := htrη hζ
  rw [hζ] at hη hp
  obtain ⟨p, hp0, hgap, m, hES⟩ := exists_restart_energySep hκ hnL hnR hp hxp hsL hsR hL
    (fun t => hRω t (by rw [hζ]; exact ENNReal.coe_lt_top)) hη htr'
  exact hnullω p m hp0 ⟨by rw [hζ]; exact ENNReal.coe_lt_top, hgap,
    by rw [hζ, ENNReal.top_sub_coe]; exact hES⟩

/-- **Lemma GB8** (pp. 523–524), given Theorem 1.3 (the continuous transient trace of the complete finite-force flow,
`Exist.Theorem13Statement`, exactly the frozen anchor's type): almost surely a first far-left contact at a finite
time (the continuation threshold when `κ − 4 ≤ −2`), no contact with `[x₊, ∞)`, and the crossing of `−(2 + 1/8)`
before the contact when `x₋ ≤ −3`. The no-contact event is excluded by the finite-energy buffer:
`ae_noContact_false`. -/
theorem gb8Statement_of_thm13 (h13 : Exist.Theorem13Statement.{u}) : GB8Statement.{u} := by
  intro κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR Ω mΩ P 𝓕 W VL VR B ζ hE htr
  have : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  filter_upwards [ae_noContact_false h13 hκ hκ4 hnL hnR hF hxm hxp hsL hsR hpsL hpsR hE,
    hE.ae_tendsto_threshold hκ, hE.2.2.2.2,
    rightNoContactStatement κ hκ hκ4 nL nR hnL hnR xL xR ρL ρR hF hxm hxp hsL hsR hpsL hpsR P 𝓕 W VL VR B ζ hE htr]
    with ω hnc hlim hp hr
  obtain ⟨τ, hτ⟩ := exists_isFirstFarContact hκ hnL hF hp hlim hxm hsR hpsL hpsR fun hζ hlt => hnc hζ hlt
  exact ⟨⟨τ, hτ, fun hk => eq_zeta_of_isFirstFarContact hnL hp hsL hk hτ⟩, hr,
    fun hx => exists_crossing_of_contact_path hp _ hx hτ⟩

/-- **The far-left input of TIP2 from Theorem 1.3**: `EventualSepStatement` holds given Theorem 1.3 (it is equivalent
to GB8, `gb8Statement_iff_eventualSep`). -/
theorem eventualSepStatement_of_thm13 (h13 : Exist.Theorem13Statement.{u}) : EventualSepStatement.{u} :=
  eventualSepStatement_of_gb8 (gb8Statement_of_thm13 h13)

end InteractingSLE.Supp8.GB8
