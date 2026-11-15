/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripNoncollision
import InteractingSLE.Spec.Zhan.StripEndpointCritical
import InteractingSLE.Spec.Zhan.WordsSublinear
import InteractingSLE.Spec.ZhanGT4.NoCluster
import InteractingSLE.Foundations.Complex.DerivLog
import InteractingSLE.Foundations.Strip.Horizontal

/-!
# The separated one-force trace stays away from its force point (Part B.2, (E5))

Packet PROVE-ZHAN-GT4-B3. Source: Astra, *Follow-up proofs and dependency audit*, §B.2 L1083–L1093 (ruling R38):
"Brownian sublinearity implies `inf_{t ≥ 0} ξ_t > −∞`. If a point starts strictly to the left of this infimum, the real
part of its image remains to the left of the driver and moves farther left; it cannot be swallowed. Consequently there
is an almost surely finite `R` with `Re β_t ≥ −R` (E5). In particular `−∞ ∉ Q`." (Additional note, Lemma 3.2,
L1409–L1414, ruling R39.)

In the R36 form, the separated one-force chordal law with its mark at `−1` and weight `ρ ≥ κ/2 − 2` *is* the
constant-drift strip law with no lower marks and end charge `τ₋ = ρ` (`Strip.IsStripSLEEvolution κ ![] ![] ![] ![] ρ`),
whose strip driver is `√κ B'_t + σ t` in strip time with `σ = ρ + 3 − κ/2 ≥ 1`
(`Zhan.exists_stripBrownian_of_prefixSums`,
for every `κ > 0`). Brownian sublinearity (`Zhan.ae_abs_le_add_mul`) bounds the strip driver below by `−M`, and the
deterministic horizontal bound `Strip.IsSepMark.exists_isForwardSol_of_re_lt_driver` keeps every strip point of real
part `< −M` alive: in the chordal chart these are the points `z ∈ ℍ` with `|z + 1| < e^{−M}`. The trace lies in the
closure of the hulls, so it never enters that disk.

## Main results

* `le_norm_add_one_of_alive`: the deterministic step (a disk of points alive at all times is never entered).
* `ae_alive_near_endMark`: for the strip law, almost surely a whole disk around the end mark `−1` stays alive.
* `IsIntegratedSLEEvolution.ae_le_norm_sub_mark_oneForce`: **for a separated one-force evolution (one left mark
  `p < 0`, weight `≥ κ/2 − 2`, no right mark), almost surely the trace keeps a positive distance from `p`**, every
  `κ > 0`; in particular `p` is not a terminal cluster point (`ae_not_isTermCluster_mark_oneForce`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H fwdHull IsForwardSol)
open Sec7.Dilation

/-! ### The deterministic step -/

/-- **A disk of points alive at all times is never entered by the trace.** If every `z ∈ ℍ` with `‖z + 1‖ < e^{−M}`
(`M ≥ 0`) is alive at every time, every generating trace on `[0, ∞)` stays at distance `≥ e^{−M}` from `−1`. -/
theorem le_norm_add_one_of_alive {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {M : ℝ} (hM : 0 ≤ M)
    (halive : ∀ t : ℝ≥0, ∀ z : ℂ, 0 < z.im → ‖z + 1‖ < Real.exp (-M) →
      ∃ u, IsForwardSol (fun r : ℝ => w r.toNNReal) z t u)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) (t : ℝ≥0) : Real.exp (-M) ≤ ‖η t + 1‖ := by
  rcases eq_zero_or_pos t with rfl | ht
  · rw [hη.1, zero_add, norm_one]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hWc : Continuous fun r : ℝ => w r.toNNReal := hw.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simpa using hw0
  have htip := hη.tendsto_fwdMapInv_tip hw.continuousOn hw0 (t := t) ENNReal.coe_lt_top
  have hcl := YuanCorollary13.mem_closure_fwdHull_of_tendsto hWc hW0 (NNReal.coe_pos.2 ht) htip
  by_contra hlt
  push Not at hlt
  have hball : Metric.ball (-1 : ℂ) (Real.exp (-M)) ∈ 𝓝 (η t) := by
    refine Metric.isOpen_ball.mem_nhds ?_
    rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add]
    exact hlt
  obtain ⟨z, hzb, hzK⟩ := mem_closure_iff_nhds.1 hcl _ hball
  rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] at hzb
  have hzH : 0 < z.im := hzK.1
  obtain ⟨u, hu⟩ := halive t z hzH hzb
  exact Ito.notMem_fwdHull_of_isForwardSol hWc hzH t.coe_nonneg hu hzK

/-! ### The strip law with no lower marks -/

section Strip

variable {κ τm : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The strip point `log (z + 1)` of a chordal point `z ∈ ℍ`. -/
theorem log_add_one_mem_piStrip {z : ℂ} (hz : 0 < z.im) : Complex.log (z + 1) ∈ Strip.piStrip := by
  have h : z + 1 ∈ H := by show 0 < (z + 1).im; simpa using hz
  have ha := DerivLog.arg_mem_Ioo_of_mem_H h
  rw [Strip.piStrip, mem_ofPred_eq, Complex.log_im]
  exact ha

theorem stripExp_log_add_one {z : ℂ} (hz : 0 < z.im) : Strip.stripExp (Complex.log (z + 1)) = z := by
  have hne : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at this
    linarith
  rw [Strip.stripExp, Complex.exp_log hne, add_sub_cancel_right]

/-- **A disk around the end mark stays alive** (B.2 (E5)). For the constant-drift strip law with no lower marks and
end charge `τ₋ ≥ κ/2 − 2` (the chordal one-force law at `−1`), almost surely there is `M ≥ 0` such that every
`z ∈ ℍ` with `‖z + 1‖ < e^{−M}` is alive at every chordal time. -/
theorem ae_alive_near_endMark (hκ : 0 < κ) (hτ : κ / 2 - 2 ≤ τm)
    (hE : Strip.IsStripSLEEvolution κ (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → ℝ) τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, ∀ z : ℂ, 0 < z.im → ‖z + 1‖ < Real.exp (-M) →
      ∃ u, IsForwardSol (fun r : ℝ => W r.toNNReal ω) z t u := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hsep : Strip.IsSeparatedStripWord (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) :=
    ⟨fun a => a.elim0, fun i => i.elim0, fun a => a.elim0, fun i => i.elim0⟩
  have hpre : Strip.HasStripPrefixSums κ (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) :=
    ⟨fun j => j.elim0, fun j => j.elim0⟩
  obtain ⟨𝓗, B', hB', hrep⟩ := Zhan.exists_stripBrownian_of_prefixSums hκ hsep hpre hE
  filter_upwards [hrep, Zhan.ae_abs_le_add_mul hB', Zhan.ae_isStripLife_of_aux6 hκ hτ hE, hE.2.2.2.2]
    with ω hrepω hsub hlife hp
  set σ : ℝ := (τm - Strip.tauPlus κ (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) τm) / 2 with hσ
  have hσ1 : 1 ≤ σ := by
    simp only [hσ, Strip.tauPlus, Finset.univ_eq_empty, Finset.sum_empty]
    linarith
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  obtain ⟨C, hC⟩ := hsub (Real.sqrt κ)⁻¹ (inv_pos.2 hsκ)
  set M : ℝ := max (Real.sqrt κ * C) 0 with hM
  have hdrv : ∀ u : ℝ≥0, -M ≤ Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last 0) · ω)) u := by
    intro u
    have h : Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last 0) · ω)) u =
        Real.sqrt κ * B' u ω + σ * u := by
      rw [(hrepω u).2]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    rw [h]
    have h1 := hC u
    have h2 : -(C + (Real.sqrt κ)⁻¹ * u) ≤ B' u ω := by linarith [neg_abs_le (B' u ω)]
    have h3 : Real.sqrt κ * (-(C + (Real.sqrt κ)⁻¹ * u)) ≤ Real.sqrt κ * B' u ω :=
      mul_le_mul_of_nonneg_left h2 hsκ.le
    have h4 : Real.sqrt κ * (-(C + (Real.sqrt κ)⁻¹ * u)) = -(Real.sqrt κ * C) - u := by
      field_simp
      ring
    have h5 : (u : ℝ) ≤ σ * u := le_mul_of_one_le_left u.coe_nonneg hσ1
    have h6 : -M ≤ -(Real.sqrt κ * C) := neg_le_neg (le_max_left _ _)
    linarith
  refine ⟨M, le_max_right _ _, fun t z hz hzM => ?_⟩
  have hS := Strip.isSepMark_of_isIntegratedSLEPath hp (hlife.2 t)
  have ht : (t : ℝ) ∈ Icc 0 (t : ℝ) := ⟨t.coe_nonneg, le_rfl⟩
  have hT : Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last 0) · ω)) t ∈
      Icc 0 (Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last 0) · ω)) t) :=
    ⟨hS.stripClock_nonneg ht, le_rfl⟩
  have hξ : ∀ r ∈ Icc 0 (Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last 0) · ω)) t),
      -M ≤ Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last 0) · ω)) r := by
    intro r hr
    have h := hdrv r.toNNReal
    rwa [Real.coe_toNNReal _ hr.1] at h
  have hzs : (Complex.log (z + 1)).re < -M := by
    have hne : (0 : ℝ) < ‖z + 1‖ := norm_pos_iff.2 fun h => by
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at this
      linarith
    rw [Complex.log_re, Real.log_lt_iff_lt_exp hne]
    exact hzM
  obtain ⟨u, hu⟩ := hS.exists_isForwardSol_of_re_lt_driver (log_add_one_mem_piStrip hz) hT hξ hzs
  rw [hS.chordalTime_stripClock ht, stripExp_log_add_one hz] at hu
  exact ⟨u, hu⟩

end Strip

/-! ### Every separated one-force law -/

section OneForce

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL ρL : Fin 1 → ℝ} {xR ρR : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The separated one-force trace keeps a positive distance from its force point** (B.2 (E5); additional note,
Lemma 3.2, first paragraph), every `κ > 0`: for a left mark `p < 0` of weight `≥ κ/2 − 2` and no right mark, almost
surely some `δ > 0` has `δ ≤ ‖η t − p‖` for every generating trace `η` on `[0, ∞)` and every `t`. -/
theorem IsIntegratedSLEEvolution.ae_le_norm_sub_mark_oneForce (hκ : 0 < κ) (hx : xL 0 < 0)
    (hρ : κ / 2 - 2 ≤ ρL 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ δ > (0 : ℝ), ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∀ t, δ ≤ ‖η t - xL 0‖ := by
  set p : ℝ := -xL 0 with hp
  have hp0 : 0 < p := neg_pos.2 hx
  set c : ℝ≥0 := ⟨p ^ 2, by positivity⟩ with hcdef
  have hc : c ≠ 0 := by
    intro h
    have : p ^ 2 = 0 := congrArg NNReal.toReal h
    exact (pow_pos hp0 2).ne' this
  have hsc : √(c : ℝ) = p := by
    rw [show (c : ℝ) = p ^ 2 from rfl, Real.sqrt_sq hp0.le]
  have hE' := hE.dilate hc
  have hxL' : (fun i => (√(c : ℝ))⁻¹ * xL i) = Strip.wordXL (Fin.elim0 : Fin 0 → ℝ) := by
    funext i
    have h1 : Strip.wordXL (Fin.elim0 : Fin 0 → ℝ) i = -1 := by
      rw [Fin.fin_one_eq_zero i]; exact Strip.wordXL_last _
    have hx0 : xL 0 ≠ 0 := hx.ne
    rw [h1, Fin.fin_one_eq_zero i, hsc, hp]
    field_simp
  have hxR' : (fun i => (√(c : ℝ))⁻¹ * xR i) = Strip.wordXR (Fin.elim0 : Fin 0 → ℝ) := funext fun i => i.elim0
  have hρL' : ρL = Strip.wordRhoL (Fin.elim0 : Fin 0 → ℝ) (ρL 0) := by
    funext i
    rw [Fin.fin_one_eq_zero i, show (0 : Fin 1) = Fin.last 0 from rfl, Strip.wordRhoL_last]
  have hρR' : ρR = (Fin.elim0 : Fin 0 → ℝ) := funext fun i => i.elim0
  rw [hxL', hxR', hρL', hρR'] at hE'
  filter_upwards [ae_alive_near_endMark hκ hρ hE', Zhan.ae_isStripLife_of_aux6 hκ hρ hE', hE'.2.2.2.2]
    with ω ⟨M, hM, halive⟩ ⟨hζ, _⟩ hpath
  set w' : ℝ≥0 → ℝ := dilPath c (fun t => W t ω) with hw'
  have hw'c : Continuous w' := by
    have h := hpath.2.2.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hw'0 : w' 0 = 0 := hpath.1
  refine ⟨p * Real.exp (-M), mul_pos hp0 (Real.exp_pos _), fun η hη t => ?_⟩
  have hη' := hη.dilate hc
  rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hη'
  have h := le_norm_add_one_of_alive hw'c hw'0 hM halive hη' (t / c)
  have hct : c * (t / c) = t := by rw [mul_comm, div_mul_cancel₀ t hc]
  rw [hct, hsc] at h
  have e : η t - (xL 0 : ℂ) = (p : ℂ) * (((p⁻¹ : ℝ) : ℂ) * η t + 1) := by
    rw [mul_add, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hp0.ne', Complex.ofReal_one, one_mul,
      mul_one, hp, Complex.ofReal_neg]
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
  exact mul_le_mul_of_nonneg_left h hp0.le

/-- The force point of a separated one-force law is not a terminal cluster point of the trace. -/
theorem IsIntegratedSLEEvolution.ae_not_isTermCluster_mark_oneForce (hκ : 0 < κ) (hx : xL 0 < 0)
    (hρ : κ / 2 - 2 ≤ ρL 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → ¬ IsTermCluster η (xL 0) := by
  filter_upwards [IsIntegratedSLEEvolution.ae_le_norm_sub_mark_oneForce hκ hx hρ hE] with ω ⟨δ, hδ, h⟩ η hη
  rw [isTermCluster_iff_not, not_not]
  exact ⟨δ, hδ, Eventually.of_forall fun t => h η hη t⟩

end OneForce

end InteractingSLE.ZhanGT4
