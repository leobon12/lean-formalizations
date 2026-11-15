/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Glue
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# Proposition GB6: the chart trace of the relative chain is the chart image of the counterflow trace

Packet PROVE-GB6C, item (b) of `planning/handoffs/PROVE-GB6B.md` §5 ("boundary values of `relMap` at real counterflow
points; these make the chart path continuous at times when the counterflow is on `ℝ`"). Supplement §8.6, proof of
Proposition GB6 (p. 519): the portion of `η` before its first contact, read in the chart of `U`, is the relative
exploration; the pathwise identification of `IsGB6ChartContinuation` is `η(ℓ(u)) = c_U⁻¹(Γ(u))` at the chart times
`u` with `Γ(u) ∈ ℍ`.

Let `Ψ = relMap U σ` be the chart of the flow's own component read in the counterflow chart, `a` the relative clock,
`W'` the glued relative driver (`GB6Glue.lean`), and `Γ` any continuous generating trace of `W'`. Here, for every
counterflow time `t` before the first contact:

* if `Γ(a(t)) ∈ ℍ`, then `γ(t) ∈ ℍ` and `Γ(a(t)) = Ψ(γ(t))` (**`relTrace_eq`**).

Proof. The tip `Γ(a(t))` lies in the closure of every later hull increment `K^{W'}_{a(t')} \ K^{W'}_{a(t)} =
Ψ(K'_{t'}) \ Ψ(K'_t) ⊆ Ψ(K'_{t'} \ K'_t)` (`mem_closure_diff_of_isGeneratingTrace`, from Yuan's `exists_mem_diff`),
and the counterflow increments `K'_{t'} \ K'_t` shrink to the counterflow tip `γ(t)` (`exists_diff_fwdHull_subset_ball`:
Lawler's hull-radius bound for the shifted driver and the tip limit of `f_t⁻¹`). If `γ(t) ∈ ℍ`, `Ψ` is continuous
there. If `γ(t)` is real, `Ψ` has no cluster point in `ℍ` at `γ(t)`: the preimage of a closed disc in `ℍ` under `Ψ` is
the image of that disc under the continuous inverse chart `relInv`, a compact subset of `ℍ`
(`exists_ball_relMap_notMem`) — this is the boundary-value fact used, and it needs no extension of `Ψ` to `ℝ`.

## Main results

* `relInv`, `relInv_relMap`, `relMap_mem_H`, `continuousOn_relInv`, `continuousAt_relMap`,
  `exists_ball_relMap_notMem`;
* `exists_diff_fwdHull_subset_ball`, `mem_closure_diff_of_isGeneratingTrace`;
* **`relTrace_eq`**, and **`ownComponentChart_inv_relMap`** (the chart inverse undoes `Ψ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Supp8

namespace GB6

/-! ### The inverse chart -/

/-- The inverse of `Ψ = relMap U σ`: `v ↦ −1/f_σ⁻¹(−1/v)`. -/
def relInv (U : ℝ → ℝ) (σ : ℝ) (v : ℂ) : ℂ := -(QuantumZipper.fwdMapInv U σ (-v⁻¹))⁻¹

section Chart

variable {U : ℝ → ℝ} {σ : ℝ}

theorem ne_zero_of_mem_H {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  have : (0 : ℝ) < z.im := hz
  rw [h, zero_im] at this
  exact lt_irrefl 0 this

theorem relMap_mem_H (hU : Continuous U) (hσ : 0 ≤ σ) {w : ℂ} (hw : w ∈ H)
    (hwK : -w⁻¹ ∉ QuantumZipper.fwdHull U σ) : relMap U σ w ∈ H :=
  neg_inv_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ ⟨neg_inv_mem_H hw, hwK⟩)

theorem relInv_mem_H (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {v : ℂ} (hv : v ∈ H) :
    relInv U σ v ∈ H :=
  neg_inv_mem_H (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hσ (neg_inv_mem_H hv)).1

theorem relInv_relMap (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {w : ℂ} (hw : w ∈ H)
    (hwK : -w⁻¹ ∉ QuantumZipper.fwdHull U σ) : relInv U σ (relMap U σ w) = w := by
  rw [relInv, relMap, neg_inv_neg_inv, QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hσ ⟨neg_inv_mem_H hw, hwK⟩,
    neg_inv_neg_inv]

theorem continuousOn_relInv (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) : ContinuousOn (relInv U σ) H := by
  intro v hv
  have h1 : ContinuousAt (fun v : ℂ => -v⁻¹) v := (continuousAt_inv₀ (ne_zero_of_mem_H hv)).neg
  have h2 : ContinuousWithinAt (QuantumZipper.fwdMapInv U σ) H (-v⁻¹) :=
    continuousOn_fwdMapInv hU hU0 hσ _ (neg_inv_mem_H hv)
  have h3 : ContinuousWithinAt (fun v : ℂ => QuantumZipper.fwdMapInv U σ (-v⁻¹)) H v :=
    ContinuousWithinAt.comp (f := fun v : ℂ => -v⁻¹) h2 h1.continuousWithinAt fun z hz => neg_inv_mem_H hz
  have hne := ne_zero_of_mem_H (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hσ (neg_inv_mem_H hv)).1
  exact (h3.inv₀ hne).neg

theorem continuousAt_relMap (hU : Continuous U) (hσ : 0 ≤ σ) {w : ℂ} (hw : w ∈ H)
    (hwK : -w⁻¹ ∉ QuantumZipper.fwdHull U σ) : ContinuousAt (relMap U σ) w := by
  have hD : -w⁻¹ ∈ H \ QuantumZipper.fwdHull U σ := ⟨neg_inv_mem_H hw, hwK⟩
  have hopen : IsOpen (H \ QuantumZipper.fwdHull U σ) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hU hσ
  have hf : ContinuousAt (QuantumZipper.fwdMap U σ) (-w⁻¹) :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hU hσ).differentiableAt (hopen.mem_nhds hD)).continuousAt
  have h1 : ContinuousAt (fun v : ℂ => -v⁻¹) w := (continuousAt_inv₀ (ne_zero_of_mem_H hw)).neg
  have hne := ne_zero_of_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ hD)
  exact ((ContinuousAt.comp (f := fun v : ℂ => -v⁻¹) hf h1).inv₀ hne).neg

/-- **No cluster point in `ℍ` at a real point.** For `z₀ ∈ ℍ` there are `δ, r > 0` such that `Ψ` maps the points
`w ∈ ℍ ∩ B(x, r)` of its domain outside `B(z₀, δ)`: the preimage of a closed disc in `ℍ` is its image under the
continuous inverse chart, a compact subset of `ℍ`. -/
theorem exists_ball_relMap_notMem (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {z₀ : ℂ} (hz₀ : z₀ ∈ H)
    (x : ℝ) : ∃ δ > 0, ∃ r > 0, ∀ w ∈ ball (x : ℂ) r, w ∈ H → -w⁻¹ ∉ QuantumZipper.fwdHull U σ →
      relMap U σ w ∉ ball z₀ δ := by
  have hz₀' : 0 < z₀.im := hz₀
  set δ : ℝ := z₀.im / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hcb : closedBall z₀ δ ⊆ H := by
    intro v hv
    have h1 : |v.im - z₀.im| ≤ δ := by
      have := abs_im_le_norm (v - z₀)
      rw [sub_im] at this
      exact this.trans (by rw [← dist_eq_norm]; exact mem_closedBall.1 hv)
    show 0 < v.im
    have := neg_abs_le (v.im - z₀.im)
    linarith
  set C := relInv U σ '' closedBall z₀ δ with hC
  have hCk : IsCompact C := (isCompact_closedBall z₀ δ).image_of_continuousOn
    ((continuousOn_relInv hU hU0 hσ).mono hcb)
  have hCH : C ⊆ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact relInv_mem_H hU hU0 hσ (hcb hv)
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨δ, hδ0, 1, one_pos, fun w _ hw hwK hmem => ?_⟩
    have : w ∈ C := ⟨relMap U σ w, ball_subset_closedBall hmem, relInv_relMap hU hU0 hσ hw hwK⟩
    rw [hCe] at this
    exact this
  obtain ⟨c, hcC, hcmin⟩ := hCk.exists_isMinOn hCne continuous_im.continuousOn
  have hc0 : 0 < c.im := hCH hcC
  refine ⟨δ, hδ0, c.im, hc0, fun w hwx hw hwK hmem => ?_⟩
  have hwC : w ∈ C := ⟨relMap U σ w, ball_subset_closedBall hmem, relInv_relMap hU hU0 hσ hw hwK⟩
  have h1 : c.im ≤ w.im := hcmin hwC
  have h2 : |w.im| < c.im := by
    have := abs_im_le_norm (w - (x : ℂ))
    rw [sub_im, ofReal_im, sub_zero] at this
    exact lt_of_le_of_lt this (by rw [← dist_eq_norm]; exact mem_ball.1 hwx)
  have := le_abs_self w.im
  linarith

/-- The inverse own-component chart undoes `Ψ` on its domain: `c_U⁻¹(Ψ(w)) = −1/w`. -/
theorem ownComponentChart_inv_relMap (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ) {w : ℂ}
    (hw : w ∈ H) (hwK : -w⁻¹ ∉ QuantumZipper.fwdHull U σ) :
    (ownComponentChart U σ).2.1 (relMap U σ w) = -w⁻¹ := by
  have hc := isDomainChart_ownComponentChart hU hU0 hσ
  have hD : -w⁻¹ ∈ (ownComponentChart U σ).2.1 '' H := by
    rw [hc.2.1]; exact ⟨neg_inv_mem_H hw, hwK⟩
  obtain ⟨v, hv, hve⟩ := hD
  rw [relMap_eq_ownComponentChart, ← hve, hc.1.2.2 v hv]

end Chart

/-! ### Hull increments and the tip -/

/-- **Hull increments shrink to the tip.** For a continuous driver with tip limit `f_t⁻¹ → x` at `0`, the increments
`K_{t+s} \ K_t` lie in `B(x, ε)` for all small `s ≥ 0`. -/
theorem exists_diff_fwdHull_subset_ball {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {x : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv W t) (𝓝[H] 0) (𝓝 x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, 0 ≤ s → s < δ →
      QuantumZipper.fwdHull W (t + s) \ QuantumZipper.fwdHull W t ⊆ ball x ε := by
  obtain ⟨r, hr, hrb⟩ := Metric.tendsto_nhdsWithin_nhds.1 htip ε hε
  -- continuity of `W` at `t`
  have hWt : ContinuousAt (fun s : ℝ => W (t + s) - W t) 0 := by fun_prop
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.continuousAt_iff.1 hWt (r / 3) (by positivity)
  set δ : ℝ := min δ₁ ((r / 9) ^ 2) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ (by positivity)
  refine ⟨δ, hδ0, fun s hs hsδ z hz => ?_⟩
  rcases hs.eq_or_lt with rfl | hs0
  · rw [add_zero, sdiff_self] at hz; exact absurd hz (notMem_empty z)
  rw [QuantumZipper.fwdHull_add_diff hW ht hs] at hz
  obtain ⟨hzD, hzK⟩ := hz
  have hbound : ∀ q ∈ Icc (0 : ℝ) s, |W (t + q) - W t| ≤ r / 3 := by
    intro q hq
    have hq' : dist q 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hq.1]
      exact lt_of_le_of_lt hq.2 (lt_of_lt_of_le hsδ (min_le_left _ _))
    have := hδ₁b hq'
    rw [Real.dist_eq, add_zero, sub_self, sub_zero] at this
    exact this.le
  have hK := QuantumZipper.CaraR.fwdHull_subset_closedBall (A := fun q => W (t + q) - W t) (by fun_prop) hs0 hbound hzK
  rw [mem_closedBall, dist_zero_right] at hK
  have hsq : 3 * Real.sqrt s < r / 3 := by
    have h1 : Real.sqrt s < r / 9 := by
      rw [Real.sqrt_lt' (by positivity)]
      exact lt_of_lt_of_le hsδ (min_le_right _ _)
    linarith
  have hfH : QuantumZipper.fwdMap W t z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hzD
  have hlt : dist (QuantumZipper.fwdMap W t z) 0 < r := by
    rw [dist_zero_right]; linarith
  have := hrb hfH hlt
  rwa [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hzD] at this

/-- **The tip is in the closure of every later hull increment** (Yuan's `exists_mem_diff`). -/
theorem mem_closure_diff_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace w ⊤ Γ)
    (hw : Continuous w) (hw0 : w 0 = 0) {u u' : ℝ} (hu : 0 ≤ u) (huu' : u < u') :
    Γ u.toNNReal ∈ closure (QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) u' \
      QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) u) := by
  have hL := isLoewnerTrace_of_isGeneratingTrace hΓ
  have hW : Continuous fun r : ℝ => w r.toNNReal := hw.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hw0]
  have hΓc : Continuous fun r : ℝ => Γ r.toNNReal := by
    have := hΓ.2.1
    simp only [le_top, ofPred_true] at this
    exact (continuousOn_univ.1 this).comp continuous_real_toNNReal
  set c : ℝ := u' - u with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hex : ∀ n : ℕ, ∃ v ∈ Ioc u (u + c / ((n : ℝ) + 1)),
      Γ v.toNNReal ∈ QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) (u + c / ((n : ℝ) + 1)) \
        QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) u := fun n =>
    hL.exists_mem_diff hW hW0 hu (lt_add_of_pos_right u (by positivity))
  choose v hv hmem using hex
  have hδ0 : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul c
    rw [mul_zero] at h1
    exact h1.congr fun n => by rw [mul_one_div]
  have hvt : Tendsto v atTop (𝓝 u) := by
    have hup : Tendsto (fun n : ℕ => u + c / ((n : ℝ) + 1)) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).add hδ0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (hv n).1.le)
      fun n => (hv n).2
  refine mem_closure_of_tendsto ((hΓc.tendsto u).comp hvt) (Eventually.of_forall fun n => ?_)
  have : c / ((n : ℝ) + 1) ≤ c := div_le_self hc0.le (by linarith [n.cast_nonneg (α := ℝ)])
  exact ⟨fwdHull_mono' (by linarith) (hmem n).1, (hmem n).2⟩

/-! ### The chart trace of the relative chain -/

section Trace

variable {Wc W' : ℝ≥0 → ℝ} {U : ℝ → ℝ} {σ : ℝ} {Tc : ℝ≥0∞} {γ Γ : ℝ≥0 → ℂ}

/-- **The chart trace is the chart image of the counterflow trace** (`relTrace_eq`). Let `γ` be a complete continuous
generating trace of the counterflow driver `Wc`, `W'` a continuous driver with complete continuous generating trace
`Γ`, and `a` the relative clock, strictly increasing before `T_c`, with `K^{W'}_{a(t)} = Ψ(K'_t)` and `K'_t` (and the
counterflow tip) in the domain of `Ψ` for `t < T_c`. If `Γ(a(t)) ∈ ℍ`, then `γ(t) ∈ ℍ` and `Γ(a(t)) = Ψ(γ(t))`. -/
theorem relTrace_eq (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ)
    (hγ : IsGeneratingTrace Wc ⊤ γ) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hΓ : IsGeneratingTrace W' ⊤ Γ)
    (hsm : StrictMonoOn (fun t : ℝ≥0 => relClock U σ (fun r : ℝ => Wc r.toNNReal) t) {t | (t : ℝ≥0∞) < Tc})
    (hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ relClock U σ (fun r : ℝ => Wc r.toNNReal) t)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (relClock U σ (fun r : ℝ => Wc r.toNNReal) t) =
        relMap U σ '' QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t)
    (hdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      ∀ w ∈ QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t, -w⁻¹ ∉ QuantumZipper.fwdHull U σ)
    (hγdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → γ t ∈ H → -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U σ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Tc)
    (hΓH : Γ (relClock U σ (fun r : ℝ => Wc r.toNNReal) t).toNNReal ∈ H) :
    γ t ∈ H ∧ Γ (relClock U σ (fun r : ℝ => Wc r.toNNReal) t).toNNReal = relMap U σ (γ t) := by
  set a : ℝ → ℝ := relClock U σ (fun r : ℝ => Wc r.toNNReal) with ha
  set z₀ := Γ (a t).toNNReal with hz₀
  have hWr : Continuous fun r : ℝ => Wc r.toNNReal := hWc.comp continuous_real_toNNReal
  have hWr0 : (fun r : ℝ => Wc r.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hWc0]
  obtain ⟨T', htT', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htT'' : (t : ℝ) < T' := by exact_mod_cast ENNReal.coe_lt_coe.1 htT'
  have htip : Tendsto (QuantumZipper.fwdMapInv (fun r : ℝ => Wc r.toNNReal) t) (𝓝[H] 0) (𝓝 (γ t)) :=
    IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hWc.continuousOn hWc0 ENNReal.coe_lt_top
  -- the tip of the relative chain is in the closure of the images of small counterflow increments
  have hkey : ∀ ρ > 0, ∃ t' : ℝ, (t : ℝ) < t' ∧
      QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t' \ QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t
        ⊆ ball (γ t) ρ ∧ (t'.toNNReal : ℝ≥0∞) < Tc ∧
      z₀ ∈ closure (relMap U σ '' (QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t' \
        QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t)) := by
    intro ρ hρ
    obtain ⟨δ, hδ, hsub⟩ := exists_diff_fwdHull_subset_ball hWr hWr0 t.2 htip hρ
    set s : ℝ := min (δ / 2) ((T' - t) / 2) with hs
    have hs0 : 0 < s := lt_min (by positivity) (by linarith)
    have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsT : (t : ℝ) + s < T' := by
      have := min_le_right (δ / 2) (((T' : ℝ) - t) / 2); linarith
    set t' : ℝ := t + s with ht'
    have ht'0 : (0 : ℝ) ≤ t' := by positivity
    have ht'nn : ((t'.toNNReal : ℝ≥0) : ℝ) = t' := Real.coe_toNNReal _ ht'0
    have ht'Tc : (t'.toNNReal : ℝ≥0∞) < Tc :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hsT.le)) hT'
    have htt' : t < t'.toNNReal := by
      rw [← NNReal.coe_lt_coe, ht'nn]; linarith
    refine ⟨t', by linarith, hsub s hs0.le hsδ, ht'Tc, ?_⟩
    have hat : a t < a t'.toNNReal := hsm ht ht'Tc htt'
    have hcl := mem_closure_diff_of_isGeneratingTrace hΓ hW' hW'0 (hnn t ht) hat
    rw [hK t ht, hK _ ht'Tc, ht'nn] at hcl
    refine closure_mono ?_ hcl
    rintro z ⟨⟨w, hw, hwz⟩, hz⟩
    exact ⟨w, ⟨hw, fun h => hz ⟨w, h, hwz⟩⟩, hwz⟩
  have hγHbar : 0 ≤ (γ t).im := Sec7.IsGeneratingTrace.mem_Hbar hγ hWc.continuousOn hWc0 le_top
  by_cases hγH : γ t ∈ H
  · refine ⟨hγH, eq_of_forall_dist_le fun ε hε => ?_⟩
    obtain ⟨ρ, hρ, hρb⟩ := Metric.continuousAt_iff.1 (continuousAt_relMap hU hσ hγH (hγdom t ht hγH)) ε hε
    obtain ⟨t', -, hsub, -, hcl⟩ := hkey ρ hρ
    have hball : relMap U σ '' (QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t' \
        QuantumZipper.fwdHull (fun r : ℝ => Wc r.toNNReal) t) ⊆ closedBall (relMap U σ (γ t)) ε := by
      rintro _ ⟨w, hw, rfl⟩
      exact (hρb (mem_ball.1 (hsub hw))).le
    exact mem_closedBall.1 (closure_minimal hball isClosed_closedBall hcl)
  · exfalso
    have hre : γ t = (((γ t).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp only [ofReal_im]
        exact le_antisymm (not_lt.1 hγH) hγHbar
    obtain ⟨δ, hδ, r, hr, hnot⟩ := exists_ball_relMap_notMem hU hU0 hσ hΓH (γ t).re
    obtain ⟨t', htt', hsub, ht'Tc, hcl⟩ := hkey r hr
    obtain ⟨_, ⟨w, hw, rfl⟩, hwz⟩ := Metric.mem_closure_iff.1 hcl δ hδ
    have hwH : w ∈ H := (QuantumZipper.fwdHull_mono (W := fun r : ℝ => Wc r.toNNReal)).2 t' hw.1
    have hwK : -w⁻¹ ∉ QuantumZipper.fwdHull U σ := by
      refine hdom t'.toNNReal ht'Tc w ?_
      rw [Real.coe_toNNReal _ (le_trans t.2 htt'.le)]
      exact hw.1
    have hwb : w ∈ ball (((γ t).re : ℝ) : ℂ) r := by rw [← hre]; exact hsub hw
    exact hnot w hwb hwH hwK (by rw [mem_ball, dist_comm]; exact hwz)

end Trace

end GB6

end Supp8

end InteractingSLE
