/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgAssemblyMean

/-!
# The cross-conditioning law at relative angle `θ`: the image word in the counterflow chart (deterministic)

Packet PROVE-CROSSCOND-THETA. The angle-specific part of PROVE-GLUECOND6/8/10's identification of the union mean in
the counterflow chart `Ψ`, at a general relative angle `θ`. In the field `h`, the exposed sides of the counterflow hull
carry the heights `−λ′ + πχ + θχ` (left) and `λ′ − πχ + θχ` (right): the counterflow's own heights `∓λ′ ± πχ` (read in
the chart `Ψ` with the lift normalized on the physical real line) shifted by `θχ`, since the counterflow is that of
`h − θχ`. The image word therefore has the junction weights `cLT θ`, `cRT θ` (`junction_height_leftT`,
`junction_height_rightT`); at `θ = π/2` they are R57's `cL6`, `cR6` (`cLT_pi_div_two`, `cRT_pi_div_two`).

* the data match `imgData0T … r = returnData (counterflow word of h − θχ at time s) r + θχ` at every real chart point
  off a finite set (`imgData0_eq_returnDataT`: exposed sides by the junction heights, the physical real line by the
  shift `θχ` alone);
* the boundary limits of the union mean in the image chart off a finite set (`exists_finite_tendsto_imgChart_realT`,
  `exists_finite_tendsto_imgChartT`; the slit-side limits are GLUECOND10's, which are generic in the shift);
* the deterministic identification `eqOn_imgChartT` and the per-sample chart mean
  `chartMean_eq_integral_of_sampleT` of the killed image word with the junction weights `cLT θ`, `cRT θ`.

Each proof is the landed one with the shift `θχ` in place of `π/2 χ` and the junction weights `cLT θ`, `cRT θ` in
    place of
`cL6`, `cR6`. Deterministic helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.Theta

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar MartChar.RealFlow Restart.RetAux79 Sec7.StripSysField GlueImg Word49
open Sec7.Lemma71C (capClock)

/-! ### The junction weights at relative angle `θ` -/

section Weights

/-- **The left junction weight at relative angle `θ`**: `(3/2 + θ/π)(κ/2 − 2) − σ` (exposed left height
`−λ′ + πχ + θχ`; at `θ = π/2` R57's `cL6 κ σ = κ − 4 − σ`). -/
def cLT (θ κ σ : ℝ) : ℝ := (3 / 2 + θ / π) * (κ / 2 - 2) - σ

/-- **The right junction weight at relative angle `θ`**: `(3/2 − θ/π)(κ/2 − 2) − σ` (exposed right height
`λ′ − πχ + θχ`; at `θ = π/2` R57's `cR6 κ σ = κ/2 − 2 − σ`). -/
def cRT (θ κ σ : ℝ) : ℝ := (3 / 2 - θ / π) * (κ / 2 - 2) - σ

theorem cLT_pi_div_two : cLT (π / 2) = cL6 := by
  funext κ σ
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [cLT, cL6]
  field_simp
  ring

theorem cRT_pi_div_two : cRT (π / 2) = cR6 := by
  funext κ σ
  have hπ : π ≠ 0 := Real.pi_ne_zero
  simp only [cRT, cR6]
  field_simp
  ring

/-- **The left junction height at relative angle `θ`**: with `ρ′_L = cLT θ κ S`, the flow-line height
`−λ(1 + S + ρ′_L)` beyond the junction is the exposed left height `−λ′ + πχ + θχ`. -/
theorem junction_height_leftT {κ : ℝ} (hκ : 0 < κ) (θ S : ℝ) :
    -(π / Real.sqrt κ) * (1 + S + cLT θ κ S) = -(π / Real.sqrt (16 / κ)) + π * chiC κ + θ * chiC κ := by
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [GlueImg.pi_div_sqrt_sixteen_div hκ, QuantumZipper.chiC, cLT]
  field_simp
  linear_combination (3 * π + 2 * θ) * hsq

/-- **The right junction height at relative angle `θ`**: `λ(1 + S + cRT θ κ S) = λ′ − πχ + θχ`. -/
theorem junction_height_rightT {κ : ℝ} (hκ : 0 < κ) (θ S : ℝ) :
    π / Real.sqrt κ * (1 + S + cRT θ κ S) = π / Real.sqrt (16 / κ) - π * chiC κ + θ * chiC κ := by
  have hr : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [GlueImg.pi_div_sqrt_sixteen_div hκ, QuantumZipper.chiC, cRT]
  field_simp
  linear_combination (2 * θ - 3 * π) * hsq

end Weights

/-! ### The data match at time `0` -/

section MatchT

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (θ : ℝ)

/-- θ-version of `imgData0` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
def imgData0T (κ : ℝ) (ω : ℝ → ℝ) (s : ℝ) : ℝ → ℝ :=
  forceBoundaryData κ (Fin.snoc ρL (cLT θ κ (∑ i, ρL i))) (Fin.snoc ρR (cRT θ κ (∑ j, ρR j)))
    (Fin.snoc (fun i => psiL ω s (xL i)) (junL ω s)) (Fin.snoc (fun j => psiR ω s (xR j)) (junR ω s))

variable {ω : ℝ → ℝ} {s : ℝ}

/-- θ-version of `imgData0_eq_left` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem imgData0_eq_leftT (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s) (hj : 0 < rightImg ω 0 s - ω s)
    (hxL : ∀ i, xL i ≤ 0) (b : ℝ → ℝ) (J : Finset ℝ) {r : ℝ} (hr : r < junL ω s) :
    imgData0T ρL ρR xL xR θ κ ω s r =
      returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ b J ω s) r + θ * chiC κ := by
  have hjL : junL ω s < 0 := by
    rw [junL, neg_div]; exact neg_neg_of_pos (div_pos one_pos hj)
  have hr0 : r < 0 := hr.trans hjL
  have hR : ∀ j, -r⁻¹ < rightImg ω (flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j) s - ω s := by
    intro j
    have h1 := rightImg_mono_index hω hs (flowLineXR_zero_nonneg _ _ j) (x := 0)
    have h2 : -r⁻¹ < rightImg ω 0 s - ω s := by
      have h3 : r < -1 / (rightImg ω 0 s - ω s) := hr
      rw [lt_div_iff₀ hj] at h3
      have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
      rw [h4, div_lt_iff_of_neg hr0]
      linarith [mul_comm (rightImg ω 0 s - ω s) r]
    linarith
  rw [cfDataAt, returnData_forceBoundaryData_left hκ _ _ _ _ hr0 hR, ← junction_height_leftT hκ θ (∑ i, ρL i)]
  unfold imgData0T forceBoundaryData
  simp only [hr0, ↓reduceIte]
  rw [sum_filter_lt_snoc, Finset.filter_true_of_mem fun i _ =>
    hr.trans_le (CrossCond.Word49.junL_le_psiL hω hs hj (hxL i))]
  simp only [hr, ↓reduceIte]
  ring

/-- θ-version of `imgData0_eq_right` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem imgData0_eq_rightT (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s)
    (hj : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxR : ∀ j, 0 ≤ xR j) (b : ℝ → ℝ) (J : Finset ℝ) {r : ℝ}
    (hr : junR ω s < r) :
    imgData0T ρL ρR xL xR θ κ ω s r =
      returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ b J ω s) r + θ * chiC κ := by
  have hjR : 0 < junR ω s := by
    rw [junR, neg_div]; exact neg_pos.2 (div_neg_of_pos_of_neg one_pos hj)
  have hr0 : 0 < r := hjR.trans hr
  have hL : ∀ i, -rightImg (fun r => -ω r) (-flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i) s - ω s <
      -r⁻¹ := by
    intro i
    have h1 := rightImg_mono_index (w := fun r => -ω r) (show Continuous fun r => -ω r from hω.neg) hs
      (neg_nonneg.2 (flowLineXL_zero_nonpos _ _ i)) (x := 0)
    have h2 : -rightImg (fun r => -ω r) 0 s - ω s < -r⁻¹ := by
      have h3 : -1 / (-rightImg (fun r => -ω r) 0 s - ω s) < r := hr
      rw [div_lt_iff_of_neg hj] at h3
      have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
      rw [h4, lt_div_iff₀ hr0]
      linarith [mul_comm (-rightImg (fun r => -ω r) 0 s - ω s) r]
    linarith
  rw [cfDataAt, returnData_forceBoundaryData_right hκ _ _ _ _ hr0 hL, ← junction_height_rightT hκ θ (∑ j, ρR j)]
  unfold imgData0T forceBoundaryData
  simp only [not_lt.2 hr0.le, ↓reduceIte]
  rw [sum_filter_snoc_le, Finset.filter_true_of_mem fun j _ =>
    (CrossCond.Word49.psiR_le_junR hω hs hj (hxR j)).trans hr.le]
  simp only [hr.le, ↓reduceIte]
  ring

/-- θ-version of `imgData0_eq_mid_neg` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem imgData0_eq_mid_negT (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s) (hj : 0 < rightImg ω 0 s - ω s)
    (hxL : ∀ i, xL i ≤ 0) {r : ℝ} (hr0 : r < 0) (hrj : junL ω s < r)
    (hrJ : ∀ x ∈ forceJumpFinset xL xR, x < 0 → psiL ω s x ≠ r) :
    imgData0T ρL ρR xL xR θ κ ω s r = returnData (cfOffset κ) (cfCoeff κ)
      (cfDataAt κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR) ω s) r +
        θ * chiC κ := by
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ) with hbdef
  set J := forceJumpFinset xL xR with hJdef
  have hM : rightImg ω 0 s < -r⁻¹ + ω s := by
    have h3 : -1 / (rightImg ω 0 s - ω s) < r := hrj
    rw [div_lt_iff₀ hj] at h3
    have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
    have h5 : rightImg ω 0 s - ω s < -r⁻¹ := by
      rw [h4, lt_div_iff_of_neg hr0]; linarith [mul_comm (rightImg ω 0 s - ω s) r]
    linarith
  obtain ⟨y, hy0, hyA, hyg⟩ := exists_alive_gImg_eq hω hs hM
  set x' : ℝ := -y⁻¹ with hx'
  have hx'0 : x' < 0 := neg_neg_of_pos (inv_pos.2 hy0)
  have hyx' : -1 / x' = y := by rw [hx']; field_simp
  have hrg : rightImg ω y s - ω s = -r⁻¹ := by rw [rightImg_eq_gImg hω hs hyA, hyg]; ring
  have hpsi : psiL ω s x' = r := by
    unfold psiL
    simp only [hx'0.ne, ↓reduceIte]
    rw [hyx', hrg]
    field_simp
  have hx'J : x' ∉ J := fun h => hrJ x' h hx'0 hpsi
  have hyJ : y ∉ counterflowJumps J := by
    simp only [counterflowJumps, returnExcept, Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨hy0.ne', fun w hw he => hx'J ?_⟩
    have : w = x' := by rw [hx', ← he, inv_neg, inv_inv, neg_neg]
    rwa [← this]
  have hXR : ∀ j, flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j ≠ y := by
    intro j he
    rcases Supp8.flowLineXR_cases 0 j with h | ⟨z, hz, -, h⟩
    · rw [h] at he; exact hy0.ne' he.symm
    · rw [h, sub_zero] at he
      exact hyJ (he ▸ Finset.filter_subset _ _ hz)
  have hb : IsPiecewiseConstantBoundaryData b J := isPiecewiseConstant_forceData κ ρL ρR xL xR _
  have e1 : cfDataAt κ b J ω s (-r⁻¹) = counterflowData κ b y := by
    rw [cfDataAt, show -r⁻¹ = gImg ω y s - ω s by linarith, forceBoundaryData_flow_right _ _ hω hs hy0 hyA hXR]
    exact Sec4.forceBoundaryData_flowLine (by positivity) (isPiecewiseConstant_counterflowData κ hb) hy0.ne' hyJ
  have hlift : liftBoundary x' = liftBoundary r := by simp [liftBoundary, hr0, hx'0]
  have e2 : b x' = -counterflowData κ b y + cfOffset κ + cfCoeff κ * liftBoundary r := by
    rw [← returnData_inverseData (cfOffset κ) (cfCoeff κ) b hx'0.ne, returnData, ← hlift]
    have : -x'⁻¹ = y := by rw [hx', inv_neg, inv_inv, neg_neg]
    rw [this]
    rfl
  have hRHS : returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ b J ω s) r = b x' := by
    rw [returnData, e1, e2]
  have hiff : ∀ i, r < psiL ω s (xL i) ↔ x' < xL i := by
    intro i
    have hxi : xL i ∈ J := Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ i)))
    have hne : xL i ≠ x' := fun h => hx'J (h ▸ hxi)
    rcases (hxL i).lt_or_eq with hneg | h0
    · have hG : 0 < rightImg ω (-1 / xL i) s - ω s := by
        have := rightImg_mono_index hω hs (x := 0) (x' := -1 / xL i)
          (div_nonneg_of_nonpos (by norm_num) (hxL i))
        linarith
      have hya : -1 / xL i ≠ y := fun h => hne (by
        have e : -1 / xL i = -1 / x' := h.trans hyx'.symm
        rw [div_eq_div_iff hneg.ne hx'0.ne] at e
        linarith)
      have hpsi' : psiL ω s (xL i) = -1 / (rightImg ω (-1 / xL i) s - ω s) := by
        unfold psiL; simp only [hneg.ne, ↓reduceIte]
      rw [hpsi', ← neg_inv_lt_iff_lt_neg_one_div hr0 hG, ← hrg, sub_lt_sub_iff_right,
        rightImg_eq_gImg hω hs hyA, ← not_le, rightImg_le_gImg_iff hω hs hyA hya]
      have h1 := neg_inv_lt_iff_of_neg_of_pos hneg hy0
      have h2 : -1 / xL i = -(xL i)⁻¹ := by rw [neg_div, one_div]
      rw [h2, h1, not_lt]
      exact ⟨fun h => lt_of_le_of_ne h hne.symm, le_of_lt⟩
    · rw [h0]
      have : psiL ω s 0 = 0 := by simp [psiL]
      rw [this]
      exact iff_of_true hr0 hx'0
  have hLHS : imgData0T ρL ρR xL xR θ κ ω s r = forceBoundaryData κ ρL ρR xL xR x' := by
    unfold imgData0T forceBoundaryData
    simp only [hr0, hx'0, ↓reduceIte]
    rw [sum_filter_lt_snoc]
    simp only [show ¬ (r < junL ω s) from not_lt.2 hrj.le, ↓reduceIte, add_zero]
    rw [Finset.filter_congr fun i _ => hiff i]
  rw [hLHS, hRHS, hbdef]
  ring

/-- θ-version of `imgData0_eq_mid_pos` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem imgData0_eq_mid_posT (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s)
    (hj : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxR : ∀ j, 0 ≤ xR j) {r : ℝ} (hr0 : 0 < r)
    (hrj : r < junR ω s) (hrJ : ∀ x ∈ forceJumpFinset xL xR, 0 < x → psiR ω s x ≠ r)
    (hrV : ∀ i, -rightImg (fun r => -ω r)
      (-flowLineXL (counterflowData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)))
        (counterflowJumps (forceJumpFinset xL xR)) 0 i) s - ω s ≠ -r⁻¹) :
    imgData0T ρL ρR xL xR θ κ ω s r = returnData (cfOffset κ) (cfCoeff κ)
      (cfDataAt κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR) ω s) r +
        θ * chiC κ := by
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ) with hbdef
  set J := forceJumpFinset xL xR with hJdef
  have hωn : Continuous fun r => -ω r := hω.neg
  have hM : rightImg (fun r => -ω r) 0 s < r⁻¹ - ω s := by
    have h3 : r < -1 / (-rightImg (fun r => -ω r) 0 s - ω s) := hrj
    rw [lt_div_iff_of_neg hj] at h3
    have h4 : -r⁻¹ = -1 / r := by rw [neg_div, one_div]
    have h5 : -r⁻¹ < -rightImg (fun r => -ω r) 0 s - ω s := by
      rw [h4, div_lt_iff₀ hr0]; linarith [mul_comm (-rightImg (fun r => -ω r) 0 s - ω s) r]
    linarith
  obtain ⟨y, hy0, hyA, hyg⟩ := exists_alive_gImg_eq hωn hs hM
  set x' : ℝ := y⁻¹ with hx'
  have hx'0 : 0 < x' := inv_pos.2 hy0
  have hyx' : 1 / x' = y := by rw [hx', one_div, inv_inv]
  have hrg : -rightImg (fun r => -ω r) y s - ω s = -r⁻¹ := by rw [rightImg_eq_gImg hωn hs hyA, hyg]; ring
  have hpsi : psiR ω s x' = r := by
    unfold psiR
    simp only [hx'0.ne', ↓reduceIte]
    rw [hyx', hrg]
    field_simp
  have hx'J : x' ∉ J := fun h => hrJ x' h hx'0 hpsi
  have hyJ : -y ∉ counterflowJumps J := by
    simp only [counterflowJumps, returnExcept, Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    refine ⟨neg_ne_zero.2 hy0.ne', fun w hw he => hx'J ?_⟩
    have hw' : w⁻¹ = y := by linarith
    have : w = x' := by rw [hx', ← hw', inv_inv]
    rwa [← this]
  have hXL : ∀ i, -flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i ≠ y := by
    intro i he
    rcases Supp8.flowLineXL_cases 0 i with h | ⟨z, hz, -, h⟩
    · rw [h, neg_zero] at he; exact hy0.ne' he.symm
    · rw [h, sub_zero] at he
      exact hyJ (by rw [← he, neg_neg]; exact Finset.filter_subset _ _ hz)
  have hb : IsPiecewiseConstantBoundaryData b J := isPiecewiseConstant_forceData κ ρL ρR xL xR _
  have e1 : cfDataAt κ b J ω s (-r⁻¹) = counterflowData κ b (-y) := by
    rw [cfDataAt, show -r⁻¹ = -gImg (fun r => -ω r) y s - ω s by rw [← rightImg_eq_gImg hωn hs hyA]; linarith,
      forceBoundaryData_flow_left _ _ hω hs hy0 hyA hXL fun i h => hrV i (by
        rw [← rightImg_eq_gImg hωn hs hyA] at h; linarith)]
    exact Sec4.forceBoundaryData_flowLine (by positivity) (isPiecewiseConstant_counterflowData κ hb)
      (neg_ne_zero.2 hy0.ne') hyJ
  have hlift : liftBoundary x' = liftBoundary r := by simp [liftBoundary, not_lt.2 hr0.le, not_lt.2 hx'0.le]
  have e2 : b x' = -counterflowData κ b (-y) + cfOffset κ + cfCoeff κ * liftBoundary r := by
    rw [← returnData_inverseData (cfOffset κ) (cfCoeff κ) b hx'0.ne', returnData, ← hlift]
    have : -x'⁻¹ = -y := by rw [hx', inv_inv]
    rw [this]
    rfl
  have hRHS : returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ b J ω s) r = b x' := by
    rw [returnData, e1, e2]
  have hm : -r⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hr0)
  have hiff : ∀ j, psiR ω s (xR j) ≤ r ↔ xR j ≤ x' := by
    intro j
    have hxj : xR j ∈ J := Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ j)))
    have hne : xR j ≠ x' := fun h => hx'J (h ▸ hxj)
    rcases (hxR j).lt_or_eq with hpos | h0
    · have hH : -rightImg (fun r => -ω r) (1 / xR j) s - ω s < 0 := by
        have := rightImg_mono_index hωn hs (x := 0) (x' := 1 / xR j) (one_div_pos.2 hpos).le
        linarith
      have hya : 1 / xR j ≠ y := fun h => hne (by
        have e : 1 / xR j = 1 / x' := h.trans hyx'.symm
        rw [div_eq_div_iff hpos.ne' hx'0.ne'] at e
        linarith)
      have hpsi' : psiR ω s (xR j) = -1 / (-rightImg (fun r => -ω r) (1 / xR j) s - ω s) := by
        unfold psiR; simp only [hpos.ne', ↓reduceIte]
      have hne' : psiR ω s (xR j) ≠ r := hrJ (xR j) hxj hpos
      have hr_eq : r = -1 / -r⁻¹ := by field_simp
      rw [le_iff_lt_or_eq, or_iff_left hne', hpsi']
      conv_lhs => rw [hr_eq]
      rw [neg_one_div_lt_neg_one_div_iff hH hm, ← hrg, sub_lt_sub_iff_right, neg_lt_neg_iff,
        rightImg_eq_gImg hωn hs hyA, ← not_le, rightImg_le_gImg_iff hωn hs hyA hya, not_lt,
        le_one_div hy0 hpos, ← hyx', one_div_one_div]
    · rw [← h0]
      have : psiR ω s 0 = 0 := by simp [psiR]
      rw [this]
      exact iff_of_true hr0.le hx'0.le
  have hLHS : imgData0T ρL ρR xL xR θ κ ω s r = forceBoundaryData κ ρL ρR xL xR x' := by
    unfold imgData0T forceBoundaryData
    simp only [not_lt.2 hr0.le, not_lt.2 hx'0.le, ↓reduceIte]
    rw [sum_filter_snoc_le]
    simp only [show ¬ (junR ω s ≤ r) from not_le.2 hrj, ↓reduceIte, add_zero]
    rw [Finset.filter_congr fun j _ => hiff j]
  rw [hLHS, hRHS, hbdef]
  ring

/-- θ-version of `imgData0_eq_returnData` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem imgData0_eq_returnDataT (hκ : 0 < κ) (hω : Continuous ω) (hs : 0 ≤ s) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {r : ℝ}
    (hr0 : r ≠ 0) (hrL : r ≠ junL ω s) (hrR : r ≠ junR ω s) (hrJ : ∀ x ∈ forceJumpFinset xL xR, psiL ω s x ≠ r)
    (hrJ' : ∀ x ∈ forceJumpFinset xL xR, psiR ω s x ≠ r)
    (hrV : ∀ i, -rightImg (fun r => -ω r)
      (-flowLineXL (counterflowData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)))
        (counterflowJumps (forceJumpFinset xL xR)) 0 i) s - ω s ≠ -r⁻¹) :
    imgData0T ρL ρR xL xR θ κ ω s r = returnData (cfOffset κ) (cfCoeff κ)
      (cfDataAt κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR) ω s) r +
        θ * chiC κ := by
  rcases lt_or_gt_of_ne hr0 with hneg | hpos
  · rcases lt_or_gt_of_ne hrL with h1 | h1
    · exact imgData0_eq_leftT ρL ρR xL xR θ hκ hω hs hjL hxL _ _ h1
    · exact imgData0_eq_mid_negT ρL ρR xL xR θ hκ hω hs hjL hxL hneg h1 fun x hx _ => hrJ x hx
  · rcases lt_or_gt_of_ne hrR with h1 | h1
    · exact imgData0_eq_mid_posT ρL ρR xL xR θ hκ hω hs hjR hxR hpos h1 (fun x hx _ => hrJ' x hx) hrV
    · exact imgData0_eq_rightT ρL ρR xL xR θ hκ hω hs hjR hxR _ _ h1

end MatchT

/-! ### The union mean at the real points of the image chart -/

section WordT

variable {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (θ : ℝ)

/-- θ-version of `imgRhoL` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
abbrev imgRhoLT (κ : ℝ) : Fin (nL + 1) → ℝ := Fin.snoc ρL (cLT θ κ (∑ i, ρL i))

/-- θ-version of `imgRhoR` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
abbrev imgRhoRT (κ : ℝ) : Fin (nR + 1) → ℝ := Fin.snoc ρR (cRT θ κ (∑ j, ρR j))

/-- θ-version of `bData` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
abbrev bDataT (κ : ℝ) : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)

/-- θ-version of `badPts` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
def badPtsT (κ : ℝ) (ω : ℝ → ℝ) (s : ℝ) : Set ℝ :=
  {0, junL ω s, junR ω s} ∪ psiL ω s '' ↑(forceJumpFinset xL xR) ∪ psiR ω s '' ↑(forceJumpFinset xL xR) ∪
    ↑(returnExcept (forceJumpFinset (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)))

/-- θ-version of `badPts_finite` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem badPts_finiteT (κ : ℝ) (ω : ℝ → ℝ) (s : ℝ) : (badPtsT ρL ρR xL xR θ κ ω s).Finite := by
  unfold badPtsT
  refine (((Set.toFinite _).union ?_).union ?_).union (Finset.finite_toSet _)
  · exact (Finset.finite_toSet _).image _
  · exact (Finset.finite_toSet _).image _

variable {ω : ℝ → ℝ} {s : ℝ} {W' : ℝ → ℝ} {η' : ℝ → ℂ} {T : ℝ}

/-- θ-version of `exists_finite_tendsto_imgChart_real` (`Sec5.GlueCondUnionImgCf`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem exists_finite_tendsto_imgChart_realT (hκ : 0 < κ) (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s)
    (hB : HasBdryLimits (fwdMapInv ω s)) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {A : Set ℂ} (hAb : Bornology.IsBounded A) (hAcl : ∀ z ∈ closure A, z ∈ A ∨ z = 0)
    (hAG : Disjoint A (negInv '' fwdHull ω s)) (hAH : A ⊆ H) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (A ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (A ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 < T)
    {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)) u) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E → (extendFrom H (fwdMapInv W' T) x).im = 0 →
      Tendsto (fun y => M (revChartInv ω s (fwdMapInv W' T y)) + θ * chiC κ -
        (u y - chiC κ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi ω s (revChartInv ω s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set Eb := badPtsT ρL ρR xL xR θ κ ω s with hEb
  refine ⟨(fun r : ℝ => (fwdMap W' T r).re) '' Eb ∪ {chartAL W' T, chartAR W' T},
    ((badPts_finiteT ρL ρR xL xR θ κ ω s).image _).union (by simp), fun x hx hFim => ?_⟩
  simp only [mem_union, mem_image, mem_insert_iff, mem_singleton_iff, not_or, not_exists, not_and] at hx
  obtain ⟨hxE, hxAL, hxAR⟩ := hx
  set r := extendFrom H (fwdMapInv W' T) x with hrdef
  have hreq : r = ((r.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hFim])
  have hF : extendFrom H (fwdMapInv W' T) x = (r.re : ℂ) := by rw [← hrdef]; exact hreq
  have hr0 : r.re ≠ 0 := by
    intro h0
    have hF0 : extendFrom H (fwdMapInv W' T) x = 0 := by rw [hF, h0, Complex.ofReal_zero]
    rcases extendFrom_eq_zero_imp hη' hη'p hW' hW'0 hT hF0 with h | h
    · exact hxAR (by rw [chartAR]; linarith)
    · exact hxAL (by rw [chartAL]; linarith)
  have hxr := (eq_re_fwdMap_of_extendFrom_eq hη' hη'p hW' hW'0 hT.le hr0 hF).1
  have hrE : r.re ∉ Eb := fun h => hxE r.re h hxr.symm
  simp only [hEb, badPtsT, mem_union, mem_insert_iff, mem_singleton_iff, mem_image, Finset.mem_coe, not_or,
    not_exists, not_and] at hrE
  obtain ⟨⟨⟨⟨-, hrjL, hrjR⟩, hrJ⟩, hrJ'⟩, hrV⟩ := hrE
  -- the counterflow mean's boundary data
  have hV := isBoundedHarmonicExtension_retMean (κ := κ) (S := forceJumpFinset
    (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
    (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) (by rwa [coe_forceJumpFinset])
  have hrV' : r.re ∉ (returnExcept (forceJumpFinset
      (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) : Set ℝ) := hrV
  -- the image marks are not at `r`
  have hmL : ∀ i, imgMarkL xL ω s i ≠ r.re := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [imgMarkL, Fin.snoc_last]; exact fun h => hrjL h.symm
    · simp only [imgMarkL, Fin.snoc_castSucc]
      exact hrJ (xL i) (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (Finset.mem_univ i))))
  have hmR : ∀ j, imgMarkR xR ω s j ≠ r.re := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [imgMarkR, Fin.snoc_last]; exact fun h => hrjR h.symm
    · simp only [imgMarkR, Fin.snoc_castSucc]
      exact hrJ' (xR j) (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_univ j))))
  have hmL0 : ∀ i, imgMarkL xL ω s i ≤ 0 := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [imgMarkL, Fin.snoc_last, junL, neg_div]; exact (neg_neg_of_pos (div_pos one_pos hjL)).le
    · simp only [imgMarkL, Fin.snoc_castSucc]; exact CrossCond.Word49.psiL_nonpos hω hs hjL (hxL i)
  -- the data match
  have hmatch : forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
      (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
      (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T) x =
      returnData (cfOffset κ) (cfCoeff κ) (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s) r.re +
        θ * chiC κ := by
    rw [forceBoundaryData_imgChart_eq _ _ hη' hη'p hW' hW'0 hT.le hmL0 hr0 hF hmL hmR]
    refine imgData0_eq_returnDataT ρL ρR xL xR θ hκ hω hs hjL hjR hxL hxR hr0 hrjL hrjR (fun c hc => hrJ c hc)
      (fun c hc => hrJ' c hc) fun i h => hrV' ?_
    simp only [returnExcept, Finset.coe_insert, Finset.coe_image, mem_insert_iff, mem_image, Finset.mem_coe]
    refine Or.inr ⟨_, Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ i))), ?_⟩
    have h' : cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s i = -r.re⁻¹ := h
    rw [h', inv_neg, inv_inv, neg_neg]
  have hxI := notMem_forceJumpSet_imgChart hη' hη'p hW' hW'0 hT.le hmL0 (fun j => ?_) hr0 hF hmL hmR
  · exact tendsto_imgChart_of_real hω hω0 hs hB hAb hAcl hAG hAH hG hInf hId hV hW' hW'0 hη' hη'p hT.le hu hr0
      hF hrV' hxI hmatch
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [imgMarkR, Fin.snoc_last, junR, neg_div]
      exact (neg_pos.2 (div_neg_of_pos_of_neg one_pos hjR)).le
    · simp only [imgMarkR, Fin.snoc_castSucc]; exact CrossCond.Word49.psiR_nonneg hω hs hjR (hxR j)

end WordT

/-! ### The assembly at the slit and real points, and the identification -/

section IdentT

variable {Wα ω W' : ℝ → ℝ} {t s T : ℝ} {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (θ : ℝ)
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- θ-version of `exists_finite_tendsto_imgChart` (`Sec5.GlueCondUnionImgAssembly`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem exists_finite_tendsto_imgChartT {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hκ : 0 < κ)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    {u uA : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)) u)
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t) (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + θ * chiC κ -
        (uA (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (α v)) (𝓝 0)) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E →
      Tendsto (fun y => M (revChartInv ω s (fwdMapInv W' T y)) + θ * chiC κ -
        (u y - chiC κ * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi ω s (revChartInv ω s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hA := isHPHull_fwdHull hWα ht.le
  obtain ⟨E₁, hE₁, h1⟩ := exists_finite_tendsto_imgChart_realT ρL ρR xL xR θ hκ hω hω0 hs hB hjL hjR hxL hxR hA.2.1
    (mem_or_eq_zero_of_mem_closure_fwdHull hWα ht.le hKt) hdisj hA.1 hv hG hInf hId hW' hW'0 hη' hη'p hT hu
  refine ⟨E₁ ∪ {0}, hE₁.union (finite_singleton 0), fun x hx => ?_⟩
  rcases (extendFrom_im_nonneg hη' hW' hW'0 hT.le x).lt_or_eq with hpos | h0
  · have hxx := chartAL_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hpos
    have hx0 : x ≠ 0 := fun h => hx (Or.inr h)
    have hmL := imgMarkL_nonpos hω hs hjL hxL
    have hmR := imgMarkR_nonneg hω hs hjR hxR
    rcases lt_or_gt_of_ne hx0 with hneg | hpos'
    · exact tendsto_imgChart_slit_left_of_flow hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjL hW' hW'0 hT hη' hη'p hGc
        hdisj hdis hK' htip hxL hxR hmL hmR huA hu hFl hxx.1 hneg
    · exact tendsto_imgChart_slit_right_of_flow hα hαp hWα hWα0 ht hKt hω hω0 hs hB hKs hjR hW' hW'0 hT hη' hη'p hGc
        hdisj hdis hK' htip hxL hxR hmL hmR huA hu hFl hxx.2 hpos'
  · exact h1 x (fun h => hx (Or.inl h)) h0.symm

/-- θ-version of `eqOn_imgChart` (`Sec5.GlueCondUnionImgAssembly`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem eqOn_imgChartT {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hκ : 0 < κ)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    {u uA : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgRhoLT ρL θ κ) (imgRhoRT ρR θ κ)
        (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
        (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)) u)
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t) (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + θ * chiC κ -
        (uA (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (α v)) (𝓝 0))
    {w u₀ : ℂ → ℝ} (hMw : ∀ z, M z + θ * chiC κ = w z + u₀ z)
    (huniq : ∀ z₀ ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s), ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀,
        w z + u₀ z = G (φc z) - chiC κ * L z) :
    ∀ z ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s), w z + u₀ z =
      u (fwdMap W' T (revChart ω s z)) -
        chiC κ * ((logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im) := by
  obtain ⟨E, hE, hlim⟩ := exists_finite_tendsto_imgChartT ρL ρR θ hα hαp hWα hWα0 ht hKt hκ hω hω0 hs hB hKs hjL hjR
    hGc hdisj hdis hxL hxR hv hG hInf hId hW' hW'0 hη' hη'p hT hK' htip hu huA hFl
  have hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s := fun z hz =>
    ⟨(isHPHull_fwdHull hWα ht.le).1 hz, fun h => disjoint_left.1 hdisj hz h⟩
  have hΦ := isConformalBijection_imgPhiChart hω hω0 hs hW' hW'0 hT.le hAG hK'
  have hφc := isConformalBijection_imgFwdChart hω hω0 hs hW' hW'0 hT.le hAG hK'
  obtain ⟨hLc, hder⟩ := deriv_imgFwdChart_eq hWα ht.le hω hω0 hs hGc hW' hT.le hAG hK'
  have hIH : I ∈ H := show (0 : ℝ) < I.im by simp
  have hz₀ := hΦ.2.mapsTo hIH
  have hcc := connectedComponentIn_H_diff_union hω hω0 hs hW' hW'0 hT.le hAG hK' hz₀
  have hf := isConformalBijection_comp hΦ isConformalBijection_cayleyInv
  have hφ : ∀ y ∈ H, fwdMap W' T (revChart ω s (revChartInv ω s (fwdMapInv W' T y))) = y := fun y hy => by
    rw [revChart_revChartInv hω hω0 hs (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy),
      QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hT.le hy]
  have hdisk := tendsto_disk_of_imgChart (v := w) (F := u₀) (G := u) (χ := chiC κ)
    (φc := fun z => fwdMap W' T (revChart ω s z))
    (L := fun z => (logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im) hlim
    (fun y _ => (hMw _).symm) hφ (fun y hy => by
      simp only [revChart_revChartInv hω hω0 hs (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy)])
  have hEd : (insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' E)).Finite := (hE.image _).insert 1
  have key := huniq _ hz₀
  rw [hcc] at key
  exact key _ _ u (fun z => (logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im) _
    hf hφc hu.1 hu.2.1 hLc hder hEd hdisk

end IdentT

/-! ### The counterflow mean in the counterflow chart -/

section MeanT

variable {κ : ℝ} {nL nR : ℕ}

/-- θ-version of `cfMeanQ_add_eq_retMean_add` (`Sec5.CrossCondMartWeights`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem cfMeanQ_add_eq_retMean_addT (hκ : 0 < κ) (θ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      u') (t : ℝ≥0) (y : HistorySpace 0 0) {z : ℂ} (hz : z ∈ H \ cfHullQ t y) :
    cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR) u' t y z +
        u₀ z + chiC κ * (GlueImg.logDerivPsi (Ito.rpath (Sec4.regPath (cfStop t y))) t z).im =
      GlueImg.retMean κ (cfU κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
          (forceJumpFinset xL xR) t (cfStop t y)) (revChart (Ito.rpath (Sec4.regPath (cfStop t y))) t z) +
        θ * chiC κ := by
  have hb := isPiecewiseConstant_forceData κ ρL ρR xL xR (-(θ * chiC κ))
  have hu_b : IsBoundedHarmonicExtension (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
      (forceJumpFinset xL xR) (fun z => u₀ z + -(θ * chiC κ)) := by
    rw [coe_forceJumpFinset]
    exact isBoundedHarmonicExtension_add_const hu₀ _
  have h := GlueImg.cfMeanQ_add_eq_retMean hκ hb hu_b hu' t y hz
  linear_combination h

end MeanT

/-! ### The chart mean on one good sample -/

section OneSampleT

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}

/-- θ-version of `chartMean_eq_integral_of_sample` (`Sec5.GlueCondUnionImgAssemblyMean`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem chartMean_eq_integral_of_sampleT (hκ : 0 < κ) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) {t : ℝ≥0} (ht : 0 < t)
    (htP : (t : ℝ) ∈ gPre s ζ W E p) {Wα : ℝ → ℝ} (hα : IsLoewnerTrace Wα (seedLine ζ W p.1))
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0)
    (hA : hullAt t (killedHistory W VL VR ζ p.1) = seedLine ζ W p.1 '' Ioc 0 t) (hy : p.2 ∈ goodHitSet)
    (himg : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 < t →
      Disjoint (seedLine ζ W p.1 '' Ioc 0 t) (negInv '' fwdHull (cfDrv p.2) s) →
      ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
        IsProperArc η' ∧ fwdHull W' T = revChart (cfDrv p.2) s '' (seedLine ζ W p.1 '' Ioc 0 t) ∧
          η' T = revChart (cfDrv p.2) s (seedLine ζ W p.1 t))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    {uA : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t) (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    {w : ℂ → ℝ}
    (hwFl : ∀ z₀ ∈ hullAt t (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, cfHullQ s p.2 ∩ ball z₀ r ⊆ hullAt t (killedHistory W VL VR ζ p.1)) →
      Tendsto (fun z => w z - (couplingMean κ Wα t uA z - u₀ z))
        (𝓝[H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)] z₀) (𝓝 0))
    (hwG : ∀ z₀ ∈ cfHullQ s p.2 ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, hullAt t (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ cfHullQ s p.2) →
      Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
          (forceJumpFinset xL xR) u' s p.2 z)
        (𝓝[H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)] z₀) (𝓝 0))
    (hwInf : Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
          (forceJumpFinset xL xR) u' s p.2 z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2))) (𝓝 0))
    (huniq : ∀ z₀ ∈ H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2),
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      SupercriticalConformalCovariance.IsConformalBijection f (ball 0 1)
        (connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀) →
      SupercriticalConformalCovariance.IsConformalBijection φc
        (connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀,
        w z + u₀ z = G (φc z) - chiC κ * L z)
    {φ : TestOn upperHalfPlaneOpens}
    (hφ : tsupport φ ⊆ H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) :
    Sec7.Lemma71D.chartMean κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) (fun r => imgW s ζ W E r p)
        (fun i r => imgVL xL s ζ W E i r p) (fun j r => imgVR xR s ζ W E j r p) (cfChart s p.2)
        (2 * π * chiC κ) (chiC κ) φ (capClock (gCurve s ζ W E p) t).toNNReal =
      ∫ z, (w z + u₀ z) * φ z := by
  set ω := cfDrv0 s p.2 with hωdef
  have hω : Continuous ω := continuous_cfDrv0 s p.2
  have hω0 : ω 0 = 0 := cfDrv0_zero s p.2
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 ht
  obtain ⟨hαp, hGc, hjL, hjR, hGeq⟩ := hEg p hp
  have hAfwd : hullAt t (killedHistory W VL VR ζ p.1) = fwdHull Wα t := by
    rw [hA, fwdHull_eq_image_Ioc hα hαp t.coe_nonneg]
  have hpre : (t : ℝ) ∈ preContact (seedLine ζ W p.1) (cfHullQ s p.2) := gPre_of_mem hp ▸ htP
  have hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s) := by
    rw [fwdHull_eq_image_Ioc hα hαp t.coe_nonneg, ← hGeq]
    refine disjoint_left.2 ?_
    rintro _ ⟨u, hu, rfl⟩ hG
    exact hpre.2 u ⟨hu.1.le, hu.2⟩ hG
  have hKt := ofReal_notMem_closure_of_isProperArc hα hαp t.coe_nonneg
  have hdis := disjoint_closure_fwdHull_negInv hWα t.coe_nonneg hKt hω s.coe_nonneg hdisj
  have hB := hasBdryLimits_cfDrv0 hy.1 s
  have hKs := eq_zero_of_mem_closure_cfDrv0 hy s
  -- the image chain
  have hd' : Disjoint (seedLine ζ W p.1 '' Ioc 0 t) (negInv '' fwdHull (cfDrv p.2) s) := by
    rw [← fwdHull_cfDrv0 hy.1 s, ← fwdHull_eq_image_Ioc hα hαp t.coe_nonneg]; exact hdisj
  obtain ⟨W', hW', hW'0, T, hT, η', hη', hη'p, hK'', htip⟩ := himg s s.coe_nonneg t ht' hd'
  rw [← revChart_cfDrv0 hy.1 s] at hK'' htip
  have hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t := by
    rw [hK'', fwdHull_eq_image_Ioc hα hαp t.coe_nonneg]
  -- the counterflow mean in the chart `Ψ`
  set bd : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ) with hbd
  set v := cfU κ bd (forceJumpFinset xL xR) s (cfStop s p.2) with hvdef
  have hv : IsBoundedHarmonicExtension (cfDataAt κ bd (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ bd (forceJumpFinset xL xR) ω s) (cfMarkR κ bd (forceJumpFinset xL xR) ω s)) v := by
    have h1 := isBoundedHarmonicExtension_cfU κ bd (forceJumpFinset xL xR) s (cfStop s p.2)
    have e := rpath_regPath_cfStop_eq hy.1 s
    have hL : cfPosL κ bd (forceJumpFinset xL xR) (Sec4.regPath (cfStop s p.2)) s =
        cfMarkL κ bd (forceJumpFinset xL xR) ω s := by
      funext i; rw [hωdef, ← e]; simp [cfPosL, cfMarkL, Ito.rpath]
    have hR : cfPosR κ bd (forceJumpFinset xL xR) (Sec4.regPath (cfStop s p.2)) s =
        cfMarkR κ bd (forceJumpFinset xL xR) ω s := by
      funext i; rw [hωdef, ← e]; simp [cfPosR, cfMarkR, Ito.rpath]
    rw [hL, hR] at h1
    exact h1
  set mG : ℂ → ℝ := fun z => cfMeanQ κ bd (forceJumpFinset xL xR) u' s p.2 z + u₀ z - θ * chiC κ with hmG
  set M : ℂ → ℝ := fun z => w z + u₀ z - θ * chiC κ with hM
  have hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (GlueImg.logDerivPsi ω s z).im =
      GlueImg.retMean κ v (revChart ω s z) := by
    intro z hz
    have h1 := cfMeanQ_add_eq_retMean_addT hκ θ ρL ρR xL xR hu₀ hu' s p.2 (z := z) (hGeq ▸ hz)
    rw [rpath_regPath_cfStop_eq hy.1 s] at h1
    simp only [hmG]
    linarith
  rw [hAfwd, hGeq] at hwFl hwG hwInf huniq hφ
  have hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0) := by
    intro z₀ hz₀ hr
    refine (hwG z₀ hz₀ hr).congr fun z => ?_
    simp only [hM, hmG]; ring
  have hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0) := by
    refine hwInf.congr fun z => ?_
    simp only [hM, hmG]; ring
  have hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + θ * chiC κ -
      (uA (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (seedLine ζ W p.1 v)) (𝓝 0) := by
    intro v hv0 hvt
    have hαv : seedLine ζ W p.1 v ∈ fwdHull Wα t := by
      rw [fwdHull_eq_image_Ioc hα hαp t.coe_nonneg]; exact ⟨v, ⟨hv0, hvt.le⟩, rfl⟩
    have hαvG : seedLine ζ W p.1 v ∉ negInv '' fwdHull ω s := fun h => disjoint_left.1 hdisj hαv h
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl _ hαvG
    refine (hwFl _ (Or.inl hαv) ⟨r, hr, fun z hz => absurd hz.1 (hball hz.2)⟩).congr fun z => ?_
    simp only [hM, couplingMean]; ring
  -- the bounded harmonic extension of the image word at `T`
  obtain ⟨u, hu⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
    (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
    (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)
  have hid := eqOn_imgChartT ρL ρR θ hα hαp hWα hWα0 ht' hKt hκ hω hω0 s.coe_nonneg hB hKs hjL hjR hGc hdisj
    hdis hxL hxR hv hG hInf hId hW' hW'0 hη' hη'p hT hK' htip hu huA hFl (w := w) (u₀ := u₀)
    (fun z => by simp only [hM]; ring) huniq
  -- the killed image word at `σ(t)`
  have hKγ : fwdHull W' T = gCurve s ζ W E p '' Ioc 0 t := by
    rw [gCurve_of_mem hp, hK', fwdHull_eq_image_Ioc hα hαp t.coe_nonneg, image_image]
    exact image_congr fun u hu => (imgCurve_of_pos hu.1).symm
  obtain ⟨hTc, hmc⟩ := meanCan_img49_eq (κ := κ) (xL := xL) (xR := xR) hEg hp htP ht' hW' hW'0 hη' hη'p hT hKγ
    (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
  have hmL : ∀ i, -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T ≤ 0 := fun i => by
    have := le_rightImg (show Continuous fun r => -W' r from hW'.neg) (-imgMarkL xL ω s i) hT.le
    linarith
  have hmR : ∀ j, 0 ≤ rightImg W' (imgMarkR xR ω s j) T - W' T := fun j => by
    have := le_rightImg hW' (imgMarkR xR ω s j) hT.le
    linarith
  have hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s := fun z hz =>
    ⟨(isHPHull_fwdHull hWα t.coe_nonneg).1 hz, fun h => disjoint_left.1 hdisj hz h⟩
  have hmaps := GlueImg.revChart_mapsTo_H_diff hω hω0 s.coe_nonneg hAG
  rw [← hK'] at hmaps
  rw [← hTc, Sec7.Lemma71D.chartMean]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  have hzC := hφ (subset_tsupport _ hz)
  have hfH : fwdMap W' T (revChart ω s z) ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT.le (hmaps hzC)
  show (Coupling.meanCan κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) (fun r => imgW s ζ W E r p)
      (fun i r => imgVL xL s ζ W E i r p) (fun j r => imgVR xR s ζ W E j r p) T.toNNReal (revChart ω s z) -
      2 * π * chiC κ - chiC κ * (cfChart s p.2).2.2 z) * φ z = (w z + u₀ z) * φ z
  rw [hmc, ← Ito.eqOn_meanHarmonic hmL hmR hu hfH, hid z hzC]
  have := chart_shift_eq κ s p.2 z
  congr 1
  linarith

end OneSampleT

end InteractingSLE.Sec5.CrossCond.Theta
