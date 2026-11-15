import InteractingSLE.Spec.Supplement.LP2Calc
import InteractingSLE.Spec.Supplement.LP3Flow
import InteractingSLE.Spec.Zhan.AvoidClock
import InteractingSLE.Spec.Sec7.TwoForceMain3Transfer

/-!
# Lemma LP2: pathwise facts for the single right seed

Packet PROVE-LP16. Along one path of the canonical single-right-seed evolution (`nL = 0`, one right mark at `0` of
weight `ρ`, infinite lifetime):

* `w_eq_of_path`: `W_t = √k B_t − (ρ/2) V_t` (the force drift `ρ/(W − V)` is `−(ρ/2)` times the mark's speed
  `2/(V − W)`);
* `vR_lt_of_isForwardSol`: while a passive point `x > 0` is alive, its image stays strictly to the right of the mark:
  `V_t < g_t(x) = W_t + Re f_t(x)`. (The gap `D = g(x) − V` solves `D' = −2D/(XR)`; near a first zero `R = X − D` is
  bounded below, so `D e^{Kt}` is nondecreasing there.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.LP.LP2

open QuantumZipper QuantumZipper.RS

section Path

variable {κ ρ : ℝ} {xL ρL : Fin 0 → ℝ} {w b : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ}
  {vR : Fin 1 → ℝ≥0 → ℝ}

/-- `ρ/(w − v) = −(ρ/2) · 2/(v − w)` (also at `w = v`, where both sides are `0`). -/
theorem div_sub_eq_neg_half_mul (ρ w v : ℝ) : ρ / (w - v) = -(ρ / 2) * (2 / (v - w)) := by
  rw [show w - v = -(v - w) by ring, div_neg]; ring

/-- **The driver of the single right seed**: `W_t = √k B_t − (ρ/2) V_t`. -/
theorem w_eq_of_path (hp : IsIntegratedSLEPath κ xL (fun _ => 0) ρL (fun _ => ρ) w vL vR b ⊤)
    (t : ℝ≥0) : w t = Real.sqrt κ * b t - ρ / 2 * vR 0 t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, -, hvReq, -⟩ := hp
  have hw := hweq t ENNReal.coe_lt_top
  have hv := hvReq t ENNReal.coe_lt_top 0
  simp only [Fin.sum_univ_zero, Fin.sum_univ_one, add_zero] at hw
  simp only [zero_add] at hv
  have hint : (∫ s in (0 : ℝ)..t, ρ / (w s.toNNReal - vR 0 s.toNNReal)) =
      -(ρ / 2) * ∫ s in (0 : ℝ)..t, 2 / (vR 0 s.toNNReal - w s.toNNReal) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => div_sub_eq_neg_half_mul _ _ _
  rw [hw, hint, ← hv]
  ring

/-- **The passive point stays right of the mark.** If `x > 0` is alive on `[0, T]`, then `V_t < W_t + Re f_t(x)`
for `t ∈ [0, T]`. -/
theorem vR_lt_of_isForwardSol
    (hp : IsIntegratedSLEPath κ xL (fun _ => 0) ρL (fun _ => ρ) w vL vR b ⊤) {x T : ℝ} (hx : 0 < x)
    (hT : 0 ≤ T) {u : ℝ → ℂ} (hu : IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) T u) :
    ∀ t ∈ Icc (0 : ℝ) T, vR 0 t.toNNReal < w t.toNNReal + (u t).re := by
  obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
  obtain ⟨-, -, hvR0, -, -, hvRc, -, -, hwvR, -, -, hgR, -, -, hvReq, -⟩ := hp
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  set V : ℝ → ℝ := fun s => vR 0 s.toNNReal with hVdef
  have hW : Continuous W := hwc.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hVc : Continuous V :=
    (continuousOn_univ.1 (by simpa using hvRc 0)).comp continuous_real_toNNReal
  have hV0 : V 0 = 0 := by simp [hVdef, hvR0 0]
  have hWV : ∀ s, W s ≤ V s := fun s => hwvR s.toNNReal ENNReal.coe_lt_top 0
  have hVeq : ∀ t, 0 ≤ t → V t = ∫ s in (0 : ℝ)..t, 2 / (V s - W s) := by
    intro t ht
    have h := hvReq t.toNNReal ENNReal.coe_lt_top 0
    rw [Real.coe_toNNReal _ ht, zero_add] at h
    exact h
  have hVint : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s => 2 / (V s - W s)) volume 0 t := by
    intro t ht
    have h := Zhan.intervalIntegrable_two_div_of_inv (w := w) (u := vR 0)
      (hgR t.toNNReal ENNReal.coe_lt_top 0)
    rwa [Real.coe_toNNReal _ ht] at h
  obtain ⟨c, hc, hcle⟩ := exists_pos_le_re_of_isForwardSol hW hW0 hx hT hu
  set Y : ℝ → ℝ := realTamed W c x with hYdef
  have hY : ∀ t ∈ Icc (0 : ℝ) T, Y t = (u t).re := realTamed_eq_re_of_isForwardSol hW hW0 hc hu hcle
  have hYc : ContinuousOn Y (Icc 0 T) := continuousOn_realTamed hW hc hT x
  have hYeq : ∀ t, 0 ≤ t → Y t + W t = x + ∫ s in (0 : ℝ)..t, realDrift c (Y s) := by
    intro t ht
    rw [hYdef, realTamed_eq hW hc x ht]; ring
  have hYge : ∀ t ∈ Icc (0 : ℝ) T, c ≤ Y t := fun t ht => by rw [hY t ht]; exact hcle t ht
  -- the gap `D = g(x) − V`
  set D : ℝ → ℝ := fun t => Y t + W t - V t with hDdef
  have hDc : ContinuousOn D (Icc 0 T) := (hYc.add hW.continuousOn).sub hVc.continuousOn
  suffices hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < D t by
    intro t ht
    have := hpos t ht
    rw [← hY t ht]
    simp only [hDdef, hWdef, hVdef] at this ⊢
    linarith
  by_contra hcon
  push Not at hcon
  set S : Set ℝ := Icc 0 T ∩ {t | D t ≤ 0} with hSdef
  have hSne : S.Nonempty := by obtain ⟨t, ht, hle⟩ := hcon; exact ⟨t, ht, hle⟩
  have hScl : IsClosed S := hDc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set s := sInf S with hsdef
  have hsS : s ∈ S := hScl.csInf_mem hSne hSbdd
  have hbefore : ∀ t ∈ Icc (0 : ℝ) T, t < s → 0 < D t := by
    intro t ht hts
    by_contra hle
    exact absurd (csInf_le hSbdd ⟨ht, not_lt.1 hle⟩) (not_le.2 hts)
  have hD0 : D 0 = x := by
    have h := hYeq 0 le_rfl
    simp only [intervalIntegral.integral_same, add_zero] at h
    simp only [hDdef, hV0]; linarith
  have hs0 : 0 < s := by
    rcases hsS.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have h2 := hsS.2; simp only [mem_ofPred_eq] at h2; rw [← h, hD0] at h2; linarith
  -- near `s`, `D < c/2`
  have hev : ∀ᶠ t in 𝓝[Icc 0 T] s, D t < c / 2 :=
    (hDc s hsS.1).eventually (gt_mem_nhds (by have := hsS.2; simp only [mem_ofPred_eq] at this; linarith))
  obtain ⟨δ, hδ, hδD⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set s₀ := max 0 (s - δ / 2) with hs₀def
  have hs₀s : s₀ < s := max_lt hs0 (by linarith)
  have hs₀0 : 0 ≤ s₀ := le_max_left _ _
  have hJ : ∀ t ∈ Icc s₀ s, t ∈ Icc (0 : ℝ) T := fun t ht =>
    ⟨hs₀0.trans ht.1, ht.2.trans hsS.1.2⟩
  have hJD : ∀ t ∈ Icc s₀ s, D t < c / 2 := by
    intro t ht
    refine hδD ⟨?_, hJ t ht⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have : s - δ / 2 ≤ s₀ := le_max_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hJR : ∀ t ∈ Icc s₀ s, c / 2 < V t - W t := by
    intro t ht
    have h1 := hYge t (hJ t ht); have h2 := hJD t ht
    simp only [hDdef] at h2; linarith
  -- `f = D e^{Kt}` is nondecreasing on `[s₀, s]`
  set K : ℝ := 4 / c ^ 2 with hK
  set f : ℝ → ℝ := fun t => D t * Real.exp (K * t) with hfdef
  have hfc : ContinuousOn f (Icc s₀ s) :=
    (hDc.mono fun t ht => hJ t ht).mul (by fun_prop)
  have hderiv : ∀ t ∈ Ioo s₀ s, HasDerivAt f
      ((realDrift c (Y t) - 2 / (V t - W t) + K * D t) * Real.exp (K * t)) t := by
    intro t ht
    have htT : t ∈ Ioo (0 : ℝ) T := ⟨hs₀0.trans_lt ht.1, ht.2.trans_le hsS.1.2⟩
    have hYct : ContinuousAt Y t := hYc.continuousAt (Icc_mem_nhds htT.1 htT.2)
    have hIoo : IsOpen (Ioo (0 : ℝ) T) := isOpen_Ioo
    have hg1c : ContinuousOn (fun r => realDrift c (Y r)) (Ioo 0 T) :=
      (lipschitz_realDrift hc).continuous.comp_continuousOn (hYc.mono Ioo_subset_Icc_self)
    have hg1 : HasDerivAt (fun t => ∫ r in (0 : ℝ)..t, realDrift c (Y r)) (realDrift c (Y t)) t := by
      refine intervalIntegral.integral_hasDerivAt_right ?_
        (hg1c.stronglyMeasurableAtFilter hIoo t htT)
        ((lipschitz_realDrift hc).continuous.continuousAt.comp hYct)
      exact ((lipschitz_realDrift hc).continuous.comp_continuousOn
        (hYc.mono (Icc_subset_Icc le_rfl htT.2.le))).intervalIntegrable_of_Icc htT.1.le
    have hRpos : ∀ r ∈ Ioo s₀ s, 0 < V r - W r := fun r hr =>
      (by positivity : (0 : ℝ) < c / 2).trans (hJR r (Ioo_subset_Icc_self hr))
    have hg2c : ContinuousOn (fun r => 2 / (V r - W r)) (Ioo s₀ s) :=
      continuousOn_const.div (hVc.continuousOn.sub hW.continuousOn) fun r hr => (hRpos r hr).ne'
    have hg2 : HasDerivAt (fun t => ∫ r in (0 : ℝ)..t, 2 / (V r - W r)) (2 / (V t - W t)) t :=
      intervalIntegral.integral_hasDerivAt_right (hVint t htT.1.le)
        (hg2c.stronglyMeasurableAtFilter isOpen_Ioo t ht)
        (hg2c.continuousAt (Ioo_mem_nhds ht.1 ht.2))
    have hDeq : ∀ᶠ r in 𝓝 t, D r = x + (∫ q in (0 : ℝ)..r, realDrift c (Y q)) -
        ∫ q in (0 : ℝ)..r, 2 / (V q - W q) := by
      filter_upwards [Ioi_mem_nhds htT.1] with r hr
      simp only [hDdef]
      rw [← hVeq r hr.le, ← hYeq r hr.le]
    have hD' : HasDerivAt D (realDrift c (Y t) - 2 / (V t - W t)) t :=
      ((hg1.const_add x).sub hg2).congr_of_eventuallyEq hDeq
    have hE : HasDerivAt (fun t => Real.exp (K * t)) (Real.exp (K * t) * K) t := by
      simpa using ((hasDerivAt_id t).const_mul K).exp
    refine (hD'.mul hE).congr_deriv ?_
    ring
  have hnonneg : ∀ t ∈ interior (Icc s₀ s),
      0 ≤ deriv f t := by
    intro t ht
    rw [interior_Icc] at ht
    rw [(hderiv t ht).deriv]
    have htJ := Ioo_subset_Icc_self ht
    have hYt := hYge t (hJ t htJ)
    have hRt := hJR t htJ
    have hDt : 0 < D t := hbefore t (hJ t htJ) ht.2
    have hYt0 : 0 < Y t := hc.trans_le hYt
    have hRt0 : 0 < V t - W t := (by positivity : (0 : ℝ) < c / 2).trans hRt
    rw [realDrift_of_le hYt]
    have hid : 2 / Y t - 2 / (V t - W t) + K * D t =
        D t * (K - 2 / (Y t * (V t - W t))) := by
      have hDeq : D t = Y t - (V t - W t) := by simp only [hDdef]; ring
      rw [hDeq]; field_simp; ring
    rw [hid]
    have hYR : c * (c / 2) ≤ Y t * (V t - W t) := mul_le_mul hYt hRt.le (by positivity) hYt0.le
    have hK2 : 2 / (Y t * (V t - W t)) ≤ K := by
      rw [hK, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have : 0 ≤ D t * (K - 2 / (Y t * (V t - W t))) := mul_nonneg hDt.le (by linarith)
    positivity
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc s₀ s) hfc
    (fun t ht => by rw [interior_Icc] at ht; exact (hderiv t ht).differentiableAt.differentiableWithinAt)
    hnonneg
  have hle := hmono ⟨le_rfl, hs₀s.le⟩ ⟨hs₀s.le, le_rfl⟩ hs₀s.le
  have hfs₀ : 0 < f s₀ := mul_pos (hbefore s₀ (hJ s₀ ⟨le_rfl, hs₀s.le⟩) hs₀s) (Real.exp_pos _)
  have hfs : f s ≤ 0 := by
    have h2 := hsS.2; simp only [mem_ofPred_eq] at h2
    exact mul_nonpos_of_nonpos_of_nonneg h2 (Real.exp_pos _).le
  linarith

end Path

end InteractingSLE.LP.LP2
