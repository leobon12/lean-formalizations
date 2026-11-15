/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP2Path

/-!
# LP4's right swallowing: the passive flow against a right mark (deterministic)

Packet PROVE-LP18. Specification p. 482 (proof of Proposition LP4): "The inverse real boundary map sends this passive
point to a physical real point strictly beyond the previous right swallowed extreme." No inverse boundary map is needed:
for a continuous driver `W` with `W 0 = 0` and a right mark `V` started at `0` (`V_t = ∫₀ᵗ 2/(V − W)`, `W ≤ V`, null
collision set), the centred flow `u_t(x)` of a passive point `x > 0` satisfies

  `V_t < W_t + Re u_t(x)` and `W_t + Re u_t(x) − V_t ≤ x` (`rightGap_bounds`)

(the gap `D = g_t(x) − V_t` solves `D' = 2/X − 2/R ≤ 0`, `X = g(x) − W ≥ R = V − W`). Consequences:

* `exists_not_alive_of_restart`: if the driver restarted at `T` swallows a point `y` beyond the restarted mark
  `V_T − W_T`, then the physical point `x = y − (V_T − W_T) > 0` is swallowed;
* `exists_restart_not_alive`: conversely, a physical point `x > 0` alive at `T` and swallowed later has a restarted
  image `y > V_T − W_T` that the restarted driver swallows.

The first bound is LP2's `LP2.vR_lt_of_isForwardSol`, whose proof only uses these properties of the mark; it is
restated here for every word (the two-seed paths of LP4 have a left mark as well).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.LP.LP4S

open QuantumZipper QuantumZipper.RS

section Gap

variable {W V : ℝ → ℝ}

/-- **The passive flow against a right mark.** For a continuous driver `W` (`W 0 = 0`) and a right mark `V` with
`V 0 = 0`, `W ≤ V`, `V_t = ∫₀ᵗ 2/(V − W)` and a null collision set, the centred flow `u` of a passive point
`x > 0` alive on `[0, T]` satisfies `V_t < W_t + Re u_t ≤ V_t + x` on `[0, T]`. -/
theorem rightGap_bounds (hW : Continuous W) (hW0 : W 0 = 0) (hVc : Continuous V) (hV0 : V 0 = 0)
    (hWV : ∀ s, W s ≤ V s) (hVeq : ∀ t, 0 ≤ t → V t = ∫ s in (0 : ℝ)..t, 2 / (V s - W s))
    (hVint : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s => 2 / (V s - W s)) volume 0 t)
    (hnull : volume {s : ℝ | 0 ≤ s ∧ W s = V s} = 0) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u) :
    ∀ t ∈ Icc (0 : ℝ) T, V t < W t + (u t).re ∧ W t + (u t).re - V t ≤ x := by
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
  have hD0 : D 0 = x := by
    have h := hYeq 0 le_rfl
    simp only [intervalIntegral.integral_same, add_zero] at h
    simp only [hDdef, hV0]; linarith
  have hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < D t := by
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
    have hs0 : 0 < s := by
      rcases hsS.1.1.lt_or_eq with h | h
      · exact h
      · exfalso; have h2 := hsS.2; simp only [mem_ofPred_eq] at h2; rw [← h, hD0] at h2; linarith
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
    have hnonneg : ∀ t ∈ interior (Icc s₀ s), 0 ≤ deriv f t := by
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
  intro t ht
  refine ⟨?_, ?_⟩
  · have := hpos t ht
    rw [← hY t ht]
    simp only [hDdef] at this
    linarith
  · -- `D_t = x + ∫₀ᵗ (2/Y − 2/(V − W)) ≤ x`: the integrand is `≤ 0` off the null collision set
    have h1 : Y t + W t - V t = x + ((∫ s in (0 : ℝ)..t, realDrift c (Y s)) -
        ∫ s in (0 : ℝ)..t, 2 / (V s - W s)) := by
      rw [← hVeq t ht.1, hYeq t ht.1]; ring
    have hi1 : IntervalIntegrable (fun s => realDrift c (Y s)) volume 0 t :=
      ((lipschitz_realDrift hc).continuous.comp_continuousOn
        (hYc.mono (Icc_subset_Icc le_rfl ht.2))).intervalIntegrable_of_Icc ht.1
    have hae : (fun s => realDrift c (Y s)) ≤ᵐ[volume.restrict (Icc 0 t)] fun s => 2 / (V s - W s) := by
      have hnull' : ∀ᵐ s ∂volume, s ∉ {s : ℝ | 0 ≤ s ∧ W s = V s} :=
        measure_eq_zero_iff_ae_notMem.1 hnull
      filter_upwards [ae_restrict_of_ae hnull', ae_restrict_mem measurableSet_Icc] with s hs hsI
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hsI.1, hsI.2.trans ht.2⟩
      have hWVs : W s ≠ V s := fun h => hs ⟨hsI.1, h⟩
      have hR0 : 0 < V s - W s := sub_pos.2 (lt_of_le_of_ne (hWV s) hWVs)
      have hYs := hYge s hsT
      have hDs := hpos s hsT
      simp only [hDdef] at hDs
      rw [realDrift_of_le hYs]
      exact div_le_div_of_nonneg_left zero_le_two hR0 (by linarith)
    have h2 := intervalIntegral.integral_mono_ae_restrict ht.1 hi1 (hVint t ht.1) hae
    rw [← hY t ht]
    linarith

/-- The hypotheses of `rightGap_bounds` from an integrated path whose right mark `vR j` starts at `0`, with infinite
lifetime. -/
theorem rightMark_props {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤) (j : Fin nR) (hj : xR j = 0) :
    Continuous (fun s : ℝ => w s.toNNReal) ∧ (fun s : ℝ => w s.toNNReal) 0 = 0 ∧
      Continuous (fun s : ℝ => vR j s.toNNReal) ∧ (fun s : ℝ => vR j s.toNNReal) 0 = 0 ∧
      (∀ s : ℝ, w s.toNNReal ≤ vR j s.toNNReal) ∧
      (∀ t : ℝ, 0 ≤ t → vR j t.toNNReal = ∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal)) ∧
      (∀ t : ℝ, 0 ≤ t →
        IntervalIntegrable (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) volume 0 t) ∧
      volume {s : ℝ | 0 ≤ s ∧ w s.toNNReal = vR j s.toNNReal} = 0 := by
  obtain ⟨hw0, -, hvR0, hwc, -, hvRc, -, -, hwvR, -, -, hgR, -, -, hvReq, -, hcolR, -⟩ := hp
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ⊤} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => ENNReal.coe_lt_top)
  refine ⟨(hcont hwc).comp continuous_real_toNNReal, by simp [hw0],
    (hcont (hvRc j)).comp continuous_real_toNNReal, by simp [hvR0 j, hj],
    fun s => hwvR s.toNNReal ENNReal.coe_lt_top j, fun t ht => ?_, fun t ht => ?_, ?_⟩
  · have h := hvReq t.toNNReal ENNReal.coe_lt_top j
    rwa [Real.coe_toNNReal _ ht, hj, zero_add] at h
  · have h := Zhan.intervalIntegrable_two_div_of_inv (w := w) (u := vR j)
      (hgR t.toNNReal ENNReal.coe_lt_top j)
    rwa [Real.coe_toNNReal _ ht] at h
  · refine measure_mono_null ?_ (hcolR j)
    intro s hs
    exact ⟨hs.1, ENNReal.coe_lt_top, hs.2⟩

end Gap

/-! ### Physical points and restarted points -/

section Restart

variable {W V : ℝ → ℝ}

/-- **From a restarted swallowing to a physical one.** If the driver restarted at `T` swallows by `S` a point `y`
beyond the restarted mark `V_T − W_T`, then the physical point `x = y − (V_T − W_T) > 0` is swallowed by `T + S`. -/
theorem exists_not_alive_of_restart (hW : Continuous W) (hW0 : W 0 = 0) (hVc : Continuous V) (hV0 : V 0 = 0)
    (hWV : ∀ s, W s ≤ V s) (hVeq : ∀ t, 0 ≤ t → V t = ∫ s in (0 : ℝ)..t, 2 / (V s - W s))
    (hVint : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s => 2 / (V s - W s)) volume 0 t)
    (hnull : volume {s : ℝ | 0 ≤ s ∧ W s = V s} = 0) {T S y : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hy : V T - W T < y) (hdead : ¬ LP3.Alive (fun r => W (T + r) - W T) y S) :
    ∃ x : ℝ, 0 < x ∧ ¬ LP3.Alive W x (T + S) := by
  refine ⟨y - (V T - W T), sub_pos.2 hy, ?_⟩
  by_cases hal : LP3.Alive W (y - (V T - W T)) T
  · obtain ⟨u, hu⟩ := hal
    have hb := (rightGap_bounds hW hW0 hVc hV0 hWV hVeq hVint hnull (sub_pos.2 hy) hT hu T
      ⟨hT, le_rfl⟩).2
    exact LP3.not_alive_of_restart hW hW0 (sub_pos.2 hy) hT hS hu (by linarith) hdead
  · exact fun h => hal (h.mono hT (le_add_of_nonneg_right hS))

/-- **From a physical swallowing to a restarted one.** A physical point `x > 0` alive at `T` and swallowed by
`T' ≥ T` has a restarted image `y > V_T − W_T` that the driver restarted at `T` swallows by `T' − T`. -/
theorem exists_restart_not_alive (hW : Continuous W) (hW0 : W 0 = 0) (hVc : Continuous V) (hV0 : V 0 = 0)
    (hWV : ∀ s, W s ≤ V s) (hVeq : ∀ t, 0 ≤ t → V t = ∫ s in (0 : ℝ)..t, 2 / (V s - W s))
    (hVint : ∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s => 2 / (V s - W s)) volume 0 t)
    (hnull : volume {s : ℝ | 0 ≤ s ∧ W s = V s} = 0) {x T T' : ℝ} (hx : 0 < x) (hT : 0 ≤ T)
    (hTT' : T ≤ T') (hal : LP3.Alive W x T) (hdead : ¬ LP3.Alive W x T') :
    ∃ y : ℝ, V T - W T < y ∧ ¬ LP3.Alive (fun r => W (T + r) - W T) y (T' - T) := by
  obtain ⟨u, hu⟩ := hal
  have hb := (rightGap_bounds hW hW0 hVc hV0 hWV hVeq hVint hnull hx hT hu T ⟨hT, le_rfl⟩).1
  refine ⟨(u T).re, by linarith, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨u', hu', -⟩ := LP3.exists_isForwardSol_glue hW hT (sub_nonneg.2 hTT') hu hv
  rw [add_sub_cancel] at hu'
  exact hdead ⟨u', hu'⟩

end Restart

end InteractingSLE.LP.LP4S
