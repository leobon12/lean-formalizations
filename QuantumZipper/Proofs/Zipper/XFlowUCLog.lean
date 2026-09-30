import QuantumZipper.Proofs.Zipper.XFlowUCDefs
import QuantumZipper.Proofs.Zipper.UnifUCIdDetD
import QuantumZipper.Proofs.GFF.CoordRegCompBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-UC-LOG: the deterministic log node `XFlowLogUCStmt`

`L_j(p) = ∫∫ log|f_u⁻¹| dfc(w, 2^{-j}) dν_p(w)` converges to `∫ log|f_u⁻¹| dν_p` uniformly on
every box `flowBox m`, `ν_p = (R_{u,s})_* fc(d, r)`. The proof follows
`RegUnif.detUnifStmt_holds` (UnifUCIdDetD.lean): a strip split in the source variable
`w ~ fc(d, r)`, `z = R_{u,s}(w)`:

* `|log|f_u⁻¹ v|| ≤ A + |log Im v|` on `[0,T] × (ℍ ∩ {‖v‖ ≤ R})`
  (`xfl_abs_log_fwdMapInv_le`), and the same bound for the smoothed values
  (`CoordReg.integral_abs_log_im_fc_le`);
* `Im R_{u,s} w ≥ Im w`, `‖R_{u,s} w‖ ≤ revBound` give the dominating function
  `g = 2A + C₀ + 2L + 2|log Im w| ≤ K (1 + |log Im w|)`;
* on `{Im w > τ}` the smoothing converges uniformly (`tendstoUniformlyOn_integral_fc_comp`);
* the new ingredient: the strip `{Im w ≤ τ}` has dominated mass `≤ K · 200 (m+2) τ^{1/4}`,
  uniformly over the box (`CoordRegComp.stripBound_foldedCircle` with `r ≥ 1/(m+2)`,
  `xfl_strip`).

Sources: none — **own elementary argument** (dominated convergence bookkeeping, as in
UnifUCIdDetD; the paper, Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 p. 18,
leaves it implicit).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint B2 CoordReg CoordRegComp CircleFubini RegSample UnzipInvariance RegUnif

/-- Logarithmic bound for `log|f_u⁻¹|`, uniform in `u ∈ [0, T]`. -/
theorem xfl_abs_log_fwdMapInv_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (T R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ Icc (0 : ℝ) T, ∀ v ∈ H, ‖v‖ ≤ R →
      |Real.log ‖fwdMapInv W u v‖| ≤ A + |Real.log v.im| := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set B1 := max (revBound (2 * M) T R) 1 with hB1
  have hlB1 : 0 ≤ Real.log B1 := Real.log_nonneg (le_max_right _ _)
  refine ⟨Real.log B1, hlB1, fun u hu v hv hvR => ?_⟩
  have hv0 : 0 < v.im := hv
  obtain ⟨_, hψB⟩ := fwdMapInv_mem_H_bound hW hW0 hM hu.1 hu.2 hv hvR
  have him : v.im ≤ ‖fwdMapInv W u v‖ := by
    rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hu.1 hv]
    exact (im_le_im_revMap _ (continuous_vRev hW u) v hv hu.1).trans (Complex.im_le_norm _)
  have a1 := Real.log_le_log hv0 him
  have a2 := Real.log_le_log (hv0.trans_le him)
    (show ‖fwdMapInv W u v‖ ≤ B1 from hψB.trans (le_max_left _ _))
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [neg_abs_le (Real.log v.im)]
  · linarith [abs_nonneg (Real.log v.im)]

/-- **Uniform strip bound** for the folded circles of the box: radius `r ≥ 1/(m+2)`. -/
theorem xfl_strip (m : ℕ) (d : ℂ) {r : ℝ} (hr : 1 / ((m : ℝ) + 2) ≤ r) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) :
    ∫ z, {z : ℂ | z.im ≤ τ}.indicator (fun z => 1 + |Real.log z.im|) z ∂foldedCircle d r
      ≤ 200 * ((m : ℝ) + 2) * τ ^ (1 / 4 : ℝ) := by
  have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hm1 : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le hm1 hr
  have h1 := stripBound_foldedCircle d hr0 τ hτ hτ1
  have hs : 1 / ((m : ℝ) + 2) ≤ Real.sqrt r := by
    have hsq : (1 / ((m : ℝ) + 2)) ^ 2 ≤ 1 / ((m : ℝ) + 2) := by
      rw [sq]
      exact mul_le_of_le_one_left hm1.le (by rw [div_le_one hm]; linarith)
    have := Real.abs_le_sqrt (x := 1 / ((m : ℝ) + 2)) (y := r) (hsq.trans hr)
    rwa [abs_of_pos hm1] at this
  have h2 : 200 / Real.sqrt r ≤ 200 * ((m : ℝ) + 2) := by
    rw [div_le_iff₀ (lt_of_lt_of_le hm1 hs)]
    calc (200 : ℝ) = 200 * ((m : ℝ) + 2) * (1 / ((m : ℝ) + 2)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))

/-- Choice of the strip width. -/
theorem xfl_exists_tau (K : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ K * τ ^ (1 / 4 : ℝ) < η := by
  have hc : Tendsto (fun τ : ℝ => K * τ ^ (1 / 4 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (1 / 4) (Or.inr (by norm_num))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))).const_mul K
    rwa [Real.zero_rpow (by norm_num), mul_zero] at this
  obtain ⟨τ, h1, h2⟩ :=
    ((hc.eventually (gt_mem_nhds hη)).and (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  exact ⟨τ, h2.1, h2.2, h1⟩

/-- **XFLOW-UC-LOG: the deterministic log node.** -/
theorem xFlowLogUCStmt_holds : XFlowLogUCStmt := by
  intro W hW hW0 m
  set T : ℝ := 2 * ((m : ℝ) + 1) with hT
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set Ra : ℝ := 2 * ((m : ℝ) + 1) + ((m : ℝ) + 2) with hRa
  set Rb : ℝ := revBound (2 * M) T Ra with hRb
  obtain ⟨A, hA0, hA⟩ := xfl_abs_log_fwdMapInv_le hW hW0 T (Rb + 1)
  obtain ⟨C₀, hC₀0, hC₀⟩ := integral_abs_log_im_fc_le Rb
  set L : ℝ := max (Real.log Rb) 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  set K : ℝ := 2 * A + C₀ + 2 * L + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set g : ℂ → ℝ := fun w => 2 * A + C₀ + 2 * L + 2 * |Real.log w.im| with hg
  -- box facts
  have hbox : ∀ p ∈ flowBox m, p.1 ∈ Icc (0 : ℝ) T ∧ 0 ≤ p.2.1 ∧ p.1 + p.2.1 ∈ Icc (0 : ℝ) T ∧
      p.2.1 ≤ T ∧ ‖p.2.2.1‖ + p.2.2.2 ≤ Ra ∧ 1 / ((m : ℝ) + 2) ≤ p.2.2.2 ∧ 0 < p.2.2.2 := by
    rintro p ⟨hu, hs, hre, him, hr⟩
    have hn := Complex.norm_le_abs_re_add_abs_im p.2.2.1
    have h1 : |p.2.2.1.re| ≤ (m : ℝ) + 1 := abs_le.2 ⟨hre.1, hre.2⟩
    have h2 : |p.2.2.1.im| ≤ (m : ℝ) + 1 := abs_le.2 ⟨by linarith [him.1], him.2⟩
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    refine ⟨⟨hu.1, by linarith [hu.2]⟩, hs.1, ⟨by linarith [hu.1, hs.1], by linarith [hu.2, hs.2]⟩,
      by linarith [hs.2], by linarith [hr.2], hr.1, lt_of_lt_of_le (by positivity) hr.1⟩
  -- geometry of `R_p`
  have hRp : ∀ p ∈ flowBox m, ∀ w ∈ H, ‖w‖ ≤ Ra →
      revMap (vrev W (p.1 + p.2.1)) p.2.1 w ∈ H ∧
        w.im ≤ (revMap (vrev W (p.1 + p.2.1)) p.2.1 w).im ∧
        ‖revMap (vrev W (p.1 + p.2.1)) p.2.1 w‖ ≤ Rb := by
    intro p hp w hw hwR
    obtain ⟨_, hs0, hus, hsT, _, _, _⟩ := hbox p hp
    have hVc := continuous_vrev hW (p.1 + p.2.1)
    refine ⟨im_revMap_pos hVc hw hs0, im_le_im_revMap _ hVc w hw hs0, ?_⟩
    exact (norm_revMap_le_revBound hVc hs0 (fun x _ => abs_vrev_le hM hus x) Ra hwR).trans
      (revBound_mono hsT)
  have hlogz : ∀ w z : ℂ, 0 < w.im → w.im ≤ z.im → ‖z‖ ≤ Rb →
      |Real.log z.im| ≤ |Real.log w.im| + L := by
    intro w z hw hwz hz
    have hz0 : 0 < z.im := hw.trans_le hwz
    have a1 := Real.log_le_log hw hwz
    have a2 := Real.log_le_log hz0 ((Complex.im_le_norm z).trans hz)
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [neg_abs_le (Real.log w.im)]
    · linarith [le_max_left (Real.log Rb) 0, abs_nonneg (Real.log w.im)]
  -- the smoothed values obey the logarithmic bound
  have hF : ∀ u ∈ Icc (0 : ℝ) T, ∀ z ∈ H, ‖z‖ ≤ Rb → ∀ j : ℕ,
      |∫ v, Real.log ‖fwdMapInv W u v‖ ∂foldedCircle z (radius j)| ≤
        A + (C₀ + |Real.log z.im|) := by
    intro u hu z hz hzR j
    have hr := radius_pos j
    have hr1 : radius j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hli := (TwoPoint.integrable_log_im_foldedCircle z hr).abs
    have hbd : ∀ᵐ v ∂foldedCircle z (radius j),
        ‖Real.log ‖fwdMapInv W u v‖‖ ≤ A + |Real.log v.im| := by
      filter_upwards [foldedCircle_ae_mem_H z hr, foldedCircle_ae_norm_le z hr.le] with v hv hvn
      rw [Real.norm_eq_abs]; exact hA u hu v hv (by linarith)
    have hgi : Integrable (fun v : ℂ => A + |Real.log v.im|) (foldedCircle z (radius j)) :=
      (integrable_const A).add hli
    have h1 := norm_integral_le_of_norm_le hgi hbd
    rw [integral_add (integrable_const A) hli, integral_const, probReal_univ, one_smul,
      Real.norm_eq_abs] at h1
    have h2 := hC₀ z hz hzR (radius j) hr hr1
    linarith
  -- joint continuity of the integrand
  have hGc : ContinuousOn (fun q : ℝ × ℂ => Real.log ‖fwdMapInv W q.1 q.2‖) (Icc 0 T ×ˢ H) :=
    (continuousOn_fwdMapInv_joint hW hW0 T).norm.log fun q hq => by
      have h0 : 0 < (fwdMapInv W q.1 q.2).im :=
        (fwdMapInv_mem_H_bound hW hW0 hM hq.1.1 hq.1.2 hq.2 le_rfl).1
      exact norm_ne_zero_iff.2 fun h => by rw [h, Complex.zero_im] at h0; exact lt_irrefl _ h0
  -- the estimate
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨τ, hτ, hτ1, hτK⟩ := xfl_exists_tau (K * (200 * ((m : ℝ) + 2))) (η := ε / 2)
    (by positivity)
  set Kc : Set ℂ := Metric.closedBall (0 : ℂ) Rb ∩ {z : ℂ | τ ≤ z.im} with hKc
  have hKcc : IsCompact Kc :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKH : Kc ⊆ H := fun z hz => lt_of_lt_of_le hτ hz.2
  obtain ⟨J, hJ⟩ := tendstoUniformlyOn_integral_fc_comp (T := T)
    (G := fun t v => Real.log ‖fwdMapInv W t v‖) hGc hKcc hKH (ε / 4) (by positivity)
  refine eventually_atTop.2 ⟨J, fun j hj p hp => ?_⟩
  show dist (∫ w, Real.log ‖fwdMapInv W p.1 w‖ ∂flowNu W p) (flowLogJ W j p) < ε
  obtain ⟨hu, hs0, hus, hsT, hRa', hrm, hr0⟩ := hbox p hp
  set μ₀ := foldedCircle p.2.2.1 p.2.2.2 with hμ₀
  set Rp := revMap (vrev W (p.1 + p.2.1)) p.2.1 with hRpdef
  have hRm : Measurable Rp := TwoPoint.measurable_revMap (continuous_vrev hW _) hs0
  set Fj : ℂ → ℝ := fun z => ∫ v, Real.log ‖fwdMapInv W p.1 v‖ ∂foldedCircle z (radius j)
    with hFj
  have hFc : Continuous Fj :=
    (continuousOn_integral_log_fwdMapInv_joint hW hW0 hT0).comp_continuous
      (continuous_const.prodMk (continuous_id.prodMk continuous_const) :
        Continuous fun z : ℂ => (p.1, (z, radius j)))
      (fun z => ⟨hu, radius_pos j⟩)
  have hsrc : ∀ᵐ w ∂μ₀, w ∈ H ∧ ‖w‖ ≤ Ra := by
    filter_upwards [foldedCircle_ae_mem_H _ hr0, foldedCircle_ae_norm_le _ hr0.le] with w h1 h2
    exact ⟨h1, h2.trans hRa'⟩
  have hGA : AEStronglyMeasurable (fun v => Real.log ‖fwdMapInv W p.1 v‖) (μ₀.map Rp) := by
    have hc : ContinuousOn (fun v => Real.log ‖fwdMapInv W p.1 v‖) H :=
      hGc.comp (f := fun v : ℂ => (p.1, v)) (continuousOn_const.prodMk continuousOn_id)
        fun v hv => ⟨hu, hv⟩
    have haeH : ∀ᵐ v ∂(μ₀.map Rp), v ∈ H :=
      (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2
        (hsrc.mono fun w hw => (hRp p hp w hw.1 hw.2).1)
    have := hc.aestronglyMeasurable (μ := μ₀.map Rp) isOpen_H.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem haeH] at this
  have e1 : flowLogJ W j p = ∫ w, Fj (Rp w) ∂μ₀ := by
    show ∫ w, Fj w ∂(μ₀.map Rp) = _
    exact integral_map hRm.aemeasurable hFc.aestronglyMeasurable
  have e2 : ∫ w, Real.log ‖fwdMapInv W p.1 w‖ ∂flowNu W p =
      ∫ w, Real.log ‖fwdMapInv W p.1 (Rp w)‖ ∂μ₀ := by
    show ∫ w, Real.log ‖fwdMapInv W p.1 w‖ ∂(μ₀.map Rp) = _
    exact integral_map hRm.aemeasurable hGA
  have hlogint : Integrable (fun w : ℂ => |Real.log w.im|) μ₀ :=
    (TwoPoint.integrable_log_im_foldedCircle _ hr0).abs
  have hg_int : Integrable g μ₀ := (integrable_const _).add (hlogint.const_mul _)
  have hpt : ∀ w ∈ H, ‖w‖ ≤ Ra →
      |Fj (Rp w)| ≤ g w ∧ |Real.log ‖fwdMapInv W p.1 (Rp w)‖| ≤ g w ∧
        |Fj (Rp w) - Real.log ‖fwdMapInv W p.1 (Rp w)‖| ≤ g w := by
    intro w hw hwR
    obtain ⟨hzH, hwz, hzR⟩ : Rp w ∈ H ∧ w.im ≤ (Rp w).im ∧ ‖Rp w‖ ≤ Rb := hRp p hp w hw hwR
    have hl := hlogz w (Rp w) hw hwz hzR
    have b1 : |Fj (Rp w)| ≤ A + (C₀ + |Real.log (Rp w).im|) := hF p.1 hu (Rp w) hzH hzR j
    have b2 := hA p.1 hu (Rp w) hzH (by linarith)
    have hl0 := abs_nonneg (Real.log w.im)
    have t := abs_sub (Fj (Rp w)) (Real.log ‖fwdMapInv W p.1 (Rp w)‖)
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hg] <;> linarith
  set S : Set ℂ := {w : ℂ | w.im ≤ τ} with hS
  have hSm : MeasurableSet S := measurableSet_le Complex.measurable_im measurable_const
  set f1 : ℂ → ℝ := fun w => 1 + |Real.log w.im| with hf1
  have hf1i : Integrable f1 μ₀ := (integrable_const 1).add hlogint
  have hdom : ∀ᵐ w ∂μ₀, ‖Fj (Rp w) - Real.log ‖fwdMapInv W p.1 (Rp w)‖‖ ≤
      K * S.indicator f1 w + ε / 4 := by
    filter_upwards [hsrc] with w hw
    rw [Real.norm_eq_abs]
    by_cases hwτ : w.im ≤ τ
    · rw [Set.indicator_of_mem (show w ∈ S from hwτ)]
      have h3 := (hpt w hw.1 hw.2).2.2
      have hgK : g w ≤ K * f1 w := by
        simp only [hg, hf1, hK]
        nlinarith [mul_nonneg (show 0 ≤ 2 * A + C₀ + 2 * L by positivity)
          (abs_nonneg (Real.log w.im))]
      linarith
    · rw [Set.indicator_of_notMem (show w ∉ S from hwτ), mul_zero, zero_add]
      obtain ⟨hzH, hwz, hzR⟩ : Rp w ∈ H ∧ w.im ≤ (Rp w).im ∧ ‖Rp w‖ ≤ Rb :=
        hRp p hp w hw.1 hw.2
      have hzK : Rp w ∈ Kc := ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hzR,
        show τ ≤ (Rp w).im by linarith [not_le.1 hwτ]⟩
      exact hJ j hj p.1 hu (Rp w) hzK
  have hbi : Integrable (fun w => K * S.indicator f1 w + ε / 4) μ₀ :=
    ((hf1i.indicator hSm).const_mul K).add (integrable_const _)
  have hbound := norm_integral_le_of_norm_le hbi hdom
  have hint1 : Integrable (fun w => Fj (Rp w)) μ₀ :=
    hg_int.mono' (hFc.measurable.comp hRm).aestronglyMeasurable
      (hsrc.mono fun w hw => by rw [Real.norm_eq_abs]; exact (hpt w hw.1 hw.2).1)
  have hint2 : Integrable (fun w => Real.log ‖fwdMapInv W p.1 (Rp w)‖) μ₀ :=
    hg_int.mono' (hGA.comp_aemeasurable hRm.aemeasurable)
      (hsrc.mono fun w hw => by rw [Real.norm_eq_abs]; exact (hpt w hw.1 hw.2).2.1)
  have hstrip : ∫ w, S.indicator f1 w ∂μ₀ ≤ 200 * ((m : ℝ) + 2) * τ ^ (1 / 4 : ℝ) :=
    xfl_strip m p.2.2.1 hrm hτ hτ1
  rw [integral_add ((hf1i.indicator hSm).const_mul K) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul, integral_sub hint1 hint2, ← e1, ← e2,
    Real.norm_eq_abs] at hbound
  have hKs := mul_le_mul_of_nonneg_left hstrip hK0
  rw [Real.dist_eq, abs_sub_comm]
  have : K * (200 * ((m : ℝ) + 2) * τ ^ (1 / 4 : ℝ)) =
      K * (200 * ((m : ℝ) + 2)) * τ ^ (1 / 4 : ℝ) := by ring
  linarith

end F1
end QuantumZipper
