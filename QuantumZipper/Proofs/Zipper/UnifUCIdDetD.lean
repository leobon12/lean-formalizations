import QuantumZipper.Proofs.Zipper.UnifUCIdDetB
import QuantumZipper.Proofs.GFF.CoordRegHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-DET: `DetUnifStmt` in general (circles that meet the real axis)

`UnifUCIdDetB.detJ_tendsto_of_compact` needs the pushed measures `alphaUS W d k p` to live in a
fixed compact subset of `ℍ`; this fails when the dyadic circle `fc(d, 2^{-k})` meets `ℝ`. Here
`RegUnif.DetUnifStmt κ T` is proved for every `d, k` by a strip split in the *source* variable
`w ~ fc(d, 2^{-k})`, with `z = R_{u,s}(w)`:

* `abs_PsiU_le`: `|PsiU κ W u v| ≤ A + B |log Im v|` on `[0,T] × (ℍ ∩ {‖v‖ ≤ R})`
  (`fwdMapInv_mem_H_bound`, `im_le_im_revMap`, `TwoPoint.abs_log_norm_deriv_revMap_le`);
* the smoothed values obey the same bound (`CoordReg.integral_abs_log_im_fc_le`), and
  `Im R_{u,s}(w) ≥ Im w`, `‖R_{u,s}(w)‖ ≤ revBound` give an integrable dominating function
  `2A + B C₀ + 2BL + 2B |log Im w|` for `fc(d, 2^{-k})`, uniform in `p ∈ tri T`;
* on `{Im w ≥ τ}` the points `z` lie in the compact set `closedBall 0 Rb ∩ {Im ≥ τ} ⊆ ℍ`, where the
  circle smoothing converges uniformly (`tendstoUniformlyOn_integral_fc_comp`);
* the strip `{Im w < τ}` has small dominated mass (`tendsto_setIntegral_of_antitone`, the folded
  circle does not charge `ℝ`).

Sources: none — **own elementary argument** (dominated convergence bookkeeping; the paper,
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 p. 18, leaves it implicit).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint B2 CoordReg CircleFubini RegSample UnzipInvariance

/-- **Logarithmic bound for `PsiU`, uniform in `u ∈ [0, T]`.** -/
theorem abs_PsiU_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (κ T R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ Icc (0 : ℝ) T, ∀ v ∈ H, ‖v‖ ≤ R →
      |PsiU κ W u v| ≤ A + (|2 / Real.sqrt κ| + |Qc (Real.sqrt κ)|) * |Real.log v.im| := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set B1 := max (revBound (2 * M) T R) 1 with hB1
  set R' := max R 1 with hR'
  set B2 := Real.log (Real.sqrt (R' ^ 2 + 4 * max T 0)) with hB2
  have hB1one : 1 ≤ B1 := le_max_right _ _
  have hlB1 : 0 ≤ Real.log B1 := Real.log_nonneg hB1one
  refine ⟨|2 / Real.sqrt κ| * Real.log B1 + |Qc (Real.sqrt κ)| * |B2|,
    add_nonneg (mul_nonneg (abs_nonneg _) hlB1) (mul_nonneg (abs_nonneg _) (abs_nonneg _)),
    fun u hu v hv hvR => ?_⟩
  have hv0 : 0 < v.im := hv
  have hVc : Continuous fun s => W (u - s) - W u :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  obtain ⟨_, hψB⟩ := fwdMapInv_mem_H_bound hW hW0 hM hu.1 hu.2 hv hvR
  have him : v.im ≤ ‖fwdMapInv W u v‖ := by
    rw [fwdMapInv_eq_revMap_timeRev W hW hW0 hu.1 hv]
    exact (im_le_im_revMap _ hVc v hv hu.1).trans (Complex.im_le_norm _)
  have h1 : |Real.log ‖fwdMapInv W u v‖| ≤ Real.log B1 + |Real.log v.im| := by
    have a1 := Real.log_le_log hv0 him
    have a2 := Real.log_le_log (hv0.trans_le him)
      (show ‖fwdMapInv W u v‖ ≤ B1 from hψB.trans (le_max_left _ _))
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [neg_abs_le (Real.log v.im)]
    · linarith [abs_nonneg (Real.log v.im)]
  have h2 : |Real.log ‖deriv (fwdMapInv W u) v‖| ≤ |B2| + |Real.log v.im| := by
    rw [deriv_fwdMapInv_eq hW hW0 hu.1 hv]
    have hb := abs_log_norm_deriv_revMap_le (continuous_vRev hW u) hu.1 hv (R := R')
      ((Complex.im_le_norm v).trans (hvR.trans (le_max_left _ _)))
    have hR'1 : 1 ≤ R' := le_max_right _ _
    have hlo : 1 ≤ Real.sqrt (R' ^ 2 + 4 * u) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by nlinarith [hu.1])
    have hhi : Real.sqrt (R' ^ 2 + 4 * u) ≤ Real.sqrt (R' ^ 2 + 4 * max T 0) :=
      Real.sqrt_le_sqrt (by linarith [hu.2, le_max_left T 0])
    have e1 : |Real.log (Real.sqrt (R' ^ 2 + 4 * u))| ≤ |B2| := by
      rw [abs_of_nonneg (Real.log_nonneg hlo)]
      exact (Real.log_le_log (by linarith) hhi).trans (le_abs_self _)
    linarith
  have e : PsiU κ W u v = 2 / Real.sqrt κ * Real.log ‖fwdMapInv W u v‖ +
      Qc (Real.sqrt κ) * Real.log ‖deriv (fwdMapInv W u) v‖ := rfl
  rw [e]
  have t := abs_add_le (2 / Real.sqrt κ * Real.log ‖fwdMapInv W u v‖)
    (Qc (Real.sqrt κ) * Real.log ‖deriv (fwdMapInv W u) v‖)
  rw [abs_mul, abs_mul] at t
  have m1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (2 / Real.sqrt κ))
  have m2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg (Qc (Real.sqrt κ)))
  calc _ ≤ _ := t
    _ ≤ |2 / Real.sqrt κ| * (Real.log B1 + |Real.log v.im|) +
        |Qc (Real.sqrt κ)| * (|B2| + |Real.log v.im|) := by linarith
    _ = _ := by ring

/-- The circle smoothing of `PsiU κ W u` at a fixed positive radius is continuous in the
centre. -/
theorem continuous_integral_PsiU_fc {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {u : ℝ}
    (hu : 0 ≤ u) (κ : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous fun z => ∫ v, PsiU κ W u v ∂foldedCircle z r := by
  set V : ℝ → ℝ := fun s => W (u - s) - W u with hVdef
  have hV : Continuous V := (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hVeq : ∀ z ∈ H, fwdMapInv W u z = revMap V u z := eqOn_fwdMapInv hW hW0 hu
  have hL1 : LogBounded (fun v : ℂ => Real.log ‖revMap V u v‖) :=
    logBounded_log_norm_revMap (W := V) (T := u) hV hu
  have hL3 : LogBounded (fun v : ℂ => Real.log ‖deriv (revMap V u) v‖) :=
    logBounded_log_norm_deriv_revMap (W := V) (T := u) hV hu
  have hc : Continuous fun z : ℂ =>
      (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V u v‖ ∂foldedCircle z r) +
        Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V u) v‖ ∂foldedCircle z r) :=
    (continuous_const.mul (hL1.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => hr))).add
    (continuous_const.mul (hL3.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => hr)))
  refine hc.congr fun z => ?_
  show (2 / Real.sqrt κ) * (∫ v, Real.log ‖revMap V u v‖ ∂foldedCircle z r) +
      Qc (Real.sqrt κ) * (∫ v, Real.log ‖deriv (revMap V u) v‖ ∂foldedCircle z r) = _
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hL1.integrable z hr).const_mul (2 / Real.sqrt κ))
      ((hL3.integrable z hr).const_mul (Qc (Real.sqrt κ)))]
  exact integral_congr_ae ((foldedCircle_ae_mem_H z hr).mono fun v hv => by
    have h2 : fwdMapInv W u v = revMap V u v := hVeq v hv
    have h3 : deriv (fwdMapInv W u) v = deriv (revMap V u) v :=
      Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hv) hVeq)
    simp only [PsiU, h0rev, h2, h3])

/-- **UNIF-RC3-DET: the deterministic parts converge uniformly on `tri T`.** -/
theorem detUnifStmt_holds (κ T : ℝ) : DetUnifStmt κ T := by
  intro W hW hW0 d k
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set μ₀ := foldedCircle d (radius k) with hμ₀
  set Ra : ℝ := ‖d‖ + radius k with hRa
  set Rb : ℝ := revBound (2 * M) T Ra with hRb
  obtain ⟨A, hA0, hA⟩ := abs_PsiU_le hW hW0 κ T (Rb + 1)
  set B : ℝ := |2 / Real.sqrt κ| + |Qc (Real.sqrt κ)| with hBdef
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨C₀, hC₀0, hC₀⟩ := integral_abs_log_im_fc_le Rb
  set L : ℝ := max (Real.log Rb) 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  set g : ℂ → ℝ := fun w => 2 * A + B * C₀ + 2 * B * L + 2 * B * |Real.log w.im| with hg
  have hlogint : Integrable (fun w : ℂ => |Real.log w.im|) μ₀ :=
    (TwoPoint.integrable_log_im_foldedCircle d (radius_pos k)).abs
  have hg_int : Integrable g μ₀ := (integrable_const _).add (hlogint.const_mul _)
  -- geometry of `R_p`
  have hRp : ∀ p ∈ tri T, ∀ w ∈ H, ‖w‖ ≤ Ra →
      revMap (vrev W (p.1 + p.2)) p.2 w ∈ H ∧ w.im ≤ (revMap (vrev W (p.1 + p.2)) p.2 w).im ∧
        ‖revMap (vrev W (p.1 + p.2)) p.2 w‖ ≤ Rb := by
    intro p hp w hw hwR
    have hVc := continuous_vrev hW (p.1 + p.2)
    refine ⟨im_revMap_pos hVc hw hp.2.1, im_le_im_revMap _ hVc w hw hp.2.1, ?_⟩
    exact (norm_revMap_le_revBound hVc hp.2.1
      (fun x _ => abs_vrev_le hM ⟨add_nonneg hp.1 hp.2.1, hp.2.2⟩ x) Ra hwR).trans
      (revBound_mono (by linarith [hp.1, hp.2.2]))
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
      |∫ v, PsiU κ W u v ∂foldedCircle z (radius j)| ≤ A + B * (C₀ + |Real.log z.im|) := by
    intro u hu z hz hzR j
    have hr := radius_pos j
    have hr1 : radius j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hli := (TwoPoint.integrable_log_im_foldedCircle z hr).abs
    have hbd : ∀ᵐ v ∂foldedCircle z (radius j), ‖PsiU κ W u v‖ ≤ A + B * |Real.log v.im| := by
      filter_upwards [foldedCircle_ae_mem_H z hr, foldedCircle_ae_norm_le z hr.le] with v hv hvn
      rw [Real.norm_eq_abs]; exact hA u hu v hv (by linarith)
    have hgi : Integrable (fun v : ℂ => A + B * |Real.log v.im|) (foldedCircle z (radius j)) :=
      (integrable_const A).add (hli.const_mul B)
    have h1 := norm_integral_le_of_norm_le hgi hbd
    rw [integral_add (integrable_const A) (hli.const_mul B), integral_const, integral_const_mul,
      probReal_univ, one_smul, Real.norm_eq_abs] at h1
    have h2 := mul_le_mul_of_nonneg_left (hC₀ z hz hzR (radius j) hr hr1) hB0
    linarith
  -- small dominated mass near the real axis
  have hstrip : ∀ η > 0, ∃ τ > 0, ∫ w in {w : ℂ | w.im < τ}, g w ∂μ₀ < η := by
    intro η hη
    set s : ℕ → Set ℂ := fun n => {w : ℂ | w.im < 1 / ((n : ℝ) + 1)} with hs
    have hsm : ∀ n, MeasurableSet (s n) := fun n =>
      measurableSet_lt Complex.measurable_im measurable_const
    have hanti : Antitone s := by
      intro m n hmn w hw
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      exact lt_of_lt_of_le hw hle
    have hlim := tendsto_setIntegral_of_antitone (μ := μ₀) (f := g) hsm hanti
      ⟨0, hg_int.integrableOn⟩
    have hInter : μ₀ (⋂ n, s n) = 0 := by
      refine measure_mono_null (fun w hw => ?_) (ae_iff.1 (foldedCircle_ae_mem_H d (radius_pos k)))
      show ¬ w ∈ H
      intro hwH
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < w.im from hwH)
      have := Set.mem_iInter.1 hw n
      exact absurd (lt_trans this hn) (lt_irrefl _)
    rw [setIntegral_measure_zero _ hInter] at hlim
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
    exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩
  -- the estimate
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨τ, hτ, hτint⟩ := hstrip (ε / 2) (by positivity)
  set K : Set ℂ := Metric.closedBall (0 : ℂ) Rb ∩ {z : ℂ | τ ≤ z.im} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKH : K ⊆ H := fun z hz => lt_of_lt_of_le hτ hz.2
  obtain ⟨J, hJ⟩ := tendstoUniformlyOn_integral_fc_comp (continuousOn_PsiU_joint hW hW0 κ T)
    hKc hKH (ε / 4) (by positivity)
  refine eventually_atTop.2 ⟨J, fun j hj p hp => ?_⟩
  have hu : p.1 ∈ Icc (0 : ℝ) T := ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩
  set Rp := revMap (vrev W (p.1 + p.2)) p.2 with hRpdef
  have hRm : Measurable Rp := TwoPoint.measurable_revMap (continuous_vrev hW _) hp.2.1
  set Fj : ℂ → ℝ := fun z => ∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j) with hFj
  have hFc : Continuous Fj := continuous_integral_PsiU_fc hW hW0 hp.1 κ (radius_pos j)
  obtain ⟨_, _, _, haeH⟩ := alphaUS_ae_mem hW T d k hp
  have hPsiA : AEStronglyMeasurable (fun v => PsiU κ W p.1 v) (alphaUS W d k p) := by
    have hc : ContinuousOn (fun v : ℂ => PsiU κ W p.1 v) H :=
      (continuousOn_PsiU_joint hW hW0 κ T).comp (f := fun v : ℂ => (p.1, v))
        (continuousOn_const.prodMk continuousOn_id) fun v hv => ⟨hu, hv⟩
    have := hc.aestronglyMeasurable (μ := alphaUS W d k p) isOpen_H.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem haeH] at this
  have hPsiM : AEStronglyMeasurable (fun v => PsiU κ W p.1 v) (μ₀.map Rp) := hPsiA
  have e1 : detJ κ W d k p j = ∫ w, Fj (Rp w) ∂μ₀ := by
    unfold detJ alphaUS
    exact integral_map hRm.aemeasurable hFc.aestronglyMeasurable
  have e2 : ∫ v, PsiU κ W p.1 v ∂alphaUS W d k p = ∫ w, PsiU κ W p.1 (Rp w) ∂μ₀ :=
    integral_map hRm.aemeasurable hPsiM
  -- pointwise bounds in the source variable
  have hsrc : ∀ᵐ w ∂μ₀, w ∈ H ∧ ‖w‖ ≤ Ra := by
    filter_upwards [foldedCircle_ae_mem_H d (radius_pos k),
      foldedCircle_ae_norm_le d (radius_pos k).le] with w h1 h2
    exact ⟨h1, h2⟩
  have hpt : ∀ w ∈ H, ‖w‖ ≤ Ra →
      |Fj (Rp w)| ≤ g w ∧ |PsiU κ W p.1 (Rp w)| ≤ g w ∧
        |Fj (Rp w) - PsiU κ W p.1 (Rp w)| ≤ g w := by
    intro w hw hwR
    obtain ⟨hzH, hwz, hzR⟩ := hRp p hp w hw hwR
    have hl := hlogz w (Rp w) hw hwz hzR
    have b1 := hF p.1 hu (Rp w) hzH hzR j
    have b2 := hA p.1 hu (Rp w) hzH (by linarith)
    have m1 := mul_le_mul_of_nonneg_left hl hB0
    have hBC : 0 ≤ B * C₀ := mul_nonneg hB0 hC₀0
    have hBL : 0 ≤ B * L := mul_nonneg hB0 hL0
    have hBl : 0 ≤ B * |Real.log w.im| := mul_nonneg hB0 (abs_nonneg _)
    have t := abs_sub (Fj (Rp w)) (PsiU κ W p.1 (Rp w))
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hg] <;> linarith
  have hint1 : Integrable (fun w => Fj (Rp w)) μ₀ :=
    hg_int.mono' (hFc.measurable.comp hRm).aestronglyMeasurable
      (hsrc.mono fun w hw => by rw [Real.norm_eq_abs]; exact (hpt w hw.1 hw.2).1)
  have hint2 : Integrable (fun w => PsiU κ W p.1 (Rp w)) μ₀ :=
    hg_int.mono' (hPsiM.comp_aemeasurable hRm.aemeasurable)
      (hsrc.mono fun w hw => by rw [Real.norm_eq_abs]; exact (hpt w hw.1 hw.2).2.1)
  set S : Set ℂ := {w : ℂ | w.im < τ} with hS
  have hSm : MeasurableSet S := measurableSet_lt Complex.measurable_im measurable_const
  have hdom : ∀ᵐ w ∂μ₀, ‖Fj (Rp w) - PsiU κ W p.1 (Rp w)‖ ≤ S.indicator g w + ε / 4 := by
    filter_upwards [hsrc] with w hw
    rw [Real.norm_eq_abs]
    by_cases hwτ : w.im < τ
    · rw [Set.indicator_of_mem (show w ∈ S from hwτ)]
      linarith [(hpt w hw.1 hw.2).2.2]
    · rw [Set.indicator_of_notMem (show w ∉ S from hwτ), zero_add]
      obtain ⟨hzH, hwz, hzR⟩ := hRp p hp w hw.1 hw.2
      have hzK : Rp w ∈ K := ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hzR,
        show τ ≤ (Rp w).im by linarith [not_lt.1 hwτ]⟩
      exact hJ j hj p.1 hu (Rp w) hzK
  have hbi : Integrable (fun w => S.indicator g w + ε / 4) μ₀ :=
    (hg_int.indicator hSm).add (integrable_const _)
  have hbound := norm_integral_le_of_norm_le hbi hdom
  rw [integral_add (hg_int.indicator hSm) (integrable_const _), integral_indicator hSm,
    integral_const, probReal_univ, one_smul, integral_sub hint1 hint2, ← e1, ← e2,
    Real.norm_eq_abs] at hbound
  rw [Real.dist_eq, abs_sub_comm]
  linarith

end RegUnif
end QuantumZipper
