import QuantumZipper.Proofs.Zipper.ZipLen2ContDefs
import QuantumZipper.Proofs.Zipper.XFlowMechDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2 continuum: the deterministic part at continuous radius

**Main result** `flowDetC_tendstoUniformlyOn`: `det^c(p, ρ) = ∫∫ Ψ_u dfc(z, ρ) dν_p(z)` converges
to `∫ Ψ_u dν_p` as `ρ → 0⁺`, uniformly on `flowBox m`. This is the continuous-radius version of
`F1.flowDetStmt_holds` (XFlowMechDet.lean), whose proof is copied with `2^{-j}` replaced by
`ρ ∈ (0, 1]`; the one input needing a continuous-radius version is the uniform circle smoothing
`RegUnif.tendstoUniformlyOn_integral_fc_comp` (UnifUCIdDetB.lean), re-proved here as
`zl2c_integral_fc_comp` by the same argument.

Sources: none — **own elementary argument** (dominated convergence bookkeeping, as in D33
UnifUCIdDetB/D and XFlowMechDet; the paper, Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1 p. 18, leaves it implicit).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

open RegCont TwoPoint B2 CoordReg CoordRegComp CircleFubini RegSample UnzipInvariance RegUnif F1

/-- **Uniform circle smoothing on a compact subset of `ℍ`, continuous radius.** Copy of
`RegUnif.tendstoUniformlyOn_integral_fc_comp` with `2^{-j}` replaced by `ρ → 0⁺`. -/
theorem zl2c_integral_fc_comp {T : ℝ} {G : ℝ → ℂ → ℝ}
    (hGc : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) (Icc 0 T ×ˢ H))
    {K : Set ℂ} (hKc : IsCompact K) (hKH : K ⊆ H) :
    ∀ ε > 0, ∃ δ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ∀ t ∈ Icc 0 T, ∀ c ∈ K,
      |(∫ v, G t v ∂foldedCircle c ρ) - G t c| ≤ ε := by
  intro ε hε
  -- `K` stays at positive distance from the real axis
  have hδ : ∃ δ > 0, ∀ c ∈ K, δ ≤ c.im := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun c hc => by rw [hemp] at hc; exact absurd hc (Set.notMem_empty c)⟩
    · obtain ⟨x₀, hx₀K, hmin⟩ := hKc.exists_isMinOn hne Complex.continuous_im.continuousOn
      have hx₀ : 0 < x₀.im := hKH hx₀K
      exact ⟨x₀.im / 2, by linarith, fun c hc => by have hcim : x₀.im ≤ c.im := hmin hc; linarith⟩
  obtain ⟨δ, hδ0, hδK⟩ := hδ
  obtain ⟨RK, hRK₀⟩ := hKc.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hRK : ∀ x ∈ K, ‖x‖ ≤ RK := fun x hx => by
    have := hRK₀ x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] at this
  set Sc : Set (ℝ × ℂ) :=
    Icc 0 T ×ˢ (Metric.closedBall (0 : ℂ) (RK + 1) ∩ {v : ℂ | δ / 2 ≤ v.im}) with hSc
  have hScc : IsCompact Sc :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const
      Complex.continuous_im))
  have hGK : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) Sc := hGc.mono fun q hq => by
    refine ⟨hq.1, ?_⟩
    show (0 : ℝ) < q.2.im
    have him : δ / 2 ≤ q.2.im := hq.2.2
    have hpos : (0 : ℝ) < δ / 2 := by positivity
    linarith [him]
  obtain ⟨η, hη0, hη⟩ := Metric.uniformContinuousOn_iff.1
    (hScc.uniformContinuousOn_of_continuous hGK) ε hε
  refine ⟨min (δ / 2) (min 1 (η / 2)), by positivity, fun ρ hρ0 hρδ t ht c hc => ?_⟩
  have hj₁ : ρ ≤ δ / 2 := (hρδ.trans_le (min_le_left _ _)).le
  have hj₂ : ρ ≤ 1 := (hρδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hj₃ : ρ ≤ η / 2 := (hρδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hδle : δ / 2 ≤ δ := by linarith
  have hrc : ρ ≤ c.im := le_trans hj₁ (le_trans hδle (hδK c hc))
  -- points of the circle of radius `ρ` around `c` stay in the compact set
  have hvS : ∀ v : ℂ, ‖v - c‖ = ρ → (t, v) ∈ Sc := fun v hvc => by
    refine ⟨ht, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hns : ‖v‖ ≤ ‖c‖ + ‖v - c‖ := by have h := norm_sub_norm_le v c; linarith
      rw [hvc] at hns
      linarith [hRK c hc, hj₂]
    · show δ / 2 ≤ v.im
      have h1 : |(v - c).im| ≤ ‖v - c‖ := Complex.abs_im_le_norm _
      have h2 : (v - c).im = v.im - c.im := by simp
      rw [h2, hvc] at h1
      have h3 := abs_le.1 h1
      linarith [hδK c hc, hj₁, h3.1]
  have hmemc : (t, c) ∈ Sc := by
    refine ⟨ht, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; linarith [hRK c hc]
    · show δ / 2 ≤ c.im
      have hcδ : δ ≤ c.im := hδK c hc
      linarith [hcδ, hδ0]
  have hvc_of : ∀ᵐ v ∂foldedCircle c (ρ), ‖v - c‖ = ρ := by
    rw [SmoothConv.foldedCircle_eq_circleUnif_sc hρ0.le hrc]
    filter_upwards [SmoothConv.ae_circleUnif_sc c (ρ)] with v hv
    rwa [abs_of_nonneg hρ0.le] at hv
  have hae : ∀ᵐ v ∂foldedCircle c (ρ), dist (G t v) (G t c) < ε := by
    filter_upwards [hvc_of] with v hvc
    have hd : dist (t, v) (t, c) < η := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm, hvc]
      linarith
    exact hη (t, v) (hvS v hvc) (t, c) hmemc hd
  -- integrability of `G t ·` against the compactly supported measure
  obtain ⟨M, hM⟩ := hScc.exists_bound_of_continuousOn hGK
  have hGt : Integrable (fun v => G t v) (foldedCircle c (ρ)) := by
    refine Integrable.of_bound ?_ M ?_
    · have hc' : ContinuousOn (fun v : ℂ => G t v) H :=
        hGc.comp (continuousOn_const.prodMk continuousOn_id)
          fun v hv => ⟨ht, hv⟩
      have := hc'.aestronglyMeasurable (μ := foldedCircle c (ρ)) isOpen_H.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem
        (foldedCircle_ae_mem_H c hρ0)] at this
    · filter_upwards [hvc_of] with v hvc
      have hb := hM (t, v) (hvS v hvc)
      rwa [Real.norm_eq_abs] at hb
  have hconst : Integrable (fun _ : ℂ => G t c) (foldedCircle c (ρ)) :=
    integrable_const (G t c)
  have hcint : (∫ v, G t c ∂foldedCircle c (ρ)) = G t c := by
    rw [integral_const, probReal_univ, one_smul]
  have hsub : (∫ v, G t v ∂foldedCircle c (ρ)) - G t c =
      ∫ v, (G t v - G t c) ∂foldedCircle c (ρ) := by
    rw [integral_sub hGt hconst, hcint]
  have key : ‖∫ v, (G t v - G t c) ∂foldedCircle c (ρ)‖ ≤ ε := by
    refine (norm_integral_le_of_norm_le_const (μ := foldedCircle c (ρ)) (C := ε) ?_).trans ?_
    · filter_upwards [hae] with v hv
      rw [Real.dist_eq] at hv
      exact hv.le
    · rw [probReal_univ, mul_one]
  rw [hsub]
  exact key

/-- **Continuous-radius deterministic node.** `det^c(p, ρ) → ∫ Ψ_u dν_p` as `ρ → 0⁺`,
uniformly on `flowBox m` (the proof of `F1.flowDetStmt_holds` with `2^{-j}` replaced by `ρ`). -/
theorem flowDetC_tendstoUniformlyOn {κ : ℝ} (hκ : 0 < κ) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (m : ℕ) :
    TendstoUniformlyOn (fun ρ p => flowDetC κ W p ρ)
      (fun p => ∫ v, RegUnif.PsiU κ W p.1 v ∂F1.flowNu W p) (𝓝[>] 0) (F1.flowBox m) := by
  set T : ℝ := 2 * ((m : ℝ) + 1) with hT
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  set Ra : ℝ := 2 * ((m : ℝ) + 1) + ((m : ℝ) + 2) with hRa
  set Rb : ℝ := revBound (2 * M) T Ra with hRb
  obtain ⟨A, hA0, hA⟩ := abs_PsiU_le hW hW0 κ T (Rb + 1)
  set B : ℝ := |2 / Real.sqrt κ| + |Qc (Real.sqrt κ)| with hBdef
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨C₀, hC₀0, hC₀⟩ := integral_abs_log_im_fc_le Rb
  set L : ℝ := max (Real.log Rb) 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  set K : ℝ := 2 * A + B * C₀ + 2 * B * L + 2 * B with hK
  have hK0 : 0 ≤ K := by positivity
  set g : ℂ → ℝ := fun w => 2 * A + B * C₀ + 2 * B * L + 2 * B * |Real.log w.im| with hg
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
  have hF : ∀ u ∈ Icc (0 : ℝ) T, ∀ z ∈ H, ‖z‖ ≤ Rb → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |∫ v, PsiU κ W u v ∂foldedCircle z ρ| ≤ A + B * (C₀ + |Real.log z.im|) := by
    intro u hu z hz hzR j hr hr1
    have hli := (TwoPoint.integrable_log_im_foldedCircle z hr).abs
    have hbd : ∀ᵐ v ∂foldedCircle z (j), ‖PsiU κ W u v‖ ≤ A + B * |Real.log v.im| := by
      filter_upwards [foldedCircle_ae_mem_H z hr, foldedCircle_ae_norm_le z hr.le] with v hv hvn
      rw [Real.norm_eq_abs]; exact hA u hu v hv (by linarith)
    have hgi : Integrable (fun v : ℂ => A + B * |Real.log v.im|) (foldedCircle z (j)) :=
      (integrable_const A).add (hli.const_mul B)
    have h1 := norm_integral_le_of_norm_le hgi hbd
    rw [integral_add (integrable_const A) (hli.const_mul B), integral_const, integral_const_mul,
      probReal_univ, one_smul, Real.norm_eq_abs] at h1
    have h2 := mul_le_mul_of_nonneg_left (hC₀ z hz hzR (j) hr hr1) hB0
    linarith
  have hGc := continuousOn_PsiU_joint hW hW0 κ T
  -- the estimate
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨τ, hτ, hτ1, hτK⟩ := xfl_exists_tau (K * (200 * ((m : ℝ) + 2))) (η := ε / 2)
    (by positivity)
  set Kc : Set ℂ := Metric.closedBall (0 : ℂ) Rb ∩ {z : ℂ | τ ≤ z.im} with hKc
  have hKcc : IsCompact Kc :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKH : Kc ⊆ H := fun z hz => lt_of_lt_of_le hτ hz.2
  obtain ⟨δ, hδ0, hJ⟩ := zl2c_integral_fc_comp hGc hKcc hKH (ε / 4) (by positivity)
  refine Filter.mem_of_superset (Ioo_mem_nhdsGT (show (0 : ℝ) < min δ 1 by positivity))
    fun j hj p hp => ?_
  have hjpos : 0 < j := hj.1
  have hjδ : j < δ := hj.2.trans_le (min_le_left _ _)
  have hj1 : j ≤ 1 := (hj.2.trans_le (min_le_right _ _)).le
  show dist (∫ v, PsiU κ W p.1 v ∂flowNu W p) (flowDetC κ W p j) < ε
  obtain ⟨hu, hs0, hus, hsT, hRa', hrm, hr0⟩ := hbox p hp
  set μ₀ := foldedCircle p.2.2.1 p.2.2.2 with hμ₀
  set Rp := revMap (vrev W (p.1 + p.2.1)) p.2.1 with hRpdef
  have hRm : Measurable Rp := TwoPoint.measurable_revMap (continuous_vrev hW _) hs0
  set Fj : ℂ → ℝ := fun z => ∫ v, PsiU κ W p.1 v ∂foldedCircle z (j) with hFj
  have hFc : Continuous Fj := continuous_integral_PsiU_fc hW hW0 hu.1 κ hjpos
  have hsrc : ∀ᵐ w ∂μ₀, w ∈ H ∧ ‖w‖ ≤ Ra := by
    filter_upwards [foldedCircle_ae_mem_H _ hr0, foldedCircle_ae_norm_le _ hr0.le] with w h1 h2
    exact ⟨h1, h2.trans hRa'⟩
  have hGA : AEStronglyMeasurable (fun v => PsiU κ W p.1 v) (μ₀.map Rp) := by
    have hc : ContinuousOn (fun v => PsiU κ W p.1 v) H :=
      hGc.comp (f := fun v : ℂ => (p.1, v)) (continuousOn_const.prodMk continuousOn_id)
        fun v hv => ⟨hu, hv⟩
    have haeH : ∀ᵐ v ∂(μ₀.map Rp), v ∈ H :=
      (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2
        (hsrc.mono fun w hw => (hRp p hp w hw.1 hw.2).1)
    have := hc.aestronglyMeasurable (μ := μ₀.map Rp) isOpen_H.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem haeH] at this
  have e1 : flowDetC κ W p j = ∫ w, Fj (Rp w) ∂μ₀ := by
    show ∫ w, Fj w ∂(μ₀.map Rp) = _
    exact integral_map hRm.aemeasurable hFc.aestronglyMeasurable
  have e2 : ∫ v, PsiU κ W p.1 v ∂flowNu W p = ∫ w, PsiU κ W p.1 (Rp w) ∂μ₀ := by
    show ∫ v, PsiU κ W p.1 v ∂(μ₀.map Rp) = _
    exact integral_map hRm.aemeasurable hGA
  have hlogint : Integrable (fun w : ℂ => |Real.log w.im|) μ₀ :=
    (TwoPoint.integrable_log_im_foldedCircle _ hr0).abs
  have hg_int : Integrable g μ₀ := (integrable_const _).add (hlogint.const_mul _)
  have hpt : ∀ w ∈ H, ‖w‖ ≤ Ra →
      |Fj (Rp w)| ≤ g w ∧ |PsiU κ W p.1 (Rp w)| ≤ g w ∧
        |Fj (Rp w) - PsiU κ W p.1 (Rp w)| ≤ g w := by
    intro w hw hwR
    obtain ⟨hzH, hwz, hzR⟩ : Rp w ∈ H ∧ w.im ≤ (Rp w).im ∧ ‖Rp w‖ ≤ Rb := hRp p hp w hw hwR
    have hl := hlogz w (Rp w) hw hwz hzR
    have b1 : |Fj (Rp w)| ≤ A + B * (C₀ + |Real.log (Rp w).im|) := hF p.1 hu (Rp w) hzH hzR j hjpos hj1
    have b2 := hA p.1 hu (Rp w) hzH (by linarith)
    have m1 := mul_le_mul_of_nonneg_left hl hB0
    have hBC : 0 ≤ B * C₀ := mul_nonneg hB0 hC₀0
    have hBL : 0 ≤ B * L := mul_nonneg hB0 hL0
    have hBl : 0 ≤ B * |Real.log w.im| := mul_nonneg hB0 (abs_nonneg _)
    have t := abs_sub (Fj (Rp w)) (PsiU κ W p.1 (Rp w))
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hg] <;> linarith
  set S : Set ℂ := {w : ℂ | w.im ≤ τ} with hS
  have hSm : MeasurableSet S := measurableSet_le Complex.measurable_im measurable_const
  set f1 : ℂ → ℝ := fun w => 1 + |Real.log w.im| with hf1
  have hf1i : Integrable f1 μ₀ := (integrable_const 1).add hlogint
  have hdom : ∀ᵐ w ∂μ₀, ‖Fj (Rp w) - PsiU κ W p.1 (Rp w)‖ ≤
      K * S.indicator f1 w + ε / 4 := by
    filter_upwards [hsrc] with w hw
    rw [Real.norm_eq_abs]
    by_cases hwτ : w.im ≤ τ
    · rw [Set.indicator_of_mem (show w ∈ S from hwτ)]
      have h3 := (hpt w hw.1 hw.2).2.2
      have hgK : g w ≤ K * f1 w := by
        simp only [hg, hf1, hK]
        nlinarith [mul_nonneg (show 0 ≤ 2 * A + B * C₀ + 2 * B * L by positivity)
          (abs_nonneg (Real.log w.im))]
      linarith
    · rw [Set.indicator_of_notMem (show w ∉ S from hwτ), mul_zero, zero_add]
      obtain ⟨hzH, hwz, hzR⟩ : Rp w ∈ H ∧ w.im ≤ (Rp w).im ∧ ‖Rp w‖ ≤ Rb :=
        hRp p hp w hw.1 hw.2
      have hzK : Rp w ∈ Kc := ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hzR,
        show τ ≤ (Rp w).im by linarith [not_le.1 hwτ]⟩
      exact hJ j hjpos hjδ p.1 hu (Rp w) hzK
  have hbi : Integrable (fun w => K * S.indicator f1 w + ε / 4) μ₀ :=
    ((hf1i.indicator hSm).const_mul K).add (integrable_const _)
  have hbound := norm_integral_le_of_norm_le hbi hdom
  have hint1 : Integrable (fun w => Fj (Rp w)) μ₀ :=
    hg_int.mono' (hFc.measurable.comp hRm).aestronglyMeasurable
      (hsrc.mono fun w hw => by rw [Real.norm_eq_abs]; exact (hpt w hw.1 hw.2).1)
  have hint2 : Integrable (fun w => PsiU κ W p.1 (Rp w)) μ₀ :=
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

end ZipLen
end B3d
end QuantumZipper
