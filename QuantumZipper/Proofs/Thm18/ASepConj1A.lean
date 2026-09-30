import QuantumZipper.Proofs.Thm18.ASepRawC
import QuantumZipper.Proofs.Thm18.ASepWitD
import QuantumZipper.Proofs.Thm18.ASepFreeOpen
import QuantumZipper.Proofs.Thm18.G4SepUC2Ident
import QuantumZipper.Proofs.LQG.RegularClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP conjunct 1 (a): the deterministic node at a continuous radius

`tendstoUniformlyOn_integral_fc_comp_rho` and `det_unif_gen_rho` are
`RegUnif.tendstoUniformlyOn_integral_fc_comp` (UnifUCIdDetB.lean) and `G4Core.det_unif_gen`
(G4SepUC2Det.lean) with the dyadic radii `2^{-j}` replaced by all radii `ρ ∈ (0, ρ₀]`; the proofs
are the same (only the smallness of the radius is used). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg CircleFubini RegSample UnzipInvariance RegUnif
open Thm18Asm.G4Core

theorem tendstoUniformlyOn_integral_fc_comp_rho {T : ℝ} {G : ℝ → ℂ → ℝ}
    (hGc : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) (Icc 0 T ×ˢ H))
    {K : Set ℂ} (hKc : IsCompact K) (hKH : K ⊆ H) :
    ∀ ε > 0, ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ t ∈ Icc 0 T, ∀ c ∈ K,
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
  refine ⟨min (δ / 2) (min 1 (η / 2)), by positivity, fun ρ hρ hρ₀ t ht c hc => ?_⟩
  have hj₁ : ρ ≤ δ / 2 := hρ₀.trans (min_le_left _ _)
  have hj₂ : ρ ≤ 1 := hρ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hj₃ : ρ ≤ η / 2 := hρ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
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
    rw [SmoothConv.foldedCircle_eq_circleUnif_sc hρ.le hrc]
    filter_upwards [SmoothConv.ae_circleUnif_sc c (ρ)] with v hv
    rwa [abs_of_nonneg hρ.le] at hv
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
        (foldedCircle_ae_mem_H c hρ)] at this
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

theorem det_unif_gen_rho {T : ℝ} {G : ℝ → ℂ → ℝ}
    (hGc : ContinuousOn (fun q : ℝ × ℂ => G q.1 q.2) (Icc 0 T ×ˢ H))
    {A B Rb : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ t ∈ Icc (0 : ℝ) T, ∀ v ∈ H, ‖v‖ ≤ Rb + 1 → |G t v| ≤ A + B * |Real.log v.im|)
    (hFm : ∀ t ∈ Icc (0 : ℝ) T, ∀ ρ : ℝ, 0 < ρ →
      Measurable fun z => ∫ v, G t v ∂foldedCircle z ρ)
    {ι : Type*} (S : Set ι) (tp : ι → ℝ) (htp : ∀ p ∈ S, tp p ∈ Icc (0 : ℝ) T)
    (μ : ι → Measure ℂ) [∀ p, IsProbabilityMeasure (μ p)] (g : ι → ℂ → ℂ)
    (hgm : ∀ p ∈ S, Measurable (g p)) {Ra c : ℝ} (hc : 0 < c)
    (hsrc : ∀ p ∈ S, ∀ᵐ w ∂μ p, w ∈ H ∧ ‖w‖ ≤ Ra)
    (hgeo : ∀ p ∈ S, ∀ w ∈ H, ‖w‖ ≤ Ra →
      g p w ∈ H ∧ c * w.im ≤ (g p w).im ∧ ‖g p w‖ ≤ Rb)
    (hlog : ∀ p ∈ S, Integrable (fun w => |Real.log w.im|) (μ p))
    {K₁ β : ℝ} (hβ : 0 < β)
    (hstrip : ∀ p ∈ S, ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ w, {w : ℂ | w.im ≤ τ}.indicator (fun w => 1 + |Real.log w.im|) w ∂μ p ≤ K₁ * τ ^ β) :
    ∀ ε > 0, ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ p ∈ S,
      |∫ z, (∫ v, G (tp p) v ∂foldedCircle z (ρ)) ∂(μ p).map (g p) -
        ∫ z, G (tp p) z ∂(μ p).map (g p)| < ε := by
  intro ε hε
  obtain ⟨C₀, hC₀0, hC₀⟩ := integral_abs_log_im_fc_le Rb
  set L : ℝ := max (Real.log Rb) 0 with hL
  have hL0 : 0 ≤ L := le_max_right _ _
  set lc : ℝ := |Real.log c| with hlc
  have hlc0 : 0 ≤ lc := abs_nonneg _
  set K : ℝ := 2 * A + B * C₀ + 2 * B * (lc + L) + 2 * B with hK
  have hK0 : 0 ≤ K := by positivity
  set g0 : ℂ → ℝ := fun w => 2 * A + B * C₀ + 2 * B * (lc + L) + 2 * B * |Real.log w.im|
    with hg0
  have hlogz : ∀ w z : ℂ, 0 < w.im → c * w.im ≤ z.im → ‖z‖ ≤ Rb →
      |Real.log z.im| ≤ |Real.log w.im| + lc + L := by
    intro w z hw hwz hz
    have hcw : 0 < c * w.im := mul_pos hc hw
    have hz0 : 0 < z.im := hcw.trans_le hwz
    have a1 := Real.log_le_log hcw hwz
    have a2 := Real.log_le_log hz0 ((Complex.im_le_norm z).trans hz)
    rw [Real.log_mul hc.ne' hw.ne'] at a1
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [neg_abs_le (Real.log w.im), neg_abs_le (Real.log c)]
    · linarith [le_max_left (Real.log Rb) 0, abs_nonneg (Real.log w.im)]
  have hF : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ H, ‖z‖ ≤ Rb → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |∫ v, G t v ∂foldedCircle z ρ| ≤ A + B * (C₀ + |Real.log z.im|) := by
    intro t ht z hz hzR ρ hr hr1
    have hli := (TwoPoint.integrable_log_im_foldedCircle z hr).abs
    have hbd : ∀ᵐ v ∂foldedCircle z (ρ), ‖G t v‖ ≤ A + B * |Real.log v.im| := by
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H z hr,
        TwoPoint.foldedCircle_ae_norm_le z hr.le] with v hv hvn
      rw [Real.norm_eq_abs]; exact hA t ht v hv (by linarith)
    have hgi : Integrable (fun v : ℂ => A + B * |Real.log v.im|) (foldedCircle z (ρ)) :=
      (integrable_const A).add (hli.const_mul B)
    have h1 := norm_integral_le_of_norm_le hgi hbd
    rw [integral_add (integrable_const A) (hli.const_mul B), integral_const, probReal_univ,
      one_smul, integral_const_mul, Real.norm_eq_abs] at h1
    have h2 := hC₀ z hz hzR (ρ) hr hr1
    nlinarith
  obtain ⟨τ, hτ, hτ1, hτK⟩ := exists_tau_rpow (K * K₁) hβ (η := ε / 2) (by positivity)
  set Kc : Set ℂ := Metric.closedBall (0 : ℂ) Rb ∩ {z : ℂ | c * τ ≤ z.im} with hKc
  have hKcc : IsCompact Kc :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKH : Kc ⊆ H := fun z hz => lt_of_lt_of_le (mul_pos hc hτ) hz.2
  obtain ⟨ρ₁, hρ₁, hJ⟩ := tendstoUniformlyOn_integral_fc_comp_rho hGc hKcc hKH (ε / 4)
    (by positivity)
  refine ⟨min ρ₁ 1, lt_min hρ₁ one_pos, fun ρ hρ hρρ p hp => ?_⟩
  have ht := htp p hp
  set μ₀ := μ p with hμ₀
  set Rp := g p with hRpdef
  have hRm : Measurable Rp := hgm p hp
  set Fj : ℂ → ℝ := fun z => ∫ v, G (tp p) v ∂foldedCircle z (ρ) with hFj
  have hFjm : Measurable Fj := hFm _ ht ρ hρ
  have hGA : AEStronglyMeasurable (fun v => G (tp p) v) (μ₀.map Rp) := by
    have hcH : ContinuousOn (fun v => G (tp p) v) H :=
      hGc.comp (f := fun v : ℂ => (tp p, v)) (continuousOn_const.prodMk continuousOn_id)
        fun v hv => ⟨ht, hv⟩
    have haeH : ∀ᵐ v ∂(μ₀.map Rp), v ∈ H :=
      (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2
        ((hsrc p hp).mono fun w hw => (hgeo p hp w hw.1 hw.2).1)
    have := hcH.aestronglyMeasurable (μ := μ₀.map Rp) isOpen_H.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem haeH] at this
  have e1 : ∫ z, Fj z ∂(μ₀.map Rp) = ∫ w, Fj (Rp w) ∂μ₀ :=
    integral_map hRm.aemeasurable hFjm.aestronglyMeasurable
  have e2 : ∫ z, G (tp p) z ∂(μ₀.map Rp) = ∫ w, G (tp p) (Rp w) ∂μ₀ :=
    integral_map hRm.aemeasurable hGA
  have hg_int : Integrable g0 μ₀ := (integrable_const _).add ((hlog p hp).const_mul _)
  have hpt : ∀ w ∈ H, ‖w‖ ≤ Ra →
      |Fj (Rp w)| ≤ g0 w ∧ |G (tp p) (Rp w)| ≤ g0 w ∧
        |Fj (Rp w) - G (tp p) (Rp w)| ≤ g0 w := by
    intro w hw hwR
    obtain ⟨hzH, hwz, hzR⟩ := hgeo p hp w hw hwR
    have hl := hlogz w (Rp w) hw hwz hzR
    have b1 : |Fj (Rp w)| ≤ A + B * (C₀ + |Real.log (Rp w).im|) := hF _ ht (Rp w) hzH hzR ρ hρ
      (hρρ.trans (min_le_right _ _))
    have b2 := hA _ ht (Rp w) hzH (by linarith)
    have hl0 := abs_nonneg (Real.log w.im)
    have hBl := mul_le_mul_of_nonneg_left hl hB0
    have t := abs_sub (Fj (Rp w)) (G (tp p) (Rp w))
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hg0] <;> nlinarith
  set Sτ : Set ℂ := {w : ℂ | w.im ≤ τ} with hS
  have hSm : MeasurableSet Sτ := measurableSet_le Complex.measurable_im measurable_const
  set f1 : ℂ → ℝ := fun w => 1 + |Real.log w.im| with hf1
  have hf1i : Integrable f1 μ₀ := (integrable_const 1).add (hlog p hp)
  have hdom : ∀ᵐ w ∂μ₀, ‖Fj (Rp w) - G (tp p) (Rp w)‖ ≤ K * Sτ.indicator f1 w + ε / 4 := by
    filter_upwards [hsrc p hp] with w hw
    rw [Real.norm_eq_abs]
    by_cases hwτ : w.im ≤ τ
    · rw [Set.indicator_of_mem (show w ∈ Sτ from hwτ)]
      have h3 := (hpt w hw.1 hw.2).2.2
      have hgK : g0 w ≤ K * f1 w := by
        simp only [hg0, hf1, hK]
        nlinarith [mul_nonneg (show 0 ≤ 2 * A + B * C₀ + 2 * B * (lc + L) by positivity)
          (abs_nonneg (Real.log w.im))]
      linarith
    · rw [Set.indicator_of_notMem (show w ∉ Sτ from hwτ), mul_zero, zero_add]
      obtain ⟨hzH, hwz, hzR⟩ := hgeo p hp w hw.1 hw.2
      have hzK : Rp w ∈ Kc := ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hzR,
        show c * τ ≤ (Rp w).im by
          nlinarith [mul_le_mul_of_nonneg_left (not_le.1 hwτ).le hc.le]⟩
      exact hJ ρ hρ (hρρ.trans (min_le_left _ _)) (tp p) ht (Rp w) hzK
  have hbi : Integrable (fun w => K * Sτ.indicator f1 w + ε / 4) μ₀ :=
    ((hf1i.indicator hSm).const_mul K).add (integrable_const _)
  have hbound := norm_integral_le_of_norm_le hbi hdom
  have hint1 : Integrable (fun w => Fj (Rp w)) μ₀ :=
    hg_int.mono' (hFjm.comp hRm).aestronglyMeasurable
      ((hsrc p hp).mono fun w hw => by rw [Real.norm_eq_abs]; exact (hpt w hw.1 hw.2).1)
  have hint2 : Integrable (fun w => G (tp p) (Rp w)) μ₀ :=
    hg_int.mono' (hGA.comp_aemeasurable hRm.aemeasurable)
      ((hsrc p hp).mono fun w hw => by rw [Real.norm_eq_abs]; exact (hpt w hw.1 hw.2).2.1)
  have hst : ∫ w, Sτ.indicator f1 w ∂μ₀ ≤ K₁ * τ ^ β := hstrip p hp τ hτ hτ1
  rw [integral_add ((hf1i.indicator hSm).const_mul K) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul, integral_sub hint1 hint2,
    Real.norm_eq_abs] at hbound
  have hKs := mul_le_mul_of_nonneg_left hst hK0
  show |∫ z, Fj z ∂(μ₀.map Rp) - ∫ z, G (tp p) z ∂(μ₀.map Rp)| < ε
  rw [e1, e2]
  have : K * (K₁ * τ ^ β) = K * K₁ * τ ^ β := by ring
  linarith

end ASep
end QuantumZipper
