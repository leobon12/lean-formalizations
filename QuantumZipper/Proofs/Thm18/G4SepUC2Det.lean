import QuantumZipper.Proofs.Zipper.UnifUCIdDetB
import QuantumZipper.Proofs.GFF.CoordRegHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G4 A-sep via GENERIC-UC (step (c)): uniform convergence of the deterministic part, generic

The deterministic input `hdet` of the engine (`GenUC.ae_unifConv_*`) for any family of pushed
measures `ν_p = (μ_p).map g_p`: if

* `G t v` is jointly continuous on `[0,T] × ℍ` with a logarithmic bound
  `|G t v| ≤ A + B |log Im v|` on a bounded part of `ℍ`,
* the source measures `μ_p` are probability measures on a bounded part of `ℍ` with `|log Im|`
  integrable and a **uniform strip bound** `∫_{Im ≤ τ} (1 + |log Im|) dμ_p ≤ K₁ τ^β`,
* the maps `g_p` keep `ℍ`, are bounded there, and satisfy the **imaginary-part comparison**
  `Im g_p(w) ≥ c · Im w` (`c > 0`),

then `∫∫ G_{t_p} dfc(z, 2^{-j}) dν_p(z) → ∫ G_{t_p} dν_p` uniformly in `p`.

This is `F1.xFlowLogUCStmt_holds` (XFlowUCLog.lean; D33 `RegUnif.detUnifStmt_holds`) with the
reverse flow `R_{u,s}` (for which `c = 1`, `Im R w ≥ Im w`) replaced by an abstract family `g_p`
with comparison constant `c`, and the folded circles of the box by an abstract uniformly
strip-bounded family. Sources: none — **own elementary argument** (dominated convergence
bookkeeping, as XFlowUCLog / UnifUCIdDetD; Duplantier–Sheffield, Invent. Math. 185 (2011),
Prop. 3.1 p. 18 leaves it implicit).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

open RegUnif CoordReg

/-- Choice of the strip width for a general exponent. -/
theorem exists_tau_rpow (K : ℝ) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ K * τ ^ β < η := by
  have hc : Tendsto (fun τ : ℝ => K * τ ^ β) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))).const_mul K
    rwa [Real.zero_rpow hβ.ne', mul_zero] at this
  obtain ⟨τ, h1, h2⟩ :=
    ((hc.eventually (gt_mem_nhds hη)).and (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  exact ⟨τ, h2.1, h2.2, h1⟩

/-- **Generic deterministic node.** -/
theorem det_unif_gen {T : ℝ} {G : ℝ → ℂ → ℝ}
    (hGc : ContinuousOn (fun q : ℝ × ℂ => G q.1 q.2) (Icc 0 T ×ˢ H))
    {A B Rb : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ t ∈ Icc (0 : ℝ) T, ∀ v ∈ H, ‖v‖ ≤ Rb + 1 → |G t v| ≤ A + B * |Real.log v.im|)
    (hFm : ∀ t ∈ Icc (0 : ℝ) T, ∀ j : ℕ,
      Measurable fun z => ∫ v, G t v ∂foldedCircle z (radius j))
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
    ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ p ∈ S,
      |∫ z, (∫ v, G (tp p) v ∂foldedCircle z (radius j)) ∂(μ p).map (g p) -
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
  have hF : ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ H, ‖z‖ ≤ Rb → ∀ j : ℕ,
      |∫ v, G t v ∂foldedCircle z (radius j)| ≤ A + B * (C₀ + |Real.log z.im|) := by
    intro t ht z hz hzR j
    have hr := radius_pos j
    have hr1 : radius j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hli := (TwoPoint.integrable_log_im_foldedCircle z hr).abs
    have hbd : ∀ᵐ v ∂foldedCircle z (radius j), ‖G t v‖ ≤ A + B * |Real.log v.im| := by
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H z hr,
        TwoPoint.foldedCircle_ae_norm_le z hr.le] with v hv hvn
      rw [Real.norm_eq_abs]; exact hA t ht v hv (by linarith)
    have hgi : Integrable (fun v : ℂ => A + B * |Real.log v.im|) (foldedCircle z (radius j)) :=
      (integrable_const A).add (hli.const_mul B)
    have h1 := norm_integral_le_of_norm_le hgi hbd
    rw [integral_add (integrable_const A) (hli.const_mul B), integral_const, probReal_univ,
      one_smul, integral_const_mul, Real.norm_eq_abs] at h1
    have h2 := hC₀ z hz hzR (radius j) hr hr1
    nlinarith
  obtain ⟨τ, hτ, hτ1, hτK⟩ := exists_tau_rpow (K * K₁) hβ (η := ε / 2) (by positivity)
  set Kc : Set ℂ := Metric.closedBall (0 : ℂ) Rb ∩ {z : ℂ | c * τ ≤ z.im} with hKc
  have hKcc : IsCompact Kc :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKH : Kc ⊆ H := fun z hz => lt_of_lt_of_le (mul_pos hc hτ) hz.2
  obtain ⟨J, hJ⟩ := tendstoUniformlyOn_integral_fc_comp hGc hKcc hKH (ε / 4) (by positivity)
  refine ⟨J, fun j hj p hp => ?_⟩
  have ht := htp p hp
  set μ₀ := μ p with hμ₀
  set Rp := g p with hRpdef
  have hRm : Measurable Rp := hgm p hp
  set Fj : ℂ → ℝ := fun z => ∫ v, G (tp p) v ∂foldedCircle z (radius j) with hFj
  have hFjm : Measurable Fj := hFm _ ht j
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
    have b1 : |Fj (Rp w)| ≤ A + B * (C₀ + |Real.log (Rp w).im|) := hF _ ht (Rp w) hzH hzR j
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
      exact hJ j hj (tp p) ht (Rp w) hzK
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

end G4Core
end Thm18Asm
end QuantumZipper
