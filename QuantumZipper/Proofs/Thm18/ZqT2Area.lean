import QuantumZipper.Proofs.Thm18.G3ZqL23Choice
import QuantumZipper.Proofs.Thm18.G3ZqS2Top

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (2): positive pulled-back area at every side point (pointwise)

* `areaProxy_pos_translate`: moving an area limit charging every open subset of `ℍ` from the
  pulled-back field `coordChange y ψ Q` to the field pulled back by the local map
  `w ↦ ψ(w + b) − x` at `x` (the area limit of the latter is `e^{γC} μ(· + b)`, as in
  `G3Zr.choiceRegularA_translate`), which then has positive area proxy at every radius.
* `hasAreaLimit_unsc`: the Duplantier–Sheffield coordinate change of the area (G1-SIDE's
  `G1Side.hasAreaLimit_sample`) for the canonical wedge `rescale w Q b` pulled back by
  `b⁻¹ Ψ₀`, i.e. for the unscaled wedge `w` pulled back by `Ψ₀`, with limit
  `pullMu μ_w (b · b⁻¹ Ψ₀)`, from the free-field inputs at the fixed map `1 · Ψ₀`.

Duplantier–Sheffield, arXiv:0808.1560, Prop. 2.1 (coordinate change of the quantum area).
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open G3Zr G3Z2b2 RegClosure G1Side

/-- A regular sample with an area limit: the limit is its vague area limit on `ℍ`. -/
theorem vague_of_area {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) : IsVagueLimitOn H (areaApprox γ x) μ := by
  obtain ⟨F, hF⟩ := hx
  exact ⟨hμ.1, hμ.2.1, fun f hf hfc hfU =>
    ((hμ.2.2 f hf hfc hfU).comp GoodSample.tendsto_one_goodFilter).congr fun k => by
      simp only [Function.comp, goodRad, GoodSample.areaR_radius γ hF]⟩

/-- The area proxy of a regular sample is the mass of its area limit on half-balls. -/
theorem areaProxy_pos_of_area {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ) {q : ℝ}
    (hq : 0 < μ (Metric.ball (0 : ℂ) q ∩ H)) : 0 < areaProxy γ x q := by
  have hv := vague_of_area hx hμ
  rw [areaProxy_eq_qAreaMeasure hv q, qAreaMeasure_eq hv]
  exact hq

/-- Half-balls about real points are nonempty. -/
theorem halfBall_real_nonempty (b : ℝ) {q : ℝ} (hq : 0 < q) :
    (Metric.ball (b : ℂ) q ∩ H).Nonempty := by
  refine ⟨(b : ℂ) + ((q / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · show (0 : ℝ) < ((b : ℂ) + ((q / 2 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    linarith

/-- **Positive area proxy of the field pulled back by the local map at a boundary point.** -/
theorem areaProxy_pos_translate {γ : ℝ} {y : FieldSample} (hy : IsRegularSample y)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψH : MapsTo ψ H H)
    (hcore : G1.ChoiceRegularCore γ y ψ) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ (coordChange y ψ (Qc γ)) μ)
    (hpos : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < μ V)
    (hN : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData y ((foldedCircle d r).map ψ)) (b x C : ℝ)
    {q : ℝ} (hq : 0 < q) :
    0 < areaProxy γ (coordChange (addConst (translate y (x : ℂ)) C)
      (fun w => ψ (w + (b : ℂ)) - (x : ℂ)) (Qc γ)) q := by
  set Z := coordChange y ψ (Qc γ) with hZ
  set V := coordChange (addConst (translate y (x : ℂ)) C) (fun w => ψ (w + (b : ℂ)) - (x : ℂ))
    (Qc γ) with hV
  set W := addConst (translate Z (b : ℂ)) C with hW
  obtain ⟨⟨FZ, hFZ⟩, hex, -⟩ := hcore
  have hFW : IsRegularWith W (fun q => FZ (q.1 + b, q.2) + C) := (hFZ.translate' b).addConst' C
  have hraw : ∀ (d : ℂ) (r : ℝ), 0 < r → V (foldedCircle d r) = W (foldedCircle d r) :=
    fun d r hr => raw_eq_translate_side hy hψm hψH hex hN b x C d hr
  have hFV : IsRegularWith V (fun q => FZ (q.1 + b, q.2) + C) :=
    RegUnif.isRegularWith_of_raw_eq (fun n k z => hraw _ _ (radius_pos k)) hFW
  have havg : avgReg W = avgReg V := by
    funext k w; unfold avgReg; congr 1; funext n; exact (hraw _ _ (radius_pos k)).symm
  set cst : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * C)) with hcst
  have hμW : HasAreaLimit γ W (cst • μ.map fun z => z - (b : ℂ)) := by
    have h1 := GoodTransforms.hasAreaLimit_translate ⟨FZ, hFZ⟩ hμ b
    have h2 := GoodSample.hasAreaLimit_add_ofFun ⟨_, hFZ.translate' b⟩ h1 (φ := fun _ => C)
      continuousOn_const
    rw [← GoodSample.addConst_eq_add_ofFun, withDensity_const] at h2
    exact h2
  have hμV := g1ssr_hasAreaLimit_congr havg hμW
  refine areaProxy_pos_of_area ⟨_, hFV⟩ hμV ?_
  have hc0 : cst ≠ 0 := by
    rw [hcst, Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  rw [Measure.smul_apply, smul_eq_mul, map_sub_ball_eq]
  exact ENNReal.mul_pos hc0 (hpos _ (Metric.isOpen_ball.inter isOpen_H) inter_subset_right
    (halfBall_real_nonempty b hq)).ne'

/-- **The area limit of the unscaled wedge pulled back by a fixed side map** (coordinate change,
`G1Side.hasAreaLimit_sample` with the map `b⁻¹ Ψ₀` and the scale `b`). -/
theorem hasAreaLimit_unsc {γ : ℝ} (hγ : 0 < γ) {x0 : FieldSample} {F : ℂ × ℝ → ℝ}
    {A0 : ℝ → ℝ} (hgood : WedgeTK.GoodRad x0 F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x0 (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A0) (hWg : IsLQGGood γ (wedgeField (lateralPart x0) A0 (Qc γ)))
    {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1)) (hcw' : Tendsto cw' atTop (𝓝 1))
    (hWin : E6.WindowLimits γ (wedgeField (lateralPart x0) A0 (Qc γ)) cw cw')
    {Ψ₀ : ℂ → ℂ} (hF : G1Side.SideMapFacts Ψ₀) {b : ℝ} (hb : 0 < b)
    (hRC3 : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (coordChange (rescale (wedgeField (lateralPart x0) A0 (Qc γ)) (Qc γ) b)
        (fun u => ((b⁻¹ : ℝ) : ℂ) * Ψ₀ u) (Qc γ)) (foldedCircle d r) =
      coordChange (rescale (wedgeField (lateralPart x0) A0 (Qc γ)) (Qc γ) b)
        (fun u => ((b⁻¹ : ℝ) : ℂ) * Ψ₀ u) (Qc γ) (foldedCircle d r))
    (HL : ∀ n : ℕ, ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ G1Side.recR n,
      Tendsto (fun j => ∫ u, avgReg x0 j u
          ∂((foldedCircle z (α * radius k)).map fun u => ((1 : ℝ) : ℂ) * Ψ₀ u)) atTop
        (𝓝 (evalReg x0 ((foldedCircle z (α * radius k)).map fun u => ((1 : ℝ) : ℂ) * Ψ₀ u))))
    (HX : ∀ n : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ G1Side.recR n,
      |evalReg x0 ((foldedCircle z (α * radius k)).map fun u => ((1 : ℝ) : ℂ) * Ψ₀ u) -
        evalReg x0 (foldedCircle (((1 : ℝ) : ℂ) * Ψ₀ z)
          (α * radius k * ‖deriv (fun u => ((1 : ℝ) : ℂ) * Ψ₀ u) z‖))| ≤ η)
    (HC : ∀ n : ℕ, ∃ k₁ : ℕ, ∀ k ≥ k₁, ∀ α ∈ Icc (1 : ℝ) 2, ∀ v ∈ G1Side.recU n, ∃ Y : ℝ,
      Tendsto (fun σ => ∫ u, F (u, σ)
        ∂((foldedCircle v (α * radius k)).map fun u => ((1 : ℝ) : ℂ) * Ψ₀ u)) (𝓝[>] 0)
        (𝓝 Y)) :
    HasAreaLimit γ (coordChange (rescale (wedgeField (lateralPart x0) A0 (Qc γ)) (Qc γ) b)
        (fun u => ((b⁻¹ : ℝ) : ℂ) * Ψ₀ u) (Qc γ))
      (pullMu (qAreaMeasure γ (wedgeField (lateralPart x0) A0 (Qc γ)))
        fun u => ((1 : ℝ) : ℂ) * Ψ₀ u) := by
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have hbb : ∀ u, (b : ℂ) * (((b⁻¹ : ℝ) : ℂ) * Ψ₀ u) = ((1 : ℝ) : ℂ) * Ψ₀ u := by
    intro u; push_cast; field_simp
  have hbbf : (fun u => (b : ℂ) * (((b⁻¹ : ℝ) : ℂ) * Ψ₀ u)) = fun u => ((1 : ℝ) : ℂ) * Ψ₀ u :=
    funext hbb
  obtain ⟨hm, hd, hi, hH, h0, hint⟩ := hF
  obtain ⟨hd', hi', hH', h0'⟩ :=
    G3ZqL.sideMapFacts_smul ⟨hm, hd, hi, hH, h0, hint⟩ (inv_pos.2 hb)
  have key := G1Side.hasAreaLimit_sample (ψ := fun u => ((b⁻¹ : ℝ) : ℂ) * Ψ₀ u) (s := b)
    hγ hgood hraw hA hWg hcw hcw' hWin (measurable_const.mul hm) hd' hi' hH' h0' ?_ hb hRC3
    (by simpa only [hbb] using HL) (by simpa only [hbb, hbbf] using HX)
    (by simpa only [hbb] using HC)
  · rw [hbbf] at key; exact key
  · intro d _ r hr
    refine ((integrable_const (Real.log ‖((b⁻¹ : ℝ) : ℂ)‖)).add (hint d ‹_› r hr)).congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
    have hda : DifferentiableAt ℂ Ψ₀ z := hd.differentiableAt (isOpen_H'.mem_nhds hz)
    show Real.log ‖((b⁻¹ : ℝ) : ℂ)‖ + Real.log ‖deriv Ψ₀ z‖ =
      Real.log ‖deriv (fun u => ((b⁻¹ : ℝ) : ℂ) * Ψ₀ u) z‖
    rw [deriv_const_mul _ hda, norm_mul, Real.log_mul
      (norm_ne_zero_iff.2 (Complex.ofReal_ne_zero.2 (inv_pos.2 hb).ne'))
      (norm_ne_zero_iff.2 (h0 z hz))]

end ZqT
end Thm18Asm
end QuantumZipper
