import QuantumZipper.Proofs.Thm18.G1RegCore

/-!
# G1-CORE, part 1: `ChoiceRegularCore` does not depend on the normalization (Theorem 1.8, G1)

A normalized uniformizer of a chord component is unique up to `z ↦ a z`, `a > 0`
(`CA.Uniformizer.normalizedUniformizer_unique_*`, Burckel Thm 6.2(ii)), so its inverse is
unique up to precomposition with a dilation (`G1.invFunOn_eqOn_of_eqOn_mul`). This file proves,
deterministically, that the regularity package `G1.ChoiceRegularCore` (RC2 regular sample, RC3
exact folded-circle values, PAIR-LIM) is invariant under `ψ ↦ ψ ∘ (b ·)`:

* `coordChange_fc_of_eqOn_comp_mul`: if `x = coordChange y ψ Q` is regular with witness `F`
  and exact on folded circles, then `x' = coordChange y ψ' Q`, `ψ' = ψ ∘ (b ·)` on `ℍ`, has raw
  folded-circle values `F (b d, b r) + Q log b` (centres `d ∈ Hbar`);
* `isRegularWith_coordChange_eqOn_comp_mul`: hence `x'` is regular with the witness of
  `rescale x Q b` (`IsRegularWith.rescale'`);
* `choiceRegularCore_of_eqOn_comp_mul`: `ChoiceRegularCore γ y ψ → ChoiceRegularCore γ y ψ'`
  (PAIR-LIM at dilation `c` for `ψ'` is PAIR-LIM at dilation `b c` for `ψ`, radii `b s`);
* `choiceRegularCore_invFunOn_of_normalized`: for a simple chord, `ChoiceRegularCore` for the
  inverse of one normalized uniformizer of a side component gives it for every other one.

Mathematical content: the remark after (1.8) in Sheffield, arXiv:1012.4797, §1.6 (the
coordinate change by a dilation is the rescaling). The proofs are own elementary arguments
(change of variables under dilations, `MeasurableEmbedding.integral_map`).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1

variable {γ : ℝ} {y : FieldSample} {ψ ψ' : ℂ → ℂ} {b : ℝ}

/-- Raw folded-circle values of `coordChange y ψ' Q` for `ψ' = ψ ∘ (b ·)` on `ℍ`, in terms of
the regularity witness `F` of `coordChange y ψ Q`. -/
theorem coordChange_fc_of_eqOn_comp_mul {F : ℂ × ℝ → ℝ} (Q : ℝ)
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    (hint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hF : IsRegularWith (coordChange y ψ Q) F)
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y ψ Q) (foldedCircle d r) = coordChange y ψ Q (foldedCircle d r))
    (hb : 0 < b) (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H) {d : ℂ} (hd : d ∈ Hbar)
    {r : ℝ} (hr : 0 < r) :
    coordChange y ψ' Q (foldedCircle d r) = F ((b : ℂ) * d, b * r) + Q * Real.log b := by
  have hbd : (b : ℂ) * d ∈ Hbar := RegClosure.mapsTo_mul_pos hb hd
  have hbr : 0 < b * r := mul_pos hb hr
  rw [CoordReg.coordChange_fc_congr y heq Q d hr,
    coordChange_comp_mul_fc y Q hψd hψ0 hψm hb d hr (hint _ hbd _ hbr),
    ← hexact _ hbd _ hbr, hF.evalReg_fc_of_mem hbd hbr]

/-- `coordChange y ψ' Q` is regular, with the witness of the rescaling by `b`. -/
theorem isRegularWith_coordChange_eqOn_comp_mul {F : ℂ × ℝ → ℝ} (Q : ℝ)
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    (hint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hF : IsRegularWith (coordChange y ψ Q) F)
    (hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange y ψ Q) (foldedCircle d r) = coordChange y ψ Q (foldedCircle d r))
    (hb : 0 < b) (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H) :
    IsRegularWith (coordChange y ψ' Q)
      (fun q => F ((b : ℂ) * q.1, b * q.2) + Q * Real.log b) := by
  have hR := hF.rescale' Q hb
  exact ⟨hR.1, fun k z hz => RegClosure.tendsto_of_eval_eq hR.1
    (fun d hd r hr => coordChange_fc_of_eqOn_comp_mul Q hψd hψ0 hψm hint hF hexact hb heq hd hr)
    k hz, hR.2.2⟩

/-- **`ChoiceRegularCore` is invariant under precomposition with a dilation.** -/
theorem choiceRegularCore_of_eqOn_comp_mul
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    (hint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hcore : ChoiceRegularCore γ y ψ) (hb : 0 < b)
    (heq : EqOn ψ' (fun w => ψ ((b : ℂ) * w)) H) :
    ChoiceRegularCore γ y ψ' := by
  obtain ⟨⟨F, hF⟩, hexact, hpair⟩ := hcore
  have hR := isRegularWith_coordChange_eqOn_comp_mul (Qc γ) hψd hψ0 hψm hint hF hexact hb heq
  have hval : ∀ u ∈ Hbar, ∀ s : ℝ, 0 < s →
      evalReg (coordChange y ψ' (Qc γ)) (foldedCircle u s) =
        evalReg (coordChange y ψ (Qc γ)) (foldedCircle ((b : ℂ) * u) (b * s)) +
          Qc γ * Real.log b := by
    intro u hu s hs
    rw [hR.evalReg_fc_of_mem hu hs,
      hF.evalReg_fc_of_mem (RegClosure.mapsTo_mul_pos hb hu) (mul_pos hb hs)]
  refine ⟨⟨_, hR⟩, fun d hd r hr => ?_, fun c hc ρ σ hσ => ?_⟩
  · rw [hR.evalReg_fc_of_mem hd hr,
      coordChange_fc_of_eqOn_comp_mul (Qc γ) hψd hψ0 hψm hint hF hexact hb heq hd hr]
  obtain ⟨hI, L, hL⟩ := hpair (b * c) (mul_pos hb hc) ρ σ hσ
  have hσp : Continuous σ ∧ HasCompactSupport σ ∧ tsupport σ ⊆ H := by
    rcases hσ with rfl | rfl
    · exact ⟨ρ.2.1.continuous, ρ.2.2.1, ρ.2.2.2⟩
    · refine ⟨ρ.2.1.continuous.neg, ρ.2.2.1.neg, ?_⟩
      show tsupport (-ρ.1) ⊆ H
      rw [tsupport_neg]; exact ρ.2.2.2
  have : IsFiniteMeasure (tmeas σ) := isFiniteMeasure_tmeas hσp.1 hσp.2.1
  set μ : Measure ℂ := (tmeas σ).map fun z => (c : ℂ) * z with hμ
  have hae : ∀ᵐ u ∂μ, u ∈ Hbar := ae_tmeas_map_mem_Hbar hσp.1 hσp.2.2 hc
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hemb : MeasurableEmbedding (fun u : ℂ => (b : ℂ) * u) :=
    (Homeomorph.mulLeft₀ (b : ℂ) hb0).measurableEmbedding
  have hmm : μ.map (fun u : ℂ => (b : ℂ) * u) =
      (tmeas σ).map fun z => ((b * c : ℝ) : ℂ) * z := by
    rw [hμ, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
    congr 1; funext z; simp only [Function.comp]; push_cast; ring
  have hcongr : ∀ s : ℝ, 0 < s →
      (fun u => evalReg (coordChange y ψ' (Qc γ)) (foldedCircle u s)) =ᵐ[μ]
        fun u => evalReg (coordChange y ψ (Qc γ)) (foldedCircle ((b : ℂ) * u) (b * s)) +
          Qc γ * Real.log b :=
    fun s hs => hae.mono fun u hu => hval u hu s hs
  have hint2 : ∀ s : ℝ, 0 < s → Integrable
      (fun u => evalReg (coordChange y ψ (Qc γ)) (foldedCircle ((b : ℂ) * u) (b * s))) μ := by
    intro s hs
    have h := hI (b * s) (mul_pos hb hs)
    rw [← hmm, hemb.integrable_map_iff] at h
    exact h
  refine ⟨fun s hs => ((hint2 s hs).add (integrable_const _)).congr (hcongr s hs).symm,
    L + Qc γ * Real.log b * μ.real univ, ?_⟩
  have hEq : ∀ s : ℝ, 0 < s →
      ∫ u, evalReg (coordChange y ψ' (Qc γ)) (foldedCircle u s) ∂μ =
        (∫ v, evalReg (coordChange y ψ (Qc γ)) (foldedCircle v (b * s))
          ∂((tmeas σ).map fun z => ((b * c : ℝ) : ℂ) * z)) + Qc γ * Real.log b * μ.real univ := by
    intro s hs
    rw [integral_congr_ae (hcongr s hs), integral_add (hint2 s hs) (integrable_const _),
      integral_const, smul_eq_mul, ← hmm, hemb.integral_map]
    ring
  have hbs : Tendsto (fun s : ℝ => b * s) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨
      tendsto_nhdsWithin_of_tendsto_nhds ((continuous_const_mul b).tendsto' 0 0 (mul_zero b)),
      eventually_nhdsWithin_of_forall fun s (hs : 0 < s) => mul_pos hb hs⟩
  refine ((hL.comp hbs).add tendsto_const_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [hEq s hs]
  rfl

/-- **Normalization independence** for the side components of a simple chord: the regularity
package for the inverse of one normalized uniformizer gives it for the inverse of any other. -/
theorem choiceRegularCore_invFunOn_of_normalized {η : ℝ → ℂ} (hη : IsSimpleChord η)
    (left : Bool) {φ₀ φ : ℂ → ℂ} (h₀ : IsNormalizedUniformizer (sideDom η left) φ₀)
    (hφ : IsNormalizedUniformizer (sideDom η left) φ)
    (hcore : ChoiceRegularCore γ y (invFunOn φ₀ (sideDom η left))) :
    ChoiceRegularCore γ y (invFunOn φ (sideDom η left)) := by
  obtain ⟨a, ha, heq⟩ : ∃ a : ℝ, 0 < a ∧
      EqOn φ (fun z => (a : ℂ) * φ₀ z) (sideDom η left) := by
    cases left
    · exact CA.Uniformizer.normalizedUniformizer_unique_rightComponent hη h₀ hφ
    · exact CA.Uniformizer.normalizedUniformizer_unique_leftComponent hη h₀ hφ
  have hinv := invFunOn_eqOn_of_eqOn_mul h₀.1 hφ.1 ha heq
  obtain ⟨hd, h0, hm, -⟩ := invFunOn_props (isOpen_component hη left) h₀
  exact choiceRegularCore_of_eqOn_comp_mul hd h0 hm
    (choiceRegular_logDeriv (isOpen_component hη left) h₀) hcore (inv_pos.2 ha) hinv

end G1
end Thm18Asm
end QuantumZipper
