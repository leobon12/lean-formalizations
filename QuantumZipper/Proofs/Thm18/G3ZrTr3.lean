import QuantumZipper.Proofs.Thm18.G3ZrTr2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (8): **`choiceRegularA_translate`**

The area-only choice regularity of the translated field pulled back by the local map
`w ↦ ψ(w + β) − x`, from the side-field data at `ψ` (see `G3ZrTr`). Own bookkeeping (the same
steps as `shiftRegA_of_det`, G1SSRMain.lean, after a real translation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2 RegClosure

/-- The small-ball mass of a translated measure is the small-ball mass at the real point. -/
theorem map_sub_ball_eq (μ : Measure ℂ) (p a : ℝ) :
    (μ.map fun z => z - (p : ℂ)) (Metric.ball (0 : ℂ) a ∩ H) = μ (Metric.ball (p : ℂ) a ∩ H) := by
  rw [Measure.map_apply (show Measurable fun z : ℂ => z - (p : ℂ) from measurable_id.sub_const _)
    (Metric.isOpen_ball.inter isOpen_H).measurableSet, g1z2_preimage_sub_ball]

/-- **Area-only choice regularity at a boundary point.** -/
theorem choiceRegularA_translate {γ : ℝ} {y : FieldSample} (hy : IsRegularSample y)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψH : MapsTo ψ H H)
    (hcore : G1.ChoiceRegularCore γ y ψ) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ (coordChange y ψ (Qc γ)) μ)
    (hsmall : ∀ p : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) (htop : μ H = ⊤)
    (hN : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData y ((foldedCircle d r).map ψ)) (b x C : ℝ) :
    G1.ChoiceRegularA γ (addConst (translate y (x : ℂ)) C)
      (fun w => ψ (w + (b : ℂ)) - (x : ℂ)) := by
  set Z := coordChange y ψ (Qc γ) with hZ
  set V := coordChange (addConst (translate y (x : ℂ)) C) (fun w => ψ (w + (b : ℂ)) - (x : ℂ))
    (Qc γ) with hV
  set W := addConst (translate Z (b : ℂ)) C with hW
  obtain ⟨⟨FZ, hFZ⟩, hex, hpair⟩ := hcore
  have hFW : IsRegularWith W (fun q => FZ (q.1 + b, q.2) + C) := (hFZ.translate' b).addConst' C
  have hraw : ∀ (d : ℂ) (r : ℝ), 0 < r → V (foldedCircle d r) = W (foldedCircle d r) :=
    fun d r hr => raw_eq_translate_side hy hψm hψH hex hN b x C d hr
  have hFV : IsRegularWith V (fun q => FZ (q.1 + b, q.2) + C) :=
    RegUnif.isRegularWith_of_raw_eq (fun n k z => hraw _ _ (radius_pos k)) hFW
  have havg : avgReg W = avgReg V := by
    funext k w; unfold avgReg; congr 1; funext n; exact (hraw _ _ (radius_pos k)).symm
  -- RC3
  have hexV : ∀ d ∈ Hbar, ∀ r > 0, evalReg V (foldedCircle d r) = V (foldedCircle d r) := by
    intro d hd r hr
    rw [hFV.evalReg_fc_of_mem hd hr, hraw d r hr]
    simp only [hW, addConst, measure_univ, ENNReal.toReal_one, mul_one]
    rw [translate_fc_eq hFZ b hd hr]
  -- area limit
  set cst : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ * C)) with hcst
  have hμW : HasAreaLimit γ W (cst • μ.map fun z => z - (b : ℂ)) := by
    have h1 := GoodTransforms.hasAreaLimit_translate ⟨FZ, hFZ⟩ hμ b
    have h2 := GoodSample.hasAreaLimit_add_ofFun ⟨_, hFZ.translate' b⟩ h1 (φ := fun _ => C)
      continuousOn_const
    rw [← GoodSample.addConst_eq_add_ofFun, withDensity_const] at h2
    exact h2
  have hμV := g1ssr_hasAreaLimit_congr havg hμW
  -- positivity of the scale parameter
  have hc0 : cst ≠ 0 := by
    rw [hcst, Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  have hcT : cst ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨a₀, ha₀, h₀⟩ := hsmall b
  have hε : 0 < ENNReal.ofReal (Real.exp (-(γ * C))) := ENNReal.ofReal_pos.2 (Real.exp_pos _)
  obtain ⟨a, ha, hlt⟩ := g1ssr_small_ball (μ := μ.map fun z => z - (b : ℂ)) ha₀
    (by rw [map_sub_ball_eq]; exact h₀) hε
  rw [map_sub_ball_eq] at hlt
  have hsmallC : (cst • μ) (Metric.ball (b : ℂ) a ∩ H) < 1 := by
    rw [Measure.smul_apply, smul_eq_mul]
    calc cst * μ (Metric.ball (b : ℂ) a ∩ H) < cst * ENNReal.ofReal (Real.exp (-(γ * C))) :=
          ENNReal.mul_lt_mul_right hc0 hcT hlt
      _ = 1 := by
          rw [hcst, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
            Real.exp_zero, ENNReal.ofReal_one]
  have htopC : (cst • μ) H = ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul, htop, ENNReal.mul_top hc0]
  obtain ⟨hs0, hbig⟩ := g1z2_translate_mass b ⟨a, ha, hsmallC⟩ htopC
  have hsubm : AEMeasurable (fun z : ℂ => z - (b : ℂ)) μ := (measurable_id.sub_const _).aemeasurable
  rw [Measure.map_smul _ hsubm] at hs0 hbig
  have hsV : 0 < scaleParam γ V := g1z2_scaleParam_pos ⟨_, hFV⟩ hμV hs0 hbig
  -- continuum limits at dilated test measures, hence scale consistency
  have hpairV : ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ,
      (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
      F1.ContData V ((G1.tmeas σ).map fun z => (c : ℂ) * z) := by
    intro c hc ρ σ hσ
    obtain ⟨hsm, hsc, hsH⟩ := ρ.2
    have hσc : Continuous σ ∧ HasCompactSupport σ ∧ tsupport σ ⊆ H := by
      rcases hσ with rfl | rfl
      · exact ⟨hsm.continuous, hsc, hsH⟩
      · exact ⟨hsm.continuous.neg, hsc.neg, by
          rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact hsH⟩
    obtain ⟨hσ1, hσ2, hσ3⟩ := hσc
    have := G1.isFiniteMeasure_tmeas hσ1 hσ2
    have hmH := G1.ae_tmeas_map_mem_Hbar hσ1 hσ3 hc
    have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
    set t : ℝ := b / c with ht
    have hmap : ((G1.tmeas σ).map fun z => (c : ℂ) * z).map (· + (b : ℂ)) =
        (G1.tmeas fun z => σ (z - (t : ℂ))).map fun z => (c : ℂ) * z := by
      rw [← tmeas_map_add, Measure.map_map (measurable_add_const _) (measurable_const_mul _),
        Measure.map_map (measurable_const_mul _) (measurable_add_const _)]
      congr 1
      funext z
      simp only [Function.comp, ht]
      push_cast
      field_simp
    have hZc : F1.ContData Z ((G1.tmeas fun z => σ (z - (t : ℂ))).map fun z => (c : ℂ) * z) := by
      rcases hσ with rfl | rfl
      · exact hpair c hc (testTranslate ρ t) _ (Or.inl rfl)
      · exact hpair c hc (testTranslate ρ t) _ (Or.inr rfl)
    have hT : F1.ContData (translate Z (b : ℂ)) ((G1.tmeas σ).map fun z => (c : ℂ) * z) :=
      contData_translate_of ⟨FZ, hFZ⟩ b hmH (by rw [hmap]; exact hZc)
    refine g1ssr_contData_shift (C := C) hmH (fun u hu ρ' hρ' => ?_) hT
    rw [hFV.evalReg_fc_of_mem hu hρ', (hFZ.translate' b).evalReg_fc_of_mem hu hρ']
  have hcoreV : G1.ChoiceRegularCore γ (addConst (translate y (x : ℂ)) C)
      (fun w => ψ (w + (b : ℂ)) - (x : ℂ)) := ⟨⟨_, hFV⟩, hexV, hpairV⟩
  exact ⟨⟨_, hFV⟩, hexV, ⟨_, hμV⟩, hsV, fun b' hb' c hc ρ σ hσ =>
    G1ZA1b.g1za1b_scaleConsistent_of_core hcoreV hb' hc ρ σ hσ⟩

end G3Zr
end Thm18Asm
end QuantumZipper
