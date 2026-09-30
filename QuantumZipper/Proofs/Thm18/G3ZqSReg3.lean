import QuantumZipper.Proofs.Thm18.G3ZqSMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3ZqS (5): the shift clauses of `G3ZqRegU` for the unscaled field (clause (iii), part 1)

The continuum limits of the UNSCALED wedge `W = wedgeU` along the circles pushed by the side map
`Ψ_a` of the unscaled path follow from those of the canonical field `canonical W = rescale W Q b`
along the side map of the scaled path `S_b a` (the coupled condition `UCond`, `ae_ucond_scaled`):
`b · Ψ_{S_b a} = Ψ_a ∘ (μ⁻¹ ·)` on `ℍ` (`G1Zm.psi_scalePath`) and the dilation step
`G3Zr.contData_dilate_of_rescale` (`contData_unscaled_pt`). With the regularity of `W` this gives
the two `RegShift` clauses of `G3ZqRegU` at every point (`regShiftU_pt`, `ae_regShiftU`).

The remaining clause of `G3ZqRegU` is the area-only choice regularity `ChoiceRegularA`; together
with the positivity of the unscaled length partner it is the node **`G3ZqSChoiceUStmt`**, and
`g3ZqSRegUStmt_of_choice : G3ZqSChoiceUStmt → G3ZqSRegUStmt`.

Sheffield, arXiv:1012.4797, p. 70. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqS

open G1Zm G3Zq G3Zr G3Z2b2 G1SSR2

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **Continuum limits of the unscaled field along the side map of the unscaled path.** -/
theorem contData_unscaled_pt {γ : ℝ} (hsel : G1PsiSel γ Ψ) {y : FieldSample}
    (hg : IsLQGGood γ y) (hb : 0 < scaleParam γ y) {a : ℝ≥0 → ℝ} (hac : Continuous a)
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (hWd : Continuous (pathDrive (γ ^ 2) a))
    (hW0 : pathDrive (γ ^ 2) a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive (γ ^ 2) a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (left : Bool) (hpe : G1RC.PsiExt (Ψ left (scalePath (scaleParam γ y) a)))
    (hu : UCond (canonical γ y) (Ψ left (scalePath (scaleParam γ y) a))) :
    ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData y ((foldedCircle d r).map (Ψ left a)) := by
  set b := scaleParam γ y with hbdef
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b a)) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs
  have hcb : Continuous (scalePath b a) := continuous_scalePath hac
  obtain ⟨ψe, -, hψec, hψeH, heq, -⟩ := hpe
  have hΨm' : Measurable (Ψ left (scalePath b a)) :=
    (hsel.1 left).comp (measurable_const.prodMk measurable_id)
  have hΨm : Measurable (Ψ left a) := (hsel.1 left).comp (measurable_const.prodMk measurable_id)
  have hΨH' : MapsTo (Ψ left (scalePath b a)) H H :=
    (G1RC.psiGood_of_sel hsel hcb hsb left).2.2.2.1
  obtain ⟨F, hF⟩ := hg.1
  have hFr := hF.rescale' (Qc γ) hb
  obtain ⟨μ, hμ, hΨ⟩ := psi_scalePath hsel hb hac hs hcb hsb hWd hW0 hex left
  intro d r hr
  have hμr : 0 < μ * r := mul_pos hμ hr
  set d' : ℂ := (μ : ℂ) * d with hd'
  have h1 : F1.ContData (rescale y (Qc γ) b) ((foldedCircle d' (μ * r)).map (Ψ left (scalePath b a))) :=
    G1SSR2.contData_of_ucond hFr hΨm' hψec hψeH heq hu d' hμr
  have hH' : ∀ᵐ u ∂((foldedCircle d' (μ * r)).map (Ψ left (scalePath b a))), u ∈ Hbar :=
    ae_map_mem_Hbar hΨm' ((TwoPoint.foldedCircle_ae_mem_H d' hμr).mono fun w hw =>
      H_subset_Hbar (hΨH' hw))
  have h2 := contData_dilate_of_rescale ⟨F, hF⟩ (Qc γ) hb hH' h1
  have hμ' : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hμ.ne'
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have e : ((foldedCircle d' (μ * r)).map (Ψ left (scalePath b a))).map (fun u => (b : ℂ) * u) =
      (foldedCircle d r).map (Ψ left a) := by
    rw [Measure.map_map (measurable_const_mul _) hΨm']
    have e1 : (foldedCircle d' (μ * r)).map ((fun u => (b : ℂ) * u) ∘ Ψ left (scalePath b a)) =
        (foldedCircle d' (μ * r)).map (Ψ left a ∘ fun w => ((μ⁻¹ : ℝ) : ℂ) * w) := by
      refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d' hμr).mono fun w hw => ?_)
      simp only [Function.comp, hΨ w hw]
      rw [← mul_assoc, show (b : ℂ) * ((b⁻¹ : ℝ) : ℂ) = 1 by push_cast; field_simp, one_mul]
      push_cast; rfl
    rw [e1, ← Measure.map_map hΨm (measurable_const_mul _),
      IndepParams.fc_map_mul' _ _ (inv_pos.2 hμ)]
    congr 2
    · rw [hd']; push_cast; field_simp
    · field_simp
  rw [← e]
  exact h2

/-- **The two shift clauses of `G3ZqRegU` from the continuum limits.** -/
theorem regShiftU_pt {y : FieldSample} (hy : IsRegularSample y) {left : Bool} {a : ℝ≥0 → ℝ}
    (hΨm : Measurable (Ψ left a)) (hΨH : MapsTo (Ψ left a) H H)
    (hcont : ∀ (d : ℂ) (r : ℝ), 0 < r → F1.ContData y ((foldedCircle d r).map (Ψ left a)))
    (x : ℝ) :
    (∀ (d : ℂ) (j : ℕ), E1.RegShift (translate y (x : ℂ))
      ((foldedCircle d (radius j)).map (g3mapB Ψ left a 1 x))) ∧
    (∀ k : ℝ, 0 < k → ∀ (d : ℂ) (j : ℕ), E1.RegShift (translate y (x : ℂ))
      ((foldedCircle d (radius j)).map fun w => g3mapB Ψ left a 1 x ((k : ℂ) * w))) := by
  have hg : g3mapB Ψ left a 1 x =
      fun w => Ψ left a (w + (g3bpre Ψ left a (x / 1) : ℂ)) - (x : ℂ) := by
    funext w
    simp [g3mapB, g3locM]
  have key : ∀ (d : ℂ) (r : ℝ), 0 < r → E1.RegShift (translate y (x : ℂ))
      ((foldedCircle d r).map (g3mapB Ψ left a 1 x)) := by
    intro d r hr
    rw [hg]
    exact regShift_translate_shift hy hΨm hΨH _ x d hr (hcont _ _ hr)
  refine ⟨fun d j => key d _ (radius_pos j), fun k hk d j => ?_⟩
  have hgm : Measurable (g3mapB Ψ left a 1 x) := by
    rw [hg]
    exact (hΨm.comp (measurable_id.add_const _)).sub_const _
  have e : (foldedCircle d (radius j)).map (fun w => g3mapB Ψ left a 1 x ((k : ℂ) * w)) =
      (foldedCircle ((k : ℂ) * d) (k * radius j)).map (g3mapB Ψ left a 1 x) := by
    rw [← IndepParams.fc_map_mul' _ _ hk, Measure.map_map hgm (measurable_const_mul _)]
    rfl
  rw [e]
  exact key _ _ (mul_pos hk (radius_pos j))

variable {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}

/-- **The shift clauses of `G3ZqRegU` for the unscaled wedge along the unscaled path, a.s.** -/
theorem ae_regShiftU {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hsel : G1PsiSel γ Ψ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') (hB : IsBrownianReal B P)
    (hsc : ∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) :
    ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P, ∀ (left : Bool) (x : ℝ),
      (∀ (d : ℂ) (j : ℕ), E1.RegShift (translate (wedgeU γ X A ω') (x : ℂ))
        ((foldedCircle d (radius j)).map (g3mapB Ψ left (pathOf B ω) 1 x))) ∧
      (∀ k : ℝ, 0 < k → ∀ (d : ℂ) (j : ℕ), E1.RegShift (translate (wedgeU γ X A ω') (x : ℂ))
        ((foldedCircle d (radius j)).map fun w =>
          g3mapB Ψ left (pathOf B ω) 1 x ((k : ℂ) * w))) := by
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  obtain ⟨c, hc, hc0, hce⟩ := exists_meas_scale hγ hγ2 hX hA hXA
  filter_upwards [ae_ucond_scaled hγ hγ2 hsel hX hA hXA hB hc0, hce,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA]
    with ω' hu he hg
  have hb : 0 < scaleParam γ (wedgeU γ X A ω') := he ▸ hc0 ω'
  filter_upwards [hu, ae_psiExt_scaled hγ hγ2 hsel hX hA hXA hB hb, ae_goodPathF hγ hγ2 hB hsc]
    with ω hu' hpe hgood left x
  obtain ⟨hac, hs', hWd, hW0, hex⟩ := hgood
  have hu2 : UCond (canonical γ (wedgeU γ X A ω'))
      (Ψ left (scalePath (scaleParam γ (wedgeU γ X A ω')) (pathOf B ω))) := by
    have := hu' left; rw [he] at this; exact this
  have hΨm : Measurable (Ψ left (pathOf B ω)) :=
    (hsel.1 left).comp (measurable_const.prodMk measurable_id)
  exact regShiftU_pt hg.1 hΨm (G1RC.psiGood_of_sel hsel hac hs' left).2.2.2.1
    (contData_unscaled_pt hsel hg hb hac hs' hWd hW0 hex left (hpe left) hu2) x

/-- **The remaining part of clause (iii) (open node):** the area-only choice regularity of the
unscaled wedge along the unscaled path at a.e. window point and at its length partner, and the
positivity of the unscaled length partner. -/
def G3ZqSChoiceUStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    (∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) →
  ∀ (U L : ℝ), ∀ᵐ ω' ∂P', ∀ᵐ ω ∂P,
    ∀ᵐ x ∂(qBoundaryMeasure γ (wedgeU γ X A ω')), x ∈ g1zWedgeWin γ true (wedgeU γ X A ω') U →
      G1.ChoiceRegularA γ (addConst (translate (wedgeU γ X A ω') (x : ℂ)) (L / γ))
          (g3mapB Ψ true (pathOf B ω) 1 x) ∧
        0 < R18.g3zPartner γ (wedgeU γ X A ω') x ∧
        G1.ChoiceRegularA γ (addConst (translate (wedgeU γ X A ω')
            (R18.g3zPartner γ (wedgeU γ X A ω') x : ℂ)) (L / γ))
          (g3mapB Ψ false (pathOf B ω) 1 (R18.g3zPartner γ (wedgeU γ X A ω') x))

/-- **Clause (iii) from its choice-regularity part.** -/
theorem g3ZqSRegUStmt_of_choice (h : G3ZqSChoiceUStmt) : G3ZqSRegUStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω _ P _ B hB hsc U L
  filter_upwards [ae_regShiftU (Ψ := Ψ) hγ hγ2 hsel hX hA hXA hB hsc,
    h γ hγ hγ2 Ψ hsel P' X A hX hA hXA P B hB hsc U L] with ω' h1 h2
  filter_upwards [h1, h2] with ω hs hc
  filter_upwards [hc] with x hx hxw
  obtain ⟨c1, hp, c2⟩ := hx hxw
  exact ⟨⟨(hs true x).1, (hs true x).2, c1⟩, hp, ⟨(hs false _).1, (hs false _).2, c2⟩⟩

/-- **`G3ZqResclRegStmt` from the choice-regularity node.** -/
theorem g3ZqResclRegStmt_of_choice (h : G3ZqSChoiceUStmt) : G3ZqResclRegStmt :=
  g3ZqResclRegStmt_of_regU (g3ZqSRegUStmt_of_choice h)

end G3ZqS
end Thm18Asm
end QuantumZipper
