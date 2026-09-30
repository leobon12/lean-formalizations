import QuantumZipper.Proofs.Thm18.G3ZqL3PathU

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-G1 (1): the one-point Palm limit needs only ONE small window

`G1WedgePalmLimStmt` (G3ZcFormat) asks, for every `ε > 0`, for SOME window length `U > 0` with
the normalized Palm-window integral eventually `ε`-close to the `γ`-wedge value. The fixed-path
node `G3ZqL.G3ZqL1PathUStmt` (G3ZqL3PathU) asks the exact limit for EVERY `U`, which needs the
Palm identity of the wedge boundary measure on windows reaching outside the unit disc (obstacle
(i) of G1-ZOOM). Here we record the weaker node that the consumer really needs:

* `G3ZqO1PathEpsStmt`: for every `ε > 0` there is `U > 0` (chosen before the path) such that for
  a.e. path the normalized fixed-path functional of the unscaled wedge is eventually `ε`-close to
  the wedge value;
* `g3ZqO1PathEpsStmt_of_pathU : G3ZqL1PathUStmt → G3ZqO1PathEpsStmt` (it is weaker);
* `eventually_lintegral_near`: dominated convergence for a family bounded by `1` that is a.e.
  eventually `e`-close to a constant (two-sided, `ℝ≥0∞`; own elementary proof);
* **`g1WedgePalmLimStmt_of_pathEps : G3ZqL1ResclIdStmt → G3ZqO1PathEpsStmt →
  G1WedgePalmLimStmt`** (copy of `G3ZqL.g1WedgePalmLimStmt_of_pathU` with the window `U` of the
  node).

Sheffield, arXiv:1012.4797, pp. 70–71 (the window is a segment of quantum length `U`; any `U`
works, and small `U` keeps the window inside the unit half-disc with high probability).
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqO

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL Factorization

/-- **The fixed-path one-point Palm limit of the unscaled wedge, at one small window.** -/
def G3ZqO1PathEpsStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Y'' : Ω'' → FieldSample), IsQuantumWedge γ γ Y'' P'' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ left : Bool,
  ∀ (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞), Measurable Γ → (∀ y, Γ y ≤ 1) →
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ U : ℝ, 0 < U ∧
  ∀ᵐ a ∂(P.map (pathOf B)), Continuous a → IsSimpleChord (pathTrace (γ ^ 2) a) →
    ∀ᶠ L in atTop,
      (ENNReal.ofReal U)⁻¹ * ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) ∂P' ≤
          ∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'' + ε ∧
        ∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'' ≤
          (ENNReal.ofReal U)⁻¹ * ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) ∂P' + ε

/-- **Dominated convergence towards a constant, two-sided, in `ℝ≥0∞`.** -/
theorem eventually_lintegral_near {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {F : ℝ → α → ℝ≥0∞} (hFm : ∀ L, AEMeasurable (F L) μ)
    (hF1 : ∀ L a, F L a ≤ 1) {c e : ℝ≥0∞} (hc : c ≤ 1) (he : 0 < e) (he1 : e ≤ 1)
    (h : ∀ᵐ a ∂μ, ∀ᶠ L in (atTop : Filter ℝ), F L a ≤ c + e ∧ c ≤ F L a + e) :
    ∀ᶠ L in (atTop : Filter ℝ), ∫⁻ a, F L a ∂μ ≤ c + e + e ∧ c ≤ ∫⁻ a, F L a ∂μ + e + e := by
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hc
  have het : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top he1
  -- upper bound through `max (F L) (c + e)`
  set g : ℝ → α → ℝ≥0∞ := fun L a => max (F L a) (c + e) with hg
  have hgl : Tendsto (fun L => ∫⁻ a, g L a ∂μ) atTop (𝓝 (∫⁻ _a, (c + e) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => 1 + (c + e))
      (Eventually.of_forall fun L => (hFm L).max aemeasurable_const)
      (Eventually.of_forall fun L => Eventually.of_forall fun a =>
        max_le ((hF1 L a).trans le_self_add) le_add_self) (by simp [hct, het]) ?_
    filter_upwards [h] with a ha
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ha] with L hL
    exact (max_eq_right hL.1).symm
  rw [lintegral_const, measure_univ, mul_one] at hgl
  have hcet : c + e ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hct, het⟩
  -- lower bound through `min (F L + e) c`
  set k : ℝ → α → ℝ≥0∞ := fun L a => min (F L a + e) c with hk
  have hkl : Tendsto (fun L => ∫⁻ a, k L a ∂μ) atTop (𝓝 (∫⁻ _a, c ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => c)
      (Eventually.of_forall fun L => ((hFm L).add aemeasurable_const).min aemeasurable_const)
      (Eventually.of_forall fun L => Eventually.of_forall fun a => min_le_right _ _)
      (by simp [hct]) ?_
    filter_upwards [h] with a ha
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ha] with L hL
    exact (min_eq_right hL.2).symm
  rw [lintegral_const, measure_univ, mul_one] at hkl
  filter_upwards [(ENNReal.tendsto_nhds hcet).1 hgl e he, (ENNReal.tendsto_nhds hct).1 hkl e he]
    with L hL1 hL2
  constructor
  · calc ∫⁻ a, F L a ∂μ ≤ ∫⁻ a, g L a ∂μ := lintegral_mono fun a => le_max_left _ _
      _ ≤ c + e + e := hL1.2
  · have h2 : c ≤ ∫⁻ a, k L a ∂μ + e := tsub_le_iff_right.1 hL2.1
    have h3 : ∫⁻ a, k L a ∂μ ≤ ∫⁻ a, F L a ∂μ + e := by
      calc ∫⁻ a, k L a ∂μ ≤ ∫⁻ a, (F L a + e) ∂μ := lintegral_mono fun a => min_le_left _ _
        _ = ∫⁻ a, F L a ∂μ + e := by
            rw [lintegral_add_right' _ aemeasurable_const, lintegral_const, measure_univ,
              mul_one]
    calc c ≤ ∫⁻ a, k L a ∂μ + e := h2
      _ ≤ ∫⁻ a, F L a ∂μ + e + e := add_le_add h3 le_rfl

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **`G1WedgePalmLimStmt` from the rescaling identity and the one-window fixed-path limit.** -/
theorem g1WedgePalmLimStmt_of_pathEps (hId : G3ZqL1ResclIdStmt) (hpath : G3ZqO1PathEpsStmt) :
    G1WedgePalmLimStmt := by
  have hZ2 : G1Z2SideGoodStmt := g1Z2SideGoodStmt_of_area
    (g1Z2SideAreaStmt_of_sel (g1Z2SideAreaSelStmt_of_top G1Top.g1Z2SideTopSelStmt_holds))
  intro γ Ω _ P _ B Y hS hIn left R Γ hΓ hΓ1 ε hε
  have hγ : 0 < γ := hS.1
  have hγ2 : γ < 2 := hS.2.1
  have hB : IsBrownianReal B P := hS.2.2.1
  obtain ⟨Ψ, hsel⟩ := g1PsiSelStmt γ hγ hγ2
  obtain ⟨Ω', _, P', hP', X, A, hX, hA, hXA, hfub⟩ :=
    G3Zr.g1zWedgePalmInt_fubiniA γ P B Y hS hIn hsel
  obtain ⟨Ω'', _, P'', Y'', -, hP'', hW, -, -⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond (γ := γ) (α := γ) (gamma_lt_Qc hγ hγ2)
  set e : ℝ≥0∞ := min ε 1 / 2 with he
  have he0 : 0 < e := ENNReal.half_pos (lt_min hε one_pos).ne'
  have he1 : e ≤ 1 := (ENNReal.half_le_self).trans (min_le_right _ _)
  have hee : e + e ≤ ε := by
    rw [he, ENNReal.add_halves]; exact min_le_left _ _
  obtain ⟨U, hU, hpathU⟩ := hpath γ hγ hγ2 Ψ hsel P' X A hX hA hXA P'' Y'' hW P B hB left R Γ
    hΓ hΓ1 e he0
  refine ⟨U, hU, Ω'', inferInstance, P'', Y'', hP'', hW, ?_⟩
  set c := ∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'' with hc
  have hc1 : c ≤ 1 := by
    calc c ≤ ∫⁻ _ω'', (1 : ℝ≥0∞) ∂P'' := lintegral_mono fun ω'' => hΓ1 _
      _ = 1 := by simp
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hS.2.2.2.1.1, Ω', inferInstance, P', X, A, hP', hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  have hcu : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P' :=
    WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  set Gu : ℝ → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun L a =>
    (ENNReal.ofReal U)⁻¹ * ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) ∂P' with hGdef
  have hGmeas : ∀ L, Measurable (Gu L) := fun L =>
    (measurable_g1PhiM_wedgeU hsel L R hΓ left U hcu).const_mul _
  have hUt : ENNReal.ofReal U ≠ 0 := by simpa using hU
  have hG1 : ∀ L a, Gu L a ≤ 1 := by
    intro L a
    have hle : ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) ∂P' ≤ ENNReal.ofReal U := by
      calc ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) ∂P'
          ≤ ∫⁻ _ω', ENNReal.ofReal U ∂P' := lintegral_mono fun ω' => g1PhiM_le hΓ1 left U _
        _ = ENNReal.ofReal U := by simp
    calc Gu L a ≤ (ENNReal.ofReal U)⁻¹ * ENNReal.ofReal U := mul_le_mul' le_rfl hle
      _ = 1 := ENNReal.inv_mul_cancel hUt ENNReal.ofReal_ne_top
  have hgm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have hsc : ∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω)) := by
    filter_upwards [hIn.2.2] with ω h
    exact h.1
  have hI : ∀ L, (ENNReal.ofReal U)⁻¹ * g1zWedgePalmInt γ P B Y left U L R Γ =
      ∫⁻ ω, Gu L (pathOf B ω) ∂P := by
    intro L
    rw [hfub left U L R Γ hΓ ((G3Zr.ae_g1FacRegA hZ2 γ P B Y hS hIn hsel left L).mono
      fun ω h => Eventually.of_forall fun x hx => h x hx.1)]
    rw [lintegral_path_rescale hB (measurable_g1PhiM hsel L R hΓ left U)
      (aemeasurable_g1PhiM_wedgeRep_prod hsel L R hΓ left U hm _)
      (aemeasurable_g1PhiM_wedgeU_prod hsel L R hΓ left U hcu _)
      (hId γ hγ hγ2 Ψ hsel P' X A hX hA hXA P B hB hsc left U L R Γ hΓ)]
    rw [lintegral_map' ((measurable_g1PhiM_wedgeU hsel L R hΓ left U hcu).aemeasurable) hgm,
      ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hUt)]
  have hae : ∀ᵐ ω ∂P, ∀ᶠ L in (atTop : Filter ℝ),
      Gu L (pathOf B ω) ≤ c + e ∧ c ≤ Gu L (pathOf B ω) + e := by
    have h1 := ae_of_ae_map hgm hpathU
    filter_upwards [h1, hIn.2.2, hB.cont] with ω hω hin hcont
    obtain ⟨hsc, -, -, -⟩ := hin
    exact hω hcont hsc
  have hev := eventually_lintegral_near (μ := P) (F := fun L ω => Gu L (pathOf B ω))
    (fun L => (hGmeas L).comp_aemeasurable hgm) (fun L ω => hG1 L _) hc1 he0 he1 hae
  filter_upwards [hev] with L hL
  rw [hI L]
  constructor
  · calc ∫⁻ ω, Gu L (pathOf B ω) ∂P ≤ c + e + e := hL.1
      _ = c + (e + e) := add_assoc _ _ _
      _ ≤ c + ε := add_le_add le_rfl hee
  · calc c ≤ ∫⁻ ω, Gu L (pathOf B ω) ∂P + e + e := hL.2
      _ = ∫⁻ ω, Gu L (pathOf B ω) ∂P + (e + e) := add_assoc _ _ _
      _ ≤ ∫⁻ ω, Gu L (pathOf B ω) ∂P + ε := add_le_add le_rfl hee

end G3ZqO
end Thm18Asm
end QuantumZipper
