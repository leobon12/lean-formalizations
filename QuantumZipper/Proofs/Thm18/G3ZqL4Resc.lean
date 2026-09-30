import QuantumZipper.Proofs.Thm18.G3ZqResc3
import QuantumZipper.Proofs.Thm18.G3ZqL3PathU
import QuantumZipper.Proofs.Thm18.G3ZrRep2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (4): the one-point rescaling identity, area-only, and its a.s. form

* `g1PhiM_canonical_scalePathA`: the area-only (D93) form of `G1Zm.g1PhiM_canonical_scalePath`,
  `g1PhiM (canonical γ W, S_b a) = g1PhiM (W, a)` with `b = scaleParam γ W`, under the regularity
  `G1Zr.G1FacRegA` (canonical field along the scaled path), `DilReg` (dilation) and
  `G3Zq.G3ZqRegU` (unscaled field along the path). One-point copy of
  `G3Zq.g3PhiM2_canonical_scalePath`.
* `g3ZqL1ResclIdStmt_of_reg : G3ZqL1ResclRegStmt → G3ZqL1ResclIdStmt`: the path facts are
  `G3Zq.ae_goodPathF`; the goodness of `wedgeU`, of `wedgeRep` and the positivity of the scale are
  proved a.s. here (`LogSingGood.wedgeRefGoodAS_holds`, `G3Zr.ae_good_wedgeRep`,
  `G1RC.ae_scale_pos`); only the field regularity along the path remains (`G3ZqL1ResclRegStmt`,
  one-point analog of `G3Zq.G3ZqResclRegStmt` without the goodness clauses).

Sheffield, arXiv:1012.4797, p. 70 (independent curve, SLE scale invariance). Own bookkeeping
(AGENT_GUIDE cost rule), following G3ZqResc2/G3ZqResc3.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Complex
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open G3Z2b2 G1Zm D3Plus G3Zq

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **The one-point rescaling identity along a fixed path, area-only regularity.** -/
theorem g1PhiM_canonical_scalePathA {γ : ℝ} (hγ : 0 < γ) (hsel : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a))
    (hWd : Continuous (pathDrive (γ ^ 2) a)) (hW0 : pathDrive (γ ^ 2) a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive (γ ^ 2) a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (left : Bool) {W : FieldSample} (hWg : IsLQGGood γ W) (hb : 0 < scaleParam γ W)
    (hac' : Continuous (scalePath (scaleParam γ W) a))
    (hs' : IsSimpleChord (pathTrace (γ ^ 2) (scalePath (scaleParam γ W) a)))
    (hN' : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ W) a)) left)
      (uniformizer (sideDom (pathTrace (γ ^ 2) (scalePath (scaleParam γ W) a)) left)))
    (hy : IsLQGGood γ (canonical γ W)) (U L : ℝ) (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    (hreg1 : ∀ᵐ x ∂(qBoundaryMeasure γ (canonical γ W)),
      x ∈ g1zWedgeWin γ left (canonical γ W) U →
        G3Zr.G1FacRegA γ L Ψ left (canonical γ W) (scalePath (scaleParam γ W) a) x)
    (hdil : ∀ x ∈ g1SideHalf left,
      DilReg γ W (scaleParam γ W) x
        (g1zLocMap left (pathDrive (γ ^ 2) (scalePath (scaleParam γ W) a)) (x / scaleParam γ W)))
    (hreg3 : ∀ᵐ x ∂(qBoundaryMeasure γ W), x ∈ g1zWedgeWin γ left W U →
      G3ZqRegU γ L Ψ left W a x) :
    g1PhiM γ L R Γ Ψ left U (canonical γ W, scalePath (scaleParam γ W) a) =
      g1PhiM γ L R Γ Ψ left U (W, a) := by
  classical
  set b := scaleParam γ W with hbdef
  rw [← G3Zr.g1Inner_eq_g1PhiMA hγ hsel hac' hs' left hN' hy U L R Γ hreg1]
  have e : canonical γ W = rescale W (Qc γ) b := rfl
  have hmeas : ∀ x, Measurable (g1zLocMap left (pathDrive (γ ^ 2) (scalePath b a)) x) :=
    fun x => (G0Map.measurable_g1zLocMap (W := pathDrive (γ ^ 2) (scalePath b a)) hs' hN').comp
      (measurable_const.prodMk measurable_id)
  rw [e, wedgePalm_rescale hγ hWg hb left U L R Γ _ hmeas hdil]
  obtain ⟨c, hc, hloc'⟩ := g1zLocMap_eq_g3locM hsel hac' hs' left hN'
  obtain ⟨μ, hμ, hsc⟩ := g3locM_scalePath hsel hb hac hs hac' hs' hWd hW0 hex left
  have hbM : bdryM γ W = qBoundaryMeasure γ W := by
    unfold bdryM; rw [if_pos (G4Core.bCert_of_isLQGGood hWg)]
  have hhalf : MeasurableSet (g1SideHalf left) := by
    cases left
    · exact measurableSet_Ioi
    · exact measurableSet_Iio
  have hwin := measurableSet_g1zWedgeWin γ left W U
  unfold g1PhiM
  rw [hbM, Measure.restrict_restrict hwin, ← lintegral_indicator (hwin.inter hhalf)]
  refine lintegral_congr_ae ?_
  filter_upwards [hreg3] with x hrx
  by_cases hx : x ∈ g1zWedgeWin γ left W U
  · have hxh : x ∈ g1SideHalf left := hx.1
    rw [indicator_of_mem (show x ∈ g1zWedgeWin γ left W U ∩ g1SideHalf left from ⟨hx, hxh⟩)]
    simp only [g1IntM, hbM]
    rw [if_pos (show x ∈ g1SideHalf left ∧
      qBoundaryMeasure γ W (g1SideSeg left x) ≤ ENNReal.ofReal U from hx)]
    rw [locFieldFull_eq_g1zLocData,
      data_dil_scalePath_eq hγ hsel hac hs left hb hc hμ hloc' hsc W L hxh (hrx hx)]
  · rw [indicator_of_notMem (fun h => hx h.1)]
    simp only [g1IntM, hbM]
    rw [if_neg (show ¬(x ∈ g1SideHalf left ∧
      qBoundaryMeasure γ W (g1SideSeg left x) ≤ ENNReal.ofReal U) from hx)]

/-- The field regularity (area-only, D93) of an unscaled field `W` and a path `a` used by the
one-point rescaling identity on side `left` at window `U` and level `L`. -/
def G3ZqL1FieldReg (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (W : FieldSample)
    (a : ℝ≥0 → ℝ) (U L : ℝ) : Prop :=
  (∀ᵐ x ∂(qBoundaryMeasure γ (canonical γ W)),
      x ∈ g1zWedgeWin γ left (canonical γ W) U →
        G3Zr.G1FacRegA γ L Ψ left (canonical γ W) (scalePath (scaleParam γ W) a) x) ∧
    (∀ x ∈ g1SideHalf left,
      DilReg γ W (scaleParam γ W) x
        (g1zLocMap left (pathDrive (γ ^ 2) (scalePath (scaleParam γ W) a))
          (x / scaleParam γ W))) ∧
    (∀ᵐ x ∂(qBoundaryMeasure γ W), x ∈ g1zWedgeWin γ left W U →
      G3ZqRegU γ L Ψ left W a x)

/-- **Almost-sure field regularity for the one-point rescaling identity (open leaf).** For the
wedge representative and an independent Brownian motion: a.s. in the field, a.s. in the Brownian
sample, the conditions `G3ZqL1FieldReg` hold along its path. -/
def G3ZqL1ResclRegStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    (∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) →
  ∀ (left : Bool) (U L : ℝ), ∀ᵐ ω' ∂P',
    ∀ᵐ ω ∂P, G3ZqL1FieldReg γ Ψ left (wedgeU γ X A ω') (pathOf B ω) U L

/-- **`G3ZqL1ResclIdStmt` from the a.s. field regularity along the path.** -/
theorem g3ZqL1ResclIdStmt_of_reg (h : G3ZqL1ResclRegStmt) : G3ZqL1ResclIdStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω _ P _ B hB hsc left U L R Γ hΓ
  have hgm : AEMeasurable (pathOf B) P := IsBrownianReal.aemeasurable_pathOf hB
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  filter_upwards [h γ hγ hγ2 Ψ hsel P' X A hX hA hXA P B hB hsc left U L,
    G1RC.ae_scale_pos hγ hγ2 hX hA hXA,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hαQ Ω' _ P' X A inferInstance hX hA hXA,
    G3Zr.ae_good_wedgeRep hγ hγ2 hX hA hXA] with ω' hae hb hWg hy
  refine ⟨hb, ?_⟩
  set b := scaleParam γ (wedgeU γ X A ω') with hbdef
  have hm1 : Measurable fun a : ℝ≥0 → ℝ =>
      g1PhiM γ L R Γ Ψ left U (wedgeRep γ X A ω', scalePath b a) :=
    (measurable_g1PhiM hsel L R hΓ left U).comp
      (measurable_const.prodMk (measurable_scalePath b))
  have hm2 : Measurable fun a : ℝ≥0 → ℝ => g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) :=
    (measurable_g1PhiM hsel L R hΓ left U).comp (measurable_const.prodMk measurable_id)
  refine (ae_map_iff hgm (measurableSet_eq_fun hm1 hm2)).2 ?_
  filter_upwards [hae, ae_goodPathF hγ hγ2 hB hsc] with ω ⟨hreg1, hdil, hreg3⟩ hgood
  obtain ⟨hac, hs', hWd, hW0, hex⟩ := hgood
  have hsb : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b (pathOf B ω))) :=
    isSimpleChord_scalePath hb _ hWd hW0 hex hs'
  exact g1PhiM_canonical_scalePathA hγ hsel hac hs' hWd hW0 hex left hWg hb
    (continuous_scalePath hac) hsb (G1ZA1a.isNormalizedUniformizer_sideDom hsb left) hy U L R Γ
    hreg1 hdil hreg3

end G3ZqL
end Thm18Asm
end QuantumZipper
