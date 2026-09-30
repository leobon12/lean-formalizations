import QuantumZipper.Proofs.Thm18.G3ZrWire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-REG (5): the curve Fubini formulas under the area-only window regularity

Copies of `G3Z2b2.g1Inner_eq_g1PhiM`, `g1zWedgePalmInt_fubini`, `g3Inner_eq_g3PhiM2` and
`g3zWedgePalmCyl_fubini` with `G1FacReg` replaced by the weaker `G1FacRegA` (D89 form, see
`G3ZrWire`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zr

open G3Z2b2 D3Plus Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- **The inner Palm-window integral through the curve maps is the measurable functional**
(area-only regularity). -/
theorem g1Inner_eq_g1PhiMA {γ : ℝ} (hγ : 0 < γ) (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool)
    (hN : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left)
      (uniformizer (sideDom (pathTrace (γ ^ 2) a) left)))
    {y : FieldSample} (hy : IsLQGGood γ y) (U L : ℝ) (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    (hreg : ∀ᵐ x ∂(qBoundaryMeasure γ y), x ∈ g1zWedgeWin γ left y U →
      G1FacRegA γ L Ψ left y a x) :
    ∫⁻ x in g1zWedgeWin γ left y U,
        Γ (locFieldFull R (canonical γ
          (zoomFieldVia γ L y x (g1zLocMap left (pathDrive (γ ^ 2) a) x))))
        ∂((qBoundaryMeasure γ y).restrict (g1SideHalf left)) =
      g1PhiM γ L R Γ Ψ left U (y, a) := by
  classical
  obtain ⟨c, hc, hloc⟩ := g1zLocMap_eq_g3locM hsel hac hs left hN
  have hbM : bdryM γ y = qBoundaryMeasure γ y := by
    unfold bdryM; rw [if_pos (G4Core.bCert_of_isLQGGood hy)]
  have hhalf : MeasurableSet (g1SideHalf left) := by
    cases left
    · exact measurableSet_Ioi
    · exact measurableSet_Iio
  have hwin := measurableSet_g1zWedgeWin γ left y U
  unfold g1PhiM
  rw [hbM, Measure.restrict_restrict hwin, ← lintegral_indicator (hwin.inter hhalf)]
  refine lintegral_congr_ae ?_
  filter_upwards [hreg] with x hrx
  have hmem : x ∈ g1zWedgeWin γ left y U ↔
      (x ∈ g1SideHalf left ∧ qBoundaryMeasure γ y (g1SideSeg left x) ≤ ENNReal.ofReal U) :=
    Iff.rfl
  by_cases hx : x ∈ g1zWedgeWin γ left y U
  · have hxh : x ∈ g1SideHalf left := hx.1
    rw [indicator_of_mem (show x ∈ g1zWedgeWin γ left y U ∩ g1SideHalf left from ⟨hx, hxh⟩)]
    simp only [g1IntM, hbM]
    rw [if_pos (hmem.1 hx), locFieldFull_eq_g1zLocData,
      data_zoom_g1zLocMap_eqA hγ hsel hac hs left hc hloc L hxh (hrx hx)]
  · rw [indicator_of_notMem (fun h => hx h.1)]
    simp only [g1IntM, hbM]
    rw [if_neg (fun h => hx (hmem.2 h))]

/-- **Z2a for the wedge Palm-window integral through the curve maps** (area-only regularity). -/
theorem g1zWedgePalmInt_fubiniA (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (hsel : G1PsiSel γ Ψ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' ∧ IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' ∧
      IndepFun X (fun ω t => A t ω) P' ∧
      ∀ (left : Bool) (U L : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞), Measurable Γ →
        (∀ᵐ ω ∂P, ∀ᵐ x ∂(qBoundaryMeasure γ (Y ω)), x ∈ g1zWedgeWin γ left (Y ω) U →
          G1FacRegA γ L Ψ left (Y ω) (pathOf B ω) x) →
        g1zWedgePalmInt γ P B Y left U L R Γ =
          ∫⁻ a, ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeRep γ X A ω', a) ∂P' ∂(P.map (pathOf B)) := by
  have hγ : 0 < γ := hS.1
  have hB : IsBrownianReal B P := hS.2.2.1
  obtain ⟨Ω', _, P', hP', X, A, hX, hA, hXA, hfub⟩ := g3PathFubiniStmt_holds γ P B Y hS hIn
  refine ⟨Ω', inferInstance, P', hP', X, A, hX, hA, hXA, fun left U L R Γ hΓ hreg => ?_⟩
  have hG := measurable_g1PhiData hsel L R hΓ left U
  have key := hfub (fun ω => ∫⁻ x in g1zWedgeWin γ left (Y ω) U,
      Γ (locFieldFull R (canonical γ
        (zoomFieldVia γ L (Y ω) x (g1zLocMap left (drive (γ ^ 2) B ω) x))))
      ∂((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf left)))
    (fun p : G1PathData => g1PhiM γ L R Γ Ψ left U (E1.fromC p.2.1, p.1)) hG ?_
  · unfold g1zWedgePalmInt
    rw [key]
    refine lintegral_congr fun a => lintegral_congr fun ω' => ?_
    exact g1PhiM_fromC _ _
  · filter_upwards [hreg, hIn.1, hIn.2.2, hB.cont] with ω hr hgood hin hc
    rw [g1PhiM_fromC]
    obtain ⟨hsc, -, hNl, hNr⟩ := hin
    have hN : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left)
        (uniformizer (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left)) := by
      cases left
      · exact hNr
      · exact hNl
    exact g1Inner_eq_g1PhiMA hγ hsel hc hsc left hN hgood.1 U L R Γ hr

/-- The area-only regularity conditions of the joint integrand at the left window point `x`. -/
def G3FacRegA (γ L : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (y : FieldSample) (a : ℝ≥0 → ℝ)
    (x : ℝ) : Prop :=
  G1FacRegA γ L Ψ true y a x ∧ 0 < R18.g3zPartner γ y x ∧
    G1FacRegA γ L Ψ false y a (R18.g3zPartner γ y x)

/-- **The inner joint Palm-window integral is the measurable functional** (area-only). -/
theorem g3Inner_eq_g3PhiM2A {γ : ℝ} (hγ : 0 < γ) (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ}
    (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a))
    (hNl : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) true)
      (uniformizer (sideDom (pathTrace (γ ^ 2) a) true)))
    (hNr : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) false)
      (uniformizer (sideDom (pathTrace (γ ^ 2) a) false)))
    {y : FieldSample} (hy : IsLQGGood γ y) (U L : ℝ) (s t : Set LawD)
    (hreg : ∀ᵐ x ∂(qBoundaryMeasure γ y), x ∈ g1zWedgeWin γ true y U →
      G3FacRegA γ L Ψ y a x) :
    ∫⁻ x in g1zWedgeWin γ true y U,
        s.indicator 1 (WedgeMeas.dataFull H (canonical γ
          (zoomFieldVia γ L y x (g1zLocMap true (pathDrive (γ ^ 2) a) x)))) *
        t.indicator 1 (WedgeMeas.dataFull H (canonical γ
          (zoomFieldVia γ L y (R18.g3zPartner γ y x)
            (g1zLocMap false (pathDrive (γ ^ 2) a) (R18.g3zPartner γ y x)))))
        ∂((qBoundaryMeasure γ y).restrict (g1SideHalf true)) =
      g3PhiM2 γ L Ψ U s t (y, a) := by
  classical
  obtain ⟨c, hc, hloc⟩ := g1zLocMap_eq_g3locM hsel hac hs true hNl
  obtain ⟨c', hc', hloc'⟩ := g1zLocMap_eq_g3locM hsel hac hs false hNr
  have hbM : bdryM γ y = qBoundaryMeasure γ y := by
    unfold bdryM; rw [if_pos (G4Core.bCert_of_isLQGGood hy)]
  have hhalf : MeasurableSet (g1SideHalf true) := measurableSet_Iio
  have hwin := measurableSet_g1zWedgeWin γ true y U
  unfold g3PhiM2
  rw [hbM, Measure.restrict_restrict hwin, ← lintegral_indicator (hwin.inter hhalf)]
  refine lintegral_congr_ae ?_
  filter_upwards [hreg] with x hrx
  have hmem : x ∈ g1zWedgeWin γ true y U ↔
      (x ∈ g1SideHalf true ∧ qBoundaryMeasure γ y (g1SideSeg true x) ≤ ENNReal.ofReal U) :=
    Iff.rfl
  have hpart : partM γ y x = R18.g3zPartner γ y x := by simp only [partM, R18.g3zPartner, hbM]
  by_cases hx : x ∈ g1zWedgeWin γ true y U
  · have hxh : x ∈ g1SideHalf true := hx.1
    rw [indicator_of_mem (show x ∈ g1zWedgeWin γ true y U ∩ g1SideHalf true from ⟨hx, hxh⟩)]
    simp only [g3IntM2, hbM]
    rw [if_pos (hmem.1 hx), hpart]
    obtain ⟨h1, hp, h2⟩ := hrx hx
    have hph : R18.g3zPartner γ y x ∈ g1SideHalf false := by simpa [g1SideHalf] using hp
    rw [data_zoom_g1zLocMap_eqA hγ hsel hac hs true hc hloc L hxh h1,
      data_zoom_g1zLocMap_eqA hγ hsel hac hs false hc' hloc' L hph h2]
  · rw [indicator_of_notMem (fun h => hx h.1)]
    simp only [g3IntM2, hbM]
    rw [if_neg (fun h => hx (hmem.2 h))]

/-- **Z2a for the joint Palm-window integral of `G3TCurveStmt`** (area-only regularity). -/
theorem g3zWedgePalmCyl_fubiniA (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (hsel : G1PsiSel γ Ψ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' ∧ IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' ∧
      IndepFun X (fun ω t => A t ω) P' ∧
      ∀ (U L : ℝ) (s t : Set LawD), MeasurableSet s → MeasurableSet t →
        (∀ᵐ ω ∂P, ∀ᵐ x ∂(qBoundaryMeasure γ (Y ω)), x ∈ g1zWedgeWin γ true (Y ω) U →
          G3FacRegA γ L Ψ (Y ω) (pathOf B ω) x) →
        R18.g3zWedgePalmCyl γ P B Y U L s t =
          ∫⁻ a, ∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeRep γ X A ω', a) ∂P' ∂(P.map (pathOf B)) := by
  have hγ : 0 < γ := hS.1
  have hB : IsBrownianReal B P := hS.2.2.1
  obtain ⟨Ω', _, P', hP', X, A, hX, hA, hXA, hfub⟩ := g3PathFubiniStmt_holds γ P B Y hS hIn
  refine ⟨Ω', inferInstance, P', hP', X, A, hX, hA, hXA, fun U L s t hs ht hreg => ?_⟩
  have hG := measurable_g3PhiData2 hsel L U hs ht
  have key := hfub (fun ω => ∫⁻ x in g1zWedgeWin γ true (Y ω) U,
      s.indicator 1 (WedgeMeas.dataFull H (canonical γ
        (zoomFieldVia γ L (Y ω) x (g1zLocMap true (drive (γ ^ 2) B ω) x)))) *
      t.indicator 1 (WedgeMeas.dataFull H (canonical γ
        (zoomFieldVia γ L (Y ω) (R18.g3zPartner γ (Y ω) x)
          (g1zLocMap false (drive (γ ^ 2) B ω) (R18.g3zPartner γ (Y ω) x)))))
      ∂((qBoundaryMeasure γ (Y ω)).restrict (g1SideHalf true)))
    (fun p : G1PathData => g3PhiM2 γ L Ψ U s t (E1.fromC p.2.1, p.1)) hG ?_
  · unfold R18.g3zWedgePalmCyl
    rw [key]
    refine lintegral_congr fun a => lintegral_congr fun ω' => ?_
    exact g3PhiM2_fromC _ _
  · filter_upwards [hreg, hIn.1, hIn.2.2, hB.cont] with ω hr hgood hin hc
    rw [g3PhiM2_fromC]
    obtain ⟨hsc, -, hNl, hNr⟩ := hin
    exact g3Inner_eq_g3PhiM2A hγ hsel hc hsc hNl hNr hgood.1 U L s t hr

end G3Zr
end Thm18Asm
end QuantumZipper
