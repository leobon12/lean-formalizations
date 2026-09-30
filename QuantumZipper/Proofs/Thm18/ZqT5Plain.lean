import QuantumZipper.Proofs.Thm18.ZqT4Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-TYP (5): the plain half of the scheme and `V + logSing` clauses

Off the side half-line the map goodness `g3zMapGdQ` is the plain goodness `g3PlainGd` (the
translated field is good with positive area), which holds at every point for fields with area
goodness: the scheme `B`/`C` fields (`R18.ae_isAreaGood_g3pBField`,
`R18.ae_isAreaGood_g3pField`) and `V + logSing` (`R18.g3pl4_ae_isAreaGood_logSing`). The Palm laws
of the schemes are absolutely continuous with respect to `P ⊗ L₀`, so a.s. statements about the
field hold at `g3pPalmLaw`-a.e. Palm pair (`ae_palm_of_ae`). Hence the two remaining clauses of
`G3ZqTMapTypFStmt` reduce to their side-half-line parts, the local area `LocAreaQ` of the
pulled-back field at typical side points: `G3ZqTSchemeSideStmt`, `G3ZqTVSideStmt`.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqT

open G1Zm G3Zq G3Z2b2 G3ZqL R18

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- Map goodness from area goodness and the side-half-line local area. -/
theorem gdQ_of_area {γ : ℝ} {side : Bool} {a : ℝ≥0 → ℝ} {y : FieldSample} {x : ℝ}
    (hA : IsAreaGood γ y) (hL : x ∈ g1SideHalf side → LocAreaQ γ (g3zqPull γ Ψ side a y x)) :
    g3zMapGdQ γ Ψ side a y x := by
  unfold g3zMapGdQ
  split_ifs with h
  · exact hL h
  · exact ⟨(hA.translate x).1, fun q hq => pos_areaProxy_of_isAreaGood (hA.translate x) hq⟩

/-- A.s. statements about the field hold at a.e. Palm pair of a scheme. -/
theorem ae_palm_of_ae {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} {q : gffBase.Ω → Prop}
    (h : ∀ᵐ ω ∂gffBase.P, q ω) : ∀ᵐ p ∂(g3pPalmLaw γ g i), q p.1 :=
  (withDensity_absolutelyContinuous _ _).ae_le (Measure.quasiMeasurePreserving_fst.ae h)

/-- **Node (scheme clause, side half-line part).** -/
def G3ZqTSchemeSideStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ᵐ a ∂(P.map (pathOf B)), G3ZqGoodPathF γ a →
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wCut γ i.η) i),
      g3pX γ (g3wCut γ i.η) i p ∈ g1SideHalf true →
      LocAreaQ γ (g3zqPull γ Ψ true a (g3pField γ (g3wCut γ i.η) p.1) (g3pX γ (g3wCut γ i.η) i p))) ∧
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wProf γ) i),
      g3pX γ (g3wProf γ) i p ∈ g1SideHalf true →
      LocAreaQ γ (g3zqPull γ Ψ true a (g3pField γ (g3wProf γ) p.1) (g3pX γ (g3wProf γ) i p))) ∧
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wCut γ i.η) i),
      g3pR γ (g3wCut γ i.η) i p ∈ g1SideHalf false →
      LocAreaQ γ (g3zqPull γ Ψ false a (g3pField γ (g3wCut γ i.η) p.1)
        (g3pR γ (g3wCut γ i.η) i p))) ∧
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wProf γ) i),
      g3pR γ (g3wProf γ) i p ∈ g1SideHalf false →
      LocAreaQ γ (g3zqPull γ Ψ false a (g3pField γ (g3wProf γ) p.1) (g3pR γ (g3wProf γ) i p)))

/-- **Node (`V + logSing` clause, side half-line part).** -/
def G3ZqTVSideStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
  ∀ᵐ a ∂(P.map (pathOf B)), G3ZqGoodPathF γ a →
    ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
      (V : Ω'' → FieldSample), IsFreeGFFModConstH V P'' →
      (∀ᵐ ω ∂P'', V ω (foldedCircle 0 1) = 0) →
      ∀ᵐ ω ∂P'', ∀ᵐ x ∂(qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))),
        (x ∈ g1SideHalf true →
          LocAreaQ γ (g3zqPull γ Ψ true a (V ω + F2.logSingField (γ ^ 2)) x)) ∧
        (g3zPartner γ (V ω + F2.logSingField (γ ^ 2)) x ∈ g1SideHalf false →
          LocAreaQ γ (g3zqPull γ Ψ false a (V ω + F2.logSingField (γ ^ 2))
            (g3zPartner γ (V ω + F2.logSingField (γ ^ 2)) x)))

theorem g3ZqTSchemeStmt_of_side (h : G3ZqTSchemeSideStmt) : G3ZqTSchemeStmt := by
  intro γ hγ hγ2 Ψ hsel Ω _ P _ B hB
  filter_upwards [h γ hγ hγ2 Ψ hsel P B hB] with a ha hg
  obtain ⟨h1, h2, h3, h4⟩ := ha hg
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · filter_upwards [h1 i, ae_palm_of_ae (ae_isAreaGood_g3pBField hγ hγ2 i.2.1)] with p hp hA
    exact gdQ_of_area hA hp
  · filter_upwards [h2 i, ae_palm_of_ae (ae_isAreaGood_g3pField hγ hγ2)] with p hp hA
    exact gdQ_of_area hA hp
  · filter_upwards [h3 i, ae_palm_of_ae (ae_isAreaGood_g3pBField hγ hγ2 i.2.1)] with p hp hA
    exact gdQ_of_area hA hp
  · filter_upwards [h4 i, ae_palm_of_ae (ae_isAreaGood_g3pField hγ hγ2)] with p hp hA
    exact gdQ_of_area hA hp

theorem g3ZqTVStmt_of_side (h : G3ZqTVSideStmt) : G3ZqTVStmt := by
  intro γ hγ hγ2 Ψ hsel Ω _ P _ B hB
  filter_upwards [h γ hγ hγ2 Ψ hsel P B hB] with a ha hg Ω'' _ P'' _ V hV hV0
  filter_upwards [ha hg P'' V hV hV0, g3pl4_ae_isAreaGood_logSing hγ hγ2 hV] with ω hω hA
  filter_upwards [hω] with x hx
  exact ⟨gdQ_of_area hA hx.1, gdQ_of_area hA hx.2⟩

end ZqT
end Thm18Asm
end QuantumZipper
