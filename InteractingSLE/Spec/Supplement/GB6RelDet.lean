/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RelDetGood

/-!
# GB6's (Det): the hull-identity clause alone

Packet PROVE-GB6-RELDET. `GB6RelDetStatement` (PROVE-GB6-RESTART) = the good-code clause (proved unconditionally in
`GB6RelDetGood`, `ae_isGoodDrvCode_gb6`) and the hull identity before the first contact. This file states the hull
identity alone and wires it through PROVE-GB6-RESTART's and PROVE-GB6D's reductions:

* **`GB6HullDetStatement`**: binders of `GB6RelDetStatement` verbatim; conclusion its hull-identity clause;
* **`gb6RelDetStatement_of_hullDet`**: `GB6HullDetStatement → GB6RelDetStatement`;
* `gb6CondDetStatement_of_hullDet`, `gb6RestartStatement_of_hullDet`, `gb6FirstContactStatement_of_hullDet`.

Nothing here uses Theorem 1.2/1.3 except where PROVE-GB6D's reduction already takes them as hypotheses (GB6 serves
Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec2.Assembly Exist.Staged Exist.StagedLaw Sec7.StripSysField

/-- **Named input: GB6's (Det), the hull identity alone** (supplement p. 519–520; Astra's follow-up 3, Q3 §§3.2–3.7).
Binders of `GB6RelDetStatement` verbatim. Almost surely on `{s < ζα, α(s) ∈ ℍ}`, before the first contact `T_c` of the
physical counterflow with `α([0, s])`, the decoded canonical driver code of the conditional field, `β = gb6Word κ θ c s
Wα`, generates the chart images `Ψ(K'_t)` of the physical counterflow hulls in the relative clock. (The other clause of
`GB6RelDetStatement`, the good code, is `ae_isGoodDrvCode_gb6`.) -/
def GB6HullDetStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode (16 / κ) 0 F →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (gb6Word κ θ c s (fun t => Wα t ω), Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) =
            relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t

/-- **`GB6RelDetStatement` from the hull identity alone**: its good-code clause is `ae_isGoodDrvCode_gb6`. -/
theorem gb6RelDetStatement_of_hullDet (hD : GB6HullDetStatement.{u}) : GB6RelDetStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc F hF c hcJ hcb
  have hgood := ae_isGoodDrvCode_gb6 (θ := θ) hκ hb hG hfl hα s hHcm hHc hF hcb
  have hhull := hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl
    hα s Hc hHcm hHc F hF c hcJ hcb
  filter_upwards [hgood, hhull] with ω h1 h2 hs hsH
  exact ⟨h1 hs hsH, h2 hs hsH⟩

/-- GB6's step (d) from the hull identity alone. -/
theorem gb6CondDetStatement_of_hullDet (hD : GB6HullDetStatement.{u}) : GB6CondDetStatement.{u} :=
  gb6CondDetStatement_of_relDet (gb6RelDetStatement_of_hullDet hD)

/-- **GB6's conditional-law half** from the hull identity alone (conditional helper; PROVE-GB6D's inputs). -/
theorem gb6RestartStatement_of_hullDet (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hC : CompleteSixteenDivStatement) (hD : GB6HullDetStatement.{u}) :
    GB6RestartStatement.{u} :=
  gb6RestartStatement_of_relDet h12p h13 hC (gb6RelDetStatement_of_hullDet hD)

/-- **GB6's first-contact assertion** from the hull identity alone (conditional helper). -/
theorem gb6FirstContactStatement_of_hullDet (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hC : CompleteSixteenDivStatement) (hD : GB6HullDetStatement.{u}) :
    GB6FirstContactStatement.{u} :=
  gb6FirstContactStatement_of_relDet h12p h13 hC (gb6RelDetStatement_of_hullDet hD)

end GB6

end Supp8

end InteractingSLE
