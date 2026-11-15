/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2FbDual
import InteractingSLE.Spec.Supplement.GW2JointDetFix
import InteractingSLE.Spec.Supplement.RelSafeS2
import InteractingSLE.Spec.Supplement.GW2JDetR4Contact
import InteractingSLE.Spec.Supplement.GW4Completion

/-!
# GW2's joint (Det) from the relative determination of two curves in the common generality of GB6 and GW2

Packet PROVE-GW2-FABLE. GB9, p. 525 and GB6, pp. 519–520. GB6's (Det) (`Supp8.GB6.GB6RelDetStatement`, PROVED from
Theorems 1.2–1.3) and GW2's joint (Det) (`GW2JointKernel.GW2JointDetC2Statement`, open) are the same statement with
the two curves exchanged (`GW2FbDual.lean`). This file states the common generalization and proves the reduction:

* `isChartTransport_own_of_joint`: if `Hc` is `h` read in the joint chart of the counterflow driver (coefficients
  `1, 2πχ(κ), χ(κ)`, R62) and `h′` is the infinity-source transport of `h`, then `Hc` is `h′` read in the
  own-component chart of the counterflow with the dual coefficients `−1, −πχ(16/κ), χ(κ)` — the hypothesis of GB6's
  statement at `16/κ`;
* **`RelDetGenStatement`** (a NAMED STATEMENT, NOT PROVED): GB6's (Det) with
  (A) no `κ < 4`: instead, the retained trace does not return to its base (a hypothesis; Aux. 25 for a flow line,
  `Wire.counterflowNoReturnStatement_of_theorem13` for a counterflow),
  (B) an explored curve of ANY lifetime (no admissibility of its word, no completeness), at an angle `θ′`, with the
  hull identity asserted before the explored lifetime and the first contact;
* **`gw2JointDetC2Statement_of_relDetGen`**: `RelDetGenStatement` (and the counterflow's no-return) imply
  `GW2JointDetC2Statement`, by the substitution `(κ, θ, θ′, h, h′) := (16/κ, 0, θ, h′, h)`.

`RelDetGenStatement` is the exact remaining proposition for GW2's root determination; GB6's proved chain
(`GB6LineL*`, `GB6LMean*`, `RelSafeS*`, `Q3Stop*`) proves its instance `κ < 4`, `θ′ = 0`, complete admissible explored
curve, and the files `GW2Fb{Config, FlowMean, Union, Mean, Local}` are its mean layer in the generality (A)+(B).

Conditional helpers with distinct names; they replace no source theorem. R48: GW2 serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Fb

open Restart Sec2.Assembly Exist.Staged Exist.StagedLaw Sec7.StripSysField Supp8.GB6 GW2JointKernel

/-! ### The chart identity, read backwards -/

/-- **The joint-chart field is the dual own-component chart field.** If `Hc` is `f` read in `jointChart w s` with
`1, 2πχ(κ), χ(κ)` and `f′` is the infinity-source transport of `f`, then `Hc` is `f′` read in the own-component chart
of `w` with the coefficients of `16/κ`. -/
theorem isChartTransport_own_of_joint {κ : ℝ} (hκ : 0 < κ) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {s : ℝ} (hs : 0 ≤ s) {f f' Hc : DistOn upperHalfPlaneOpens}
    (hT : IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) f f')
    (hHc : IsChartTransport (jointChart w s) 1 (specOffset κ) (chiC κ) f Hc) :
    IsChartTransport (ownComponentChart w s) (-1) (-(Real.pi * chiC (16 / κ))) (chiC (16 / (16 / κ))) f' Hc := by
  have hk : (0 : ℝ) < 16 / κ := by positivity
  have e16 : 16 / (16 / κ) = κ := by field_simp
  have hR := Chart.isConformal_infinitySourceChart
  have hL := isConformal_loewner hw hw0 hs
  have hown : (ownComponentChart w s).IsConformal := hL.trans hR
  have hℓR := Chart.continuousOn_infinitySourceChart_lift
  have hℓL := continuousOn_loewner_lift hw hw0 hs
  have hℓown : ContinuousOn (fun z => (ownComponentChart w s).2.2 ((ownComponentChart w s).2.1 z)) H :=
    continuousOn_trans_lift hL hR hℓL hℓR
  have h1 := Supp8.RelSafeS.isChartTransport_own_cfField hk hw hw0 hs f'
  have e : chiC (16 / (16 / κ)) = -1 * chiC (16 / κ) := by
    rw [e16, Sec4.chiC_sixteen_div hκ]
    ring
  have h1' := h1
  rw [e] at h1'
  have h2 := isChartTransport_trans_sign hR hown hℓR hℓown hT h1'
  have e3 : (-1 : ℝ) * -1 = 1 := by ring
  have e4 : (-1 : ℝ) * -(Real.pi * chiC κ) + -(Real.pi * chiC (16 / κ)) = specOffset κ := by
    rw [Sec4.chiC_sixteen_div hκ, specOffset]
    ring
  have e5 : (-1 : ℝ) * chiC (16 / κ) = chiC κ := by
    rw [Sec4.chiC_sixteen_div hκ]
    ring
  rw [e3, e4, e5] at h2
  have e6 := hHc.unique (isConformal_jointChart hw hw0 hs) h2
  rw [e6]
  exact h1

/-! ### The named statement -/

/-- **Named statement (NOT proved): the relative determination of two curves** — GB6's (Det)
(`Supp8.GB6.GB6RelDetStatement`) in the common generality of GB6 and GW2. The RETAINED curve `(Wα, ζα, α)` is a
flow-line driver of `h` at `κ > 0` and angle `θ` whose traces do not return to `0` (no `κ < 4`); the EXPLORED curve
`(W, ζ, γ)` is a flow-line driver of the transported field `h′` at `16/κ` and angle `θ′`, of any lifetime. Almost
surely on `{s < ζα, α(s) ∈ ℍ}`, with `β = gb6Word κ θ c s Wα` (the retained stop word returned through `R`): the
canonical driver code `F (β, Hc)` of the chart field at angle `θ′` is good, and before the explored lifetime and the
first contact its decoded driver generates the chart images `Ψ(K_t)` of the explored hulls in the relative clock. -/
def RelDetGenStatement : Prop :=
  ∀ (κ θ θ' : ℝ), 0 < κ → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 → -(Real.pi / 2) ≤ θ' → θ' ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' θ' P h' W ζ →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    (∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α ω v ≠ 0) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞, IsCanonicalDriverCode (16 / κ) θ' F →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
        IsGoodDrvCode (F (gb6Word κ θ c s (fun t => Wα t ω), Hc ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
          (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (gb6Word κ θ c s (fun t => Wα t ω), Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) =
            relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t

/-! ### The reduction -/

/-- **GW2's joint (Det) from the relative determination of two curves** (conditional helper): the instance
`(κ, θ, θ′, h, h′) := (16/κ, 0, θ, h′, h)` of `RelDetGenStatement`, with the retained curve the counterflow (which
does not return to its base) and the explored curve the flow line. -/
theorem gw2JointDetC2Statement_of_relDetGen (hNR : GW4Ident.CounterflowNoReturnStatement.{u})
    (hD : RelDetGenStatement.{u}) : GW2JointDetC2Statement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc hHcm
    hHc F hF c' hc'J hc'b
  have hk : (0 : ℝ) < 16 / κ := by positivity
  have e16 : 16 / (16 / κ) = κ := by field_simp
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC (16 / κ)))
      (chiC (16 / (16 / κ))) (h' ω) (h ω) := fun ω => isChartTransport_dual hκ (hT ω)
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hreg.mono fun ω hω => hω.1
  have hfl' : IsFlowLineDriver (16 / (16 / κ)) b J θ P h Wα ζα := by
    rw [e16]
    exact hfl
  have hγ' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω) := hreg.mono fun ω hω => by
    rw [hω.1]
    exact hω.2.1
  have hnr : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ ω → γ ω v ≠ 0 := by
    have h1 := hNR κ hκ hκ4 b J hb P h hh W ζ ⟨b', J', h', hb', hT, hcf⟩ hζ
    filter_upwards [h1, hreg] with ω hω hr v hv _
    exact hω (γ ω) hr.2.1 v hv
  have hdrv := ae_driver_zero_continuousOn hcf
  have hHc' : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω → γ ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => W r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC (16 / κ))) (chiC (16 / (16 / κ))) (h' ω) (Hc ω) := by
    filter_upwards [hHc, hdrv, hζ] with ω hω hd hz _ hsH
    have hcont : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := hd.2
    rw [hz] at hcont
    have hc : Continuous fun t => W t ω := continuousOn_univ.1 (hcont.mono fun t _ => ENNReal.coe_lt_top)
    have h0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by
      show W (0 : ℝ).toNNReal ω = 0
      rw [Real.toNNReal_zero]
      exact hd.1
    exact isChartTransport_own_of_joint hκ (hc.comp continuous_real_toNNReal) h0 s.coe_nonneg (hT ω) (hω hsH)
  have hF' : IsCanonicalDriverCode (16 / (16 / κ)) θ F := by
    rw [e16]
    exact hF
  have hpi := Real.pi_pos
  have key := hD (16 / κ) 0 θ hk (by linarith) (by linarith) hθ₁ hθ₂ Ω mΩ P hP h' b' J' Wα W ζα ζ α γ b J h hb'
    hG' hb hT' hfl' hα hcf hγ' hnr s Hc hHcm hHc' F hF' c' hc'J hc'b
  filter_upwards [key, hζ] with ω hω hz hsH
  have hs : (s : ℝ≥0∞) < ζ ω := by
    rw [hz]
    exact ENNReal.coe_lt_top
  obtain ⟨hgood, hhull⟩ := hω hs hsH
  have ew : gb6Word (16 / κ) 0 c' s (fun t => W t ω) = jointWord (specOffset κ) κ c' s (fun t => W t ω) :=
    (jointWordOfRec_specOffset hκ c' _).symm
  rw [ew] at hgood hhull
  refine ⟨hgood, fun t htζ htc => hhull t htζ ?_⟩
  rw [GW2JDetR4.firstContactTime_sphereInv (α ω) (γ ω) s]
  exact htc

end InteractingSLE.Theorem14.GW2Fb
