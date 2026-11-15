/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ConeQ
import InteractingSLE.Spec.Supplement.GW2JointKernel

/-!
# GW2's tip exhaustion: the canonical construction for every schedule set

Packet PROVE-T14-TIP9. Follow-up note A.1 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt`, lines 59–76, ruling
R53): "In fact the argument works for any deterministic dense `Q` with the stated truncation convention." The tip
exhaustion is run on the canonical construction (`GW2Tip.canonSpecFam`, the field-determined pieces, PROVE-T14-TIP3);
this file states it for **every** deterministic countable dense schedule set `Q ⊂ (0, ∞)`
(`GW2TipExhaustionCanonAllQStatement`) and wires it to the two consumers:

* `gw2TipExhaustionCanonStatement_of_canonAllQ`: the canonical exhaustion for one chosen `Q`
  (`GW2Tip.GW2TipExhaustionCanonStatement`, PROVE-T14-TIP6), by choosing the positive rationals;
* `gw2TipExhaustionAllQStatement_of_canonAllQ`: BR7's `GW2TipExhaustionAllQStatement` (every `Q`, every staged family
  with almost surely continuous launched pieces, ruling R51), from Theorems 1.2 and 1.3 (frozen types), by the R51
  identification `GW2Tip.ae_boundaryLightConeFamily_eq_canon` (PROVE-T14-TIP6), which holds for every countable `Q`;
* `completedRange_eq_closure_lightCone_of_canonAllQ`: the version-2 light-cone anchor's shape on GB9a's schedule set
  (`completedRange_eq_closure_lightCone_of_interiorQ`, PROVE-T14-BR7) with the canonical exhaustion in place of
  BR7's input.

So the whole light-cone chain of Theorem 1.4 needs, for the tip exhaustion, only the canonical statement for every `Q`.

The last step of the exhaustion (GB9, p. 526: "Unbounded points in the `ψ` chart pull back to `p` by continuity of
`ψ⁻¹` at infinity"; follow-up note A.5) is proved here as well:

* `GW2TipJointUnboundedStatement` (named): almost surely on the interior-tip event `γ(s) ∈ ℍ`, the part of the canonical
  light-cone family off the counterflow hull has an unbounded image in the joint chart of the counterflow stop
  (`GW2JointKernel.jointChart`) — the conclusion of the stage experiment of follow-up note A.3–A.5 ("The selected
  ranges are consequently unbounded in the joint chart");
* `gw2TipExhaustionCanonAllQStatement_of_jointUnbounded`: it implies the canonical exhaustion for every `Q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Tip

open GW2Schedule GW2Cone GW2Later Exist Staged StagedLaw Restart LQGMetric

/-- **Named statement: GW2's exhaustion at an interior counterflow tip, for the canonical construction and every
deterministic countable dense schedule set** (follow-up note A.1: the argument "works for any deterministic dense `Q`").
As `GW2TipExhaustionCanonStatement`, with `Q` arbitrary instead of chosen. -/
def GW2TipExhaustionCanonAllQStatement : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord), IsStopLaw.{u} κ βA →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord), IsPiecewiseConstantBoundaryData b jumps →
      c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∀ Q : Set ℝ≥0, Q.Countable → Dense Q → (∀ q ∈ Q, 0 < q) →
      ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
        ∀ s : ℝ≥0, ∀ᵐ ω ∂P, γ ω s ∈ H →
          -(γ ω s)⁻¹ ∈ closure (boundaryLightConeFamily κ b jumps Θ Q
            (fun spec k => canonSpecFam hκ h12p βA c₀ h spec k ω))

/-- **The canonical exhaustion for one chosen `Q`** from the canonical exhaustion for every `Q` (choose the positive
rationals, `exists_countable_dense_pos`). -/
theorem gw2TipExhaustionCanonStatement_of_canonAllQ (hEx : GW2TipExhaustionCanonAllQStatement.{u}) :
    GW2TipExhaustionCanonStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos⟩ := exists_countable_dense_pos
  exact ⟨Q, hQc, hQd, hQpos,
    hEx κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos⟩

/-- **BR7's exhaustion for every `Q` and every R51 staged family from the canonical exhaustion for every `Q`**
(Theorems 1.2–1.3 as their frozen types: the canonical construction uses Theorem 1.2 in its word-measurable form, and
the identification of an R51 family with the canonical one, `ae_boundaryLightConeFamily_eq_canon`, uses Theorem 1.3's
complete trace). As `gw2TipExhaustionR51Statement_of_canon`, with the schedule set `Q` given instead of chosen. -/
theorem gw2TipExhaustionAllQStatement_of_canonAllQ (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (hEx : GW2TipExhaustionCanonAllQStatement.{u}) : GW2TipExhaustionAllQStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos E hE hreg γ hγ s
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨βA, hβA⟩ := (stopLawStatement_iff.1 stopLawStatement.{u}) κ hκ hκ4
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  filter_upwards [ae_boundaryLightConeFamily_eq_canon hκ h12p h13 hβA hb hc₀J hc₀ hh hΘ hΘc hQc hE hreg,
    hEx κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos γ hγ s]
    with ω hfam hω hs
  rw [hfam]
  exact hω hs

/-- **Theorem 1.4, light cone, version 2** (`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`, R51),
provider shape, on GB9a's schedule set, with the canonical exhaustion for every `Q`: as
`completedRange_eq_closure_lightCone_of_interiorQ` (PROVE-T14-BR7), whose exhaustion input is supplied by
`gw2TipExhaustionAllQStatement_of_canonAllQ`. Conditional helper (not the provider). -/
theorem completedRange_eq_closure_lightCone_of_canonAllQ (h12 : Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u})
    (hBR4a : BR4a.BR4aStatement.{u}) (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (hQ : GW2InteriorScheduleQStatement.{u}) (hEx : GW2TipExhaustionCanonAllQStatement.{u})
    (hGW2a : GW2aContainmentStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {Θ : Set ℝ} (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by assumption)
    (hΘc : Θ.Countable := by assumption)
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ := by assumption) :
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
            counterflowCompletedRange (fun t => W' t ω)) ∧
        ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
          ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
              (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
              {0}) =
            counterflowCompletedRange (fun t => W' t ω) :=
  completedRange_eq_closure_lightCone_of_interiorQ h13 h13₀ hBR6 hBR4a hGB6 hG hQ
    (gw2TipExhaustionAllQStatement_of_canonAllQ h12 h13 hEx) hGW2a

/-! ### The last step: unbounded joint-chart images pull back to the tip -/

/-- **Named statement: the canonical light cone is unbounded in the joint chart of every interior counterflow stop**
(follow-up note A.5: "Relative capacity is therefore unbounded. A bounded relative trace range would bound its filled
hull in a rectangle, and hence bound its half-plane capacity. The selected ranges are consequently unbounded in the
joint chart"; GB9, p. 526). Binders of `GW2TipExhaustionCanonAllQStatement`; conclusion: almost surely on
`{γ(s) ∈ ℍ}`, the points of the canonical family `boundaryLightConeFamily … (canonSpecFam …)` lying in the physical
complement `−1/(ℍ \ K_s)` of the counterflow hull have an unbounded image under the joint chart
`GW2JointKernel.jointChart W' s` (`z ↦ −1/f_s(−1/z)`, physical tip `−1/γ(s)` at `∞`). -/
def GW2TipJointUnboundedStatement : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord), IsStopLaw.{u} κ βA →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord), IsPiecewiseConstantBoundaryData b jumps →
      c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∀ Q : Set ℝ≥0, Q.Countable → Dense Q → (∀ q ∈ Q, 0 < q) →
      ∀ γ : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω)) →
        ∀ s : ℝ≥0, ∀ᵐ ω ∂P, γ ω s ∈ H →
          ¬ Bornology.IsBounded ((GW2JointKernel.jointChart (fun r : ℝ => W' r.toNNReal ω) s).1 ''
            (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => canonSpecFam hκ h12p βA c₀ h spec k ω) ∩
              (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) s)))

/-- **The canonical exhaustion for every `Q` from the unboundedness in the joint chart** (GB9, p. 526; follow-up note
A.5: "The inverse chart sends points tending to infinity to `p`, so `p ∈ L_{Θ,Q}`"). The counterflow driver is almost
surely continuous with `W'(0) = 0` (it is a flow-line driver at `16/κ`), the inverse joint chart tends to the physical
tip `−1/γ(s)` at `∞` (`GW2JointKernel.tendsto_jointChart_inv_tip`), so the unbounded part of the family accumulates
there (`GW2JointKernel.mem_closure_of_not_isBounded_jointChart`). -/
theorem gw2TipExhaustionCanonAllQStatement_of_jointUnbounded (hU : GW2TipJointUnboundedStatement.{u}) :
    GW2TipExhaustionCanonAllQStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos
    γ hγ s
  have hUs := hU κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos
    γ hγ s
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  filter_upwards [hUs, hdrv, hζ', hγ] with ω hUω hdω hζω hγω hsH
  rw [hζω] at hdω
  have hWc : ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < ⊤} := hdω.2
  have hWc' : Continuous fun r : ℝ => W' r.toNNReal ω := by
    have hc : Continuous fun t => W' t ω := by
      simp only [ENNReal.coe_lt_top, ofPred_true] at hWc
      exact continuousOn_univ.1 hWc
    exact hc.comp continuous_real_toNNReal
  have hγs : γ ω s ≠ 0 := fun h0 => by
    have : (0 : ℝ) < (γ ω s).im := hsH
    rw [h0, Complex.zero_im] at this
    exact lt_irrefl 0 this
  have hmem := GW2JointKernel.mem_closure_of_not_isBounded_jointChart hγω hWc hdω.1 ENNReal.coe_lt_top hγs hWc'
    inter_subset_right (hUω hsH)
  exact closure_mono inter_subset_left hmem

end GW2Tip

end Theorem14

end InteractingSLE
