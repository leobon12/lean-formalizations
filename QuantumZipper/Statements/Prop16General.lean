import QuantumZipper.Statements.Prop16

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6 without the positivity presupposition (companion of `theorem1_6`, D96)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Proposition 1.6 (PDF p. 24):

> Fix γ ∈ [0,2) and let D be a bounded subdomain of H for which ∂D ∩ R is a segment of positive
> length. Let h̃ be an instance of the GFF with zero boundary conditions on ∂D \ R and free
> boundary conditions on ∂D ∩ R. Let [a,b] be any sub-interval of ∂D ∩ R and let h0 be a
> continuous function on D that extends continuously to the interval (a,b). […] let ν_h[a,b] dh
> denote the measure whose Radon-Nikodym derivative w.r.t. dh is ν_h[a,b]. (Assume that this is a
> finite measure — i.e., the dh expectation of ν_h[a,b] is finite.) Now suppose we
> 1. sample h from ν_h[a,b] dh (normalized to be a probability measure), […]

`theorem1_6_general` is `theorem1_6` (`Statements/Prop16.lean`, unchanged) with the hypothesis
`0 < ∫⁻ ν_h[a,b] dP` **removed**: as in the paper, only `E ν_h[a,b] < ∞` is assumed; positivity
is proved (`Prop16Asm.prop16Gen_lintegral_pos`: a.s. `ν_h` charges `(a,b)`).

**Remaining differences from the paper** (all other modelling choices are those of
`theorem1_6`, see its module docstring and DEVIATIONS.md A19):

* `0 < γ` (the paper allows `γ = 0`, where `C/γ` is undefined; STATEMENT_SPEC B2).
* The half-disc condition `∀ t ∈ (c,d), ∃ r > 0, B(t,r) ∩ ℍ ⊆ D` is **kept**. The paper only says
  "∂D ∩ R is a segment of positive length", which also allows e.g. a slit of `∂D` ending at a
  point `t₀ ∈ (a,b)`. Task PROP16-GEN tried to weaken it to "for Lebesgue-a.e. `t ∈ (c,d)`" and
  did not succeed. Reasons, all in the proof: (1) the local boundary measure `ν_h =
  qBoundaryMeasureOn γ h (a,b)` is a vague limit tested against every `f ∈ C_c((a,b))`, including
  test functions whose support contains `t₀`. Its existence near a slit base needs moment bounds
  for the mixed field there. The proved bounds (`Prop16BdryMom*`) and the domain Markov coupling
  (`prop16MixedFreeLocCoupling_holds`) use half-discs. Without the limit, `ν_h` is the junk `0`.
  (2) The whole Prop. 1.6 chain works with `V = D ∪ (a,b)` relatively open in `closure ℍ`
  (`locGood_exists_open`), which fails at a slit base. (3) The weakening would also need
  `ν_h(bad set) = 0` a.s. (absolute continuity of the Palm intensity), which is not formalized.
  The weakest condition this proof handles is therefore the everywhere half-disc condition on
  `(c,d)` (`K3.Prop16Geometry`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QuantumZipper

/-- **Proposition 1.6, positivity not presupposed (D96).** Exactly `theorem1_6` without the
hypothesis `0 < ∫⁻ ν_h[a,b] dP`: only `E ν_h[a,b] < ∞` is assumed, as in the paper. -/
def theorem1_6_general : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (D : Set ℂ) (c d a b : ℝ), IsOpen D → IsConnected D → Bornology.IsBounded D → D ⊆ H →
    c < d → frontier D ∩ {z : ℂ | z.im = 0} = realSet (Set.Icc c d) →
    (∀ t ∈ Set.Ioo c d, ∃ r > 0, Metric.ball (t : ℂ) r ∩ H ⊆ D) →
    a < b → c ≤ a → b ≤ d →
  ∀ h0 : ℂ → ℝ, ContinuousOn h0 (D ∪ realSet (Set.Ioo a b)) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsMixedGFF D (realSet (Set.Icc c d)) X P →
    ∫⁻ ω, prop16Nu γ h0 a b (X ω) (Set.Icc a b) ∂P < ⊤ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ W P' ∧
      AreaConvergesInLawOn γ (prop16Law P (fun ω => prop16Nu γ h0 a b (X ω)) a b)
        (fun C p => canonicalOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))
        (fun C p => canonicalDomainOn γ (zoomField γ C (ofFun h0 + X p.1) p.2)
          (zoomDomain D p.2))
        P' W

end QuantumZipper
