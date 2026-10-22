import HigherDimLQGMetric.Sec8b.Lemma85Weyl
import HigherDimLQGMetric.Sec8.Events

/-! One almost-sure event for all deterministic continuous perturbations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Length, two-sided comparison and reverse Weyl identities hold together
for every continuous shift. This avoids separate null sets for the many bump
sums considered in Lemma 8.5. -/
theorem s7b_shifted_metric_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcs : 0 ≤ cs) (hCs : 0 < Cs)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v)) :
    ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ),
      (D (addFun (h ω) f)).IsLength ∧
      (Dt (addFun (h ω) f)).IsLength ∧
      (∀ u v : Rd d,
        cs * (D (addFun (h ω) f)).1 (u, v) ≤
          (Dt (addFun (h ω) f)).1 (u, v) ∧
        (Dt (addFun (h ω) f)).1 (u, v) ≤
          Cs * (D (addFun (h ω) f)).1 (u, v)) ∧
      IsWeylOf ξ (-f) (D (addFun (h ω) f)) (D (h ω)) ∧
      IsWeylOf ξ (-f) (Dt (addFun (h ω) f)) (Dt (h ω)) := by
  have hcmp := hD.ae_apply_compare hDt hh.isLGFPlusCont hcs hCs hcomp
  filter_upwards [hD.length P h hh.isLGFPlusCont,
    hDt.length P h hh.isLGFPlusCont,
    hD.weyl P h hh.isLGFPlusCont,
    hDt.weyl P h hh.isLGFPlusCont,
    hcmp] with ω hlen htlen hw htw hcompω
  intro f
  have hDweyl : IsWeylOf ξ f (D (h ω)) (D (addFun (h ω) f)) :=
    fun u v => (hw f u v).symm
  have hDtWeyl : IsWeylOf ξ f (Dt (h ω)) (Dt (addFun (h ω) f)) :=
    fun u v => (htw f u v).symm
  exact ⟨s7b_weyl_length _ _ ξ f hDweyl,
    s7b_weyl_length _ _ ξ f hDtWeyl,
    hcompω f,
    s7b_weyl_reverse _ _ ξ f hlen hDweyl,
    s7b_weyl_reverse _ _ ξ f htlen hDtWeyl⟩

end HigherDimLQGMetric
