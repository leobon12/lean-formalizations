import HigherDimLQGMetric.Locality.FiniteCIWithH
import HigherDimLQGMetric.Locality.LawCI

/-! The directed monotone-class passage can be carried out on a standard
Borel observation law even when the original sample space is arbitrary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

theorem l7a_condIndepEv_iSup_observation
    {Ω S : Type*} [MeasurableSpace Ω]
    [mS : MeasurableSpace S] [StandardBorelSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → S) (hX : Measurable X)
    {ι κ : Type*} (G H : MeasurableSpace S)
    (A : ι → MeasurableSpace S) (B : κ → MeasurableSpace S)
    (hG : G ≤ mS) (hH : H ≤ mS)
    (hA : ∀ i, A i ≤ mS) (hB : ∀ j, B j ≤ mS)
    (hfinite : ∀ (U : Finset ι) (T : Finset κ),
      LQGMetric.CondIndepEv (G.comap X)
        ((⨆ i ∈ U, A i).comap X)
        ((H ⊔ ⨆ j ∈ T, B j).comap X) P) :
    LQGMetric.CondIndepEv (G.comap X)
      ((⨆ i, A i).comap X)
      ((H ⊔ ⨆ j, B j).comap X) P := by
  letI : MeasurableSpace S := mS
  have hfiniteLaw (U : Finset ι) (T : Finset κ) :
      LQGMetric.CondIndepEv G (⨆ i ∈ U, A i)
        (H ⊔ ⨆ j ∈ T, B j) (P.map X) :=
    LQGMetric.DFGPS.L217.condIndepEv_map hX hG
      (iSup₂_le fun i _ => hA i)
      (sup_le hH (iSup₂_le fun j _ => hB j)) (hfinite U T)
  have hLaw := l7a_condIndepEv_iSup_of_finite_with_fixed
    G H A B hG hH hA hB hfiniteLaw
  exact LQGMetric.DFGPS.L217.condIndepEv_comap_of_map hX hG
    (iSup_le hA) (sup_le hH (iSup_le hB)) hLaw

end HigherDimLQGMetric
