import HigherDimLQGMetric.Locality.FiniteCI

/-! Directed passage for finite internal families with the full field kept
on the exterior side at every finite stage. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

theorem l7a_condIndepEv_iSup_of_finite_with_fixed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ι κ : Type*} (G H : MeasurableSpace Ω)
    (A : ι → MeasurableSpace Ω) (B : κ → MeasurableSpace Ω)
    (hG : G ≤ mΩ) (hH : H ≤ mΩ)
    (hA : ∀ i, A i ≤ mΩ) (hB : ∀ j, B j ≤ mΩ)
    (hfinite : ∀ (S : Finset ι) (T : Finset κ),
      LQGMetric.CondIndepEv G (⨆ i ∈ S, A i)
        (H ⊔ ⨆ j ∈ T, B j) P) :
    LQGMetric.CondIndepEv G (⨆ i, A i)
      (H ⊔ ⨆ j, B j) P := by
  classical
  let AF : Finset ι → MeasurableSpace Ω := fun S => ⨆ i ∈ S, A i
  let BF : Finset κ → MeasurableSpace Ω := fun T => H ⊔ ⨆ j ∈ T, B j
  have hAF (S : Finset ι) : AF S ≤ mΩ := iSup₂_le fun i _ => hA i
  have hBF (T : Finset κ) : BF T ≤ mΩ :=
    sup_le hH (iSup₂_le fun j _ => hB j)
  have hAdir : Directed (· ≤ ·) AF := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩
    · exact iSup₂_le fun i hi => le_iSup₂_of_le i (Finset.mem_union_left T hi) le_rfl
    · exact iSup₂_le fun i hi => le_iSup₂_of_le i (Finset.mem_union_right S hi) le_rfl
  have hBmono (S T : Finset κ) (hST : S ⊆ T) : BF S ≤ BF T := by
    have hcomp : (⨆ j ∈ S, B j) ≤ (⨆ j ∈ T, B j) :=
      iSup₂_le fun j hj => le_iSup₂_of_le j (hST hj) le_rfl
    exact sup_le le_sup_left (hcomp.trans le_sup_right)
  have hBdir : Directed (· ≤ ·) BF := by
    intro S T
    exact ⟨S ∪ T, hBmono S _ (Finset.subset_union_left),
      hBmono T _ (Finset.subset_union_right)⟩
  have hAB (S : Finset ι) : LQGMetric.CondIndepEv G (AF S) (⨆ T, BF T) P := by
    have hcond : CondIndep G (⨆ T, BF T) (AF S) hG P :=
      condIndep_iSup_of_directed_le
        (fun T => (LQGMetric.condIndep_iff_condIndepEv hG (hBF T) (hAF S)).2
          (hfinite S T).symm)
        hBF (hAF S) hBdir
    exact (LQGMetric.condIndep_iff_condIndepEv hG (hAF S) (iSup_le hBF)).1 hcond.symm
  have hlim : LQGMetric.CondIndepEv G (⨆ S, AF S) (⨆ T, BF T) P := by
    have hcond : CondIndep G (⨆ S, AF S) (⨆ T, BF T) hG P :=
      condIndep_iSup_of_directed_le
        (fun S => (LQGMetric.condIndep_iff_condIndepEv hG (hAF S)
          (iSup_le hBF)).2 (hAB S))
        hAF (iSup_le hBF) hAdir
    exact (LQGMetric.condIndep_iff_condIndepEv hG
      (iSup_le hAF) (iSup_le hBF)).1 hcond
  have hAe : (⨆ S, AF S) = ⨆ i, A i := by
    apply le_antisymm
    · exact iSup_le fun S => iSup₂_le fun i _ => le_iSup A i
    · exact iSup_le fun i => le_iSup_of_le ({i} : Finset ι)
        (le_iSup₂_of_le i (Finset.mem_singleton_self i) le_rfl)
  have hBe : (⨆ T, BF T) = H ⊔ ⨆ j, B j := by
    apply le_antisymm
    · exact iSup_le fun T => sup_le le_sup_left
        (iSup₂_le fun j _ => (le_iSup B j).trans le_sup_right)
    · apply sup_le
      · exact le_iSup_of_le (∅ : Finset κ) le_sup_left
      · exact iSup_le fun j => le_iSup_of_le ({j} : Finset κ)
          (show B j ≤ BF ({j} : Finset κ) from
            (le_iSup₂_of_le (f := fun k (_ : k ∈ ({j} : Finset κ)) => B k)
              j (Finset.mem_singleton_self j) le_rfl).trans le_sup_right)
  simpa only [hAe, hBe] using hlim

end HigherDimLQGMetric
