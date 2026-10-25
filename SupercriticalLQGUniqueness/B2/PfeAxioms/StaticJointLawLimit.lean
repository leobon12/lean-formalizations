import SupercriticalLQGUniqueness.B2.PfeAxioms.JointLawLimit
import Mathlib.MeasureTheory.Measure.Prod

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem static_joint_limit_law_eq
    {S T Ω Ω' : Type*} [MeasurableSpace S]
    [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] [BorelSpace T]
    [HasOuterApproxClosed (Bool × T)]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : Ω → S) (X' : Ω' → S)
    (hX : Measurable X) (hX' : Measurable X')
    (F : ℕ → Ω → T) (F' : ℕ → Ω' → T)
    (L : Ω → T) (L' : Ω' → T)
    (hmF : ∀ n, AEMeasurable (F n) P)
    (hmF' : ∀ n, AEMeasurable (F' n) P')
    (hmL : AEMeasurable L P) (hmL' : AEMeasurable L' P')
    (hLaw : ∀ n, P.map (fun ω => (X ω, F n ω)) =
      P'.map (fun ω => (X' ω, F' n ω)))
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (L ω)))
    (hConv' : ∀ᵐ ω ∂P', Tendsto (fun n => F' n ω) atTop (𝓝 (L' ω))) :
    P.map (fun ω => (X ω, L ω)) =
      P'.map (fun ω => (X' ω, L' ω)) := by
  classical
  apply Measure.ext_prod
  intro A B hA hB
  let χ : S → Bool := fun s => if s ∈ A then true else false
  have hχ : Measurable χ := measurable_const.ite hA measurable_const
  let J : S × T → Bool × T := Prod.map χ id
  have hJ : Measurable J :=
    (hχ.comp measurable_fst).prodMk measurable_snd
  have hLawBool n :
      P.map (fun ω => (χ (X ω), F n ω)) =
      P'.map (fun ω => (χ (X' ω), F' n ω)) := by
    have hs : AEMeasurable (fun ω => (X ω, F n ω)) P :=
      hX.aemeasurable.prodMk (hmF n)
    have ht : AEMeasurable (fun ω => (X' ω, F' n ω)) P' :=
      hX'.aemeasurable.prodMk (hmF' n)
    have hsrc := AEMeasurable.map_map_of_aemeasurable hJ.aemeasurable hs
    have hdst := AEMeasurable.map_map_of_aemeasurable hJ.aemeasurable ht
    calc
      P.map (fun ω => (χ (X ω), F n ω)) =
          (P.map (fun ω => (X ω, F n ω))).map J := by
        simpa only [Function.comp_def, J, Prod.map_apply, id_eq] using hsrc.symm
      _ = (P'.map (fun ω => (X' ω, F' n ω))).map J :=
        congrArg (Measure.map J) (hLaw n)
      _ = P'.map (fun ω => (χ (X' ω), F' n ω)) := by
        simpa only [Function.comp_def, J, Prod.map_apply, id_eq] using hdst
  have hLawBoolLimit :
      P.map (fun ω => (χ (X ω), L ω)) =
      P'.map (fun ω => (χ (X' ω), L' ω)) := by
    apply joint_limit_law_eq_of_finite_laws P P'
      (fun n ω => (χ (X ω), F n ω))
      (fun n ω => (χ (X' ω), F' n ω))
      (fun ω => (χ (X ω), L ω))
      (fun ω => (χ (X' ω), L' ω))
    · intro n
      exact (hχ.comp hX).aemeasurable.prodMk (hmF n)
    · intro n
      exact (hχ.comp hX').aemeasurable.prodMk (hmF' n)
    · exact (hχ.comp hX).aemeasurable.prodMk hmL
    · exact (hχ.comp hX').aemeasurable.prodMk hmL'
    · exact hLawBool
    · filter_upwards [hConv] with ω hω
      exact tendsto_const_nhds.prodMk_nhds hω
    · filter_upwards [hConv'] with ω hω
      exact tendsto_const_nhds.prodMk_nhds hω
  have hRect : MeasurableSet ({true} ×ˢ B) :=
    (measurableSet_singleton true).prod hB
  have hleft :
      (fun ω => (χ (X ω), L ω)) ⁻¹' ({true} ×ˢ B) =
      (fun ω => (X ω, L ω)) ⁻¹' (A ×ˢ B) := by
    ext ω
    simp [χ]
  have hright :
      (fun ω => (χ (X' ω), L' ω)) ⁻¹' ({true} ×ˢ B) =
      (fun ω => (X' ω, L' ω)) ⁻¹' (A ×ˢ B) := by
    ext ω
    simp [χ]
  have h1 : AEMeasurable (fun ω => (X ω, L ω)) P :=
    hX.aemeasurable.prodMk hmL
  have h2 : AEMeasurable (fun ω => (X' ω, L' ω)) P' :=
    hX'.aemeasurable.prodMk hmL'
  have hb1 : AEMeasurable (fun ω => (χ (X ω), L ω)) P :=
    (hχ.comp hX).aemeasurable.prodMk hmL
  have hb2 : AEMeasurable (fun ω => (χ (X' ω), L' ω)) P' :=
    (hχ.comp hX').aemeasurable.prodMk hmL'
  calc
    (P.map (fun ω => (X ω, L ω))) (A ×ˢ B) =
        (P.map (fun ω => (χ (X ω), L ω))) ({true} ×ˢ B) := by
      rw [Measure.map_apply_of_aemeasurable h1 (hA.prod hB),
        Measure.map_apply_of_aemeasurable hb1 hRect, hleft]
    _ = (P'.map (fun ω => (χ (X' ω), L' ω))) ({true} ×ˢ B) :=
      congrArg (fun μ : Measure (Bool × T) => μ ({true} ×ˢ B)) hLawBoolLimit
    _ = (P'.map (fun ω => (X' ω, L' ω))) (A ×ˢ B) := by
      rw [Measure.map_apply_of_aemeasurable h2 (hA.prod hB),
        Measure.map_apply_of_aemeasurable hb2 hRect, hright]

end SupercriticalLQGUniqueness.B2.PfeAxioms
