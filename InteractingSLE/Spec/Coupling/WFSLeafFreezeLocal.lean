/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafFreezeMarkov
import InteractingSLE.Spec.Coupling.WholeFieldMarked

/-!
# History-marked locality from the retained Gaussian kernel

For each history event, localize the Gaussian argument to its intersection
with avoidance of a deterministic open set. The Markov factorization then
makes that event's conditional probability depend only on the complementary
field projection. This proves the marked avoidance criterion directly.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace

namespace InteractingSLE.WFS

open LQGMetric LocalSets WholeField QuantumZipper

/-- Factorization of the Markov projection on one event identifies its
conditional probability as a function of the complementary projection. -/
theorem exists_condExp_event_eq_comp_of_factorsOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    {E : Set Ω} (hE : MeasurableSet E)
    (hfac : FactorsOn P (fun ω => G (h ω)) (fun ω => markovCompl G (h ω)) E) :
    ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
      P⟦E | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P]
        fun ω => g (markovCompl G (h ω)) := by
  have hXm : Measurable (fun ω => G (h ω)) := hG.comp hhm
  have hYm : Measurable (fun ω => markovCompl G (h ω)) := (measurable_markovCompl hG).comp hhm
  have h𝓜 : MeasurableSpace.generateFrom {E} ≤ mΩ := MeasurableSpace.generateFrom_singleton_le hE
  have huniv : FactorsOn P (fun ω => G (h ω)) (fun ω => markovCompl G (h ω)) univ := by
    intro Φ Ψ
    simp only [Measure.restrict_univ]
    have hi := hd.indepFun.integral_fun_comp_mul_comp
      (f := fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Φ : ℂ)))
      (g := fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ)))
      hXm.aemeasurable hYm.aemeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply Φ)).aestronglyMeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply Ψ)).aestronglyMeasurable
    simpa only [markovCompl] using hi
  have hci := condIndepEv_of_factorsOn hXm hYm h𝓜 fun m hm => by
    rcases measurableSet_generateFrom_singleton_iff.1 hm with rfl | rfl | rfl | rfl
    · intro Φ Ψ
      simp
    · exact hfac
    · intro Φ Ψ
      have hF : Integrable (fun ω => Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))) P := integrable_exp_mul_exp (P := P)
        ((measurable_distOn_apply Φ).comp hXm) ((measurable_distOn_apply Ψ).comp hYm)
      have hY : Integrable (fun ω => Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))) P :=
        GFF.integrable_exp_I_mul (P := P) ((measurable_distOn_apply Ψ).comp hYm)
      rw [setIntegral_compl hE hF, setIntegral_compl hE hY,
        show (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P) =
          (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
            (∫ ω, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P) by
          simpa only [Measure.restrict_univ] using huniv Φ Ψ,
        hfac Φ Ψ, mul_sub]
    · exact huniv
  have hkey := LQGMetric.condExp_sup_eq_of_condIndepEv hYm.comap_le hXm.comap_le h𝓜 hci.symm
    (MeasurableSpace.measurableSet_generateFrom (show E ∈ ({E} : Set (Set Ω)) from rfl))
  rw [← comap_eq_sup_markov h hG] at hkey
  obtain ⟨g, hg, hgeq⟩ := (stronglyMeasurable_condExp
    (m := MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
    (μ := P) (f := E.indicator fun _ => (1 : ℝ))).exists_eq_measurable_comp
  refine ⟨g, hg.measurable, hkey.trans ?_⟩
  rw [hgeq]
  rfl

/-- A Gaussian kernel with a mean harmonic off a recorded random set makes
the set local with all conditioning information retained as marks. -/
theorem isHistoryAvoidanceLocal_of_retainedKernel
    {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h M : Ω → DistOn upperHalfPlaneOpens}
    {A : Ω → Set ℂ} (hℋ : ℋ ≤ mΩ) (hhm : Measurable h)
    (hA : Measurable[ℋ, hittingSigma] A)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hMh : ∀ᵐ ω ∂P, IsHarmonicDistOn (M ω) (H \ A ω))
    (hker : ∀ φ : TestOn upperHalfPlaneOpens,
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | ℋ] =ᵐ[P]
        fun ω => rangeKerCF (M ω) (H \ A ω) φ) :
    IsHistoryAvoidanceLocal ℋ A h P := by
  intro U G hUH hG hd F hF
  let E : Set Ω := {ω | Disjoint (A ω) (U : Set ℂ)} ∩ F
  have hEm : MeasurableSet[ℋ] E := (hA (measurableSet_avoid U.isOpen hUH)).inter hF
  let W : Ω → ℂ := E.indicator fun _ => 1
  have hWm : StronglyMeasurable[ℋ] W := stronglyMeasurable_const.indicator hEm
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E <;> simp [W, hω]
  have hV : ∀ᵐ ω ∂P, W ω ≠ 0 → IsOpen (H \ A ω) ∧ (H \ A ω) ⊆ H ∧
      (U : Set ℂ) ⊆ H \ A ω ∧ IsHarmonicDistOn (M ω) (H \ A ω) := by
    filter_upwards [hAc, hMh] with ω hAcω hMω hW
    have hωE : ω ∈ E := by
      by_contra hn
      exact hW (by simp only [W, indicator_of_notMem hn])
    exact ⟨hAcω.2, sdiff_subset,
      fun z hz => ⟨hUH hz, fun hzA => Set.disjoint_left.1 hωE.1 hzA hz⟩, hMω⟩
  apply exists_condExp_event_eq_comp_of_factorsOn hhm hG hd (hℋ _ hEm)
  intro Φ Ψ
  have hfac := integral_mul_exp_markov_of_kernel_on hℋ hUH hV hker hhm hG hd hWm hWb Φ Ψ
  have he : ∀ Z : Ω → ℂ, (fun ω => W ω * Z ω) = E.indicator Z := fun Z => by
    funext ω
    by_cases hω : ω ∈ E <;> simp [W, hω]
  rw [he, he, integral_indicator (hℋ _ hEm), integral_indicator (hℋ _ hEm)] at hfac
  exact hfac

end InteractingSLE.WFS
