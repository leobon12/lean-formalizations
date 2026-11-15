import InteractingSLE.GFF.LocalSets.Characterization

/-!
# Independence of random distributions from characteristic functionals

For random distributions `X Y : Ω → 𝒟'(ℍ)` and a σ-algebra `𝓜`, if for all test functions
`Φ, Ψ` and all `m ∈ 𝓜`
`∫_m e^{i X(Φ)} e^{i Y(Ψ)} dP = (∫ e^{i X(Φ)} dP) · ∫_m e^{i Y(Ψ)} dP`,
then `σ(X)` is independent of `σ(Y) ⊔ 𝓜` (`indep_comap_sup_of_setIntegral_exp`). Proof: on the
π-systems of finite-dimensional cylinders, the restricted joint law of
`((X(φᵢ))_{i∈I}, (Y(ψⱼ))_{j∈J})` on `m` has the characteristic function of the product law
(linearity of `X ω`, `Y ω`), so equals it (`ProbabilityTheory.charFunDual_eq_prod_iff`).

Used for Lemma 3.6, (iv) ⇒ (ii) ("one first checks this identity for cylinder functions of the
distributional coordinates and then uses the monotone class theorem", p. 55).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open LQGMetric

/-- The finite-dimensional projection `T ↦ (T φ)_{φ ∈ I}`. -/
def distProj (I : Finset (TestOn upperHalfPlaneOpens)) (T : DistOn upperHalfPlaneOpens) :
    I → ℝ :=
  fun i => T i

theorem measurable_distProj (I : Finset (TestOn upperHalfPlaneOpens)) :
    Measurable (distProj I) :=
  measurable_pi_iff.mpr fun i => measurable_distOn_apply (i : TestOn upperHalfPlaneOpens)

open scoped Classical in
/-- A continuous linear functional of a finite-dimensional projection is a pairing. -/
theorem dual_apply_distProj (I : Finset (TestOn upperHalfPlaneOpens))
    (L : StrongDual ℝ (I → ℝ)) (T : DistOn upperHalfPlaneOpens) :
    L (distProj I T) =
      T (∑ i : I, L (fun j => if i = j then 1 else 0) • (i : TestOn upperHalfPlaneOpens)) := by
  have := LinearMap.pi_apply_eq_sum_univ (L : (I → ℝ) →ₗ[ℝ] ℝ) (distProj I T)
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl

section Indep

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

open scoped Classical in
/-- The restricted joint law of finite-dimensional projections is the product law. -/
theorem map_restrict_distProj_eq_prod {X Y : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hY : Measurable Y) {m : Set Ω}
    (hid : ∀ Φ Ψ : TestOn upperHalfPlaneOpens,
      ∫ ω in m, Complex.exp (Complex.I * (X ω Φ : ℂ)) * Complex.exp (Complex.I * (Y ω Ψ : ℂ)) ∂P =
        (∫ ω, Complex.exp (Complex.I * (X ω Φ : ℂ)) ∂P) *
          ∫ ω in m, Complex.exp (Complex.I * (Y ω Ψ : ℂ)) ∂P)
    (I J : Finset (TestOn upperHalfPlaneOpens)) :
    (P.restrict m).map (fun ω => (distProj I (X ω), distProj J (Y ω))) =
      (P.map fun ω => distProj I (X ω)).prod ((P.restrict m).map fun ω => distProj J (Y ω)) := by
  have hξ : Measurable fun ω => distProj I (X ω) := (measurable_distProj I).comp hX
  have hζ : Measurable fun ω => distProj J (Y ω) := (measurable_distProj J).comp hY
  refine (charFunDual_eq_prod_iff).1 fun L => ?_
  rw [charFunDual_apply, charFunDual_apply, charFunDual_apply,
    integral_map (hξ.prodMk hζ).aemeasurable (by fun_prop),
    integral_map hξ.aemeasurable (by fun_prop), integral_map hζ.aemeasurable (by fun_prop)]
  set Φ := ∑ i : I, (L.comp (.inl ℝ (I → ℝ) (J → ℝ))) (fun j => if i = j then 1 else 0) •
    (i : TestOn upperHalfPlaneOpens)
  set Ψ := ∑ i : J, (L.comp (.inr ℝ (I → ℝ) (J → ℝ))) (fun j => if i = j then 1 else 0) •
    (i : TestOn upperHalfPlaneOpens)
  have hL : ∀ ω, L (distProj I (X ω), distProj J (Y ω)) = X ω Φ + Y ω Ψ := by
    intro ω
    rw [← L.comp_inl_add_comp_inr, dual_apply_distProj, dual_apply_distProj]
  have h1 : ∀ ω, (L.comp (.inl ℝ (I → ℝ) (J → ℝ))) (distProj I (X ω)) = X ω Φ :=
    fun ω => dual_apply_distProj I _ _
  have h2 : ∀ ω, (L.comp (.inr ℝ (I → ℝ) (J → ℝ))) (distProj J (Y ω)) = Y ω Ψ :=
    fun ω => dual_apply_distProj J _ _
  simp_rw [hL, h1, h2]
  have e : ∀ ω, Complex.exp (((X ω Φ + Y ω Ψ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (X ω Φ : ℂ)) * Complex.exp (Complex.I * (Y ω Ψ : ℂ)) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [e, hid Φ Ψ, mul_comm _ Complex.I]

end Indep

/-- **Independence from characteristic functionals.** -/
theorem indep_comap_sup_of_setIntegral_exp {Ω : Type*} {𝓜 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (hY : Measurable Y) (h𝓜 : 𝓜 ≤ mΩ)
    (hid : ∀ (Φ Ψ : TestOn upperHalfPlaneOpens) (m : Set Ω), MeasurableSet[𝓜] m →
      ∫ ω in m, Complex.exp (Complex.I * (X ω Φ : ℂ)) * Complex.exp (Complex.I * (Y ω Ψ : ℂ)) ∂P =
        (∫ ω, Complex.exp (Complex.I * (X ω Φ : ℂ)) ∂P) *
          ∫ ω in m, Complex.exp (Complex.I * (Y ω Ψ : ℂ)) ∂P) :
    Indep (MeasurableSpace.comap X inferInstance)
      (MeasurableSpace.comap Y inferInstance ⊔ 𝓜) P := by
  set evX : Ω → TestOn upperHalfPlaneOpens → ℝ := fun ω φ => X ω φ
  set evY : Ω → TestOn upperHalfPlaneOpens → ℝ := fun ω φ => Y ω φ
  set C := measurableCylinders fun _ : TestOn upperHalfPlaneOpens => ℝ
  set p₁ : Set (Set Ω) := {s | ∃ t ∈ C, evX ⁻¹' t = s}
  set pY : Set (Set Ω) := {s | ∃ t ∈ C, evY ⁻¹' t = s}
  set p₂ : Set (Set Ω) := {s | ∃ t ∈ pY, ∃ m, MeasurableSet[𝓜] m ∧ s = t ∩ m}
  have hcomap : ∀ Z : Ω → DistOn upperHalfPlaneOpens,
      MeasurableSpace.comap Z inferInstance =
        MeasurableSpace.generateFrom {s | ∃ t ∈ C, (fun ω φ => Z ω φ) ⁻¹' t = s} := by
    intro Z
    change MeasurableSpace.comap Z (MeasurableSpace.comap
      (fun (T : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) => T φ)
        MeasurableSpace.pi) = _
    rw [MeasurableSpace.comap_comp, ← generateFrom_measurableCylinders,
      MeasurableSpace.comap_generateFrom]
    rfl
  have hpY : IsPiSystem pY := isPiSystem_measurableCylinders.comap evY
  have hunivY : univ ∈ pY := ⟨univ, univ_mem_measurableCylinders _, preimage_univ⟩
  refine IndepSets.indep (p1 := p₁) (p2 := p₂) hX.comap_le (sup_le hY.comap_le h𝓜)
    (isPiSystem_measurableCylinders.comap evX) ?_ (hcomap X) ?_ ?_
  · rintro _ ⟨t, ht, m, hm, rfl⟩ _ ⟨t', ht', m', hm', rfl⟩ hne
    refine ⟨t ∩ t', hpY t ht t' ht' ?_, m ∩ m', hm.inter hm', by
      ext ω; simp only [mem_inter_iff]; tauto⟩
    obtain ⟨ω, hω⟩ := hne
    exact ⟨ω, hω.1.1, hω.2.1⟩
  · refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
    · rw [hcomap Y]
      refine MeasurableSpace.generateFrom_mono fun s hs => ⟨s, hs, univ, MeasurableSet.univ, ?_⟩
      rw [inter_univ]
    · intro m hm
      exact MeasurableSpace.measurableSet_generateFrom ⟨univ, hunivY, m, hm, by rw [univ_inter]⟩
    · rintro _ ⟨t, ht, m, hm, rfl⟩
      refine MeasurableSet.inter ?_ ((le_sup_right : 𝓜 ≤ _) m hm)
      refine (le_sup_left : MeasurableSpace.comap Y inferInstance ≤ _) t ?_
      rw [hcomap Y]
      exact MeasurableSpace.measurableSet_generateFrom ht
  · rw [IndepSets_iff]
    rintro _ _ ⟨t₁, ht₁, rfl⟩ ⟨_, ⟨t₂, ht₂, rfl⟩, m, hm, rfl⟩
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders t₁).1 ht₁
    obtain ⟨J, S', hS', rfl⟩ := (mem_measurableCylinders t₂).1 ht₂
    have hm0 : MeasurableSet m := h𝓜 m hm
    have hξ : Measurable fun ω => distProj I (X ω) := (measurable_distProj I).comp hX
    have hζ : Measurable fun ω => distProj J (Y ω) := (measurable_distProj J).comp hY
    have e₁ : evX ⁻¹' cylinder I S = (fun ω => distProj I (X ω)) ⁻¹' S := rfl
    have e₂ : evY ⁻¹' cylinder J S' = (fun ω => distProj J (Y ω)) ⁻¹' S' := rfl
    rw [e₁, e₂]
    have key := map_restrict_distProj_eq_prod hX hY (m := m)
      (fun Φ Ψ => hid Φ Ψ m hm) I J
    have hprod := congrArg (fun μ : Measure ((I → ℝ) × (J → ℝ)) => μ (S ×ˢ S')) key
    rw [Measure.map_apply (hξ.prodMk hζ) (hS.prod hS'), Measure.prod_prod,
      Measure.map_apply hξ hS, Measure.map_apply hζ hS',
      Measure.restrict_apply ((hξ.prodMk hζ) (hS.prod hS')),
      Measure.restrict_apply (hζ hS')] at hprod
    rw [← hprod]
    congr 1
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_prod]
    tauto

end LocalSets
end InteractingSLE
