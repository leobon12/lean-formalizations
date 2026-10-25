import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.FiniteStable




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
open LQGMetric (DistC TestC)

theorem rawFiniteStable_circle_shifted_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    {ι : Type} (Z : Finset ι)
    (W : ι → Set ℂ) (hW : ∀ i ∈ Z, IsOpen (W i))
    (hWc : ∀ i ∈ Z, IsCompact (closure (W i)))
    (hWne : ∀ i ∈ Z, (W i)ᶜ.Nonempty)
    (V : ι → TopologicalSpace.Opens ℂ)
    (hVW : ∀ i ∈ Z, closure (V i : Set ℂ) ⊆ W i)
    (Ctime Q : ℝ) (r : ι → Set.Ioi (0 : ℝ)) (z : ι → ℂ)
    (φ : TestC) :
    NullMeasurableSet
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
        ∀ i ∈ Z, ∃ c : ℝ, IsCircleAverage g (r i) (z i) c ∧
          SourceStable (D g) P' T (W i) (V i)
            (ENNReal.ofReal Ctime * ENNReal.ofReal
              (((r i : Set.Ioi (0 : ℝ)) : ℝ) ^ ((ξ : ℝ) * Q) *
                Real.exp ((ξ : ℝ) * c)))}
      (P.map h) := by
  let Eu : Set DistC :=
    {g | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic
        (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T}
  let Ei (i : ι) : Set DistC :=
    {g | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic
        (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
      ∃ c : ℝ, IsCircleAverage g (r i) (z i) c ∧
        SourceStable (D g) P' T (W i) (V i)
          (ENNReal.ofReal Ctime * ENNReal.ofReal
            ((r i : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)))}
  have hEu : NullMeasurableSet Eu (P.map h) :=
    Measurability.SetGeodesicCodes.rawUniqueSetGeodesic_shifted_nullMeasurable P h hh hD
      K₁ K₂ hK₁ hK₂ φ
  have hEi : ∀ i ∈ Z, NullMeasurableSet (Ei i) (P.map h) := by
    intro i hi
    exact rawUniqueStable_circle_shifted_nullMeasurable P h hh hD
      K₁ K₂ hK₁ hK₂ (W i) (hW i hi) (hWc i hi) (hWne i hi)
      (V i) (hVW i hi) Ctime Q (r i) (z i) φ
  have hInter : NullMeasurableSet (Eu ∩ ⋂ i ∈ Z, Ei i) (P.map h) :=
    hEu.inter (Z.nullMeasurableSet_biInter hEi)
  have hEq :
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
        ∀ i ∈ Z, ∃ c : ℝ, IsCircleAverage g (r i) (z i) c ∧
          SourceStable (D g) P' T (W i) (V i)
            (ENNReal.ofReal Ctime * ENNReal.ofReal
              ((r i : ℝ) ^ ((ξ : ℝ) * Q) *
                Real.exp ((ξ : ℝ) * c)))} =
      Eu ∩ ⋂ i ∈ Z, Ei i := by
    ext g
    constructor
    · rintro ⟨P', T, hU, hAll⟩
      refine ⟨⟨P', T, hU⟩, ?_⟩
      simp only [Set.mem_iInter]
      intro i
      by_cases hi : i ∈ Z
      · intro _
        obtain ⟨c, hc, hs⟩ := hAll i hi
        exact ⟨P', T, hU, c, hc, hs⟩
      · intro hfalse
        exact False.elim (hi hfalse)
    · rintro ⟨⟨P', T, hU⟩, hEach⟩
      refine ⟨P', T, hU, ?_⟩
      intro i hi
      have hi' : g ∈ Ei i := (Set.mem_iInter.mp (Set.mem_iInter.mp hEach i) hi)
      obtain ⟨Pi, Ti, hUi, c, hc, hs⟩ := hi'
      obtain ⟨hTi, hEqPath⟩ := hU.2 Pi Ti hUi.1
      subst Ti
      exact ⟨c, hc,
        (sourceStable_congr_on (D g) Pi P' T (W i) (V i) _ hEqPath).1 hs⟩
  rw [hEq]
  exact hInter

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
