/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GPrimeBoundary
import InteractingSLE.Spec.Sec5.Aux61SlitVNest

/-! # Nested marked comparison along a free access

Add the smaller germs using proved marked locality, then use nested
Gaussian uniqueness on the event where the larger comparison union
agrees with the retained union. The boundary estimate is componentwise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Filter Set Topology Metric
namespace InteractingSLE.Sec5.Aux61GPrime
open QuantumZipper LQGMetric LocalSets WholeField
open InteractingSLE.Theorem14.SB.FinRel
variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Relative means at a retained union cancel through the components
missed by that union, after comparison with a smaller local set. -/
theorem ae_tendsto_sub_flowMean_comp {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    {g : Ω → DistOn upperHalfPlaneOpens} (hgm : Measurable[𝒢] g)
    (hgh : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A ω))
    (hgc : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) fun ω => h ω - g ω)
    {ι : Type*} [Countable ι] {L : ι → Ω → Set ℂ} {g₂ : ι → Ω → DistOn upperHalfPlaneOpens}
    (hLm : ∀ i, Measurable[mΩ, hittingSigma] (L i)) (hLc : ∀ i, ∀ᵐ ω ∂P, L i ω ⊆ H ∧ IsOpen (H \ L i ω))
    (hLunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (L i ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (L i ω)) z))
    (hg₂ : ∀ i, IsLocalSetMean (L i) h P (g₂ i))
    {A' : ι → Ω → Set ℂ} {ℳ : ι → MeasurableSpace Ω} (hℳ : ∀ i, ℳ i ≤ mΩ)
    (hA'm : ∀ i, Measurable[mΩ, hittingSigma] (A' i))
    (hA'c : ∀ i, ∀ᵐ ω ∂P, A' i ω ⊆ H ∧ IsOpen (H \ A' i ω))
    (hloc : ∀ i, IsHistoryAvoidanceLocal (ℳ i) (A' i) h P)
    (hAℳ : ∀ i, Measurable[ℳ i, hittingSigma] A) (hAA' : ∀ i ω, A ω ∩ H ⊆ A' i ω)
    (hLℳ : ∀ i, Measurable[ℳ i, hittingSigma] (L i)) (hLA' : ∀ i ω, L i ω ∩ H ⊆ A' i ω)
    (h𝒢ℳ : ∀ i, 𝒢 ≤ germSigma A h ⊔ ℳ i)
    {S : ι → Set Ω} (hS : ∀ i, MeasurableSet[𝒢] (S i)) (hSA : ∀ i, ∀ᵐ ω ∂P, ω ∈ S i → A' i ω = A ω) :
    ∀ᵐ ω ∂P, ∀ i, ω ∈ S i → ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ A ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ - g₂ i ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ L i ω ∪ {z : ℂ | z.im = 0}, ∀ r > 0,
        Tendsto u (𝓝[freeNear (A ω) (L i ω) z₀ r] z₀) (𝓝 0) := by
  classical
  have hhm := hh.measurable
  refine ae_all_iff.2 fun i => ?_
  -- the marks of the larger union, with the germs of `A` and `L i`
  have hloc₁ : IsHistoryAvoidanceLocal (ℳ i ⊔ germSigma A h) (A' i) h P :=
    Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh (hℳ i) (hA'm i) (hloc i) (hAℳ i) (hAA' i)
  have hℳ₁ : ℳ i ⊔ germSigma A h ≤ mΩ := sup_le (hℳ i) (germSigma_le hAm hhm)
  have hloc₂ : IsHistoryAvoidanceLocal ((ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h) (A' i) h P :=
    Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℳ₁ (hA'm i) hloc₁
      ((hLℳ i).mono le_sup_left le_rfl) (hLA' i)
  have h𝒦 : (ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h ≤ mΩ := sup_le hℳ₁ (germSigma_le (hLm i) hhm)
  obtain ⟨g', hg'm, hg'h, hg'c⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh (hA'm i) h𝒦 hloc₂ (hA'c i)
  have h𝒥 : germSigma (A' i) h ⊔ ((ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h) ≤ mΩ :=
    sup_le (germSigma_le (hA'm i) hhm) h𝒦
  have hU : ∀ ω, H \ (A' i ω ∪ L i ω) = H \ A' i ω := fun ω => by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      exact ⟨hz, fun h' => hz' (Or.inl h')⟩
    · rintro ⟨hz, hz'⟩
      exact ⟨hz, fun h' => h'.elim hz' fun hL => hz' (hLA' i ω ⟨hL, hz⟩)⟩
  have hUf : (fun ω => H \ (A' i ω ∪ L i ω)) = fun ω => H \ A' i ω := funext hU
  have hg'm𝒥 : Measurable[germSigma (A' i) h ⊔ ((ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h)] g' :=
    hg'm.mono le_sup_left le_rfl
  -- the marked nested Proposition 3.8 for `A' i ⊇ L i`
  have hT := ae_tendsto_sub_of_condLaw_comp hh (hA'm i) (hLm i) (hA'c i) (hLc i) (hLunb i) h𝒥
    (le_sup_right.trans le_sup_right)
    (sup_le ((comap_le_germSigma (A' i) h).trans le_sup_left)
      ((comap_le_germSigma (L i) h).trans (le_sup_right.trans le_sup_right)))
    hg'm𝒥 (by filter_upwards [hg'h] with ω hω; rw [hU]; exact hω) (by rw [hUf]; exact hg'c) (hg₂ i)
  -- nested uniqueness: `g' = g` on `S i`
  have h𝒢𝒥 : 𝒢 ≤ germSigma (A' i) h ⊔ ((ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h) :=
    (h𝒢ℳ i).trans (sup_le ((le_sup_right.trans le_sup_left).trans le_sup_right)
      ((le_sup_left.trans le_sup_left).trans le_sup_right))
  have hEq := Aux61SlitV.ae_forall_apply_eq_of_le h𝒢𝒥 h𝒥 hhm hgm hg'm𝒥 hgc hg'c (hS i)
    (by filter_upwards [hSA i] with ω hω hωS; rw [hω hωS]) (O := fun ω => H \ A ω)
    (by filter_upwards [hA'c i, hSA i] with ω hω hωA hωS; rw [← hωA hωS]; exact ⟨hω.2, sdiff_subset⟩)
    (by filter_upwards [hgh] with ω hω _; exact hω)
    (by filter_upwards [hg'h, hSA i] with ω hω hωA hωS; rw [← hωA hωS]; exact hω)
  filter_upwards [hT, hEq, hSA i] with ω hTω hEqω hSAω hωS
  obtain ⟨u, hu, hrep, hlim⟩ := hTω
  have hA' : A' i ω = A ω := hSAω hωS
  rw [hU, hA'] at hu
  refine ⟨u, hu, fun φ hφ => ?_, fun z₀ hz₀ r hr => ?_⟩
  · rw [← hEqω hωS φ hφ]
    exact hrep φ (by rw [hU, hA']; exact hφ)
  · have := hlim z₀ hz₀ r hr
    rwa [hA'] at this

end InteractingSLE.Sec5.Aux61GPrime
