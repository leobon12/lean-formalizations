import LQGMetric.Field.CameronMartin
import LQGMetric.Blueprint.M2Defs




 




























set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProducerField

 

 
theorem exists_saturated_good_event {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (act : X → ℝ → X) (N : X → X) (hN : Measurable N)
    (hNact : ∀ x c, N (act x c) = N x) (horbit : ∀ x, ∃ c, act (N x) c = x)
    {ι : Type*} [Countable ι] (p : ι → X → Prop)
    (hsat : ∀ i x c, p i x → p i (act x c))
    (hp : ∀ i, ∀ᵐ y ∂(μ.map N), p i y)
    {S E₀ : Set X} (hE₀ : MeasurableSet E₀) (hE₀sat : ∀ x c, x ∈ E₀ ↔ act x c ∈ E₀)
    (hSsat : ∀ x c, (∀ i, p i x) → (x ∈ S ↔ act x c ∈ S))
    (hSE : ∀ᵐ y ∂(μ.map N), y ∈ E₀ → y ∈ S) :
    ∃ E : Set X, MeasurableSet E ∧ (∀ x c, x ∈ E ↔ act x c ∈ E) ∧ E ⊆ S ∧
      (∀ x ∈ E, ∀ i, p i x) ∧ E =ᵐ[μ] E₀ := by
  set ν := μ.map N with hν
  set B : Set X := {y | ¬ ∀ i, p i y} ∪ (E₀ \ S) with hB
  have hB0 : ν B = 0 := by
    refine measure_union_null ?_ ?_
    · have : ∀ᵐ y ∂ν, ∀ i, p i y := ae_all_iff.2 hp
      rwa [ae_iff] at this
    · have h2 := hSE
      rw [ae_iff] at h2
      refine measure_mono_null ?_ h2
      rintro y ⟨hy, hyS⟩ hcon
      exact hyS (hcon hy)
  set T := toMeasurable ν B with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable ν B
  have hT0 : ν T = 0 := by rw [hT, measure_toMeasurable]; exact hB0
  
  have hE₀N : ∀ x, x ∈ E₀ ↔ N x ∈ E₀ := by
    intro x
    obtain ⟨c, hc⟩ := horbit x
    have := hE₀sat (N x) c
    rw [hc] at this
    exact this.symm
  refine ⟨N ⁻¹' (E₀ \ T), (hE₀.diff hTm).preimage hN, ?_, ?_, ?_, ?_⟩
  · intro x c
    simp only [mem_preimage, hNact]
  · rintro x ⟨hxE, hxT⟩
    have hgood : ∀ i, p i (N x) := by
      by_contra hcon
      exact hxT (subset_toMeasurable ν B (Or.inl hcon))
    have hNS : N x ∈ S := by
      by_contra hcon
      exact hxT (subset_toMeasurable ν B (Or.inr ⟨hxE, hcon⟩))
    obtain ⟨c, hc⟩ := horbit x
    have := (hSsat (N x) c hgood).1 hNS
    rwa [hc] at this
  · rintro x ⟨-, hxT⟩ i
    have hgood : ∀ i, p i (N x) := by
      by_contra hcon
      exact hxT (subset_toMeasurable ν B (Or.inl hcon))
    obtain ⟨c, hc⟩ := horbit x
    have := hsat i (N x) c (hgood i)
    rwa [hc] at this
  · 
    have heq : N ⁻¹' (E₀ \ T) = E₀ \ N ⁻¹' T := by
      ext x
      simp only [mem_preimage, mem_sdiff]
      rw [← hE₀N x]
    have hnull : μ (N ⁻¹' T) = 0 := by
      rw [← Measure.map_apply hN hTm]; exact hT0
    rw [heq]
    exact sdiff_null_ae_eq_self hnull

 


theorem map_null_of_retraction {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (N N₁ : X → X) (hN : Measurable N) (hN₁ : Measurable N₁)
    (hret : ∀ᵐ u ∂μ, N₁ (N u) = u) {Bad : Set X} (hBad : μ Bad = 0)
    (hinv : ∀ y ∈ Bad, N₁ y ∈ Bad) : (μ.map N) Bad = 0 := by
  set B₀ := toMeasurable μ Bad with hB₀
  have hB₀m : MeasurableSet B₀ := measurableSet_toMeasurable μ Bad
  have hB₀0 : μ B₀ = 0 := by rw [hB₀, measure_toMeasurable]; exact hBad
  have hsub : Bad ⊆ N₁ ⁻¹' B₀ := fun y hy => subset_toMeasurable μ Bad (hinv y hy)
  refine measure_mono_null hsub ?_
  rw [Measure.map_apply hN (hB₀m.preimage hN₁)]
  have heq : N ⁻¹' (N₁ ⁻¹' B₀) =ᵐ[μ] B₀ := by
    filter_upwards [hret] with u hu
    simp only [eq_iff_iff]
    change N₁ (N u) ∈ B₀ ↔ u ∈ B₀
    rw [hu]
  rw [measure_congr heq]
  exact hB₀0

 



theorem exists_saturated_good_event_of_retraction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (act : X → ℝ → X) (N N₁ : X → X) (hN : Measurable N) (hN₁ : Measurable N₁)
    (hNact : ∀ x c, N (act x c) = N x) (horbit : ∀ x, ∃ c, act (N x) c = x)
    (hN₁orbit : ∀ y, ∃ c, N₁ y = act y c) (hret : ∀ᵐ u ∂μ, N₁ (N u) = u)
    {ι : Type*} [Countable ι] (p : ι → X → Prop)
    (hsat : ∀ i x c, p i x → p i (act x c))
    (hsat' : ∀ i x c, p i (act x c) → p i x)
    {S E₀ : Set X} (hE₀ : MeasurableSet E₀) (hE₀sat : ∀ x c, x ∈ E₀ ↔ act x c ∈ E₀)
    (hSsat : ∀ x c, (∀ i, p i x) → (x ∈ S ↔ act x c ∈ S))
    (hbad : μ ({y | ¬ ∀ i, p i y} ∪ (E₀ \ S)) = 0) :
    ∃ E : Set X, MeasurableSet E ∧ (∀ x c, x ∈ E ↔ act x c ∈ E) ∧ E ⊆ S ∧
      (∀ x ∈ E, ∀ i, p i x) ∧ E =ᵐ[μ] E₀ := by
  set Bad : Set X := {y | ¬ ∀ i, p i y} ∪ (E₀ \ S) with hBad
  have hinv : ∀ y ∈ Bad, N₁ y ∈ Bad := by
    intro y hy
    obtain ⟨c, hc⟩ := hN₁orbit y
    rw [hc]
    rcases hy with hy | ⟨hyE, hyS⟩
    · left
      intro hall
      exact hy fun i => hsat' i y c (hall i)
    · by_cases hg : ∀ i, p i y
      · right
        exact ⟨(hE₀sat y c).1 hyE, fun h => hyS ((hSsat y c hg).2 h)⟩
      · left
        intro hall
        exact hg fun i => hsat' i y c (hall i)
  have hν : (μ.map N) Bad = 0 := map_null_of_retraction μ N N₁ hN hN₁ hret hbad hinv
  have hp : ∀ i, ∀ᵐ y ∂(μ.map N), p i y := by
    intro i
    rw [ae_iff]
    refine measure_mono_null ?_ hν
    intro y hy
    exact Or.inl fun hall => hy (hall i)
  have hSE : ∀ᵐ y ∂(μ.map N), y ∈ E₀ → y ∈ S := by
    rw [ae_iff]
    refine measure_mono_null ?_ hν
    intro y hy
    simp only [mem_ofPred_eq, Classical.not_imp] at hy
    exact Or.inr ⟨hy.1, hy.2⟩
  exact exists_saturated_good_event μ act N hN hNact horbit p hsat hp hE₀ hE₀sat hSsat hSE

 

open LQGMetric

theorem ofCont_const_apply (c : ℝ) (φ : TestC) :
    ofCont (ContinuousMap.const ℂ c) φ = c * ∫ z, φ z := by
  simp only [ofCont]
  rw [Distribution.ofFun_apply
    ((ContinuousMap.const ℂ c).continuous.locallyIntegrable.locallyIntegrableOn _)]
  change ∫ z, φ z * c = c * ∫ z, φ z
  rw [integral_mul_const, mul_comm]

theorem addConst_apply (u : DistC) (c : ℝ) (φ : TestC) :
    addConst u c φ = u φ + c * ∫ z, φ z := by
  simp only [addConst, addFun]
  rw [add_apply, ofCont_const_apply]

 
def nrm (φ₀ : TestC) (u : DistC) : DistC := addConst u (-(u φ₀))

theorem nrm_apply (φ₀ : TestC) (u : DistC) (φ : TestC) :
    nrm φ₀ u φ = u φ - u φ₀ * ∫ z, φ z := by
  rw [nrm, addConst_apply]; ring

theorem nrm_addConst (φ₀ : TestC) (hφ₀ : ∫ z, φ₀ z = 1) (u : DistC) (c : ℝ) :
    nrm φ₀ (addConst u c) = nrm φ₀ u := by
  ext φ
  rw [nrm_apply, nrm_apply, addConst_apply, addConst_apply, hφ₀]
  ring

theorem addConst_nrm (φ₀ : TestC) (u : DistC) :
    addConst (nrm φ₀ u) (u φ₀) = u := by
  ext φ
  rw [addConst_apply, nrm_apply]
  ring

theorem measurable_nrm (φ₀ : TestC) : Measurable (nrm φ₀) := by
  have key : Measurable fun u : DistC => fun φ : TestC => nrm φ₀ u φ := by
    refine measurable_pi_iff.mpr fun φ => ?_
    simp only [nrm_apply]
    exact (measurable_evalDist φ).sub ((measurable_evalDist φ₀).mul_const _)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact key ht

 

theorem mem_fieldSigma0On_id_addConst {V : Set ℂ} {E₀ : Set DistC}
    (hE : @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigma0On (id : DistC → DistC) V) E₀)
    (u : DistC) (c : ℝ) : u ∈ E₀ ↔ addConst u c ∈ E₀ := by
  unfold LQGMetric.Blueprint.fieldSigma0On at hE
  obtain ⟨s, -, rfl⟩ := hE
  simp only [mem_preimage, id_eq]
  have : (fun ψ : {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ V} => addConst u c ψ.1.1) =
      (fun ψ : {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ V} => u ψ.1.1) := by
    funext ψ
    rw [addConst_apply, ψ.1.2, mul_zero, add_zero]
  rw [this]

theorem mem_fieldSigmaClosed0_id_addConst {K : Set ℂ} {E₀ : Set DistC}
    (hE : @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) E₀)
    (u : DistC) (c : ℝ) : u ∈ E₀ ↔ addConst u c ∈ E₀ := by
  unfold LQGMetric.Blueprint.fieldSigmaClosed0 at hE
  have h1 := MeasurableSpace.measurableSet_iInf.mp (MeasurableSpace.measurableSet_iInf.mp hE 1)
    one_pos
  exact mem_fieldSigma0On_id_addConst h1 u c

theorem fieldSigmaClosed0_id_le (K : Set ℂ) :
    LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K ≤
      (inferInstance : MeasurableSpace DistC) := by
  refine iInf₂_le_of_le 1 one_pos ?_
  unfold LQGMetric.Blueprint.fieldSigma0On
  refine Measurable.comap_le ?_
  exact measurable_pi_iff.mpr fun ψ => (LQGMetric.measurable_evalDist ψ.1.1).comp measurable_id

 

 



theorem exists_fieldEvent_v2 (μ : Measure DistC) (φ₀ : TestC) (hφ₀ : ∫ z, φ₀ z = 1)
    {ι : Type*} [Countable ι] (p : ι → DistC → Prop)
    (hsat : ∀ i u c, p i u → p i (addConst u c))
    (hp : ∀ i, ∀ᵐ y ∂(μ.map (nrm φ₀)), p i y)
    {K : Set ℂ} {S E₀ : Set DistC}
    (hE₀ : @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC) K) E₀)
    (hSsat : ∀ u c, (∀ i, p i u) → (u ∈ S ↔ addConst u c ∈ S))
    (hSE : ∀ᵐ y ∂(μ.map (nrm φ₀)), y ∈ E₀ → y ∈ S) :
    ∃ E : Set DistC, MeasurableSet E ∧ (∀ u c, u ∈ E ↔ addConst u c ∈ E) ∧ E ⊆ S ∧
      (∀ u ∈ E, ∀ i, p i u) ∧ E =ᵐ[μ] E₀ :=
  exists_saturated_good_event μ addConst (nrm φ₀) (measurable_nrm φ₀)
    (fun u c => nrm_addConst φ₀ hφ₀ u c) (fun u => ⟨u φ₀, addConst_nrm φ₀ u⟩) p hsat hp
    (fieldSigmaClosed0_id_le K E₀ hE₀) (mem_fieldSigmaClosed0_id_addConst hE₀) hSsat hSE

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProducerField

