import HigherDimLQGMetric.Limits.CompareClosed
import HigherDimLQGMetric.Limits.LengthLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

def l6c_compareLaw {d : ℕ} {ι Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → Ω → C(Rd d × Rd d, ℝ)) (i : ι) :
    ProbabilityMeasure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)) :=
  ⟨P.map (fun ω => (A i ω, B i ω)), inferInstance⟩

/-- In a jointly convergent sequence, a fixed random comparison factor
survives as some finite deterministic comparison factor almost surely. -/
theorem l6c_compare_joint_limit_good {d : ℕ}
    {ι Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → Ω → C(Rd d × Rd d, ℝ)) (S : Set ι)
    (hA : TightFamily P A S)
    (hBm : ∀ i ∈ S, AEMeasurable (B i) P)
    (hAalg : ∀ i ∈ S, ∀ᵐ ω ∂P, A i ω ∈ metricAlgSet_select)
    (hBalg : ∀ i ∈ S, ∀ᵐ ω ∂P, B i ω ∈ metricAlgSet_select)
    (M : Ω → ℝ) (hM : Measurable M)
    (hcmp : ∀ i ∈ S, ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A i ω p ≤ B i ω p ∧
      B i ω p ≤ Real.exp (M ω) * A i ω p)
    (is : ℕ → ι) (his : ∀ n, is n ∈ S)
    (η : ProbabilityMeasure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)))
    (hconv : Tendsto (fun n => l6c_compareLaw P A B (is n)) atTop (𝓝 η)) :
    ∀ᵐ q ∂(η : Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))),
      IsContinuousMetric q.2 ∧ IsProperFn q.2 := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  have hprojA (n : ℕ) :
      (l6c_compareLaw P A B (is n)).map Prod.fst =
        (⟨P.map (A (is n)), inferInstance⟩ : ProbabilityMeasure C(Rd d × Rd d, ℝ)) := by
    apply Subtype.ext
    change (P.map (fun ω => (A (is n) ω, B (is n) ω))).map Prod.fst = P.map (A (is n))
    simpa only [Function.comp_def] using
      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
        ((hA.1 (is n) (his n)).prodMk (hBm (is n) (his n)))
  have hAlim : Tendsto
      (fun n => (l6c_compareLaw P A B (is n)).map Prod.fst)
      atTop (𝓝 (η.map Prod.fst)) := by
    have ht := ((ProbabilityMeasure.continuous_map continuous_fst).tendsto η).comp hconv
    change Tendsto (fun n => (l6c_compareLaw P A B (is n)).map Prod.fst)
      atTop (𝓝 (η.map Prod.fst)) at ht
    exact ht
  have hAmem : η.map Prod.fst ∈ closure
      {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ i ∈ S, (ν : Measure C(Rd d × Rd d, ℝ)) = P.map (A i)} :=
    mem_closure_of_tendsto hAlim
      (Filter.Eventually.of_forall fun n => ⟨is n, his n, by rw [hprojA]; rfl⟩)
  have hAgood : ∀ᵐ q ∂(η : Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))),
      IsContinuousMetric q.1 ∧ IsProperFn q.1 := by
    have h := hA.2.2 (η.map Prod.fst) hAmem
    rw [ProbabilityMeasure.toMeasure_map] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hCN (N : ℕ) : P {ω | M ω ≤ N} ≤
      (η : Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)))
        (l6c_compareClosed (N : ℝ)) := by
    have hmass (n : ℕ) : P {ω | M ω ≤ N} ≤
        (P.map (fun ω => (A (is n) ω, B (is n) ω)))
          (l6c_compareClosed (N : ℝ)) :=
      l6c_compareClosed_mass P A B M hM (is n)
        (hA.1 (is n) (his n)) (hBm (is n) (his n))
        (hAalg (is n) (his n)) (hBalg (is n) (his n))
        (hcmp (is n) (his n)) N
    have hlimsup : P {ω | M ω ≤ N} ≤
        limsup (fun n => (P.map (fun ω => (A (is n) ω, B (is n) ω)))
          (l6c_compareClosed (N : ℝ))) atTop := by
      simpa only [limsup_const] using
        (limsup_le_limsup (f := atTop) (Filter.Eventually.of_forall hmass)
          (u := fun _ : ℕ => P {ω | M ω ≤ N}))
    exact hlimsup.trans
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
        (l6c_compareClosed_isClosed (N : ℝ)))
  have hMevent : Monotone (fun N : ℕ => {ω : Ω | M ω ≤ N}) := by
    intro n m hnm ω hω
    change M ω ≤ (n : ℝ) at hω
    change M ω ≤ (m : ℝ)
    exact hω.trans (by exact_mod_cast hnm)
  have hMuniv : (⋃ N : ℕ, {ω : Ω | M ω ≤ N}) = univ := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    obtain ⟨N, hN⟩ := exists_nat_ge (M ω)
    exact ⟨N, hN⟩
  have hMmass : (⨆ N : ℕ, P {ω | M ω ≤ N}) = 1 := by
    rw [← hMevent.measure_iUnion, hMuniv, measure_univ]
  let F : Set (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)) :=
    ⋃ N : ℕ, l6c_compareClosed (N : ℝ)
  have hF : MeasurableSet F := MeasurableSet.iUnion fun N =>
    (l6c_compareClosed_isClosed (N : ℝ)).measurableSet
  have hFmass : (η : Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))) F = 1 := by
    apply le_antisymm prob_le_one
    rw [← hMmass]
    apply iSup_le
    intro N
    exact (hCN N).trans (measure_mono (show l6c_compareClosed (N : ℝ) ⊆ F from
      fun q hq => mem_iUnion.mpr ⟨N, hq⟩))
  have hFae : ∀ᵐ q ∂(η : Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))),
      q ∈ F := (ae_mem_iff_measure_eq hF.nullMeasurableSet).2 (by simpa using hFmass)
  filter_upwards [hAgood, hFae] with q hq hFq
  change q ∈ ⋃ N : ℕ, l6c_compareClosed (N : ℝ) at hFq
  obtain ⟨N, hN⟩ := mem_iUnion.mp hFq
  exact l6c_good_of_compare hq hN.1 (Real.exp_pos _) (Real.exp_pos _).le hN.2

end HigherDimLQGMetric
