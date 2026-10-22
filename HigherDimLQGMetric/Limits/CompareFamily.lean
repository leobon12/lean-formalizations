import HigherDimLQGMetric.Limits.AeMapImage

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Closure support under two-sided random comparison for a varying tight
family of pure laws. -/
theorem l6c_compare_family_closure_good {d : ℕ}
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
    (hBT : IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, ν = P.map (B i)})
    (ν : ProbabilityMeasure C(Rd d × Rd d, ℝ))
    (hν : ν ∈ closure {ρ : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
      ∃ i ∈ S, (ρ : Measure C(Rd d × Rd d, ℝ)) = P.map (B i)}) :
    ∀ᵐ D ∂(ν : Measure C(Rd d × Rd d, ℝ)), IsContinuousMetric D ∧ IsProperFn D := by
  classical
  let _ : PolishSpace C(Rd d × Rd d, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable C(Rd d × Rd d, ℝ)
  obtain ⟨νs, hνs, hνlim⟩ := mem_closure_iff_seq_limit.mp hν
  have his (n : ℕ) : ∃ i ∈ S, (νs n : Measure C(Rd d × Rd d, ℝ)) = P.map (B i) := hνs n
  choose is hisS hisLaw using his
  let law : ℕ → ProbabilityMeasure
      (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)) :=
    fun n => l6c_compareLaw P A B (is n)
  have hJT : IsTightMeasureSet
      {((ρ : ProbabilityMeasure
        (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))) :
          Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))) |
        ρ ∈ range law} := by
    apply (l6c_compare_joint_tight P A B S hA.1 hBm hA.2.1 hBT).subset
    rintro ρ ⟨η, ⟨n, rfl⟩, rfl⟩
    exact ⟨is n, hisS n, rfl⟩
  obtain ⟨η, -, ψ, hψ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet hJT).tendsto_subseq
      (x := law) (fun n => subset_closure ⟨n, rfl⟩)
  have hBproj (n : ℕ) : (law n).map Prod.snd = νs n := by
    apply Subtype.ext
    change (P.map (fun ω => (A (is n) ω, B (is n) ω))).map Prod.snd =
      (νs n : Measure C(Rd d × Rd d, ℝ))
    rw [hisLaw n]
    simpa only [Function.comp_def] using
      AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
        ((hA.1 (is n) (hisS n)).prodMk (hBm (is n) (hisS n)))
  have hνψ : Tendsto (fun n => νs (ψ n)) atTop (𝓝 ν) :=
    hνlim.comp hψ.tendsto_atTop
  have hηB : η.map Prod.snd = ν := by
    have ht := ((ProbabilityMeasure.continuous_map continuous_snd).tendsto η).comp hlim
    change Tendsto (fun n => (law (ψ n)).map Prod.snd) atTop (𝓝 (η.map Prod.snd)) at ht
    have ht' : Tendsto (fun n => νs (ψ n)) atTop (𝓝 (η.map Prod.snd)) := by
      simpa only [hBproj] using ht
    exact tendsto_nhds_unique ht' hνψ
  have hgood : ∀ᵐ q ∂(η : Measure
      (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))),
      IsContinuousMetric q.2 ∧ IsProperFn q.2 :=
    l6c_compare_joint_limit_good P A B S hA hBm hAalg hBalg M hM hcmp
      (is ∘ ψ) (fun n => hisS (ψ n)) η hlim
  have hpush : ∀ᵐ D ∂((η : Measure
      (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ))).map Prod.snd),
      IsContinuousMetric D ∧ IsProperFn D :=
    l6c_ae_map_of_ae_sb
      (η : Measure (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)))
      (Prod.snd : C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ) →
        C(Rd d × Rd d, ℝ)) measurable_snd
      (fun D => IsContinuousMetric D ∧ IsProperFn D) hgood
  rw [← ProbabilityMeasure.toMeasure_map, hηB] at hpush
  exact hpush

/-- Varying-law random comparison preserves the full tight-family condition. -/
theorem l6c_tightFamily_of_randomCompare {d : ℕ}
    {ι Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ι → Ω → C(Rd d × Rd d, ℝ)) (S : Set ι)
    (hA : TightFamily P A S)
    (hBm : ∀ i ∈ S, AEMeasurable (B i) P)
    (hAalg : ∀ i ∈ S, ∀ᵐ ω ∂P, A i ω ∈ metricAlgSet_select)
    (hBalg : ∀ i ∈ S, ∀ᵐ ω ∂P, B i ω ∈ metricAlgSet_select)
    (M : Ω → ℝ) (hM : Measurable M)
    (hcmp : ∀ i ∈ S, ∀ᵐ ω ∂P, ∀ p : Rd d × Rd d,
      Real.exp (-M ω) * A i ω p ≤ B i ω p ∧
      B i ω p ≤ Real.exp (M ω) * A i ω p) :
    TightFamily P B S := by
  have hBT := l6c_tight_of_randomCompare P A B S hA hBm hAalg hBalg M hM hcmp
  exact ⟨hBm, hBT,
    l6c_compare_family_closure_good P A B S hA hBm hAalg hBalg M hM hcmp hBT⟩

end HigherDimLQGMetric
