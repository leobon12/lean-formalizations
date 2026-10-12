import MeshOnly.MeshOnlyHeatPoissonLaw

/-! Support control for the actual absorbed walk at a Poisson horizon. Only
neighbors of active vertices can be visited before absorption. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] (N : FiniteConductanceNetwork V)

lemma uniformizedStepPMF_mem_support_cases (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) {v w : V} (hw : w ∈ (N.uniformizedStepPMF m hm S v).support) :
    w = v ∨ (v ∈ S ∧ N.a v w ≠ 0) := by
  classical
  by_cases hwv : w = v
  · exact Or.inl hwv
  right
  have hne := (PMF.mem_support_iff _ _).mp hw
  by_cases hv : v ∈ S
  · refine ⟨hv, ?_⟩
    intro ha
    simp [uniformizedStepPMF_apply, uniformizedTransition, hv, hwv, ha] at hne
  · simp [uniformizedStepPMF_apply, uniformizedTransition, hv, hwv] at hne

lemma uniformizedNStepPMF_support_subset (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S K : Set V)
    (hK : ∀ v ∈ K, v ∈ S → ∀ w, N.a v w ≠ 0 → w ∈ K)
    (n : ℕ) {v : V} (hv : v ∈ K) :
    (N.uniformizedNStepPMF m hm S n v).support ⊆ K := by
  induction n generalizing v with
  | zero => simpa [uniformizedNStepPMF] using Set.singleton_subset_iff.mpr hv
  | succ n ih =>
    intro y hy
    rw [uniformizedNStepPMF, PMF.mem_support_bind_iff] at hy
    obtain ⟨w, hw, hy⟩ := hy
    apply ih (v := w) _ hy
    rcases N.uniformizedStepPMF_mem_support_cases m hm S hw with h | ⟨hS, ha⟩
    · exact h.symm ▸ hv
    · exact hK v hv hS w ha

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The same reachable region works for every Poisson parameter. -/
theorem poissonizedUniformizedLaw_ae_mem (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S K : Set V)
    (hK : ∀ v ∈ K, v ∈ S → ∀ w, N.a v w ≠ 0 → w ∈ K)
    {v : V} (hv : v ∈ K) (t : ℝ≥0) :
    ∀ᵐ w ∂N.poissonizedUniformizedLaw m hm S v t, w ∈ K := by
  let r : ℝ≥0 := ⟨(t : ℝ) * N.uniformizationRate m,
    mul_nonneg t.coe_nonneg (N.uniformizationRate_pos m hm).le⟩
  let p := (poissonMeasure r).toPMF.bind (fun n => N.uniformizedNStepPMF m hm S n v)
  have hsub : p.support ⊆ K := by
    intro y hy
    obtain ⟨n, _, hyn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
    exact N.uniformizedNStepPMF_support_subset m hm S K hK n hv hyn
  change ∀ᵐ w ∂p.toMeasure, w ∈ K
  apply ae_iff.mpr
  apply (p.toMeasure_apply_eq_zero_iff (Set.toFinite _).measurableSet).mpr
  exact Set.disjoint_left.mpr (fun w hw hnot => hnot (hsub hw))

end BouRabeeGwynne.FiniteConductanceNetwork
