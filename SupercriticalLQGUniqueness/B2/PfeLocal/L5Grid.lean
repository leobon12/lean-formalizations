import SupercriticalLQGUniqueness.B2.PfeLocal.L5ES

 












set_option autoImplicit false
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric.LM

 
def l5VLines (ε c : ℝ) : Set ℂ := {x | ∃ k : ℤ, x.re = ε * (k + c)}

 
def l5HLines (ε c : ℝ) : Set ℂ := {x | ∃ k : ℤ, x.im = ε * (k + c)}

theorem l5_measurableSet_VLines (ε c : ℝ) : MeasurableSet (l5VLines ε c) := by
  have : l5VLines ε c = ⋃ k : ℤ, Complex.re ⁻¹' {ε * (k + c)} := by ext x; simp [l5VLines]
  rw [this]
  exact MeasurableSet.iUnion fun k => Complex.measurable_re (measurableSet_singleton _)

theorem l5_measurableSet_HLines (ε c : ℝ) : MeasurableSet (l5HLines ε c) := by
  have : l5HLines ε c = ⋃ k : ℤ, Complex.im ⁻¹' {ε * (k + c)} := by ext x; simp [l5HLines]
  rw [this]
  exact MeasurableSet.iUnion fun k => Complex.measurable_im (measurableSet_singleton _)

theorem l5_grid_eq (ε : ℝ) (θ : ℝ × ℝ) : t17Grid ε θ = l5VLines ε θ.1 ∪ l5HLines ε θ.2 := rfl

 
theorem l5_shift_disjoint {ε : ℝ} (hε : 0 < ε) {M i i' : ℕ} (hi : i < M) (hi' : i' < M)
    (hii : i ≠ i') {u : ℝ} {k k' : ℤ} (h1 : u = ε * (k + (i : ℝ) / M))
    (h2 : u = ε * (k' + (i' : ℝ) / M)) : False := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hi)
  have h3 : ((k : ℝ) + i / M) = k' + i' / M := by
    have := h1.symm.trans h2
    exact mul_left_cancel₀ hε.ne' this
  have h4 : ((k - k' : ℤ) : ℝ) * M = (i' : ℝ) - i := by
    have : ((k : ℝ) - k') * M = (i' - i) := by
      field_simp at h3
      linarith
    push_cast
    exact this
  have h5 : (k - k') * (M : ℤ) = (i' : ℤ) - i := by exact_mod_cast h4
  have hi1 : (i : ℤ) < M := by exact_mod_cast hi
  have hi2 : (i' : ℤ) < M := by exact_mod_cast hi'
  have hne : (i : ℤ) ≠ i' := by exact_mod_cast hii
  rcases lt_trichotomy (k - k') 0 with h | h | h
  · have : (k - k') * (M : ℤ) ≤ -M := by nlinarith
    omega
  · rw [h, zero_mul] at h5
    omega
  · have : (M : ℤ) ≤ (k - k') * (M : ℤ) := by nlinarith
    omega

 

theorem l5_grid_sum (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ} (hc : T17Curve (D.pt ∘ P) a b)
    (hPe : ContinuousOn P (Icc a b)) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∑ i ∈ Finset.range M, pathLengthIn D P a b (t17Grid ε ((i : ℝ) / M, (i : ℝ) / M)) ≤
      2 * D.len P a b := by
  set μ := t17LenMeas (D.pt ∘ P) a b
  have hlen : D.len P a b = μ (Icc a b) := (t17LenMeas_Icc hc).symm
  have hV : ∑ i ∈ Finset.range M, μ (P ⁻¹' l5VLines ε ((i : ℝ) / M) ∩ Icc a b) ≤ μ (Icc a b) := by
    rw [← measure_biUnion_finset]
    · exact measure_mono (iUnion₂_subset fun i _ => inter_subset_right)
    · intro i hi i' hi' hii
      refine Set.disjoint_left.2 fun t ht ht' => ?_
      obtain ⟨k, hk⟩ := ht.1
      obtain ⟨k', hk'⟩ := ht'.1
      exact l5_shift_disjoint hε (Finset.mem_range.1 hi) (Finset.mem_range.1 hi') hii hk hk'
    · exact fun i _ => l5_measurableSet_preimage hPe (l5_measurableSet_VLines _ _)
  have hH : ∑ i ∈ Finset.range M, μ (P ⁻¹' l5HLines ε ((i : ℝ) / M) ∩ Icc a b) ≤ μ (Icc a b) := by
    rw [← measure_biUnion_finset]
    · exact measure_mono (iUnion₂_subset fun i _ => inter_subset_right)
    · intro i hi i' hi' hii
      refine Set.disjoint_left.2 fun t ht ht' => ?_
      obtain ⟨k, hk⟩ := ht.1
      obtain ⟨k', hk'⟩ := ht'.1
      exact l5_shift_disjoint hε (Finset.mem_range.1 hi) (Finset.mem_range.1 hi') hii hk hk'
    · exact fun i _ => l5_measurableSet_preimage hPe (l5_measurableSet_HLines _ _)
  calc ∑ i ∈ Finset.range M, pathLengthIn D P a b (t17Grid ε ((i : ℝ) / M, (i : ℝ) / M))
      ≤ ∑ i ∈ Finset.range M, (μ (P ⁻¹' l5VLines ε ((i : ℝ) / M) ∩ Icc a b) +
          μ (P ⁻¹' l5HLines ε ((i : ℝ) / M) ∩ Icc a b)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        unfold pathLengthIn
        rw [l5_grid_eq, preimage_union, union_inter_distrib_right]
        exact measure_union_le _ _
    _ = ∑ i ∈ Finset.range M, μ (P ⁻¹' l5VLines ε ((i : ℝ) / M) ∩ Icc a b) +
          ∑ i ∈ Finset.range M, μ (P ⁻¹' l5HLines ε ((i : ℝ) / M) ∩ Icc a b) :=
        Finset.sum_add_distrib
    _ ≤ μ (Icc a b) + μ (Icc a b) := add_le_add hV hH
    _ = 2 * D.len P a b := by rw [hlen, two_mul]

 
theorem l5_sum_sq_le {α : Type} (s : Finset α) (g : α → ℝ) {m : ℝ} (h0 : ∀ x ∈ s, 0 ≤ g x)
    (hm : ∀ x ∈ s, g x ≤ m) : ∑ x ∈ s, g x ^ 2 ≤ m * ∑ x ∈ s, g x := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x hx => by
    rw [sq]; exact mul_le_mul_of_nonneg_right (hm x hx) (h0 x hx)

end SupercriticalLQGUniqueness.B2.PfeLocal
