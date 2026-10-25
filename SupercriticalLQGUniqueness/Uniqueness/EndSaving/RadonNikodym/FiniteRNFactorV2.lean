import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.EnergyV2




 





set_option autoImplicit false
noncomputable section
open Set Finset MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
open LQGMetric (DistC TestC)

private theorem cmDensity_zero (g : DistC) :
    LQGMetric.cmDensity (0 : TestC) (LQGMetric.pair0 g) = 1 := by
  have hE : LQGMetric.gradEnergy (⇑(0 : TestC)) = 0 := by
    simp only [LQGMetric.gradEnergy, FunLike.coe_zero, Pi.zero_apply,
      fderiv_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      integral_zero, mul_zero]
  have hC : LQGMetric.pair0 g (LQGMetric.cmTest0 (0 : TestC)) = 0 := by
    change g (LQGMetric.cmTest (0 : TestC)) = 0
    have hz : LQGMetric.cmTest (0 : TestC) = 0 := by
      ext x
      have hLap : Laplacian.laplacian (fun _ : ℂ => (0 : ℝ)) = 0 :=
        InnerProductSpace.laplacian_const
      change -(2 * Real.pi)⁻¹ *
        Laplacian.laplacian (fun _ : ℂ => (0 : ℝ)) x = 0
      rw [hLap]
      simp only [Pi.zero_apply, mul_zero]
    rw [hz, map_zero]
  rw [LQGMetric.cmDensity, hE, hC]
  norm_num

 
theorem tsupport_finset_sum_subset {ι : Type} (Z : Finset ι) (f : ι → TestC) :
    tsupport (⇑(∑ i ∈ Z, f i : TestC) : ℂ → ℝ) ⊆
      ⋃ i ∈ Z, tsupport (⇑(f i) : ℂ → ℝ) := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
      simpa only [sum_empty, FunLike.coe_zero, tsupport_zero] using
        (Set.empty_subset (⋃ i ∈ (∅ : Finset ι),
          tsupport (⇑(f i) : ℂ → ℝ)))
  | @insert a S ha ih =>
      rw [sum_insert ha]
      change tsupport ((⇑(f a) : ℂ → ℝ) +
        (⇑(∑ i ∈ S, f i : TestC) : ℂ → ℝ)) ⊆ _
      intro x hx
      have hx' := (tsupport_add _ _) hx
      rcases hx' with hxa | hxS
      · exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a S, hxa⟩
      · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ih hxS)
        exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hxi⟩

 

theorem cmDensity_finset_sum_of_disjoint {ι : Type} [DecidableEq ι]
    (Z : Finset ι) (f : ι → TestC)
    (hdisj : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
      Disjoint (tsupport (⇑(f i) : ℂ → ℝ))
        (tsupport (⇑(f j) : ℂ → ℝ)))
    (g : DistC) :
    LQGMetric.cmDensity (∑ i ∈ Z, f i) (LQGMetric.pair0 g) =
      ∏ i ∈ Z, LQGMetric.cmDensity (f i) (LQGMetric.pair0 g) := by
  induction Z using Finset.induction_on with
  | empty =>
      simp only [sum_empty]
      exact cmDensity_zero g
  | @insert a S ha ih =>
      have hs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
          Disjoint (tsupport (⇑(f i) : ℂ → ℝ))
            (tsupport (⇑(f j) : ℂ → ℝ)) := by
        intro i hi j hj hij
        exact hdisj i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij
      have hsep : Disjoint (tsupport (⇑(f a) : ℂ → ℝ))
          (tsupport (⇑(∑ i ∈ S, f i : TestC) : ℂ → ℝ)) := by
        apply Set.disjoint_left.mpr
        intro x hxa hxsum
        obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp
          (tsupport_finset_sum_subset S f hxsum)
        exact Set.disjoint_left.mp
          (hdisj a (Finset.mem_insert_self a S) j
            (Finset.mem_insert_of_mem hj) (by
              intro heq
              exact ha (heq ▸ hj)))
          hxa hxj
      rw [sum_insert ha, prod_insert ha,
        cmDensity_add_of_disjoint (f a) (∑ i ∈ S, f i) hsep g,
        ih hs]

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
