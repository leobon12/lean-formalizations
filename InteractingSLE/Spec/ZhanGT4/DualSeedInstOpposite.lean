/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstOwn

/-!
# The actual opposite seeded view satisfies D9

Packet PROVE-ZHAN-GT4-A22. Fix a positive first prefix. The full image of
the opposite enclosure clears every integrated seed access. All constants
below are chosen before the opposite path and stopping horizon.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (fwdMap fwdHull)

/-- Protected enclosures supply the actual selected opposite-view D9
constants for integrated seeds, uniformly over the entire second prefix. -/
theorem exists_seedTView_D9Const_of_enclosures {n : ℕ} {H₁ H₂ : Set ℂ}
    {δ p q d S s Tm κ : ℝ} (hp : A1SeedField.IsProtectedPair H₁ H₂ δ p q d)
    (rr : Fin n → ℝ) (W₁ Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ)
    (hW₁ : Continuous W₁) (h0₁ : W₁ 0 = 0) (hS : 0 < S)
    (hs : s ∈ Ioc (0 : ℝ) S) (hSm : S ≤ Tm) (hK₁ : fwdHull W₁ S ⊆ H₁)
    (hlo : IsSeedCoordinate W₁ Vlo S) (hhi : IsSeedCoordinate W₁ Vhi S)
    (hseed : ∀ m, IsSeedCoordinate W₁ (V m) S)
    (hVI : ∀ m, V m s ∈ uIcc (Vlo s) (Vhi s)) (hinj : Function.Injective fun m => V m s) :
    ∃ r a₀ γ Γ lam : ℝ, 0 < r ∧ 0 < a₀ ∧ 0 < γ ∧
      ∀ (W₂ : ℝ → ℝ) (T : ℝ), Continuous W₂ → W₂ 0 = p → 0 < T → T ≤ Tm →
        fwdHull W₂ T ⊆ H₂ →
        (seedTView κ rr W₁ W₂ (seedTSrcClock W₁ W₂ T) (seedTSrcDriver W₁ W₂ T) V s).D9Const
          (fwdHull (fun u => W₁ u - p) s) T r a₀ γ Γ lam := by
  have hsI := Ioc_subset_Icc_self hs
  have hsrc := closure_mono hK₁ (start_mem_closure_fwdHull hW₁ hS)
  obtain ⟨rseed, hrseed, hseedclear⟩ :=
    exists_seed_clearance_of_enclosures hp.hull₁ hp.hull₂ hp.sep_pos hp.sep
  obtain ⟨rtip, hrtip, htip⟩ :=
    exists_le_norm_fwdMap_uniform hp.hull₁ hp.hull₂.2.1 hp.hull₂.1 hp.sep_pos hp.sep
  let ρ := min rseed rtip
  have hρ : 0 < ρ := lt_min hrseed hrtip
  let E := transl (-p) (frzChart W₁ s '' H₂)
  have hE : IsHPHull E := isHPHull_transl
    (isHPHull_frzChart_enclosure hW₁ h0₁ hS hsI hp.hull₂ hp.sep_pos hp.sep hK₁) (-p)
  let z : Option (Fin n) → ℝ := fun i => i.elim (W₁ s - p) (fun m => V m s - p)
  have hz : Function.Injective z := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        apply False.elim ((hseed j).ne s hs ?_)
        change W₁ s - p = V j s - p at he
        linarith
    | some i =>
      cases j with
      | none =>
        apply False.elim ((hseed i).ne s hs ?_)
        change V i s - p = W₁ s - p at he
        linarith
      | some j =>
        change V i s - p = V j s - p at he
        have hh : V i s = V j s := by linarith
        exact congrArg some (hinj hh)
  have hclear : ∀ i, Disjoint (ball (z i : ℂ) ρ) E := by
    intro i
    cases i with
    | none =>
      have hh := OwnData.disjoint_ball_of_le_norm
        (fun w hw => htip W₁ hW₁ hsrc S hK₁ s hsI w hw)
      have hh' := disjoint_ball_transl (hh.mono_left (ball_subset_ball (min_le_right rseed rtip))) (-p)
      have he : (fun w => fwdMap W₁ s w + (W₁ s : ℂ)) = frzChart W₁ s := rfl
      rw [he] at hh'
      simpa only [z, Option.elim, sub_eq_add_neg] using hh'
    | some m =>
      have hh := hseedclear W₁ Vlo Vhi S hW₁ hsrc hK₁ hlo hhi s hsI (V m s) (hVI m)
      have hh' := disjoint_ball_transl (hh.mono_left (ball_subset_ball (min_le_left rseed rtip))) (-p)
      simpa only [z, Option.elim, sub_eq_add_neg] using hh'
  obtain ⟨γ, Γ, lam, hγ, hD9⟩ := exists_D9Const_of_image_enclosure hE z hz hρ hclear Tm
  obtain ⟨r, a₀, hr, ha, hown⟩ := exists_seedTOwn_bounds_of_enclosures hp Tm
  refine ⟨r, a₀, γ, Γ, lam, hr, ha, hγ, ?_⟩
  intro W₂ T hW₂ h02 hT hTm hK₂
  have ho := seedTSrcOwn_of_enclosures hW₁ hW₂ hT hsI hp.sep_pos hp.sep hK₁ hK₂
  have ho' : OwnData (fun u => W₂ u - p) (fwdHull (fun u => W₁ u - p) s)
      (frzChart (fun u => W₁ u - p) s) T (seedTSrcClock W₁ W₂ T s) (seedTSrcDriver W₁ W₂ T s) := by
    simpa only [h02] using ho
  obtain ⟨hclr, hA1⟩ := hown W₁ W₂ S T s _ _ hW₁ hW₂ h0₁ h02 hS hs hSm hTm hK₁ hK₂ ho'
  have hK : fwdHull (seedTSrcDriver W₁ W₂ T s) (seedTSrcClock W₁ W₂ T s T) ⊆ E := by
    rw [ho'.img T ⟨hT.le, le_rfl⟩]
    exact (Set.image_mono (fwdHull_sub_const_subset hK₂)).trans
      (frzChart_image_transl W₁ p s H₂).subset
  have hclock : ∀ t ∈ Icc (0 : ℝ) T, seedTSrcClock W₁ W₂ T s t ≤ Tm := by
    intro t ht
    exact (ho'.toImgData.clock_le hr hclr ht).trans (ht.2.trans hTm)
  refine hD9 _ _ _ r a₀ ?_ hr ha ?_ ?_ ?_ ?_ hclock hK
  · simpa only [seedTView, h02] using ho'
  · simp only [seedTView, h02, z, Option.elim]
  · intro m; simp only [seedTView, h02, z, Option.elim]
  · intro t ht
    change Disjoint (ball (((W₂ t - W₂ 0) : ℝ) : ℂ) r)
      (frzChart (fun u => W₂ u - W₂ 0) t '' fwdHull (fun u => W₁ u - p) s)
    simpa only [h02] using hclr t ht
  · simpa only [seedTView, FrzData.A, h02] using hA1

end InteractingSLE.ZhanGT4
