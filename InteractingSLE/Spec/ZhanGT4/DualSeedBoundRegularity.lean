/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBoundAnalytic
import InteractingSLE.Spec.ZhanGT4.DualSeedPathBand

/-!
# Regularity inputs for the normalized seeded density

Packet PROVE-ZHAN-GT4-A22. Continuity of the normalized factors includes the
time axis, where the unnormalized gaps can vanish. Positive derivatives on
the force-coordinate interval also give nonvanishing of the image gaps used
in A21's band cutoff.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE.ZhanGT4

namespace SeedData

variable {n : ℕ} (d : SeedData n)

/-- The real derivative in the divided differences equals `F 1`. -/
theorem deriv_F_zero {t x : ℝ}
    (hd : DifferentiableAt ℂ (ownExt d.W d.W' d.a d.φ t) x) :
    deriv (d.F 0 t) x = d.F 1 t x := by
  exact hd.hasDerivAt.real_of_complex.deriv

/-- Continuity of all quantities in the band family, including at time zero.
The vanishing of an own gap at zero does not obstruct this assertion. -/
theorem continuousOn_gapVal {I : Set ℝ}
    (hA0 : ContinuousOn (d.A 0) I) (hA20 : ContinuousOn d.A20 I)
    (hA21 : ContinuousOn d.A21 I)
    (hB0 : ∀ m, ContinuousOn (fun t => d.B0 t m) I)
    (hB1 : ∀ m, ContinuousOn (fun t => d.B1 t m) I)
    (hW : ContinuousOn d.W I) (hV0 : ContinuousOn d.V₀ I)
    (hV : ∀ m, ContinuousOn (d.V m) I) :
    ∀ i, ContinuousOn (d.gapVal i) I := by
  intro i
  rcases i with i | i
  · fin_cases i
    · change ContinuousOn (fun t => d.A20 t - d.A 0 t) I
      exact hA20.sub hA0
    · change ContinuousOn d.A21 I
      exact hA21
    · change ContinuousOn (fun t => d.V₀ t - d.W t) I
      exact hV0.sub hW
  · rcases i with ⟨i, m⟩ | ⟨i, m, k⟩
    · fin_cases i
      · change ContinuousOn (fun t => d.B0 t m - d.A 0 t) I
        exact (hB0 m).sub hA0
      · change ContinuousOn (fun t => d.A20 t - d.B0 t m) I
        exact hA20.sub (hB0 m)
      · change ContinuousOn (fun t => d.B1 t m) I
        exact hB1 m
      · change ContinuousOn (fun t => d.V m t - d.W t) I
        exact (hV m).sub hW
      · change ContinuousOn (fun t => d.V₀ t - d.V m t) I
        exact hV0.sub (hV m)
    · by_cases hmk : m = k
      · apply (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) I).congr
        intro t _
        simp only [gapVal, hmk, ↓reduceIte]
      · fin_cases i
        · apply ((hB0 m).sub (hB0 k)).congr
          intro t _
          simp [gapVal, hmk]
        · apply ((hV m).sub (hV k)).congr
          intro t _
          simp [gapVal, hmk]

/-- Positivity of the derivative on a convex coordinate interval gives all
image-gap noncollisions from the corresponding own-coordinate noncollisions.
The remaining gaps are the separated other-source gaps. -/
theorem gapVal_ne_zero_of_deriv {t : ℝ} {I : Set ℝ}
    (hI : Convex ℝ I) (hd : DifferentiableOn ℝ (d.F 0 t) I)
    (hder : ∀ x ∈ I, 0 < deriv (d.F 0 t) x)
    (hF1 : ∀ x ∈ I, d.F 1 t x = deriv (d.F 0 t) x)
    (hW : d.W t ∈ I) (hV : ∀ m, d.V m t ∈ I)
    (h21 : d.A21 t ≠ 0) (h0 : d.A20 t ≠ d.A 0 t)
    (h2m : ∀ m, d.A20 t ≠ d.B0 t m)
    (hV0 : d.V₀ t ≠ d.W t) (hVm : ∀ m, d.V m t ≠ d.W t)
    (hV0m : ∀ m, d.V₀ t ≠ d.V m t)
    (hVmk : Function.Injective (fun m => d.V m t)) :
    ∀ i, d.gapVal i t ≠ 0 := by
  have hmono := strictMonoOn_of_deriv_pos hI hd.continuousOn
    (fun x hx => hder x (interior_subset hx))
  have hBW : ∀ m, d.B0 t m ≠ d.A 0 t := fun m he =>
    hVm m (hmono.injOn (hV m) hW he)
  have hBB : ∀ m k, m ≠ k → d.B0 t m ≠ d.B0 t k := fun m k hmk he =>
    hmk (hVmk (hmono.injOn (hV m) (hV k) he))
  have hB1 : ∀ m, d.B1 t m ≠ 0 := fun m =>
    ne_of_gt (by rw [B1, hF1 _ (hV m)]; exact hder _ (hV m))
  intro i
  rcases i with i | i
  · fin_cases i
    · simpa [gapVal] using sub_ne_zero.2 h0
    · simpa [gapVal] using h21
    · simpa [gapVal] using sub_ne_zero.2 hV0
  · rcases i with ⟨i, m⟩ | ⟨i, m, k⟩
    · fin_cases i
      · simpa [gapVal] using sub_ne_zero.2 (hBW m)
      · simpa [gapVal] using sub_ne_zero.2 (h2m m)
      · simpa [gapVal] using hB1 m
      · simpa [gapVal] using sub_ne_zero.2 (hVm m)
      · simpa [gapVal] using sub_ne_zero.2 (hV0m m)
    · by_cases hmk : m = k
      · simp only [gapVal, hmk, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]
      · fin_cases i
        · simpa [gapVal, hmk] using sub_ne_zero.2 (hBB m k hmk)
        · simpa [gapVal, hmk] using sub_ne_zero.2 (fun he => hmk (hVmk he))

/-- Continuity of the normalized logarithm from continuity and nonvanishing
of its normalized factors. This has no own-gap noncollision assumption. -/
theorem continuousOn_normEll_of_factors {I : Set ℝ}
    (h21 : ContinuousOn (fun t => d.A21 t) I)
    (h21n : ∀ t ∈ I, d.A21 t ≠ 0) (hL : ContinuousOn d.L I)
    (hB1 : ∀ m, ContinuousOn (fun t => d.B1 t m) I)
    (hB1n : ∀ m t, t ∈ I → d.B1 t m ≠ 0)
    (h2m : ∀ m, ContinuousOn
      (fun t => (d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t)) I)
    (h2mn : ∀ m t, t ∈ I →
      (d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t) ≠ 0)
    (hmk : ∀ m k, m < k → ContinuousOn
      (fun t => dslope (d.F 0 t) (d.V k t) (d.V m t)) I)
    (hmkn : ∀ m k, m < k → ∀ t ∈ I,
      dslope (d.F 0 t) (d.V k t) (d.V m t) ≠ 0)
    (h1 : ContinuousOn (fun t => d.A 1 t) I)
    (h1n : ∀ t ∈ I, d.A 1 t ≠ 0)
    (h0 : ContinuousOn (fun t => (d.A 0 t - d.A20 t) / (d.W t - d.V₀ t)) I)
    (h0n : ∀ t ∈ I, (d.A 0 t - d.A20 t) / (d.W t - d.V₀ t) ≠ 0)
    (hm : ∀ m, ContinuousOn (fun t => dslope (d.F 0 t) (d.V m t) (d.W t)) I)
    (hmn : ∀ m t, t ∈ I → dslope (d.F 0 t) (d.V m t) (d.W t) ≠ 0) :
    ContinuousOn d.normEll I := by
  have hb := continuousOn_finsetSum (Finset.univ : Finset (Fin n)) (fun m _ =>
    ((hB1 m).log (hB1n m)).const_mul (dualGamma d.κ (d.r m)) |>.add
      (((h2m m).log (h2mn m)).const_mul (-(d.κ / 4) * d.r m)))
  have hp : ContinuousOn (fun t => pairSum (fun m k => dualDelta d.κ (d.r m) (d.r k)
      * Real.log (dslope (d.F 0 t) (d.V k t) (d.V m t)))) I := by
    unfold pairSum
    apply continuousOn_finsetSum
    intro p hp
    have hlt := (Finset.mem_filter.1 hp).2
    exact ((hmk p.1 p.2 hlt).log (hmkn p.1 p.2 hlt)).const_mul _
  have hs := continuousOn_finsetSum (Finset.univ : Finset (Fin n))
    (fun m _ => ((hm m).log (hmn m)).const_mul (d.r m))
  exact (((((h21.log h21n).const_mul _).sub (hL.const_mul _)).add hb).add hp).add
    ((((h1.log h1n).const_mul _).sub ((h0.log h0n).const_mul _)).add hs)

/-- The right-continuity needed in A19's passage to time zero. -/
theorem tendsto_exp_normEll_zero {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn d.normEll (Icc 0 T)) :
    Tendsto (fun t => Real.exp (d.normEll t)) (𝓝[>] 0)
      (𝓝 (Real.exp (d.normEll 0))) := by
  have hmem : Icc (0 : ℝ) T ∈ 𝓝[>] 0 :=
    mem_of_superset (Ioo_mem_nhdsGT hT) Ioo_subset_Icc_self
  exact (Real.continuous_exp.continuousAt.tendsto.comp
    (hc 0 ⟨le_rfl, hT.le⟩).tendsto).mono_left (nhdsWithin_le_of_mem hmem)

end SeedData

end InteractingSLE.ZhanGT4
