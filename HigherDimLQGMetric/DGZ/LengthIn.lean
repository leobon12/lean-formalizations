import HigherDimLQGMetric.DGZ.Functionals
import HigherDimLFPP.Paths.Polygon
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Restricted LFPP lengths `len(γ|_S)` (packet L3b1)

Source: MA7 (`planning/audits/MA7-ref2-sections-4-6.md`) Details (a) D-5.11 ("paths are finite
concatenations of pieces … their total length is `≤ ℓ_{B₂\𝒰}(γ)`", the multiplicity bound
`Σ_z w_j ℓ_{A′_z}(γ′) ≤ Σ_j 41^d w_j ℓ(γ′)`), D-5.12 (restricted length of the polygonal path,
"a point of `γ` lies in at most `5^d` such shells") and G23 (DGZ (2.3) for piecewise `C¹` paths,
as the set integral `lfppLengthIn`).

For a piecewise `C¹` path `γ` and a continuous field `φ`
(`lfppLengthIn ξ φ γ S = ∫_{[0,1] ∩ γ⁻¹ S} e^{ξ φ(γ t)} |γ'(t)| dt`):
* `lfppLengthIn_nonneg`, `lfppLengthIn_univ`, `lfppLengthIn_eq_lfppLength_of_mapsTo`,
  `lfppLengthIn_eq_zero_of_mapsTo_compl`, `lfppLengthIn_le_lfppLength`, `lfppLengthIn_mono`;
* `integral_le_lfppLengthIn` (a parameter interval mapped into `S`) and
  `sum_integral_le_lfppLengthIn` (finitely many parameter intervals with disjoint interiors);
* `sum_lfppLengthIn_le_mul` (**multiplicity bound**: if every point of `ℝ^d` lies in at most `N`
  of the measurable sets `S i`, then `Σ_i len(γ|_{S i}) ≤ N len(γ)`);
* `lfppLengthIn_le_mul_of_exp_le` (field comparison on `S`);
* `lfppLengthIn_concatPath` (additivity under concatenation, measurable `S`) and
  `lfppLengthIn_polygonPath` (a polygonal path: the sum over its edges).

Helper: `measurableSet_Icc_inter_preimage` (`[a, b] ∩ γ⁻¹ S` is measurable when `γ` is continuous on
`[a, b]` and `S` is measurable).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP

variable {d : ℕ} {ξ : ℝ} {φ ψ : Rd d → ℝ} {γ γ₁ γ₂ : ℝ → Rd d} {x y z : Rd d}
  {S S' : Set (Rd d)}

theorem lfppLengthIn_eq_setIntegral (ξ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) (S : Set (Rd d)) :
    lfppLengthIn ξ φ γ S = ∫ t in Icc (0 : ℝ) 1 ∩ γ ⁻¹' S, lfppIntegrand ξ φ γ t := rfl

theorem lfppLengthIn_nonneg (ξ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) (S : Set (Rd d)) :
    0 ≤ lfppLengthIn ξ φ γ S :=
  integral_nonneg fun t => lfppIntegrand_nonneg ξ φ γ t

/-- The LFPP integrand of a piecewise `C¹` path is integrable on `[0,1]` (continuous field). -/
theorem integrableOn_lfppIntegrand (hγ : IsPcwC1Path γ x y) (hφ : Continuous φ)
    (ξ : ℝ) : IntegrableOn (lfppIntegrand ξ φ γ) (Icc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1
    (hγ.intervalIntegrable_lfppIntegrand hφ ξ)

theorem lfppLength_eq_setIntegral (ξ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) :
    lfppLength ξ φ γ = ∫ t in Icc (0 : ℝ) 1, lfppIntegrand ξ φ γ t := by
  rw [lfppLength_eq_integral, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

theorem lfppLengthIn_univ (ξ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) :
    lfppLengthIn ξ φ γ univ = lfppLength ξ φ γ := by
  rw [lfppLengthIn_eq_setIntegral, preimage_univ, inter_univ, lfppLength_eq_setIntegral]

/-- If `γ` stays in `S`, its restricted length is its length. -/
theorem lfppLengthIn_eq_lfppLength_of_mapsTo (h : MapsTo γ (Icc 0 1) S) :
    lfppLengthIn ξ φ γ S = lfppLength ξ φ γ := by
  rw [lfppLengthIn_eq_setIntegral,
    inter_eq_left.2 (show Icc (0 : ℝ) 1 ⊆ γ ⁻¹' S from fun t ht => h ht),
    lfppLength_eq_setIntegral]

/-- If `γ` avoids `S`, its restricted length vanishes. -/
theorem lfppLengthIn_eq_zero_of_mapsTo_compl (h : MapsTo γ (Icc 0 1) Sᶜ) :
    lfppLengthIn ξ φ γ S = 0 := by
  have he : Icc (0 : ℝ) 1 ∩ γ ⁻¹' S = ∅ :=
    eq_empty_iff_forall_notMem.2 fun t ht => h ht.1 ht.2
  rw [lfppLengthIn_eq_setIntegral, he, Measure.restrict_empty, integral_zero_measure]

theorem lfppLengthIn_le_lfppLength (hφ : Continuous φ) (hγ : IsPcwC1Path γ x y) :
    lfppLengthIn ξ φ γ S ≤ lfppLength ξ φ γ := by
  rw [lfppLength_eq_setIntegral]
  exact setIntegral_mono_set (integrableOn_lfppIntegrand hγ hφ ξ)
    (ae_of_all _ fun t => lfppIntegrand_nonneg ξ φ γ t) inter_subset_left.eventuallyLE

theorem lfppLengthIn_mono (hφ : Continuous φ) (hγ : IsPcwC1Path γ x y) (hSS' : S ⊆ S') :
    lfppLengthIn ξ φ γ S ≤ lfppLengthIn ξ φ γ S' :=
  setIntegral_mono_set ((integrableOn_lfppIntegrand hγ hφ ξ).mono_set inter_subset_left)
    (ae_of_all _ fun t => lfppIntegrand_nonneg ξ φ γ t)
    (inter_subset_inter_right _ (preimage_mono hSS')).eventuallyLE

/-- A parameter interval mapped into `S` contributes at most `len(γ|_S)`. -/
theorem integral_le_lfppLengthIn (hφ : Continuous φ) (hγ : IsPcwC1Path γ x y) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) (hS : ∀ t ∈ Icc u v, γ t ∈ S) :
    ∫ t in u..v, lfppIntegrand ξ φ γ t ≤ lfppLengthIn ξ φ γ S := by
  rw [intervalIntegral.integral_of_le huv]
  have hsub : Ioc u v ⊆ Icc (0 : ℝ) 1 ∩ γ ⁻¹' S := fun t ht =>
    ⟨⟨hu.trans ht.1.le, ht.2.trans hv⟩, hS t ⟨ht.1.le, ht.2⟩⟩
  exact setIntegral_mono_set ((integrableOn_lfppIntegrand hγ hφ ξ).mono_set inter_subset_left)
    (ae_of_all _ fun t => lfppIntegrand_nonneg ξ φ γ t) hsub.eventuallyLE

/-- **Pieces on disjoint parameter intervals** (MA7 D-5.11, "Length"): if the parameter intervals
`[u i, v i] ⊆ [0,1]` have pairwise disjoint interiors and are mapped into `S`, the sum of the
lengths of the corresponding pieces is at most `len(γ|_S)`. -/
theorem sum_integral_le_lfppLengthIn (hφ : Continuous φ) (hγ : IsPcwC1Path γ x y) {ι : Type*}
    (s : Finset ι) (u v : ι → ℝ) (huv : ∀ i ∈ s, 0 ≤ u i ∧ u i ≤ v i ∧ v i ≤ 1)
    (hS : ∀ i ∈ s, ∀ t ∈ Icc (u i) (v i), γ t ∈ S)
    (hdisj : Set.Pairwise (s : Set ι) fun i j => Disjoint (Ioo (u i) (v i)) (Ioo (u j) (v j))) :
    ∑ i ∈ s, ∫ t in u i..v i, lfppIntegrand ξ φ γ t ≤ lfppLengthIn ξ φ γ S := by
  have hI := integrableOn_lfppIntegrand hγ hφ ξ
  have h1 : ∀ i ∈ s, ∫ t in u i..v i, lfppIntegrand ξ φ γ t =
      ∫ t in Ioo (u i) (v i), lfppIntegrand ξ φ γ t := fun i hi => by
    rw [intervalIntegral.integral_of_le (huv i hi).2.1, integral_Ioc_eq_integral_Ioo]
  rw [Finset.sum_congr rfl h1, ← integral_biUnion_finset s (fun i _ => measurableSet_Ioo) hdisj
    fun i hi => hI.mono_set (Ioo_subset_Icc_self.trans
      (Icc_subset_Icc (huv i hi).1 (huv i hi).2.2))]
  have hsub : (⋃ i ∈ s, Ioo (u i) (v i)) ⊆ Icc (0 : ℝ) 1 ∩ γ ⁻¹' S := by
    intro t ht
    simp only [mem_iUnion] at ht
    obtain ⟨i, hi, hti⟩ := ht
    exact ⟨⟨(huv i hi).1.trans hti.1.le, hti.2.le.trans (huv i hi).2.2⟩,
      hS i hi t ⟨hti.1.le, hti.2.le⟩⟩
  exact setIntegral_mono_set (hI.mono_set inter_subset_left)
    (ae_of_all _ fun t => lfppIntegrand_nonneg ξ φ γ t) hsub.eventuallyLE

/-- `[a, b] ∩ γ⁻¹ S` is measurable when `γ` is continuous on `[a, b]` and `S` is measurable. -/
theorem measurableSet_Icc_inter_preimage {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hS : MeasurableSet S) : MeasurableSet (Icc a b ∩ γ ⁻¹' S) := by
  set γ' : ℝ → Rd d := fun t => γ (projIcc a b hab t) with hγ'def
  have hγ' : Continuous γ' :=
    hγ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun t =>
      (projIcc a b hab t).2
  have he : Icc a b ∩ γ ⁻¹' S = Icc a b ∩ γ' ⁻¹' S := by
    ext t
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨ht, h⟩
      exact ⟨ht, by simpa only [hγ'def, projIcc_of_mem hab ht] using h⟩
    · rintro ⟨ht, h⟩
      exact ⟨ht, by simpa only [hγ'def, projIcc_of_mem hab ht] using h⟩
  rw [he]
  exact measurableSet_Icc.inter (hγ'.measurable hS)

open Classical in
/-- **Multiplicity bound** (MA7 D-5.11, D-5.12): if every point of `ℝ^d` lies in at most `N` of the
measurable sets `S i` (`i ∈ s`), then `Σ_i len(γ|_{S i}) ≤ N len(γ)`. -/
theorem sum_lfppLengthIn_le_mul (hφ : Continuous φ) (hγ : IsPcwC1Path γ x y) {ι : Type*}
    (s : Finset ι) (S : ι → Set (Rd d)) (hS : ∀ i ∈ s, MeasurableSet (S i)) {N : ℕ}
    (hN : ∀ z : Rd d, (s.filter fun i => z ∈ S i).card ≤ N) :
    ∑ i ∈ s, lfppLengthIn ξ φ γ (S i) ≤ N * lfppLength ξ φ γ := by
  classical
  have hI := integrableOn_lfppIntegrand hγ hφ ξ
  set f := lfppIntegrand ξ φ γ with hf
  have hA : ∀ i ∈ s, MeasurableSet (Icc (0 : ℝ) 1 ∩ γ ⁻¹' S i) := fun i hi =>
    measurableSet_Icc_inter_preimage zero_le_one hγ.continuousOn (hS i hi)
  have h1 : ∀ i ∈ s, lfppLengthIn ξ φ γ (S i) =
      ∫ t in Icc (0 : ℝ) 1, (Icc (0 : ℝ) 1 ∩ γ ⁻¹' S i).indicator f t := fun i hi => by
    rw [setIntegral_indicator (hA i hi), ← inter_assoc, inter_self]
    rfl
  rw [Finset.sum_congr rfl h1, ← integral_finsetSum _ fun i hi => hI.indicator (hA i hi),
    lfppLength_eq_setIntegral, ← integral_const_mul]
  refine setIntegral_mono_on (integrable_finsetSum _ fun i hi => hI.indicator (hA i hi))
    (hI.const_mul _) measurableSet_Icc fun t ht => ?_
  have hsum : ∑ i ∈ s, (Icc (0 : ℝ) 1 ∩ γ ⁻¹' S i).indicator f t =
      ((s.filter fun i => γ t ∈ S i).card : ℝ) * f t := by
    simp only [Set.indicator_apply, mem_inter_iff, mem_preimage, ht, true_and]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hN (γ t))
    (lfppIntegrand_nonneg ξ φ γ t)

/-- **Field comparison** for restricted lengths: if `e^{ξ φ} ≤ C e^{ξ ψ}` on the measurable set
`S` (`C ≥ 0`), then `len_φ(γ|_S) ≤ C len_ψ(γ|_S)`. -/
theorem lfppLengthIn_le_mul_of_exp_le (hφ : Continuous φ) (hψ : Continuous ψ)
    (hγ : IsPcwC1Path γ x y) (hS : MeasurableSet S) {C : ℝ}
    (h : ∀ z ∈ S, Real.exp (ξ * φ z) ≤ C * Real.exp (ξ * ψ z)) :
    lfppLengthIn ξ φ γ S ≤ C * lfppLengthIn ξ ψ γ S := by
  have hA := measurableSet_Icc_inter_preimage zero_le_one hγ.continuousOn hS
  rw [lfppLengthIn_eq_setIntegral, lfppLengthIn_eq_setIntegral, ← integral_const_mul]
  refine setIntegral_mono_on ((integrableOn_lfppIntegrand hγ hφ ξ).mono_set inter_subset_left)
    (((integrableOn_lfppIntegrand hγ hψ ξ).mono_set inter_subset_left).const_mul C) hA
    fun t ht => ?_
  unfold lfppIntegrand
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (h _ ht.2) (norm_nonneg _)

/-! ## Concatenation -/

/-- On `t < 1/2` the integrand of a concatenation is twice the integrand of the first path at
`2 t`. -/
theorem lfppIntegrand_concatPath_left (ξ : ℝ) (φ : Rd d → ℝ) (γ₁ γ₂ : ℝ → Rd d) {t : ℝ}
    (ht : t < 1 / 2) :
    lfppIntegrand ξ φ (concatPath γ₁ γ₂) t = 2 * lfppIntegrand ξ φ γ₁ (2 * t) := by
  have hev : concatPath γ₁ γ₂ =ᶠ[𝓝 t] fun v => γ₁ (2 * v) :=
    Filter.eventuallyEq_of_mem (Iio_mem_nhds ht)
      fun v hv => concatPath_eqOn_left γ₁ γ₂ (mem_Iic.2 (le_of_lt hv))
  unfold lfppIntegrand
  rw [hev.deriv_eq, hev.eq_of_nhds, deriv_comp_mul_left, norm_smul, Real.norm_two]
  ring

/-- On `t > 1/2` the integrand of a concatenation is twice the integrand of the second path at
`2 t - 1`. -/
theorem lfppIntegrand_concatPath_right (ξ : ℝ) (φ : Rd d → ℝ) {γ₁ γ₂ : ℝ → Rd d}
    (h12 : γ₁ 1 = γ₂ 0) {t : ℝ} (ht : 1 / 2 < t) :
    lfppIntegrand ξ φ (concatPath γ₁ γ₂) t = 2 * lfppIntegrand ξ φ γ₂ (2 * t - 1) := by
  have hev : concatPath γ₁ γ₂ =ᶠ[𝓝 t] fun v => γ₂ (2 * v - 1) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht)
      fun v hv => concatPath_eqOn_right h12 (mem_Ici.2 (le_of_lt hv))
  unfold lfppIntegrand
  have hd : deriv (fun v => γ₂ (2 * v - 1)) t = (2 : ℝ) • deriv γ₂ (2 * t - 1) := by
    have := deriv_comp_affine γ₂ 2 (-1) t
    simp only [← sub_eq_add_neg] at this
    exact this
  rw [hev.deriv_eq, hev.eq_of_nhds, hd, norm_smul, Real.norm_two]
  ring

/-- **Additivity of restricted lengths under concatenation** (measurable `S`, continuous field). -/
theorem lfppLengthIn_concatPath (hφ : Continuous φ) (h₁ : IsPcwC1Path γ₁ x y)
    (h₂ : IsPcwC1Path γ₂ y z) (hS : MeasurableSet S) :
    lfppLengthIn ξ φ (concatPath γ₁ γ₂) S = lfppLengthIn ξ φ γ₁ S + lfppLengthIn ξ φ γ₂ S := by
  have h12 : γ₁ 1 = γ₂ 0 := h₁.target.trans h₂.source.symm
  set c := concatPath γ₁ γ₂ with hc
  have hcp : IsPcwC1Path c x z := h₁.concat h₂
  have hI := integrableOn_lfppIntegrand hcp hφ ξ
  have hA := measurableSet_Icc_inter_preimage zero_le_one hcp.continuousOn hS
  have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 / 2 := by
    have := (countable_singleton (1 / 2 : ℝ)).ae_notMem volume
    filter_upwards [this] with t ht
    exact ht
  -- split `[0,1] ∩ c⁻¹ S` at `1/2`
  set A₁ := Icc (0 : ℝ) (1 / 2) ∩ (Icc (0 : ℝ) 1 ∩ c ⁻¹' S) with hA₁
  set A₂ := Ioc (1 / 2 : ℝ) 1 ∩ (Icc (0 : ℝ) 1 ∩ c ⁻¹' S) with hA₂
  have hA₁m : MeasurableSet A₁ := measurableSet_Icc.inter hA
  have hA₂m : MeasurableSet A₂ := measurableSet_Ioc.inter hA
  have hunion : Icc (0 : ℝ) 1 ∩ c ⁻¹' S = A₁ ∪ A₂ := by
    ext t
    simp only [hA₁, hA₂, mem_union, mem_inter_iff, mem_Icc, mem_Ioc, mem_preimage]
    constructor
    · rintro ⟨⟨h0, h1⟩, hs⟩
      rcases le_or_gt t (1 / 2) with h | h
      · exact Or.inl ⟨⟨h0, h⟩, ⟨h0, h1⟩, hs⟩
      · exact Or.inr ⟨⟨h, h1⟩, ⟨h0, h1⟩, hs⟩
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
  have hdisj : Disjoint A₁ A₂ := by
    rw [Set.disjoint_left]
    rintro t ⟨⟨-, h1⟩, -⟩ ⟨⟨h2, -⟩, -⟩
    linarith
  have hsplit : lfppLengthIn ξ φ c S =
      (∫ t in A₁, lfppIntegrand ξ φ c t) + ∫ t in A₂, lfppIntegrand ξ φ c t := by
    rw [lfppLengthIn_eq_setIntegral, hunion]
    exact setIntegral_union hdisj hA₂m (hI.mono_set (inter_subset_right.trans inter_subset_left))
      (hI.mono_set (inter_subset_right.trans inter_subset_left))
  rw [hsplit]
  congr 1
  · -- the first half: `t ↦ 2 t` maps `A₁` onto `[0,1] ∩ γ₁⁻¹ S`
    have hA₁' : A₁ = Icc (0 : ℝ) (1 / 2) ∩ {t | γ₁ (2 * t) ∈ S} := by
      ext t
      simp only [hA₁, mem_inter_iff, mem_Icc, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h0, h1⟩, -, hs⟩
        refine ⟨⟨h0, h1⟩, ?_⟩
        rwa [hc, concatPath_eqOn_left γ₁ γ₂ (mem_Iic.2 h1)] at hs
      · rintro ⟨⟨h0, h1⟩, hs⟩
        refine ⟨⟨h0, h1⟩, ⟨h0, by linarith⟩, ?_⟩
        rwa [hc, concatPath_eqOn_left γ₁ γ₂ (mem_Iic.2 h1)]
    have himage : (fun t : ℝ => 2 * t) '' A₁ = Icc (0 : ℝ) 1 ∩ γ₁ ⁻¹' S := by
      rw [hA₁']
      ext s
      simp only [mem_image, mem_inter_iff, mem_Icc, mem_ofPred_eq, mem_preimage]
      constructor
      · rintro ⟨t, ⟨⟨h0, h1⟩, hs⟩, rfl⟩
        exact ⟨⟨by linarith, by linarith⟩, hs⟩
      · rintro ⟨⟨h0, h1⟩, hs⟩
        exact ⟨s / 2, ⟨⟨by linarith, by linarith⟩, by rwa [mul_div_cancel₀ s two_ne_zero]⟩,
          mul_div_cancel₀ s two_ne_zero⟩
    have hcov := integral_image_eq_integral_abs_deriv_smul (s := A₁) (f := fun t : ℝ => 2 * t)
      (f' := fun _ => 2) hA₁m
      (fun t _ => by simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).hasDerivWithinAt)
      ((mul_right_injective₀ (two_ne_zero (α := ℝ))).injOn) (lfppIntegrand ξ φ γ₁)
    rw [himage] at hcov
    rw [lfppLengthIn_eq_setIntegral, hcov]
    refine setIntegral_congr_ae hA₁m ?_
    filter_upwards [hnull] with t ht htA
    have hlt : t < 1 / 2 := lt_of_le_of_ne htA.1.2 ht
    rw [lfppIntegrand_concatPath_left ξ φ γ₁ γ₂ hlt, abs_two, smul_eq_mul]
  · -- the second half: `t ↦ 2 t - 1` maps `A₂` onto `(0,1] ∩ γ₂⁻¹ S`
    have hA₂' : A₂ = Ioc (1 / 2 : ℝ) 1 ∩ {t | γ₂ (2 * t - 1) ∈ S} := by
      ext t
      simp only [hA₂, mem_inter_iff, mem_Ioc, mem_Icc, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨h0, h1⟩, -, hs⟩
        refine ⟨⟨h0, h1⟩, ?_⟩
        rwa [hc, concatPath_eqOn_right h12 (mem_Ici.2 h0.le)] at hs
      · rintro ⟨⟨h0, h1⟩, hs⟩
        refine ⟨⟨h0, h1⟩, ⟨by linarith, h1⟩, ?_⟩
        rwa [hc, concatPath_eqOn_right h12 (mem_Ici.2 h0.le)]
    have himage : (fun t : ℝ => 2 * t - 1) '' A₂ = Ioc (0 : ℝ) 1 ∩ γ₂ ⁻¹' S := by
      rw [hA₂']
      ext s
      simp only [mem_image, mem_inter_iff, mem_Ioc, mem_ofPred_eq, mem_preimage]
      constructor
      · rintro ⟨t, ⟨⟨h0, h1⟩, hs⟩, rfl⟩
        exact ⟨⟨by linarith, by linarith⟩, hs⟩
      · rintro ⟨⟨h0, h1⟩, hs⟩
        have e : 2 * ((s + 1) / 2) - 1 = s := by ring
        exact ⟨(s + 1) / 2, ⟨⟨by linarith, by linarith⟩, by rwa [e]⟩, e⟩
    have hinj : InjOn (fun t : ℝ => 2 * t - 1) A₂ := fun a _ b _ hab => by
      simp only at hab
      linarith
    have hcov := integral_image_eq_integral_abs_deriv_smul (s := A₂)
      (f := fun t : ℝ => 2 * t - 1) (f' := fun _ => 2) hA₂m
      (fun t _ => by
        simpa using (((hasDerivAt_id t).const_mul (2 : ℝ)).sub_const 1).hasDerivWithinAt)
      hinj (lfppIntegrand ξ φ γ₂)
    rw [himage] at hcov
    have hIoc : ∫ t in Ioc (0 : ℝ) 1 ∩ γ₂ ⁻¹' S, lfppIntegrand ξ φ γ₂ t =
        lfppLengthIn ξ φ γ₂ S := by
      rw [lfppLengthIn_eq_setIntegral]
      exact setIntegral_congr_set (Ioc_ae_eq_Icc.inter (EventuallyEq.refl _ _))
    rw [← hIoc, hcov]
    refine setIntegral_congr_ae hA₂m ?_
    filter_upwards with t htA
    rw [lfppIntegrand_concatPath_right ξ φ h12 htA.1.1, abs_two, smul_eq_mul]

/-- **Restricted length of a polygonal path**: the sum over its edges (measurable `S`). -/
theorem lfppLengthIn_polygonPath (hφ : Continuous φ) (hS : MeasurableSet S) (p : ℕ → Rd d)
    (N : ℕ) : lfppLengthIn ξ φ (polygonPath p N) S =
      ∑ i ∈ Finset.range N, lfppLengthIn ξ φ (segPath (p i) (p (i + 1))) S := by
  induction N generalizing p with
  | zero =>
    simp only [polygonPath, Finset.range_zero, Finset.sum_empty]
    rw [lfppLengthIn_eq_setIntegral]
    have h0 : ∀ t, lfppIntegrand ξ φ (segPath (p 0) (p 0)) t = 0 := fun t => by
      simp only [lfppIntegrand, deriv_segPath, sub_self, norm_zero, mul_zero]
    simp only [h0, integral_zero]
  | succ n ih =>
    simp only [polygonPath]
    rw [lfppLengthIn_concatPath hφ (isPcwC1Path_segPath (p 0) (p 1))
      (isPcwC1Path_polygonPath (fun i => p (i + 1)) n) hS, ih, Finset.sum_range_succ', add_comm]

end HigherDimLQGMetric.DGZ
