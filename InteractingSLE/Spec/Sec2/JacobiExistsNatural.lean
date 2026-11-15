/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiSDE
import InteractingSLE.Spec.Sec2.JacobiLaw

/-!
# A solution of the polynomial martingale problem is a Jacobi diffusion in its natural filtration

Packet PROVE-YW-JACOBI. The landed `Jacobi.IsJacobiMP κ a b P U` tests the compensated increment
`D = U_v^n - U_w^n - ∫_w^v L(x^n)(U_x) dx` against products `∏ U_{s_i}^{k_i}` with `s_i ≤ w`.
`IsJacobiMP.isJacobiDiffusion` upgrades this to the conditional form `E[D | 𝓗_w] = 0` of
`Jacobi.IsJacobiDiffusion`, for the natural filtration `𝓗_w = σ(U_s : s ≤ w)` (`natFilt`):

* for a cylinder `{U_{s_i} ∈ B_i ∀ i}` (`setIntegral_cylinder_eq_zero`), the finite measures
  `(D⁺ P) ∘ V⁻¹` and `(D⁻ P) ∘ V⁻¹` on the cube `[0, 1]^m` (`V = (U_{s_i})_i`) have the same integrals
  against all monomials, hence are equal (polynomials are a point-separating subalgebra; Mathlib's
  `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`, as in the landed
  `IsJacobiMP.map_eq`), so `∫_{cylinder} D = 0`;
* the cylinders form a π-system generating `𝓗_w` (`piiUnionInter`), so `∫_A D = 0` for every
  `A ∈ 𝓗_w` (Dynkin's π-λ theorem), which is `E[D | 𝓗_w] = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology BoundedContinuousFunction

namespace InteractingSLE

namespace Sec2

namespace Jacobi

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {κ a b : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {U : ℝ → Ω → ℝ}

/-- The natural filtration `σ(U_s : s ≤ w)`. -/
def natFilt (hU : ∀ t, Measurable (U t)) : Filtration ℝ mΩ where
  seq w := ⨆ j ∈ Iic w, MeasurableSpace.comap (U j) inferInstance
  mono' _ _ h := biSup_mono fun _ hj => mem_Iic.2 (le_trans (mem_Iic.1 hj) h)
  le' _ := iSup₂_le fun j _ => (hU j).comap_le

theorem measurable_natFilt (hU : ∀ t, Measurable (U t)) (w : ℝ) :
    Measurable[natFilt hU w] (U w) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂ (f := fun j (_ : j ∈ Iic w) => MeasurableSpace.comap (U j) inferInstance) w
    (mem_Iic.2 le_rfl)

/-- The compensated increment `U_v^n - U_w^n - ∫_w^v L(x^n)(U_x) dx`. -/
def incr (κ a b : ℝ) (U : ℝ → Ω → ℝ) (n : ℕ) (w v : ℝ) (ω : Ω) : ℝ :=
  U v ω ^ n - U w ω ^ n - ∫ x in w..v, gen κ a b (fun y => y ^ n) (U x ω)

omit [IsProbabilityMeasure P] in
theorem IsJacobiMP.measurable_incr (hU : IsJacobiMP κ a b P U) (n : ℕ) (w v : ℝ) :
    Measurable (incr κ a b U n w v) := by
  have h2 : Measurable fun p : Ω × ℝ => U p.2 p.1 := hU.measurable_uncurry
  have hg : Measurable fun p : Ω × ℝ => gen κ a b (fun y => y ^ n) (U p.2 p.1) := by
    simp only [gen_pow]
    exact ((h2.pow_const _).const_mul _).add ((h2.pow_const _).const_mul _)
  have hint : Measurable fun ω => ∫ x in w..v, gen κ a b (fun y => y ^ n) (U x ω) := by
    rcases le_total w v with hwv | hvw
    · simp only [intervalIntegral.integral_of_le hwv]
      exact (hg.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc w v))).measurable
    · simp only [intervalIntegral.integral_of_ge hvw]
      exact (hg.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc v w))).measurable.neg
  exact (((hU.measurable v).pow_const n).sub ((hU.measurable w).pow_const n)).sub hint

omit [IsProbabilityMeasure P] in
theorem IsJacobiMP.abs_incr_le (hU : IsJacobiMP κ a b P U) (n : ℕ) {w v : ℝ} (hwv : w ≤ v)
    (ω : Ω) : |incr κ a b U n w v ω| ≤ 2 + (|dcoef κ a n| + |ccoef κ a b n|) * (v - w) := by
  have hg : ∀ x, |gen κ a b (fun y => y ^ n) (U x ω)| ≤ |dcoef κ a n| + |ccoef κ a b n| := by
    intro x
    rw [gen_pow]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc x ω (n - 1))
    have h2 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc x ω n)
    nlinarith [abs_nonneg (dcoef κ a n), abs_nonneg (ccoef κ a b n)]
  have hI : |∫ x in w..v, gen κ a b (fun y => y ^ n) (U x ω)| ≤
      (|dcoef κ a n| + |ccoef κ a b n|) * (v - w) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := w) (b := v)
      (f := fun x => gen κ a b (fun y => y ^ n) (U x ω)) (fun x _ => by
        rw [Real.norm_eq_abs]; exact hg x)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hwv)] at this
  have h1 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc v ω n)
  have h2 := abs_le_one_of_mem_Icc (hU.pow_mem_Icc w ω n)
  simp only [incr]
  refine (abs_sub _ _).trans ?_
  linarith [abs_sub (U v ω ^ n) (U w ω ^ n)]

theorem IsJacobiMP.integrable_incr (hU : IsJacobiMP κ a b P U) (n : ℕ) {w v : ℝ} (hwv : w ≤ v) :
    Integrable (incr κ a b U n w v) P :=
  Integrable.of_bound (hU.measurable_incr n w v).aestronglyMeasurable _
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hU.abs_incr_le n hwv ω)

theorem abs_max_zero_le (x : ℝ) : |max x 0| ≤ |x| := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, abs_zero]; exact abs_nonneg x

omit [IsProbabilityMeasure P] in
/-- Integration against `(f⁺ P) ∘ V⁻¹`. -/
theorem integral_map_withDensity_ofReal {m : ℕ} {V : Ω → cube m} (hV : Measurable V) {f : Ω → ℝ}
    (hf : Measurable f) {g : cube m → ℝ} (hg : Measurable g) :
    ∫ y, g y ∂((P.withDensity fun ω => ENNReal.ofReal (f ω)).map V) =
      ∫ ω, max (f ω) 0 * g (V ω) ∂P := by
  rw [integral_map hV.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]

/-- **The cylinder identity.** -/
theorem IsJacobiMP.setIntegral_cylinder_eq_zero (hU : IsJacobiMP κ a b P U) (n : ℕ) {w v : ℝ} (hwv : w ≤ v) {m : ℕ} (s : Fin m → ℝ)
    (hs : ∀ i, s i ≤ w) (B : Fin m → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    ∫ ω in {ω | ∀ i, U (s i) ω ∈ B i}, incr κ a b U n w v ω ∂P = 0 := by
  set D := incr κ a b U n w v
  have hDm : Measurable D := hU.measurable_incr n w v
  have hDi : Integrable D P := hU.integrable_incr n hwv
  set V : Ω → cube m := fun ω => ⟨fun i => U (s i) ω, fun i => hU.mem_Icc _ _⟩ with hVdef
  have hV : Measurable V := (Measurable.of_eval fun i => hU.measurable (s i)).subtype_mk
  set μp := (P.withDensity fun ω => ENNReal.ofReal (D ω)).map V
  set μm := (P.withDensity fun ω => ENNReal.ofReal (-D ω)).map V
  have : IsFiniteMeasure (P.withDensity fun ω => ENNReal.ofReal (D ω)) :=
    isFiniteMeasure_withDensity_ofReal hDi.hasFiniteIntegral
  have : IsFiniteMeasure (P.withDensity fun ω => ENNReal.ofReal (-D ω)) :=
    isFiniteMeasure_withDensity_ofReal hDi.neg.hasFiniteIntegral
  -- integrals against bounded measurable functions of `V`
  have hdiff : ∀ g : cube m → ℝ, Measurable g → (∃ C, ∀ y, |g y| ≤ C) →
      ∫ y, g y ∂μp - ∫ y, g y ∂μm = ∫ ω, g (V ω) * D ω ∂P := by
    intro g hg ⟨C, hC⟩
    rw [integral_map_withDensity_ofReal hV hDm hg,
      integral_map_withDensity_ofReal (f := fun ω => -D ω) hV hDm.neg hg]
    have i1 : Integrable (fun ω => max (D ω) 0 * g (V ω)) P :=
      Integrable.of_bound ((hDm.max measurable_const).mul (hg.comp hV)).aestronglyMeasurable
        (|C| * (2 + (|dcoef κ a n| + |ccoef κ a b n|) * (v - w))) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          have h1 : |max (D ω) 0| ≤ 2 + (|dcoef κ a n| + |ccoef κ a b n|) * (v - w) :=
            (abs_max_zero_le _).trans (hU.abs_incr_le n hwv ω)
          have h2 := (hC (V ω)).trans (le_abs_self C)
          nlinarith [abs_nonneg (max (D ω) 0), abs_nonneg (g (V ω))])
    have i2 : Integrable (fun ω => max (-D ω) 0 * g (V ω)) P :=
      Integrable.of_bound ((hDm.neg.max measurable_const).mul (hg.comp hV)).aestronglyMeasurable
        (|C| * (2 + (|dcoef κ a n| + |ccoef κ a b n|) * (v - w))) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          have h1 : |max (-D ω) 0| ≤ 2 + (|dcoef κ a n| + |ccoef κ a b n|) * (v - w) := by
            refine (abs_max_zero_le _).trans ?_
            rw [abs_neg]; exact hU.abs_incr_le n hwv ω
          have h2 := (hC (V ω)).trans (le_abs_self C)
          nlinarith [abs_nonneg (max (-D ω) 0), abs_nonneg (g (V ω))])
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    rcases le_total 0 (D ω) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  -- the two measures agree on monomials, hence are equal
  have hμ : μp = μm := by
    refine ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable (𝕜 := ℝ)
      (A := StarAlgebra.adjoin ℝ (range (coordB (m := m)))) ?_ ?_
    · intro x y hxy
      obtain ⟨i, hi⟩ : ∃ i, (x : Fin m → ℝ) i ≠ (y : Fin m → ℝ) i := by
        by_contra h
        exact hxy (Subtype.ext (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩))
      refine ⟨coordB i, ?_, hi⟩
      simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, mem_image,
        SetLike.mem_coe, exists_exists_and_eq_and]
      exact ⟨coordB i, StarAlgebra.subset_adjoin ℝ _ ⟨i, rfl⟩, rfl⟩
    · intro g hg
      have hs' : star (range (coordB (m := m))) = range coordB := by
        ext f
        simp only [mem_star, mem_range]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i, by rw [← star_coordB, hi, star_star]⟩
        · rintro ⟨i, rfl⟩
          exact ⟨i, star_coordB i⟩
      have hg' : g ∈ Subalgebra.toSubmodule (Algebra.adjoin ℝ (range (coordB (m := m)))) := by
        have : g ∈ (StarAlgebra.adjoin ℝ (range (coordB (m := m)))).toSubalgebra := hg
        rwa [StarAlgebra.adjoin_toSubalgebra, hs', union_self] at this
      rw [Algebra.adjoin_eq_span] at hg'
      clear hg
      induction hg' using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨k, hk⟩ := exists_monomial_of_mem_closure hg
        have h := hdiff g g.continuous.measurable ⟨‖g‖, fun y => by
          rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm y⟩
        have hmp : ∫ ω, g (V ω) * D ω ∂P = 0 := by
          have := hU.2.2.2 m s k n w v hs hwv
          rw [← this]
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only [hk, hVdef, D, incr]
        rw [hmp, sub_eq_zero] at h
        exact h
      | zero => simp
      | add f g _ _ hf hg =>
        simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
        rw [integral_add (f.integrable _) (g.integrable _), integral_add (f.integrable _)
          (g.integrable _), hf, hg]
      | smul c f _ hf =>
        simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
        rw [integral_const_mul, integral_const_mul, hf]
  -- evaluate at the cylinder
  set C : Set (cube m) := {y | ∀ i, (y : Fin m → ℝ) i ∈ B i}
  have hC : MeasurableSet C := by
    have : C = (Subtype.val : cube m → Fin m → ℝ) ⁻¹' (Set.pi univ B) := by
      ext y; simp [C, Set.mem_pi]
    rw [this]
    exact measurable_subtype_coe (MeasurableSet.univ_pi hB)
  have h := hdiff (C.indicator 1) (measurable_one.indicator hC) ⟨1, fun y => by
    by_cases hy : y ∈ C <;> simp [hy]⟩
  rw [hμ, sub_self] at h
  have hcyl : MeasurableSet {ω | ∀ i, U (s i) ω ∈ B i} := by
    rw [ofPred_forall]; exact MeasurableSet.iInter fun i => hU.measurable (s i) (hB i)
  rw [← integral_indicator hcyl]
  rw [h]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  by_cases hω : ∀ i, U (s i) ω ∈ B i
  · have : V ω ∈ C := hω
    simp [indicator_of_mem (show ω ∈ {ω | ∀ i, U (s i) ω ∈ B i} from hω), this]
  · have : V ω ∉ C := hω
    simp [indicator_of_notMem (show ω ∉ {ω | ∀ i, U (s i) ω ∈ B i} from hω), this]

/-- **A solution of the polynomial martingale problem is a Jacobi diffusion in its natural
filtration.** -/
theorem IsJacobiMP.isJacobiDiffusion (hU : IsJacobiMP κ a b P U) :
    IsJacobiDiffusion κ a b P (natFilt hU.measurable) U := by
  refine ⟨hU.mem_Icc, hU.continuous, measurable_natFilt hU.measurable, fun n w v hwv => ?_⟩
  set D := incr κ a b U n w v
  have hDi : Integrable D P := hU.integrable_incr n hwv
  -- `∫_A D = 0` for every `A ∈ 𝓗_w`
  have hA : ∀ A, MeasurableSet[natFilt hU.measurable w] A → ∫ ω in A, D ω ∂P = 0 := by
    intro A hAm
    have h_eq : natFilt hU.measurable w = MeasurableSpace.generateFrom
        (piiUnionInter (fun j => {s | MeasurableSet[MeasurableSpace.comap (U j) inferInstance] s})
          (Iic w)) :=
      (generateFrom_piiUnionInter_measurableSet _ _).symm
    have hpi : IsPiSystem (piiUnionInter
        (fun j => {s | MeasurableSet[MeasurableSpace.comap (U j) inferInstance] s}) (Iic w)) :=
      isPiSystem_piiUnionInter _
        (fun j => @MeasurableSpace.isPiSystem_measurableSet Ω
          (MeasurableSpace.comap (U j) inferInstance)) _
    have hmeas : ∀ s, MeasurableSet[natFilt hU.measurable w] s → MeasurableSet s :=
      fun s hs => (natFilt hU.measurable).le w s hs
    have hD0 : ∫ ω, D ω ∂P = 0 := by
      have := hU.2.2.2 0 Fin.elim0 Fin.elim0 n w v (fun i => Fin.elim0 i) hwv
      simpa [D, incr] using this
    refine MeasurableSpace.induction_on_inter (C := fun A _ => ∫ ω in A, D ω ∂P = 0) h_eq hpi
      (by simp) ?_ ?_ ?_ A hAm
    · -- the π-system
      rintro _ ⟨t, ht, f, hf, rfl⟩
      classical
      have hB : ∀ x ∈ t, ∃ B : Set ℝ, MeasurableSet B ∧ U x ⁻¹' B = f x := fun x hx => by
        have := hf x hx
        simp only [mem_ofPred_eq] at this
        exact MeasurableSpace.measurableSet_comap.1 this
      choose! Bf hBm hBeq using hB
      set m := t.card
      set e := t.equivFin
      set s : Fin m → ℝ := fun i => (e.symm i : ℝ)
      have hs : ∀ i, s i ≤ w := fun i => ht (e.symm i).2
      have hset : (⋂ x ∈ t, f x) = {ω | ∀ i, U (s i) ω ∈ Bf (s i)} := by
        ext ω
        simp only [mem_iInter, mem_ofPred_eq]
        constructor
        · intro h i
          have := h (s i) (e.symm i).2
          rw [← hBeq _ (e.symm i).2] at this
          exact this
        · intro h x hx
          have := h (e ⟨x, hx⟩)
          simp only [s, Equiv.symm_apply_apply] at this
          rw [← hBeq x hx]
          exact this
      rw [hset]
      exact hU.setIntegral_cylinder_eq_zero n hwv s hs (fun i => Bf (s i))
        (fun i => hBm _ (e.symm i).2)
    · -- complements
      intro A hAm' hA'
      rw [setIntegral_compl (hmeas A hAm') hDi, hD0, hA', sub_zero]
    · -- countable disjoint unions
      intro f hdisj hfm hf
      rw [integral_iUnion (fun i => hmeas _ (hfm i)) hdisj hDi.integrableOn]
      simp [hf]
  have h := ae_eq_condExp_of_forall_setIntegral_eq ((natFilt hU.measurable).le w) hDi
    (g := fun _ => (0 : ℝ)) (fun _ _ _ => integrableOn_zero)
    (fun A hAm _ => by rw [hA A hAm]; simp) aestronglyMeasurable_const
  exact h.symm

end Jacobi

end Sec2

end InteractingSLE
