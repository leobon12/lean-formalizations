/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHRec

/-!
# Aux. lemma 54: the law of the record is determined by the history law and the kernel at the stop

Packet PROVE-LOCEXT-H, item (M). Aux. lemma 54 (specification p. 246): "The pair `(𝓗_S, H_S)` has exactly the same
joint law in the stopped coupling and in the fixed full reference coupling: the first marginal is the common stopped
driving law, and its conditional second marginal is the specified Gaussian kernel." With the record `recOf h Y =
(Y, ψ ↦ h(ψ) 1[supp ψ ∩ K = ∅])` of `LocalExtHRec`:

* `measure_eq_of_setIntegral_cexp_pi`: two finite measures on `Γ × (ι → ℝ)` (product σ-algebra) are equal if, on every
  rectangle `B × (ι → ℝ)`, they have the same integrals of `exp(i Σ_{j ∈ F} c_j x_j)` for every finite `F` (finite
  dimensional characteristic functions on the measurable cylinders);
* `HasHistKernel P m Y h G`: given `m`, the characteristic functional of `h` at every test function whose support avoids
  the recorded hull is the fixed functional `G φ` of the recorded history `Y`;
* **`map_recOf_eq_of_hasHistKernel`**: two such configurations with the same functional `G` and the same history law
  have the same record law. On the event that exactly the test functions of `J ⊆ F` avoid the hull, the tested
  combination is `h(Σ_{j ∈ J} c_j φ_j)`, whose support avoids the hull; the kernel replaces it by `G` of the history.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open LQGMetric

/-! ### Finite-dimensional characteristic functions on a product with a function space -/

/-- **Two finite measures on `Γ × (ι → ℝ)` with the same finite-dimensional characteristic functions on every rectangle
`B × (ι → ℝ)` are equal.** -/
theorem measure_eq_of_setIntegral_cexp_pi {Γ ι : Type*} [MeasurableSpace Γ]
    {ν₁ ν₂ : Measure (Γ × (ι → ℝ))} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h : ∀ (F : Finset ι) (c : ι → ℝ) (B : Set Γ), MeasurableSet B →
      ∫ p in B ×ˢ univ, Complex.exp (((∑ j ∈ F, c j * p.2 j : ℝ) : ℂ) * Complex.I) ∂ν₁ =
        ∫ p in B ×ˢ univ, Complex.exp (((∑ j ∈ F, c j * p.2 j : ℝ) : ℂ) * Complex.I) ∂ν₂) : ν₁ = ν₂ := by
  classical
  set C₁ := measurableCylinders (fun _ : ι => ℝ) with hC₁def
  set C := Set.image2 (fun x1 x2 => x1 ×ˢ x2) {B : Set Γ | MeasurableSet B} C₁ with hCdef
  have hC₁ : IsPiSystem C₁ := isPiSystem_measurableCylinders
  have hcylU : (univ : Set (ι → ℝ)) ∈ C₁ := by
    rw [hC₁def, mem_measurableCylinders]
    exact ⟨∅, univ, MeasurableSet.univ, by simp [cylinder]⟩
  have hspan₁ : IsCountablySpanning C₁ := ⟨fun _ => univ, fun _ => hcylU, iUnion_const univ⟩
  have hgen : (inferInstance : MeasurableSpace (Γ × (ι → ℝ))) = MeasurableSpace.generateFrom C := by
    calc (inferInstance : MeasurableSpace (Γ × (ι → ℝ)))
        = @Prod.instMeasurableSpace _ _ (MeasurableSpace.generateFrom {B : Set Γ | MeasurableSet B})
            (MeasurableSpace.generateFrom C₁) := by
          rw [hC₁def, generateFrom_measurableCylinders, MeasurableSpace.generateFrom_measurableSet]
      _ = MeasurableSpace.generateFrom C := generateFrom_prod_eq isCountablySpanning_measurableSet hspan₁
  have hrect : ∀ s ∈ C, ν₁ s = ν₂ s := by
    rintro _ ⟨B, hB, E, ht, rfl⟩
    rw [hC₁def, mem_measurableCylinders] at ht
    obtain ⟨S', Sx, hSx, rfl⟩ := ht
    set pr : (ι → ℝ) → EuclideanSpace ℝ S' := fun x => WithLp.toLp 2 (fun j : S' => x j) with hprdef
    have hpr : Measurable pr := (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun j => measurable_pi_apply (j : ι))
    have hpr2 : Measurable (fun p : Γ × (ι → ℝ) => pr p.2) := hpr.comp measurable_snd
    have hBU : MeasurableSet (B ×ˢ univ : Set (Γ × (ι → ℝ))) := hB.prod MeasurableSet.univ
    set c : EuclideanSpace ℝ S' → ι → ℝ := fun t i => if hi : i ∈ S' then t.ofLp ⟨i, hi⟩ else 0 with hcdef
    have key : ∀ (x : ι → ℝ) (t : EuclideanSpace ℝ S'), inner ℝ (pr x) t = ∑ j ∈ S', c t j * x j := by
      intro x t
      rw [PiLp.inner_apply, ← Finset.sum_coe_sort S']
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hprdef, hcdef, WithLp.ofLp_toLp, Finset.coe_mem, ↓reduceDIte, Subtype.coe_eta,
        RCLike.inner_apply, conj_trivial]
    have hchar : charFun ((ν₁.restrict (B ×ˢ univ)).map (fun p => pr p.2)) =
        charFun ((ν₂.restrict (B ×ˢ univ)).map (fun p => pr p.2)) := by
      funext t
      rw [charFun_apply, charFun_apply,
        integral_map hpr2.aemeasurable (by fun_prop), integral_map hpr2.aemeasurable (by fun_prop)]
      simp_rw [key]
      exact h S' (c t) B hB
    have heq := Measure.ext_of_charFun hchar
    have hset : B ×ˢ cylinder S' Sx =
        (fun p : Γ × (ι → ℝ) => pr p.2) ⁻¹' {y | y.ofLp ∈ Sx} ∩ (B ×ˢ univ) := by
      ext p
      simp [hprdef, cylinder, and_comm]
      exact fun _ => Iff.rfl
    have hmS : MeasurableSet {y : EuclideanSpace ℝ S' | y.ofLp ∈ Sx} :=
      (WithLp.measurable_ofLp 2 _) hSx
    have hval : ∀ ν : Measure (Γ × (ι → ℝ)),
        ν (B ×ˢ cylinder S' Sx) = ((ν.restrict (B ×ˢ univ)).map (fun p => pr p.2)) {y | y.ofLp ∈ Sx} := by
      intro ν
      rw [Measure.map_apply hpr2 hmS, Measure.restrict_apply (hpr2 hmS), hset]
    rw [hval, hval, heq]
  refine ext_of_generate_finite C hgen (MeasurableSpace.isPiSystem_measurableSet.prod hC₁) hrect ?_
  have := hrect (univ ×ˢ univ) ⟨univ, MeasurableSet.univ, univ, hcylU, rfl⟩
  rwa [univ_prod_univ] at this

/-! ### Kernels read from the recorded history -/

section Kernel

/-- **The kernel at the stop read from the recorded history**: given `m`, at every test function `φ` whose support
avoids the recorded hull `tsHull (Y ω)`, the conditional characteristic functional of `h` is `G φ (Y ω)`. -/
def HasHistKernel {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (m : MeasurableSpace Ω) (Y : Ω → TwoSeedHist)
    (h : Ω → DistOn upperHalfPlaneOpens) (G : TestOn upperHalfPlaneOpens → TwoSeedHist → ℂ) : Prop :=
  ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (tsHull (Y ω)) →
    P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | m] ω = G φ (Y ω)

theorem integrable_cexp_field {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
  Integrable.of_bound (Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((measurable_distOn_apply φ).comp hh)))).aestronglyMeasurable 1
    (Eventually.of_forall fun _ => (Complex.norm_exp_I_mul_ofReal _).le)

/-- **On a history event avoiding `supp φ`, the kernel computes the tested integral.** -/
theorem setIntegral_eq_of_hasHistKernel {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (hm : m ≤ mΩ)
    {Y : Ω → TwoSeedHist} (hY : Measurable[m] Y) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {G : TestOn upperHalfPlaneOpens → TwoSeedHist → ℂ} (hk : HasHistKernel P m Y h G)
    (φ : TestOn upperHalfPlaneOpens) {Γ : Set TwoSeedHist} (hΓ : MeasurableSet Γ)
    (hΓd : ∀ y ∈ Γ, Disjoint (tsupport φ) (tsHull y)) :
    ∫ ω in Y ⁻¹' Γ, Complex.exp (Complex.I * (h ω φ : ℂ)) ∂P = ∫ ω in Y ⁻¹' Γ, G φ (Y ω) ∂P := by
  rw [← setIntegral_condExp hm (integrable_cexp_field hh φ) (hY hΓ)]
  refine setIntegral_congr_ae ((hY.mono hm le_rfl) hΓ) ?_
  filter_upwards [hk φ] with ω hω hωΓ using hω (hΓd _ hωΓ)

open Classical in
/-- The test functions of `F` whose supports avoid the hull recorded in `y`. -/
def avoidSet (F : Finset (TestOn upperHalfPlaneOpens)) (y : TwoSeedHist) : Finset (TestOn upperHalfPlaneOpens) :=
  F.filter fun j => Disjoint (tsupport j) (tsHull y)

theorem measurableSet_avoidSet_eq (F J : Finset (TestOn upperHalfPlaneOpens)) :
    MeasurableSet {y : TwoSeedHist | avoidSet F y = J} := by
  classical
  have e : {y : TwoSeedHist | avoidSet F y = J} =
      (if J ⊆ F then univ else ∅) ∩ ⋂ j ∈ F, {y : TwoSeedHist | Disjoint (tsupport j) (tsHull y) ↔ j ∈ J} := by
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro rfl
      refine ⟨by simp only [avoidSet, Finset.filter_subset, ↓reduceIte, mem_univ], fun j hj => ?_⟩
      simp only [avoidSet, Finset.mem_filter, hj, true_and]
    · rintro ⟨hJ, hall⟩
      have hJF : J ⊆ F := by
        by_contra hc
        simp only [hc, ↓reduceIte, mem_empty_iff_false] at hJ
      ext j
      simp only [avoidSet, Finset.mem_filter]
      constructor
      · rintro ⟨hj, hd⟩
        exact (hall j hj).1 hd
      · intro hj
        exact ⟨hJF hj, (hall j (hJF hj)).2 hj⟩
  rw [e]
  refine MeasurableSet.inter (by split_ifs <;> simp) (MeasurableSet.biInter F.countable_toSet fun j _ => ?_)
  have hd := measurableSet_disjoint_tsHull (K := tsupport j) j.hasCompactSupport.isCompact
  by_cases hj : j ∈ J
  · simpa only [hj, iff_true] using hd
  · simp only [hj, iff_false]
    exact hd.compl

/-- On the event that exactly the test functions of `J` avoid the hull, the support of `Σ_{j ∈ J} c_j φ_j` avoids it. -/
theorem disjoint_tsupport_sum_of_avoidSet (F : Finset (TestOn upperHalfPlaneOpens)) (y : TwoSeedHist)
    (c : TestOn upperHalfPlaneOpens → ℝ) :
    Disjoint (tsupport ⇑(∑ j ∈ avoidSet F y, c j • j)) (tsHull y) := by
  classical
  refine Finset.sum_induction _ (fun φ : TestOn upperHalfPlaneOpens => Disjoint (tsupport φ) (tsHull y)) ?_ ?_ ?_
  · intro a b ha hb
    have h1 : tsupport ⇑(a + b) ⊆ tsupport ⇑a ∪ tsupport ⇑b := by
      rw [FunLike.coe_add]
      exact tsupport_add _ _
    exact Disjoint.mono_left h1 (disjoint_union_left.2 ⟨ha, hb⟩)
  · rw [FunLike.coe_zero, tsupport_zero]
    exact Set.empty_disjoint _
  · intro j hj
    have h1 : tsupport ⇑(c j • j) ⊆ tsupport ⇑j := by
      rw [FunLike.coe_smul]
      exact tsupport_smul_subset_right (fun _ => c j) _
    exact Disjoint.mono_left h1 (Finset.mem_filter.1 hj).2

/-- **The finite-dimensional characteristic functions of a record law** on a rectangle `B × (TestOn → ℝ)`: a sum over
the subsets `J ⊆ F` of history integrals of the kernel functional at `Σ_{j ∈ J} c_j φ_j`, on the events that exactly
the members of `J` avoid the hull. -/
theorem setIntegral_map_recOf {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (hm : m ≤ mΩ) {Y : Ω → TwoSeedHist} (hY : Measurable[m] Y)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) {G : TestOn upperHalfPlaneOpens → TwoSeedHist → ℂ}
    (hG : ∀ φ, Measurable (G φ)) (hk : HasHistKernel P m Y h G) (F : Finset (TestOn upperHalfPlaneOpens))
    (c : TestOn upperHalfPlaneOpens → ℝ) {B : Set TwoSeedHist} (hB : MeasurableSet B) :
    ∫ p in B ×ˢ univ, Complex.exp (((∑ j ∈ F, c j * p.2 j : ℝ) : ℂ) * Complex.I)
        ∂(P.map fun ω => recOf (h ω) (Y ω)) =
      ∑ J ∈ F.powerset, ∫ y in B ∩ {y | avoidSet F y = J}, G (∑ j ∈ J, c j • j) y ∂(P.map Y) := by
  classical
  have hYm : Measurable Y := hY.mono hm le_rfl
  have hrec : Measurable fun ω => recOf (h ω) (Y ω) := measurable_recOf.comp (hh.prodMk hYm)
  have hcm : Measurable fun p : RecSp => Complex.exp (((∑ j ∈ F, c j * p.2 j : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_exp.measurable.comp ((Complex.measurable_ofReal.comp
      (Finset.measurable_sum _ fun j _ => measurable_const.mul
        ((measurable_pi_apply j).comp measurable_snd))).mul_const _)
  have hpre : (fun ω => recOf (h ω) (Y ω)) ⁻¹' (B ×ˢ univ) = Y ⁻¹' B := by
    ext ω
    simp [recOf]
  rw [setIntegral_map (hB.prod MeasurableSet.univ) hcm.aestronglyMeasurable hrec.aemeasurable, hpre]
  -- the integrand is a finite sum over the possible sets of avoiding test functions
  set f : TestOn upperHalfPlaneOpens → Ω → ℂ := fun φ ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hfdef
  have hfm : ∀ φ, Measurable (f φ) := fun φ => Complex.continuous_exp.measurable.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp ((measurable_distOn_apply φ).comp hh)))
  have hA : ∀ J : Finset (TestOn upperHalfPlaneOpens), MeasurableSet (Y ⁻¹' {y | avoidSet F y = J}) :=
    fun J => hYm (measurableSet_avoidSet_eq F J)
  have hpt : ∀ ω, Complex.exp (((∑ j ∈ F, c j * (recOf (h ω) (Y ω)).2 j : ℝ) : ℂ) * Complex.I) =
      ∑ J ∈ F.powerset, (Y ⁻¹' {y | avoidSet F y = J}).indicator (f (∑ j ∈ J, c j • j)) ω := by
    intro ω
    rw [Finset.sum_eq_single (avoidSet F (Y ω))]
    · rw [indicator_of_mem (show ω ∈ Y ⁻¹' {y | avoidSet F y = avoidSet F (Y ω)} from rfl)]
      simp only [hfdef, recOf, fieldRec, map_sum, map_smul, smul_eq_mul]
      rw [mul_comm Complex.I]
      congr 3
      rw [avoidSet, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · intro J _ hJ
      exact indicator_of_notMem (fun h' => hJ h'.symm) _
    · intro h'
      exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ _)) h'
  simp_rw [hpt]
  rw [integral_finsetSum _ fun J _ => (Integrable.of_bound (hfm _).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)).indicator (hA J) |>.integrableOn]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [setIntegral_indicator (hA J), ← preimage_inter]
  have hΓ : MeasurableSet (B ∩ {y | avoidSet F y = J}) := hB.inter (measurableSet_avoidSet_eq F J)
  rw [setIntegral_eq_of_hasHistKernel hm hY hh hk _ hΓ fun y hy => by
      rw [← hy.2]; exact disjoint_tsupport_sum_of_avoidSet F y c,
    ← setIntegral_map hΓ (hG _).aestronglyMeasurable hYm.aemeasurable]

/-- **Aux. lemma 54's record law** (specification p. 246, "the first marginal is the common stopped driving law, and
its conditional second marginal is the specified Gaussian kernel"): two configurations whose fields have the same
kernel functional `G` of their recorded histories, and whose histories have the same law, have the same record law. -/
theorem map_recOf_eq_of_hasHistKernel {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} [mΩ₁ : MeasurableSpace Ω₁]
    {m₂ : MeasurableSpace Ω₂} [mΩ₂ : MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsFiniteMeasure P₁]
    [IsFiniteMeasure P₂] (hm₁ : m₁ ≤ mΩ₁) (hm₂ : m₂ ≤ mΩ₂) {Y₁ : Ω₁ → TwoSeedHist} {Y₂ : Ω₂ → TwoSeedHist}
    (hY₁ : Measurable[m₁] Y₁) (hY₂ : Measurable[m₂] Y₂) {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂)
    {G : TestOn upperHalfPlaneOpens → TwoSeedHist → ℂ} (hG : ∀ φ, Measurable (G φ))
    (hk₁ : HasHistKernel P₁ m₁ Y₁ h₁ G) (hk₂ : HasHistKernel P₂ m₂ Y₂ h₂ G) (hlaw : P₁.map Y₁ = P₂.map Y₂) :
    P₁.map (fun ω => recOf (h₁ ω) (Y₁ ω)) = P₂.map (fun ω => recOf (h₂ ω) (Y₂ ω)) := by
  refine measure_eq_of_setIntegral_cexp_pi fun F c B hB => ?_
  rw [setIntegral_map_recOf hm₁ hY₁ hh₁ hG hk₁ F c hB, setIntegral_map_recOf hm₂ hY₂ hh₂ hG hk₂ F c hB, hlaw]

end Kernel

end LocalExt

end InteractingSLE
