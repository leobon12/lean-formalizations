import SupercriticalConformalCovariance.GM24.Decomp

/-!
# Measurability of the cutoff shift

The hypothesis `hXS` of `tendsto_tvDist_gm24` (measurability of `ω ↦ X ω + S ω` on `B`) for GM's
cutoff shift `S = χ · (Y − (Y, f_r))`:

* `exists_modification`: a jointly measurable random function with an a.s. property `p` (`p 0`) has a
  jointly measurable modification with the property for every `ω` (null set from
  `exists_measurable_superset_of_null`);
* `measurable_extend_zero`: extension by zero off `V` of a function jointly measurable on `Ω × V`;
* `measurable_smoothDist_cutoff`: Fubini measurability of `ω ↦ ∫ g S_ω`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter Topology
open LQGMetric

namespace SupercriticalConformalCovariance.GM24

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Modification on a null set.** -/
theorem exists_modification {V : Opens ℂ} {Y : Ω → ℂ → ℝ}
    (hYm : Measurable fun p : Ω × V => Y p.1 p.2) {p : (ℂ → ℝ) → Prop} (hp0 : p 0)
    (hp : ∀ᵐ ω ∂P, p (Y ω)) :
    ∃ Y' : Ω → ℂ → ℝ, (∀ ω, p (Y' ω)) ∧ (∀ᵐ ω ∂P, Y' ω = Y ω) ∧
      Measurable fun q : Ω × V => Y' q.1 q.2 := by
  classical
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hp)
  refine ⟨fun ω => if ω ∈ N then 0 else Y ω, fun ω => ?_, ?_, ?_⟩
  · by_cases hω : ω ∈ N
    · simp only [hω, if_true]; exact hp0
    · simp only [hω, if_false]
      by_contra h
      exact hω (hsub h)
  · rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hN0
    by_contra hωN
    exact hω (by simp only [hωN, if_false])
  · have hm : MeasurableSet {q : Ω × V | q.1 ∈ N} := measurable_fst hNm
    have e : (fun q : Ω × V => (if q.1 ∈ N then (0 : ℂ → ℝ) else Y q.1) q.2) =
        fun q => if q.1 ∈ N then 0 else Y q.1 q.2 := by
      funext q; split_ifs <;> rfl
    rw [e]
    exact Measurable.ite hm measurable_const hYm

/-- Extension by zero off `V`. -/
theorem measurable_extend_zero {V : Opens ℂ} {Y : Ω → ℂ → ℝ}
    (hYm : Measurable fun q : Ω × V => Y q.1 q.2) :
    Measurable fun q : Ω × ℂ => (V : Set ℂ).indicator (Y q.1) q.2 := by
  have hs : MeasurableSet {q : Ω × ℂ | q.2 ∈ (V : Set ℂ)} :=
    measurable_snd V.isOpen.measurableSet
  refine measurable_of_restrict_of_restrict_compl hs ?_ ?_
  · change Measurable fun q : {q : Ω × ℂ // q.2 ∈ (V : Set ℂ)} =>
      (V : Set ℂ).indicator (Y q.1.1) q.1.2
    have e : (fun q : {q : Ω × ℂ // q.2 ∈ (V : Set ℂ)} => (V : Set ℂ).indicator (Y q.1.1) q.1.2) =
        (fun q : Ω × V => Y q.1 q.2) ∘
          fun q : {q : Ω × ℂ // q.2 ∈ (V : Set ℂ)} => (q.1.1, (⟨q.1.2, q.2⟩ : V)) := by
      funext q
      exact indicator_of_mem q.2 _
    rw [e]
    exact hYm.comp ((measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk))
  · change Measurable fun q : ↥({q : Ω × ℂ | q.2 ∈ (V : Set ℂ)}ᶜ) =>
      (V : Set ℂ).indicator (Y q.1.1) q.1.2
    have e : (fun q : ↥({q : Ω × ℂ | q.2 ∈ (V : Set ℂ)}ᶜ) =>
        (V : Set ℂ).indicator (Y q.1.1) q.1.2) = fun _ => (0 : ℝ) := by
      funext q
      exact indicator_of_notMem (s := (V : Set ℂ)) (f := Y q.1.1) q.2
    rw [e]
    exact measurable_const

/-- Fubini measurability of a pairing `ω ↦ ∫ g · F(ω, ·)` with `g` supported in `B ⊆ V`. -/
theorem measurable_integral_test_mul {B V : Opens ℂ} (hBV : B ≤ V) (g : TestOn B)
    {F : Ω → ℂ → ℝ} {G : Ω × ℂ → ℝ} (hG : Measurable G)
    (hFG : ∀ ω, ∀ x ∈ (B : Set ℂ), F ω x = G (ω, x)) :
    Measurable fun ω => ∫ x, g x * F ω x := by
  have e : (fun ω => ∫ x, g x * F ω x) = fun ω => ∫ x, g x * G (ω, x) := by
    funext ω
    congr 1
    funext x
    by_cases hx : x ∈ (B : Set ℂ)
    · rw [hFG ω x hx]
    · have : g x = 0 := g.zero_on_compl hx
      rw [this, zero_mul, zero_mul]
  rw [e]
  have hm : Measurable fun q : Ω × ℂ => g q.2 * G q := (g.continuous.measurable.comp measurable_snd).mul hG
  exact (StronglyMeasurable.integral_prod_right' (ν := volume) hm.stronglyMeasurable).measurable

/-- **Measurability of the cutoff shift as a distribution on `B`.** -/
theorem measurable_smoothDist_cutoff {B V : Opens ℂ} (hBV : B ≤ V) {χ : ℂ → ℝ}
    (hχ : Continuous χ) (fr : TestOn B) {Y : Ω → ℂ → ℝ}
    (hYm : Measurable fun q : Ω × V => Y q.1 q.2) (hYc : ∀ ω, ContinuousOn (Y ω) B) :
    Measurable fun ω => smoothDist B (cutoffShift χ fr (Y ω)) := by
  have hYe := measurable_extend_zero hYm
  have hc : Measurable fun ω => smoothDist B (Y ω) fr := by
    have e : (fun ω => smoothDist B (Y ω) fr) = fun ω => ∫ x, fr x * Y ω x := by
      funext ω; exact smoothDist_apply (hYc ω) fr
    rw [e]
    exact measurable_integral_test_mul hBV fr hYe fun ω x hx =>
      (indicator_of_mem (hBV hx) _).symm
  apply measurable_distOn_iff.mpr
  intro g
  have hSc : ∀ ω, ContinuousOn (cutoffShift χ fr (Y ω)) B := fun ω =>
    hχ.continuousOn.mul ((hYc ω).sub continuousOn_const)
  have e : (fun ω => smoothDist B (cutoffShift χ fr (Y ω)) g) =
      fun ω => ∫ x, g x * cutoffShift χ fr (Y ω) x := by
    funext ω; exact smoothDist_apply (hSc ω) g
  rw [e]
  refine measurable_integral_test_mul hBV g (G := fun q : Ω × ℂ =>
    χ q.2 * ((V : Set ℂ).indicator (Y q.1) q.2 - smoothDist B (Y q.1) fr)) ?_ ?_
  · exact (hχ.measurable.comp measurable_snd).mul (hYe.sub (hc.comp measurable_fst))
  · intro ω x hx
    simp only [cutoffShift, indicator_of_mem (hBV hx)]

/-- The sum `X + S` of `hXS`. -/
theorem measurable_add_smoothDist_cutoff {B V : Opens ℂ} (hBV : B ≤ V) {χ : ℂ → ℝ}
    (hχ : Continuous χ) (fr : TestOn B) {X : Ω → DistOn B} (hX : Measurable X) {Y : Ω → ℂ → ℝ}
    (hYm : Measurable fun q : Ω × V => Y q.1 q.2) (hYc : ∀ ω, ContinuousOn (Y ω) B) :
    Measurable fun ω => X ω + smoothDist B (cutoffShift χ fr (Y ω)) := by
  apply measurable_distOn_iff.mpr
  intro g
  have h2 := measurable_distOn_iff.mp (measurable_smoothDist_cutoff hBV hχ fr hYm hYc) g
  have h1 := measurable_distOn_iff.mp hX g
  change Measurable fun ω => (X ω) g + (smoothDist B (cutoffShift χ fr (Y ω))) g
  exact h1.add h2

end SupercriticalConformalCovariance.GM24
