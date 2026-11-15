/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.NonBoundaryKernel
import InteractingSLE.WangWu.Locality
import InteractingSLE.GFF.LocalSets.AvoidIndep
import InteractingSLE.Spec.Sobolev.ThinRange

/-!
# Omitting the field-germ information (Wang–Wu Corollary 4.23, last paragraph)

Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.5, end of the proof of Corollary 4.23
(text dump lines 1805–1815): "A countable determining family identifies the full conditional probability kernel. It is
Gaussian and depends only on the labelled geometry `A` … More explicitly, encode any additional local-set information
used in conditioning by a standard Borel variable `L` measurable from `(A, h)`. The preceding kernel identity says that
`h` and `L` are conditionally independent given `A`. Lemma 4.2 then shows that `L` is already measurable from `A`."

Abstract form: if the conditional characteristic functional of the field `F` given `𝒢` is `𝒜`-measurable for a
smaller `𝒜` (the labelled geometry), then `F ⟂ 𝒢 | 𝒜` (`condIndepEv_of_condExp_exp`), and any `L ≤ 𝒢` a.s. determined
by `𝒜 ∨ σ(F)` is a.s. determined by `𝒜` alone (`aeDeterminedSigma_of_condExp_exp`, through Lemma 4.2,
`aeDeterminedSigma_of_condIndepEv_of_sup`). The kernel identity `ae_condExp_exp_eq_gaussCF` supplies the hypothesis when
the mean `v` and the kernel `G` are functions of the geometry.

The uniqueness step uses `Sobolev.measure_eq_of_setIntegral_exp` (laws on `DistOn` are determined by characteristic
functionals) for the two finite measures `B ↦ P(g ∩ F⁻¹B)` and `B ↦ E[P(g | 𝒜); F ∈ B]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace InteractingSLE.WangWu

section Germ

variable {Ω : Type*} {𝒜 𝒢 L : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- Clamping into `[0, 1]`. -/
def clampOne (Y : Ω → ℝ) : Ω → ℝ := fun ω => max 0 (min 1 (Y ω))

omit mΩ [IsProbabilityMeasure P] in
lemma clampOne_nonneg (Y : Ω → ℝ) (ω : Ω) : 0 ≤ clampOne Y ω := le_max_left _ _

omit mΩ [IsProbabilityMeasure P] in
lemma clampOne_le_one (Y : Ω → ℝ) (ω : Ω) : clampOne Y ω ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

omit mΩ [IsProbabilityMeasure P] in
lemma stronglyMeasurable_clampOne {m : MeasurableSpace Ω} {Y : Ω → ℝ}
    (hY : StronglyMeasurable[m] Y) : StronglyMeasurable[m] (clampOne Y) := by
  have h := (hY.measurable.min (@measurable_const _ _ _ m (1 : ℝ))).max
    (@measurable_const _ _ _ m (0 : ℝ))
  have e : clampOne Y = fun ω => max (min (Y ω) 1) 0 := by
    funext ω; simp only [clampOne, max_comm, min_comm]
  rw [e]
  exact h.stronglyMeasurable

omit [IsProbabilityMeasure P] in
/-- The conditional probability of an event, clamped into `[0, 1]`, is a version of it. -/
lemma clampOne_condExp_ae_eq {g : Set Ω} :
    clampOne (P⟦g | 𝒜⟧) =ᵐ[P] P⟦g | 𝒜⟧ := by
  have h0 : 0 ≤ᵐ[P] P⟦g | 𝒜⟧ :=
    condExp_nonneg (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have h1 : ∀ᵐ ω ∂P, |(P⟦g | 𝒜⟧) ω| ≤ (1 : ℝ) := by
    refine ae_bdd_abs_condExp_of_ae_bdd_abs (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ g <;> simp [hω]
  filter_upwards [h0, h1] with ω ha hb
  have hb' : (P⟦g | 𝒜⟧) ω ≤ 1 := (le_abs_self _).trans hb
  have ha' : 0 ≤ (P⟦g | 𝒜⟧) ω := by simpa using ha
  simp only [clampOne, min_eq_right hb', max_eq_right ha']

/-- Truncation into the closed unit disc. -/
def truncOne (Φ : Ω → ℂ) : Ω → ℂ := fun ω => if ‖Φ ω‖ ≤ 1 then Φ ω else 0

omit mΩ [IsProbabilityMeasure P] in
lemma norm_truncOne_le (Φ : Ω → ℂ) (ω : Ω) : ‖truncOne Φ ω‖ ≤ 1 := by
  unfold truncOne
  split_ifs with h
  · exact h
  · simp

omit mΩ [IsProbabilityMeasure P] in
lemma stronglyMeasurable_truncOne {m : MeasurableSpace Ω} {Φ : Ω → ℂ}
    (hΦ : StronglyMeasurable[m] Φ) : StronglyMeasurable[m] (truncOne Φ) := by
  have hs : MeasurableSet[m] {ω | ‖Φ ω‖ ≤ 1} :=
    measurableSet_le hΦ.measurable.norm (@measurable_const _ _ _ m (1 : ℝ))
  exact StronglyMeasurable.ite hs hΦ stronglyMeasurable_const

/-- `∫_s X = E[P(s | 𝒜) X]` for a bounded `𝒜`-measurable real `X`. -/
lemma setIntegral_eq_integral_condExp_mul_real (h𝒜 : 𝒜 ≤ mΩ) {s : Set Ω} (hs : MeasurableSet s)
    {X : Ω → ℝ} (hX : StronglyMeasurable[𝒜] X) (hXb : ∀ ω, |X ω| ≤ 1) :
    ∫ ω in s, X ω ∂P = ∫ ω, (P⟦s | 𝒜⟧) ω * X ω ∂P := by
  have hXi : Integrable X P :=
    Integrable.of_bound (C := 1) (hX.mono h𝒜).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hXb ω)
  have hind : Integrable (s.indicator fun _ => (1 : ℝ)) P := (integrable_const (1 : ℝ)).indicator hs
  have hprod : Integrable ((s.indicator fun _ => (1 : ℝ)) * X) P := by
    refine (hXi.indicator hs).congr (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ s <;> simp [hω]
  have hpull := condExp_mul_of_aestronglyMeasurable_right (m := 𝒜) (μ := P)
    hX.aestronglyMeasurable hprod hind
  calc ∫ ω in s, X ω ∂P = ∫ ω, ((s.indicator fun _ => (1 : ℝ)) * X) ω ∂P := by
        rw [← integral_indicator hs]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        by_cases hω : ω ∈ s <;> simp [hω]
    _ = ∫ ω, (P[(s.indicator fun _ => (1 : ℝ)) * X | 𝒜]) ω ∂P := (integral_condExp h𝒜).symm
    _ = ∫ ω, (P⟦s | 𝒜⟧) ω * X ω ∂P := integral_congr_ae hpull

/-- **The two finite measures agree.** If the conditional characteristic functional of `F` given `𝒢` is
`𝒜`-measurable (`𝒜 ≤ 𝒢`), then for every `g ∈ 𝒢` and every measurable `S`,
`P(g ∩ F⁻¹S) = ∫_{F⁻¹S} P(g | 𝒜)` (with the conditional probability clamped into `[0, 1]`). -/
theorem measure_inter_preimage_eq (h𝒜𝒢 : 𝒜 ≤ 𝒢) (h𝒢 : 𝒢 ≤ mΩ) (hF : Measurable F)
    (hΦ : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∃ Φ : Ω → ℂ, StronglyMeasurable[𝒜] Φ ∧
      P[fun ω => Complex.exp (Complex.I * (F ω φ : ℂ)) | 𝒢] =ᵐ[P] Φ)
    {g : Set Ω} (hg : MeasurableSet[𝒢] g) {S : Set (LQGMetric.DistOn upperHalfPlaneOpens)}
    (hS : MeasurableSet S) :
    P (g ∩ F ⁻¹' S) = ∫⁻ ω in F ⁻¹' S, ENNReal.ofReal (clampOne (P⟦g | 𝒜⟧) ω) ∂P := by
  have h𝒜 : 𝒜 ≤ mΩ := h𝒜𝒢.trans h𝒢
  have hg0 : MeasurableSet g := h𝒢 _ hg
  set Y := clampOne (P⟦g | 𝒜⟧) with hY
  have hYm : StronglyMeasurable[𝒜] Y := stronglyMeasurable_clampOne stronglyMeasurable_condExp
  have hYae : Y =ᵐ[P] P⟦g | 𝒜⟧ := clampOne_condExp_ae_eq
  set d : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Y ω) with hd
  have hdm : Measurable d := ENNReal.measurable_ofReal.comp (hYm.mono h𝒜).measurable
  have hdfin : ∫⁻ ω, d ω ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ω, (1 : ℝ≥0∞) ∂P) (by simp) (lintegral_mono fun ω => ?_)
    rw [hd, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (clampOne_le_one _ ω)
  have : IsFiniteMeasure (P.withDensity d) := isFiniteMeasure_withDensity hdfin
  set ι : Ω → LQGMetric.DistOn upperHalfPlaneOpens × Unit := fun ω => (F ω, ()) with hι
  have hιm : Measurable ι := hF.prodMk measurable_const
  have key : (P.restrict g).map ι = (P.withDensity d).map ι := by
    refine Sobolev.measure_eq_of_setIntegral_exp fun φ B hB => ?_
    rcases B.eq_empty_or_nonempty with rfl | hne
    · simp
    have hBu : B = univ := eq_univ_of_forall fun u => by
      obtain ⟨v, hv⟩ := hne
      exact (Subsingleton.elim u v) ▸ hv
    subst hBu
    rw [univ_prod_univ, setIntegral_univ, setIntegral_univ]
    obtain ⟨Φ, hΦm, hΦe⟩ := hΦ φ
    have hmexp : Measurable fun p : LQGMetric.DistOn upperHalfPlaneOpens × Unit =>
        Complex.exp (↑(p.1 φ) * Complex.I) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        ((Sobolev.measurable_distOn_apply φ).comp measurable_fst)).mul_const _)
    rw [integral_map hιm.aemeasurable hmexp.aestronglyMeasurable,
      integral_map hιm.aemeasurable hmexp.aestronglyMeasurable]
    simp only [hι]
    simp_rw [mul_comm _ Complex.I]
    set e : Ω → ℂ := fun ω => Complex.exp (Complex.I * (F ω φ : ℂ)) with he
    have he_int : Integrable e P := by
      refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
      · exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
          ((Sobolev.measurable_distOn_apply φ).comp hF)))).aestronglyMeasurable
      · rw [he, Complex.norm_exp_I_mul_ofReal]
    set Φ' := truncOne Φ with hΦ'
    have hΦ'm : StronglyMeasurable[𝒜] Φ' := stronglyMeasurable_truncOne hΦm
    have hΦ'e : P[e | 𝒢] =ᵐ[P] Φ' := by
      have hb := ae_bdd_norm_condExp_of_ae_bdd_norm (m := 𝒢) (μ := P) (f := e) (R := 1)
        (Eventually.of_forall fun ω => by rw [he, Complex.norm_exp_I_mul_ofReal])
      filter_upwards [hΦe, hb] with ω h1 h2
      rw [hΦ', truncOne, ← h1]
      simp [h2]
    have hW : StronglyMeasurable[𝒢] fun ω => (Y ω : ℂ) :=
      Complex.continuous_ofReal.comp_stronglyMeasurable (hYm.mono h𝒜𝒢)
    have hWb : ∀ ω, ‖(Y ω : ℂ)‖ ≤ 1 := fun ω => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (clampOne_nonneg _ ω)]
      exact clampOne_le_one _ ω
    calc ∫ ω in g, e ω ∂P = ∫ ω in g, (P[e | 𝒢]) ω ∂P := (setIntegral_condExp h𝒢 he_int hg).symm
      _ = ∫ ω in g, Φ' ω ∂P := setIntegral_congr_ae hg0 (hΦ'e.mono fun ω h _ => h)
      _ = ∫ ω, (((P⟦g | 𝒜⟧) ω : ℝ) : ℂ) * Φ' ω ∂P :=
          LocalSets.setIntegral_eq_integral_condExp_mul h𝒜 hg0 hΦ'm (norm_truncOne_le Φ)
      _ = ∫ ω, (Y ω : ℂ) * Φ' ω ∂P := integral_congr_ae (hYae.mono fun ω h => by simp only [h])
      _ = ∫ ω, (Y ω : ℂ) * (P[e | 𝒢]) ω ∂P := integral_congr_ae (hΦ'e.mono fun ω h => by simp only [h])
      _ = ∫ ω, (Y ω : ℂ) * e ω ∂P := (LocalSets.integral_mul_condExp_of_bdd h𝒢 hW hWb he_int).symm
      _ = ∫ ω, e ω ∂(P.withDensity d) := by
          rw [integral_withDensity_eq_integral_toReal_smul hdm
            (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          show (Y ω : ℂ) * e ω = (ENNReal.ofReal (Y ω)).toReal • e ω
          rw [ENNReal.toReal_ofReal (clampOne_nonneg _ ω), Complex.real_smul]
  have h1 := congrArg (fun ν => ν (S ×ˢ univ)) key
  rw [Measure.map_apply hιm (hS.prod MeasurableSet.univ),
    Measure.map_apply hιm (hS.prod MeasurableSet.univ)] at h1
  have hpre : ι ⁻¹' (S ×ˢ univ) = F ⁻¹' S := by ext ω; simp [hι]
  rw [hpre, Measure.restrict_apply (hF hS), withDensity_apply _ (hF hS)] at h1
  rw [inter_comm]
  exact h1

/-- **Conditional independence from an `𝒜`-measurable characteristic functional** (Corollary 4.23: "The preceding
kernel identity says that `h` and `L` are conditionally independent given `A`"). If `𝒜 ≤ 𝒢 ≤ mΩ` and for every test
function `φ` the conditional characteristic functional `E[e^{iFφ} | 𝒢]` has an `𝒜`-measurable version, then
`σ(F) ⟂ 𝒢 | 𝒜`. -/
theorem condIndepEv_of_condExp_exp (h𝒜𝒢 : 𝒜 ≤ 𝒢) (h𝒢 : 𝒢 ≤ mΩ) (hF : Measurable F)
    (hΦ : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∃ Φ : Ω → ℂ, StronglyMeasurable[𝒜] Φ ∧
      P[fun ω => Complex.exp (Complex.I * (F ω φ : ℂ)) | 𝒢] =ᵐ[P] Φ) :
    LQGMetric.CondIndepEv 𝒜 (MeasurableSpace.comap F inferInstance) 𝒢 P := by
  have h𝒜 : 𝒜 ≤ mΩ := h𝒜𝒢.trans h𝒢
  refine LQGMetric.condIndepEv_of_condExp_sup_eq h𝒜 hF.comap_le h𝒢 ?_
  rintro _ ⟨S, hS, rfl⟩
  rw [sup_eq_left.2 h𝒜𝒢]
  set a := F ⁻¹' S with ha
  have ha0 : MeasurableSet a := hF hS
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝒢 ((integrable_const (1 : ℝ)).indicator ha0)
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs _ => ?_)
    (stronglyMeasurable_condExp.mono h𝒜𝒢).aestronglyMeasurable).symm
  have hs0 : MeasurableSet s := h𝒢 _ hs
  set Ya := clampOne (P⟦a | 𝒜⟧) with hYa
  set Ys := clampOne (P⟦s | 𝒜⟧) with hYs
  have hYam : StronglyMeasurable[𝒜] Ya := stronglyMeasurable_clampOne stronglyMeasurable_condExp
  have hYsm : StronglyMeasurable[𝒜] Ys := stronglyMeasurable_clampOne stronglyMeasurable_condExp
  have hYab : ∀ ω, |Ya ω| ≤ 1 := fun ω => by
    rw [abs_of_nonneg (clampOne_nonneg _ ω)]; exact clampOne_le_one _ ω
  have hYsb : ∀ ω, |Ys ω| ≤ 1 := fun ω => by
    rw [abs_of_nonneg (clampOne_nonneg _ ω)]; exact clampOne_le_one _ ω
  have hYae : Ya =ᵐ[P] P⟦a | 𝒜⟧ := clampOne_condExp_ae_eq
  have hYse : Ys =ᵐ[P] P⟦s | 𝒜⟧ := clampOne_condExp_ae_eq
  -- `∫_s P(a|𝒜) = ∫_a P(s|𝒜)` (both equal `E[P(s|𝒜) P(a|𝒜)]`)
  have hsym : ∫ ω in s, (P⟦a | 𝒜⟧) ω ∂P = ∫ ω in a, Ys ω ∂P := by
    calc ∫ ω in s, (P⟦a | 𝒜⟧) ω ∂P = ∫ ω in s, Ya ω ∂P :=
          setIntegral_congr_ae hs0 (hYae.mono fun ω h _ => h.symm)
      _ = ∫ ω, (P⟦s | 𝒜⟧) ω * Ya ω ∂P :=
          setIntegral_eq_integral_condExp_mul_real h𝒜 hs0 hYam hYab
      _ = ∫ ω, Ys ω * Ya ω ∂P := integral_congr_ae (hYse.mono fun ω h => by simp only [h])
      _ = ∫ ω, (P⟦a | 𝒜⟧) ω * Ys ω ∂P :=
          integral_congr_ae (hYae.mono fun ω h => by simp only [h]; ring)
      _ = ∫ ω in a, Ys ω ∂P := (setIntegral_eq_integral_condExp_mul_real h𝒜 ha0 hYsm hYsb).symm
  rw [hsym, setIntegral_indicator ha0, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => clampOne_nonneg _ ω)
      ((hYsm.mono h𝒜).aestronglyMeasurable),
    ← measure_inter_preimage_eq h𝒜𝒢 h𝒢 hF hΦ hs hS]

/-- **Wang–Wu Corollary 4.23, last paragraph (the field-germ information may be omitted).** Under the hypotheses of
`condIndepEv_of_condExp_exp`, any further information `L ≤ 𝒢` that is a.s. determined by `𝒜 ∨ σ(F)` is a.s.
determined by `𝒜` alone (Lemma 4.2, `aeDeterminedSigma_of_condIndepEv_of_sup`). -/
theorem aeDeterminedSigma_of_condExp_exp (h𝒜𝒢 : 𝒜 ≤ 𝒢) (h𝒢 : 𝒢 ≤ mΩ) (hF : Measurable F)
    (hΦ : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∃ Φ : Ω → ℂ, StronglyMeasurable[𝒜] Φ ∧
      P[fun ω => Complex.exp (Complex.I * (F ω φ : ℂ)) | 𝒢] =ᵐ[P] Φ)
    (hL : L ≤ 𝒢)
    (hdet : LQGMetric.AEDeterminedSigma L (𝒜 ⊔ MeasurableSpace.comap F inferInstance) P) :
    LQGMetric.AEDeterminedSigma L 𝒜 P := by
  have hci := (condIndepEv_of_condExp_exp h𝒜𝒢 h𝒢 hF hΦ).symm
  have hci' : LQGMetric.CondIndepEv 𝒜 L (MeasurableSpace.comap F inferInstance) P :=
    fun b a hb ha => hci b a (hL b hb) ha
  exact aeDeterminedSigma_of_condIndepEv_of_sup (hL.trans h𝒢) (h𝒜𝒢.trans h𝒢) hF.comap_le hdet hci'

end Germ

end InteractingSLE.WangWu
