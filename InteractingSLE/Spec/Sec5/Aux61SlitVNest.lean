/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MeanIdNested
import InteractingSLE.Spec.Sec5.Aux61MeanIdUniq
import InteractingSLE.Spec.Sec7.Lemma725RefMarksGerm
import InteractingSLE.Spec.Sec7.Lemma72CLocal

/-!
# Aux. lemma 61, second half: the union mean against the flow line's own mean near the new slit (physical form)

Packet PROVE-AUX61-SLIT. Astra's follow-up 4 §1.1 (`source/external/AstraIG1/ig1_followup4_audited.txt` L113–L123,
ruling R71): "At every further pre-contact stop the two new sides have the canonical flow-line germs. Indeed each
compact part of a new side is separated from `K` and from the older forward range; Proposition 3.8 and its
boundary-patch proof, [S], pp. 59–60, compare its union mean with its own flow-line mean." and L84–L88: "We may
condition on the additional retained germ, prove the zero endpoint probability there, and then forget that germ by the
tower property."

The union `A` at the glued stop (counterflow hull ∪ flow prefix) comes with a conditional Gaussian decomposition
given a σ-algebra `𝒢` (the germs of `A` and the retained marks). The flow line's own prefix `L` at a deterministic own
time is an ordinary local set with its own mean `g₂` (the flow-line coupling mean). The two sets are not conditionally
independent and `L` is not measurable for `𝒢`; following Astra, the comparison is made for the LARGER union `A'` (the
union at the later stop `max(T, ρ)`, which contains `L`), with the germs of `A` and of `L` added to its marks (the germ
of a smaller set can be added to the marks of a larger marked local set,
`Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma`, R69), and then transferred back to `𝒢` on the event
`{A' = A}` by the tower property:

* **`ae_cexp_eq_of_le`**, **`ae_apply_eq_of_le`**, **`ae_forall_apply_eq_of_le`** (nested uniqueness): two conditional
  Gaussian decompositions of the same field given NESTED σ-algebras `𝒢 ≤ 𝒥`, whose domains agree on an event
  `S ∈ 𝒢`, have the same harmonic part almost surely on `S` (simultaneously for every test inside a common harmonic
  domain);
* **`ae_tendsto_sub_flowMean`**: almost surely, for every index `i` (countably many own times) and on the event
  `S i = {A' i = A}`, the harmonic function `u` representing `g − g₂ i` on `ℍ ∖ A` tends to `0` at every point
  `z₀ ∈ L i ∪ ℝ` near which `A ⊆ L i` — every point of the new slit sides separated from the counterflow hull and from
  the later part of the flow prefix.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal

namespace InteractingSLE.Sec5.Aux61SlitV

open QuantumZipper LQGMetric
open LocalSets WholeField

/-! ### Nested uniqueness of the harmonic part -/

section Nested

variable {Ω : Type u} {𝒢 𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {h g g' : Ω → DistOn upperHalfPlaneOpens} {U U' : Ω → Set ℂ} {S : Set Ω}

/-- A unit complex number with real part `1` is `1`. -/
theorem eq_one_of_re_eq_one {Z : ℂ} (hZ : ‖Z‖ = 1) (hre : Z.re = 1) : Z = 1 := by
  have h2 : Complex.normSq Z = 1 := by
    rw [← Complex.sq_norm, hZ, one_pow]
  rw [Complex.normSq_apply, hre, one_mul] at h2
  have him : Z.im = 0 := by nlinarith
  exact Complex.ext hre him

/-- **Nested uniqueness, one test, phase form.** Let `h − g` be conditionally a zero-boundary GFF on `U` given `𝒢`
and `h − g'` conditionally a zero-boundary GFF on `U'` given `𝒥 ⊇ 𝒢`, with `U' = U` on an event `S ∈ 𝒢`. Then
almost surely on `S`, `e^{i g'(φ)} = e^{i g(φ)}`.

Proof: with `Z = e^{i(g'(φ) − g(φ))}` (`𝒥`-measurable) and the covariance factor `c = e^{−½‖φ‖²_U}`,
`∫_S e^{i(h−g)(φ)} = ∫_S c` (condition on `𝒢`) and `= ∫_S Z c` (condition on `𝒥`, pull `Z` out, `U' = U` on `S`);
so `∫_S c (1 − Re Z) = 0` with a nonnegative integrand and `c > 0`, hence `Re Z = 1`, `Z = 1` on `S`. -/
theorem ae_cexp_eq_of_le (h𝒢𝒥 : 𝒢 ≤ 𝒥) (h𝒥 : 𝒥 ≤ mΩ) (hhm : Measurable h) (hg : Measurable[𝒢] g)
    (hg' : Measurable[𝒥] g') (hc : IsCondZeroBoundaryGFF P 𝒢 U fun ω => h ω - g ω)
    (hc' : IsCondZeroBoundaryGFF P 𝒥 U' fun ω => h ω - g' ω) (hS : MeasurableSet[𝒢] S)
    (hU : ∀ᵐ ω ∂P, ω ∈ S → U' ω = U ω) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ S →
      Complex.exp (Complex.I * (g' ω φ : ℂ)) = Complex.exp (Complex.I * (g ω φ : ℂ)) := by
  have h𝒢 : 𝒢 ≤ mΩ := h𝒢𝒥.trans h𝒥
  have hS𝒥 : MeasurableSet[𝒥] S := h𝒢𝒥 _ hS
  have hSm : MeasurableSet S := h𝒢 _ hS
  have hg𝒥 : Measurable[𝒥] fun ω => g ω φ :=
    (Sobolev.measurable_distOn_apply φ).comp (hg.mono h𝒢𝒥 le_rfl)
  have hg'𝒥 : Measurable[𝒥] fun ω => g' ω φ := (Sobolev.measurable_distOn_apply φ).comp hg'
  have hhφ : Measurable fun ω => h ω φ := (Sobolev.measurable_distOn_apply φ).comp hhm
  have hgφ : Measurable fun ω => g ω φ := hg𝒥.mono h𝒥 le_rfl
  have hg'φ : Measurable fun ω => g' ω φ := hg'𝒥.mono h𝒥 le_rfl
  set Z : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((g' ω φ - g ω φ : ℝ) : ℂ)) with hZdef
  set Y : Ω → ℂ := fun ω => Complex.exp (Complex.I * (((h ω - g ω) φ : ℝ) : ℂ)) with hYdef
  set Y' : Ω → ℂ := fun ω => Complex.exp (Complex.I * (((h ω - g' ω) φ : ℝ) : ℂ)) with hY'def
  set c₁ : Ω → ℝ := fun ω => Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) with hc₁def
  have hZn : ∀ ω, ‖Z ω‖ = 1 := fun ω => Complex.norm_exp_I_mul_ofReal _
  have hZsm : StronglyMeasurable[𝒥] Z :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (hg'𝒥.sub hg𝒥)))).stronglyMeasurable
  have hYm : Measurable fun ω => ((h ω - g ω) φ : ℝ) := by
    simp only [sub_apply]
    exact hhφ.sub hgφ
  have hY'm : Measurable fun ω => ((h ω - g' ω) φ : ℝ) := by
    simp only [sub_apply]
    exact hhφ.sub hg'φ
  have hYi : Integrable Y P := GFF.integrable_exp_I_mul hYm
  have hY'i : Integrable Y' P := GFF.integrable_exp_I_mul hY'm
  -- `Y = Z · Y'`
  have hYZ : Y = fun ω => (ContinuousLinearMap.mul ℝ ℂ) (Z ω) (Y' ω) := by
    funext ω
    have e₀ : ((h ω - g ω) φ : ℝ) = (g' ω φ - g ω φ) + (h ω - g' ω) φ := by
      simp only [sub_apply]
      ring
    have e : Complex.I * (((h ω - g ω) φ : ℝ) : ℂ) =
        Complex.I * ((g' ω φ - g ω φ : ℝ) : ℂ) + Complex.I * (((h ω - g' ω) φ : ℝ) : ℂ) := by
      rw [← mul_add, ← Complex.ofReal_add, e₀]
    simp only [hYdef, hZdef, hY'def, ContinuousLinearMap.mul_apply']
    rw [e, Complex.exp_add]
  -- the two conditional characteristic functionals
  have hc₁ : P[Y | 𝒢] =ᵐ[P] fun ω => ((c₁ ω : ℝ) : ℂ) := hc φ
  have hc₂ := hc' φ
  have hpull := condExp_stronglyMeasurable_bilin_of_bound (ContinuousLinearMap.mul ℝ ℂ) h𝒥 hZsm hY'i 1
    (ae_of_all _ fun ω => (hZn ω).le)
  have hc₁i : Integrable (fun ω => ((c₁ ω : ℝ) : ℂ)) P := integrable_condExp.congr hc₁
  have hZc₁i : Integrable (fun ω => Z ω * ((c₁ ω : ℝ) : ℂ)) P :=
    hc₁i.bdd_mul (hZsm.mono h𝒥).aestronglyMeasurable (ae_of_all _ fun ω => (hZn ω).le)
  -- the set integrals of `Y` over `S`
  have i₁ : ∫ ω in S, Y ω ∂P = ∫ ω in S, ((c₁ ω : ℝ) : ℂ) ∂P := by
    rw [← setIntegral_condExp h𝒢 hYi hS]
    exact setIntegral_congr_ae hSm (hc₁.mono fun ω hω _ => hω)
  have i₂ : ∫ ω in S, Y ω ∂P = ∫ ω in S, Z ω * ((c₁ ω : ℝ) : ℂ) ∂P := by
    rw [← setIntegral_condExp h𝒥 hYi hS𝒥]
    refine setIntegral_congr_ae hSm ?_
    filter_upwards [hpull, hc₂, hU] with ω h1 h2 h3 hωS
    rw [hYZ, h1, ContinuousLinearMap.mul_apply', h2, h3 hωS]
  -- `∫_S c (1 − Re Z) = 0`
  have i₃ : ∫ ω in S, (((c₁ ω : ℝ) : ℂ) - Z ω * ((c₁ ω : ℝ) : ℂ)) ∂P = 0 := by
    rw [integral_sub hc₁i.integrableOn hZc₁i.integrableOn, ← i₁, ← i₂, sub_self]
  have hfi : Integrable (fun ω => ((c₁ ω : ℝ) : ℂ) - Z ω * ((c₁ ω : ℝ) : ℂ)) P := hc₁i.sub hZc₁i
  have i₄ : ∫ ω in S, c₁ ω * (1 - (Z ω).re) ∂P = 0 := by
    have hre := integral_re (𝕜 := ℂ) (μ := P.restrict S) hfi.integrableOn
    rw [i₃, map_zero] at hre
    rw [← hre]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [RCLike.re_to_complex, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  have hc₁pos : ∀ ω, 0 < c₁ ω := fun ω => Real.exp_pos _
  have hnn : ∀ ω, 0 ≤ c₁ ω * (1 - (Z ω).re) := fun ω => by
    have : (Z ω).re ≤ 1 := (Complex.re_le_norm (Z ω)).trans (hZn ω).le
    exact mul_nonneg (hc₁pos ω).le (by linarith)
  have hfi' : IntegrableOn (fun ω => c₁ ω * (1 - (Z ω).re)) S P := by
    refine (hfi.re.congr (ae_of_all _ fun ω => ?_)).integrableOn
    simp only [RCLike.re_to_complex, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  have i₅ := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hnn) hfi').1 i₄
  filter_upwards [(ae_restrict_iff' hSm).1 i₅] with ω hω hωS
  have h0 : c₁ ω * (1 - (Z ω).re) = 0 := hω hωS
  have hre : (Z ω).re = 1 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h (hc₁pos ω).ne'
    · linarith
  have hZ1 : Z ω = 1 := eq_one_of_re_eq_one (hZn ω) hre
  have e : Complex.exp (Complex.I * (g' ω φ : ℂ)) =
      Z ω * Complex.exp (Complex.I * (g ω φ : ℂ)) := by
    rw [hZdef, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e, hZ1, one_mul]

/-- **Nested uniqueness, one test.** Under the hypotheses of `ae_cexp_eq_of_le`, almost surely on `S`,
`g'(φ) = g(φ)` (apply the phase identity to `φ/(n+1)` for every `n`). -/
theorem ae_apply_eq_of_le (h𝒢𝒥 : 𝒢 ≤ 𝒥) (h𝒥 : 𝒥 ≤ mΩ) (hhm : Measurable h) (hg : Measurable[𝒢] g)
    (hg' : Measurable[𝒥] g') (hc : IsCondZeroBoundaryGFF P 𝒢 U fun ω => h ω - g ω)
    (hc' : IsCondZeroBoundaryGFF P 𝒥 U' fun ω => h ω - g' ω) (hS : MeasurableSet[𝒢] S)
    (hU : ∀ᵐ ω ∂P, ω ∈ S → U' ω = U ω) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ S → g' ω φ = g ω φ := by
  set φn : ℕ → TestOn upperHalfPlaneOpens := fun n => (1 / ((n : ℝ) + 1)) • φ with hφn
  have hall := ae_all_iff.2 fun n => ae_cexp_eq_of_le h𝒢𝒥 h𝒥 hhm hg hg' hc hc' hS hU (φn n)
  filter_upwards [hall] with ω hω hωS
  refine (Aux61MeanId.eq_of_forall_cexp_div fun n => ?_)
  have e := hω n hωS
  have h1 : g' ω (φn n) = 1 / ((n : ℝ) + 1) * g' ω φ := by simp only [hφn, map_smul, smul_eq_mul]
  have h2 : g ω (φn n) = 1 / ((n : ℝ) + 1) * g ω φ := by simp only [hφn, map_smul, smul_eq_mul]
  rw [h1, h2] at e
  convert e using 4 <;> ring

/-- **Nested uniqueness, every test at once.** If moreover both parts are harmonic on a common random open set
`O ⊆ ℍ` on `S`, then almost surely on `S` they agree on every test supported in `O`. -/
theorem ae_forall_apply_eq_of_le (h𝒢𝒥 : 𝒢 ≤ 𝒥) (h𝒥 : 𝒥 ≤ mΩ) (hhm : Measurable h) (hg : Measurable[𝒢] g)
    (hg' : Measurable[𝒥] g') (hc : IsCondZeroBoundaryGFF P 𝒢 U fun ω => h ω - g ω)
    (hc' : IsCondZeroBoundaryGFF P 𝒥 U' fun ω => h ω - g' ω) (hS : MeasurableSet[𝒢] S)
    (hU : ∀ᵐ ω ∂P, ω ∈ S → U' ω = U ω) {O : Ω → Set ℂ} (hO : ∀ᵐ ω ∂P, ω ∈ S → IsOpen (O ω) ∧ O ω ⊆ H)
    (hgh : ∀ᵐ ω ∂P, ω ∈ S → IsHarmonicDistOn (g ω) (O ω))
    (hg'h : ∀ᵐ ω ∂P, ω ∈ S → IsHarmonicDistOn (g' ω) (O ω)) :
    ∀ᵐ ω ∂P, ω ∈ S → ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O ω → g' ω φ = g ω φ := by
  classical
  set O' : Ω → Set ℂ := fun ω => if ω ∈ S then O ω else ∅ with hO'def
  have hO' : ∀ᵐ ω ∂P, IsOpen (O' ω) ∧ O' ω ⊆ H := by
    filter_upwards [hO] with ω hω
    by_cases hωS : ω ∈ S
    · simp only [hO'def, hωS, ↓reduceIte]; exact hω hωS
    · simp only [hO'def, hωS, ↓reduceIte]; exact ⟨isOpen_empty, empty_subset _⟩
  have hharm : ∀ {T : Ω → DistOn upperHalfPlaneOpens}, (∀ᵐ ω ∂P, ω ∈ S → IsHarmonicDistOn (T ω) (O ω)) →
      ∀ᵐ ω ∂P, IsHarmonicDistOn (T ω) (O' ω) := fun {T} hT => by
    filter_upwards [hT] with ω hω
    by_cases hωS : ω ∈ S
    · simp only [hO'def, hωS, ↓reduceIte]; exact hω hωS
    · simp only [hO'def, hωS, ↓reduceIte]; exact Aux61MeanId.isHarmonicDistOn_empty _
  have key := LocalSets.ae_forall_apply_eq_of_bump (P := P) (O := O') hO' (hharm hg'h) (hharm hgh)
    fun z δ hδ hBδ => by
      filter_upwards [ae_apply_eq_of_le h𝒢𝒥 h𝒥 hhm hg hg' hc hc' hS hU (GFF.bumpTest z hδ hBδ)] with ω hω hsub
      by_cases hωS : ω ∈ S
      · exact hω hωS
      · simp only [hO'def, hωS, ↓reduceIte, subset_empty_iff] at hsub
        exact absurd hsub (nonempty_closedBall.2 hδ.le).ne_empty
  filter_upwards [key] with ω hω hωS φ hφ
  refine hω φ ?_
  simp only [hO'def, hωS, ↓reduceIte]
  exact hφ

end Nested

/-! ### The union mean against the flow line's own mean -/

section Flow

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Aux. lemma 61's slit-side comparison, physical form** (Astra's follow-up 4 §1.1, L113–L123).

Let `h` be a zero-boundary GFF on `ℍ`, `A` a hitting-measurable random set with a conditional Gaussian decomposition
`g` given `𝒢` (`g` is `𝒢`-measurable and harmonic off `A`, `h − g` conditionally a zero-boundary GFF on `ℍ ∖ A`).
For countably many indices `i` let `L i` be an ordinary local set with mean `g₂ i` (the flow line's own prefix at a
deterministic own time, with the flow-line mean), every component of `L i ∪ {Im ≤ 0}` unbounded, and `A' i ⊇ A, L i`
(on `ℍ`) a marked local set for marks `ℳ i` that record `A` and `L i` (the union at the later stop), with
`𝒢 ≤ germ(A) ∨ ℳ i`, and `S i ∈ 𝒢` an event on which `A' i = A`.

Then almost surely, for every `i`, on `S i`: the harmonic function `u` representing `g − g₂ i` on `ℍ ∖ A` tends to
`0` at every `z₀ ∈ L i ∪ ℝ` near which `A ⊆ L i`.

Proof: add the germs of `A` and `L i` to the marks of `A' i` (R69's lemma, twice); the decomposition of `A' i` given
`𝒥 = germ(A' i) ∨ ℳ i ∨ germ(A) ∨ germ(L i)` (Aux. 18 with history) is compared with `g₂ i` by the marked nested
Proposition 3.8 (`Aux61MeanId.ae_tendsto_sub_of_condLaw`, `ℍ ∖ (A' i ∪ L i) = ℍ ∖ A' i`), and agrees with `g` on
`S i` by nested uniqueness (`𝒢 ≤ 𝒥`). -/
theorem ae_tendsto_sub_flowMean {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    {g : Ω → DistOn upperHalfPlaneOpens} (hgm : Measurable[𝒢] g)
    (hgh : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A ω))
    (hgc : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) fun ω => h ω - g ω)
    {ι : Type*} [Countable ι] {L : ι → Ω → Set ℂ} {g₂ : ι → Ω → DistOn upperHalfPlaneOpens}
    (hLm : ∀ i, Measurable[mΩ, hittingSigma] (L i)) (hLc : ∀ i, ∀ᵐ ω ∂P, L i ω ⊆ H ∧ IsOpen (H \ L i ω))
    (hLunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (L i ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (L i ω)) z))
    (hg₂ : ∀ i, IsLocalSetMean (L i) h P (g₂ i))
    {A' : ι → Ω → Set ℂ} {ℳ : ι → MeasurableSpace Ω} (hℳ : ∀ i, ℳ i ≤ mΩ)
    (hA'm : ∀ i, Measurable[mΩ, hittingSigma] (A' i))
    (hA'c : ∀ i, ∀ᵐ ω ∂P, A' i ω ⊆ H ∧ IsOpen (H \ A' i ω))
    (hloc : ∀ i, IsHistoryAvoidanceLocal (ℳ i) (A' i) h P)
    (hAℳ : ∀ i, Measurable[ℳ i, hittingSigma] A) (hAA' : ∀ i ω, A ω ∩ H ⊆ A' i ω)
    (hLℳ : ∀ i, Measurable[ℳ i, hittingSigma] (L i)) (hLA' : ∀ i ω, L i ω ∩ H ⊆ A' i ω)
    (h𝒢ℳ : ∀ i, 𝒢 ≤ germSigma A h ⊔ ℳ i)
    {S : ι → Set Ω} (hS : ∀ i, MeasurableSet[𝒢] (S i)) (hSA : ∀ i, ∀ᵐ ω ∂P, ω ∈ S i → A' i ω = A ω) :
    ∀ᵐ ω ∂P, ∀ i, ω ∈ S i → ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ A ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ - g₂ i ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ L i ω ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A ω ∩ ball z₀ r ⊆ L i ω) →
        Tendsto u (𝓝[H \ A ω] z₀) (𝓝 0) := by
  classical
  have hhm := hh.measurable
  refine ae_all_iff.2 fun i => ?_
  -- the marks of the larger union, with the germs of `A` and `L i`
  have hloc₁ : IsHistoryAvoidanceLocal (ℳ i ⊔ germSigma A h) (A' i) h P :=
    Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh (hℳ i) (hA'm i) (hloc i) (hAℳ i) (hAA' i)
  have hℳ₁ : ℳ i ⊔ germSigma A h ≤ mΩ := sup_le (hℳ i) (germSigma_le hAm hhm)
  have hloc₂ : IsHistoryAvoidanceLocal ((ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h) (A' i) h P :=
    Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℳ₁ (hA'm i) hloc₁
      ((hLℳ i).mono le_sup_left le_rfl) (hLA' i)
  have h𝒦 : (ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h ≤ mΩ := sup_le hℳ₁ (germSigma_le (hLm i) hhm)
  obtain ⟨g', hg'm, hg'h, hg'c⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh (hA'm i) h𝒦 hloc₂ (hA'c i)
  have h𝒥 : germSigma (A' i) h ⊔ ((ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h) ≤ mΩ :=
    sup_le (germSigma_le (hA'm i) hhm) h𝒦
  have hU : ∀ ω, H \ (A' i ω ∪ L i ω) = H \ A' i ω := fun ω => by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      exact ⟨hz, fun h' => hz' (Or.inl h')⟩
    · rintro ⟨hz, hz'⟩
      exact ⟨hz, fun h' => h'.elim hz' fun hL => hz' (hLA' i ω ⟨hL, hz⟩)⟩
  have hUf : (fun ω => H \ (A' i ω ∪ L i ω)) = fun ω => H \ A' i ω := funext hU
  have hg'm𝒥 : Measurable[germSigma (A' i) h ⊔ ((ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h)] g' :=
    hg'm.mono le_sup_left le_rfl
  -- the marked nested Proposition 3.8 for `A' i ⊇ L i`
  have hT := Aux61MeanId.ae_tendsto_sub_of_condLaw hh (hA'm i) (hLm i) (hA'c i) (hLc i) (hLunb i) h𝒥
    (le_sup_right.trans le_sup_right)
    (sup_le ((comap_le_germSigma (A' i) h).trans le_sup_left)
      ((comap_le_germSigma (L i) h).trans (le_sup_right.trans le_sup_right)))
    hg'm𝒥 (by filter_upwards [hg'h] with ω hω; rw [hU]; exact hω) (by rw [hUf]; exact hg'c) (hg₂ i)
  -- nested uniqueness: `g' = g` on `S i`
  have h𝒢𝒥 : 𝒢 ≤ germSigma (A' i) h ⊔ ((ℳ i ⊔ germSigma A h) ⊔ germSigma (L i) h) :=
    (h𝒢ℳ i).trans (sup_le ((le_sup_right.trans le_sup_left).trans le_sup_right)
      ((le_sup_left.trans le_sup_left).trans le_sup_right))
  have hEq := ae_forall_apply_eq_of_le h𝒢𝒥 h𝒥 hhm hgm hg'm𝒥 hgc hg'c (hS i)
    (by filter_upwards [hSA i] with ω hω hωS; rw [hω hωS]) (O := fun ω => H \ A ω)
    (by filter_upwards [hA'c i, hSA i] with ω hω hωA hωS; rw [← hωA hωS]; exact ⟨hω.2, sdiff_subset⟩)
    (by filter_upwards [hgh] with ω hω _; exact hω)
    (by filter_upwards [hg'h, hSA i] with ω hω hωA hωS; rw [← hωA hωS]; exact hω)
  filter_upwards [hT, hEq, hSA i] with ω hTω hEqω hSAω hωS
  obtain ⟨u, hu, hrep, hlim⟩ := hTω
  have hA' : A' i ω = A ω := hSAω hωS
  rw [hU, hA'] at hu
  refine ⟨u, hu, fun φ hφ => ?_, fun z₀ hz₀ ⟨r, hr, hrA⟩ => ?_⟩
  · rw [← hEqω hωS φ hφ]
    exact hrep φ (by rw [hU, hA']; exact hφ)
  · have := hlim z₀ hz₀ ⟨r, hr, by rw [hA']; exact hrA⟩
    rwa [hU, hA'] at this

/-- **A marked local set is an ordinary local set** (Lemma 3.6 (i) ⇒ (iii) through the unmarked avoidance
criterion). So the comparison set `L` of `ae_tendsto_sub_flowMean` may also be a marked local set — e.g. the union at
the restart time, which gives Aux. lemma 61's "zero relative boundary values on the old boundary" at the glued stop
(take `L = A₀ ⊆ A' = A`, `S = univ`). -/
theorem exists_isLocalSetMean_of_isHistoryAvoidanceLocal {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {L : Ω → Set ℂ} (hLm : Measurable[mΩ, hittingSigma] L)
    (hLc : ∀ᵐ ω ∂P, L ω ⊆ H ∧ IsOpen (H \ L ω)) (hloc : IsHistoryAvoidanceLocal 𝒢 L h P) :
    ∃ g₂ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean L h P g₂ :=
  isGermConditionalLaw_iff.1 (hloc.isAvoidanceLocal.isGermConditionalLaw hh hLm hLc)

end Flow

end InteractingSLE.Sec5.Aux61SlitV
