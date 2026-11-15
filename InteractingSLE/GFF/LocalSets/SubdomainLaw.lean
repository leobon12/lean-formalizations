import InteractingSLE.GFF.LocalSets.SubdomainCov
import InteractingSLE.GFF.LocalSets.UnionLaw
import InteractingSLE.GFF.LocalSets.PointVariance

/-!
# Comparing conditional Gaussian laws of the field given nested σ-algebras

Infrastructure for Propositions 3.8–3.9 (specification §3.2, pp. 58–59, transcription
`source/spec/p049-096.md#prop-3.8`, `#prop-3.9`), packet PROVE-LS-C.

The proofs of Propositions 3.8 and 3.9 condition the field on two nested σ-algebras
`𝒢 ⊆ 𝒦` (e.g. `𝒢 = 𝒜₁`, the germ σ-algebra of `A₁`, and `𝒦 = 𝒥 = σ(A₁, A₂, 𝒜, 𝒜₁, 𝒜₂)`), under each of
which the field is a harmonic mean plus a zero-boundary GFF on a random domain. Instead of the
specification's conditional domains ("Condition on `𝒜₁` and subtract `𝒞_{A₁}` … in this conditional
law, `A₂ ∖ A₁` is a local set of the remaining zero-boundary GFF on `D ∖ A₁`", p. 59) the two
conditional laws are compared directly on `ℍ` (ruling R34 lets internal lemmas choose the form):

* `ae_cos_eq_one_of_condCharFun` : if `E[e^{i(X − M)} | 𝒢] = e^{−s/2}`,
  `E[e^{i(X − M')} | 𝒦] = e^{−s'/2}`, `M` is `𝒢`-measurable, `M'` is `𝒦`-measurable and `s = s'` on
  `G ∈ 𝒢`, then `cos(M' − M) = 1` almost surely on `G` (tower property against `1_G` and
  `1_G e^{i(M' − M)}`);
* `ae_apply_eq_of_isCondZeroBoundaryGFF` : applied to `φ/(n+1)`, the two means agree on `G` in the
  pairing with `φ` whenever the two conditional variances of the multiples of `φ` agree there;
* `IsLocalSetMean` : the local-set mean `𝒞_A` of Lemma 3.6 (iii) as a predicate on random
  distributions (`IsGermConditionalLaw A h P ↔ ∃ g, IsLocalSetMean A h P g`), and its uniqueness
  `IsLocalSetMean.ae_apply_eq`;
* `ae_forall_apply_eq_of_bump` : two random distributions, almost surely harmonic on a random open
  set `O`, that agree in the pairings with the countably many bumps inside `O` agree on `O`
  simultaneously for all test functions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 LQGMetric

/-! ### The tower argument -/

section Tower

variable {Ω : Type*} {𝒢 𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma integrable_ofReal_exp_of_condExp {m : MeasurableSpace Ω} {F : Ω → ℂ} {s : Ω → ℝ}
    (hc : P[F | m] =ᵐ[P] fun ω => ((Real.exp (-(1 / 2) * s ω) : ℝ) : ℂ)) :
    Integrable (fun ω => ((Real.exp (-(1 / 2) * s ω) : ℝ) : ℂ)) P :=
  integrable_condExp.congr hc

/-- **Tower property for two conditional Gaussian laws.** Under `𝒢 ⊆ 𝒦`, if
`E[e^{i(X − M)} | 𝒢] = e^{−s/2}` and `E[e^{i(X − M')} | 𝒦] = e^{−s'/2}` with `M` `𝒢`-measurable and
`M'` `𝒦`-measurable, and `s = s'` almost surely on `G ∈ 𝒢`, then `cos(M' − M) = 1` almost surely on
`G`. -/
theorem ae_cos_eq_one_of_condCharFun (h𝒢𝒦 : 𝒢 ≤ 𝒦) (h𝒦 : 𝒦 ≤ mΩ) {X M M' : Ω → ℝ}
    (hX : Measurable X) (hM : Measurable[𝒢] M) (hM' : Measurable[𝒦] M') {s s' : Ω → ℝ}
    (hc : P[fun ω => Complex.exp (Complex.I * ((X ω - M ω : ℝ) : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * s ω) : ℝ) : ℂ))
    (hc' : P[fun ω => Complex.exp (Complex.I * ((X ω - M' ω : ℝ) : ℂ)) | 𝒦] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * s' ω) : ℝ) : ℂ))
    {G : Set Ω} (hG : MeasurableSet[𝒢] G) (hss' : ∀ᵐ ω ∂P, ω ∈ G → s ω = s' ω) :
    ∀ᵐ ω ∂P, ω ∈ G → Real.cos (M' ω - M ω) = 1 := by
  have h𝒢 : 𝒢 ≤ mΩ := h𝒢𝒦.trans h𝒦
  have hMm : Measurable M := hM.mono h𝒢 le_rfl
  have hM'm : Measurable M' := hM'.mono h𝒦 le_rfl
  set E : Ω → ℂ := fun ω => ((Real.exp (-(1 / 2) * s ω) : ℝ) : ℂ) with hE
  have hEi : Integrable E P := integrable_ofReal_exp_of_condExp hc
  set I₁ : Ω → ℂ := G.indicator fun _ => (1 : ℂ) with hI₁
  set I₂ : Ω → ℂ := fun ω => I₁ ω * Complex.exp (Complex.I * ((M' ω - M ω : ℝ) : ℂ)) with hI₂
  have hI₁m : StronglyMeasurable[𝒢] I₁ :=
    (stronglyMeasurable_const.indicator hG)
  have hI₂m : StronglyMeasurable[𝒦] I₂ :=
    ((hI₁m.mono h𝒢𝒦).mul (@GFF.measurable_exp_I_mul Ω 𝒦 _
      (hM'.sub (hM.mono h𝒢𝒦 le_rfl))).stronglyMeasurable)
  have hI₁b : ∀ ω, ‖I₁ ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ G <;> simp [hI₁, hω]
  have hI₂b : ∀ ω, ‖I₂ ω‖ ≤ 1 := fun ω => by
    rw [hI₂, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]; exact hI₁b ω
  have hF₁ : Integrable (fun ω => Complex.exp (Complex.I * ((X ω - M ω : ℝ) : ℂ))) P :=
    GFF.integrable_exp_I_mul (hX.sub hMm)
  have hF₂ : Integrable (fun ω => Complex.exp (Complex.I * ((X ω - M' ω : ℝ) : ℂ))) P :=
    GFF.integrable_exp_I_mul (hX.sub hM'm)
  -- (a) the `𝒢`-law against `1_G`
  have ha := integral_mul_condExp_of_bdd h𝒢 hI₁m hI₁b hF₁
  -- (b) the `𝒦`-law against `1_G e^{i(M' − M)}`
  have hb := integral_mul_condExp_of_bdd h𝒦 hI₂m hI₂b hF₂
  have e12 : (fun ω => I₁ ω * Complex.exp (Complex.I * ((X ω - M ω : ℝ) : ℂ))) =
      fun ω => I₂ ω * Complex.exp (Complex.I * ((X ω - M' ω : ℝ) : ℂ)) := by
    funext ω
    simp only [hI₂, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e12, hb] at ha
  have h1 : ∫ ω, I₂ ω * P[fun ω => Complex.exp (Complex.I * ((X ω - M' ω : ℝ) : ℂ)) | 𝒦] ω ∂P =
      ∫ ω, I₂ ω * ((Real.exp (-(1 / 2) * s' ω) : ℝ) : ℂ) ∂P :=
    integral_congr_ae (by filter_upwards [hc'] with ω hω; rw [hω])
  have h2 : ∫ ω, I₁ ω * P[fun ω => Complex.exp (Complex.I * ((X ω - M ω : ℝ) : ℂ)) | 𝒢] ω ∂P =
      ∫ ω, I₁ ω * E ω ∂P :=
    integral_congr_ae (by filter_upwards [hc] with ω hω; rw [hω])
  have ha'' : ∫ ω, I₂ ω * E ω ∂P = ∫ ω, I₂ ω * ((Real.exp (-(1 / 2) * s' ω) : ℝ) : ℂ) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hss'] with ω hω
    by_cases hωG : ω ∈ G
    · rw [hE]; simp only; rw [hω hωG]
    · simp [hI₂, hI₁, hωG]
  have ha' : ∫ ω, I₂ ω * E ω ∂P = ∫ ω, I₁ ω * E ω ∂P := by
    rw [ha'', ← h1, ha, h2]
  -- the real part of `∫ 1_G e^{−s/2} (1 − e^{i(M' − M)})` vanishes
  set D : Ω → ℝ := fun ω => G.indicator (fun ω => Real.exp (-(1 / 2) * s ω) *
    (1 - Real.cos (M' ω - M ω))) ω with hD
  have hEr : Integrable (fun ω => Real.exp (-(1 / 2) * s ω)) P := by
    refine hEi.re.congr (Eventually.of_forall fun ω => ?_)
    show RCLike.re (E ω) = _
    rw [hE, RCLike.re_to_complex, Complex.ofReal_re]
  have hDi : Integrable D P := by
    refine (Integrable.indicator ?_ (h𝒢 _ hG))
    refine Integrable.mono' (hEr.const_mul 2) ?_ (Eventually.of_forall fun ω => ?_)
    · exact (hEr.aestronglyMeasurable.mul
        (((hM'm.sub hMm).cos).const_sub 1).aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 : |1 - Real.cos (M' ω - M ω)| ≤ 2 := by
        rw [abs_le]; constructor <;> nlinarith [Real.cos_le_one (M' ω - M ω),
          Real.neg_one_le_cos (M' ω - M ω)]
      nlinarith [Real.exp_pos (-(1 / 2) * s ω)]
  have hD0 : ∀ ω, 0 ≤ D ω := fun ω => by
    simp only [hD]
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω]
      exact mul_nonneg (Real.exp_pos _).le (by linarith [Real.cos_le_one (M' ω - M ω)])
    · rw [indicator_of_notMem hω]
  have hint : ∫ ω, D ω ∂P = 0 := by
    have hre : ∀ ω, D ω = ((I₁ ω * E ω) - (I₂ ω * E ω)).re := fun ω => by
      simp only [hD, hI₂, hI₁, hE]
      by_cases hω : ω ∈ G
      · rw [indicator_of_mem hω, indicator_of_mem hω, mul_comm Complex.I]
        simp only [one_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
        ring
      · rw [indicator_of_notMem hω, indicator_of_notMem hω]; simp
    have hI₁E : Integrable (fun ω => I₁ ω * E ω) P :=
      hEi.bdd_mul (hI₁m.mono h𝒢).aestronglyMeasurable (Eventually.of_forall hI₁b)
    have hI₂E : Integrable (fun ω => I₂ ω * E ω) P :=
      hEi.bdd_mul (hI₂m.mono h𝒦).aestronglyMeasurable (Eventually.of_forall hI₂b)
    have hre' := integral_re (𝕜 := ℂ) (f := fun ω => I₁ ω * E ω - I₂ ω * E ω) (hI₁E.sub hI₂E)
    simp only [RCLike.re_to_complex] at hre'
    rw [integral_congr_ae (Eventually.of_forall hre), hre', integral_sub hI₁E hI₂E, ha',
      sub_self, Complex.zero_re]
  have hae := (integral_eq_zero_iff_of_nonneg hD0 hDi).1 hint
  filter_upwards [hae] with ω hω hωG
  have : Real.exp (-(1 / 2) * s ω) * (1 - Real.cos (M' ω - M ω)) = 0 := by
    have := hω
    simp only [hD, Pi.zero_apply, indicator_of_mem hωG] at this
    exact this
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (Real.exp_pos _).ne'
  · linarith

/-- If `cos(d/(n+1)) = 1` for every `n`, then `d = 0`. -/
lemma eq_zero_of_forall_cos_eq_one {d : ℝ} (h : ∀ n : ℕ, Real.cos (((n : ℝ) + 1)⁻¹ * d) = 1) :
    d = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|d| / (2 * Real.pi))
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).1 (h n)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpi := Real.pi_pos
  have hlt : |((n : ℝ) + 1)⁻¹ * d| < 2 * Real.pi := by
    rw [abs_mul, abs_inv, abs_of_pos hn1, inv_mul_lt_iff₀ hn1]
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  rw [← hk, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hlt
  have hk0 : k = 0 := by
    have : |(k : ℝ)| < 1 := by nlinarith
    rw [← Int.cast_abs] at this
    have : |k| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.1 this
  rw [hk0, Int.cast_zero, zero_mul, eq_comm, mul_eq_zero] at hk
  rcases hk with h | h
  · exact absurd h (inv_ne_zero hn1.ne')
  · exact h

/-- **Agreement of two conditional means.** Under `𝒢 ⊆ 𝒦`, let the field be `M + GFF_U` given `𝒢`
and `M' + GFF_{U'}` given `𝒦` (`M` `𝒢`-measurable, `M'` `𝒦`-measurable). If the two conditional
variances of every multiple of `φ` agree almost surely on `G ∈ 𝒢`, then `M φ = M' φ` almost surely on
`G`. -/
theorem ae_apply_eq_of_isCondZeroBoundaryGFF (h𝒢𝒦 : 𝒢 ≤ 𝒦) (h𝒦 : 𝒦 ≤ mΩ)
    {h M M' : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hM : Measurable[𝒢] M)
    (hM' : Measurable[𝒦] M') {U U' : Ω → Set ℂ}
    (hc : IsCondZeroBoundaryGFF P 𝒢 U fun ω => h ω - M ω)
    (hc' : IsCondZeroBoundaryGFF P 𝒦 U' fun ω => h ω - M' ω)
    (φ : TestOn upperHalfPlaneOpens) {G : Set Ω} (hG : MeasurableSet[𝒢] G)
    (hUU' : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      zeroGFFTestCov (U ω) ⇑(c • φ) ⇑(c • φ) = zeroGFFTestCov (U' ω) ⇑(c • φ) ⇑(c • φ)) :
    ∀ᵐ ω ∂P, ω ∈ G → M ω φ = M' ω φ := by
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, ω ∈ G →
      Real.cos (((n : ℝ) + 1)⁻¹ * (M' ω φ - M ω φ)) = 1 := by
    intro n
    set c : ℝ := ((n : ℝ) + 1)⁻¹
    have hX : Measurable fun ω => h ω (c • φ) := (measurable_distOn_apply _).comp hh
    have hMm : Measurable[𝒢] fun ω => M ω (c • φ) :=
      @Measurable.comp _ _ _ 𝒢 _ _ _ _ (measurable_distOn_apply (c • φ)) hM
    have hM'm : Measurable[𝒦] fun ω => M' ω (c • φ) :=
      @Measurable.comp _ _ _ 𝒦 _ _ _ _ (measurable_distOn_apply (c • φ)) hM'
    have h1 := ae_cos_eq_one_of_condCharFun (P := P) h𝒢𝒦 h𝒦 hX hMm hM'm (hc (c • φ))
      (hc' (c • φ)) hG (hUU' c)
    filter_upwards [h1] with ω hω hωG
    have := hω hωG
    rwa [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub] at this
  filter_upwards [ae_all_iff.2 hn] with ω hω hωG
  have := eq_zero_of_forall_cos_eq_one fun n => hω n hωG
  linarith

end Tower

/-! ### The local-set mean -/

section Mean

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `g` is a version of the local-set mean `𝒞_A` of Lemma 3.6 (iii): `g` is `𝒜`-measurable, almost
surely harmonic on `ℍ ∖ A`, and given the germ σ-algebra `𝒜` the field `h − g` is a zero-boundary
GFF on `ℍ ∖ A`. -/
def IsLocalSetMean (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω)
    (g : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  Measurable[germSigma A h] g ∧ (∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A ω)) ∧
    IsCondZeroBoundaryGFF P (germSigma A h) (fun ω => H \ A ω) (fun ω => h ω - g ω)

omit [IsProbabilityMeasure P] in
theorem isGermConditionalLaw_iff {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens} :
    IsGermConditionalLaw A h P ↔ ∃ g, IsLocalSetMean A h P g := Iff.rfl

/-- **Uniqueness of the local-set mean**: two versions agree almost surely in every pairing. -/
theorem IsLocalSetMean.ae_apply_eq {A : Ω → Set ℂ} {h g g' : Ω → DistOn upperHalfPlaneOpens}
    (hA : Measurable[mΩ, hittingSigma] A) (hhm : Measurable h) (hg : IsLocalSetMean A h P g)
    (hg' : IsLocalSetMean A h P g') (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, g ω φ = g' ω φ := by
  have := ae_apply_eq_of_isCondZeroBoundaryGFF (P := P) le_rfl (germSigma_le hA hhm) hhm hg.1
    hg'.1 hg.2.2 hg'.2.2 φ MeasurableSet.univ (fun c => Eventually.of_forall fun _ _ => rfl)
  filter_upwards [this] with ω hω using hω (mem_univ ω)

/-- **Existence of the local-set mean** (Lemma 3.6, (iv) ⇒ (iii)): a local set of a zero-boundary
GFF on `ℍ` has a version of `𝒞_A`. -/
theorem IsLocalSet.exists_isLocalSetMean {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hA : Measurable[_, hittingSigma] A)
    (hl : IsLocalSet A h P) : ∃ g, IsLocalSetMean A h P g :=
  ((isLocalSet_tfae hh hA hl.2.1).out 4 3).1 hl

end Mean

/-! ### From countably many bumps to all test functions -/

section Bump

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Two random distributions, almost surely harmonic on the random open set `O ⊆ ℍ`, that agree
almost surely in the pairing with each bump whose closed ball lies in `O`, agree almost surely on
`O` simultaneously for all test functions. -/
theorem ae_forall_apply_eq_of_bump {T₁ T₂ : Ω → DistOn upperHalfPlaneOpens} {O : Ω → Set ℂ}
    (hO : ∀ᵐ ω ∂P, IsOpen (O ω) ∧ O ω ⊆ H) (h₁ : ∀ᵐ ω ∂P, IsHarmonicDistOn (T₁ ω) (O ω))
    (h₂ : ∀ᵐ ω ∂P, IsHarmonicDistOn (T₂ ω) (O ω))
    (hb : ∀ (x : ℂ) (δ : ℝ) (hδ : 0 < δ) (hB : closedBall x δ ⊆ (upperHalfPlaneOpens : Set ℂ)),
      ∀ᵐ ω ∂P, closedBall x δ ⊆ O ω →
        T₁ ω (GFF.bumpTest x hδ hB) = T₂ ω (GFF.bumpTest x hδ hB)) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O ω → T₁ ω φ = T₂ ω φ := by
  set x : ℕ → ℂ := TopologicalSpace.denseSeq ℂ
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hpair : ∀ p : ℕ × ℕ, ∀ᵐ ω ∂P,
      ∀ hB : closedBall (x p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ (upperHalfPlaneOpens : Set ℂ),
      closedBall (x p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ O ω →
        T₁ ω (GFF.bumpTest (x p.1) (hδ p.2) hB) = T₂ ω (GFF.bumpTest (x p.1) (hδ p.2) hB) := by
    intro p
    by_cases hB : closedBall (x p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ (upperHalfPlaneOpens : Set ℂ)
    · filter_upwards [hb (x p.1) _ (hδ p.2) hB] with ω hω hB' hsub
      exact hω hsub
    · exact Eventually.of_forall fun ω hB' => absurd hB' hB
  filter_upwards [ae_all_iff.2 hpair, hO, h₁, h₂] with ω hω ⟨hOo, hOH⟩ ⟨v₁, hv₁, hT₁⟩ ⟨v₂, hv₂, hT₂⟩
  -- the two harmonic representatives agree on `O ω`
  have hval : ∀ (k n : ℕ), closedBall (x k) (1 / ((n : ℝ) + 1)) ⊆ O ω →
      closedBall (x k) (1 / ((n : ℝ) + 1)) ⊆ (upperHalfPlaneOpens : Set ℂ) → v₁ (x k) = v₂ (x k) := by
    intro k n hsub hB
    have e := hω (k, n) hB hsub
    have hts : tsupport (GFF.bumpTest (x k) (hδ n) hB) ⊆ O ω :=
      (GFF.tsupport_bumpFun_subset (hδ n)).trans hsub
    rw [hT₁ _ hts, hT₂ _ hts, GFF.coe_bumpTest,
      GFF.integral_mul_bumpFun_of_harmonic hOo hv₁ (hδ n) hsub,
      GFF.integral_mul_bumpFun_of_harmonic hOo hv₂ (hδ n) hsub] at e
    have : 0 < (1 / ((n : ℝ) + 1)) ^ 2 * GFF.bumpMass := by
      have := GFF.bumpMass_pos; have := hδ n; positivity
    exact mul_right_cancel₀ this.ne' e
  have heq : ∀ z ∈ O ω, v₁ z = v₂ z := by
    intro z hz
    by_contra hne
    have hd : 0 < |v₁ z - v₂ z| := abs_pos.2 (sub_ne_zero.2 hne)
    have hc : ContinuousAt (fun w => v₁ w - v₂ w) z :=
      (hv₁ z hz).1.continuousAt.sub (hv₂ z hz).1.continuousAt
    obtain ⟨η, hη, hηc⟩ := Metric.continuousAt_iff.1 hc _ hd
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hOo z hz
    set r := min η ρ with hr
    have hr0 : 0 < r := lt_min hη hρ
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z (r / 2)
      (half_pos hr0)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hr0)
    have hsub : closedBall (x k) (1 / ((n : ℝ) + 1)) ⊆ O ω := by
      intro w hw
      refine hρO ?_
      rw [mem_ball]
      have h1 := dist_triangle w (x k) z
      rw [mem_closedBall] at hw
      have h2 : dist (x k) z < r / 2 := by rw [dist_comm]; exact hk
      have h3 : r ≤ ρ := min_le_right _ _
      linarith
    have hk' := hval k n hsub (hsub.trans hOH)
    have hdk : dist (x k) z < η := by
      have h2 : dist (x k) z < r / 2 := by rw [dist_comm]; exact hk
      have h3 : r ≤ η := min_le_left _ _
      linarith
    have := hηc hdk
    rw [hk', sub_self, Real.dist_eq, zero_sub, abs_neg] at this
    exact lt_irrefl _ this
  intro φ hφ
  rw [hT₁ φ hφ, hT₂ φ hφ]
  congr 1
  funext z
  by_cases hz : z ∈ O ω
  · rw [heq z hz]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφ h)), mul_zero, mul_zero]

end Bump

end LocalSets
end InteractingSLE
