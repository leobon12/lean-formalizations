import InteractingSLE.Spec.Coupling.WholeFieldMarked
import InteractingSLE.GFF.LocalSets.SubdomainCov

/-!
# The history-marked local-set mean is the prescribed mean (Aux. lemma 18, last paragraph)

Packet PROVE-WHOLEFIELD (ruling R36). Specification Aux. lemma 18 (`source/spec/p097-144.md#aux-18-proof`,
pp. 97–98): "Finally, fix a smooth test `φ` with support outside `K_τ`; rigorously work on the history-measurable
avoidance event for its deterministic support … Both conditional Gaussian laws have the same variance
`v = (φ, G_{ℍ∖K_τ} φ)`. The tower property for their first and second moments gives, on this event,
`E[(𝒞_{K_τ}, φ) | 𝓕_τ] = (F_τ, φ)`, `Var((𝒞_{K_τ}, φ) | 𝓕_τ) = 0`. Therefore their means agree in every such
pairing."

Here the comparison is made with characteristic functions at all real frequencies (`c (h, φ)`), which needs no
second moments of the means: the tower property against `1_G e^{−icm}` gives `E[1_G e^{−½c²v}(1 − cos(c(M − m)))] = 0`,
so `cos(c (M − m)) = 1` on `G` for every `c`, and `c = 1/(n+1)` forces `M = m`.

## Main results

* `ae_cos_eq_one_of_condCharFun_on`: the tower step, for abstract nested σ-algebras `ℋ ≤ 𝒦`;
* `ae_eq_of_forall_cos_eq_one`: `cos(x/(n+1)) = 1` for all `n` forces `x = 0`;
* `ae_condExp_germSigma_history_eq` (**the marked kernel (PK1)**): if `A` satisfies the history-marked avoidance
  criterion for the marks `ℋ`, and conditionally on `ℋ` the field `(h, φ)` is Gaussian with an `ℋ`-measurable mean
  `m` and variance `σ²_{ℍ∖A}(φ)` on an event `G ∈ ℋ`, then on `G` the same Gaussian law holds conditionally on the
  germ σ-algebra of `A` together with `ℋ`: `E[e^{i(h,φ)} | 𝒜 ∨ ℋ] = e^{im} e^{−σ²/2}` and
  `E[(h, φ) | 𝒜 ∨ ℋ] = m`.

For the optional hull coupling, `ℋ` is the stopped driving history `𝓕_τ`, `A = K_τ`, `G = {supp φ ∩ K_τ = ∅}` and
`m = (𝔥_τ, φ)`: this is (PK1) of Aux. lemma 48 and (GB2) of Aux. lemma 47.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB

/-! ### The tower step -/

section Tower

variable {Ω : Type*} {ℋ 𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Comparison of two conditional characteristic functions on an event.** Let `ℋ ≤ 𝒦` and `G ∈ ℋ`. If
`E[e^{icX} | 𝒦] = e^{icM} e^{−s/2}` (`M` `𝒦`-measurable) and, on `G`, `E[e^{icX} | ℋ] = e^{icm} e^{−s/2}`
(`m` `ℋ`-measurable), then `cos(c (M − m)) = 1` almost surely on `G`. -/
theorem ae_cos_eq_one_of_condCharFun_on (hℋ𝒦 : ℋ ≤ 𝒦) (h𝒦 : 𝒦 ≤ mΩ) {X M m s : Ω → ℝ}
    (hX : Measurable X) (hm : Measurable[ℋ] m) {G : Set Ω}
    (hG : MeasurableSet[ℋ] G) (c : ℝ)
    (h𝒦c : P[fun ω => Complex.exp (Complex.I * ((c * X ω : ℝ) : ℂ)) | 𝒦] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * ((c * M ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * s ω) : ℝ) : ℂ))
    (hℋc : ∀ᵐ ω ∂P, ω ∈ G →
      (P[fun ω => Complex.exp (Complex.I * ((c * X ω : ℝ) : ℂ)) | ℋ]) ω =
        Complex.exp (Complex.I * ((c * m ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * s ω) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, ω ∈ G → Real.cos (c * (M ω - m ω)) = 1 := by
  set F : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((c * X ω : ℝ) : ℂ)) with hFdef
  have hFm : Measurable F := GFF.measurable_exp_I_mul (measurable_const.mul hX)
  have hFi : Integrable F P := by
    refine Integrable.of_bound (C := 1) hFm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    exact (Complex.norm_exp_I_mul_ofReal _).le
  set W₁ : Ω → ℂ := G.indicator fun ω => Complex.exp (Complex.I * ((-(c * m ω) : ℝ) : ℂ))
    with hW₁def
  have hW₁ℋ : StronglyMeasurable[ℋ] W₁ :=
    (@GFF.measurable_exp_I_mul Ω ℋ _ (measurable_const.mul hm).neg).stronglyMeasurable.indicator hG
  have hW₁b : ∀ ω, ‖W₁ ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hW₁def, indicator_of_mem hω]
      exact (Complex.norm_exp_I_mul_ofReal _).le
    · simp [hW₁def, hω]
  have e1 := integral_mul_condExp_of_bdd (P := P) (hℋ𝒦.trans h𝒦) hW₁ℋ hW₁b hFi
  have e2 := integral_mul_condExp_of_bdd (P := P) h𝒦 (hW₁ℋ.mono hℋ𝒦) hW₁b hFi
  have hint : ∀ {n : MeasurableSpace Ω}, Integrable (fun ω => W₁ ω * (P[F | n]) ω) P := fun {n} =>
    integrable_condExp.bdd_mul ((hW₁ℋ.mono (hℋ𝒦.trans h𝒦)).aestronglyMeasurable)
      (Eventually.of_forall hW₁b)
  set r : Ω → ℂ := fun ω => ((Real.exp (-(1 / 2) * s ω) : ℝ) : ℂ) with hrdef
  set a : Ω → ℂ := G.indicator r with hadef
  set b : Ω → ℂ := G.indicator fun ω => Complex.exp (Complex.I * ((c * (M ω - m ω) : ℝ) : ℂ)) * r ω
    with hbdef
  have ha : (fun ω => W₁ ω * (P[F | ℋ]) ω) =ᵐ[P] a := by
    filter_upwards [hℋc] with ω hω
    by_cases hωG : ω ∈ G
    · simp only [hW₁def, hadef, indicator_of_mem hωG, hω hωG, hrdef, ← mul_assoc, ← Complex.exp_add]
      rw [← mul_add, ← Complex.ofReal_add, neg_add_cancel, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, one_mul]
    · simp [hW₁def, hadef, hωG]
  have hb : (fun ω => W₁ ω * (P[F | 𝒦]) ω) =ᵐ[P] b := by
    filter_upwards [h𝒦c] with ω hω
    by_cases hωG : ω ∈ G
    · simp only [hW₁def, hbdef, indicator_of_mem hωG, hω, hrdef, ← mul_assoc, ← Complex.exp_add]
      congr 3
      push_cast; ring
    · simp [hW₁def, hbdef, hωG]
  have hai : Integrable a P := hint.congr ha
  have hbi : Integrable b P := hint.congr hb
  have hab : ∫ ω, (a ω - b ω) ∂P = 0 := by
    rw [integral_sub hai hbi, ← integral_congr_ae ha, ← integral_congr_ae hb, ← e1, ← e2, sub_self]
  set d : Ω → ℝ := G.indicator fun ω => Real.exp (-(1 / 2) * s ω) * (1 - Real.cos (c * (M ω - m ω)))
    with hddef
  have hre : ∀ ω, (a ω - b ω).re = d ω := fun ω => by
    by_cases hωG : ω ∈ G
    · simp only [hadef, hbdef, hddef, indicator_of_mem hωG, hrdef, Complex.sub_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
      ring
    · simp [hadef, hbdef, hddef, hωG]
  have hd0 : 0 ≤ᵐ[P] d := Eventually.of_forall fun ω => by
    by_cases hωG : ω ∈ G
    · simp only [hddef, indicator_of_mem hωG, Pi.zero_apply]
      exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 (Real.cos_le_one _))
    · simp [hddef, hωG]
  have hdi : Integrable d P := by
    have := (hai.sub hbi).re
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    exact hre ω
  have hdint : ∫ ω, d ω ∂P = 0 := by
    have hre' : ∫ ω, d ω ∂P = ∫ ω, RCLike.re ((a - b) ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (hre ω).symm)
    rw [hre', integral_re (hai.sub hbi)]
    simp only [Pi.sub_apply]
    rw [hab]
    simp
  have hdz := (integral_eq_zero_iff_of_nonneg_ae hd0 hdi).1 hdint
  filter_upwards [hdz] with ω hω hωG
  simp only [hddef, indicator_of_mem hωG, Pi.zero_apply, mul_eq_zero] at hω
  rcases hω with h | h
  · exact absurd h (Real.exp_pos _).ne'
  · linarith

/-- If `cos(x/(n+1)) = 1` for every `n`, then `x = 0`. -/
theorem eq_zero_of_forall_cos_eq_one {x : ℝ} (hx : ∀ n : ℕ, Real.cos ((1 / ((n : ℝ) + 1)) * x) = 1) :
    x = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|x| / (2 * Real.pi))
  have hpi := Real.pi_pos
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : |(1 / ((n : ℝ) + 1)) * x| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity), one_div, inv_mul_lt_iff₀ hn1]
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 hn
    nlinarith
  have h0 := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [neg_abs_le ((1 / ((n : ℝ) + 1)) * x)])
    (lt_of_le_of_lt (le_abs_self _) hlt)).1 (hx n)
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h (by positivity)
  · exact h

end Tower

/-! ### The marked kernel -/

section Kernel

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The history-marked kernel** (Aux. lemma 18, last paragraph; (PK1) of Aux. lemma 48, (GB2) of Aux. lemma 47).
Let `A` satisfy the history-marked avoidance criterion for the marks `ℋ` (a zero-boundary GFF `h`). Suppose that
on an event `G ∈ ℋ`, conditionally on `ℋ`, `(h, φ)` is Gaussian with an `ℋ`-measurable mean `m` and variance
`σ²_{ℍ∖A}(φ)` (at every frequency `c`). Then on `G` the same holds conditionally on the germ σ-algebra of `A`
together with `ℋ`: `E[(h, φ) | 𝒜 ∨ ℋ] = m` and `E[e^{i(h,φ)} | 𝒜 ∨ ℋ] = e^{im} e^{−σ²_{ℍ∖A}(φ)/2}`. -/
theorem ae_condExp_germSigma_history_eq (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsHistoryAvoidanceLocal ℋ A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (φ : TestOn upperHalfPlaneOpens) {G : Set Ω}
    (hG : MeasurableSet[ℋ] G) {m : Ω → ℝ} (hm : Measurable[ℋ] m)
    (hkern : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      (P[fun ω' => Complex.exp (Complex.I * ((c * h ω' φ : ℝ) : ℂ)) | ℋ]) ω =
        Complex.exp (Complex.I * ((c * m ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ)) :
    (∀ᵐ ω ∂P, ω ∈ G → (P[fun ω' => h ω' φ | germSigma A h ⊔ ℋ]) ω = m ω) ∧
      ∀ᵐ ω ∂P, ω ∈ G → (P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | germSigma A h ⊔ ℋ]) ω =
        Complex.exp (Complex.I * (m ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ) := by
  have hhm := hh.measurable
  have hℋ𝒦 : ℋ ≤ germSigma A h ⊔ ℋ := le_sup_right
  have h𝒦 : germSigma A h ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hA hhm) hℋ
  have hXm : Measurable fun ω => h ω φ := (measurable_distOn_apply φ).comp hhm
  have hrel : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      zeroGFFTestCov (H \ relClosureH (A ω)) ψ ψ = zeroGFFTestCov (H \ A ω) ψ ψ := fun ψ => by
    filter_upwards [hAc] with ω ⟨hs, ho⟩
    rw [relClosureH_eq hs ho]
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_germSigma_history hh hA hℋ hloc hAc φ
  -- the germ-side kernel at every frequency
  have hfreq : ∀ c : ℝ,
      P[fun ω => Complex.exp (Complex.I * ((c * h ω φ : ℝ) : ℂ)) | germSigma A h ⊔ ℋ] =ᵐ[P]
        fun ω => Complex.exp (Complex.I * ((c * M ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c
    obtain ⟨Mc, -, hMc1, hMc2⟩ := exists_condExp_germSigma_history hh hA hℋ hloc hAc (c • φ)
    have hlin : (fun ω => h ω (c • φ)) = c • fun ω => h ω φ := by
      funext ω; rw [map_smul, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    have hMc : Mc =ᵐ[P] fun ω => c * M ω := by
      have h1 := condExp_smul (μ := P) (m := germSigma A h ⊔ ℋ) c (fun ω => h ω φ)
      rw [← hlin] at h1
      filter_upwards [hMc1, h1, hM1] with ω e1 e2 e3
      rw [e1, e2, Pi.smul_apply, smul_eq_mul, ← e3]
    have hexp : (fun ω => Complex.exp (Complex.I * ((c * h ω φ : ℝ) : ℂ))) =
        fun ω => Complex.exp (Complex.I * (h ω (c • φ) : ℂ)) := by
      funext ω; rw [map_smul, smul_eq_mul]
    rw [hexp]
    filter_upwards [hMc2, hMc, hrel φ, hrel (c • φ), hAc] with ω e1 e2 e3 e4 ⟨_, ho⟩
    rw [← e1, e2, e4, zeroGFFTestCov_smul_self ho sdiff_subset]
  -- the tower step at the frequencies `1/(n+1)`
  have hcos : ∀ n : ℕ, ∀ᵐ ω ∂P, ω ∈ G → Real.cos ((1 / ((n : ℝ) + 1)) * (M ω - m ω)) = 1 :=
    fun n => ae_cos_eq_one_of_condCharFun_on hℋ𝒦 h𝒦 hXm hm hG _ (hfreq _) (hkern _)
  have hMm : ∀ᵐ ω ∂P, ω ∈ G → M ω = m ω := by
    filter_upwards [ae_all_iff.2 hcos] with ω hω hωG
    exact sub_eq_zero.1 (eq_zero_of_forall_cos_eq_one fun n => hω n hωG)
  refine ⟨?_, ?_⟩
  · filter_upwards [hM1, hMm] with ω e1 e2 hωG
    rw [← e1, e2 hωG]
  · have h1 := hfreq 1
    simp only [one_mul, one_pow] at h1
    filter_upwards [h1, hMm] with ω e1 e2 hωG
    rw [e1, e2 hωG]

end Kernel

end WholeField

end InteractingSLE
