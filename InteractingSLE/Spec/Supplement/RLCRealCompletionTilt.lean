/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA3Gauss
import InteractingSLE.Spec.Sec7.LocalExtDCov
import InteractingSLE.Spec.Coupling.WholeField8Local

/-!
# The conditional Cameron–Martin tilt with a source in retained pockets (toward Corollary G7a)

Packet PROVE-G3RESTART. Source: Corollary G7a's proof (supplement p. 499: "The Cameron–Martin projection formula applies
componentwise with every born pocket retained"); Aux. lemma 97's proof (p. 327: "the full weighting changes the
reference conditional mean to `M_A^ref + P_{ℍ∖A} f`, with all pockets retained").

In the interval route of Lemma G3 (PROVE-L1-CMI, `Restart.FlowStopIdentCMI.ae_condExp_shift_eq_ref`) the source `s` of
the Cameron–Martin density `k e^{−Λ}`, `Λ = lim h(s_k)`, lies off the hull at every stop, so the frozen off-hull kernel
gives the joint conditional law of `(h(φ), h(s_k))`, and the tilt (`LocalExt.ae_condExp_tilt_of_joint`, then the limit
`k → ∞`) needs the convergence of the conditional means `E[h(s_k) | 𝓕_τ]`, obtained there from explicit bounds of the
coupling mean. Past a real contact outside the seed collar the curve swallows a pocket containing part of `s`: the
joint law then comes from the retained-range kernel (`WholeField.HasRetainedRangeKernel`, proved for `0 < κ < 4` with a
trace: `WholeField.retainedRangeKernelTraceStatement`), whose mean `M` is only known to be harmonic off the range, so
the in-pocket means are not controlled near the real line.

**The point of this file: they are not needed.** At each level `k` the Gaussian tilt splits as
`E[e^{−Y_k} e^{iX} | m] = E[e^{−Y_k} | m] · exp(i(μ₁ − s₁₂ᵏ) − s₁₁/2)` (the mean `μ₂ᵏ` of `Y_k` cancels), and the limit
`k → ∞` only needs `L¹` convergence of the densities `e^{−Y_k} → e^{−Λ}` (Vitali, from `Y_k → Λ` almost surely and a
uniform Gaussian exponential moment) and convergence of the cross covariances `s₁₂ᵏ`.

* `ae_condExp_mul_eq_of_joint`: the level-`k` split;
* **`ae_condExp_tilt_of_joint_limit`**: the split in the limit, with conditional expectations converging along a
  subsequence (`L¹` contraction of `condExp`, convergence in measure);
* `rangeKerCF_eq_cfVal`, `zeroGFFTestCov_combo`, **`ae_condExp_joint_of_rangeKer`**: the retained-range kernel
  (`WholeField.rangeKerCF`, for every test function, in particular for tests inside pockets) gives exactly the
  joint-Gaussian hypothesis of the two tilt lemmas, with the zero-boundary covariance of the retained domain;
* `eq_of_cfVal_eq_rat`, `ae_eq_of_condExp_cfVal`: two Gaussian conditional characteristic functions of the same
  variable at all rational multiples have the same parameters (to match, off the hull, the retained-range mean and
  variance with the frozen kernel's).

Conditional helpers (abstract probability); they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace RLC

namespace G7aTilt

open LocalExt

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The Gaussian tilt splits off the conditional Laplace transform of the source** (one level `k`): if `(X, Y)` has,
given `m`, almost surely on `D`, the characteristic function of a Gaussian pair with means `μ₁, μ₂` and covariances
`s₁₁, s₁₂, s₂₂`, then almost surely on `D`, `E[e^{−Y} e^{iX} | m] = E[e^{−Y} | m] · exp(i(μ₁ − s₁₂) − s₁₁/2)`. -/
theorem ae_condExp_mul_eq_of_joint [IsProbabilityMeasure P] (hm : m ≤ mΩ) {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) (hint : Integrable (fun ω => Real.exp (-Y ω)) P) {D : Set Ω} {μ₁ μ₂ s₁₁ s₁₂ s₂₂ : Ω → ℝ}
    (hjoint : ∀ a b : ℝ, ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => Complex.exp (Complex.I * ((a * X ω' + b * Y ω' : ℝ) : ℂ)) | m]) ω =
        cfVal (a * μ₁ ω + b * μ₂ ω) (a ^ 2 * s₁₁ ω + 2 * a * b * s₁₂ ω + b ^ 2 * s₂₂ ω)) :
    ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => ((Real.exp (-Y ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (X ω' : ℂ)) | m]) ω =
        (P[fun ω' => ((Real.exp (-Y ω') : ℝ) : ℂ) | m]) ω * cfVal (μ₁ ω - s₁₂ ω) (s₁₁ ω) := by
  have h1 := ae_condExp_tilt_of_joint hm hX hY hint hjoint
  have h0 := ae_condExp_tilt_of_joint (Y₁ := fun _ => (0 : ℝ)) (D := D) (μ₁ := fun _ => 0) (s₁₁ := fun _ => 0)
    (s₁₂ := fun _ => 0) (μ₂ := μ₂) (s₂₂ := s₂₂) hm measurable_const hY hint (fun a b => by
      filter_upwards [hjoint 0 b] with ω hω hD
      have e : (fun ω' => Complex.exp (Complex.I * ((a * (fun _ => (0 : ℝ)) ω' + b * Y ω' : ℝ) : ℂ))) =
          fun ω' => Complex.exp (Complex.I * (((0 : ℝ) * X ω' + b * Y ω' : ℝ) : ℂ)) := by
        funext ω'; simp
      rw [e, hω hD]
      congr 1 <;> ring)
  filter_upwards [h1, h0] with ω e1 e0 hD
  have e0' := e0 hD
  have hfun : (fun ω' => ((Real.exp (-Y ω') : ℝ) : ℂ) *
      Complex.exp (Complex.I * (((fun _ => (0 : ℝ)) ω' : ℝ) : ℂ))) = fun ω' => ((Real.exp (-Y ω') : ℝ) : ℂ) := by
    funext ω'; simp
  rw [hfun] at e0'
  rw [e1 hD, e0']
  have hc : cfVal ((fun _ => (0 : ℝ)) ω - (fun _ => (0 : ℝ)) ω) ((fun _ => (0 : ℝ)) ω) = 1 := by
    simp [cfVal]
  rw [hc, mul_one]

/-- **The Gaussian tilt in the limit, without convergence of the source means** (Corollary G7a's pocket step). Let
`Y_k → Λ` with `e^{−Y_k} → e^{−Λ}` in `L¹`, and let each `(X, Y_k)` be conditionally Gaussian given `m`, almost surely
on `D`, with fixed law of `X` (mean `μ₁`, variance `s₁₁`), arbitrary means and variances of `Y_k`, and cross covariances
`s₁₂ᵏ → s₁₂` on `D`. Then almost surely on `D`, `E[e^{−Λ} e^{iX} | m] = E[e^{−Λ} | m] · exp(i(μ₁ − s₁₂) − s₁₁/2)`. -/
theorem ae_condExp_tilt_of_joint_limit [IsProbabilityMeasure P] (hm : m ≤ mΩ) {X Λ : Ω → ℝ} {Y : ℕ → Ω → ℝ}
    (hX : Measurable X) (hY : ∀ k, Measurable (Y k)) (hΛ : Measurable Λ)
    (hint : ∀ k, Integrable (fun ω => Real.exp (-Y k ω)) P) (hintΛ : Integrable (fun ω => Real.exp (-Λ ω)) P)
    (hL1 : Tendsto (fun k => eLpNorm (fun ω => Real.exp (-Y k ω) - Real.exp (-Λ ω)) 1 P) atTop (𝓝 0))
    {D : Set Ω} {μ₁ s₁₁ s₁₂ : Ω → ℝ} {μ₂ s₁₂' s₂₂ : ℕ → Ω → ℝ}
    (hjoint : ∀ k, ∀ a b : ℝ, ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => Complex.exp (Complex.I * ((a * X ω' + b * Y k ω' : ℝ) : ℂ)) | m]) ω =
        cfVal (a * μ₁ ω + b * μ₂ k ω) (a ^ 2 * s₁₁ ω + 2 * a * b * s₁₂' k ω + b ^ 2 * s₂₂ k ω))
    (hs : ∀ᵐ ω ∂P, ω ∈ D → Tendsto (fun k => s₁₂' k ω) atTop (𝓝 (s₁₂ ω))) :
    ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (X ω' : ℂ)) | m]) ω =
        (P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) | m]) ω * cfVal (μ₁ ω - s₁₂ ω) (s₁₁ ω) := by
  -- the tilted and untilted densities, at each level and in the limit
  set f : ℕ → Ω → ℂ := fun k ω => ((Real.exp (-Y k ω) : ℝ) : ℂ) * Complex.exp (Complex.I * (X ω : ℂ)) with hfdef
  set g : ℕ → Ω → ℂ := fun k ω => ((Real.exp (-Y k ω) : ℝ) : ℂ) with hgdef
  set f' : Ω → ℂ := fun ω => ((Real.exp (-Λ ω) : ℝ) : ℂ) * Complex.exp (Complex.I * (X ω : ℂ)) with hf'def
  set g' : Ω → ℂ := fun ω => ((Real.exp (-Λ ω) : ℝ) : ℂ) with hg'def
  have hcX : Measurable fun ω => Complex.exp (Complex.I * (X ω : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hX))
  have hgm : ∀ k, Measurable (g k) := fun k =>
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hY k).neg)
  have hg'm : Measurable g' := Complex.measurable_ofReal.comp (Real.measurable_exp.comp hΛ.neg)
  have hnf : ∀ (r : ℝ) (ω : Ω), ‖((r : ℝ) : ℂ) * Complex.exp (Complex.I * (X ω : ℂ))‖ = ‖r‖ := fun r ω => by
    rw [norm_mul, norm_cexp_I_mul, mul_one, Complex.norm_real]
  have hfi : ∀ k, Integrable (f k) P := fun k =>
    (hint k).mono ((hgm k).mul hcX).aestronglyMeasurable (ae_of_all _ fun ω => (hnf _ ω).le)
  have hgi : ∀ k, Integrable (g k) P := fun k =>
    (hint k).mono (hgm k).aestronglyMeasurable (ae_of_all _ fun ω => (Complex.norm_real _).le)
  have hf'i : Integrable f' P :=
    hintΛ.mono (hg'm.mul hcX).aestronglyMeasurable (ae_of_all _ fun ω => (hnf _ ω).le)
  have hg'i : Integrable g' P :=
    hintΛ.mono hg'm.aestronglyMeasurable (ae_of_all _ fun ω => (Complex.norm_real _).le)
  -- `L¹` contraction of the conditional expectations
  have hcontr : ∀ (u : ℕ → Ω → ℂ) (u' : Ω → ℂ), (∀ k, Integrable (u k) P) → Integrable u' P →
      (∀ k ω, ‖u k ω - u' ω‖ = ‖Real.exp (-Y k ω) - Real.exp (-Λ ω)‖) →
      Tendsto (fun k => eLpNorm (P[u k | m] - P[u' | m]) 1 P) atTop (𝓝 0) := by
    intro u u' hui hu'i hnorm
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 (fun k => zero_le) fun k => ?_
    calc eLpNorm (P[u k | m] - P[u' | m]) 1 P = eLpNorm (P[u k - u' | m]) 1 P :=
          eLpNorm_congr_ae (condExp_sub (hui k) hu'i m).symm
      _ ≤ eLpNorm (u k - u') 1 P := eLpNorm_condExp_le_eLpNorm _ le_rfl
      _ = eLpNorm (fun ω => Real.exp (-Y k ω) - Real.exp (-Λ ω)) 1 P :=
          eLpNorm_congr_norm_ae (ae_of_all _ fun ω => hnorm k ω)
  have hLf := hcontr f f' hfi hf'i fun k ω => by
    simp only [hfdef, hf'def]
    rw [← sub_mul, ← Complex.ofReal_sub, hnf]
  have hLg := hcontr g g' hgi hg'i fun k ω => by
    simp only [hgdef, hg'def]
    rw [← Complex.ofReal_sub, Complex.norm_real]
  have hsm : ∀ u : Ω → ℂ, AEStronglyMeasurable (P[u | m]) P := fun u =>
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  -- a common subsequence along which both conditional expectations converge almost surely
  obtain ⟨ns, hns, hfa⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun k => hsm (f k)) (hsm f') hLf).exists_seq_tendsto_ae
  obtain ⟨ns₂, hns₂, hga⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun k => hsm (g (ns k))) (hsm g')
    (hLg.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have step : ∀ k, ∀ᵐ ω ∂P, ω ∈ D → (P[f k | m]) ω = (P[g k | m]) ω * cfVal (μ₁ ω - s₁₂' k ω) (s₁₁ ω) :=
    fun k => ae_condExp_mul_eq_of_joint hm hX (hY k) (hint k) (hjoint k)
  filter_upwards [hfa, hga, ae_all_iff.2 step, hs] with ω hfω hgω hstep hsω hD
  have hlim1 : Tendsto (fun i => (P[f (ns (ns₂ i)) | m]) ω) atTop (𝓝 ((P[f' | m]) ω)) :=
    hfω.comp hns₂.tendsto_atTop
  have hlim2 : Tendsto (fun i => (P[f (ns (ns₂ i)) | m]) ω) atTop
      (𝓝 ((P[g' | m]) ω * cfVal (μ₁ ω - s₁₂ ω) (s₁₁ ω))) := by
    have e : (fun i => (P[f (ns (ns₂ i)) | m]) ω) =
        fun i => (P[g (ns (ns₂ i)) | m]) ω * cfVal (μ₁ ω - s₁₂' (ns (ns₂ i)) ω) (s₁₁ ω) :=
      funext fun i => hstep _ hD
    rw [e]
    refine hgω.mul ?_
    have hc : Tendsto (fun i => s₁₂' (ns (ns₂ i)) ω) atTop (𝓝 (s₁₂ ω)) :=
      (hsω hD).comp (hns.comp hns₂).tendsto_atTop
    exact (continuous_cfVal.tendsto _).comp ((tendsto_const_nhds.sub hc).prodMk_nhds tendsto_const_nhds)
  exact tendsto_nhds_unique hlim1 hlim2

/-! ### The joint law from the retained-range kernel -/

open LQGMetric (TestOn DistOn) in
/-- The retained-range kernel value is the Gaussian characteristic-function value of the mean and the variance. -/
theorem rangeKerCF_eq_cfVal (M : DistOn upperHalfPlaneOpens) (V : Set ℂ) (χ : TestOn upperHalfPlaneOpens) :
    WholeField.rangeKerCF M V χ = cfVal (M χ) (QuantumZipper.zeroGFFTestCov V χ χ) := rfl

open LQGMetric (TestOn) in
/-- The zero-boundary covariance of a combination of two test functions. -/
theorem zeroGFFTestCov_combo {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ QuantumZipper.H) (a b : ℝ)
    (φ ψ : TestOn upperHalfPlaneOpens) :
    QuantumZipper.zeroGFFTestCov V ⇑(a • φ + b • ψ) ⇑(a • φ + b • ψ) =
      a ^ 2 * QuantumZipper.zeroGFFTestCov V φ φ + 2 * a * b * QuantumZipper.zeroGFFTestCov V φ ψ +
        b ^ 2 * QuantumZipper.zeroGFFTestCov V ψ ψ := by
  simp only [LocalExt.zeroGFFTestCov_add_left hV hVH, LocalExt.zeroGFFTestCov_add_right hV hVH,
    LocalExt.zeroGFFTestCov_smul_left hV hVH, LocalExt.zeroGFFTestCov_smul_right hV hVH]
  rw [LocalExt.zeroGFFTestCov_comm hV hVH ψ φ]
  ring

open LQGMetric (TestOn DistOn) in
/-- **The joint conditional law of two pairings from the retained-range kernel** (Aux. lemma 16's kernel,
`WholeField.HasRetainedRangeKernel`, at one stop): if for every test function `χ` the conditional characteristic
function of `h(χ)` is `rangeKerCF (M ω) (V ω) χ` with `V ω` open in `ℍ` (the retained domain `ℍ \ η[0, τ]`, pockets
included), then `(h(φ), h(ψ))` is conditionally Gaussian with means `(M φ, M ψ)` and the covariances of the
zero-boundary GFF on `V ω`: the hypothesis `hjoint` of `ae_condExp_mul_eq_of_joint` and
`ae_condExp_tilt_of_joint_limit`. -/
theorem ae_condExp_joint_of_rangeKer {h M : Ω → DistOn upperHalfPlaneOpens} {V : Ω → Set ℂ}
    (hV : ∀ᵐ ω ∂P, IsOpen (V ω) ∧ V ω ⊆ QuantumZipper.H)
    (hker : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      (P[fun ω' => Complex.exp (Complex.I * (h ω' χ : ℂ)) | m]) ω = WholeField.rangeKerCF (M ω) (V ω) χ)
    (φ ψ : TestOn upperHalfPlaneOpens) (a b : ℝ) :
    ∀ᵐ ω ∂P, (P[fun ω' => Complex.exp (Complex.I * ((a * h ω' φ + b * h ω' ψ : ℝ) : ℂ)) | m]) ω =
      cfVal (a * M ω φ + b * M ω ψ) (a ^ 2 * QuantumZipper.zeroGFFTestCov (V ω) φ φ +
        2 * a * b * QuantumZipper.zeroGFFTestCov (V ω) φ ψ + b ^ 2 * QuantumZipper.zeroGFFTestCov (V ω) ψ ψ) := by
  have e : (fun ω' => Complex.exp (Complex.I * ((a * h ω' φ + b * h ω' ψ : ℝ) : ℂ))) =
      fun ω' => Complex.exp (Complex.I * (h ω' (a • φ + b • ψ) : ℂ)) := by
    funext ω'; rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  filter_upwards [hker (a • φ + b • ψ), hV] with ω hω hVω
  rw [e, hω, rangeKerCF_eq_cfVal, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    zeroGFFTestCov_combo hVω.1 hVω.2]

/-! ### Identification of Gaussian parameters -/

/-- **Gaussian parameters from the characteristic function at rational multiples.** -/
theorem eq_of_cfVal_eq_rat {a a' q q' : ℝ}
    (h : ∀ t : ℚ, cfVal ((t : ℝ) * a) ((t : ℝ) ^ 2 * q) = cfVal ((t : ℝ) * a') ((t : ℝ) ^ 2 * q')) :
    a = a' ∧ q = q' := by
  have h1 := h 1
  simp only [Rat.cast_one, one_mul, one_pow] at h1
  have hq : q = q' := by
    have hn := congrArg norm h1
    rw [norm_cfVal, norm_cfVal] at hn
    have := Real.exp_injective hn
    linarith
  subst hq
  refine ⟨?_, rfl⟩
  by_contra hne
  have hd : a - a' ≠ 0 := sub_ne_zero.2 hne
  have hdpos : 0 < |a - a'| := abs_pos.2 hd
  have hpos : (0 : ℝ) < 2 * Real.pi / |a - a'| := div_pos (by positivity) hdpos
  obtain ⟨t, ht0, ht⟩ := exists_rat_btwn hpos
  have ht' := h t
  unfold cfVal at ht'
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 ht'
  have him := congrArg Complex.im hn
  simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, one_mul, mul_zero, zero_add, sub_zero, add_zero, Complex.mul_re] at him
  have key : (t : ℝ) * (a - a') = (n : ℝ) * (2 * Real.pi) := by linarith
  have hlt : |(t : ℝ) * (a - a')| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos ht0]
    rwa [lt_div_iff₀ hdpos] at ht
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Int.cast_zero, zero_mul, mul_eq_zero] at key
    rcases key with h0 | h0
    · exact absurd h0 ht0.ne'
    · exact hd h0
  · have h1n : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
    have : 2 * Real.pi ≤ |(t : ℝ) * (a - a')| := by
      rw [key, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos]
    linarith

/-- **Two Gaussian conditional laws of one variable agree in their parameters**: if, almost surely on `D`, the
conditional characteristic function of `X` at every rational multiple is Gaussian with parameters `(A, Q)` and also with
`(A', Q')`, then `A = A'` and `Q = Q'` almost surely on `D`. -/
theorem ae_eq_of_condExp_cfVal {X A A' Q Q' : Ω → ℝ} {D : Set Ω}
    (h₁ : ∀ t : ℚ, ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => Complex.exp (Complex.I * (((t : ℝ) * X ω' : ℝ) : ℂ)) | m]) ω =
        cfVal ((t : ℝ) * A ω) ((t : ℝ) ^ 2 * Q ω))
    (h₂ : ∀ t : ℚ, ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => Complex.exp (Complex.I * (((t : ℝ) * X ω' : ℝ) : ℂ)) | m]) ω =
        cfVal ((t : ℝ) * A' ω) ((t : ℝ) ^ 2 * Q' ω)) :
    ∀ᵐ ω ∂P, ω ∈ D → A ω = A' ω ∧ Q ω = Q' ω := by
  filter_upwards [ae_all_iff.2 h₁, ae_all_iff.2 h₂] with ω e1 e2 hD
  exact eq_of_cfVal_eq_rat fun t => (e1 t hD).symm.trans (e2 t hD)

end G7aTilt

end RLC

end InteractingSLE
