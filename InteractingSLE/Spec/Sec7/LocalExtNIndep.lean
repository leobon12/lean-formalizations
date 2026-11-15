/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.Spec.Coupling.ResampleProjCore

/-!
# The projection identity on the events of a σ-algebra gives independence of the projection

Packet PROVE-LOCEXT-N. Let `X` be a zero-boundary GFF on `ℍ`, `U ⊆ ℍ` open, `G` a Borel version of the projection onto
`H(U)` and `Y = X − G X`. If the projection identity of `Coupling.IsFamilyLocal`

  `∫_D e^{i X(−Δf/2π + Ξ)} = exp(−‖∇f‖²/2 − ⟪∇f, covVec_U Ξ⟫) ∫_D e^{i X(Ξ)}`

holds on an event `D` for every `f ∈ C_c^∞(U)` and every test function `Ξ`, then

  `∫_D e^{i G X(Φ)} e^{i Y(Ψ)} = exp(−‖covVec_U Φ‖²/2) ∫_D e^{i Y(Ψ)}`

(`setIntegral_markov_mul_eq`). Proof: `G X(Φ − Ψ)` is the `L²` limit of the Dirichlet pairings `X(−Δf_n/2π)` with
`∇f_n → covVec_U(Φ − Ψ)`, and `G X(Φ − Ψ) + X(Ψ) = G X(Φ) + Y(Ψ)`; so the identity with `Ξ = Ψ` passes to the limit, and
the case `Φ = 0` removes `X(Ψ)` in favour of `Y(Ψ)`. If it holds on every event of a σ-algebra `𝓜`, then `G X` is
independent of `σ(Y) ⊔ 𝓜` (`indep_markov_of_setIntegral_lapTest`).

## Main results

* `setIntegral_markov_mul_eq`, `integral_cexp_markov_eq`;
* `indep_markov_of_setIntegral_lapTest`;
* `cexp_covVec_lapTest_add_eq`: `exp(−‖covVec_U(−Δf/2π + Ξ)‖²/2) = projFactor · exp(−‖covVec_U Ξ‖²/2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE

namespace LocalExt

open LQGMetric LQGMetric.MarkovZB LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm Coupling

section Indep

variable {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens} {U : Opens ℂ}
  {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}

/-- The Gaussian factor of the projection onto `H(U)` at `Φ`. -/
def gaussFactor (U : Opens ℂ) (Φ : TestOn upperHalfPlaneOpens) : ℂ :=
  Complex.exp (((-(1 / 2) * ‖covVec (U : Set ℂ) Φ‖ ^ 2 : ℝ) : ℂ))

/-- **The Dirichlet direction enters the Gaussian factor with the projection factor.** -/
theorem gaussFactor_lapTest_add (hUH : (U : Set ℂ) ⊆ H) (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    gaussFactor U (lapTest U f + Ξ) = projFactor U f Ξ * gaussFactor U Ξ := by
  rw [gaussFactor, gaussFactor, projFactor, ← Complex.exp_add,
    norm_covVec_lapTest_add_sq U.isOpen hUH subset_rfl f Ξ]
  congr 1
  push_cast
  ring

/-- **The projection identity on one event, in the limit form.** -/
theorem setIntegral_markov_mul_eq_aux (hXm : Measurable X) (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) P) {D : Set Ω} (hD : MeasurableSet D)
    (hid : ∀ (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens),
      ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
        projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P)
    (Φ Ψ : TestOn upperHalfPlaneOpens) :
    ∫ ω in D, Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (X ω) Ψ : ℂ)) ∂P =
      Complex.exp (((-(1 / 2) * ‖covVec (U : Set ℂ) (Φ - Ψ)‖ ^ 2 -
          ⟪covVec (U : Set ℂ) (Φ - Ψ), covVec (U : Set ℂ) Ψ⟫ : ℝ) : ℂ)) *
        ∫ ω in D, Complex.exp (Complex.I * (X ω Ψ : ℂ)) ∂P := by
  have hU : U ≤ upperHalfPlaneOpens := hUH
  obtain ⟨f, hfgrad, hf⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd (Φ - Ψ)
  set a : ℕ → Ω → ℝ := fun n ω => X ω (lapTest U (f n)) with ha_def
  set b : Ω → ℝ := fun ω => G (X ω) (Φ - Ψ) with hb_def
  have ham : ∀ n, Measurable (a n) := fun n => (measurable_distOn_apply _).comp hXm
  have hbm : Measurable b := (measurable_distOn_apply _).comp (hG.comp hXm)
  have hmem : ∀ n, MemLp (fun ω => a n ω - b ω) 2 P := fun n => by
    have h1 := (memLp_markov_sub_lapTest hU hd (Φ - Ψ) (f n)).neg
    convert h1 using 1
    funext ω
    simp only [Pi.neg_apply, a, b, neg_sub]
  have hlim : Tendsto (fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂P) atTop (𝓝 0) := by
    refine hf.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [a, b]
    ring
  set Z : Ω → ℂ := D.indicator fun ω => Complex.exp (Complex.I * (X ω Ψ : ℂ)) with hZdef
  have hZm : Measurable Z :=
    (GFF.measurable_exp_I_mul ((measurable_distOn_apply Ψ).comp hXm)).indicator hD
  have hZb : ∀ ω, ‖Z ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ D
    · rw [hZdef, indicator_of_mem hω]; exact (Complex.norm_exp_I_mul_ofReal _).le
    · rw [hZdef, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have h1 := tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim hZb
    (fun n => ((GFF.measurable_exp_I_mul (ham n)).mul hZm).aestronglyMeasurable)
    ((GFF.measurable_exp_I_mul hbm).mul hZm).aestronglyMeasurable
  -- the approximating integrals
  have h2 : ∀ n, ∫ ω, Complex.exp (Complex.I * (a n ω : ℂ)) * Z ω ∂P =
      projFactor U (f n) Ψ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ψ : ℂ)) ∂P := by
    intro n
    rw [← hid (f n) Ψ, ← setIntegral_eq_integral_indicator_mul hD]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [a, map_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  -- the limit of the projection factors
  have h3 : Tendsto (fun n => projFactor U (f n) Ψ) atTop
      (𝓝 (Complex.exp (((-(1 / 2) * ‖covVec (U : Set ℂ) (Φ - Ψ)‖ ^ 2 -
        ⟪covVec (U : Set ℂ) (Φ - Ψ), covVec (U : Set ℂ) Ψ⟫ : ℝ) : ℂ)))) := by
    have hc : Continuous fun v : _ => Complex.exp (((-(1 / 2) * ‖v‖ ^ 2 -
        ⟪v, covVec (U : Set ℂ) Ψ⟫ : ℝ) : ℂ)) := by fun_prop
    exact (hc.tendsto _).comp hfgrad
  have h4 := h3.mul_const (∫ ω in D, Complex.exp (Complex.I * (X ω Ψ : ℂ)) ∂P)
  rw [← funext h2] at h4
  have hlimeq := tendsto_nhds_unique h1 h4
  rw [← hlimeq, ← setIntegral_eq_integral_indicator_mul hD]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [b, markovCompl, map_sub, sub_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The projection identity on an event gives the product form with the Gaussian factor.** -/
theorem setIntegral_markov_mul_eq (hXm : Measurable X) (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) P) {D : Set Ω} (hD : MeasurableSet D)
    (hid : ∀ (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens),
      ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
        projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P)
    (Φ Ψ : TestOn upperHalfPlaneOpens) :
    ∫ ω in D, Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (X ω) Ψ : ℂ)) ∂P =
      gaussFactor U Φ * ∫ ω in D, Complex.exp (Complex.I * (markovCompl G (X ω) Ψ : ℂ)) ∂P := by
  have hA := setIntegral_markov_mul_eq_aux hXm hUH hG hd hD hid Φ Ψ
  have hB := setIntegral_markov_mul_eq_aux hXm hUH hG hd hD hid 0 Ψ
  have hz : ∀ ω, G (X ω) (0 : TestOn upperHalfPlaneOpens) = 0 := fun ω => map_zero _
  simp only [hz, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hB
  have hlin : covVec (U : Set ℂ) (⇑Φ - ⇑Ψ) = covVec (U : Set ℂ) Φ - covVec (U : Set ℂ) Ψ := by
    simpa using covVec_sub U.isOpen hUH Φ Ψ
  have hlin0 : covVec (U : Set ℂ) (⇑(0 : TestOn upperHalfPlaneOpens) - ⇑Ψ) = -covVec (U : Set ℂ) Ψ := by
    have := covVec_sub U.isOpen hUH 0 Ψ
    rw [covVec_zero _ U.isOpen hUH, zero_sub] at this
    simpa using this
  have hexp : Complex.exp (((-(1 / 2) * ‖covVec (U : Set ℂ) (⇑Φ - ⇑Ψ)‖ ^ 2 -
      ⟪covVec (U : Set ℂ) (⇑Φ - ⇑Ψ), covVec (U : Set ℂ) Ψ⟫ : ℝ) : ℂ)) =
      gaussFactor U Φ * Complex.exp (((-(1 / 2) * ‖covVec (U : Set ℂ) (⇑(0 : TestOn upperHalfPlaneOpens) - ⇑Ψ)‖ ^ 2 -
        ⟪covVec (U : Set ℂ) (⇑(0 : TestOn upperHalfPlaneOpens) - ⇑Ψ), covVec (U : Set ℂ) Ψ⟫ : ℝ) : ℂ)) := by
    rw [gaussFactor, ← Complex.exp_add, hlin, hlin0]
    congr 1
    rw [norm_sub_sq_real, norm_neg, inner_neg_left, inner_sub_left, real_inner_self_eq_norm_sq]
    push_cast
    ring
  rw [hA, hB, hexp, mul_assoc]

/-- **The characteristic functional of the projection.** -/
theorem integral_cexp_markov_eq (hXm : Measurable X) (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) P)
    (hid : ∀ (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens),
      ∫ ω, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
        projFactor U f Ξ * ∫ ω, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P)
    (Φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) ∂P = gaussFactor U Φ := by
  have := setIntegral_markov_mul_eq hXm hUH hG hd MeasurableSet.univ (by simpa only [Measure.restrict_univ] using hid)
    Φ 0
  have hz : ∀ ω, markovCompl G (X ω) (0 : TestOn upperHalfPlaneOpens) = 0 := fun ω => map_zero _
  simp only [Measure.restrict_univ, hz, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    integral_const, probReal_univ, one_smul] at this
  exact this

/-- **Independence of the projection** from the complementary projection and a σ-algebra on whose events the
projection identity holds. -/
theorem indep_markov_of_setIntegral_lapTest (hXm : Measurable X) (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) P)
    (h𝓜 : 𝓜 ≤ mΩ)
    (hid : ∀ (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (D : Set Ω), MeasurableSet[𝓜] D →
      ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
        projFactor U f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P) :
    Indep (MeasurableSpace.comap (fun ω => G (X ω)) inferInstance)
      (MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ⊔ 𝓜) P := by
  refine indep_comap_sup_of_setIntegral_exp (hG.comp hXm) ((measurable_markovCompl hG).comp hXm) h𝓜
    fun Φ Ψ m hm => ?_
  rw [setIntegral_markov_mul_eq hXm hUH hG hd (h𝓜 _ hm) (fun f Ξ => hid f Ξ m hm) Φ Ψ,
    integral_cexp_markov_eq hXm hUH hG hd (fun f Ξ => by
      have hu : MeasurableSet[𝓜] (univ : Set Ω) := MeasurableSet.univ
      have := hid f Ξ univ hu
      rwa [Measure.restrict_univ] at this) Φ]

/-- **The characteristic functional of a Markov projection**: `E e^{i G X(Φ)} = exp(−‖covVec_U Φ‖²/2)`. -/
theorem integral_cexp_markov_eq_gauss (hXm : Measurable X) (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) P) (Φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) ∂P = gaussFactor U Φ := by
  have hm : Measurable fun ω => X ω - G (X ω) := (measurable_markovCompl hG).comp hXm
  have hc := hd.condExp_exp_zbPart hm Φ
  rw [← integral_condExp (hm.comap_le), integral_congr_ae hc, integral_const, probReal_univ, one_smul,
    gaussFactor, zeroGFFTestCov_eq_inner_covVec U.isOpen hUH, real_inner_self_eq_norm_sq, Complex.ofReal_exp]

/-- **The projection identity on the whole space**, for a zero-boundary GFF with a Markov decomposition at `U`. -/
theorem integral_lapTest_eq_of_isMarkovDecomposition (hXm : Measurable X) (hUH : (U : Set ℂ) ⊆ H)
    (hG : Measurable G) (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) P)
    (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      projFactor U f Ξ * ∫ ω, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P := by
  have hU : U ≤ upperHalfPlaneOpens := hUH
  have hZm : Measurable fun ω => G (X ω) := hG.comp hXm
  have hYm : Measurable fun ω => markovCompl G (X ω) := (measurable_markovCompl hG).comp hXm
  have hlap : ∀ᵐ ω ∂P, markovCompl G (X ω) (lapTest U f) = 0 := by
    filter_upwards [ae_markov_sub_lapTest_eq hU hd (lapTest U f) f] with ω hω
    rw [sub_self, map_zero] at hω
    simp only [markovCompl, sub_apply]
    linarith
  have hfac : ∀ Φ Ψ : TestOn upperHalfPlaneOpens,
      ∫ ω, Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) * Complex.exp (Complex.I * (markovCompl G (X ω) Ψ : ℂ)) ∂P =
        (∫ ω, Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) ∂P) *
          ∫ ω, Complex.exp (Complex.I * (markovCompl G (X ω) Ψ : ℂ)) ∂P := fun Φ Ψ => by
    have := hd.indepFun.integral_fun_comp_mul_comp (f := fun T : DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * (T Φ : ℂ)))
      (g := fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ)))
      hZm.aemeasurable hYm.aemeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply Φ)).aestronglyMeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply Ψ)).aestronglyMeasurable
    simpa [markovCompl] using this
  have hsplit : ∀ Φ : TestOn upperHalfPlaneOpens, ∀ ω, Complex.exp (Complex.I * (X ω Φ : ℂ)) =
      Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) * Complex.exp (Complex.I * (markovCompl G (X ω) Φ : ℂ)) :=
    fun Φ ω => by
      rw [← Complex.exp_add]
      congr 1
      simp only [markovCompl, sub_apply]
      push_cast
      ring
  have h1 : ∫ ω, Complex.exp (Complex.I * (X ω (lapTest U f + Ξ) : ℂ)) ∂P =
      ∫ ω, Complex.exp (Complex.I * (G (X ω) (lapTest U f + Ξ) : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (X ω) Ξ : ℂ)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hlap] with ω hω
    rw [hsplit, map_add (markovCompl G (X ω)), hω, zero_add]
  rw [h1, hfac, integral_cexp_markov_eq_gauss hXm hUH hG hd, gaussFactor_lapTest_add hUH,
    integral_congr_ae (Eventually.of_forall (hsplit Ξ)), hfac, integral_cexp_markov_eq_gauss hXm hUH hG hd, mul_assoc]

end Indep

end LocalExt

end InteractingSLE
