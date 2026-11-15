/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import MathFin.Probability.Brownian.LevyCharacterization
import MathFin.Probability.Brownian.QuadraticVariationL2
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal
import InteractingSLE.GFF.LocalSets.GermLaw

/-!
# Brownian driving noise after the hull germ is retained (Aux. lemma 47, Brownian conclusion)

Packet PROVE-SEC7-A3 (specification §7.1, Aux. lemma 47, `source/spec/p193-240.md` L653–L690,
pp. 227–229). Aux. lemma 47 enlarges the own driving filtration `𝓕` by the canonical field germ of the
hull, `𝒢ₜ ⊇ 𝓕ₜ`, and proves that the Brownian motion `B` of the integrated driving equation is still a
Brownian motion in `𝒢`. The source shows first that `B` is a continuous `𝒢`-local martingale (the
harmonic-mean martingale (GB2) at a point above the hulls, (GB3) `dM = k dB`, and (GB4)
`B = ∫ k⁻¹ dM`), then identifies its quadratic variation `t` pathwise and applies Lévy's
characterization. This file proves the second half in full generality:

* `isFilteredBrownianReal_of_martingale`: **a Brownian motion that is a martingale in a filtration
  `𝒢` is a Brownian motion in `𝒢`** (every increment `B_t − B_s` is independent of `𝒢ₛ`), for paths
  continuous everywhere with `B₀ = 0`;
* `isFilteredBrownianReal_of_martingale_of_null`: the same for Mathlib's `IsBrownianReal` (paths
  continuous almost surely) when every `𝒢ₛ` contains the measurable null sets (the usual augmentation
  of Aux. lemma 47 does).

The quadratic-variation step (`setIntegral_sq_sub_sq_eq_of_martingale_of_isPreBrownianReal`): for
`A ∈ 𝒢ₛ` the increments of the `𝒢`-martingale `B` are orthogonal on `A`
(`setIntegral_sq_sub_sq_eq_of_martingale`), so `∫_A (B_t² − B_s²) = ∫_A ∑ₖ (ΔBₖ)²` along every
uniform partition of `[s, t]`, and `∑ₖ (ΔBₖ)² → t − s` in `L²` because this is a statement about the
law of `B` alone (MathFin's `tendsto_qv` for the shifted Brownian motion). Hence `B² − t` is a
`𝒢`-martingale and MathFin's Lévy characterization applies. "Its quadratic variation is the pathwise
quantity `t ∧ σ`" (p. 229) is exactly this: the bracket does not depend on the filtration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝒢 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- Orthogonality of martingale increments: for a square-integrable martingale `B` and `A ∈ 𝒢ᵤ`,
`∫_A (B_v² − B_u²) = ∫_A (B_v − B_u)²`. -/
lemma setIntegral_sq_sub_sq_eq_of_martingale [IsFiniteMeasure P] (hBm : Martingale B 𝒢 P)
    (hL2 : ∀ t, MemLp (B t) 2 P) {u v : ℝ≥0} (huv : u ≤ v) {A : Set Ω}
    (hA : MeasurableSet[𝒢 u] A) :
    ∫ ω in A, (B v ω ^ 2 - B u ω ^ 2) ∂P = ∫ ω in A, (B v ω - B u ω) ^ 2 ∂P := by
  have hA' : MeasurableSet A := 𝒢.le u A hA
  have hint : ∀ a b, Integrable (fun ω => B a ω * B b ω) P := fun a b =>
    (hL2 a).integrable_mul (hL2 b)
  -- `∫_A B_u B_v = ∫_A B_u²`
  have hcross : ∫ ω in A, B u ω * B v ω ∂P = ∫ ω in A, B u ω * B u ω ∂P := by
    have h1 : P[fun ω => B u ω * B v ω | 𝒢 u] =ᵐ[P] fun ω => B u ω * B u ω := by
      have := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 u) (hBm.stronglyAdapted u)
        (hint u v) (hBm.integrable v)
      refine this.trans ?_
      filter_upwards [hBm.condExp_ae_eq huv] with ω hω
      simp only [Pi.mul_apply, hω]
    rw [← setIntegral_condExp (𝒢.le u) (hint u v) hA]
    exact setIntegral_congr_ae hA' (h1.mono fun ω hω _ => hω)
  have e1 : ∀ ω, (B v ω - B u ω) ^ 2
      = (B v ω ^ 2 - B u ω ^ 2) - 2 * (B u ω * B v ω - B u ω * B u ω) := fun ω => by ring
  have hI1 : Integrable (fun ω => B v ω ^ 2 - B u ω ^ 2) P :=
    (hL2 v).integrable_sq.sub (hL2 u).integrable_sq
  have hI2 : Integrable (fun ω => B u ω * B v ω - B u ω * B u ω) P := (hint u v).sub (hint u u)
  calc ∫ ω in A, (B v ω ^ 2 - B u ω ^ 2) ∂P
      = ∫ ω in A, (B v ω ^ 2 - B u ω ^ 2) ∂P
          - 2 * (∫ ω in A, B u ω * B v ω ∂P - ∫ ω in A, B u ω * B u ω ∂P) := by
        rw [hcross, sub_self, mul_zero, sub_zero]
    _ = ∫ ω in A, ((B v ω ^ 2 - B u ω ^ 2) - 2 * (B u ω * B v ω - B u ω * B u ω)) ∂P := by
        rw [integral_sub hI1.integrableOn (hI2.const_mul 2).integrableOn, integral_const_mul,
          integral_sub (hint u v).integrableOn (hint u u).integrableOn]
    _ = ∫ ω in A, (B v ω - B u ω) ^ 2 ∂P := by simp_rw [← e1]

/-- **The quadratic-variation step.** If a Brownian motion `B` is a martingale in `𝒢`, then for
`s ≤ t` and `A ∈ 𝒢ₛ`, `∫_A (B_t² − B_s²) = (t − s) P(A)`: by orthogonality of the increments the left
side is `∫_A ∑ₖ (ΔBₖ)²` along every uniform partition of `[s, t]`, and `∑ₖ (ΔBₖ)² → t − s` in `L²`. -/
lemma setIntegral_sq_sub_sq_eq_of_martingale_of_isPreBrownianReal [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hBm : Martingale B 𝒢 P) (hL2 : ∀ t, MemLp (B t) 2 P)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝒢 s] A) :
    ∫ ω in A, (B t ω ^ 2 - B s ω ^ 2) ∂P = ((t : ℝ) - s) * P.real A := by
  have hmeas : ∀ r, Measurable (B r) := fun r => ((hBm.stronglyAdapted r).mono (𝒢.le r)).measurable
  have hsq : ∀ a b : ℝ≥0, Integrable (fun ω => (B a ω - B b ω) ^ 2) P := fun a b =>
    ((hL2 a).sub (hL2 b)).integrable_sq
  have hsq' : ∀ a b : ℝ≥0, Integrable (fun ω => B a ω ^ 2 - B b ω ^ 2) P := fun a b =>
    (hL2 a).integrable_sq.sub (hL2 b).integrable_sq
  have hSint : ∀ n, Integrable (fun ω => ∑ k ∈ Finset.range n,
      (B (MathFin.unifPartIcc s t n (k + 1)) ω - B (MathFin.unifPartIcc s t n k) ω) ^ 2) P :=
    fun n => integrable_finsetSum _ fun k _ => hsq _ _
  -- the set integral equals that of the sum of squared increments
  have hrepr : ∀ n, n ≠ 0 → ∫ ω in A, (B t ω ^ 2 - B s ω ^ 2) ∂P = ∫ ω in A, ∑ k ∈ Finset.range n,
      (B (MathFin.unifPartIcc s t n (k + 1)) ω - B (MathFin.unifPartIcc s t n k) ω) ^ 2 ∂P := by
    intro n hn
    have htel : ∀ ω, B t ω ^ 2 - B s ω ^ 2 = ∑ k ∈ Finset.range n,
        (B (MathFin.unifPartIcc s t n (k + 1)) ω ^ 2 - B (MathFin.unifPartIcc s t n k) ω ^ 2) :=
      fun ω => by
        rw [Finset.sum_range_sub (fun k => B (MathFin.unifPartIcc s t n k) ω ^ 2),
          MathFin.unifPartIcc_zero, MathFin.unifPartIcc_self hst hn]
    simp_rw [htel]
    rw [integral_finsetSum (Finset.range n) fun k _ => (hsq' _ _).integrableOn,
      integral_finsetSum (Finset.range n) fun k _ => (hsq _ _).integrableOn]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsk : s ≤ MathFin.unifPartIcc s t n k := le_self_add
    exact setIntegral_sq_sub_sq_eq_of_martingale hBm hL2
      (MathFin.unifPartIcc_mono s t n (Nat.le_succ k)) (𝒢.mono hsk A hA)
  -- the sums converge to `t − s` in `L²`, by the shifted Brownian motion
  have hqv := MathFin.QuadraticVariationL2.tendsto_qv (hB.shift s)
    (fun r => (hmeas _).sub (hmeas _)) (t - s)
  have hts : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - s := NNReal.coe_sub hst
  have hqv' : Tendsto (fun n => ∫ ω, ((∑ k ∈ Finset.range n,
      (B (MathFin.unifPartIcc s t n (k + 1)) ω - B (MathFin.unifPartIcc s t n k) ω) ^ 2)
        - ((t : ℝ) - s)) ^ 2 ∂P) atTop (𝓝 0) := by
    refine hqv.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have hsum : ∀ k ∈ Finset.range n,
        (B (s + MathFin.unifPart (t - s) n (k + 1)) ω - B s ω
          - (B (s + MathFin.unifPart (t - s) n k) ω - B s ω)) ^ 2
        = (B (MathFin.unifPartIcc s t n (k + 1)) ω - B (MathFin.unifPartIcc s t n k) ω) ^ 2 :=
      fun k _ => by rw [sub_sub_sub_cancel_right]; rfl
    show (∑ k ∈ Finset.range n, (B (s + MathFin.unifPart (t - s) n (k + 1)) ω - B s ω
          - (B (s + MathFin.unifPart (t - s) n k) ω - B s ω)) ^ 2 - ((t - s : ℝ≥0) : ℝ)) ^ 2 = _
    rw [Finset.sum_congr rfl hsum, hts]
  have hinc2 : ∀ a b : ℝ≥0, MemLp (fun ω => (B a ω - B b ω) ^ 2) 2 P := fun a b => by
    have h := MathFin.QuadraticVariationL2.memLp_increment_sq_centered_two hB b a 0
    refine (memLp_congr_ae (Eventually.of_forall fun ω => ?_)).1 h
    simp only [sub_zero]
  have hmem : ∀ n, MemLp (fun ω => (∑ k ∈ Finset.range n,
      (B (MathFin.unifPartIcc s t n (k + 1)) ω - B (MathFin.unifPartIcc s t n k) ω) ^ 2)
        - ((t : ℝ) - s)) 2 P := fun n =>
    (memLp_finsetSum (Finset.range n) fun k _ => hinc2 _ _).sub (memLp_const _)
  have hlim := LocalSets.tendsto_setIntegral_of_tendsto_integral_sq
    (f := fun _ => (t : ℝ) - s) (integrable_const _) hSint hmem hqv' A
  rw [setIntegral_const, smul_eq_mul, mul_comm] at hlim
  refine tendsto_nhds_unique (f := fun _ : ℕ => ∫ ω in A, (B t ω ^ 2 - B s ω ^ 2) ∂P)
    tendsto_const_nhds (hlim.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (hrepr n hn).symm

/-- **A Brownian motion that is a martingale in a filtration is a Brownian motion in that
filtration.** If `B` is a Brownian motion with continuous paths, `B₀ = 0`, and `B` is a martingale
for `𝒢`, then every increment `B_t − B_s` is independent of `𝒢ₛ`. Lévy's characterization, after
the quadratic-variation step: `B² − t` is a `𝒢`-martingale. -/
theorem isFilteredBrownianReal_of_martingale [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hBc : ∀ ω, Continuous fun t => B t ω) (hB0 : ∀ ω, B 0 ω = 0) (hBm : Martingale B 𝒢 P) :
    IsFilteredBrownianReal 𝒢 B P := by
  have hpre := hB.toIsPreBrownianReal
  have hL2 : ∀ r, MemLp (B r) 2 P := fun r => by
    have h4 := MathFin.QuadraticVariationL2.memLp_increment_four hpre 0 r
    simp only [hB0, sub_zero] at h4
    exact h4.mono_exponent (by norm_num)
  have hsqa : StronglyAdapted 𝒢 (fun t ω => B t ω ^ 2 - (t : ℝ)) := fun r =>
    ((hBm.stronglyAdapted r).pow 2).sub stronglyMeasurable_const
  have hsqi : ∀ r, Integrable (fun ω => B r ω ^ 2 - (r : ℝ)) P := fun r =>
    (hL2 r).integrable_sq.sub (integrable_const _)
  have hsqm : Martingale (fun t ω => B t ω ^ 2 - (t : ℝ)) 𝒢 P := by
    refine ⟨hsqa, fun s t hst => ?_⟩
    refine (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le s) (hsqi t)
      (fun A _ _ => (hsqi s).integrableOn) (fun A hA _ => ?_)
      (hsqa s).aestronglyMeasurable).symm
    have hA' : MeasurableSet A := 𝒢.le s A hA
    have key := setIntegral_sq_sub_sq_eq_of_martingale_of_isPreBrownianReal hpre hBm hL2 hst hA
    rw [integral_sub (hL2 t).integrable_sq.integrableOn (hL2 s).integrable_sq.integrableOn] at key
    rw [integral_sub (hL2 t).integrable_sq.integrableOn (integrable_const _).integrableOn,
      integral_sub (hL2 s).integrable_sq.integrableOn (integrable_const _).integrableOn,
      setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul]
    linarith
  have hBloc : IsLocalMartingale B 𝒢 P :=
    Martingale.IsLocalMartingale hBm fun ω => (hBc ω).isCadlag
  have hB2loc : IsLocalMartingale (fun t ω => B t ω ^ 2 - (t : ℝ)) 𝒢 P :=
    Martingale.IsLocalMartingale hsqm fun ω =>
      (((hBc ω).pow 2).sub NNReal.continuous_coe).isCadlag
  have hfp := MathFin.LevyCharacterization.isFilteredPreBrownian_of_localMartingale
    hBm.stronglyAdapted hBc hB0 hBloc hB2loc
  exact ⟨hB, hBm.stronglyAdapted.adapted, fun s t hst => hfp.indep s t hst⟩

/-- The same conclusion when the paths are only almost surely continuous (as for Mathlib's
`IsBrownianReal`), provided every `𝒢ₛ` contains the measurable `P`-null sets (as the usual augmentation
does). -/
theorem isFilteredBrownianReal_of_martingale_of_null [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (hnull : ∀ s (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 s] N)
    (hBm : Martingale B 𝒢 P) : IsFilteredBrownianReal 𝒢 B P := by
  classical
  have hgood : ∀ᵐ ω ∂P, Continuous (fun t => B t ω) ∧ B 0 ω = 0 :=
    hB.cont.and hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodN : ∀ ω, ω ∉ N → Continuous (fun t => B t ω) ∧ B 0 ω = 0 := fun ω hω => by
    by_contra h
    exact hω (hNsub h)
  set C : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N then 0 else B t ω with hC
  have hCc : ∀ ω, Continuous fun t => C t ω := fun ω => by
    by_cases hω : ω ∈ N
    · simp only [hC, hω, ite_true]; exact continuous_const
    · simp only [hC, hω, ite_false]; exact (hgoodN ω hω).1
  have hC0 : ∀ ω, C 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ N
    · simp [hC, hω]
    · simp [hC, hω, (hgoodN ω hω).2]
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hae : ∀ t, C t =ᵐ[P] B t := fun t => hNae.mono fun ω hω => by simp [hC, hω]
  have hCB : IsBrownianReal C P :=
    { toIsPreBrownianReal := hB.toIsPreBrownianReal.congr fun t => (hae t).symm
      cont := ae_of_all _ hCc }
  have hCm : Martingale C 𝒢 P := by
    refine ⟨fun t => ?_, fun s t hst => ?_⟩
    · exact StronglyMeasurable.ite (hnull t N hNm hN0) stronglyMeasurable_const
        (hBm.stronglyAdapted t)
    · exact (condExp_congr_ae (hae t)).trans ((hBm.condExp_ae_eq hst).trans (hae s).symm)
  have hres := isFilteredBrownianReal_of_martingale hCB hCc hC0 hCm
  refine ⟨hB, hBm.stronglyAdapted.adapted, fun s t hst => ?_⟩
  have hind := hres.2.2 s t hst
  rw [Indep_iff] at hind ⊢
  rintro _ t₂ ⟨S, hS, rfl⟩ ht₂
  have hset : (fun ω => B t ω - B s ω) ⁻¹' S =ᵐ[P] (fun ω => C t ω - C s ω) ⁻¹' S := by
    filter_upwards [hNae] with ω hω
    simp [hC, hω]
  rw [measure_congr (hset.inter (ae_eq_refl t₂)), measure_congr hset]
  exact hind _ t₂ ⟨S, hS, rfl⟩ ht₂

end Sec7

end InteractingSLE
