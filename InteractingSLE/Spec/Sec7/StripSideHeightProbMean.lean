/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSideHeightProb
import InteractingSLE.Spec.Coupling.WholeFieldMean
import InteractingSLE.WangWu.PrefixLocalMean

/-!
# (S), probabilistic half, step 2: the local-set mean of the angle-varying path is the stage mean

Packet PROVE-STRIPSYS16. Specification §7.4, proof of Aux. lemma 130 (`source/spec/p385-432.md` L440–L456, p. 411):
"Retain the two full marked local sets. Nested local-set boundary comparison identifies the union mean with each
single-path mean on this collar. To implement that statement with own-path couplings, choose finite rational own times
beyond the compact subarc, use the two stopped canonical means". For the angle-varying path `α` the stopped
canonical mean is the mean given the retained records of both pieces (`ae_condExp_cexp_stopChart`,
`StripSideHeightProb.lean`).

**`ae_apply_eq_stageMean`**: let `A` be a random set (for instance the range of `α` up to own time `t₀ + r`) which is
a local set of the centred field `h⁰ = h − 𝔥₀` satisfying the history-marked avoidance criterion for the retained
records of the two pieces (`WholeField.IsHistoryAvoidanceLocal`, the marked local-set structure the source retains),
and whose complement contains the domain `D` after the stopped continuation as a union of components. Then every
version `g` of its local-set mean satisfies, almost surely on the good event, for every test function `φ` supported in
`D`:

  `g(φ) = ∫ (𝔤 ∘ F − χ ℓ) φ − ∫ 𝔥₀ φ`,

with `F` the chart after the stopped continuation, `ℓ` its lift and `𝔤` the bounded harmonic mean of the stop word
(the transport rule `v + 𝔥₀ = (v' + 𝔥'₀) ∘ f_T − χ arg f_T′` of `StripSideHeight.hasSideHeights_of_restart`).

Proof: the conditional characteristic functional of `(h⁰, φ)` given the records at every frequency (Gaussian, from the
stage law); the mean is recovered as an measurable function of the records (`WholeField.meanOfCharFun`); the
germ-and-history conditional mean equals it (`WholeField.ae_condExp_germSigma_history_eq`); the local-set mean is the
germ-and-history mean (`WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup`, which needs the marked criterion).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace StripSideHeightProb

universe u

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ}
  {t₀ : ℝ≥0} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The local-set mean of a set retained with the records is the stage mean** on the domain after the stopped
continuation. -/
theorem ae_apply_eq_stageMean (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (r : ℝ≥0) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal (pastTwo κ b jumps θ₀ t₀ θ r E) A (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E →
      ((stopChart κ b jumps θ₀ t₀ θ r E ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom))
    {g : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∃ β : Ω → BoundaryWord, Measurable[pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 1] β ∧
      ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E →
        tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom →
        g ω φ = (∫ z, ((stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean
            ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z) -
            chiC κ * (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z) * φ z) - ∫ z, u₀ z * φ z := by
  classical
  obtain ⟨β, hβ, hlaw⟩ := ae_condExp_cexp_stopChart hκ hb hh hS hreg r
  refine ⟨β, hβ, fun φ => ?_⟩
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have h𝓗 := pastTwo_le (κ := κ) (θ₀ := θ₀) (t₀ := t₀) (θ := θ) hb hS.1 hreg r
  have hG : MeasurableSet[pastTwo κ b jumps θ₀ t₀ θ r E] (goodEv κ b jumps θ₀ t₀ θ r E ∩
      {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom}) :=
    (measurableSet_goodEv hb hS.1 hreg).inter (measurableSet_tsupport_subset_stopChart hb hS.1 hreg r φ)
  -- the stage mean of `φ`
  obtain ⟨m, hm⟩ : ∃ m : Ω → ℝ, m = fun ω => (∫ z, ((stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean
      ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z) - chiC κ * (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z) * φ z) -
        ∫ z, u₀ z * φ z := ⟨_, rfl⟩
  -- the Gaussian kernel at every frequency
  have hfreq : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E ∩
      {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom} →
      (P[fun ω' => Complex.exp (Complex.I * ((c * WholeField.centredField h u₀ ω' φ : ℝ) : ℂ)) |
        pastTwo κ b jumps θ₀ t₀ θ r E]) ω =
        Complex.exp (Complex.I * ((c * m ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c
    set U : ℝ := ∫ z, u₀ z * φ z with hU
    have hfun : (fun ω' => Complex.exp (Complex.I * ((c * WholeField.centredField h u₀ ω' φ : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * ((c * U : ℝ) : ℂ))) •
          fun ω' => Complex.exp (Complex.I * (h ω' (c • φ) : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, WholeField.centredField_apply h hu₀.1 ω' φ, map_smul,
        smul_eq_mul]
      congr 1
      push_cast
      ring
    have hsm := condExp_smul (μ := P) (Complex.exp (-(Complex.I * ((c * U : ℝ) : ℂ))))
      (fun ω' => Complex.exp (Complex.I * (h ω' (c • φ) : ℂ))) (pastTwo κ b jumps θ₀ t₀ θ r E)
    filter_upwards [hlaw (c • φ), hsm, hAD, hloc.2.1] with ω hlω hsmω hADω hAc hω
    obtain ⟨hωG, hωS⟩ := hω
    obtain ⟨hDA, hDo⟩ := hADω hωG
    have hS' : tsupport ⇑(c • φ) ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom :=
      (WholeField.tsupport_smul_testOn_subset c φ).trans hωS
    have hdomH : ((stopChart κ b jumps θ₀ t₀ θ r E ω).dom : Set ℂ) ⊆ H := fun z hz => (hDA hz).1
    have hcov : QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ =
        QuantumZipper.zeroGFFTestCov ((stopChart κ b jumps θ₀ t₀ θ r E ω).dom : Set ℂ) φ φ :=
      zeroGFFTestCov_eq_of_isClopen hAc.2 sdiff_subset (stopChart κ b jumps θ₀ t₀ θ r E ω).dom.isOpen hDA hDo φ
        hωS
    have hcov' := zeroGFFTestCov_smul_self (stopChart κ b jumps θ₀ t₀ θ r E ω).dom.isOpen hdomH c φ
    rw [hfun, hsmω, Pi.smul_apply, smul_eq_mul, hlω hωG hS', WholeField.integral_mul_smul, hcov', hcov, hm]
    rw [← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the mean, recovered as a function of the records
  set ψ : ℕ → Ω → ℂ := fun n => P[fun ω' => Complex.exp (Complex.I *
      ((1 / ((n : ℝ) + 1) * WholeField.centredField h u₀ ω' φ : ℝ) : ℂ)) | pastTwo κ b jumps θ₀ t₀ θ r E]
    with hψ_def
  have hψm : ∀ n, StronglyMeasurable[pastTwo κ b jumps θ₀ t₀ θ r E] (ψ n) := fun n => stronglyMeasurable_condExp
  have hmm : Measurable[pastTwo κ b jumps θ₀ t₀ θ r E] (WholeField.meanOfCharFun ψ) :=
    WholeField.measurable_meanOfCharFun hψm
  have hmeq : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E ∩
      {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom} → WholeField.meanOfCharFun ψ ω = m ω := by
    filter_upwards [ae_all_iff.2 fun n : ℕ => hfreq (1 / ((n : ℝ) + 1))] with ω hω hωG
    exact WholeField.meanOfCharFun_eq fun n => hω n hωG
  have hkern : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E ∩
      {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom} →
      (P[fun ω' => Complex.exp (Complex.I * ((c * WholeField.centredField h u₀ ω' φ : ℝ) : ℂ)) |
        pastTwo κ b jumps θ₀ t₀ θ r E]) ω =
        Complex.exp (Complex.I * ((c * WholeField.meanOfCharFun ψ ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * QuantumZipper.zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c
    filter_upwards [hfreq c, hmeq] with ω h1 h2 hωG
    rw [h2 hωG]
    exact h1 hωG
  obtain ⟨k1, -⟩ := WholeField.ae_condExp_germSigma_history_eq hh0 hA h𝓗 hmark hloc.2.1 φ hG hmm hkern
  have e := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hh0 hA hloc h𝓗 hmark hg φ
  filter_upwards [k1, e, hmeq] with ω h1 h2 h3 hωG hωS
  rw [h2, h1 ⟨hωG, hωS⟩, h3 ⟨hωG, hωS⟩, hm]

end StripSideHeightProb

end Sec7

end InteractingSLE
