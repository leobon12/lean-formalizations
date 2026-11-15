/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# The tower property of regular conditional kernels

Packet PROVE-T14-BR6. For sub-σ-algebras `m ≤ m' ≤ mΩ` of a standard Borel space and a finite measure `P`, the regular
conditional kernels `condExpKernel P m` and `condExpKernel P m'` satisfy the tower property: for every measurable `A`,
almost surely, `κ_m(ω)(A) = ∫ κ_{m'}(x)(A) dκ_m(ω)(x)` (`ae_condExpKernel_eq_lintegral`). Consequently an event that
holds almost surely under almost every conditional law given `m'`, when these are sampled from a conditional law given
`m`, holds almost surely under that conditional law (`ae_ae_of_ae_ae_condExpKernel`). Lemma GW1 uses this when it says
"auxiliary stage encodings may be forgotten by the tower property" (supplement p. 620) and GW2a when it chains the
conditional pairs of successive launches.

* `setLIntegral_condExpKernel`: `∫⁻ ω in C, κ_m(ω)(A) ∂P = P (C ∩ A)` for `C ∈ m` (Mathlib's
  `compProd_trim_condExpKernel`);
* `lintegral_lintegral_condExpKernel`: `∫⁻ ω, ∫⁻ x, G x ∂κ_m(ω) ∂P = ∫⁻ G ∂P` (`condExpKernel_comp_trim`);
* `ae_condExpKernel_compl_eq_zero`: the kernel lives on the side of an `m`-event containing the sample;
* **`ae_condExpKernel_eq_lintegral`**, **`ae_ae_of_ae_ae_condExpKernel`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace InteractingSLE

namespace KernelTower

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P]

/-- **The defining property of the regular conditional kernel**: on an event `C` of `m`, the integral of the
conditional probability of `A` is `P (C ∩ A)`. -/
theorem setLIntegral_condExpKernel (hm : m ≤ mΩ) {C : Set Ω} (hC : MeasurableSet[m] C) {A : Set Ω}
    (hA : MeasurableSet A) : ∫⁻ ω in C, condExpKernel P m ω A ∂P = P (C ∩ A) := by
  have hf : Measurable[m] fun ω => condExpKernel P m ω A := measurable_condExpKernel hA
  rw [← setLIntegral_trim hm hf hC, ← Measure.compProd_apply_prod hC hA, compProd_trim_condExpKernel hm,
    Measure.map_apply (f := Function.diag) ((measurable_id'' hm).prodMk measurable_id) (hC.prod hA)]
  rfl

/-- Integrating the conditional law against `P` gives back `P`. -/
theorem lintegral_lintegral_condExpKernel (hm : m ≤ mΩ) {G : Ω → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, ∫⁻ x, G x ∂(condExpKernel P m ω) ∂P = ∫⁻ x, G x ∂P := by
  have hf : Measurable[m] fun ω => ∫⁻ x, G x ∂(condExpKernel P m ω) := hG.lintegral_kernel
  rw [← lintegral_trim hm hf]
  conv_rhs => rw [← condExpKernel_comp_trim (μ := P) hm]
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hG.aemeasurable]

/-- The conditional kernel lives on the side of a conditioning event that contains the sample. -/
theorem ae_condExpKernel_compl_eq_zero (hm : m ≤ mΩ) {C : Set Ω} (hC : MeasurableSet[m] C) :
    ∀ᵐ ω ∂P, (ω ∈ C → condExpKernel P m ω Cᶜ = 0) ∧ (ω ∉ C → condExpKernel P m ω C = 0) := by
  have hCΩ : MeasurableSet C := hm _ hC
  have hfC : Measurable fun ω => condExpKernel P m ω C := (measurable_condExpKernel hCΩ).mono hm le_rfl
  have hfCc : Measurable fun ω => condExpKernel P m ω Cᶜ := (measurable_condExpKernel hCΩ.compl).mono hm le_rfl
  have h1 : ∫⁻ ω in C, condExpKernel P m ω Cᶜ ∂P = 0 := by
    rw [setLIntegral_condExpKernel hm hC hCΩ.compl, inter_compl_self, measure_empty]
  have h2 : ∫⁻ ω in Cᶜ, condExpKernel P m ω C ∂P = 0 := by
    rw [setLIntegral_condExpKernel hm hC.compl hCΩ, compl_inter_self, measure_empty]
  rw [lintegral_eq_zero_iff hfCc, EventuallyEq, ae_restrict_iff' hCΩ] at h1
  rw [lintegral_eq_zero_iff hfC, EventuallyEq, ae_restrict_iff' hCΩ.compl] at h2
  filter_upwards [h1, h2] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **Tower property of regular conditional kernels**: for `m ≤ m'`, the conditional probability given `m` is the
average, under the conditional law given `m`, of the conditional probability given `m'`. -/
theorem ae_condExpKernel_eq_lintegral (hm : m ≤ m') (hm' : m' ≤ mΩ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂P, condExpKernel P m ω A = ∫⁻ x, condExpKernel P m' x A ∂(condExpKernel P m ω) := by
  have hmΩ : m ≤ mΩ := hm.trans hm'
  have hf : Measurable[m] fun ω => condExpKernel P m ω A := measurable_condExpKernel hA
  have hF : Measurable fun x => condExpKernel P m' x A := (measurable_condExpKernel hA).mono hm' le_rfl
  have hg : Measurable[m] fun ω => ∫⁻ x, condExpKernel P m' x A ∂(condExpKernel P m ω) := hF.lintegral_kernel
  refine ae_of_ae_trim hmΩ ?_
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hf hg fun C hC _ => ?_
  have hCΩ : MeasurableSet C := hmΩ _ hC
  rw [setLIntegral_trim hmΩ hf hC, setLIntegral_trim hmΩ hg hC, setLIntegral_condExpKernel hmΩ hC hA]
  have h1 : ∀ᵐ ω ∂P, C.indicator (fun ω => ∫⁻ x, condExpKernel P m' x A ∂(condExpKernel P m ω)) ω =
      ∫⁻ x, C.indicator (fun x => condExpKernel P m' x A) x ∂(condExpKernel P m ω) := by
    filter_upwards [ae_condExpKernel_compl_eq_zero hmΩ hC] with ω hω
    by_cases hωC : ω ∈ C
    · rw [indicator_of_mem hωC]
      refine lintegral_congr_ae ?_
      have : ∀ᵐ x ∂(condExpKernel P m ω), x ∈ C := by
        rw [ae_iff]
        exact hω.1 hωC
      filter_upwards [this] with x hx
      rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hωC]
      symm
      rw [lintegral_eq_zero_iff (hF.indicator hCΩ)]
      have : ∀ᵐ x ∂(condExpKernel P m ω), x ∉ C := by
        rw [ae_iff]
        simpa only [not_not, ofPred_mem_eq] using hω.2 hωC
      filter_upwards [this] with x hx
      rw [indicator_of_notMem hx]
      rfl
  rw [← lintegral_indicator hCΩ, lintegral_congr_ae h1,
    lintegral_lintegral_condExpKernel hmΩ (hF.indicator hCΩ), lintegral_indicator hCΩ,
    setLIntegral_condExpKernel hm' (hm _ hC) hA]

/-- **Tower property, almost-sure form**: if under the conditional law given `m` almost every sample has `A` almost
surely under its conditional law given `m' ≥ m`, then `A` holds almost surely under the conditional law given `m`. -/
theorem ae_ae_of_ae_ae_condExpKernel (hm : m ≤ m') (hm' : m' ≤ mΩ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂P, (∀ᵐ x ∂(condExpKernel P m ω), ∀ᵐ y ∂(condExpKernel P m' x), y ∈ A) →
      ∀ᵐ y ∂(condExpKernel P m ω), y ∈ A := by
  filter_upwards [ae_condExpKernel_eq_lintegral hm hm' hA.compl] with ω hω h
  rw [ae_iff]
  change condExpKernel P m ω Aᶜ = 0
  rw [hω]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with x hx
  exact ae_iff.1 hx

/-- **A `P`-almost-sure property holds almost surely under almost every conditional law** (no measurability needed). -/
theorem ae_ae_condExpKernel_of_ae (hm : m ≤ mΩ) {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(condExpKernel P m ω), p x := by
  have h' : ∀ᵐ x ∂(condExpKernel P m ∘ₘ P.trim hm), p x := by
    rw [condExpKernel_comp_trim hm]
    exact h
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp h')

/-- **Chaining conditional data along an increasing family of σ-algebras** (downward induction with the tower
property). Let `𝒢 0 ≤ 𝒢 1 ≤ ⋯` and let `D j` be a property of the sample at stage `j` (for instance "the conditional
counterflow pair is available at the `j`-th launch"; it need not be measurable). If almost surely `D K` makes the
measurable event `A` almost sure under the conditional law given `𝒢 K`, and almost surely `D j` makes `D (j + 1)`
almost sure under the conditional law given `𝒢 j`, then for every `j ≤ K`, almost surely `D j` makes `A` almost sure
under the conditional law given `𝒢 j`. (The non-measurable `D j` are never integrated; only `A` is.) -/
theorem ae_ae_of_chain {𝒢 : ℕ → MeasurableSpace Ω} (hmono : ∀ j, 𝒢 j ≤ 𝒢 (j + 1)) (hle : ∀ j, 𝒢 j ≤ mΩ)
    {D : ℕ → Ω → Prop} {A : Set Ω} (hA : MeasurableSet A) (K : ℕ)
    (htop : ∀ᵐ ω ∂P, D K ω → ∀ᵐ x ∂(condExpKernel P (𝒢 K) ω), x ∈ A)
    (hstep : ∀ j < K, ∀ᵐ ω ∂P, D j ω → ∀ᵐ x ∂(condExpKernel P (𝒢 j) ω), D (j + 1) x) :
    ∀ j ≤ K, ∀ᵐ ω ∂P, D j ω → ∀ᵐ x ∂(condExpKernel P (𝒢 j) ω), x ∈ A := by
  suffices H : ∀ d j, j + d = K → ∀ᵐ ω ∂P, D j ω → ∀ᵐ x ∂(condExpKernel P (𝒢 j) ω), x ∈ A from
    fun j hj => H (K - j) j (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    have hjK : j = K := by omega
    subst hjK
    exact htop
  | succ d ih =>
    intro j hj
    have hnext := ae_ae_condExpKernel_of_ae (P := P) (hle j) (ih (j + 1) (by omega))
    filter_upwards [hstep j (by omega), hnext, ae_ae_of_ae_ae_condExpKernel (P := P) (hmono j) (hle (j + 1)) hA]
      with ω hs hn htw hD
    refine htw ?_
    filter_upwards [hs hD, hn] with x hx hnx
    exact hnx hx

end KernelTower

end InteractingSLE
