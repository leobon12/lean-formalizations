/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MxCore
import InteractingSLE.Spec.Supplement.GW2KModTransfer

/-!
# Gluing conditional laws over a random stage index

Packet PROVE-SB2-LCMEAN, round 14 (item 4: gluing over the offset). The relative stage `j` of `EL` lifts B's stage
`j + relOff`, a random index. The `P`-level induction produces conditional laws given the marks `𝓜 n` of each fixed
B-stage `n`. Given a random index `N` whose events `{N = n}` are known to `𝓜 n`, the **stopped σ-algebra**
`{A | ∀ n, A ∩ {N = n} ∈ 𝓜 n}` has the same trace as `𝓜 n` on `{N = n}`, so its regular conditional laws are those of
`𝓜 n` there (`GW2KMod.ae_condExpKernel_eq_of_trace`), and per-stage laws glue into one law given it:

* `stopSigma`, `stopSigma_le`, `measurableSet_stopSigma_eq`, `measurableSet_inter_stopSigma_iff`, `le_stopSigma`,
  `measurable_stopSigma_glue`, `measurable_stopIdx`, `measurable_glue`;
* **`ae_condExpKernel_stopSigma_eq`**: on `{N = n}` the kernels given the stopped σ-algebra and given `𝓜 n` agree;
* **`ae_isGFF_stopSigma`**: per-stage conditional GFF laws glue into the conditional law of the glued field.

All statements are standard measure theory (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.SB.Mx

open Restart Exist Exist.StagedLaw

section Stop

variable {Ω : Type*}

/-- **The σ-algebra of the family `𝓜` stopped at the random index `N`** (the events of `{N = n}` known to `𝓜 n`). -/
abbrev stopSigma (𝓜 : ℕ → MeasurableSpace Ω) (N : Ω → ℕ) (hN : ∀ n, MeasurableSet[𝓜 n] {ω | N ω = n}) :
    MeasurableSpace Ω where
  MeasurableSet' A := ∀ n, MeasurableSet[𝓜 n] (A ∩ {ω | N ω = n})
  measurableSet_empty n := by
    rw [empty_inter]
    exact @MeasurableSet.empty Ω (𝓜 n)
  measurableSet_compl A hA n := by
    have e : Aᶜ ∩ {ω | N ω = n} = {ω | N ω = n} \ (A ∩ {ω | N ω = n}) := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_ofPred_eq]
      tauto
    rw [e]
    exact (hN n).diff (hA n)
  measurableSet_iUnion f hf n := by
    rw [iUnion_inter]
    exact MeasurableSet.iUnion fun i => hf i n

variable {𝓜 : ℕ → MeasurableSpace Ω} {N : Ω → ℕ} {hN : ∀ n, MeasurableSet[𝓜 n] {ω | N ω = n}}

theorem measurableSet_stopSigma_iff {A : Set Ω} :
    MeasurableSet[stopSigma 𝓜 N hN] A ↔ ∀ n, MeasurableSet[𝓜 n] (A ∩ {ω | N ω = n}) := Iff.rfl

theorem stopSigma_le [mΩ : MeasurableSpace Ω] (h𝓜 : ∀ n, 𝓜 n ≤ mΩ) : stopSigma 𝓜 N hN ≤ mΩ := by
  intro A hA
  have e : A = ⋃ n, A ∩ {ω | N ω = n} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_and_left, exists_eq', and_true]
  rw [e]
  exact MeasurableSet.iUnion fun n => h𝓜 n _ (hA n)

theorem measurableSet_stopSigma_eq (n : ℕ) : MeasurableSet[stopSigma 𝓜 N hN] {ω | N ω = n} := by
  intro n'
  by_cases h : n' = n
  · subst h
    rw [inter_self]
    exact hN n'
  · have e : {ω | N ω = n} ∩ {ω | N ω = n'} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact h (h2.symm.trans h1)
    rw [e]
    exact @MeasurableSet.empty Ω (𝓜 n')

/-- **On `{N = n}`, the stopped σ-algebra and `𝓜 n` have the same trace.** -/
theorem measurableSet_inter_stopSigma_iff (n : ℕ) (t : Set Ω) :
    MeasurableSet[stopSigma 𝓜 N hN] ({ω | N ω = n} ∩ t) ↔ MeasurableSet[𝓜 n] ({ω | N ω = n} ∩ t) := by
  constructor
  · intro h
    have := h n
    rwa [inter_comm, ← inter_assoc, inter_self] at this
  · intro h n'
    by_cases hn : n' = n
    · subst hn
      rwa [inter_comm, ← inter_assoc, inter_self]
    · have e : {ω | N ω = n} ∩ t ∩ {ω | N ω = n'} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        rintro ⟨h1, -⟩ h2
        exact hn (h2.symm.trans h1)
      rw [e]
      exact @MeasurableSet.empty Ω (𝓜 n')

theorem le_stopSigma {ℋ : MeasurableSpace Ω} (h : ∀ n, ℋ ≤ 𝓜 n) : ℋ ≤ stopSigma 𝓜 N hN :=
  fun _ hA n => (h n _ hA).inter (hN n)

/-- A family measurable for each `𝓜 n`, glued along `N`, is measurable for the stopped σ-algebra. -/
theorem measurable_stopSigma_glue {β : Type*} [MeasurableSpace β] {f : ℕ → Ω → β}
    (hf : ∀ n, Measurable[𝓜 n] (f n)) : Measurable[stopSigma 𝓜 N hN] (fun ω => f (N ω) ω) := by
  intro s hs n
  have e : (fun ω => f (N ω) ω) ⁻¹' s ∩ {ω | N ω = n} = f n ⁻¹' s ∩ {ω | N ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [h2] at h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h2]; exact h1, h2⟩
  rw [e]
  exact (hf n hs).inter (hN n)

theorem measurable_stopIdx : Measurable[stopSigma 𝓜 N hN] N :=
  measurable_stopSigma_glue (f := fun n _ => n) fun _ => measurable_const

/-- A family of measurable maps glued along a measurable index is measurable. -/
theorem measurable_glue [MeasurableSpace Ω] {β : Type*} [MeasurableSpace β] {f : ℕ → Ω → β}
    (hf : ∀ n, Measurable (f n)) {N : Ω → ℕ} (hNm : Measurable N) : Measurable (fun ω => f (N ω) ω) := by
  intro s hs
  have e : (fun ω => f (N ω) ω) ⁻¹' s = ⋃ n, f n ⁻¹' s ∩ N ⁻¹' {n} := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro h
      exact ⟨N ω, h, rfl⟩
    · rintro ⟨n, h1, h2⟩
      rw [h2]
      exact h1
  rw [e]
  exact MeasurableSet.iUnion fun n => (hf n hs).inter (hNm (measurableSet_singleton n))

end Stop

section Kernel

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓜 : ℕ → MeasurableSpace Ω} {N : Ω → ℕ} {hN : ∀ n, MeasurableSet[𝓜 n] {ω | N ω = n}}

/-- **On `{N = n}` the regular conditional laws given the stopped σ-algebra and given `𝓜 n` agree.** -/
theorem ae_condExpKernel_stopSigma_eq (h𝓜 : ∀ n, 𝓜 n ≤ mΩ) (n : ℕ) :
    ∀ᵐ ω ∂μ, N ω = n → condExpKernel μ (stopSigma 𝓜 N hN) ω = condExpKernel μ (𝓜 n) ω :=
  GW2KMod.ae_condExpKernel_eq_of_trace (stopSigma_le h𝓜) (h𝓜 n) (measurableSet_stopSigma_eq n)
    (measurableSet_inter_stopSigma_iff n)

/-- **Per-stage conditional GFF laws glue** into the conditional law of the glued field given the stopped σ-algebra. -/
theorem ae_isGFF_stopSigma (h𝓜 : ∀ n, 𝓜 n ≤ mΩ) {G : ℕ → Set Ω} {Z : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hZ : ∀ n, Measurable (Z n)) {c : ℕ → Ω → BoundaryWord}
    (hlaw : ∀ n, ∀ᵐ ω₁ ∂μ, ω₁ ∈ G n → N ω₁ = n →
      IsGFFWithBoundaryData (condExpKernel μ (𝓜 n) ω₁) (Z n) (c n ω₁).fn (c n ω₁).jumps) :
    ∀ᵐ ω₁ ∂μ, ω₁ ∈ G (N ω₁) → IsGFFWithBoundaryData (condExpKernel μ (stopSigma 𝓜 N hN) ω₁)
      (fun ω => Z (N ω) ω) (c (N ω₁) ω₁).fn (c (N ω₁) ω₁).jumps := by
  have hNm : Measurable N := (measurable_stopIdx (hN := hN)).mono (stopSigma_le h𝓜) le_rfl
  filter_upwards [ae_all_iff.2 hlaw, ae_all_iff.2 fun n => ae_condExpKernel_stopSigma_eq (μ := μ) (hN := hN) h𝓜 n,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := μ) (stopSigma_le h𝓜) (measurable_stopIdx (hN := hN))]
    with ω₁ hl hk hN₁ hG
  have hk' := hk (N ω₁) rfl
  rw [hk']
  have hlaw₁ := hl (N ω₁) hG rfl
  refine isGFFWithBoundaryData_congr_ae hlaw₁ (measurable_glue hZ hNm) ?_
  rw [← hk']
  filter_upwards [hN₁] with ω hω
  simp only [hω]

end Kernel

end InteractingSLE.Theorem14.SB.Mx
