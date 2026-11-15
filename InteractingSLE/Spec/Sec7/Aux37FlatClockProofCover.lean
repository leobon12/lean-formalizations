/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofGauss
import InteractingSLE.Spec.Sec6.Aux27Germ
import InteractingSLE.GFF.LocalSets.UnionLaw
import InteractingSLE.Spec.Coupling.WholeFieldMarked

/-!
# Aux. lemma 37's flat clock, part 2: nested history-marked local sets

Packet PROVE-FLATCLOCK. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L84–L95, p. 198), at two
deterministic times. PROVE-STRIPSYS43 (§5.3) identified the missing piece: a *nested* Proposition 3.9 for local sets
`A₁ ⊆ A₂` of one exploration. It is proved here, for history-marked local sets whose marks increase and record the
smaller set:

**Theorem** (`IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq`). Let `A₁ ⊆ A₂` (almost surely) be history-marked local
sets of a zero-boundary GFF `h` with marks `ℋ₁ ≤ ℋ₂`, `A₁` recorded by `σ(A₂) ∨ ℋ₂` up to null sets, and `g₁`, `g₂`
versions of their means. For every test function `φ`, almost surely, `σ²_{ℍ∖A₁}(φ) = σ²_{ℍ∖A₂}(φ)` implies
`g₁(φ) = g₂(φ)`.

**Proof.** Conditionally on `𝒦₁ = 𝒜₁ ∨ σ(A₁) ∨ ℋ₁` (`𝒜₁` the germ σ-algebra of `A₁`) the pairing `h(φ)` is Gaussian
with mean `g₁(φ)` and variance `σ²_{ℍ∖A₁}(φ)` (Aux. lemma 18 with the history retained: the landed cover argument,
`LocalSets.exists_condExp_germSigmaK`). The same holds for `A₂` given the larger σ-algebra
`𝒦₂ = ⋂_j aeσ(𝒢_j(A₂))`, the intersection of the cover σ-algebras of `A₂` up to null sets (`exists_condExp_germSigmaK`
allows every `𝒦` between `𝒜₂` and all the `𝒢_j(A₂)`). The germ of the smaller set lies in every cover σ-algebra of the
larger one (`germSigma_le_aeSigma_of_ae_subset`, the almost sure form of `LocalSets.germSigma_le_aeSigma_of_subset`),
so `𝒦₁ ≤ 𝒦₂`, and the two-level lemma `IsCondGaussian.ae_mean_eq_of_var_eq` concludes. Neither conditional
independence of `A₁` and `A₂` (Proposition 3.9) nor stopping times are used.

* `aeSigma_mono`, `measurableSet_aeSigma_of_ae_eq`: the null-set completion of a σ-algebra;
* `germSigma_le_aeSigma_of_ae_subset`;
* `isCondGaussian_of_cover`: the conditional Gaussian law of `h(φ)` given any `𝒦` between the germ σ-algebra and the
  cover σ-algebras, with the mean of an arbitrary version `g` of the local-set mean;
* `ae_apply_eq_of_coverMarking`: the same with general cover marking data;
* **`IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq`**.

No Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped ENNReal NNReal

namespace InteractingSLE.Sec7.FlatClockProof

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF measurable_distOn_apply)
open LocalSets Sec6.Prop65

/-! ### Completion by null sets -/

section AeSigma

variable {Ω : Type*} {m m' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem aeSigma_mono (hmm' : m ≤ m') : aeSigma m P ≤ aeSigma m' P :=
  fun _ ⟨G', hG', he⟩ => ⟨G', hmm' _ hG', he⟩

theorem measurableSet_aeSigma_of_ae_eq {G G' : Set Ω} (he : G =ᵐ[P] G')
    (hG' : MeasurableSet[aeSigma m P] G') : MeasurableSet[aeSigma m P] G := by
  obtain ⟨G'', hG'', he'⟩ := hG'
  exact ⟨G'', hG'', he.trans he'⟩

end AeSigma

/-! ### The germ of a smaller set in the cover σ-algebras of a larger one -/

section Germ

variable {Ω : Type u} {𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The germ σ-algebra of an almost surely smaller set `A' ⊆ A` recorded (up to null sets) in `𝒦` lies in every
cover σ-algebra of `A` up to null sets** (the almost sure form of `LocalSets.germSigma_le_aeSigma_of_subset`). -/
theorem germSigma_le_aeSigma_of_ae_subset {A A' : Ω → Set ℂ}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA𝒦 : MeasurableSpace.comap A hittingSigma ≤ 𝒦)
    (hA'𝒦 : MeasurableSpace.comap A' hittingSigma ≤ aeSigma 𝒦 P)
    (hA'A : ∀ᵐ ω ∂P, A' ω ⊆ A ω) (j : ℕ) : germSigma A' h ≤ aeSigma (coverSigmaM 𝒦 j A h) P := by
  intro G hG
  have hG' := measurableSet_germSigmaAt_coverRad hG j
  have hM : aeSigma 𝒦 P ≤ aeSigma (coverSigmaM 𝒦 j A h) P :=
    aeSigma_mono (le_sup_left : 𝒦 ≤ coverSigmaM 𝒦 j A h)
  refine (sup_le (hA'𝒦.trans hM) (MeasurableSpace.generateFrom_le ?_) :
    germSigmaAt A' h (coverRad j) ≤ _) G hG'
  rintro _ ⟨φ, B, hB, rfl⟩
  have e : ({ω | tsupport φ ⊆ germNbhd (coverRad j) (A' ω)} ∩ (fun ω => h ω φ) ⁻¹' B : Set Ω) =ᵐ[P]
      ({ω | tsupport φ ⊆ germNbhd (coverRad j) (A' ω)} ∩
        ({ω | tsupport φ ⊆ germNbhd (coverRad j) (A ω)} ∩ (fun ω => h ω φ) ⁻¹' B) : Set Ω) := by
    filter_upwards [hA'A] with ω hω
    refine propext ?_
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h1.trans (germNbhd_mono_set hω), h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  refine measurableSet_aeSigma_of_ae_eq e (MeasurableSet.inter (hA'𝒦.trans hM _ ⟨_,
    measurableSet_subset_germNbhd φ.hasCompactSupport φ.tsupport_subset (coverRad_pos j), rfl⟩) ?_)
  exact germSigmaAt_le_aeSigmaM hh hA𝒦 j _ (le_sup_right (a := MeasurableSpace.comap A hittingSigma) _
    (MeasurableSpace.measurableSet_generateFrom ⟨φ, B, hB, rfl⟩))

end Germ

/-! ### The conditional Gaussian law between the germ and the cover σ-algebras -/

section Law

variable {Ω : Type u} {ℳ 𝒦 : MeasurableSpace Ω} {𝒮 : Set ℂ → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The conditional Gaussian law of `h(φ)` given `𝒦`**, for every `𝒦` between the germ σ-algebra of `A` and (up to
null sets) all cover σ-algebras of `A` with marking data `ℳ`: mean `g(φ)` for any version `g` of the local-set mean,
variance `σ²_{ℍ∖A}(φ)`, bounded by `σ²_ℍ(φ)`. -/
theorem isCondGaussian_of_cover (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) (hmk : IsCoverMarking A h P ℳ 𝒮)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (h𝒦A : germSigma A h ≤ 𝒦) (hle : 𝒦 ≤ mΩ)
    (h𝒦tr : ∀ j, 𝒦 ≤ aeSigma (coverSigmaM ℳ j A h) P) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A h P g) (φ : TestOn upperHalfPlaneOpens) :
    IsCondGaussian 𝒦 P (fun ω => h ω φ) (fun ω => g ω φ)
      (fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) (zeroGFFTestCov H φ φ) := by
  have hhm := hh.measurable
  have hgerm := germSigma_le hA hhm
  -- the conditional characteristic function given `𝒦`, with the mean of the version `g`
  have hmean : ∀ ψ : TestOn upperHalfPlaneOpens, ∃ M : Ω → ℝ, (fun ω => g ω ψ) =ᵐ[P] M ∧
      (fun ω => cexp (I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) ψ ψ) : ℝ) : ℂ)) =ᵐ[P]
        P[fun ω => cexp (I * (h ω ψ : ℂ)) | 𝒦] := by
    intro ψ
    obtain ⟨M, hMm, -, hM1, hM2⟩ := exists_condExp_germSigmaK hh hA hmk hAc h𝒦A hle h𝒦tr ψ
    have hψi : Integrable (fun ω => h ω ψ) P :=
      (hh.process.gaussian.hasGaussianLaw_eval ψ).memLp_two.integrable one_le_two
    have hMi : Integrable M P := integrable_condExp.congr hM1.symm
    have e1 : P[P[fun ω => h ω ψ | 𝒦] | germSigma A h] =ᵐ[P] P[fun ω => h ω ψ | germSigma A h] :=
      condExp_condExp_of_le h𝒦A hle
    have e2 : P[P[fun ω => h ω ψ | 𝒦] | germSigma A h] =ᵐ[P] P[M | germSigma A h] :=
      condExp_congr_ae hM1.symm
    rw [condExp_of_stronglyMeasurable hgerm hMm.stronglyMeasurable hMi] at e2
    have hg' := Sec6.IsLocalSetMean.ae_eq_condExp hA hhm hg (hAc.mono fun ω hω => hω.2) ψ hψi
    exact ⟨M, hg'.trans (e1.symm.trans e2), hM2⟩
  refine ⟨hle, (measurable_distOn_apply φ).comp hhm,
    ((measurable_distOn_apply φ).comp hg.1).mono h𝒦A le_rfl, ?_, fun ω => ?_, fun ω => ?_, fun t => ?_⟩
  · exact (measurable_comap_zeroGFFTestCov_compl A φ φ).mono ((comap_le_germSigma A h).trans h𝒦A) le_rfl
  · exact zeroGFFTestCov_self_nonneg (isOpen_H_diff_relClosureH _) sdiff_subset φ
  · exact zeroGFFTestCov_mono (isOpen_H_diff_relClosureH _) QuantumZipper.isOpen_H sdiff_subset subset_rfl φ
  · obtain ⟨M, hgM, hM⟩ := hmean (t • φ)
    have e : (fun ω => cexp (I * ((t * h ω φ : ℝ) : ℂ))) = fun ω => cexp (I * (h ω (t • φ) : ℂ)) := by
      funext ω
      rw [map_smul, smul_eq_mul]
    rw [e]
    filter_upwards [hgM, hM] with ω h1 h2
    rw [← h2, ← h1, map_smul, smul_eq_mul,
      zeroGFFTestCov_smul_self (isOpen_H_diff_relClosureH _) sdiff_subset t φ]

end Law

/-! ### Nested history-marked local sets -/

section Nested

variable {Ω : Type u} {ℋ₁ ℋ₂ ℳ₁ ℳ₂ : MeasurableSpace Ω} {𝒮₁ 𝒮₂ : Set ℂ → MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Nested local sets with cover marking data**: for `A₁ ⊆ A₂` (almost surely) with marking data `ℳ₁`, `ℳ₂`, `σ(A₂)`
recorded in `ℳ₂` and `ℳ₁` recorded in `ℳ₂` up to null sets, almost surely equal variances force equal means. -/
theorem ae_apply_eq_of_coverMarking (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A₁ A₂ : Ω → Set ℂ} (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hmk₁ : IsCoverMarking A₁ h P ℳ₁ 𝒮₁) (hmk₂ : IsCoverMarking A₂ h P ℳ₂ 𝒮₂)
    (hAc₁ : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) (hAc₂ : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hsub : ∀ᵐ ω ∂P, A₁ ω ⊆ A₂ ω) (hℳ₁₂ : ℳ₁ ≤ aeSigma ℳ₂ P)
    {g₁ g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₁ : IsLocalSetMean A₁ h P g₁) (hg₂ : IsLocalSetMean A₂ h P g₂)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, zeroGFFTestCov (H \ A₁ ω) φ φ = zeroGFFTestCov (H \ A₂ ω) φ φ → g₁ ω φ = g₂ ω φ := by
  have hhm := hh.measurable
  -- level 1: `𝒦₁ = 𝒜₁ ∨ ℳ₁`
  have htr₁ : ∀ j, germSigma A₁ h ⊔ ℳ₁ ≤ aeSigma (coverSigmaM ℳ₁ j A₁ h) P := fun j =>
    sup_le (fun G hG => germSigmaAt_le_aeSigmaM hh hmk₁.comap_le j G (measurableSet_germSigmaAt_coverRad hG j))
      ((le_sup_left : ℳ₁ ≤ coverSigmaM ℳ₁ j A₁ h).trans (le_aeSigma _ P))
  have G₁ := isCondGaussian_of_cover hh hA₁ hmk₁ hAc₁ le_sup_left (sup_le (germSigma_le hA₁ hhm) hmk₁.le) htr₁
    hg₁ φ
  -- level 2: `𝒦₂ = ⋂_j aeσ(𝒢_j(A₂))`
  have hgerm₂ : germSigma A₂ h ≤ mΩ ⊓ ⨅ j : ℕ, aeSigma (coverSigmaM ℳ₂ j A₂ h) P :=
    le_inf (germSigma_le hA₂ hhm) (le_iInf fun j G hG =>
      germSigmaAt_le_aeSigmaM hh hmk₂.comap_le j G (measurableSet_germSigmaAt_coverRad hG j))
  have G₂ := isCondGaussian_of_cover hh hA₂ hmk₂ hAc₂ hgerm₂ inf_le_left
    (fun j => inf_le_right.trans (iInf_le _ j)) hg₂ φ
  -- `𝒦₁ ≤ 𝒦₂`
  have h12 : germSigma A₁ h ⊔ ℳ₁ ≤ mΩ ⊓ ⨅ j : ℕ, aeSigma (coverSigmaM ℳ₂ j A₂ h) P := by
    refine le_inf (sup_le (germSigma_le hA₁ hhm) hmk₁.le) (le_iInf fun j => sup_le ?_ ?_)
    · exact germSigma_le_aeSigma_of_ae_subset hh hmk₂.comap_le (hmk₁.comap_le.trans hℳ₁₂) hsub j
    · exact hℳ₁₂.trans (aeSigma_mono (le_sup_left : ℳ₂ ≤ coverSigmaM ℳ₂ j A₂ h))
  filter_upwards [IsCondGaussian.ae_mean_eq_of_var_eq h12 G₁ G₂, hAc₁, hAc₂] with ω hω h1 h2 hv
  refine hω ?_
  rw [relClosureH_eq h1.1 h1.2, relClosureH_eq h2.1 h2.2]
  exact hv

/-- **Nested history-marked local sets: the flat clock at two deterministic levels.** For history-marked local sets
`A₁ ⊆ A₂` (almost surely) of a zero-boundary GFF with marks `ℋ₁ ≤ ℋ₂`, `A₁` recorded by `σ(A₂) ∨ ℋ₂` up to null sets,
and versions `g₁`, `g₂` of their means: almost surely, if `φ` has the same variance in `ℍ ∖ A₁` and in `ℍ ∖ A₂`, then
`g₁(φ) = g₂(φ)`. -/
theorem IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A₁ A₂ : Ω → Set ℂ} (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hℋ₁ : ℋ₁ ≤ mΩ) (hℋ₂ : ℋ₂ ≤ mΩ) (hℋ : ℋ₁ ≤ ℋ₂)
    (hloc₁ : WholeField.IsHistoryAvoidanceLocal ℋ₁ A₁ h P) (hloc₂ : WholeField.IsHistoryAvoidanceLocal ℋ₂ A₂ h P)
    (hAc₁ : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) (hAc₂ : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hsub : ∀ᵐ ω ∂P, A₁ ω ⊆ A₂ ω)
    (hA₁ℋ : MeasurableSpace.comap A₁ hittingSigma ≤ aeSigma (MeasurableSpace.comap A₂ hittingSigma ⊔ ℋ₂) P)
    {g₁ g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₁ : IsLocalSetMean A₁ h P g₁) (hg₂ : IsLocalSetMean A₂ h P g₂)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, zeroGFFTestCov (H \ A₁ ω) φ φ = zeroGFFTestCov (H \ A₂ ω) φ φ → g₁ ω φ = g₂ ω φ :=
  ae_apply_eq_of_coverMarking hh hA₁ hA₂ (WholeField.isCoverMarking_history hh hA₁ hℋ₁ hloc₁)
    (WholeField.isCoverMarking_history hh hA₂ hℋ₂ hloc₂) hAc₁ hAc₂ hsub
    (sup_le hA₁ℋ (hℋ.trans ((le_sup_right : ℋ₂ ≤ MeasurableSpace.comap A₂ hittingSigma ⊔ ℋ₂).trans
      (le_aeSigma _ P)))) hg₁ hg₂ φ

end Nested

end InteractingSLE.Sec7.FlatClockProof
