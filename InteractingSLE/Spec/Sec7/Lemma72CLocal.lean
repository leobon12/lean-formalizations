/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeFieldMarked
import InteractingSLE.GFF.LocalSets.GermVersion
import InteractingSLE.Spec.Sec7.LocalExtGLocal

/-!
# History-marked local sets: enlargement, the germ law with history, and conditional locality

Packet PROVE-LEMMA72C. Specification §7.1, proof of Lemma 7.1 (`source/spec/p193-240.md` L600–L602, pp. 224–225:
"For each bounded stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies to the
revealed outer curves and the middle prefix […] the optional history marking of the original coupling supplies the
required history locality") and §3.2 (Lemma 3.6, Aux. lemma 18).

Generic tools for the locality (L) of the mapped hulls and for the conditional pocket coupling of `Lemma72CMain`.
The pocket region `ψ⁻¹(ℍ ∖ K_τ)` is one complementary component of the explored set `E_τ = η_{θ₁} ∪ η_{θ₂} ∪ η[0, τ]`
of the three curves; its complement `B_τ = (ℍ ∖ C) ∪ ψ⁻¹(K_τ) ⊇ E_τ` is a function of the labeled histories. Lemma 6.2
with labels (`Sec6.isHistoryAvoidanceLocal_explored`) gives the history-marked avoidance criterion of `E_τ`; the tools
below pass it to `B_τ` and turn it into the conditional law of the field given the germ of `B_τ` and the histories:

* `isHistoryAvoidanceLocal_mono_set`: the history-marked avoidance criterion passes to every almost surely larger
  random set that is measurable for the marks (on the avoidance event of the larger set the smaller one avoids too);
* `exists_germLaw_of_isHistoryAvoidanceLocal` (Aux. lemma 18 with the history retained, in the form of Lemma 3.6 (iii)):
  there is a germ-measurable `h₁`, harmonic off `A`, such that `h − h₁` is a zero-boundary GFF on `ℍ ∖ A`
  conditionally on `𝒜 ∨ ℋ` (germs and marks);
* `isLocalSet_of_isCondZeroBoundaryGFF`: Lemma 3.6 (iii) ⇒ (iv) for **any** conditioning σ-algebra `𝒢` for which `A`
  and `h₁` are measurable;
* **`isLocalSet_cond_of_isHistoryAvoidanceLocal`**: a history-marked local set is local under `P[· | D]` for every event
  `D ∈ 𝒜 ∨ ℋ` (germs and marks) of positive probability (Aux. lemma 53's "forgetting that germ preserves locality",
  conditionally on a mark).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov)
open scoped ENNReal

universe u

namespace InteractingSLE.Sec7.Lemma72C

open LQGMetric LocalSets WholeField

/-! ### Enlarging a history-marked local set -/

section Mono

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The history-marked avoidance criterion passes to larger mark-measurable sets.** If `A` satisfies the criterion
for the marks `ℋ`, and `B ⊇ A` almost surely is `ℋ`-measurable (hitting σ-algebra), then `B` satisfies it: for an open
`U` and a mark `F`, `{B ∩ U = ∅} ∩ F = {A ∩ U = ∅} ∩ ({B ∩ U = ∅} ∩ F)` almost surely, and `{B ∩ U = ∅} ∩ F` is a
mark. -/
theorem isHistoryAvoidanceLocal_mono_set {A B : Ω → Set ℂ} (hloc : IsHistoryAvoidanceLocal ℋ A h P)
    (hB : Measurable[ℋ, hittingSigma] B) (hAB : ∀ᵐ ω ∂P, A ω ⊆ B ω) : IsHistoryAvoidanceLocal ℋ B h P := by
  intro U G hUH hG hd F hF
  have hE : MeasurableSet[ℋ] {ω | Disjoint (B ω) (U : Set ℂ)} := hB (measurableSet_avoid U.isOpen hUH)
  obtain ⟨g, hg, hgeq⟩ := hloc U G hUH hG hd ({ω | Disjoint (B ω) (U : Set ℂ)} ∩ F) (hE.inter hF)
  refine ⟨g, hg, Filter.EventuallyEq.trans ?_ hgeq⟩
  refine condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)
  filter_upwards [hAB] with ω hω
  apply propext
  simp only [mem_inter_iff, mem_ofPred_eq]
  exact ⟨fun h' => ⟨h'.1.mono_left hω, h'⟩, fun h' => h'.2⟩

end Mono

/-! ### The germ law with the history retained -/

section GermLaw

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}

/-- **Lemma 3.6 (iii) with the history retained** (Aux. lemma 18, second paragraph). For a zero-boundary GFF `h` on
`ℍ` and an almost surely relatively closed `A ⊆ ℍ` satisfying the history-marked avoidance criterion for the marks
`ℋ`, there is a germ-measurable random distribution `h₁`, almost surely harmonic on `ℍ ∖ A`, such that `h − h₁` is a
zero-boundary GFF on `ℍ ∖ A` conditionally on the germs and the marks `𝒜 ∨ ℋ`. (`h₁` is the germ version of Lemma
3.6; its pairings are the conditional means given `𝒜`, which are those given `𝒜 ∨ ℋ`.) -/
theorem exists_germLaw_of_isHistoryAvoidanceLocal (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsHistoryAvoidanceLocal ℋ A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) :
    ∃ h₁ : Ω → DistOn upperHalfPlaneOpens, Measurable[germSigma A h] h₁ ∧
      (∀ᵐ ω ∂P, IsHarmonicDistOn (h₁ ω) (H \ A ω)) ∧
      IsCondZeroBoundaryGFF P (germSigma A h ⊔ ℋ) (fun ω => H \ A ω) (fun ω => h ω - h₁ ω) := by
  have hav := hloc.isAvoidanceLocal
  obtain ⟨M, h₁, hM, hMlim, hh₁m, hh₁⟩ := exists_germVersion hh hA hav hAc
  refine ⟨h₁, hh₁m, ae_isHarmonicDistOn_germVersion hh hA hav hAc hM hMlim hh₁, fun φ => ?_⟩
  have hhm := hh.measurable
  have hle := germSigma_le hA hhm
  have hle' : germSigma A h ⊔ ℋ ≤ mΩ := sup_le hle hℋ
  obtain ⟨M', hM'm, hM'e, hM'c⟩ := exists_condExp_germSigma_history hh hA hℋ hloc hAc φ
  -- the germ mean is also the mean given the germs and the marks
  have hM'i : Integrable M' P := integrable_condExp.congr hM'e.symm
  have hMM' : M φ =ᵐ[P] M' := by
    refine (hM φ).2.1.trans ?_
    calc P[fun ω => h ω φ | germSigma A h]
        =ᵐ[P] P[P[fun ω => h ω φ | germSigma A h ⊔ ℋ] | germSigma A h] :=
          (condExp_condExp_of_le le_sup_left hle').symm
      _ =ᵐ[P] P[M' | germSigma A h] := condExp_congr_ae hM'e.symm
      _ = M' := condExp_of_stronglyMeasurable hle hM'm.stronglyMeasurable hM'i
  -- pull out the germ-measurable phase
  set W : Ω → ℂ := fun ω => Complex.exp (-(Complex.I * (h₁ ω φ : ℂ)))
  have hWm0 : Measurable[germSigma A h] W :=
    Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_distOn_apply φ).comp hh₁m))).neg)
  have hWm : StronglyMeasurable[germSigma A h ⊔ ℋ] W :=
    (hWm0.mono (le_sup_left : germSigma A h ≤ germSigma A h ⊔ ℋ) le_rfl).stronglyMeasurable
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := fun ω => by
    simp only [W, neg_mul_eq_mul_neg, ← Complex.ofReal_neg, Complex.norm_exp_I_mul_ofReal]; rfl
  have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hhm)
  have hWF : Integrable (fun ω => W ω * Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    hF.bdd_mul (hWm.mono hle').aestronglyMeasurable (Eventually.of_forall hWb)
  have hpull := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hWm
    (by simpa [ContinuousLinearMap.mul_apply'] using hWF) hF
  have e : (fun ω => Complex.exp (Complex.I * (((h ω - h₁ ω) φ : ℝ) : ℂ))) =
      fun ω => (ContinuousLinearMap.mul ℝ ℂ) (W ω) (Complex.exp (Complex.I * (h ω φ : ℂ))) := by
    funext ω
    simp only [W, ContinuousLinearMap.mul_apply', sub_apply, Complex.ofReal_sub, ← Complex.exp_add]
    congr 1; ring
  rw [e]
  filter_upwards [hpull, hM'c, hh₁ φ, hMM', hAc] with ω h1 h2 h3 h4 ⟨hsub, hopen⟩
  rw [h1, ContinuousLinearMap.mul_apply', ← h2]
  simp only [W, h3, h4, relClosureH_eq hsub hopen, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, one_mul]

end GermLaw

/-! ### Locality from a conditional zero-boundary law -/

section Local

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h₁ : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}

/-- **Lemma 3.6, (iii) ⇒ (iv), for any conditioning σ-algebra.** If `A` and `h₁` are measurable for a sub-σ-algebra
`𝒢`, `h₁` is almost surely harmonic on `ℍ ∖ A`, and `h − h₁` is a zero-boundary GFF on `ℍ ∖ A` conditionally on `𝒢`,
then `A` is a local set of `h`. The two-step model is the original space (`A` replaced by its relative closure, almost
surely equal): conditionally on `σ(A) ∨ σ(h₁) ≤ 𝒢` the residual keeps its law by the tower property, since its
conditional characteristic functional is a function of `A`. -/
theorem isLocalSet_of_isCondZeroBoundaryGFF (h𝒢 : 𝒢 ≤ mΩ)
    (hA𝒢 : Measurable[𝒢, hittingSigma] A) (hh : Measurable h) (hh₁ : Measurable[𝒢] h₁)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hharm : ∀ᵐ ω ∂P, IsHarmonicDistOn (h₁ ω) (H \ A ω))
    (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) (fun ω => h ω - h₁ ω)) : IsLocalSet A h P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  have hA : Measurable[mΩ, hittingSigma] A := hA𝒢.mono h𝒢 le_rfl
  have hh₁m : Measurable h₁ := hh₁.mono h𝒢 le_rfl
  have hAeq : ∀ᵐ ω ∂P, relClosureH (A ω) = A ω := by
    filter_upwards [hAc] with ω hω
    exact relClosureH_eq hω.1 hω.2
  refine ⟨(hA.prodMk hh).aemeasurable, hAc, Ω, mΩ, P, inferInstance,
    fun ω => relClosureH (A ω), h₁, fun ω => h ω - h₁ ω,
    measurable_relClosureH.comp hA, hh₁m,
    measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp hh).sub ((measurable_distOn_apply φ).comp hh₁m),
    fun ω => ⟨relClosureH_subset _, isOpen_H_diff_relClosureH _⟩, ?_, ?_, ?_⟩
  · filter_upwards [hharm, hAeq] with ω h1 h2
    rw [h2]
    exact h1
  · intro φ
    set 𝒦 : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => relClosureH (A ω)) hittingSigma ⊔
      MeasurableSpace.comap h₁ inferInstance with h𝒦def
    have h𝒦 : 𝒦 ≤ 𝒢 := by
      refine sup_le ?_ hh₁.comap_le
      rw [comap_relClosureH_comp]
      exact hA𝒢.comap_le
    have hcov : Measurable[𝒦] fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) φ φ := by
      refine (measurable_comap_zeroGFFTestCov_compl A φ φ).mono ?_ le_rfl
      rw [← comap_relClosureH_comp]
      exact le_sup_left
    set c' : Ω → ℂ := fun ω =>
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) with hc'def
    have hc'm : StronglyMeasurable[𝒦] c' :=
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hcov.const_mul _))).stronglyMeasurable
    have hcc' : (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ)) =ᵐ[P] c' := by
      filter_upwards [hAeq] with ω hω
      simp only [c', hω]
    have hc'i : Integrable c' P := (integrable_condExp.congr (hcond φ)).congr hcc'
    calc P[(fun ω => Complex.exp (Complex.I * ((h ω - h₁ ω) φ : ℂ)))|𝒦]
        =ᵐ[P] P[P[(fun ω => Complex.exp (Complex.I * ((h ω - h₁ ω) φ : ℂ)))|𝒢]|𝒦] :=
          (condExp_condExp_of_le h𝒦 h𝒢).symm
      _ =ᵐ[P] P[c'|𝒦] := condExp_congr_ae ((hcond φ).trans hcc')
      _ = c' := condExp_of_stronglyMeasurable (h𝒦.trans h𝒢) hc'm hc'i
  · refine Measure.map_congr ?_
    filter_upwards [hAeq] with ω hω
    simp [hω]

end Local

/-! ### Conditional locality on a mark -/

section Cond

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}

/-- **A history-marked local set is local conditionally on every mark** (Aux. lemma 53, p. 245: "Its zero-boundary
residual field … has the same law for every germ with that recorded history … Forgetting that germ preserves
locality"). For a zero-boundary GFF `h` on `ℍ`, an almost surely relatively closed `A ⊆ ℍ` satisfying the
history-marked avoidance criterion for the marks `ℋ`, and an event `D ∈ 𝒜 ∨ ℋ` of positive probability (a mark, or an
event of the germs and the marks), `A` is a local set of `h` under `P[· | D]`. -/
theorem isLocalSet_cond_of_isHistoryAvoidanceLocal (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsHistoryAvoidanceLocal ℋ A h P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) {D : Set Ω} (hD : MeasurableSet[germSigma A h ⊔ ℋ] D)
    (hPD : P D ≠ 0) :
    IsLocalSet A h (P[|D]) := by
  obtain ⟨h₁, hh₁, hharm, hcond⟩ := exists_germLaw_of_isHistoryAvoidanceLocal hh hA hℋ hloc hAc
  have hhm := hh.measurable
  have hle : germSigma A h ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hA hhm) hℋ
  have : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hac : P[|D] ≪ P := cond_absolutelyContinuous
  have hAg : Measurable[germSigma A h ⊔ ℋ, hittingSigma] A :=
    (measurable_iff_comap_le.2 (comap_le_germSigma A h)).mono le_sup_left le_rfl
  refine isLocalSet_of_isCondZeroBoundaryGFF hle hAg hhm (hh₁.mono le_sup_left le_rfl) (hac.ae_le hAc)
    (hac.ae_le hharm) fun φ => ?_
  have hcov : Measurable[germSigma A h ⊔ ℋ] fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) φ φ :=
    (measurable_comap_zeroGFFTestCov_compl A φ φ).mono
      ((comap_le_germSigma A h).trans le_sup_left) le_rfl
  set c' : Ω → ℂ := fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ)
    with hc'def
  have hc'm : StronglyMeasurable[germSigma A h ⊔ ℋ] c' :=
    (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hcov.const_mul _))).stronglyMeasurable
  have hcc' : (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ)) =ᵐ[P] c' := by
    filter_upwards [hAc] with ω hω
    simp only [c', relClosureH_eq hω.1 hω.2]
  have hc'i : Integrable c' P := (integrable_condExp.congr (hcond φ)).congr hcc'
  have hX : Integrable (fun ω => Complex.exp (Complex.I * (((h ω - h₁ ω) φ : ℝ) : ℂ))) P :=
    GFF.integrable_exp_I_mul (((measurable_distOn_apply φ).comp hhm).sub
      ((measurable_distOn_apply φ).comp (hh₁.mono (germSigma_le hA hhm) le_rfl)))
  have key := LocalExt.condExp_cond_ae_eq le_rfl hle hD hPD hX hc'm hc'i
    ((hcond φ).trans hcc')
  refine key.trans ?_
  filter_upwards [hac.ae_le hAc] with ω hω
  simp only [c', relClosureH_eq hω.1 hω.2]

end Cond

end InteractingSLE.Sec7.Lemma72C
