/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.Prop39Indep
import InteractingSLE.Spec.Sec6.Prop61BMarked

/-!
# The marked Proposition 3.9: the field on a union of components chosen from the marks

Packet PROVE-STRIPSYS9. Specification §3.2, Proposition 3.9 (p. 71), in the **marked** form used by Aux. lemma 124
(`source/spec/p385-432.md#aux-124`, pp. 393–394: "Condition first on the complete marked `A`. Its residual GFF is
the orthogonal sum of its zero-boundary fields in the components of `D ∖ A`. Reveal all summands except the one in
`C`.") and by Aux. lemma 125.

The landed Proposition 3.9 (`LocalSets.IsLocalSetMean.condExp_exp_eq_on_of_union`) conditions on the **unmarked** germ
σ-algebra `𝒜₁` and needs the union of components `C` to be measurable from `σ(A₁)`. In Aux. 124 the component `C` is
chosen from the labels of an earlier set `A`, while the conditioning set is `A ∪ R_t`, which does not determine those
labels. Here `A₁` carries an arbitrary σ-algebra of marks `ℋ` (labels, stopped histories, earlier germs) for which it
satisfies the history-marked avoidance criterion (`WholeField.IsHistoryAvoidanceLocal`, Aux. lemma 18), and `C` is
measurable from `σ(A₁) ∨ ℋ`.

## Statement

For a local set `A` of the zero-boundary GFF `h` with marks `ℋ`, a union `C` of components of `ℍ ∖ A` with `ℍ ∖ C`
measurable from `σ(A) ∨ ℋ`, and a test function `φ`, almost surely on `{supp φ ⊆ C}`:

`E[e^{i(h, φ)} | 𝒥] = e^{i(𝒞_A, φ)} e^{−σ²_C(φ)/2}`

for **every** σ-algebra `𝒥` between `𝒜 ∨ ℋ` and `𝒦 = 𝒮 ∨ σ(A) ∨ ℋ ∨ 𝒜 ∨ σ(h|_{ℍ∖C})`, where `𝒮` is the germ σ-algebra
of `S = (ℍ ∖ C) ∪ A` (`ae_condExp_exp_eq_of_le_markedOffCover`). The cases `𝒥 = 𝒜 ∨ ℋ` and
`𝒥 = 𝒜 ∨ ℋ ∨ σ(h|_{ℍ∖C})` are the two clauses of the marked Proposition 3.9 (`ae_condExp_exp_marked`,
`ae_condExp_exp_offSigma_marked`); the case with the germ of `S` retained is the further reveal in Aux. 124's proof
("One may also retain the canonical germ of `B ∪ R_t`").

## Proof

The landed proof of Proposition 3.9's second clause, with the marking `σ(A) ∨ ℋ` and the marked avoidance
σ-algebras `histAvoidSigma A ℋ` in place of `σ(A₁, A₂)` and `avoidSigma₂ A₁ A₂`:

* `measurableSet_histAvoidSigma_inter_sup`: every event of `σ(A) ∨ ℋ`, intersected with an avoidance event
  `{A ∩ V₀ = ∅}`, is a marked avoidance event;
* `isCoverMarking_history_of_subset`: hence `(σ(A) ∨ ℋ, histAvoidSigma A ℋ)` is cover-marking data for every
  `(σ(A) ∨ ℋ)`-measurable random set `S ⊇ A` (the atoms of the covers of `S` lie in avoidance events of `A`);
* the landed cover argument (`exists_condExp_germSigmaK`) for `S = (ℍ ∖ C) ∪ A` gives the law `M + GFF_C` given `𝒦`;
  the tower argument against the local-set law of `A` (`ae_cos_eq_one_of_condCharFun`) identifies `M = 𝒞_A` on
  `{supp φ ⊆ C}`;
* the tower property (`Sec6.condExp_ae_eq_on_of_le`) transfers the law to every `𝒥` in between.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE
namespace Sec7
namespace MarkedProp39

open QuantumZipper LQGMetric LocalSets WholeField

/-! ### The marking `σ(A) ∨ ℋ` on avoidance events -/

section Marking

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} {A : Ω → Set ℂ}

/-- **Trace of `σ(A) ∨ ℋ` on an avoidance event**: for open `W ⊆ V₀ ⊆ ℍ` and `B ∈ σ(A) ∨ ℋ`, the event
`B ∩ {A ∩ V₀ = ∅}` is a marked avoidance event of `W`. -/
theorem measurableSet_histAvoidSigma_inter_sup {W V₀ : Set ℂ} (hV₀ : IsOpen V₀) (hWV₀ : W ⊆ V₀)
    (hV₀H : V₀ ⊆ H) {B : Set Ω}
    (hB : MeasurableSet[MeasurableSpace.comap A hittingSigma ⊔ ℋ] B) :
    MeasurableSet[histAvoidSigma A ℋ W] (B ∩ {ω | Disjoint (A ω) V₀}) := by
  have hE₀ : MeasurableSet[histAvoidSigma A ℋ W] {ω | Disjoint (A ω) V₀} :=
    avoidSigma_le_histAvoidSigma A ℋ W _ (measurableSet_avoidSigma hV₀ hWV₀ hV₀H)
  refine (sup_le ?_ ?_ : _ ≤ traceSigma (histAvoidSigma A ℋ W) _ hE₀) B hB
  · rintro _ ⟨B₁, hB₁, rfl⟩
    exact avoidSigma_le_histAvoidSigma A ℋ W _ (measurableSet_avoidSigma_inter hV₀ hWV₀ hV₀H hB₁)
  · intro F hF
    show MeasurableSet[histAvoidSigma A ℋ W] (F ∩ {ω | Disjoint (A ω) V₀})
    rw [inter_comm]
    exact measurableSet_histAvoidSigma hV₀ hWV₀ hV₀H hF

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Cover-marking data for a set containing a marked local set.** If `A` satisfies the history-marked avoidance
criterion for the marks `ℋ`, then `(σ(A) ∨ ℋ, histAvoidSigma A ℋ)` is cover-marking data for every
`(σ(A) ∨ ℋ)`-measurable random set `S ⊇ A`. -/
theorem isCoverMarking_history_of_subset (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsHistoryAvoidanceLocal ℋ A h P)
    {S : Ω → Set ℂ} (hSm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma] S)
    (hAS : ∀ ω, A ω ⊆ S ω) :
    IsCoverMarking S h P (MeasurableSpace.comap A hittingSigma ⊔ ℋ) (histAvoidSigma A ℋ) where
  le := sup_le hA.comap_le hℋ
  le_avoid := histAvoidSigma_le hA hℋ
  comap_le := hSm.comap_le
  trace := by
    intro j T B hB
    by_cases hT : T ⊆ coverIdx j
    · have hatom : MeasurableSet[MeasurableSpace.comap A hittingSigma ⊔ ℋ] (coverAtom j S T) :=
        hSm (measurableSet_removedIdx_eq j T)
      have hsub : coverAtom j S T ⊆ {ω | Disjoint (A ω) (coverThick j T)} := by
        intro ω hω
        have := coverAtom_subset_avoid j S T hω
        simp only [mem_ofPred_eq] at this
        exact this.mono_left (hAS ω)
      have e : B ∩ coverAtom j S T = (B ∩ coverAtom j S T) ∩ {ω | Disjoint (A ω) (coverThick j T)} :=
        (inter_eq_left.2 (inter_subset_right.trans hsub)).symm
      rw [e]
      exact measurableSet_histAvoidSigma_inter_sup (isOpen_coverThick j T)
        (inter_subset_left.trans (coverOpen_subset_coverThick j T)) (coverThick_subset_H hT)
        (hB.inter hatom)
    · rw [coverAtom_eq_empty hT, inter_empty]
      exact @MeasurableSet.empty _ (histAvoidSigma A ℋ (markovOpen T))
  indep T := indep_markov_histAvoidSigma hh hA hℋ hloc (measurable_coverMarkov.{u} T)
    (isMarkovDecomposition_coverMarkov hh T)

end Marking

/-! ### The marked law on `C` -/

section Law

variable {Ω : Type u} {ℋ 𝒥 : MeasurableSpace Ω} {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The conditioning σ-algebra of the marked cover argument for `S = (ℍ ∖ C) ∪ A`: the germs of `S`, the set `A`
with its marks `ℋ`, the germs of `A`, and the field off `C`. -/
@[instance_reducible]
def markedOffCoverSigma (A C : Ω → Set ℂ) (ℋ : MeasurableSpace Ω) (h : Ω → DistOn upperHalfPlaneOpens) :
    MeasurableSpace Ω :=
  germSigma (fun ω => (H \ C ω) ∪ A ω) h ⊔ (MeasurableSpace.comap A hittingSigma ⊔ ℋ) ⊔
    germSigma A h ⊔ offSigma C h

theorem le_markedOffCoverSigma_germ (C : Ω → Set ℂ) : germSigma A h ⊔ ℋ ≤ markedOffCoverSigma A C ℋ h :=
  sup_le (le_sup_right.trans le_sup_left)
    ((le_sup_right : ℋ ≤ MeasurableSpace.comap A hittingSigma ⊔ ℋ).trans (le_sup_right.trans
      (le_sup_left.trans le_sup_left)))

theorem offSigma_le_markedOffCoverSigma (C : Ω → Set ℂ) : offSigma C h ≤ markedOffCoverSigma A C ℋ h :=
  le_sup_right

theorem germSigma_le_markedOffCoverSigma (C : Ω → Set ℂ) :
    germSigma (fun ω => (H \ C ω) ∪ A ω) h ≤ markedOffCoverSigma A C ℋ h :=
  le_sup_left.trans (le_sup_left.trans le_sup_left)

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem markedOffCoverSigma_le {C : Ω → Set ℂ} (hhm : Measurable h) (hA : Measurable[mΩ, hittingSigma] A)
    (hℋ : ℋ ≤ mΩ) (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω) :
    markedOffCoverSigma A C ℋ h ≤ mΩ := by
  have hℳ : MeasurableSpace.comap A hittingSigma ⊔ ℋ ≤ mΩ := sup_le hA.comap_le hℋ
  have hS : Measurable[mΩ, hittingSigma] fun ω => (H \ C ω) ∪ A ω :=
    measurable_union_hitting (hCm.mono hℳ le_rfl) hA
  refine sup_le (sup_le (sup_le (germSigma_le hS hhm) hℳ) (germSigma_le hA hhm)) ?_
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨ψ, B, hB, rfl⟩
  exact hℳ _ (hCm (measurableSet_subset_relClosureH ψ.hasCompactSupport ψ.tsupport_subset)) |>.inter
    ((measurable_distOn_apply ψ).comp hhm hB)

/-- **The marked local-set law in subtracted form**: given the germs and the marks, `h(ψ) − g(ψ)` has the
conditional characteristic function `e^{−σ²_{ℍ∖A}(ψ)/2}` (Aux. lemma 18's marked law, with its mean identified as
the local-set mean). -/
theorem condExp_exp_sub_marked (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet A h P)
    (hmark : IsHistoryAvoidanceLocal ℋ A h P) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A h P g) (ψ : TestOn upperHalfPlaneOpens) :
    P[fun ω => Complex.exp (Complex.I * ((h ω ψ - g ω ψ : ℝ) : ℂ)) | germSigma A h ⊔ ℋ] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) ψ ψ) : ℝ) : ℂ) := by
  have hhm := hh.measurable
  have hle := germSigma_le hA hhm
  have h𝒥le : germSigma A h ⊔ ℋ ≤ mΩ := sup_le hle hℋ
  obtain ⟨M, hMm, hM1, hM2⟩ := exists_condExp_germSigma_history hh hA hℋ hmark hloc.2.1 ψ
  have hMi : Integrable M P := integrable_condExp.congr hM1.symm
  have hMg : M =ᵐ[P] fun ω => g ω ψ := by
    have e1 : P[P[fun ω => h ω ψ | germSigma A h ⊔ ℋ] | germSigma A h] =ᵐ[P]
        P[fun ω => h ω ψ | germSigma A h] := condExp_condExp_of_le le_sup_left h𝒥le
    have e2 : P[P[fun ω => h ω ψ | germSigma A h ⊔ ℋ] | germSigma A h] =ᵐ[P]
        P[M | germSigma A h] := condExp_congr_ae hM1.symm
    rw [condExp_of_stronglyMeasurable hle hMm.stronglyMeasurable hMi] at e2
    exact e2.symm.trans (e1.trans (Sec6.IsLocalSetMean.ae_eq_condExp_germSigma hh hA hloc hg ψ).symm)
  have hgψ : Measurable[germSigma A h ⊔ ℋ] fun ω => -g ω ψ :=
    ((measurable_distOn_apply ψ).comp hg.1).neg.mono le_sup_left le_rfl
  have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply ψ).comp hhm)
  have hpull := condExp_exp_mul_of_measurable (m := germSigma A h ⊔ ℋ) (W := fun ω => -g ω ψ) hgψ hF h𝒥le
  have e : (fun ω => Complex.exp (Complex.I * ((h ω ψ - g ω ψ : ℝ) : ℂ))) =
      fun ω => Complex.exp (Complex.I * ((-g ω ψ : ℝ) : ℂ)) * Complex.exp (Complex.I * (h ω ψ : ℂ)) := by
    funext ω; rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]
  filter_upwards [hpull, hM2, hMg] with ω h1 h2 h3
  rw [h1, ← h2, ← mul_assoc, ← Complex.exp_add, h3]
  have : Complex.I * ((-g ω ψ : ℝ) : ℂ) + Complex.I * (g ω ψ : ℂ) = 0 := by push_cast; ring
  rw [this, Complex.exp_zero, one_mul]

/-- **The marked cover law** (core of the marked Proposition 3.9). Let `A` be a local set of the zero-boundary GFF
`h` on `ℍ` with local-set mean `g`, satisfying the history-marked avoidance criterion for the marks `ℋ`, and let `C`
be a random union of components of `ℍ ∖ A` with `ℍ ∖ C` measurable from `σ(A) ∨ ℋ`. Given
`𝒦 = markedOffCoverSigma A C ℋ h`, almost surely on `{supp φ ⊆ C}`: `E[(h, φ) | 𝒦] = (g, φ)` and
`E[e^{i(h, φ)} | 𝒦] = e^{i(g, φ)} e^{−σ²_C(φ)/2}`. -/
theorem ae_condExp_markedOffCover (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet A h P)
    (hmark : IsHistoryAvoidanceLocal ℋ A h P) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g) (φ : TestOn upperHalfPlaneOpens) :
    (∀ᵐ ω ∂P, tsupport φ ⊆ C ω →
      P[fun ω => h ω φ | markedOffCoverSigma A C ℋ h] ω = g ω φ) ∧
    (∀ᵐ ω ∂P, tsupport φ ⊆ C ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | markedOffCoverSigma A C ℋ h] ω =
        Complex.exp (Complex.I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (C ω) φ φ) : ℝ) : ℂ)) := by
  classical
  have hhm := hh.measurable
  have hℳle : (MeasurableSpace.comap A hittingSigma ⊔ ℋ) ≤ mΩ := sup_le hA.comap_le hℋ
  set S : Ω → Set ℂ := fun ω => (H \ C ω) ∪ A ω with hSdef
  have hAS : ∀ ω, A ω ⊆ S ω := fun ω z hz => Or.inr hz
  have hSm : Measurable[(MeasurableSpace.comap A hittingSigma ⊔ ℋ), hittingSigma] S :=
    @measurable_union_hitting Ω (MeasurableSpace.comap A hittingSigma ⊔ ℋ) _ _ hCm ((comap_measurable A).mono le_sup_left le_rfl)
  have hSm' : Measurable[mΩ, hittingSigma] S := hSm.mono hℳle le_rfl
  have hmk := isCoverMarking_history_of_subset hh hA hℋ hmark hSm hAS
  -- the structural facts, almost surely
  have hgood : ∀ᵐ ω ∂P, IsOpen (H \ A ω) ∧ IsOpen (C ω) ∧ C ω ⊆ H \ A ω ∧
      IsOpen ((H \ A ω) \ C ω) ∧ S ω = H \ C ω ∧ relClosureH (A ω) = A ω := by
    filter_upwards [hloc.2.1, hC] with ω ⟨hs, ho⟩ ⟨hCs, hCc⟩
    refine ⟨ho, isOpen_of_forall_connectedComponentIn_subset ho hCs hCc, hCs,
      isOpen_diff_of_forall_connectedComponentIn_subset ho hCc, ?_, relClosureH_eq hs ho⟩
    refine subset_antisymm ?_ (fun z hz => Or.inl hz)
    rintro z (hz | hz)
    · exact hz
    · exact ⟨hs hz, fun hzC => (hCs hzC).2 hz⟩
  have hSc : ∀ᵐ ω ∂P, S ω ⊆ H ∧ IsOpen (H \ S ω) := by
    filter_upwards [hgood] with ω ⟨_, hCo, hCs, _, hS, _⟩
    rw [hS, sdiff_sdiff_cancel_left (hCs.trans sdiff_subset)]
    exact ⟨sdiff_subset, hCo⟩
  -- the conditioning σ-algebra of the cover argument
  have h𝒦S : germSigma S h ≤ (markedOffCoverSigma A C ℋ h) := germSigma_le_markedOffCoverSigma C
  have h𝒦A : germSigma A h ≤ (markedOffCoverSigma A C ℋ h) := le_sup_right.trans le_sup_left
  have h𝒦le : (markedOffCoverSigma A C ℋ h) ≤ mΩ := markedOffCoverSigma_le hhm hA hℋ hCm
  have h𝒦tr : ∀ j, (markedOffCoverSigma A C ℋ h) ≤ aeSigma (coverSigmaM (MeasurableSpace.comap A hittingSigma ⊔ ℋ) j S h) P := by
    intro j
    have hℳ' : (MeasurableSpace.comap A hittingSigma ⊔ ℋ) ≤ aeSigma (coverSigmaM (MeasurableSpace.comap A hittingSigma ⊔ ℋ) j S h) P := le_sup_left.trans (le_aeSigma _ P)
    refine sup_le (sup_le (sup_le (fun G hG => germSigmaAt_le_aeSigmaM hh hmk.comap_le j G
      (measurableSet_germSigmaAt_coverRad hG j)) hℳ')
      (germSigma_le_aeSigma_of_subset hh hmk.comap_le le_sup_left hAS j)) ?_
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨ψ, B, hB, rfl⟩
    have hE₁ : MeasurableSet[(MeasurableSpace.comap A hittingSigma ⊔ ℋ)] {ω | tsupport ψ ⊆ relClosureH (H \ C ω)} :=
      hCm (measurableSet_subset_relClosureH ψ.hasCompactSupport ψ.tsupport_subset)
    have hX : MeasurableSet[germSigmaAt S h (coverRad j)]
        ({ω | tsupport ψ ⊆ germNbhd (coverRad j) (S ω)} ∩ (fun ω => h ω ψ) ⁻¹' B) :=
      (le_sup_right : MeasurableSpace.generateFrom {E | ∃ (φ : TestOn upperHalfPlaneOpens)
        (B : Set ℝ), MeasurableSet B ∧ E = {ω | tsupport φ ⊆ germNbhd (coverRad j) (S ω)} ∩
          (fun ω => h ω φ) ⁻¹' B} ≤ germSigmaAt S h (coverRad j)) _
        (MeasurableSpace.measurableSet_generateFrom ⟨ψ, B, hB, rfl⟩)
    have hsub : {ω | tsupport ψ ⊆ relClosureH (H \ C ω)} ⊆
        {ω | tsupport ψ ⊆ germNbhd (coverRad j) (S ω)} := by
      intro ω hω z hz
      have hz' := hω hz
      refine ⟨hz'.1, Or.inl (thickening_subset_of_subset _ subset_union_left
        (closure_subset_thickening (coverRad_pos j) _ (closure_mono ?_ hz'.2)))⟩
      exact inter_subset_inter_left _ (fun w hw => Or.inl hw)
    have e : {ω | tsupport ψ ⊆ relClosureH (H \ C ω)} ∩ (fun ω => h ω ψ) ⁻¹' B =
        {ω | tsupport ψ ⊆ relClosureH (H \ C ω)} ∩
          ({ω | tsupport ψ ⊆ germNbhd (coverRad j) (S ω)} ∩ (fun ω => h ω ψ) ⁻¹' B) := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, hsub h1, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    rw [e]
    exact (hℳ' _ hE₁).inter (germSigmaAt_le_aeSigmaM hh hmk.comap_le j _ hX)
  -- the cover law at `φ` and at its multiples `φ/(n+1)`
  obtain ⟨M, hMm, -, hMc, hMe⟩ := exists_condExp_germSigmaK hh hSm' hmk hSc h𝒦S h𝒦le h𝒦tr φ
  set c : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with hcdef
  choose Mn hMnm hMnlim hMnc hMne using fun n : ℕ =>
    exists_condExp_germSigmaK hh hSm' hmk hSc h𝒦S h𝒦le h𝒦tr (c n • φ)
  -- the event `{supp φ ⊆ C}`
  set G : Set Ω := {ω | Disjoint (tsupport φ) (relClosureH (H \ C ω))} with hGdef
  have hGc : MeasurableSet[(MeasurableSpace.comap A hittingSigma ⊔ ℋ)] G :=
    hCm (measurableSet_disjoint_relClosureH φ.hasCompactSupport φ.tsupport_subset)
  have hGsub : ∀ᵐ ω ∂P, (ω ∈ G ↔ tsupport φ ⊆ C ω) := by
    filter_upwards [hgood] with ω ⟨_, hCo, hCs, _, _, _⟩
    have hrc : relClosureH (H \ C ω) = H \ C ω := by
      refine relClosureH_eq sdiff_subset ?_
      rw [sdiff_sdiff_cancel_left (hCs.trans sdiff_subset)]; exact hCo
    simp only [hGdef, mem_ofPred_eq, hrc]
    constructor
    · intro hdis z hz
      by_contra hzC
      exact Set.disjoint_left.1 hdis hz ⟨φ.tsupport_subset hz, hzC⟩
    · intro hsub
      exact Set.disjoint_left.2 fun z hz hz' => hz'.2 (hsub hz)
  have h𝒢 : germSigma A h ⊔ ℋ ≤ (markedOffCoverSigma A C ℋ h) := le_markedOffCoverSigma_germ C
  have hG𝒢 : MeasurableSet[germSigma A h ⊔ ℋ] G :=
    (sup_le ((comap_le_germSigma A h).trans le_sup_left) le_sup_right : (MeasurableSpace.comap A hittingSigma ⊔ ℋ) ≤ germSigma A h ⊔ ℋ) _ hGc
  -- the variances on `G`
  have hvar : ∀ a : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      zeroGFFTestCov (H \ relClosureH (A ω)) ⇑(a • φ) ⇑(a • φ) =
        zeroGFFTestCov (H \ relClosureH (S ω)) ⇑(a • φ) ⇑(a • φ) ∧
      zeroGFFTestCov (H \ relClosureH (A ω)) ⇑(a • φ) ⇑(a • φ) = zeroGFFTestCov (C ω) ⇑(a • φ) ⇑(a • φ) := by
    intro a
    filter_upwards [hgood, hGsub] with ω ⟨ho, hCo, hCs, hd, hS, hrcA⟩ hG hωG
    have hsupp : tsupport ⇑(a • φ) ⊆ C ω :=
      (tsupport_smul_subset_right (fun _ => a) φ).trans (hG.1 hωG)
    have e1 := zeroGFFTestCov_eq_of_isClopen ho sdiff_subset hCo hCs hd (a • φ) hsupp
    have hHS : H \ S ω = C ω := by rw [hS, sdiff_sdiff_cancel_left (hCs.trans sdiff_subset)]
    have hrcS : relClosureH (S ω) = S ω :=
      relClosureH_eq (by rw [hS]; exact sdiff_subset) (by rw [hHS]; exact hCo)
    rw [hrcA, hrcS, hHS]
    exact ⟨e1, e1⟩
  -- the cover law in subtracted form
  have hlaw₂ : ∀ n, P[fun ω => Complex.exp (Complex.I * ((h ω (c n • φ) - Mn n ω : ℝ) : ℂ)) | (markedOffCoverSigma A C ℋ h)] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) *
        zeroGFFTestCov (H \ relClosureH (S ω)) ⇑(c n • φ) ⇑(c n • φ)) : ℝ) : ℂ) := by
    intro n
    have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω (c n • φ) : ℂ))) P :=
      GFF.integrable_exp_I_mul ((measurable_distOn_apply _).comp hhm)
    have hpull := condExp_exp_mul_of_measurable (m := (markedOffCoverSigma A C ℋ h))
      (W := fun ω => -Mn n ω) ((hMnm n).neg.mono h𝒦S le_rfl) hF h𝒦le
    have e : (fun ω => Complex.exp (Complex.I * ((h ω (c n • φ) - Mn n ω : ℝ) : ℂ))) =
        fun ω => Complex.exp (Complex.I * ((-Mn n ω : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (h ω (c n • φ) : ℂ)) := by
      funext ω; rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]
    filter_upwards [hpull, hMne n] with ω h1 h2
    rw [h1, ← h2, ← mul_assoc, ← Complex.exp_add]
    have : Complex.I * ((-Mn n ω : ℝ) : ℂ) + Complex.I * (Mn n ω : ℂ) = 0 := by push_cast; ring
    rw [this, Complex.exp_zero, one_mul]
  -- the tower argument at each multiple, against the marked law of `A`
  have hcos : ∀ n, ∀ᵐ ω ∂P, ω ∈ G → Real.cos (Mn n ω - g ω (c n • φ)) = 1 := fun n => by
    have hX : Measurable fun ω => h ω (c n • φ) := (measurable_distOn_apply _).comp hhm
    have hM₁ : Measurable[germSigma A h ⊔ ℋ] fun ω => g ω (c n • φ) :=
      ((measurable_distOn_apply _).comp hg.1).mono le_sup_left le_rfl
    exact ae_cos_eq_one_of_condCharFun (P := P) h𝒢 h𝒦le hX hM₁ ((hMnm n).mono h𝒦S le_rfl)
      (condExp_exp_sub_marked hh hA hℋ hloc hmark hg _) (hlaw₂ n) hG𝒢
      (by filter_upwards [hvar (c n)] with ω hω hωG using (hω hωG).1)
  have hMn : ∀ n, Mn n =ᵐ[P] fun ω => c n * M ω := by
    intro n
    have e : (fun ω => h ω (c n • φ)) = c n • fun ω => h ω φ := by
      funext ω; rw [map_smul]; rfl
    have h1 := hMnc n
    rw [e] at h1
    filter_upwards [h1, condExp_smul (μ := P) (c n) (fun ω => h ω φ) (markedOffCoverSigma A C ℋ h), hMc] with ω h1 h2 h3
    rw [h1, h2, Pi.smul_apply, smul_eq_mul, ← h3]
  have hMg : ∀ᵐ ω ∂P, ω ∈ G → M ω = g ω φ := by
    filter_upwards [ae_all_iff.2 hcos, ae_all_iff.2 hMn] with ω h1 h2 hωG
    have : ∀ n : ℕ, Real.cos (((n : ℝ) + 1)⁻¹ * (M ω - g ω φ)) = 1 := fun n => by
      have := h1 n hωG
      rwa [h2 n, map_smul, smul_eq_mul, ← mul_sub] at this
    have := eq_zero_of_forall_cos_eq_one this
    linarith
  -- the common value `Z = e^{i(𝒞_A, φ)} e^{−σ²/2}`
  set F : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hFdef
  have hFi : Integrable F P := GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hhm)
  set Z : Ω → ℂ := fun ω => Complex.exp (Complex.I * (g ω φ : ℂ)) *
    ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) with hZdef
  -- the cover law on `G`
  have hlawK : ∀ᵐ ω ∂P, ω ∈ G → P[F | (markedOffCoverSigma A C ℋ h)] ω = Z ω := by
    filter_upwards [hMe, hMg, hvar 1] with ω h1 h2 h3 hωG
    rw [← h1, h2 hωG, hZdef]
    simp only
    have := (h3 hωG).1
    simp only [one_smul] at this
    rw [this]
  refine ⟨?_, ?_⟩
  · filter_upwards [hMc, hMg, hGsub] with ω h1 h2 h3 hsupp
    rw [← h1, h2 (h3.2 hsupp)]
  · filter_upwards [hlawK, hGsub, hvar 1] with ω h1 h2 h4 hsupp
    have hωG : ω ∈ G := h2.2 hsupp
    rw [h1 hωG, hZdef]
    simp only
    have := (h4 hωG).2
    simp only [one_smul] at this
    rw [this]

/-- **Forgetting information** (Aux. lemma 125's proof, p. 396: "Both the mean and that covariance depend only on `Θ`
and the relative stopped history. The tower property therefore leaves exactly this Gaussian kernel when the extra
ambient history and germs are forgotten"). For any `𝒥 ≤ markedOffCoverSigma A C ℋ h`, a `𝒥`-event `G` and
`𝒥`-measurable `m, v` such that almost surely on `G` the test function `φ` is supported in `C` with `(𝒞_A, φ) = m` and
`σ²_C(φ) = v`: almost surely on `G`, `E[e^{i(h, φ)} | 𝒥] = e^{i m} e^{−v/2}`. -/
theorem ae_condExp_exp_eq_of_le_markedOffCover_forget (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet A h P)
    (hmark : IsHistoryAvoidanceLocal ℋ A h P) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g)
    (h𝒥𝒦 : 𝒥 ≤ markedOffCoverSigma A C ℋ h) (φ : TestOn upperHalfPlaneOpens)
    {G : Set Ω} (hG : MeasurableSet[𝒥] G) {m v : Ω → ℝ} (hm : Measurable[𝒥] m) (hv : Measurable[𝒥] v)
    (hGC : ∀ᵐ ω ∂P, ω ∈ G → tsupport φ ⊆ C ω ∧ g ω φ = m ω ∧ zeroGFFTestCov (C ω) φ φ = v ω) :
    ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒥] ω =
        Complex.exp (Complex.I * (m ω : ℂ)) * ((Real.exp (-(1 / 2) * v ω) : ℝ) : ℂ) := by
  have hhm := hh.measurable
  have h𝒦le := markedOffCoverSigma_le hhm hA hℋ hCm
  have hFi : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hhm)
  set Y : Ω → ℂ := fun ω => Complex.exp (Complex.I * (m ω : ℂ)) * ((Real.exp (-(1 / 2) * v ω) : ℝ) : ℂ)
    with hYdef
  have hYm : StronglyMeasurable[𝒥] Y :=
    ((@GFF.measurable_exp_I_mul Ω 𝒥 _ hm).mul (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hv)))).stronglyMeasurable
  -- on `G`, `v ≥ 0`, so `1_G Y` is bounded
  have hYi : Integrable (G.indicator Y) P := by
    refine Integrable.of_bound (((hYm.indicator hG).mono (h𝒥𝒦.trans h𝒦le)).aestronglyMeasurable) 1 ?_
    filter_upwards [hGC, hC, hloc.2.1] with ω hω ⟨hCs, hCc⟩ ⟨_, ho⟩
    by_cases hωG : ω ∈ G
    · rw [indicator_of_mem hωG, hYdef]
      simp only
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, ← (hω hωG).2.2]
      have := zeroGFFTestCov_self_nonneg (isOpen_of_forall_connectedComponentIn_subset ho hCs hCc)
        (hCs.trans sdiff_subset) φ
      nlinarith
    · rw [indicator_of_notMem hωG, norm_zero]; exact zero_le_one
  have hK := (ae_condExp_markedOffCover hh hA hℋ hloc hmark hCm hC hg φ).2
  have hKG : ∀ᵐ ω ∂P, ω ∈ G →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | markedOffCoverSigma A C ℋ h] ω = G.indicator Y ω := by
    filter_upwards [hK, hGC] with ω h1 h2 hωG
    rw [h1 (h2 hωG).1, indicator_of_mem hωG, hYdef, (h2 hωG).2.1, (h2 hωG).2.2]
  have hfin := Sec6.condExp_ae_eq_on_of_le h𝒥𝒦 h𝒦le hFi (hYm.indicator hG) hYi hG hKG
  filter_upwards [hfin] with ω h1 hωG
  rw [h1 hωG, indicator_of_mem hωG]

/-- **Forgetting information, the conditional mean.** For any `𝒥 ≤ markedOffCoverSigma A C ℋ h`, a `𝒥`-event `G` and a
`𝒥`-measurable `m` such that almost surely on `G` the test function `φ` is supported in `C` with `(𝒞_A, φ) = m`: almost
surely on `G`, `E[(h, φ) | 𝒥] = m`. -/
theorem ae_condExp_apply_eq_of_le_markedOffCover_forget (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet A h P)
    (hmark : IsHistoryAvoidanceLocal ℋ A h P) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g)
    (h𝒥𝒦 : 𝒥 ≤ markedOffCoverSigma A C ℋ h) (φ : TestOn upperHalfPlaneOpens)
    {G : Set Ω} (hG : MeasurableSet[𝒥] G) {m : Ω → ℝ} (hm : Measurable[𝒥] m)
    (hGC : ∀ᵐ ω ∂P, ω ∈ G → tsupport φ ⊆ C ω ∧ g ω φ = m ω) :
    ∀ᵐ ω ∂P, ω ∈ G → P[fun ω => h ω φ | 𝒥] ω = m ω := by
  have hhm := hh.measurable
  have h𝒦le := markedOffCoverSigma_le hhm hA hℋ hCm
  have hG𝒦 : MeasurableSet[markedOffCoverSigma A C ℋ h] G := h𝒥𝒦 G hG
  have hGm : MeasurableSet G := h𝒦le G hG𝒦
  have hX : Integrable (fun ω => h ω φ) P :=
    (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
  have hgi : Integrable (fun ω => g ω φ) P :=
    integrable_condExp.congr (Sec6.IsLocalSetMean.ae_eq_condExp_germSigma hh hA hloc hg φ).symm
  have hYi : Integrable (G.indicator m) P := by
    refine (hgi.indicator hGm).congr ?_
    filter_upwards [hGC] with ω hω
    by_cases hωG : ω ∈ G
    · rw [indicator_of_mem hωG, indicator_of_mem hωG, (hω hωG).2]
    · rw [indicator_of_notMem hωG, indicator_of_notMem hωG]
  have hYm : StronglyMeasurable[𝒥] (G.indicator m) := hm.stronglyMeasurable.indicator hG
  have hK := (ae_condExp_markedOffCover hh hA hℋ hloc hmark hCm hC hg φ).1
  have h1 : P[G.indicator (fun ω => h ω φ) | 𝒥] =ᵐ[P] G.indicator (P[fun ω => h ω φ | 𝒥]) :=
    condExp_indicator hX hG
  have h2 : P[P[G.indicator (fun ω => h ω φ) | markedOffCoverSigma A C ℋ h] | 𝒥] =ᵐ[P]
      P[G.indicator (fun ω => h ω φ) | 𝒥] := condExp_condExp_of_le h𝒥𝒦 h𝒦le
  have h3 : P[G.indicator (fun ω => h ω φ) | markedOffCoverSigma A C ℋ h] =ᵐ[P] G.indicator m := by
    filter_upwards [condExp_indicator (m := markedOffCoverSigma A C ℋ h) hX hG𝒦, hK, hGC] with ω hω hk hgc
    rw [hω]
    by_cases hωG : ω ∈ G
    · rw [indicator_of_mem hωG, indicator_of_mem hωG, hk (hgc hωG).1, (hgc hωG).2]
    · rw [indicator_of_notMem hωG, indicator_of_notMem hωG]
  have h4 : P[G.indicator m | 𝒥] = G.indicator m :=
    condExp_of_stronglyMeasurable (h𝒥𝒦.trans h𝒦le) hYm hYi
  have h5 : P[P[G.indicator (fun ω => h ω φ) | markedOffCoverSigma A C ℋ h] | 𝒥] =ᵐ[P]
      P[G.indicator m | 𝒥] := condExp_congr_ae h3
  filter_upwards [h1, h2, h5] with ω e1 e2 e5 hωG
  have := e1.symm.trans (e2.symm.trans (e5.trans (congrFun h4 ω)))
  rwa [indicator_of_mem hωG, indicator_of_mem hωG] at this

/-- **The marked Proposition 3.9, sandwich form.** In the setting of `ae_condExp_markedOffCover`, for every σ-algebra
`𝒥` with `𝒜 ∨ ℋ ≤ 𝒥 ≤ markedOffCoverSigma A C ℋ h` and every test function `φ`, almost surely on `{supp φ ⊆ C}`,
`E[e^{i(h, φ)} | 𝒥] = e^{i(g, φ)} e^{−σ²_C(φ)/2}`. -/
theorem ae_condExp_exp_eq_of_le_markedOffCover (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet A h P)
    (hmark : IsHistoryAvoidanceLocal ℋ A h P) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g)
    (h𝒥 : germSigma A h ⊔ ℋ ≤ 𝒥) (h𝒥𝒦 : 𝒥 ≤ markedOffCoverSigma A C ℋ h)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ C ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒥] ω =
        Complex.exp (Complex.I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (C ω) φ φ) : ℝ) : ℂ) := by
  have hhm := hh.measurable
  set G : Set Ω := {ω | Disjoint (tsupport φ) (relClosureH (H \ C ω))} with hGdef
  have hG : MeasurableSet[𝒥] G :=
    h𝒥 _ ((sup_le ((comap_le_germSigma A h).trans le_sup_left) le_sup_right :
      MeasurableSpace.comap A hittingSigma ⊔ ℋ ≤ germSigma A h ⊔ ℋ) _
        (hCm (measurableSet_disjoint_relClosureH φ.hasCompactSupport φ.tsupport_subset)))
  have hm : Measurable[𝒥] fun ω => g ω φ :=
    ((measurable_distOn_apply φ).comp hg.1).mono (le_sup_left.trans h𝒥) le_rfl
  have hv : Measurable[𝒥] fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) φ φ :=
    (measurable_comap_zeroGFFTestCov_compl A φ φ).mono
      ((comap_le_germSigma A h).trans (le_sup_left.trans h𝒥)) le_rfl
  have hGsub : ∀ᵐ ω ∂P, (ω ∈ G ↔ tsupport φ ⊆ C ω) ∧ (ω ∈ G →
      zeroGFFTestCov (C ω) φ φ = zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) := by
    filter_upwards [hloc.2.1, hC] with ω ⟨hs, ho⟩ ⟨hCs, hCc⟩
    have hCo := isOpen_of_forall_connectedComponentIn_subset ho hCs hCc
    have hrc : relClosureH (H \ C ω) = H \ C ω := by
      refine relClosureH_eq sdiff_subset ?_
      rw [sdiff_sdiff_cancel_left (hCs.trans sdiff_subset)]; exact hCo
    have hiff : ω ∈ G ↔ tsupport φ ⊆ C ω := by
      simp only [hGdef, mem_ofPred_eq, hrc]
      constructor
      · intro hdis z hz
        by_contra hzC
        exact Set.disjoint_left.1 hdis hz ⟨φ.tsupport_subset hz, hzC⟩
      · intro hsub
        exact Set.disjoint_left.2 fun z hz hz' => hz'.2 (hsub hz)
    refine ⟨hiff, fun hωG => ?_⟩
    rw [relClosureH_eq hs ho, zeroGFFTestCov_eq_of_isClopen ho sdiff_subset hCo hCs
      (isOpen_diff_of_forall_connectedComponentIn_subset ho hCc) φ (hiff.1 hωG)]
  have hf := ae_condExp_exp_eq_of_le_markedOffCover_forget hh hA hℋ hloc hmark hCm hC hg h𝒥𝒦 φ hG hm hv
    (by filter_upwards [hGsub] with ω h1 hωG using ⟨h1.1.1 hωG, rfl, h1.2 hωG⟩)
  filter_upwards [hf, hGsub] with ω h1 h2 hsupp
  rw [h1 (h2.1.2 hsupp), h2.2 (h2.1.2 hsupp)]

/-- **The marked law on `C`** (the case `𝒥 = 𝒜 ∨ ℋ`): given the germs of `A` and the marks, the field on a union
`C` of components of `ℍ ∖ A` chosen from `σ(A) ∨ ℋ` is `𝒞_A + GFF_C`. -/
theorem ae_condExp_exp_marked (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet A h P)
    (hmark : IsHistoryAvoidanceLocal ℋ A h P) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ C ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma A h ⊔ ℋ] ω =
        Complex.exp (Complex.I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (C ω) φ φ) : ℝ) : ℂ) :=
  ae_condExp_exp_eq_of_le_markedOffCover hh hA hℋ hloc hmark hCm hC hg le_rfl
    (le_markedOffCoverSigma_germ C) φ

/-- **The marked Proposition 3.9, second clause** ("`h|_C` is independent of `h|_{D∖C}` given the marked `A`";
Aux. lemma 124's (ER1) with the labels retained): for every test function `φ`, almost surely on `{supp φ ⊆ C}`,
revealing the field off `C` does not change the conditional characteristic function given the marked `A`, and both
are `e^{i(𝒞_A, φ)} e^{−σ²_C(φ)/2}`. -/
theorem ae_condExp_exp_offSigma_marked (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hloc : IsLocalSet A h P)
    (hmark : IsHistoryAvoidanceLocal ℋ A h P) {C : Ω → Set ℂ}
    (hCm : Measurable[MeasurableSpace.comap A hittingSigma ⊔ ℋ, hittingSigma] fun ω => H \ C ω)
    (hC : ∀ᵐ ω ∂P, C ω ⊆ H \ A ω ∧ ∀ z ∈ C ω, connectedComponentIn (H \ A ω) z ⊆ C ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ C ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma A h ⊔ ℋ ⊔ offSigma C h] ω =
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma A h ⊔ ℋ] ω ∧
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | germSigma A h ⊔ ℋ] ω =
        Complex.exp (Complex.I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (C ω) φ φ) : ℝ) : ℂ) := by
  have h1 := ae_condExp_exp_eq_of_le_markedOffCover hh hA hℋ hloc hmark hCm hC hg le_sup_left
    (sup_le (le_markedOffCoverSigma_germ C) (offSigma_le_markedOffCoverSigma C)) φ
  have h2 := ae_condExp_exp_marked hh hA hℋ hloc hmark hCm hC hg φ
  filter_upwards [h1, h2] with ω h1 h2 hsupp
  exact ⟨(h1 hsupp).trans (h2 hsupp).symm, h2 hsupp⟩

end Law

end MarkedProp39
end Sec7
end InteractingSLE
