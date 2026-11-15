/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeFieldMarked
import InteractingSLE.Spec.Coupling.WholeFieldCoding
import InteractingSLE.Spec.Coupling.WholeField2Code

/-!
# The history-marked union of two conditionally independent local sets

Packet PROVE-WW-B18 (step B3 of the contact step, the field side). Proposition 3.7 (the conditionally independent
union of local sets) with **retained histories**: if `A₁` satisfies the history-marked avoidance criterion
(`WholeField.IsHistoryAvoidanceLocal`, Aux. lemma 18) for marks `ℋ₁`, `A₂` for marks `ℋ₂`, and the two pairs
`(A₁, ℋ₁)`, `(A₂, ℋ₂)` are read from σ-algebras `𝒜₁`, `𝒜₂` that are conditionally independent given the field, then
`A₁ ∪ A₂` satisfies the criterion for the joint marks `ℋ₁ ∨ ℋ₂`.

Proof: for product marks `F₁ ∩ F₂` the marked avoidance event of the union is the intersection of the two marked
avoidance events, whose conditional probability given the field is the product of the two (conditional
independence), a function of `h − G h` by the criterion for each set ("the conditional law of `(R₁, R₂)` given `h` is
the product of those two kernels. It also depends only on `Y`", specification p. 57). The class of marks for which the
conclusion holds is a Dynkin system (complements by linearity; countable disjoint unions by the finite case
`exists_condExp_biUnion_eq_comp` and the limit step `exists_condExp_eq_comp_of_tendsto`), so the π–λ theorem extends it
from the products to `ℋ₁ ∨ ℋ₂`.

## Main results

* `generateFrom_interSets`: the products `F₁ ∩ F₂` form a π-system generating `ℋ₁ ∨ ℋ₂`;
* **`isHistoryAvoidanceLocal_union`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open scoped ENNReal

namespace InteractingSLE.WangWu

open WholeField LocalSets

/-! ### Product marks -/

section Product

variable {Ω : Type*}

/-- The products `F₁ ∩ F₂` of events of `ℋ₁` and `ℋ₂`. -/
def interSets (ℋ₁ ℋ₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[ℋ₁] a ∧ MeasurableSet[ℋ₂] b ∧ s = a ∩ b}

theorem isPiSystem_interSets (ℋ₁ ℋ₂ : MeasurableSpace Ω) : IsPiSystem (interSets ℋ₁ ℋ₂) := by
  rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩ -
  refine ⟨a ∩ a', b ∩ b', ha.inter ha', hb.inter hb', ?_⟩
  ext ω
  simp only [mem_inter_iff]
  tauto

theorem generateFrom_interSets (ℋ₁ ℋ₂ : MeasurableSpace Ω) :
    ℋ₁ ⊔ ℋ₂ = MeasurableSpace.generateFrom (interSets ℋ₁ ℋ₂) := by
  refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
  · intro a ha
    exact MeasurableSpace.measurableSet_generateFrom ⟨a, univ, ha, MeasurableSet.univ, (inter_univ a).symm⟩
  · intro b hb
    exact MeasurableSpace.measurableSet_generateFrom ⟨univ, b, MeasurableSet.univ, hb, (univ_inter b).symm⟩
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact (le_sup_left (b := ℋ₂) a ha).inter (le_sup_right (a := ℋ₁) b hb)

end Product

/-! ### The union lemma -/

section Union

variable {Ω : Type*} {𝒜₁ 𝒜₂ ℋ₁ ℋ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Proposition 3.7 with retained histories.** Let `A₁`, `A₂` be hitting-measurable for σ-algebras `𝒜₁`, `𝒜₂`
which are conditionally independent given the field `h`, and let `A_i` satisfy the history-marked avoidance criterion
for marks `ℋ_i ≤ 𝒜_i`. Then `A₁ ∪ A₂` satisfies the history-marked avoidance criterion for `ℋ₁ ∨ ℋ₂`. -/
theorem isHistoryAvoidanceLocal_union (h𝒜₁ : 𝒜₁ ≤ mΩ) (h𝒜₂ : 𝒜₂ ≤ mΩ)
    (hℋ₁ : ℋ₁ ≤ 𝒜₁) (hℋ₂ : ℋ₂ ≤ 𝒜₂) {A₁ A₂ : Ω → Set ℂ} (hA₁ : Measurable[𝒜₁, hittingSigma] A₁)
    (hA₂ : Measurable[𝒜₂, hittingSigma] A₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance) 𝒜₁ 𝒜₂ P)
    (h₁ : IsHistoryAvoidanceLocal ℋ₁ A₁ h P) (h₂ : IsHistoryAvoidanceLocal ℋ₂ A₂ h P) :
    IsHistoryAvoidanceLocal (ℋ₁ ⊔ ℋ₂) (fun ω => A₁ ω ∪ A₂ ω) h P := by
  intro U G hUH hG hd F hF
  set D : Set Ω := {ω | Disjoint (A₁ ω ∪ A₂ ω) (U : Set ℂ)} with hD
  have hav := measurableSet_avoid U.isOpen hUH
  have hD₁ : MeasurableSet[𝒜₁] {ω | Disjoint (A₁ ω) (U : Set ℂ)} := hA₁ hav
  have hD₂ : MeasurableSet[𝒜₂] {ω | Disjoint (A₂ ω) (U : Set ℂ)} := hA₂ hav
  have hDm : MeasurableSet D := by
    have e : D = {ω | Disjoint (A₁ ω) (U : Set ℂ)} ∩ {ω | Disjoint (A₂ ω) (U : Set ℂ)} := by
      ext ω; simp only [hD, mem_ofPred_eq, mem_inter_iff, disjoint_union_left]
    rw [e]
    exact (h𝒜₁ _ hD₁).inter (h𝒜₂ _ hD₂)
  have hsup : ℋ₁ ⊔ ℋ₂ ≤ mΩ := sup_le (hℋ₁.trans h𝒜₁) (hℋ₂.trans h𝒜₂)
  -- the products
  have hbasic : ∀ a b, MeasurableSet[ℋ₁] a → MeasurableSet[ℋ₂] b →
      ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
        P⟦D ∩ (a ∩ b) | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P] fun ω => g (markovCompl G (h ω)) := by
    intro a b ha hb
    obtain ⟨g₁, hg₁, hge₁⟩ := h₁ U G hUH hG hd a ha
    obtain ⟨g₂, hg₂, hge₂⟩ := h₂ U G hUH hG hd b hb
    have e : D ∩ (a ∩ b) = ({ω | Disjoint (A₁ ω) (U : Set ℂ)} ∩ a) ∩ ({ω | Disjoint (A₂ ω) (U : Set ℂ)} ∩ b) := by
      ext ω
      simp only [hD, mem_ofPred_eq, mem_inter_iff, disjoint_union_left]
      tauto
    refine ⟨fun y => g₁ y * g₂ y, hg₁.mul hg₂, ?_⟩
    rw [e]
    filter_upwards [hci _ _ (hD₁.inter (hℋ₁ a ha)) (hD₂.inter (hℋ₂ b hb)), hge₁, hge₂] with ω h0 h1 h2
    rw [h0, Pi.mul_apply, h1, h2]
  -- the Dynkin argument
  refine MeasurableSpace.induction_on_inter (m := ℋ₁ ⊔ ℋ₂)
    (C := fun F _ => ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
      P⟦D ∩ F | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P] fun ω => g (markovCompl G (h ω)))
    (generateFrom_interSets ℋ₁ ℋ₂) (isPiSystem_interSets ℋ₁ ℋ₂) ?_ ?_ ?_ ?_ F hF
  · refine ⟨fun _ => 0, measurable_const, ?_⟩
    rw [inter_empty, indicator_empty, show (fun _ : Ω => (0 : ℝ)) = 0 from rfl, condExp_zero]
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact hbasic a b ha hb
  · rintro t htm ⟨g, hg, hge⟩
    obtain ⟨gU, hgU, hgeU⟩ := hbasic univ univ MeasurableSet.univ MeasurableSet.univ
    simp only [inter_univ] at hgeU
    have htm' : MeasurableSet t := hsup t htm
    refine ⟨fun y => gU y - g y, hgU.sub hg, ?_⟩
    have hind : (D ∩ tᶜ).indicator (fun _ => (1 : ℝ)) =
        D.indicator (fun _ => (1 : ℝ)) - (D ∩ t).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h1 : ω ∈ D <;> by_cases h2 : ω ∈ t <;> simp [h1, h2]
    rw [hind]
    filter_upwards [condExp_sub (m := MeasurableSpace.comap h inferInstance) ((integrable_const (1 : ℝ)).indicator hDm)
      ((integrable_const (1 : ℝ)).indicator (hDm.inter htm')), hgeU, hge] with ω h0 h1 h2
    rw [h0, Pi.sub_apply, h1, h2]
  · intro f hdisj hfm hf
    have hfm' : ∀ i, MeasurableSet (f i) := fun i => hsup _ (hfm i)
    have hEm : ∀ i, MeasurableSet (D ∩ f i) := fun i => hDm.inter (hfm' i)
    set Es : ℕ → Set Ω := fun k => ⋃ j ∈ Finset.range k, D ∩ f j with hEs
    have hEsm : ∀ k, MeasurableSet (Es k) := fun k =>
      Finset.measurableSet_biUnion _ fun j _ => hEm j
    have hEU : D ∩ ⋃ i, f i = ⋃ k, Es k := by
      ext ω
      simp only [hEs, mem_inter_iff, mem_iUnion, Finset.mem_range]
      constructor
      · rintro ⟨hD', i, hi⟩
        exact ⟨i + 1, i, Nat.lt_succ_self i, hD', hi⟩
      · rintro ⟨k, i, -, hD', hi⟩
        exact ⟨hD', i, hi⟩
    have hEsub : ∀ k, Es k ⊆ D ∩ ⋃ i, f i := fun k => by
      rw [hEU]; exact subset_iUnion Es k
    have hmono : Monotone Es := fun k k' hkk' => biUnion_subset_biUnion_left
      (fun j hj => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) hkk'))
    refine exists_condExp_eq_comp_of_tendsto (m := MeasurableSpace.comap h inferInstance)
      (hDm.inter (MeasurableSet.iUnion hfm')) hEsm ?_ fun k => ?_
    · have e : ∀ k, symmDiff (Es k) (D ∩ ⋃ i, f i) = (D ∩ ⋃ i, f i) \ Es k := fun k => by
        rw [symmDiff_def, sup_eq_right.2 (by rw [sdiff_eq_empty.2 (hEsub k)]; exact bot_le)]
      simp_rw [e]
      have hanti : Antitone fun k => (D ∩ ⋃ i, f i) \ Es k := fun k k' hkk' =>
        sdiff_subset_sdiff_right (hmono hkk')
      have hlim := tendsto_measure_iInter_atTop (μ := P)
        (fun k => ((hDm.inter (MeasurableSet.iUnion hfm')).diff (hEsm k)).nullMeasurableSet) hanti
        ⟨0, measure_ne_top _ _⟩
      have hempty : (⋂ k, (D ∩ ⋃ i, f i) \ Es k) = ∅ := by
        rw [← sdiff_iUnion, ← hEU, sdiff_self]
      rwa [hempty, measure_empty] at hlim
    · refine exists_condExp_biUnion_eq_comp (m := MeasurableSpace.comap h inferInstance) (Finset.range k) hEm
        (Eventually.of_forall fun ω i _ j _ hij hω => ?_) fun j _ => hf j
      exact Set.disjoint_left.1 (hdisj hij) hω.1.2 hω.2.2

end Union

end InteractingSLE.WangWu
