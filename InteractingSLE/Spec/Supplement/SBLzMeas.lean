/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5Code
import InteractingSLE.Spec.Supplement.SB2Remainder

/-!
# Convention S1 through path codes: S1 events are null-measurable

Packet PROVE-T14-SBLEAVES5, the first half of SB3's measurability inputs (I2), (I2′). Convention S1
(`IsOneSided A β a`: some proper completion of `β|[0, a]` has `A` in its closed right side) is an `∃` over
completions. As for W0's predicate (`Theorem15D5Code`, PROVE-T15-D5), it is coded by dyadic path codes:

* the closed right side of a decoded proper completion is closed, and membership is countable: the seed family and
  rational polygonal reachability from `q 0 0 + 1 − i` (`isClosed_closedRightSide`, `mem_closedRightSide_iff`,
  `mem_closedRightSide_decC_iff`);
* the relation `S1Rel` between `((code of β, dense family of A), a)` and a completion code is Borel
  (`measurableSet_s1Rel`; the prefix length `a` is a coordinate);
* for a continuous `β` and a family `d` with `range d ⊆ A ⊆ closure (range d)`, S1 is the projection of `S1Rel`
  (`isOneSided_iff_exists`);
* `isOneSided_congr` (S1 reads the path only on `[0, a]`);
* hence **`nullMeasurableSet_isOneSided`**: an S1 event is null-measurable as soon as, almost surely, its data are
  read off an a.e.-measurable code (Lusin, `nullMeasurableSet_preimage_setOf_exists`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Lz

open Theorem15D5 Supp9B

/-! ### The closed right side -/

/-- **The closed right side is closed** when the seed-ray closure is. -/
theorem isClosed_closedRightSide {γ : ℝ≥0 → ℂ} (hF : IsClosed (seedRayClosure γ)) :
    IsClosed (closedRightSide γ) := by
  unfold closedRightSide rightSide
  rw [← closure_subset_iff_isClosed, closure_union, hF.closure_eq]
  rintro x (hx | hx)
  · by_cases hxF : x ∈ seedRayClosure γ
    · exact Or.inr hxF
    · left
      obtain ⟨y, hyx, hyC⟩ := mem_closure_iff.mp hx _ (hF.isOpen_compl.connectedComponentIn)
        (mem_connectedComponentIn hxF)
      rw [connectedComponentIn_eq hyC, ← connectedComponentIn_eq hyx]
      exact mem_connectedComponentIn hxF
  · exact Or.inr hx

/-- Points of the closed right side: the seed-ray closure, and the points reached from the base point
`γ 0 + 1 − i` by rational polygonal paths off it. -/
theorem mem_closedRightSide_iff {γ : ℝ≥0 → ℂ} (hF : IsClosed (seedRayClosure γ)) {z : ℂ} :
    z ∈ closedRightSide γ ↔
      z ∈ seedRayClosure γ ∨ ∃ k, Reach (seedRayClosure γ)ᶜ (γ 0 + 1 - Complex.I) k z := by
  unfold closedRightSide rightSide
  rw [mem_union, mem_connectedComponentIn_iff_exists_reach hF.isOpen_compl, or_comm]

/-- Membership in the closed right side of a decoded proper completion, through `seedFamily` and polygonal
reachability from `q 0 0 + 1 − i`. -/
theorem mem_closedRightSide_decC_iff {q : CCode} (h : GoodAll q) (hp : PropC q) (z : ℂ) :
    z ∈ closedRightSide (decC q) ↔ z ∈ closure (range (seedFamily q)) ∨
      ∃ j, Reach (closure (range (seedFamily q)))ᶜ (q 0 0 + 1 - Complex.I) j z := by
  have hF : IsClosed (seedRayClosure (decC q)) := by
    rw [seedRayClosure_decC h hp]; exact isClosed_closure
  rw [mem_closedRightSide_iff hF, seedRayClosure_decC h hp, h.decC_zero]

/-! ### The Borel S1 relation -/

/-- **The S1 relation** between `((code of the prefix path, dense family of the set), prefix length)` and the code of
a proper completion with the family in its closed right side. -/
def S1Rel : Set (((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode) :=
  {x | GoodAll x.1.1.1 ∧ GoodAll x.2 ∧ InjC x.2 ∧ ImC x.2 ∧ PropC x.2 ∧ AgreeC x.2 x.1.1.1 x.1.2 ∧
    ∀ i, x.1.1.2 i ∈ closure (range (seedFamily x.2)) ∨
      ∃ j, Reach (closure (range (seedFamily x.2)))ᶜ (x.2 0 0 + 1 - Complex.I) j (x.1.1.2 i)}

/-- `AgreeC` is measurable jointly in the two codes and the prefix length. -/
theorem measurable_agreeC_joint : Measurable fun x : (CCode × CCode) × ℝ≥0 => AgreeC x.1.1 x.1.2 x.2 := by
  unfold AgreeC
  refine Measurable.forall fun n => Measurable.forall fun k => ?_
  refine (measurableSet_setOfPred.mp (measurableSet_le measurable_const measurable_snd)).imp ?_
  exact measurableSet_setOfPred.mp (measurableSet_eq_fun ((measurable_coord n k).comp measurable_fst.fst)
    ((measurable_coord n k).comp measurable_fst.snd))

/-- **The S1 relation is Borel.** -/
theorem measurableSet_s1Rel : MeasurableSet S1Rel := by
  have m0 : Measurable fun x : ((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode => x.1.1.1 := measurable_fst.fst.fst
  have md : Measurable fun x : ((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode => x.1.1.2 := measurable_fst.fst.snd
  have ma : Measurable fun x : ((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode => x.1.2 := measurable_fst.snd
  have mq : Measurable fun x : ((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode => x.2 := measurable_snd
  have hcq : ∀ n k, Measurable fun x : ((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode => x.2 n k :=
    fun n k => (measurable_coord n k).comp mq
  have hfam : ∀ i, Measurable fun x : ((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode => seedFamily x.2 i :=
    measurable_seedFamily hcq
  have hw : Measurable fun x : ((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode => x.2 0 0 + 1 - Complex.I :=
    ((hcq 0 0).add measurable_const).sub measurable_const
  refine measurableSet_setOfPred.mpr ?_
  refine (measurable_goodAll.comp m0).and <| (measurable_goodAll.comp mq).and <| (measurable_injC.comp mq).and <|
    (measurable_imC.comp mq).and <| (measurable_propC.comp mq).and <|
    (measurable_agreeC_joint.comp ((mq.prodMk m0).prodMk ma)).and ?_
  refine Measurable.forall fun i => ?_
  have hdi : Measurable fun x : ((CCode × (ℕ → ℂ)) × ℝ≥0) × CCode => x.1.1.2 i :=
    (measurable_pi_apply i).comp md
  exact (measurableSet_setOfPred.mp (measurableSet_mem_closure_range hfam hdi)).or
    (Measurable.exists fun j => measurableSet_setOfPred.mp (measurableSet_reach hfam hw j hdi))

/-! ### S1 as a projection -/

/-- **S1 through codes**: for a continuous path `β` and a countable family `d` with `range d ⊆ A ⊆ closure (range d)`,
`IsOneSided A β a` holds iff `((encC β, d), a)` lies in the projection of `S1Rel`. -/
theorem isOneSided_iff_exists {A : Set ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0} {d : ℕ → ℂ} (hβ : Continuous β)
    (hdA : range d ⊆ A) (hAd : A ⊆ closure (range d)) :
    IsOneSided A β a ↔ ∃ y, (((encC β, d), a), y) ∈ S1Rel := by
  have hgβ : GoodAll (encC β) := goodAll_encC hβ
  have hga : GoodC (encC β) a := goodC_encC hβ.continuousOn
  have hdec : decC (encC β) = β := decC_encC_of_continuous hβ
  constructor
  · rintro ⟨β', hβ', hA⟩
    have hg' : GoodAll (encC β') := goodAll_encC hβ'.1
    have hdec' : decC (encC β') = β' := decC_encC_of_continuous hβ'.1
    have hc := (isProperCompletion_decC_iff hga hg').mp (by rw [hdec, hdec']; exact hβ')
    refine ⟨encC β', hgβ, hg', hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, fun i => ?_⟩
    have hi : d i ∈ closedRightSide (decC (encC β')) := by
      rw [hdec']; exact hA (hdA (mem_range_self i))
    exact (mem_closedRightSide_decC_iff hg' hc.2.2.1 _).mp hi
  · rintro ⟨y, -, hgy, hinj, him, hprop, hagree, hmem⟩
    have hc := (isProperCompletion_decC_iff hga hgy).mpr ⟨hinj, him, hprop, hagree⟩
    rw [hdec] at hc
    refine ⟨decC y, hc, ?_⟩
    have hF : IsClosed (seedRayClosure (decC y)) := by
      rw [seedRayClosure_decC hgy hprop]; exact isClosed_closure
    refine hAd.trans (closure_minimal ?_ (isClosed_closedRightSide hF))
    rintro _ ⟨i, rfl⟩
    exact (mem_closedRightSide_decC_iff hgy hprop _).mpr (hmem i)

/-- S1 for a prefix depends on the path only on `[0, a]`. -/
theorem isOneSided_congr {A : Set ℂ} {β β' : ℝ≥0 → ℂ} {a : ℝ≥0} (h : ∀ t ≤ a, β t = β' t)
    (hS : IsOneSided A β a) : IsOneSided A β' a := by
  obtain ⟨γ, ⟨h1, h2, h3, h4, h5⟩, hA⟩ := hS
  exact ⟨γ, ⟨h1, h2, h3, h4, fun t ht => (h5 t ht).trans (h t ht)⟩, hA⟩

/-- **S1 events are null-measurable** when their data are, almost surely, read off an a.e.-measurable code: if
`Z ω = ((encC (β ω), d ω), a ω)` almost surely, with `β ω` continuous and `range (d ω) ⊆ A ω ⊆ closure (range (d ω))`,
then `{ω | IsOneSided (A ω) (β ω) (a ω)}` is null-measurable. -/
theorem nullMeasurableSet_isOneSided {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {A : Ω → Set ℂ} {β : Ω → ℝ≥0 → ℂ} {a : Ω → ℝ≥0} {d : Ω → ℕ → ℂ}
    {Z : Ω → (CCode × (ℕ → ℂ)) × ℝ≥0} (hZ : AEMeasurable Z P)
    (hrep : ∀ᵐ ω ∂P, Z ω = ((encC (β ω), d ω), a ω) ∧ Continuous (β ω) ∧ range (d ω) ⊆ A ω ∧
      A ω ⊆ closure (range (d ω))) :
    NullMeasurableSet {ω | IsOneSided (A ω) (β ω) (a ω)} P := by
  have hS : NullMeasurableSet {ω | ∃ y, (Z ω, y) ∈ S1Rel} P :=
    nullMeasurableSet_preimage_setOf_exists hZ measurableSet_s1Rel
  refine hS.congr ?_
  refine Filter.eventuallyEqSet_iff.mpr ?_
  filter_upwards [hrep] with ω ⟨hz, hc, hdA, hAd⟩
  change (∃ y, (Z ω, y) ∈ S1Rel) ↔ IsOneSided (A ω) (β ω) (a ω)
  rw [hz]
  exact (isOneSided_iff_exists hc hdA hAd).symm

end InteractingSLE.Theorem14.SB.Lz
