/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFilled
import InteractingSLE.Spec.Restart.FCDetTransfer

/-!
# Finite measurable splitting by force-word type

Packet PROVE-RETPLUMB. Bounded numbers of marks and a finite palette of weights
give finitely many types. Their Borel type sets yield a disjoint measurable
partition. The hypotheses on the palette are explicit; no finiteness claim is
made for arbitrary real-valued boundary words.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

/-- The discrete data kept fixed when applying stopped K2. -/
structure ForceWordType where
  nL : ℕ
  nR : ℕ
  rhoL : Fin nL → ℝ
  rhoR : Fin nR → ℝ

/-- A finite space of possible force-word types. Positions are not part of a type. -/
abbrev BoundedForceTypes (N : ℕ) (weights : Finset ℝ) :=
  Σ nL : Fin (N + 1), Σ nR : Fin (N + 1),
    (Fin nL.val → ↥weights) × (Fin nR.val → ↥weights)

/-- Forget the finite-palette membership proofs. -/
def boundedForceType (N : ℕ) (weights : Finset ℝ) (i : BoundedForceTypes N weights) : ForceWordType :=
  ⟨i.1.val, i.2.1.val, fun j => (i.2.2.1 j).val, fun j => (i.2.2.2 j).val⟩

/-- The Borel set of words of one discrete type. -/
def forceTypeSet (κ θ : ℝ) (a : ForceWordType) : Set BoundaryWord :=
  FCDet.typeSet κ θ a.nL a.nR a.rhoL a.rhoR

theorem measurableSet_forceTypeSet (κ θ : ℝ) (a : ForceWordType) :
    MeasurableSet (forceTypeSet κ θ a) :=
  FCDet.measurableSet_typeSet κ θ a.nL a.nR a.rhoL a.rhoR

/-- Explicit sufficient finite-palette inputs for a single word. The weights
are the existing padded flow-word coordinates, restricted to actual marks. -/
def HasBoundedForceType (κ θ : ℝ) (N : ℕ) (weights : Finset ℝ) (c : BoundaryWord) : Prop :=
  flowLineNL c.fn c.jumps 0 ≤ N ∧ flowLineNR c.fn c.jumps 0 ≤ N ∧
    (∀ i : Fin (flowLineNL c.fn c.jumps 0), (flowPad κ θ (c, 0)).2.1 i ∈ weights) ∧
    ∀ j : Fin (flowLineNR c.fn c.jumps 0), (flowPad κ θ (c, 0)).2.2 j ∈ weights

open scoped Classical in
/-- All possible seed weights and jump weights from a finite height palette. -/
def flowWeightPalette (κ θ : ℝ) (heights : Finset ℝ) : Finset ℝ :=
  (heights.image (fun a => -(a + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) ∪
    heights.image (fun a => (a + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)) ∪
      (heights.product heights).image (fun p => (p.1 - p.2) / sleLambda κ)

/-- Counts and weights of a bounded-length word with finitely many heights are
bounded uniformly, without assumptions on the positions or sortedness. -/
theorem hasBoundedForceType_of_heights {κ θ : ℝ} {N : ℕ} {heights : Finset ℝ}
    {c : BoundaryWord} (hN : c.1 ≤ N) (hh : ∀ j ≤ c.1, c.2.2 j ∈ heights) :
    HasBoundedForceType κ θ (N + 1) (flowWeightPalette κ θ heights) c := by
  classical
  open PiecewiseConstantBoundaryData in
    have hL : ∀ y, leftLim c.fn y ∈ heights := by
      intro y
      rw [c.leftLim_fn]
      apply hh
      simpa only [BoundaryWord.index, Finset.card_range] using
        (Finset.card_filter_le (Finset.range c.1) (fun i => c.2.1 i < y))
    have hR : ∀ y, rightLim c.fn y ∈ heights := by
      intro y
      rw [c.rightLim_fn]
      apply hh
      simpa only [BoundaryWord.indexLE, Finset.card_range] using
        (Finset.card_filter_le (Finset.range c.1) (fun i => c.2.1 i ≤ y))
    have hcard : c.jumps.card ≤ c.1 :=
      (Finset.card_image_le).trans_eq (Finset.card_range _)
    have hnl : flowLineNL c.fn c.jumps 0 ≤ N + 1 := by
      apply Nat.add_le_add_right
      exact ((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)).trans (hcard.trans hN)
    have hnr : flowLineNR c.fn c.jumps 0 ≤ N + 1 := by
      apply Nat.add_le_add_right
      exact ((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)).trans (hcard.trans hN)
    have hjump : ∀ y, (rightLim c.fn y - leftLim c.fn y) / sleLambda κ ∈ flowWeightPalette κ θ heights := by
      intro y
      exact Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(rightLim c.fn y, leftLim c.fn y), Finset.mem_product.2 ⟨hR y, hL y⟩, rfl⟩)
    refine ⟨hnl, hnr, ?_, ?_⟩
    · intro i
      simp only [flowPad, i.2, ↓reduceDIte]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hL 0)))
      · exact hjump _
    · intro i
      simp only [flowPad, i.2, ↓reduceDIte]
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hR 0)))
      · exact hjump _

open scoped Classical in
/-- The fixed finite palette of retained boundary heights. -/
def retainedHeightPalette (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) : Finset ℝ :=
  (Finset.range (c₀.1 + 1)).image c₀.2.2 ∪ {g₁, g₂, g₃, g₄}

/-- The word builder has uniformly bounded length and only the prescribed
heights. No ordering assumption on the four counts is needed for this bound. -/
theorem zbuild_length_heights (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ)
    {k₁ k₂ k₃ k₄ : ℕ} (h₁ : k₁ ≤ c₀.1) (h₂ : k₂ ≤ c₀.1)
    (h₃ : k₃ ≤ c₀.1) (h₄ : k₄ ≤ c₀.1) (Tp : ℕ → ℝ) (L₂ R₂ L₁ M₁ R₁ : ℝ) :
    let c := Sec7.Lemma76G.zbuild c₀ g₁ g₂ g₃ g₄ k₁ k₂ k₃ k₄ Tp L₂ R₂ L₁ M₁ R₁
    c.1 ≤ 3 * c₀.1 + 6 ∧ ∀ j ≤ c.1, c.2.2 j ∈ retainedHeightPalette c₀ g₁ g₂ g₃ g₄ := by
  classical
  have hbase : ∀ j ≤ c₀.1, c₀.2.2 j ∈ retainedHeightPalette c₀ g₁ g₂ g₃ g₄ := by
    intro j hj
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))
  dsimp only [Sec7.Lemma76G.zbuild]
  constructor
  · omega
  · intro j hj
    split_ifs
    all_goals first
      | (apply hbase; omega)
      | simp only [retainedHeightPalette, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto

/-- Every explicit retained word has a uniformly bounded force type, on all
samples. The finite palette is independent of the chart and all positions. -/
theorem hasBoundedForceType_wordM {Ω : Type*} (d : Supp7.RetData Ω)
    (κ θ : ℝ) (c₀ : BoundaryWord) (g₁ g₂ g₃ g₄ : ℝ) (ω : Ω) :
    HasBoundedForceType κ θ (3 * c₀.1 + 7)
      (flowWeightPalette κ θ (retainedHeightPalette c₀ g₁ g₂ g₃ g₄))
      (Sec7.Lemma76G.wordM d c₀ g₁ g₂ g₃ g₄ ω) := by
  have hlt : ∀ y, Sec7.Lemma76G.cntLt c₀ y ≤ c₀.1 := by
    intro y
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hle : ∀ y, Sec7.Lemma76G.cntLe c₀ y ≤ c₀.1 := by
    intro y
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hword := zbuild_length_heights c₀ g₁ g₂ g₃ g₄
    (hlt (Sec7.Lemma76G.A₂ d ω)) (hle (Sec7.Lemma76G.B₂ d ω))
    (hlt (Sec7.Lemma76G.A₁ d ω)) (hle (Sec7.Lemma76G.B₁ d ω)) (fun _ => 0) 0 0 0 0 0
  exact hasBoundedForceType_of_heights hword.1 hword.2

/-- Bounded counts and a finite palette produce a member of the finite type space. -/
theorem exists_boundedForceType {κ θ : ℝ} {N : ℕ} {weights : Finset ℝ} {c : BoundaryWord}
    (hc : HasBoundedForceType κ θ N weights c) :
    ∃ i : BoundedForceTypes N weights, c ∈ forceTypeSet κ θ (boundedForceType N weights i) := by
  refine ⟨⟨⟨_, Nat.lt_succ_of_le hc.1⟩, ⟨_, Nat.lt_succ_of_le hc.2.1⟩,
    (fun i => ⟨_, hc.2.2.1 i⟩), (fun j => ⟨_, hc.2.2.2 j⟩)⟩, ?_⟩
  exact ⟨rfl, rfl, (fun _ => rfl), fun _ => rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Disjointify a finite measurable cover, retaining the original index labels. -/
theorem exists_measurable_finite_partition {n : ℕ} {S : Fin n → Set Ω} {F : Set Ω}
    (hm : ∀ i, MeasurableSet (S i)) (hcover : ⋃ i, S i = F) :
    ∃ M : Fin n → Set Ω, (∀ i, MeasurableSet (M i)) ∧
      Pairwise (fun i j => Disjoint (M i) (M j)) ∧ (⋃ i, M i) = F ∧ ∀ i, M i ⊆ S i := by
  let M : Fin n → Set Ω := fun i => S i \ ⋃ j : Fin n, ⋃ (_ : j < i), S j
  refine ⟨M, (fun i => (hm i).diff (MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun _ => hm j)), ?_, ?_, fun _ => sdiff_subset⟩
  · intro i j hij
    refine Set.disjoint_left.2 fun ω hi hj => ?_
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hj.2 (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hlt, hi.1⟩⟩)
    · exact hi.2 (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hgt, hj.1⟩⟩)
  · rw [← hcover]
    ext ω
    constructor
    · intro hω
      obtain ⟨i, hi⟩ := mem_iUnion.1 hω
      exact mem_iUnion.2 ⟨i, hi.1⟩
    · intro hω
      obtain ⟨i, hi, hmin⟩ := Set.exists_min_image {i : Fin n | ω ∈ S i}
        (fun i => i) (Set.toFinite _) (mem_iUnion.1 hω)
      refine mem_iUnion.2 ⟨i, hi, ?_⟩
      intro hh
      obtain ⟨j, hj⟩ := mem_iUnion.1 hh
      obtain ⟨hji, hωj⟩ := mem_iUnion.1 hj
      exact (not_le_of_gt hji) (hmin j hωj)

/-- Finite measurable force-type partition of a retained event. Repeated type
labels are harmless because the cover is disjointified before it is used. -/
theorem exists_finite_forceType_partition {κ θ : ℝ} {N : ℕ} {weights : Finset ℝ}
    {c : Ω → BoundaryWord} {F : Set Ω} (hc : Measurable c) (hF : MeasurableSet F)
    (hbound : ∀ ω ∈ F, HasBoundedForceType κ θ N weights (c ω)) :
    ∃ (n : ℕ) (a : Fin n → ForceWordType) (M : Fin n → Set Ω),
      (∀ i, MeasurableSet (M i)) ∧ Pairwise (fun i j => Disjoint (M i) (M j)) ∧
        (⋃ i, M i) = F ∧ ∀ i, M i ⊆ F ∩ c ⁻¹' forceTypeSet κ θ (a i) := by
  let e := Fintype.equivFin (BoundedForceTypes N weights)
  let a := fun i => boundedForceType N weights (e.symm i)
  let S := fun i => F ∩ c ⁻¹' forceTypeSet κ θ (a i)
  have hcover : ⋃ i, S i = F := by
    apply Subset.antisymm (iUnion_subset fun _ => inter_subset_left)
    intro ω hω
    obtain ⟨j, hj⟩ := exists_boundedForceType (hbound ω hω)
    refine mem_iUnion.2 ⟨e j, hω, ?_⟩
    simpa only [mem_preimage, a, Equiv.symm_apply_apply] using hj
  obtain ⟨M, hMm, hMd, hMF, hMS⟩ := exists_measurable_finite_partition
    (fun i => hF.inter (hc (measurableSet_forceTypeSet κ θ (a i)))) hcover
  exact ⟨_, a, M, hMm, hMd, hMF, hMS⟩

/-- The retained explicit word splits any measurable event into finitely many
measurable parts of fixed force type. Only measurability of the chosen word
version in the desired sigma-algebra remains an input. -/
theorem exists_finite_retWord_partition {κ θ₁ θ₂ : ℝ} {c₀ : BoundaryWord}
    {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {u r : ℝ≥0} {F : Set Ω}
    (hc : Measurable (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r)) (hF : MeasurableSet F) :
    ∃ (n : ℕ) (a : Fin n → ForceWordType) (M : Fin n → Set Ω),
      (∀ i, MeasurableSet (M i)) ∧ Pairwise (fun i j => Disjoint (M i) (M j)) ∧
        (⋃ i, M i) = F ∧ ∀ i, M i ⊆ F ∩
          (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r) ⁻¹' forceTypeSet κ θ₂ (a i) := by
  apply exists_finite_forceType_partition hc hF
    (N := 3 * c₀.1 + 7)
    (weights := flowWeightPalette κ θ₂ (retainedHeightPalette c₀
      (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)))
  intro ω _
  exact hasBoundedForceType_wordM _ _ _ _ _ _ _ _ _

/-- On each type part, the existing Borel position readers supply the exact
typed positions; globally their force-word order and signs already hold. -/
theorem forceType_positions {κ θ : ℝ} {c : Ω → BoundaryWord} (hc : Measurable c)
    (a : ForceWordType) {M : Set Ω} (hM : M ⊆ c ⁻¹' forceTypeSet κ θ a) :
    Measurable (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) ∧
      Measurable (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) ∧
      (∀ ω, IsOrderedForceWord
        (FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω))
        (FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω))) ∧
      ∀ ω ∈ M, FCDet.IsFlowType κ θ (c ω)
        (FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (c ω))
        (FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (c ω)) a.rhoL a.rhoR :=
  ⟨(FCDet.measurable_typeXL κ θ a.nL a.nR a.rhoL a.rhoR).comp hc,
    (FCDet.measurable_typeXR κ θ a.nL a.nR a.rhoL a.rhoR).comp hc,
    (fun ω => FCDet.isOrderedForceWord_typeXL (c ω)),
    fun _ hω => FCDet.isFlowType_of_mem_typeSet (hM hω)⟩

end InteractingSLE.Restart.RetAux79
