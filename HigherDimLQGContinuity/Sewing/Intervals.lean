import HigherDimLQGContinuity.Core.Interfaces
import Mathlib.Topology.Order.IntermediateValue

/-!
# Finite covers of a compact interval by relative open intervals

This file proves the corrected interval-cover combinatorics of ruling N17.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set

/-- A relatively open interval of `[s,t]`, presented by its ambient open endpoints. -/
def sewInterval {ι : Type*} (s t : ℝ) (a b : ι → ℝ) (i : ι) : Set ℝ :=
  Ioo (a i) (b i) ∩ Icc s t

private theorem sewInterval_subset {ι : Type*} (s t : ℝ) (a b : ι → ℝ)
    (i : ι) : sewInterval s t a b i ⊆ Icc s t := fun _ hx => hx.2

private theorem sewInterval_mono {ι : Type*} (s t : ℝ) (a b : ι → ℝ)
    {i j : ι} (ha : a i ≤ a j) (hb : b j ≤ b i) :
    sewInterval s t a b j ⊆ sewInterval s t a b i := by
  intro x hx
  exact ⟨⟨lt_of_le_of_lt ha hx.1.1, lt_of_lt_of_le hx.1.2 hb⟩, hx.2⟩

/-- A finite relative-interval cover has an inclusion-minimal subcover. Each retained
interval has a private point of `[s,t]`. -/
private theorem sew_exists_minimal_cover {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (F : Finset ι)
    (hcov : Icc s t ⊆ ⋃ i ∈ F, sewInterval s t a b i) :
    ∃ S : Finset ι, S ⊆ F ∧
      Icc s t ⊆ ⋃ i ∈ S, sewInterval s t a b i ∧
      (∀ i ∈ S, ¬ Icc s t ⊆ ⋃ j ∈ S.erase i, sewInterval s t a b j) ∧
      (∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
        ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j) := by
  classical
  let C : Finset (Finset ι) :=
    F.powerset.filter (fun S => Icc s t ⊆ ⋃ i ∈ S, sewInterval s t a b i)
  have hC : C.Nonempty := ⟨F, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset_self F, hcov⟩⟩
  obtain ⟨S, hSC, hmin⟩ := C.exists_min_image Finset.card hC
  obtain ⟨hSF, hcover⟩ := Finset.mem_filter.mp hSC
  have herase : ∀ i ∈ S, ¬ Icc s t ⊆ ⋃ j ∈ S.erase i, sewInterval s t a b j := by
    intro i hi h
    have hmem : S.erase i ∈ C := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset i S).trans
        (Finset.mem_powerset.mp hSF)), h⟩
    have hle := hmin _ hmem
    have hlt := Finset.card_erase_lt_of_mem hi
    omega
  refine ⟨S, Finset.mem_powerset.mp hSF, hcover, herase, ?_⟩
  intro i hi
  have hnot := herase i hi
  obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hji : j = i := by
    by_contra hne
    exact hxnot (Set.mem_iUnion₂.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hne, hj⟩, hxj⟩)
  subst j
  refine ⟨x, hxj, ?_⟩
  intro j hj hne hxj'
  exact hxnot (Set.mem_iUnion₂.mpr
    ⟨j, Finset.mem_erase.mpr ⟨hne, hj⟩, hxj'⟩)

private theorem sew_no_subset {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    ¬ sewInterval s t a b i ⊆ sewInterval s t a b j := by
  obtain ⟨x, hx, hxprivate⟩ := hprivate i hi
  intro hsub
  exact hxprivate j hj hij.symm (hsub hx)

private theorem sew_endpoint_order {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    a i < a j ↔ b i < b j := by
  constructor
  · intro ha
    by_contra h
    have hb : b j ≤ b i := le_of_not_gt h
    exact sew_no_subset s t a b S hprivate hj hi hij.symm
      (sewInterval_mono s t a b ha.le hb)
  · intro hb
    by_contra h
    have ha : a j ≤ a i := le_of_not_gt h
    exact sew_no_subset s t a b S hprivate hi hj hij
      (sewInterval_mono s t a b ha hb.le)

private theorem sew_left_ne {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) : a i ≠ a j := by
  intro ha
  rcases lt_trichotomy (b i) (b j) with hb | hb | hb
  · exact (sew_no_subset s t a b S hprivate hi hj hij)
      (sewInterval_mono s t a b ha.ge hb.le)
  · exact (sew_no_subset s t a b S hprivate hi hj hij)
      (sewInterval_mono s t a b ha.ge hb.le)
  · exact (sew_no_subset s t a b S hprivate hj hi hij.symm)
      (sewInterval_mono s t a b ha.le hb.le)

/-- A third indispensable interval cannot lie between two intersecting ones. -/
private theorem sew_no_inter_of_between {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j)
    {i k j : ι} (hi : i ∈ S) (hk : k ∈ S) (hj : j ∈ S)
    (hik : a i < a k) (hkj : a k < a j) :
    ¬ (sewInterval s t a b i ∩ sewInterval s t a b j).Nonempty := by
  have hbik : b i < b k :=
    (sew_endpoint_order s t a b S hprivate hi hk
      (by intro h; subst k; exact (lt_irrefl _ hik))).mp hik
  have hbkj : b k < b j :=
    (sew_endpoint_order s t a b S hprivate hk hj
      (by intro h; subst j; exact (lt_irrefl _ hkj))).mp hkj
  intro hmeet
  obtain ⟨y, hyi, hyj⟩ := hmeet
  have hbridge : a j < b i := lt_trans hyj.1.1 hyi.1.2
  obtain ⟨x, hxk, hxprivate⟩ := hprivate k hk
  by_cases hxb : x < b i
  · have hxi : x ∈ sewInterval s t a b i :=
      ⟨⟨lt_trans hik hxk.1.1, hxb⟩, hxk.2⟩
    exact hxprivate i hi (by intro h; subst i; exact (lt_irrefl _ hik)) hxi
  · have hxj : x ∈ sewInterval s t a b j :=
      ⟨⟨lt_of_lt_of_le hbridge (le_of_not_gt hxb),
         lt_trans hxk.1.2 hbkj⟩, hxk.2⟩
    exact hxprivate j hj (by intro h; subst j; exact (lt_irrefl _ hkj)) hxj

private theorem sew_inter_of_cross {ι : Type*} (s t : ℝ) (hst : s < t) (a b : ι → ℝ)
    {i j : ι} (hi : (sewInterval s t a b i).Nonempty)
    (hj : (sewInterval s t a b j).Nonempty)
    (hai : a i < a j) (hbij : b i < b j)
    (haj : a j < b i) :
    (sewInterval s t a b i ∩ sewInterval s t a b j).Nonempty := by
  obtain ⟨xi, hxi⟩ := hi
  obtain ⟨xj, hxj⟩ := hj
  have hlo : max (a j) s < min (b i) t := by
    apply max_lt
    · apply lt_min haj (lt_of_lt_of_le hxj.1.1 hxj.2.2)
    · apply lt_min (lt_of_le_of_lt hxi.2.1 hxi.1.2) hst
  obtain ⟨x, hxl, hxu⟩ := exists_between hlo
  refine ⟨x, ?_, ?_⟩
  · exact ⟨⟨lt_trans hai (lt_of_le_of_lt (le_max_left _ _) hxl),
       lt_of_lt_of_le hxu (min_le_left _ _)⟩,
       ⟨lt_of_le_of_lt (le_max_right _ _) hxl |>.le,
        (lt_of_lt_of_le hxu (min_le_right _ _)).le⟩⟩
  · exact ⟨⟨lt_of_le_of_lt (le_max_left _ _) hxl,
       lt_trans (lt_of_lt_of_le hxu (min_le_left _ _)) hbij⟩,
       ⟨(lt_of_le_of_lt (le_max_right _ _) hxl).le,
        (lt_of_lt_of_le hxu (min_le_right _ _)).le⟩⟩

/-- Consecutive indispensable intervals overlap. -/
private theorem sew_inter_of_adjacent {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (hst : s < t) (a b : ι → ℝ) (S : Finset ι)
    (hcover : Icc s t ⊆ ⋃ i ∈ S, sewInterval s t a b i)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : a i < a j)
    (hadj : ∀ k ∈ S, ¬ (a i < a k ∧ a k < a j)) :
    (sewInterval s t a b i ∩ sewInterval s t a b j).Nonempty := by
  have hb : b i < b j :=
    (sew_endpoint_order s t a b S hprivate hi hj
      (by intro h; subst j; exact (lt_irrefl _ hij))).mp hij
  obtain ⟨xi, hxi, _⟩ := hprivate i hi
  obtain ⟨xj, hxj, _⟩ := hprivate j hj
  by_contra hmeet
  have hgap : b i ≤ a j := by
    by_contra h
    exact hmeet (sew_inter_of_cross s t hst a b ⟨xi, hxi⟩ ⟨xj, hxj⟩
      hij hb (lt_of_not_ge h))
  let u : ℝ := (b i + a j) / 2
  have hu₁ : b i ≤ u := by dsimp [u]; linarith
  have hu₂ : u ≤ a j := by dsimp [u]; linarith
  have hu : u ∈ Icc s t := ⟨by linarith [hxi.2.1, hxi.1.2],
    by linarith [hxj.2.2, hxj.1.1]⟩
  obtain ⟨k, hk, huk⟩ := Set.mem_iUnion₂.mp (hcover hu)
  by_cases hki : a k ≤ a i
  · have hbk : b k ≤ b i := by
      by_cases h : k = i
      · subst k; exact le_rfl
      · have hlt : a k < a i := lt_of_le_of_ne hki
          (sew_left_ne s t a b S hprivate hk hi h)
        exact ((sew_endpoint_order s t a b S hprivate hk hi h).mp hlt).le
    exact (not_lt_of_ge (hbk.trans hu₁)) huk.1.2
  · have hajk : a j ≤ a k := by
      by_contra h
      exact hadj k hk ⟨lt_of_not_ge hki, lt_of_not_ge h⟩
    exact (not_lt_of_ge (hu₂.trans hajk)) huk.1.1

private theorem sew_first {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (hst : s < t) (a b : ι → ℝ) (S : Finset ι)
    (hcover : Icc s t ⊆ ⋃ i ∈ S, sewInterval s t a b i)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j) :
    ∃ i ∈ S, s ∈ sewInterval s t a b i ∧
      ∀ j ∈ S, j ≠ i → a i < a j := by
  obtain ⟨i, hi, hsi⟩ := Set.mem_iUnion₂.mp (hcover (left_mem_Icc.mpr hst.le))
  refine ⟨i, hi, hsi, ?_⟩
  intro j hj hji
  by_contra h
  have haji : a j < a i := lt_of_le_of_ne (le_of_not_gt h)
    (sew_left_ne s t a b S hprivate hj hi hji)
  have hbji : b j < b i :=
    (sew_endpoint_order s t a b S hprivate hj hi hji).mp haji
  apply sew_no_subset s t a b S hprivate hj hi hji
  intro x hx
  exact ⟨⟨lt_of_lt_of_le hsi.1.1 hx.2.1, lt_trans hx.1.2 hbji⟩, hx.2⟩

private theorem sew_last {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (hst : s < t) (a b : ι → ℝ) (S : Finset ι)
    (hcover : Icc s t ⊆ ⋃ i ∈ S, sewInterval s t a b i)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j) :
    ∃ i ∈ S, t ∈ sewInterval s t a b i ∧
      ∀ j ∈ S, j ≠ i → a j < a i := by
  obtain ⟨i, hi, hti⟩ := Set.mem_iUnion₂.mp (hcover (right_mem_Icc.mpr hst.le))
  refine ⟨i, hi, hti, ?_⟩
  intro j hj hji
  by_contra h
  have haij : a i < a j := lt_of_le_of_ne (le_of_not_gt h)
    (sew_left_ne s t a b S hprivate hi hj hji.symm)
  have hbij : b i < b j :=
    (sew_endpoint_order s t a b S hprivate hi hj hji.symm).mp haij
  apply sew_no_subset s t a b S hprivate hj hi hji
  intro x hx
  exact ⟨⟨lt_trans haij hx.1.1, lt_of_le_of_lt hx.2.2 hti.1.2⟩, hx.2⟩

private theorem sew_interior {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j)
    {i : ι} (hi : i ∈ S)
    (hs : s ∉ sewInterval s t a b i)
    (ht : t ∉ sewInterval s t a b i) :
    s ≤ a i ∧ a i < b i ∧ b i ≤ t ∧ sewInterval s t a b i = Ioo (a i) (b i) := by
  obtain ⟨x, hx, _⟩ := hprivate i hi
  have hasi : s ≤ a i := by
    by_contra h
    apply hs
    exact ⟨⟨lt_of_not_ge h, lt_of_le_of_lt hx.2.1 hx.1.2⟩,
      ⟨le_rfl, hx.2.1.trans hx.2.2⟩⟩
  have hbti : b i ≤ t := by
    by_contra h
    apply ht
    exact ⟨⟨lt_of_lt_of_le hx.1.1 hx.2.2, lt_of_not_ge h⟩,
      ⟨hx.2.1.trans hx.2.2, le_rfl⟩⟩
  refine ⟨hasi, lt_trans hx.1.1 hx.1.2, hbti, ?_⟩
  ext y
  constructor
  · exact fun hy => hy.1
  · intro hy
    exact ⟨hy, ⟨hasi.trans hy.1.le, hy.2.le.trans hbti⟩⟩

private theorem sew_unique_start {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hsi : s ∈ sewInterval s t a b i)
    (hsj : s ∈ sewInterval s t a b j) : i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne (sew_left_ne s t a b S hprivate hi hj hij) with ha | ha
  · have hb := (sew_endpoint_order s t a b S hprivate hi hj hij).mp ha
    apply sew_no_subset s t a b S hprivate hi hj hij
    intro x hx
    exact ⟨⟨lt_of_lt_of_le hsj.1.1 hx.2.1, lt_trans hx.1.2 hb⟩, hx.2⟩
  · have hb := (sew_endpoint_order s t a b S hprivate hj hi (Ne.symm hij)).mp ha
    apply sew_no_subset s t a b S hprivate hj hi (Ne.symm hij)
    intro x hx
    exact ⟨⟨lt_of_lt_of_le hsi.1.1 hx.2.1, lt_trans hx.1.2 hb⟩, hx.2⟩

private theorem sew_unique_end {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hprivate : ∀ i ∈ S, ∃ x ∈ sewInterval s t a b i,
      ∀ j ∈ S, j ≠ i → x ∉ sewInterval s t a b j)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hti : t ∈ sewInterval s t a b i)
    (htj : t ∈ sewInterval s t a b j) : i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne (sew_left_ne s t a b S hprivate hi hj hij) with ha | ha
  · apply sew_no_subset s t a b S hprivate hj hi (Ne.symm hij)
    intro x hx
    exact ⟨⟨lt_trans ha hx.1.1, lt_of_le_of_lt hx.2.2 hti.1.2⟩, hx.2⟩
  · apply sew_no_subset s t a b S hprivate hi hj hij
    intro x hx
    exact ⟨⟨lt_trans ha hx.1.1, lt_of_le_of_lt hx.2.2 htj.1.2⟩, hx.2⟩

private theorem sew_inf {ι : Type*} (s t : ℝ) (a b : ι → ℝ) (i : ι)
    (hne : (sewInterval s t a b i).Nonempty) :
    sInf (sewInterval s t a b i) = max (a i) s := by
  have hlower : ∀ x ∈ sewInterval s t a b i, max (a i) s ≤ x := by
    intro x hx
    exact max_le hx.1.1.le hx.2.1
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt hne hlower
  intro w hw
  obtain ⟨x, hx⟩ := hne
  by_cases hlt : max (a i) s < x
  · have hmin : max (a i) s < min x w := lt_min hlt hw
    obtain ⟨y, hylo, hyhi⟩ := exists_between hmin
    refine ⟨y, ?_, lt_of_lt_of_le hyhi (min_le_right _ _)⟩
    have hyx : y < x := lt_of_lt_of_le hyhi (min_le_left _ _)
    exact ⟨⟨lt_of_le_of_lt (le_max_left _ _) hylo, lt_trans hyx hx.1.2⟩,
      ⟨(lt_of_le_of_lt (le_max_right _ _) hylo).le, hyx.le.trans hx.2.2⟩⟩
  · have heq : x = max (a i) s := le_antisymm (le_of_not_gt hlt) (hlower x hx)
    exact ⟨x, hx, heq ▸ hw⟩

private theorem sew_sup {ι : Type*} (s t : ℝ) (a b : ι → ℝ) (i : ι)
    (hne : (sewInterval s t a b i).Nonempty) :
    sSup (sewInterval s t a b i) = min (b i) t := by
  have hupper : ∀ x ∈ sewInterval s t a b i, x ≤ min (b i) t := by
    intro x hx
    exact le_min hx.1.2.le hx.2.2
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt hne hupper
  intro w hw
  obtain ⟨x, hx⟩ := hne
  by_cases hlt : x < min (b i) t
  · have hmax : max x w < min (b i) t := max_lt hlt hw
    obtain ⟨y, hylo, hyhi⟩ := exists_between hmax
    refine ⟨y, ?_, lt_of_le_of_lt (le_max_right _ _) hylo⟩
    have hxy : x < y := lt_of_le_of_lt (le_max_left _ _) hylo
    exact ⟨⟨lt_trans hx.1.1 hxy, lt_of_lt_of_le hyhi (min_le_left _ _)⟩,
      ⟨hx.2.1.trans hxy.le, (lt_of_lt_of_le hyhi (min_le_right _ _)).le⟩⟩
  · have heq : x = min (b i) t := le_antisymm (hupper x hx) (le_of_not_gt hlt)
    exact ⟨x, hx, heq ▸ hw⟩

/-- Corrected interval-cover lemma (ruling N17). The selected `S` is ordered by the
left endpoints `a`; the last clause says precisely that consecutive selected intervals
overlap and selected intervals with another one between them are disjoint. This finset
form avoids choosing an arbitrary enumeration of the input family. -/
theorem interval_cover {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (hst : s < t) (a b : ι → ℝ) (F : Finset ι)
    (hcov : Icc s t ⊆ ⋃ i ∈ F, sewInterval s t a b i) :
    ∃ S : Finset ι, S ⊆ F ∧
      Icc s t ⊆ ⋃ i ∈ S, sewInterval s t a b i ∧
      (∀ T : Finset ι, T ⊂ S → ¬ Icc s t ⊆ ⋃ i ∈ T, sewInterval s t a b i) ∧
      (∀ i ∈ S, ∀ j ∈ S, a i ≤ a j →
        sInf (sewInterval s t a b i) ≤ sInf (sewInterval s t a b j) ∧
        sSup (sewInterval s t a b i) ≤ sSup (sewInterval s t a b j)) ∧
      ∃ first ∈ S, ∃ last ∈ S,
        s ∈ sewInterval s t a b first ∧ t ∈ sewInterval s t a b last ∧
        (∀ i ∈ S, i ≠ first → a first < a i) ∧
        (∀ i ∈ S, i ≠ last → a i < a last) ∧
        (∀ i ∈ S, i ≠ first → i ≠ last →
          s ≤ a i ∧ a i < b i ∧ b i ≤ t ∧ sewInterval s t a b i = Ioo (a i) (b i)) ∧
        (∀ i ∈ S, ∀ j ∈ S, a i < a j →
          ((∃ k ∈ S, a i < a k ∧ a k < a j) ↔
            ¬ (sewInterval s t a b i ∩ sewInterval s t a b j).Nonempty)) := by
  classical
  obtain ⟨S, hSF, hcover, herase, hprivate⟩ :=
    sew_exists_minimal_cover s t a b F hcov
  obtain ⟨first, hfirst, hsfirst, hfirstmin⟩ :=
    sew_first s t hst a b S hcover hprivate
  obtain ⟨last, hlast, htlast, hlastmax⟩ :=
    sew_last s t hst a b S hcover hprivate
  refine ⟨S, hSF, hcover, ?_, ?_, first, hfirst, last, hlast,
    hsfirst, htlast, hfirstmin, hlastmax, ?_, ?_⟩
  · intro T hTS hTcov
    obtain ⟨i, hi, hTi⟩ := Finset.ssubset_iff_exists_subset_erase.mp hTS
    exact herase i hi (hTcov.trans (by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨j, hTi hj, hxj⟩))
  · intro i hi j hj ha
    have hbi : b i ≤ b j := by
      by_cases hij : i = j
      · subst j; exact le_rfl
      · have hstrict : a i < a j := lt_of_le_of_ne ha
          (sew_left_ne s t a b S hprivate hi hj hij)
        exact ((sew_endpoint_order s t a b S hprivate hi hj hij).mp hstrict).le
    obtain ⟨xi, hxi, _⟩ := hprivate i hi
    obtain ⟨xj, hxj, _⟩ := hprivate j hj
    rw [sew_inf s t a b i ⟨xi, hxi⟩, sew_inf s t a b j ⟨xj, hxj⟩,
      sew_sup s t a b i ⟨xi, hxi⟩, sew_sup s t a b j ⟨xj, hxj⟩]
    exact ⟨max_le_max ha le_rfl, min_le_min hbi le_rfl⟩
  · intro i hi hif hil
    apply sew_interior s t a b S hprivate hi
    · intro hsi
      exact hif (sew_unique_start s t a b S hprivate hi hfirst hsi hsfirst)
    · intro hti
      exact hil (sew_unique_end s t a b S hprivate hi hlast hti htlast)
  · intro i hi j hj hij
    constructor
    · rintro ⟨k, hk, hik, hkj⟩
      exact sew_no_inter_of_between s t a b S hprivate hi hk hj hik hkj
    · intro hno
      by_contra hnone
      have hadj : ∀ k ∈ S, ¬ (a i < a k ∧ a k < a j) := by
        intro k hk hbetween
        exact hnone ⟨k, hk, hbetween⟩
      exact hno (sew_inter_of_adjacent s t hst a b S hcover hprivate hi hj hij hadj)

/-- The left endpoints of an inclusion-minimal relative-interval cover are
distinct. This gives consumers a canonical increasing enumeration. -/
theorem sew_minimal_left_injective {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hcover : Icc s t ⊆ ⋃ i ∈ S, sewInterval s t a b i)
    (hminimal : ∀ T : Finset ι, T ⊂ S →
      ¬ Icc s t ⊆ ⋃ i ∈ T, sewInterval s t a b i)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (ha : a i = a j) : i = j := by
  classical
  have hprivate : ∀ k ∈ S, ∃ x ∈ sewInterval s t a b k,
      ∀ l ∈ S, l ≠ k → x ∉ sewInterval s t a b l := by
    intro k hk
    have herase : S.erase k ⊂ S := Finset.erase_ssubset hk
    obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp (hminimal _ herase)
    obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hlk : l = k := by
      by_contra hne
      exact hxnot (Set.mem_iUnion₂.mpr
        ⟨l, Finset.mem_erase.mpr ⟨hne, hl⟩, hxl⟩)
    subst l
    refine ⟨x, hxl, ?_⟩
    intro l hl hne hxl'
    exact hxnot (Set.mem_iUnion₂.mpr
      ⟨l, Finset.mem_erase.mpr ⟨hne, hl⟩, hxl'⟩)
  by_contra hne
  exact sew_left_ne s t a b S hprivate hi hj hne ha

/-- Enumerate a minimal cover in strictly increasing order of its ambient left
endpoints. -/
theorem sew_ordered_enumeration {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (a b : ι → ℝ) (S : Finset ι)
    (hcover : Icc s t ⊆ ⋃ i ∈ S, sewInterval s t a b i)
    (hminimal : ∀ T : Finset ι, T ⊂ S →
      ¬ Icc s t ⊆ ⋃ i ∈ T, sewInterval s t a b i) :
    ∃ j : Fin S.card → ι,
      Finset.univ.image j = S ∧ StrictMono (fun k => a (j k)) := by
  classical
  have ha_inj : Function.Injective (fun i : S => a i.1) := by
    intro i j hij
    exact Subtype.ext (sew_minimal_left_injective s t a b S
      hcover hminimal i.2 j.2 hij)
  let _ : LinearOrder S := LinearOrder.lift' (fun i : S => a i.1) ha_inj
  let e : Fin S.card ≃o S :=
    Fintype.orderIsoFinOfCardEq S (by simp)
  let j : Fin S.card → ι := fun k => (e k).1
  refine ⟨j, ?_, ?_⟩
  · ext i
    constructor
    · intro hi
      obtain ⟨k, -, hki⟩ := Finset.mem_image.mp hi
      rw [← hki]
      exact (e k).2
    · intro hi
      refine Finset.mem_image.mpr ⟨e.symm ⟨i, hi⟩, Finset.mem_univ _, ?_⟩
      simp [j]
  · intro k l hkl
    have h := e.strictMono hkl
    exact h

/-- A nonempty connected set that is open relative to `[s,t]` has the ambient-open
endpoint presentation used by `interval_cover`. -/
theorem sew_relative_interval_representation (s t : ℝ) (J V : Set ℝ)
    (hne : J.Nonempty) (hconn : IsPreconnected J)
    (hV : IsOpen V) (hJV : J = V ∩ Icc s t) :
    ∃ a b : ℝ, J = Ioo a b ∩ Icc s t := by
  classical
  have hsub : J ⊆ Icc s t := by rw [hJV]; exact inter_subset_right
  have hbelow : BddBelow J := ⟨s, fun x hx => (hsub hx).1⟩
  have habove : BddAbove J := ⟨t, fun x hx => (hsub hx).2⟩
  let A := sInf J
  let B := sSup J
  let a := if s ∈ J then s - 1 else A
  let b := if t ∈ J then t + 1 else B
  have hleft : ∀ x ∈ J, x ≠ s → A < x := by
    intro x hx hxs
    have hsx : s < x := lt_of_le_of_ne (hsub hx).1 (Ne.symm hxs)
    have hxV : x ∈ V := by rw [hJV] at hx; exact hx.1
    obtain ⟨l, u, ⟨hlx, hxu⟩, hlu⟩ :=
      (mem_nhds_iff_exists_Ioo_subset.mp (hV.mem_nhds hxV))
    obtain ⟨y, hyl, hyx⟩ := exists_between (max_lt hlx hsx)
    have hyJ : y ∈ J := by
      rw [hJV]
      exact ⟨hlu ⟨lt_of_le_of_lt (le_max_left _ _) hyl,
          lt_trans hyx hxu⟩,
        ⟨(lt_of_le_of_lt (le_max_right _ _) hyl).le,
          hyx.le.trans (hsub hx).2⟩⟩
    exact lt_of_le_of_lt (csInf_le hbelow hyJ) hyx
  have hright : ∀ x ∈ J, x ≠ t → x < B := by
    intro x hx hxt
    have hxt' : x < t := lt_of_le_of_ne (hsub hx).2 hxt
    have hxV : x ∈ V := by rw [hJV] at hx; exact hx.1
    obtain ⟨l, u, ⟨hlx, hxu⟩, hlu⟩ :=
      (mem_nhds_iff_exists_Ioo_subset.mp (hV.mem_nhds hxV))
    obtain ⟨y, hxy, hyu⟩ := exists_between (lt_min hxu hxt')
    have hyJ : y ∈ J := by
      rw [hJV]
      exact ⟨hlu ⟨lt_trans hlx hxy,
          lt_of_lt_of_le hyu (min_le_left _ _)⟩,
        ⟨(hsub hx).1.trans hxy.le,
          (lt_of_lt_of_le hyu (min_le_right _ _)).le⟩⟩
    exact lt_of_lt_of_le hxy (le_csSup habove hyJ)
  refine ⟨a, b, ?_⟩
  ext x
  constructor
  · intro hx
    have hxI := hsub hx
    refine ⟨⟨?_, ?_⟩, hxI⟩
    · by_cases hs : s ∈ J
      · simp only [a, hs, ↓reduceIte]; linarith [hxI.1]
      · simp only [a, hs, ↓reduceIte]
        exact hleft x hx (by intro h; subst x; exact hs hx)
    · by_cases ht : t ∈ J
      · simp only [b, ht, ↓reduceIte]; linarith [hxI.2]
      · simp only [b, ht, ↓reduceIte]
        exact hright x hx (by intro h; subst x; exact ht hx)
  · rintro ⟨⟨hax, hxb⟩, hxI⟩
    by_cases hxs : x = s
    · subst x
      by_cases hs : s ∈ J
      · exact hs
      · have : a = A := by simp [a, hs]
        have hAs : s ≤ A := le_csInf hne (fun y hy => (hsub hy).1)
        rw [this] at hax
        linarith
    by_cases hxt : x = t
    · subst x
      by_cases ht : t ∈ J
      · exact ht
      · have : b = B := by simp [b, ht]
        have hBt : B ≤ t := csSup_le hne (fun y hy => (hsub hy).2)
        rw [this] at hxb
        linarith
    have hAx : A < x := by
      by_cases hs : s ∈ J
      · have hAs : A ≤ s := csInf_le hbelow hs
        have hsx : s < x := lt_of_le_of_ne hxI.1 (Ne.symm hxs)
        exact lt_of_le_of_lt hAs hsx
      · simpa only [a, hs, ↓reduceIte] using hax
    have hxB : x < B := by
      by_cases ht : t ∈ J
      · have htB : t ≤ B := le_csSup habove ht
        have hxt' : x < t := lt_of_le_of_ne hxI.2 hxt
        exact lt_of_lt_of_le hxt' htB
      · simpa only [b, ht, ↓reduceIte] using hxb
    have hconnJ : IsConnected J := ⟨hne, hconn⟩
    exact hconnJ.Ioo_csInf_csSup_subset hbelow habove ⟨hAx, hxB⟩

end HigherDimLQGContinuity
