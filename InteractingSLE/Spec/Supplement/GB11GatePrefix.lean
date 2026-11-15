/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11FaceExtension
import Mathlib.Topology.Maps.Proper.Basic

/-!
# GB11: global selection of unvisited incoming wall prefixes

The hit condition is written without inversion, as `α r * γ u = -1`.
Compactness of the explored time interval makes its projection closed, even at
the original target `α 0 = 0`. Reverse first-visit order then makes the hit set
either a closed final interval or empty. The latter is the attachment at infinity
in the original wall parameter, not a missing finite minimizer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- Wall parameters whose physical inversions have been visited by time `t`.
The multiplication equation excludes both zero values automatically. -/
def wallHitParameters (γ α : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℝ≥0 :=
  {r | ∃ u ∈ Icc 0 t, α r * γ u = -1}

/-- The global wall hit set is closed; inversion at the target is unnecessary. -/
theorem isClosed_wallHitParameters {γ α : ℝ≥0 → ℂ}
    (hγ : Continuous γ) (hα : Continuous α) (t : ℝ≥0) :
    IsClosed (wallHitParameters γ α t) := by
  let T := Icc (0 : ℝ≥0) t
  have : CompactSpace T := isCompact_iff_compactSpace.1 isCompact_Icc
  have hc : Continuous (fun p : T × ℝ≥0 => α p.2 * γ p.1) :=
    (hα.comp continuous_snd).mul (hγ.comp (continuous_subtype_val.comp continuous_fst))
  have hclosed := isClosedMap_snd_of_compactSpace
    {p : T × ℝ≥0 | α p.2 * γ p.1 = -1} (isClosed_eq hc continuous_const)
  convert hclosed using 1
  ext r
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨(⟨u, hu⟩, r), he, rfl⟩
  · rintro ⟨⟨u, v⟩, he, rfl⟩
    exact ⟨u, u.2, he⟩

/-- The closed multiplication condition is exactly the first-visit sublevel set. -/
theorem mem_wallHitParameters_iff {γ α : ℝ≥0 → ℂ} (hγ : Continuous γ)
    {t r : ℝ≥0} : r ∈ wallHitParameters γ α t ↔ GB11.firstVisit γ (α r) ≤ t := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hne : γ u ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at he
      exact (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)) he.symm
    have hp : α r = -(γ u)⁻¹ := by
      calc
        α r = (α r * γ u) * (γ u)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
        _ = -(γ u)⁻¹ := by rw [he, neg_one_mul]
    rw [hp]
    exact (GB11.firstVisit_le hne).trans (ENNReal.coe_le_coe.2 hu.2)
  · intro ht
    have hfin := lt_of_le_of_lt ht (ENNReal.coe_lt_top (r := t))
    have hne := ne_zero_of_firstVisit_lt_top hfin
    obtain ⟨u, hu, he⟩ := negInv_mem_image_of_firstVisit_le hγ hfin ht
    refine ⟨u, hu, ?_⟩
    rw [he, mul_neg, mul_inv_cancel₀ hne]

/-- Global cut selection, including a cut at infinity. The finite cut itself is
already visited, and every earlier positive wall point is unvisited. -/
theorem exists_wall_visit_cut {γ α : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (hα : Continuous α) (hα0 : α 0 = 0)
    (hrev : ∀ a a' : ℝ≥0, 0 < a → a < a' →
      GB11.firstVisit γ (α a') < GB11.firstVisit γ (α a)) (t : ℝ≥0) :
    ∃ cut : ℝ≥0∞, 0 < cut ∧
      (∀ r : ℝ≥0, r ∈ wallHitParameters γ α t ↔ cut ≤ (r : ℝ≥0∞)) ∧
      (∀ a : ℝ≥0, (t : ℝ≥0∞) < GB11.firstVisit γ (α a) → (a : ℝ≥0∞) < cut) := by
  classical
  have h0 : (0 : ℝ≥0) ∉ wallHitParameters γ α t := by
    rw [mem_wallHitParameters_iff hγ, hα0, firstVisit_zero_eq_top]
    exact not_le.2 ENNReal.coe_lt_top
  by_cases hne : (wallHitParameters γ α t).Nonempty
  · obtain ⟨r₀, hr₀⟩ := hne
    obtain ⟨a, ha, hmin⟩ :=
      (isCompact_Icc.inter_right (isClosed_wallHitParameters hγ hα t)).exists_isLeast
        ⟨r₀, ⟨⟨zero_le, le_rfl⟩, hr₀⟩⟩
    have hleast : ∀ r ∈ wallHitParameters γ α t, a ≤ r := by
      intro r hr
      rcases le_or_gt r r₀ with hle | hgt
      · exact hmin ⟨⟨zero_le, hle⟩, hr⟩
      · exact ha.1.2.trans hgt.le
    have ha0 : 0 < a := pos_iff_ne_zero.2 (fun he => h0 (he ▸ ha.2))
    have hiff : ∀ r : ℝ≥0, r ∈ wallHitParameters γ α t ↔ (a : ℝ≥0∞) ≤ r := by
      intro r
      constructor
      · exact fun hr => ENNReal.coe_le_coe.2 (hleast r hr)
      · intro har
        rw [mem_wallHitParameters_iff hγ]
        exact (firstVisit_anti hα0 hrev (ENNReal.coe_le_coe.1 har)).trans
          ((mem_wallHitParameters_iff hγ).1 ha.2)
    refine ⟨a, ENNReal.coe_pos.2 ha0, hiff, ?_⟩
    intro b hb
    exact lt_of_not_ge fun hab => (not_le.2 hb) ((mem_wallHitParameters_iff hγ).1 ((hiff b).2 hab))
  · refine ⟨⊤, ENNReal.zero_lt_top, ?_, fun _ _ => ENNReal.coe_lt_top⟩
    intro r
    exact iff_of_false (fun hr => hne ⟨r, hr⟩) (not_le.2 ENNReal.coe_lt_top)

/-- Every positive point of the selected unvisited prefix lies in the canonical
forward-extension domain, including original-real contacts. -/
theorem negInv_mem_freeUpper_of_lt_cut {W' : ℝ≥0 → ℝ} {γ α : ℝ≥0 → ℂ}
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ a a' : ℝ≥0, 0 < a → a < a' →
      GB11.firstVisit γ (α a') < GB11.firstVisit γ (α a))
    {t r : ℝ≥0} {cut : ℝ≥0∞}
    (hcut : ∀ v : ℝ≥0, v ∈ wallHitParameters γ α t ↔ cut ≤ (v : ℝ≥0∞))
    (hr0 : 0 < r) (hr : (r : ℝ≥0∞) < cut) :
    -(α r)⁻¹ ∈ freeUpper (fun u : ℝ => W' u.toNNReal) t := by
  have hne : α r ≠ 0 := fun he => hr0.ne' (hα.2.1 (he.trans hα.2.2.1.symm))
  have hfin := firstVisit_lt_top_of_ne_zero hα.2.2.1 hrev hne
  have hnot : r ∉ wallHitParameters γ α t := fun hv => (not_le.2 hr) ((hcut r).1 hv)
  have ht : (t : ℝ≥0∞) < GB11.firstVisit γ (α r) :=
    lt_of_not_ge (fun hle => hnot ((mem_wallHitParameters_iff
      (Sec5.continuous_of_isGeneratingTrace_top hγ)).2 hle))
  exact ⟨negInv_mem_Hbar (hα.2.2.2.1 r),
    negInv_notMem_closure_of_lt_firstVisit hW' hW'0 hγ hfin ht⟩

end InteractingSLE.Theorem14.GB11Chart
