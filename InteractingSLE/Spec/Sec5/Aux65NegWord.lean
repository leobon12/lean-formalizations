/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CovWire
import InteractingSLE.Spec.Sec5.Aux22ChartEFlow
import InteractingSLE.Spec.Sec5.Aux65NegDelete
import InteractingSLE.Spec.Sec7.StripDet

/-!
# The negative reference has exactly two active force marks

The arbitrary jump-candidate set and the passive seed marks do not add active
weights. Deleting them leaves the two left marks `x₁, x₂` with weights `r, -r`,
where `r = -v / λ - 1 ≤ κ/2 - 4`. This is precisely the reflected word in
Auxiliary lemma 132's bottom-right entry; no post-swallow continuation is used.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux65Neg

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

variable {κ x₂ x₁ v : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- The one-sided limits at the two marked endpoints of the reference interval. -/
theorem endpoint_limits (h₂₁ : x₂ < x₁) (h₁ : x₁ < 0)
    (hm : ∀ z, x₁ < z → z < 0 → b z = -sleLambda κ)
    (hi : ∀ z, x₂ < z → z < x₁ → b z = v)
    (hl : ∀ z, z < x₂ → b z = -sleLambda κ) :
    leftLim b x₁ = v ∧ rightLim b x₁ = -sleLambda κ ∧
      leftLim b x₂ = -sleLambda κ ∧ rightLim b x₂ = v := by
  refine ⟨Sec4.leftLim_eq_of_forall h₂₁ (fun z hz => hi z hz.1 hz.2),
    Sec4.rightLim_eq_of_forall h₁ (fun z hz => hm z hz.1 hz.2),
    Sec4.leftLim_eq_of_forall (show x₂ - 1 < x₂ by linarith) (fun z hz => hl z hz.2),
    Sec4.rightLim_eq_of_forall h₂₁ (fun z hz => hi z hz.1 hz.2)⟩

/-- Away from the two endpoints the negative reference is locally constant. -/
theorem left_limits_eq {y : ℝ} (_h₂₁ : x₂ < x₁) (_h₁ : x₁ < 0)
    (hm : ∀ z, x₁ < z → z < 0 → b z = -sleLambda κ)
    (hi : ∀ z, x₂ < z → z < x₁ → b z = v)
    (hl : ∀ z, z < x₂ → b z = -sleLambda κ)
    (hy : y < 0) (hy₁ : y ≠ x₁) (hy₂ : y ≠ x₂) : leftLim b y = rightLim b y := by
  rcases lt_or_gt_of_ne hy₂ with hy₂ | hy₂
  · exact (Sec4.leftLim_eq_of_forall (show y - 1 < y by linarith)
      (fun z hz => hl z (hz.2.trans hy₂))).trans
      (Sec4.rightLim_eq_of_forall hy₂ (fun z hz => hl z hz.2)).symm
  · rcases lt_or_gt_of_ne hy₁ with hy₁ | hy₁
    · exact (Sec4.leftLim_eq_of_forall hy₂ (fun z hz => hi z hz.1 (hz.2.trans hy₁))).trans
        (Sec4.rightLim_eq_of_forall hy₁ (fun z hz => hi z (hy₂.trans hz.1) hz.2)).symm
    · exact (Sec4.leftLim_eq_of_forall hy₁ (fun z hz => hm z hz.1 (hz.2.trans hy))).trans
        (Sec4.rightLim_eq_of_forall hy (fun z hz => hm z (hy₁.trans hz.1) hz.2)).symm

/-- A low cumulative weight differs from the passive reference value. -/
theorem height_ne_basic (hκ : 0 < κ) (hκ4 : κ < 4)
    (hr : Sec4.cumWeightLeft κ v ≤ κ / 2 - 4) : v ≠ -sleLambda κ := by
  intro he
  have hLambda := (Sec4.sleLambda_pos hκ).ne'
  rw [he, Sec4.cumWeightLeft, neg_neg, div_self hLambda] at hr
  linarith

/-- Deleting passive marks in `RefNeg` leaves exactly the two-mark word.
The positions and weights are stated pointwise to avoid casts between finite types. -/
theorem subword_of_refNeg (hκ : 0 < κ) {I : Set ℝ} (h : Aux61Cov.RefNeg κ b J I) :
    ∃ (x₂ x₁ r : ℝ) (eL : Fin 2 ↪o Fin (flowLineNL b J 0))
      (eR : Fin 0 ↪o Fin (flowLineNR b J 0)),
      x₂ < x₁ ∧ x₁ < 0 ∧ r ≤ κ / 2 - 4 ∧ I ⊆ Ioo x₂ x₁ ∧
      (∀ i, flowLineXL b J 0 (eL i) = ![x₁, x₂] i) ∧
      (∀ i, flowLineRhoL κ b J 0 0 (eL i) = ![r, -r] i) ∧
      (∀ i, i ∉ Set.range eL → flowLineRhoL κ b J 0 0 i = 0) ∧
      (∀ j, j ∉ Set.range eR → flowLineRhoR κ b J 0 0 j = 0) := by
  classical
  obtain ⟨hκ4, hb, x₂, x₁, v, h₂₁, h₁, hp, hm, hi, hl, hr, hI⟩ := h
  have hv := height_ne_basic hκ hκ4 hr
  obtain ⟨hL₁, hR₁, hL₂, hR₂⟩ := endpoint_limits h₂₁ h₁ hm hi hl
  have hmem₁ : x₁ ∈ jumpSet b J := by
    have hn : leftLim b x₁ ≠ rightLim b x₁ := by rw [hL₁, hR₁]; exact hv
    exact Finset.mem_filter.2 ⟨by_contra fun hh =>
      hn (Theorem14.GW1.leftLim_eq_rightLim_of_notMem hb hh), hn⟩
  have hmem₂ : x₂ ∈ jumpSet b J := by
    have hn : leftLim b x₂ ≠ rightLim b x₂ := by rw [hL₂, hR₂]; exact hv.symm
    exact Finset.mem_filter.2 ⟨by_contra fun hh =>
      hn (Theorem14.GW1.leftLim_eq_rightLim_of_notMem hb hh), hn⟩
  obtain ⟨i₁, hi₁, -⟩ := Aux22ChartE.exists_flowLineXL_eq hmem₁ h₁ hκ
  obtain ⟨i₂, hi₂, -⟩ := Aux22ChartE.exists_flowLineXL_eq hmem₂ (h₂₁.trans h₁) hκ
  have hord := Theorem15.isOrderedForceWord_flowLine b J 0
  have hidx : i₁ < i₂ := lt_of_not_ge fun hh =>
    (not_le.2 h₂₁) (by simpa only [hi₁, hi₂] using hord.1 hh)
  let eL : Fin 2 ↪o Fin (flowLineNL b J 0) :=
    OrderEmbedding.ofStrictMono ![i₁, i₂] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
  let eR : Fin 0 ↪o Fin (flowLineNR b J 0) :=
    OrderEmbedding.ofStrictMono Fin.elim0 (fun i => i.elim0)
  have hseedL : leftLim b 0 = -sleLambda κ :=
    Sec4.leftLim_eq_of_forall h₁ (fun z hz => hm z hz.1 hz.2)
  have hseedR : rightLim b 0 = sleLambda κ :=
    Sec4.rightLim_eq_of_forall zero_lt_one (fun z hz => hp z hz.1)
  have hwL : ∀ i, flowLineRhoL κ b J 0 0 i =
      if flowLineXL b J 0 i = x₁ then Sec4.cumWeightLeft κ v
      else if flowLineXL b J 0 i = x₂ then -Sec4.cumWeightLeft κ v else 0 := by
    unfold flowLineRhoL flowLineXL flowLineNL
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, zero_mul, add_zero, hseedL,
        h₁.ne', (h₂₁.trans h₁).ne', ↓reduceIte]
      field_simp [(Sec4.sleLambda_pos hκ).ne']
      ring
    · simp only [Fin.cons_succ, sub_zero, zero_mul, add_zero]
      let y := ((jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev j)
      change (rightLim b y - leftLim b y) / sleLambda κ =
        if y = x₁ then Sec4.cumWeightLeft κ v
        else if y = x₂ then -Sec4.cumWeightLeft κ v else 0
      by_cases hy₁ : y = x₁
      · rw [hy₁, hL₁, hR₁]
        simp only [↓reduceIte, Sec4.cumWeightLeft]
        field_simp [(Sec4.sleLambda_pos hκ).ne']
        ring
      · by_cases hy₂ : y = x₂
        · rw [hy₂, hL₂, hR₂]
          simp only [h₂₁.ne, ↓reduceIte, Sec4.cumWeightLeft]
          field_simp [(Sec4.sleLambda_pos hκ).ne']
          ring
        · have hym := ((jumpSet b J).filter (· < 0)).orderEmbOfFin_mem rfl (Fin.rev j)
          have hy0 : y < 0 := (Finset.mem_filter.1 hym).2
          have he := left_limits_eq h₂₁ h₁ hm hi hl hy0 hy₁ hy₂
          change (rightLim b y - leftLim b y) / sleLambda κ =
            if y = x₁ then _ else if y = x₂ then _ else 0
          rw [he, sub_self, zero_div]
          simp only [hy₁, hy₂, ↓reduceIte]
  have hwR : ∀ j, flowLineRhoR κ b J 0 0 j = 0 := by
    unfold flowLineRhoR flowLineNR
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, zero_mul, add_zero, hseedR]
      exact sub_eq_zero.2 (div_self (Sec4.sleLambda_pos hκ).ne')
    · simp only [Fin.cons_succ]
      let y := ((jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl j
      have hy : 0 < y := (Finset.mem_filter.1
        (((jumpSet b J).filter (0 < ·)).orderEmbOfFin_mem rfl j)).2
      have hL : leftLim b y = sleLambda κ :=
        Sec4.leftLim_eq_of_forall hy (fun z hz => hp z hz.1)
      have hR : rightLim b y = sleLambda κ :=
        Sec4.rightLim_eq_of_forall (show y < y + 1 by linarith)
          (fun z hz => hp z (hy.trans hz.1))
      change (rightLim b y - leftLim b y) / sleLambda κ = 0
      rw [hL, hR, sub_self, zero_div]
  refine ⟨x₂, x₁, Sec4.cumWeightLeft κ v, eL, eR, h₂₁, h₁, hr, hI, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hi₁
    · exact hi₂
  · intro i
    rw [hwL]
    fin_cases i
    · change (if flowLineXL b J 0 i₁ = x₁ then Sec4.cumWeightLeft κ v
        else if flowLineXL b J 0 i₁ = x₂ then -Sec4.cumWeightLeft κ v else 0) =
          Sec4.cumWeightLeft κ v
      simp only [hi₁, ↓reduceIte]
    · change (if flowLineXL b J 0 i₂ = x₁ then Sec4.cumWeightLeft κ v
        else if flowLineXL b J 0 i₂ = x₂ then -Sec4.cumWeightLeft κ v else 0) =
          -Sec4.cumWeightLeft κ v
      simp only [hi₂, h₂₁.ne, ↓reduceIte]
  · intro i hi
    rw [hwL]
    have hposinj := (Sec7.StripDet.strictAnti_flowLineXL b J).injective
    have hne₁ : flowLineXL b J 0 i ≠ x₁ := by
      intro he
      exact hi ⟨0, show i₁ = i from (hposinj (he.trans hi₁.symm)).symm⟩
    have hne₂ : flowLineXL b J 0 i ≠ x₂ := by
      intro he
      exact hi ⟨1, show i₂ = i from (hposinj (he.trans hi₂.symm)).symm⟩
    simp only [hne₁, hne₂, ↓reduceIte]
  · exact fun j _ => hwR j

end InteractingSLE.Sec5.Aux65Neg
