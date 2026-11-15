/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MfFill
import InteractingSLE.Spec.Sec5.Aux61RestartGeoRecord

/-!
# Equality events of random hulls and fills of unions

Worker REVIEW-FABLE-T14 (the retained law at the base of SB2(2)'s induction; orchestrator split of PROVE-SB2-LCMEAN's
handoff R13.8).

* **`measurableSet_eq_of_hitting`**: for two random relatively closed subsets of `ℍ` observed through their hitting
  events, the event that they are equal is measurable (rational discs inside `ℍ` separate distinct relatively closed
  sets);
* `fillH_closure_union_of_subset`: adding to a set `S` a set lying in the hull `F = fill(closure S)` does not change the
  fill;
* `fillVer_union_of_le`: if the filled version of `S ∪ T₂` is a bounded set `F = fill(closure S)`, then so is the filled
  version of `S ∪ T₁` for every `T₁ ⊆ T₂`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Qt

open LocalSets Mf

/-! ### Equality events -/

/-- A rational disc inside `ℍ` around a point of an open set inside `ℍ`. -/
theorem exists_rat_ball_subset {V : Set ℂ} (hV : IsOpen V) {z : ℂ} (hz : z ∈ V) :
    ∃ q : ℚ × ℚ × ℚ, z ∈ ball (⟨q.1, q.2.1⟩ : ℂ) q.2.2 ∧ ball (⟨q.1, q.2.1⟩ : ℂ) q.2.2 ⊆ V := by
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV z hz
  obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 3 by linarith)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - r / 2 < z.re + r / 2 by linarith)
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show z.im - r / 2 < z.im + r / 2 by linarith)
  have hd : dist z (⟨a, c⟩ : ℂ) < r := by
    rw [Complex.dist_eq]
    calc ‖z - (⟨a, c⟩ : ℂ)‖ ≤ |(z - (⟨a, c⟩ : ℂ)).re| + |(z - (⟨a, c⟩ : ℂ)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < r / 2 + r / 2 := by
          refine add_lt_add ?_ ?_
          · simp only [Complex.sub_re]
            rw [abs_lt]
            constructor <;> linarith
          · simp only [Complex.sub_im]
            rw [abs_lt]
            constructor <;> linarith
      _ = r := by ring
  refine ⟨(a, c, r), mem_ball.2 hd, fun w hw => hεV (mem_ball.2 ?_)⟩
  calc dist w z ≤ dist w (⟨a, c⟩ : ℂ) + dist (⟨a, c⟩ : ℂ) z := dist_triangle _ _ _
    _ < r + r := add_lt_add (mem_ball.1 hw) (by rw [dist_comm]; exact hd)
    _ < ε := by linarith

/-- **The equality event of two random relatively closed subsets of `ℍ` is measurable** when both are observed through
their hitting events. -/
theorem measurableSet_eq_of_hitting {Ω : Type*} {m : MeasurableSpace Ω} {A B : Ω → Set ℂ}
    (hA : Measurable[m, hittingSigma] A) (hB : Measurable[m, hittingSigma] B)
    (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) :
    MeasurableSet[m] {ω | A ω = B ω} := by
  classical
  set U : ℚ × ℚ × ℚ → Set ℂ := fun q => ball (⟨q.1, q.2.1⟩ : ℂ) q.2.2 with hU
  have heq : {ω | A ω = B ω} =
      ⋂ q : ℚ × ℚ × ℚ, ⋂ (_ : U q ⊆ H), {ω | Disjoint (A ω) (U q) ↔ Disjoint (B ω) (U q)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro e q _
      rw [e]
    · intro hall
      have key : ∀ {X Y : Set ℂ}, X ⊆ H → IsOpen (H \ Y) →
          (∀ q : ℚ × ℚ × ℚ, U q ⊆ H → (Disjoint X (U q) ↔ Disjoint Y (U q))) → X ⊆ Y := by
        intro X Y hXH hYo hXY z hz
        by_contra hzY
        obtain ⟨q, hzq, hqV⟩ := exists_rat_ball_subset hYo ⟨hXH hz, hzY⟩
        have hqH : U q ⊆ H := hqV.trans sdiff_subset
        have hdY : Disjoint Y (U q) := Set.disjoint_left.2 fun w hwY hwU => (hqV hwU).2 hwY
        exact Set.disjoint_left.1 ((hXY q hqH).2 hdY) hz hzq
      exact Subset.antisymm (key (hAc ω).1 (hBc ω).2 fun q hq => hall q hq)
        (key (hBc ω).1 (hAc ω).2 fun q hq => (hall q hq).symm)
  rw [heq]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_
  have hUo : IsOpen (U q) := isOpen_ball
  have h1 : MeasurableSet[m] {ω | Disjoint (A ω) (U q)} := hA (measurableSet_avoid hUo hq)
  have h2 : MeasurableSet[m] {ω | Disjoint (B ω) (U q)} := hB (measurableSet_avoid hUo hq)
  have e : {ω | Disjoint (A ω) (U q) ↔ Disjoint (B ω) (U q)} =
      ({ω | Disjoint (A ω) (U q)} ∩ {ω | Disjoint (B ω) (U q)}) ∪
        ({ω | Disjoint (A ω) (U q)}ᶜ ∩ {ω | Disjoint (B ω) (U q)}ᶜ) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
    tauto
  rw [e]
  exact (h1.inter h2).union (h1.compl.inter h2.compl)

/-! ### Fills of unions -/

/-- **Adding a subset of the hull does not change the fill.** If `F = fill(closure S)` is a hull and `T ⊆ F`, then
`fill(closure (S ∪ T)) = F`. -/
theorem fillH_closure_union_of_subset {S T F : Set ℂ} (hF : IsHPHull F) (hSF : fillH (closure S) = F)
    (hS : S ⊆ H) (hT : T ⊆ F) : fillH (closure (S ∪ T)) = F := by
  refine Subset.antisymm ?_ ?_
  · have hSF' : S ⊆ F := fun z hz => hSF ▸ mem_fillH_of_mem_closure (hS hz) (subset_closure (subset_closure hz))
    have h1 : closure (S ∪ T) ⊆ closure F := closure_mono (union_subset hSF' hT)
    exact (fillH_mono h1).trans (Sec5.Aux61Restart.fillH_closure_of_isHPHull hF).le
  · rw [← hSF]
    exact fillH_mono (closure_mono subset_union_left)

open Classical in
/-- **The filled version of a smaller union**: if the filled version of `S ∪ T₂` is a bounded set `F` equal to
`fill(closure S)` with `S` bounded, then the filled version of `S ∪ T₁` is `F` for every `T₁ ⊆ T₂`. -/
theorem fillVer_union_of_le {Ω : Type*} {S T₁ T₂ : Ω → Set ℂ} {ω : Ω} {F : Set ℂ}
    (hF : Bornology.IsBounded F) (hSF : fillH (closure (S ω)) = F)
    (h₂ : fillVer (fun ω => S ω ∪ T₂ ω) ω = F) (hT : T₁ ω ⊆ T₂ ω) :
    fillVer (fun ω => S ω ∪ T₁ ω) ω = F := by
  have hb₂ : Bornology.IsBounded (S ω ∪ T₂ ω) := by
    by_contra hnb
    rw [fillVer_of_not_bounded (B := fun ω => S ω ∪ T₂ ω) hnb] at h₂
    exact hnb (h₂ ▸ hF)
  have hb₁ : Bornology.IsBounded (S ω ∪ T₁ ω) := hb₂.subset (union_subset_union_right _ hT)
  rw [fillVer_of_bounded (B := fun ω => S ω ∪ T₂ ω) hb₂] at h₂
  rw [fillVer_of_bounded (B := fun ω => S ω ∪ T₁ ω) hb₁]
  refine Subset.antisymm ?_ ?_
  · rw [← h₂]
    exact fillH_mono (closure_mono (union_subset_union_right _ hT))
  · rw [← hSF]
    exact fillH_mono (closure_mono subset_union_left)

end InteractingSLE.Theorem14.SB.Qt
