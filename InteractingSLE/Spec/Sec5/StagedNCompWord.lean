/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompMart
import InteractingSLE.Spec.Sec5.StagedNodeClause

/-!
# The flag candidate's weights in tree order are the node experiment's stage weights

Packet PROVE-STAGED-NODECOMP. The word entrance of the flag candidate (`exists_isWordEntrance_candF`) is stated for
the restarted image word's weights `imgStageRhoL κ θ₀ (flowLineRhoL … θ₀) (θ_· − θ₀) ℓ` read in tree order
(`treeIdx`), with `θ₀ = flagAngle (fl 0)`. This file identifies them with the words of PROVE-PROP59-NODETREE:

* `candAngF_of_le`: the flag candidate's angles are `flagAngle (fl m)`; `swL_candAngF`, `swR_candAngF`: its switch
  weights are the born weights `bornL κ fl`, `bornR κ fl`;
* `sum_flowLineRhoL_angle`, `cLT_flowLine`, `cRT_flowLine`: the junction weight of the angle-`θ` image word does not
  depend on `θ` (R57); hence **`imgRhoLT_flowLine`**, **`imgRhoRT_flowLine`**: the root block is `nodeρL0 κ c θ`,
  `nodeρR0 κ c θ`;
* **`imgStageRhoL_treeIdxF`**, **`imgStageRhoR_treeIdxF`**: the tree-ordered weights are
  `consAlt (bornL κ fl) (nodeρL0 κ c θ₀) ℓ` (resp. right);
* **`stageρL_nodeρL`**, **`stageρR_nodeρR`**: at the node depth `nodeLen s + j` with the node flags these are the
  node law's weights `stageρL κ (nodeρL κ c s) j` (indices cast along `Nat.add_assoc`);
* **`imgStageRhoL_treeIdx_node`**, **`imgStageRhoR_treeIdx_node`**: the combination, for every admissible list.

Deterministic. R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any
`*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open QuantumZipper (chiC)
open scoped NNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open Prop513TreeExtract Prop513Schedule Prop59Stage Prop59System Prop59Pieces Prop59NodeTree Restart
open StagedS6 StagedFinal CrossCond.Word49
open Theorem14.GW2Schedule (schedAngle)

/-! ### Angles and switch weights of a flag candidate -/

section Angles

variable {κ : ℝ} {fl : ℕ → Bool} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

/-- **The flag candidate's angles are the flag angles** up to the last piece. -/
theorem candAngF_of_le (hv : IsValid ℓ t) {m : ℕ} (hm : m ≤ ℓ) : candAngF fl ℓ t m = flagAngle (fl m) :=
  schedAngle_mkSchedF_of_le hv (lt_add_one _) hm

/-- **The left switch weights of the flag candidate are the born weights.** -/
theorem swL_candAngF (hv : IsValid ℓ t) {m : ℕ} (hm : m + 1 ≤ ℓ) :
    swL κ (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) (m + 1) = bornL κ fl m := by
  simp only [swL, bornL, Nat.add_sub_cancel]
  rw [candAngF_of_le hv hm, candAngF_of_le hv (by omega : m ≤ ℓ)]
  ring

/-- **The right switch weights of the flag candidate are the born weights.** -/
theorem swR_candAngF (hv : IsValid ℓ t) {m : ℕ} (hm : m + 1 ≤ ℓ) :
    swR κ (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) (m + 1) = bornR κ fl m := by
  simp only [swR, bornR, Nat.add_sub_cancel]
  rw [candAngF_of_le hv hm, candAngF_of_le hv (by omega : m ≤ ℓ)]
  ring

end Angles

/-! ### The root block: the junction weight does not depend on the first angle -/

section Root

variable (κ : ℝ) (c : BoundaryWord)

theorem sum_flowLineRhoL_angle (θ : ℝ) :
    ∑ i, flowLineRhoL κ c.fn c.jumps 0 θ i =
      ∑ i, flowLineRhoL κ c.fn c.jumps 0 (π / 2) i + (π / 2 - θ) * (chiC κ / sleLambda κ) := by
  have h := flowLineRhoL_sub κ c.fn c.jumps 0 θ (π / 2)
  have e : ∑ i, flowLineRhoL κ c.fn c.jumps 0 θ i - ∑ i, flowLineRhoL κ c.fn c.jumps 0 (π / 2) i =
      (π / 2 - θ) * (chiC κ / sleLambda κ) := by
    rw [← sum_sub_distrib, sum_congr rfl fun i _ => h i]
    rw [sum_eq_single (⟨0, flowLineNL_pos c.fn c.jumps 0⟩ : Fin (flowLineNL c.fn c.jumps 0))]
    · simp
    · intro b _ hb
      have hb' : (b : ℕ) ≠ 0 := fun h0 => hb (Fin.ext h0)
      simp only [hb', ↓reduceIte]
    · intro hn; exact absurd (mem_univ _) hn
  linarith

theorem sum_flowLineRhoR_angle (θ : ℝ) :
    ∑ j, flowLineRhoR κ c.fn c.jumps 0 θ j =
      ∑ j, flowLineRhoR κ c.fn c.jumps 0 (π / 2) j + (θ - π / 2) * (chiC κ / sleLambda κ) := by
  have h := flowLineRhoR_sub κ c.fn c.jumps 0 θ (π / 2)
  have e : ∑ j, flowLineRhoR κ c.fn c.jumps 0 θ j - ∑ j, flowLineRhoR κ c.fn c.jumps 0 (π / 2) j =
      (θ - π / 2) * (chiC κ / sleLambda κ) := by
    rw [← sum_sub_distrib, sum_congr rfl fun i _ => h i]
    rw [sum_eq_single (⟨0, flowLineNR_pos c.fn c.jumps 0⟩ : Fin (flowLineNR c.fn c.jumps 0))]
    · simp
    · intro b _ hb
      have hb' : (b : ℕ) ≠ 0 := fun h0 => hb (Fin.ext h0)
      simp only [hb', ↓reduceIte]
    · intro hn; exact absurd (mem_univ _) hn
  linarith

variable {κ}

/-- **The left junction weight of the angle-`θ` image word is the root word's** (R57). -/
theorem cLT_flowLine (hκ : 0 < κ) (θ : ℝ) :
    Theta.cLT θ κ (∑ i, flowLineRhoL κ c.fn c.jumps 0 θ i) =
      cL6 κ (∑ i, flowLineRhoL κ c.fn c.jumps 0 (π / 2) i) := by
  have hr : chiC κ / sleLambda κ = (2 - κ / 2) / π := by
    rw [eq_div_iff Real.pi_pos.ne', mul_comm, ← angleWeightBound_eq hκ, angleWeightBound, mul_div_assoc]
  rw [sum_flowLineRhoL_angle, hr, Theta.cLT, cL6]
  field_simp
  ring

/-- **The right junction weight of the angle-`θ` image word is the root word's** (R57). -/
theorem cRT_flowLine (hκ : 0 < κ) (θ : ℝ) :
    Theta.cRT θ κ (∑ j, flowLineRhoR κ c.fn c.jumps 0 θ j) =
      cR6 κ (∑ j, flowLineRhoR κ c.fn c.jumps 0 (π / 2) j) := by
  have hr : chiC κ / sleLambda κ = (2 - κ / 2) / π := by
    rw [eq_div_iff Real.pi_pos.ne', mul_comm, ← angleWeightBound_eq hκ, angleWeightBound, mul_div_assoc]
  rw [sum_flowLineRhoR_angle, hr, Theta.cRT, cR6]
  field_simp
  ring

/-- **The root block of the angle-`θ` image word is the node experiment's initial root word.** -/
theorem imgRhoLT_flowLine (hκ : 0 < κ) (θ : ℝ) :
    Theta.imgRhoLT (flowLineRhoL κ c.fn c.jumps 0 θ) θ κ = nodeρL0 κ c θ := by
  rw [Theta.imgRhoLT, nodeρL0, cLT_flowLine c hκ θ]

theorem imgRhoRT_flowLine (hκ : 0 < κ) (θ : ℝ) :
    Theta.imgRhoRT (flowLineRhoR κ c.fn c.jumps 0 θ) θ κ = nodeρR0 κ c θ := by
  rw [Theta.imgRhoRT, nodeρR0, cRT_flowLine c hκ θ]

end Root

/-! ### The weights in tree order -/

section Tree

variable {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) {fl : ℕ → Bool} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

include hκ in
/-- **The left weights of the flag candidate's restarted word in tree order** are the born weights in front of the
initial root word at the first angle. -/
theorem imgStageRhoL_treeIdxF (hv : IsValid ℓ t) (i : Fin (rootNL c + ℓ)) :
    imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (fl 0)))
        (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ (treeIdx ℓ (rootNL c) i) =
      consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) ℓ i := by
  rw [consAlt_apply]
  by_cases h : (i : ℕ) < ℓ
  · rw [imgStageRhoL, append_treeIdx_of_lt _ _ h]
    simp only [consAltN, h, ↓reduceIte]
    have e : (((⟨ℓ - 1 - i, by omega⟩ : Fin ℓ) : ℕ) + 1) = (ℓ - 1 - i) + 1 := rfl
    exact swL_candAngF hv (m := ℓ - 1 - i) (by omega)
  · rw [imgStageRhoL, append_treeIdx_of_ge _ _ (not_lt.1 h), imgRhoLT_flowLine c hκ]
    have hi : (i : ℕ) - ℓ < rootNL c := by omega
    simp only [consAltN, h, ↓reduceIte, hi, ↓reduceDIte]

include hκ in
theorem imgStageRhoR_treeIdxF (hv : IsValid ℓ t) (j : Fin (rootNR c + ℓ)) :
    imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (fl 0)))
        (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ (treeIdx ℓ (rootNR c) j) =
      consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) ℓ j := by
  rw [consAlt_apply]
  by_cases h : (j : ℕ) < ℓ
  · rw [imgStageRhoR, append_treeIdx_of_lt _ _ h]
    simp only [consAltN, h, ↓reduceIte]
    exact swR_candAngF hv (m := ℓ - 1 - j) (by omega)
  · rw [imgStageRhoR, append_treeIdx_of_ge _ _ (not_lt.1 h), imgRhoRT_flowLine c hκ]
    have hj : (j : ℕ) - ℓ < rootNR c := by omega
    simp only [consAltN, h, ↓reduceIte, hj, ↓reduceDIte]

end Tree

/-! ### At the node depth: the node law's stage weights -/

section Node

variable (κ : ℝ) (c : BoundaryWord) (s : Schedule)

/-- After the node prefix the born weights are the alternating stage weights. -/
theorem bornL_nodeFlag_add (k : ℕ) : bornL κ (nodeFlag s) (nodeLen s + k) = newL κ k := by
  rw [bornL, show nodeLen s + k + 1 = nodeLen s + (k + 1) by omega, nodeFlag_add, nodeFlag_add, newL,
    angleWeightBound]
  rcases Nat.even_or_odd k with hk | hk
  · have hk' : ¬ Even (k + 1) := Nat.not_even_iff_odd.2 hk.add_one
    simp only [stageFlag, flagAngle, decide_eq_true hk, decide_eq_false hk', ↓reduceIte, hk.neg_one_pow,
      Bool.false_eq_true]
    ring
  · have hk' : Even (k + 1) := hk.add_one
    have hk0 : ¬ Even k := Nat.not_even_iff_odd.2 hk
    simp only [stageFlag, flagAngle, decide_eq_false hk0, decide_eq_true hk', ↓reduceIte, hk.neg_one_pow,
      Bool.false_eq_true]
    ring

theorem bornR_nodeFlag_add (k : ℕ) : bornR κ (nodeFlag s) (nodeLen s + k) = newR κ k := by
  have h := bornL_nodeFlag_add κ s k
  rw [bornL, newL] at h
  rw [bornR, newR]
  linarith

/-- **The node law's left stage weights are the born weights of the node flags at the full depth.** -/
theorem stageρL_nodeρL (j : ℕ) (i : Fin (rootNL c + nodeLen s + j)) :
    stageρL κ (nodeρL κ c s) j i =
      consAlt (bornL κ (nodeFlag s)) (nodeρL0 κ c (flagAngle (nodeFlag s 0))) (nodeLen s + j)
        (Fin.cast (Nat.add_assoc _ _ _) i) := by
  rw [stageρL, consAlt_apply, consAlt_apply, nodeρL]
  simp only [consAltN, Fin.val_cast]
  by_cases h : (i : ℕ) < j
  · simp only [h, ↓reduceIte, show (i : ℕ) < nodeLen s + j by omega]
    rw [show nodeLen s + j - 1 - i = nodeLen s + (j - 1 - i) by omega, bornL_nodeFlag_add]
  · simp only [h, ↓reduceIte, show (i : ℕ) - j < rootNL c + nodeLen s by omega, ↓reduceDIte]
    rw [consAlt_apply]
    simp only [consAltN]
    by_cases h' : (i : ℕ) < nodeLen s + j
    · simp only [show (i : ℕ) - j < nodeLen s by omega, h', ↓reduceIte]
      rw [show nodeLen s - 1 - ((i : ℕ) - j) = nodeLen s + j - 1 - i by omega]
    · simp only [show ¬ ((i : ℕ) - j < nodeLen s) by omega, h', ↓reduceIte,
        show (i : ℕ) - j - nodeLen s = i - (nodeLen s + j) by omega]

theorem stageρR_nodeρR (j : ℕ) (i : Fin (rootNR c + nodeLen s + j)) :
    stageρR κ (nodeρR κ c s) j i =
      consAlt (bornR κ (nodeFlag s)) (nodeρR0 κ c (flagAngle (nodeFlag s 0))) (nodeLen s + j)
        (Fin.cast (Nat.add_assoc _ _ _) i) := by
  rw [stageρR, consAlt_apply, consAlt_apply, nodeρR]
  simp only [consAltN, Fin.val_cast]
  by_cases h : (i : ℕ) < j
  · simp only [h, ↓reduceIte, show (i : ℕ) < nodeLen s + j by omega]
    rw [show nodeLen s + j - 1 - i = nodeLen s + (j - 1 - i) by omega, bornR_nodeFlag_add]
  · simp only [h, ↓reduceIte, show (i : ℕ) - j < rootNR c + nodeLen s by omega, ↓reduceDIte]
    rw [consAlt_apply]
    simp only [consAltN]
    by_cases h' : (i : ℕ) < nodeLen s + j
    · simp only [show (i : ℕ) - j < nodeLen s by omega, h', ↓reduceIte]
      rw [show nodeLen s - 1 - ((i : ℕ) - j) = nodeLen s + j - 1 - i by omega]
    · simp only [show ¬ ((i : ℕ) - j < nodeLen s) by omega, h', ↓reduceIte,
        show (i : ℕ) - j - nodeLen s = i - (nodeLen s + j) by omega]

variable {κ}

/-- **The node candidate's weights**: at the node depth `nodeLen s + j`, for the node flags and any admissible list,
the flag candidate's left weights in tree order are the node law's stage weights. -/
theorem imgStageRhoL_treeIdx_node (hκ : 0 < κ) (j : ℕ) {t : Fin (nodeLen s + j) → ℝ≥0}
    (hv : IsValid (nodeLen s + j) t) (i : Fin (rootNL c + nodeLen s + j)) :
    imgStageRhoL κ (flagAngle (nodeFlag s 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (nodeFlag s 0)))
        (fun k => candAngF (nodeFlag s) (nodeLen s + j) t k - candAngF (nodeFlag s) (nodeLen s + j) t 0)
        (nodeLen s + j) (treeIdx (nodeLen s + j) (rootNL c) (Fin.cast (Nat.add_assoc _ _ _) i)) =
      stageρL κ (nodeρL κ c s) j i := by
  rw [imgStageRhoL_treeIdxF hκ c hv, stageρL_nodeρL]

theorem imgStageRhoR_treeIdx_node (hκ : 0 < κ) (j : ℕ) {t : Fin (nodeLen s + j) → ℝ≥0}
    (hv : IsValid (nodeLen s + j) t) (i : Fin (rootNR c + nodeLen s + j)) :
    imgStageRhoR κ (flagAngle (nodeFlag s 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (nodeFlag s 0)))
        (fun k => candAngF (nodeFlag s) (nodeLen s + j) t k - candAngF (nodeFlag s) (nodeLen s + j) t 0)
        (nodeLen s + j) (treeIdx (nodeLen s + j) (rootNR c) (Fin.cast (Nat.add_assoc _ _ _) i)) =
      stageρR κ (nodeρR κ c s) j i := by
  rw [imgStageRhoR_treeIdxF hκ c hv, stageρR_nodeρR]

end Node

end InteractingSLE.Sec5.CrossCond.StagedNComp
