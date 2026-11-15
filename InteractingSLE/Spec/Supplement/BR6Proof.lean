/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR6ProofSeed
import InteractingSLE.Spec.Supplement.BR6
import InteractingSLE.Spec.Supplement.BR3Ref
import InteractingSLE.Spec.Supplement.G12RemPassiveWord

/-!
# Theorem BR6, sufficiency, for ordered words with a left mark and a right mark before `z`

Packet PROVE-T14-BR4. Supplement p. 610, Theorem BR6 (sufficiency, "⇐"): for `k > 4`, `z > 0` and an ordered finite
force word satisfying the three conditions (left group ends admissible; right group ends before `z` admissible; every
right interval meeting `(z, ∞)` has cumulative weight `≤ k/2 − 4`), every integrated evolution with a generating trace
visits `z` at a finite time almost surely.

Here the word is required to have a left mark and a right mark strictly before `z`. Every flow-line word has both (its
seed marks sit at `0⁻` and `0⁺`, `flowLineXL`/`flowLineXR`), so this covers every use of BR6 in the supplement's
proofs of Theorem 1.4 (BW2, GW2's forced arcs, GW2a's connectors), which apply it to (reflected) counterflow words.

**Reduction to the core** (`BR6Proof.ae_visit_dist`, `BR6ProofSeed`):
1. insert `z` as a passive right mark right after the last right mark below `z`
   (`Supp7.G12.isIntegratedSLEEvolution_insertPassive`, on the given evolution);
2. amalgamate coincident marks (`IsIntegratedSLEEvolution.amalgamate`): a distinct word whose right class of `z` has
   index `J ≥ 1` (the class of the right mark below `z` precedes it), with the same driver, lifetime and trace;
3. BR6's conditions become the core's: class partial sums are sums over positions (`sum_le_amCls_eq`,
   `sum_le_amClsL_eq`), the passive mark has weight `0` (`sum_insertNth_filter_le`), and each position threshold is a
   group end of the original word (`exists_groupEnd_right`, `exists_groupEnd_left`).

## Main results

* `BR6Proof.ae_visit_dist_idx`: the core with a general right length and target index;
* **`BR6Proof.ae_visit_of_conditions`**: BR6 sufficiency for ordered words with a left mark and a right mark below `z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace BR6Proof

open BR3Ref

/-! ### The core with a general right length -/

/-- **BR6 sufficiency, core, with a general target index** `J : Fin nR` (`J ≥ 1`): the form of `ae_visit_dist` for a
right list of any length. -/
theorem ae_visit_dist_idx (hT13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 4 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hD : LP.IsDistinctForceWord xL xR)
    (J : Fin nR) (hJ : 1 ≤ (J : ℕ)) (hnL : 0 < nL)
    (hL : ∀ i : Fin nL, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hR : ∀ i : Fin nR, i < J → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hlow : ∀ i : Fin nR, J ≤ i → ∑ l ∈ univ.filter (· ≤ i), ρR l ≤ κ / 2 - 4) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ η ω t = xR J := by
  obtain ⟨j, hjJ⟩ : ∃ j : ℕ, (J : ℕ) = j := ⟨_, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, nR = j + 1 + m := ⟨nR - (j + 1), by have := J.isLt; omega⟩
  have hJe : J = LP.retargetIdx j m := Fin.ext (by simp [LP.retargetIdx, hjJ])
  subst hJe
  refine ae_visit_dist hT13 hκ hD (by omega) hnL hL (fun i hi => hR i ?_) (fun v hv1 hv2 => ?_) hE hη
  · rw [Fin.lt_def]; simpa [LP.retargetIdx] using hi
  · have hv0 : v - 1 < j + 1 + m := by omega
    have e : pre ρR v = ∑ l ∈ univ.filter (· ≤ (⟨v - 1, hv0⟩ : Fin (j + 1 + m))), ρR l := by
      rw [sum_filter_le_eq_pre]
      congr 1
      simp only
      omega
    rw [e]
    exact hlow _ (by rw [Fin.le_def]; simp [LP.retargetIdx]; omega)

/-! ### Sums over positions -/

section Sums

variable {n : ℕ}

/-- A zero weight inserted at a new position does not change a position-threshold sum. -/
theorem sum_insertNth_filter_le (x : Fin n → ℝ) (ρ : Fin n → ℝ) (p : Fin (n + 1)) (y q : ℝ) :
    ∑ i ∈ univ.filter (fun i => Fin.insertNth (α := fun _ => ℝ) p y x i ≤ q),
        Fin.insertNth (α := fun _ => ℝ) p 0 ρ i = ∑ i ∈ univ.filter (fun i => x i ≤ q), ρ i := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_succAbove _ p]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, ite_self, zero_add]

/-- **Right class partial sums are position-threshold sums**: the partial sum of the amalgamated weights up to the
class `c` is the total weight of the marks at positions `≤ amPos x c`. -/
theorem sum_le_amCls_eq (x : Fin n → ℝ) (ρ : Fin n → ℝ) (c : Fin (Finset.univ.image x).card) :
    ∑ l ∈ univ.filter (· ≤ c), LP.amWeight (LP.amCls x) ρ l =
      ∑ i ∈ univ.filter (fun i => x i ≤ LP.amPos x c), ρ i := by
  rw [sum_filter_le_eq_pre, pre_amWeight]
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  rw [Nat.lt_succ_iff, ← Fin.le_def, ← (LP.strictMono_amPos x).le_iff_le, LP.amPos_amCls]

/-- **Left class partial sums are position-threshold sums**: the partial sum of the amalgamated left weights up to the
class `c` (classes outward from the seed) is the total weight of the marks at positions `≥ amXL x c`. -/
theorem sum_le_amClsL_eq (x : Fin n → ℝ) (ρ : Fin n → ℝ) (c : Fin (Finset.univ.image x).card) :
    ∑ l ∈ univ.filter (· ≤ c), LP.amWeight (LP.amClsL x) ρ l =
      ∑ i ∈ univ.filter (fun i => LP.amXL x c ≤ x i), ρ i := by
  rw [sum_filter_le_eq_pre, pre_amWeight]
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  rw [Nat.lt_succ_iff, ← Fin.le_def]
  conv_lhs => rw [← LP.amClsL_amRepL x c]
  rw [amClsL_le_amClsL_iff, LP.apply_amRepL x c]

/-- **A right position threshold is a group end**: for monotone positions and a threshold `q` above some mark, the
last mark at a position `≤ q` ends its group, and the partial sum up to it is the total weight at positions `≤ q`. -/
theorem exists_groupEnd_right {x : Fin n → ℝ} (hx : Monotone x) (ρ : Fin n → ℝ) {q : ℝ} (hne : ∃ i, x i ≤ q) :
    ∃ m : Fin n, (∀ i, m < i → x m < x i) ∧ x m ≤ q ∧ (∀ i, x i ≤ q → x i ≤ x m) ∧
      ∑ i ∈ univ.filter (· ≤ m), ρ i = ∑ i ∈ univ.filter (fun i => x i ≤ q), ρ i := by
  set A := univ.filter (fun i => x i ≤ q) with hA
  have hAne : A.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hA, hi]⟩
  set m := A.max' hAne with hm
  have hmA : x m ≤ q := (mem_filter.1 (A.max'_mem hAne)).2
  have hle : ∀ i, x i ≤ q → i ≤ m := fun i hi => A.le_max' i (by simp [hA, hi])
  refine ⟨m, fun i hi => ?_, hmA, fun i hi => hx (hle i hi), ?_⟩
  · by_contra h
    rw [not_lt] at h
    exact absurd (hle i (h.trans hmA)) (not_le.2 hi)
  · refine Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => (hx h).trans hmA, hle i⟩) fun _ _ => rfl

/-- **A left position threshold is a group end** (antitone positions; the last mark at a position `≥ q`). -/
theorem exists_groupEnd_left {x : Fin n → ℝ} (hx : Antitone x) (ρ : Fin n → ℝ) {q : ℝ} (hne : ∃ i, q ≤ x i) :
    ∃ m : Fin n, (∀ i, m < i → x i < x m) ∧ q ≤ x m ∧
      ∑ i ∈ univ.filter (· ≤ m), ρ i = ∑ i ∈ univ.filter (fun i => q ≤ x i), ρ i := by
  set A := univ.filter (fun i => q ≤ x i) with hA
  have hAne : A.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hA, hi]⟩
  set m := A.max' hAne with hm
  have hmA : q ≤ x m := (mem_filter.1 (A.max'_mem hAne)).2
  have hle : ∀ i, q ≤ x i → i ≤ m := fun i hi => A.le_max' i (by simp [hA, hi])
  refine ⟨m, fun i hi => ?_, hmA, ?_⟩
  · by_contra h
    rw [not_lt] at h
    exact absurd (hle i (hmA.trans h)) (not_le.2 hi)
  · refine Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => hmA.trans (hx h), hle i⟩) fun _ _ => rfl

end Sums

/-! ### BR6 sufficiency -/

/-- **Theorem BR6, sufficiency** (supplement p. 610, "⇐"), for ordered words with a left mark and a right mark strictly
before `z` (every flow-line word: seed marks at `0⁻`, `0⁺`). For `k > 4` and `z > 0`, if every left group end is
admissible (condition 1), every right group end before `z` is admissible (condition 2) and every right interval meeting
`(z, ∞)` has cumulative weight at most `k/2 − 4` (condition 3), then every integrated `SLE_k(ρ)` evolution with a
generating trace `η` visits `z` at a finite time `t ≤ ζ` almost surely. -/
theorem ae_visit_of_conditions (hT13 : Exist.Theorem13Statement.{u}) {k : ℝ} (hk : 4 < k) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {z : ℝ} (hz : 0 < z)
    (hF : IsOrderedForceWord xL xR) (hnL : 0 < nL) (hzR : ∃ i, xR i < z) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω))
    (h1 : GW0.LeftGroupEndsAdmissible xL ρL) (h2 : BR6.RightAdmissibleBefore xR ρR z)
    (h3 : BR6.RightLowBeyond k xR ρR z) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ η ω t = z := by
  obtain ⟨hxLa, hxL0, hxRm, hxR0⟩ := hF
  -- the last right mark below `z`
  set A := univ.filter (fun i => xR i < z) with hA
  have hAne : A.Nonempty := by
    obtain ⟨i, hi⟩ := hzR
    exact ⟨i, by simp [hA, hi]⟩
  set kk := A.max' hAne with hkk
  have hkz : xR kk < z := (mem_filter.1 (A.max'_mem hAne)).2
  have hky : ∀ j, xR j < z → j ≤ kk := fun j hj => A.le_max' j (by simp [hA, hj])
  -- step 1: insert `z` as a passive right mark
  have hE1 := Supp7.G12.isIntegratedSLEEvolution_insertPassive hE ⟨hxLa, hxL0, hxRm, hxR0⟩ hz hkz hky
  set xR' := Fin.insertNth (α := fun _ => ℝ) kk.succ z xR with hxR'
  set ρR' := Fin.insertNth (α := fun _ => ℝ) kk.succ 0 ρR with hρR'
  have hb : ∀ j : Fin nR, j.castSucc < kk.succ → xR j ≤ z := fun j hj =>
    (hxRm (Fin.castSucc_lt_succ_iff.1 hj)).trans hkz.le
  have ha : ∀ j : Fin nR, kk.succ ≤ j.castSucc → z ≤ xR j := fun j hj => by
    by_contra h
    rw [not_le] at h
    have h' := hky j h
    rw [Fin.le_def] at hj h'
    simp only [Fin.val_succ, Fin.val_castSucc] at hj
    omega
  have hxR'm : Monotone xR' := Supp7.G12.monotone_insertNth hxRm kk.succ hb ha
  have hxR'0 : ∀ i, 0 ≤ xR' i := by
    intro i
    rcases Fin.eq_self_or_eq_succAbove kk.succ i with rfl | ⟨j, rfl⟩
    · simp only [hxR', Fin.insertNth_apply_same]; exact hz.le
    · simp only [hxR', Fin.insertNth_apply_succAbove]; exact hxR0 j
  have hF' : IsOrderedForceWord xL xR' := ⟨hxLa, hxL0, hxR'm, hxR'0⟩
  -- step 2: amalgamate
  have hEa := hE1.amalgamate hF'
  have hDa := LP.isDistinctForceWord_amalgamate hF'
  set J := LP.amCls xR' kk.succ with hJ
  have hJpos : LP.amPos xR' J = z := by
    rw [hJ, LP.amPos_amCls]; simp only [hxR', Fin.insertNth_apply_same]
  have hval : ∀ j : Fin nR, xR' (kk.succ.succAbove j) = xR j := fun j => by
    simp only [hxR', Fin.insertNth_apply_succAbove]
  have hJ1 : 1 ≤ (J : ℕ) := by
    have hlt : LP.amCls xR' (kk.succ.succAbove kk) < J := by
      rw [hJ, amCls_lt_amCls_iff, hval]
      simpa [hxR'] using hkz
    rw [Fin.lt_def] at hlt
    omega
  have hnLa : 0 < (Finset.univ.image xL).card :=
    Finset.card_pos.2 ⟨xL ⟨0, hnL⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  -- step 3: the conditions of the core
  have hLa : ∀ c, -2 < ∑ l ∈ univ.filter (· ≤ c), LP.amWeight (LP.amClsL xL) ρL l := by
    intro c
    rw [sum_le_amClsL_eq]
    obtain ⟨m, hmend, -, hmsum⟩ := exists_groupEnd_left hxLa ρL (q := LP.amXL xL c)
      ⟨LP.amRepL xL c, (LP.apply_amRepL xL c).ge⟩
    rw [← hmsum]
    exact h1 m hmend
  have hsumR : ∀ c, ∑ l ∈ univ.filter (· ≤ c), LP.amWeight (LP.amCls xR') ρR' l =
      ∑ i ∈ univ.filter (fun i => xR i ≤ LP.amPos xR' c), ρR i := fun c => by
    rw [sum_le_amCls_eq]
    exact sum_insertNth_filter_le xR ρR kk.succ z _
  have hRa : ∀ c, c < J → -2 < ∑ l ∈ univ.filter (· ≤ c), LP.amWeight (LP.amCls xR') ρR' l := by
    intro c hc
    rw [hsumR]
    have hq : LP.amPos xR' c < z := by rw [← hJpos]; exact LP.strictMono_amPos xR' hc
    have hne : ∃ i, xR i ≤ LP.amPos xR' c := by
      rcases Fin.eq_self_or_eq_succAbove kk.succ (LP.amRep xR' c) with h | ⟨j, hj⟩
      · exfalso
        have e := LP.apply_amRep xR' c
        rw [h] at e
        simp only [hxR', Fin.insertNth_apply_same] at e
        linarith
      · refine ⟨j, le_of_eq ?_⟩
        rw [← hval j, ← hj, LP.apply_amRep xR' c]
    obtain ⟨m, hmend, hmq, -, hmsum⟩ := exists_groupEnd_right hxRm ρR hne
    rw [← hmsum]
    exact h2 m hmend (lt_of_le_of_lt hmq hq)
  have hlowa : ∀ c, J ≤ c → ∑ l ∈ univ.filter (· ≤ c), LP.amWeight (LP.amCls xR') ρR' l ≤ k / 2 - 4 := by
    intro c hc
    rw [hsumR]
    have hq : z ≤ LP.amPos xR' c := by rw [← hJpos]; exact (LP.strictMono_amPos xR').monotone hc
    obtain ⟨m, -, hmq, hmax, hmsum⟩ := exists_groupEnd_right hxRm ρR (q := LP.amPos xR' c) ⟨kk, hkz.le.trans hq⟩
    have hbeyond : ∀ i, xR i ≤ xR m ∨ z < xR i := fun i => by
      by_cases h : xR i ≤ LP.amPos xR' c
      · exact Or.inl (hmax i h)
      · exact Or.inr (lt_of_le_of_lt hq (not_le.1 h))
    have h3m := h3 (xR m) (Or.inr ⟨m, rfl⟩) hbeyond
    have e : ∑ i ∈ univ.filter (fun i => xR i ≤ LP.amPos xR' c), ρR i =
        ∑ i ∈ univ.filter (fun i => xR i ≤ xR m), ρR i :=
      Finset.sum_congr (Finset.filter_congr fun i _ => ⟨hmax i, fun h => h.trans hmq⟩) fun _ _ => rfl
    rw [e]
    exact h3m
  have hmain := ae_visit_dist_idx hT13 hk hDa J hJ1 hnLa hLa hRa hlowa hEa hη
  filter_upwards [hmain] with ω ⟨t, ht, hηt⟩
  exact ⟨t, ht, by rw [hηt, hJpos]⟩

end BR6Proof

end Theorem14

end InteractingSLE
