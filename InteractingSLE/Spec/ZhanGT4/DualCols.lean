/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualD12Cols

/-!
# Zhan's A.1.4, (D12): the random column ends are stopping times; the column product is a martingale

Packet PROVE-ZHAN-GT4-A14. Source: Astra, *Follow-up proofs*, §A.1.4 (`ig1_followup_proofs.txt` L385–L407, R38):
"The `R_k` are increasing stopping times, and `I_{k+1}` is measurable at `R_k` … For a time `I ≤ t̄` known at a
stopping time `R`, the process `M(R + s, I)` … is a local martingale in `s` … On each `[R_{k−1}, R_k]`, its ratio to
its value at `R_{k−1}` is `M(s, I_k)/M(R_{k−1}, I_k)`. After at most `n` such intervals it is constant. Thus
`M*(s, t̄)` is a bounded martingale."

The second curve is **frozen** (a fixed path of it): its exit times `S₂ i` and the cap `t̄` are numbers. The first
curve's exit times `S₁ i` are stopping times of a filtration `𝓕`. The column ends of the staircase are the `S₁ i ω`;
they are visited in increasing order by `colTime S₁ k` (`τ₀ = 0`, `τ_{k+1}` = the least column end above `τ_k`), and
on the column `[τ_k, τ_{k+1}]` the height index `colIdx` is an index of maximal `S₂` among the rectangles reaching
beyond `τ_k` (a fixed tie-break), chosen from the information at `τ_k`.

## Main results

* `nextIn_le_iff` (deterministic): `nextIn C x ≤ u ↔ (C ≤ x ∧ x ≤ u) ∨ ∃ c ∈ C, x < c ≤ u`;
* `isStoppingTime_colTime`: **the column ends `τ_k` are stopping times**;
* `measurableSet_colIdx_eq`: **the height index on `[τ_k, τ_{k+1}]` is `𝓕_{τ_k}`-measurable**;
* `concatProc_colTime_eq`: the concatenation of the frozen-height processes `Y_i(s) = N(s ∧ S₁ i, S₂ i ∧ t̄)` along
  `(τ_k, j_k)` is, pathwise, the closed column product `∏_c N(c ∧ s, h c ∧ t̄)/N(prev c ∧ s, h c ∧ t̄)` of (D11);
* **`martingale_colProd`**: if every `Y_i` is a right-continuous martingale with values in `[c, C]`, `c > 0`, the column
  product is a right-continuous martingale bounded by `(C/c)^{|ι|}` — the stochastic half of (D12) for one frozen path
  of the second curve;
* `colProd_zero`, `colProd_eq_colProdT`, **`integral_colProd_eq_one`**: the product is `1` at `s = 0`, equals its
  terminal value `colProdT` once `s` exceeds every column end, and has mean one (`E[M*(Σ₁, t̄) N(Σ₁, 0)/N(0, 0)] = 1`
  for bounded exit times — the first of the two successive optional samplings of §A.1.3);
* `martingale_patch_mul_marginal`: the same for `M*(s, t̄) · N(max C ∧ s, 0)/N(0, 0)` ((D11) with the normalization
  (D6) in the ordinary base, `patch_mul_marginal`).
-/

set_option autoImplicit false

noncomputable section

open Set Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-! ### `nextIn`, deterministic -/

/-- **`nextIn` below a level**: `nextIn C x ≤ u` iff either no element of `C` lies above `x` and `x ≤ u`, or some
element of `C` lies in `(x, u]`. -/
theorem nextIn_le_iff {C : Finset ℝ} {x u : ℝ} :
    nextIn C x ≤ u ↔ ((∀ c ∈ C, c ≤ x) ∧ x ≤ u) ∨ ∃ c ∈ C, x < c ∧ c ≤ u := by
  unfold nextIn
  split_ifs with h
  · have hm := (C.filter (x < ·)).min'_mem h
    obtain ⟨hmC, hmx⟩ := Finset.mem_filter.1 hm
    constructor
    · intro hu
      exact Or.inr ⟨_, hmC, hmx, hu⟩
    · rintro (⟨hall, -⟩ | ⟨c, hc, hxc, hcu⟩)
      · exact absurd (hall _ hmC) (not_le.2 hmx)
      · exact ((C.filter (x < ·)).min'_le c (Finset.mem_filter.2 ⟨hc, hxc⟩)).trans hcu
  · have hall : ∀ c ∈ C, c ≤ x := fun c hc => by
      by_contra hcx
      exact h ⟨c, Finset.mem_filter.2 ⟨hc, not_le.1 hcx⟩⟩
    constructor
    · intro hu; exact Or.inl ⟨hall, hu⟩
    · rintro (⟨-, hu⟩ | ⟨c, hc, hxc, -⟩)
      · exact hu
      · exact absurd (hall c hc) (not_le.2 hxc)

/-- If some element of `C` lies above `x`, `nextIn C x` is one of them, the least. -/
theorem nextIn_spec {C : Finset ℝ} {x : ℝ} (h : ∃ c ∈ C, x < c) :
    nextIn C x ∈ C ∧ x < nextIn C x ∧ ∀ c ∈ C, x < c → nextIn C x ≤ c := by
  have hne : (C.filter (x < ·)).Nonempty := by
    obtain ⟨c, hc, hxc⟩ := h
    exact ⟨c, Finset.mem_filter.2 ⟨hc, hxc⟩⟩
  have e : nextIn C x = (C.filter (x < ·)).min' hne := by unfold nextIn; simp only [hne, ↓reduceDIte]
  obtain ⟨hmC, hmx⟩ := Finset.mem_filter.1 ((C.filter (x < ·)).min'_mem hne)
  refine ⟨e ▸ hmC, e ▸ hmx, fun c hc hxc => ?_⟩
  rw [e]
  exact (C.filter (x < ·)).min'_le c (Finset.mem_filter.2 ⟨hc, hxc⟩)

/-- If no element of `C` lies above `x`, `nextIn C x = x`. -/
theorem nextIn_eq_self {C : Finset ℝ} {x : ℝ} (h : ∀ c ∈ C, c ≤ x) : nextIn C x = x := by
  have hne : ¬ (C.filter (x < ·)).Nonempty := by
    rintro ⟨c, hc⟩
    obtain ⟨hcC, hxc⟩ := Finset.mem_filter.1 hc
    exact absurd (h c hcC) (not_le.2 hxc)
  unfold nextIn
  simp only [hne, ↓reduceDIte]

theorem colSeq_succ (C : Finset ℝ) (x : ℝ) (k : ℕ) : colSeq C x (k + 1) = nextIn C (colSeq C x k) := by
  unfold colSeq
  rw [Function.iterate_succ_apply']


/-! ### The column ends of a random staircase -/

section Times

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι]
  {S₁ : ι → Ω → ℝ≥0}

/-- The column ends of the staircase of the path `ω`: the values `S₁ i ω`. -/
def colEnds (S₁ : ι → Ω → ℝ≥0) (ω : Ω) : Finset ℝ := stairCols fun i => (S₁ i ω : ℝ)

/-- **The `k`-th column end in increasing order** (`τ₀ = 0`, `τ_{k+1}` = the least column end above `τ_k`, or
`τ_k` if there is none). -/
def colTime (S₁ : ι → Ω → ℝ≥0) (k : ℕ) (ω : Ω) : ℝ≥0 :=
  ⟨colSeq (colEnds S₁ ω) 0 k, le_colSeq _ _ _⟩

theorem coe_colTime (S₁ : ι → Ω → ℝ≥0) (k : ℕ) (ω : Ω) :
    (colTime S₁ k ω : ℝ) = colSeq (colEnds S₁ ω) 0 k := rfl

theorem colTime_zero (S₁ : ι → Ω → ℝ≥0) (ω : Ω) : colTime S₁ 0 ω = 0 := NNReal.eq rfl

theorem colTime_le_succ (S₁ : ι → Ω → ℝ≥0) (k : ℕ) (ω : Ω) : colTime S₁ k ω ≤ colTime S₁ (k + 1) ω := by
  rw [← NNReal.coe_le_coe, coe_colTime, coe_colTime, colSeq_succ]
  exact le_nextIn _ _

theorem mem_colEnds {ω : Ω} {c : ℝ} : c ∈ colEnds S₁ ω ↔ ∃ i, (S₁ i ω : ℝ) = c := by
  simp only [colEnds, stairCols, Finset.mem_image, Finset.mem_univ, true_and]

theorem card_colEnds_le (S₁ : ι → Ω → ℝ≥0) (ω : Ω) : (colEnds S₁ ω).card ≤ Fintype.card ι :=
  Finset.card_image_le.trans (le_of_eq Finset.card_univ)

/-- `τ_{k+1} ≤ u` iff either every column end is `≤ τ_k ≤ u`, or some column end lies in `(τ_k, u]`. -/
theorem colTime_succ_le_iff {k : ℕ} {ω : Ω} {u : ℝ≥0} :
    colTime S₁ (k + 1) ω ≤ u ↔ ((∀ i, S₁ i ω ≤ colTime S₁ k ω) ∧ colTime S₁ k ω ≤ u) ∨
      ∃ i, colTime S₁ k ω < S₁ i ω ∧ S₁ i ω ≤ u := by
  rw [← NNReal.coe_le_coe, coe_colTime, colSeq_succ, nextIn_le_iff, ← coe_colTime]
  constructor
  · rintro (⟨hall, hu⟩ | ⟨c, hc, hxc, hcu⟩)
    · exact Or.inl ⟨fun i => NNReal.coe_le_coe.1 (hall _ (mem_colEnds.2 ⟨i, rfl⟩)), NNReal.coe_le_coe.1 hu⟩
    · obtain ⟨i, rfl⟩ := mem_colEnds.1 hc
      exact Or.inr ⟨i, NNReal.coe_lt_coe.1 hxc, NNReal.coe_le_coe.1 hcu⟩
  · rintro (⟨hall, hu⟩ | ⟨i, hxi, hiu⟩)
    · refine Or.inl ⟨fun c hc => ?_, NNReal.coe_le_coe.2 hu⟩
      obtain ⟨i, rfl⟩ := mem_colEnds.1 hc
      exact NNReal.coe_le_coe.2 (hall i)
    · exact Or.inr ⟨_, mem_colEnds.2 ⟨i, rfl⟩, NNReal.coe_lt_coe.2 hxi, NNReal.coe_le_coe.2 hiu⟩

/-- **The column ends are stopping times** ((D12): "the `R_k` are increasing stopping times"): if every `S₁ i` is a
stopping time, so is every `τ_k`. -/
theorem isStoppingTime_colTime (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0)) (k : ℕ) :
    IsStoppingTime 𝓕 fun ω => (colTime S₁ k ω : WithTop ℝ≥0) := by
  induction k with
  | zero =>
    simp only [colTime_zero]
    exact isStoppingTime_const 𝓕 _
  | succ k ih =>
    intro u
    have e : {ω | (colTime S₁ (k + 1) ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
        ({ω | ∀ i, (S₁ i ω : WithTop ℝ≥0) ≤ colTime S₁ k ω} ∩
          {ω | (colTime S₁ k ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)}) ∪
        ⋃ i, ({ω | (S₁ i ω : WithTop ℝ≥0) ≤ colTime S₁ k ω}ᶜ ∩
          {ω | (S₁ i ω : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_compl_iff,
        WithTop.coe_le_coe, not_le]
      exact colTime_succ_le_iff
    rw [e]
    refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun i => ?_)
    · have hA : MeasurableSet[ih.measurableSpace] {ω | ∀ i, (S₁ i ω : WithTop ℝ≥0) ≤ colTime S₁ k ω} := by
        rw [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => IsStoppingTime.measurableSet_stopping_time_le (hS i) ih
      exact ((ih.measurableSet _).1 hA).2 u
    · have hB : MeasurableSet[(hS i).measurableSpace] {ω | (S₁ i ω : WithTop ℝ≥0) ≤ colTime S₁ k ω}ᶜ :=
        (IsStoppingTime.measurableSet_le_stopping_time (hS i) ih).compl
      exact (((hS i).measurableSet _).1 hB).2 u

/-! ### The height index chosen at `τ_k` -/

/-- A fixed choice of an index of maximal `S₂` in a finite set `F` of indices (`i₀` if `F` is empty). -/
def argmaxIdx (S₂ : ι → ℝ) (i₀ : ι) (F : Finset ι) : ι :=
  if h : F.Nonempty then (F.exists_max_image S₂ h).choose else i₀

omit [Fintype ι] in
theorem argmaxIdx_spec (S₂ : ι → ℝ) (i₀ : ι) {F : Finset ι} (h : F.Nonempty) :
    argmaxIdx S₂ i₀ F ∈ F ∧ ∀ i ∈ F, S₂ i ≤ S₂ (argmaxIdx S₂ i₀ F) := by
  have e : argmaxIdx S₂ i₀ F = (F.exists_max_image S₂ h).choose := by
    unfold argmaxIdx; simp only [h, ↓reduceDIte]
  rw [e]
  exact (F.exists_max_image S₂ h).choose_spec

/-- **The height index on the column `[τ_k, τ_{k+1}]`**: an index of maximal `S₂` among the rectangles reaching
beyond `τ_k` ((D12): `I_{k+1} = max{S₂ m : S₁ m > R_k, …}`). -/
def colIdx (S₁ : ι → Ω → ℝ≥0) (S₂ : ι → ℝ) (i₀ : ι) (k : ℕ) (ω : Ω) : ι :=
  argmaxIdx S₂ i₀ (Finset.univ.filter fun i => colTime S₁ k ω < S₁ i ω)

/-- **The height index is known at `τ_k`** ((D12): "`I_{k+1}` is measurable at `R_k`"). -/
theorem measurableSet_colIdx_eq (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0)) (S₂ : ι → ℝ)
    (i₀ : ι) (k : ℕ) (i : ι) :
    MeasurableSet[(isStoppingTime_colTime hS k).measurableSpace] {ω | colIdx S₁ S₂ i₀ k ω = i} := by
  classical
  set hτ := isStoppingTime_colTime hS k
  have e : {ω | colIdx S₁ S₂ i₀ k ω = i} =
      ⋃ F ∈ (Finset.univ.filter fun F : Finset ι => argmaxIdx S₂ i₀ F = i),
        {ω | (Finset.univ.filter fun m => colTime S₁ k ω < S₁ m ω) = F} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, colIdx,
      exists_prop]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨F, hF, rfl⟩; exact hF
  rw [e]
  refine Finset.measurableSet_biUnion _ fun F _ => ?_
  have e2 : {ω | (Finset.univ.filter fun m => colTime S₁ k ω < S₁ m ω) = F} =
      ⋂ m, {ω | colTime S₁ k ω < S₁ m ω ↔ m ∈ F} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [e2]
  refine MeasurableSet.iInter fun m => ?_
  have hle : MeasurableSet[hτ.measurableSpace] {ω | (S₁ m ω : WithTop ℝ≥0) ≤ colTime S₁ k ω} :=
    IsStoppingTime.measurableSet_stopping_time_le (hS m) hτ
  by_cases hm : m ∈ F
  · have e3 : {ω | colTime S₁ k ω < S₁ m ω ↔ m ∈ F} = {ω | (S₁ m ω : WithTop ℝ≥0) ≤ colTime S₁ k ω}ᶜ := by
      ext ω
      simp only [hm, iff_true, Set.mem_ofPred_eq, Set.mem_compl_iff, WithTop.coe_le_coe, not_le]
    rw [e3]
    exact hle.compl
  · have e3 : {ω | colTime S₁ k ω < S₁ m ω ↔ m ∈ F} = {ω | (S₁ m ω : WithTop ℝ≥0) ≤ colTime S₁ k ω} := by
      ext ω
      simp only [hm, iff_false, Set.mem_ofPred_eq, WithTop.coe_le_coe, not_lt]
    rw [e3]
    exact hle

end Times

/-! ### The concatenation along the random columns is the closed column product -/

section Product

variable {Ω : Type*} {ι : Type*} [Fintype ι] {S₁ : ι → Ω → ℝ≥0}

/-- Stopping at a finite time is evaluation at the minimum. -/
theorem stoppedProcess_coe {X : ℝ≥0 → Ω → ℝ} (ρ : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) :
    stoppedProcess X (fun ω => (ρ ω : WithTop ℝ≥0)) s ω = X (min s (ρ ω)) ω := by
  simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]

/-- **The frozen-height process of the rectangle `i`**: `Y_i(s) = N(s ∧ S₁ i, S₂ i ∧ t̄)` — the first curve grown to
`s` and stopped at its exit time, the second curve frozen at height `S₂ i ∧ t̄`. -/
def frzHeightProc (N : Ω → ℝ → ℝ → ℝ) (S₁ : ι → Ω → ℝ≥0) (S₂ : ι → ℝ) (tb : ℝ) (i : ι) (s : ℝ≥0) (ω : Ω) : ℝ :=
  N ω (min (s : ℝ) (S₁ i ω)) (min (S₂ i) tb)

/-- **The closed column product of (D11)** along the path `ω`: `∏_c N(c ∧ s, h c ∧ t̄)/N(prev c ∧ s, h c ∧ t̄)`. -/
def colProd (N : Ω → ℝ → ℝ → ℝ) (S₁ : ι → Ω → ℝ≥0) (S₂ : ι → ℝ) (tb : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  ∏ c ∈ colEnds S₁ ω, (N ω (min c s) (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) tb) /
    N ω (min (prevIn (colEnds S₁ ω) c) s) (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) tb))

/-- **The concatenation along the column ends is the closed column product**: with `τ_k = colTime S₁ k`, the
height indices `j_k = colIdx`, and `n ≥ |ι|`, the concatenated frozen-height processes equal `colProd`. -/
theorem concatProc_colTime_eq {S₂ : ι → ℝ} (hS₂ : ∀ i, 0 ≤ S₂ i) (i₀ : ι) {N : Ω → ℝ → ℝ → ℝ}
    (hN : ∀ ω x y, 0 < N ω x y) (tb : ℝ) {n : ℕ} (hn : Fintype.card ι ≤ n) (s : ℝ≥0) (ω : Ω) :
    concatProc (frzHeightProc N S₁ S₂ tb) (fun k ω => (colTime S₁ k ω : WithTop ℝ≥0)) (colIdx S₁ S₂ i₀) n s ω =
      colProd N S₁ S₂ tb s ω := by
  classical
  have hmono : ∀ k, (fun ω => (colTime S₁ k ω : WithTop ℝ≥0)) ≤ fun ω => (colTime S₁ (k + 1) ω : WithTop ℝ≥0) :=
    fun k ω => WithTop.coe_le_coe.2 (colTime_le_succ S₁ k ω)
  rw [concatProc_eq_prod _ hmono]
  set C := colEnds S₁ ω with hC
  set S₁' : ι → ℝ := fun i => (S₁ i ω : ℝ) with hS₁'
  set f : ℝ → ℝ → ℝ := fun x y => N ω (min x s) (min (stairH S₁' S₂ x) tb) / N ω (min y s) (min (stairH S₁' S₂ x) tb)
    with hf
  have hf1 : ∀ y, f y y = 1 := fun y => div_self (hN _ _ _).ne'
  have key : ∀ k, stoppedProcess (frzHeightProc N S₁ S₂ tb (colIdx S₁ S₂ i₀ k ω))
      (fun ω => (colTime S₁ (k + 1) ω : WithTop ℝ≥0)) s ω /
      stoppedProcess (frzHeightProc N S₁ S₂ tb (colIdx S₁ S₂ i₀ k ω)) (fun ω => (colTime S₁ k ω : WithTop ℝ≥0)) s ω =
      f (colSeq C 0 (k + 1)) (colSeq C 0 k) := by
    intro k
    rw [stoppedProcess_coe, stoppedProcess_coe]
    simp only [frzHeightProc, NNReal.coe_min, coe_colTime]
    rw [colSeq_succ]
    set x := colSeq C 0 k with hx
    by_cases hex : ∃ c ∈ C, x < c
    · obtain ⟨hyC, hxy, hymin⟩ := nextIn_spec hex
      set y := nextIn C x with hy
      set F := Finset.univ.filter fun i => colTime S₁ k ω < S₁ i ω with hF
      have hFne : F.Nonempty := by
        obtain ⟨c, hc, hxc⟩ := hex
        obtain ⟨i, rfl⟩ := mem_colEnds.1 hc
        refine ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
        rw [← NNReal.coe_lt_coe, coe_colTime]; exact hxc
      obtain ⟨hjF, hjmax⟩ := argmaxIdx_spec S₂ i₀ hFne
      set j := colIdx S₁ S₂ i₀ k ω with hj
      have hjF' : j ∈ F := hjF
      have hxj : x < S₁ j ω := by
        have := (Finset.mem_filter.1 hjF').2
        rw [← NNReal.coe_lt_coe, coe_colTime] at this; exact this
      have hyj : y ≤ S₁ j ω := hymin _ (mem_colEnds.2 ⟨j, rfl⟩) hxj
      have hset : ∀ i, (y ≤ S₁' i ↔ i ∈ F) := fun i => by
        simp only [hS₁', hF, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← NNReal.coe_lt_coe, coe_colTime]
        exact ⟨fun h => hxy.trans_le h, fun h => hymin _ (mem_colEnds.2 ⟨i, rfl⟩) h⟩
      have hH : stairH S₁' S₂ y = S₂ j := by
        unfold stairH
        rw [Finset.max'_eq_iff]
        refine ⟨Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _,
          (hset j).2 hjF'⟩, rfl⟩), fun b hb => ?_⟩
        rcases Finset.mem_insert.1 hb with rfl | hb
        · exact hS₂ j
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
          exact hjmax i ((hset i).1 (Finset.mem_filter.1 hi).2)
      simp only [hf, hH]
      rw [min_eq_left ((min_le_right _ _).trans hyj), min_eq_left ((min_le_right _ _).trans hxj.le),
        min_comm (s : ℝ) y, min_comm (s : ℝ) x]
    · push Not at hex
      rw [nextIn_eq_self hex, div_self (hN _ _ _).ne', hf1]
  rw [Finset.prod_congr rfl fun k _ => key k]
  have hC0 : ∀ c ∈ C, 0 ≤ c := fun c hc => by
    obtain ⟨i, rfl⟩ := mem_colEnds.1 hc; exact (S₁ i ω).coe_nonneg
  exact prod_colSeq_eq f hf1 hC0 ((card_colEnds_le S₁ ω).trans hn)

/-- **The terminal column product** `∏_c N(c, h c ∧ t̄)/N(prev c, h c ∧ t̄)` (all columns completed). -/
def colProdT (N : Ω → ℝ → ℝ → ℝ) (S₁ : ι → Ω → ℝ≥0) (S₂ : ι → ℝ) (tb : ℝ) (ω : Ω) : ℝ :=
  ∏ c ∈ colEnds S₁ ω, (N ω c (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) tb) /
    N ω (prevIn (colEnds S₁ ω) c) (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) tb))

theorem nonneg_of_mem_colEnds {ω : Ω} {c : ℝ} (hc : c ∈ colEnds S₁ ω) : 0 ≤ c := by
  simp only [colEnds, stairCols, Finset.mem_image] at hc
  obtain ⟨i, -, rfl⟩ := hc
  exact (S₁ i ω).coe_nonneg

/-- The column product is `1` at time `0`. -/
theorem colProd_zero {N : Ω → ℝ → ℝ → ℝ} (hN : ∀ ω x y, 0 < N ω x y) (S₂ : ι → ℝ) (tb : ℝ) (ω : Ω) :
    colProd N S₁ S₂ tb 0 ω = 1 := by
  unfold colProd
  refine Finset.prod_eq_one fun c hc => ?_
  rw [NNReal.coe_zero, min_eq_right (nonneg_of_mem_colEnds hc), min_eq_right (prevIn_nonneg _ c)]
  exact div_self (hN _ _ _).ne'

/-- Once `s` exceeds every column end, the column product is its terminal value. -/
theorem colProd_eq_colProdT (N : Ω → ℝ → ℝ → ℝ) (S₂ : ι → ℝ) (tb : ℝ) {s : ℝ≥0} {ω : Ω}
    (hs : ∀ i, S₁ i ω ≤ s) : colProd N S₁ S₂ tb s ω = colProdT N S₁ S₂ tb ω := by
  unfold colProd colProdT
  refine Finset.prod_congr rfl fun c hc => ?_
  obtain ⟨i, rfl⟩ := mem_colEnds.1 hc
  have h1 : ((S₁ i ω : ℝ)) ≤ s := NNReal.coe_le_coe.2 (hs i)
  have h2 : prevIn (colEnds S₁ ω) (S₁ i ω) ≤ s := (prevIn_le (S₁ i ω).coe_nonneg).trans h1
  rw [min_eq_left h1, min_eq_left h2]

end Product

/-! ### The column product is a martingale -/

section Mart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {ι : Type*} [Fintype ι]
  {S₁ : ι → Ω → ℝ≥0}

/-- **The stochastic half of (D12) for one frozen path of the second curve.** If the column ends `S₁ i` are stopping
times and every frozen-height process `Y_i(s) = N(s ∧ S₁ i, S₂ i ∧ t̄)` is a right-continuous martingale with values in
`[c, C]`, `c > 0`, then the closed column product of (D11) is a right-continuous martingale bounded by `(C/c)^{|ι|}`. -/
theorem martingale_colProd [IsFiniteMeasure P] (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0))
    {S₂ : ι → ℝ} (hS₂ : ∀ i, 0 ≤ S₂ i) (i₀ : ι) {N : Ω → ℝ → ℝ → ℝ} (hN : ∀ ω x y, 0 < N ω x y) (tb : ℝ)
    (hY : ∀ i, Martingale (frzHeightProc N S₁ S₂ tb i) 𝓕 P)
    (hYrc : ∀ i ω t, ContinuousWithinAt (frzHeightProc N S₁ S₂ tb i · ω) (Ici t) t) {c C : ℝ} (hc : 0 < c)
    (hYb : ∀ i s ω, c ≤ frzHeightProc N S₁ S₂ tb i s ω ∧ frzHeightProc N S₁ S₂ tb i s ω ≤ C) :
    Martingale (colProd N S₁ S₂ tb) 𝓕 P ∧ (∀ ω t, ContinuousWithinAt (colProd N S₁ S₂ tb · ω) (Ici t) t) ∧
      ∀ s ω, |colProd N S₁ S₂ tb s ω| ≤ (C / c) ^ Fintype.card ι := by
  have hτ := isStoppingTime_colTime (𝓕 := 𝓕) hS
  have hmono : ∀ k, (fun ω => (colTime S₁ k ω : WithTop ℝ≥0)) ≤ fun ω => (colTime S₁ (k + 1) ω : WithTop ℝ≥0) :=
    fun k ω => WithTop.coe_le_coe.2 (colTime_le_succ S₁ k ω)
  have h := martingale_concatProc hY hYrc hc hYb hτ hmono (measurableSet_colIdx_eq hS S₂ i₀) (Fintype.card ι)
  have e : concatProc (frzHeightProc N S₁ S₂ tb) (fun k ω => (colTime S₁ k ω : WithTop ℝ≥0)) (colIdx S₁ S₂ i₀)
      (Fintype.card ι) = colProd N S₁ S₂ tb :=
    funext fun s => funext fun ω => concatProc_colTime_eq hS₂ i₀ hN tb le_rfl s ω
  rw [e] at h
  exact h

/-- **The column product has mean one**: `∫ colProd(s) dP = 1` at every time, and `∫ colProdT dP = 1` when the column
ends are bounded by a deterministic `T` (the first of the two successive optional samplings of §A.1.3: "The positive
density `M(S₁, S₂)` … has expectation one, by optional sampling successively in the two coordinates"). -/
theorem integral_colProd_eq_one [IsProbabilityMeasure P] {N : Ω → ℝ → ℝ → ℝ} (hN : ∀ ω x y, 0 < N ω x y)
    {S₂ : ι → ℝ} {tb : ℝ} (hM : Martingale (colProd N S₁ S₂ tb) 𝓕 P) :
    (∀ s, ∫ ω, colProd N S₁ S₂ tb s ω ∂P = 1) ∧
      ∀ T : ℝ≥0, (∀ i ω, S₁ i ω ≤ T) → ∫ ω, colProdT N S₁ S₂ tb ω ∂P = 1 := by
  have h0 : ∀ s, ∫ ω, colProd N S₁ S₂ tb s ω ∂P = 1 := fun s => by
    have h := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ s) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    simp only [colProd_zero hN, integral_const, probReal_univ, smul_eq_mul, mul_one]
  refine ⟨h0, fun T hT => ?_⟩
  rw [← h0 T]
  exact integral_congr_ae (ae_of_all _ fun ω => (colProd_eq_colProdT N S₂ tb fun i => hT i ω).symm)

/-- **(D12) in the ordinary base, for one frozen path of the second curve**: `M*(s, t̄) · N(max C ∧ s, 0)/N(0, 0)` is
a right-continuous martingale, where `M*` is the patched density (D11) of the normalized
`M = N(x, y)N(0, 0)/(N(x, 0)N(0, y))` ((D6)), under the hypotheses of `martingale_colProd`. -/
theorem martingale_patch_mul_marginal [IsFiniteMeasure P]
    (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0)) {S₂ : ι → ℝ} (hS₂ : ∀ i, 0 ≤ S₂ i) (i₀ : ι)
    {N : Ω → ℝ → ℝ → ℝ} (hN : ∀ ω x y, 0 < N ω x y) (tb : ℝ)
    (hY : ∀ i, Martingale (frzHeightProc N S₁ S₂ tb i) 𝓕 P)
    (hYrc : ∀ i ω t, ContinuousWithinAt (frzHeightProc N S₁ S₂ tb i · ω) (Ici t) t) {c C : ℝ} (hc : 0 < c)
    (hYb : ∀ i s ω, c ≤ frzHeightProc N S₁ S₂ tb i s ω ∧ frzHeightProc N S₁ S₂ tb i s ω ≤ C) :
    Martingale (fun (s : ℝ≥0) ω => patch (fun i => (S₁ i ω : ℝ)) S₂
      (fun x y => N ω x y * N ω 0 0 / (N ω x 0 * N ω 0 y)) s tb *
        (N ω (min (maxIn (colEnds S₁ ω)) s) 0 / N ω 0 0)) 𝓕 P := by
  have e : (fun (s : ℝ≥0) ω => patch (fun i => (S₁ i ω : ℝ)) S₂
      (fun x y => N ω x y * N ω 0 0 / (N ω x 0 * N ω 0 y)) s tb *
        (N ω (min (maxIn (colEnds S₁ ω)) s) 0 / N ω 0 0)) = colProd N S₁ S₂ tb :=
    funext fun s => funext fun ω =>
      patch_mul_marginal (fun i => (S₁ i ω).coe_nonneg) (hN ω) s.coe_nonneg tb
  rw [e]
  exact (martingale_colProd hS hS₂ i₀ hN tb hY hYrc hc hYb).1

end Mart

end InteractingSLE.ZhanGT4
