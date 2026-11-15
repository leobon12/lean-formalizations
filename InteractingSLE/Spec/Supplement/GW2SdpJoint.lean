/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdpNear

/-!
# The near structure (N3), step D: the height forms of the joint (root) word

Packet PROVE-GW2-SDE (round 15). The root word is the counterflow's stopped word (parameter `16/κ`, angle `0`, data
word `c′`) returned through `z ↦ −1/z` with R62's offset (`GW2JointKernel.jointWordOfRec (specOffset κ) κ c′ r`). Its
heights, by the stopped-piece profile (`fn_stopWord_left/right` at `16/κ`):

* **`jointWord_left_form`**: left of `0` every height is `−λ′(1 + S) + πχ` with `S` the counterflow's flank (`0`) or a
  right prefix sum of the counterflow word;
* **`jointWord_right_form`**: right of `0` every height is `λ′(1 + S) − πχ` with `S` the flank or a left prefix sum;
* **`nearStruct_stageWord`** (assembly, even histories): a stage word whose root word has these two forms and the two
  far heights, whose junctions are strictly off the tip, and whose first piece's junctions are both beyond `3√s`, has
  ROOT2's upper or lower structure at the near scale `s` (the junction span never shrinks, so one junction stays
  beyond `3√s`).

With every prefix sum `> −2` (Lemma GW0 for the complete counterflow, `GW0.counterflow_admissible`), these are
exactly the forms of ROOT2's structure (`NearStructBot.left`, `NearStructTop.right`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Sdp

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSysField GW2JointKernel GW2TipSystem.RootH10

/-- The right labels `≤ y` of a flow-line word form a prefix. -/
theorem exists_prefix_right (b : ℝ → ℝ) (J : Finset ℝ) {y : ℝ} (hy : 0 ≤ y) :
    ∃ i₀ : Fin (flowLineNR b J 0), (univ.filter fun j => flowLineXR b J 0 j ≤ y) = univ.filter fun j => j ≤ i₀ := by
  classical
  have hne : (univ.filter fun j : Fin (flowLineNR b J 0) => flowLineXR b J 0 j ≤ y).Nonempty :=
    ⟨⟨0, Supp8.GB6.zero_lt_flowLineNR _ _⟩, mem_filter.2 ⟨mem_univ _, hy⟩⟩
  refine ⟨(univ.filter fun j => flowLineXR b J 0 j ≤ y).max' hne, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact Finset.le_max' _ j (mem_filter.2 ⟨mem_univ _, h⟩)
  · intro h
    have hm := (mem_filter.1 (Finset.max'_mem _ hne)).2
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact hm
    · exact (GW0.flowLineXR_lt b J 0 hlt).le.trans hm

/-- The left labels right of `y < 0` of a flow-line word form a prefix. -/
theorem exists_prefix_left (b : ℝ → ℝ) (J : Finset ℝ) {y : ℝ} (hy : y < 0) :
    ∃ i₀ : Fin (flowLineNL b J 0), (univ.filter fun i => y < flowLineXL b J 0 i) = univ.filter fun i => i ≤ i₀ := by
  classical
  have hne : (univ.filter fun i : Fin (flowLineNL b J 0) => y < flowLineXL b J 0 i).Nonempty :=
    ⟨⟨0, Supp8.GB6.zero_lt_flowLineNL _ _⟩, mem_filter.2 ⟨mem_univ _, hy⟩⟩
  refine ⟨(univ.filter fun i => y < flowLineXL b J 0 i).max' hne, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact Finset.le_max' _ i (mem_filter.2 ⟨mem_univ _, h⟩)
  · intro h
    have hm := (mem_filter.1 (Finset.max'_mem _ hne)).2
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact hm
    · exact hm.trans (GW0.flowLineXL_lt b J 0 hlt)

variable {κ : ℝ}

/-- **The joint word left of `0`: `−λ′(1 + S) + πχ`** with `S > −2` (the flank or a right prefix sum). -/
theorem jointWord_left_form (hκ : 0 < κ) (c' : BoundaryWord)
    (hadm : ∀ i : Fin (flowLineNR c'.fn c'.jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0 l)
    (r : RecData) {y : ℝ} (hy : y < 0) (hyJ : y ∉ (jointWordOfRec (specOffset κ) κ c' r).jumps) :
    ∃ S : ℝ, -2 < S ∧
      (jointWordOfRec (specOffset κ) κ c' r).fn y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ := by
  classical
  have hk : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hgs := isSorted_stopWord (16 / κ) (c', 0, r)
  have hb := c'.isPiecewiseConstantBoundaryData
  unfold jointWordOfRec at hyJ ⊢
  rw [fn_retWord hgs _ _ hyJ]
  have hz0 : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
  have hzJ : -y⁻¹ ∉ (stopWord (16 / κ) (c', 0, r)).jumps := fun h => hyJ (GW2Wm.neg_inv_mem_jumps_retWord hgs _ _ h)
  have hconst : retA κ + specOffset κ + retL κ * -(2 * Real.pi) = Real.pi * chiC κ := by
    rw [retA_add_specOffset hκ]
    unfold retL
    rw [Sec4.chiC_sixteen_div hκ]
    ring
  -- the counterflow's stopped word at `z = −1/y > 0`: its right flank or an original right height
  have hstop : ∃ S : ℝ, -2 < S ∧ (stopWord (16 / κ) (c', 0, r)).fn (-y⁻¹) = sleLambda (16 / κ) * (1 + S) := by
    have horig : ∀ z, 0 < z → z ∉ (stopWord (16 / κ) (c', 0, r)).jumps →
        markPos (rdrv r) (rtime r) 0 < z →
        ∃ S : ℝ, -2 < S ∧ (stopWord (16 / κ) (c', 0, r)).fn z = sleLambda (16 / κ) * (1 + S) := by
      intro z hz hzJ' hmz
      obtain ⟨y', hy'0, hy'J, hfz⟩ := (fn_stopWord_right hk c' 0 r le_rfl hz hzJ').2 hmz
      obtain ⟨i₀, hi₀⟩ := exists_prefix_right c'.fn c'.jumps hy'0.le
      refine ⟨_, hadm i₀, ?_⟩
      rw [hfz, ← Sec4.forceBoundaryData_flowLine hk hb hy'0.ne' hy'J, Sec4.forceBoundaryData_of_nonneg _ _ _ _ hy'0.le,
        hi₀]
    rcases lt_trichotomy (-y⁻¹) (markPos (rdrv r) (rtime r) 0) with hlt | heq | hgt
    · rcases (fn_stopWord_right hk c' 0 r le_rfl hz0 hzJ).1 hlt with hs | ⟨y', h1, h2, -⟩
      · exact ⟨0, by norm_num, by rw [hs]; ring⟩
      · exact absurd (h1.trans h2) (lt_irrefl _)
    · obtain ⟨z, hz, hzJ', hzv⟩ := exists_near_right (stopWord (16 / κ) (c', 0, r)) hzJ
      obtain ⟨S, hS, hfz⟩ := horig z (hz0.trans hz) hzJ' (heq ▸ hz)
      exact ⟨S, hS, hzv ▸ hfz⟩
    · exact horig _ hz0 hzJ hgt
  obtain ⟨S, hS, hfz⟩ := hstop
  refine ⟨S, hS, ?_⟩
  unfold returnData liftBoundary
  rw [hfz, ite_eq_left_of_eq_true _ _ (eq_true hy)]
  linarith

/-- **The joint word right of `0`: `λ′(1 + S) − πχ`** with `S > −2` (the flank or a left prefix sum). -/
theorem jointWord_right_form (hκ : 0 < κ) (c' : BoundaryWord)
    (hadm : ∀ i : Fin (flowLineNL c'.fn c'.jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0 l)
    (r : RecData) {y : ℝ} (hy : 0 < y) (hyJ : y ∉ (jointWordOfRec (specOffset κ) κ c' r).jumps) :
    ∃ S : ℝ, -2 < S ∧
      (jointWordOfRec (specOffset κ) κ c' r).fn y = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ := by
  classical
  have hk : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hgs := isSorted_stopWord (16 / κ) (c', 0, r)
  have hb := c'.isPiecewiseConstantBoundaryData
  unfold jointWordOfRec at hyJ ⊢
  rw [fn_retWord hgs _ _ hyJ]
  have hz0 : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy)
  have hzJ : -y⁻¹ ∉ (stopWord (16 / κ) (c', 0, r)).jumps := fun h => hyJ (GW2Wm.neg_inv_mem_jumps_retWord hgs _ _ h)
  have hconst : retA κ + specOffset κ + retL κ * 0 = -(Real.pi * chiC κ) := by
    rw [retA_add_specOffset hκ]
    ring
  have hstop : ∃ S : ℝ, -2 < S ∧ (stopWord (16 / κ) (c', 0, r)).fn (-y⁻¹) = -sleLambda (16 / κ) * (1 + S) := by
    have horig : ∀ z, z < 0 → z ∉ (stopWord (16 / κ) (c', 0, r)).jumps →
        z < markPosL (rdrv r) (rtime r) 0 →
        ∃ S : ℝ, -2 < S ∧ (stopWord (16 / κ) (c', 0, r)).fn z = -sleLambda (16 / κ) * (1 + S) := by
      intro z hz hzJ' hmz
      obtain ⟨y', hy'0, hy'J, hfz⟩ := (fn_stopWord_left hk c' 0 r le_rfl hz hzJ').2 hmz
      obtain ⟨i₀, hi₀⟩ := exists_prefix_left c'.fn c'.jumps hy'0
      refine ⟨_, hadm i₀, ?_⟩
      rw [hfz, ← Sec4.forceBoundaryData_flowLine hk hb hy'0.ne hy'J, Sec4.forceBoundaryData_of_neg _ _ _ _ hy'0, hi₀]
    rcases lt_trichotomy (-y⁻¹) (markPosL (rdrv r) (rtime r) 0) with hlt | heq | hgt
    · exact horig _ hz0 hzJ hlt
    · obtain ⟨z, hz, hzJ', hzv⟩ := exists_near_left (stopWord (16 / κ) (c', 0, r)) hzJ
      obtain ⟨S, hS, hfz⟩ := horig z (hz.trans hz0) hzJ' (heq ▸ hz)
      exact ⟨S, hS, hzv ▸ hfz⟩
    · rcases (fn_stopWord_left hk c' 0 r le_rfl hz0 hzJ).1 hgt with hs | ⟨y', h1, h2, -⟩
      · exact ⟨0, by norm_num, by rw [hs]; ring⟩
      · exact absurd (h1.trans h2) (lt_irrefl _)
  obtain ⟨S, hS, hfz⟩ := hstop
  refine ⟨S, hS, ?_⟩
  unfold returnData liftBoundary
  rw [hfz, ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hy.le))]
  linarith

section Assembly

universe v

variable {S : Type v}

/-- **The near structure of a stage word** (even histories): side invariant, junction span, root-word forms and far
heights. -/
theorem nearStruct_stageWord (hκ : 0 < κ) (hκ4 : κ < 4) (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (n : ℕ) (x : GW2JDetR5.Past S (n + 1)) {s : ℝ≥0}
    (hs : s ≠ 0)
    (hformL : ∀ h ∈ rootHeightsL (W₀ (GW2Wm.pastRoot (n + 1) x)), h ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hformR : ∀ h ∈ rootHeightsR (W₀ (GW2Wm.pastRoot (n + 1) x)), h ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hfarL : GW2Wm.FarL (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) (-sleLambda (16 / κ) + Real.pi * chiC κ))
    (hfarR : GW2Wm.FarR (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) (sleLambda (16 / κ) - Real.pi * chiC κ))
    (hjL : junctionL (n + 1) x < 0) (hjR : 0 < junctionR (n + 1) x)
    (hfirst : 3 * Real.sqrt s ≤ -junctionL 1 (pastFirst n x) ∧ 3 * Real.sqrt s ≤ junctionR 1 (pastFirst n x)) :
    GW2Sdy.NearStruct κ s false (GW2JDetR5.stageWord (κ := κ) W₀ θ (n + 1) x) := by
  have hinv := sideInv_stageWord hκ W₀ θ hθ (n + 1) x
  have hspan := junction_span n x
  have hfL := GW2Wm.farL_flowLine hκ hfarL
  have hfR := GW2Wm.farR_flowLine hκ hfarR
  by_cases hR3 : 3 * Real.sqrt s ≤ junctionR (n + 1) x
  · exact Or.inr (nearStructBot_of_sideInv hκ hκ4 hs hinv hR3 hjL hformL hfL hfR)
  · refine Or.inl (nearStructTop_of_sideInv hκ hκ4 hs hinv ?_ hjR hformR hfL hfR)
    linarith [hfirst.1, hfirst.2, not_le.1 hR3]

end Assembly

end InteractingSLE.Theorem14.GW2Sdp
