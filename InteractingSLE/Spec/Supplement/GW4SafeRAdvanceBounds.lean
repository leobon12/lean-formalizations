/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanWire

/-!
# GW4: cumulative upper bounds from the incoming boundary heights

GW3.1's left heights are at least `Λ` and its right heights at most `-Λ`.
After the compatible inversion these give every upper cumulative bound in
GW3.2, including the two seed bounds needed by Aux. 122. The geometric proof of
the actual incoming-height inequalities is not supplied by defining them here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Supp8.Q3Stop Sec7.StripSysField GW3Word

/-- The first upper partial-sum bound is exactly the seed upper bound. -/
theorem seed_le_of_partialSums {n : ℕ} {a : ℝ} {ρ : Fin (n + 1) → ℝ}
    (hs : ∀ i, (∑ j ∈ univ.filter (fun j => j ≤ i), ρ j) ≤ a) : ρ 0 ≤ a := by
  simpa only [Fin.le_zero_iff, Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.sum_singleton] using hs 0

/-- Upper left cumulative weights from a lower bound on the boundary heights. -/
theorem sum_flowLineRhoL_le_of_height {k a : ℝ} (hk : 0 < k) {b : ℝ → ℝ}
    {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ y, y < 0 → y ∉ J → -(a + 1) * sleLambda k ≤ b y)
    (i : Fin (flowLineNL b J 0)) :
    (∑ j ∈ univ.filter (fun j => j ≤ i), flowLineRhoL k b J 0 0 j) ≤ a := by
  rw [filter_le_eq_filter_le_flowLineXL]
  obtain ⟨y, -, hy, hyJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoL_eq hk hb
    (lo := flowLineXL b J 0 i - 1) (by linarith) (flowLineXL_nonpos b J i)
  rw [hS, Sec4.cumWeightLeft]
  have h := hL y (lt_of_lt_of_le hy (flowLineXL_nonpos b J i)) hyJ
  have hdiv : -b y / sleLambda k ≤ a + 1 :=
    (div_le_iff₀ (Sec4.sleLambda_pos hk)).2 (by linarith only [h])
  linarith only [hdiv]

/-- Upper right cumulative weights from an upper bound on the boundary heights. -/
theorem sum_flowLineRhoR_le_of_height {k a : ℝ} (hk : 0 < k) {b : ℝ → ℝ}
    {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hR : ∀ y, 0 < y → y ∉ J → b y ≤ (a + 1) * sleLambda k)
    (i : Fin (flowLineNR b J 0)) :
    (∑ j ∈ univ.filter (fun j => j ≤ i), flowLineRhoR k b J 0 0 j) ≤ a := by
  rw [filter_le_eq_filter_flowLineXR_le]
  obtain ⟨y, hy, hyJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoR_eq hk hb
    (flowLineXR_nonneg b J i)
  rw [hS, Sec4.cumWeightRight]
  have h := hR y (lt_of_le_of_lt (flowLineXR_nonneg b J i) hy) hyJ
  have hdiv : b y / sleLambda k ≤ a + 1 := (div_le_iff₀ (Sec4.sleLambda_pos hk)).2 h
  linarith only [hdiv]

/-- The height inequalities of GW3.1, off the actual finite exceptional set.
Proving these for a selected component still requires the low-connector and
incident-flow-germ argument. -/
def IncomingHeightBounds (κ : ℝ) (bC : ℝ → ℝ) (JC : Finset ℝ) : Prop :=
  (∀ x, x < 0 → x ∉ JC → sleLambda (16 / κ) ≤ bC x) ∧
    ∀ x, 0 < x → x ∉ JC → bC x ≤ -sleLambda (16 / κ)

/-- The compatible inversion converts the incoming heights to the two upper
height bounds at parameter `16/κ`. Every original and connector-junction mark
is retained through the exact equality of exceptional sets. -/
theorem counterflow_height_bounds_of_incoming {κ : ℝ} (hκ : 0 < κ)
    {bC : ℝ → ℝ} {JC : Finset ℝ} (hh : IncomingHeightBounds κ bC JC)
    {c₀ : BoundaryWord} (hJ : c₀.jumps = counterflowJumps JC)
    (hc : ∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) :
    (∀ y, y < 0 → y ∉ c₀.jumps →
      -((16 / κ / 2 - 4) + 1) * sleLambda (16 / κ) ≤ c₀.fn y) ∧
    ∀ y, 0 < y → y ∉ c₀.jumps →
      c₀.fn y ≤ ((16 / κ / 2 - 4) + 1) * sleLambda (16 / κ) := by
  have hπ : Real.pi * chiC κ = (16 / κ / 2 - 2) * sleLambda (16 / κ) := by
    have h := Sec4.two_pi_mul_chiC_eq_sixteen_div_sub_mul hκ
    linarith only [h]
  constructor
  · intro y hy hyJ
    rw [hc y hyJ, counterflowData_of_neg hκ _ hy]
    have hxJ := negInv_notMem_of_notMem_returnExcept (hJ ▸ hyJ)
    have h := hh.2 (-y⁻¹) (neg_pos.2 (inv_lt_zero.2 hy)) hxJ
    nlinarith only [h, hπ]
  · intro y hy hyJ
    rw [hc y hyJ, counterflowData_of_pos hκ _ hy]
    have hxJ := negInv_notMem_of_notMem_returnExcept (hJ ▸ hyJ)
    have h := hh.1 (-y⁻¹) (neg_neg_of_pos (inv_pos.2 hy)) hxJ
    nlinarith only [h, hπ]

/-- All cumulative upper bounds of GW3.2 from the incoming height bounds. -/
theorem word_upper_bounds_of_incoming {κ : ℝ} (hκ : 0 < κ)
    {bC : ℝ → ℝ} {JC : Finset ℝ} (hh : IncomingHeightBounds κ bC JC)
    {c₀ : BoundaryWord} (hJ : c₀.jumps = counterflowJumps JC)
    (hc : ∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) :
    (∀ i : Fin (flowLineNL c₀.fn c₀.jumps 0),
      (∑ j ∈ univ.filter (fun j => j ≤ i), flowLineRhoL (16 / κ) c₀.fn c₀.jumps 0 0 j)
        ≤ 16 / κ / 2 - 4) ∧
    ∀ i : Fin (flowLineNR c₀.fn c₀.jumps 0),
      (∑ j ∈ univ.filter (fun j => j ≤ i), flowLineRhoR (16 / κ) c₀.fn c₀.jumps 0 0 j)
        ≤ 16 / κ / 2 - 4 := by
  have h := counterflow_height_bounds_of_incoming hκ hh hJ hc
  have hk : 0 < 16 / κ := div_pos (by norm_num) hκ
  exact ⟨sum_flowLineRhoL_le_of_height hk c₀.isPiecewiseConstantBoundaryData h.1,
    sum_flowLineRhoR_le_of_height hk c₀.isPiecewiseConstantBoundaryData h.2⟩

/-- In particular the exact typed seed weights satisfy Aux. 122's GW4 bounds. -/
theorem typed_seed_upper_of_incoming {κ : ℝ} (hκ : 0 < κ)
    {bC : ℝ → ℝ} {JC : Finset ℝ} (hh : IncomingHeightBounds κ bC JC)
    {c₀ : BoundaryWord} (hJ : c₀.jumps = counterflowJumps JC)
    (hc : ∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) :
    typedRhoL (wordType (16 / κ) c₀) (componentSeedL (16 / κ) c₀) ≤ 16 / κ / 2 - 4 ∧
      typedRhoR (wordType (16 / κ) c₀) (componentSeedR (16 / κ) c₀) ≤ 16 / κ / 2 - 4 := by
  obtain ⟨hL, hR⟩ := word_upper_bounds_of_incoming hκ hh hJ hc
  have htL : ∀ i, typedRhoL (wordType (16 / κ) c₀) i =
      flowLineRhoL (16 / κ) c₀.fn c₀.jumps 0 0 i := fun i => padFL_snd_fst_fin _ _ _ _ i
  have htR : ∀ i, typedRhoR (wordType (16 / κ) c₀) i =
      flowLineRhoR (16 / κ) c₀.fn c₀.jumps 0 0 i := fun i => padFL_snd_snd_fin _ _ _ _ i
  constructor
  · rw [htL]
    exact seed_le_of_partialSums hL
  · rw [htR]
    exact seed_le_of_partialSums hR

end InteractingSLE.Theorem14.GW4Fix
