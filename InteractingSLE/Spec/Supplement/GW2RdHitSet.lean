/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2BdryVisit
import InteractingSLE.Spec.Supplement.S9Propagation
import InteractingSLE.Spec.Supplement.GW0
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Sec4.PartialSums
import InteractingSLE.Spec.Sec5.Prop59NodeTreeWord

/-!
# GW2's lifetime as a hitting time, part 2: the hitting set, avoided before the lifetime

Packet PROVE-GW2-RELDET (`FlowLifetimeHitStatement`). The closed set is

  `hitSet κ b J θ = closure {y real : 0 < y, Σ_{x^R_i ≤ y} ρ^R_i ≤ −2  or  y < 0, Σ_{y ≤ x^L_i} ρ^L_i ≤ −2}`

for the angle-`θ` flow-line word from `0` (`hitBadR`, `hitBadL`): the real points whose prefix of marks, on the side
facing the seed, has total weight `≤ −2`. This file proves that **almost surely the flow line avoids it strictly
before its lifetime** (`ae_trace_notMem_hitSet`), from three landed facts about flow lines:

* a real visit before the lifetime has an admissible incident height (`Restart.FCPlumb.ae_live_real_incident_bounds`,
  i.e. the continuation-threshold exclusion off the jumps);
* the jumps are never visited at positive times before the lifetime (`RLC.jumpVisitStatement`, Lemma G12);
* at positive lifetime both seed weights exceed `−2` (`Supp9.ae_seedWeights_of_isFlowLine`).

The prefix weights convert to heights by `Sec4.cumWeightRight_forceBoundaryData` and `Sec4.forceBoundaryData_flowLine`
(`sum_filter_flowLineXR_le_theta`, `sum_filter_le_flowLineXL_theta`); the closure adds no point off the seed and the
jumps since the prefix sets are locally constant there (`filter_le_eq_of_near`, `filter_ge_eq_of_near`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open PiecewiseConstantBoundaryData (leftLim rightLim)

/-! ### The hitting set -/

/-- **Right bad points**: positive `y` whose right prefix weight (over the marks `≤ y`) of the angle-`θ` flow-line
word from `0` is `≤ −2`. -/
def hitBadR (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) : Set ℝ :=
  {y | 0 < y ∧ ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ y), flowLineRhoR κ b J 0 θ i ≤ -2}

/-- **Left bad points**: negative `y` whose left prefix weight (over the marks `≥ y`) of the angle-`θ` flow-line word
from `0` is `≤ −2`. -/
def hitBadL (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) : Set ℝ :=
  {y | y < 0 ∧ ∑ i ∈ univ.filter (fun i => y ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i ≤ -2}

/-- **GW2's hitting set**: the closure of the bad real points. -/
def hitSet (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) : Set ℂ :=
  closure ((fun y : ℝ => (y : ℂ)) '' (hitBadR κ b J θ ∪ hitBadL κ b J θ))

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ}

theorem isClosed_hitSet : IsClosed (hitSet κ b J θ) := isClosed_closure

theorem ofReal_mem_hitSet {y : ℝ} (hy : y ∈ hitBadR κ b J θ ∪ hitBadL κ b J θ) :
    (y : ℂ) ∈ hitSet κ b J θ :=
  subset_closure ⟨y, hy, rfl⟩

/-- A point of the closure of a set of real points is a real point of the closure. -/
theorem exists_real_of_mem_closure_ofReal {S : Set ℝ} {z : ℂ}
    (hz : z ∈ closure ((fun y : ℝ => (y : ℂ)) '' S)) : ∃ y ∈ closure S, z = y := by
  have him : z.im = 0 := by
    have hcl : IsClosed {w : ℂ | w.im = 0} := isClosed_eq Complex.continuous_im continuous_const
    have hsub : (fun y : ℝ => (y : ℂ)) '' S ⊆ {w : ℂ | w.im = 0} := by
      rintro _ ⟨y, -, rfl⟩
      simp
    exact closure_minimal hsub hcl hz
  have hre : z.re ∈ closure S := by
    have h1 := image_closure_subset_closure_image Complex.continuous_re (mem_image_of_mem Complex.re hz)
    rwa [image_image, show (fun y : ℝ => ((y : ℂ)).re) = id from funext fun y => Complex.ofReal_re y,
      image_id] at h1
  exact ⟨z.re, hre, Complex.ext (by simp) (by simp [him])⟩

/-! ### Local constancy of prefix sets -/

/-- Finitely many reals stay a positive distance from a given point, except those equal to it. -/
theorem exists_pos_le_abs_sub {n : ℕ} (x : Fin n → ℝ) (y : ℝ) :
    ∃ δ > (0 : ℝ), ∀ i, x i ≠ y → δ ≤ |x i - y| := by
  have hcl : IsClosed (range x \ {y}) := ((finite_range x).subset fun z hz => hz.1).isClosed
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl y (fun h => h.2 rfl)
  refine ⟨δ, hδ, fun i hi => ?_⟩
  by_contra hlt
  exact hball (by rw [Metric.mem_ball, Real.dist_eq]; exact not_le.1 hlt) ⟨⟨i, rfl⟩, hi⟩

/-- The set of marks `≤ y'` is the set of marks `≤ y` for `y'` near `y` (on the right of `y`, or anywhere if `y` is
not a mark). -/
theorem filter_le_eq_of_near {n : ℕ} {x : Fin n → ℝ} {y y' δ : ℝ} (hδ : ∀ i, x i ≠ y → δ ≤ |x i - y|)
    (hy' : |y' - y| < δ) (hside : y ≤ y' ∨ ∀ i, x i ≠ y) :
    univ.filter (fun i => x i ≤ y') = univ.filter (fun i => x i ≤ y) := by
  have h1 := abs_lt.1 hy'
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra hlt
    have hlt' : y < x i := not_le.1 hlt
    have := hδ i hlt'.ne'
    rw [abs_of_pos (sub_pos.2 hlt')] at this
    linarith [h1.2]
  · intro hi
    rcases hside with hle | hne
    · exact hi.trans hle
    · have hlt : x i < y := lt_of_le_of_ne hi (hne i)
      have := hδ i (hne i)
      rw [abs_of_neg (sub_neg.2 hlt)] at this
      linarith [h1.1]

/-- The set of marks `≥ y'` is the set of marks `≥ y` for `y'` near `y` (on the left of `y`, or anywhere if `y` is
not a mark). -/
theorem filter_ge_eq_of_near {n : ℕ} {x : Fin n → ℝ} {y y' δ : ℝ} (hδ : ∀ i, x i ≠ y → δ ≤ |x i - y|)
    (hy' : |y' - y| < δ) (hside : y' ≤ y ∨ ∀ i, x i ≠ y) :
    univ.filter (fun i => y' ≤ x i) = univ.filter (fun i => y ≤ x i) := by
  have h1 := abs_lt.1 hy'
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    by_contra hlt
    have hlt' : x i < y := not_le.1 hlt
    have := hδ i hlt'.ne
    rw [abs_of_neg (sub_neg.2 hlt')] at this
    linarith [h1.1]
  · intro hi
    rcases hside with hle | hne
    · exact hle.trans hi
    · have hlt : y < x i := lt_of_le_of_ne hi (Ne.symm (hne i))
      have := hδ i (hne i)
      rw [abs_of_pos (sub_pos.2 hlt)] at this
      linarith [h1.2]

/-! ### The marks and the prefix weights of the flow-line word -/

/-- The right marks of the flow-line word from `0` are the seed or jump candidates. -/
theorem flowLineXR_eq_zero_or_mem (b : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNR b J 0)) :
    flowLineXR b J 0 i = 0 ∨ flowLineXR b J 0 i ∈ J := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact Or.inl rfl
  · right
    show ((PiecewiseConstantBoundaryData.jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl j - 0 ∈ J
    rw [sub_zero]
    have h := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet b J).filter (0 < ·)) rfl j
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1

/-- The left marks of the flow-line word from `0` are the seed or jump candidates. -/
theorem flowLineXL_eq_zero_or_mem (b : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL b J 0)) :
    flowLineXL b J 0 i = 0 ∨ flowLineXL b J 0 i ∈ J := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact Or.inl rfl
  · right
    show ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev j) - 0 ∈ J
    rw [sub_zero]
    have h := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < 0)) rfl
      (Fin.rev j)
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1

/-- **Right prefix weight at a point off the jumps**: `Σ_{x^R_i ≤ y} ρ^R_i = (b(y) + θχ)/λ − 1` for `y > 0`. -/
theorem sum_filter_flowLineXR_le_theta (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) {y : ℝ}
    (hy : 0 < y) (hyJ : y ∉ J) :
    ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ y), flowLineRhoR κ b J 0 θ i =
      Sec4.cumWeightRight κ (b y + θ * chiC κ) := by
  have h0 := Sec4.cumWeightRight_forceBoundaryData hκ (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0)
    (flowLineXL b J 0) (flowLineXR b J 0) hy.le
  rw [Sec4.forceBoundaryData_flowLine hκ hb hy.ne' hyJ, Sec4.cumWeightRight] at h0
  have hsub := Sec5.Prop59NodeTree.flowLineRhoR_sub κ b J 0 θ 0
  have hmem : (⟨0, by unfold flowLineNR; omega⟩ : Fin (flowLineNR b J 0)) ∈
      univ.filter (fun i => flowLineXR b J 0 i ≤ y) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hy.le⟩
  have hdiff : ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ y), flowLineRhoR κ b J 0 θ i -
      ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ y), flowLineRhoR κ b J 0 0 i =
      (θ - 0) * (chiC κ / sleLambda κ) := by
    rw [← sum_sub_distrib, sum_congr rfl fun i _ => hsub i, sum_eq_single_of_mem _ hmem]
    · simp
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext h0)
      simp only [hj', ↓reduceIte]
  rw [Sec4.cumWeightRight]
  have e : (b y + θ * chiC κ) / sleLambda κ - 1 = (b y / sleLambda κ - 1) + (θ - 0) * (chiC κ / sleLambda κ) := by
    ring
  rw [e]
  linarith

/-- **Left prefix weight at a point off the jumps**: `Σ_{y ≤ x^L_i} ρ^L_i = −(b(y) + θχ)/λ − 1` for `y < 0`. -/
theorem sum_filter_le_flowLineXL_theta (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) {y : ℝ}
    (hy : y < 0) (hyJ : y ∉ J) :
    ∑ i ∈ univ.filter (fun i => y ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i =
      Sec4.cumWeightLeft κ (b y + θ * chiC κ) := by
  have hF : univ.filter (fun i => y ≤ flowLineXL b J 0 i) = univ.filter (fun i => y < flowLineXL b J 0 i) := by
    refine filter_congr fun i _ => ⟨fun h => lt_of_le_of_ne h fun he => ?_, le_of_lt⟩
    rcases flowLineXL_eq_zero_or_mem b J i with h0 | h0
    · rw [h0] at he; exact hy.ne he
    · rw [← he] at h0; exact hyJ h0
  rw [hF]
  have h0 := Sec4.cumWeightLeft_forceBoundaryData hκ (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0)
    (flowLineXL b J 0) (flowLineXR b J 0) hy
  rw [Sec4.forceBoundaryData_flowLine hκ hb hy.ne hyJ, Sec4.cumWeightLeft] at h0
  have hsub := Sec5.Prop59NodeTree.flowLineRhoL_sub κ b J 0 θ 0
  have hmem : (⟨0, by unfold flowLineNL; omega⟩ : Fin (flowLineNL b J 0)) ∈
      univ.filter (fun i => y < flowLineXL b J 0 i) := Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
  have hdiff : ∑ i ∈ univ.filter (fun i => y < flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i -
      ∑ i ∈ univ.filter (fun i => y < flowLineXL b J 0 i), flowLineRhoL κ b J 0 0 i =
      (0 - θ) * (chiC κ / sleLambda κ) := by
    rw [← sum_sub_distrib, sum_congr rfl fun i _ => hsub i, sum_eq_single_of_mem _ hmem]
    · simp
    · intro j _ hj
      have hj' : (j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext h0)
      simp only [hj', ↓reduceIte]
  rw [Sec4.cumWeightLeft]
  have e : -(b y + θ * chiC κ) / sleLambda κ - 1 =
      (-b y / sleLambda κ - 1) + (0 - θ) * (chiC κ / sleLambda κ) := by
    ring
  rw [e]
  linarith

/-- The right prefix at the seed is the seed mark alone. -/
theorem sum_filter_flowLineXR_le_zero (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) :
    ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ 0), flowLineRhoR κ b J 0 θ i =
      Sec4.cumWeightRight κ (rightLim b 0 + θ * chiC κ) := by
  have hpos : 0 < flowLineNR b J 0 := by unfold flowLineNR; omega
  have hmem : (⟨0, hpos⟩ : Fin (flowLineNR b J 0)) ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ 0) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, le_of_eq rfl⟩
  rw [sum_eq_single_of_mem _ hmem]
  · rfl
  · intro j hj hj0
    exfalso
    have hlt : (⟨0, hpos⟩ : Fin (flowLineNR b J 0)) < j :=
      Fin.lt_def.2 (Nat.pos_of_ne_zero fun h => hj0 (Fin.ext h))
    have h1 := Theorem14.GW0.flowLineXR_lt b J 0 hlt
    have h2 := (Finset.mem_filter.1 hj).2
    have h3 : flowLineXR b J 0 ⟨0, hpos⟩ = 0 := rfl
    linarith

/-- The left prefix at the seed is the seed mark alone. -/
theorem sum_filter_zero_le_flowLineXL (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) :
    ∑ i ∈ univ.filter (fun i => 0 ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i =
      Sec4.cumWeightLeft κ (leftLim b 0 + θ * chiC κ) := by
  have hpos : 0 < flowLineNL b J 0 := by unfold flowLineNL; omega
  have hmem : (⟨0, hpos⟩ : Fin (flowLineNL b J 0)) ∈ univ.filter (fun i => 0 ≤ flowLineXL b J 0 i) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, le_of_eq rfl⟩
  rw [sum_eq_single_of_mem _ hmem]
  · rfl
  · intro j hj hj0
    exfalso
    have hlt : (⟨0, hpos⟩ : Fin (flowLineNL b J 0)) < j :=
      Fin.lt_def.2 (Nat.pos_of_ne_zero fun h => hj0 (Fin.ext h))
    have h1 := Theorem14.GW0.flowLineXL_lt b J 0 hlt
    have h2 := (Finset.mem_filter.1 hj).2
    have h3 : flowLineXL b J 0 ⟨0, hpos⟩ = 0 := rfl
    linarith

/-! ### The closure adds no point off the seed and the jumps -/

/-- A good positive point off the jumps is not in the closure of the bad set. -/
theorem notMem_closure_of_pos {y : ℝ} (hy : 0 < y) (hyJ : y ∉ J) (hbad : y ∉ hitBadR κ b J θ) :
    y ∉ closure (hitBadR κ b J θ ∪ hitBadL κ b J θ) := by
  obtain ⟨δ, hδ, hδx⟩ := exists_pos_le_abs_sub (flowLineXR b J 0) y
  have hne : ∀ i, flowLineXR b J 0 i ≠ y := fun i he => by
    rcases flowLineXR_eq_zero_or_mem b J i with h | h
    · rw [h] at he; exact hy.ne he
    · rw [he] at h; exact hyJ h
  intro hcl
  obtain ⟨y', hy'S, hdist⟩ := Metric.mem_closure_iff.1 hcl (min δ y) (lt_min hδ hy)
  have hd : |y' - y| < min δ y := by rw [abs_sub_comm, ← Real.dist_eq]; exact hdist
  have hd1 : |y' - y| < δ := hd.trans_le (min_le_left _ _)
  have hd2 := abs_lt.1 (hd.trans_le (min_le_right _ _))
  have hy'pos : 0 < y' := by linarith [hd2.1]
  rcases hy'S with hR | hL
  · obtain ⟨-, hs⟩ := hR
    rw [filter_le_eq_of_near hδx hd1 (Or.inr hne)] at hs
    exact hbad ⟨hy, hs⟩
  · obtain ⟨hneg, -⟩ := hL
    linarith

/-- A good negative point off the jumps is not in the closure of the bad set. -/
theorem notMem_closure_of_neg {y : ℝ} (hy : y < 0) (hyJ : y ∉ J) (hbad : y ∉ hitBadL κ b J θ) :
    y ∉ closure (hitBadR κ b J θ ∪ hitBadL κ b J θ) := by
  obtain ⟨δ, hδ, hδx⟩ := exists_pos_le_abs_sub (flowLineXL b J 0) y
  have hne : ∀ i, flowLineXL b J 0 i ≠ y := fun i he => by
    rcases flowLineXL_eq_zero_or_mem b J i with h | h
    · rw [h] at he; exact hy.ne' he
    · rw [he] at h; exact hyJ h
  intro hcl
  obtain ⟨y', hy'S, hdist⟩ := Metric.mem_closure_iff.1 hcl (min δ (-y)) (lt_min hδ (neg_pos.2 hy))
  have hd : |y' - y| < min δ (-y) := by rw [abs_sub_comm, ← Real.dist_eq]; exact hdist
  have hd1 : |y' - y| < δ := hd.trans_le (min_le_left _ _)
  have hd2 := abs_lt.1 (hd.trans_le (min_le_right _ _))
  have hy'neg : y' < 0 := by linarith [hd2.2]
  rcases hy'S with hR | hL
  · obtain ⟨hpos, -⟩ := hR
    linarith
  · obtain ⟨-, hs⟩ := hL
    rw [filter_ge_eq_of_near hδx hd1 (Or.inr hne)] at hs
    exact hbad ⟨hy, hs⟩

/-- With both seed prefix weights above `−2`, the seed is not in the closure of the bad set. -/
theorem zero_notMem_closure
    (hR : -2 < ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ 0), flowLineRhoR κ b J 0 θ i)
    (hL : -2 < ∑ i ∈ univ.filter (fun i => 0 ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i) :
    (0 : ℝ) ∉ closure (hitBadR κ b J θ ∪ hitBadL κ b J θ) := by
  obtain ⟨δR, hδR, hR'⟩ := exists_pos_le_abs_sub (flowLineXR b J 0) 0
  obtain ⟨δL, hδL, hL'⟩ := exists_pos_le_abs_sub (flowLineXL b J 0) 0
  intro hcl
  obtain ⟨y', hy'S, hdist⟩ := Metric.mem_closure_iff.1 hcl (min δR δL) (lt_min hδR hδL)
  have hd : |y' - 0| < min δR δL := by rw [abs_sub_comm, ← Real.dist_eq]; exact hdist
  rcases hy'S with h | h
  · obtain ⟨hpos, hs⟩ := h
    rw [filter_le_eq_of_near hR' (hd.trans_le (min_le_left _ _)) (Or.inl hpos.le)] at hs
    linarith
  · obtain ⟨hneg, hs⟩ := h
    rw [filter_ge_eq_of_near hL' (hd.trans_le (min_le_right _ _)) (Or.inl hneg.le)] at hs
    linarith

/-! ### Clause 1: no visit before the lifetime -/

section Visit

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}

/-- A flow-line driver with an almost sure generating trace is a flow line from `0`. -/
theorem isFlowLine_of_driver (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) : IsFlowLine κ b J 0 θ P h α ζα := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hcpl⟩ := hfl
  exact ⟨h', 𝓕, Wα, VL, VR, B, htr, hcpl, hα.mono fun ω hω => by simpa only [Complex.ofReal_zero, sub_zero] using hω⟩

/-- **Clause 1 of `FlowLifetimeHitStatement`**: almost surely the flow line does not meet the hitting set strictly
before its lifetime. -/
theorem ae_trace_notMem_hitSet [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → α ω t ∉ hitSet κ b J θ := by
  have hη := isFlowLine_of_driver hfl hα
  filter_upwards [Restart.FCPlumb.ae_live_real_incident_bounds hκ hκ4 hb hh hη,
    RLC.jumpVisitStatement κ hκ hκ4 b J hb 0 θ P h hh α ζα hη, Supp9.ae_seedWeights_of_isFlowLine hη, hα]
    with ω hinc hjump hseed hαω t ht hmem
  obtain ⟨y, hycl, hy⟩ := exists_real_of_mem_closure_ofReal hmem
  have ht0 : y ≠ 0 → 0 < t := fun hy0 => by
    rcases eq_or_ne t 0 with h0 | h0
    · exfalso
      rw [h0, hαω.1] at hy
      exact hy0 (by exact_mod_cast hy.symm)
    · exact pos_iff_ne_zero.2 h0
  rcases lt_trichotomy y 0 with hy0 | rfl | hy0
  · by_cases hyJ : y ∈ J
    · exact hjump t (ht0 hy0.ne) ht y hyJ hy0.ne hy
    · have hg := (hinc t ht y hy).1 hy0.le
      rw [Exist.StagedLaw.leftLim_eq_of_notMem hb hyJ] at hg
      refine notMem_closure_of_neg hy0 hyJ ?_ hycl
      rintro ⟨-, hs⟩
      rw [sum_filter_le_flowLineXL_theta hκ hb hy0 hyJ] at hs
      exact absurd hs (not_le.2 ((Restart.FCPlumb.cumWeightLeft_gt_iff hκ).2 hg))
  · have hpos : 0 < ζα ω := lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ t) ht
    obtain ⟨hsL, hsR⟩ := hseed hpos
    refine zero_notMem_closure ?_ ?_ hycl
    · rw [sum_filter_flowLineXR_le_zero]; exact hsR
    · rw [sum_filter_zero_le_flowLineXL]; exact hsL
  · by_cases hyJ : y ∈ J
    · exact hjump t (ht0 hy0.ne') ht y hyJ hy0.ne' hy
    · have hg := (hinc t ht y hy).2 hy0.le
      rw [Exist.StagedLaw.rightLim_eq_of_notMem hb hyJ] at hg
      refine notMem_closure_of_pos hy0 hyJ ?_ hycl
      rintro ⟨-, hs⟩
      rw [sum_filter_flowLineXR_le_theta hκ hb hy0 hyJ] at hs
      exact absurd hs (not_le.2 ((Restart.FCPlumb.cumWeightRight_gt_iff hκ).2 hg))

end Visit

end InteractingSLE.Theorem14.GW2Rd
