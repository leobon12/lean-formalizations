import InteractingSLE.WangWu.MeanIdentChamber
import InteractingSLE.GFF.LocalSets.Prop39
import InteractingSLE.GFF.LocalSets.HittingSigma

/-!
# Wang–Wu at `κ = 4`: Proposition 4.20, the exterior components

Packet PROVE-WW-B7. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Proposition 4.20
(text dump L1701–1745): "The untouched-component lemma identifies the two exterior components."

The untouched-component lemma is the specification's Proposition 3.9 (`LocalSets.IsLocalSetMean.ae_eq_on_of_union`). Its
hypothesis `hCm` asks the region `C` to be a hitting-measurable function of the first set. Here `C` is the left side
of the left line (resp. the right side of the right line), and the missing piece (PROVE-WW-B6, obstruction 2) is:

* **Hitting-measurability of sides** (`measurable_compl_leftSideOf_relClosureH`, `…_rightSideOf_…`): the map
  `A ↦ ℍ \ leftSideOf (relClosureH A)` is `hittingSigma`-measurable. The hitting σ-algebra only sees the relative
  closure `relClosureH A = ℍ ∩ cl(A ∩ ℍ)`, so the side is taken of it; for a proper arc this is the arc's own side
  (`leftSideOf_relClosureH_arcRange`). Proof: an open `U ⊆ ℍ` lies in the side iff it avoids `A` and its rational
  points do; a point `q` lies in the side iff its component reaches a compact real window `[−N−1, −1/(N+1)]`, which is
  detected by rational points within `1/(m+1)` of the window (`closure_inter_nonempty_iff_rat`); and the component of
  `q` in the open set `ℍ \ relClosureH A` is the union of the chains of rational balls with closures in that set
  started at `q` (`mem_connectedComponentIn_iff_reach`), each ball condition being the avoidance of a compact set.
* **The exterior identification** (`ae_eq_on_leftSideOf_union`, `ae_eq_on_rightSideOf_union`): for ordered lines `L`
  (left) and `R`, the union mean equals the single-line mean of `L` on the left side of `L`, and that of `R` on the
  right side of `R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv IsZeroBoundaryGFF)
open InteractingSLE.LocalSets

universe u

namespace InteractingSLE.WangWu

/-! ### Rational points and rational balls -/

theorem exists_ratPt_dist_lt (z : ℂ) {ε : ℝ} (hε : 0 < ε) : ∃ a b : ℚ, dist (ratPt a b) z < ε := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re + ε / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - ε / 2 < z.im + ε / 2 by linarith)
  refine ⟨a, b, ?_⟩
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  have hre : (ratPt a b - z).re = a - z.re := by simp [ratPt]
  have him : (ratPt a b - z).im = b - z.im := by simp [ratPt]
  rw [hre, him]
  have h1 : |(a : ℝ) - z.re| < ε / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  have h2 : |(b : ℝ) - z.im| < ε / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  linarith

theorem exists_ratPt_mem {V : Set ℂ} (hV : IsOpen V) {z : ℂ} (hz : z ∈ V) : ∃ a b : ℚ, ratPt a b ∈ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV z hz
  obtain ⟨a, b, hab⟩ := exists_ratPt_dist_lt z hε
  exact ⟨a, b, hball hab⟩

/-- A rational ball `(a, b, r)`: centre `a + b i`, radius `r`. -/
abbrev RatBall := ℚ × ℚ × ℚ

/-- The centre of a rational ball. -/
def RatBall.cen (β : RatBall) : ℂ := ratPt β.1 β.2.1

/-- The radius of a rational ball. -/
def RatBall.rad (β : RatBall) : ℝ := β.2.2

/-- Every point of an open set lies in a rational ball whose closure is in the set. -/
theorem exists_rBall {V : Set ℂ} (hV : IsOpen V) {z : ℂ} (hz : z ∈ V) :
    ∃ β : RatBall, 0 < β.rad ∧ closedBall β.cen β.rad ⊆ V ∧ z ∈ ball β.cen β.rad := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV z hz
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
  obtain ⟨a, b, hab⟩ := exists_ratPt_dist_lt z (show 0 < ε / 4 by linarith)
  refine ⟨(a, b, r), ?_, fun y hy => hball ?_, ?_⟩
  · simp only [RatBall.rad]; linarith
  · rw [mem_closedBall] at hy
    rw [mem_ball]
    simp only [RatBall.cen, RatBall.rad] at hy
    have := dist_triangle y (ratPt a b) z
    linarith
  · rw [mem_ball, dist_comm]
    simp only [RatBall.cen, RatBall.rad]
    linarith

/-! ### Components of an open set through chains of rational balls -/

/-- The rational balls with closure in `O` reachable from `q` by a chain of at most `n + 1` pairwise-overlapping
such balls. -/
def ratReach (O : Set ℂ) (q : ℂ) : ℕ → Set RatBall
  | 0 => {β | 0 < β.rad ∧ closedBall β.cen β.rad ⊆ O ∧ q ∈ ball β.cen β.rad}
  | n + 1 => ratReach O q n ∪ {β | 0 < β.rad ∧ closedBall β.cen β.rad ⊆ O ∧
      ∃ β' ∈ ratReach O q n, (ball β.cen β.rad ∩ ball β'.cen β'.rad).Nonempty}

theorem ball_subset_of_mem_reach {O : Set ℂ} {q : ℂ} {n : ℕ} {β : RatBall} (hβ : β ∈ ratReach O q n) :
    ball β.cen β.rad ⊆ connectedComponentIn O q := by
  induction n generalizing β with
  | zero =>
    obtain ⟨-, hsub, hq⟩ := hβ
    exact (isPreconnected_ball).subset_connectedComponentIn hq (ball_subset_closedBall.trans hsub)
  | succ n ih =>
    rcases hβ with hβ | ⟨-, hsub, β', hβ', z, hz, hz'⟩
    · exact ih hβ
    · have hzq : z ∈ connectedComponentIn O q := ih hβ' hz'
      rw [connectedComponentIn_eq hzq]
      exact (isPreconnected_ball).subset_connectedComponentIn hz (ball_subset_closedBall.trans hsub)

/-- **The component of `q` in an open set is the union of the reachable rational balls.** -/
theorem mem_connectedComponentIn_iff_ratReach {O : Set ℂ} (hO : IsOpen O) {q : ℂ} (hq : q ∈ O) {p : ℂ} :
    p ∈ connectedComponentIn O q ↔ ∃ n : ℕ, ∃ β ∈ ratReach O q n, p ∈ ball β.cen β.rad := by
  refine ⟨fun hp => ?_, fun ⟨n, β, hβ, hp⟩ => ball_subset_of_mem_reach hβ hp⟩
  set R : Set ℂ := ⋃ n : ℕ, ⋃ β ∈ ratReach O q n, ball β.cen β.rad with hR
  have hRo : IsOpen R := isOpen_iUnion fun n => isOpen_biUnion fun β _ => isOpen_ball
  have hsplit : connectedComponentIn O q ⊆ R ∪ (closure R)ᶜ := by
    intro z hz
    by_cases hzR : z ∈ R
    · exact Or.inl hzR
    refine Or.inr fun hzc => hzR ?_
    obtain ⟨β, hβr, hβO, hzβ⟩ := exists_rBall hO (connectedComponentIn_subset _ _ hz)
    obtain ⟨y, hyβ, hyR⟩ := mem_closure_iff.1 hzc _ isOpen_ball hzβ
    simp only [hR, mem_iUnion] at hyR
    obtain ⟨n, β', hβ', hyβ'⟩ := hyR
    simp only [hR, mem_iUnion]
    exact ⟨n + 1, β, Or.inr ⟨hβr, hβO, β', hβ', y, hyβ, hyβ'⟩, hzβ⟩
  have hqR : q ∈ R := by
    obtain ⟨β, hβr, hβO, hqβ⟩ := exists_rBall hO hq
    simp only [hR, mem_iUnion]
    exact ⟨0, β, ⟨hβr, hβO, hqβ⟩, hqβ⟩
  have hsub := (isPreconnected_connectedComponentIn).subset_left_of_subset_union hRo
    isClosed_closure.isOpen_compl (Set.disjoint_left.2 fun z hz hzc => hzc (subset_closure hz)) hsplit
    ⟨q, mem_connectedComponentIn hq, hqR⟩
  have := hsub hp
  simpa [hR] using this

/-! ### Sides through compact real windows -/

/-- The side of `A` facing the real set `I` (`leftSideOf = sideOf (Iio 0)`, `rightSideOf = sideOf (Ioi 0)`). -/
def sideOf (I : Set ℝ) (A : Set ℂ) : Set ℂ :=
  {z | z ∈ H \ A ∧ ∃ x ∈ I, (x : ℂ) ∉ A ∧ (x : ℂ) ∈ closure (connectedComponentIn (H \ A) z)}

theorem leftSideOf_eq_sideOf (A : Set ℂ) : leftSideOf A = sideOf (Iio 0) A := rfl

theorem rightSideOf_eq_sideOf (A : Set ℂ) : rightSideOf A = sideOf (Ioi 0) A := rfl

/-- A side is a union of components. -/
theorem mem_sideOf_of_mem_connectedComponentIn {I : Set ℝ} {A : Set ℂ} {z w : ℂ} (hz : z ∈ sideOf I A)
    (hw : w ∈ connectedComponentIn (H \ A) z) : w ∈ sideOf I A := by
  obtain ⟨-, x, hx, hxA, hxcl⟩ := hz
  refine ⟨connectedComponentIn_subset _ _ hw, x, hx, hxA, ?_⟩
  rwa [← connectedComponentIn_eq hw]

/-- **The closure of an open set meets a compact set iff rational points of the set approach it.** -/
theorem closure_inter_nonempty_iff_rat {O K : Set ℂ} (hO : IsOpen O) (hK : IsCompact K) (hKne : K.Nonempty) :
    (closure O ∩ K).Nonempty ↔
      ∀ m : ℕ, ∃ a b : ℚ, ratPt a b ∈ O ∧ infDist (ratPt a b) K < 1 / ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨x, hxO, hxK⟩ m
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨y, hyb, hyO⟩ := mem_closure_iff.1 hxO _ isOpen_ball (mem_ball_self (half_pos hε))
    obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 (hO.inter isOpen_ball) y ⟨hyO, hyb⟩
    obtain ⟨a, b, hab⟩ := exists_ratPt_dist_lt y hε'
    have hmem := hball hab
    refine ⟨a, b, hmem.1, ?_⟩
    have h2 : dist (ratPt a b) x < 1 / ((m : ℝ) + 1) / 2 := hmem.2
    calc infDist (ratPt a b) K ≤ dist (ratPt a b) x := infDist_le_dist_of_mem hxK
      _ < 1 / ((m : ℝ) + 1) := h2.trans (half_lt_self hε)
  · intro h
    by_contra hne
    have hsub : K ⊆ (closure O)ᶜ := fun z hz hzc => hne ⟨z, hzc, hz⟩
    obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open isClosed_closure.isOpen_compl hsub
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨a, b, habO, habK⟩ := h m
    have : ratPt a b ∈ thickening δ K := (mem_thickening_iff_infDist_lt hKne).2 (habK.trans hm)
    exact hδK this (subset_closure habO)

section Windows

variable {I : Set ℝ} {Kw : ℕ → Set ℝ}

/-- **Side membership through compact real windows**: for a relatively closed `B ⊆ ℍ` and windows `Kw N ⊆ I`
covering `I`, `z` lies in the side of `B` facing `I` iff it is off `B` and, for some window, rational points of its
component come arbitrarily close to the window. -/
theorem mem_sideOf_iff_rat {B : Set ℂ} (hBH : B ⊆ H) (hBo : IsOpen (H \ B)) (hKc : ∀ N, IsCompact (Kw N))
    (hKne : ∀ N, (Kw N).Nonempty) (hKI : ∀ N, Kw N ⊆ I) (hIK : ∀ x ∈ I, ∃ N, x ∈ Kw N) {z : ℂ} :
    z ∈ sideOf I B ↔ z ∈ H \ B ∧ ∃ N : ℕ, ∀ m : ℕ, ∃ a b : ℚ, ratPt a b ∈ connectedComponentIn (H \ B) z ∧
      infDist (ratPt a b) ((fun x : ℝ => (x : ℂ)) '' Kw N) < 1 / ((m : ℝ) + 1) := by
  have hnot : ∀ x : ℝ, (x : ℂ) ∉ B := fun x hx => by
    have := hBH hx
    exact lt_irrefl (0 : ℝ) (by simpa using (show (0 : ℝ) < (x : ℂ).im from this))
  have hcO : IsOpen (connectedComponentIn (H \ B) z) := hBo.connectedComponentIn
  have hKc' : ∀ N, IsCompact ((fun x : ℝ => (x : ℂ)) '' Kw N) := fun N =>
    (hKc N).image Complex.continuous_ofReal
  have hKne' : ∀ N, ((fun x : ℝ => (x : ℂ)) '' Kw N).Nonempty := fun N => (hKne N).image _
  constructor
  · rintro ⟨hz, x, hxI, -, hxcl⟩
    obtain ⟨N, hN⟩ := hIK x hxI
    exact ⟨hz, N, (closure_inter_nonempty_iff_rat hcO (hKc' N) (hKne' N)).1 ⟨x, hxcl, x, hN, rfl⟩⟩
  · rintro ⟨hz, N, h⟩
    obtain ⟨_, hycl, x, hxK, rfl⟩ := (closure_inter_nonempty_iff_rat hcO (hKc' N) (hKne' N)).2 h
    exact ⟨hz, x, hKI N hxK, hnot x, hycl⟩

/-- Avoidance of a point of `ℍ` by the relative closure is hitting-measurable. -/
theorem measurableSet_notMem_relClosureH {z : ℂ} (hz : z ∈ H) :
    MeasurableSet[hittingSigma] {A : Set ℂ | z ∉ relClosureH A} := by
  have : {A : Set ℂ | z ∉ relClosureH A} = {A : Set ℂ | Disjoint {z} (relClosureH A)} := by
    ext A
    simp only [mem_ofPred_eq, Set.disjoint_singleton_left]
  rw [this]
  exact measurableSet_disjoint_relClosureH isCompact_singleton (singleton_subset_iff.2 hz)

/-- The closure of a rational ball lies in `ℍ \ relClosureH A`: a hitting-measurable condition on `A`. -/
theorem measurableSet_good_ratBall (β : RatBall) :
    MeasurableSet[hittingSigma]
      {A : Set ℂ | 0 < β.rad ∧ closedBall β.cen β.rad ⊆ H \ relClosureH A} := by
  by_cases hd : 0 < β.rad ∧ closedBall β.cen β.rad ⊆ H
  · have : {A : Set ℂ | 0 < β.rad ∧ closedBall β.cen β.rad ⊆ H \ relClosureH A} =
        {A : Set ℂ | Disjoint (closedBall β.cen β.rad) (relClosureH A)} := by
      ext A
      simp only [mem_ofPred_eq, subset_sdiff]
      exact ⟨fun h => h.2.2, fun h => ⟨hd.1, hd.2, h⟩⟩
    rw [this]
    exact measurableSet_disjoint_relClosureH (isCompact_closedBall _ _) hd.2
  · have : {A : Set ℂ | 0 < β.rad ∧ closedBall β.cen β.rad ⊆ H \ relClosureH A} = ∅ := by
      ext A
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hd ⟨h.1, h.2.trans sdiff_subset⟩
    rw [this]
    exact @MeasurableSet.empty _ hittingSigma

/-- Reachability of a rational ball in `ℍ \ relClosureH A` is a hitting-measurable condition on `A`. -/
theorem measurableSet_mem_ratReach (q : ℂ) (n : ℕ) (β : RatBall) :
    MeasurableSet[hittingSigma] {A : Set ℂ | β ∈ ratReach (H \ relClosureH A) q n} := by
  induction n generalizing β with
  | zero =>
    have : {A : Set ℂ | β ∈ ratReach (H \ relClosureH A) q 0} =
        {A : Set ℂ | 0 < β.rad ∧ closedBall β.cen β.rad ⊆ H \ relClosureH A} ∩
          {_A : Set ℂ | q ∈ ball β.cen β.rad} := by
      ext A
      simp only [ratReach, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [this]
    exact (measurableSet_good_ratBall β).inter (MeasurableSet.const _)
  | succ n ih =>
    have : {A : Set ℂ | β ∈ ratReach (H \ relClosureH A) q (n + 1)} =
        {A : Set ℂ | β ∈ ratReach (H \ relClosureH A) q n} ∪
          ({A : Set ℂ | 0 < β.rad ∧ closedBall β.cen β.rad ⊆ H \ relClosureH A} ∩
            ⋃ β' : RatBall, ({A : Set ℂ | β' ∈ ratReach (H \ relClosureH A) q n} ∩
              {_A : Set ℂ | (ball β.cen β.rad ∩ ball β'.cen β'.rad).Nonempty})) := by
      ext A
      simp only [ratReach, mem_ofPred_eq, mem_union, mem_inter_iff, mem_iUnion, and_assoc]
    rw [this]
    exact (ih β).union ((measurableSet_good_ratBall β).inter
      (MeasurableSet.iUnion fun β' => (ih β').inter (MeasurableSet.const _)))

/-- Membership in the component of a point `q ∈ ℍ` of `ℍ \ relClosureH A` is hitting-measurable. -/
theorem measurableSet_mem_component {q : ℂ} (hq : q ∈ H) (p : ℂ) :
    MeasurableSet[hittingSigma]
      {A : Set ℂ | q ∉ relClosureH A ∧ p ∈ connectedComponentIn (H \ relClosureH A) q} := by
  have : {A : Set ℂ | q ∉ relClosureH A ∧ p ∈ connectedComponentIn (H \ relClosureH A) q} =
      {A : Set ℂ | q ∉ relClosureH A} ∩ ⋃ n : ℕ, ⋃ β : RatBall,
        ({A : Set ℂ | β ∈ ratReach (H \ relClosureH A) q n} ∩ {_A : Set ℂ | p ∈ ball β.cen β.rad}) := by
    ext A
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    refine and_congr_right fun hqA => ?_
    rw [mem_connectedComponentIn_iff_ratReach (isOpen_H_diff_relClosureH A) ⟨hq, hqA⟩]
  rw [this]
  exact (measurableSet_notMem_relClosureH hq).inter (MeasurableSet.iUnion fun n => MeasurableSet.iUnion
    fun β => (measurableSet_mem_ratReach q n β).inter (MeasurableSet.const _))

/-- Membership of a point of `ℍ` in the side of `relClosureH A` facing `I` is hitting-measurable. -/
theorem measurableSet_mem_sideOf_relClosureH (hKc : ∀ N, IsCompact (Kw N)) (hKne : ∀ N, (Kw N).Nonempty)
    (hKI : ∀ N, Kw N ⊆ I) (hIK : ∀ x ∈ I, ∃ N, x ∈ Kw N) {z : ℂ} (hz : z ∈ H) :
    MeasurableSet[hittingSigma] {A : Set ℂ | z ∈ sideOf I (relClosureH A)} := by
  have : {A : Set ℂ | z ∈ sideOf I (relClosureH A)} =
      {A : Set ℂ | z ∉ relClosureH A} ∩ ⋃ N : ℕ, ⋂ m : ℕ, ⋃ a : ℚ, ⋃ b : ℚ,
        ({A : Set ℂ | z ∉ relClosureH A ∧ ratPt a b ∈ connectedComponentIn (H \ relClosureH A) z} ∩
          {_A : Set ℂ | infDist (ratPt a b) ((fun x : ℝ => (x : ℂ)) '' Kw N) < 1 / ((m : ℝ) + 1)}) := by
    ext A
    rw [mem_ofPred_eq, mem_sideOf_iff_rat (relClosureH_subset A) (isOpen_H_diff_relClosureH A) hKc hKne hKI hIK]
    simp only [mem_inter_iff, mem_iUnion, mem_iInter, mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨-, hzA⟩, N, h⟩
      exact ⟨hzA, N, fun m => by
        obtain ⟨a, b, h1, h2⟩ := h m
        exact ⟨a, b, ⟨hzA, h1⟩, h2⟩⟩
    · rintro ⟨hzA, N, h⟩
      exact ⟨⟨hz, hzA⟩, N, fun m => by
        obtain ⟨a, b, ⟨-, h1⟩, h2⟩ := h m
        exact ⟨a, b, h1, h2⟩⟩
  rw [this]
  exact (measurableSet_notMem_relClosureH hz).inter (MeasurableSet.iUnion fun N => MeasurableSet.iInter
    fun m => MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      (measurableSet_mem_component hz _).inter (MeasurableSet.const _))

/-- An open `U ⊆ ℍ` lies in the side of `relClosureH A` iff it avoids `A` and its rational points lie in the side. -/
theorem subset_sideOf_relClosureH_iff {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) (A : Set ℂ) :
    U ⊆ sideOf I (relClosureH A) ↔
      Disjoint A U ∧ ∀ a b : ℚ, ratPt a b ∈ U → ratPt a b ∈ sideOf I (relClosureH A) := by
  constructor
  · intro h
    refine ⟨Set.disjoint_left.2 fun z hzA hzU => (h hzU).1.2 ⟨hUH hzU, subset_closure ⟨hzA, hUH hzU⟩⟩,
      fun a b hab => h hab⟩
  · rintro ⟨hdis, hrat⟩ z hzU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨a, b, hab⟩ := exists_ratPt_dist_lt z hε
    have hq := hrat a b (hball hab)
    have hsub : ball z ε ⊆ H \ relClosureH A := fun y hy => by
      refine ⟨hUH (hball hy), fun hyA => ?_⟩
      obtain ⟨w, hwA, hwU⟩ := (relClosureH_inter_nonempty_iff hU hUH).1 ⟨y, hyA, hball hy⟩
      exact Set.disjoint_left.1 hdis hwA hwU
    have hz : z ∈ connectedComponentIn (H \ relClosureH A) (ratPt a b) :=
      (isPreconnected_ball).subset_connectedComponentIn hab hsub (mem_ball_self hε)
    exact mem_sideOf_of_mem_connectedComponentIn hq hz

/-- **The complement of a side of the relative closure is a hitting-measurable function of the set.** -/
theorem measurable_compl_sideOf_relClosureH (hKc : ∀ N, IsCompact (Kw N)) (hKne : ∀ N, (Kw N).Nonempty)
    (hKI : ∀ N, Kw N ⊆ I) (hIK : ∀ x ∈ I, ∃ N, x ∈ Kw N) :
    Measurable[hittingSigma, hittingSigma] fun A : Set ℂ => H \ sideOf I (relClosureH A) := by
  refine @measurable_generateFrom (Set ℂ) (Set ℂ) hittingSigma _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have : (fun A : Set ℂ => H \ sideOf I (relClosureH A)) ⁻¹' {S | (S ∩ U).Nonempty} =
      ({A : Set ℂ | Disjoint A U} ∩ ⋂ a : ℚ, ⋂ b : ℚ,
        {A : Set ℂ | ratPt a b ∈ U → ratPt a b ∈ sideOf I (relClosureH A)})ᶜ := by
    ext A
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, mem_inter_iff, mem_iInter]
    rw [← subset_sideOf_relClosureH_iff hU hUH A]
    constructor
    · rintro ⟨z, ⟨-, hzs⟩, hzU⟩ hsub
      exact hzs (hsub hzU)
    · intro hns
      obtain ⟨z, hzU, hzs⟩ := not_subset.1 hns
      exact ⟨z, ⟨hUH hzU, hzs⟩, hzU⟩
  rw [this]
  refine (MeasurableSet.inter (measurableSet_avoid hU hUH) (MeasurableSet.iInter fun a =>
    MeasurableSet.iInter fun b => ?_)).compl
  by_cases hab : ratPt a b ∈ U
  · have e : {A : Set ℂ | ratPt a b ∈ U → ratPt a b ∈ sideOf I (relClosureH A)} =
        {A : Set ℂ | ratPt a b ∈ sideOf I (relClosureH A)} := by
      ext A
      simp only [mem_ofPred_eq, hab, true_imp_iff]
    rw [e]
    exact measurableSet_mem_sideOf_relClosureH hKc hKne hKI hIK (hUH hab)
  · have e : {A : Set ℂ | ratPt a b ∈ U → ratPt a b ∈ sideOf I (relClosureH A)} = univ := by
      ext A
      simp only [mem_ofPred_eq, hab, false_imp_iff, mem_univ]
    rw [e]
    exact @MeasurableSet.univ _ hittingSigma

end Windows

/-! ### Left and right sides -/

theorem exists_nat_window {x : ℝ} (hx : 0 < x) : ∃ N : ℕ, 1 / ((N : ℝ) + 1) ≤ x ∧ x ≤ (N : ℝ) + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max x (1 / x))
  have hN1 : max x (1 / x) < (N : ℝ) + 1 := hN.trans (lt_add_one _)
  refine ⟨N, ?_, (le_max_left _ _).trans hN1.le⟩
  have h1 : 1 / x < (N : ℝ) + 1 := (le_max_right _ _).trans_lt hN1
  rw [div_le_iff₀ (by positivity)]
  have := (div_lt_iff₀ hx).1 h1
  linarith

theorem one_div_le_self_add_one (N : ℕ) : 1 / ((N : ℝ) + 1) ≤ (N : ℝ) + 1 := by
  have h : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
  calc 1 / ((N : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; exact h
    _ ≤ (N : ℝ) + 1 := h

/-- **The complement of the left side of the relative closure is a hitting-measurable function of the set.** -/
theorem measurable_compl_leftSideOf_relClosureH :
    Measurable[hittingSigma, hittingSigma] fun A : Set ℂ => H \ leftSideOf (relClosureH A) :=
  measurable_compl_sideOf_relClosureH (Kw := fun N => Icc (-((N : ℝ) + 1)) (-(1 / ((N : ℝ) + 1))))
    (fun _ => isCompact_Icc) (fun N => nonempty_Icc.2 (by linarith [one_div_le_self_add_one N]))
    (fun N x hx => show x < 0 by
      have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith [hx.2])
    (fun x hx => by
      obtain ⟨N, h1, h2⟩ := exists_nat_window (neg_pos.2 (show x < 0 from hx))
      exact ⟨N, by constructor <;> linarith⟩)

/-- **The complement of the right side of the relative closure is a hitting-measurable function of the set.** -/
theorem measurable_compl_rightSideOf_relClosureH :
    Measurable[hittingSigma, hittingSigma] fun A : Set ℂ => H \ rightSideOf (relClosureH A) :=
  measurable_compl_sideOf_relClosureH (Kw := fun N => Icc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1))
    (fun _ => isCompact_Icc) (fun N => nonempty_Icc.2 (one_div_le_self_add_one N))
    (fun N x hx => show 0 < x by
      have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
      linarith [hx.1])
    (fun x hx => by
      obtain ⟨N, h1, h2⟩ := exists_nat_window (show 0 < x from hx)
      exact ⟨N, h1, h2⟩)

namespace IsProperArc

variable {γ : ℝ → ℂ}

/-- The relative closure of a proper arc is its part in `ℍ`. -/
theorem relClosureH_arcRange (hγ : IsProperArc γ) : relClosureH (arcRange γ) = arcRange γ ∩ H := by
  have hcl : IsClosed (arcRange γ) := hγ.isClosed_image isClosed_Ici subset_rfl
  ext z
  exact ⟨fun ⟨hzH, hzc⟩ => ⟨hcl.closure_subset (closure_mono inter_subset_left hzc), hzH⟩,
    fun ⟨hzS, hzH⟩ => ⟨hzH, subset_closure ⟨hzS, hzH⟩⟩⟩

/-- The sides of the relative closure of a proper arc are the arc's sides (for real sets off `0`). -/
theorem sideOf_relClosureH (hγ : IsProperArc γ) {I : Set ℝ} (hI : (0 : ℝ) ∉ I) :
    sideOf I (relClosureH (arcRange γ)) = sideOf I (arcRange γ) := by
  rw [hγ.relClosureH_arcRange]
  have hd : H \ (arcRange γ ∩ H) = H \ arcRange γ := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  ext z
  simp only [sideOf, mem_ofPred_eq, hd]
  refine and_congr_right fun _ => exists_congr fun x => and_congr_right fun hx => and_congr_left fun _ => ?_
  have hx0 : x ≠ 0 := fun h => hI (h ▸ hx)
  exact ⟨fun _ => hγ.ofReal_notMem_arcRange hx0, fun h hm => h hm.1⟩

theorem leftSideOf_relClosureH (hγ : IsProperArc γ) :
    leftSideOf (relClosureH (arcRange γ)) = leftSideOf (arcRange γ) :=
  hγ.sideOf_relClosureH (I := Iio 0) (lt_irrefl (0 : ℝ))

theorem rightSideOf_relClosureH (hγ : IsProperArc γ) :
    rightSideOf (relClosureH (arcRange γ)) = rightSideOf (arcRange γ) :=
  hγ.sideOf_relClosureH (I := Ioi 0) (lt_irrefl (0 : ℝ))

end IsProperArc

/-! ### Proposition 4.20: the exterior components -/

section Probabilistic

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Wang–Wu Proposition 4.20, the left exterior component** ("the untouched-component lemma identifies the two
exterior components"). Let `R, L` be random simple proper arcs whose ranges are local sets of the zero-boundary GFF
`h`, conditionally independent given `h` (e.g. both determined by `h`), with `L` to the left of `R`. Then almost
surely the mean of the union `R ∪ L` agrees with the single-line mean of `L` on every test function supported in the
left side of `L`. -/
theorem ae_eq_on_leftSideOf_union (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω)) h P) (hLloc : IsLocalSet (fun ω => arcRange (L ω)) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (arcRange (L ω)) (rightSideOf (arcRange (R ω))))
    {g gL : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => arcRange (R ω) ∪ arcRange (L ω)) h P g)
    (hgL : IsLocalSetMean (fun ω => arcRange (L ω)) h P gL) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ leftSideOf (arcRange (L ω)) → g ω φ = gL ω φ := by
  set C : Ω → Set ℂ := fun ω => leftSideOf (relClosureH (arcRange (L ω))) with hCdef
  have hCm : Measurable[MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma, hittingSigma]
      fun ω => H \ C ω :=
    measurable_compl_leftSideOf_relClosureH.comp (comap_measurable _)
  have hCeq : ∀ᵐ ω ∂P, C ω = leftSideOf (arcRange (L ω)) := by
    filter_upwards [harc] with ω hω
    exact hω.2.leftSideOf_relClosureH
  have hC : ∀ᵐ ω ∂P, C ω ⊆ H \ arcRange (L ω) ∧
      ∀ z ∈ C ω, connectedComponentIn (H \ arcRange (L ω)) z ⊆ C ω := by
    filter_upwards [hCeq] with ω hω
    rw [hω]
    exact ⟨fun z hz => hz.1, fun z hz w hw => mem_leftSideOf_of_mem_connectedComponentIn hz hw⟩
  have hCA₂ : ∀ᵐ ω ∂P, Disjoint (C ω) (arcRange (R ω)) := by
    filter_upwards [hCeq, harc, hord] with ω hω hω' hord'
    rw [hω]
    exact Set.disjoint_left.2 fun z hz hzR =>
      (hω'.1.leftSideOf_subset_of_disjoint hω'.2 hord' hz).1.2 hzR
  have e : (fun ω => arcRange (L ω) ∪ arcRange (R ω)) = fun ω => arcRange (R ω) ∪ arcRange (L ω) :=
    funext fun ω => union_comm _ _
  have hg' : IsLocalSetMean (fun ω => arcRange (L ω) ∪ arcRange (R ω)) h P g := e ▸ hg
  have key := IsLocalSetMean.ae_eq_on_of_union hh hLm hRm hci hLloc hRloc hCm hC hCA₂ hg' hgL
  filter_upwards [key, hCeq] with ω hω hCω φ hφ
  exact hω φ (hCω ▸ hφ)

/-- **Wang–Wu Proposition 4.20, the right exterior component**: the mean of the union `R ∪ L` agrees with the
single-line mean of `R` on every test function supported in the right side of `R`. -/
theorem ae_eq_on_rightSideOf_union (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {R L : Ω → ℝ → ℂ}
    (hRm : Measurable[mΩ, hittingSigma] fun ω => arcRange (R ω))
    (hLm : Measurable[mΩ, hittingSigma] fun ω => arcRange (L ω))
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (L ω)) hittingSigma) P)
    (hRloc : IsLocalSet (fun ω => arcRange (R ω)) h P) (hLloc : IsLocalSet (fun ω => arcRange (L ω)) h P)
    (harc : ∀ᵐ ω ∂P, IsProperArc (R ω) ∧ IsProperArc (L ω))
    (hord : ∀ᵐ ω ∂P, Disjoint (arcRange (L ω)) (rightSideOf (arcRange (R ω))))
    {g gR : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => arcRange (R ω) ∪ arcRange (L ω)) h P g)
    (hgR : IsLocalSetMean (fun ω => arcRange (R ω)) h P gR) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ rightSideOf (arcRange (R ω)) → g ω φ = gR ω φ := by
  set C : Ω → Set ℂ := fun ω => rightSideOf (relClosureH (arcRange (R ω))) with hCdef
  have hCm : Measurable[MeasurableSpace.comap (fun ω => arcRange (R ω)) hittingSigma, hittingSigma]
      fun ω => H \ C ω :=
    measurable_compl_rightSideOf_relClosureH.comp (comap_measurable _)
  have hCeq : ∀ᵐ ω ∂P, C ω = rightSideOf (arcRange (R ω)) := by
    filter_upwards [harc] with ω hω
    exact hω.1.rightSideOf_relClosureH
  have hC : ∀ᵐ ω ∂P, C ω ⊆ H \ arcRange (R ω) ∧
      ∀ z ∈ C ω, connectedComponentIn (H \ arcRange (R ω)) z ⊆ C ω := by
    filter_upwards [hCeq] with ω hω
    rw [hω]
    exact ⟨fun z hz => hz.1, fun z hz w hw => mem_rightSideOf_of_mem_connectedComponentIn hz hw⟩
  have hCA₂ : ∀ᵐ ω ∂P, Disjoint (C ω) (arcRange (L ω)) := by
    filter_upwards [hCeq, hord] with ω hω hord'
    rw [hω]
    exact hord'.symm
  have key := IsLocalSetMean.ae_eq_on_of_union hh hRm hLm hci hRloc hLloc hCm hC hCA₂ hg hgR
  filter_upwards [key, hCeq] with ω hω hCω φ hφ
  exact hω φ (hCω ▸ hφ)

end Probabilistic

end InteractingSLE.WangWu
