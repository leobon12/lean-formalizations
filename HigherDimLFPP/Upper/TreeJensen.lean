import HigherDimLFPP.Upper.CutTree
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Combinatorics of well-formed cut trees and the tree Jensen inequality

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.1, proof of Lemma 4.1 (the telescoping
identities `R_v = θ(v) exp(Σ_{u≺v} a_u)`, `Σ_v θ(v) H_v = H_root + Σ_u θ(u) Δ_u`, flow
conservation and Jensen's inequality), as written out in HA3 D2
(`planning/audits/HA3-section-4.md`).

2D source: the first half of `LQGDimension/LFPP/TreeInequalityAux.lean` (`TreeIneqJ42.prefix_mem`,
`take_mem`, `ctime`, `times_mem`, `R_le_S`, `R_pos`, `flow_child`, `below`, `chainSum`, `Claim`,
`claim_leaf`, `claim_internal`, `claim_all`, `tree_jensen_root`).  Everything here only uses
norms, so it is stated for paths with values in any normed additive group `E`; the root chord
`R_root = 1` is a field of `TreeHyp` (for an admissible path it is `‖e₁‖ = 1`).

* `tree_jensen_root`: if a node function `L` is additive over children and dominates
  `R_v e^{F v}` at leaves, then `F [] + Σ_v θ(v) Σ_{j<|v|} Y(v.take j) ≤ log L []` whenever
  `Y u ≤ a_u + Σ_i p_{u,i} F(u i) - F u` at internal nodes; moreover `θ` is a probability on the
  leaves and `L [] > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLFPP.Upper

namespace TreeJensen

/-! ## Combinatorics of well-formed cut trees -/

section Tree

variable {E : Type*} [NormedAddCommGroup E] {T : CutTree} {γ : ℝ → E} {K : ℕ} {ε ρ₀ : ℝ}

theorem prefix_mem_aux (hT : T.WF γ K ε ρ₀) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n →
      ∀ (w : List ℕ) (i : ℕ), w ++ [i] <+: v → w ∈ T.nodes ∧ i < T.nch w := by
  induction n with
  | zero =>
    intro v _ hlen w i hp
    have := hp.length_le
    simp only [List.length_append, List.length_singleton] at this
    omega
  | succ n ih =>
    intro v hv hlen w i hp
    rcases hT.is_child v hv with rfl | ⟨u, hu, i', hi', rfl⟩
    · simp at hlen
    · rcases List.prefix_concat_iff.1 hp with h | h
      · obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
        injection h2 with h3
        subst h3
        exact ⟨hu, hi'⟩
      · exact ih u hu (by simpa using hlen) w i h

/-- Every strict prefix of a node is a node, and the next letter is a valid child index. -/
theorem prefix_mem (hT : T.WF γ K ε ρ₀) {v : List ℕ} (hv : v ∈ T.nodes) {w : List ℕ} {i : ℕ}
    (hp : w ++ [i] <+: v) : w ∈ T.nodes ∧ i < T.nch w :=
  prefix_mem_aux hT _ v hv rfl w i hp

/-- The strict prefixes of a node are internal nodes. -/
theorem take_mem (hT : T.WF γ K ε ρ₀) {v : List ℕ} (hv : v ∈ T.nodes) {j : ℕ}
    (hj : j < v.length) : v.take j ∈ T.nodes ∧ 0 < T.nch (v.take j) := by
  have h := prefix_mem hT hv (w := v.take j) (i := v[j]) (by
    rw [List.take_append_getElem hj]; exact List.take_prefix _ _)
  exact ⟨h.1, by omega⟩

theorem exists_child_prefix (hT : T.WF γ K ε ρ₀) {u v : List ℕ} (hv : v ∈ T.nodes)
    (hp : u <+: v) (hne : u ≠ v) : ∃ i < T.nch u, u ++ [i] <+: v := by
  have hlt : u.length < v.length :=
    lt_of_le_of_ne hp.length_le (fun h => hne (hp.eq_of_length h))
  have hu : v.take u.length = u := (List.prefix_iff_eq_take.1 hp).symm
  have heq : v.take u.length ++ [v[u.length]] = v.take (u.length + 1) :=
    List.take_append_getElem hlt
  rw [hu] at heq
  have hpre : u ++ [v[u.length]] <+: v := heq ▸ List.take_prefix _ _
  exact ⟨_, (prefix_mem hT hv hpre).2, hpre⟩

/-- Consecutive child times of a node: `ctime u i = t₀ (u ++ [i])` for `i < nch u`, and
`ctime u (nch u) = t₁ u`. -/
def ctime (T : CutTree) (u : List ℕ) (j : ℕ) : ℝ :=
  if j < T.nch u then T.t₀ (u ++ [j]) else T.t₁ u

theorem ctime_zero (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    ctime T u 0 = T.t₀ u := by
  rw [ctime, ite_eq_left hn, (hT.consecutive u hu hn).1]

theorem ctime_nch (u : List ℕ) : ctime T u (T.nch u) = T.t₁ u := by
  rw [ctime, ite_eq_right (lt_irrefl _)]

theorem t₀_child {u : List ℕ} {i : ℕ} (hi : i < T.nch u) : T.t₀ (u ++ [i]) = ctime T u i := by
  rw [ctime, ite_eq_left hi]

theorem t₁_child (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) : T.t₁ (u ++ [i]) = ctime T u (i + 1) := by
  have hn : 0 < T.nch u := by omega
  obtain ⟨_, hlast, hcons⟩ := hT.consecutive u hu hn
  by_cases h : i + 1 < T.nch u
  · rw [ctime, ite_eq_left h, hcons i h]
  · have : i = T.nch u - 1 := by omega
    rw [ctime, ite_eq_right h, this]
    exact hlast

theorem ctime_mono (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ T.nch u) : ctime T u i ≤ ctime T u j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have hjn : j < T.nch u := by omega
    calc ctime T u i ≤ ctime T u j := ih (by omega)
      _ = T.t₀ (u ++ [j]) := (t₀_child hjn).symm
      _ ≤ T.t₁ (u ++ [j]) := hT.time_le _ (hT.child_mem u hu j hjn)
      _ = ctime T u (j + 1) := t₁_child hT hu hjn

theorem times_mem_aux (hT : T.WF γ K ε ρ₀) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n → 0 ≤ T.t₀ v ∧ T.t₁ v ≤ 1 := by
  induction n with
  | zero =>
    intro v _ hlen
    rw [List.eq_nil_of_length_eq_zero hlen, hT.root_time.1, hT.root_time.2]
    exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    intro v hv hlen
    rcases hT.is_child v hv with rfl | ⟨u, hu, i, hi, rfl⟩
    · simp at hlen
    · obtain ⟨h0, h1⟩ := ih u hu (by simpa using hlen)
      have hn : 0 < T.nch u := by omega
      refine ⟨?_, ?_⟩
      · calc (0 : ℝ) ≤ T.t₀ u := h0
          _ = ctime T u 0 := (ctime_zero hT hu hn).symm
          _ ≤ ctime T u i := ctime_mono hT hu (Nat.zero_le _) hi.le
          _ = T.t₀ (u ++ [i]) := (t₀_child hi).symm
      · calc T.t₁ (u ++ [i]) = ctime T u (i + 1) := t₁_child hT hu hi
          _ ≤ ctime T u (T.nch u) := ctime_mono hT hu (by omega) le_rfl
          _ = T.t₁ u := ctime_nch u
          _ ≤ 1 := h1

/-- All node times lie in `[0,1]`. -/
theorem times_mem (hT : T.WF γ K ε ρ₀) {v : List ℕ} (hv : v ∈ T.nodes) :
    0 ≤ T.t₀ v ∧ T.t₀ v ≤ T.t₁ v ∧ T.t₁ v ≤ 1 :=
  have h := times_mem_aux hT _ v hv rfl
  ⟨h.1, hT.time_le v hv, h.2⟩

theorem ctime_mem (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u)
    {j : ℕ} (hj : j ≤ T.nch u) : 0 ≤ ctime T u j ∧ ctime T u j ≤ 1 := by
  obtain ⟨h0, -, h1⟩ := times_mem hT hu
  constructor
  · calc (0 : ℝ) ≤ T.t₀ u := h0
      _ = ctime T u 0 := (ctime_zero hT hu hn).symm
      _ ≤ ctime T u j := ctime_mono hT hu (Nat.zero_le _) hj
  · calc ctime T u j ≤ ctime T u (T.nch u) := ctime_mono hT hu hj le_rfl
      _ = T.t₁ u := ctime_nch u
      _ ≤ 1 := h1

/-- The children's chords add up to the parent chord: `y_u - x_u = Σ_i (y_{ui} - x_{ui})`. -/
theorem sum_child_chords (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes)
    (hn : 0 < T.nch u) :
    ∑ i ∈ Finset.range (T.nch u), (T.y γ (u ++ [i]) - T.x γ (u ++ [i])) = T.y γ u - T.x γ u := by
  have key : ∑ i ∈ Finset.range (T.nch u), (γ (ctime T u (i + 1)) - γ (ctime T u i)) =
      T.y γ u - T.x γ u := by
    rw [Finset.sum_range_sub (fun j => γ (ctime T u j)), ctime_nch, ctime_zero hT hu hn]
    rfl
  rw [← key]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [CutTree.x, CutTree.y, t₀_child hi, t₁_child hT hu hi]

/-- Chord lengths of the children dominate the chord of the parent (triangle inequality). -/
theorem R_le_S (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    T.R γ u ≤ T.S γ u := by
  unfold CutTree.R CutTree.S
  rw [← sum_child_chords hT hu hn]
  exact norm_sum_le _ _

/-- Hypotheses on the tree used throughout: well-formedness, root chord `1`, `K > 0`. -/
structure TreeHyp (T : CutTree) (γ : ℝ → E) (K : ℕ) (ε ρ₀ : ℝ) : Prop where
  wf : T.WF γ K ε ρ₀
  root : T.R γ [] = 1
  Kpos : 0 < K

theorem R_pos_aux (hT : TreeHyp T γ K ε ρ₀) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n → 0 < T.R γ v := by
  induction n with
  | zero =>
    intro v _ hlen
    rw [List.eq_nil_of_length_eq_zero hlen, hT.root]
    exact one_pos
  | succ n ih =>
    intro v hv hlen
    rcases hT.wf.is_child v hv with rfl | ⟨u, hu, i, hi, rfl⟩
    · simp at hlen
    · have h1 := (hT.wf.scale u hu i hi).1
      have h2 := ih u hu (by simpa using hlen)
      have hK' : (0 : ℝ) < 2 * K := by
        have : (0 : ℝ) < K := Nat.cast_pos.2 hT.Kpos
        linarith
      exact lt_of_lt_of_le (div_pos h2 hK') h1

/-- All chords are nondegenerate. -/
theorem R_pos (hT : TreeHyp T γ K ε ρ₀) {v : List ℕ} (hv : v ∈ T.nodes) : 0 < T.R γ v :=
  R_pos_aux hT _ v hv rfl

theorem S_pos (hT : TreeHyp T γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    0 < T.S γ u :=
  lt_of_lt_of_le (R_pos hT hu) (R_le_S hT.wf hu hn)

/-- The log excess of an internal node is nonnegative. -/
theorem A_nonneg (hT : TreeHyp T γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    0 ≤ T.A γ u :=
  Real.log_nonneg ((one_le_div (R_pos hT hu)).2 (R_le_S hT.wf hu hn))

theorem q_sum (hT : TreeHyp T γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u = 1 := by
  rw [← Finset.sum_div]
  exact div_self (S_pos hT hu hn).ne'

theorem q_pos (hT : TreeHyp T γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) : 0 < T.R γ (u ++ [i]) / T.S γ u :=
  div_pos (R_pos hT (hT.wf.child_mem u hu i hi)) (S_pos hT hu (by omega))

theorem flow_nil : T.flow γ [] = 1 := by
  simp [CutTree.flow]

theorem flow_child (u : List ℕ) (i : ℕ) :
    T.flow γ (u ++ [i]) = T.flow γ u * (T.R γ (u ++ [i]) / T.S γ u) := by
  unfold CutTree.flow
  rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (l₂ := [i]) (show j + 1 ≤ u.length by omega),
      List.take_append_of_le_length (l₂ := [i]) (show j ≤ u.length by omega)]
  · have e1 : (u ++ [i]).take (u.length + 1) = u ++ [i] := List.take_of_length_le (by simp)
    have e2 : (u ++ [i]).take u.length = u := List.take_left
    rw [e1, e2]

theorem flow_pos_aux (hT : TreeHyp T γ K ε ρ₀) (n : ℕ) :
    ∀ v ∈ T.nodes, v.length = n → 0 < T.flow γ v := by
  induction n with
  | zero =>
    intro v _ hlen
    rw [List.eq_nil_of_length_eq_zero hlen, flow_nil]
    exact one_pos
  | succ n ih =>
    intro v hv hlen
    rcases hT.wf.is_child v hv with rfl | ⟨u, hu, i, hi, rfl⟩
    · simp at hlen
    · rw [flow_child]
      exact mul_pos (ih u hu (by simpa using hlen)) (q_pos hT hu hi)

/-- The flow is positive at every node. -/
theorem flow_pos (hT : TreeHyp T γ K ε ρ₀) {v : List ℕ} (hv : v ∈ T.nodes) : 0 < T.flow γ v :=
  flow_pos_aux hT _ v hv rfl

/-! ### Leaves below a node -/

/-- The leaves having `u` as a prefix. -/
def below (T : CutTree) (u : List ℕ) : Finset (List ℕ) := T.leaves.filter fun v => u <+: v

theorem mem_below {u v : List ℕ} : v ∈ below T u ↔ v ∈ T.leaves ∧ u <+: v :=
  Finset.mem_filter

theorem below_nil : below T [] = T.leaves :=
  Finset.filter_true_of_mem fun _ _ => List.nil_prefix

theorem below_leaf (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.leaves) : below T u = {u} := by
  ext v
  simp only [mem_below, Finset.mem_singleton]
  constructor
  · rintro ⟨hv, hp⟩
    by_contra hne
    obtain ⟨i, hi, -⟩ := exists_child_prefix hT (Finset.mem_filter.1 hv).1 hp (Ne.symm hne)
    rw [(Finset.mem_filter.1 hu).2] at hi
    exact Nat.not_lt_zero _ hi
  · rintro rfl
    exact ⟨hu, List.prefix_refl _⟩

theorem below_internal (hT : T.WF γ K ε ρ₀) {u : List ℕ} (_hu : u ∈ T.nodes)
    (hn : 0 < T.nch u) :
    below T u = (Finset.range (T.nch u)).biUnion fun i => below T (u ++ [i]) := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_range, mem_below]
  constructor
  · rintro ⟨hv, hp⟩
    have hne : u ≠ v := by
      rintro rfl
      rw [(Finset.mem_filter.1 hv).2] at hn
      exact lt_irrefl _ hn
    obtain ⟨i, hi, hpi⟩ := exists_child_prefix hT (Finset.mem_filter.1 hv).1 hp hne
    exact ⟨i, hi, hv, hpi⟩
  · rintro ⟨i, _, hv, hp⟩
    exact ⟨hv, (List.prefix_append u [i]).trans hp⟩

theorem below_disjoint (u : List ℕ) (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint fun i => below T (u ++ [i]) := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have h1 := (mem_below.1 hvi).2
  have h2 := (mem_below.1 hvj).2
  have : u ++ [i] = u ++ [j] := by
    rw [List.prefix_iff_eq_take] at h1 h2
    rw [h1, h2]
    simp
  simp at this
  exact hij this

theorem sum_below_internal (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes)
    (hn : 0 < T.nch u) (f : List ℕ → ℝ) :
    ∑ v ∈ below T u, f v = ∑ i ∈ Finset.range (T.nch u), ∑ v ∈ below T (u ++ [i]), f v := by
  rw [below_internal hT hu hn, Finset.sum_biUnion (below_disjoint u _)]

/-! ### Chain sums and the tree Jensen inequality -/

/-- `Σ_{v leaf below u} θ(v) Σ_{|u| ≤ j < |v|} Y(v.take j)`. -/
def chainSum (T : CutTree) (γ : ℝ → E) (Y : List ℕ → ℝ) (u : List ℕ) : ℝ :=
  ∑ v ∈ below T u, T.flow γ v * ∑ j ∈ Finset.Ico u.length v.length, Y (v.take j)

theorem chainSum_leaf (hT : T.WF γ K ε ρ₀) {Y : List ℕ → ℝ} {u : List ℕ} (hu : u ∈ T.leaves) :
    chainSum T γ Y u = 0 := by
  simp [chainSum, below_leaf hT hu]

theorem chainSum_internal (hT : T.WF γ K ε ρ₀) {Y : List ℕ → ℝ} {u : List ℕ}
    (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    chainSum T γ Y u = ∑ i ∈ Finset.range (T.nch u),
      ((∑ v ∈ below T (u ++ [i]), T.flow γ v) * Y u + chainSum T γ Y (u ++ [i])) := by
  unfold chainSum
  rw [sum_below_internal hT hu hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hp := (mem_below.1 hv).2
  have hlen : (u ++ [i]).length ≤ v.length := hp.length_le
  simp only [List.length_append, List.length_singleton] at hlen ⊢
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : u.length < v.length)]
  have : v.take u.length = u :=
    (List.prefix_iff_eq_take.1 ((List.prefix_append u [i]).trans hp)).symm
  rw [this]
  ring

/-- The inductive statement of the tree Jensen inequality at node `u`. -/
def Claim (T : CutTree) (γ : ℝ → E) (L F Y : List ℕ → ℝ) (u : List ℕ) : Prop :=
  ∑ v ∈ below T u, T.flow γ v = T.flow γ u ∧ 0 < L u ∧
    T.flow γ u * (Real.log (T.R γ u) + F u) + chainSum T γ Y u ≤ T.flow γ u * Real.log (L u)

theorem claim_leaf (hT : TreeHyp T γ K ε ρ₀) {L F Y : List ℕ → ℝ}
    (hLleaf : ∀ v ∈ T.leaves, T.R γ v * Real.exp (F v) ≤ L v) {u : List ℕ}
    (hu : u ∈ T.leaves) : Claim T γ L F Y u := by
  have hun : u ∈ T.nodes := (Finset.mem_filter.1 hu).1
  have hR := R_pos hT hun
  have hθ := flow_pos hT hun
  have hRe : 0 < T.R γ u * Real.exp (F u) := mul_pos hR (Real.exp_pos _)
  have hL : 0 < L u := lt_of_lt_of_le hRe (hLleaf u hu)
  refine ⟨by simp [below_leaf hT.wf hu], hL, ?_⟩
  rw [chainSum_leaf hT.wf hu, add_zero]
  refine mul_le_mul_of_nonneg_left ?_ hθ.le
  have := Real.log_le_log hRe (hLleaf u hu)
  rwa [Real.log_mul hR.ne' (Real.exp_pos _).ne', Real.log_exp] at this

theorem claim_internal (hT : TreeHyp T γ K ε ρ₀) {L F Y : List ℕ → ℝ}
    (hLsum : ∀ u ∈ T.nodes, 0 < T.nch u → L u = ∑ i ∈ Finset.range (T.nch u), L (u ++ [i]))
    (hY : ∀ u ∈ T.nodes, 0 < T.nch u → Y u ≤ T.A γ u +
      (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u * F (u ++ [i]) - F u))
    {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u)
    (ih : ∀ i < T.nch u, Claim T γ L F Y (u ++ [i])) : Claim T γ L F Y u := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℝ, ∀ i, q i = T.R γ (u ++ [i]) / T.S γ u := ⟨_, fun _ => rfl⟩
  have hR := R_pos hT hu
  have hSpos := S_pos hT hu hn
  have hθ := flow_pos hT hu
  have hRi : ∀ i ∈ Finset.range (T.nch u), 0 < T.R γ (u ++ [i]) := fun i hi =>
    R_pos hT (hT.wf.child_mem u hu i (Finset.mem_range.1 hi))
  have hq_pos : ∀ i ∈ Finset.range (T.nch u), 0 < q i := fun i hi => by
    rw [hq]; exact q_pos hT hu (Finset.mem_range.1 hi)
  have hq_sum : ∑ i ∈ Finset.range (T.nch u), q i = 1 := by
    simp only [hq]; exact q_sum hT hu hn
  have hθi : ∀ i, T.flow γ (u ++ [i]) = T.flow γ u * q i := fun i => by
    rw [hq]; exact flow_child u i
  have hsum_i : ∀ i ∈ Finset.range (T.nch u),
      ∑ v ∈ below T (u ++ [i]), T.flow γ v = T.flow γ u * q i := fun i hi =>
    (ih i (Finset.mem_range.1 hi)).1.trans (hθi i)
  have hLi : ∀ i ∈ Finset.range (T.nch u), 0 < L (u ++ [i]) := fun i hi =>
    (ih i (Finset.mem_range.1 hi)).2.1
  -- flow conservation
  have hflow : ∑ v ∈ below T u, T.flow γ v = T.flow γ u := by
    rw [sum_below_internal hT.wf hu hn, Finset.sum_congr rfl hsum_i, ← Finset.mul_sum, hq_sum,
      mul_one]
  -- additivity and positivity of `L`
  have hLu : L u = ∑ i ∈ Finset.range (T.nch u), L (u ++ [i]) := hLsum u hu hn
  have hLpos : 0 < L u := by
    rw [hLu]; exact Finset.sum_pos hLi (Finset.nonempty_range_iff.2 hn.ne')
  refine ⟨hflow, hLpos, ?_⟩
  -- chain sums
  have hchain : chainSum T γ Y u =
      T.flow γ u * Y u + ∑ i ∈ Finset.range (T.nch u), chainSum T γ Y (u ++ [i]) := by
    rw [chainSum_internal hT.wf hu hn, Finset.sum_add_distrib]
    congr 1
    calc ∑ i ∈ Finset.range (T.nch u), (∑ v ∈ below T (u ++ [i]), T.flow γ v) * Y u
        = ∑ i ∈ Finset.range (T.nch u), T.flow γ u * q i * Y u :=
          Finset.sum_congr rfl fun i hi => by rw [hsum_i i hi]
      _ = T.flow γ u * Y u := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hq_sum, mul_one]
  -- induction hypotheses, rearranged
  have hIH : ∀ i ∈ Finset.range (T.nch u), chainSum T γ Y (u ++ [i]) ≤
      T.flow γ u * (q i * (Real.log (L (u ++ [i])) - Real.log (T.R γ (u ++ [i])) -
        F (u ++ [i]))) := by
    intro i hi
    have h := (ih i (Finset.mem_range.1 hi)).2.2
    rw [hθi i] at h
    linarith
  -- Jensen for the concave logarithm with weights `q`
  have hJ : ∑ i ∈ Finset.range (T.nch u), q i * Real.log (L (u ++ [i]) / q i) ≤
      Real.log (L u) := by
    have := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := Finset.range (T.nch u))
      (w := q) (p := fun i => L (u ++ [i]) / q i) (fun i hi => (hq_pos i hi).le) hq_sum
      (fun i hi => div_pos (hLi i hi) (hq_pos i hi))
    simp only [smul_eq_mul] at this
    rw [hLu]
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have := (hq_pos i hi).ne'
    field_simp
  have hlogq : ∀ i ∈ Finset.range (T.nch u), q i * Real.log (L (u ++ [i]) / q i) =
      q i * (Real.log (L (u ++ [i])) - Real.log (T.R γ (u ++ [i])) - F (u ++ [i])) +
        q i * F (u ++ [i]) + q i * Real.log (T.S γ u) := by
    intro i hi
    rw [Real.log_div (hLi i hi).ne' (hq_pos i hi).ne', hq,
      Real.log_div (hRi i hi).ne' hSpos.ne']
    ring
  have e2 : ∑ i ∈ Finset.range (T.nch u), q i * Real.log (L (u ++ [i]) / q i) =
      ∑ i ∈ Finset.range (T.nch u),
          q i * (Real.log (L (u ++ [i])) - Real.log (T.R γ (u ++ [i])) - F (u ++ [i])) +
        ∑ i ∈ Finset.range (T.nch u), q i * F (u ++ [i]) + Real.log (T.S γ u) := by
    rw [Finset.sum_congr rfl hlogq, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, hq_sum, one_mul]
  have hA : T.A γ u = Real.log (T.S γ u) - Real.log (T.R γ u) :=
    Real.log_div hSpos.ne' hR.ne'
  have hYu := hY u hu hn
  simp only [← hq] at hYu
  rw [hA] at hYu
  have h1 := mul_le_mul_of_nonneg_left hYu hθ.le
  have h2 := mul_le_mul_of_nonneg_left hJ hθ.le
  rw [e2] at h2
  have h3 : ∑ i ∈ Finset.range (T.nch u), chainSum T γ Y (u ++ [i]) ≤
      T.flow γ u * ∑ i ∈ Finset.range (T.nch u),
        q i * (Real.log (L (u ++ [i])) - Real.log (T.R γ (u ++ [i])) - F (u ++ [i])) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hIH
  rw [hchain]
  linarith

theorem claim_all (hT : TreeHyp T γ K ε ρ₀) {L F Y : List ℕ → ℝ}
    (hLsum : ∀ u ∈ T.nodes, 0 < T.nch u → L u = ∑ i ∈ Finset.range (T.nch u), L (u ++ [i]))
    (hLleaf : ∀ v ∈ T.leaves, T.R γ v * Real.exp (F v) ≤ L v)
    (hY : ∀ u ∈ T.nodes, 0 < T.nch u → Y u ≤ T.A γ u +
      (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u * F (u ++ [i]) - F u)) :
    ∀ u ∈ T.nodes, Claim T γ L F Y u := by
  suffices H : ∀ m : ℕ, ∀ u ∈ T.nodes, T.nodes.sup List.length - u.length ≤ m →
      Claim T γ L F Y u from fun u hu => H _ u hu le_rfl
  intro m
  induction m with
  | zero =>
    intro u hu hm
    have hleaf : T.nch u = 0 := by
      by_contra h
      have hc := hT.wf.child_mem u hu 0 (Nat.pos_of_ne_zero h)
      have := Finset.le_sup (f := List.length) hc
      simp only [List.length_append, List.length_singleton] at this
      omega
    exact claim_leaf hT hLleaf (Finset.mem_filter.2 ⟨hu, hleaf⟩)
  | succ m ih =>
    intro u hu hm
    by_cases hleaf : T.nch u = 0
    · exact claim_leaf hT hLleaf (Finset.mem_filter.2 ⟨hu, hleaf⟩)
    · refine claim_internal hT hLsum hY hu (Nat.pos_of_ne_zero hleaf) fun i hi =>
        ih _ (hT.wf.child_mem u hu i hi) ?_
      have := Finset.le_sup (f := List.length) (hT.wf.child_mem u hu i hi)
      simp only [List.length_append, List.length_singleton] at this ⊢
      omega

/-- **Tree Jensen inequality** at the root (HA3 D2, steps 3–4): flow conservation, positivity
of `L`, and `F [] + Σ_v θ(v) Σ_{u ≺ v} Y u ≤ log L []`. -/
theorem tree_jensen_root (hT : TreeHyp T γ K ε ρ₀) {L F Y : List ℕ → ℝ}
    (hLsum : ∀ u ∈ T.nodes, 0 < T.nch u → L u = ∑ i ∈ Finset.range (T.nch u), L (u ++ [i]))
    (hLleaf : ∀ v ∈ T.leaves, T.R γ v * Real.exp (F v) ≤ L v)
    (hY : ∀ u ∈ T.nodes, 0 < T.nch u → Y u ≤ T.A γ u +
      (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u * F (u ++ [i]) - F u)) :
    ∑ v ∈ T.leaves, T.flow γ v = 1 ∧ 0 < L [] ∧
      F [] + ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length, Y (v.take j) ≤
        Real.log (L []) := by
  obtain ⟨hs, hL, hineq⟩ := claim_all hT hLsum hLleaf hY [] hT.wf.root_mem
  rw [below_nil, flow_nil] at hs
  refine ⟨hs, hL, ?_⟩
  unfold chainSum at hineq
  simp only [below_nil, flow_nil, hT.root, Real.log_one, zero_add, one_mul,
    List.length_nil, Nat.Ico_zero_eq_range] at hineq
  exact hineq

end Tree

end TreeJensen

end HigherDimLFPP.Upper
