import SupercriticalLFPPAS.Contraction.ChainJoin
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PaidTraces

/-!
# The alternating chain of Lemma 4.1 (SB2 D6 step 8)

The real pieces of Lemma 4.1 in time order are `γ^H_0, γ^G_0, γ^H_1, …, γ^G_{k−1}, γ^H_k` (prior-comparison curves
on the complementary segments `H_i`, good-scale curves on the crossings `G_i`); between `γ^H_i` and `γ^G_i` sits the
target separator `σ^s_i` around `P(s_i)`, between `γ^G_i` and `γ^H_{i+1}` the separator `σ^t_i` around `P(t_i)`. The
loose ends at each junction lie in the bounded complementary component of the separator (paper l. 440–445).

`l41_join` applies chain lemma J (`ChainJoin.lean`) to this configuration: the node type `L41Node` has the real
nodes `hp i`, `gp i`, `js i`, `jt i` and the virtual nodes `vs i`, `vt i` (the components); the initial chain
`hp 0, vs 0, gp 0, vt 0, hp 1, …, hp k` goes from `B₀` to `B₁`; removing the virtual nodes leaves a chain of real
nodes, and the internal set distance is at most the total length of all real pieces.

Also: `l41_component_subset_closedBall` (SB2 D2, T3: a bounded complementary component of a set inside a closed ball
lies in the ball) and `l41_ball_not_subset_closedBall` (a large ball is not inside a small one).
-/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Contraction

open SupercriticalLQGUniqueness

/-- **T3** (SB2 D2): a bounded complementary component of a set contained in a closed ball lies in that ball. -/
theorem l41_component_subset_closedBall {K : Set ℂ} {x p : ℂ} {M : ℝ} (hKM : K ⊆ closedBall p M)
    (hM : 0 ≤ M) (hV : Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
    connectedComponentIn Kᶜ x ⊆ closedBall p M := by
  intro z hz
  by_contra hzM
  have hunb : ¬ Bornology.IsBounded (connectedComponentIn (closedBall p M)ᶜ z) :=
    LQGMetric.not_isBounded_connectedComponentIn_compl_of_convex (convex_closedBall p M)
      (mem_closedBall_self hM) hzM
  have hsub : connectedComponentIn (closedBall p M)ᶜ z ⊆ connectedComponentIn Kᶜ x := by
    have hmono := connectedComponentIn_mono z (compl_subset_compl.mpr hKM)
    rw [← connectedComponentIn_eq hz] at hmono
    exact hmono
  exact hunb (hV.subset hsub)

/-- An open ball of radius `ρ > 2M ≥ 0` is not contained in a closed ball of radius `M`. -/
theorem l41_ball_not_subset_closedBall {z p : ℂ} {ρ M : ℝ} (hM : 0 ≤ M) (hρ : 2 * M < ρ) :
    ¬ ball z ρ ⊆ closedBall p M := by
  intro hsub
  set t : ℝ := (2 * M + ρ) / 2 with ht
  have hρpos : 0 < ρ := by linarith
  have hz : z ∈ closedBall p M := hsub (mem_ball_self hρpos)
  have hzt_dist : dist (z + (t : ℂ)) z = t := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by rw [ht]; linarith)]
  have hzt : z + (t : ℂ) ∈ closedBall p M := hsub (by
    rw [mem_ball, hzt_dist, ht]
    linarith)
  have h1 := dist_triangle (z + (t : ℂ)) p z
  rw [hzt_dist, dist_comm p z] at h1
  have h2 : dist (z + (t : ℂ)) p ≤ M := hzt
  have h3 : dist z p ≤ M := hz
  rw [ht] at h1
  linarith

/-- The nodes of the alternating chain: real pieces `hp i` (`γ^H_i`), `gp i` (`γ^G_i`), real separators `js i`
(`σ^s_i`), `jt i` (`σ^t_i`), and virtual nodes `vs i`, `vt i` (the bounded components of the separators). -/
inductive L41Node
  | hp : ℕ → L41Node
  | gp : ℕ → L41Node
  | js : ℕ → L41Node
  | jt : ℕ → L41Node
  | vs : ℕ → L41Node
  | vt : ℕ → L41Node
  deriving DecidableEq

/-- The curves of the alternating chain: `k` crossings, `k + 1` complementary pieces, `2k` separators with their
centres `ps i = P(s_i)`, `pt i = P(t_i)`. -/
structure L41Pieces where
  k : ℕ
  γH : ℕ → ℝ → ℂ
  aH : ℕ → ℝ
  bH : ℕ → ℝ
  γG : ℕ → ℝ → ℂ
  aG : ℕ → ℝ
  bG : ℕ → ℝ
  σs : ℕ → ℝ → ℂ
  aS : ℕ → ℝ
  bS : ℕ → ℝ
  ps : ℕ → ℂ
  σt : ℕ → ℝ → ℂ
  aT : ℕ → ℝ
  bT : ℕ → ℝ
  pt : ℕ → ℂ

namespace L41Pieces

/-- The set of a node: a curve trace for a real node, the bounded component for a virtual node. -/
def S (Q : L41Pieces) : L41Node → Set ℂ
  | .hp i => Q.γH i '' Icc (Q.aH i) (Q.bH i)
  | .gp i => Q.γG i '' Icc (Q.aG i) (Q.bG i)
  | .js i => Q.σs i '' Icc (Q.aS i) (Q.bS i)
  | .jt i => Q.σt i '' Icc (Q.aT i) (Q.bT i)
  | .vs i => connectedComponentIn (Q.σs i '' Icc (Q.aS i) (Q.bS i))ᶜ (Q.ps i)
  | .vt i => connectedComponentIn (Q.σt i '' Icc (Q.aT i) (Q.bT i))ᶜ (Q.pt i)

/-- The cost of a node: the target length of a real node, `0` for a virtual node. -/
def cost (D : LSCMetric) (Q : L41Pieces) : L41Node → ℝ≥0∞
  | .hp i => D.len (Q.γH i) (Q.aH i) (Q.bH i)
  | .gp i => D.len (Q.γG i) (Q.aG i) (Q.bG i)
  | .js i => D.len (Q.σs i) (Q.aS i) (Q.bS i)
  | .jt i => D.len (Q.σt i) (Q.aT i) (Q.bT i)
  | .vs _ => 0
  | .vt _ => 0

/-- The hypotheses of the alternating chain: the curves are target curves in `W`, Euclidean continuous; no endpoint
set lies in a separator's component; the loose ends at each junction lie in the component; the chain starts in `B₀`
and ends in `B₁`. -/
structure Valid (D : LSCMetric) (W B₀ B₁ : Set ℂ) (Q : L41Pieces) : Prop where
  hH : ∀ i ≤ Q.k, D.IsCurve (Q.γH i) (Q.aH i) (Q.bH i) ∧
    ContinuousOn (Q.γH i) (Icc (Q.aH i) (Q.bH i)) ∧ ∀ u ∈ Icc (Q.aH i) (Q.bH i), Q.γH i u ∈ W
  hG : ∀ i < Q.k, D.IsCurve (Q.γG i) (Q.aG i) (Q.bG i) ∧
    ContinuousOn (Q.γG i) (Icc (Q.aG i) (Q.bG i)) ∧ ∀ u ∈ Icc (Q.aG i) (Q.bG i), Q.γG i u ∈ W
  hS : ∀ i < Q.k, D.IsCurve (Q.σs i) (Q.aS i) (Q.bS i) ∧
    ContinuousOn (Q.σs i) (Icc (Q.aS i) (Q.bS i)) ∧ (∀ u ∈ Icc (Q.aS i) (Q.bS i), Q.σs i u ∈ W) ∧
    ¬ B₀ ⊆ Q.S (.vs i) ∧ ¬ B₁ ⊆ Q.S (.vs i) ∧
    Q.γH i (Q.bH i) ∈ Q.S (.vs i) ∧ Q.γG i (Q.aG i) ∈ Q.S (.vs i)
  hT : ∀ i < Q.k, D.IsCurve (Q.σt i) (Q.aT i) (Q.bT i) ∧
    ContinuousOn (Q.σt i) (Icc (Q.aT i) (Q.bT i)) ∧ (∀ u ∈ Icc (Q.aT i) (Q.bT i), Q.σt i u ∈ W) ∧
    ¬ B₀ ⊆ Q.S (.vt i) ∧ ¬ B₁ ⊆ Q.S (.vt i) ∧
    Q.γG i (Q.bG i) ∈ Q.S (.vt i) ∧ Q.γH (i + 1) (Q.aH (i + 1)) ∈ Q.S (.vt i)
  start : Q.γH 0 (Q.aH 0) ∈ B₀
  finish : Q.γH Q.k (Q.bH Q.k) ∈ B₁

end L41Pieces

/-- The separator node of a virtual node. -/
def l41Jn : L41Node → L41Node
  | .vs i => .js i
  | .vt i => .jt i
  | u => u

/-- A finite sum over a union is at most the sum of the two sums (nonnegative values). -/
theorem l41_sum_union_le {ι : Type*} [DecidableEq ι] (s t : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter]
  exact le_self_add

/-- **The alternating chain bound** (SB2 D6 step 8 with chain lemma J): the internal set distance between `B₀` and
`B₁` is at most the total length of all real pieces and all separators. -/
theorem l41_join (D : LSCMetric) (W : Set ℂ) {B₀ B₁ : Set ℂ} (hB₀ : IsPreconnected B₀)
    (hB₁ : IsPreconnected B₁) (Q : L41Pieces) (hQ : Q.Valid D W B₀ B₁) :
    D.internalSetDist W {y | (y : ℂ) ∈ B₀} {y | (y : ℂ) ∈ B₁} ≤
      (∑ i ∈ Finset.range (Q.k + 1), D.len (Q.γH i) (Q.aH i) (Q.bH i) +
        ∑ i ∈ Finset.range Q.k, D.len (Q.γG i) (Q.aG i) (Q.bG i)) +
      (∑ i ∈ Finset.range Q.k, D.len (Q.σs i) (Q.aS i) (Q.bS i) +
        ∑ i ∈ Finset.range Q.k, D.len (Q.σt i) (Q.aT i) (Q.bT i)) := by
  classical
  set M : Finset L41Node :=
    (Finset.range (Q.k + 1)).image L41Node.hp ∪ (Finset.range Q.k).image L41Node.gp with hM
  set V : Finset L41Node :=
    (Finset.range Q.k).image L41Node.vs ∪ (Finset.range Q.k).image L41Node.vt with hV
  have hpM : ∀ i ≤ Q.k, L41Node.hp i ∈ M ∪ V := fun i hi =>
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))))
  have hgM : ∀ i < Q.k, L41Node.gp i ∈ M ∪ V := fun i hi =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)))
  have hvsV : ∀ i < Q.k, L41Node.vs i ∈ M ∪ V := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)))
  have hvtV : ∀ i < Q.k, L41Node.vt i ∈ M ∪ V := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)))
  have hHmem : ∀ i ≤ Q.k, Q.aH i ∈ Icc (Q.aH i) (Q.bH i) ∧ Q.bH i ∈ Icc (Q.aH i) (Q.bH i) :=
    fun i hi => ⟨⟨le_rfl, (hQ.hH i hi).1.1⟩, ⟨(hQ.hH i hi).1.1, le_rfl⟩⟩
  have hGmem : ∀ i < Q.k, Q.aG i ∈ Icc (Q.aG i) (Q.bG i) ∧ Q.bG i ∈ Icc (Q.aG i) (Q.bG i) :=
    fun i hi => ⟨⟨le_rfl, (hQ.hG i hi).1.1⟩, ⟨(hQ.hG i hi).1.1, le_rfl⟩⟩
  -- the initial chain `hp 0, vs 0, gp 0, vt 0, hp 1, …, hp k`
  have hreach : ∀ i ≤ Q.k, Relation.ReflTransGen (L41Rel Q.S (M ∪ V)) (.hp 0) (.hp i) := by
    intro i
    induction i with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ i ih =>
      intro hi
      have hik : i < Q.k := by omega
      have h1 : L41Rel Q.S (M ∪ V) (.hp i) (.vs i) :=
        ⟨hpM i hik.le, hvsV i hik, ⟨Q.γH i (Q.bH i), ⟨Q.bH i, (hHmem i hik.le).2, rfl⟩,
          (hQ.hS i hik).2.2.2.2.2.1⟩⟩
      have h2 : L41Rel Q.S (M ∪ V) (.vs i) (.gp i) :=
        ⟨hvsV i hik, hgM i hik, ⟨Q.γG i (Q.aG i), (hQ.hS i hik).2.2.2.2.2.2,
          ⟨Q.aG i, (hGmem i hik).1, rfl⟩⟩⟩
      have h3 : L41Rel Q.S (M ∪ V) (.gp i) (.vt i) :=
        ⟨hgM i hik, hvtV i hik, ⟨Q.γG i (Q.bG i), ⟨Q.bG i, (hGmem i hik).2, rfl⟩,
          (hQ.hT i hik).2.2.2.2.2.1⟩⟩
      have h4 : L41Rel Q.S (M ∪ V) (.vt i) (.hp (i + 1)) :=
        ⟨hvtV i hik, hpM (i + 1) hi, ⟨Q.γH (i + 1) (Q.aH (i + 1)), (hQ.hT i hik).2.2.2.2.2.2,
          ⟨Q.aH (i + 1), (hHmem (i + 1) hi).1, rfl⟩⟩⟩
      exact ((((ih hik.le).tail h1).tail h2).tail h3).tail h4
  have hch0 : L41Chain Q.S (M ∪ V) B₀ B₁ :=
    ⟨.hp 0, hpM 0 (Nat.zero_le _), .hp Q.k, hpM Q.k le_rfl,
      ⟨Q.γH 0 (Q.aH 0), ⟨Q.aH 0, (hHmem 0 (Nat.zero_le _)).1, rfl⟩, hQ.start⟩,
      ⟨Q.γH Q.k (Q.bH Q.k), ⟨Q.bH Q.k, (hHmem Q.k le_rfl).2, rfl⟩, hQ.finish⟩,
      hreach Q.k le_rfl⟩
  -- the hypotheses of chain lemma J
  have hVdata : ∀ v ∈ V, IsPreconnected (Q.S v) ∧ IsPreconnected (Q.S (l41Jn v)) ∧
      (∀ Z : Set ℂ, IsPreconnected Z → Disjoint Z (Q.S (l41Jn v)) → (Z ∩ Q.S v).Nonempty →
        Z ⊆ Q.S v) ∧ ¬ B₀ ⊆ Q.S v ∧ ¬ B₁ ⊆ Q.S v := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      have hik := Finset.mem_range.mp hi
      obtain ⟨hc, hcont, _, hB₀i, hB₁i, _, _⟩ := hQ.hS i hik
      refine ⟨isPreconnected_connectedComponentIn, isPreconnected_Icc.image _ hcont, ?_, hB₀i, hB₁i⟩
      intro Z hZ hdisj hmeet
      exact Uniqueness.Toolkit.PlanarSeparation.preconnected_subset_component_of_meets hZ
        hdisj.subset_compl_right hmeet
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      have hik := Finset.mem_range.mp hi
      obtain ⟨hc, hcont, _, hB₀i, hB₁i, _, _⟩ := hQ.hT i hik
      refine ⟨isPreconnected_connectedComponentIn, isPreconnected_Icc.image _ hcont, ?_, hB₀i, hB₁i⟩
      intro Z hZ hdisj hmeet
      exact Uniqueness.Toolkit.PlanarSeparation.preconnected_subset_component_of_meets hZ
        hdisj.subset_compl_right hmeet
  have hMdata : ∀ u ∈ M, IsPreconnected (Q.S u) := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact isPreconnected_Icc.image _ (hQ.hH i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2.1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact isPreconnected_Icc.image _ (hQ.hG i (Finset.mem_range.mp hi)).2.1
  have hch1 := l41_chain_remove_virtual Q.S l41Jn hB₀ hB₁ V hVdata M hMdata hch0
  -- every node of `M ∪ jn(V)` is real
  have hreal : ∀ u ∈ M ∪ V.image l41Jn, ∃ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b ∧
      (∀ t ∈ Icc a b, γ t ∈ W) ∧ Q.S u = γ '' Icc a b ∧ Q.cost D u = D.len γ a b := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
        have h := hQ.hH i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        exact ⟨Q.γH i, Q.aH i, Q.bH i, h.1, h.2.2, rfl, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
        have h := hQ.hG i (Finset.mem_range.mp hi)
        exact ⟨Q.γG i, Q.aG i, Q.bG i, h.1, h.2.2, rfl, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        have h := hQ.hS i (Finset.mem_range.mp hi)
        exact ⟨Q.σs i, Q.aS i, Q.bS i, h.1, h.2.2.1, rfl, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        have h := hQ.hT i (Finset.mem_range.mp hi)
        exact ⟨Q.σt i, Q.aT i, Q.bT i, h.1, h.2.2.1, rfl, rfl⟩
  have hSW : ∀ u ∈ M ∪ V.image l41Jn, Q.S u ⊆ W := by
    intro u hu
    obtain ⟨γ, a, b, _, hW, hSu, _⟩ := hreal u hu
    rw [hSu]
    rintro _ ⟨t, ht, rfl⟩
    exact hW t ht
  have hcost : ∀ u ∈ M ∪ V.image l41Jn, ∀ x y : ℂ, ∀ (hx : x ∈ W) (hy : y ∈ W),
      x ∈ Q.S u → y ∈ Q.S u → D.internal W (⟨x, hx⟩, ⟨y, hy⟩) ≤ Q.cost D u := by
    intro u hu x y hx hy hxu hyu
    obtain ⟨γ, a, b, hγ, hW, hSu, hcu⟩ := hreal u hu
    rw [hSu] at hxu hyu
    rw [hcu]
    exact l41_trace_internal_le D hγ hW hx hy hxu hyu
  refine (l41_internalSetDist_le_of_chain D W Q.S (Q.cost D) _ hSW hcost hch1).trans ?_
  -- the sum over the final node set
  have hsumM : ∑ u ∈ M, Q.cost D u ≤
      ∑ i ∈ Finset.range (Q.k + 1), D.len (Q.γH i) (Q.aH i) (Q.bH i) +
        ∑ i ∈ Finset.range Q.k, D.len (Q.γG i) (Q.aG i) (Q.bG i) := by
    refine (l41_sum_union_le _ _ _).trans (add_le_add ?_ ?_)
    · exact (Finset.sum_image_le_of_nonneg (fun _ _ => zero_le)).trans le_rfl
    · exact (Finset.sum_image_le_of_nonneg (fun _ _ => zero_le)).trans le_rfl
  have hsumV : ∑ u ∈ V.image l41Jn, Q.cost D u ≤
      ∑ i ∈ Finset.range Q.k, D.len (Q.σs i) (Q.aS i) (Q.bS i) +
        ∑ i ∈ Finset.range Q.k, D.len (Q.σt i) (Q.aT i) (Q.bT i) := by
    refine (Finset.sum_image_le_of_nonneg (fun _ _ => zero_le)).trans ?_
    refine (l41_sum_union_le _ _ _).trans (add_le_add ?_ ?_)
    · exact (Finset.sum_image_le_of_nonneg (fun _ _ => zero_le)).trans le_rfl
    · exact (Finset.sum_image_le_of_nonneg (fun _ _ => zero_le)).trans le_rfl
  exact (l41_sum_union_le _ _ _).trans (add_le_add hsumM hsumV)

end SupercriticalLFPPAS.Contraction
