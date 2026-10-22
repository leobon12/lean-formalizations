import LQGMetric.Metric.CurveLength
import LQGMetric.Metric.Internal

/-!
# Partition suprema, lengths for arbitrary distance functions, induced internal distances

Packet M1 (Phase A, block A2): the generic layer behind the source's Lemma 2.1 (blueprint
`s2-compact.tex`, Lemma `lem:21`; MA1 A2), for an arbitrary type `X`.

* `IccPartition a b`: partitions `a = t 0 ≤ t 1 ≤ ⋯ ≤ t n = b`; `IccPartition.single` (one
  interval) and `IccPartition.append` (concatenation).
* `partitionSup g a b`: the supremum over partitions of `∑ g (t i) (t (i + 1))`, for any
  `g : ℝ → ℝ → [0, ∞]`. Superadditivity over adjacent intervals (`partitionSup_add_le`, by
  concatenation; `sum_partitionSup_le` for a chain), and additivity when `g` increases under
  subdivision (`partitionSup_le_add`, `partitionSup_add`, by inserting the junction point);
  monotonicity in `g` (`partitionSup_mono`), constants (`partitionSup_const_mul`).
* `curveLengthWith δ P a b` (MA1's shape, `curveLengthWith_eq_iSup`): the length of the curve
  `P : ℝ → X` on `[a, b]` measured with an arbitrary `δ : X → X → [0, ∞]`; for `δ = edist` it is
  LQGMetric's `curveLength` (`curveLengthWith_edist`); comparison of distance functions
  (`curveLengthWith_mono`, `curveLengthWith_const_mul`), additivity.
* `internalWith δ S x y`: the infimum of `curveLengthWith δ P 0 1` over continuous curves
  `P : [0, 1] → S` from `x` to `y` (the internal distance of `S` induced by `δ`); for
  `δ = edist` it is LQGMetric's `internalEDist` (`internalWith_edist`).

Elementary partition arguments (BBI §2.3); own proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-! ### Partitions -/

/-- A partition `a = t 0 ≤ t 1 ≤ ⋯ ≤ t n = b` of `[a, b]` (the values `t i`, `i > n`, are
irrelevant). -/
structure IccPartition (a b : ℝ) where
  /-- the number of intervals -/
  n : ℕ
  /-- the partition points -/
  t : ℕ → ℝ
  mono : MonotoneOn t (Iic n)
  zero : t 0 = a
  last : t n = b

namespace IccPartition

variable {a b c : ℝ}

/-- The partition sum `∑_{i < n} g (t i) (t (i + 1))`. -/
def sum (p : IccPartition a b) (g : ℝ → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range p.n, g (p.t i) (p.t (i + 1))

theorem le_t (p : IccPartition a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.n) : p.t i ≤ p.t j :=
  p.mono (mem_Iic.2 (hij.trans hj)) (mem_Iic.2 hj) hij

theorem mem_Icc (p : IccPartition a b) {i : ℕ} (hi : i ≤ p.n) : p.t i ∈ Icc a b := by
  have h1 := p.le_t (Nat.zero_le i) hi
  have h2 := p.le_t hi le_rfl
  rw [p.zero] at h1
  rw [p.last] at h2
  exact ⟨h1, h2⟩

theorem le (p : IccPartition a b) : a ≤ b := by
  have := p.le_t (Nat.zero_le p.n) le_rfl
  rwa [p.zero, p.last] at this

/-- Consecutive partition points lie in `[a, b]` in increasing order. -/
theorem step (p : IccPartition a b) {i : ℕ} (hi : i < p.n) :
    a ≤ p.t i ∧ p.t i ≤ p.t (i + 1) ∧ p.t (i + 1) ≤ b :=
  ⟨(p.mem_Icc hi.le).1, p.le_t (Nat.le_succ i) hi, (p.mem_Icc hi).2⟩

/-- The partition with one interval. -/
def single (hab : a ≤ b) : IccPartition a b where
  n := 1
  t i := if i = 0 then a else b
  mono := by
    intro i _ j _ hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp [hi, hj, hab]
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  zero := by simp
  last := by simp

theorem single_sum (hab : a ≤ b) (g : ℝ → ℝ → ℝ≥0∞) : (single hab).sum g = g a b := by
  simp [sum, single]

/-- Concatenation of a partition of `[a, b]` and a partition of `[b, c]`. -/
def append (p : IccPartition a b) (q : IccPartition b c) : IccPartition a c where
  n := p.n + q.n
  t i := if i ≤ p.n then p.t i else q.t (i - p.n)
  mono := by
    intro i hi j hj hij
    simp only [mem_Iic] at hi hj
    dsimp only
    by_cases hip : i ≤ p.n
    · by_cases hjp : j ≤ p.n
      · rw [ite_eq_left hip, ite_eq_left hjp]; exact p.le_t hij hjp
      · rw [ite_eq_left hip, ite_eq_right hjp]
        calc p.t i ≤ p.t p.n := p.le_t hip le_rfl
          _ = q.t 0 := p.last.trans q.zero.symm
          _ ≤ q.t (j - p.n) := q.le_t (Nat.zero_le _) (by omega)
    · have hjp : ¬j ≤ p.n := by omega
      rw [ite_eq_right hip, ite_eq_right hjp]
      exact q.le_t (by omega) (by omega)
  zero := by simp [p.zero]
  last := by
    by_cases hq : q.n = 0
    · have h1 := q.last
      rw [hq, q.zero] at h1
      rw [hq, add_zero, ite_eq_left le_rfl, p.last, h1]
    · rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, q.last]

theorem append_t_add (p : IccPartition a b) (q : IccPartition b c) (k : ℕ) :
    (p.append q).t (p.n + k) = q.t k := by
  show (if p.n + k ≤ p.n then p.t (p.n + k) else q.t (p.n + k - p.n)) = q.t k
  by_cases hk : k = 0
  · subst hk; rw [ite_eq_left (by omega), add_zero, p.last, q.zero]
  · rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

theorem append_t_of_le (p : IccPartition a b) (q : IccPartition b c) {i : ℕ} (hi : i ≤ p.n) :
    (p.append q).t i = p.t i := by
  show (if i ≤ p.n then p.t i else q.t (i - p.n)) = p.t i
  rw [ite_eq_left hi]

theorem append_sum (p : IccPartition a b) (q : IccPartition b c) (g : ℝ → ℝ → ℝ≥0∞) :
    (p.append q).sum g = p.sum g + q.sum g := by
  unfold sum
  rw [show (p.append q).n = p.n + q.n from rfl, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [append_t_of_le p q hi.le, append_t_of_le p q hi]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [append_t_add, show p.n + k + 1 = p.n + (k + 1) by ring, append_t_add]

end IccPartition

/-! ### Partition suprema -/

/-- `partitionSup g a b`: the supremum over partitions `a = t 0 ≤ ⋯ ≤ t n = b` of
`∑ g (t i) (t (i + 1))` (`0` if `b < a`, when there is no partition). -/
def partitionSup (g : ℝ → ℝ → ℝ≥0∞) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ p : IccPartition a b, p.sum g

section PartitionSup

variable {g g' : ℝ → ℝ → ℝ≥0∞} {a b c : ℝ}

theorem le_partitionSup (p : IccPartition a b) : p.sum g ≤ partitionSup g a b :=
  le_iSup (fun p : IccPartition a b => p.sum g) p

theorem partitionSup_le {e : ℝ≥0∞} (h : ∀ p : IccPartition a b, p.sum g ≤ e) :
    partitionSup g a b ≤ e :=
  iSup_le h

/-- The literal nested form (MA1's shape). -/
theorem partitionSup_eq_iSup (g : ℝ → ℝ → ℝ≥0∞) (a b : ℝ) :
    partitionSup g a b = ⨆ (n : ℕ) (t : ℕ → ℝ) (_ : MonotoneOn t (Iic n)) (_ : t 0 = a)
      (_ : t n = b), ∑ i ∈ Finset.range n, g (t i) (t (i + 1)) := by
  apply le_antisymm
  · exact partitionSup_le fun p => le_iSup_of_le p.n <| le_iSup_of_le p.t <|
      le_iSup_of_le p.mono <| le_iSup_of_le p.zero <| le_iSup_of_le p.last le_rfl
  · exact iSup_le fun n => iSup_le fun t => iSup_le fun ht => iSup_le fun h0 => iSup_le fun hn =>
      le_partitionSup (g := g) ⟨n, t, ht, h0, hn⟩

theorem partitionSup_of_lt (h : b < a) : partitionSup g a b = 0 :=
  le_antisymm (partitionSup_le fun p => absurd p.le (not_le.2 h)) bot_le

theorem le_partitionSup_single (hab : a ≤ b) : g a b ≤ partitionSup g a b := by
  have := le_partitionSup (g := g) (IccPartition.single hab)
  rwa [IccPartition.single_sum] at this

/-- **Superadditivity** over adjacent intervals (concatenation of partitions). -/
theorem partitionSup_add_le (hab : a ≤ b) (hbc : b ≤ c) :
    partitionSup g a b + partitionSup g b c ≤ partitionSup g a c := by
  have : Nonempty (IccPartition a b) := ⟨IccPartition.single hab⟩
  have : Nonempty (IccPartition b c) := ⟨IccPartition.single hbc⟩
  refine ENNReal.iSup_add_iSup_le fun p q => ?_
  rw [← IccPartition.append_sum]
  exact le_partitionSup _

/-- Superadditivity along a chain `u 0 ≤ u 1 ≤ ⋯ ≤ u N`. -/
theorem sum_partitionSup_le {u : ℕ → ℝ} (hu : Monotone u) (N : ℕ) :
    ∑ k ∈ Finset.range N, partitionSup g (u k) (u (k + 1)) ≤ partitionSup g (u 0) (u N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact (add_le_add_left ih _).trans
      (partitionSup_add_le (hu (Nat.zero_le N)) (hu (Nat.le_succ N)))

/-- Superadditivity along the points of a partition. -/
theorem IccPartition.sum_partitionSup_le (p : IccPartition a b) (g : ℝ → ℝ → ℝ≥0∞) :
    ∑ i ∈ Finset.range p.n, partitionSup g (p.t i) (p.t (i + 1)) ≤ partitionSup g a b := by
  have hmono : Monotone fun i => p.t (min i p.n) := fun i j hij =>
    p.le_t (min_le_min_right p.n hij) (min_le_right _ _)
  have h := HigherDimLQGMetric.sum_partitionSup_le (g := g) hmono p.n
  simp only [min_self, Nat.zero_min, p.zero, p.last] at h
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_)) h
  rw [Finset.mem_range] at hi
  rw [min_eq_left hi.le, min_eq_left (by omega)]

theorem partitionSup_mono (h : ∀ u v, a ≤ u → u ≤ v → v ≤ b → g u v ≤ g' u v) :
    partitionSup g a b ≤ partitionSup g' a b :=
  partitionSup_le fun p => (Finset.sum_le_sum fun i hi => by
    obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
    exact h _ _ h1 h2 h3).trans (le_partitionSup p)

theorem partitionSup_congr (h : ∀ u v, a ≤ u → u ≤ v → v ≤ b → g u v = g' u v) :
    partitionSup g a b = partitionSup g' a b :=
  le_antisymm (partitionSup_mono fun u v h1 h2 h3 => (h u v h1 h2 h3).le)
    (partitionSup_mono fun u v h1 h2 h3 => (h u v h1 h2 h3).ge)

theorem partitionSup_const_mul (e : ℝ≥0∞) (g : ℝ → ℝ → ℝ≥0∞) (a b : ℝ) :
    partitionSup (fun u v => e * g u v) a b = e * partitionSup g a b := by
  unfold partitionSup IccPartition.sum
  rw [ENNReal.mul_iSup]
  simp only [Finset.mul_sum]

/-- Inserting the point `b` into a partition of `[a, c]` splits it into partitions of `[a, b]`
and `[b, c]`; if `g` does not decrease under subdivision, the sum does not decrease. -/
theorem partitionSup_le_add
    (hsplit : ∀ u x v, a ≤ u → u ≤ x → x ≤ v → v ≤ c → g u v ≤ g u x + g x v)
    (hab : a ≤ b) (hbc : b ≤ c) :
    partitionSup g a c ≤ partitionSup g a b + partitionSup g b c := by
  refine partitionSup_le fun p => ?_
  classical
  set n := p.n with hn
  set t := p.t with ht
  set j := Nat.findGreatest (fun i => t i ≤ b) n with hj
  have hjn : j ≤ n := Nat.findGreatest_le n
  have htj : t j ≤ b := Nat.findGreatest_spec (P := fun i => t i ≤ b) (Nat.zero_le n)
    (by simp only [ht, p.zero]; exact hab)
  have hgt : ∀ i, j < i → i ≤ n → b < t i := fun i h1 h2 =>
    not_le.1 (Nat.findGreatest_is_greatest h1 h2)
  rcases hjn.eq_or_lt with hjeq | hjlt
  · -- `t n ≤ b`, so `b = c`
    have hbc' : b = c := by
      have h := htj
      rw [hjeq] at h
      exact le_antisymm hbc (p.last ▸ h)
    subst hbc'
    calc p.sum g ≤ partitionSup g a b := le_partitionSup p
      _ ≤ partitionSup g a b + partitionSup g b b := le_self_add
  · -- the partition of `[a, b]`: `t 0, …, t j, b`
    let p₁ : IccPartition a b :=
      { n := j + 1
        t := fun i => if i ≤ j then t i else b
        mono := by
          intro i hi i' hi' hii'
          simp only [mem_Iic] at hi hi'
          dsimp only
          by_cases h1 : i' ≤ j
          · rw [ite_eq_left (hii'.trans h1), ite_eq_left h1]
            exact p.le_t hii' (h1.trans hjn)
          · rw [ite_eq_right h1]
            by_cases h2 : i ≤ j
            · rw [ite_eq_left h2]; exact (p.le_t h2 hjn).trans htj
            · rw [ite_eq_right h2]
        zero := by simp only [Nat.zero_le, ite_true, ht, p.zero]
        last := by simp }
    -- the partition of `[b, c]`: `b, t (j + 1), …, t n`
    let p₂ : IccPartition b c :=
      { n := n - j
        t := fun i => if i = 0 then b else t (j + i)
        mono := by
          intro i hi i' hi' hii'
          simp only [mem_Iic] at hi hi'
          dsimp only
          by_cases h1 : i = 0
          · rw [ite_eq_left h1]
            by_cases h2 : i' = 0
            · rw [ite_eq_left h2]
            · rw [ite_eq_right h2]; exact (hgt _ (by omega) (by omega)).le
          · have h2 : i' ≠ 0 := by omega
            rw [ite_eq_right h1, ite_eq_right h2]
            exact p.le_t (by omega) (by omega)
        zero := by simp
        last := by
          show (if n - j = 0 then b else t (j + (n - j))) = c
          rw [ite_eq_right (by omega), show j + (n - j) = n by omega, ht, p.last] }
    have hs₁ : p₁.sum g = (∑ i ∈ Finset.range j, g (t i) (t (i + 1))) + g (t j) b := by
      simp only [IccPartition.sum, p₁]
      rw [Finset.sum_range_succ, ite_eq_left le_rfl, ite_eq_right (by omega)]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [ite_eq_left hi.le, ite_eq_left (show i + 1 ≤ j by omega)]
    obtain ⟨m, hm⟩ : ∃ m, n = j + 1 + m := ⟨n - j - 1, by omega⟩
    have hs₂ : p₂.sum g = g b (t (j + 1)) +
        ∑ k ∈ Finset.range m, g (t (j + 1 + k)) (t (j + 1 + k + 1)) := by
      show ∑ i ∈ Finset.range (n - j),
          g (if i = 0 then b else t (j + i)) (if i + 1 = 0 then b else t (j + (i + 1))) = _
      rw [show n - j = m + 1 by omega, Finset.sum_range_succ', add_comm (g b _)]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [ite_eq_right (Nat.succ_ne_zero k), ite_eq_right (Nat.succ_ne_zero (k + 1)),
          show j + (k + 1) = j + 1 + k by omega, show j + (k + 1 + 1) = j + 1 + k + 1 by omega]
    have hs : p.sum g = (∑ i ∈ Finset.range j, g (t i) (t (i + 1))) + g (t j) (t (j + 1)) +
        ∑ k ∈ Finset.range m, g (t (j + 1 + k)) (t (j + 1 + k + 1)) := by
      show ∑ i ∈ Finset.range n, g (t i) (t (i + 1)) = _
      rw [hm, Finset.sum_range_add, Finset.sum_range_succ]
    have hjt : g (t j) (t (j + 1)) ≤ g (t j) b + g b (t (j + 1)) :=
      hsplit _ _ _ (p.mem_Icc hjn).1 htj (hgt _ (Nat.lt_succ_self j) hjlt).le
        (p.mem_Icc hjlt).2
    calc p.sum g = (∑ i ∈ Finset.range j, g (t i) (t (i + 1))) + g (t j) (t (j + 1)) +
          ∑ k ∈ Finset.range m, g (t (j + 1 + k)) (t (j + 1 + k + 1)) := hs
      _ ≤ (∑ i ∈ Finset.range j, g (t i) (t (i + 1))) + (g (t j) b + g b (t (j + 1))) +
          ∑ k ∈ Finset.range m, g (t (j + 1 + k)) (t (j + 1 + k + 1)) := by
        gcongr
      _ = p₁.sum g + p₂.sum g := by rw [hs₁, hs₂]; ring
      _ ≤ partitionSup g a b + partitionSup g b c :=
        add_le_add (le_partitionSup p₁) (le_partitionSup p₂)

/-- **Additivity** when `g` does not decrease under subdivision. -/
theorem partitionSup_add
    (hsplit : ∀ u x v, a ≤ u → u ≤ x → x ≤ v → v ≤ c → g u v ≤ g u x + g x v)
    (hab : a ≤ b) (hbc : b ≤ c) :
    partitionSup g a b + partitionSup g b c = partitionSup g a c :=
  le_antisymm (partitionSup_add_le hab hbc) (partitionSup_le_add hsplit hab hbc)

/-- **Reparametrization** by a continuous monotone `φ` on `[c, d]`: partitions of `[c, d]` are
pushed forward by `φ`, and partitions of `[φ c, φ d]` are pulled back by choosing the first
preimage of each point (intermediate value theorem). -/
theorem partitionSup_comp {φ : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d) (hφc : ContinuousOn φ (Icc c d))
    (hφm : MonotoneOn φ (Icc c d)) (G : ℝ → ℝ → ℝ≥0∞) :
    partitionSup (fun u v => G (φ u) (φ v)) c d = partitionSup G (φ c) (φ d) := by
  apply le_antisymm
  · refine partitionSup_le fun p => ?_
    let q : IccPartition (φ c) (φ d) :=
      { n := p.n
        t := fun i => φ (p.t i)
        mono := fun i hi j hj hij => hφm (p.mem_Icc hi) (p.mem_Icc hj) (p.mono hi hj hij)
        zero := by simp only [p.zero]
        last := by simp only [p.last] }
    exact le_partitionSup (g := G) q
  · refine partitionSup_le fun q => ?_
    rcases Nat.eq_zero_or_pos q.n with hq0 | hqpos
    · simp [IccPartition.sum, hq0]
    -- the sets of preimages
    set S : ℕ → Set ℝ := fun i => Icc c d ∩ φ ⁻¹' {q.t i} with hS
    have hSc : ∀ i, IsClosed (S i) := fun i =>
      hφc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hSb : ∀ i, BddBelow (S i) := fun i => ⟨c, fun x hx => hx.1.1⟩
    have hSne : ∀ i, i ≤ q.n → (S i).Nonempty := by
      intro i hi
      obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc hcd hφc (q.mem_Icc hi)
      exact ⟨s, hs, hφs⟩
    have hSmem : ∀ i, i ≤ q.n → sInf (S i) ∈ S i := fun i hi =>
      (hSc i).csInf_mem (hSne i hi) (hSb i)
    set τ : ℕ → ℝ := fun i => if i = q.n then d else sInf (S i) with hτ
    have hτmem : ∀ i, i ≤ q.n → τ i ∈ Icc c d := by
      intro i hi
      by_cases h : i = q.n
      · simp only [hτ, ite_eq_left h]; exact ⟨hcd, le_rfl⟩
      · simp only [hτ, ite_eq_right h]; exact (hSmem i hi).1
    have hφτ : ∀ i, i ≤ q.n → φ (τ i) = q.t i := by
      intro i hi
      by_cases h : i = q.n
      · simp only [hτ, ite_eq_left h]; rw [h, q.last]
      · simp only [hτ, ite_eq_right h]; exact (hSmem i hi).2
    let p : IccPartition c d :=
      { n := q.n
        t := τ
        mono := by
          intro i hi j hj hij
          simp only [mem_Iic] at hi hj
          by_cases hjn : j = q.n
          · rw [show τ j = d by simp only [hτ, ite_eq_left hjn]]
            exact (hτmem i hi).2
          · have hin : i ≠ q.n := by omega
            rw [show τ i = sInf (S i) by simp only [hτ, ite_eq_right hin],
              show τ j = sInf (S j) by simp only [hτ, ite_eq_right hjn]]
            obtain ⟨hsj, hφsj⟩ := hSmem j hj
            have hφc' : ContinuousOn φ (Icc c (sInf (S j))) := hφc.mono (Icc_subset_Icc le_rfl hsj.2)
            have hmem : q.t i ∈ Icc (φ c) (φ (sInf (S j))) := by
              refine ⟨(q.mem_Icc hi).1, ?_⟩
              rw [show φ (sInf (S j)) = q.t j from hφsj]
              exact q.le_t hij hj
            obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc hsj.1 hφc' hmem
            exact (csInf_le (hSb i) ⟨⟨hs.1, hs.2.trans hsj.2⟩, hφs⟩).trans hs.2
        zero := by
          have h0 : (0 : ℕ) ≠ q.n := by omega
          show τ 0 = c
          simp only [hτ, ite_eq_right h0]
          refine le_antisymm (csInf_le (hSb 0) ⟨⟨le_rfl, hcd⟩, ?_⟩) (le_csInf (hSne 0 (Nat.zero_le _))
            fun x hx => hx.1.1)
          show φ c = q.t 0
          rw [q.zero]
        last := by
          show τ q.n = d
          simp only [hτ, ite_eq_left rfl] }
    have hsum : p.sum (fun u v => G (φ u) (φ v)) = q.sum G := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < q.n := Finset.mem_range.1 hi
      show G (φ (τ i)) (φ (τ (i + 1))) = G (q.t i) (q.t (i + 1))
      rw [hφτ i hi'.le, hφτ (i + 1) hi']
    rw [← hsum]
    exact le_partitionSup p

/-- The reflection `t ↦ c + d - t` of a partition of `[c, d]`. -/
def IccPartition.reflect {c d : ℝ} (p : IccPartition c d) : IccPartition c d where
  n := p.n
  t i := c + d - p.t (p.n - i)
  mono := by
    intro i hi j hj hij
    simp only [mem_Iic] at hi hj
    have := p.le_t (show p.n - j ≤ p.n - i by omega) (Nat.sub_le _ _)
    linarith
  zero := by simp only [Nat.sub_zero, p.last]; ring
  last := by simp only [Nat.sub_self, p.zero]; ring

theorem IccPartition.reflect_sum {c d : ℝ} (p : IccPartition c d) (G : ℝ → ℝ → ℝ≥0∞) :
    p.reflect.sum (fun u v => G (c + d - v) (c + d - u)) = p.sum G := by
  unfold IccPartition.sum
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < p.n := Finset.mem_range.1 hi
  show G (c + d - (c + d - p.t (p.n - (p.n - 1 - i + 1))))
      (c + d - (c + d - p.t (p.n - (p.n - 1 - i)))) = G (p.t i) (p.t (i + 1))
  rw [show p.n - (p.n - 1 - i + 1) = i by omega, show p.n - (p.n - 1 - i) = i + 1 by omega]
  congr 1 <;> ring

theorem IccPartition.reflect_sum' {c d : ℝ} (p : IccPartition c d) (G : ℝ → ℝ → ℝ≥0∞) :
    p.reflect.sum G = p.sum (fun u v => G (c + d - v) (c + d - u)) := by
  unfold IccPartition.sum
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < p.n := Finset.mem_range.1 hi
  show G (c + d - p.t (p.n - (p.n - 1 - i))) (c + d - p.t (p.n - (p.n - 1 - i + 1))) =
    G (c + d - p.t (i + 1)) (c + d - p.t i)
  rw [show p.n - (p.n - 1 - i + 1) = i by omega, show p.n - (p.n - 1 - i) = i + 1 by omega]

/-- **Reversal** of the parameter interval. -/
theorem partitionSup_reflect (G : ℝ → ℝ → ℝ≥0∞) (c d : ℝ) :
    partitionSup (fun u v => G (c + d - v) (c + d - u)) c d = partitionSup G c d := by
  apply le_antisymm
  · refine partitionSup_le fun p => ?_
    rw [← p.reflect_sum' G]
    exact le_partitionSup _
  · refine partitionSup_le fun p => ?_
    rw [← p.reflect_sum G]
    exact le_partitionSup _

end PartitionSup

/-! ### Lengths for an arbitrary distance function -/

section CurveLengthWith

variable {X : Type*}

/-- The length of `P : ℝ → X` on `[a, b]` measured with `δ : X → X → [0, ∞]`: the supremum over
partitions of `∑ δ (P (t i)) (P (t (i + 1)))` (MA1's `curveLengthWith`). -/
def curveLengthWith (δ : X → X → ℝ≥0∞) (P : ℝ → X) (a b : ℝ) : ℝ≥0∞ :=
  partitionSup (fun u v => δ (P u) (P v)) a b

/-- MA1's literal shape. -/
theorem curveLengthWith_eq_iSup (δ : X → X → ℝ≥0∞) (P : ℝ → X) (a b : ℝ) :
    curveLengthWith δ P a b = ⨆ (n : ℕ) (t : ℕ → ℝ) (_ : MonotoneOn t (Iic n)) (_ : t 0 = a)
      (_ : t n = b), ∑ i ∈ Finset.range n, δ (P (t i)) (P (t (i + 1))) :=
  partitionSup_eq_iSup _ a b

variable {δ δ' : X → X → ℝ≥0∞} {P : ℝ → X} {a b c : ℝ}

theorem le_curveLengthWith (hab : a ≤ b) : δ (P a) (P b) ≤ curveLengthWith δ P a b :=
  le_partitionSup_single (g := fun u v => δ (P u) (P v)) hab

theorem curveLengthWith_of_lt (h : b < a) : curveLengthWith δ P a b = 0 :=
  partitionSup_of_lt h

theorem curveLengthWith_mono
    (h : ∀ u v, a ≤ u → u ≤ v → v ≤ b → δ (P u) (P v) ≤ δ' (P u) (P v)) :
    curveLengthWith δ P a b ≤ curveLengthWith δ' P a b :=
  partitionSup_mono h

theorem curveLengthWith_congr
    (h : ∀ u v, a ≤ u → u ≤ v → v ≤ b → δ (P u) (P v) = δ' (P u) (P v)) :
    curveLengthWith δ P a b = curveLengthWith δ' P a b :=
  partitionSup_congr h

theorem curveLengthWith_const_mul (e : ℝ≥0∞) :
    curveLengthWith (fun x y => e * δ x y) P a b = e * curveLengthWith δ P a b :=
  partitionSup_const_mul e _ a b

theorem curveLengthWith_add_le (hab : a ≤ b) (hbc : b ≤ c) :
    curveLengthWith δ P a b + curveLengthWith δ P b c ≤ curveLengthWith δ P a c :=
  partitionSup_add_le hab hbc

theorem sum_curveLengthWith_le {u : ℕ → ℝ} (hu : Monotone u) (N : ℕ) :
    ∑ k ∈ Finset.range N, curveLengthWith δ P (u k) (u (k + 1)) ≤
      curveLengthWith δ P (u 0) (u N) :=
  sum_partitionSup_le hu N

/-- Additivity for a distance function satisfying the triangle inequality along `P`. -/
theorem curveLengthWith_add
    (htri : ∀ u x v, a ≤ u → u ≤ x → x ≤ v → v ≤ c → δ (P u) (P v) ≤ δ (P u) (P x) + δ (P x) (P v))
    (hab : a ≤ b) (hbc : b ≤ c) :
    curveLengthWith δ P a b + curveLengthWith δ P b c = curveLengthWith δ P a c :=
  partitionSup_add htri hab hbc

/-- Lengths over subintervals are smaller (superadditivity). -/
theorem curveLengthWith_mono_interval {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htc : t ≤ c) :
    curveLengthWith δ P s t ≤ curveLengthWith δ P a c :=
  calc curveLengthWith δ P s t ≤ curveLengthWith δ P a s + curveLengthWith δ P s t := le_add_self
    _ ≤ curveLengthWith δ P a s + curveLengthWith δ P s t + curveLengthWith δ P t c := le_self_add
    _ ≤ curveLengthWith δ P a t + curveLengthWith δ P t c :=
      add_le_add (curveLengthWith_add_le has hst) le_rfl
    _ ≤ curveLengthWith δ P a c := curveLengthWith_add_le (has.trans hst) htc

end CurveLengthWith

section EdistLength

variable {X : Type*} [PseudoEMetricSpace X]

/-- `curveLengthWith edist` is LQGMetric's `curveLength` (mathlib's variation). -/
theorem curveLengthWith_edist (P : ℝ → X) (a b : ℝ) :
    curveLengthWith edist P a b = curveLength P a b := by
  apply le_antisymm
  · refine partitionSup_le fun p => ?_
    have hmono : Monotone (fun i => p.t (min i p.n)) := fun i j hij =>
      p.le_t (min_le_min_right p.n hij) (min_le_right _ _)
    have hmem : ∀ i, p.t (min i p.n) ∈ Icc a b := fun i => p.mem_Icc (min_le_right _ _)
    calc p.sum (fun u v => edist (P u) (P v))
        = ∑ i ∈ Finset.range p.n, edist (P (p.t (min (i + 1) p.n))) (P (p.t (min i p.n))) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [min_eq_left (by omega), min_eq_left (by omega), edist_comm]
      _ ≤ curveLength P a b := eVariationOn.sum_le (f := P) hmono hmem
  · rw [curveLength_eq_partitionLengthSup]
    refine iSup_le fun n => iSup_le fun t => iSup_le fun ht => iSup_le fun h0 => iSup_le fun hn =>
      ?_
    refine le_trans (le_of_eq ?_) (le_partitionSup (g := fun u v => edist (P u) (P v))
      ⟨n, t, ht.monotoneOn, h0, hn⟩)
    exact Finset.sum_congr rfl fun i _ => edist_comm _ _

/-- A distance function bounded below by `m · edist` gives lengths bounded below by `m · len`. -/
theorem le_curveLengthWith_of_le {δ : X → X → ℝ≥0∞} {P : ℝ → X} {a b : ℝ} {m : ℝ≥0∞}
    (h : ∀ u v, a ≤ u → u ≤ v → v ≤ b → m * edist (P u) (P v) ≤ δ (P u) (P v)) :
    m * curveLength P a b ≤ curveLengthWith δ P a b := by
  rw [← curveLengthWith_edist, ← curveLengthWith_const_mul]
  exact curveLengthWith_mono h

/-- A distance function bounded above by `M · edist` gives lengths bounded above by `M · len`. -/
theorem curveLengthWith_le_of_le {δ : X → X → ℝ≥0∞} {P : ℝ → X} {a b : ℝ} {M : ℝ≥0∞}
    (h : ∀ u v, a ≤ u → u ≤ v → v ≤ b → δ (P u) (P v) ≤ M * edist (P u) (P v)) :
    curveLengthWith δ P a b ≤ M * curveLength P a b := by
  rw [← curveLengthWith_edist, ← curveLengthWith_const_mul]
  exact curveLengthWith_mono h

end EdistLength

/-! ### Induced internal distances -/

section InternalWith

variable {X : Type*} [TopologicalSpace X]

/-- The internal distance of `S` induced by `δ`: the infimum of the `δ`-lengths of continuous
curves `P : [0, 1] → S` from `x` to `y` (`∞` if there is none). -/
def internalWith (δ : X → X → ℝ≥0∞) (S : Set X) (x y : X) : ℝ≥0∞ :=
  ⨅ (P : ℝ → X) (_ : ContinuousOn P (Icc 0 1)) (_ : P 0 = x) (_ : P 1 = y)
    (_ : MapsTo P (Icc 0 1) S), curveLengthWith δ P 0 1

variable {δ δ' : X → X → ℝ≥0∞} {S T : Set X} {x y : X}

theorem internalWith_le {P : ℝ → X} (hc : ContinuousOn P (Icc 0 1)) (h0 : P 0 = x) (h1 : P 1 = y)
    (hS : MapsTo P (Icc 0 1) S) : internalWith δ S x y ≤ curveLengthWith δ P 0 1 :=
  iInf_le_of_le P <| iInf_le_of_le hc <| iInf_le_of_le h0 <| iInf_le_of_le h1 <|
    iInf_le_of_le hS le_rfl

theorem le_internalWith {e : ℝ≥0∞}
    (h : ∀ P : ℝ → X, ContinuousOn P (Icc 0 1) → P 0 = x → P 1 = y → MapsTo P (Icc 0 1) S →
      e ≤ curveLengthWith δ P 0 1) : e ≤ internalWith δ S x y := by
  simp only [internalWith, le_iInf_iff]
  exact h

/-- Antitone in the set. -/
theorem internalWith_anti (hST : S ⊆ T) : internalWith δ T x y ≤ internalWith δ S x y :=
  le_internalWith fun _ hc h0 h1 hS => internalWith_le hc h0 h1 (hS.mono_right hST)

/-- Monotone in the distance function. -/
theorem internalWith_mono (h : ∀ x y, δ x y ≤ δ' x y) :
    internalWith δ S x y ≤ internalWith δ' S x y :=
  le_internalWith fun _ hc h0 h1 hS => (internalWith_le hc h0 h1 hS).trans
    (curveLengthWith_mono fun _ _ _ _ _ => h _ _)

end InternalWith

section InternalEDist

variable {X : Type*} [PseudoEMetricSpace X]

/-- LQGMetric's `internalEDist` (paths on `[0, 1]`) as an infimum over curves on `[0, 1]`. -/
theorem internalEDist_eq_iInf_curve (S : Set X) (x y : X) :
    internalEDist S x y = ⨅ (P : ℝ → X) (_ : ContinuousOn P (Icc 0 1)) (_ : P 0 = x)
      (_ : P 1 = y) (_ : MapsTo P (Icc 0 1) S), curveLength P 0 1 := by
  apply le_antisymm
  · refine le_iInf fun P => le_iInf fun hc => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hS =>
      ?_
    have h := internalEDist_le_curveLength (Y := S) zero_le_one hc hS
    rwa [h0, h1] at h
  · refine le_iInf fun γ => ?_
    refine iInf_le_of_le (⇑γ.1.extend) <| iInf_le_of_le γ.1.continuous_extend.continuousOn <|
      iInf_le_of_le (Path.extend_zero γ.1) <| iInf_le_of_le (Path.extend_one γ.1) <|
      iInf_le_of_le (fun t ht => ?_) le_rfl
    rw [Path.extend_apply γ.1 ht]
    exact γ.2 _

/-- `internalWith edist` is LQGMetric's `internalEDist`. -/
theorem internalWith_edist (S : Set X) (x y : X) :
    internalWith edist S x y = internalEDist S x y := by
  rw [internalEDist_eq_iInf_curve]
  simp only [internalWith, curveLengthWith_edist]

end InternalEDist

end HigherDimLQGMetric
