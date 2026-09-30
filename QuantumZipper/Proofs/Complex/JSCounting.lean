import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Int

/-!
# EXT-JS node D5: mean porosity implies decay of the volume of thickenings

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 step D.4 and §3 node D5
(`volume_thickening_le_of_meanPorous`).

**Hypothesis (mean porosity, `IsMeanPorous E c C K j₀ n₀`).** For every `p ∈ E` and every
`n ≥ n₀`, at least `(n - j₀)/K` of the scales `j ∈ [j₀, n]` carry a *hole*: a point `q` with
`B(q, c 2^{-j}) ⊆ B(p, C 2^{-j}) \ E`. (The blueprint's form is `K = 2`, "half of the scales";
node D4 produces it.)

**Conclusion.** If `E ⊆ ℂ` is bounded, `0 < c` and `0 < K`, there are `C'` and `η > 0` with
`volume (thickening r E) ≤ C' r^η` for all `r ∈ (0, 1]`. In particular the upper Minkowski
dimension of `E` is at most `2 - η`. This is the classical fact "mean porous sets have upper
Minkowski dimension `< 2`" (Koskela–Rohde, *Hausdorff dimension and mean porosity*,
Math. Ann. 309 (1997) 593–609; used for Hölder domains by Jones–Smirnov, Ark. Mat. 38 (2000),
proof of Corollary 2, via Jones–Makarov). The proof here is self-contained.

## Proof

* **Grids.** For `ω ∈ {0,1,2}` and base `2^s`, the grid `ω` at level `m` consists of the squares
  `ω/3 (1+i) + 2^{-sm} ([k₁, k₁+1) × [k₂, k₂+1))`; `jsIdx s ω m z` is the index of the square
  containing `z`. Grids are nested across levels (`jsPar_jsIdx`).
* **One-third trick** (`exists_grid_cell`). Since `3 ∤ 2^{sm}`, grid points of distinct grids
  are `≥ 2^{-sm}/3` apart, so every ball of radius `ρ` with `6ρ < 2^{-sm}` lies inside one
  level-`m` square of at least one of the three grids.
* **Porous nodes.** A hole at scale `j`, with `m = ⌊j/s⌋` and `j mod s` in a fixed window
  (`jsUsable`), makes the node of `p` at level `m` (in a grid containing `B(p, C 2^{-j})`) have
  a child square disjoint from `E` (`jsPorous_of_hole`).
* **Weighted tree count** (`sum_jsW_le`). In a tree with at most `b` children per node and at
  most `b - 1` at porous nodes, the weights `∏ (1/(b-1) or 1/b)` along root paths sum to at most
  the number of roots. A leaf with `P` porous ancestors has weight `b^{-N} (b/(b-1))^P`.
* **Counting.** Every point has porous ancestors at `≳ N/(6K)` of the `N` levels in one of the
  three grids (pigeonhole, `exists_omega_card`, `porous_count_bound`); hence the number of
  level-`N` cells is `≲ b^N (b/(b-1))^{-N/(6K)}`, and the thickening is covered by balls of
  radius `2·2^{-sN}` around their centres.
-/

namespace QuantumZipper.JS

open MeasureTheory Metric

/-! ### The hypothesis -/

open scoped Classical in
/-- **Mean porosity** (blueprint node D5 hypothesis, produced by D4). For every `p ∈ E` and
every `n ≥ n₀`, at least `(n - j₀) / K` of the scales `j ∈ [j₀, n]` carry a hole
`B(q, c 2^{-j}) ⊆ B(p, C 2^{-j}) \ E`. The blueprint's version is `K = 2`. -/
def IsMeanPorous (E : Set ℂ) (c C : ℝ) (K j₀ n₀ : ℕ) : Prop :=
  ∀ p ∈ E, ∀ n : ℕ, n₀ ≤ n →
    n - j₀ ≤ K * ((Finset.Icc j₀ n).filter fun j =>
      ∃ q : ℂ, ball q (c * (2:ℝ)⁻¹ ^ j) ⊆ ball p (C * (2:ℝ)⁻¹ ^ j) \ E).card

/-! ### Weighted counting in a tree -/

section Tree

variable {α : Type*} (π : α → α) (T : ℕ → Finset α) (b : ℕ)

/-- A node `k` at level `m` is porous if some child of `k` is not a level-`m+1` node. -/
def jsPorous (m : ℕ) (k : α) : Prop := ∃ k', π k' = k ∧ k' ∉ T (m + 1)

open scoped Classical in
/-- Weight factor of a node. -/
noncomputable def jsF (m : ℕ) (k : α) : ℝ :=
  if jsPorous π T m k then 1 / ((b : ℝ) - 1) else 1 / (b : ℝ)

/-- Weight of a node: product of the factors of its strict ancestors. -/
noncomputable def jsW : ℕ → α → ℝ
  | 0, _ => 1
  | m + 1, k => jsW m (π k) * jsF π T b m (π k)

variable {π T b}

lemma jsF_nonneg (hb : 2 ≤ b) (m : ℕ) (k : α) : 0 ≤ jsF π T b m k := by
  have : (2:ℝ) ≤ b := by exact_mod_cast hb
  unfold jsF
  split_ifs <;> apply div_nonneg zero_le_one <;> linarith

lemma jsW_nonneg (hb : 2 ≤ b) (m : ℕ) : ∀ k, 0 ≤ jsW π T b m k := by
  induction m with
  | zero => intro k; simp [jsW]
  | succ m ih => intro k; exact mul_nonneg (ih _) (jsF_nonneg hb _ _)

lemma card_mul_jsF_le [DecidableEq α] (hb : 2 ≤ b)
    (hfib : ∀ k : α, ∃ F : Finset α, F.card ≤ b ∧ ∀ k', π k' = k → k' ∈ F) (m : ℕ) (k : α) :
    (((T (m + 1)).filter fun k' => π k' = k).card : ℝ) * jsF π T b m k ≤ 1 := by
  obtain ⟨F, hF, hmem⟩ := hfib k
  have hb2 : (2:ℝ) ≤ b := by exact_mod_cast hb
  unfold jsF
  split_ifs with hp
  · obtain ⟨k', hk', hk'T⟩ := hp
    have hsub : ((T (m + 1)).filter fun k'' => π k'' = k) ⊆ F.erase k' := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_erase]
      exact ⟨fun h => hk'T (h ▸ hx.1), hmem x hx.2⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (F.erase k').card = F.card - 1 := Finset.card_erase_of_mem (hmem k' hk')
    have h0 : 1 ≤ F.card := Finset.card_pos.mpr ⟨k', hmem k' hk'⟩
    have h3 : ((T (m + 1)).filter fun k'' => π k'' = k).card + 1 ≤ b := by omega
    have h4 : (((T (m + 1)).filter fun k'' => π k'' = k).card : ℝ) + 1 ≤ b := by
      exact_mod_cast h3
    rw [mul_one_div, div_le_one (by linarith)]
    linarith
  · have h1 : ((T (m + 1)).filter fun k'' => π k'' = k).card ≤ b :=
      (Finset.card_le_card (fun x hx => hmem x (Finset.mem_filter.mp hx).2)).trans hF
    have h4 : (((T (m + 1)).filter fun k'' => π k'' = k).card : ℝ) ≤ b := by exact_mod_cast h1
    rw [mul_one_div, div_le_one (by linarith)]
    exact h4

/-- **Weighted tree count.** The weights of the level-`N` nodes sum to at most the number of
roots. -/
theorem sum_jsW_le [DecidableEq α] (hb : 2 ≤ b) (hπ : ∀ m, ∀ k ∈ T (m + 1), π k ∈ T m)
    (hfib : ∀ k : α, ∃ F : Finset α, F.card ≤ b ∧ ∀ k', π k' = k → k' ∈ F) (N : ℕ) :
    ∑ k ∈ T N, jsW π T b N k ≤ (T 0).card := by
  induction N with
  | zero => simp [jsW]
  | succ N ih =>
    calc ∑ k ∈ T (N + 1), jsW π T b (N + 1) k
        = ∑ k₀ ∈ T N, ∑ k ∈ (T (N + 1)).filter (fun k => π k = k₀), jsW π T b (N + 1) k :=
          (Finset.sum_fiberwise_of_maps_to (hπ N) _).symm
      _ = ∑ k₀ ∈ T N, (((T (N + 1)).filter fun k => π k = k₀).card : ℝ) * jsF π T b N k₀ *
            jsW π T b N k₀ := by
          refine Finset.sum_congr rfl fun k₀ _ => ?_
          rw [Finset.sum_congr rfl (g := fun _ => jsW π T b N k₀ * jsF π T b N k₀)]
          · rw [Finset.sum_const, nsmul_eq_mul]; ring
          · intro k hk
            rw [Finset.mem_filter] at hk
            show jsW π T b N (π k) * jsF π T b N (π k) = _
            rw [hk.2]
      _ ≤ ∑ k₀ ∈ T N, jsW π T b N k₀ := by
          refine Finset.sum_le_sum fun k₀ _ => ?_
          have h1 := card_mul_jsF_le (T := T) hb hfib N k₀
          have hW := jsW_nonneg (π := π) (T := T) hb N k₀
          nlinarith
      _ ≤ _ := ih

/-- Along a chain of nodes, the weight is the product of the factors. -/
lemma jsW_chain {β : Type*} (idx : ℕ → β → α) (z : β)
    (hnest : ∀ m, π (idx (m + 1) z) = idx m z) (N : ℕ) :
    jsW π T b N (idx N z) = ∏ i ∈ Finset.range N, jsF π T b i (idx i z) := by
  induction N with
  | zero => simp [jsW]
  | succ N ih =>
    rw [Finset.prod_range_succ, ← ih]
    show jsW π T b N (π (idx (N + 1) z)) * jsF π T b N (π (idx (N + 1) z)) = _
    rw [hnest]

open scoped Classical in
lemma prod_jsF_eq (hb : 2 ≤ b) (g : ℕ → α) (N : ℕ) :
    ∏ i ∈ Finset.range N, jsF π T b i (g i) =
      (1 / (b : ℝ)) ^ N * ((b : ℝ) / ((b : ℝ) - 1)) ^
        ((Finset.range N).filter fun i => jsPorous π T i (g i)).card := by
  have hb2 : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hb1 : (b : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have key : ∀ i, jsF π T b i (g i) =
      1 / (b : ℝ) * (if jsPorous π T i (g i) then (b : ℝ) / ((b : ℝ) - 1) else 1) := by
    intro i
    unfold jsF
    split_ifs
    · rw [div_mul_div_comm, one_mul, div_mul_cancel_left₀ hb0, one_div]
    · ring
  rw [Finset.prod_congr rfl fun i _ => key i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

end Tree

/-! ### Three shifted grids of base `2^s` -/

/-- Index of the square of grid `ω` (offset `ω/3 · (1 + i)`) at level `m` (side `2^{-sm}`)
containing `z`. -/
noncomputable def jsIdx (s ω m : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊(z.re - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋, ⌊(z.im - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋)

/-- Parent index. -/
def jsPar (s : ℕ) (k : ℤ × ℤ) : ℤ × ℤ := (k.1 / ((2 ^ s : ℕ) : ℤ), k.2 / ((2 ^ s : ℕ) : ℤ))

/-- Centre of a square of grid `ω` at level `N`. -/
noncomputable def jsCenter (s ω N : ℕ) (ℓ : ℤ × ℤ) : ℂ :=
  ⟨((ℓ.1 : ℝ) + 1 / 2) / (2:ℝ) ^ (s * N) + (ω : ℝ) / 3,
    ((ℓ.2 : ℝ) + 1 / 2) / (2:ℝ) ^ (s * N) + (ω : ℝ) / 3⟩

lemma floor_mul_two_pow_div (x : ℝ) (s m : ℕ) :
    ⌊x * (2:ℝ) ^ (s * (m + 1))⌋ / ((2 ^ s : ℕ) : ℤ) = ⌊x * (2:ℝ) ^ (s * m)⌋ := by
  rw [← Int.floor_div_natCast]
  congr 1
  rw [mul_add, mul_one, pow_add]
  push_cast
  rw [← mul_assoc, mul_div_assoc, div_self (by positivity), mul_one]

lemma jsPar_jsIdx (s ω m : ℕ) (z : ℂ) : jsPar s (jsIdx s ω (m + 1) z) = jsIdx s ω m z := by
  simp only [jsPar, jsIdx, floor_mul_two_pow_div]

lemma jsPar_fiber (s : ℕ) (k : ℤ × ℤ) :
    ∃ F : Finset (ℤ × ℤ), F.card ≤ 2 ^ s * 2 ^ s ∧ ∀ k', jsPar s k' = k → k' ∈ F := by
  have hM : (0:ℤ) < ((2 ^ s : ℕ) : ℤ) := by positivity
  refine ⟨Finset.Ico (k.1 * ((2 ^ s : ℕ) : ℤ)) (k.1 * ((2 ^ s : ℕ) : ℤ) + ((2 ^ s : ℕ) : ℤ)) ×ˢ
    Finset.Ico (k.2 * ((2 ^ s : ℕ) : ℤ)) (k.2 * ((2 ^ s : ℕ) : ℤ) + ((2 ^ s : ℕ) : ℤ)), ?_, ?_⟩
  · rw [Finset.card_product, Int.card_Ico, Int.card_Ico, add_sub_cancel_left,
      add_sub_cancel_left, Int.toNat_natCast]
  · intro k' hk'
    simp only [jsPar, Prod.ext_iff] at hk'
    obtain ⟨h1, h2⟩ := hk'
    simp only [Finset.mem_product, Finset.mem_Ico]
    have a1 := Int.emod_add_mul_ediv k'.1 ((2 ^ s : ℕ) : ℤ)
    have b1 := Int.emod_nonneg k'.1 hM.ne'
    have c1 := Int.emod_lt_of_pos k'.1 hM
    have a2 := Int.emod_add_mul_ediv k'.2 ((2 ^ s : ℕ) : ℤ)
    have b2 := Int.emod_nonneg k'.2 hM.ne'
    have c2 := Int.emod_lt_of_pos k'.2 hM
    rw [h1] at a1
    rw [h2] at a2
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

lemma abs_sub_lt_of_floor_eq {a b o X : ℝ} (hX : 0 < X) (h : ⌊(a - o) * X⌋ = ⌊(b - o) * X⌋) :
    |a - b| < X⁻¹ := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_mul, sub_sub_sub_cancel_right, abs_mul, abs_of_pos hX] at h1
  calc |a - b| = |a - b| * X * X⁻¹ := by field_simp
    _ < 1 * X⁻¹ := by gcongr
    _ = X⁻¹ := one_mul _

lemma norm_sub_lt_of_jsIdx_eq {s ω m : ℕ} {z w : ℂ} (h : jsIdx s ω m z = jsIdx s ω m w) :
    ‖z - w‖ < 2 * ((2:ℝ) ^ (s * m))⁻¹ := by
  have hX : (0:ℝ) < 2 ^ (s * m) := by positivity
  simp only [jsIdx, Prod.mk.injEq] at h
  have h1 := abs_sub_lt_of_floor_eq hX h.1
  have h2 := abs_sub_lt_of_floor_eq hX h.2
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < _ := by rw [Complex.sub_re, Complex.sub_im]; linarith

lemma abs_sub_cell_center {a o X : ℝ} (hX : 0 < X) :
    |a - ((⌊(a - o) * X⌋ + 1 / 2) / X + o)| ≤ 1 / (2 * X) := by
  have h1 := Int.floor_le ((a - o) * X)
  have h2 := Int.lt_floor_add_one ((a - o) * X)
  have e : a - ((⌊(a - o) * X⌋ + 1 / 2) / X + o) = ((a - o) * X - ⌊(a - o) * X⌋ - 1 / 2) / X := by
    field_simp
    ring
  have e2 : 1 / (2 * X) * X = 1 / 2 := by field_simp
  rw [e, abs_div, abs_of_pos hX, div_le_iff₀ hX, e2, abs_le]
  constructor <;> linarith

lemma norm_sub_jsCenter_le (s ω N : ℕ) (z : ℂ) :
    ‖z - jsCenter s ω N (jsIdx s ω N z)‖ ≤ ((2:ℝ) ^ (s * N))⁻¹ := by
  have hX : (0:ℝ) < 2 ^ (s * N) := by positivity
  have h1 := abs_sub_cell_center (a := z.re) (o := (ω : ℝ) / 3) hX
  have h2 := abs_sub_cell_center (a := z.im) (o := (ω : ℝ) / 3) hX
  have h3 := Complex.norm_le_abs_re_add_abs_im (z - jsCenter s ω N (jsIdx s ω N z))
  simp only [Complex.sub_re, Complex.sub_im, jsCenter, jsIdx] at h3
  simp only [jsCenter, jsIdx]
  have e : (1:ℝ) / (2 * 2 ^ (s * N)) + 1 / (2 * 2 ^ (s * N)) = ((2:ℝ) ^ (s * N))⁻¹ := by ring
  linarith

lemma finite_jsIdx_image {E : Set ℂ} (hE : Bornology.IsBounded E) (s ω m : ℕ) :
    (jsIdx s ω m '' E).Finite := by
  obtain ⟨R, hR⟩ := hE.subset_closedBall 0
  have hX : (0:ℝ) ≤ 2 ^ (s * m) := by positivity
  have hω : (0:ℝ) ≤ (ω : ℝ) / 3 := by positivity
  refine (Set.finite_Icc
    (⌊(-R - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋, ⌊(-R - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋)
    (⌊(R - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋, ⌊(R - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  have hn : ‖z‖ ≤ R := by simpa using hR hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  rw [abs_le] at hre him
  simp only [jsIdx]
  rw [Set.mem_Icc, Prod.mk_le_mk, Prod.mk_le_mk]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> apply Int.floor_mono <;>
    apply mul_le_mul_of_nonneg_right _ hX <;> linarith

/-- The level-`m` squares of grid `ω` meeting `E`. -/
noncomputable def jsT {E : Set ℂ} (hE : Bornology.IsBounded E) (s ω m : ℕ) : Finset (ℤ × ℤ) :=
  (finite_jsIdx_image hE s ω m).toFinset

lemma mem_jsT {E : Set ℂ} {hE : Bornology.IsBounded E} {s ω m : ℕ} {k : ℤ × ℤ} :
    k ∈ jsT hE s ω m ↔ ∃ z ∈ E, jsIdx s ω m z = k := by
  simp [jsT]

lemma jsPar_mem_jsT {E : Set ℂ} (hE : Bornology.IsBounded E) (s ω m : ℕ) :
    ∀ k ∈ jsT hE s ω (m + 1), jsPar s k ∈ jsT hE s ω m := by
  intro k hk
  rw [mem_jsT] at hk ⊢
  obtain ⟨z, hz, rfl⟩ := hk
  exact ⟨z, hz, (jsPar_jsIdx s ω m z).symm⟩

/-! ### The one-third trick -/

lemma exists_int_between_of_floor_ne {L U : ℝ} (hLU : L ≤ U) (h : ⌊L⌋ ≠ ⌊U⌋) :
    ∃ k : ℤ, L < k ∧ (k : ℝ) ≤ U := by
  refine ⟨⌊U⌋, ?_, Int.floor_le U⟩
  have h1 : ⌊L⌋ < ⌊U⌋ := lt_of_le_of_ne (Int.floor_mono hLU) h
  have h2 : ⌊L⌋ + 1 ≤ ⌊U⌋ := h1
  have h3 := Int.lt_floor_add_one L
  have h4 : ((⌊L⌋ + 1 : ℤ) : ℝ) ≤ ⌊U⌋ := by exact_mod_cast h2
  push_cast at h4
  linarith

lemma grid_bad_exclusive {y ρ : ℝ} {s m ω₁ ω₂ : ℕ} (hρ : 0 ≤ ρ)
    (hsmall : 6 * ρ * (2:ℝ) ^ (s * m) < 1) (h1 : ω₁ < 3) (h2 : ω₂ < 3) (hne : ω₁ ≠ ω₂)
    (b1 : ⌊(y - ρ - (ω₁ : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ ≠ ⌊(y + ρ - (ω₁ : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋)
    (b2 : ⌊(y - ρ - (ω₂ : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ ≠ ⌊(y + ρ - (ω₂ : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋) :
    False := by
  have hX : (0:ℝ) < 2 ^ (s * m) := by positivity
  have hle : ∀ ω : ℕ, (y - ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m) ≤
      (y + ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m) := fun ω =>
    mul_le_mul_of_nonneg_right (by linarith) hX.le
  obtain ⟨k₁, hk₁, hk₁'⟩ := exists_int_between_of_floor_ne (hle ω₁) b1
  obtain ⟨k₂, hk₂, hk₂'⟩ := exists_int_between_of_floor_ne (hle ω₂) b2
  have habs : |((3 * (k₁ - k₂) + ((ω₁ : ℤ) - ω₂) * 2 ^ (s * m) : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith
  have hn0 : 3 * (k₁ - k₂) + ((ω₁ : ℤ) - ω₂) * 2 ^ (s * m) = 0 := by
    rw [← Int.abs_lt_one_iff]
    exact_mod_cast habs
  have hdvd : (3:ℤ) ∣ ((ω₁ : ℤ) - ω₂) * 2 ^ (s * m) := ⟨k₂ - k₁, by linarith⟩
  rcases Int.prime_three.dvd_or_dvd hdvd with h | h
  · omega
  · have := Int.prime_three.dvd_of_dvd_pow h
    omega

lemma floor_eq_of_between {L U a b : ℝ} (h : ⌊L⌋ = ⌊U⌋) (ha1 : L ≤ a) (ha2 : a ≤ U)
    (hb1 : L ≤ b) (hb2 : b ≤ U) : ⌊a⌋ = ⌊b⌋ := by
  have := Int.floor_mono ha1
  have := Int.floor_mono ha2
  have := Int.floor_mono hb1
  have := Int.floor_mono hb2
  omega

/-- **One-third trick.** A ball of radius `ρ` with `6 ρ 2^{sm} < 1` lies in a single level-`m`
square of one of the three grids. -/
lemma exists_grid_cell (p : ℂ) {ρ : ℝ} {s m : ℕ} (hρ : 0 ≤ ρ)
    (hsmall : 6 * ρ * (2:ℝ) ^ (s * m) < 1) :
    ∃ ω < 3, ∀ w ∈ ball p ρ, jsIdx s ω m w = jsIdx s ω m p := by
  have hX : (0:ℝ) < 2 ^ (s * m) := by positivity
  have key : ∃ ω : ℕ, ω < 3 ∧
      ⌊(p.re - ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ =
        ⌊(p.re + ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ ∧
      ⌊(p.im - ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ =
        ⌊(p.im + ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ := by
    by_contra hcon
    push Not at hcon
    have c : ∀ ω : ℕ, ω < 3 →
        ⌊(p.re - ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ ≠
          ⌊(p.re + ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ ∨
        ⌊(p.im - ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ ≠
          ⌊(p.im + ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ := by
      intro ω hω
      by_cases h' : ⌊(p.re - ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ =
          ⌊(p.re + ρ - (ω : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋
      · exact Or.inr (hcon ω hω h')
      · exact Or.inl h'
    have ex : ∀ (y : ℝ) (ω₁ ω₂ : ℕ), ω₁ < 3 → ω₂ < 3 → ω₁ ≠ ω₂ →
        ⌊(y - ρ - (ω₁ : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ ≠
          ⌊(y + ρ - (ω₁ : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ →
        ⌊(y - ρ - (ω₂ : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ ≠
          ⌊(y + ρ - (ω₂ : ℝ) / 3) * (2:ℝ) ^ (s * m)⌋ → False :=
      fun y ω₁ ω₂ h1 h2 hne b1 b2 => grid_bad_exclusive hρ hsmall h1 h2 hne b1 b2
    rcases c 0 (by norm_num) with a0 | a0 <;> rcases c 1 (by norm_num) with a1 | a1 <;>
      rcases c 2 (by norm_num) with a2 | a2
    · exact ex p.re 0 1 (by norm_num) (by norm_num) (by norm_num) a0 a1
    · exact ex p.re 0 1 (by norm_num) (by norm_num) (by norm_num) a0 a1
    · exact ex p.re 0 2 (by norm_num) (by norm_num) (by norm_num) a0 a2
    · exact ex p.im 1 2 (by norm_num) (by norm_num) (by norm_num) a1 a2
    · exact ex p.re 1 2 (by norm_num) (by norm_num) (by norm_num) a1 a2
    · exact ex p.im 0 2 (by norm_num) (by norm_num) (by norm_num) a0 a2
    · exact ex p.im 0 1 (by norm_num) (by norm_num) (by norm_num) a0 a1
    · exact ex p.im 0 1 (by norm_num) (by norm_num) (by norm_num) a0 a1
  obtain ⟨ω, hω, hre, him⟩ := key
  refine ⟨ω, hω, fun w hw => ?_⟩
  rw [mem_ball, dist_eq_norm] at hw
  have h1 := Complex.abs_re_le_norm (w - p)
  have h2 := Complex.abs_im_le_norm (w - p)
  rw [Complex.sub_re, abs_le] at h1
  rw [Complex.sub_im, abs_le] at h2
  simp only [jsIdx, Prod.mk.injEq]
  constructor
  · refine floor_eq_of_between hre ?_ ?_ ?_ ?_ <;>
      apply mul_le_mul_of_nonneg_right _ hX.le <;> linarith
  · refine floor_eq_of_between him ?_ ?_ ?_ ?_ <;>
      apply mul_le_mul_of_nonneg_right _ hX.le <;> linarith

/-- A hole inside the square of `p` forces the node of `p` to be porous. -/
lemma jsPorous_of_hole {E : Set ℂ} (hE : Bornology.IsBounded E) {s ω m : ℕ} {p q : ℂ}
    {ρ c' : ℝ} (hcell : ∀ w ∈ ball p ρ, jsIdx s ω m w = jsIdx s ω m p) (hc' : 0 < c')
    (hhole : ball q c' ⊆ ball p ρ \ E) (hsize : 2 * ((2:ℝ) ^ (s * (m + 1)))⁻¹ ≤ c') :
    jsPorous (jsPar s) (jsT hE s ω) m (jsIdx s ω m p) := by
  have hq : q ∈ ball p ρ := (hhole (mem_ball_self hc')).1
  refine ⟨jsIdx s ω (m + 1) q, by rw [jsPar_jsIdx, hcell q hq], ?_⟩
  rw [mem_jsT]
  rintro ⟨z, hz, hzq⟩
  have := norm_sub_lt_of_jsIdx_eq hzq
  have hzb : z ∈ ball q c' := by rw [mem_ball, dist_eq_norm]; linarith
  exact (hhole hzb).2 hz

/-! ### Bookkeeping of scales -/

/-- Scale `j` is usable when its residue mod `s` lies in `[t, s - κ]`. -/
def jsUsable (s t κ j : ℕ) : Prop := t ≤ j % s ∧ j % s + κ ≤ s

lemma two_inv_pow_add_mul (a r : ℕ) : (2:ℝ)⁻¹ ^ (a + r) * 2 ^ a = (2:ℝ)⁻¹ ^ r := by
  rw [pow_add, mul_right_comm, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, one_mul]

lemma usable_small {C : ℝ} {s t j : ℕ} (hC : 0 ≤ C) (ht : 6 * C < 2 ^ t) (hu : t ≤ j % s) :
    6 * (C * (2:ℝ)⁻¹ ^ j) * (2:ℝ) ^ (s * (j / s)) < 1 := by
  have e : (2:ℝ)⁻¹ ^ j * (2:ℝ) ^ (s * (j / s)) = (2:ℝ)⁻¹ ^ (j % s) := by
    have : (2:ℝ)⁻¹ ^ j = (2:ℝ)⁻¹ ^ (s * (j / s) + j % s) := by rw [Nat.div_add_mod]
    rw [this, two_inv_pow_add_mul]
  have h1 : (2:ℝ)⁻¹ ^ (j % s) ≤ (2:ℝ)⁻¹ ^ t := pow_le_pow_of_le_one (by norm_num) (by norm_num) hu
  have h2 : 6 * C * (2:ℝ)⁻¹ ^ t < 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact ht
  calc 6 * (C * (2:ℝ)⁻¹ ^ j) * (2:ℝ) ^ (s * (j / s))
      = 6 * C * ((2:ℝ)⁻¹ ^ j * (2:ℝ) ^ (s * (j / s))) := by ring
    _ = 6 * C * (2:ℝ)⁻¹ ^ (j % s) := by rw [e]
    _ ≤ 6 * C * (2:ℝ)⁻¹ ^ t := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ < 1 := h2

lemma usable_size {c : ℝ} {s κ j : ℕ} (hκ : 2 ≤ c * 2 ^ κ) (hu : j % s + κ ≤ s) :
    2 * ((2:ℝ) ^ (s * (j / s + 1)))⁻¹ ≤ c * (2:ℝ)⁻¹ ^ j := by
  have hexp : s * (j / s + 1) = j + (s - j % s) := by
    have := Nat.div_add_mod j s
    rw [mul_add, mul_one]
    generalize s * (j / s) = A at *
    omega
  rw [hexp, ← inv_pow, pow_add]
  have h1 : (2:ℝ)⁻¹ ^ (s - j % s) ≤ (2:ℝ)⁻¹ ^ κ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : 2 * (2:ℝ)⁻¹ ^ κ ≤ c := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    exact hκ
  have h3 : (0:ℝ) ≤ (2:ℝ)⁻¹ ^ j := by positivity
  have h4 : 2 * (2:ℝ)⁻¹ ^ (s - j % s) ≤ c := by linarith
  calc 2 * ((2:ℝ)⁻¹ ^ j * (2:ℝ)⁻¹ ^ (s - j % s))
      = (2:ℝ)⁻¹ ^ j * (2 * (2:ℝ)⁻¹ ^ (s - j % s)) := by ring
    _ ≤ (2:ℝ)⁻¹ ^ j * c := mul_le_mul_of_nonneg_left h4 h3
    _ = c * (2:ℝ)⁻¹ ^ j := mul_comm _ _

open scoped Classical in
lemma card_not_usable_le (s t κ N : ℕ) (hs : 0 < s) :
    ((Finset.range (s * N)).filter fun j => ¬ jsUsable s t κ j).card ≤ N * (t + κ) := by
  have hsub : ((Finset.range s).filter fun r => r < t ∨ s < r + κ) ⊆
      Finset.range t ∪ Finset.Ico (s - κ) s := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hcard : ((Finset.range s).filter fun r => r < t ∨ s < r + κ).card ≤ t + κ := by
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    simp only [Finset.card_range, Nat.card_Ico]
    omega
  calc _ ≤ (Finset.range N ×ˢ (Finset.range s).filter fun r => r < t ∨ s < r + κ).card := by
        refine Finset.card_le_card_of_injOn (fun j => (j / s, j % s)) ?_ ?_
        · intro j hj
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
          unfold jsUsable at hj
          rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range,
            Finset.mem_range]
          show j / s < N ∧ j % s < s ∧ (j % s < t ∨ s < j % s + κ)
          refine ⟨?_, Nat.mod_lt j hs, by omega⟩
          rw [Nat.div_lt_iff_lt_mul hs]
          rw [mul_comm]
          exact hj.1
        · intro j₁ _ j₂ _ h
          simp only [Prod.mk.injEq] at h
          rw [← Nat.div_add_mod j₁ s, ← Nat.div_add_mod j₂ s, h.1, h.2]
    _ = N * ((Finset.range s).filter fun r => r < t ∨ s < r + κ).card := by
        rw [Finset.card_product, Finset.card_range]
    _ ≤ N * (t + κ) := Nat.mul_le_mul_left _ hcard

open scoped Classical in
/-- Good and usable scales of `p` in `[j₀, sN)`. -/
noncomputable def jsGset (E : Set ℂ) (c C : ℝ) (s t κ j₀ N : ℕ) (p : ℂ) : Finset ℕ :=
  (Finset.Ico j₀ (s * N)).filter fun j =>
    (∃ q : ℂ, ball q (c * (2:ℝ)⁻¹ ^ j) ⊆ ball p (C * (2:ℝ)⁻¹ ^ j) \ E) ∧ jsUsable s t κ j

open scoped Classical in
/-- Good and usable scales of `p` in `[j₀, sN)` whose ball fits in a square of grid `ω`. -/
noncomputable def jsGωset (E : Set ℂ) (c C : ℝ) (s t κ j₀ N ω : ℕ) (p : ℂ) : Finset ℕ :=
  (Finset.Ico j₀ (s * N)).filter fun j =>
    (∃ q : ℂ, ball q (c * (2:ℝ)⁻¹ ^ j) ⊆ ball p (C * (2:ℝ)⁻¹ ^ j) \ E) ∧ jsUsable s t κ j ∧
      ∀ w ∈ ball p (C * (2:ℝ)⁻¹ ^ j), jsIdx s ω (j / s) w = jsIdx s ω (j / s) p

open scoped Classical in
/-- Number of porous ancestors (levels `< N`) of the square of `p` in grid `ω`. -/
noncomputable def jsPcount {E : Set ℂ} (hE : Bornology.IsBounded E) (s ω N : ℕ) (p : ℂ) : ℕ :=
  ((Finset.range N).filter fun i => jsPorous (jsPar s) (jsT hE s ω) i (jsIdx s ω i p)).card

lemma exists_omega_card {E : Set ℂ} {c C : ℝ} {s t κ j₀ N : ℕ} (hc : 0 < c)
    (ht : 6 * C < 2 ^ t) (p : ℂ) :
    ∃ ω < 3, (jsGset E c C s t κ j₀ N p).card ≤ 3 * (jsGωset E c C s t κ j₀ N ω p).card := by
  classical
  have hsub : jsGset E c C s t κ j₀ N p ⊆ jsGωset E c C s t κ j₀ N 0 p ∪
      jsGωset E c C s t κ j₀ N 1 p ∪ jsGωset E c C s t κ j₀ N 2 p := by
    intro j hj
    simp only [jsGset, Finset.mem_filter] at hj
    obtain ⟨hjI, ⟨q, hq⟩, hu⟩ := hj
    have hqp : q ∈ ball p (C * (2:ℝ)⁻¹ ^ j) := (hq (mem_ball_self (by positivity))).1
    have hCpos : 0 < C * (2:ℝ)⁻¹ ^ j := lt_of_le_of_lt dist_nonneg hqp
    have hC : 0 < C :=
      lt_of_mul_lt_mul_right (by rw [zero_mul]; exact hCpos) (by positivity : (0:ℝ) ≤ 2⁻¹ ^ j)
    obtain ⟨ω, hω, hcell⟩ := exists_grid_cell p hCpos.le (usable_small hC.le ht hu.1)
    have hmem : j ∈ jsGωset E c C s t κ j₀ N ω p := by
      simp only [jsGωset, Finset.mem_filter]
      exact ⟨hjI, ⟨q, hq⟩, hu, hcell⟩
    simp only [Finset.mem_union]
    rcases (by omega : ω = 0 ∨ ω = 1 ∨ ω = 2) with rfl | rfl | rfl
    · exact Or.inl (Or.inl hmem)
    · exact Or.inl (Or.inr hmem)
    · exact Or.inr hmem
  have h1 := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  by_contra hcon
  push Not at hcon
  have := hcon 0 (by norm_num)
  have := hcon 1 (by norm_num)
  have := hcon 2 (by norm_num)
  omega

lemma card_Gω_le {E : Set ℂ} (hE : Bornology.IsBounded E) {c C : ℝ} {s t κ j₀ N ω : ℕ}
    {p : ℂ} (hc : 0 < c) (hκ : 2 ≤ c * 2 ^ κ) (hs : 0 < s) :
    (jsGωset E c C s t κ j₀ N ω p).card ≤ s * jsPcount hE s ω N p := by
  classical
  refine (Finset.card_le_mul_card_image (f := fun j => j / s) _ s ?_).trans
    (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  · intro i _
    calc _ ≤ (Finset.Ico (s * i) (s * i + s)).card := by
          refine Finset.card_le_card ?_
          intro j hj
          simp only [Finset.mem_filter] at hj
          simp only [Finset.mem_Ico]
          have h1 := Nat.div_add_mod j s
          have h2 := Nat.mod_lt j hs
          rw [hj.2] at h1
          omega
      _ = s := by simp
  · intro i hi
    simp only [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    simp only [jsGωset, Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨⟨_, hjN⟩, ⟨q, hq⟩, hu, hcell⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, jsPorous_of_hole hE hcell (by positivity) hq (usable_size hκ hu.2)⟩
    rw [Nat.div_lt_iff_lt_mul hs, mul_comm]
    exact hjN

open scoped Classical in
lemma card_good_le {E : Set ℂ} {c C : ℝ} {s t κ j₀ N : ℕ} {p : ℂ} (hs : 0 < s)
    (hN : 1 ≤ s * N) :
    ((Finset.Icc j₀ (s * N - 1)).filter fun j =>
      ∃ q : ℂ, ball q (c * (2:ℝ)⁻¹ ^ j) ⊆ ball p (C * (2:ℝ)⁻¹ ^ j) \ E).card ≤
      (jsGset E c C s t κ j₀ N p).card + N * (t + κ) := by
  calc _ ≤ (jsGset E c C s t κ j₀ N p ∪
        (Finset.range (s * N)).filter fun j => ¬ jsUsable s t κ j).card := by
        refine Finset.card_le_card ?_
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        simp only [Finset.mem_union, jsGset, Finset.mem_filter, Finset.mem_Ico,
          Finset.mem_range]
        by_cases hu : jsUsable s t κ j
        · left; exact ⟨⟨hj.1.1, by omega⟩, hj.2, hu⟩
        · right; exact ⟨by omega, hu⟩
    _ ≤ _ := (Finset.card_union_le _ _).trans (Nat.add_le_add_left
          (card_not_usable_le s t κ N hs) _)

open scoped Classical in
/-- **Porous ancestors.** If `ω` is a best grid for `p`, the square of `p` has at least
`N/(6K) - (1 + j₀ + n₀)` porous ancestors among the levels `< N`. -/
lemma porous_count_bound {E : Set ℂ} (hE : Bornology.IsBounded E) {c C : ℝ}
    {K j₀ n₀ t κ s N ω : ℕ} (hc : 0 < c) (hK : 0 < K) (hpor : IsMeanPorous E c C K j₀ n₀)
    (hκ : 2 ≤ c * 2 ^ κ) (hs : s = 2 * K * (t + κ) + 1) {p : ℂ} (hp : p ∈ E)
    (hω : (jsGset E c C s t κ j₀ N p).card ≤ 3 * (jsGωset E c C s t κ j₀ N ω p).card) :
    (N : ℝ) / (6 * K) - (1 + j₀ + n₀) ≤ jsPcount hE s ω N p := by
  have hs0 : 0 < s := by omega
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hP0 : (0:ℝ) ≤ jsPcount hE s ω N p := Nat.cast_nonneg _
  have hj0 : (0:ℝ) ≤ j₀ := Nat.cast_nonneg _
  have hn0 : (0:ℝ) ≤ n₀ := Nat.cast_nonneg _
  by_cases hN : N ≤ n₀
  · have h1 : (N : ℝ) / (6 * K) ≤ N := div_le_self (Nat.cast_nonneg _) (by linarith)
    have h2 : (N : ℝ) ≤ n₀ := by exact_mod_cast hN
    linarith
  · push Not at hN
    have hNs : N ≤ s * N := Nat.le_mul_of_pos_left N hs0
    have hsN : 1 ≤ s * N := by omega
    have h1 := hpor p hp (s * N - 1) (by omega)
    have h2 := card_good_le (E := E) (c := c) (C := C) (t := t) (κ := κ) (j₀ := j₀) (p := p)
      hs0 hsN
    have h4 := card_Gω_le hE (C := C) (t := t) (j₀ := j₀) (N := N) (ω := ω) (p := p) hc hκ hs0
    have r1 : (s : ℝ) * N ≤ K * ((Finset.Icc j₀ (s * N - 1)).filter fun j =>
        ∃ q : ℂ, ball q (c * (2:ℝ)⁻¹ ^ j) ⊆ ball p (C * (2:ℝ)⁻¹ ^ j) \ E).card + 1 + j₀ := by
      have : s * N ≤ K * ((Finset.Icc j₀ (s * N - 1)).filter fun j =>
          ∃ q : ℂ, ball q (c * (2:ℝ)⁻¹ ^ j) ⊆ ball p (C * (2:ℝ)⁻¹ ^ j) \ E).card + 1 + j₀ := by
        omega
      exact_mod_cast this
    have r2 : (((Finset.Icc j₀ (s * N - 1)).filter fun j =>
        ∃ q : ℂ, ball q (c * (2:ℝ)⁻¹ ^ j) ⊆ ball p (C * (2:ℝ)⁻¹ ^ j) \ E).card : ℝ) ≤
        (jsGset E c C s t κ j₀ N p).card + N * (t + κ) := by exact_mod_cast h2
    have r3 : ((jsGset E c C s t κ j₀ N p).card : ℝ) ≤
        3 * (jsGωset E c C s t κ j₀ N ω p).card := by exact_mod_cast hω
    have r4 : ((jsGωset E c C s t κ j₀ N ω p).card : ℝ) ≤ s * jsPcount hE s ω N p := by
      exact_mod_cast h4
    have rs : (s : ℝ) = 2 * K * (t + κ) + 1 := by rw [hs]; push_cast; ring
    have hK0 : (0:ℝ) ≤ K := by linarith
    have m2 := mul_le_mul_of_nonneg_left r2 hK0
    have m3 := mul_le_mul_of_nonneg_left r3 hK0
    have m4 := mul_le_mul_of_nonneg_left r4 (by linarith : (0:ℝ) ≤ 3 * K)
    have e1 : 2 * ((K : ℝ) * (N * (t + κ))) = ((s : ℝ) - 1) * N := by rw [rs]; ring
    have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg _
    have r6 : (s : ℝ) * N ≤ 6 * K * s * jsPcount hE s ω N p + 2 * (1 + j₀) := by
      nlinarith
    have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs0
    have r7 : (N : ℝ) ≤ 6 * K * jsPcount hE s ω N p + 6 * K * (1 + j₀) := by
      by_contra hcon
      push Not at hcon
      have a1 := mul_lt_mul_of_pos_left hcon (by linarith : (0:ℝ) < s)
      have hKs : (1:ℝ) ≤ K * s := by nlinarith
      have a2 : 2 * (1 + (j₀ : ℝ)) ≤ 6 * K * s * (1 + j₀) := by nlinarith
      nlinarith
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    nlinarith

/-! ### The main estimate -/

/-- **Blueprint node D5.** A bounded mean porous set `E ⊆ ℂ` has thickenings of volume
`O(r^η)` for some `η > 0`. -/
theorem volume_thickening_le_of_meanPorous {E : Set ℂ} (hE : Bornology.IsBounded E) {c C : ℝ}
    {K j₀ n₀ : ℕ} (hc : 0 < c) (hK : 0 < K) (hpor : IsMeanPorous E c C K j₀ n₀) :
    ∃ C' η : ℝ, 0 < η ∧ ∀ r ∈ Set.Ioc (0:ℝ) 1,
      volume (thickening r E) ≤ ENNReal.ofReal (C' * r ^ η) := by
  classical
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (6 * C) (one_lt_two : (1:ℝ) < 2)
  obtain ⟨κ, hκ'⟩ := pow_unbounded_of_one_lt (2 / c) (one_lt_two : (1:ℝ) < 2)
  have hκ : 2 ≤ c * 2 ^ κ := by
    rw [div_lt_iff₀ hc] at hκ'
    linarith
  obtain ⟨s, hs⟩ : ∃ s, s = 2 * K * (t + κ) + 1 := ⟨_, rfl⟩
  have hs0 : 0 < s := by omega
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = 2 ^ s * 2 ^ s := ⟨_, rfl⟩
  have hb2 : 2 ≤ b := by
    have : 2 ≤ 2 ^ s := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs0
    rw [hb]
    nlinarith
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb2
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (b : ℝ) / ((b : ℝ) - 1) := ⟨_, rfl⟩
  have hlam1 : 1 < lam := by
    rw [hlam, lt_div_iff₀ (by linarith)]
    linarith
  have hloglam : 0 < Real.log lam := Real.log_pos hlam1
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = 1 + j₀ + n₀ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ ω ∈ Finset.range 3, ((jsT hE s ω 0).card : ℝ) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = (volume (ball (0:ℂ) 1)).toReal := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hVdef]; exact ENNReal.toReal_nonneg
  have hV : volume (ball (0:ℂ) 1) = ENNReal.ofReal V := by
    rw [hVdef, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  have hK6 : (0:ℝ) < 6 * K := by
    have : (1:ℝ) ≤ K := by exact_mod_cast hK
    linarith
  obtain ⟨Lk, hLk⟩ : ∃ Lk : ℝ, Lk = Real.log lam / (6 * K) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = Real.log lam / (6 * K * s * Real.log 2) := ⟨_, rfl⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsR : (0:ℝ) < s := by exact_mod_cast hs0
  have hη0 : 0 < η := by rw [hη]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = c₂ * Real.log lam + Lk := ⟨_, rfl⟩
  refine ⟨4 * A * Real.exp D * V, η, hη0, ?_⟩
  rintro r ⟨hr0, hr1⟩
  -- the level `N`
  have hex : ∃ n : ℕ, (2:ℝ)⁻¹ ^ (s * (n + 1)) < r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr0 (by norm_num : (2:ℝ)⁻¹ < 1)
    refine ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_) hn⟩
    have := Nat.le_mul_of_pos_left (n + 1) hs0
    omega
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, (2:ℝ)⁻¹ ^ (s * (N + 1)) < r ∧ r ≤ ((2:ℝ) ^ (s * N))⁻¹ := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rw [← inv_pow]
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, mul_zero, pow_zero]
      exact hr1
    · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rw [e] at this
      exact not_lt.mp this
  have hX : (0:ℝ) < 2 ^ (s * N) := by positivity
  -- the points whose best grid is `ω`
  let Eω : ℕ → Set ℂ := fun ω => {p ∈ E |
    (jsGset E c C s t κ j₀ N p).card ≤ 3 * (jsGωset E c C s t κ j₀ N ω p).card}
  have hfinL : ∀ ω, (jsIdx s ω N '' Eω ω).Finite := fun ω =>
    (finite_jsIdx_image hE s ω N).subset (Set.image_mono (fun p hp => hp.1))
  let L : ℕ → Finset (ℤ × ℤ) := fun ω => (hfinL ω).toFinset
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.exp ((N / (6 * K) - c₂) * Real.log lam) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ]; exact Real.exp_pos _
  -- counting
  have hcount : ∀ ω, ((L ω).card : ℝ) * (1 / (b : ℝ)) ^ N ≤ (jsT hE s ω 0).card * Q⁻¹ := by
    intro ω
    have hL : L ω ⊆ jsT hE s ω N := by
      intro ℓ hℓ
      simp only [L, Set.Finite.mem_toFinset] at hℓ
      rw [mem_jsT]
      obtain ⟨p, hp, rfl⟩ := hℓ
      exact ⟨p, hp.1, rfl⟩
    have hsum := sum_jsW_le (π := jsPar s) (T := jsT hE s ω) (b := b) hb2
      (jsPar_mem_jsT hE s ω) (fun k => hb ▸ jsPar_fiber s k) N
    have hW : ∀ ℓ ∈ L ω, (1 / (b : ℝ)) ^ N * Q ≤ jsW (jsPar s) (jsT hE s ω) b N ℓ := by
      intro ℓ hℓ
      simp only [L, Set.Finite.mem_toFinset] at hℓ
      obtain ⟨p, ⟨hpE, hpω⟩, rfl⟩ := hℓ
      rw [jsW_chain (fun m => jsIdx s ω m) p (fun m => jsPar_jsIdx s ω m p) N,
        prod_jsF_eq hb2 (fun i => jsIdx s ω i p) N]
      have hP := porous_count_bound hE hc hK hpor hκ hs hpE hpω
      unfold jsPcount at hP
      rw [← hc₂] at hP
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hQ, ← hlam]
      calc Real.exp ((N / (6 * K) - c₂) * Real.log lam)
          ≤ Real.exp (((Finset.range N).filter fun i =>
              jsPorous (jsPar s) (jsT hE s ω) i (jsIdx s ω i p)).card * Real.log lam) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hP hloglam.le)
        _ = lam ^ ((Finset.range N).filter fun i =>
              jsPorous (jsPar s) (jsT hE s ω) i (jsIdx s ω i p)).card := by
            rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    have h1 : ((L ω).card : ℝ) * ((1 / (b : ℝ)) ^ N * Q) ≤ (jsT hE s ω 0).card := by
      calc ((L ω).card : ℝ) * ((1 / (b : ℝ)) ^ N * Q)
          = ∑ ℓ ∈ L ω, (1 / (b : ℝ)) ^ N * Q := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ ℓ ∈ L ω, jsW (jsPar s) (jsT hE s ω) b N ℓ := Finset.sum_le_sum hW
        _ ≤ ∑ ℓ ∈ jsT hE s ω N, jsW (jsPar s) (jsT hE s ω) b N ℓ :=
            Finset.sum_le_sum_of_subset_of_nonneg hL (fun _ _ _ => jsW_nonneg hb2 _ _)
        _ ≤ _ := hsum
    rw [le_mul_inv_iff₀ hQ0]
    calc ((L ω).card : ℝ) * (1 / (b : ℝ)) ^ N * Q
        = ((L ω).card : ℝ) * ((1 / (b : ℝ)) ^ N * Q) := by ring
      _ ≤ _ := h1
  -- covering
  have hcover : thickening r E ⊆ ⋃ ω ∈ Finset.range 3, ⋃ ℓ ∈ L ω,
      ball (jsCenter s ω N ℓ) (2 * ((2:ℝ) ^ (s * N))⁻¹) := by
    intro w hw
    rw [mem_thickening_iff] at hw
    obtain ⟨z, hzE, hwz⟩ := hw
    obtain ⟨ω, hω3, hzω⟩ := exists_omega_card (E := E) (c := c) (C := C) (s := s) (κ := κ)
      (j₀ := j₀) (N := N) hc ht z
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨ω, Finset.mem_range.mpr hω3, jsIdx s ω N z, ?_, ?_⟩
    · simp only [L, Set.Finite.mem_toFinset]
      exact ⟨z, ⟨hzE, hzω⟩, rfl⟩
    · rw [mem_ball]
      have hcz := norm_sub_jsCenter_le s ω N z
      calc dist w (jsCenter s ω N (jsIdx s ω N z))
          ≤ dist w z + dist z (jsCenter s ω N (jsIdx s ω N z)) := dist_triangle _ _ _
        _ < r + ((2:ℝ) ^ (s * N))⁻¹ := by rw [dist_eq_norm z]; linarith
        _ ≤ 2 * ((2:ℝ) ^ (s * N))⁻¹ := by linarith
  -- the exponent
  have hlogr : -((s : ℝ) * (N + 1) * Real.log 2) < Real.log r := by
    have := Real.log_lt_log (by positivity) hN1
    rw [Real.log_pow, Real.log_inv] at this
    push_cast at this
    linarith
  have hηs : η * ((s : ℝ) * (N + 1) * Real.log 2) = ((N : ℝ) + 1) * Lk := by
    rw [hη, hLk]
    field_simp
  have key : -((N / (6 * K) - c₂) * Real.log lam) ≤ D + Real.log r * η := by
    have m := mul_le_mul_of_nonneg_left hlogr.le hη0.le
    have e1 : (N / (6 * K) - c₂) * Real.log lam = N * Lk - c₂ * Real.log lam := by
      rw [hLk]; ring
    rw [e1, hD]
    nlinarith
  have hQinv : Q⁻¹ ≤ Real.exp D * r ^ η := by
    rw [hQ, ← Real.exp_neg, Real.rpow_def_of_pos hr0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr key
  have hXb : (2 * ((2:ℝ) ^ (s * N))⁻¹) ^ 2 = 4 * (1 / (b : ℝ)) ^ N := by
    have e : ((2:ℝ) ^ s * 2 ^ s) ^ N = (2 ^ (s * N)) ^ 2 := by
      rw [mul_pow, ← pow_mul, sq]
    rw [hb, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, one_div, inv_pow, e, mul_pow, inv_pow]
    norm_num
  have hball : ∀ x : ℂ, volume (ball x (2 * ((2:ℝ) ^ (s * N))⁻¹)) =
      ENNReal.ofReal ((2 * ((2:ℝ) ^ (s * N))⁻¹) ^ 2 * V) := by
    intro x
    rw [Measure.addHaar_ball volume x (by positivity), Complex.finrank_real_complex, hV,
      ← ENNReal.ofReal_mul (by positivity)]
  calc volume (thickening r E)
      ≤ volume (⋃ ω ∈ Finset.range 3, ⋃ ℓ ∈ L ω,
          ball (jsCenter s ω N ℓ) (2 * ((2:ℝ) ^ (s * N))⁻¹)) := measure_mono hcover
    _ ≤ ∑ ω ∈ Finset.range 3, volume (⋃ ℓ ∈ L ω,
          ball (jsCenter s ω N ℓ) (2 * ((2:ℝ) ^ (s * N))⁻¹)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ ω ∈ Finset.range 3, ∑ ℓ ∈ L ω,
          volume (ball (jsCenter s ω N ℓ) (2 * ((2:ℝ) ^ (s * N))⁻¹)) :=
        Finset.sum_le_sum fun ω _ => measure_biUnion_finset_le _ _
    _ = ∑ ω ∈ Finset.range 3,
          ENNReal.ofReal ((L ω).card * ((2 * ((2:ℝ) ^ (s * N))⁻¹) ^ 2 * V)) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        simp only [hball, Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∑ ω ∈ Finset.range 3,
          (L ω).card * ((2 * ((2:ℝ) ^ (s * N))⁻¹) ^ 2 * V)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ ≤ ENNReal.ofReal (4 * A * Real.exp D * V * r ^ η) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∑ ω ∈ Finset.range 3, (L ω).card * ((2 * ((2:ℝ) ^ (s * N))⁻¹) ^ 2 * V)
            = ∑ ω ∈ Finset.range 3, 4 * V * ((L ω).card * (1 / (b : ℝ)) ^ N) := by
              refine Finset.sum_congr rfl fun ω _ => ?_
              rw [hXb]; ring
          _ ≤ ∑ ω ∈ Finset.range 3, 4 * V * ((jsT hE s ω 0).card * Q⁻¹) :=
              Finset.sum_le_sum fun ω _ =>
                mul_le_mul_of_nonneg_left (hcount ω) (by positivity)
          _ = 4 * V * A * Q⁻¹ := by
              rw [hA, Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun ω _ => by ring
          _ ≤ 4 * V * A * (Real.exp D * r ^ η) :=
              mul_le_mul_of_nonneg_left hQinv (by positivity)
          _ = 4 * A * Real.exp D * V * r ^ η := by ring

end QuantumZipper.JS
