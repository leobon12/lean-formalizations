import HigherDimLQGMetric.DGZ.FoldDefs
import HigherDimLQGMetric.DGZ.FreeSites

/-!
# Folding and box surgery (packet L3a2, MA7 D-BOX)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.9, around half (TeX l. 1898 and its
footnote, p. 36): "there exists an open cluster … that encloses `B_{r₂}(0)` … connect `l₁` and `l₂`
… inside this open cluster … contained within `B`" — a duality inside a box, used without proof.
Planning audit `planning/audits/MA7-ref2-sections-4-6.md`, gap G3(a) and Details (a) D-BOX; the
statement shapes are those of Details (c) §A (`DGZ/FoldDefs.lean`).

Main results (namespace `HigherDimLQGMetric.DGZ`):

* `foldSmall (d) : FoldSmall d` (D-BOX (i), every `d`): if the closed clusters of `O ∪ Λᶜ`
  (`Λ = latBox a b`, sides `> 2D + 2`) have diameter `≤ D`, the folded configuration
  `foldBox a b ⁻¹' O` has bounded closed clusters of diameter `≤ 2D + 1`;
* `boxSurgery (d) (_ : 2 ≤ d) : BoxSurgery d` (D-BOX (ii); the proof works for every `d`,
  `boxSurgery_of_any`): two sites that are free for the folded configuration are joined by an
  L-path of open sites of `Λ` within `2D + 2` of any reference L-path in `Λ` between them.

Properties of the folding `foldZ a b` (`L = b - a + 1 > 0`), MA7 D-BOX (α)–(γ):

* (α) `foldZ_of_mem`: the identity on `[a, b]`; `foldZ_mem_Icc`: values in `[a, b]`;
* (β) `abs_foldZ_sub_le`: 1-Lipschitz (from the one-step bound `abs_foldZ_add_one_sub_le`);
* sheets: on `[a + kL, a + kL + L - 1]` the folding is `t ↦ t - kL` (`k` even) or
  `t ↦ a + b + kL - t` (`k` odd) (`foldZ_sheet`), hence an isometry there
  (`abs_foldZ_sub_eq_of_sheet`);
* (γ), in the form used: `sub_le_of_abs_foldZ_sub_le` — if `foldZ` varies by at most `D` on an
  integer interval `[t, t']` and `D + 1 ≤ b - a`, then `t' - t ≤ 2D + 1`. (An interval meeting three
  sheets contains a whole sheet, on which `foldZ` varies by `b - a > D`; an interval inside one or
  two sheets is the union of at most two pieces on which `foldZ` is an isometry.)

Proof of `FoldSmall` (MA7 D-BOX). Let `C` be a closed cluster of `foldBox⁻¹(O)`. The folding maps
`*`-adjacent sites to equal or `*`-adjacent sites (β) and maps into `Λ`, so `foldBox(C)` is a
`*`-connected set of closed sites of `O ∪ Λᶜ` and lies in one closed cluster `C₀`, of diameter
`≤ D` (`exists_isClosedCluster_superset`). In each coordinate `i`, the values `z i`, `z ∈ C`, fill
an integer interval (`exists_mem_apply_eq_of_reflTransGen`, a discrete intermediate value property
along `*`-paths), on which `foldZ` varies by at most `D`; by (γ) this interval has length
`≤ 2D + 1`.

Proof of `BoxSurgery`. By `FoldSmall`, `SmallClusters (foldBox⁻¹ O) (2D + 1)`; free surgery
(`freeSurgery`, MA7 D-FS(i)) for the folded configuration gives an open L-path within `2D + 2` of
the reference path `γ`; its image under `foldBox` is an L-path (consecutive images are equal or
L-adjacent) of sites of `O ∩ Λ` with the same endpoints (α), and the distance to `γ ⊆ Λ` does not
increase (β, α).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open Relation Set

variable {d : ℕ}

/-! ### The folding of `ℤ` -/

section FoldZ

variable {a b : ℤ}

/-- The residue `(t - a) mod 2(b - a + 1)` lies in `[0, 2(b - a + 1))`. -/
lemma foldZ_res_bounds (hab : a ≤ b) (t : ℤ) :
    0 ≤ (t - a) % (2 * (b - a + 1)) ∧ (t - a) % (2 * (b - a + 1)) < 2 * (b - a + 1) :=
  ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

/-- **(range)** `foldZ` takes values in `[a, b]`. -/
lemma foldZ_mem_Icc (hab : a ≤ b) (t : ℤ) : a ≤ foldZ a b t ∧ foldZ a b t ≤ b := by
  obtain ⟨h0, h1⟩ := foldZ_res_bounds hab t
  unfold foldZ
  generalize (t - a) % (2 * (b - a + 1)) = r at *
  split_ifs <;> omega

/-- **MA7 D-BOX (α)**: `foldZ` is the identity on `[a, b]`. -/
lemma foldZ_of_mem {t : ℤ} (ha : a ≤ t) (hb : t ≤ b) : foldZ a b t = t := by
  have h : (t - a) % (2 * (b - a + 1)) = t - a := Int.emod_eq_of_lt (by omega) (by omega)
  unfold foldZ
  rw [h, ite_eq_left (by omega)]
  ring

/-- The residue of `t + 1` is the residue of `t` plus one, or `0` after a full period. -/
lemma foldZ_res_succ (hab : a ≤ b) (t : ℤ) :
    (t + 1 - a) % (2 * (b - a + 1)) = (t - a) % (2 * (b - a + 1)) + 1 ∨
      ((t - a) % (2 * (b - a + 1)) = 2 * (b - a + 1) - 1 ∧
        (t + 1 - a) % (2 * (b - a + 1)) = 0) := by
  obtain ⟨h0, h1⟩ := foldZ_res_bounds hab t
  have e : t + 1 - a = (t - a) + 1 := by ring
  rw [e, Int.add_emod, Int.emod_eq_of_lt (b := 2 * (b - a + 1)) zero_le_one (by omega)]
  rcases lt_or_eq_of_le (show (t - a) % (2 * (b - a + 1)) + 1 ≤ 2 * (b - a + 1) by omega) with
    h | h
  · left
    exact Int.emod_eq_of_lt (by omega) h
  · right
    refine ⟨by omega, ?_⟩
    rw [h, Int.emod_self]

/-- One step of `foldZ` moves by at most `1`. -/
lemma abs_foldZ_add_one_sub_le (hab : a ≤ b) (t : ℤ) :
    |foldZ a b (t + 1) - foldZ a b t| ≤ 1 := by
  have hs := foldZ_res_succ hab t
  obtain ⟨h0, h1⟩ := foldZ_res_bounds hab t
  obtain ⟨h0', h1'⟩ := foldZ_res_bounds hab (t + 1)
  unfold foldZ
  generalize (t - a) % (2 * (b - a + 1)) = r at *
  generalize (t + 1 - a) % (2 * (b - a + 1)) = r' at *
  rw [abs_le]
  split_ifs <;> omega

lemma abs_foldZ_add_natCast_sub_le (hab : a ≤ b) (t : ℤ) (n : ℕ) :
    |foldZ a b (t + n) - foldZ a b t| ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := abs_foldZ_add_one_sub_le hab (t + n)
    have e : t + ((n + 1 : ℕ) : ℤ) = t + n + 1 := by push_cast; ring
    rw [e]
    calc |foldZ a b (t + n + 1) - foldZ a b t|
        ≤ |foldZ a b (t + n + 1) - foldZ a b (t + n)| + |foldZ a b (t + n) - foldZ a b t| :=
          abs_sub_le _ _ _
      _ ≤ 1 + n := add_le_add h1 ih
      _ = ((n + 1 : ℕ) : ℤ) := by push_cast; ring

/-- **MA7 D-BOX (β)**: `foldZ` is 1-Lipschitz. -/
lemma abs_foldZ_sub_le (hab : a ≤ b) (t t' : ℤ) :
    |foldZ a b t - foldZ a b t'| ≤ |t - t'| := by
  rcases le_total t' t with h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = t' + n := ⟨(t - t').toNat, by omega⟩
    rw [hn, show t' + (n : ℤ) - t' = n by ring, Nat.abs_cast]
    exact abs_foldZ_add_natCast_sub_le hab t' n
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t' = t + n := ⟨(t' - t).toNat, by omega⟩
    rw [hn, abs_sub_comm (foldZ a b t), abs_sub_comm t, show t + (n : ℤ) - t = n by ring,
      Nat.abs_cast]
    exact abs_foldZ_add_natCast_sub_le hab t n

/-- **Sheets.** On the sheet `[a + kL, a + kL + L - 1]` (`L = b - a + 1`) the folding is the
translation `t ↦ t - kL` for even `k` and the reflection `t ↦ a + b + kL - t` for odd `k`. -/
lemma foldZ_sheet (hab : a ≤ b) {k t : ℤ} (h0 : (b - a + 1) * k ≤ t - a)
    (h1 : t - a < (b - a + 1) * k + (b - a + 1)) :
    (Even k → foldZ a b t = t - (b - a + 1) * k) ∧
      (Odd k → foldZ a b t = a + b + (b - a + 1) * k - t) := by
  constructor
  · rintro ⟨m, rfl⟩
    have hr : (t - a) % (2 * (b - a + 1)) = t - a - (b - a + 1) * (m + m) := by
      have e : t - a = (t - a - (b - a + 1) * (m + m)) + 2 * (b - a + 1) * m := by ring
      calc (t - a) % (2 * (b - a + 1))
          = ((t - a - (b - a + 1) * (m + m)) + 2 * (b - a + 1) * m) % (2 * (b - a + 1)) := by
            rw [← e]
        _ = (t - a - (b - a + 1) * (m + m)) % (2 * (b - a + 1)) :=
            Int.add_mul_emod_self_left _ _ _
        _ = t - a - (b - a + 1) * (m + m) := Int.emod_eq_of_lt (by omega) (by omega)
    unfold foldZ
    rw [hr, ite_eq_left (by omega)]
    ring
  · rintro ⟨m, rfl⟩
    have hr : (t - a) % (2 * (b - a + 1)) =
        t - a - (b - a + 1) * (2 * m + 1) + (b - a + 1) := by
      have e : t - a = (t - a - (b - a + 1) * (2 * m + 1) + (b - a + 1)) +
          2 * (b - a + 1) * m := by ring
      calc (t - a) % (2 * (b - a + 1))
          = ((t - a - (b - a + 1) * (2 * m + 1) + (b - a + 1)) + 2 * (b - a + 1) * m) %
              (2 * (b - a + 1)) := by
            rw [← e]
        _ = (t - a - (b - a + 1) * (2 * m + 1) + (b - a + 1)) % (2 * (b - a + 1)) :=
            Int.add_mul_emod_self_left _ _ _
        _ = t - a - (b - a + 1) * (2 * m + 1) + (b - a + 1) :=
            Int.emod_eq_of_lt (by omega) (by omega)
    unfold foldZ
    rw [hr, ite_eq_right (by omega)]
    ring

/-- On one sheet the folding is an isometry. -/
lemma abs_foldZ_sub_eq_of_sheet (hab : a ≤ b) {k s s' : ℤ}
    (hs0 : (b - a + 1) * k ≤ s - a) (hs1 : s - a < (b - a + 1) * k + (b - a + 1))
    (hs0' : (b - a + 1) * k ≤ s' - a) (hs1' : s' - a < (b - a + 1) * k + (b - a + 1)) :
    |foldZ a b s - foldZ a b s'| = |s - s'| := by
  rcases Int.even_or_odd k with hk | hk
  · rw [(foldZ_sheet hab hs0 hs1).1 hk, (foldZ_sheet hab hs0' hs1').1 hk]
    congr 1
    ring
  · rw [(foldZ_sheet hab hs0 hs1).2 hk, (foldZ_sheet hab hs0' hs1').2 hk, abs_sub_comm s s']
    congr 1
    ring

/-- **MA7 D-BOX (γ), in the form used.** If `D + 1 ≤ b - a` and `foldZ` varies by at most `D` on
the integer interval `[t, t']`, then `t' - t ≤ 2D + 1`. -/
lemma sub_le_of_abs_foldZ_sub_le {D : ℤ} (hD : D + 1 ≤ b - a) {t t' : ℤ} (htt' : t ≤ t')
    (hvar : ∀ s, t ≤ s → s ≤ t' → ∀ s', t ≤ s' → s' ≤ t' →
      |foldZ a b s - foldZ a b s'| ≤ D) :
    t' - t ≤ 2 * D + 1 := by
  have hD0 : 0 ≤ D := by
    have h := hvar t le_rfl htt' t le_rfl htt'
    rwa [sub_self, abs_zero] at h
  have hab : a ≤ b := by omega
  -- the sheet `k` of `t`
  obtain ⟨k, hk0, hk1⟩ : ∃ k, (b - a + 1) * k ≤ t - a ∧ t - a < (b - a + 1) * k + (b - a + 1) := by
    refine ⟨(t - a) / (b - a + 1), ?_, ?_⟩ <;>
      have h := Int.mul_ediv_add_emod (t - a) (b - a + 1) <;>
      have h0 := Int.emod_nonneg (t - a) (show b - a + 1 ≠ 0 by omega) <;>
      have h1 := Int.emod_lt_of_pos (t - a) (show 0 < b - a + 1 by omega) <;>
      omega
  have e1 : (b - a + 1) * (k + 1) = (b - a + 1) * k + (b - a + 1) := by ring
  by_cases hA : t' - a < (b - a + 1) * k + (b - a + 1)
  · -- `t'` lies on the sheet of `t`
    have h := abs_foldZ_sub_eq_of_sheet hab hk0 hk1 (s' := t') (by omega) hA
    have hv := hvar t le_rfl htt' t' htt' le_rfl
    rw [h, abs_sub_comm, abs_of_nonneg (by omega)] at hv
    omega
  by_cases hB : t' - a < (b - a + 1) * k + 2 * (b - a + 1)
  · -- `t'` lies on the next sheet: split at `m = a + (k + 1) L`
    set m := a + (b - a + 1) * k + (b - a + 1) with hm
    have h1 := abs_foldZ_sub_eq_of_sheet hab hk0 hk1 (s' := m - 1) (by omega) (by omega)
    have h2 := abs_foldZ_sub_eq_of_sheet hab (k := k + 1) (s := t') (s' := m) (by omega)
      (by omega) (by omega) (by omega)
    have hv1 := hvar t le_rfl htt' (m - 1) (by omega) (by omega)
    have hv2 := hvar t' htt' le_rfl m (by omega) (by omega)
    rw [h1, abs_sub_comm, abs_of_nonneg (by omega)] at hv1
    rw [h2, abs_of_nonneg (by omega)] at hv2
    omega
  · -- the whole next sheet lies in `[t, t']`, and `foldZ` varies by `b - a > D` on it
    exfalso
    set m := a + (b - a + 1) * k + (b - a + 1) with hm
    have h := abs_foldZ_sub_eq_of_sheet hab (k := k + 1) (s := m + (b - a)) (s' := m) (by omega)
      (by omega) (by omega) (by omega)
    have hv := hvar (m + (b - a)) (by omega) (by omega) m (by omega) (by omega)
    rw [h, abs_of_nonneg (by omega)] at hv
    omega

end FoldZ

/-! ### Lattice paths under maps -/

/-- An L-step changes one coordinate by `1` and keeps the others. -/
lemma exists_coord_of_lAdj {x y : Zd d} (h : LAdj x y) :
    ∃ i, (∀ k, k ≠ i → x k = y k) ∧ |x i - y i| = 1 := by
  obtain ⟨i, hi | hi⟩ := h.exists_eq_add_single
  · refine ⟨i, fun k hk => ?_, ?_⟩
    · rw [hi, add_single_apply_of_ne x hk]
    · rw [hi, add_single_apply_self]
      simp
  · refine ⟨i, fun k hk => ?_, ?_⟩
    · rw [hi, add_single_apply_of_ne y hk]
    · rw [hi, add_single_apply_self]
      simp

/-- Sites that differ by `1` in one coordinate and agree elsewhere are L-adjacent. -/
lemma lAdj_of_coord {x y : Zd d} (i : Fin d) (hne : ∀ k, k ≠ i → x k = y k)
    (hi : |x i - y i| = 1) : LAdj x y := by
  unfold LAdj
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [hne k hk, sub_self, abs_zero])
    (fun h => absurd (Finset.mem_univ i) h)]
  exact hi

/-- A map sending each `adj`-step to an `adj`-step or to a constant step maps `adj`-paths in `S`
to `adj`-paths in `T` (if it maps `S` into `T`). -/
lemma reflTransGen_stepIn_map {S T : Set (Zd d)} {adj : Zd d → Zd d → Prop} (f : Zd d → Zd d)
    (hST : ∀ x ∈ S, f x ∈ T) (hadj : ∀ x y, adj x y → f x = f y ∨ adj (f x) (f y))
    {x y : Zd d} (h : ReflTransGen (StepIn S adj) x y) :
    ReflTransGen (StepIn T adj) (f x) (f y) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b c _ hbc ih =>
    rcases hadj b c hbc.2.2 with he | he
    · rw [← he]
      exact ih
    · exact ih.tail ⟨hST b hbc.1, hST c hbc.2.1, he⟩

/-- **Discrete intermediate values.** Along a path whose steps are `ℓ^∞`-steps of size `≤ 1`, each
coordinate takes every integer value between its values at the two ends. -/
lemma exists_mem_apply_eq_of_reflTransGen {S : Set (Zd d)} {adj : Zd d → Zd d → Prop}
    (hadj : ∀ x y, adj x y → WithinInf 1 x y) {x y : Zd d} (hx : x ∈ S)
    (h : ReflTransGen (StepIn S adj) x y) (i : Fin d) :
    ∀ s, min (x i) (y i) ≤ s → s ≤ max (x i) (y i) → ∃ z ∈ S, z i = s := by
  induction h with
  | refl =>
    intro s h1 h2
    exact ⟨x, hx, by omega⟩
  | @tail b c _ hbc ih =>
    intro s h1 h2
    by_cases hs : min (x i) (b i) ≤ s ∧ s ≤ max (x i) (b i)
    · exact ih s hs.1 hs.2
    · have hbc1 := hadj _ _ hbc.2.2 i
      rw [abs_le] at hbc1
      rw [not_and_or, not_le, not_le] at hs
      exact ⟨c, hbc.2.1, by omega⟩

/-! ### The folding of `ℤ^d` -/

section FoldBox

variable {a b : Zd d}

/-- The folding maps into the box. -/
lemma foldBox_mem_latBox (hab : ∀ i, a i ≤ b i) (x : Zd d) : foldBox a b x ∈ latBox a b :=
  fun i => foldZ_mem_Icc (hab i) (x i)

/-- The folding is the identity on the box (MA7 D-BOX (α)). -/
lemma foldBox_of_mem {x : Zd d} (hx : x ∈ latBox a b) : foldBox a b x = x :=
  funext fun i => foldZ_of_mem (hx i).1 (hx i).2

/-- The folding does not increase `ℓ^∞`-distances (MA7 D-BOX (β)). -/
lemma withinInf_foldBox (hab : ∀ i, a i ≤ b i) {r : ℤ} {x y : Zd d} (h : WithinInf r x y) :
    WithinInf r (foldBox a b x) (foldBox a b y) :=
  fun i => (abs_foldZ_sub_le (hab i) (x i) (y i)).trans (h i)

/-- `*`-adjacent sites have equal or `*`-adjacent foldings. -/
lemma foldBox_eq_or_sAdj (hab : ∀ i, a i ≤ b i) {x y : Zd d} (h : SAdj x y) :
    foldBox a b x = foldBox a b y ∨ SAdj (foldBox a b x) (foldBox a b y) := by
  by_cases he : foldBox a b x = foldBox a b y
  · exact Or.inl he
  · exact Or.inr ⟨he, withinInf_foldBox hab h.withinInf⟩

/-- L-adjacent sites have equal or L-adjacent foldings. -/
lemma foldBox_eq_or_lAdj (hab : ∀ i, a i ≤ b i) {x y : Zd d} (h : LAdj x y) :
    foldBox a b x = foldBox a b y ∨ LAdj (foldBox a b x) (foldBox a b y) := by
  obtain ⟨i, hne, hi⟩ := exists_coord_of_lAdj h
  have hne' : ∀ k, k ≠ i → foldBox a b x k = foldBox a b y k := fun k hk => by
    simp only [foldBox, hne k hk]
  have hle : |foldBox a b x i - foldBox a b y i| ≤ 1 :=
    (abs_foldZ_sub_le (hab i) (x i) (y i)).trans hi.le
  by_cases he : foldBox a b x i = foldBox a b y i
  · left
    funext k
    by_cases hk : k = i
    · rw [hk]
      exact he
    · exact hne' k hk
  · right
    refine lAdj_of_coord i hne' ?_
    have h0 : foldBox a b x i - foldBox a b y i ≠ 0 := sub_ne_zero.2 he
    rw [abs_le] at hle
    rcases lt_or_gt_of_ne h0 with h0 | h0
    · rw [abs_of_neg h0]
      omega
    · rw [abs_of_pos h0]
      omega

end FoldBox

/-! ### MA7 D-BOX (i): folding keeps clusters small -/

/-- **MA7 D-BOX (i): `FoldSmall`** (every `d`). If the closed clusters of `O ∪ Λᶜ`
(`Λ = latBox a b`, all sides `bᵢ - aᵢ > 2D + 2`) have diameter `≤ D`, then the closed clusters of
the folded configuration `foldBox a b ⁻¹' O` are bounded with diameter `≤ 2D + 1`. -/
theorem foldSmall (d : ℕ) : FoldSmall d := by
  intro O a b D hab hsmall C hC
  have hab' : ∀ i, a i ≤ b i := fun i => by have := hab i; omega
  -- the folding of `C` is a `*`-connected set of closed sites of `O ∪ Λᶜ`
  have hconn : ConnIn (foldBox a b '' C) SAdj := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    exact reflTransGen_stepIn_map (foldBox a b) (fun x hx => mem_image_of_mem _ hx)
      (fun x y h => foldBox_eq_or_sAdj hab' h) (hC.2.2.1 y hy y' hy')
  have hclosed : foldBox a b '' C ⊆ (O ∪ (latBox a b)ᶜ)ᶜ := by
    rintro _ ⟨y, hy, rfl⟩ h
    rcases h with h | h
    · exact hC.2.1 hy h
    · exact h (foldBox_mem_latBox hab' y)
  obtain ⟨c, hc⟩ := hC.1
  obtain ⟨C₀, hC₀, hsub⟩ :=
    exists_isClosedCluster_superset hconn hclosed (mem_image_of_mem _ hc)
  have hdiam₀ := (hsmall C₀ hC₀).2
  -- in each coordinate the values on `C` form an integer interval of length `≤ 2D + 1`
  have key : ∀ y ∈ C, ∀ y' ∈ C, ∀ i, y i ≤ y' i → y' i - y i ≤ 2 * (D : ℤ) + 1 := by
    intro y hy y' hy' i hle
    have hpath := hC.2.2.1 y hy y' hy'
    refine sub_le_of_abs_foldZ_sub_le (a := a i) (b := b i) (by have := hab i; omega) hle ?_
    intro s hs1 hs2 s' hs1' hs2'
    obtain ⟨z, hz, rfl⟩ := exists_mem_apply_eq_of_reflTransGen (fun _ _ h => h.withinInf) hy
      hpath i s (by omega) (by omega)
    obtain ⟨z', hz', rfl⟩ := exists_mem_apply_eq_of_reflTransGen (fun _ _ h => h.withinInf) hy
      hpath i s' (by omega) (by omega)
    exact hdiam₀ _ (hsub (mem_image_of_mem _ hz)) _ (hsub (mem_image_of_mem _ hz')) i
  have hdiam : ∀ y ∈ C, ∀ y' ∈ C, WithinInf ((2 * D + 1 : ℕ) : ℤ) y y' := by
    intro y hy y' hy' i
    push_cast
    rw [abs_le]
    rcases le_total (y i) (y' i) with h | h
    · have := key y hy y' hy' i h
      constructor <;> omega
    · have := key y' hy' y hy i h
      constructor <;> omega
  refine ⟨?_, hdiam⟩
  obtain ⟨M, hM⟩ := exists_withinInf_of_list [c]
  exact ⟨_, fun y hy => (hdiam y hy c hc).trans (hM c (List.mem_singleton_self c))⟩

/-! ### MA7 D-BOX (ii): box surgery -/

/-- **MA7 D-BOX (ii): box surgery, for every `d`.** -/
theorem boxSurgery_of_any (d : ℕ) : BoxSurgery d := by
  intro O a b D hab hsmall γ u v hγ hγΛ hu hv hfu hfv
  have hab' : ∀ i, a i ≤ b i := fun i => by have := hab i; omega
  have hpath := freeSurgery d _ _ (foldSmall d O a b D hab hsmall) γ u v hγ hu hv hfu hfv
  have huΛ : u ∈ latBox a b := hγΛ u (List.mem_of_mem_head? hu)
  have hvΛ : v ∈ latBox a b := hγΛ v (List.mem_of_mem_getLast? hv)
  have e : (((2 * D + 1 : ℕ) : ℤ) + 1) = 2 * (D : ℤ) + 2 := by push_cast; ring
  have hmap := reflTransGen_stepIn_map (foldBox a b)
    (T := {y | y ∈ O ∩ latBox a b ∧ ∃ x ∈ γ, WithinInf (2 * (D : ℤ) + 2) y x})
    (fun y hy => by
      obtain ⟨hyO, x, hxγ, hyx⟩ := hy
      refine ⟨⟨hyO, foldBox_mem_latBox hab' y⟩, x, hxγ, ?_⟩
      rw [← foldBox_of_mem (hγΛ x hxγ), ← e]
      exact withinInf_foldBox hab' hyx)
    (fun x y h => foldBox_eq_or_lAdj hab' h) hpath
  rwa [foldBox_of_mem huΛ, foldBox_of_mem hvΛ] at hmap

/-- **MA7 D-BOX (ii): `BoxSurgery`** (MA7 §5 row L3a2 target form; the hypothesis `2 ≤ d` is not
used, see `boxSurgery_of_any`). Rerouting inside a lattice box: two sites that are free for the
folded configuration are joined by an L-path of open sites of the box within `2D + 2` of any
reference L-path in the box between them. -/
theorem boxSurgery (d : ℕ) (_hd : 2 ≤ d) : BoxSurgery d :=
  boxSurgery_of_any d

end DGZ

end HigherDimLQGMetric
