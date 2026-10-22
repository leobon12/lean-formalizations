import HigherDimLQGMetric.DGZ.DiscretizeDefs

/-!
# Discretization of continuous paths (packet L3a2, MA7 D-DISC)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 5.12(1) (TeX l. 2641–2647) and the
discretizations in Lemmas 4.1, 4.9, 4.10; planning audit `planning/audits/MA7-ref2-sections-4-6.md`,
gap G13 and Details (a) D-DISC (generalizing HigherDimLFPP's `exists_latticePath`); statement shapes
in `DGZ/DiscretizeDefs.lean`.

Main results (namespace `HigherDimLQGMetric.DGZ`):

* `exists_discretization` (the working form, on any parameter interval `[t₀, t₁]`): for mesh
  `s > 0`, a lattice point `c`, `N ≥ 1` and a continuous path `P : [t₀, t₁] → obox (s c) (s N)`,
  there is a **duplicate-free** L-path of sites `x` with `|x - c|_∞ ≤ N - 1` (hence
  `obox (s x) s ⊆ obox (s c) (s N)`), each open box `obox (s x) s` meeting `P`, the first containing
  `P t₀` and the last containing `P t₁`;
* `discretizeOpen (d) : DiscretizeLemmaOpen d` (open variant) and
  `discretize (d) : DiscretizeLemma d` (closed variant, MA7 Details (c) §B), for every `d`;
* `obox_latPt_subset_iff`: `obox (s x) s ⊆ obox (s c) (s N) ↔ |x - c|_∞ ≤ N - 1`.

Proof (MA7 D-DISC, lattice units `s = 1`). For `z ∈ Ω = obox(c, N)` let `T(z)` be the set of sites
`x` with `|x - c|_∞ ≤ N - 1` and `|xᵢ - zᵢ| < 1` for all `i`; it is a product of nonempty integer
intervals of length `≤ 2`. If `|z - z'|_∞ ≤ 1/2` then `T(z) ∩ T(z') ≠ ∅`
(`exists_int_abs_sub_lt_one`: in each coordinate, `⌊max(zᵢ, z'ᵢ)⌋` works unless it is `≤ cᵢ - N`,
and then `cᵢ - N + 1` works). By uniform continuity choose `M` with `|P τ - P τ'|_∞ ≤ 1/2` for
`|τ - τ'| ≤ (t₁ - t₀)/M`, put `τⱼ = t₀ + j (t₁ - t₀)/M`, pick `yⱼ ∈ T(P τⱼ) ∩ T(P τⱼ₊₁)`
(`j < M`), and join `yⱼ` to `yⱼ₊₁` by the coordinate path of `Perc.reflTransGen_cube`, which stays
in the product set `T(P τⱼ₊₁)`. The open-box variant implies the closed one (`obox ⊆ cbox`).
Loop erasure is HigherDimLFPP's `exists_nodup_isChain_of_reflTransGen`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

namespace DGZ

open Set Relation
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox mem_obox_self abs_apply_le_norm
  exists_nodup_isChain_of_reflTransGen)

variable {d : ℕ}

/-! ### One coordinate -/

/-- **A common admissible integer** (MA7 D-DISC, one coordinate, lattice units). If `u, u'` lie in
`(c - N, c + N)` (`N ≥ 1`) and `|u - u'| ≤ 1/2`, some integer `x` with `|x - c| ≤ N - 1` lies at
distance `< 1` from both. -/
lemma exists_int_abs_sub_lt_one (c : ℤ) {N : ℕ} (hN : 1 ≤ N) {u u' : ℝ}
    (hu : |u - c| < N) (hu' : |u' - c| < N) (huu' : |u - u'| ≤ 1 / 2) :
    ∃ x : ℤ, |u - x| < 1 ∧ |u' - x| < 1 ∧ |x - c| ≤ (N : ℤ) - 1 := by
  rw [abs_lt] at hu hu'
  rw [abs_le] at huu'
  obtain ⟨v, hvu, hvu', hv1, hv2, hvlt⟩ : ∃ v : ℝ, u ≤ v ∧ u' ≤ v ∧ v - u ≤ 1 / 2 ∧
      v - u' ≤ 1 / 2 ∧ v < c + N := by
    rcases le_total u u' with h | h
    · exact ⟨u', h, le_rfl, by linarith, by linarith, by linarith⟩
    · exact ⟨u, le_rfl, h, by linarith, by linarith, by linarith⟩
  have hfl := Int.floor_le v
  have hfl' := Int.lt_floor_add_one v
  by_cases h : c - N + 1 ≤ ⌊v⌋
  · have h2 : ⌊v⌋ < c + N := Int.floor_lt.2 (by push_cast; linarith)
    refine ⟨⌊v⌋, ?_, ?_, ?_⟩
    · rw [abs_lt]
      constructor <;> linarith
    · rw [abs_lt]
      constructor <;> linarith
    · rw [abs_le]
      constructor <;> omega
  · have h2 : v < ((c - N + 1 : ℤ) : ℝ) := Int.floor_lt.1 (by omega)
    have h3 : ((c - N : ℤ) : ℝ) < u := by push_cast; linarith
    have h4 : ((c - N : ℤ) : ℝ) < u' := by push_cast; linarith
    push_cast at h2 h3 h4
    refine ⟨c - N + 1, ?_, ?_, ?_⟩
    · rw [abs_lt]
      push_cast
      constructor <;> linarith
    · rw [abs_lt]
      push_cast
      constructor <;> linarith
    · rw [abs_le]
      constructor <;> omega

/-- **A common admissible integer at mesh `s`** (MA7 D-DISC, one coordinate). -/
lemma exists_int_abs_sub_mul_lt {s : ℝ} (hs : 0 < s) (c : ℤ) {N : ℕ} (hN : 1 ≤ N) {z z' : ℝ}
    (hz : |z - s * c| < s * N) (hz' : |z' - s * c| < s * N) (hzz' : |z - z'| ≤ s / 2) :
    ∃ x : ℤ, |z - s * x| < s ∧ |z' - s * x| < s ∧ |x - c| ≤ (N : ℤ) - 1 := by
  have key : ∀ w : ℝ, ∀ y : ℝ, w - s * y = s * (w / s - y) := fun w y => by
    field_simp
  have hu : |z / s - c| < N := by
    rw [show z / s - c = (z - s * c) / s by field_simp, abs_div, abs_of_pos hs, div_lt_iff₀ hs]
    linarith
  have hu' : |z' / s - c| < N := by
    rw [show z' / s - c = (z' - s * c) / s by field_simp, abs_div, abs_of_pos hs, div_lt_iff₀ hs]
    linarith
  have huu' : |z / s - z' / s| ≤ 1 / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hs, div_le_iff₀ hs]
    linarith
  obtain ⟨x, h1, h2, h3⟩ := exists_int_abs_sub_lt_one c hN hu hu' huu'
  refine ⟨x, ?_, ?_, h3⟩
  · rw [key, abs_mul, abs_of_pos hs]
    calc s * |z / s - x| < s * 1 := mul_lt_mul_of_pos_left h1 hs
      _ = s := mul_one s
  · rw [key, abs_mul, abs_of_pos hs]
    calc s * |z' / s - x| < s * 1 := mul_lt_mul_of_pos_left h2 hs
      _ = s := mul_one s

/-! ### Boxes of sites -/

/-- If `|x - c|_∞ ≤ N - 1`, the open `s`-box of `x` lies in the open box of `c` of radius `s N`. -/
lemma obox_latPt_subset {s : ℝ} (hs : 0 < s) {x c : Zd d} {N : ℕ}
    (h : WithinInf ((N : ℤ) - 1) x c) : obox (latPt s x) s ⊆ obox (latPt s c) (s * N) := by
  intro z hz i
  have h1 : |z i - s * x i| < s := hz i
  have h2 : |((x i - c i : ℤ) : ℝ)| ≤ (N : ℝ) - 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast h i
  push_cast at h2
  have h3 : |s * (x i : ℝ) - s * c i| ≤ s * ((N : ℝ) - 1) := by
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left h2 hs.le
  show |z i - s * c i| < s * N
  calc |z i - s * c i| ≤ |z i - s * x i| + |s * x i - s * c i| := abs_sub_le _ _ _
    _ < s + s * ((N : ℝ) - 1) := by linarith
    _ = s * N := by ring

/-- The open `s`-box of `x` lies in the open box of `c` of radius `s N` iff `|x - c|_∞ ≤ N - 1`
(the lattice box `Λ = {x : obox (s x) s ⊆ obox (s c) (s N)}` of MA7 D-4.9 is
`latBox (c - (N - 1)) (c + (N - 1))`, see `withinInf_iff_mem_latBox`). -/
lemma obox_latPt_subset_iff {s : ℝ} (hs : 0 < s) {x c : Zd d} {N : ℕ} :
    obox (latPt s x) s ⊆ obox (latPt s c) (s * N) ↔ WithinInf ((N : ℤ) - 1) x c := by
  refine ⟨fun h i => ?_, obox_latPt_subset hs⟩
  have h1 : |s * (x i : ℝ) - s * c i| < s * N := h (mem_obox_self _ hs) i
  rw [← mul_sub, abs_mul, abs_of_pos hs] at h1
  have h2 : |((x i - c i : ℤ) : ℝ)| < N := by
    push_cast
    exact lt_of_mul_lt_mul_left h1 hs.le
  rw [← Int.cast_abs] at h2
  have h3 : |x i - c i| < (N : ℤ) := by exact_mod_cast h2
  omega

/-- Two sites whose open `s`-boxes contain a common point are at `ℓ^∞`-distance `≤ 1`. -/
lemma withinInf_one_of_abs_sub_lt {s : ℝ} (hs : 0 < s) {x x' : Zd d} {z : Rd d}
    (hx : ∀ i, |z i - s * x i| < s) (hx' : ∀ i, |z i - s * x' i| < s) : WithinInf 1 x x' := by
  intro i
  have h1 := hx i
  have h2 := hx' i
  rw [abs_lt] at h1 h2
  have h3 : s * ((x i : ℝ) - x' i) < s * 2 := by linarith
  have h4 : s * (-2) < s * ((x i : ℝ) - x' i) := by linarith
  have h5 : ((x i - x' i : ℤ) : ℝ) < 2 := by
    push_cast
    exact lt_of_mul_lt_mul_left h3 hs.le
  have h6 : (-2 : ℝ) < ((x i - x' i : ℤ) : ℝ) := by
    push_cast
    exact lt_of_mul_lt_mul_left h4 hs.le
  have h5' : x i - x' i < 2 := by exact_mod_cast h5
  have h6' : -2 < x i - x' i := by exact_mod_cast h6
  rw [abs_le]
  constructor <;> omega

/-! ### The discretization -/

/-- **MA7 D-DISC, working form** (open boxes, any parameter interval, loop-erased). Let `s > 0`,
`c ∈ ℤ^d`, `N ≥ 1`, `t₀ ≤ t₁`, and let `P` be continuous on `[t₀, t₁]` with values in the open box
`obox (s c) (s N)`. Then there is a duplicate-free L-path `l` of sites `x` with `|x - c|_∞ ≤ N - 1`
(hence `obox (s x) s ⊆ obox (s c) (s N)`) whose open `s`-boxes meet `P`, the first one containing
`P t₀` and the last one `P t₁`. -/
theorem exists_discretization {s : ℝ} (hs : 0 < s) (c : Zd d) {N : ℕ} (hN : 1 ≤ N)
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {P : ℝ → Rd d} (hPc : ContinuousOn P (Icc t₀ t₁))
    (hPΩ : MapsTo P (Icc t₀ t₁) (obox (latPt s c) (s * N))) :
    ∃ (l : List (Zd d)) (x₀ x₁ : Zd d), l.Nodup ∧ l.IsChain LAdj ∧ l.head? = some x₀ ∧
      l.getLast? = some x₁ ∧ P t₀ ∈ obox (latPt s x₀) s ∧ P t₁ ∈ obox (latPt s x₁) s ∧
      ∀ x ∈ l, WithinInf ((N : ℤ) - 1) x c ∧ obox (latPt s x) s ⊆ obox (latPt s c) (s * N) ∧
        ∃ t ∈ Icc t₀ t₁, P t ∈ obox (latPt s x) s := by
  -- uniform continuity of `P` on `[t₀, t₁]`
  obtain ⟨δ, hδ, hPδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hPc) (s / 2) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt ((t₁ - t₀) / δ)
  set M : ℕ := n + 1 with hM
  have hMpos : (0 : ℝ) < M := by positivity
  have hstep : (t₁ - t₀) / M < δ := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hδ] at hn
    have : (n : ℝ) < M := by rw [hM]; push_cast; linarith
    nlinarith
  -- the times `τ j = t₀ + j (t₁ - t₀) / M`
  set τ : ℕ → ℝ := fun j => t₀ + j * (t₁ - t₀) / M with hτ
  have hτmem : ∀ j ≤ M, τ j ∈ Icc t₀ t₁ := by
    intro j hj
    have hj' : (j : ℝ) ≤ M := by exact_mod_cast hj
    have h0 : 0 ≤ (j : ℝ) * (t₁ - t₀) / M :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg j) (by linarith)) hMpos.le
    have h1 : (j : ℝ) * (t₁ - t₀) / M ≤ t₁ - t₀ := by
      rw [div_le_iff₀ hMpos]
      nlinarith
    exact ⟨by simp only [hτ]; linarith, by simp only [hτ]; linarith⟩
  have hτ0 : τ 0 = t₀ := by simp [hτ]
  have hτM : τ M = t₁ := by
    simp only [hτ]
    field_simp
    ring
  have hclose : ∀ j < M, ∀ i, |P (τ j) i - P (τ (j + 1)) i| ≤ s / 2 := by
    intro j hj i
    have hd' : dist (τ j) (τ (j + 1)) < δ := by
      rw [Real.dist_eq]
      have e : τ j - τ (j + 1) = -((t₁ - t₀) / M) := by
        simp only [hτ]
        push_cast
        ring
      rw [e, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hMpos.le)]
      exact hstep
    have h1 := hPδ _ (hτmem j hj.le) _ (hτmem (j + 1) hj) hd'
    rw [dist_eq_norm] at h1
    have h2 := abs_apply_le_norm (P (τ j) - P (τ (j + 1))) i
    rw [PiLp.sub_apply] at h2
    linarith
  -- the admissible sites of a point
  set T : Rd d → Set (Zd d) := fun z =>
    {x | (∀ i, |z i - s * x i| < s) ∧ WithinInf ((N : ℤ) - 1) x c} with hT
  set G : Set (Zd d) := {x | WithinInf ((N : ℤ) - 1) x c ∧
    obox (latPt s x) s ⊆ obox (latPt s c) (s * N) ∧ ∃ t ∈ Icc t₀ t₁, P t ∈ obox (latPt s x) s}
    with hG
  have hTG : ∀ j ≤ M, T (P (τ j)) ⊆ G := by
    intro j hj x hx
    exact ⟨hx.2, obox_latPt_subset hs hx.2, τ j, hτmem j hj, hx.1⟩
  -- common sites of consecutive points
  have hex : ∀ j : ℕ, ∃ y : Zd d, j < M → y ∈ T (P (τ j)) ∧ y ∈ T (P (τ (j + 1))) := by
    intro j
    by_cases hj : j < M
    · have hz := hPΩ (hτmem j hj.le)
      have hz' := hPΩ (hτmem (j + 1) hj)
      have hco : ∀ i, ∃ xi : ℤ, (|P (τ j) i - s * xi| < s ∧ |P (τ (j + 1)) i - s * xi| < s) ∧
          |xi - c i| ≤ (N : ℤ) - 1 := fun i => by
        obtain ⟨x, h1, h2, h3⟩ := exists_int_abs_sub_mul_lt hs (c i) hN (hz i) (hz' i)
          (hclose j hj i)
        exact ⟨x, ⟨h1, h2⟩, h3⟩
      choose y hy using hco
      exact ⟨y, fun _ => ⟨⟨fun i => (hy i).1.1, fun i => (hy i).2⟩,
        ⟨fun i => (hy i).1.2, fun i => (hy i).2⟩⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose y hy using hex
  -- the chain `y 0 → y 1 → ⋯ → y n` inside `G`
  have hchain : ∀ j < M, ReflTransGen (StepIn G LAdj) (y 0) (y j) := by
    intro j hj
    induction j with
    | zero => exact ReflTransGen.refl
    | succ j ih =>
      have h1 := (hy j (by omega)).2
      have h2 := (hy (j + 1) hj).1
      have hW : WithinInf 1 (y j) (y (j + 1)) := withinInf_one_of_abs_sub_lt hs h1.1 h2.1
      have hcube : cube (y j) (y (j + 1)) ⊆ G := by
        intro w hw
        refine hTG (j + 1) hj.le ⟨fun i => ?_, fun i => ?_⟩
        · rcases hw i with h | h <;> rw [h]
          · exact h1.1 i
          · exact h2.1 i
        · rcases hw i with h | h <;> rw [h]
          · exact h1.2 i
          · exact h2.2 i
      exact (ih (by omega)).trans (reflTransGen_stepIn_mono hcube (reflTransGen_cube hW))
  have hy0 := (hy 0 (by omega)).1
  have hyn := (hy n (by omega)).2
  rw [hτ0] at hy0
  rw [show n + 1 = M from rfl, hτM] at hyn
  have hy0G : y 0 ∈ G := hTG 0 (Nat.zero_le _) (by rw [hτ0]; exact hy0)
  obtain ⟨l, hnd, hch, hh, hl, hS⟩ :=
    exists_nodup_isChain_of_reflTransGen hy0G (hchain n (by omega))
  exact ⟨l, y 0, y n, hnd, hch, hh, hl, hy0.1, hyn.1, hS⟩

/-- **MA7 D-DISC, open variant** (every `d`). -/
theorem discretizeOpen (d : ℕ) : DiscretizeLemmaOpen d := by
  intro s hs c N hN P hPc hPΩ
  obtain ⟨l, x₀, x₁, -, hch, hh, hl, h0, h1, hS⟩ :=
    exists_discretization hs c hN zero_le_one hPc hPΩ
  exact ⟨l, x₀, x₁, hch, hh, hl, h0, h1, fun x hx => (hS x hx).2⟩

/-- **MA7 D-DISC, closed variant: `DiscretizeLemma`** (MA7 Details (c) §B; every `d`). -/
theorem discretize (d : ℕ) : DiscretizeLemma d := by
  intro s hs c N hN P hPc hPΩ
  obtain ⟨l, x₀, x₁, hch, hh, hl, h0, h1, hS⟩ := discretizeOpen d hs c N hN hPc hPΩ
  refine ⟨l, x₀, x₁, hch, hh, hl, obox_subset_cbox _ _ h0, obox_subset_cbox _ _ h1,
    fun x hx => ?_⟩
  obtain ⟨h2, t, ht, hPt⟩ := hS x hx
  exact ⟨h2, t, ht, obox_subset_cbox _ _ hPt⟩

end DGZ

end HigherDimLQGMetric
