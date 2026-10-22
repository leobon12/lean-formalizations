import HigherDimLQGMetric.DGZ.Sec41Defs
import HigherDimLQGMetric.DGZ.FreeSites
import HigherDimLQGMetric.DGZ.Shell
import HigherDimLQGMetric.DGZ.Functionals

/-!
# DGZ Props 4.3^s, 4.5^s: the level-`m` link (packet L3c2; MA7 D-4.3s, Step 2)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), proofs of Props 4.3 and 4.5 (TeX
l. 1487–1600); planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-4.3s
(self-internal chaining), Step 2.

The deterministic core of the chaining: two **free** sites `u, v` of the `m`-open configuration
`O = mOpen ξ Q η φ m a` (DGZ (4.4)), under `SmallClusters O D` (the event `ℰ_{m,n}`), are joined by
an `m`-open L-path within `ℓ^∞`-distance `D + 1` of the coordinate path from `u` to `v` (free
surgery, MA7 D-FS(i)); loop erasure makes it simple, so it has at most `(2(R + D + 1) + 1)^d` sites
when `|u - v|_∞ ≤ R`. If the box hull of `u, v`, enlarged by `D + 3` lattice steps, stays inside
`B_ρ(0)` (`ρ ≤ 2`), every site `z` of the path lies in `𝓛_m` and `B_{2^{1-m}}(2^{-m} z) ⊆ B_ρ(0)`,
so (4.4), monotonicity of `D_n(·, ·; ·)` in the domain and the triangle inequality give
`D_n(2^{-m} u, 2^{-m} v; B_ρ(0)) ≤ (2(R + D + 1) + 1)^d 2^{-(1-ξQ+η)m} a`
(`lfppDistOn_le_of_freeSite`).

Helpers: the chain bound along an L-path (`lfppDistOn_le_mul_of_isChain`), nonnegativity of the
level `a` at an open site of `𝓛_m` (`nonneg_of_mem_mOpen`), and lattice/real conversions
(`latPt_two_smul`, `abs_latPt_sub_le_of_withinInf`, `withinInf_of_abs_latPt_sub_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Relation

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox latPt_apply convex_obox mem_obox_self)

variable {d : ℕ}

/-! ### Lattice points -/

/-- The coarse site `y` (mesh `2^{-k}`) is the fine site `2 • y` (mesh `2^{-(k+1)}`). -/
theorem latPt_two_smul (k : ℕ) (y : Zd d) :
    latPt ((2 : ℝ)⁻¹ ^ (k + 1)) (2 • y) = latPt ((2 : ℝ)⁻¹ ^ k) y := by
  ext i
  rw [latPt_apply, latPt_apply, two_smul_apply]
  push_cast
  rw [pow_succ]
  field_simp

/-- `|x - y|_∞ ≤ R` on sites gives `|s x - s y|_∞ ≤ s R` on lattice points. -/
theorem abs_latPt_sub_le_of_withinInf {s : ℝ} (hs : 0 ≤ s) {R : ℤ} {x y : Zd d}
    (h : WithinInf R x y) (i : Fin d) : |latPt s x i - latPt s y i| ≤ s * R := by
  rw [latPt_apply, latPt_apply, ← mul_sub, abs_mul, abs_of_nonneg hs]
  have h' : |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| ≤ (R : ℝ) := by
    have := (Int.cast_le (R := ℝ)).2 (h i)
    push_cast at this
    exact this
  exact mul_le_mul_of_nonneg_left h' hs

/-- Conversely, `|s x - s y|_∞ ≤ s R` (`s > 0`) gives `|x - y|_∞ ≤ R`. -/
theorem withinInf_of_abs_latPt_sub_le {s : ℝ} (hs : 0 < s) {R : ℕ} {x y : Zd d}
    (h : ∀ i, |latPt s x i - latPt s y i| ≤ s * R) : WithinInf (R : ℤ) x y := fun i => by
  have h' := h i
  rw [latPt_apply, latPt_apply, ← mul_sub, abs_mul, abs_of_pos hs] at h'
  have h'' : |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| ≤ (R : ℝ) := le_of_mul_le_mul_left h' hs
  have : ((|x i - y i| : ℤ) : ℝ) ≤ ((R : ℤ) : ℝ) := by push_cast; exact h''
  exact_mod_cast this

/-! ### Chains of open sites -/

/-- **Chain bound along an L-path**: if any two L-adjacent sites of `S` are at internal distance
`≤ b` (through the points `f x ∈ V`, `V` convex), then the endpoints of an L-path in `S` with `N`
sites are at distance `≤ (N - 1) b`. -/
theorem lfppDistOn_le_mul_of_isChain {ζ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {V : Set (Rd d)} (hV : Convex ℝ V) {f : Zd d → Rd d} {S : Set (Zd d)}
    (hfV : ∀ x ∈ S, f x ∈ V) {b : ℝ}
    (hstep : ∀ x ∈ S, ∀ y ∈ S, LAdj x y → lfppDistOn ζ φ V (f x) (f y) ≤ b) :
    ∀ (l : List (Zd d)) (u v : Zd d), l.IsChain LAdj → l.head? = some u →
      l.getLast? = some v → (∀ x ∈ l, x ∈ S) →
      lfppDistOn ζ φ V (f u) (f v) ≤ ((l.length - 1 : ℕ) : ℝ) * b := by
  intro l
  induction l with
  | nil => intro u v _ h; simp at h
  | cons a t ih =>
    intro u v hch hh hl hS
    rw [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases t with
    | nil =>
      rw [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      simp [lfppDistOn_self]
    | cons b' t' =>
      rw [List.isChain_cons_cons] at hch
      rw [List.getLast?_cons_cons] at hl
      have hS' : ∀ x ∈ b' :: t', x ∈ S := fun x hx => hS x (List.mem_cons_of_mem _ hx)
      have ih' := ih b' v hch.2 rfl hl hS'
      have ha : a ∈ S := hS a List.mem_cons_self
      have hb : b' ∈ S := hS' b' List.mem_cons_self
      have hv : v ∈ S := hS' v (List.mem_of_mem_getLast? hl)
      have h1 := lfppDistOn_triangle (ζ := ζ) hφ (PcwJoined.of_convex hV (hfV a ha) (hfV b' hb))
        (PcwJoined.of_convex hV (hfV b' hb) (hfV v hv))
      have h2 := hstep a ha b' hb hch.1
      have e1 : ((b' :: t').length - 1 : ℕ) = t'.length := by simp
      have e2 : ((a :: b' :: t').length - 1 : ℕ) = t'.length + 1 := by simp
      rw [e1] at ih'
      rw [e2]
      push_cast
      linarith

/-- The level `a` of the `m`-open configuration is nonnegative as soon as some site of `𝓛_m` is
open (its (4.4) bound bounds a nonnegative distance). -/
theorem nonneg_of_mem_mOpen (hd : 1 ≤ d) {ξ Q η a : ℝ} {φ : Rd d → ℝ} {m : ℕ} {x : Zd d}
    (hx : x ∈ mOpen ξ Q η φ m a) (hreg : x ∈ latRegion m) : 0 ≤ a := by
  have h := lfppDistOn_le_of_mem_mOpen hx hreg (lAdj_add_single x ⟨0, hd⟩)
  have h0 := lfppDistOn_nonneg ξ φ (obox (latPt ((2 : ℝ)⁻¹ ^ m) x) (2 * (2 : ℝ)⁻¹ ^ m))
    (latPt ((2 : ℝ)⁻¹ ^ m) x) (latPt ((2 : ℝ)⁻¹ ^ m) (x + Pi.single ⟨0, hd⟩ 1))
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1 - ξ * Q + η) * m) := Real.rpow_pos_of_pos two_pos _
  exact (mul_nonneg_iff_of_pos_left hpos).1 (h0.trans h)

/-- A site within `D` of a point of the coordinate hull of `a, b` is within `max |a| |b| + D` of
`0` (one coordinate). -/
private lemma int_abs_le_max_add {a b c D y : ℤ} (h1 : min a b ≤ c) (h2 : c ≤ max a b)
    (h3 : |y - c| ≤ D) : |y| ≤ max |a| |b| + D := by
  rw [abs_le] at h3 ⊢
  constructor
  · have : -max |a| |b| ≤ min a b := by
      rw [neg_le]
      rcases le_total a b with h | h
      · rw [min_eq_left h]; exact (neg_le_abs a).trans (le_max_left _ _)
      · rw [min_eq_right h]; exact (neg_le_abs b).trans (le_max_right _ _)
    omega
  · have : max a b ≤ max |a| |b| := max_le_max (le_abs_self a) (le_abs_self b)
    omega

/-- A site within `D` of a point of the coordinate hull of `a, b` is within `|a - b| + D` of `a`
(one coordinate). -/
private lemma int_abs_sub_le_add {a b c D y : ℤ} (h1 : min a b ≤ c) (h2 : c ≤ max a b)
    (h3 : |y - c| ≤ D) : |y - a| ≤ |a - b| + D := by
  rw [abs_le] at h3 ⊢
  rcases le_total a b with h | h
  · rw [min_eq_left h] at h1; rw [max_eq_right h] at h2
    rw [abs_of_nonpos (by omega)]; constructor <;> omega
  · rw [min_eq_right h] at h1; rw [max_eq_left h] at h2
    rw [abs_of_nonneg (by omega)]; constructor <;> omega

/-- **The level-`m` link** (MA7 D-4.3s, Step 2): let `u, v` be free sites of the `m`-open
configuration `O = mOpen ξ Q η φ m a` with `SmallClusters O D` and `|u - v|_∞ ≤ R`, such that
`|2^{-m} u_i| + (D + 3) 2^{-m} ≤ ρ` and `|2^{-m} v_i| + (D + 3) 2^{-m} ≤ ρ` for all `i`
(`ρ ≤ 2`). Then `D(2^{-m} u, 2^{-m} v; B_ρ(0)) ≤ (2(R + D + 1) + 1)^d 2^{-(1-ξQ+η)m} a`. -/
theorem lfppDistOn_le_of_freeSite (hd : 1 ≤ d) {φ : Rd d → ℝ} (hφ : Continuous φ)
    {ξ Q η a ρ : ℝ} {m D R : ℕ} (hρ : ρ ≤ 2)
    (hsmall : SmallClusters (mOpen ξ Q η φ m a) D) {u v : Zd d}
    (hu : FreeSite (mOpen ξ Q η φ m a) u) (hv : FreeSite (mOpen ξ Q η φ m a) v)
    (huv : WithinInf (R : ℤ) u v)
    (hmu : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ m) u i| + ((D : ℝ) + 3) * (2 : ℝ)⁻¹ ^ m ≤ ρ)
    (hmv : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ m) v i| + ((D : ℝ) + 3) * (2 : ℝ)⁻¹ ^ m ≤ ρ) :
    lfppDistOn ξ φ (obox (0 : Rd d) ρ) (latPt ((2 : ℝ)⁻¹ ^ m) u) (latPt ((2 : ℝ)⁻¹ ^ m) v) ≤
      ((2 * (R + D + 1) + 1 : ℕ) : ℝ) ^ d * ((2 : ℝ) ^ (-(1 - ξ * Q + η) * m) * a) := by
  classical
  set s : ℝ := (2 : ℝ)⁻¹ ^ m with hs_def
  have hs : 0 < s := by positivity
  set O := mOpen ξ Q η φ m a with hO
  set hull : Set (Zd d) := {z | ∀ k, min (u k) (v k) ≤ z k ∧ z k ≤ max (u k) (v k)} with hhull
  have huh : u ∈ hull := fun k => ⟨min_le_left _ _, le_max_left _ _⟩
  obtain ⟨γ, hγ, hγh, hγl, hγS⟩ := exists_lAdj_chain_of_reflTransGen huh
    (reflTransGen_of_forall_between (S := hull) fun z hz => hz)
  have hsurg := freeSurgery d O D hsmall γ u v hγ hγh hγl hu hv
  set T : Set (Zd d) := {y | y ∈ O ∧ ∃ x ∈ γ, WithinInf ((D : ℤ) + 1) y x} with hT
  have huT : u ∈ T :=
    ⟨hu.1, u, List.mem_of_mem_head? hγh, withinInf_refl (by positivity) u⟩
  obtain ⟨l, hnd, hch, hlh, hll, hlT⟩ :=
    HigherDimLFPP.DGZ.exists_nodup_isChain_of_reflTransGen huT hsurg
  -- integer bounds for the sites of `T`
  have hTint : ∀ y ∈ T, ∀ k, |y k| ≤ max |u k| |v k| + ((D : ℤ) + 1) ∧
      |y k - u k| ≤ (R : ℤ) + ((D : ℤ) + 1) := by
    rintro y ⟨-, x, hxγ, hyx⟩ k
    have hx := hγS x hxγ k
    refine ⟨int_abs_le_max_add hx.1 hx.2 (hyx k), ?_⟩
    have := int_abs_sub_le_add hx.1 hx.2 (hyx k)
    have := huv k
    linarith
  -- real margins for the sites of `T`
  have hTreal : ∀ y ∈ T, ∀ k, |latPt s y k| + 2 * s ≤ ρ := by
    intro y hy k
    have h1 := (hTint y hy k).1
    have h1' : |((y k : ℤ) : ℝ)| ≤ max |((u k : ℤ) : ℝ)| |((v k : ℤ) : ℝ)| + ((D : ℝ) + 1) := by
      have := (Int.cast_le (R := ℝ)).2 h1
      push_cast at this
      exact this
    have hu' := hmu k
    have hv' := hmv k
    rw [latPt_apply, abs_mul, abs_of_pos hs] at hu' hv' ⊢
    have h2 := mul_le_mul_of_nonneg_left h1' hs.le
    rcases le_total |((u k : ℤ) : ℝ)| |((v k : ℤ) : ℝ)| with h | h
    · rw [max_eq_right h] at h2
      linarith
    · rw [max_eq_left h] at h2
      linarith
  have hTV : ∀ y ∈ T, latPt s y ∈ obox (0 : Rd d) ρ := fun y hy i => by
    rw [PiLp.zero_apply, sub_zero]
    have := hTreal y hy i
    linarith
  have hTbox : ∀ y ∈ T, obox (latPt s y) (2 * s) ⊆ obox (0 : Rd d) ρ := fun y hy w hw i => by
    rw [PiLp.zero_apply, sub_zero]
    have h1 := hw i
    have h2 := hTreal y hy i
    have h3 := abs_sub_abs_le_abs_sub (w i) (latPt s y i)
    linarith
  have hTreg : ∀ y ∈ T, y ∈ latRegion m := fun y hy =>
    (mem_latRegion_iff_mem_obox m y).2 (obox_mono hρ (hTV y hy))
  have ha : 0 ≤ a := nonneg_of_mem_mOpen hd hu.1 (hTreg u huT)
  have hb : 0 ≤ (2 : ℝ) ^ (-(1 - ξ * Q + η) * m) * a :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) ha
  have hstep : ∀ x ∈ T, ∀ y ∈ T, LAdj x y →
      lfppDistOn ξ φ (obox (0 : Rd d) ρ) (latPt s x) (latPt s y) ≤
        (2 : ℝ) ^ (-(1 - ξ * Q + η) * m) * a := by
    intro x hx y _ hxy
    have hyb : latPt s y ∈ obox (latPt s x) (2 * s) := fun i => by
      have h1 := abs_latPt_sub_le_of_withinInf hs.le (LAdj.withinInf hxy).symm i
      push_cast at h1
      linarith
    calc lfppDistOn ξ φ (obox (0 : Rd d) ρ) (latPt s x) (latPt s y)
        ≤ lfppDistOn ξ φ (obox (latPt s x) (2 * s)) (latPt s x) (latPt s y) :=
          lfppDistOn_mono (hTbox x hx)
            (PcwJoined.of_convex (convex_obox _ _) (mem_obox_self _ (by positivity)) hyb)
      _ ≤ _ := lfppDistOn_le_of_mem_mOpen hx.1 (hTreg x hx) hxy
  have hchain := lfppDistOn_le_mul_of_isChain hφ (convex_obox (0 : Rd d) ρ) hTV hstep l u v hch
    hlh hll hlT
  -- the number of sites of the simple path
  have hlen : l.length ≤ (2 * (R + D + 1) + 1) ^ d := by
    rw [← List.toFinset_card_of_nodup hnd, ← card_boxF u (R + D + 1)]
    refine Finset.card_le_card fun y hy => ?_
    rw [List.mem_toFinset] at hy
    rw [mem_boxF]
    intro k
    have := (hTint y (hlT y hy) k).2
    push_cast
    linarith
  calc lfppDistOn ξ φ (obox (0 : Rd d) ρ) (latPt s u) (latPt s v)
      ≤ ((l.length - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (-(1 - ξ * Q + η) * m) * a) := hchain
    _ ≤ ((2 * (R + D + 1) + 1 : ℕ) : ℝ) ^ d * ((2 : ℝ) ^ (-(1 - ξ * Q + η) * m) * a) := by
      refine mul_le_mul_of_nonneg_right ?_ hb
      rw [← Nat.cast_pow]
      exact_mod_cast (Nat.sub_le _ _).trans hlen

end DGZ

end HigherDimLQGMetric
