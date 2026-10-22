import HigherDimLQGMetric.DGZ.SuperExpAcross
import HigherDimLQGMetric.DGZ.Fold
import HigherDimLQGMetric.DGZ.Shell

/-!
# DGZ Lemma 4.9, around half: the deterministic certificate (packet L3c3; MA7 D-4.9)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.9 (TeX l. 1814–1905, pp. 35–37);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, §5 row L3c3, gap G3 and Details (a)
D-4.9, steps (1)–(6) "On `E`" (the repair of the duality inside a box, G3(a), by box surgery via
folding, D-BOX, and of the clipped-diameter footnote, G3(b), by self-internal diameters).

Setting: mesh `s > 0`, `ρ ≥ 8 s`, `16 ρ ≤ r₂`, `16 ρ ≤ r₁ - r₂`, `D = ⌊ρ/s⌋`; the cube
`B = obox (s c) (s N)` (`c ∈ ℤ^d`, `N ∈ ℕ`) contains `0` with `|c|_∞ ≤ N - 1` (so `B_s(0) ⊆ B`) and,
in every coordinate, extends at least `r₁` on one side of `0`; `Λ = [c - (N-1), c + (N-1)]` is the
lattice box of sites `x` with `B_s(s x) ⊆ B`.

Main result `aroundGood_of_smallClusters`: if the closed clusters of a site configuration `O` have
diameter `≤ D` (`SmallClusters O D`) and every open site `x ∈ Λ` of the shell region
`Σ = {r₂ + ρ/2 ≤ s|x|_∞ ≤ r₁ - ρ/2}` has `selfDiam(φ)(B_s(s x)) ≤ t`, then
`AroundGood ξ φ 0 r₁ r₂ B (2 (2K+1)^d t)` with `K = ⌈r₁/s⌉`.

Proof (MA7 D-4.9 (1)–(6)). (1) A crossing `γ_i` contains a sub-crossing of
`B̄_{r₁-4ρ} \ B_{r₂+4ρ}`; (2) its discretization (D-DISC, open boxes, in `B`) is an L-path in `Λ` of
diameter `> 2D + 1`; (3) by `FoldSmall` the folded configuration `foldBox⁻¹ O` has closed clusters
of diameter `≤ 2D + 1`, so the free-site lemma gives a free site `u_i` of the folded
configuration on this path, with `γ_i(τ_i) ∈ B_s(s u_i)`; (4) D-SHELL joins `u₁, u₂` inside the
lattice shell `{⌈(r₂+3ρ)/s⌉ ≤ |x|_∞ ≤ ⌊(r₁-3ρ)/s⌋} ∩ Λ`; (5) `BoxSurgery` reroutes this chain
through open sites of `Λ` within `2D + 2` of it, hence in `Σ`; (6) consecutive boxes `B_s(s x)`
overlap, so chaining through midpoints gives `D(γ₁(τ₁), γ₂(τ₂); shell ∩ B) ≤ 2 L t` (`L` the
number of sites of the loop-erased path, `≤ (2K+1)^d`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Relation

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox obox_subset_cbox convex_obox mem_obox_self)

variable {d : ℕ}

/-! ### Chains of overlapping boxes -/

section Chains

variable {ξ : ℝ} {φ : Rd d → ℝ} {V : Set (Rd d)} {s t : ℝ}

/-- **One step**: for L-adjacent sites `x, y` whose open `s`-boxes lie in `V` and have
self-internal diameter `≤ t`, `D_V(s x, s y) ≤ 2t` (through the midpoint, which lies in both
boxes), and `s x, s y` are joined in `V`. -/
lemma step_le_of_lAdj (hφ : Continuous φ) (hs : 0 < s) {x y : Zd d} (hxy : LAdj x y)
    (hxV : obox (latPt s x) s ⊆ V) (hyV : obox (latPt s y) s ⊆ V)
    (hxt : selfDiam ξ φ (latPt s x) s ≤ t) (hyt : selfDiam ξ φ (latPt s y) s ≤ t) :
    PcwJoined V (latPt s x) (latPt s y) ∧ lfppDistOn ξ φ V (latPt s x) (latPt s y) ≤ 2 * t := by
  have hW := LAdj.withinInf hxy
  have hmid : ∀ i, ((2 : ℝ)⁻¹ • (latPt s x + latPt s y)) i = 2⁻¹ * (s * x i) + 2⁻¹ * (s * y i) :=
    fun i => by simp [latPt_apply]
  have hdiff : ∀ i, |s * (x i : ℝ) - s * (y i : ℝ)| ≤ s := fun i => by
    have h1 : |((x i - y i : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast hW i
    push_cast at h1
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    nlinarith
  have hpx : (2 : ℝ)⁻¹ • (latPt s x + latPt s y) ∈ obox (latPt s x) s := fun i => by
    rw [hmid, latPt_apply]
    have e : 2⁻¹ * (s * (x i : ℝ)) + 2⁻¹ * (s * y i) - s * x i = -(2⁻¹ * (s * x i - s * y i)) := by
      ring
    rw [e, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    linarith [hdiff i]
  have hpy : (2 : ℝ)⁻¹ • (latPt s x + latPt s y) ∈ obox (latPt s y) s := fun i => by
    rw [hmid, latPt_apply]
    have e : 2⁻¹ * (s * (x i : ℝ)) + 2⁻¹ * (s * y i) - s * y i = 2⁻¹ * (s * x i - s * y i) := by
      ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    linarith [hdiff i]
  have hx := mem_obox_self (latPt s x) hs
  have hy := mem_obox_self (latPt s y) hs
  have hj1 : PcwJoined V (latPt s x) ((2 : ℝ)⁻¹ • (latPt s x + latPt s y)) :=
    (PcwJoined.of_convex (convex_obox _ _) hx hpx).mono hxV
  have hj2 : PcwJoined V ((2 : ℝ)⁻¹ • (latPt s x + latPt s y)) (latPt s y) :=
    (PcwJoined.of_convex (convex_obox _ _) hpy hy).mono hyV
  refine ⟨hj1.trans hj2, ?_⟩
  calc lfppDistOn ξ φ V (latPt s x) (latPt s y)
      ≤ lfppDistOn ξ φ V (latPt s x) ((2 : ℝ)⁻¹ • (latPt s x + latPt s y)) +
          lfppDistOn ξ φ V ((2 : ℝ)⁻¹ • (latPt s x + latPt s y)) (latPt s y) :=
        lfppDistOn_triangle hφ hj1 hj2
    _ ≤ selfDiam ξ φ (latPt s x) s + selfDiam ξ φ (latPt s y) s :=
        add_le_add (lfppDistOn_le_selfDiam_of_subset hφ hxV hx hpx)
          (lfppDistOn_le_selfDiam_of_subset hφ hyV hpy hy)
    _ ≤ 2 * t := by linarith

/-- **Chains of boxes**: along an L-path of sites whose open `s`-boxes lie in `V` and have
self-internal diameter `≤ t`, the end points are joined in `V` and
`D_V(s u, s v) ≤ 2 (length - 1) t`. -/
theorem chain_le_of_isChain (hφ : Continuous φ) (hs : 0 < s) {S : Set (Zd d)}
    (hSV : ∀ x ∈ S, obox (latPt s x) s ⊆ V) (hSt : ∀ x ∈ S, selfDiam ξ φ (latPt s x) s ≤ t) :
    ∀ (l : List (Zd d)) (u v : Zd d), l.IsChain LAdj → l.head? = some u →
      l.getLast? = some v → (∀ x ∈ l, x ∈ S) →
      PcwJoined V (latPt s u) (latPt s v) ∧
        lfppDistOn ξ φ V (latPt s u) (latPt s v) ≤ 2 * ((l.length - 1 : ℕ) : ℝ) * t := by
  intro l
  induction l with
  | nil => intro u v _ h; simp at h
  | cons a tl ih =>
    intro u v hch hh hl hS
    rw [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases tl with
    | nil =>
      rw [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      have ha : a ∈ S := hS a List.mem_cons_self
      refine ⟨PcwJoined.refl (hSV a ha (mem_obox_self _ hs)), ?_⟩
      simp [lfppDistOn_self]
    | cons b' t' =>
      rw [List.isChain_cons_cons] at hch
      rw [List.getLast?_cons_cons] at hl
      have hS' : ∀ x ∈ b' :: t', x ∈ S := fun x hx => hS x (List.mem_cons_of_mem _ hx)
      obtain ⟨hj', ih'⟩ := ih b' v hch.2 rfl hl hS'
      have ha : a ∈ S := hS a List.mem_cons_self
      have hb : b' ∈ S := hS' b' List.mem_cons_self
      obtain ⟨hj1, h1⟩ := step_le_of_lAdj hφ hs hch.1 (hSV a ha) (hSV b' hb) (hSt a ha)
        (hSt b' hb)
      refine ⟨hj1.trans hj', ?_⟩
      have h2 := lfppDistOn_triangle (ζ := ξ) hφ hj1 hj'
      have e1 : ((b' :: t').length - 1 : ℕ) = t'.length := by simp
      have e2 : ((a :: b' :: t').length - 1 : ℕ) = t'.length + 1 := by simp
      rw [e1] at ih'
      rw [e2]
      push_cast
      linarith

end Chains

/-! ### A free site on each crossing -/

section Crossing

variable {s ρ r₁ r₂ : ℝ} {c : Zd d} {N : ℕ}

/-- **A free site of the folded configuration on a crossing** (MA7 D-4.9 (1)–(3)): a crossing `γ`
of the closed shell `B̄_{r₁} \ B_{r₂}` inside `B = obox (s c) (s N)` passes through the open
`s`-box of a site `u ∈ Λ` that is free for the folded configuration and lies in the real shell
`r₂ + 3ρ < s|u|_∞ < r₁ - 3ρ`. -/
theorem exists_freeSite_of_crossing (hd : 2 ≤ d) (hs : 0 < s) (hsρ : 8 * s ≤ ρ)
    (hρ₁ : 16 * ρ ≤ r₁ - r₂) (hN1 : 1 ≤ N) {a b : Zd d} {O : Set (Zd d)}
    (hfold : SmallClusters (foldBox a b ⁻¹' O) (2 * ⌊ρ / s⌋₊ + 1)) {γ : ℝ → Rd d}
    (hγ : IsShellCrossing 0 r₁ r₂ (obox (latPt s c) (s * N)) γ) :
    ∃ τ ∈ Icc (0 : ℝ) 1, ∃ u : Zd d, FreeSite (foldBox a b ⁻¹' O) u ∧
      WithinInf ((N : ℤ) - 1) u c ∧ (∃ i, r₂ + 3 * ρ < s * |(u i : ℝ)|) ∧
      (∀ i, s * |(u i : ℝ)| < r₁ - 3 * ρ) ∧ γ τ ∈ obox (latPt s u) s := by
  have hρ0 : 0 < ρ := by linarith
  have hshell : r₂ + 4 * ρ < r₁ - 4 * ρ := by linarith
  have h0 : γ 0 ∈ cbox (0 : Rd d) (r₂ + 4 * ρ) := cbox_mono (by linarith) (mem_lsph.1 hγ.start).1
  have h1 : γ 1 ∉ obox (0 : Rd d) (r₁ - 4 * ρ) := fun h =>
    (mem_lsph.1 hγ.stop).2 (obox_mono (by linarith) h)
  obtain ⟨t₀, t₁, ht0, h01, ht1, ht₀, ht₁, hin, -⟩ :=
    (isShellPair_box (0 : Rd d) hshell).exists_crossing_of_le zero_le_one hγ.pcw.continuousOn h0 h1
  obtain ⟨l, x₀, x₁, -, hl, hhead, hlast, hx₀, hx₁, hsites⟩ :=
    exists_discretization hs c hN1 h01.le (hγ.pcw.continuousOn.mono (Icc_subset_Icc ht0 ht1))
      (hγ.inB.mono_left (Icc_subset_Icc ht0 ht1))
  -- the discretized path has diameter `> 2D + 1`
  have hD : (⌊ρ / s⌋₊ : ℝ) * s ≤ ρ := by
    have := Nat.floor_le (div_nonneg hρ0.le hs.le)
    rwa [le_div_iff₀ hs] at this
  have hfar : ¬ WithinInf ((2 * ⌊ρ / s⌋₊ + 1 : ℕ) : ℤ) x₀ x₁ := by
    obtain ⟨j, hj⟩ : ∃ j, r₁ - 4 * ρ ≤ |γ t₁ j| := by
      have h := ht₁.2
      rw [mem_obox] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, by simpa using hj⟩
    have h0j : |γ t₀ j| ≤ r₂ + 4 * ρ := by
      have := ht₀.1 j
      simpa using this
    have hx₀j : |γ t₀ j - s * (x₀ j : ℝ)| < s := hx₀ j
    have hx₁j : |γ t₁ j - s * (x₁ j : ℝ)| < s := hx₁ j
    intro hW
    have hWj : |((x₁ j : ℤ) : ℝ) - (x₀ j : ℝ)| ≤ 2 * (⌊ρ / s⌋₊ : ℝ) + 1 := by
      have := hW j
      rw [abs_sub_comm] at this
      exact_mod_cast this
    have h3 : s * |((x₁ j : ℤ) : ℝ) - (x₀ j : ℝ)| ≤ s * (2 * (⌊ρ / s⌋₊ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hWj hs.le
    have h4 : |s * (x₁ j : ℝ) - s * (x₀ j : ℝ)| = s * |((x₁ j : ℤ) : ℝ) - (x₀ j : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hs]
    have h5 := abs_sub_abs_le_abs_sub (γ t₁ j) (γ t₀ j)
    have key : |γ t₁ j - γ t₀ j| ≤ |γ t₁ j - s * (x₁ j : ℝ)| +
        |s * (x₁ j : ℝ) - s * (x₀ j : ℝ)| + |γ t₀ j - s * (x₀ j : ℝ)| := by
      rw [abs_sub_comm (γ t₀ j)]
      calc |γ t₁ j - γ t₀ j| = |(γ t₁ j - s * (x₁ j : ℝ)) + (s * (x₁ j : ℝ) - s * (x₀ j : ℝ)) +
            (s * (x₀ j : ℝ) - γ t₀ j)| := by ring_nf
        _ ≤ _ := abs_add_three _ _ _
    nlinarith
  obtain ⟨u, hul, hufree⟩ := exists_freeSite_mem_of_isChain hd hfold hl
    ⟨x₀, List.mem_of_mem_head? hhead, x₁, List.mem_of_mem_getLast? hlast, hfar⟩
  obtain ⟨huΛ, -, τ, hτ, hγτ⟩ := hsites u hul
  refine ⟨τ, ⟨ht0.trans hτ.1, hτ.2.trans ht1⟩, u, hufree, huΛ, ?_, fun i => ?_, hγτ⟩
  · obtain ⟨j, hj⟩ : ∃ j, r₂ + 4 * ρ ≤ |γ τ j| := by
      have h := (hin τ hτ).2
      rw [mem_obox] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact ⟨j, by simpa using hj⟩
    refine ⟨j, ?_⟩
    have h1 : |γ τ j - s * (u j : ℝ)| < s := hγτ j
    have h2 := abs_sub_abs_le_abs_sub (γ τ j) (s * (u j : ℝ))
    rw [abs_mul, abs_of_pos hs] at h2
    linarith
  · have h1 : |γ τ i - s * (u i : ℝ)| < s := hγτ i
    have h2 : |γ τ i| ≤ r₁ - 4 * ρ := by
      have := (hin τ hτ).1 i
      simpa using this
    have h3 := abs_sub_abs_le_abs_sub (s * (u i : ℝ)) (γ τ i)
    rw [abs_sub_comm] at h1
    rw [abs_mul, abs_of_pos hs] at h3
    linarith

end Crossing

/-! ### The certificate -/

/-- **The around certificate** (MA7 D-4.9, "On `E`", steps (1)–(6)): if the closed clusters of
`O` have diameter `≤ ⌊ρ/s⌋` and every open site `x ∈ Λ` of the shell region
`r₂ + ρ/2 ≤ s|x|_∞ ≤ r₁ - ρ/2` has `selfDiam(φ)(B_s(s x)) ≤ t`, then any two crossings of the closed
shell `B̄_{r₁}(0) \ B_{r₂}(0)` inside `B = obox (s c) (s N)` are joined inside the shell `∩ B` by a
path of `φ`-length `≤ 2 (2⌈r₁/s⌉ + 1)^d t`. -/
theorem aroundGood_of_smallClusters (hd : 2 ≤ d) {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {r₁ r₂ ρ s : ℝ} (hs : 0 < s) (hsρ : 8 * s ≤ ρ) (hρ₂ : 16 * ρ ≤ r₂) (hρ₁ : 16 * ρ ≤ r₁ - r₂)
    {c : Zd d} {N : ℕ} (hc0 : WithinInf ((N : ℤ) - 1) 0 c)
    (hside : ∀ i, r₁ ≤ s * ((c i : ℝ) + N) ∨ s * ((c i : ℝ) - N) ≤ -r₁)
    {O : Set (Zd d)} (hsmall : SmallClusters O ⌊ρ / s⌋₊) {t : ℝ} (ht : 0 ≤ t)
    (hgood : ∀ x ∈ O, WithinInf ((N : ℤ) - 1) x c → (∃ i, r₂ + ρ / 2 ≤ s * |(x i : ℝ)|) →
      (∀ i, s * |(x i : ℝ)| ≤ r₁ - ρ / 2) → selfDiam ξ φ (latPt s x) s ≤ t) :
    AroundGood ξ φ 0 r₁ r₂ (obox (latPt s c) (s * N))
      (2 * ((2 * ⌈r₁ / s⌉₊ + 1) ^ d : ℕ) * t) := by
  intro γ₁ γ₂ hγ₁ hγ₂
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, ⌊ρ / s⌋₊ = D := ⟨_, rfl⟩
  rw [hDdef] at hsmall
  have hDs : (D : ℝ) * s ≤ ρ := by
    have := Nat.floor_le (div_nonneg hρ0.le hs.le)
    rwa [hDdef, le_div_iff₀ hs] at this
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  obtain ⟨a, hadef⟩ : ∃ a : Zd d, (fun i => c i - ((N : ℤ) - 1)) = a := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : Zd d, (fun i => c i + ((N : ℤ) - 1)) = b := ⟨_, rfl⟩
  have hΛ : ∀ x : Zd d, WithinInf ((N : ℤ) - 1) x c ↔ x ∈ latBox a b := fun x => by
    rw [← hadef, ← hbdef]
    exact withinInf_iff_mem_latBox
  -- the box is large: `D + 3 ≤ N`
  have hci : ∀ i, |((c i : ℤ) : ℝ)| ≤ (N : ℝ) - 1 := fun i => by
    have := hc0 i
    simp only [Pi.zero_apply, zero_sub, abs_neg] at this
    exact_mod_cast this
  have hND : (D : ℝ) + 3 ≤ N := by
    have i : Fin d := ⟨0, by omega⟩
    have key : 32 * ρ ≤ s * (2 * N - 1) := by
      rcases hside i with h | h
      · have h1 := le_abs_self ((c i : ℤ) : ℝ)
        have h2 := mul_le_mul_of_nonneg_left
          (show ((c i : ℤ) : ℝ) + N ≤ 2 * N - 1 by linarith [hci i]) hs.le
        linarith
      · have h1 := neg_abs_le ((c i : ℤ) : ℝ)
        have h2 := mul_le_mul_of_nonneg_left
          (show -(2 * N - 1 : ℝ) ≤ ((c i : ℤ) : ℝ) - N by linarith [hci i]) hs.le
        linarith
    have h1 : s * (32 * D) ≤ s * (2 * N - 1) := by linarith
    have h2 : s * 256 ≤ s * (2 * N - 1) := by linarith
    have h1' := le_of_mul_le_mul_left h1 hs
    have h2' := le_of_mul_le_mul_left h2 hs
    linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hab : ∀ i, 2 * (D : ℤ) + 2 < b i - a i := by
    intro i
    rw [← hadef, ← hbdef]
    have : (D : ℤ) + 3 ≤ N := by exact_mod_cast hND
    simp only
    omega
  have hsmallΛ : SmallClusters (O ∪ (latBox a b)ᶜ) D :=
    smallClusters_of_subset hsmall subset_union_left
  have hfold : SmallClusters (foldBox a b ⁻¹' O) (2 * ⌊ρ / s⌋₊ + 1) := by
    rw [hDdef]
    exact foldSmall d O a b D hab hsmallΛ
  -- (1)–(3) a free site on each crossing
  obtain ⟨τ₁, hτ₁, u₁, hu₁f, hu₁Λ, hu₁i, hu₁o, hγu₁⟩ :=
    exists_freeSite_of_crossing hd hs hsρ hρ₁ hN1 hfold hγ₁
  obtain ⟨τ₂, hτ₂, u₂, hu₂f, hu₂Λ, hu₂i, hu₂o, hγu₂⟩ :=
    exists_freeSite_of_crossing hd hs hsρ hρ₁ hN1 hfold hγ₂
  -- (4) the lattice shell `{ρ₂' ≤ |x|_∞ ≤ ρ₁'}`
  obtain ⟨ρ₂', hρ₂'⟩ : ∃ z : ℤ, ⌈(r₂ + 3 * ρ) / s⌉ = z := ⟨_, rfl⟩
  obtain ⟨ρ₁', hρ₁'⟩ : ∃ z : ℤ, ⌊(r₁ - 3 * ρ) / s⌋ = z := ⟨_, rfl⟩
  have hρ₂'le : r₂ + 3 * ρ ≤ s * ρ₂' := by
    have := Int.le_ceil ((r₂ + 3 * ρ) / s)
    rw [hρ₂', div_le_iff₀ hs] at this
    linarith
  have hρ₁'le : s * ρ₁' ≤ r₁ - 3 * ρ := by
    have := Int.floor_le ((r₁ - 3 * ρ) / s)
    rw [hρ₁', le_div_iff₀ hs] at this
    linarith
  have hρ₂'1 : 1 ≤ ρ₂' := by
    rw [← hρ₂']
    have : (0 : ℝ) < (r₂ + 3 * ρ) / s := div_pos (by linarith) hs
    have h := Int.le_ceil ((r₂ + 3 * ρ) / s)
    have : (0 : ℝ) < (⌈(r₂ + 3 * ρ) / s⌉ : ℝ) := by linarith
    have : (0 : ℤ) < ⌈(r₂ + 3 * ρ) / s⌉ := by exact_mod_cast this
    omega
  have hρ' : ρ₂' < ρ₁' := by
    have h1 := Int.ceil_lt_add_one ((r₂ + 3 * ρ) / s)
    have h2 := Int.sub_one_lt_floor ((r₁ - 3 * ρ) / s)
    rw [hρ₂'] at h1
    rw [hρ₁'] at h2
    have h3 : (r₂ + 3 * ρ) / s + 2 ≤ (r₁ - 3 * ρ) / s := by
      rw [div_add' _ _ _ hs.ne', div_le_div_iff_of_pos_right hs]
      linarith
    have : (ρ₂' : ℝ) < ρ₁' := by linarith
    exact_mod_cast this
  have hushell : ∀ u : Zd d, WithinInf ((N : ℤ) - 1) u c →
      (∃ i, r₂ + 3 * ρ < s * |(u i : ℝ)|) → (∀ i, s * |(u i : ℝ)| < r₁ - 3 * ρ) →
      u ∈ {x | x ∈ latBox a b ∧ (∃ i, ρ₂' ≤ |x i - (0 : Zd d) i|) ∧ WithinInf ρ₁' x 0} := by
    intro u hu hi ho
    refine ⟨(hΛ u).1 hu, ?_, fun i => ?_⟩
    · obtain ⟨i, hi⟩ := hi
      refine ⟨i, ?_⟩
      simp only [Pi.zero_apply, sub_zero]
      rw [← hρ₂', Int.ceil_le, div_le_iff₀ hs]
      push_cast
      linarith
    · simp only [Pi.zero_apply, sub_zero]
      rw [← hρ₁', Int.le_floor, le_div_iff₀ hs]
      push_cast
      linarith [ho i]
  have hc0' : (0 : Zd d) ∈ latBox a b := (hΛ 0).1 hc0
  have hside' : ∀ i, (0 : Zd d) i + ρ₁' ≤ b i ∨ a i ≤ (0 : Zd d) i - ρ₁' := by
    intro i
    rw [← hadef, ← hbdef]
    simp only [Pi.zero_apply, zero_add, zero_sub]
    rcases hside i with h | h
    · left
      have h1 : s * ρ₁' ≤ s * (((c i : ℤ) : ℝ) + N - 1) := by linarith
      have h2 := le_of_mul_le_mul_left h1 hs
      have : (ρ₁' : ℝ) ≤ ((c i + ((N : ℤ) - 1) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · right
      have h1 : s * (((c i : ℤ) : ℝ) - N + 1) ≤ s * (-ρ₁') := by linarith
      have h2 := le_of_mul_le_mul_left h1 hs
      have : ((c i - ((N : ℤ) - 1) : ℤ) : ℝ) ≤ ((-ρ₁' : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  obtain ⟨γ', hγ'ch, hγ'h, hγ'l, hγ'mem⟩ := exists_shell_chain hd hρ₂'1 hρ' hc0' hside'
    (hushell u₁ hu₁Λ hu₁i hu₁o) (hushell u₂ hu₂Λ hu₂i hu₂o)
  -- (5) box surgery and loop erasure
  have hsurg := boxSurgery d hd O a b D hab hsmallΛ γ' u₁ u₂ hγ'ch
    (fun x hx => (hγ'mem x hx).1) hγ'h hγ'l hu₁f hu₂f
  have hu₁O : u₁ ∈ O := by
    have h := hu₁f.1
    rwa [Set.mem_preimage, foldBox_of_mem ((hΛ u₁).1 hu₁Λ)] at h
  have hu₁S : u₁ ∈ {y | y ∈ O ∩ latBox a b ∧ ∃ x ∈ γ', WithinInf (2 * (D : ℤ) + 2) y x} :=
    ⟨⟨hu₁O, (hΛ u₁).1 hu₁Λ⟩, u₁, List.mem_of_mem_head? hγ'h, fun i => by
      rw [sub_self, abs_zero]; positivity⟩
  obtain ⟨l, hlnd, hlch, hlh, hll, hlS⟩ :=
    HigherDimLFPP.DGZ.exists_nodup_isChain_of_reflTransGen hu₁S hsurg
  -- the sites of the rerouted path are good
  have hSfacts : ∀ y ∈ {y | y ∈ O ∩ latBox a b ∧ ∃ x ∈ γ', WithinInf (2 * (D : ℤ) + 2) y x},
      obox (latPt s y) s ⊆ (cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂) ∩
          obox (latPt s c) (s * N) ∧
        selfDiam ξ φ (latPt s y) s ≤ t ∧ y ∈ boxF 0 ⌈r₁ / s⌉₊ := by
    intro y hy
    obtain ⟨⟨hyO, hyΛ⟩, x, hxγ, hyx⟩ := hy
    obtain ⟨-, ⟨j, hj⟩, hxo⟩ := hγ'mem x hxγ
    have hyc : WithinInf ((N : ℤ) - 1) y c := (hΛ y).2 hyΛ
    have hyx' : ∀ i, |((y i : ℤ) : ℝ) - (x i : ℝ)| ≤ 2 * D + 2 := fun i => by
      have := hyx i
      exact_mod_cast this
    have hyi : ∀ i, s * |(y i : ℝ)| ≤ r₁ - ρ / 2 := by
      intro i
      have hxi : |(x i : ℝ)| ≤ ρ₁' := by
        have := hxo i
        simp only [Pi.zero_apply, sub_zero] at this
        exact_mod_cast this
      have h1 := abs_sub_abs_le_abs_sub (y i : ℝ) (x i : ℝ)
      have h2 : |(y i : ℝ)| ≤ ρ₁' + (2 * D + 2) := by linarith [hyx' i]
      have h3 := mul_le_mul_of_nonneg_left h2 hs.le
      linarith
    have hyj : r₂ + ρ / 2 ≤ s * |(y j : ℝ)| := by
      have hxj : (ρ₂' : ℝ) ≤ |(x j : ℝ)| := by
        simp only [Pi.zero_apply, sub_zero] at hj
        exact_mod_cast hj
      have h1 := abs_sub_abs_le_abs_sub (x j : ℝ) (y j : ℝ)
      rw [abs_sub_comm] at h1
      have h2 : (ρ₂' : ℝ) - (2 * D + 2) ≤ |(y j : ℝ)| := by linarith [hyx' j]
      have h3 := mul_le_mul_of_nonneg_left h2 hs.le
      linarith
    refine ⟨fun z hz => ⟨⟨fun i => ?_, fun hzo => ?_⟩, obox_latPt_subset hs hyc hz⟩,
      hgood y hyO hyc ⟨j, hyj⟩ hyi, ?_⟩
    · have h1 : |z i - s * (y i : ℝ)| < s := hz i
      have h2 := abs_sub_abs_le_abs_sub (z i) (s * (y i : ℝ))
      rw [abs_mul, abs_of_pos hs] at h2
      simp only [PiLp.zero_apply, sub_zero]
      linarith [hyi i]
    · have h1 : |z j - s * (y j : ℝ)| < s := hz j
      have h2 : |z j - 0| < r₂ := hzo j
      rw [sub_zero] at h2
      have h3 := abs_sub_abs_le_abs_sub (s * (y j : ℝ)) (z j)
      rw [abs_sub_comm] at h1
      rw [abs_mul, abs_of_pos hs] at h3
      linarith
    · rw [mem_boxF]
      intro i
      have h1 : |(y i : ℝ)| ≤ r₁ / s := by
        rw [le_div_iff₀ hs]
        linarith [hyi i]
      have h2 : |(y i : ℝ)| ≤ (⌈r₁ / s⌉₊ : ℝ) := h1.trans (Nat.le_ceil _)
      simp only [Pi.zero_apply, sub_zero]
      exact_mod_cast h2
  -- (6) the chain of boxes
  have hu₂S := hlS u₂ (List.mem_of_mem_getLast? hll)
  obtain ⟨hV₁, ht₁, -⟩ := hSfacts u₁ hu₁S
  obtain ⟨hV₂, ht₂, -⟩ := hSfacts u₂ hu₂S
  obtain ⟨hjc, hdc⟩ := chain_le_of_isChain (ξ := ξ) hφ hs (fun y hy => (hSfacts y hy).1)
    (fun y hy => (hSfacts y hy).2.1) l u₁ u₂ hlch hlh hll hlS
  have hj₁ := (PcwJoined.of_convex (convex_obox _ _) hγu₁ (mem_obox_self _ hs)).mono hV₁
  have hj₂ := (PcwJoined.of_convex (convex_obox _ _) (mem_obox_self _ hs) hγu₂).mono hV₂
  have hlen : (l.length : ℝ) ≤ ((2 * ⌈r₁ / s⌉₊ + 1) ^ d : ℕ) := by
    have h1 : l.toFinset ⊆ boxF 0 ⌈r₁ / s⌉₊ := fun y hy =>
      (hSfacts y (hlS y (List.mem_toFinset.1 hy))).2.2
    have h2 := Finset.card_le_card h1
    rw [List.toFinset_card_of_nodup hlnd, card_boxF] at h2
    exact_mod_cast h2
  have hlen1 : 1 ≤ l.length := by
    rcases l with _ | ⟨y, l'⟩
    · simp at hlh
    · simp
  have hcast : ((l.length - 1 : ℕ) : ℝ) = l.length - 1 := by
    rw [Nat.cast_sub hlen1, Nat.cast_one]
  rw [hcast] at hdc
  refine ⟨τ₁, hτ₁, τ₂, hτ₂, hj₁.trans (hjc.trans hj₂), ?_⟩
  have e1 := lfppDistOn_triangle (ζ := ξ) hφ hj₁ (hjc.trans hj₂)
  have e2 := lfppDistOn_triangle (ζ := ξ) hφ hjc hj₂
  have e3 := lfppDistOn_le_selfDiam_of_subset (ξ := ξ) hφ hV₁ hγu₁ (mem_obox_self _ hs)
  have e4 := lfppDistOn_le_selfDiam_of_subset (ξ := ξ) hφ hV₂ (mem_obox_self _ hs) hγu₂
  have e5 := mul_le_mul_of_nonneg_right hlen ht
  nlinarith

/-! ### The certificate as a property of a coarse and a fine field -/

/-- **The around certificate** (MA7 D-4.9, the event `E = 𝒢₁ ∩ 𝒢₂`, written as a property of a
coarse field `ψ` and a fine field `g`): `|ψ| ≤ lev` on the closed shell `B̄_{r₁}(0) \ B_{r₂}(0)`,
and the closed sites — the sites `x` of the shell region `r₂ + ϱ/2 ≤ s|x|_∞ ≤ r₁ - ϱ/2` with
`selfDiam(g)(B_s(s x)) > T` — form clusters of `ℓ^∞`-diameter `≤ ⌊ϱ/s⌋`. It depends only on
`ψ, g` on the closed shell (`aroundCert_congr`, `measurableSet_aroundCert_comap`). -/
def AroundCert (ξ : ℝ) (ψ g : Rd d → ℝ) (r₁ r₂ ϱ s T lev : ℝ) : Prop :=
  (∀ z ∈ cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂, |ψ z| ≤ lev) ∧
    SmallClusters {x : Zd d | ¬ (((∃ i, r₂ + ϱ / 2 ≤ s * |(x i : ℝ)|) ∧
      ∀ i, s * |(x i : ℝ)| ≤ r₁ - ϱ / 2) ∧ T < selfDiam ξ g (latPt s x) s)} ⌊ϱ / s⌋₊

/-- The closed `s`-box of a site of the shell region lies in the closed shell (`2s ≤ ϱ`). -/
lemma cbox_latPt_subset_shell {r₁ r₂ ϱ s : ℝ} (hs : 0 < s) (hsϱ : 2 * s ≤ ϱ) {x : Zd d}
    (hi : ∃ i, r₂ + ϱ / 2 ≤ s * |(x i : ℝ)|) (ho : ∀ i, s * |(x i : ℝ)| ≤ r₁ - ϱ / 2) :
    cbox (latPt s x) s ⊆ cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂ := by
  intro z hz
  refine ⟨fun i => ?_, fun hzo => ?_⟩
  · have h1 : |z i - s * (x i : ℝ)| ≤ s := hz i
    have h2 := abs_sub_abs_le_abs_sub (z i) (s * (x i : ℝ))
    rw [abs_mul, abs_of_pos hs] at h2
    simp only [PiLp.zero_apply, sub_zero]
    linarith [ho i]
  · obtain ⟨j, hj⟩ := hi
    have h1 : |z j - s * (x j : ℝ)| ≤ s := hz j
    have h2 : |z j - 0| < r₂ := hzo j
    rw [sub_zero] at h2
    have h3 := abs_sub_abs_le_abs_sub (s * (x j : ℝ)) (z j)
    rw [abs_sub_comm] at h1
    rw [abs_mul, abs_of_pos hs] at h3
    linarith

/-- **Locality of the certificate**: it only depends on `ψ` and `g` on the closed shell
`B̄_{r₁}(0) \ B_{r₂}(0)` (`2s ≤ ϱ`). -/
theorem aroundCert_congr {ξ : ℝ} {ψ g ψ' g' : Rd d → ℝ} {r₁ r₂ ϱ s T lev : ℝ} (hs : 0 < s)
    (hsϱ : 2 * s ≤ ϱ) (hψ : ∀ z ∈ cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂, ψ z = ψ' z)
    (hg : ∀ z ∈ cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂, g z = g' z) :
    AroundCert ξ ψ g r₁ r₂ ϱ s T lev ↔ AroundCert ξ ψ' g' r₁ r₂ ϱ s T lev := by
  have hsd : ∀ x : Zd d, ((∃ i, r₂ + ϱ / 2 ≤ s * |(x i : ℝ)|) ∧
      ∀ i, s * |(x i : ℝ)| ≤ r₁ - ϱ / 2) →
      selfDiam ξ g (latPt s x) s = selfDiam ξ g' (latPt s x) s := fun x hx =>
    selfDiam_congr fun z hz =>
      hg z (cbox_latPt_subset_shell hs hsϱ hx.1 hx.2 (obox_subset_cbox _ _ hz))
  have hset : {x : Zd d | ¬ (((∃ i, r₂ + ϱ / 2 ≤ s * |(x i : ℝ)|) ∧
      ∀ i, s * |(x i : ℝ)| ≤ r₁ - ϱ / 2) ∧ T < selfDiam ξ g (latPt s x) s)} =
      {x : Zd d | ¬ (((∃ i, r₂ + ϱ / 2 ≤ s * |(x i : ℝ)|) ∧
        ∀ i, s * |(x i : ℝ)| ≤ r₁ - ϱ / 2) ∧ T < selfDiam ξ g' (latPt s x) s)} := by
    ext x
    simp only [mem_ofPred_eq]
    constructor
    · rintro hx ⟨hreg, hT⟩
      exact hx ⟨hreg, by rwa [hsd x hreg]⟩
    · rintro hx ⟨hreg, hT⟩
      exact hx ⟨hreg, by rwa [← hsd x hreg]⟩
  unfold AroundCert
  rw [hset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun z hz => by rw [← hψ z hz]; exact h1 z hz, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun z hz => by rw [hψ z hz]; exact h1 z hz, h2⟩

/-- **The certificate gives the around-good property** (MA7 D-4.9 "On `E`"): for continuous `ψ, g`
and `ξ ≥ 0`, `AroundCert ξ ψ g r₁ r₂ ϱ s T lev` gives `AroundGood` for the field `ψ + g` in every
admissible cube `B = obox (s c) (s N)`, with threshold `2 (2⌈r₁/s⌉+1)^d e^{ξ lev} T`. -/
theorem aroundGood_of_aroundCert (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 ≤ ξ) {ψ g : Rd d → ℝ}
    (hψ : Continuous ψ) (hg : Continuous g) {r₁ r₂ ϱ s T lev : ℝ} (hs : 0 < s)
    (hsϱ : 8 * s ≤ ϱ) (hϱ₂ : 16 * ϱ ≤ r₂) (hϱ₁ : 16 * ϱ ≤ r₁ - r₂) (hT : 0 ≤ T)
    (hcert : AroundCert ξ ψ g r₁ r₂ ϱ s T lev) {c : Zd d} {N : ℕ}
    (hc0 : WithinInf ((N : ℤ) - 1) 0 c)
    (hside : ∀ i, r₁ ≤ s * ((c i : ℝ) + N) ∨ s * ((c i : ℝ) - N) ≤ -r₁) :
    AroundGood ξ (fun z => ψ z + g z) 0 r₁ r₂ (obox (latPt s c) (s * N))
      (2 * ((2 * ⌈r₁ / s⌉₊ + 1) ^ d : ℕ) * (Real.exp (ξ * lev) * T)) := by
  refine aroundGood_of_smallClusters hd (hψ.add hg) hs hsϱ hϱ₂ hϱ₁ hc0 hside hcert.2
    (mul_nonneg (Real.exp_pos _).le hT) fun x hx _ hi ho => ?_
  have hgT : selfDiam ξ g (latPt s x) s ≤ T := by
    by_contra hlt
    exact hx ⟨⟨hi, ho⟩, not_le.1 hlt⟩
  refine (selfDiam_le_mul_of_exp_le (hψ.add hg) hg (Real.exp_pos _).le fun z hz => ?_).trans
    (mul_le_mul_of_nonneg_left hgT (Real.exp_pos _).le)
  have hz := cbox_latPt_subset_shell hs (by linarith) hi ho (obox_subset_cbox _ _ hz)
  have h1 := le_trans (le_abs_self (ψ z)) (hcert.1 z hz)
  show Real.exp (ξ * (ψ z + g z)) ≤ Real.exp (ξ * lev) * Real.exp (ξ * g z)
  rw [← Real.exp_add, Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_left h1 hξ
  linarith

/-- **Measurability of the certificate event** for continuous fields with measurable values. -/
theorem measurableSet_aroundCert {Ω : Type*} [MeasurableSpace Ω] {ψ g : Rd d → Ω → ℝ}
    (hψc : ∀ ω, Continuous fun z => ψ z ω) (hψm : ∀ z, Measurable (ψ z))
    (hgc : ∀ ω, Continuous fun z => g z ω) (hgm : ∀ z, Measurable (g z))
    (ξ r₁ r₂ ϱ : ℝ) {s : ℝ} (hs : 0 < s) (T lev : ℝ) :
    MeasurableSet {ω | AroundCert ξ (fun z => ψ z ω) (fun z => g z ω) r₁ r₂ ϱ s T lev} := by
  set closed : Zd d → Set Ω := fun x => {ω | ((∃ i, r₂ + ϱ / 2 ≤ s * |(x i : ℝ)|) ∧
    ∀ i, s * |(x i : ℝ)| ≤ r₁ - ϱ / 2) ∧ T < selfDiam ξ (fun z => g z ω) (latPt s x) s}
    with hclosed
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ⌈|r₁ - ϱ / 2| / s⌉₊ = K := ⟨_, rfl⟩
  have hF : ∀ x, x ∉ boxF 0 K → closed x = ∅ := by
    intro x hx
    ext ω
    simp only [hclosed, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, ho⟩, -⟩
    apply hx
    rw [mem_boxF]
    intro i
    simp only [Pi.zero_apply, sub_zero]
    have h2 : |(x i : ℝ)| ≤ K := by
      rw [← hK]
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ hs]
      linarith [ho i, le_abs_self (r₁ - ϱ / 2)]
    exact_mod_cast h2
  have hm : ∀ x, MeasurableSet (closed x) := fun x => by
    show MeasurableSet {ω | _ ∧ _}
    rw [Set.ofPred_and]
    exact (MeasurableSet.const _).inter
      (measurableSet_lt measurable_const (measurable_selfDiam hgc hgm ξ _ s))
  have h1 : MeasurableSet
      {ω | ∀ z ∈ cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂, |ψ z ω| ≤ lev} := by
    have := (measurableSet_exists_lt_abs hψc (fun z _ => hψm z) lev
      (B := cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂)).compl
    convert this using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_exists, not_and, not_lt]
  have h2 := measurableSet_setOf_config closed (boxF 0 K) hF hm
    (fun O => SmallClusters O ⌊ϱ / s⌋₊)
  exact h1.inter h2

/-- **Local measurability of the certificate event**: it is measurable for the σ-algebra generated
by `ψ` and `g` on the closed shell `B̄_{r₁}(0) \ B_{r₂}(0)` (`0 < s`, `2s ≤ ϱ`). -/
theorem measurableSet_aroundCert_comap {Ω : Type*} {ψ g : Rd d → Ω → ℝ}
    (hψc : ∀ ω, Continuous fun z => ψ z ω) (hgc : ∀ ω, Continuous fun z => g z ω)
    (ξ r₁ r₂ ϱ : ℝ) {s : ℝ} (hs : 0 < s) (hsϱ : 2 * s ≤ ϱ) (T lev : ℝ) :
    MeasurableSet[MeasurableSpace.comap
        (fun ω (z : (cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂ : Set (Rd d))) => ψ z ω)
        MeasurableSpace.pi ⊔
      MeasurableSpace.comap
        (fun ω (z : (cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂ : Set (Rd d))) => g z ω)
        MeasurableSpace.pi]
      {ω | AroundCert ξ (fun z => ψ z ω) (fun z => g z ω) r₁ r₂ ϱ s T lev} := by
  set m₁ : MeasurableSpace Ω := MeasurableSpace.comap
    (fun ω (z : (cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂ : Set (Rd d))) => ψ z ω)
    MeasurableSpace.pi with hm₁
  set m₂ : MeasurableSpace Ω := MeasurableSpace.comap
    (fun ω (z : (cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂ : Set (Rd d))) => g z ω)
    MeasurableSpace.pi with hm₂
  let mΩ : MeasurableSpace Ω := m₁ ⊔ m₂
  set closed : Zd d → Set Ω := fun x => {ω | ((∃ i, r₂ + ϱ / 2 ≤ s * |(x i : ℝ)|) ∧
    ∀ i, s * |(x i : ℝ)| ≤ r₁ - ϱ / 2) ∧ T < selfDiam ξ (fun z => g z ω) (latPt s x) s}
    with hclosed
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ⌈|r₁ - ϱ / 2| / s⌉₊ = K := ⟨_, rfl⟩
  have hF : ∀ x, x ∉ boxF 0 K → closed x = ∅ := by
    intro x hx
    ext ω
    simp only [hclosed, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, ho⟩, -⟩
    apply hx
    rw [mem_boxF]
    intro i
    simp only [Pi.zero_apply, sub_zero]
    have h2 : |(x i : ℝ)| ≤ K := by
      rw [← hK]
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ hs]
      linarith [ho i, le_abs_self (r₁ - ϱ / 2)]
    exact_mod_cast h2
  have hm : ∀ x, MeasurableSet (closed x) := by
    intro x
    by_cases hreg : (∃ i, r₂ + ϱ / 2 ≤ s * |(x i : ℝ)|) ∧ ∀ i, s * |(x i : ℝ)| ≤ r₁ - ϱ / 2
    · have hf := measurable_selfDiam_comap hgc ξ (latPt s x) hs.le
      have hset : MeasurableSet[MeasurableSpace.comap
          (fun ω (z : cbox (latPt s x) s) => g z ω) MeasurableSpace.pi]
          {ω | T < selfDiam ξ (fun z => g z ω) (latPt s x) s} :=
        measurableSet_lt measurable_const hf
      have hle : MeasurableSpace.comap (fun ω (z : cbox (latPt s x) s) => g z ω)
          MeasurableSpace.pi ≤ m₁ ⊔ m₂ :=
        (comap_restrict_le g (cbox_latPt_subset_shell hs hsϱ hreg.1 hreg.2)).trans le_sup_right
      have e : closed x = {ω | T < selfDiam ξ (fun z => g z ω) (latPt s x) s} := by
        ext ω
        exact ⟨fun h => h.2, fun h => ⟨hreg, h⟩⟩
      rw [e]
      exact hle _ hset
    · have e : closed x = ∅ := by
        ext ω
        exact ⟨fun h => hreg h.1, fun h => h.elim⟩
      rw [e]
      exact MeasurableSet.empty
  have h1 : MeasurableSet
      {ω | ∀ z ∈ cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂, |ψ z ω| ≤ lev} := by
    have h := (measurableSet_exists_lt_comap hψc
      (subset_refl (cbox (0 : Rd d) r₁ \ obox (0 : Rd d) r₂)) lev).2
    have h' := (le_sup_left : m₁ ≤ m₁ ⊔ m₂) _ h
    convert h'.compl using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_exists, not_and, not_lt]
  have h2 := measurableSet_setOf_config closed (boxF 0 K) hF hm
    (fun O => SmallClusters O ⌊ϱ / s⌋₊)
  exact h1.inter h2

end DGZ

end HigherDimLQGMetric
