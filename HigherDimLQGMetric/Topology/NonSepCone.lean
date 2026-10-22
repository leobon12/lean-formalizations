import HigherDimLQGMetric.Topology.NonSepMV
import HigherDimLFPP.Frozen.Rd
import Mathlib.Topology.Homotopy.Affine
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Codimension-two nonseparation (D-NS), part 3: loops in a punctured ball (NS-2), punctured
balls are path-connected, arcs have empty interior (NS-4)

Packet M4 (ruling M9). Source: planning audit `planning/audits/MA1-sections-1-4.md`, Details (a)
**A15**, steps NS-2 and NS-4 (MA1 probe `loopContractible_ball_diff`). Carrier: `ℝ^d` as
`HigherDimLFPP.Rd d = EuclideanSpace ℝ (Fin d)`.

* `loopsContractibleIn_ball_diff` (**NS-2**, the cone argument, `d ≥ 3`): every loop in
  `B(c, ρ) ∖ {p}` is freely null-homotopic there. Proof: the straight-line homotopy from the loop
  `ℓ` to its piecewise-linear interpolation `λ` at the nodes `ℓ(k/n)` (`pwLinear`, built from tent
  functions) stays in balls `B(ℓ(k/n), r) ⊆ B(c, ρ) ∖ {p}`; the "shadow" of `λ` seen from `p` lies in
  the countably many affine planes `p + span{ℓ(k/n) - p, ℓ((k+1)/n) - p}`, which are Lebesgue-null
  for `d ≥ 3` (Mathlib `Measure.addHaar_affineSubspace`); the straight-line contraction of `λ`
  to a point `c₀ ∈ B(c, ρ)` off these planes avoids `p`.
* `loopContractible_ball_diff`: NS-2 in the exact shape of the MA1 probe.
* `joinedIn_ball_diff_singleton` (`d ≥ 2`): a punctured ball is path-connected (segment, or a
  two-segment detour through a point off the line).
* `not_ball_subset_range` (**NS-4**, `d ≥ 2`): an arc (injective continuous image of `[0,1]`)
  contains no ball. Proof: the inverse of the arc is continuous; along two paths in the ball with
  common endpoints and disjoint interiors it takes the mean of its endpoint values (intermediate
  value theorem) at two different points, contradicting injectivity.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGMetric.Topology

open Set unitInterval MeasureTheory Metric
open scoped RealInnerProductSpace
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### Null affine subspaces -/

/-- An affine subspace of `ℝ^d` through `p` spanned by `k < d` vectors is Lebesgue-null. -/
lemma volume_mk'_span_eq_zero {k : ℕ} (hk : k < d) (p : Rd d) (v : Fin k → Rd d) :
    volume (AffineSubspace.mk' p (Submodule.span ℝ (range v)) : Set (Rd d)) = 0 := by
  apply Measure.addHaar_affineSubspace
  intro htop
  have h1 := congrArg AffineSubspace.direction htop
  rw [AffineSubspace.direction_mk', AffineSubspace.direction_top] at h1
  have h2 : Module.finrank ℝ (Submodule.span ℝ (range v)) ≤ k := by
    simpa [Set.finrank] using finrank_range_le_card (R := ℝ) v
  rw [h1, finrank_top, finrank_euclideanSpace_fin] at h2
  omega

/-- A ball of positive radius is not contained in a Lebesgue-null set. -/
lemma exists_mem_ball_notMem_of_null {c : Rd d} {ρ : ℝ} (hρ : 0 < ρ) {Z : Set (Rd d)}
    (hZ : volume Z = 0) : ∃ z ∈ ball c ρ, z ∉ Z := by
  by_contra h
  push Not at h
  exact (measure_ball_pos volume c hρ).ne' (measure_mono_null h hZ)

/-! ### Piecewise-linear interpolation -/

/-- The tent function `max 0 (1 - |x|)`. -/
def tent (x : ℝ) : ℝ := max 0 (1 - |x|)

lemma continuous_tent : Continuous tent :=
  continuous_const.max (continuous_const.sub continuous_abs)

lemma tent_eq_zero {x : ℝ} (h : 1 ≤ |x|) : tent x = 0 := max_eq_left (by linarith)

lemma tent_of_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : tent x = 1 - x := by
  rw [tent, abs_of_nonneg h0, max_eq_right (by linarith)]

lemma tent_of_nonpos {x : ℝ} (h0 : -1 ≤ x) (h1 : x ≤ 0) : tent x = 1 + x := by
  rw [tent, abs_of_nonpos h1, max_eq_right (by linarith)]
  ring

/-- Piecewise-linear interpolation of the nodes `a 0, …, a n` at the points `k / n`. -/
def pwLinear {E : Type*} [AddCommGroup E] [Module ℝ E] (n : ℕ) (a : ℕ → E) (s : ℝ) : E :=
  ∑ k ∈ Finset.range (n + 1), tent (n * s - k) • a k

lemma continuous_pwLinear {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (n : ℕ) (a : ℕ → E) :
    Continuous (pwLinear n a) := by
  unfold pwLinear
  exact continuous_finsetSum _ fun k _ =>
    (continuous_tent.comp ((continuous_const.mul continuous_id).sub continuous_const)).smul
      continuous_const

/-- On `[k/n, (k+1)/n]` the interpolation is the convex combination of the two nodes. -/
lemma pwLinear_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {n k : ℕ} (a : ℕ → E) (hk : k < n)
    {s : ℝ} (h0 : (k : ℝ) ≤ n * s) (h1 : n * s ≤ k + 1) :
    pwLinear n a s = (1 - (n * s - k)) • a k + (n * s - k) • a (k + 1) := by
  unfold pwLinear
  rw [Finset.sum_eq_add k (k + 1) (by omega)]
  · rw [tent_of_nonneg (by linarith) (by linarith),
      tent_of_nonpos (by push_cast; linarith) (by push_cast; linarith)]
    push_cast
    congr 1
    congr 1
    ring
  · intro m _ hne
    rw [tent_eq_zero, zero_smul]
    rcases lt_or_gt_of_ne hne.1 with hlt | hgt
    · have : (m : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have : (k : ℝ) + 2 ≤ m := by
        have : k + 2 ≤ m := by omega
        exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]
      linarith
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- Every `s ∈ [0, 1]` lies in some `[k/n, (k+1)/n]` with `k < n`. -/
lemma exists_cell_index {n : ℕ} (hn : 0 < n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ k < n, (k : ℝ) ≤ n * s ∧ n * s ≤ k + 1 := by
  by_cases h : ⌊(n : ℝ) * s⌋₊ < n
  · refine ⟨⌊(n : ℝ) * s⌋₊, h, Nat.floor_le (by positivity), (Nat.lt_floor_add_one _).le⟩
  · refine ⟨n - 1, by omega, ?_, ?_⟩
    · have h1 : (n : ℝ) ≤ n * s := by
        have := Nat.floor_le (show (0 : ℝ) ≤ n * s by positivity)
        have h2 : (n : ℝ) ≤ ⌊(n : ℝ) * s⌋₊ := by exact_mod_cast not_lt.1 h
        linarith
      have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      linarith
    · rw [Nat.cast_sub (by omega)]
      have : (n : ℝ) * s ≤ n := by
        have : (0 : ℝ) ≤ n := by positivity
        nlinarith
      push_cast
      linarith

/-! ### NS-2: loops in a punctured ball are null-homotopic (`d ≥ 3`) -/

/-- If `x - p` lies in a subspace `V` and `c₀ - p` does not, the segment from `x` to `c₀` avoids
`p` (unless `x = p`). -/
lemma lineMap_ne_of_notMem {x c₀ p : Rd d} {V : Submodule ℝ (Rd d)} (hxV : x - p ∈ V)
    (hc₀ : c₀ - p ∉ V) (hxp : x ≠ p) {τ : ℝ} :
    AffineMap.lineMap x c₀ τ ≠ p := by
  rw [AffineMap.lineMap_apply_module]
  intro h
  by_cases hτ : τ = 0
  · subst hτ
    apply hxp
    simpa using h
  · apply hc₀
    have key : τ • (c₀ - p) = (-(1 - τ)) • (x - p) := by
      rw [← sub_eq_zero]
      rw [show τ • (c₀ - p) - (-(1 - τ)) • (x - p) = ((1 - τ) • x + τ • c₀) - p by module, h,
        sub_self]
    have : c₀ - p = τ⁻¹ • ((-(1 - τ)) • (x - p)) := by
      rw [← key, inv_smul_smul₀ hτ]
    rw [this]
    exact V.smul_mem _ (V.smul_mem _ hxV)

/-- **NS-2.** For `d ≥ 3`, every loop in a punctured ball `B(c, ρ) ∖ {p}` is freely
null-homotopic in `B(c, ρ) ∖ {p}` (`p ∈ ℝ^d` arbitrary). -/
theorem loopsContractibleIn_ball_diff (hd : 3 ≤ d) (c : Rd d) (ρ : ℝ) (p : Rd d) :
    LoopsContractibleIn (ball c ρ \ {p}) := by
  intro ℓ hℓ hloop
  set U := ball c ρ \ {p} with hU
  have hUo : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hρ : 0 < ρ := pos_of_mem_ball (hℓ 0).1
  -- a uniform radius `r` with `B(ℓ t, r) ⊆ U`
  obtain ⟨r, hr, hrU⟩ := (isCompact_range ℓ.continuous).exists_thickening_subset_open hUo
    (range_subset_iff.2 hℓ)
  have hball : ∀ t, ball (ℓ t) r ⊆ U :=
    fun t => (ball_subset_thickening (mem_range_self t) r).trans hrU
  -- uniform continuity: `|s - t| < η ⇒ |ℓ s - ℓ t| < r`
  obtain ⟨η, hη, hηℓ⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous ℓ.continuous) r hr
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnη : 1 / (n : ℝ) < η := by rwa [one_div_lt hnpos hη]
  -- the nodes and the piecewise-linear loop
  set a : ℕ → Rd d := fun k => ℓ (clampI ((k : ℝ) / n)) with ha
  set lam : C(I, Rd d) := ⟨fun s => pwLinear n a s,
    (continuous_pwLinear n a).comp continuous_subtype_val⟩ with hlam
  -- the planes containing the shadow
  set V : ℕ → Submodule ℝ (Rd d) :=
    fun k => Submodule.span ℝ (range ![a k - p, a (k + 1) - p]) with hV
  -- local structure: `ℓ s, λ s ∈ B(a k, r)` and `λ s - p ∈ V k`
  have hloc : ∀ s : I, ∃ k, ball (a k) r ⊆ U ∧ ℓ s ∈ ball (a k) r ∧ lam s ∈ ball (a k) r ∧
      lam s - p ∈ V k := by
    intro s
    obtain ⟨k, hk, hk0, hk1⟩ := exists_cell_index hn0 s.2.1 s.2.2
    have hkn0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    have hkn1 : (k : ℝ) / n ≤ 1 := by
      rw [div_le_one hnpos]; exact_mod_cast hk.le
    have hk1n0 : (0 : ℝ) ≤ ((k : ℝ) + 1) / n := by positivity
    have hk1n1 : ((k : ℝ) + 1) / n ≤ 1 := by
      rw [div_le_one hnpos]; exact_mod_cast hk
    have hsk : (k : ℝ) / n ≤ s := by rw [div_le_iff₀ hnpos]; linarith
    have hsk1 : (s : ℝ) ≤ ((k : ℝ) + 1) / n := by rw [le_div_iff₀ hnpos]; linarith
    have hstep : ((k : ℝ) + 1) / n - (k : ℝ) / n = 1 / n := by ring
    refine ⟨k, hball _, ?_, ?_, ?_⟩
    · -- `ℓ s` is close to `ℓ (k/n)`
      rw [mem_ball]
      apply hηℓ
      rw [Subtype.dist_eq, coe_clampI hkn0 hkn1, Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    · -- `λ s` is a convex combination of `a k` and `a (k+1)`
      have hlam_s : lam s = (1 - (n * (s : ℝ) - k)) • a k + (n * (s : ℝ) - k) • a (k + 1) :=
        pwLinear_eq a hk hk0 hk1
      have hak1 : a (k + 1) ∈ ball (a k) r := by
        rw [mem_ball]
        apply hηℓ
        rw [Subtype.dist_eq, coe_clampI (by push_cast; exact hk1n0) (by push_cast; exact hk1n1),
          coe_clampI hkn0 hkn1, Real.dist_eq]
        push_cast
        rw [hstep, abs_of_pos (by positivity)]
        exact hnη
      rw [hlam_s]
      exact convex_ball (a k) r (mem_ball_self hr) hak1 (by linarith) (by linarith) (by ring)
    · -- `λ s - p ∈ V k`
      have hlam_s : lam s = (1 - (n * (s : ℝ) - k)) • a k + (n * (s : ℝ) - k) • a (k + 1) :=
        pwLinear_eq a hk hk0 hk1
      rw [hlam_s]
      have h1 : a k - p ∈ V k := Submodule.subset_span ⟨0, by simp⟩
      have h2 : a (k + 1) - p ∈ V k := Submodule.subset_span ⟨1, by simp⟩
      have : (1 - (n * (s : ℝ) - k)) • a k + (n * (s : ℝ) - k) • a (k + 1) - p =
          (1 - (n * (s : ℝ) - k)) • (a k - p) + (n * (s : ℝ) - k) • (a (k + 1) - p) := by
        module
      rw [this]
      exact (V k).add_mem ((V k).smul_mem _ h1) ((V k).smul_mem _ h2)
  -- the cone point `c₀`, off all the planes `p + V k`
  have hZ0 : volume (⋃ k : ℕ, (AffineSubspace.mk' p (V k) : Set (Rd d))) = 0 :=
    measure_iUnion_null fun k =>
      volume_mk'_span_eq_zero (k := 2) (by omega) p ![a k - p, a (k + 1) - p]
  obtain ⟨c₀, hc₀B, hc₀Z⟩ := exists_mem_ball_notMem_of_null (c := c) hρ hZ0
  have hc₀V : ∀ k, c₀ - p ∉ V k := fun k h =>
    hc₀Z (mem_iUnion.2 ⟨k, AffineSubspace.mem_mk'.2 (by rwa [vsub_eq_sub])⟩)
  -- endpoints of the polygonal loop
  have hlam0 : lam 0 = ℓ 0 := by
    have := pwLinear_eq (n := n) (k := 0) a hn0 (s := 0) (by simp) (by simp)
    simp only [Nat.cast_zero, mul_zero, sub_zero, one_smul, zero_smul, add_zero] at this
    rw [hlam]
    show pwLinear n a ((0 : I) : ℝ) = ℓ 0
    rw [Set.Icc.coe_zero, this]
    simp only [ha, Nat.cast_zero, zero_div, clampI_zero]
  have hlam1 : lam 1 = ℓ 1 := by
    have := pwLinear_eq (n := n) (k := n - 1) a (by omega) (s := 1)
      (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
      (by rw [Nat.cast_sub (by omega)]; push_cast; linarith)
    rw [Nat.cast_sub (by omega), Nat.sub_add_cancel (by omega)] at this
    rw [hlam]
    show pwLinear n a ((1 : I) : ℝ) = ℓ 1
    rw [Set.Icc.coe_one, this]
    have h1 : (1 - ((n : ℝ) * 1 - ((n : ℝ) - (1 : ℕ)))) = 0 := by push_cast; ring
    have h2 : ((n : ℝ) * 1 - ((n : ℝ) - (1 : ℕ))) = 1 := by push_cast; ring
    rw [h1, h2, zero_smul, one_smul, zero_add]
    simp only [ha, div_self hnpos.ne', clampI_one]
  -- the two straight-line homotopies, `ℓ ≃ λ ≃ c₀`
  set K := (ContinuousMap.Homotopy.affine ℓ lam).trans
    (ContinuousMap.Homotopy.affine lam (ContinuousMap.const I c₀)) with hK
  refine ⟨K.toContinuousMap.comp ContinuousMap.prodSwap, ?_, ?_, ?_, c₀, ?_⟩
  · rintro ⟨s, t⟩
    show K (t, s) ∈ U
    obtain ⟨k, hkU, hℓk, hlamk, hlamV⟩ := hloc s
    rw [hK, ContinuousMap.Homotopy.trans_apply]
    split_ifs with h
    · rw [ContinuousMap.Homotopy.affine_apply]
      apply hkU
      exact (convex_ball (a k) r).lineMap_mem hℓk hlamk
        ⟨by simp only; linarith [t.2.1], by simp only; linarith⟩
    · rw [ContinuousMap.Homotopy.affine_apply]
      have hlamU : lam s ∈ U := hkU hlamk
      refine ⟨(convex_ball c ρ).lineMap_mem hlamU.1 hc₀B ⟨?_, ?_⟩, ?_⟩
      · simp only; linarith
      · simp only; linarith [t.2.2]
      · exact lineMap_ne_of_notMem hlamV (hc₀V k) hlamU.2
  · intro s
    show K (0, s) = ℓ s
    exact K.apply_zero s
  · intro t
    show K (t, 0) = K (t, 1)
    simp only [hK, ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.affine_apply,
      hloop, hlam0, hlam1, ContinuousMap.const_apply]
  · intro s
    show K (1, s) = c₀
    rw [K.apply_one]
    rfl

/-- **NS-2** in the exact shape of the MA1 probe `loopContractible_ball_diff`. -/
theorem loopContractible_ball_diff (hd : 3 ≤ d) (c : Rd d) (ρ : ℝ) (p : Rd d)
    (ℓ : C(I, Rd d)) (hℓ : ∀ t, ℓ t ∈ ball c ρ \ {p}) (hloop : ℓ 0 = ℓ 1) :
    ∃ H : C(I × I, Rd d), (∀ q, H q ∈ ball c ρ \ {p}) ∧
      (∀ s, H (s, 0) = ℓ s) ∧ (∀ t, H (0, t) = H (1, t)) ∧ ∃ c' : Rd d, ∀ s, H (s, 1) = c' :=
  loopsContractibleIn_ball_diff hd c ρ p ℓ hℓ hloop

/-- A point outside a given ball (`d ≥ 1`). -/
lemma exists_notMem_ball (hd : 1 ≤ d) (c : Rd d) (ρ : ℝ) : ∃ p : Rd d, p ∉ ball c ρ := by
  refine ⟨c + (|ρ| + 1) • EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ), ?_⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have := le_abs_self ρ
  linarith

/-- NS-2 for a ball minus a set with at most one point (`d ≥ 3`). -/
theorem loopsContractibleIn_ball_diff_of_subsingleton (hd : 3 ≤ d) (c : Rd d) (ρ : ℝ)
    {S : Set (Rd d)} (hS : S.Subsingleton) : LoopsContractibleIn (ball c ρ \ S) := by
  rcases hS.eq_empty_or_singleton with rfl | ⟨p, rfl⟩
  · obtain ⟨p, hp⟩ := exists_notMem_ball (by omega) c ρ
    rw [sdiff_empty, ← sdiff_singleton_eq_self hp]
    exact loopsContractibleIn_ball_diff hd c ρ p
  · exact loopsContractibleIn_ball_diff hd c ρ p

/-! ### Punctured balls are path-connected (`d ≥ 2`) -/

/-- A punctured ball in `ℝ^d`, `d ≥ 2`, is path-connected: two of its points are joined by a
path inside it. -/
theorem joinedIn_ball_diff_singleton (hd : 2 ≤ d) (c p : Rd d) (ρ : ℝ) {x y : Rd d}
    (hx : x ∈ ball c ρ \ {p}) (hy : y ∈ ball c ρ \ {p}) : JoinedIn (ball c ρ \ {p}) x y := by
  by_cases hpxy : p ∈ segment ℝ x y
  · -- detour through a point `z` off the line through `x` and `y`
    have hρ : 0 < ρ := pos_of_mem_ball hx.1
    set V : Submodule ℝ (Rd d) := Submodule.span ℝ (range ![y - x]) with hV
    obtain ⟨z, hz, hzL⟩ := exists_mem_ball_notMem_of_null (c := c) hρ
      (volume_mk'_span_eq_zero (k := 1) (by omega) x ![y - x])
    have hzV : z - x ∉ V := fun h => hzL (AffineSubspace.mem_mk'.2 (by rwa [vsub_eq_sub]))
    have hyx : y - x ∈ V := Submodule.subset_span ⟨0, by simp⟩
    rw [segment_eq_image'] at hpxy
    obtain ⟨θ, -, hθ⟩ := hpxy
    have hpx : p - x ∈ V := by
      rw [← hθ, add_sub_cancel_left]
      exact V.smul_mem _ hyx
    have h1 : segment ℝ x z ⊆ ball c ρ \ {p} := by
      intro w hw
      refine ⟨(convex_ball c ρ).segment_subset hx.1 hz hw, ?_⟩
      rintro rfl
      rw [segment_eq_image'] at hw
      obtain ⟨a, -, ha⟩ := hw
      by_cases ha0 : a = 0
      · subst ha0
        apply hx.2
        rw [← ha]
        simp
      · apply hzV
        have : z - x = a⁻¹ • (w - x) := by
          rw [← ha, add_sub_cancel_left, inv_smul_smul₀ ha0]
        rw [this]
        exact V.smul_mem _ hpx
    have h2 : segment ℝ z y ⊆ ball c ρ \ {p} := by
      intro w hw
      refine ⟨(convex_ball c ρ).segment_subset hz hy.1 hw, ?_⟩
      rintro rfl
      rw [segment_eq_image'] at hw
      obtain ⟨a, -, ha⟩ := hw
      by_cases ha1 : a = 1
      · subst ha1
        apply hy.2
        rw [← ha]
        simp
      · apply hzV
        have ha1' : (1 - a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha1)
        have key : (1 - a) • (z - x) = (w - x) - a • (y - x) := by
          rw [← ha]
          module
        have : z - x = (1 - a)⁻¹ • ((w - x) - a • (y - x)) := by
          rw [← key, inv_smul_smul₀ ha1']
        rw [this]
        exact V.smul_mem _ (V.sub_mem hpx (V.smul_mem _ hyx))
    exact (JoinedIn.of_segment_subset h1).trans (JoinedIn.of_segment_subset h2)
  · exact JoinedIn.of_segment_subset fun w hw =>
      ⟨(convex_ball c ρ).segment_subset hx.1 hy.1 hw, fun h => hpxy (h ▸ hw)⟩

/-! ### NS-4: arcs have empty interior (`d ≥ 2`) -/

/-- **NS-4.** For `d ≥ 2`, an arc (injective continuous image of `[0,1]`) in `ℝ^d` contains no
ball of positive radius. -/
theorem not_ball_subset_range (hd : 2 ≤ d) (α : C(I, Rd d)) (hα : Function.Injective α)
    (c : Rd d) {r : ℝ} (hr : 0 < r) : ¬ ball c r ⊆ range α := by
  intro hsub
  -- two orthonormal vectors
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hon := b.orthonormal
  set u := b ⟨0, by omega⟩ with hu
  set v := b ⟨1, by omega⟩ with hv
  have hun : ‖u‖ = 1 := hon.1 _
  have hvn : ‖v‖ = 1 := hon.1 _
  have huv : ⟪u, v⟫ = 0 := hon.2 (by simp [Fin.ext_iff])
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hvn]; norm_num
  -- two paths from `c - (r/2) u` to `c + (r/2) u` on opposite sides of the hyperplane `v⊥`
  let w : I → ℝ := fun t => 1 - |2 * (t : ℝ) - 1|
  let sp : ℝ → I → Rd d := fun ε t => c + (r / 2) • ((2 * (t : ℝ) - 1) • u + (ε * w t) • v)
  have hw0 : ∀ t, 0 ≤ w t := by
    intro t
    have := t.2.1
    have := t.2.2
    simp only [w, sub_nonneg, abs_le]
    constructor <;> linarith
  have hspmem : ∀ ε : ℝ, |ε| ≤ 1 → ∀ t, sp ε t ∈ ball c r := by
    intro ε hε t
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    have h1 : ‖(2 * (t : ℝ) - 1) • u + (ε * w t) • v‖ ≤ 1 := by
      calc ‖(2 * (t : ℝ) - 1) • u + (ε * w t) • v‖
          ≤ ‖(2 * (t : ℝ) - 1) • u‖ + ‖(ε * w t) • v‖ := norm_add_le _ _
        _ = |2 * (t : ℝ) - 1| + |ε| * w t := by
          rw [norm_smul, norm_smul, hun, hvn, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (hw0 t)]
          ring
        _ ≤ |2 * (t : ℝ) - 1| + 1 * w t := by gcongr; exact hw0 t
        _ = 1 := by simp only [w]; ring
    nlinarith
  have hspcont : ∀ ε, Continuous (sp ε) := fun ε => by
    simp only [sp, w]
    fun_prop
  have hinner : ∀ ε t, ⟪sp ε t, v⟫ = ⟪c, v⟫ + (r / 2) * (ε * w t) := by
    intro ε t
    simp only [sp, inner_add_left, inner_smul_left, huv, hvv, RCLike.conj_to_real]
    ring
  have hsp0 : ∀ ε, sp ε 0 = c - (r / 2) • u := by
    intro ε
    simp only [sp, w, Set.Icc.coe_zero]
    norm_num
    module
  have hsp1 : ∀ ε, sp ε 1 = c + (r / 2) • u := by
    intro ε
    simp only [sp, w, Set.Icc.coe_one]
    norm_num
  -- the inverse of the arc, along the two paths
  let e := (α.continuous.isClosedEmbedding hα).isEmbedding.toHomeomorph
  let g : ∀ ε : ℝ, |ε| ≤ 1 → I → ℝ :=
    fun ε hε t => (e.symm ⟨sp ε t, hsub (hspmem ε hε t)⟩ : ℝ)
  have hgcont : ∀ ε hε, Continuous (g ε hε) := fun ε hε =>
    continuous_subtype_val.comp (e.symm.continuous.comp
      ((hspcont ε).subtype_mk fun t => hsub (hspmem ε hε t)))
  have hginj : ∀ ε hε ε' hε' t t', g ε hε t = g ε' hε' t' → sp ε t = sp ε' t' := by
    intro ε hε ε' hε' t t' h
    have h1 := e.symm.injective (Subtype.ext h)
    exact congrArg Subtype.val h1
  have hgcongr : ∀ ε hε ε' hε' t t', sp ε t = sp ε' t' → g ε hε t = g ε' hε' t' := by
    intro ε hε ε' hε' t t' h
    simp only [g, h]
  have h1abs : |(1 : ℝ)| ≤ 1 := by norm_num
  have hm1abs : |(-1 : ℝ)| ≤ 1 := by norm_num
  set A := g 1 h1abs 0 with hA
  set B := g 1 h1abs 1 with hB
  have hAB : A ≠ B := by
    intro h
    have h2 := hginj 1 h1abs 1 h1abs 0 1 h
    rw [hsp0, hsp1] at h2
    have h3 : ‖(c + (r / 2) • u) - (c - (r / 2) • u)‖ = r := by
      rw [show (c + (r / 2) • u) - (c - (r / 2) • u) = r • u by module, norm_smul, hun,
        Real.norm_eq_abs, abs_of_pos hr, mul_one]
    rw [← h2, sub_self, norm_zero] at h3
    exact hr.ne h3
  have hA' : ∀ ε hε, g ε hε 0 = A := fun ε hε =>
    hgcongr ε hε 1 h1abs 0 0 ((hsp0 ε).trans (hsp0 1).symm)
  have hB' : ∀ ε hε, g ε hε 1 = B := fun ε hε =>
    hgcongr ε hε 1 h1abs 1 1 ((hsp1 ε).trans (hsp1 1).symm)
  -- by the intermediate value theorem each path hits the mean value `m`
  set m := (A + B) / 2 with hm
  have hmA : m ≠ A := by intro h; apply hAB; linarith
  have hmB : m ≠ B := by intro h; apply hAB; linarith
  have hivt : ∀ ε hε, ∃ t, g ε hε t = m := by
    intro ε hε
    have hmem : m ∈ range (g ε hε) := by
      rcases le_total A B with h | h
      · exact mem_range_of_exists_le_of_exists_ge (hgcont ε hε)
          ⟨0, by rw [hA' ε hε]; linarith⟩ ⟨1, by rw [hB' ε hε]; linarith⟩
      · exact mem_range_of_exists_le_of_exists_ge (hgcont ε hε)
          ⟨1, by rw [hB' ε hε]; linarith⟩ ⟨0, by rw [hA' ε hε]; linarith⟩
    exact hmem
  have hwpos : ∀ ε hε t, g ε hε t = m → 0 < w t := by
    intro ε hε t ht
    have ht0 : t ≠ 0 := by rintro rfl; exact hmA (ht.symm.trans (hA' ε hε))
    have ht1 : t ≠ 1 := by rintro rfl; exact hmB (ht.symm.trans (hB' ε hε))
    have h0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (fun h => ht0 (Subtype.ext h.symm))
    have h1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun h => ht1 (Subtype.ext h))
    simp only [w, sub_pos, abs_lt]
    constructor <;> linarith
  obtain ⟨t₁, ht₁⟩ := hivt 1 h1abs
  obtain ⟨t₂, ht₂⟩ := hivt (-1) hm1abs
  have heq := hginj 1 h1abs (-1) hm1abs t₁ t₂ (ht₁.trans ht₂.symm)
  have h1 := hinner 1 t₁
  have h2 := hinner (-1) t₂
  rw [heq] at h1
  have hw1 := hwpos 1 h1abs t₁ ht₁
  have hw2 := hwpos (-1) hm1abs t₂ ht₂
  nlinarith

/-- Consequence of NS-4: a nonempty open set is not covered by an arc (`d ≥ 2`). -/
theorem nonempty_diff_range (hd : 2 ≤ d) (α : C(I, Rd d)) (hα : Function.Injective α)
    {U : Set (Rd d)} (hU : IsOpen U) (hne : U.Nonempty) : (U \ range α).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  by_contra h
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
  exact not_ball_subset_range hd α hα x hr (hrU.trans h)

/-- Consequence of NS-4: a nonempty open set is not covered by the union of two arcs
(`d ≥ 2`). -/
theorem nonempty_diff_range_union (hd : 2 ≤ d) (α β : C(I, Rd d)) (hα : Function.Injective α)
    (hβ : Function.Injective β) {U : Set (Rd d)} (hU : IsOpen U) (hne : U.Nonempty) :
    (U \ (range α ∪ range β)).Nonempty := by
  have hβc : IsClosed (range β) := (isCompact_range β.continuous).isClosed
  obtain ⟨x, hx⟩ := nonempty_diff_range hd β hβ hU hne
  obtain ⟨y, hy⟩ := nonempty_diff_range hd α hα (hU.sdiff hβc) ⟨x, hx⟩
  exact ⟨y, hy.1.1, fun h => h.elim hy.2 hy.1.2⟩

end HigherDimLQGMetric.Topology

end
