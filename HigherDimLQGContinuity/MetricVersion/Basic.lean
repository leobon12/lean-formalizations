import HigherDimLQGContinuity.Core.Interfaces
import LQGMetric.Metric.Midpoint
import Mathlib.Topology.Order.Compact

/-!
# Metric-valued versions (packet E5): deterministic tools

Part C, Section `c:sec-optional` (blueprint `blueprint/sections/c3-median.tex`), the metric-valued strengthening of
[C] §§5.3–5.4 (rulings N11, N20). This file collects the deterministic tools used by the whole packet:

* `mvInf K F = inf_{p ∈ K} F p` for `F ∈ C(ℝ^d × ℝ^d, ℝ)` (Part C's `F(A, B)` for `K = A × B`): continuity in `F` for
  compact `K` (`continuous_mvInf`), attainment, and the order characterizations;
* closed conditions pass from the rational points of a parameter set to all of it (`mv_mem_of_dense`,
  `mv_mem_of_rat`, `mv_mem_of_rat_Icc`): this is how every identity or inequality proved at deterministic rational
  parameters is extended to the whole positive subcritical set along an a.s. continuous family;
* the first-exit inequality for length metrics (`mv_exists_exit`, `mvInf_exit_le`): a path from a point inside a
  Euclidean sphere to a point outside an outer sphere crosses both spheres, in this order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ## Infima over compact sets -/

/-- `F(K) = inf_{p ∈ K} F(p)` for `F ∈ C(ℝ^d × ℝ^d, ℝ)` (Part C, `c:sec-optional`: `F(A, B)` for `K = A × B`). -/
def mvInf (K : Set (Rd d × Rd d)) (F : C(Rd d × Rd d, ℝ)) : ℝ :=
  sInf ((⇑F) '' K)

/-- For compact `K`, `F ↦ F(K)` is continuous on `C(ℝ^d × ℝ^d, ℝ)` (compact-open topology). -/
theorem continuous_mvInf {K : Set (Rd d × Rd d)} (hK : IsCompact K) : Continuous (mvInf K) :=
  hK.continuous_sInf (f := fun (F : C(Rd d × Rd d, ℝ)) (p : Rd d × Rd d) => F p) continuous_eval

theorem measurable_mvInf {K : Set (Rd d × Rd d)} (hK : IsCompact K) : Measurable (mvInf K) :=
  (continuous_mvInf hK).measurable

theorem mvInf_le {K : Set (Rd d × Rd d)} (hK : IsCompact K) (F : C(Rd d × Rd d, ℝ)) {p : Rd d × Rd d}
    (hp : p ∈ K) : mvInf K F ≤ F p :=
  csInf_le (hK.bddBelow_image F.continuous.continuousOn) (mem_image_of_mem F hp)

/-- For nonnegative `F` no compactness is needed. -/
theorem mvInf_le_of_nonneg {K : Set (Rd d × Rd d)} {F : C(Rd d × Rd d, ℝ)} (hF : ∀ p, 0 ≤ F p)
    {p : Rd d × Rd d} (hp : p ∈ K) : mvInf K F ≤ F p :=
  csInf_le ⟨0, by rintro _ ⟨q, -, rfl⟩; exact hF q⟩ (mem_image_of_mem F hp)

/-- On a nonempty compact set the infimum is attained. -/
theorem exists_eq_mvInf {K : Set (Rd d × Rd d)} (hK : IsCompact K) (hne : K.Nonempty)
    (F : C(Rd d × Rd d, ℝ)) : ∃ p ∈ K, F p = mvInf K F := by
  obtain ⟨p, hp, hpe⟩ := (hK.image F.continuous).sInf_mem (hne.image F)
  exact ⟨p, hp, hpe⟩

theorem mvInf_le_iff {K : Set (Rd d × Rd d)} (hK : IsCompact K) (hne : K.Nonempty)
    (F : C(Rd d × Rd d, ℝ)) (c : ℝ) : mvInf K F ≤ c ↔ ∃ p ∈ K, F p ≤ c := by
  constructor
  · intro h
    obtain ⟨p, hp, hpe⟩ := exists_eq_mvInf hK hne F
    exact ⟨p, hp, hpe ▸ h⟩
  · rintro ⟨p, hp, hpc⟩
    exact (mvInf_le hK F hp).trans hpc

theorem lt_mvInf_iff {K : Set (Rd d × Rd d)} (hK : IsCompact K) (hne : K.Nonempty)
    (F : C(Rd d × Rd d, ℝ)) (c : ℝ) : c < mvInf K F ↔ ∀ p ∈ K, c < F p := by
  rw [← not_le, mvInf_le_iff hK hne]
  push Not
  rfl

theorem le_mvInf_iff {K : Set (Rd d × Rd d)} (hK : IsCompact K) (hne : K.Nonempty)
    (F : C(Rd d × Rd d, ℝ)) (c : ℝ) : c ≤ mvInf K F ↔ ∀ p ∈ K, c ≤ F p := by
  constructor
  · intro h p hp
    exact h.trans (mvInf_le hK F hp)
  · intro h
    exact le_csInf (hne.image F) (by rintro _ ⟨p, hp, rfl⟩; exact h p hp)

/-! ## Closed conditions at rational parameters -/

/-- A closed condition on a function continuous on `s` that holds on a subset `t` with `s ⊆ closure t` holds on
`s`. -/
theorem mv_mem_of_dense {Y : Type*} [TopologicalSpace Y] {s t : Set ℝ} {f : ℝ → Y} (hf : ContinuousOn f s)
    (hts : t ⊆ s) (hst : s ⊆ closure t) {C : Set Y} (hC : IsClosed C) (h : ∀ x ∈ t, f x ∈ C) :
    ∀ x ∈ s, f x ∈ C := by
  intro x hx
  have h1 : f x ∈ closure (f '' t) := ((hf x hx).mono hts).mem_closure_image (hst hx)
  exact closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact h y hy) hC h1

theorem mv_subset_closure_rat {U : Set ℝ} (hU : IsOpen U) : U ⊆ closure (U ∩ range ((↑) : ℚ → ℝ)) :=
  Rat.denseRange_cast.open_subset_closure_inter hU

theorem mv_Icc_subset_closure_rat {c c' : ℝ} (hcc : c < c') :
    Icc c c' ⊆ closure (Icc c c' ∩ range ((↑) : ℚ → ℝ)) := by
  have h1 : Ioo c c' ⊆ closure (Ioo c c' ∩ range ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
  have h2 : closure (Ioo c c') ⊆ closure (Icc c c' ∩ range ((↑) : ℚ → ℝ)) :=
    closure_minimal (h1.trans (closure_mono (inter_subset_inter_left _ Ioo_subset_Icc_self)))
      isClosed_closure
  rwa [closure_Ioo hcc.ne] at h2

/-- A closed condition holding at the rational points of an open set holds on the whole set. -/
theorem mv_mem_of_rat {Y : Type*} [TopologicalSpace Y] {U : Set ℝ} (hU : IsOpen U) {f : ℝ → Y}
    (hf : ContinuousOn f U) {C : Set Y} (hC : IsClosed C) (h : ∀ q : ℚ, (q : ℝ) ∈ U → f q ∈ C) :
    ∀ x ∈ U, f x ∈ C :=
  mv_mem_of_dense hf inter_subset_left (mv_subset_closure_rat hU) hC
    (by rintro _ ⟨hxU, q, rfl⟩; exact h q hxU)

/-- A closed condition holding at the rational points of a nondegenerate closed interval holds on it. -/
theorem mv_mem_of_rat_Icc {Y : Type*} [TopologicalSpace Y] {c c' : ℝ} (hcc : c < c') {f : ℝ → Y}
    (hf : ContinuousOn f (Icc c c')) {C : Set Y} (hC : IsClosed C)
    (h : ∀ q : ℚ, (q : ℝ) ∈ Icc c c' → f q ∈ C) : ∀ x ∈ Icc c c', f x ∈ C :=
  mv_mem_of_dense hf inter_subset_left (mv_Icc_subset_closure_rat hcc) hC
    (by rintro _ ⟨hxJ, q, rfl⟩; exact h q hxJ)

/-- The real-valued form: an inequality between functions continuous on an open set that holds at its rational
points holds everywhere on it. -/
theorem mv_le_of_rat {U : Set ℝ} (hU : IsOpen U) {φ ψ : ℝ → ℝ} (hφ : ContinuousOn φ U) (hψ : ContinuousOn ψ U)
    (h : ∀ q : ℚ, (q : ℝ) ∈ U → φ q ≤ ψ q) : ∀ x ∈ U, φ x ≤ ψ x :=
  mv_mem_of_rat (f := fun x => (φ x, ψ x)) hU (hφ.prodMk hψ) (isClosed_le continuous_fst continuous_snd) h

/-! ## First exit in a length metric -/

/-- **First exit.** In a length metric `G`, if `N(x) ≤ a ≤ b ≤ N(y)` for a continuous `N`, then for every `ε > 0` some
`u, w` with `N(u) = a`, `N(w) = b` have `G(u, w) ≤ G(x, y) + ε` (cut a near-geodesic path at a crossing of
`{N = b}` and at an earlier crossing of `{N = a}`). -/
theorem mv_exists_exit {G : ContMetric d} (hG : G.IsLength) {N : Rd d → ℝ} (hN : Continuous N)
    {x y : Rd d} {a b : ℝ} (hxa : N x ≤ a) (hab : a ≤ b) (hby : b ≤ N y) {ε : ℝ} (hε : 0 < ε) :
    ∃ u w : Rd d, N u = a ∧ N w = b ∧ G.1 (u, w) ≤ G.1 (x, y) + ε := by
  obtain ⟨γ, hγ⟩ := hG (G.pt x) (G.pt y) ε hε
  set φ : ℝ → ℝ := fun t => N (G.unpt (γ.extend t)) with hφ
  have hφc : Continuous φ := hN.comp (G.continuous_unpt.comp γ.continuous_extend)
  have h0 : φ 0 = N x := by simp only [hφ, Path.extend_zero, ContMetric.unpt_pt]
  have h1 : φ 1 = N y := by simp only [hφ, Path.extend_one, ContMetric.unpt_pt]
  obtain ⟨t₂, ht₂, hφt₂⟩ := intermediate_value_Icc (zero_le_one' ℝ) hφc.continuousOn
    (show b ∈ Icc (φ 0) (φ 1) from ⟨h0 ▸ hxa.trans hab, h1 ▸ hby⟩)
  obtain ⟨t₁, ht₁, hφt₁⟩ := intermediate_value_Icc ht₂.1 hφc.continuousOn
    (show a ∈ Icc (φ 0) (φ t₂) from ⟨h0 ▸ hxa, hφt₂ ▸ hab⟩)
  refine ⟨G.unpt (γ.extend t₁), G.unpt (γ.extend t₂), hφt₁, hφt₂, ?_⟩
  have hle : edist (γ.extend t₁) (γ.extend t₂) ≤ pathLength γ :=
    (edist_le_curveLength γ.extend ht₁.2).trans (curveLength_mono γ.extend ht₁.1 ht₂.2)
  have hxy : edist (G.pt x) (G.pt y) = ENNReal.ofReal (G.1 (x, y)) := G.edist_pt x y
  have huw : edist (γ.extend t₁) (γ.extend t₂) =
      ENNReal.ofReal (G.1 (G.unpt (γ.extend t₁), G.unpt (γ.extend t₂))) :=
    G.edist_pt (G.unpt (γ.extend t₁)) (G.unpt (γ.extend t₂))
  have hfin : ENNReal.ofReal (G.1 (G.unpt (γ.extend t₁), G.unpt (γ.extend t₂))) ≤
      ENNReal.ofReal (G.1 (x, y) + ε) := by
    rw [← huw, ENNReal.ofReal_add (G.nonneg x y) hε.le, ← hxy]
    exact hle.trans hγ
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (G.nonneg x y) hε.le)).1 hfin

/-- **First exit, infimum form**: `G({N = a} × {N = b}) ≤ G(x, y)` for a length metric `G` and `N(x) ≤ a ≤ b ≤ N(y)`. -/
theorem mvInf_exit_le {G : ContMetric d} (hG : G.IsLength) {N : Rd d → ℝ} (hN : Continuous N)
    {x y : Rd d} {a b : ℝ} (hxa : N x ≤ a) (hab : a ≤ b) (hby : b ≤ N y) :
    mvInf ({u | N u = a} ×ˢ {w | N w = b}) G.1 ≤ G.1 (x, y) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨u, w, hu, hw, hle⟩ := mv_exists_exit hG hN hxa hab hby hε
  have hmem : (u, w) ∈ {u | N u = a} ×ˢ {w | N w = b} := ⟨hu, hw⟩
  exact (mvInf_le_of_nonneg (fun p => G.nonneg p.1 p.2) hmem).trans hle

/-- The sphere form of the first exit (centre `c`, radii `a ≤ b`). -/
theorem mvInf_sphere_exit_le {G : ContMetric d} (hG : G.IsLength) (c x y : Rd d) {a b : ℝ}
    (hxa : dist x c ≤ a) (hab : a ≤ b) (hby : b ≤ dist y c) :
    mvInf (sphere c a ×ˢ sphere c b) G.1 ≤ G.1 (x, y) :=
  mvInf_exit_le (N := fun z => dist z c) hG (continuous_id.dist continuous_const) hxa hab hby

end HigherDimLQGContinuity
