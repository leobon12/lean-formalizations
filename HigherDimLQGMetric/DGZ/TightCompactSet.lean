import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Compact sets of pseudo-metrics with local Hölder bounds (packet L5a, DGZ Prop 6.3)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Prop 6.3 (TeX l. 2910–2916, p. 57);
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, D-6.1–6.3 ("the modulus condition …
tightness on `C(ℝ^d×ℝ^d, ℝ)` by the local criterion"); blueprint Part C, Prop `r2:prop:63`.

For a metric space `X` with an increasing sequence of sets `K j` such that every point has a
neighbourhood inside some `K j`, constants `M j ≥ 0` and `β > 0`, the set
`holderMetricSet K M β` of functions `g : X × X → ℝ` with `g(x, x) = 0`, the triangle inequality and
`g(x, y) ≤ M j dist(x, y)^β` on `K j × K j` consists of continuous functions, and the corresponding
set of `C(X × X, ℝ)` is compact for the compact-open topology (`isCompact_holderMetricSet`,
Arzelà–Ascoli: Mathlib `ArzelaAscoli.isCompact_of_equicontinuous`). This is the local version of
`LQGMetric.LFPP.isTightMeasureSet_of_modulus` (which needs a compact connected `X`) and replaces the
port of `DFGPS.isTightMeasureSet_of_restrN`: the local Hölder bounds give pointwise bounds directly,
so neither compactness nor connectedness of `X` is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set Metric

namespace HigherDimLQGMetric

namespace DGZ

variable {X : Type*} [MetricSpace X]

/-- Functions on `X × X` vanishing on the diagonal, with the triangle inequality and the local
Hölder bounds `g(x, y) ≤ M j dist(x, y)^β` on `K j × K j`. -/
def holderMetricSet (K : ℕ → Set X) (M : ℕ → ℝ) (β : ℝ) : Set (X × X → ℝ) :=
  {g | (∀ x, g (x, x) = 0) ∧ (∀ x y z, g (x, z) ≤ g (x, y) + g (y, z)) ∧
    ∀ j, ∀ x ∈ K j, ∀ y ∈ K j, g (x, y) ≤ M j * dist x y ^ β}

variable {K : ℕ → Set X} {M : ℕ → ℝ} {β : ℝ}

/-- The local modulus: `|g(x, y) - g(x₀, y₀)| ≤ M j dist(x, x₀)^β + M j dist(y, y₀)^β` on `K j`. -/
lemma holderMetricSet_abs_sub_le {g : X × X → ℝ} (hg : g ∈ holderMetricSet K M β) {j : ℕ}
    {x x₀ y y₀ : X} (hx : x ∈ K j) (hx₀ : x₀ ∈ K j) (hy : y ∈ K j) (hy₀ : y₀ ∈ K j) :
    |g (x, y) - g (x₀, y₀)| ≤ M j * dist x x₀ ^ β + M j * dist y y₀ ^ β := by
  obtain ⟨-, htri, hhol⟩ := hg
  have a1 := hhol j x hx x₀ hx₀
  have a2 := hhol j x₀ hx₀ x hx
  have a3 := hhol j y hy y₀ hy₀
  have a4 := hhol j y₀ hy₀ y hy
  have t1 := htri x x₀ y
  have t2 := htri x₀ y₀ y
  have t3 := htri x₀ x y₀
  have t4 := htri x y y₀
  rw [dist_comm x₀ x] at a2
  rw [dist_comm y₀ y] at a4
  rw [abs_le]
  constructor <;> linarith

/-- The pointwise bound: `|g(x, y)| ≤ M j dist(x, y)^β` on `K j`. -/
lemma holderMetricSet_abs_le {g : X × X → ℝ} (hg : g ∈ holderMetricSet K M β) {j : ℕ}
    {x y : X} (hx : x ∈ K j) (hy : y ∈ K j) : |g (x, y)| ≤ M j * dist x y ^ β := by
  obtain ⟨hdiag, htri, hhol⟩ := hg
  have a1 := hhol j x hx y hy
  have a2 := hhol j y hy x hx
  have t1 := htri x y x
  rw [hdiag x, dist_comm y x] at *
  rw [abs_le]
  constructor <;> linarith

/-- The set `holderMetricSet K M β` is closed in the product topology. -/
lemma isClosed_holderMetricSet (K : ℕ → Set X) (M : ℕ → ℝ) (β : ℝ) :
    IsClosed (holderMetricSet K M β) := by
  have e : holderMetricSet K M β = (⋂ x, {g : X × X → ℝ | g (x, x) = 0}) ∩
      ((⋂ x, ⋂ y, ⋂ z, {g : X × X → ℝ | g (x, z) ≤ g (x, y) + g (y, z)}) ∩
        ⋂ j, ⋂ x, ⋂ y, {g : X × X → ℝ | x ∈ K j → y ∈ K j → g (x, y) ≤ M j * dist x y ^ β}) := by
    ext g
    simp only [holderMetricSet, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun j x y hx hy => h3 j x hx y hy⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun j x hx y hy => h3 j x y hx hy⟩
  rw [e]
  refine (isClosed_iInter fun x => isClosed_eq (f := fun g : X × X → ℝ => g (x, x))
      (continuous_apply _) continuous_const).inter
    ((isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
      isClosed_le (f := fun g : X × X → ℝ => g (x, z)) (g := fun g => g (x, y) + g (y, z))
        (continuous_apply _) ((continuous_apply _).add (continuous_apply _))).inter
    (isClosed_iInter fun j => isClosed_iInter fun x => isClosed_iInter fun y => ?_))
  by_cases hx : x ∈ K j
  · by_cases hy : y ∈ K j
    · simp only [hx, hy, true_imp_iff]
      exact isClosed_le (f := fun g : X × X → ℝ => g (x, y)) (continuous_apply _)
        continuous_const
    · simp only [hy, false_imp_iff, imp_true_iff, ofPred_true]
      exact isClosed_univ
  · simp only [hx, false_imp_iff, ofPred_true]
    exact isClosed_univ

/-- **Uniform local modulus**: at every point `p₀`, for every `ε > 0`, eventually in `p`,
`dist (g p₀) (g p) < ε` for all `g ∈ holderMetricSet K M β` simultaneously. -/
lemma holderMetricSet_eventually (hKmono : Monotone K) (hKnhds : ∀ x, ∃ j, K j ∈ 𝓝 x)
    (hβ : 0 < β) (hM : ∀ j, 0 ≤ M j) (p₀ : X × X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in 𝓝 p₀, ∀ g ∈ holderMetricSet K M β, dist (g p₀) (g p) < ε := by
  obtain ⟨jx, hjx⟩ := hKnhds p₀.1
  obtain ⟨jy, hjy⟩ := hKnhds p₀.2
  set j := max jx jy with hj
  have hKx : K j ∈ 𝓝 p₀.1 := mem_of_superset hjx (hKmono (le_max_left _ _))
  have hKy : K j ∈ 𝓝 p₀.2 := mem_of_superset hjy (hKmono (le_max_right _ _))
  set δ : ℝ := (ε / (2 * (M j + 1))) ^ β⁻¹ with hδ
  have hMj := hM j
  have hδ0 : 0 < δ := by positivity
  have hδβ : δ ^ β = ε / (2 * (M j + 1)) := Real.rpow_inv_rpow (by positivity) hβ.ne'
  have hN : (K j ∩ ball p₀.1 δ) ×ˢ (K j ∩ ball p₀.2 δ) ∈ 𝓝 p₀ :=
    prod_mem_nhds (inter_mem hKx (ball_mem_nhds _ hδ0)) (inter_mem hKy (ball_mem_nhds _ hδ0))
  filter_upwards [hN] with p hp g hg
  obtain ⟨⟨hpx, hpx'⟩, ⟨hpy, hpy'⟩⟩ := hp
  have hx₀ := mem_of_mem_nhds hKx
  have hy₀ := mem_of_mem_nhds hKy
  have h1 := holderMetricSet_abs_sub_le hg hpx hx₀ hpy hy₀
  have h2 : dist p.1 p₀.1 ^ β ≤ δ ^ β :=
    Real.rpow_le_rpow dist_nonneg (le_of_lt (mem_ball.1 hpx')) hβ.le
  have h3 : dist p.2 p₀.2 ^ β ≤ δ ^ β :=
    Real.rpow_le_rpow dist_nonneg (le_of_lt (mem_ball.1 hpy')) hβ.le
  rw [Real.dist_eq, abs_sub_comm]
  calc |g (p.1, p.2) - g (p₀.1, p₀.2)| ≤ M j * dist p.1 p₀.1 ^ β + M j * dist p.2 p₀.2 ^ β := h1
    _ ≤ M j * δ ^ β + M j * δ ^ β := by gcongr
    _ = M j / (M j + 1) * ε := by rw [hδβ]; field_simp; ring
    _ < ε := by
        have : M j / (M j + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        nlinarith

/-- Every function of `holderMetricSet K M β` is continuous. -/
lemma continuous_of_mem_holderMetricSet (hKmono : Monotone K) (hKnhds : ∀ x, ∃ j, K j ∈ 𝓝 x)
    (hβ : 0 < β) (hM : ∀ j, 0 ≤ M j) {g : X × X → ℝ} (hg : g ∈ holderMetricSet K M β) :
    Continuous g := by
  refine continuous_iff_continuousAt.2 fun p₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [holderMetricSet_eventually hKmono hKnhds hβ hM p₀ hε] with p hp
  rw [dist_comm]
  exact hp g hg

/-- **Compactness (Arzelà–Ascoli)**: the continuous maps in `holderMetricSet K M β` form a compact
subset of `C(X × X, ℝ)`. -/
theorem isCompact_holderMetricSet (hKmono : Monotone K) (hKnhds : ∀ x, ∃ j, K j ∈ 𝓝 x)
    (hβ : 0 < β) (hM : ∀ j, 0 ≤ M j) :
    IsCompact {f : C(X × X, ℝ) | ⇑f ∈ holderMetricSet K M β} := by
  set S := {f : C(X × X, ℝ) | ⇑f ∈ holderMetricSet K M β} with hS
  have himg : ContinuousMap.toFun '' S = holderMetricSet K M β := by
    ext g
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro hg
      exact ⟨⟨g, continuous_of_mem_holderMetricSet hKmono hKnhds hβ hM hg⟩, hg, rfl⟩
  choose j₀ hj₀ using hKnhds
  set b : X × X → ℝ := fun p => M (max (j₀ p.1) (j₀ p.2)) * dist p.1 p.2 ^ β with hb
  have hsub : holderMetricSet K M β ⊆ Set.pi univ fun p => Icc (-b p) (b p) := by
    intro g hg p _
    have hx : p.1 ∈ K (max (j₀ p.1) (j₀ p.2)) :=
      hKmono (le_max_left _ _) (mem_of_mem_nhds (hj₀ p.1))
    have hy : p.2 ∈ K (max (j₀ p.1) (j₀ p.2)) :=
      hKmono (le_max_right _ _) (mem_of_mem_nhds (hj₀ p.2))
    exact abs_le.1 (holderMetricSet_abs_le hg hx hy)
  have hcpt : IsCompact (holderMetricSet K M β) :=
    (isCompact_univ_pi fun p => isCompact_Icc).of_isClosed_subset
      (isClosed_holderMetricSet K M β) hsub
  refine ArzelaAscoli.isCompact_of_equicontinuous S (himg ▸ hcpt) ?_
  intro p₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  filter_upwards [holderMetricSet_eventually hKmono (fun x => ⟨j₀ x, hj₀ x⟩) hβ hM p₀ hε]
    with p hp f
  exact hp f f.2

end DGZ

end HigherDimLQGMetric
