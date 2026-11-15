/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS3ProofReachOpen
import InteractingSLE.Foundations.Measure.Tightness
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# DS2 in reach form, I: tools on the path space `C([0, T], X)`

Packet PROVE-T14-DS (Lemma DS2, spec p. 553, reach form `DSReach.DS2ReachStatement`). The proof of DS2 in this
project replaces the source's limiting martingale problem by **pathwise uniqueness** (the route recommended in
`planning/handoffs/PROVE-T14-TIP7.md` §5.2): the laws of the stopped state paths and of the driving Brownian paths
are tight; any subsequential weak limit satisfies the limiting integrated equations before the buffer exit; and a
conditionally independent coupling of two such limits over the same Brownian path, together with deterministic
uniqueness of solutions driven by one path (`Sec2.UpTo.agree_of_lt_min`), shows that the limit gives the reach
event the probability of the limiting word.

This file collects the measure-theoretic and topological tools on the path space `C([0, T], X)` (`[0, T] ⊆ ℝ≥0`,
uniform topology), used by the later files:

* `PathMeas`: the Borel σ-algebra on `C([0, T], X)` (scoped instances);
* `measurable_to_pathSpace`: a map into `C([0, T], X)` is measurable when every evaluation is;
* `pathAt`: the path extended constantly to `ℝ≥0`, and joint continuity of `(f, t) ↦ f(t)`;
* `isOpen_setOf_forall_le_mem`: the paths staying in an open set up to time `t` form an open set;
* `measure_le_of_tendsto_of_isOpen`: Portmanteau for open sets with an eventual upper bound;
* `isCompact_modulusSet`: Arzelà–Ascoli for a closed set of paths with a uniform modulus and a uniform bound;
* `exists_glue`: a conditionally independent coupling of two laws with the same marginal on a common coordinate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped NNReal ENNReal BoundedContinuousFunction

namespace InteractingSLE

namespace Supp12

namespace DSReach

/-! ### The Borel σ-algebra on the path space -/

namespace PathMeas

/-- The Borel σ-algebra on `C([0, T], X)` (uniform topology). -/
scoped instance instMeasurableSpace {X : Type*} [TopologicalSpace X] (T : ℝ≥0) :
    MeasurableSpace C(Set.Icc (0 : ℝ≥0) T, X) :=
  borel _

scoped instance instBorelSpace {X : Type*} [TopologicalSpace X] (T : ℝ≥0) :
    BorelSpace C(Set.Icc (0 : ℝ≥0) T, X) :=
  ⟨rfl⟩

end PathMeas

open scoped PathMeas

section Measurability

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {T : ℝ≥0}

/-- **A map into the path space is measurable when every evaluation is.** -/
theorem measurable_to_pathSpace {Ω : Type*} [MeasurableSpace Ω] (Φ : Ω → C(Set.Icc (0 : ℝ≥0) T, X))
    (hΦ : ∀ x, Measurable fun ω => Φ ω x) : Measurable Φ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ≥0) T)
  have hcb : ∀ (g : C(Set.Icc (0 : ℝ≥0) T, X)) (c : ℝ), 0 ≤ c →
      {ω | dist (Φ ω) g ≤ c} = ⋂ x ∈ D, {ω | dist (Φ ω x) (g x) ≤ c} := by
    intro g c hc
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h x _
      exact (ContinuousMap.dist_apply_le_dist x).trans h
    · intro h
      rw [ContinuousMap.dist_le hc]
      have hcl : IsClosed {x | dist (Φ ω x) (g x) ≤ c} :=
        isClosed_le ((Φ ω).continuous.dist g.continuous) continuous_const
      have hD : D ⊆ {x | dist (Φ ω x) (g x) ≤ c} := fun x hx => h x hx
      intro x
      exact (hcl.closure_subset_iff.mpr hD) (by rw [hDd.closure_eq]; exact mem_univ x)
  have hmcb : ∀ g c, MeasurableSet {ω | dist (Φ ω) g ≤ c} := by
    intro g c
    rcases lt_or_ge c 0 with hc | hc
    · have : {ω | dist (Φ ω) g ≤ c} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
        exact hc.trans_le dist_nonneg
      rw [this]
      exact MeasurableSet.empty
    · rw [hcb g c hc]
      exact MeasurableSet.biInter hDc
        (fun x _ => measurableSet_le ((hΦ x).dist measurable_const) measurable_const)
  have hmb : ∀ g r, MeasurableSet (Φ ⁻¹' Metric.ball g r) := by
    intro g r
    have : Φ ⁻¹' Metric.ball g r = ⋃ n : ℕ, {ω | dist (Φ ω) g ≤ r - 1 / ((n : ℝ) + 1)} := by
      ext ω
      simp only [mem_preimage, Metric.mem_ball, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [this]
    exact MeasurableSet.iUnion fun n => hmcb g _
  refine measurable_of_isOpen fun U hU => ?_
  have hr : ∀ g : U, ∃ r > 0, Metric.ball (g : C(Set.Icc (0 : ℝ≥0) T, X)) r ⊆ U :=
    fun g => Metric.isOpen_iff.mp hU g g.2
  choose r hr0 hrU using hr
  obtain ⟨S, hSc, hSeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun g : U => Metric.ball (g : C(Set.Icc (0 : ℝ≥0) T, X)) (r g)) (fun _ => Metric.isOpen_ball)
  have hUeq : U = ⋃ g ∈ S, Metric.ball (g : C(Set.Icc (0 : ℝ≥0) T, X)) (r g) := by
    rw [hSeq]
    apply Subset.antisymm
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr0 _)⟩
    · exact iUnion_subset fun g => hrU g
  rw [hUeq, preimage_iUnion₂]
  exact MeasurableSet.biUnion hSc fun g _ => hmb _ _

omit [SecondCountableTopology X] in
/-- Evaluation at a time is measurable on the path space. -/
theorem measurable_eval_path (x : Set.Icc (0 : ℝ≥0) T) :
    Measurable fun f : C(Set.Icc (0 : ℝ≥0) T, X) => f x :=
  (continuous_eval_const x).measurable

end Measurability

/-! ### Paths extended to `ℝ≥0` -/

section PathAt

variable {X : Type*} [TopologicalSpace X] {T : ℝ≥0}

/-- The path `f` on `[0, T]` extended constantly to `ℝ≥0` (the value at `min t T`). -/
def pathAt (f : C(Set.Icc (0 : ℝ≥0) T, X)) (t : ℝ≥0) : X :=
  f (Set.projIcc 0 T (zero_le : (0 : ℝ≥0) ≤ T) t)

theorem pathAt_of_le (f : C(Set.Icc (0 : ℝ≥0) T, X)) {t : ℝ≥0} (ht : t ≤ T) :
    pathAt f t = f ⟨t, zero_le, ht⟩ := by
  unfold pathAt
  rw [Set.projIcc_of_mem _ ⟨zero_le, ht⟩]

theorem pathAt_coe (f : C(Set.Icc (0 : ℝ≥0) T, X)) (t : Set.Icc (0 : ℝ≥0) T) :
    pathAt f t = f t := by
  rw [pathAt_of_le f t.2.2]

/-- `(f, t) ↦ f(t)` is jointly continuous. -/
theorem continuous_pathAt_uncurry :
    Continuous fun p : C(Set.Icc (0 : ℝ≥0) T, X) × ℝ≥0 => pathAt p.1 p.2 :=
  continuous_eval.comp (continuous_fst.prodMk
    ((continuous_projIcc (h := (zero_le : (0 : ℝ≥0) ≤ T))).comp continuous_snd))

theorem continuous_pathAt (f : C(Set.Icc (0 : ℝ≥0) T, X)) : Continuous (pathAt f) :=
  f.continuous.comp continuous_projIcc

theorem continuous_pathAt_const (t : ℝ≥0) :
    Continuous fun f : C(Set.Icc (0 : ℝ≥0) T, X) => pathAt f t :=
  continuous_eval_const _

end PathAt

/-! ### Open sets of paths -/

section OpenSets

variable {X : Type*} [MetricSpace X] {T : ℝ≥0}

/-- The paths that stay in an open set `U` up to time `t` form an open set (the image of `[0, t]` is compact). -/
theorem isOpen_setOf_forall_le_mem (t : ℝ≥0) {U : Set X} (hU : IsOpen U) :
    IsOpen {f : C(Set.Icc (0 : ℝ≥0) T, X) | ∀ s : Set.Icc (0 : ℝ≥0) T, (s : ℝ≥0) ≤ t → f s ∈ U} := by
  rw [Metric.isOpen_iff]
  intro f hf
  set K : Set X := f '' {s : Set.Icc (0 : ℝ≥0) T | (s : ℝ≥0) ≤ t}
  have hKc : IsCompact K :=
    ((isClosed_le continuous_subtype_val continuous_const).isCompact).image f.continuous
  have hKU : K ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    exact hf s hs
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, fun g hg s hs => ?_⟩
  have hd : dist (g s) (f s) < δ :=
    lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist s) (Metric.mem_ball.1 hg)
  exact hthick (Metric.mem_thickening_iff.2 ⟨f s, ⟨s, hs, rfl⟩, hd⟩)

end OpenSets

/-! ### Portmanteau with an eventual bound -/

section Portmanteau

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
  [HasOuterApproxClosed Ω]

/-- **Portmanteau for open sets with an eventual upper bound**: if `μₖ → μ` weakly, `G` is open and
`μₖ(G) ≤ c` for all large `k`, then `μ(G) ≤ c`. -/
theorem measure_le_of_tendsto_of_isOpen {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hlim : Tendsto μs atTop (𝓝 μ)) {G : Set Ω} (hG : IsOpen G) {c : ℝ≥0∞}
    (hc : ∀ᶠ k in atTop, (μs k : Measure Ω) G ≤ c) : (μ : Measure Ω) G ≤ c :=
  (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG).trans
    (liminf_le_of_frequently_le' hc.frequently)

/-- An open set of eventually zero mass has zero mass in the limit. -/
theorem measure_eq_zero_of_tendsto_of_isOpen {μs : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hlim : Tendsto μs atTop (𝓝 μ)) {G : Set Ω} (hG : IsOpen G)
    (hc : ∀ᶠ k in atTop, (μs k : Measure Ω) G = 0) : (μ : Measure Ω) G = 0 :=
  le_antisymm (measure_le_of_tendsto_of_isOpen hlim hG (hc.mono fun _ h => h.le)) bot_le

end Portmanteau

/-! ### Arzelà–Ascoli for a uniform modulus -/

section Ascoli

variable {X : Type*} [MetricSpace X] {T : ℝ≥0}

/-- **Arzelà–Ascoli** for paths with values in a compact set `s` and a uniform modulus: for every `k`, times at
distance at most `h k > 0` have values at distance at most `ω k`, where `ω k → 0`. -/
theorem isCompact_modulusSet {s : Set X} (hs : IsCompact s) {h ω : ℕ → ℝ} (hh : ∀ k, 0 < h k)
    (hω : Tendsto ω atTop (𝓝 0)) :
    IsCompact {f : C(Set.Icc (0 : ℝ≥0) T, X) | (∀ x, f x ∈ s) ∧
      ∀ k x y, dist x y ≤ h k → dist (f x) (f y) ≤ ω k} := by
  set e := ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc (0 : ℝ≥0) T) X
  set A : Set (Set.Icc (0 : ℝ≥0) T →ᵇ X) :=
    {g | (∀ x, g x ∈ s) ∧ ∀ k x y, dist x y ≤ h k → dist (g x) (g y) ≤ ω k} with hA
  have hAc : IsClosed A := by
    have h1 : IsClosed {g : Set.Icc (0 : ℝ≥0) T →ᵇ X | ∀ x, g x ∈ s} := by
      have : {g : Set.Icc (0 : ℝ≥0) T →ᵇ X | ∀ x, g x ∈ s} = ⋂ x, (fun g => g x) ⁻¹' s := by
        ext g
        simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
      rw [this]
      exact isClosed_iInter fun x => hs.isClosed.preimage (continuous_eval_const x)
    have h2 : IsClosed {g : Set.Icc (0 : ℝ≥0) T →ᵇ X |
        ∀ k x y, dist x y ≤ h k → dist (g x) (g y) ≤ ω k} := by
      have : {g : Set.Icc (0 : ℝ≥0) T →ᵇ X | ∀ k x y, dist x y ≤ h k → dist (g x) (g y) ≤ ω k} =
          ⋂ k, ⋂ x, ⋂ y, {g : Set.Icc (0 : ℝ≥0) T →ᵇ X | dist x y ≤ h k → dist (g x) (g y) ≤ ω k} := by
        ext g
        simp only [mem_ofPred_eq, mem_iInter]
      rw [this]
      refine isClosed_iInter fun k => isClosed_iInter fun x => isClosed_iInter fun y => ?_
      by_cases hxy : dist x y ≤ h k
      · simp only [hxy, true_implies]
        exact isClosed_le ((continuous_eval_const (F := Set.Icc (0 : ℝ≥0) T →ᵇ X) x).dist
          (continuous_eval_const y)) continuous_const
      · simp only [hxy, false_implies]
        exact isClosed_univ
    exact h1.inter h2
  have hAeq : Equicontinuous ((↑) : A → Set.Icc (0 : ℝ≥0) T → X) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := (hω.eventually (gt_mem_nhds hε)).exists
    refine ⟨h k, hh k, fun x hx g => ?_⟩
    exact lt_of_le_of_lt (g.2.2 k x₀ x (by rw [dist_comm]; exact hx.le)) hk
  have hcpt : IsCompact A := BoundedContinuousFunction.arzela_ascoli₂ s hs A hAc
    (fun g x hg => hg.1 x) hAeq
  have he : {f : C(Set.Icc (0 : ℝ≥0) T, X) | (∀ x, f x ∈ s) ∧
      ∀ k x y, dist x y ≤ h k → dist (f x) (f y) ≤ ω k} = e ⁻¹' A := by
    ext f
    rfl
  rw [he]
  exact e.toHomeomorph.isCompact_preimage.2 hcpt


/-- **A compact set of paths has a uniform modulus of continuity.** -/
theorem exists_modulus_of_isCompact {K : Set C(Set.Icc (0 : ℝ≥0) T, X)} (hK : IsCompact K) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ f ∈ K, ∀ x y : Set.Icc (0 : ℝ≥0) T, dist x y < δ → dist (f x) (f y) < ε := by
  obtain ⟨S, -, hSfin, hcover⟩ := hK.finite_cover_balls (e := ε / 3) (by positivity)
  have hδ : ∀ g ∈ S, ∃ δ > 0, ∀ x y : Set.Icc (0 : ℝ≥0) T, dist x y < δ → dist (g x) (g y) < ε / 3 :=
    fun g _ => Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε / 3) (by positivity)
  choose! δg hδg0 hδg using hδ
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ g ∈ S, δ < δg g :=
    (hSfin.eventually_all).2 fun g hg => Filter.mem_of_superset (Ioo_mem_nhdsGT (hδg0 g hg))
      fun _ h => h.2
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ ∀ g ∈ S, δ < δg g := h1.and h2
  obtain ⟨δ, hδ0, hδS⟩ := hev.exists
  refine ⟨δ, hδ0, fun f hf x y hxy => ?_⟩
  obtain ⟨g, hgS, hfg⟩ := mem_iUnion₂.1 (hcover hf)
  have h1 : dist (f x) (g x) < ε / 3 :=
    lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) (Metric.mem_ball.1 hfg)
  have h2 : dist (f y) (g y) < ε / 3 :=
    lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist y) (Metric.mem_ball.1 hfg)
  have h3 : dist (g x) (g y) < ε / 3 := hδg g hgS x y (hxy.trans (hδS g hgS))
  calc dist (f x) (f y) ≤ dist (f x) (g x) + dist (g x) (g y) + dist (g y) (f y) := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by rw [dist_comm (g y)]; linarith
    _ = ε := by ring

end Ascoli

/-! ### Gluing two laws along a common coordinate -/

section Glue

variable {Y X₁ X₂ : Type*} [MeasurableSpace Y] [MeasurableSpace X₁] [MeasurableSpace X₂]
  [StandardBorelSpace X₁] [Nonempty X₁] [StandardBorelSpace X₂] [Nonempty X₂]

/-- **Conditionally independent gluing.** Two probability laws `π₁` on `X₁ × Y` and `π₂` on `X₂ × Y` with the same
law of the `Y`-coordinate are the two marginals of one law `γ` on `Y × X₁ × X₂` (the two `X`-coordinates
conditionally independent given `Y`). -/
theorem exists_glue (π₁ : Measure (X₁ × Y)) (π₂ : Measure (X₂ × Y)) [IsProbabilityMeasure π₁]
    [IsProbabilityMeasure π₂] (h : π₁.map Prod.snd = π₂.map Prod.snd) :
    ∃ γ : Measure (Y × X₁ × X₂), IsProbabilityMeasure γ ∧
      γ.map (fun z => (z.2.1, z.1)) = π₁ ∧ γ.map (fun z => (z.2.2, z.1)) = π₂ := by
  set ρ₁ : Measure (Y × X₁) := π₁.map Prod.swap
  set ρ₂ : Measure (Y × X₂) := π₂.map Prod.swap
  have hρ₁ : IsProbabilityMeasure ρ₁ := inferInstance
  have hρ₂ : IsProbabilityMeasure ρ₂ := inferInstance
  have hfst₁ : ρ₁.fst = π₁.map Prod.snd := by
    rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    rfl
  have hfst₂ : ρ₂.fst = π₂.map Prod.snd := by
    rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    rfl
  set ν := ρ₁.fst
  have hν₂ : ρ₂.fst = ν := by rw [hfst₂, ← h, hfst₁]
  set γ : Measure (Y × X₁ × X₂) := ν ⊗ₘ (ρ₁.condKernel ×ₖ ρ₂.condKernel)
  have hd₁ : ν ⊗ₘ ρ₁.condKernel = ρ₁ := ρ₁.disintegrate ρ₁.condKernel
  have hd₂ : ν ⊗ₘ ρ₂.condKernel = ρ₂ := by rw [← hν₂]; exact ρ₂.disintegrate ρ₂.condKernel
  have hm₁ : γ.map (Prod.map id Prod.fst) = ρ₁ := by
    rw [← Measure.compProd_map measurable_fst]
    rw [← Kernel.fst_eq, Kernel.fst_prod, hd₁]
  have hm₂ : γ.map (Prod.map id Prod.snd) = ρ₂ := by
    rw [← Measure.compProd_map measurable_snd]
    rw [← Kernel.snd_eq, Kernel.snd_prod, hd₂]
  refine ⟨γ, inferInstance, ?_, ?_⟩
  · have e : (fun z : Y × X₁ × X₂ => (z.2.1, z.1)) = Prod.swap ∘ Prod.map id Prod.fst := rfl
    rw [e, ← Measure.map_map measurable_swap (measurable_id.prodMap measurable_fst), hm₁,
      Measure.map_map measurable_swap measurable_swap]
    simp only [Prod.swap_swap_eq, Measure.map_id]
  · have e : (fun z : Y × X₁ × X₂ => (z.2.2, z.1)) = Prod.swap ∘ Prod.map id Prod.snd := rfl
    rw [e, ← Measure.map_map measurable_swap (measurable_id.prodMap measurable_snd), hm₂,
      Measure.map_map measurable_swap measurable_swap]
    simp only [Prod.swap_swap_eq, Measure.map_id]

omit [StandardBorelSpace X₁] [Nonempty X₁] [StandardBorelSpace X₂] [Nonempty X₂] in
/-- **Equality of the laws of an event under two glued marginals.** If, `γ`-almost surely, the first `X`-coordinate
is in `A₁` exactly when the second is in `A₂`, the two laws give `A₁ × Y` and `A₂ × Y` the same probability. -/
theorem measure_prod_univ_eq_of_glue {γ : Measure (Y × X₁ × X₂)} {π₁ : Measure (X₁ × Y)}
    {π₂ : Measure (X₂ × Y)} (h₁ : γ.map (fun z => (z.2.1, z.1)) = π₁)
    (h₂ : γ.map (fun z => (z.2.2, z.1)) = π₂) {A₁ : Set X₁} {A₂ : Set X₂} (hA₁ : MeasurableSet A₁)
    (hA₂ : MeasurableSet A₂) (hiff : ∀ᵐ z ∂γ, (z.2.1 ∈ A₁ ↔ z.2.2 ∈ A₂)) :
    π₁ (A₁ ×ˢ univ) = π₂ (A₂ ×ˢ univ) := by
  have hm₁ : Measurable fun z : Y × X₁ × X₂ => (z.2.1, z.1) := (measurable_fst.comp measurable_snd).prodMk
    measurable_fst
  have hm₂ : Measurable fun z : Y × X₁ × X₂ => (z.2.2, z.1) := (measurable_snd.comp measurable_snd).prodMk
    measurable_fst
  rw [← h₁, ← h₂, Measure.map_apply hm₁ (hA₁.prod MeasurableSet.univ),
    Measure.map_apply hm₂ (hA₂.prod MeasurableSet.univ)]
  refine measure_congr ?_
  filter_upwards [hiff] with z hz
  simp only [mem_preimage, mem_prod, mem_univ, and_true, eq_iff_iff]
  exact hz

end Glue

end DSReach

end Supp12

end InteractingSLE
