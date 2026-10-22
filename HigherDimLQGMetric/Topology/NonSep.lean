import HigherDimLQGMetric.Topology.NonSepCone

/-!
# Codimension-two nonseparation (D-NS), part 4: balls (NS-5), chaining (NS-6), main theorems

Packet M4 (ruling M9: the Krupski–Valov input [5], used in the source's §4 (l. 567–571, Lemma 4.1
l. 617–620 and 634–637), is replaced by the elementary theorem D-NS). Source: planning audit
`planning/audits/MA1-sections-1-4.md`, item 25 and Details (a) **A15** (MA1 probes `ns_arc`,
`ns_tree`); MA0 §2.9. Carrier: `ℝ^d` as `HigherDimLFPP.Rd d = EuclideanSpace ℝ (Fin d)`.

**Theorem D-NS.** Let `d ≥ 3`, `Ω ⊆ ℝ^d` open and connected, and `T = A ∪ A′` where `A, A′` are
arcs (injective continuous images of `[0,1]`; `A′ = ∅` allowed) with `A ∩ A′` at most one point.
Then `Ω ∖ T` is path-connected (`ns_arc`, `ns_tree`), and any two of its points are joined by a
polygonal path in `Ω ∖ T` (`ns_arc_polygonal`, `ns_tree_polygonal`).

* `joinedIn_ball_diff_range` (**NS-5**, one arc): for a ball `B`, `B ∖ A` is path-connected.
  Bisection: if `x, y` were not joined in `B ∖ α([a, b])`, then (NS-3 with `G₁ = B ∖ α([a, m])`,
  `G₂ = B ∖ α([m, b])`, `G₁ ∪ G₂ = B ∖ {α(m)}`, NS-2) they would not be joined in one of the
  halves; the nested intervals shrink to `t*`, but a path from `x` to `y` in `B ∖ {α(t*)}` avoids
  `α([a, b])` for short intervals around `t*`.
* `joinedIn_ball_diff_range_union` (NS-5, two arcs): NS-3 with `G₁ = B ∖ A`, `G₂ = B ∖ A′`.
* `joinedIn_diff_of_ball` (**NS-6**): balls chain along `Ω` (open–closed argument
  `IsPreconnected.induction₂'`), using that `T` has empty interior (NS-4).
* `ns_arc_Icc`, `ns_tree_Icc`: the same for arcs parametrized on intervals `[a, b]`, `a < b`.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGMetric.Topology

open Set unitInterval Metric Filter
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### Sub-arcs -/

/-- The sub-arc `α([a, b])` of a path `α : [0,1] → X`. -/
def subArc {X : Type*} (α : I → X) (a b : ℝ) : Set X :=
  α '' {t : I | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b}

lemma isCompact_subArc {X : Type*} [TopologicalSpace X] (α : C(I, X)) (a b : ℝ) :
    IsCompact (subArc α a b) := by
  apply IsCompact.image _ α.continuous
  apply IsClosed.isCompact
  exact (isClosed_le continuous_const continuous_subtype_val).inter
    (isClosed_le continuous_subtype_val continuous_const)

lemma subArc_zero_one {X : Type*} (α : I → X) : subArc α 0 1 = range α := by
  ext z
  simp only [subArc, mem_image, mem_ofPred_eq, mem_range]
  exact ⟨fun ⟨t, _, ht⟩ => ⟨t, ht⟩, fun ⟨t, ht⟩ => ⟨t, ⟨t.2.1, t.2.2⟩, ht⟩⟩

lemma subArc_subset_range {X : Type*} (α : I → X) (a b : ℝ) : subArc α a b ⊆ range α :=
  image_subset_range _ _

lemma subArc_union {X : Type*} (α : I → X) {a m b : ℝ} :
    subArc α a m ∪ subArc α m b = subArc α a b ∨ ¬ (a ≤ m ∧ m ≤ b) := by
  by_cases h : a ≤ m ∧ m ≤ b
  · left
    ext z
    simp only [subArc, mem_union, mem_image, mem_ofPred_eq]
    constructor
    · rintro (⟨t, ⟨h1, h2⟩, rfl⟩ | ⟨t, ⟨h1, h2⟩, rfl⟩)
      · exact ⟨t, ⟨h1, h2.trans h.2⟩, rfl⟩
      · exact ⟨t, ⟨h.1.trans h1, h2⟩, rfl⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      rcases le_total (t : ℝ) m with htm | htm
      · exact Or.inl ⟨t, ⟨h1, htm⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨htm, h2⟩, rfl⟩
  · exact Or.inr h

/-- Two adjacent sub-arcs make up the sub-arc of the union interval. -/
lemma subArc_union_of_le {X : Type*} (α : I → X) {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b) :
    subArc α a m ∪ subArc α m b = subArc α a b :=
  (subArc_union α).resolve_right (not_not.2 ⟨ham, hmb⟩)

/-- Two adjacent sub-arcs of an injective path meet in at most one point. -/
lemma subArc_inter_subsingleton {X : Type*} {α : I → X} (hα : Function.Injective α)
    (a m b : ℝ) : (subArc α a m ∩ subArc α m b).Subsingleton := by
  rintro _ ⟨⟨t₁, ⟨-, h1⟩, rfl⟩, ⟨t₂, ⟨h2, -⟩, h12⟩⟩ _ ⟨⟨t₃, ⟨-, h3⟩, rfl⟩, ⟨t₄, ⟨h4, -⟩, h34⟩⟩
  have e12 := hα h12
  have e34 := hα h34
  subst e12
  subst e34
  have : t₂ = t₄ := Subtype.ext (by linarith)
  rw [this]

/-! ### NS-5: balls -/

/-- **NS-5, one arc.** For `d ≥ 3`, an open ball `B` and an arc `A = α([0,1])`, any two points of
`B ∖ A` are joined by a path in `B ∖ A`. -/
theorem joinedIn_ball_diff_range (hd : 3 ≤ d) (c : Rd d) (ρ : ℝ) (α : C(I, Rd d))
    (hα : Function.Injective α) {x y : Rd d} (hx : x ∈ ball c ρ \ range α)
    (hy : y ∈ ball c ρ \ range α) : JoinedIn (ball c ρ \ range α) x y := by
  by_contra hxy
  have hxA : ∀ a b, x ∈ ball c ρ \ subArc α a b :=
    fun a b => ⟨hx.1, fun h => hx.2 (subArc_subset_range α a b h)⟩
  have hyA : ∀ a b, y ∈ ball c ρ \ subArc α a b :=
    fun a b => ⟨hy.1, fun h => hy.2 (subArc_subset_range α a b h)⟩
  refine bisection_false (fun a b => ¬ JoinedIn (ball c ρ \ subArc α a b) x y) zero_le_one
    (by rwa [subArc_zero_one]) ?_ ?_
  · -- splitting: Mayer–Vietoris (NS-3) with `G₁ ∪ G₂ = B ∖ {α(m)}`
    intro a b _ hab _ hP
    by_contra h
    rw [not_or, not_not, not_not] at h
    apply hP
    set m := (a + b) / 2 with hm
    have hW : LoopsContractibleIn ((ball c ρ \ subArc α a m) ∪ (ball c ρ \ subArc α m b)) := by
      rw [← sdiff_inter]
      exact loopsContractibleIn_ball_diff_of_subsingleton hd c ρ
        (subArc_inter_subsingleton hα a m b)
    have key := joinedIn_inter_of_joinedIn
      (isOpen_ball.sdiff (isCompact_subArc α a m).isClosed)
      (isOpen_ball.sdiff (isCompact_subArc α m b).isClosed) hW ⟨hyA a m, hyA m b⟩ h.1 h.2
    rwa [sdiff_inter_sdiff, subArc_union_of_le α (by rw [hm]; linarith) (by rw [hm]; linarith)]
      at key
  · -- locality: a path avoiding `α(t)` avoids `α([a', b'])` for short intervals around `t`
    intro t ht
    set p := α ⟨t, ht⟩ with hp
    have hpx : x ∈ ball c ρ \ {p} := ⟨hx.1, fun h => hx.2 ⟨_, (mem_singleton_iff.1 h).symm⟩⟩
    have hpy : y ∈ ball c ρ \ {p} := ⟨hy.1, fun h => hy.2 ⟨_, (mem_singleton_iff.1 h).symm⟩⟩
    obtain ⟨γ, hγ⟩ := joinedIn_ball_diff_singleton (by omega) c p ρ hpx hpy
    have hK : IsClosed (range γ) := (isCompact_range γ.continuous).isClosed
    have hpK : p ∉ range γ := by
      rintro ⟨s, hs⟩
      exact (hγ s).2 hs
    obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 hK.isOpen_compl p hpK
    obtain ⟨η, hη, hηα⟩ := Metric.continuous_iff.1 α.continuous ⟨t, ht⟩ ε hε
    refine ⟨η, hη, fun a' b' ha' hb' hab' hP => hP ⟨γ, fun s => ⟨(hγ s).1, ?_⟩⟩⟩
    rintro ⟨u, ⟨hu1, hu2⟩, hu⟩
    have hdist : dist (α u) p < ε := by
      apply hηα
      rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
      simp only
      constructor <;> linarith
    exact hεK (mem_ball.2 (hu ▸ hdist)) ⟨s, rfl⟩

/-- **NS-5, two arcs.** For `d ≥ 3`, an open ball `B` and two arcs `A = α([0,1])`,
`A′ = β([0,1])` meeting in at most one point, any two points of `B ∖ (A ∪ A′)` are joined by a
path in `B ∖ (A ∪ A′)`. -/
theorem joinedIn_ball_diff_range_union (hd : 3 ≤ d) (c : Rd d) (ρ : ℝ) (α β : C(I, Rd d))
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (hαβ : (range α ∩ range β).Subsingleton) {x y : Rd d}
    (hx : x ∈ ball c ρ \ (range α ∪ range β)) (hy : y ∈ ball c ρ \ (range α ∪ range β)) :
    JoinedIn (ball c ρ \ (range α ∪ range β)) x y := by
  have hxα : x ∈ ball c ρ \ range α := ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
  have hyα : y ∈ ball c ρ \ range α := ⟨hy.1, fun h => hy.2 (Or.inl h)⟩
  have hxβ : x ∈ ball c ρ \ range β := ⟨hx.1, fun h => hx.2 (Or.inr h)⟩
  have hyβ : y ∈ ball c ρ \ range β := ⟨hy.1, fun h => hy.2 (Or.inr h)⟩
  have hW : LoopsContractibleIn ((ball c ρ \ range α) ∪ (ball c ρ \ range β)) := by
    rw [← sdiff_inter]
    exact loopsContractibleIn_ball_diff_of_subsingleton hd c ρ hαβ
  have key := joinedIn_inter_of_joinedIn
    (isOpen_ball.sdiff (isCompact_range α.continuous).isClosed)
    (isOpen_ball.sdiff (isCompact_range β.continuous).isClosed) hW ⟨hyα, hyβ⟩
    (joinedIn_ball_diff_range hd c ρ α hα hxα hyα) (joinedIn_ball_diff_range hd c ρ β hβ hxβ hyβ)
  rwa [sdiff_inter_sdiff] at key

/-! ### NS-6: chaining balls -/

/-- **NS-6 (chaining balls).** Let `Ω` be open and preconnected in a metric space and `T` a set
such that, for every ball `B`, any two points of `B ∖ T` are joined in `B ∖ T`, and every nonempty
open set meets the complement of `T`. Then any two points of `Ω ∖ T` are joined in `Ω ∖ T`. -/
theorem joinedIn_diff_of_ball {X : Type*} [PseudoMetricSpace X] {Ω T : Set X}
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hball : ∀ (c : X) (ρ : ℝ), ∀ x ∈ ball c ρ \ T, ∀ y ∈ ball c ρ \ T,
      JoinedIn (ball c ρ \ T) x y)
    (hint : ∀ U : Set X, IsOpen U → U.Nonempty → (U \ T).Nonempty)
    {x y : X} (hx : x ∈ Ω \ T) (hy : y ∈ Ω \ T) : JoinedIn (Ω \ T) x y := by
  -- `R z z'`: all points of `B(z, ε) ∖ T` and `B(z', ε') ∖ T` are joined in `Ω ∖ T`
  let R : X → X → Prop := fun z z' => ∃ ε > 0, ∃ ε' > 0, ball z ε ⊆ Ω ∧ ball z' ε' ⊆ Ω ∧
    ∀ w ∈ ball z ε \ T, ∀ w' ∈ ball z' ε' \ T, JoinedIn (Ω \ T) w w'
  have hmono : ∀ {c : X} {ρ : ℝ}, ball c ρ ⊆ Ω → ball c ρ \ T ⊆ Ω \ T :=
    fun h => sdiff_subset_sdiff_left h
  have hR : R x y := by
    refine hΩc.induction₂' R ?_ ?_ hx.1 hy.1
    · intro z hz
      obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩo z hz
      filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (half_pos hε))] with z' hz'
      have hsub : ball z' (ε / 2) ⊆ ball z ε := by
        apply ball_subset_ball'
        rw [mem_ball] at hz'
        linarith
      refine ⟨⟨ε, hε, ε / 2, half_pos hε, hεΩ, hsub.trans hεΩ, ?_⟩,
        ⟨ε / 2, half_pos hε, ε, hε, hsub.trans hεΩ, hεΩ, ?_⟩⟩
      · intro w hw w' hw'
        exact (hball z ε w hw w' ⟨hsub hw'.1, hw'.2⟩).mono (hmono hεΩ)
      · intro w hw w' hw'
        exact (hball z ε w ⟨hsub hw.1, hw.2⟩ w' hw').mono (hmono hεΩ)
    · rintro z₁ z₂ z₃ - - - ⟨ε₁, hε₁, ε₂, hε₂, h₁Ω, h₂Ω, h₁₂⟩ ⟨ε₂', hε₂', ε₃, hε₃, h₂Ω', h₃Ω, h₂₃⟩
      obtain ⟨u, hu⟩ := hint (ball z₂ (min ε₂ ε₂')) isOpen_ball
        ⟨z₂, mem_ball_self (lt_min hε₂ hε₂')⟩
      have hu₂ : u ∈ ball z₂ ε₂ \ T := ⟨ball_subset_ball (min_le_left _ _) hu.1, hu.2⟩
      have hu₂' : u ∈ ball z₂ ε₂' \ T := ⟨ball_subset_ball (min_le_right _ _) hu.1, hu.2⟩
      exact ⟨ε₁, hε₁, ε₃, hε₃, h₁Ω, h₃Ω, fun w hw w'' hw'' =>
        (h₁₂ w hw u hu₂).trans (h₂₃ u hu₂' w'' hw'')⟩
  obtain ⟨ε, hε, ε', hε', -, -, hR'⟩ := hR
  exact hR' x ⟨mem_ball_self hε, hx.2⟩ y ⟨mem_ball_self hε', hy.2⟩

/-! ### D-NS -/

/-- **D-NS, one arc** (MA1 probe `ns_arc`). For `d ≥ 3`, an open connected `Ω ⊆ ℝ^d` and an arc
`A = α([0,1])` (`α` continuous and injective), `Ω ∖ A` is path-connected. -/
theorem ns_arc (hd : 3 ≤ d) {Ω : Set (Rd d)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (α : C(I, Rd d)) (hα : Function.Injective α) :
    IsPathConnected (Ω \ Set.range α) := by
  obtain ⟨x, hx⟩ := nonempty_diff_range (by omega) α hα hΩo hΩc.nonempty
  exact ⟨x, hx, fun {y} hy => joinedIn_diff_of_ball hΩo hΩc.isPreconnected
    (fun c ρ _ hx' _ hy' => joinedIn_ball_diff_range hd c ρ α hα hx' hy')
    (fun _ hU hne => nonempty_diff_range (by omega) α hα hU hne) hx hy⟩

/-- **D-NS, two arcs meeting in at most one point** (MA1 probe `ns_tree`; both uses in the
source's Lemma 4.1, l. 617–620 and 634–637). For `d ≥ 3`, an open connected `Ω ⊆ ℝ^d` and arcs
`A = α([0,1])`, `A′ = β([0,1])` with `A ∩ A′` at most one point, `Ω ∖ (A ∪ A′)` is
path-connected. -/
theorem ns_tree (hd : 3 ≤ d) {Ω : Set (Rd d)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (α β : C(I, Rd d)) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hαβ : (Set.range α ∩ Set.range β).Subsingleton) :
    IsPathConnected (Ω \ (Set.range α ∪ Set.range β)) := by
  obtain ⟨x, hx⟩ := nonempty_diff_range_union (by omega) α β hα hβ hΩo hΩc.nonempty
  exact ⟨x, hx, fun {y} hy => joinedIn_diff_of_ball hΩo hΩc.isPreconnected
    (fun c ρ _ hx' _ hy' => joinedIn_ball_diff_range_union hd c ρ α β hα hβ hαβ hx' hy')
    (fun _ hU hne => nonempty_diff_range_union (by omega) α β hα hβ hU hne) hx hy⟩

/-! ### Polygonal connectivity -/

/-- `x` and `y` are joined in `U` by a polygonal path: there are points `z 0 = x, …, z n = y`
such that every segment `[z i, z (i + 1)]` lies in `U`. -/
def PolygonalJoinedIn {E : Type*} [AddCommGroup E] [Module ℝ E] (U : Set E) (x y : E) : Prop :=
  ∃ (n : ℕ) (z : ℕ → E), z 0 = x ∧ z n = y ∧ ∀ i < n, segment ℝ (z i) (z (i + 1)) ⊆ U

section Polygonal

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {U : Set E} {x y z : E}

/-- Reversing a polygonal path. -/
lemma PolygonalJoinedIn.symm (h : PolygonalJoinedIn U x y) : PolygonalJoinedIn U y x := by
  obtain ⟨n, f, h0, hn, hseg⟩ := h
  refine ⟨n, fun i => f (n - i), by simpa using hn, by simpa using h0, fun i hi => ?_⟩
  have := hseg (n - (i + 1)) (by omega)
  rw [show n - (i + 1) + 1 = n - i by omega, segment_symm] at this
  exact this

/-- Concatenating polygonal paths. -/
lemma PolygonalJoinedIn.trans (h₁ : PolygonalJoinedIn U x y) (h₂ : PolygonalJoinedIn U y z) :
    PolygonalJoinedIn U x z := by
  obtain ⟨n, f, hf0, hfn, hf⟩ := h₁
  obtain ⟨m, g, hg0, hgm, hg⟩ := h₂
  have hfg : f n = g 0 := hfn.trans hg0.symm
  -- the concatenated chain
  set h : ℕ → E := fun i => if i ≤ n then f i else g (i - n) with hh
  have hh_lo : ∀ i, i ≤ n → h i = f i := fun i hi => by simp only [hh, hi, ↓reduceIte]
  have hh_hi : ∀ i, n ≤ i → h i = g (i - n) := by
    intro i hi
    by_cases hin : i ≤ n
    · have : i = n := le_antisymm hin hi
      subst this
      simp only [hh, le_refl, ↓reduceIte, Nat.sub_self, hfg]
    · simp only [hh, hin, ↓reduceIte]
  refine ⟨n + m, h, by rw [hh_lo 0 (Nat.zero_le n), hf0], ?_, fun i hi => ?_⟩
  · rw [hh_hi (n + m) (Nat.le_add_right n m), Nat.add_sub_cancel_left, hgm]
  · by_cases hin : i < n
    · rw [hh_lo i hin.le, hh_lo (i + 1) hin]
      exact hf i hin
    · rw [hh_hi i (not_lt.1 hin), hh_hi (i + 1) (by omega),
        show i + 1 - n = i - n + 1 by omega]
      exact hg (i - n) (by omega)

end Polygonal

/-- In a real normed space, any two points of an open preconnected set `U` are joined by a
polygonal path in `U`. -/
theorem polygonalJoinedIn_of_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    PolygonalJoinedIn U x y := by
  refine hUc.induction₂ (PolygonalJoinedIn U) (fun z hz => ?_)
    (fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ _ _ h => h.symm) hx hy
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z hε)] with z' hz'
  refine ⟨1, fun i => if i = 0 then z else z', by simp, by simp, fun i hi => ?_⟩
  have hi0 : i = 0 := by omega
  subst hi0
  simp only [↓reduceIte, zero_add, one_ne_zero]
  exact ((convex_ball z ε).segment_subset (mem_ball_self hε) hz').trans hεU

/-- **D-NS, one arc, polygonal form.** For `d ≥ 3`, an open connected `Ω ⊆ ℝ^d` and an arc
`A = α([0,1])`, `Ω ∖ A` is open, and any two of its points are joined by a polygonal path in
`Ω ∖ A`. -/
theorem ns_arc_polygonal (hd : 3 ≤ d) {Ω : Set (Rd d)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    (α : C(I, Rd d)) (hα : Function.Injective α) :
    IsOpen (Ω \ Set.range α) ∧ ∀ x ∈ Ω \ Set.range α, ∀ y ∈ Ω \ Set.range α,
      PolygonalJoinedIn (Ω \ Set.range α) x y := by
  have ho : IsOpen (Ω \ Set.range α) := hΩo.sdiff (isCompact_range α.continuous).isClosed
  exact ⟨ho, fun x hx y hy => polygonalJoinedIn_of_isOpen ho
    (ns_arc hd hΩo hΩc α hα).isConnected.isPreconnected hx hy⟩

/-- **D-NS, two arcs, polygonal form.** For `d ≥ 3`, an open connected `Ω ⊆ ℝ^d` and arcs
`A = α([0,1])`, `A′ = β([0,1])` meeting in at most one point, `Ω ∖ (A ∪ A′)` is open, and any two
of its points are joined by a polygonal path in `Ω ∖ (A ∪ A′)`. -/
theorem ns_tree_polygonal (hd : 3 ≤ d) {Ω : Set (Rd d)} (hΩo : IsOpen Ω)
    (hΩc : IsConnected Ω) (α β : C(I, Rd d)) (hα : Function.Injective α)
    (hβ : Function.Injective β) (hαβ : (Set.range α ∩ Set.range β).Subsingleton) :
    IsOpen (Ω \ (Set.range α ∪ Set.range β)) ∧
      ∀ x ∈ Ω \ (Set.range α ∪ Set.range β), ∀ y ∈ Ω \ (Set.range α ∪ Set.range β),
        PolygonalJoinedIn (Ω \ (Set.range α ∪ Set.range β)) x y := by
  have ho : IsOpen (Ω \ (Set.range α ∪ Set.range β)) :=
    hΩo.sdiff ((isCompact_range α.continuous).union (isCompact_range β.continuous)).isClosed
  exact ⟨ho, fun x hx y hy => polygonalJoinedIn_of_isOpen ho
    (ns_tree hd hΩo hΩc α β hα hβ hαβ).isConnected.isPreconnected hx hy⟩

/-! ### Arcs parametrized on an interval -/

/-- A continuous map on `[a, b]` (`a < b`) that is injective there is an arc: its image is the
range of an injective continuous `α : [0,1] → X`. -/
lemma exists_arc_of_injOn {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {a b : ℝ} (hab : a < b)
    (hγc : ContinuousOn γ (Icc a b)) (hγi : InjOn γ (Icc a b)) :
    ∃ α : C(I, X), Function.Injective α ∧ Set.range α = γ '' Icc a b := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hmem : ∀ t : I, a + (t : ℝ) * (b - a) ∈ Icc a b := fun t =>
    ⟨by nlinarith [t.2.1], by nlinarith [t.2.2]⟩
  refine ⟨⟨fun t => γ (a + (t : ℝ) * (b - a)),
    hγc.comp_continuous (by fun_prop) hmem⟩, ?_, ?_⟩
  · intro t t' h
    have h1 := hγi (hmem t) (hmem t') h
    apply Subtype.ext
    have h2 : ((t : ℝ) - t') * (b - a) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · linarith
  · ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, hmem t, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨(s - a) / (b - a), div_nonneg (by linarith [hs.1]) hba.le,
        (div_le_one hba).2 (by linarith [hs.2])⟩, ?_⟩
      show γ (a + (s - a) / (b - a) * (b - a)) = γ s
      rw [div_mul_cancel₀ _ hba.ne', add_sub_cancel]

/-- **D-NS, one arc on an interval.** For `d ≥ 3`, an open connected `Ω ⊆ ℝ^d` and `γ`
continuous and injective on `[a, b]` (`a < b`), `Ω ∖ γ([a, b])` is path-connected. -/
theorem ns_arc_Icc (hd : 3 ≤ d) {Ω : Set (Rd d)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {γ : ℝ → Rd d} {a b : ℝ} (hab : a < b) (hγc : ContinuousOn γ (Icc a b))
    (hγi : InjOn γ (Icc a b)) : IsPathConnected (Ω \ γ '' Icc a b) := by
  obtain ⟨α, hα, hrange⟩ := exists_arc_of_injOn hab hγc hγi
  rw [← hrange]
  exact ns_arc hd hΩo hΩc α hα

/-- **D-NS, two arcs on intervals.** For `d ≥ 3`, an open connected `Ω ⊆ ℝ^d` and `γ₁, γ₂`
continuous and injective on `[a₁, b₁]`, `[a₂, b₂]` (`a₁ < b₁`, `a₂ < b₂`) whose images meet in at
most one point, `Ω ∖ (γ₁([a₁, b₁]) ∪ γ₂([a₂, b₂]))` is path-connected. -/
theorem ns_tree_Icc (hd : 3 ≤ d) {Ω : Set (Rd d)} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω)
    {γ₁ γ₂ : ℝ → Rd d} {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (h₂ : a₂ < b₂)
    (hc₁ : ContinuousOn γ₁ (Icc a₁ b₁)) (hc₂ : ContinuousOn γ₂ (Icc a₂ b₂))
    (hi₁ : InjOn γ₁ (Icc a₁ b₁)) (hi₂ : InjOn γ₂ (Icc a₂ b₂))
    (h12 : (γ₁ '' Icc a₁ b₁ ∩ γ₂ '' Icc a₂ b₂).Subsingleton) :
    IsPathConnected (Ω \ (γ₁ '' Icc a₁ b₁ ∪ γ₂ '' Icc a₂ b₂)) := by
  obtain ⟨α, hα, hrα⟩ := exists_arc_of_injOn h₁ hc₁ hi₁
  obtain ⟨β, hβ, hrβ⟩ := exists_arc_of_injOn h₂ hc₂ hi₂
  rw [← hrα, ← hrβ] at h12 ⊢
  exact ns_tree hd hΩo hΩc α β hα hβ h12

end HigherDimLQGMetric.Topology

end
