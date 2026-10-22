import HigherDimLQGMetric.Trap.Sets

/-!
# The trap for the base configuration at one index ([S] Lemma 4.2, MA1 A17 "(ii) for `ξ₀`")

Packet S3. In a metric space `Z` (the base coordinate `ζ` is the distance), fix one weight
`w = w_N` of the collapse sequence and assume that every confined weighted geodesic of S1c's
`CollapseGeodesicCandidate` form has a marked shortcut (the conclusion of S1c's
`lemma32_shortcut` at index `N`). Then every `(w·ζ)`-minimizer between points of `closure V` at
distance `≥ b/2` has a subcurve of weighted length `≥ λ_N a₁/2` with a shortcut of ratio `≤ ĉ`
inside `Y′ = trapSet A V a_col` (`trap_base_ii`). The proof follows MA1 A17: the minimizer stays in
`Y′` by the collar (C); it hits the closed `η_N`-tube (otherwise its cost is `≥ a₀ b/2 > 3ε₀`); the
parts before the first and after the last tube contact have length `≤ 3ε₀/a₀ < b/8`; the middle
segment is a `Y′`-confined geodesic between points of the closed tube at distance `≥ b/4`; its
parametrization by weighted arc length is a collapse candidate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- A finite rectifiable graph has bounded intrinsic diameter. -/
theorem trap_graph_bound {Z : Type*} [MetricSpace Z] {K : Set Z} (hK : IsFiniteRectGraph K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ K, ∀ q ∈ K, internalEDist K p q ≤ ENNReal.ofReal D := by
  have hKc : IsCompact (K ×ˢ K) := hK.isCompact.prod hK.isCompact
  have hcont : ContinuousOn (fun p : Z × Z => (internalEDist K p.1 p.2).toReal) (K ×ˢ K) := by
    intro p hp
    have h1 := hK.continuousOn_internal p hp
    have hfin := hK.internal_finite hp.1 hp.2
    exact ContinuousAt.comp_continuousWithinAt (g := ENNReal.toReal)
      (f := fun p : Z × Z => internalEDist K p.1 p.2) (ENNReal.continuousAt_toReal hfin) h1
  obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max D 0, le_max_right _ _, fun p hp q hq => ?_⟩
  have hb := hD (p, q) ⟨hp, hq⟩
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hb
  rw [← ENNReal.ofReal_toReal (hK.internal_finite hp hq)]
  exact ENNReal.ofReal_le_ofReal (hb.trans (le_max_left _ _))

/-- A shortest curve in a finite rectifiable graph, as a curve on `[0, 1]`. -/
theorem trap_graph_curve {Z : Type*} [MetricSpace Z] {K : Set Z} (hK : IsFiniteRectGraph K)
    {p q : Z} (hp : p ∈ K) (hq : q ∈ K) :
    ∃ P : ℝ → Z, ContinuousOn P (Icc 0 1) ∧ P 0 = p ∧ P 1 = q ∧ MapsTo P (Icc 0 1) K ∧
      curveLength P 0 1 = internalEDist K p q := by
  obtain ⟨γ, hγK, hγlen⟩ := hK.exists_shortest_path hp hq
  refine ⟨γ.extend, γ.continuous_extend.continuousOn, γ.extend_zero, γ.extend_one, ?_, hγlen⟩
  intro t ht
  rw [Path.extend_apply _ ht]
  exact hγK ⟨t, ht⟩

/-- A lower bound that holds on `[a, t)` passes to `t` by continuity. -/
theorem trap_le_of_left {f : ℝ → ℝ} {a t c : ℝ} (hat : a < t)
    (hf : ContinuousWithinAt f (Ico a t) t) (h : ∀ τ ∈ Ico a t, c ≤ f τ) : c ≤ f t := by
  have hmem : t ∈ closure (Ico a t) := by
    rw [closure_Ico hat.ne]
    exact ⟨hat.le, le_rfl⟩
  exact ContinuousWithinAt.closure_le hmem continuousWithinAt_const hf h

/-- A lower bound that holds on `(t, b]` passes to `t` by continuity. -/
theorem trap_le_of_right {f : ℝ → ℝ} {t b c : ℝ} (htb : t < b)
    (hf : ContinuousWithinAt f (Ioc t b) t) (h : ∀ τ ∈ Ioc t b, c ≤ f τ) : c ≤ f t := by
  have hmem : t ∈ closure (Ioc t b) := by
    rw [closure_Ioc htb.ne]
    exact ⟨le_rfl, htb.le⟩
  exact ContinuousWithinAt.closure_le hmem continuousWithinAt_const hf h

/-- Before the first contact with the closed `η`-tube, the curve pays at least `a₀` per unit
length. -/
theorem trap_prefix_bound {Z : Type*} [MetricSpace Z] {K : Set Z} {w : Z → ℝ} {η a₀ : ℝ}
    (hwoff : ∀ p, η ≤ Metric.infDist p K → a₀ ≤ w p) {Q : ℝ → Z}
    (hQ : ContinuousOn Q (Icc 0 1)) {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1)
    (hbefore : ∀ τ ∈ Ico 0 t₁, η < Metric.infDist (Q τ) K) :
    ENNReal.ofReal a₀ * edist (Q 0) (Q t₁) ≤ weightedLength w Q 0 1 := by
  rcases ht₁.1.lt_or_eq with hpos | hzero
  · have hcontf : ContinuousOn (fun τ => Metric.infDist (Q τ) K) (Icc 0 1) :=
      (Metric.continuous_infDist_pt K).comp_continuousOn hQ
    have hlast : η ≤ Metric.infDist (Q t₁) K :=
      trap_le_of_left hpos ((hcontf t₁ ht₁).mono fun τ hτ => ⟨hτ.1, hτ.2.le.trans ht₁.2⟩)
        fun τ hτ => (hbefore τ hτ).le
    have hw : ∀ τ ∈ Icc 0 t₁, a₀ ≤ w (Q τ) := by
      intro τ hτ
      rcases hτ.2.lt_or_eq with hlt | heq
      · exact hwoff _ (hbefore τ ⟨hτ.1, hlt⟩).le
      · exact hwoff _ (heq ▸ hlast)
    calc ENNReal.ofReal a₀ * edist (Q 0) (Q t₁)
        ≤ ENNReal.ofReal a₀ * curveLength Q 0 t₁ :=
          mul_le_mul' le_rfl (edist_le_curveLength Q ht₁.1)
      _ ≤ weightedLength w Q 0 t₁ := ofReal_mul_curveLength_le_weightedLength ht₁.1 hw
      _ ≤ weightedLength w Q 0 1 := weightedLength_mono_interval le_rfl ht₁.1 ht₁.2
  · rw [← hzero, edist_self, mul_zero]
    exact bot_le

/-- After the last contact with the closed `η`-tube, the curve pays at least `a₀` per unit
length. -/
theorem trap_suffix_bound {Z : Type*} [MetricSpace Z] {K : Set Z} {w : Z → ℝ} {η a₀ : ℝ}
    (hwoff : ∀ p, η ≤ Metric.infDist p K → a₀ ≤ w p) {Q : ℝ → Z}
    (hQ : ContinuousOn Q (Icc 0 1)) {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1)
    (hafter : ∀ τ ∈ Ioc t₂ 1, η < Metric.infDist (Q τ) K) :
    ENNReal.ofReal a₀ * edist (Q t₂) (Q 1) ≤ weightedLength w Q 0 1 := by
  rcases ht₂.2.lt_or_eq with hlt1 | hone
  · have hcontf : ContinuousOn (fun τ => Metric.infDist (Q τ) K) (Icc 0 1) :=
      (Metric.continuous_infDist_pt K).comp_continuousOn hQ
    have hfirst : η ≤ Metric.infDist (Q t₂) K :=
      trap_le_of_right hlt1 ((hcontf t₂ ht₂).mono fun τ hτ => ⟨ht₂.1.trans hτ.1.le, hτ.2⟩)
        fun τ hτ => (hafter τ hτ).le
    have hw : ∀ τ ∈ Icc t₂ 1, a₀ ≤ w (Q τ) := by
      intro τ hτ
      rcases hτ.1.lt_or_eq with hlt | heq
      · exact hwoff _ (hafter τ ⟨hlt, hτ.2⟩).le
      · exact hwoff _ (heq ▸ hfirst)
    calc ENNReal.ofReal a₀ * edist (Q t₂) (Q 1)
        ≤ ENNReal.ofReal a₀ * curveLength Q t₂ 1 :=
          mul_le_mul' le_rfl (edist_le_curveLength Q ht₂.2)
      _ ≤ weightedLength w Q t₂ 1 := ofReal_mul_curveLength_le_weightedLength ht₂.2 hw
      _ ≤ weightedLength w Q 0 1 := weightedLength_mono_interval ht₂.1 ht₂.2 le_rfl
  · rw [hone, edist_self, mul_zero]
    exact bot_le

/-- A subsegment of a minimizer that stays in `Y` is a `Y`-confined minimizer. -/
theorem trap_middle_minimal {Z : Type*} [MetricSpace Z] {w : Z → ℝ} {Y : Set Z} {Q : ℝ → Z}
    (hQ : ContinuousOn Q (Icc 0 1)) (hQY : MapsTo Q (Icc 0 1) Y)
    (hmin : weightedLength w Q 0 1 = weylDistOn w univ (Q 0) (Q 1))
    (hfin : weightedLength w Q 0 1 ≠ ⊤) {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    (h2 : t₂ ≤ 1) :
    weightedLength w Q t₁ t₂ = weylDistOn w Y (Q t₁) (Q t₂) := by
  have hsub : Icc t₁ t₂ ⊆ Icc 0 1 := Icc_subset_Icc h0 h2
  apply le_antisymm _ (weylDistOn_le_of_curve h12 (hQ.mono hsub) (hQY.mono_left hsub))
  have hadd1 := weightedLength_add (w := w) (P := Q) h0 h12
  have hadd2 := weightedLength_add (w := w) (P := Q) (h0.trans h12) h2
  have hA_ne : weightedLength w Q 0 t₁ ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (weightedLength_mono_interval le_rfl h0 (h12.trans h2))
  have hC_ne : weightedLength w Q t₂ 1 ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (weightedLength_mono_interval (h0.trans h12) h2 le_rfl)
  have htri : weylDistOn w univ (Q 0) (Q 1) ≤
      weightedLength w Q 0 t₁ + weylDistOn w Y (Q t₁) (Q t₂) + weightedLength w Q t₂ 1 := by
    calc weylDistOn w univ (Q 0) (Q 1)
        ≤ weylDistOn w univ (Q 0) (Q t₂) + weylDistOn w univ (Q t₂) (Q 1) :=
          weylDistOn_triangle _ _ _
      _ ≤ (weylDistOn w univ (Q 0) (Q t₁) + weylDistOn w univ (Q t₁) (Q t₂)) +
            weylDistOn w univ (Q t₂) (Q 1) := add_le_add (weylDistOn_triangle _ _ _) le_rfl
      _ ≤ weightedLength w Q 0 t₁ + weylDistOn w Y (Q t₁) (Q t₂) + weightedLength w Q t₂ 1 := by
          gcongr
          · exact weylDistOn_le_of_curve h0 (hQ.mono (Icc_subset_Icc le_rfl (h12.trans h2)))
              (mapsTo_univ _ _)
          · exact weylDistOn_anti (subset_univ Y)
          · exact weylDistOn_le_of_curve h2 (hQ.mono (Icc_subset_Icc (h0.trans h12) le_rfl))
              (mapsTo_univ _ _)
  rw [← hmin, ← hadd2, ← hadd1] at htri
  have h3 := (ENNReal.add_le_add_iff_right hC_ne).1 htri
  exact (ENNReal.add_le_add_iff_left hA_ne).1 h3

end HigherDimLQGMetric
