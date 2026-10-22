import HigherDimLQGMetric.Coord.ConfinedAttainment

/-! # Convergence of near minimizers for confined weighted distances -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- MA1 Lemma 2.5′(b): constant weighted speed and near minimality give an
attaining limit curve. The family assumptions are precisely the coordinate
lower modulus and local realization used in part (a). -/
theorem lemma25b
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n)) (hρlim : IsCoordinate ρlim)
    (w : X → ℝ) {Y K O Y' : Set X}
    (hYc : IsCompact Y) (hY'c : IsCompact Y')
    (hYK : Y ⊆ K) (hKO : K ⊆ closure O) (hOY : closure O ⊆ Y')
    (hOc : IsCompact (closure O))
    (hw : ContinuousOn w Y') (hpos : ∀ z ∈ Y', 0 < w z)
    (hconv : TendstoUniformlyOn ρ ρlim atTop (Y' ×ˢ Y'))
    (hmod : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      (∀ n, ∀ u ∈ Y', ∀ v ∈ Y',
        ρ n (u, v) < b → dist u v < χ) ∧
      (∀ u ∈ Y', ∀ v ∈ Y',
        ρlim (u, v) < b → dist u v < χ))
    {δloc : ℝ} (hδloc : 0 < δloc)
    (hlocal : ∀ n, ∀ a ∈ K, ∀ b ∈ K, ρ n (a, b) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = a ∧ R 1 = b ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ n (a, b)))
    (hlocalLim : ∀ a ∈ K, ∀ b ∈ K, ρlim (a, b) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = a ∧ R 1 = b ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρlim (a, b)))
    (hH : ∀ a ∈ Y, ∀ b ∈ Y,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' a b =
        weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w K a b)
    (hfin : ∀ a ∈ Y, ∀ b ∈ Y,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' a b ≠ ∞)
    (xseq yseq : ℕ → X) (x y : X)
    (hxy : ∀ n, xseq n ∈ Y ∧ yseq n ∈ Y) (hx : x ∈ Y) (hy : y ∈ Y)
    (hxn : Tendsto xseq atTop (𝓝 x)) (hyn : Tendsto yseq atTop (𝓝 y))
    (P : ℕ → I →ᵇ X) (hPY : ∀ n t, P n t ∈ Y')
    (hP0 : ∀ n, P n 0 = xseq n) (hP1 : ∀ n, P n 1 = yseq n)
    (hspeed : ∀ n : ℕ, ∀ s t : I, (s : ℝ) ≤ t →
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) s t ≤
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 *
        ENNReal.ofReal ((t : ℝ) - s))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcost : ∀ n,
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
        (Set.IccExtend zero_le_one (P n)) 0 1 ≤
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y'
        (xseq n) (yseq n) + ENNReal.ofReal (e n)) :
    ∃ Q : I →ᵇ X, (∀ t, Q t ∈ Y') ∧ Q 0 = x ∧ Q 1 = y ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 =
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n t => P (φ n) t) Q atTop := by
  let Wn : ℕ → X → X → ℝ≥0∞ :=
    fun n a b => weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y' a b
  let W : X → X → ℝ≥0∞ :=
    fun a b => weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' a b
  have huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ a ∈ Y, ∀ b ∈ Y,
      Wn n a b ≤ W a b + ENNReal.ofReal ε ∧
      W a b ≤ Wn n a b + ENNReal.ofReal ε := by
    intro ε hε
    exact lemma25a ρ ρlim hρ hρlim w hYc hY'c hYK hKO hOY hOc
      hw hpos hconv hmod hδloc hlocal hlocalLim hH hfin hε
  obtain ⟨m, M, hm, hM, hbounds⟩ := compact_positive_weight_bounds hY'c hw hpos
  have hcont : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      W (xseq n) (yseq n) ≤ W x y + ENNReal.ofReal ε ∧
      W x y ≤ W (xseq n) (yseq n) + ENNReal.ofReal ε := by
    intro ε hε
    exact confined_distance_endpoint_continuity ρlim hρlim w hOY
      hM hδloc (fun z hz => (hbounds z (hOY hz)).2) hlocalLim
      xseq yseq x y (fun n => ⟨hYK (hxy n).1, hYK (hxy n).2⟩)
      (hYK hx) (hYK hy) hxn hyn hε
  have hD : Tendsto (fun n => Wn n (xseq n) (yseq n)) atTop (𝓝 (W x y)) :=
    confined_distance_tendsto_of_uniform_bounds Wn W xseq yseq x y hxy huni hcont
  have hlower : ∀ Q : I →ᵇ X, (∀ t, Q t ∈ Y') → Q 0 = x → Q 1 = y →
      W x y ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 := by
    intro Q hQY hQ0 hQ1
    exact weylDistOnWith_le
      (continuous_IccExtend_iff.mpr Q.continuous).continuousOn
      (by rw [Set.IccExtend_of_mem _ _ (show (0 : ℝ) ∈ Icc 0 1 from
        ⟨le_rfl, zero_le_one⟩)]; exact hQ0)
      (by rw [Set.IccExtend_of_mem _ _ (show (1 : ℝ) ∈ Icc 0 1 from
        ⟨zero_le_one, le_rfl⟩)]; exact hQ1)
      (fun t ht => by rw [Set.IccExtend_of_mem _ _ ht]; exact hQY ⟨t, ht⟩)
  exact confined_attainment_of_distance_convergence hY'c ρ ρlim hρ hconv
    (fun χ hχ => by
      obtain ⟨b, hb, hbn, -⟩ := hmod χ hχ
      exact ⟨b, hb, hbn⟩)
    w hw hpos xseq yseq x y hxn hyn
    (fun n => Wn n (xseq n) (yseq n)) (W x y) hD (hfin x hx y hy)
    P hPY hP0 hP1 hspeed e he hcost hlower

end HigherDimLQGMetric
