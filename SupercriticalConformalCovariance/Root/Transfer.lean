import SupercriticalConformalCovariance.Domain.Geometry

/-!
# Lemma 7.1, deterministic core: transfer of a comparison under Weyl scaling

Paper l. 518–530 (Lemma 7.1): "Simultaneous continuous Weyl scaling holds … for every continuous
correction at once. Hence adding the random continuous difference transfers the inequality pathwise
… Under the conformal map, the same correction is composed with the inverse map, so corresponding
path weights agree exactly."

On one sample: carriers `X = (ℂ, D₁)` (source) and `Y = (ℂ, D₂)` (target), internal weighted metrics
`δ₁ = (w₁·D₁)_S`, `δ₂ = (w₂·D₂)_T`, and a map `Φ : S → T` with `δ₂(Φ x, Φ y) ≤ δ₁(x, y)`. Then every
further Weyl scaling by weights that agree under `Φ` preserves the inequality:
`(g₂·δ₂)_T(Φ x, Φ y) ≤ (g₁·δ₁)_S(x, y)` (`weylDistOnWith_transfer`). The only analytic point is that
`Φ ∘ P` is again a `D₂`-continuous curve, which follows from the two local topology lemmas of
`HigherDimLQGMetric` (`exists_weylDistOn_lt_of_isLocallyLengthOn`, `exists_edist_lt_of_weylDistOn_lt`).
`isLocallyLengthOn_SV` supplies the local length property of `(ℂ, D)` on an open set from the
length-space axiom.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.Root

open HigherDimLQGMetric
open LQGMetric.MetricGeometry (curveLength edist_le_curveLength curveLength_mono
  curveLength_comp_of_continuousOn_monotoneOn)
open SupercriticalLQGUniqueness (LSCMetric)

section Abstract

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- **Weyl transfer** (Lemma 7.1, pathwise). -/
theorem weylDistOnWith_transfer {S : Set X} {T : Set Y}
    {w₁ g₁ : X → ℝ} {w₂ g₂ : Y → ℝ} (hloc : IsLocallyLengthOn S)
    (hw₁ : ∀ x ∈ S, ContinuousAt w₁ x) (hw₂ : ∀ y ∈ T, ContinuousAt w₂ y)
    (hpos₂ : ∀ y ∈ T, 0 < w₂ y) {Φ : X → Y} (hΦ : MapsTo Φ S T)
    (hle : ∀ x ∈ S, ∀ y ∈ S, weylDistOn w₂ T (Φ x) (Φ y) ≤ weylDistOn w₁ S x y)
    (hg : ∀ x ∈ S, g₂ (Φ x) = g₁ x) (x y : X) :
    weylDistOnWith (weylDistOn w₂ T) g₂ T (Φ x) (Φ y) ≤
      weylDistOnWith (weylDistOn w₁ S) g₁ S x y := by
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun h0 => le_iInf fun h1 =>
    le_iInf fun hPS => ?_
  -- `Φ ∘ P` is a curve in `T`
  have hc : ContinuousOn (Φ ∘ P) (Icc 0 1) := by
    intro s hs
    rw [EMetric.continuousWithinAt_iff]
    intro ε hε
    have hT' : Φ (P s) ∈ T := hΦ (hPS hs)
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ :=
      exists_edist_lt_of_weylDistOn_lt (U := T) (hw₂ _ hT') (hpos₂ _ hT') hε
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
      exists_weylDistOn_lt_of_isLocallyLengthOn hloc (hPS hs) (hw₁ _ (hPS hs)) hδ₂
    obtain ⟨ρ, hρ, hρ'⟩ := EMetric.continuousWithinAt_iff.1 (hP s hs) δ₁ hδ₁
    refine ⟨ρ, hρ, fun t ht hts => ?_⟩
    have hPt : edist (P s) (P t) < δ₁ := by
      rw [edist_comm]; exact hρ' ht hts
    have h1' := hδ₁' (P t) hPt
    have h2' := (hle _ (hPS hs) _ (hPS ht)).trans_lt h1'
    rw [edist_comm]
    exact hδ₂' _ h2'
  refine iInf_le_of_le (Φ ∘ P) <| iInf_le_of_le hc <| iInf_le_of_le (by simp [h0]) <|
    iInf_le_of_le (by simp [h1]) <| iInf_le_of_le (fun t ht => hΦ (hPS ht)) ?_
  unfold weightedLengthWith
  refine partitionSup_mono fun u v hu huv hv => ?_
  have hinf : infAlong g₂ (Φ ∘ P) u v = infAlong g₁ P u v := by
    unfold infAlong
    refine iInf_congr fun s => iInf_congr fun hs => ?_
    rw [Function.comp_apply, hg _ (hPS ⟨hu.trans hs.1, hs.2.trans hv⟩)]
  rw [hinf]
  refine mul_le_mul' le_rfl ?_
  unfold curveLengthWith
  exact partitionSup_mono fun s t hs hst ht =>
    hle _ (hPS ⟨hu.trans hs, (hst.trans ht).trans hv⟩) _
      (hPS ⟨(hu.trans hs).trans hst, ht.trans hv⟩)

end Abstract

/-! ## The local length property on an open subset of a length space -/

/-- An open subset of a length space `(ℂ, D)` is locally length. -/
theorem isLocallyLengthOn_of_isLengthSpace (D : LSCMetric) (hL : D.IsLengthSpace)
    {S : Set D.Space} (hS : IsOpen S) : IsLocallyLengthOn S := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hball⟩ := EMetric.isOpen_iff.1 hS x₀ hx₀
  set r : ℝ≥0∞ := min (ε / 4) 1 with hr
  have hr0 : 0 < r := lt_min (ENNReal.div_pos hε.ne' (by norm_num)) one_pos
  have hrtop : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨r, hr0, fun z hz => hball ?_, ?_⟩
  · rw [Metric.mem_eball] at hz ⊢
    refine hz.trans_le ?_
    calc 4 * r ≤ 4 * (ε / 4) := mul_le_mul' le_rfl (min_le_left _ _)
      _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  intro x y hx hy ε' hε'
  have hxy : edist x y < 2 * r := by
    calc edist x y ≤ edist x x₀ + edist x₀ y := edist_triangle _ _ _
      _ < r + r := by rw [edist_comm] at hx; exact ENNReal.add_lt_add hx hy
      _ = 2 * r := (two_mul r).symm
  have hA : edist x₀ x + edist x y < 3 * r := by
    calc edist x₀ x + edist x y < r + 2 * r := ENNReal.add_lt_add hx hxy
      _ = 3 * r := by ring
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hA
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε'
  set δ : NNReal := min δ₁ δ₂ with hδ
  have hδ0 : (0 : ℝ) < δ := by
    show (0 : ℝ) < ((min δ₁ δ₂ : NNReal) : ℝ)
    exact_mod_cast lt_min hδ₁0 (ENNReal.coe_pos.1 hδ₂0)
  have hfin : D (x, y) < ⊤ := hxy.trans (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hrtop.lt_top)
  obtain ⟨P', a, b, hcurve, hPa, hPb, hlen⟩ := hL x y hfin (δ : ℝ) hδ0
  have hab : a ≤ b := hcurve.1
  set τ : ℝ → ℝ := fun t => a + t * (b - a) with hτ
  have hτc : ContinuousOn τ (Icc 0 1) := (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
  have hτm : MonotoneOn τ (Icc 0 1) := fun s _ t _ hst => by
    simp only [hτ]; nlinarith [sub_nonneg.2 hab]
  have hτmaps : MapsTo τ (Icc 0 1) (Icc a b) := fun t ht => by
    simp only [hτ, mem_Icc]
    constructor <;> nlinarith [sub_nonneg.2 hab, ht.1, ht.2]
  set P : ℝ → D.Space := (D.pt ∘ P') ∘ τ with hPdef
  have hP0 : P 0 = x := by simp [hPdef, hτ, hPa]; rfl
  have hP1 : P 1 = y := by simp [hPdef, hτ, hPb]; rfl
  have hlenP : curveLength P 0 1 = D.len P' a b := by
    rw [hPdef, curveLength_comp_of_continuousOn_monotoneOn _ zero_le_one hτc hτm]
    simp [hτ]
    rfl
  have hlenP' : curveLength P 0 1 ≤ edist x y + (δ : ℝ≥0∞) := by
    rw [hlenP]
    refine hlen.trans (add_le_add le_rfl ?_)
    rw [ENNReal.ofReal_coe_nnreal]
  refine ⟨P, hcurve.2.comp hτc hτmaps, hP0, hP1, fun t ht => ?_, ?_⟩
  · rw [Metric.mem_eball]
    calc edist (P t) x₀ = edist x₀ (P t) := edist_comm _ _
      _ ≤ edist x₀ x + edist x (P t) := edist_triangle _ _ _
      _ ≤ edist x₀ x + curveLength P 0 1 := by
          refine add_le_add le_rfl ?_
          rw [← hP0]
          exact (edist_le_curveLength P ht.1).trans (curveLength_mono P le_rfl ht.2)
      _ ≤ edist x₀ x + (edist x y + (δ₁ : ℝ≥0∞)) :=
          add_le_add le_rfl (hlenP'.trans (add_le_add le_rfl (by exact_mod_cast min_le_left _ _)))
      _ = edist x₀ x + edist x y + δ₁ := (add_assoc _ _ _).symm
      _ < 3 * r := hδ₁
  · refine hlenP'.trans (add_le_add le_rfl ?_)
    exact (by exact_mod_cast min_le_right _ _ : ((δ : NNReal) : ℝ≥0∞) ≤ δ₂).trans hδ₂.le

end SupercriticalConformalCovariance.Root
