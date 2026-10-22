import HigherDimLQGMetric.Coord.RecoveryEventual

/-! # Upper bound for confined weighted distances -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- For fixed endpoints, MA1 A7's upper bound follows from the quantitative
recovery lemma and the shared inverse modulus. -/
theorem lemma25_fixed_upper
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n)) (hρlim : IsCoordinate ρlim)
    (w : X → ℝ) {K O Y' : Set X}
    (hKO : K ⊆ closure O) (hOY : closure O ⊆ Y')
    (hOc : IsCompact (closure O)) (hYc : IsCompact Y')
    (hw : ContinuousOn w Y') (hpos : ∀ z ∈ Y', 0 < w z)
    (hconv : TendstoUniformlyOn ρ ρlim atTop (closure O ×ˢ closure O))
    (hmod : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      (∀ n, ∀ u ∈ closure O, ∀ v ∈ closure O,
        ρ n (u, v) < b → dist u v < χ) ∧
      (∀ u ∈ closure O, ∀ v ∈ closure O,
        ρlim (u, v) < b → dist u v < χ))
    {δloc : ℝ} (hδloc : 0 < δloc)
    (hlocal : ∀ n, ∀ x ∈ K, ∀ y ∈ K, ρ n (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ n (x, y)))
    (x y : X)
    (hH : weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y =
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w K x y)
    (hfin : weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y' x y ≤
        weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
          ENNReal.ofReal ε := by
  let W := weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y
  have hKfin : weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w K x y ≠ ∞ := by
    rw [← hH]
    exact hfin
  obtain ⟨Q, hQK, hQ0, hQ1, hQcost⟩ :=
    exists_near_confined_competitor (fun u v => ENNReal.ofReal (ρlim (u, v)))
      w K x y hKfin (by positivity : 0 < ε / 4)
  have hQcost' : weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
      (Set.IccExtend zero_le_one Q) 0 1 < W + ENNReal.ofReal (ε / 4) := by
    simpa [W, hH] using hQcost
  have hQcostfin : weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
      (Set.IccExtend zero_le_one Q) 0 1 ≠ ∞ := by
    apply ne_top_of_lt
    exact hQcost'.trans_le (le_top)
  obtain ⟨m, M, hm, hM, hbounds⟩ :=
    compact_positive_weight_bounds hYc hw hpos
  have hQlenfin : curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 ≠ ∞ :=
    curveLengthWith_ne_top_of_weightedLengthWith_ne_top zero_le_one hm
      (fun t ht => by simpa only [Set.IccExtend_of_mem _ _ ht] using
        (hbounds _ (hOY (hKO (hQK ⟨t, ht⟩)))).1) hQcostfin
  let L : ℝ := (curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
    (Set.IccExtend zero_le_one Q) 0 1).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hQlen : curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
      (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal L := by
    exact le_of_eq (ENNReal.ofReal_toReal hQlenfin).symm
  have hMpos : 0 < M :=
    lt_of_lt_of_le hm ((hbounds (Q 0) (hOY (hKO (hQK 0)))).1.trans
      (hbounds (Q 0) (hOY (hKO (hQK 0)))).2)
  let Ω : ℝ := min M (ε / (16 * (L + 1)))
  have hΩ : 0 < Ω := by dsimp [Ω]; positivity
  have hΩerr : 2 * Ω * L ≤ ε / 8 := by
    have hden : 0 < 16 * (L + 1) := by positivity
    have hfrac : (2 * L * ε) / (16 * (L + 1)) ≤ ε / 8 := by
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg hε.le (by linarith : 0 ≤ L + 1)]
    have hΩle : Ω ≤ ε / (16 * (L + 1)) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hΩle (by positivity : 0 ≤ 2 * L)
    calc
      2 * Ω * L = Ω * (2 * L) := by ring
      _ ≤ (ε / (16 * (L + 1))) * (2 * L) := hmul
      _ = (2 * L * ε) / (16 * (L + 1)) := by ring
      _ ≤ ε / 8 := hfrac
  have hwOc : ContinuousOn w (closure O) := hw.mono hOY
  obtain ⟨χ, hχ, hosc⟩ :=
    Metric.uniformContinuousOn_iff_le.mp
      (hOc.uniformContinuousOn_of_continuous hwOc) Ω hΩ
  obtain ⟨b, hb, hmodn, hmodlim⟩ := hmod χ hχ
  let δ : ℝ := min (b / 4) (δloc / 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδb : 2 * δ < b := by dsimp [δ]; linarith [min_le_left (b / 4) (δloc / 4)]
  have hδlocal : 2 * δ < δloc := by dsimp [δ]; linarith [min_le_right (b / 4) (δloc / 4)]
  have hInvlim : ∀ u ∈ closure O, ∀ v ∈ closure O,
      ρlim (u, v) ≤ 2 * δ → dist u v ≤ χ := by
    intro u hu v hv huv
    exact (hmodlim u hu v hv (huv.trans_lt hδb)).le
  have hInvn : ∀ n, ∀ u ∈ closure O, ∀ v ∈ closure O,
      ρ n (u, v) ≤ 2 * δ → dist u v ≤ χ := by
    intro n u hu v hv huv
    exact (hmodn n u hu v hv (huv.trans_lt hδb)).le
  have hOsc : ∀ u ∈ closure O, ∀ v ∈ closure O,
      dist u v ≤ χ → |w u - w v| ≤ Ω := by
    intro u hu v hv huv
    simpa [Real.dist_eq] using (hosc u hu v hv huv)
  let C : ℝ := 2 * M * (L / δ + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let e : ℝ := min δ (ε / (4 * (C + 1)))
  have he : 0 < e := by dsimp [e]; positivity
  have heδ : e ≤ δ := min_le_left _ _
  have heC : C * e ≤ ε / 4 := by
    have he' : e ≤ ε / (4 * (C + 1)) := min_le_right _ _
    have hden : 0 < 4 * (C + 1) := by positivity
    have hbound : C * (ε / (4 * (C + 1))) ≤ ε / 4 := by
      have hfrac : (C * ε) / (4 * (C + 1)) ≤ ε / 4 := by
        apply (div_le_iff₀ hden).2
        nlinarith [mul_nonneg hε.le (by linarith : 0 ≤ C + 1)]
      convert hfrac using 1; ring
    exact (mul_le_mul_of_nonneg_left he' hC).trans hbound
  have hWerr : 0 ≤ 2 * Ω * L + 2 * M * (L / δ + 1) * e := by
    dsimp [Ω]; positivity
  have herr : ε / 4 + (2 * Ω * L + 2 * M * (L / δ + 1) * e) ≤ ε := by
    dsimp [C] at heC
    nlinarith [hΩerr]
  have hupper := lemma24_eventual_recovery ρ ρlim hρ hρlim w hKO hconv
    hL hδ hδlocal hχ.le hΩ.le (min_le_left _ _) hInvlim hInvn
    (fun z hz => ⟨by linarith [(hbounds z (hOY hz)).1], (hbounds z (hOY hz)).2⟩)
    hOsc hlocal Q hQK hQlen he heδ
  filter_upwards [hupper] with n hn
  have hresult : weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y'
      (Q 0) (Q 1) ≤ W + ENNReal.ofReal ε := by
    calc
    weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y' (Q 0) (Q 1)
        ≤ weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w
            (closure O) (Q 0) (Q 1) :=
          weylDistOnWith_anti_set _ _ hOY _ _
    _ ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
          (Set.IccExtend zero_le_one Q) 0 1 +
          ENNReal.ofReal (2 * Ω * L + 2 * M * (L / δ + 1) * e) := hn
    _ ≤ W + ENNReal.ofReal (ε / 4) +
          ENNReal.ofReal (2 * Ω * L + 2 * M * (L / δ + 1) * e) :=
        add_le_add hQcost'.le le_rfl
    _ ≤ W + ENNReal.ofReal ε := by
      rw [add_assoc, ← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 4) hWerr]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal herr)
  simpa [W, hQ0, hQ1] using hresult

/-- Upper bound with moving endpoints in the compact inner set. -/
theorem lemma25_moving_upper
    {X : Type*} [MetricSpace X]
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n)) (hρlim : IsCoordinate ρlim)
    (w : X → ℝ) {K O Y' : Set X}
    (hKO : K ⊆ closure O) (hOY : closure O ⊆ Y')
    (hOc : IsCompact (closure O)) (hYc : IsCompact Y')
    (hw : ContinuousOn w Y') (hpos : ∀ z ∈ Y', 0 < w z)
    (hconv : TendstoUniformlyOn ρ ρlim atTop (closure O ×ˢ closure O))
    (hmod : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      (∀ n, ∀ u ∈ closure O, ∀ v ∈ closure O,
        ρ n (u, v) < b → dist u v < χ) ∧
      (∀ u ∈ closure O, ∀ v ∈ closure O,
        ρlim (u, v) < b → dist u v < χ))
    {δloc : ℝ} (hδloc : 0 < δloc)
    (hlocal : ∀ n, ∀ x ∈ K, ∀ y ∈ K, ρ n (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ n (x, y)))
    (xn yn : ℕ → X) (x y : X)
    (hxn : Tendsto xn atTop (𝓝 x)) (hyn : Tendsto yn atTop (𝓝 y))
    (hmem : ∀ n, xn n ∈ K ∧ yn n ∈ K) (hx : x ∈ K) (hy : y ∈ K)
    (hH : weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y =
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w K x y)
    (hfin : weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y'
          (xn n) (yn n) ≤
        weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
          ENNReal.ofReal ε := by
  obtain ⟨m, M, hm, hM, hbounds⟩ := compact_positive_weight_bounds hYc hw hpos
  have hnearx : Tendsto (fun n => ρ n (xn n, x)) atTop (𝓝 0) := by
    simpa [hρlim.metric.self_eq_zero] using
      coordinate_moving_pair_tendsto ρ ρlim hρlim hconv xn (fun _ => x) x x
        hxn tendsto_const_nhds (hKO hx) (hKO hx)
        (fun n => ⟨hKO (hmem n).1, hKO hx⟩)
  have hneary : Tendsto (fun n => ρ n (y, yn n)) atTop (𝓝 0) := by
    simpa [hρlim.metric.self_eq_zero] using
      coordinate_moving_pair_tendsto ρ ρlim hρlim hconv (fun _ => y) yn y y
        tendsto_const_nhds hyn (hKO hy) (hKO hy)
        (fun n => ⟨hKO hy, hKO (hmem n).2⟩)
  let η : ℝ := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  have hfixed := lemma25_fixed_upper ρ ρlim hρ hρlim w hKO hOY hOc hYc
    hw hpos hconv hmod hδloc hlocal x y hH hfin hη
  have hnearxCost : ∀ᶠ n in atTop,
      ENNReal.ofReal (M * ρ n (xn n, x)) ≤ ENNReal.ofReal η := by
    have ht : Tendsto (fun n => ENNReal.ofReal (M * ρ n (xn n, x))) atTop
        (𝓝 (0 : ℝ≥0∞)) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hnearx)
    exact (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))).mono
      (fun n hn => hn.le)
  have hnearyCost : ∀ᶠ n in atTop,
      ENNReal.ofReal (M * ρ n (y, yn n)) ≤ ENNReal.ofReal η := by
    have ht : Tendsto (fun n => ENNReal.ofReal (M * ρ n (y, yn n))) atTop
        (𝓝 (0 : ℝ≥0∞)) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_const_nhds.mul hneary)
    exact (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))).mono
      (fun n hn => hn.le)
  have hshortx : ∀ᶠ n in atTop, ρ n (xn n, x) < δloc :=
    hnearx.eventually (gt_mem_nhds hδloc)
  have hshorty : ∀ᶠ n in atTop, ρ n (y, yn n) < δloc :=
    hneary.eventually (gt_mem_nhds hδloc)
  filter_upwards [hfixed, hnearxCost, hnearyCost, hshortx, hshorty] with n
    hfixedn hxc hyc hsx hsy
  let E : X → X → ℝ≥0∞ := fun u v => ENNReal.ofReal (ρ n (u, v))
  let D : X → X → ℝ≥0∞ := weylDistOnWith E w Y'
  have hxbound : D (xn n) x ≤ ENNReal.ofReal (M * ρ n (xn n, x)) :=
    confined_short_connector_bound (ρ n) w hOY hM
      (fun z hz => (hbounds z (hOY hz)).2)
      (hlocal n (xn n) (hmem n).1 x hx hsx)
  have hybound : D y (yn n) ≤ ENNReal.ofReal (M * ρ n (y, yn n)) :=
    confined_short_connector_bound (ρ n) w hOY hM
      (fun z hz => (hbounds z (hOY hz)).2)
      (hlocal n y hy (yn n) (hmem n).2 hsy)
  have htri := weylDistOnWith_triangle E (ofReal_metric_triangle (hρ n).metric) w Y'
  have hηsum : ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hη.le hη.le,
      ← ENNReal.ofReal_add (by positivity : 0 ≤ η + η) hη.le]
    congr 1
    dsimp [η]
    ring
  calc
    D (xn n) (yn n) ≤ D (xn n) x + D x (yn n) := htri _ _ _
    _ ≤ D (xn n) x + (D x y + D y (yn n)) :=
      add_le_add le_rfl (htri x y (yn n))
    _ ≤ ENNReal.ofReal η +
        ((weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
          ENNReal.ofReal η) + ENNReal.ofReal η) := by
      exact add_le_add (hxbound.trans hxc)
        (add_le_add hfixedn (hybound.trans hyc))
    _ = weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
        ENNReal.ofReal ε := by
      calc
        _ = weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
            (ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η) := by ac_rfl
        _ = _ := by rw [hηsum]

end HigherDimLQGMetric
