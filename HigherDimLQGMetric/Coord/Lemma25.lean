import HigherDimLQGMetric.Coord.ConfinedContinuity

/-! # Uniform convergence of confined weighted distances -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- MA1 Lemma 2.5′(a), with the finiteness correction of ruling M22.
The conclusion uses two additive `ℝ≥0∞` inequalities. -/
theorem lemma25a
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
    (hlocal : ∀ n, ∀ x ∈ K, ∀ y ∈ K, ρ n (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρ n (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρ n (x, y)))
    (hlocalLim : ∀ x ∈ K, ∀ y ∈ K, ρlim (x, y) < δloc →
      ∃ R : I →ᵇ X, (∀ t, R t ∈ closure O) ∧ R 0 = x ∧ R 1 = y ∧
        curveLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v)))
          (Set.IccExtend zero_le_one R) 0 1 = ENNReal.ofReal (ρlim (x, y)))
    (hH : ∀ x ∈ Y, ∀ y ∈ Y,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y =
        weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w K x y)
    (hfin : ∀ x ∈ Y, ∀ y ∈ Y,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ Y, ∀ y ∈ Y,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y' x y ≤
        weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
          ENNReal.ofReal ε ∧
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y ≤
        weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y' x y +
          ENNReal.ofReal ε := by
  have hmodO : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      (∀ n, ∀ u ∈ closure O, ∀ v ∈ closure O,
        ρ n (u, v) < b → dist u v < χ) ∧
      (∀ u ∈ closure O, ∀ v ∈ closure O,
        ρlim (u, v) < b → dist u v < χ) := by
    intro χ hχ
    obtain ⟨b, hb, hbn, hbl⟩ := hmod χ hχ
    exact ⟨b, hb, fun n u hu v hv hs => hbn n u (hOY hu) v (hOY hv) hs,
      fun u hu v hv hs => hbl u (hOY hu) v (hOY hv) hs⟩
  obtain ⟨m, M, hm, hM, hbounds⟩ := compact_positive_weight_bounds hY'c hw hpos
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηsum : ENNReal.ofReal η + ENNReal.ofReal η = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hη.le hη.le]
    congr 1
    dsimp [η]
    ring
  have hmoveUpper : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∀ xs ys : ℕ → X, (∀ k, xs k ∈ Y ∧ ys k ∈ Y) →
      ∀ x ∈ Y, ∀ y ∈ Y,
        Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) →
        ∀ᶠ k in atTop,
          weylDistOnWith (fun u v => ENNReal.ofReal (ρ (ns k) (u, v))) w Y'
              (xs k) (ys k) ≤
            weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y'
              (xs k) (ys k) +
              ENNReal.ofReal ε := by
    intro ns hns xs ys hxs x hx y hy hxsconv hysconv
    let ρs : ℕ → X × X → ℝ := fun k => ρ (ns k)
    have hconvs : TendstoUniformlyOn ρs ρlim atTop (Y' ×ˢ Y') :=
      tendstoUniformlyOn_subseq hconv ns hns
    have hmods : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
        (∀ k, ∀ u ∈ closure O, ∀ v ∈ closure O,
          ρs k (u, v) < b → dist u v < χ) ∧
        (∀ u ∈ closure O, ∀ v ∈ closure O,
          ρlim (u, v) < b → dist u v < χ) := by
      intro χ hχ
      obtain ⟨b, hb, hbn, hbl⟩ := hmodO χ hχ
      exact ⟨b, hb, fun k => hbn (ns k), hbl⟩
    have hmov := lemma25_moving_upper ρs ρlim (fun k => hρ (ns k)) hρlim w
      hKO hOY hOc hY'c hw hpos
      (hconvs.mono (Set.prod_mono hOY hOY)) hmods hδloc
      (fun k => hlocal (ns k)) xs ys x y hxsconv hysconv
      (fun k => ⟨hYK (hxs k).1, hYK (hxs k).2⟩)
      (hYK hx) (hYK hy) (hH x hx y hy) (hfin x hx y hy) hη
    have hcont := confined_distance_endpoint_continuity ρlim hρlim w hOY
      hM hδloc (fun z hz => (hbounds z (hOY hz)).2) hlocalLim
      xs ys x y (fun k => ⟨hYK (hxs k).1, hYK (hxs k).2⟩)
      (hYK hx) (hYK hy) hxsconv hysconv hη
    filter_upwards [hmov, hcont] with k hm hc
    calc
      _ ≤ weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
          ENNReal.ofReal η := hm
      _ ≤ (weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y'
          (xs k) (ys k) + ENNReal.ofReal η) + ENNReal.ofReal η :=
        add_le_add hc.2 le_rfl
      _ = _ := by rw [add_assoc, hηsum]
  have hmoveLower : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∀ xs ys : ℕ → X, (∀ k, xs k ∈ Y ∧ ys k ∈ Y) →
      ∀ x ∈ Y, ∀ y ∈ Y,
        Tendsto xs atTop (𝓝 x) → Tendsto ys atTop (𝓝 y) →
        ∀ᶠ k in atTop,
          weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y'
              (xs k) (ys k) ≤
            weylDistOnWith (fun u v => ENNReal.ofReal (ρ (ns k) (u, v))) w Y'
              (xs k) (ys k) + ENNReal.ofReal ε := by
    intro ns hns xs ys hxs x hx y hy hxsconv hysconv
    let ρs : ℕ → X × X → ℝ := fun k => ρ (ns k)
    have hmods : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
        ∀ k, ∀ u ∈ Y', ∀ v ∈ Y',
          ρs k (u, v) < b → dist u v < χ := by
      intro χ hχ
      obtain ⟨b, hb, hbn, -⟩ := hmod χ hχ
      exact ⟨b, hb, fun k => hbn (ns k)⟩
    have hmov := lemma25_moving_lower hY'c ρs ρlim (fun k => hρ (ns k))
      (tendstoUniformlyOn_subseq hconv ns hns) hmods w hw hpos
      xs ys x y hxsconv hysconv (hfin x hx y hy) hη
    have hcont := confined_distance_endpoint_continuity ρlim hρlim w hOY
      hM hδloc (fun z hz => (hbounds z (hOY hz)).2) hlocalLim
      xs ys x y (fun k => ⟨hYK (hxs k).1, hYK (hxs k).2⟩)
      (hYK hx) (hYK hy) hxsconv hysconv hη
    filter_upwards [hmov, hcont] with k hm hc
    calc
      _ ≤ weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
          ENNReal.ofReal η := hc.1
      _ ≤ (weylDistOnWith (fun u v => ENNReal.ofReal (ρ (ns k) (u, v))) w Y'
          (xs k) (ys k) + ENNReal.ofReal η) + ENNReal.ofReal η :=
        add_le_add hm le_rfl
      _ = _ := by rw [add_assoc, hηsum]
  have hupper := eventually_uniform_on_compact_square hYc
    (fun n x y => weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y' x y ≤
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y +
        ENNReal.ofReal ε) hmoveUpper
  have hlower := eventually_uniform_on_compact_square hYc
    (fun n x y => weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y ≤
      weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y' x y +
        ENNReal.ofReal ε) hmoveLower
  filter_upwards [hupper, hlower] with n hu hl x hx y hy
  exact ⟨hu x hx y hy, hl x hx y hy⟩

end HigherDimLQGMetric
