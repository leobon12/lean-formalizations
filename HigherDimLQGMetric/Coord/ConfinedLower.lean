import HigherDimLQGMetric.Coord.ConfinedUpper

/-! # Lower bound for confined weighted distances -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

/-- MA1 A7's lower bound for converging endpoints.  It needs only the
compactness and common inverse-modulus properties on the confinement set. -/
theorem lemma25_moving_lower
    {X : Type*} [MetricSpace X] {Y' : Set X} (hYc : IsCompact Y')
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρ : ∀ n, IsCoordinate (ρ n))
    (hconv : TendstoUniformlyOn ρ ρlim atTop (Y' ×ˢ Y'))
    (hmod : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      ∀ n, ∀ u ∈ Y', ∀ v ∈ Y',
        ρ n (u, v) < b → dist u v < χ)
    (w : X → ℝ) (hw : ContinuousOn w Y') (hpos : ∀ z ∈ Y', 0 < w z)
    (xn yn : ℕ → X) (x y : X)
    (hxn : Tendsto xn atTop (𝓝 x)) (hyn : Tendsto yn atTop (𝓝 y))
    (hWfin : weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y ≤
        weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y'
          (xn n) (yn n) + ENNReal.ofReal ε := by
  let W : ℝ≥0∞ := weylDistOnWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w Y' x y
  let Wn : ℕ → ℝ≥0∞ := fun n =>
    weylDistOnWith (fun u v => ENNReal.ofReal (ρ n (u, v))) w Y' (xn n) (yn n)
  by_contra hnot
  have hbadFreq : ∃ᶠ n in atTop, ¬ W ≤ Wn n + ENNReal.ofReal ε := by
    exact Filter.not_eventually.mp hnot
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hbadFreq
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η + η ≤ ε := by dsimp [η]; linarith
  have hWpos : 0 < W := by
    have hb : Wn (φ 0) + ENNReal.ofReal ε < W := lt_of_not_ge (hbad 0)
    exact ((ENNReal.ofReal_pos.mpr hε).trans_le le_add_self).trans hb
  obtain ⟨m, M, hm, hM, hbounds⟩ := compact_positive_weight_bounds hYc hw hpos
  have hWrep : W = ENNReal.ofReal W.toReal := (ENNReal.ofReal_toReal hWfin).symm
  let B : ℝ := W.toReal + η
  have hB : 0 ≤ B := add_nonneg ENNReal.toReal_nonneg hη.le
  have hWplus : W + ENNReal.ofReal η = ENNReal.ofReal B := by
    rw [hWrep, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hη.le]
  have hQexists : ∀ k : ℕ, ∃ Q : I →ᵇ X,
      (∀ t, Q t ∈ Y') ∧ Q 0 = xn (φ k) ∧ Q 1 = yn (φ k) ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (φ k) (u, v))) w
        (Set.IccExtend zero_le_one Q) 0 1 < Wn (φ k) + ENNReal.ofReal η := by
    intro k
    have hWnfin : Wn (φ k) ≠ ∞ := by
      have hb : Wn (φ k) + ENNReal.ofReal ε < W := lt_of_not_ge (hbad k)
      exact ne_top_of_lt ((le_self_add).trans_lt hb)
    exact exists_near_confined_competitor _ w Y' _ _ hWnfin hη
  choose Q hQmem hQ0 hQ1 hQcost using hQexists
  have hQcostBound (k : ℕ) :
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (φ k) (u, v))) w
        (Set.IccExtend zero_le_one (Q k)) 0 1 ≤ ENNReal.ofReal B := by
    have hb : Wn (φ k) + ENNReal.ofReal ε < W := lt_of_not_ge (hbad k)
    have hWnle : Wn (φ k) ≤ W := (le_self_add).trans hb.le
    exact (hQcost k).le.trans ((add_le_add hWnle le_rfl).trans_eq hWplus)
  have hQlenfin (k : ℕ) :
      curveLengthWith (fun u v => ENNReal.ofReal (ρ (φ k) (u, v)))
        (Set.IccExtend zero_le_one (Q k)) 0 1 ≠ ∞ := by
    have hcostfin : weightedLengthWith (fun u v => ENNReal.ofReal (ρ (φ k) (u, v))) w
        (Set.IccExtend zero_le_one (Q k)) 0 1 ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hQcostBound k)
    exact curveLengthWith_ne_top_of_weightedLengthWith_ne_top zero_le_one hm
      (fun t ht => by simpa only [Set.IccExtend_of_mem _ _ ht] using
        (hbounds _ (hQmem k ⟨t, ht⟩)).1) hcostfin
  have hQlenBound (k : ℕ) :
      (curveLengthWith (fun u v => ENNReal.ofReal (ρ (φ k) (u, v)))
        (Set.IccExtend zero_le_one (Q k)) 0 1).toReal ≤ B / m := by
    let length : ℝ≥0∞ := curveLengthWith (fun u v => ENNReal.ofReal (ρ (φ k) (u, v)))
      (Set.IccExtend zero_le_one (Q k)) 0 1
    have hlow := ofReal_mul_curveLengthWith_le_weightedLengthWith
      (δ := fun u v => ENNReal.ofReal (ρ (φ k) (u, v)))
      (P := Set.IccExtend zero_le_one (Q k)) zero_le_one (fun t ht => by
        simpa only [Set.IccExtend_of_mem _ _ ht] using
          (hbounds _ (hQmem k ⟨t, ht⟩)).1)
    have hlenrep : length = ENNReal.ofReal length.toReal :=
      (ENNReal.ofReal_toReal (hQlenfin k)).symm
    have hreal : m * length.toReal ≤ B := by
      have h : ENNReal.ofReal (m * length.toReal) ≤ ENNReal.ofReal B := by
        rw [ENNReal.ofReal_mul hm.le, ← hlenrep]
        exact hlow.trans (hQcostBound k)
      exact (ENNReal.ofReal_le_ofReal_iff hB).1 h
    exact (le_div_iff₀ hm).2 (by nlinarith)
  have hPexists : ∀ k : ℕ, ∃ P : I →ᵇ X,
      (∀ t, P t ∈ Y') ∧ P 0 = xn (φ k) ∧ P 1 = yn (φ k) ∧
      (∀ s t : I, ρ (φ k) (P s, P t) ≤ (B / m) * dist s t) ∧
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (φ k) (u, v))) w
          (Set.IccExtend zero_le_one P) 0 1 =
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (φ k) (u, v))) w
          (Set.IccExtend zero_le_one (Q k)) 0 1 := by
    intro k
    obtain ⟨P, hPY, hP0, hP1, hspeed, hweight⟩ :=
      coordinate_reparam_bounded (ρ (φ k)) (hρ (φ k)) w (Q k) (hQmem k) (hQlenfin k)
    refine ⟨P, hPY, hP0.trans (hQ0 k), hP1.trans (hQ1 k), ?_, hweight⟩
    intro s t
    exact (hspeed s t).trans
      (mul_le_mul_of_nonneg_right (hQlenBound k) (dist_nonneg))
  choose P hPY hP0 hP1 hPspeed hPweight using hPexists
  have hmod' : ∀ χ : ℝ, 0 < χ → ∃ b : ℝ, 0 < b ∧
      ∀ k, ∀ u ∈ Y', ∀ v ∈ Y',
        ρ (φ k) (u, v) < b → dist u v < χ := by
    intro χ hχ
    obtain ⟨b, hb, hbn⟩ := hmod χ hχ
    exact ⟨b, hb, fun k u hu v hv hsmall => hbn (φ k) u hu v hv hsmall⟩
  obtain ⟨R, hRY, ψ, hψ, hPconv, -, -, hweightedLSC⟩ :=
    lemmaCC zero_le_one hYc (fun k => ρ (φ k)) ρlim
      (fun k => (hρ (φ k)).continuous.continuousOn)
      (by
        rw [tendstoUniformlyOn_iff_tendsto] at hconv ⊢
        exact hconv.comp ((hφtop.comp tendsto_fst).prodMk tendsto_snd))
      (B / m) P hPY
      (fun χ hχ => hmod' χ hχ) hPspeed
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hR0 : R 0 = x :=
    tendsto_nhds_unique (hPconv.tendsto_at 0)
      (by simpa only [Function.comp_def, hP0] using hxn.comp (hφtop.comp hψtop))
  have hR1 : R 1 = y :=
    tendsto_nhds_unique (hPconv.tendsto_at 1)
      (by simpa only [Function.comp_def, hP1] using hyn.comp (hφtop.comp hψtop))
  have hRlower : W ≤ weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
      (Set.IccExtend zero_le_one R) 0 1 :=
    weylDistOnWith_le (continuous_IccExtend_iff.mpr R.continuous).continuousOn
      (by rw [Set.IccExtend_of_mem _ _ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)]; exact hR0)
      (by rw [Set.IccExtend_of_mem _ _ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]; exact hR1)
      (fun t ht => by rw [Set.IccExtend_of_mem _ _ ht]; exact hRY ⟨t, ht⟩)
  have hcW : (ENNReal.ofReal η) ≤ W := by
    have hb : Wn (φ 0) + ENNReal.ofReal ε < W := lt_of_not_ge (hbad 0)
    have hηε' : ENNReal.ofReal η ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith [hηε])
    exact (hηε'.trans (le_add_self : ENNReal.ofReal ε ≤
      Wn (φ 0) + ENNReal.ofReal ε)).trans hb.le
  have hcostUpper (k : ℕ) :
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (φ (ψ k)) (u, v))) w
        (Set.IccExtend zero_le_one (P (ψ k))) 0 1 ≤ W - ENNReal.ofReal η := by
    have hb : Wn (φ (ψ k)) + ENNReal.ofReal ε < W := lt_of_not_ge (hbad (ψ k))
    have hc : weightedLengthWith (fun u v => ENNReal.ofReal (ρ (φ (ψ k)) (u, v))) w
        (Set.IccExtend zero_le_one (P (ψ k))) 0 1 + ENNReal.ofReal η ≤ W := by
      rw [hPweight (ψ k)]
      have hηsum : ENNReal.ofReal η + ENNReal.ofReal η ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hη.le hη.le]
        exact ENNReal.ofReal_le_ofReal hηε
      calc
        _ ≤ Wn (φ (ψ k)) + ENNReal.ofReal η + ENNReal.ofReal η :=
          add_le_add (hQcost (ψ k)).le le_rfl
        _ ≤ Wn (φ (ψ k)) + ENNReal.ofReal ε := by
          rw [add_assoc]
          exact add_le_add le_rfl hηsum
        _ ≤ W := hb.le
    exact (ENNReal.le_sub_iff_add_le_right ENNReal.ofReal_ne_top hcW).2 hc
  have hRupper : weightedLengthWith (fun u v => ENNReal.ofReal (ρlim (u, v))) w
      (Set.IccExtend zero_le_one R) 0 1 ≤ W - ENNReal.ofReal η := by
    calc
      _ ≤ liminf (fun k => weightedLengthWith
          (fun u v => ENNReal.ofReal (ρ (φ (ψ k)) (u, v))) w
          (Set.IccExtend zero_le_one (P (ψ k))) 0 1) atTop :=
        hweightedLSC w hw le_rfl zero_le_one le_rfl
      _ ≤ liminf (fun _ : ℕ => W - ENNReal.ofReal η) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall hcostUpper)
      _ = W - ENNReal.ofReal η := tendsto_const_nhds.liminf_eq
  have hWlt : W - ENNReal.ofReal η < W :=
    ENNReal.sub_lt_self hWfin (ne_of_gt hWpos) (ne_of_gt (ENNReal.ofReal_pos.mpr hη))
  exact (not_lt_of_ge (hRlower.trans hRupper)) hWlt

end HigherDimLQGMetric
