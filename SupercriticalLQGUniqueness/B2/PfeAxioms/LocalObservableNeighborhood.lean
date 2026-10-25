import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaSandwich

 







set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

def neighborhoodInternal (E : LSCMetric) (V : Set ℂ)
    (x y : V) (ρ : ℝ) : ℝ≥0∞ :=
  ⨅ (u : V) (_ : dist (u : ℂ) x < ρ),
    ⨅ (v : V) (_ : dist (v : ℂ) y < ρ), E.internal V (u, v)

def lowerNeighborhoodObservable (G : ℕ → LSCMetric) (V : Set ℂ)
    (x y : V) : ℝ≥0∞ :=
  ⨆ k : ℕ, liminf
    (fun n => neighborhoodInternal (G n) V x y (1 / (k + 1 : ℝ))) atTop

theorem exists_pair_of_neighborhoodInternal_lt
    (E : LSCMetric) {V : Set ℂ} (x y : V) {ρ : ℝ} {C : ℝ≥0∞}
    (h : neighborhoodInternal E V x y ρ < C) :
    ∃ u v : V,
      dist (u : ℂ) x < ρ ∧ dist (v : ℂ) y < ρ ∧
        E.internal V (u, v) < C := by
  simp only [neighborhoodInternal, iInf_lt_iff] at h
  obtain ⟨u, hu, v, hv, hcost⟩ := h
  exact ⟨u, v, hu, hv, hcost⟩

theorem eventually_neighborhoodInternal_lt
    {G : ℕ → LSCMetric} {V : Set ℂ}
    (x y : V) (u v : ℕ → V)
    (hu : Tendsto (fun n => (u n : ℂ)) atTop (𝓝 (x : ℂ)))
    (hv : Tendsto (fun n => (v n : ℂ)) atTop (𝓝 (y : ℂ)))
    {ρ : ℝ} (hρ : 0 < ρ) {C : ℝ≥0∞}
    (hcost : ∀ᶠ n in atTop, (G n).internal V (u n, v n) < C) :
    ∀ᶠ n in atTop, neighborhoodInternal (G n) V x y ρ < C := by
  have hux : ∀ᶠ n in atTop, dist (u n : ℂ) x < ρ :=
    hu.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  have hvy : ∀ᶠ n in atTop, dist (v n : ℂ) y < ρ :=
    hv.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  filter_upwards [hux, hvy, hcost] with n hnx hny hnc
  exact (iInf_le_of_le (u n) <| iInf_le_of_le hnx <|
    iInf_le_of_le (v n) <| iInf_le_of_le hny le_rfl).trans_lt hnc

theorem buffered_neighborhood_upper
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (PfeWeyl.euclidForget (G n)))
    {W V K : Set ℂ} (hWV : W ⊆ V) (hWK : W ⊆ interior K)
    (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hneFront : (frontier V).Nonempty)
    (hdisj : Disjoint K (frontier V))
    (hsmall : PfeWeyl.SmallAnnulusCosts G D K V)
    (x y : W) {C : ℝ} (hC : 0 < C)
    (hxy : D.internal W (x, y) < ENNReal.ofReal C)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ n in atTop,
      neighborhoodInternal (G n) V
        ⟨(x : ℂ), hWV x.property⟩
        ⟨(y : ℂ), hWV y.property⟩ ρ < ENNReal.ofReal C := by
  obtain ⟨u, v, hu, hv, hcost⟩ :=
    buffered_inner_internal_upper_of_compact_collar hG hLen hPath hforget
      hWV hWK hV hK hfront hneFront hdisj hsmall x y hC hxy
  exact eventually_neighborhoodInternal_lt
    ⟨(x : ℂ), hWV x.property⟩ ⟨(y : ℂ), hWV y.property⟩ u v
    ((continuous_subtype_val.tendsto _).comp hu)
    ((continuous_subtype_val.tendsto _).comp hv) hρ hcost

theorem compact_buffer_neighborhood_lower
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {V K U : Set ℂ} (hVK : V ⊆ K) (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : V) (u v : ℕ → V) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hu : ∀ n, dist (u n : ℂ) x < ρ n)
    (hv : ∀ n, dist (v n : ℂ) y < ρ n)
    {C : ℝ≥0∞} (hcost : ∀ n, (G n).internal V (u n, v n) < C) :
    D.internal U
      (⟨(x : ℂ), hKU (hVK x.property)⟩,
        ⟨(y : ℂ), hKU (hVK y.property)⟩) ≤ C := by
  have hux : Tendsto (fun n => (u n : ℂ)) atTop (𝓝 (x : ℂ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero'
      (Eventually.of_forall fun n => dist_nonneg)
      (Eventually.of_forall fun n => (hu n).le) hρ
  have hvy : Tendsto (fun n => (v n : ℂ)) atTop (𝓝 (y : ℂ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero'
      (Eventually.of_forall fun n => dist_nonneg)
      (Eventually.of_forall fun n => (hv n).le) hρ
  have hlower := buffered_internal_liminf hG hVK hK hKU u v x y hux hvy
  have hlim : liminf (fun n => (G n).internal V (u n, v n)) atTop ≤ C := by
    have hlim' : liminf (fun n => (G n).internal V (u n, v n)) atTop ≤
        liminf (fun _ : ℕ => C) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall fun n => (hcost n).le)
    simpa using hlim'
  exact hlower.trans hlim

theorem compact_buffer_shrinking_neighborhood_lower
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {V K U : Set ℂ} (hVK : V ⊆ K) (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : V) {C : ℝ≥0∞}
    (hbad : ∀ k : ℕ, ∃ n ≥ k,
      neighborhoodInternal (G n) V x y (1 / (k + 1 : ℝ)) < C) :
    D.internal U
      (⟨(x : ℂ), hKU (hVK x.property)⟩,
        ⟨(y : ℂ), hKU (hVK y.property)⟩) ≤ C := by
  classical
  let n : ℕ → ℕ := fun k => (hbad k).choose
  have hnk : ∀ k, k ≤ n k := fun k => (hbad k).choose_spec.1
  have hnt : Tendsto n atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (hnk k)
  have hsel : ∀ k : ℕ,
      ∃ u v : V,
        dist (u : ℂ) x < 1 / (k + 1 : ℝ) ∧
        dist (v : ℂ) y < 1 / (k + 1 : ℝ) ∧
        (G (n k)).internal V (u, v) < C := by
    intro k
    exact exists_pair_of_neighborhoodInternal_lt (G (n k)) x y
      (hbad k).choose_spec.2
  choose u v hu hv hcost using hsel
  have hρ : Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact compact_buffer_neighborhood_lower (hG.comp hnt) hVK hK hKU
    x y u v _ hρ hu hv hcost

theorem eventually_compact_buffer_neighborhood_lower
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {V K U : Set ℂ} (hVK : V ⊆ K) (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : V) {C : ℝ≥0∞}
    (hC : C < D.internal U
      (⟨(x : ℂ), hKU (hVK x.property)⟩,
        ⟨(y : ℂ), hKU (hVK y.property)⟩)) :
    ∃ k : ℕ, ∀ᶠ n in atTop,
      C ≤ neighborhoodInternal (G n) V x y (1 / (k + 1 : ℝ)) := by
  classical
  by_contra hnot
  have hbad : ∀ k : ℕ, ∃ n ≥ k,
      neighborhoodInternal (G n) V x y (1 / (k + 1 : ℝ)) < C := by
    intro k
    have hk : ¬ ∀ᶠ n in atTop,
        C ≤ neighborhoodInternal (G n) V x y (1 / (k + 1 : ℝ)) := by
      intro he
      exact hnot ⟨k, he⟩
    simp only [Filter.eventually_atTop, not_exists, not_forall, not_le] at hk
    obtain ⟨n, hnk, hnlt⟩ := hk k
    exact ⟨n, hnk, hnlt⟩
  exact (not_lt_of_ge
    (compact_buffer_shrinking_neighborhood_lower hG hVK hK hKU x y hbad)) hC

theorem compact_buffer_le_lowerNeighborhoodObservable
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {V K U : Set ℂ} (hVK : V ⊆ K) (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : V) :
    D.internal U
      (⟨(x : ℂ), hKU (hVK x.property)⟩,
        ⟨(y : ℂ), hKU (hVK y.property)⟩) ≤
      lowerNeighborhoodObservable G V x y := by
  by_contra hnot
  have hlt : lowerNeighborhoodObservable G V x y <
      D.internal U
        (⟨(x : ℂ), hKU (hVK x.property)⟩,
          ⟨(y : ℂ), hKU (hVK y.property)⟩) := lt_of_not_ge hnot
  obtain ⟨C, hobsC, hCd⟩ := exists_between hlt
  obtain ⟨k, hk⟩ :=
    eventually_compact_buffer_neighborhood_lower hG hVK hK hKU x y hCd
  have hClim : C ≤ liminf
      (fun n => neighborhoodInternal (G n) V x y (1 / (k + 1 : ℝ))) atTop := by
    have h := Filter.liminf_le_liminf hk
    simpa using h
  have hCobs : C ≤ lowerNeighborhoodObservable G V x y :=
    hClim.trans (le_iSup (fun k : ℕ => liminf
      (fun n => neighborhoodInternal (G n) V x y (1 / (k + 1 : ℝ))) atTop) k)
  exact (not_lt_of_ge hCobs) hobsC

theorem lowerNeighborhoodObservable_le_inner
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (PfeWeyl.euclidForget (G n)))
    {W V K : Set ℂ} (hWV : W ⊆ V) (hWK : W ⊆ interior K)
    (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hneFront : (frontier V).Nonempty)
    (hdisj : Disjoint K (frontier V))
    (hsmall : PfeWeyl.SmallAnnulusCosts G D K V)
    (x y : W) :
    lowerNeighborhoodObservable G V
        ⟨(x : ℂ), hWV x.property⟩
        ⟨(y : ℂ), hWV y.property⟩ ≤ D.internal W (x, y) := by
  by_contra hnot
  have hlt : D.internal W (x, y) < lowerNeighborhoodObservable G V
      ⟨(x : ℂ), hWV x.property⟩
      ⟨(y : ℂ), hWV y.property⟩ := lt_of_not_ge hnot
  obtain ⟨C, hdC, hCobs⟩ := exists_between hlt
  have hfin : C ≠ ∞ := ne_top_of_lt (lt_of_lt_of_le hCobs le_top)
  have hCpos : 0 < C := lt_of_le_of_lt bot_le hdC
  have hCreal : 0 < C.toReal := ENNReal.toReal_pos hCpos.ne' hfin
  have hxy : D.internal W (x, y) < ENNReal.ofReal C.toReal := by
    rw [ENNReal.ofReal_toReal hfin]
    exact hdC
  have hobsle : lowerNeighborhoodObservable G V
      ⟨(x : ℂ), hWV x.property⟩
      ⟨(y : ℂ), hWV y.property⟩ ≤ C := by
    apply iSup_le
    intro k
    have hρ : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    have hk := buffered_neighborhood_upper hG hLen hPath hforget hWV
      hWK hV hK hfront hneFront hdisj hsmall x y hCreal hxy hρ
    have hlim : liminf (fun n => neighborhoodInternal (G n) V
        ⟨(x : ℂ), hWV x.property⟩
        ⟨(y : ℂ), hWV y.property⟩ (1 / (k + 1 : ℝ))) atTop ≤
        ENNReal.ofReal C.toReal := by
      have hh : liminf (fun n => neighborhoodInternal (G n) V
          ⟨(x : ℂ), hWV x.property⟩
          ⟨(y : ℂ), hWV y.property⟩ (1 / (k + 1 : ℝ))) atTop ≤
          liminf (fun _ : ℕ => ENNReal.ofReal C.toReal) atTop :=
        Filter.liminf_le_liminf (hk.mono fun n hn => hn.le)
      simpa using hh
    simpa only [ENNReal.ofReal_toReal hfin] using hlim
  exact (not_lt_of_ge hobsle) hCobs

theorem buffered_neighborhood_observable_sandwich
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    (hLen : ∀ n, (G n).IsLengthSpace)
    (hPath : ∀ n, FinitePathsEuclideanContinuous (G n))
    (hforget : ∀ n, Continuous (PfeWeyl.euclidForget (G n)))
    {W V K Kout U : Set ℂ}
    (hWV : W ⊆ V) (hWK : W ⊆ interior K)
    (hVKout : V ⊆ Kout) (hKout : IsCompact Kout) (hKoutU : Kout ⊆ U)
    (hV : IsOpen V) (hK : IsCompact K)
    (hfront : IsCompact (frontier V))
    (hneFront : (frontier V).Nonempty)
    (hdisj : Disjoint K (frontier V))
    (hsmall : PfeWeyl.SmallAnnulusCosts G D K V)
    (x y : W) :
    D.internal U
        (⟨(x : ℂ), hKoutU (hVKout (hWV x.property))⟩,
          ⟨(y : ℂ), hKoutU (hVKout (hWV y.property))⟩) ≤
      lowerNeighborhoodObservable G V
        ⟨(x : ℂ), hWV x.property⟩
        ⟨(y : ℂ), hWV y.property⟩ ∧
      lowerNeighborhoodObservable G V
        ⟨(x : ℂ), hWV x.property⟩
        ⟨(y : ℂ), hWV y.property⟩ ≤ D.internal W (x, y) := by
  let xV : V := ⟨(x : ℂ), hWV x.property⟩
  let yV : V := ⟨(y : ℂ), hWV y.property⟩
  have hleft := compact_buffer_le_lowerNeighborhoodObservable hG hVKout
    hKout hKoutU xV yV
  have hright := lowerNeighborhoodObservable_le_inner hG hLen hPath hforget
    hWV hWK hV hK hfront hneFront hdisj hsmall x y
  exact ⟨hleft, hright⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
