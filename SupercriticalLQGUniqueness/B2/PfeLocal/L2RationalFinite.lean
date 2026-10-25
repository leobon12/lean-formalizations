import SupercriticalLQGUniqueness.B2.PfeLocal.L3NonDawdle

 
















set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
theorem l2_normalized_eq_crossLenIn (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (u v : ℂ) :
    PfeWeyl.normalizedLFPPMetric ξ a φ (u, v) =
      ENNReal.ofReal ((a : ℝ)⁻¹) * crossLenIn ξ φ (univ : Set ℂ) {u} {v} := by
  rw [PfeWeyl.normalizedLFPPMetric_apply, LQGMetric.DFGPS.crossLenIn_singleton,
    B2.LscTop.lfppDistance_eq_lfppD]

 
theorem l2_rationalCircle_point {O : Set ℂ} (hO : Iface.IsRationalCircle O) :
    ∃ u ∈ O, Iface.IsRationalPoint u := by
  obtain ⟨x, y, r, hr, rfl⟩ := hO
  refine ⟨⟨((x + r * (3 / 5) : ℚ) : ℝ), ((y + r * (4 / 5) : ℚ) : ℝ)⟩, ?_,
    ⟨x + r * (3 / 5), y + r * (4 / 5), rfl⟩⟩
  rw [mem_sphere, Complex.dist_eq]
  have e : (⟨((x + r * (3 / 5) : ℚ) : ℝ), ((y + r * (4 / 5) : ℚ) : ℝ)⟩ : ℂ) -
      ⟨(x : ℝ), (y : ℝ)⟩ = ⟨(r : ℝ) * (3 / 5), (r : ℝ) * (4 / 5)⟩ := by
    apply Complex.ext <;> simp
  rw [e, Complex.norm_eq_sqrt_sq_add_sq]
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  rw [show ((r : ℝ) * (3 / 5)) ^ 2 + ((r : ℝ) * (4 / 5)) ^ 2 = (r : ℝ) ^ 2 by ring,
    Real.sqrt_sq hr']

 
theorem l2_rationalPoint_finite (hS4 : Iface.DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (L : Ω' → LSCMetric)
    (hrat : ∀ᵐ ω ∂P', ∀ u v : ℂ, Iface.IsRationalPoint u → Iface.IsRationalPoint v →
      Tendsto (fun n => PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω)) (u, v))
        atTop (𝓝 (L ω (u, v)))) :
    ∀ᵐ ω ∂P', ∀ u v : ℂ, Iface.IsRationalPoint u → Iface.IsRationalPoint v →
      L ω (u, v) < ∞ := by
  obtain ⟨hprob, hcan⟩ := PfeAxioms.normalized_canonical_model
  have hX := l1_isHeatSmoothing_canonical V hV
  
  have hpair : ∀ u v : ℂ, ∀ᵐ ω ∂P', (∀ u v : ℂ, Iface.IsRationalPoint u →
      Iface.IsRationalPoint v → Tendsto (fun n => PfeWeyl.normalizedLFPPMetric ξ (m (e n))
        (V (e n) (hN n ω)) (u, v)) atTop (𝓝 (L ω (u, v)))) →
      Iface.IsRationalPoint u → Iface.IsRationalPoint v → L ω (u, v) < ∞ := by
    intro u v
    by_cases huv : u = v
    · refine Eventually.of_forall fun ω _ _ _ => ?_
      rw [huv, (L ω).2.1.1 v]
      exact ENNReal.zero_lt_top
    
    have htight := (hS4 ξ Q hQ m hm).1 normGFFLaw id hcan V hX ⊤
      (by simpa using isConnected_univ) u v (mem_univ _) (mem_univ _) huv
    have hbad : ∀ η : ℝ, 0 < η → P' {ω | (∀ u v : ℂ, Iface.IsRationalPoint u →
        Iface.IsRationalPoint v → Tendsto (fun n => PfeWeyl.normalizedLFPPMetric ξ (m (e n))
          (V (e n) (hN n ω)) (u, v)) atTop (𝓝 (L ω (u, v)))) ∧ Iface.IsRationalPoint u ∧
            Iface.IsRationalPoint v ∧ L ω (u, v) = ∞} ≤ ENNReal.ofReal η := by
      intro η hη
      obtain ⟨M, hM, hMt⟩ := htight.2 η hη
      set A : ℕ → Set Ω' := fun n => {ω | ENNReal.ofReal M <
        PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω)) (u, v)} with hA
      have hsub : {ω | (∀ u v : ℂ, Iface.IsRationalPoint u → Iface.IsRationalPoint v →
          Tendsto (fun n => PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω)) (u, v))
            atTop (𝓝 (L ω (u, v)))) ∧ Iface.IsRationalPoint u ∧ Iface.IsRationalPoint v ∧
              L ω (u, v) = ∞} ⊆ {ω | ∀ᶠ n in atTop, ω ∈ A n} := by
        rintro ω ⟨hconv, hu, hv, hinf⟩
        have := hconv u v hu hv
        rw [hinf] at this
        exact this.eventually (eventually_gt_nhds (ENNReal.ofReal_lt_top))
      refine (measure_mono hsub).trans (l1_measure_eventually_le ?_)
      filter_upwards [(tendsto_order.1 he).2 1 one_pos] with n hn1
      let εn : Set.Ioo (0 : ℝ) 1 := ⟨e n, (e n).2, hn1⟩
      have hlaw : P' (A n) = normGFFLaw {g | ENNReal.ofReal M <
          ENNReal.ofReal ((m ⟨εn, εn.property.1⟩ : ℝ)⁻¹) *
            crossLenIn ξ (V ⟨εn, εn.property.1⟩ g) (⊤ : TopologicalSpace.Opens ℂ) {u} {v}} := by
        have hmeas : Measurable fun g : DistC =>
            PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) g) (u, v) := by
          simp_rw [l2_normalized_eq_crossLenIn]
          exact measurable_const.mul (B2.DG20Pt.measurable_crossLenIn_open ξ ⊤ _ _
            (fun x g => V (e n) g x) (fun g => (V (e n) g).continuous)
            (fun x => (continuous_eval_const x).measurable.comp (hVm (e n))))
        rw [show A n = hN n ⁻¹' {g | ENNReal.ofReal M <
          PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) g) (u, v)} from rfl,
          ← Measure.map_apply (hNm n) (measurableSet_lt measurable_const hmeas), hNlaw n]
        congr 1
        ext g
        simp only [mem_ofPred_eq, l2_normalized_eq_crossLenIn]
        rfl
      rw [hlaw]
      exact (hMt εn).1
    have hnull : P' {ω | (∀ u v : ℂ, Iface.IsRationalPoint u →
        Iface.IsRationalPoint v → Tendsto (fun n => PfeWeyl.normalizedLFPPMetric ξ (m (e n))
          (V (e n) (hN n ω)) (u, v)) atTop (𝓝 (L ω (u, v)))) ∧ Iface.IsRationalPoint u ∧
            Iface.IsRationalPoint v ∧ L ω (u, v) = ∞} = 0 := by
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_) (zero_le)
      rw [zero_add]
      simpa using hbad η (by exact_mod_cast hη)
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    simp only [mem_ofPred_eq, not_imp, not_lt, top_le_iff] at hω
    exact ⟨hω.1, hω.2.1, hω.2.2.1, hω.2.2.2⟩
  
  have hall : ∀ᵐ ω ∂P', ∀ x y x' y' : ℚ, (∀ u v : ℂ, Iface.IsRationalPoint u →
      Iface.IsRationalPoint v → Tendsto (fun n => PfeWeyl.normalizedLFPPMetric ξ (m (e n))
        (V (e n) (hN n ω)) (u, v)) atTop (𝓝 (L ω (u, v)))) →
      Iface.IsRationalPoint ⟨(x : ℝ), (y : ℝ)⟩ → Iface.IsRationalPoint ⟨(x' : ℝ), (y' : ℝ)⟩ →
        L ω (⟨(x : ℝ), (y : ℝ)⟩, ⟨(x' : ℝ), (y' : ℝ)⟩) < ∞ := by
    simp only [ae_all_iff]
    intro x y x' y'
    exact hpair _ _
  filter_upwards [hall, hrat] with ω hω hω' u v hu hv
  obtain ⟨x, y, rfl⟩ := hu
  obtain ⟨x', y', rfl⟩ := hv
  exact hω x y x' y' hω' ⟨x, y, rfl⟩ ⟨x', y', rfl⟩

 

theorem l2_rationalCircle_finite {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (L : Ω' → LSCMetric)
    (hfin : ∀ᵐ ω ∂P', ∀ u v : ℂ, Iface.IsRationalPoint u → Iface.IsRationalPoint v →
      L ω (u, v) < ∞) :
    ∀ᵐ ω ∂P', ∀ O O' : Set ℂ, Iface.IsRationalCircle O → Iface.IsRationalCircle O' →
      Iface.setDistance (L ω).1 O O' < ∞ := by
  filter_upwards [hfin] with ω hω O O' hO hO'
  obtain ⟨u, huO, hu⟩ := l2_rationalCircle_point hO
  obtain ⟨v, hvO, hv⟩ := l2_rationalCircle_point hO'
  exact lt_of_le_of_lt (iInf₂_le_of_le u huO (iInf₂_le v hvO)) (hω u v hu hv)

end SupercriticalLQGUniqueness.B2.PfeLocal
