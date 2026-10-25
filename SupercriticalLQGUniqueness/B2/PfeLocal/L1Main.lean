import SupercriticalLQGUniqueness.B2.PfeLocal.L1Limit

 


















set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

theorem l1_ratio_transport (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (e : ℕ → Set.Ioi (0 : ℝ)) (q : ℚ) (hq : 0 < q)
    (r : ℝ) (hr : 0 < r) (hqr : (q : ℝ) = r)
    (h : Tendsto (fun n => (q : ℝ) *
      (m ⟨(e n : ℝ) / (q : ℝ), Set.mem_Ioi.mpr (div_pos (e n).2 (Rat.cast_pos.mpr hq))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop (𝓝 (c ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hq)⟩ : ℝ))) :
    Tendsto (fun n => r * (m ⟨(e n : ℝ) / r, Set.mem_Ioi.mpr (div_pos (e n).2 hr)⟩ : ℝ) /
      (m (e n) : ℝ)) atTop (𝓝 (c ⟨r, hr⟩ : ℝ)) := by
  subst hqr
  exact h

theorem l1Scale_eq_rat (k₀ k : ℕ) : (((1 / 16 : ℚ) ^ (k₀ + k) : ℚ) : ℝ) = l1Scale k₀ k := by
  unfold l1Scale; push_cast; ring

 
theorem l1_coupled_iteration (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hc : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(e n : ℝ) / (r : ℝ), Set.mem_Ioi.mpr (div_pos (e n).2 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ)))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (h' : Ω' → DistC) (hh' : IsNormalizedWholePlaneGFF h' P')
    (hN : ℕ → Ω' → DistC) (hNm : ∀ n, Measurable (hN n))
    (hNlaw : ∀ n, P'.map (hN n) = normGFFLaw)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    (L : Ω' → LSCMetric)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (L ω)))
    (a : ℝ) (ha : 0 < a) (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    ∃ C : Set.Ioi (1 : ℝ), ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (z : ℂ) (k₀ J : ℕ),
      P' {ω | (LQGMetric.Blueprint.countOcc (fun k =>
        annulusEvent (ξ : ℝ) c h' L z ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ C) J ω : ℝ) < b * J} ≤
        ENNReal.ofReal (c₀ * Real.exp (-a * J)) := by
  obtain ⟨q, hq, hcov⟩ := exists_l1AcrossNet
  obtain ⟨Ch, c₀, hCh1, hc₀, hfin⟩ :=
    l1_canonical_count_bound hS4 hPerc ξ Q hQ m hm V hVm hV q hq a ha b hb hb1
  have hCh : 0 < Ch := by linarith
  set Ct : ℝ := 16 * Ch * Real.exp ξ + 1 with hCt
  have hCt1 : 1 < Ct := by rw [hCt]; have := Real.exp_pos (ξ : ℝ); nlinarith
  refine ⟨⟨Ct, hCt1⟩, c₀, hc₀, fun z k₀ J => ?_⟩
  set r : ℕ → ℝ := l1Scale k₀ with hrdef
  have hr0 : ∀ k, 0 < r k := l1Scale_pos k₀
  have hh'm : Measurable h' := hh'.1.measurable
  
  set Heat : ℕ → ℕ → Set Ω' := fun n k => hN n ⁻¹' l1HeatFam ξ m V q z k₀ Ch (e n) k
    with hHeat
  set Close : ℕ → ℕ → Set Ω' :=
    fun n k => {ω | |circleAvg (hN n ω) (r k) z - circleAvg (h' ω) (r k) z| ≤ 1} with hClose
  set A : ℕ → Set Ω' := fun n =>
    {ω | (LQGMetric.Blueprint.countOcc (Heat n) J ω : ℝ) < b * J} ∪
      ⋃ k ∈ Finset.Icc 1 J, (Close n k)ᶜ with hA
  have hFam : ∀ n k, MeasurableSet (l1HeatFam ξ m V q z k₀ Ch (e n) k) := fun n k =>
    l1_measurableSet_heatGood ξ _ _ (hVm (e n)) q z _ Ch (measurable_circleAvg_left _ z)
  have hCloseM : ∀ n k, MeasurableSet (Close n k) := fun n k =>
    measurableSet_le (((measurable_circleAvg_left (r k) z).comp (hNm n)).sub
      ((measurable_circleAvg_left (r k) z).comp hh'm)).abs measurable_const
  
  have hincl : {ω | (LQGMetric.Blueprint.countOcc (fun k =>
      annulusEvent (ξ : ℝ) c h' L z ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ ⟨Ct, hCt1⟩) J ω : ℝ) <
        b * J} ≤ᵐ[P'] {ω | ∀ᶠ n in atTop, ω ∈ A n} := by
    filter_upwards [hconv] with ω hω htarget
    by_contra hnot
    simp only [not_eventually] at hnot
    refine (not_lt.2 ?_) htarget
    refine l1_count_of_frequently (fun n k => Heat n k ∩ Close n k) _ J ω (b * J) ?_ ?_
    · refine hnot.mono fun n hn => ?_
      simp only [hA, mem_union, mem_ofPred_eq, mem_iUnion, mem_compl_iff, not_or, not_lt,
        not_exists, not_not] at hn
      have hle : LQGMetric.Blueprint.countOcc (Heat n) J ω ≤
          LQGMetric.Blueprint.countOcc (fun k => Heat n k ∩ Close n k) J ω :=
        l1_countOcc_mono fun k hk h => ⟨h, hn.2 k hk⟩
      exact hn.1.trans (by exact_mod_cast hle)
    · intro k hk hfr
      have hκ := l1_ratio_transport m c e _ (by positivity) (r k) (hr0 k) (l1Scale_eq_rat k₀ k)
        (hc _ (by positivity))
      have := l1_annulusEvent_of_frequently ξ m V q hq hcov c e ⟨r k, hr0 k⟩ hκ hCh z
        (fun n => hN n ω) (h' ω) (L ω) hω (hfr.mono fun n hn => hn)
      exact this
  
  have hmain : ∀ τ : ℝ, 0 < τ → P' {ω | (LQGMetric.Blueprint.countOcc (fun k =>
      annulusEvent (ξ : ℝ) c h' L z ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ ⟨Ct, hCt1⟩) J ω : ℝ) <
        b * J} ≤ ENNReal.ofReal (c₀ * Real.exp (-a * J)) + ENNReal.ofReal τ +
          ENNReal.ofReal τ := by
    intro τ hτ
    refine (measure_mono_ae hincl).trans (l1_measure_eventually_le ?_)
    have hcirc : ∀ᶠ n in atTop, ∀ k ∈ Finset.Icc 1 J,
        P' (Close n k)ᶜ ≤ ENNReal.ofReal (τ / (J + 1)) := by
      rw [Filter.eventually_all_finset]
      intro k _
      have ht := l1_circleAvg_tendsto_prob P' h' hh' hN hNm hNlaw hpair z (hr0 k)
        (η := 1) one_pos
      filter_upwards [(ENNReal.tendsto_nhds_zero.1 ht) (ENNReal.ofReal (τ / (J + 1)))
        (ENNReal.ofReal_pos.2 (by positivity))] with n hn
      refine le_trans (measure_mono fun ω hω => ?_) hn
      simp only [hClose, mem_compl_iff, mem_ofPred_eq, not_le] at hω
      exact hω
    filter_upwards [hfin z k₀ J e he τ hτ, hcirc] with n hn hn'
    have hlaw : P' {ω | (LQGMetric.Blueprint.countOcc (Heat n) J ω : ℝ) < b * J} =
        normGFFLaw {g | (LQGMetric.Blueprint.countOcc (l1HeatFam ξ m V q z k₀ Ch (e n)) J g : ℝ) <
          b * J} := by
      rw [← hNlaw n, Measure.map_apply (hNm n) (measurableSet_lt (measurable_from_nat.comp
        (l1_measurable_countOcc (hFam n) J)) measurable_const :
          MeasurableSet {g : DistC | (LQGMetric.Blueprint.countOcc
            (l1HeatFam ξ m V q z k₀ Ch (e n)) J g : ℝ) < b * J})]
      rfl
    have hsum : ∑ k ∈ Finset.Icc 1 J, ENNReal.ofReal (τ / (J + 1)) ≤ ENNReal.ofReal τ := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    calc P' (A n) ≤ P' {ω | (LQGMetric.Blueprint.countOcc (Heat n) J ω : ℝ) < b * J} +
          ∑ k ∈ Finset.Icc 1 J, P' (Close n k)ᶜ :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
      _ ≤ (ENNReal.ofReal (c₀ * Real.exp (-a * J)) + ENNReal.ofReal τ) +
          ∑ k ∈ Finset.Icc 1 J, ENNReal.ofReal (τ / (J + 1)) :=
        add_le_add (hlaw ▸ hn) (Finset.sum_le_sum hn')
      _ ≤ ENNReal.ofReal (c₀ * Real.exp (-a * J)) + ENNReal.ofReal τ + ENNReal.ofReal τ :=
        add_le_add le_rfl hsum
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
  refine (hmain _ hε2).trans (le_of_eq ?_)
  rw [add_assoc, ← ENNReal.ofReal_add hε2.le hε2.le, add_halves, ENNReal.ofReal_coe_nnreal]

end SupercriticalLQGUniqueness.B2.PfeLocal
