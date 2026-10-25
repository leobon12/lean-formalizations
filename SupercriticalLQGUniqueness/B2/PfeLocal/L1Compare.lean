import SupercriticalLQGUniqueness.B2.PfeLocal.L1Local

 













set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def l1Recenter (z : ℂ) (ρ : ℝ) (g : DistC) : DistC := addConst g (-circleAvg g ρ z)

theorem measurable_l1Recenter (z : ℂ) (ρ : ℝ) : Measurable (l1Recenter z ρ) :=
  LQGMetric.DFGPS.L219.measurable_addConst_of measurable_id (measurable_circleAvg_left ρ z).neg

 
def l1CompGood (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (D : Set ℂ) (ε : Set.Ioi (0 : ℝ))
    (z : ℂ) (r ρ δ : ℝ) (g : DistC) : Prop :=
  ∀ x ∈ D, x ∈ ball z (3 * r) →
    |(V ε g x - circleAvg g ρ z) - LFPP.locMollify (ε : ℝ) ε.2 (l1Recenter z ρ g) x| ≤ δ

theorem l1_measurableSet_compGood (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hVm : ∀ δ, Measurable (V δ)) {D : Set ℂ} (hD : D.Countable) (ε : Set.Ioi (0 : ℝ))
    (z : ℂ) (r ρ δ : ℝ) : MeasurableSet {g | l1CompGood V D ε z r ρ δ g} := by
  have e : {g | l1CompGood V D ε z r ρ δ g} = ⋂ x ∈ D ∩ ball z (3 * r),
      {g | |(V ε g x - circleAvg g ρ z) - LFPP.locMollify (ε : ℝ) ε.2 (l1Recenter z ρ g) x| ≤ δ} := by
    ext g; simp only [l1CompGood, mem_ofPred_eq, mem_iInter, mem_inter_iff]
    exact ⟨fun h x hx => h x hx.1 hx.2, fun h x hx hx' => h x ⟨hx, hx'⟩⟩
  rw [e]
  refine MeasurableSet.biInter (hD.mono inter_subset_left) fun x _ => ?_
  have h1 : Measurable fun g => V ε g x := (continuous_eval_const x).measurable.comp (hVm ε)
  have h2 : Measurable fun g => LFPP.locMollify (ε : ℝ) ε.2 (l1Recenter z ρ g) x :=
    (measurable_distOn_apply (LFPP.locTest (ε : ℝ) ε.2 x)).comp (measurable_l1Recenter z ρ)
  exact measurableSet_le ((h1.sub (measurable_circleAvg_left ρ z)).sub h2).abs measurable_const

 
theorem l1_compGood_all (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) {D : Set ℂ} (hD : Dense D)
    (ε : Set.Ioi (0 : ℝ)) (z : ℂ) (r ρ δ : ℝ) {g : DistC} (h : l1CompGood V D ε z r ρ δ g) :
    ∀ x ∈ ball z (3 * r), |(V ε g - ContinuousMap.const ℂ (circleAvg g ρ z)) x -
      LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.2 (l1Recenter z ρ g) x| ≤ δ := by
  have hcont : Continuous fun x => |(V ε g - ContinuousMap.const ℂ (circleAvg g ρ z)) x -
      LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.2 (l1Recenter z ρ g) x| :=
    ((V ε g - ContinuousMap.const ℂ (circleAvg g ρ z)).continuous.sub
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.2 (l1Recenter z ρ g)).continuous).abs
  have hcl : IsClosed {x | |(V ε g - ContinuousMap.const ℂ (circleAvg g ρ z)) x -
      LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.2 (l1Recenter z ρ g) x| ≤ δ} :=
    isClosed_le hcont continuous_const
  intro x hx
  have hsub : ball z (3 * r) ∩ D ⊆ {x | |(V ε g - ContinuousMap.const ℂ (circleAvg g ρ z)) x -
      LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.2 (l1Recenter z ρ g) x| ≤ δ} := by
    rintro y ⟨hy1, hy2⟩
    exact h y hy2 hy1
  exact hcl.closure_subset_iff.2 hsub (hD.open_subset_closure_inter isOpen_ball hx)

 
theorem l1_measure_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    (h : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ A n) : Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
  set B : ℕ → Set Ω := fun n => ⋃ m ≥ n, A m with hB
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    MeasurableSet.biUnion (to_countable _) fun m _ => hA m
  have hBa : Antitone B := fun n n' hnn' =>
    biUnion_subset_biUnion_left fun m hm => le_trans hnn' hm
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hBm n).nullMeasurableSet) hBa
    ⟨0, measure_ne_top μ _⟩
  have hnull : μ (⋂ n, B n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 hω
    intro hmem
    obtain ⟨m, hm, hmA⟩ := mem_iUnion₂.1 (mem_iInter.1 hmem N)
    exact hN m hm hmA
  rw [hnull] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => zero_le) (fun n => measure_mono (subset_biUnion_of_mem (le_refl n)))

 
theorem l1_ae_eventually_compGood (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (D : Set ℂ) (z : ℂ) (r ρ δ : ℝ) (hδ : 0 < δ) (e : ℕ → Set.Ioi (0 : ℝ))
    (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0)) :
    ∀ᵐ g ∂normGFFLaw, ∀ᶠ n in atTop, l1CompGood V D (e n) z r ρ δ g := by
  obtain ⟨-, hcan⟩ := PfeAxioms.normalized_canonical_model
  have hY := PfeAxioms.isGFFPlusBddCont_recentered hcan ρ z
  have hcomp := PfeAxioms.localizedLFPP_compare hY (U := ball z (3 * r)) isBounded_ball
    ⟨1, Set.mem_Ioi.mpr one_pos⟩
  have hF1 : ∀ᵐ g ∂normGFFLaw, ∀ n, ∀ x,
      V (e n) g x - circleAvg g ρ z = heatMollify (e n : ℝ) (l1Recenter z ρ g) x := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hV (e n), hcan.1.ae_tendstoLocallyUniformly_heatMollify (e n : ℝ)
      (e n).2.ne'] with g hg hconv x
    simp only [id_eq] at hconv
    unfold l1Recenter
    rw [LQGMetric.DFGPS.heatMollify_addConst_of_tendsto (e n).2.ne'
      ((tendstoLocallyUniformlyOn_univ.2 hconv.1).tendsto_at (mem_univ x)), hg x]
    rfl
  have hen : Tendsto (fun n => (e n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨he, Eventually.of_forall fun n => (e n).2⟩
  filter_upwards [hcomp, hF1] with g hg hg1
  filter_upwards [hen.eventually (hg.1 δ hδ)] with n hn x _ hx
  rw [hg1 n x]
  exact hn (e n).2 x (subset_closure hx)

theorem l1_tendsto_compBad (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    {D : Set ℂ} (hD : D.Countable) (z : ℂ) (r ρ δ : ℝ) (hδ : 0 < δ)
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => normGFFLaw {g | ¬ l1CompGood V D (e n) z r ρ δ g}) atTop (𝓝 0) := by
  obtain ⟨hprob, -⟩ := PfeAxioms.normalized_canonical_model
  refine l1_measure_tendsto_zero (fun n => (l1_measurableSet_compGood V hVm hD (e n) z r ρ δ).compl)
    ?_
  filter_upwards [l1_ae_eventually_compGood V hV D z r ρ δ hδ e he] with g hg
  filter_upwards [hg] with n hn
  exact fun h => h hn

 

theorem l1_ae_circleAvg_recenter (z : ℂ) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    ∀ᵐ g ∂normGFFLaw, circleAvg (l1Recenter z ρ g) r z = circleAvg g r z - circleAvg g ρ z := by
  obtain ⟨-, hcan⟩ := PfeAxioms.normalized_canonical_model
  filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst hcan.1 z hr] with g hg
  unfold l1Recenter
  rw [show circleAvg (addConst g (-circleAvg g ρ z)) r z = circleAvg g r z + -circleAvg g ρ z
    from hg _]
  ring

 
theorem l1_heat_to_loc (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {D : Set ℂ} (hD : Dense D) (ε : Set.Ioi (0 : ℝ)) (q : Finset ℂ)
    (hq : ∀ i ∈ q, i ∈ l1Shell) (z : ℂ) {r : ℝ} (hr : 0 < r) (ρ : ℝ) {C : ℝ} (hC : 0 < C)
    (δ : ℝ) {g : DistC} (hcirc : circleAvg (l1Recenter z ρ g) r z = circleAvg g r z - circleAvg g ρ z)
    (hcomp : l1CompGood V D ε z r ρ δ g)
    (h : l1HeatGood ξ a b (V ε g) q z r C (circleAvg g r z)) :
    l1LocGood ξ a b ε ε.2 (l1Recenter z ρ g) q z r (C * Real.exp (|ξ| * δ)) := by
  rw [l1_heatGood_sub_const ξ a b (V ε g) q z r C (circleAvg g r z) (circleAvg g ρ z),
    ← hcirc] at h
  exact l1_heatGood_mono ξ a b _ _ q hq z hr hC _ δ (l1_compGood_all V hD ε z r ρ δ hcomp) h

 
theorem l1_loc_to_heat (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {D : Set ℂ} (hD : Dense D) (ε : Set.Ioi (0 : ℝ)) (q : Finset ℂ)
    (hq : ∀ i ∈ q, i ∈ l1Shell) (z : ℂ) {r : ℝ} (hr : 0 < r) (ρ : ℝ) {C : ℝ} (hC : 0 < C)
    (δ : ℝ) {g : DistC} (hcirc : circleAvg (l1Recenter z ρ g) r z = circleAvg g r z - circleAvg g ρ z)
    (hcomp : l1CompGood V D ε z r ρ δ g)
    (h : l1LocGood ξ a b ε ε.2 (l1Recenter z ρ g) q z r C) :
    l1HeatGood ξ a b (V ε g) q z r (C * Real.exp (|ξ| * δ)) (circleAvg g r z) := by
  unfold l1LocGood at h
  rw [hcirc] at h
  rw [l1_heatGood_sub_const ξ a b (V ε g) q z r _ (circleAvg g r z) (circleAvg g ρ z)]
  refine l1_heatGood_mono ξ a b _ _ q hq z hr hC _ δ (fun x hx => ?_) h
  rw [abs_sub_comm]
  exact l1_compGood_all V hD ε z r ρ δ hcomp x hx

end SupercriticalLQGUniqueness.B2.PfeLocal
