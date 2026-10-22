import HigherDimLQGMetric.Determ.ESAvg
import LQGMetric.Papers.LM.T1_7V15

/-! Bounds on Efron–Stein increments through compatible metric copies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

theorem determ_ES_le (ν : Measure (ContMetric dim)) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 ≤ C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd dim, p.2.1 (z, w) ≤ C * p.1.1 (z, w)) {ε R : ℝ}
    {F : ContMetric dim → ℝ} (hFm : Measurable F)
    {Φ : (Fin dim → ℝ) × (determFixedBox (d := dim) ε R → ℕ → ℝ≥0∞) → ℝ} (hΦ : Measurable Φ)
    (K : Kernel ((Fin dim → ℝ) × (determFixedBox (d := dim) ε R → ℕ → ℝ≥0∞)) (ContMetric dim)) [IsMarkovKernel K]
    (hslice : ∀ᵐ θ ∂(determShiftLaw dim), (ν.map (determY ε θ (determFixedBox (d := dim) ε R))) ⊗ₘ
        (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) =
      ν.map fun d => (determY ε θ (determFixedBox (d := dim) ε R) d, d))
    (hΦF : ∀ᵐ θ ∂(determShiftLaw dim), ∀ᵐ d ∂ν, F d = Φ (θ, determY ε θ (determFixedBox (d := dim) ε R) d))
    (hprod : ∀ᵐ θ ∂(volume : Measure (Fin dim → ℝ)), ν.map (determY ε θ (determFixedBox (d := dim) ε R)) =
      Measure.pi fun k : determFixedBox (d := dim) ε R => ν.map (determ_enc (determCube ε θ k))) :
    ∀ᵐ d ∂ν, ∀ᵐ θ ∂(determShiftLaw dim), ∀ b : determFixedBox (d := dim) ε R → ℝ,
      (∀ (k : determFixedBox (d := dim) ε R) (d'' : ContMetric dim), DetermCompat C ε θ (determFixedBox (d := dim) ε R) d d'' k.1 →
        max (F d'' - F d) 0 ^ 2 ≤ b k) →
      determES ε R F Φ ν θ d ≤ ∑ k, ENNReal.ofReal (b k) := by
  letI : Nonempty (ContMetric dim) := nonempty_of_isProbabilityMeasure ν
  set p := TopologicalSpace.denseSeq (Rd dim × Rd dim)
  obtain ⟨M, hM, hML, hνM⟩ := determ_measurable_ae_subset ν hL
  have hY := determ_measurable_gridY ε (determFixedBox (d := dim) ε R)
  have hev : ∀ n, Measurable fun d : ContMetric dim => d.1 (p n) := fun n =>
    (continuous_eval_const _).measurable.comp measurable_subtype_coe
  -- resampled coordinates and the good set of `D^S`
  set yS : (determFixedBox (d := dim) ε R) → ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim → (determFixedBox (d := dim) ε R) → ℕ → ℝ≥0∞ := fun k q =>
    Function.update (determY ε q.1.1 (determFixedBox (d := dim) ε R) q.1.2) k (determY ε q.1.1 (determFixedBox (d := dim) ε R) q.2 k) with hySdef
  have hyS : ∀ k, Measurable (yS k) := fun k =>
    (LQGMetric.LM.t17v_measurable_update k).comp ((hY.comp measurable_fst).prodMk
      (hY.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  set T : (determFixedBox (d := dim) ε R) → Set ((((Fin dim → ℝ) × ContMetric dim) × ContMetric dim) × ContMetric dim) := fun k =>
    {t | t.2 ∈ M ∧ (∀ n, t.2.1 (p n) ≤ C ^ 2 * t.1.1.2.1 (p n)) ∧
      (∀ n, t.1.1.2.1 (p n) ≤ C ^ 2 * t.2.1 (p n)) ∧ determY ε t.1.1.1 (determFixedBox (d := dim) ε R) t.2 = yS k t.1 ∧
      F t.2 = Φ (t.1.1.1, yS k t.1)} with hTdef
  have hT : ∀ k, MeasurableSet (T k) := by
    intro k
    have hB1 : MeasurableSet {t : (((Fin dim → ℝ) × ContMetric dim) × ContMetric dim) × ContMetric dim |
        ∀ n, t.2.1 (p n) ≤ C ^ 2 * t.1.1.2.1 (p n)} := by
      have : {t : (((Fin dim → ℝ) × ContMetric dim) × ContMetric dim) × ContMetric dim |
          ∀ n, t.2.1 (p n) ≤ C ^ 2 * t.1.1.2.1 (p n)} = ⋂ n, {t | t.2.1 (p n) ≤
            C ^ 2 * t.1.1.2.1 (p n)} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun n => measurableSet_le ((hev n).comp measurable_snd)
        (measurable_const.mul ((hev n).comp
          (measurable_snd.comp (measurable_fst.comp measurable_fst))))
    have hB2 : MeasurableSet {t : (((Fin dim → ℝ) × ContMetric dim) × ContMetric dim) × ContMetric dim |
        ∀ n, t.1.1.2.1 (p n) ≤ C ^ 2 * t.2.1 (p n)} := by
      have : {t : (((Fin dim → ℝ) × ContMetric dim) × ContMetric dim) × ContMetric dim |
          ∀ n, t.1.1.2.1 (p n) ≤ C ^ 2 * t.2.1 (p n)} = ⋂ n, {t | t.1.1.2.1 (p n) ≤
            C ^ 2 * t.2.1 (p n)} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun n => measurableSet_le
        ((hev n).comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
        (measurable_const.mul ((hev n).comp measurable_snd))
    have hθ3 : Measurable fun t : (((Fin dim → ℝ) × ContMetric dim) × ContMetric dim) × ContMetric dim => t.1.1.1 :=
      measurable_fst.comp (measurable_fst.comp measurable_fst)
    exact (measurable_snd hM).inter (hB1.inter (hB2.inter ((measurableSet_eq_fun
      (hY.comp (hθ3.prodMk measurable_snd)) ((hyS k).comp measurable_fst)).inter
      (measurableSet_eq_fun (hFm.comp measurable_snd)
        (hΦ.comp (hθ3.prodMk ((hyS k).comp measurable_fst)))))))
  -- the bad mass at `(θ, d)`
  set Kq : (determFixedBox (d := dim) ε R) → Kernel (((Fin dim → ℝ) × ContMetric dim) × ContMetric dim) (ContMetric dim) := fun k =>
    K.comap (fun q => (q.1.1, yS k q)) ((measurable_fst.comp measurable_fst).prodMk (hyS k))
  have hKq : ∀ k, IsMarkovKernel (Kq k) := fun k => by simp only [Kq]; infer_instance
  have hbadq : ∀ k, Measurable fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim =>
      Kq k q (Prod.mk q ⁻¹' (T k)ᶜ) := fun k =>
    (Kq k).measurable_kernel_prodMk_left (hT k).compl
  set bad : (Fin dim → ℝ) × ContMetric dim → ℝ≥0∞ := fun x =>
    ∑ k, ∫⁻ d', Kq k (x, d') (Prod.mk (x, d') ⁻¹' (T k)ᶜ) ∂ν with hbaddef
  have hbad : Measurable bad :=
    Finset.measurable_sum _ fun k _ => (hbadq k).lintegral_prod_right'
  -- for a.e. `θ`, `bad (θ, ·) = 0` `ν`-a.e. (`LQGMetric.LM.t17v_resample_kernel`)
  set Rel : ContMetric dim → ContMetric dim → Prop := fun d d'' => d'' ∈ M ∧
    (∀ n, d''.1 (p n) ≤ C ^ 2 * d.1 (p n)) ∧ (∀ n, d.1 (p n) ≤ C ^ 2 * d''.1 (p n))
  have hR : ∀ π : Measure (ContMetric dim × ContMetric dim), π.map Prod.fst = ν → π.map Prod.snd = ν →
      ∀ᵐ q ∂π, Rel q.1 q.2 := by
    intro π h1 h2
    have hl : ∀ᵐ q ∂π, q.2 ∈ M := ae_of_ae_map measurable_snd.aemeasurable (h2 ▸ hνM)
    have hb1 := determ_bilip_any_coupling hC hcopy h1 h2
    have hs1 : (π.map Prod.swap).map Prod.fst = ν := by
      rw [Measure.map_map measurable_fst measurable_swap]; exact h2
    have hs2 : (π.map Prod.swap).map Prod.snd = ν := by
      rw [Measure.map_map measurable_snd measurable_swap]; exact h1
    have hb2 := ae_of_ae_map measurable_swap.aemeasurable (determ_bilip_any_coupling hC hcopy hs1 hs2)
    filter_upwards [hl, hb1, hb2] with q hq1 hq2 hq3
    exact ⟨hq1, fun n => hq2 _ _, fun n => hq3 _ _⟩
  have hθd : ∀ᵐ θ ∂(determShiftLaw dim), ∀ᵐ d ∂ν, bad (θ, d) = 0 := by
    filter_upwards [hslice, hΦF, ae_restrict_of_ae hprod] with θ hs hf hp
    have hYθ : Measurable (determY ε θ (determFixedBox (d := dim) ε R)) := determ_measurable_Y ε θ (determFixedBox (d := dim) ε R)
    have hΦθ : Measurable fun y : (determFixedBox (d := dim) ε R) → ℕ → ℝ≥0∞ => Φ (θ, y) :=
      hΦ.comp (measurable_const.prodMk measurable_id)
    have hFθ : F =ᵐ[ν] (fun y : (determFixedBox (d := dim) ε R) → ℕ → ℝ≥0∞ => Φ (θ, y)) ∘ determY ε θ (determFixedBox (d := dim) ε R) := hf
    have hex := LQGMetric.LM.t17v_resample_kernel (ι := (determFixedBox (d := dim) ε R)) (E := ℕ → ℝ≥0∞) ν (Y := determY ε θ (determFixedBox (d := dim) ε R)) hYθ hp
      (F := F) (Φ := fun y => Φ (θ, y)) hΦθ hFm hFθ
      (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) hs Rel hR
    filter_upwards [hex] with d hd
    refine Finset.sum_eq_zero fun k _ => ?_
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hd k] with d' hd'
    simp only [Pi.zero_apply]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    simp only [Kq, Kernel.comap_apply] at hd' ⊢
    filter_upwards [hd'] with d'' ⟨⟨h1, h2, h3⟩, h4, h5⟩
    simp only [mem_preimage, mem_compl_iff, not_not, hTdef, hySdef, mem_ofPred_eq]
    exact ⟨h1, h2, h3, h4, h5⟩
  -- exchange the quantifiers
  have hG : MeasurableSet {x : (Fin dim → ℝ) × ContMetric dim | bad (x.1, x.2) = 0} :=
    measurableSet_eq_fun hbad measurable_const
  have hswap := (Measure.ae_ae_comm (μ := determShiftLaw dim) (ν := ν)
    (p := fun θ d => bad (θ, d) = 0) hG).1 hθd
  filter_upwards [hswap, hνM] with d hdG hdM
  filter_upwards [hdG] with θ hθG b hb
  have hd := hML hdM
  unfold determES
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : ∫⁻ d', Kq k ((θ, d), d') (Prod.mk ((θ, d), d') ⁻¹' (T k)ᶜ) ∂ν = 0 :=
    (Finset.sum_eq_zero_iff.1 hθG) k (Finset.mem_univ k)
  have hk' := (lintegral_eq_zero_iff ((hbadq k).comp (measurable_const.prodMk measurable_id))).1 hk
  have hint : ∀ᵐ d' ∂ν, ENNReal.ofReal (max (Φ (θ, Function.update (determY ε θ (determFixedBox (d := dim) ε R) d) k
      (determY ε θ (determFixedBox (d := dim) ε R) d' k)) - F d) 0 ^ 2) ≤ ENNReal.ofReal (b k) := by
    filter_upwards [hk'] with d' hd'
    have hae : ∀ᵐ d'' ∂K (θ, yS k ((θ, d), d')), (((θ, d), d'), d'') ∈ T k := by
      have := measure_eq_zero_iff_ae_notMem.1 hd'
      simp only [Kq, Kernel.comap_apply] at this
      filter_upwards [this] with d'' h
      simpa using h
    obtain ⟨d'', h1, h2, h3, h4, h5⟩ := @Filter.Eventually.exists _ _ _ (by infer_instance) hae
    refine ENNReal.ofReal_le_ofReal ?_
    have hΦe : Φ (θ, Function.update (determY ε θ (determFixedBox (d := dim) ε R) d) k (determY ε θ (determFixedBox (d := dim) ε R) d' k)) = F d'' := h5.symm
    rw [hΦe]
    refine hb k d'' ⟨hML h1, determ_le_of_dense h2, determ_le_of_dense h3, fun j hj hjk => ?_⟩
    have hjk' : (⟨j, hj⟩ : (determFixedBox (d := dim) ε R)) ≠ k := fun h => hjk (by rw [← h])
    have henc : determ_enc (determCube ε θ j) d'' = determ_enc (determCube ε θ j) d := by
      have := congrFun h4 ⟨j, hj⟩
      simp only [hySdef] at this
      rwa [Function.update_of_ne hjk'] at this
    exact determ_internal_eq_of_enc hd (hML h1) (determ_isOpen_cube ε θ j) henc
  calc ∫⁻ d', ENNReal.ofReal (max (Φ (θ, Function.update (determY ε θ (determFixedBox (d := dim) ε R) d) k
        (determY ε θ (determFixedBox (d := dim) ε R) d' k)) - F d) 0 ^ 2) ∂ν
      ≤ ∫⁻ _, ENNReal.ofReal (b k) ∂ν := lintegral_mono_ae hint
    _ = ENNReal.ofReal (b k) := by rw [lintegral_const, measure_univ, mul_one]

end HigherDimLQGMetric
