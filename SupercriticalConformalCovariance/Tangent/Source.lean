import SupercriticalConformalCovariance.Tangent.LscLemmas
import SupercriticalConformalCovariance.Domain.Sample
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas

/-!
# Lemma 3.3: the source metrics `d_n = D_h(·,·;K_n)`

Paper l. 194–198: `d_n = D_h(·,·;K_n)`, `K_n = B̄_{R_n}`, extended by `+∞` outside `K_n × K_n`.
`d_n → D_h` holds **almost surely**, deterministically on the sample event where `D_h` is a length
space whose curves are Euclidean continuous: `d_n ≥ D_h`, and a near-geodesic of finite length is
Euclidean compact, hence inside `K_n` for large `n`. Lemma 3.2 (expanding confinement) is not
needed for `d_n`; the paper's route through it (l. 224–230, "identifies every subsequential
marginal limit of `d_n` ... as `D_h`") is correct but not necessary for this coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCMetric LSCTendsto IsStrongLQGMetric)
open LQGMetric (DistC IsGFFPlusCont)

/-- The internal metric of `D` on `K`, extended by `+∞` outside `K × K` (paper l. 196). -/
def extInternal (D : LSCMetric) (K : Set ℂ) (q : ℂ × ℂ) : ℝ≥0∞ :=
  open Classical in if hq : q.1 ∈ K ∧ q.2 ∈ K then D.internal K (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩) else ⊤

theorem le_extInternal (D : LSCMetric) (K : Set ℂ) (q : ℂ × ℂ) : D q ≤ extInternal D K q := by
  unfold extInternal
  split_ifs with hq
  · exact D.edist_le_internal K (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)
  · exact le_top

theorem extInternal_le_len (D : LSCMetric) (K : Set ℂ) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hK : ∀ t ∈ Icc a b, P t ∈ K) :
    extInternal D K (P a, P b) ≤ D.len P a b := by
  unfold extInternal
  rw [dite_cond_eq_true (eq_true ⟨hK a ⟨le_rfl, hP.1⟩, hK b ⟨hP.1, le_rfl⟩⟩)]
  exact D.internal_le_len K P a b hP hK

/-- **Deterministic core.** If `D` is a length space whose curves are Euclidean continuous
(`Continuous (forget D)`), then the internal metrics on closed disks of radii `R_n → ∞`, extended
by `+∞`, converge to `D` in the sense of DG Definition 1.2. -/
theorem lscTendsto_extInternal_of_sample (D : LSCMetric)
    (hf : Continuous (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget D))
    (hL : D.IsLengthSpace) {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    LSCTendsto (fun n q => (extInternal D (closedBall 0 (R n)) q : EReal))
      (fun q => (D q : EReal)) := by
  refine lscTendsto_of_ge_of_tendsto ?_ (Eventually.of_forall fun n q =>
    EReal.coe_ennreal_le_coe_ennreal_iff.2 (le_extInternal D _ q)) fun q => ?_
  · exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous D.lowerSemicontinuous
      EReal.coe_ennreal_strictMono.monotone
  · refine (continuous_coe_ennreal_ereal.tendsto _).comp ?_
    refine tendsto_order.2 ⟨fun c hc => Eventually.of_forall fun n =>
      hc.trans_le (le_extInternal D _ q), fun c hc => ?_⟩
    have hfin : D q < ⊤ := hc.trans_le le_top
    obtain ⟨r, hr0, hrc⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hc
    obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ := hL q.1 q.2 hfin (r : ℝ) (by exact_mod_cast hr0)
    -- the curve is Euclidean continuous, hence bounded
    have hPc : ContinuousOn P (Icc a b) := hf.comp_continuousOn hP.2
    obtain ⟨ρ, hρ⟩ := ((isCompact_Icc.image_of_continuousOn hPc).isBounded).subset_closedBall 0
    filter_upwards [hR.eventually_ge_atTop ρ] with n hn
    have hK : ∀ t ∈ Icc a b, P t ∈ closedBall (0 : ℂ) (R n) := fun t ht =>
      closedBall_subset_closedBall hn (hρ (mem_image_of_mem P ht))
    calc extInternal D (closedBall 0 (R n)) q
        = extInternal D (closedBall 0 (R n)) (P a, P b) := by rw [hPa, hPb]
      _ ≤ D.len P a b := extInternal_le_len D _ hP hK
      _ ≤ D (q.1, q.2) + ENNReal.ofReal r := hlen
      _ < c := by simpa using hrc

/-- **`d_n → D_h` almost surely** (paper l. 194–198, (5), first metric coordinate), for every whole
plane GFF plus a continuous function `h` and every `R_n → ∞`. -/
theorem ae_lscTendsto_source {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusCont h P) {R : ℕ → ℝ}
    (hR : Tendsto R atTop atTop) :
    ∀ᵐ ω ∂P, LSCTendsto (fun n q => (extInternal (D (h ω)) (closedBall 0 (R n)) q : EReal))
      (fun q => (D (h ω) q : EReal)) := by
  filter_upwards [SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P h hh] with ω hω
  obtain ⟨hf, hL, _⟩ := hω
  exact lscTendsto_extInternal_of_sample _ hf hL hR

end SupercriticalConformalCovariance.Tangent
