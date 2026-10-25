import SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids.AX10Measure
import LQGMetric.Field.Measurable




 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales

open LQGMetric (DistC addConst restrictTo circleAvg pairJ)
open SupercriticalLQGUniqueness
open LQGMetric.Blueprint

def collar (z : ℂ) (r : Set.Ioi (0 : ℝ)) : TopologicalSpace.Opens ℂ :=
  annulus z ((1 / 2 : ℝ) * r) ((9 / 10 : ℝ) * r)

def shape (z : ℂ) (r : Set.Ioi (0 : ℝ)) : EuclideanAnnulus :=
  Positivity.Witnesses.annulusTranslate (Positivity.Witnesses.crossingAnnulus.dilate r r.2) z

theorem inner_subset_collar (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    (shape z r).innerBoundary ⊆ (collar z r : Set ℂ) := by
  intro x hx
  simp only [shape, Positivity.Witnesses.annulusTranslate, Positivity.Witnesses.crossingAnnulus,
    EuclideanAnnulus.innerBoundary, EuclideanAnnulus.center,
    EuclideanAnnulus.innerRadius, EuclideanAnnulus.dilate,
    Metric.mem_sphere] at hx
  change (1 / 2 : ℝ) * r < ‖x - z‖ ∧ ‖x - z‖ < (9 / 10 : ℝ) * r
  rw [← dist_eq_norm]
  simp only [smul_zero, zero_add] at hx
  have hr : (0 : ℝ) < r := r.2
  constructor <;> nlinarith

theorem outer_subset_collar (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    (shape z r).outerBoundary ⊆ (collar z r : Set ℂ) := by
  intro x hx
  simp only [shape, Positivity.Witnesses.annulusTranslate, Positivity.Witnesses.crossingAnnulus,
    EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center,
    EuclideanAnnulus.outerRadius, EuclideanAnnulus.dilate,
    Metric.mem_sphere] at hx
  change (1 / 2 : ℝ) * r < ‖x - z‖ ∧ ‖x - z‖ < (9 / 10 : ℝ) * r
  rw [← dist_eq_norm]
  simp only [smul_zero, zero_add] at hx
  have hr : (0 : ℝ) < r := r.2
  constructor <;> nlinarith

 
theorem local_good_event_original
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (p c : ℝ) (_hc : 0 < c)
    (htail : ∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)),
      ENNReal.ofReal p ≤ μ {u |
        ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u r z)) ≤ acrossDist (D u) (shape z r)})
    (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    ∃ E : Set DistC,
      MeasurableSet[fieldSigma (fun u => addConst u (-circleAvg u r z)) (collar z r)] E ∧
      ENNReal.ofReal p ≤ μ E ∧
      (∀ᵐ u ∂μ, u ∈ E →
        ∀ (x : ℂ) (hx : x ∈ (shape z r).innerBoundary)
          (y : ℂ) (hy : y ∈ (shape z r).outerBoundary),
          ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q)) ≤
            (D (addConst u (-circleAvg u r z))).internal (collar z r : Set ℂ)
              (⟨x, inner_subset_collar z r hx⟩,
               ⟨y, outer_subset_collar z r hy⟩)) := by
  let U := collar z r
  let G : DistC → DistC := fun u => addConst u (-circleAvg u r z)
  let R : DistC → (LQGMetric.CoordJ → ℝ) := fun u =>
    pairJ U (restrictTo U (G u))
  let A : Set DistC := {u |
    ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg u r z)) ≤ acrossDist (D u) (shape z r)}
  let B : Set DistC := {u | ∀ (x : ℂ) (hx : x ∈ (shape z r).innerBoundary)
      (y : ℂ) (hy : y ∈ (shape z r).outerBoundary),
      ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q)) ≤
        (D (G u)).internal (U : Set ℂ)
          (⟨x, inner_subset_collar z r hx⟩,
           ⟨y, outer_subset_collar z r hy⟩)}
  obtain ⟨F, hFm, hloc⟩ :=
    Positivity.Grids.canonical_centered_locality μ hμ ξ Q D hD z r U
  have hscale := Positivity.Grids.canonical_centered_internal_scale μ hμ ξ Q D hD z r
  let Wraw : Set DistC := {u |
    (D (G u)).internal (U : Set ℂ) = F (restrictTo U (G u)) ∧
    ∀ q : (↥(U : Set ℂ)) × (↥(U : Set ℂ)),
      (D (G u)).internal (U : Set ℂ) q =
        ENNReal.ofReal (Real.exp (-((ξ : ℝ) * circleAvg u r z))) *
          (D u).internal (U : Set ℂ) q}
  have hWraw : ∀ᵐ u ∂μ, u ∈ Wraw := by
    filter_upwards [hloc, hscale] with u hu hs
    exact ⟨hu, hs (U : Set ℂ)⟩
  obtain ⟨W, hWae, hWm, hWsub⟩ := hWraw.exists_measurable_mem
  have hAm : MeasurableSet A := by
    dsimp [A]
    apply measurableSet_le
    · exact (measurable_const.mul (((LQGMetric.measurable_circleAvg_left r z).const_mul _).exp)).ennreal_ofReal
    · exact (measurable_acrossDist (shape z r)).comp hD.measurable
  have hRm : Measurable R := by
    apply (LQGMetric.measurable_pairJ U).comp
    apply (LQGMetric.measurable_restrictTo U).comp
    dsimp [G]
    exact LQGMetric.DFGPS.L219.measurable_addConst_of measurable_id
      (LQGMetric.measurable_circleAvg_left r z).neg
  have hAB : A ∩ W ⊆ B := by
    intro u hu
    have hw := hWsub u hu.2
    intro x hx y hy
    exact Positivity.Grids.ambient_success_implies_internal (D u) (D (G u)) (shape z r)
      (U : Set ℂ) (c * (r : ℝ) ^ ((ξ : ℝ) * Q))
      ((ξ : ℝ) * circleAvg u r z) hw.2 hu.1
      (inner_subset_collar z r) (outer_subset_collar z r) x hx y hy
  have hsat : ∀ u ∈ W, ∀ v ∈ W, R u = R v → u ∈ B → v ∈ B := by
    intro u hu v hv huv hub
    have hres : restrictTo U (G u) = restrictTo U (G v) :=
      LQGMetric.injective_pairJ U huv
    have hDuv : (D (G u)).internal (U : Set ℂ) =
        (D (G v)).internal (U : Set ℂ) := by
      rw [(hWsub u hu).1, (hWsub v hv).1, hres]
    intro x hx y hy
    rw [← hDuv]
    exact hub x hx y hy
  obtain ⟨A₀, E, hA₀m, hA₀sub, hA₀eq, hEm, hEeq, hEge, hEimp⟩ :=
    Positivity.Grids.s1_analytic_local_subset μ R R hRm (ae_eq_refl R)
      A W B hAm.nullMeasurableSet hWm hWae hAB hsat
  refine ⟨E, ?_, ?_, ?_⟩
  · obtain ⟨S, hSm, hSE⟩ := hEm
    rw [← hSE]
    have hRfield : Measurable[fieldSigma G U] R := by
      exact (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
    exact hRfield hSm
  · calc
      ENNReal.ofReal p ≤ μ A := htail z r
      _ = μ A₀ := hA₀eq.symm
      _ ≤ μ E := hEge
  · exact hEimp

 
private theorem centered_collar_relation (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    ∀ y : ℂ, y ∈ annulus 0 ((1 / 2 : ℝ) * r) ((9 / 10 : ℝ) * r) ↔
      (1 : ℝ) • y + z ∈ collar z r := by
  intro y
  change ((1 / 2 : ℝ) * r < ‖y - 0‖ ∧ ‖y - 0‖ < (9 / 10 : ℝ) * r) ↔
    ((1 / 2 : ℝ) * r < ‖(1 : ℝ) • y + z - z‖ ∧
      ‖(1 : ℝ) • y + z - z‖ < (9 / 10 : ℝ) * r)
  simp only [sub_zero, one_smul, add_sub_cancel_right]

 
theorem scale_restore_lower_bound (t a : ℝ) (d e : ℝ≥0∞)
    (he : e = ENNReal.ofReal (Real.exp (-a)) * d)
    (ht : ENNReal.ofReal t ≤ e) :
    ENNReal.ofReal (t * Real.exp a) ≤ d := by
  have hmul : ENNReal.ofReal (Real.exp a) *
      ENNReal.ofReal (Real.exp (-a)) = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)),
      ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one]
  calc
    ENNReal.ofReal (t * Real.exp a) =
        ENNReal.ofReal (Real.exp a) * ENNReal.ofReal t := by
      rw [mul_comm t, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    _ ≤ ENNReal.ofReal (Real.exp a) * e := by gcongr
    _ = d := by rw [he, ← mul_assoc, hmul, one_mul]

 
theorem local_good_event_translated
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (p c : ℝ) (hc : 0 < c)
    (htail : ∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)),
      ENNReal.ofReal p ≤ μ {u |
        ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u r z)) ≤ acrossDist (D u) (shape z r)})
    (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    ∃ E : Set DistC,
      MeasurableSet[fieldSigma
        (fun u => addConst
          (addConst (translateDist z u) (-circleAvg u 1 z))
          (-circleAvg (addConst (translateDist z u) (-circleAvg u 1 z)) r 0))
        (annulus 0 ((1 / 2 : ℝ) * r) ((9 / 10 : ℝ) * r))] E ∧
      ENNReal.ofReal p ≤ μ E ∧
      (∀ᵐ u ∂μ, u ∈ E →
        ∀ (x : ℂ) (hx : x ∈ (shape z r).innerBoundary)
          (y : ℂ) (hy : y ∈ (shape z r).outerBoundary),
          ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q)) ≤
            (D (addConst u (-circleAvg u r z))).internal (collar z r : Set ℂ)
              (⟨x, inner_subset_collar z r hx⟩,
               ⟨y, outer_subset_collar z r hy⟩)) := by
  obtain ⟨E₀, hE₀m, hE₀p, hE₀imp⟩ :=
    local_good_event_original μ hμ ξ Q D hD p c hc htail z r
  have hAE : AEEventIn μ
      (fieldSigma
        (fun u => addConst
          (addConst (translateDist z u) (-circleAvg u 1 z))
          (-circleAvg (addConst (translateDist z u) (-circleAvg u 1 z)) r 0))
        (annulus 0 ((1 / 2 : ℝ) * r) ((9 / 10 : ℝ) * r))) E₀ :=
    aeEventIn_centered_translate hμ z r (collar z r)
      (annulus 0 ((1 / 2 : ℝ) * r) ((9 / 10 : ℝ) * r))
      (centered_collar_relation z r) ⟨E₀, hE₀m, Filter.Eventually.of_forall (fun _ => rfl)⟩
  obtain ⟨E, hEm, hEeq⟩ := hAE
  refine ⟨E, hEm, ?_, ?_⟩
  · calc
      ENNReal.ofReal p ≤ μ E₀ := hE₀p
      _ = μ E := measure_congr hEeq
  · filter_upwards [hEeq, hE₀imp] with u hu hi hEu
    exact hi (hu.mpr hEu)

 
def Paid (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (c : ℝ) (z : ℂ) (r : Set.Ioi (0 : ℝ)) (u : DistC) : Prop :=
  ∀ (x : ℂ) (hx : x ∈ (shape z r).innerBoundary)
    (y : ℂ) (hy : y ∈ (shape z r).outerBoundary),
    ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg u r z)) ≤
      (D u).internal (collar z r : Set ℂ)
        (⟨x, inner_subset_collar z r hx⟩,
         ⟨y, outer_subset_collar z r hy⟩)

 
theorem local_good_event_paid
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (p c : ℝ) (hc : 0 < c)
    (htail : ∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)),
      ENNReal.ofReal p ≤ μ {u |
        ENNReal.ofReal (c * (r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * circleAvg u r z)) ≤ acrossDist (D u) (shape z r)})
    (z : ℂ) (r : Set.Ioi (0 : ℝ)) :
    ∃ E : Set DistC,
      MeasurableSet[fieldSigma
        (fun u => addConst
          (addConst (translateDist z u) (-circleAvg u 1 z))
          (-circleAvg (addConst (translateDist z u) (-circleAvg u 1 z)) r 0))
        (annulus 0 ((1 / 2 : ℝ) * r) ((9 / 10 : ℝ) * r))] E ∧
      ENNReal.ofReal p ≤ μ E ∧
      (∀ᵐ u ∂μ, u ∈ E → Paid ξ Q D c z r u) := by
  obtain ⟨E, hEm, hEp, hEi⟩ :=
    local_good_event_translated μ hμ ξ Q D hD p c hc htail z r
  refine ⟨E, hEm, hEp, ?_⟩
  have hs := Positivity.Grids.canonical_centered_internal_scale μ hμ ξ Q D hD z r
  filter_upwards [hEi, hs] with u hi hu hEu
  intro x hx y hy
  exact scale_restore_lower_bound
    (c * (r : ℝ) ^ ((ξ : ℝ) * Q)) ((ξ : ℝ) * circleAvg u r z)
    ((D u).internal (collar z r : Set ℂ)
      (⟨x, inner_subset_collar z r hx⟩,
       ⟨y, outer_subset_collar z r hy⟩))
    ((D (addConst u (-circleAvg u r z))).internal (collar z r : Set ℂ)
      (⟨x, inner_subset_collar z r hx⟩,
       ⟨y, outer_subset_collar z r hy⟩))
    (hu (collar z r : Set ℂ) _) (hi hEu x hx y hy)

 
def dyadicRadius (k : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨((2 : ℝ) ^ k)⁻¹, Set.mem_Ioi.mpr (by positivity)⟩

 
theorem ax10_dyadic_events
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (G : ℕ → Finset ℂ) :
    ∃ (c : ℝ) (E : ℂ → ℕ → Set DistC), 0 < c ∧
      (∀ (z : ℂ) (k : ℕ),
        MeasurableSet[fieldSigma
          (fun u => addConst
            (addConst (translateDist z u) (-circleAvg u 1 z))
            (-circleAvg (addConst (translateDist z u) (-circleAvg u 1 z))
              (dyadicRadius k) 0))
          (annulus 0 ((1 / 2 : ℝ) * (dyadicRadius k : ℝ))
            ((9 / 10 : ℝ) * (dyadicRadius k : ℝ)))] (E z k)) ∧
      (∀ (z : ℂ) (k : ℕ), ENNReal.ofReal p ≤ μ (E z k)) ∧
      (∀ᵐ u ∂μ, ∀ K : ℕ, ∀ z ∈ G K, ∀ k : ℕ,
        u ∈ E z k → Paid ξ Q D c z (dyadicRadius k) u) := by
  obtain ⟨c, hc, htail⟩ := Positivity.Witnesses.ax9_canonical_tail μ hμ ξ Q D hD p hp0 hp1
  have hex (z : ℂ) (k : ℕ) : ∃ E : Set DistC,
      MeasurableSet[fieldSigma
        (fun u => addConst
          (addConst (translateDist z u) (-circleAvg u 1 z))
          (-circleAvg (addConst (translateDist z u) (-circleAvg u 1 z))
            (dyadicRadius k) 0))
        (annulus 0 ((1 / 2 : ℝ) * (dyadicRadius k : ℝ))
          ((9 / 10 : ℝ) * (dyadicRadius k : ℝ)))] E ∧
      ENNReal.ofReal p ≤ μ E ∧
      (∀ᵐ u ∂μ, u ∈ E → Paid ξ Q D c z (dyadicRadius k) u) := by
    exact local_good_event_paid μ hμ ξ Q D hD p c hc htail z (dyadicRadius k)
  choose E hE using hex
  refine ⟨c, E, hc, (fun z k => (hE z k).1),
    (fun z k => (hE z k).2.1), ?_⟩
  have hK (K : ℕ) : ∀ᵐ u ∂μ, ∀ z ∈ G K, ∀ k : ℕ,
      u ∈ E z k → Paid ξ Q D c z (dyadicRadius k) u := by
    have hzk (z : {z : ℂ // z ∈ G K}) :
        ∀ᵐ u ∂μ, ∀ k : ℕ,
          u ∈ E z.1 k → Paid ξ Q D c z.1 (dyadicRadius k) u := by
      exact ae_all_iff.mpr (fun k => (hE z.1 k).2.2)
    have hzall : ∀ᵐ u ∂μ, ∀ z : {z : ℂ // z ∈ G K}, ∀ k : ℕ,
          u ∈ E z.1 k → Paid ξ Q D c z.1 (dyadicRadius k) u :=
      ae_all_iff.mpr hzk
    filter_upwards [hzall] with u hu z hz k hEuk
    exact hu ⟨z, hz⟩ k hEuk
  exact ae_all_iff.mpr hK






end SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales
