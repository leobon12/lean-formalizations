import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import LQGMetric.Meas.UM
import LQGMetric.Field.StandardBorelRange
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas




 







set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids

open LQGMetric (DistC DistOn addConst restrictTo circleAvg)
open SupercriticalLQGUniqueness

 
theorem canonical_centered_locality
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (z : ℂ) (r : Ioi (0 : ℝ))
    (U : TopologicalSpace.Opens ℂ) :
    ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞),
      Measurable F ∧
        ∀ᵐ u ∂μ, (D (addConst u (-circleAvg u r z))).internal (U : Set ℂ) =
          F (restrictTo U (addConst u (-circleAvg u r z))) := by
  exact hD.locality μ (fun u => addConst u (-circleAvg u r z))
    (center_at_circleAvg_isGFFPlusCont hμ z r) U

 
theorem canonical_centered_internal_scale
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ u ∂μ, ∀ (U : Set ℂ) (p : U × U),
      (D (addConst u (-circleAvg u r z))).internal U p =
        ENNReal.ofReal (Real.exp (-((ξ : ℝ) * circleAvg u r z))) *
          (D u).internal U p := by
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  filter_upwards [Positivity.Witnesses.ae_internal_addConst_eq_mul μ id hwhole ξ Q D hD
      (fun u => -circleAvg u r z)] with u hu U p
  simpa only [id_eq, mul_neg] using hu U p

 
theorem scale_cancel_lower_bound (t a : ℝ)
    (d e : ℝ≥0∞)
    (hd : ENNReal.ofReal (t * Real.exp a) ≤ d)
    (he : e = ENNReal.ofReal (Real.exp (-a)) * d) :
    ENNReal.ofReal t ≤ e := by
  rw [he]
  calc
    ENNReal.ofReal t = ENNReal.ofReal (Real.exp (-a)) *
        ENNReal.ofReal (t * Real.exp a) := by
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
      congr 1
      calc
        t = t * (Real.exp (-a) * Real.exp a) := by
          rw [← Real.exp_add]
          simp only [neg_add_cancel, Real.exp_zero, mul_one]
        _ = Real.exp (-a) * (t * Real.exp a) := by ring
    _ ≤ ENNReal.ofReal (Real.exp (-a)) * d := by gcongr

 
theorem ambient_success_implies_internal
    (D₀ D₁ : LSCMetric) (A : EuclideanAnnulus) (U : Set ℂ)
    (t a : ℝ)
    (hscale : ∀ p : U × U,
      D₁.internal U p = ENNReal.ofReal (Real.exp (-a)) * D₀.internal U p)
    (hsuccess : ENNReal.ofReal (t * Real.exp a) ≤ acrossDist D₀ A)
    (hinner : A.innerBoundary ⊆ U) (houter : A.outerBoundary ⊆ U) :
    ∀ (x : ℂ) (hx : x ∈ A.innerBoundary) (y : ℂ) (hy : y ∈ A.outerBoundary),
      ENNReal.ofReal t ≤ D₁.internal U (⟨x, hinner hx⟩, ⟨y, houter hy⟩) := by
  intro x hx y hy
  let p : U × U := (⟨x, hinner hx⟩, ⟨y, houter hy⟩)
  have hcost : ENNReal.ofReal (t * Real.exp a) ≤ D₀.internal U p :=
    hsuccess.trans (acrossDist_le_internal D₀ A U x y hx hy (hinner hx) (houter hy))
  exact scale_cancel_lower_bound t a _ _ hcost (hscale p)

theorem s1_analytic_local_subset
    {β γ : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    [TopologicalSpace γ] [T2Space γ] [PolishSpace γ] [MeasurableSpace γ]
    [BorelSpace γ]
    (μ : Measure β) [IsProbabilityMeasure μ]
    (R V : β → γ)
    (hR : Measurable R)
    (hVR : ∀ᵐ u ∂μ, V u = R u)
    (A W B : Set β)
    (hA : NullMeasurableSet A μ)
    (hW : MeasurableSet W) (hWae : ∀ᵐ u ∂μ, u ∈ W)
    (hAB : A ∩ W ⊆ B)
    (hsat : ∀ u ∈ W, ∀ v ∈ W, R u = R v → u ∈ B → v ∈ B) :
    ∃ A₀ E : Set β,
      MeasurableSet A₀ ∧ A₀ ⊆ A ∩ W ∧ μ A₀ = μ A ∧
      MeasurableSet[MeasurableSpace.comap V inferInstance] E ∧
        μ E = (μ.map R) (R '' A₀) ∧ μ A₀ ≤ μ E ∧
      (∀ᵐ u ∂μ, u ∈ E → u ∈ B) := by
  have hAW : NullMeasurableSet (A ∩ W) μ := hA.inter hW.nullMeasurableSet
  obtain ⟨A₀, hA₀sub, hA₀m, hA₀ae⟩ := hAW.exists_measurable_subset_ae_eq
  have hAWeq : A ∩ W =ᵐ[μ] A := by
    filter_upwards [hWae] with u hu
    simp only [mem_inter_iff, hu, and_true]
  have hA₀eq : μ A₀ = μ A := by
    calc μ A₀ = μ (A ∩ W) := measure_congr hA₀ae
      _ = μ A := measure_congr hAWeq
  let S : Set γ := R '' A₀
  have hSn : NullMeasurableSet S (μ.map R) :=
    QuantumZipper.Thm18Asm.G4Core.analyticSet_nullMeasurableSet
      (hA₀m.analyticSet_image hR) (μ.map R)
  obtain ⟨S₁, hS₁sub, hS₁m, hS₁ae⟩ := hSn.exists_measurable_subset_ae_eq
  let E : Set β := V ⁻¹' S₁
  have hEe : μ E = (μ.map R) S := by
    have hER : E =ᵐ[μ] R ⁻¹' S₁ := by
      filter_upwards [hVR] with u hu
      simp only [E, mem_preimage, hu]
    calc
      μ E = μ (R ⁻¹' S₁) := measure_congr hER
      _ = (μ.map R) S₁ := (Measure.map_apply hR hS₁m).symm
      _ = (μ.map R) S := measure_congr hS₁ae
  have hV : Measurable[MeasurableSpace.comap V inferInstance] V :=
    Measurable.of_comap_le le_rfl
  have hprob : μ A₀ ≤ μ E := by
    rw [hEe]
    exact Measure.le_map_apply_image hR.aemeasurable A₀
  refine ⟨A₀, E, hA₀m, hA₀sub, hA₀eq, hV hS₁m, hEe, hprob, ?_⟩
  filter_upwards [hVR, hWae] with u hu hWu hEu
  have hRu : R u ∈ S := hS₁sub (by simpa only [E, mem_preimage, hu] using hEu)
  obtain ⟨v, hA₀v, hRv⟩ := hRu
  have hWv : v ∈ W := (hA₀sub hA₀v).2
  exact hsat v hWv u hWu hRv (hAB (hA₀sub hA₀v))


end SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids
