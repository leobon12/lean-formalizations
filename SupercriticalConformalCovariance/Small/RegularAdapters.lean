import SupercriticalConformalCovariance.Regular.Measurability
import SupercriticalConformalCovariance.Selection.JVN

set_option autoImplicit false
noncomputable section

namespace SupercriticalConformalCovariance.Small

open SupercriticalLQGUniqueness
open SupercriticalConformalCovariance.Regular
open MeasureTheory

/-- The field-dependent normalization in (7) can be replaced by a fixed upper
bound on the event where that normalization is bounded. -/
theorem sourceRegularPair_mono_m
    (D : LSCMetric) (z u v : ℂ) (r α θ m m' : ℝ)
    (hα : α < 1) (hmm' : m ≤ m')
    (h : SourceRegularPair D z u v r α θ m) :
    SourceRegularPair D z u v r α θ m' := by
  rcases h with ⟨hgeo, hu, hv, h7, h8u, h8v⟩
  have hfac : 0 ≤ (1 - α)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hα.le)
  have hmul : (1 - α)⁻¹ * m ≤ (1 - α)⁻¹ * m' :=
    mul_le_mul_of_nonneg_left hmm' hfac
  exact ⟨hgeo, hu, hv, le_trans h7 (ENNReal.ofReal_le_ofReal hmul), h8u, h8v⟩

/-- A fixed bound on the source normalization gives a fixed-distance Borel
failure relation. The source regularity tests (8) are unchanged. -/
theorem sourceFailure_of_regular_and_bound
    (D E : LSCMetric) (z u v : ℂ) (α θ m T η : ℝ)
    (hα : α < 1) (hmT : m ≤ T)
    (hreg : SourceRegularPair D z u v 1 α θ m)
    (hfail : ENNReal.ofReal (1 + η) * D (u, v) ≤ E (u, v)) :
    SourceFailure D E z u v 1 α θ T ((1 - α)⁻¹ * T) (1 - α) η := by
  have hsep : 1 - α ≤ dist u v := by
    have hu : dist u z = α := by
      simpa only [Metric.mem_sphere, mul_one] using hreg.2.1
    have hv : dist v z = 1 := by
      simpa only [Metric.mem_sphere] using hreg.2.2.1
    have htri := dist_triangle v u z
    rw [hv, dist_comm v u, hu] at htri
    linarith
  have hregT := sourceRegularPair_mono_m D z u v 1 α θ m T hα hmT hreg
  exact ⟨hregT, hregT.2.2.2.1, hsep, hfail⟩

/-- Printed Lemma 4.2/JvN step on a Polish field coordinate, after the
normalization threshold has been made deterministic. -/
theorem selected_witnesses_of_source_failure
    {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → X) (hZ : Measurable Z)
    (D E : X → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (z : ℂ) (r α θ m M b η : ℝ) :
    ∃ W : Ω → Witness, AEMeasurable W P ∧
      ∀ ω, (∃ u v : ℂ, SourceFailure (D (Z ω)) (E (Z ω))
          z u v r α θ m M b η) →
        FailureWitness z r α θ m M b η ((D (Z ω), E (Z ω)), W ω) := by
  let A : Set (X × Witness) :=
    {p | FailureWitness z r α θ m M b η ((D p.1, E p.1), p.2)}
  have hp : Measurable (fun p : X × Witness => ((D p.1, E p.1), p.2)) :=
    ((hD.comp measurable_fst).prodMk (hE.comp measurable_fst)).prodMk measurable_snd
  have hA : AnalyticSet A :=
    ((failureWitness_borel z r α θ m M b η).preimage hp).analyticSet
  obtain ⟨W, hW, hselect⟩ :=
    SupercriticalConformalCovariance.Selection.analytic_uniformization_probability P hZ hA
  refine ⟨W, hW, ?_⟩
  intro ω hfailure
  apply hselect ω
  rcases hfailure with ⟨u, v, huv⟩
  obtain ⟨Q, hQ⟩ :=
    (sourceFailure_iff_witness (D (Z ω)) (E (Z ω)) z u v
      r α θ m M b η).mp huv
  exact ⟨(Z ω, (Q, (u, v))), hQ, rfl⟩

/-- The selector has a Borel measurable version, sufficient to adjoin to a
joint law before Skorokhod representation. Its witness property holds a.s. -/
theorem selected_measurable_witnesses_of_source_failure
    {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → X) (hZ : Measurable Z)
    (D E : X → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (z : ℂ) (r α θ m M b η : ℝ) :
    ∃ W : Ω → Witness, Measurable W ∧
      ∀ᵐ ω ∂P, (∃ u v : ℂ, SourceFailure (D (Z ω)) (E (Z ω))
          z u v r α θ m M b η) →
        FailureWitness z r α θ m M b η ((D (Z ω), E (Z ω)), W ω) := by
  obtain ⟨W, hW, hselect⟩ :=
    selected_witnesses_of_source_failure P Z hZ D E hD hE z r α θ m M b η
  refine ⟨hW.mk W, hW.measurable_mk, ?_⟩
  filter_upwards [hW.ae_eq_mk] with ω hω
  rw [← hω]
  exact hselect ω

/-- The compact-coordinate version used by Proposition 4.3: only endpoints
are adjoined to the joint Skorokhod law, not the path code. -/
theorem selected_measurable_endpoints_of_source_failure
    {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → X) (hZ : Measurable Z)
    (D E : X → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (z : ℂ) (r α θ m M b η : ℝ) :
    ∃ V : Ω → ℂ × ℂ, Measurable V ∧
      ∀ᵐ ω ∂P, (∃ u v : ℂ, SourceFailure (D (Z ω)) (E (Z ω))
          z u v r α θ m M b η) →
        SourceFailure (D (Z ω)) (E (Z ω))
          z (V ω).1 (V ω).2 r α θ m M b η := by
  obtain ⟨W, hW, hselect⟩ :=
    selected_measurable_witnesses_of_source_failure P Z hZ D E hD hE
      z r α θ m M b η
  refine ⟨fun ω => (W ω).2, measurable_snd.comp hW, ?_⟩
  filter_upwards [hselect] with ω hω
  intro hfailure
  exact (sourceFailure_iff_witness (D (Z ω)) (E (Z ω))
    z (W ω).2.1 (W ω).2.2 r α θ m M b η).mpr ⟨(W ω).1, hω hfailure⟩

/-- At unit scale, the selected endpoints can be made to lie in a fixed
compact disk on every sample, while preserving the failure witness a.s. -/
theorem selected_compact_endpoints_of_source_failure
    {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → X) (hZ : Measurable Z)
    (D E : X → LSCMetric) (hD : Measurable D) (hE : Measurable E)
    (z : ℂ) (α θ m M η : ℝ) (hα : α ≤ 1) :
    ∃ V : Ω → ℂ × ℂ, Measurable V ∧
      (∀ ω, (V ω).1 ∈ Metric.closedBall z 1 ∧
        (V ω).2 ∈ Metric.closedBall z 1) ∧
      (∀ᵐ ω ∂P, (∃ u v : ℂ, SourceFailure (D (Z ω)) (E (Z ω))
          z u v 1 α θ m M (1 - α) η) →
        SourceFailure (D (Z ω)) (E (Z ω))
          z (V ω).1 (V ω).2 1 α θ m M (1 - α) η) := by
  classical
  obtain ⟨V, hV, hselect⟩ :=
    selected_measurable_endpoints_of_source_failure P Z hZ D E hD hE
      z 1 α θ m M (1 - α) η
  let K : Set ℂ := Metric.closedBall z 1
  let B : Set (ℂ × ℂ) := K ×ˢ K
  have hB : MeasurableSet B :=
    (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall).measurableSet
  let V' : Ω → ℂ × ℂ := fun ω => if V ω ∈ B then V ω else ((z, z) : ℂ × ℂ)
  have hV' : Measurable V' :=
    Measurable.ite (hB.preimage hV) hV measurable_const
  refine ⟨V', hV', ?_, ?_⟩
  · intro ω
    change V' ω ∈ B
    by_cases hω : V ω ∈ B
    · simp only [V', hω, ↓reduceIte]
    · have hz : z ∈ K := by simp only [K, Metric.mem_closedBall, dist_self]; norm_num
      simpa only [V', hω, ↓reduceIte] using (show (z, z) ∈ B from ⟨hz, hz⟩)
  · filter_upwards [hselect] with ω hω
    intro hex
    have hf := hω hex
    have hu : (V ω).1 ∈ K := by
      have hs : dist (V ω).1 z = α := by
        simpa only [Metric.mem_sphere, mul_one] using hf.1.2.1
      change dist (V ω).1 z ≤ 1
      rw [hs]
      exact hα
    have hv : (V ω).2 ∈ K := by
      have hs : dist (V ω).2 z = 1 := by
        simpa only [Metric.mem_sphere] using hf.1.2.2.1
      change dist (V ω).2 z ≤ 1
      exact hs.le
    simpa only [V', show V ω ∈ B from ⟨hu, hv⟩, ↓reduceIte] using hf


end SupercriticalConformalCovariance.Small
