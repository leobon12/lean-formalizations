import SupercriticalLQGUniqueness.B2.Median.Height
import SupercriticalLQGUniqueness.B2.Median.Lower
import Mathlib.MeasureTheory.Measure.Continuity

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

theorem measurable_crossingInf :
    Measurable (fun d : LSCMetric => crossingInf d) :=
  Uniqueness.Toolkit.CompactPathInfimum.compactPathInf_measurable
    (show IsCompact unitSquare by
      change IsCompact LQGMetric.Blueprint.closedUnitSquare
      exact LQGMetric.DFGPS.isCompact_closedUnitSquare)
    LQGMetric.GM.isCompact_leftSide LQGMetric.GM.isCompact_rightSide

theorem isMedian_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ≥0∞) (m c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hmed : IsMedian P X m) :
    IsMedian P (fun ω => c * X ω) (c * m) := by
  have hlow : {ω | c * X ω ≤ c * m} = {ω | X ω ≤ m} := by
    ext ω
    change c * X ω ≤ c * m ↔ X ω ≤ m
    simpa only [mul_comm] using
      (ENNReal.mul_le_mul_iff_left hc0 hcTop (a := X ω) (b := m))
  have hhigh : {ω | c * m ≤ c * X ω} = {ω | m ≤ X ω} := by
    ext ω
    change c * m ≤ c * X ω ↔ m ≤ X ω
    simpa only [mul_comm] using
      (ENNReal.mul_le_mul_iff_left hc0 hcTop (a := m) (b := X ω))
  exact ⟨hmed.1.const_mul _, by rw [hlow]; exact hmed.2.1,
    by rw [hhigh]; exact hmed.2.2⟩

theorem isMedian_normalized_lfppCrossing
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (ξ ε a : Set.Ioi (0 : ℝ))
    (ha : IsLFPPNormalizer ξ ε a)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ω → C(ℂ, ℝ)) (hX : IsHeatSmoothing P h ε X) :
    IsMedian P
      (fun ω => ENNReal.ofReal ((a : ℝ)⁻¹) *
        lfppCrossingLength (ξ : ℝ) (X ω)) 1 := by
  have hmed := ha P h hh X hX
  have hc0 : ENNReal.ofReal ((a : ℝ)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr a.property)).ne'
  have hscale := isMedian_mul P
    (fun ω => lfppCrossingLength (ξ : ℝ) (X ω))
    (ENNReal.ofReal (a : ℝ)) (ENNReal.ofReal ((a : ℝ)⁻¹))
    hc0 ENNReal.ofReal_ne_top hmed
  have hprod : ENNReal.ofReal ((a : ℝ)⁻¹) * ENNReal.ofReal (a : ℝ) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr a.property.le),
      inv_mul_cancel₀ a.property.ne', ENNReal.ofReal_one]
  rwa [hprod] at hscale

private theorem measure_limsup_ge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : ℕ → Set Ω)
    (hA : ∀ n, NullMeasurableSet (A n) P) {c : ℝ≥0∞}
    (hc : ∀ n, c ≤ P (A n)) :
    c ≤ P (⋂ N : ℕ, ⋃ n ≥ N, A n) := by
  let S : ℕ → Set Ω := fun N => ⋃ n ≥ N, A n
  have hSm : ∀ N, NullMeasurableSet (S N) P := by
    intro N
    exact NullMeasurableSet.biUnion (Set.to_countable _) (fun n _ => hA n)
  have hanti : ∀ᵐ ω ∂P, Antitone (fun N => ω ∈ S N) := by
    filter_upwards [] with ω
    intro N M hNM hM
    obtain ⟨n, hnM, hnA⟩ := mem_iUnion₂.mp hM
    exact mem_iUnion₂.mpr ⟨n, hNM.trans hnM, hnA⟩
  have hfin : ∃ N, P (S N) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top ?_ (measure_mono (subset_univ _))⟩
    simp
  rw [show (⋂ N : ℕ, ⋃ n ≥ N, A n) = ⋂ N, S N from rfl,
    measure_iInter_of_ae_antitone hanti hSm hfin]
  refine le_iInf fun N => ?_
  exact (hc N).trans (measure_mono (show A N ⊆ S N by
    intro ω hω
    exact mem_iUnion₂.mpr ⟨N, le_rfl, hω⟩))

theorem measure_closed_ge_of_ae_tendsto
    {Ω α : Type*} [MeasurableSpace Ω] [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → α) (Z : Ω → α) (F : Set α)
    (hF : IsClosed F) (hX : ∀ n, AEMeasurable (X n) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)))
    {c : ℝ≥0∞} (hc : ∀ n, c ≤ P {ω | X n ω ∈ F}) :
    c ≤ P {ω | Z ω ∈ F} := by
  let A : ℕ → Set Ω := fun n => {ω | X n ω ∈ F}
  have hA : ∀ n, NullMeasurableSet (A n) P := fun n =>
    (hX n).nullMeasurableSet_preimage hF.measurableSet
  have hlimsup := measure_limsup_ge P A hA hc
  have hsub : (⋂ N : ℕ, ⋃ n ≥ N, A n) ≤ᵐ[P] {ω | Z ω ∈ F} := by
    filter_upwards [hconv] with ω hω
    intro hωS
    by_contra hz
    have hzopen : Z ω ∈ Fᶜ := hz
    have hevent : ∀ᶠ n in atTop, X n ω ∈ Fᶜ :=
      hω.eventually (hF.isOpen_compl.mem_nhds hzopen)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    have hωN : ω ∈ ⋃ n ≥ N, A n := mem_iInter.mp hωS N
    obtain ⟨n, hnN, hnA⟩ := mem_iUnion₂.mp hωN
    exact hN n hnN hnA
  exact hlimsup.trans (measure_mono_ae hsub)

theorem isMedian_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ≥0∞) (Z : Ω → ℝ≥0∞)
    (hX : ∀ n, AEMeasurable (X n) P) (hZ : AEMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Z ω)))
    (m : ℝ≥0∞) (hmed : ∀ n, IsMedian P (X n) m) :
    IsMedian P Z m := by
  refine ⟨hZ, ?_, ?_⟩
  · exact measure_closed_ge_of_ae_tendsto P X Z (Iic m) isClosed_Iic hX hconv
      (fun n => (hmed n).2.1)
  · exact measure_closed_ge_of_ae_tendsto P X Z (Ici m) isClosed_Ici hX hconv
      (fun n => (hmed n).2.2)

 



theorem isMedian_crossing_one_of_ae_tendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hnorm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (D : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D)
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (hconv : ∀ᵐ ω ∂P, Tendsto
      (fun n => ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
        lfppCrossingLength (ξ : ℝ) (X (ε n) ω)) atTop
      (𝓝 (crossingInf (D (h ω))))) :
    IsMedian P (fun ω => crossingInf (D (h ω))) 1 := by
  let Y : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal ((m (ε n) : ℝ)⁻¹) *
      lfppCrossingLength (ξ : ℝ) (X (ε n) ω)
  let Z : Ω → ℝ≥0∞ := fun ω => crossingInf (D (h ω))
  have hmed (n : ℕ) : IsMedian P (Y n) 1 :=
    isMedian_normalized_lfppCrossing P h ξ (ε n) (m (ε n))
      (hnorm (ε n)) hh (X (ε n)) (hX (ε n))
  have hYm (n : ℕ) : AEMeasurable (Y n) P := (hmed n).1
  have hZm : AEMeasurable Z P :=
    (measurable_crossingInf.comp (hD.comp hh.1.measurable)).aemeasurable
  exact isMedian_of_ae_tendsto P Y Z hYm hZm hconv 1 hmed

end SupercriticalLQGUniqueness.B2.Median
