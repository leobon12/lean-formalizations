/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafVersionFPast

/-!
# One continuous non-anticipating reader from dyadic scalar versions

The reader is the limit along the existing lower-dyadic approximation. A
single countable intersection identifies it with the continuous process at
all times, hence also at arbitrary random times.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.FlowStopIdentG

/-- Extend the raw-past scalar versions from dyadic times by their lower-dyadic limit. -/
def sampleLimitReader {nL nR : ℕ}
    (f : (ℕ × ℕ) → ((ℕ × ℕ) → DrivingValue nL nR) → ℝ)
    (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ :=
  limUnder atTop fun n => f (lowerDyadic t n) (samplePast (dyadicTime (lowerDyadic t n)) γ)

/-- Every fixed-time evaluation of the limit reader is Borel. -/
theorem measurable_sampleLimitReader {nL nR : ℕ}
    {f : (ℕ × ℕ) → ((ℕ × ℕ) → DrivingValue nL nR) → ℝ}
    (hf : ∀ p, Measurable (f p)) (t : ℝ≥0) :
    Measurable fun γ => sampleLimitReader f γ t :=
  (StronglyMeasurable.limUnder fun n =>
    ((hf (lowerDyadic t n)).comp (measurable_samplePast _)).stronglyMeasurable).measurable

/-- The limit reader uses only samples at or before the current time. -/
theorem isNonAnticipating_sampleLimitReader {nL nR : ℕ}
    (f : (ℕ × ℕ) → ((ℕ × ℕ) → DrivingValue nL nR) → ℝ) :
    IsNonAnticipating (sampleLimitReader f) := by
  intro γ δ p h
  unfold sampleLimitReader
  congr 1
  funext n
  rw [samplePast_congr (fun q hq => h q (hq.trans (dyadicTime_lowerDyadic_le _ n)))]

/-- Almost sure agreement at countably many dyadic times identifies the limit
reader with the process simultaneously at every time of each continuous sample. -/
theorem ae_sampleLimitReader_eq_process {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {nL nR : ℕ} {Y : Ω → HistorySpace nL nR}
    {X : ℝ≥0 → Ω → ℝ}
    {f : (ℕ × ℕ) → ((ℕ × ℕ) → DrivingValue nL nR) → ℝ}
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (he : ∀ p, X (dyadicTime p) =ᵐ[P] fun ω => f p (samplePast (dyadicTime p) (Y ω))) :
    ∀ᵐ ω ∂P, ∀ t, sampleLimitReader f (Y ω) t = X t ω := by
  filter_upwards [hc, ae_all_iff.2 he] with ω hc he
  intro t
  have hlim := (hc.tendsto t).comp (tendsto_dyadicTime_lowerDyadic t)
  exact (hlim.congr (fun n => he (lowerDyadic t n))).limUnder_eq

/-- A continuous process measurable for the completed raw dyadic past has a
single Borel non-anticipating history reader, indistinguishable from that process. -/
theorem exists_historyReader_of_rawPast_process
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {nL nR : ℕ} {Y : Ω → HistorySpace nL nR} (hY : Measurable Y)
    {X : ℝ≥0 → Ω → ℝ} (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hm : ∀ p, Measurable[samplePastSigma Y (dyadicTime p) ⊔ nullSigma P] (X (dyadicTime p)))
    (hint : ∀ p, Integrable (X (dyadicTime p)) P) :
    ∃ M : HistorySpace nL nR → ℝ≥0 → ℝ,
      (∀ t, Measurable fun γ => M γ t) ∧ IsNonAnticipating M ∧
      ∀ᵐ ω ∂P, ∀ t, M (Y ω) t = X t ω := by
  have hf : ∀ p, ∃ f : ((ℕ × ℕ) → DrivingValue nL nR) → ℝ, Measurable f ∧
      X (dyadicTime p) =ᵐ[P] fun ω => f (samplePast (dyadicTime p) (Y ω)) := fun p =>
    exists_borel_factor_of_nullAugmented_comap ((measurable_samplePast _).comp hY) (hm p) (hint p)
  choose f hfm hfe using hf
  exact ⟨sampleLimitReader f, measurable_sampleLimitReader hfm, isNonAnticipating_sampleLimitReader f,
    ae_sampleLimitReader_eq_process hc hfe⟩

end InteractingSLE.WFS
