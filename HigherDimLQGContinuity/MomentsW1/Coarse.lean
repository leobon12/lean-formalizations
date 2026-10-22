import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.DGZ.FieldTailsMeas
import HigherDimLQGMetric.DGZ.FieldTails
import HigherDimLQGMetric.DGZ.FieldTailsOsc
import HigherDimLQGMetric.DGZ.TightBasics

/-!
# The coarse field envelope for Appendix A, W1

The envelope is a countable supremum on a dense subset of the closed box. This makes its
measurability independent of any full-measure continuity event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox)
open HigherDimLQGMetric.DGZ

variable {d : ℕ}

private def wnDenseBox (R : ℝ) : Set (Rd d) :=
  Classical.choose (exists_countable_subset_dense (cbox (0 : Rd d) (R + 5)))

private theorem wnDenseBox_subset (R : ℝ) :
    wnDenseBox (d := d) R ⊆ cbox (0 : Rd d) (R + 5) :=
  (Classical.choose_spec (exists_countable_subset_dense (cbox (0 : Rd d) (R + 5)))).1

private theorem wnDenseBox_countable (R : ℝ) : (wnDenseBox (d := d) R).Countable :=
  (Classical.choose_spec (exists_countable_subset_dense (cbox (0 : Rd d) (R + 5)))).2.1

private theorem wnDenseBox_dense (R : ℝ) :
    cbox (0 : Rd d) (R + 5) ⊆ closure (wnDenseBox (d := d) R) :=
  (Classical.choose_spec (exists_countable_subset_dense (cbox (0 : Rd d) (R + 5)))).2.2

/-- Extended coarse excess, with `⊤` on realizations with unbounded excess. -/
def wnZRext {Ω : Type*} (R Q C : ℝ) (H : ℕ → Rd d → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ m : ℕ, ⨆ z : wnDenseBox (d := d) R,
    ENNReal.ofReal (H m z ω - Q * m * Real.log 2 - C * Real.log (2 + R))

/-- The real-valued measurable coarse envelope; its `⊤` exceptional case is assigned zero. -/
def wnZR {Ω : Type*} (R Q C : ℝ) (H : ℕ → Rd d → Ω → ℝ) (ω : Ω) : ℝ :=
  (wnZRext (d := d) R Q C H ω).toReal

theorem measurable_wnZRext {Ω : Type*} [MeasurableSpace Ω] {H : ℕ → Rd d → Ω → ℝ}
    (hH : ∀ m z, Measurable (H m z)) (R Q C : ℝ) :
    Measurable (wnZRext (d := d) R Q C H) := by
  haveI : Countable (wnDenseBox (d := d) R) := (wnDenseBox_countable (d := d) R).to_subtype
  unfold wnZRext
  exact Measurable.iSup fun m => Measurable.iSup fun z =>
    ENNReal.measurable_ofReal.comp (((hH m z).sub measurable_const).sub measurable_const)

theorem measurable_wnZR {Ω : Type*} [MeasurableSpace Ω] {H : ℕ → Rd d → Ω → ℝ}
    (hH : ∀ m z, Measurable (H m z)) (R Q C : ℝ) :
    Measurable (wnZR (d := d) R Q C H) :=
  ENNReal.measurable_toReal.comp (measurable_wnZRext hH R Q C)

theorem measurable_wnZR_of_realization {κ : Rd d → ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H)
    (R Q C : ℝ) : Measurable (wnZR (d := d) R Q C H) :=
  measurable_wnZR (fun m z => (hH.band m).measurable z) R Q C

/-- A finite coarse envelope bounds the field on the entire closed box. -/
theorem wnZR_bound {Ω : Type*} {H : ℕ → Rd d → Ω → ℝ}
    (hcont : ∀ m ω, Continuous (fun z => H m z ω))
    (R Q C : ℝ) (ω : Ω) (hfinite : wnZRext (d := d) R Q C H ω ≠ ⊤)
    (m : ℕ) (z : Rd d) (hz : z ∈ cbox (0 : Rd d) (R + 5)) :
    H m z ω ≤ Q * m * Real.log 2 + C * Real.log (2 + R) + wnZR (d := d) R Q C H ω := by
  have hclosed : IsClosed {w : Rd d |
      H m w ω - Q * m * Real.log 2 - C * Real.log (2 + R) ≤
        wnZR (d := d) R Q C H ω} :=
    isClosed_le (((hcont m ω).sub continuous_const).sub continuous_const) continuous_const
  have hdense : wnDenseBox (d := d) R ⊆ {w : Rd d |
      H m w ω - Q * m * Real.log 2 - C * Real.log (2 + R) ≤
        wnZR (d := d) R Q C H ω} := by
    intro w hw
    have hsup : ENNReal.ofReal
        (H m w ω - Q * m * Real.log 2 - C * Real.log (2 + R)) ≤
          wnZRext (d := d) R Q C H ω := by
      unfold wnZRext
      exact le_iSup_of_le m (le_iSup_of_le (⟨w, hw⟩ : wnDenseBox (d := d) R) le_rfl)
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hsup
  have hbound := (closure_minimal hdense hclosed) ((wnDenseBox_dense (d := d) R) hz)
  change H m z ω - Q * m * Real.log 2 - C * Real.log (2 + R) ≤
    wnZR (d := d) R Q C H ω at hbound
  linarith

/-- The finite mesh of the coarse box has a cell containing every point of the box. -/
theorem wnGrid_cover (R a : ℝ) (ha : 0 < a) (z : Rd d)
    (hz : z ∈ cbox (0 : Rd d) (R + 5)) :
    ∃ g ∈ Osc.grid (0 : Rd d) (R + 5) a, z ∈ cbox g a := by
  refine ⟨Osc.gridOf (0 : Rd d) (R + 5) a z,
    Osc.gridOf_mem_grid 0 ha hz, ?_⟩
  intro i
  have h := (Osc.gridOf_coord 0 ha hz i)
  exact abs_le.mpr ⟨by linarith [h.1], h.2.le⟩

/-- Exceeding the envelope forces one scale to exceed its deterministic threshold. -/
theorem wnZR_tail_event_subset {Ω : Type*} (R Q C u : ℝ) (hu : 0 ≤ u)
    (H : ℕ → Rd d → Ω → ℝ) :
    {ω | u < wnZR (d := d) R Q C H ω} ⊆
      ⋃ m : ℕ, {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
        Q * m * Real.log 2 + C * Real.log (2 + R) + u < H m z ω} := by
  intro ω hω
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hnot
  have hbound : wnZRext (d := d) R Q C H ω ≤ ENNReal.ofReal u := by
    unfold wnZRext
    refine iSup_le fun m => iSup_le fun z => ?_
    have hz := wnDenseBox_subset (d := d) R z.property
    have hle : H m z ω ≤ Q * m * Real.log 2 + C * Real.log (2 + R) + u :=
      le_of_not_gt (fun hlt => hnot m z ⟨hz, hlt⟩)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hreal : wnZR (d := d) R Q C H ω ≤ u :=
    ENNReal.toReal_le_of_le_ofReal hu hbound
  exact (not_lt_of_ge hreal) hω

/-- The extended excess has the same one-scale exceedance event, including its infinite case. -/
theorem wnZRext_tail_event_subset {Ω : Type*} (R Q C u : ℝ)
    (H : ℕ → Rd d → Ω → ℝ) :
    {ω | ENNReal.ofReal u < wnZRext (d := d) R Q C H ω} ⊆
      ⋃ m : ℕ, {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
        Q * m * Real.log 2 + C * Real.log (2 + R) + u < H m z ω} := by
  intro ω hω
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hnot
  have hbound : wnZRext (d := d) R Q C H ω ≤ ENNReal.ofReal u := by
    unfold wnZRext
    refine iSup_le fun m => iSup_le fun z => ?_
    have hz := wnDenseBox_subset (d := d) R z.property
    have hle : H m z ω ≤ Q * m * Real.log 2 + C * Real.log (2 + R) + u :=
      le_of_not_gt (fun hlt => hnot m z ⟨hz, hlt⟩)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact (not_lt_of_ge hbound) hω

/-- A finite grid reduces a box supremum event to small-box supremum events. -/
theorem wnGrid_measure_sup_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Rd d → Ω → ℝ) {R a t : ℝ} (ha : 0 < a) {B : ℝ≥0∞}
    (hB : ∀ g ∈ Osc.grid (0 : Rd d) (R + 5) a,
      P {ω | ∃ z ∈ cbox g a, t < |F z ω|} ≤ B) :
    P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5), t < F z ω} ≤
      (Osc.grid (0 : Rd d) (R + 5) a).card * B := by
  let G := Osc.grid (0 : Rd d) (R + 5) a
  have hsub : {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5), t < F z ω} ⊆
      ⋃ g ∈ G, {ω | ∃ z ∈ cbox g a, t < |F z ω|} := by
    intro ω hω
    obtain ⟨z, hz, hlt⟩ := hω
    obtain ⟨g, hg, hzg⟩ := wnGrid_cover R a ha z hz
    exact Set.mem_biUnion hg ⟨z, hzg, lt_of_lt_of_le hlt (le_abs_self _)⟩
  calc
    P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5), t < F z ω}
        ≤ P (⋃ g ∈ G, {ω | ∃ z ∈ cbox g a, t < |F z ω|}) := measure_mono hsub
    _ ≤ ∑ g ∈ G, P {ω | ∃ z ∈ cbox g a, t < |F z ω|} :=
      measure_biUnion_finset_le G _
    _ ≤ ∑ _g ∈ G, B := Finset.sum_le_sum fun g hg => hB g hg
    _ = G.card * B := by simp

/-- The one-scale box tail, with the point and cell terms kept separate. -/
theorem wnZR_oneScale_tail {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ},
        IsDyadicRealization κ P W H → ∀ (m : ℕ) (R u w : ℝ), 0 ≤ u → 0 ≤ w →
          P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5), u + C + w < H m z ω} ≤
            ((Osc.grid (0 : Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ≥0∞) *
              ENNReal.ofReal
                (2 * Real.exp (-u ^ 2 / (2 * Real.log (1 / ((2 : ℝ)⁻¹ ^ m)))) +
                  2 * Real.exp (-w ^ 2 / C)) := by
  obtain ⟨C, hC, htail⟩ := exists_smallBox_gaussian_tail (d := d) hκ
    (R := 1) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W H hH m R u w hu hw
  have ha : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have hab : (2 : ℝ)⁻¹ ^ m ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  apply wnGrid_measure_sup_le P (H m) ha
  intro g hg
  simpa only [one_mul] using
    htail hH.whiteNoise ha hab (hH.band m) g hu hw

/-- The grid has polynomial spatial growth and dyadic exponential growth. -/
theorem wnZR_grid_card_le (R : ℝ) (hR : 1 ≤ R) (m : ℕ) :
    ((Osc.grid (0 : Rd d) (R + 5) ((2 : ℝ)⁻¹ ^ m)).card : ℝ) ≤
      (16 * (1 + R) * (2 : ℝ) ^ m) ^ d := by
  have ha : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have hc := Osc.card_grid_le (0 : Rd d) (show 0 ≤ R + 5 by linarith) ha
  rw [inv_pow, div_inv_eq_mul] at hc
  rw [inv_pow]
  refine hc.trans (pow_le_pow_left₀ ?_ ?_ d)
  · positivity
  · have hm : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (show 0 ≤ R by linarith) (show 0 ≤ (2 : ℝ) ^ m by positivity)]

/-- Countable subadditivity for the coarse envelope tail. -/
theorem wnZR_tail_tsum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℕ → Rd d → Ω → ℝ) (R Q C u : ℝ) (hu : 0 ≤ u) :
    P {ω | u < wnZR (d := d) R Q C H ω} ≤
      ∑' m : ℕ, P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
        Q * m * Real.log 2 + C * Real.log (2 + R) + u < H m z ω} :=
  (measure_mono (wnZR_tail_event_subset R Q C u hu H)).trans (measure_iUnion_le _)

theorem wnZRext_tail_tsum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℕ → Rd d → Ω → ℝ) (R Q C u : ℝ) :
    P {ω | ENNReal.ofReal u < wnZRext (d := d) R Q C H ω} ≤
      ∑' m : ℕ, P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
        Q * m * Real.log 2 + C * Real.log (2 + R) + u < H m z ω} :=
  (measure_mono (wnZRext_tail_event_subset R Q C u H)).trans (measure_iUnion_le _)

/-- The zero-scale term in the tail sum is null because the empty band vanishes a.s. -/
theorem wnZR_zero_scale_null {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : IsDyadicRealization κ P W H)
    (R C u : ℝ) (hthreshold : 0 ≤ C * Real.log (2 + R) + u) :
    P {ω | ∃ z ∈ cbox (0 : Rd d) (R + 5),
      C * Real.log (2 + R) + u < H 0 z ω} = 0 := by
  have h0 := ae_forall_eq_zero_of_isBandVersion_self hκ hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h0)
  obtain ⟨z, -, hz⟩ := hω
  intro hall
  rw [hall z] at hz
  linarith

end HigherDimLQGContinuity
