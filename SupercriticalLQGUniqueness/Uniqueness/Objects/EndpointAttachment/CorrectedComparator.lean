import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate
import SLUMetricAPI2




 
set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachment

 

theorem exists_corrected_loop_lt (D : LSCMetric) (y : ℂ) (r R : ℝ)
    {B : ENNReal} (hB : Objects.CorrectedEvent.around D y r R < B) :
    ∃ (π : ℝ → ℂ) (s t : ℝ), D.IsCurve π s t ∧
      π '' Icc s t ⊆ Objects.CorrectedEvent.ann y r R ∧
      LQGMetric.Disconnects (π '' Icc s t) (sphere y r) (sphere y R) ∧
      D.len π s t < B := by
  simp only [Objects.CorrectedEvent.around, iInf_lt_iff] at hB
  obtain ⟨π, s, t, hπ, hinside, hsep, hlen⟩ := hB
  exact ⟨π, s, t, hπ, hinside, hsep, hlen⟩


 

theorem exists_corrected_paid_loop (D : LSCMetric) (y : ℂ)
    (ri ro si so : ℝ) {coeff d : ℝ}
    (hcoeff : 0 < coeff) (hd : 0 < d)
    (hcompare : Objects.CorrectedEvent.around D y ro so ≤
      ENNReal.ofReal coeff * Objects.CorrectedEvent.acr D y ri si)
    (hcross : Objects.CorrectedEvent.acr D y ri si ≤ ENNReal.ofReal d) :
    ∃ (π : ℝ → ℂ) (s t : ℝ), D.IsCurve π s t ∧
      π '' Icc s t ⊆ Objects.CorrectedEvent.ann y ro so ∧
      LQGMetric.Disconnects (π '' Icc s t) (sphere y ro) (sphere y so) ∧
      D.len π s t < ENNReal.ofReal (2 * coeff * d) := by
  have hbound : Objects.CorrectedEvent.around D y ro so ≤ ENNReal.ofReal (coeff * d) := by
    calc
      Objects.CorrectedEvent.around D y ro so ≤
          ENNReal.ofReal coeff * Objects.CorrectedEvent.acr D y ri si := hcompare
      _ ≤ ENNReal.ofReal coeff * ENNReal.ofReal d := by gcongr
      _ = ENNReal.ofReal (coeff * d) := (ENNReal.ofReal_mul hcoeff.le).symm
  have hstrict : ENNReal.ofReal (coeff * d) < ENNReal.ofReal (2 * coeff * d) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    nlinarith
  exact exists_corrected_loop_lt D y ro so (hbound.trans_lt hstrict)


 

theorem exists_corrected_paid_loop_continuous (D : LSCMetric) (y : ℂ)
    (ri ro si so : ℝ) {coeff d : ℝ}
    (hcoeff : 0 < coeff) (hd : 0 < d)
    (hcompare : Objects.CorrectedEvent.around D y ro so ≤
      ENNReal.ofReal coeff * Objects.CorrectedEvent.acr D y ri si)
    (hcross : Objects.CorrectedEvent.acr D y ri si ≤ ENNReal.ofReal d) :
    ∃ (π : ℝ → ℂ) (s t : ℝ), D.IsCurve π s t ∧
      ContinuousOn π (Icc s t) ∧
      π '' Icc s t ⊆ Objects.CorrectedEvent.ann y ro so ∧
      LQGMetric.Disconnects (π '' Icc s t) (sphere y ro) (sphere y so) ∧
      D.len π s t < ENNReal.ofReal (2 * coeff * d) := by
  obtain ⟨π, s, t, hπ, htrace, hsep, hlen⟩ :=
    exists_corrected_paid_loop D y ri ro si so hcoeff hd hcompare hcross
  have hclosed : MapsTo π (Icc s t) (closedBall y so) := by
    intro q hq
    have hqAnn : π q ∈ Objects.CorrectedEvent.ann y ro so := htrace ⟨q, hq, rfl⟩
    exact (mem_closedBall).2 hqAnn.2.le
  have hEuclid : ContinuousOn π (Icc s t) :=
    hπ.continuousOn_of_mapsTo (isCompact_closedBall y so) hclosed
  exact ⟨π, s, t, hπ, hEuclid, htrace, hsep, hlen⟩


 


theorem corrected_acr_le_crossing_length (D : LSCMetric)
    {P : ℝ → ℂ} {y : ℂ} {ri ro s t : ℝ}
    (hP : D.IsCurve P s t)
    (htrace : P '' Icc s t ⊆ Objects.CorrectedEvent.cann y ri ro)
    (hs : P s ∈ sphere y ri) (ht : P t ∈ sphere y ro) :
    Objects.CorrectedEvent.acr D y ri ro ≤ D.len P s t := by
  unfold Objects.CorrectedEvent.acr
  exact iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t
    (iInf_le_of_le hP (iInf_le_of_le htrace
      (iInf_le_of_le hs (iInf_le_of_le ht le_rfl))))))


end SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachment
