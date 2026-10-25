import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ShieldAllPairs
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit




set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding


 

theorem shield_acr_pos (D : LSCMetric) (z : ℂ) (t : ℝ) (ht : 0 < t) :
    0 < Objects.CorrectedEvent.acr D z (2 * t) (3 * t) := by
  let C : Set ℂ := closedBall z (3 * t)
  let δ : ENNReal :=
    ⨅ p : {q : ℂ × ℂ // q.1 ∈ C ∧ q.2 ∈ C ∧ 2 * (t / 2) ≤ dist q.1 q.2}, D p.val
  have hδpos : 0 < δ := Toolkit.PlanarSeparation.compactSeparatedCost_pos D (isCompact_closedBall z (3 * t))
    (by linarith : 0 < t / 2)
  have hδacr : δ ≤ Objects.CorrectedEvent.acr D z (2 * t) (3 * t) := by
    unfold Objects.CorrectedEvent.acr
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun _ => le_iInf fun ha => le_iInf fun hb => ?_
    have hqa : dist (P a) z = 2 * t := mem_sphere.mp ha
    have hqb : dist (P b) z = 3 * t := mem_sphere.mp hb
    have hsep : 2 * (t / 2) ≤ dist (P a) (P b) := by
      have htri := dist_triangle (P b) (P a) z
      rw [dist_comm (P b) (P a), hqa, hqb] at htri
      linarith
    let p : {q : ℂ × ℂ // q.1 ∈ C ∧ q.2 ∈ C ∧
        2 * (t / 2) ≤ dist q.1 q.2} :=
      ⟨(P a, P b),
        ⟨mem_closedBall.mpr (by linarith), mem_closedBall.mpr (by linarith), hsep⟩⟩
    have hδp : δ ≤ D (P a, P b) := by
      exact iInf_le (fun q : {q : ℂ × ℂ // q.1 ∈ C ∧ q.2 ∈ C ∧
        2 * (t / 2) ≤ dist q.1 q.2} => D q.val) p
    exact hδp.trans (D.apply_le_len P hP.1)
  exact hδpos.trans_le hδacr

 
theorem shieldAt_strict (C : Objects.CorrectedEvent.Constants) (D : LSCMetric)
    (z : ℂ) (t : ℝ) (ht : 0 < t) (hLam : C.lamConst < 1)
    (hfinite : Objects.CorrectedEvent.around D z t (2 * t) < ⊤)
    (hshield : Objects.CorrectedEvent.around D z t (2 * t) ≤
      ENNReal.ofReal C.lamConst * Objects.CorrectedEvent.acr D z (2 * t) (3 * t)) :
    Objects.CorrectedEvent.around D z t (2 * t) < Objects.CorrectedEvent.acr D z (2 * t) (3 * t) := by
  have hpos := shield_acr_pos D z t ht
  by_cases hinf : Objects.CorrectedEvent.acr D z (2 * t) (3 * t) = ⊤
  · exact hinf ▸ hfinite
  · have hLam' : ENNReal.ofReal C.lamConst < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hLam
    have hstrict : ENNReal.ofReal C.lamConst * Objects.CorrectedEvent.acr D z (2 * t) (3 * t) <
        Objects.CorrectedEvent.acr D z (2 * t) (3 * t) := by
      have h := ENNReal.mul_lt_mul_right hpos.ne' hinf hLam'
      simpa only [mul_comm, one_mul] using h
    exact hshield.trans_lt hstrict

theorem shieldAt_strict_zero (C : Objects.CorrectedEvent.Constants) (D : LSCMetric)
    (t : ℝ) (ht : 0 < t) (hLam : C.lamConst < 1)
    (h : Objects.Excursions.shieldAt C D t) :
    Objects.CorrectedEvent.around D 0 t (2 * t) < Objects.CorrectedEvent.acr D 0 (2 * t) (3 * t) :=
  shieldAt_strict C D 0 t ht hLam h.1 h.2

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
