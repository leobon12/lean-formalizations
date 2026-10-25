import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldLMBridge
import LQGMetric.Topo.Disconnect




 






set_option autoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

theorem around_wide_le_narrow (d : LSCMetric) (w : ℂ) (t : ℝ) (ht : 0 < t) :
    Objects.CorrectedEvent.around d w t (2 * t) ≤
      Objects.CorrectedEvent.around d w ((21 / 20) * t) ((39 / 20) * t) := by
  unfold Objects.CorrectedEvent.around
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hc =>
    le_iInf fun htrace => le_iInf fun hdisc => ?_
  have htrace' : P '' Icc a b ⊆ Objects.CorrectedEvent.ann w t (2 * t) := by
    intro x hx
    have hh := htrace hx
    change (21 / 20) * t < dist x w ∧ dist x w < (39 / 20) * t at hh
    change t < dist x w ∧ dist x w < 2 * t
    constructor <;> nlinarith only [ht, hh.1, hh.2]
  have hdisc' : LQGMetric.Disconnects (P '' Icc a b)
      (sphere w t) (sphere w (2 * t)) := by
    have hsep : (21 / 20) * t ≤ (39 / 20) * t := by linarith
    have hbase := LQGMetric.Disconnects.closedBall_compl_ball hsep hdisc
    apply hbase.mono (by rfl)
    · intro x hx
      change dist x w = t at hx
      change dist x w ≤ (21 / 20) * t
      linarith
    · intro x hx
      change dist x w = 2 * t at hx
      change ¬dist x w < (39 / 20) * t
      linarith
  apply iInf_le_of_le P
  apply iInf_le_of_le a
  apply iInf_le_of_le b
  apply iInf_le_of_le hc
  apply iInf_le_of_le htrace'
  exact iInf_le_of_le hdisc' le_rfl

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
