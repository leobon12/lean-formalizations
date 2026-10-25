import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.SourceStatementsV2




 
set_option autoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open LQGMetric (DistC)

 
theorem q_pos_of_weak_metric (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) : 0 < Q :=
  Positivity.FromAxioms.axpos ξ Q D hD

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
