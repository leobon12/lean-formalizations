import SupercriticalLQGUniqueness.B2.WeakStrong.AxiomIV
import SupercriticalLQGUniqueness.B2.WeakStrong.AxiomV
import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric

 








set_option autoImplicit false

open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 

theorem isStrongLQGMetric_of_isWeakLQGMetric :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric),
      IsLFPPExponent ξ Q → IsWeakLQGMetric ξ Q D → IsStrongLQGMetric ξ Q D :=
  fun _ _ _ hQ hD =>
    ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2.1, scaling_of_weak hQ hD, finiteness_of_weak hD⟩

end SupercriticalLQGUniqueness.B2.WeakStrong
