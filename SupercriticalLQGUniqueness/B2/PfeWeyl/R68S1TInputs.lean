import SupercriticalLQGUniqueness.B2.Final.CouplingData

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

def CoupledAllRationalCircles
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (e : ℕ → Ioi (0 : ℝ))
    (V : Ioi (0 : ℝ) → LQGMetric.DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (hN : ℕ → Ω' → LQGMetric.DistC) (L : Ω' → LSCMetric) : Prop :=
  ∀ᵐ ω ∂P', ∀ O O' : Set ℂ, IsRationalCircle O → IsRationalCircle O' →
    Tendsto (fun n => setDistance
      (normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))) O O')
      atTop (𝓝 (setDistance (L ω) O O'))

end SupercriticalLQGUniqueness.B2.PfeWeyl
