import SupercriticalLQGUniqueness.B2.PfeWeyl.GammaCompact
import SupercriticalLQGUniqueness.B2.Iface.Statements

 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem isCompact_of_isRationalCircle {O : Set ℂ}
    (hO : B2.Iface.IsRationalCircle O) : IsCompact O := by
  obtain ⟨x, y, r, hr, rfl⟩ := hO
  exact isCompact_sphere (Complex.mk (x : ℝ) (y : ℝ)) (r : ℝ)

 

theorem setDistance_liminf_of_compact {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) {O O' : Set ℂ}
    (hO : IsCompact O) (hO' : IsCompact O') :
    B2.Iface.setDistance D O O' ≤
      liminf (fun n => B2.Iface.setDistance (G n) O O') atTop := by
  have h := compact_iInf_liminf hG (hO.prod hO')
  have heq (E : LSCMetric) :
      B2.Iface.setDistance E O O' = ⨅ p ∈ O ×ˢ O', E p := by
    simp only [B2.Iface.setDistance, iInf_prod, mem_prod, iInf_and]
    apply iInf_congr
    intro u
    exact iInf_comm
  simpa only [← heq] using h

 
theorem rationalCircle_liminf {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) {O O' : Set ℂ}
    (hO : B2.Iface.IsRationalCircle O)
    (hO' : B2.Iface.IsRationalCircle O') :
    B2.Iface.setDistance D O O' ≤
      liminf (fun n => B2.Iface.setDistance (G n) O O') atTop :=
  setDistance_liminf_of_compact hG
    (isCompact_of_isRationalCircle hO) (isCompact_of_isRationalCircle hO')

end SupercriticalLQGUniqueness.B2.PfeWeyl
