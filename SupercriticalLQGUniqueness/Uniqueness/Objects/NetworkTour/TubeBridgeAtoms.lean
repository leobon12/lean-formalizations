import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Tube
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 





set_option autoImplicit false
noncomputable section
open Set

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour

 
theorem polar_eq_pol (R θ : ℝ) : Objects.CorrectedEvent.polar R θ = Objects.Tube.pol R θ := rfl

 
theorem blockNorm_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams)
    (hα : T.alpha = P.α) : Objects.CorrectedEvent.blockNorm T = Objects.Tube.blockNorm P.α := by
  simp only [Objects.CorrectedEvent.blockNorm, Objects.Tube.blockNorm, hα]

 
theorem site_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hK : T.K = P.K) (k : Fin T.K) :
    Objects.CorrectedEvent.site T k = P.site r (k.val : ℤ) := by
  simp only [Objects.CorrectedEvent.site, Objects.Tube.TubeParams.site, Objects.Tube.TubeParams.ω,
    Objects.CorrectedEvent.polar, Objects.Tube.pol, Objects.Tube.ex, hr, hK]
  norm_cast

 
theorem moduleMap_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (k : Fin T.K) (w : ℂ) :
    Objects.CorrectedEvent.moduleMap T k w = P.modMap r (k.val : ℤ) w := by
  unfold Objects.CorrectedEvent.moduleMap Objects.Tube.TubeParams.modMap
  rw [site_eq T P r hr hK k, hρ, hr, hn]

 
theorem block_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α) (k : Fin T.K) :
    Objects.CorrectedEvent.block T k = P.block r (k.val : ℤ) := by
  unfold Objects.CorrectedEvent.block Objects.Tube.TubeParams.block
  rw [blockNorm_eq T P hα]
  congr 1
  funext w
  exact moduleMap_eq T P r hr hρ hK hn k w

theorem innerCenter_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hα : T.alpha = P.α)
    (hψu : T.psiU = P.ψu) (k : Fin T.K) :
    Objects.CorrectedEvent.innerCenter T k = P.uC r (k.val : ℤ) := by
  unfold Objects.CorrectedEvent.innerCenter Objects.Tube.TubeParams.uC Objects.CorrectedEvent.uNorm
  rw [moduleMap_eq T P r hr hρ hK hn k]
  simp only [hα, hψu, polar_eq_pol]

theorem outerCenter_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ) (hK : T.K = P.K)
    (hn : T.orientation = P.n) (hψv : T.psiV = P.ψv) (k : Fin T.K) :
    Objects.CorrectedEvent.outerCenter T k = P.vC r (k.val : ℤ) := by
  unfold Objects.CorrectedEvent.outerCenter Objects.Tube.TubeParams.vC Objects.CorrectedEvent.vNorm
  rw [moduleMap_eq T P r hr hρ hK hn k]
  simp only [hψv, polar_eq_pol]

theorem tubeWidth_eq (T : Objects.CorrectedEvent.TubeData) (P : Objects.Tube.TubeParams) (r : ℝ)
    (hr : T.r = r) (hρ : T.rho = P.ρ)
    (hwp : P.wp = T.lambda*T.A_endpt) :
    Objects.CorrectedEvent.tubeWidth T = P.w r := by
  simp only [Objects.CorrectedEvent.tubeWidth, Objects.Tube.TubeParams.w, hr, hρ, hwp]


end SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
