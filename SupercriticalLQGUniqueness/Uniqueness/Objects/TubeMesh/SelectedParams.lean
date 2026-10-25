import SupercriticalLQGUniqueness.Uniqueness.Objects.TubeBridge.ForwardTube
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Params




 







set_option autoImplicit false
noncomputable section

open Set Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh

 
structure TubeSelection (C : Objects.CorrectedEvent.Constants) (P : Objects.Tube.TubeParams) : Prop where
  lamTiny : C.lamConst < 1 / 10 ^ 100
  locGt : 3 < C.A_loc
  annLo : 3 / 4 < C.K_ann
  annHi : C.K_ann < 1
  endptLe : C.A_endpt ≤ C.lamConst * (1 - C.K_ann) ^ 2
  spLo : C.A_endpt ≤ P.sp
  spHi : P.sp ≤ Real.sqrt C.A_endpt
  rhoTwo : C.ρ ≤ 10 * C.lamConst ^ 2 / (Real.pi ^ 2 * C.A_loc ^ 2)
  rhoEq : P.ρ = C.ρ
  alphaEq : P.α = C.K_ann
  countEq : P.K = ⌈C.lamConst / (C.A_loc * C.ρ)⌉₊
  orientFourth : P.n ^ 4 = 1
  orientNorm : ‖P.n‖ = 1
  angleU : P.ψu ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  angleV : P.ψv ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  widthEq : P.wp = C.lamConst * C.A_endpt

 
theorem TubeSelection.good {C : Objects.CorrectedEvent.Constants} {P : Objects.Tube.TubeParams}
    (S : TubeSelection C P) : P.Good := by
  apply Objects.Tube.TubeParams.good_of_DG P C.lamPos S.lamTiny S.locGt
    (S.alphaEq ▸ S.annLo) (S.alphaEq ▸ S.annHi)
    C.endptPos (S.alphaEq ▸ S.endptLe) S.spLo S.spHi S.widthEq
  · rw [S.rhoEq]; exact C.rhoPos
  · rw [S.rhoEq]; exact S.rhoTwo
  · rw [S.rhoEq]; exact S.countEq
  · exact S.orientNorm
  · exact S.angleU
  · exact S.angleV

 
theorem TubeSelection.blockRadius_bounds {C : Objects.CorrectedEvent.Constants} {P : Objects.Tube.TubeParams}
    (S : TubeSelection C P) :
    C.A_endpt * C.ρ * C.r ≤ P.s C.r ∧
      P.s C.r ≤ Real.sqrt C.A_endpt * C.ρ * C.r := by
  unfold Objects.Tube.TubeParams.s
  rw [S.rhoEq]
  have hρr : 0 ≤ C.ρ * C.r := (mul_pos C.rhoPos C.rPos).le
  constructor
  · calc C.A_endpt * C.ρ * C.r = C.A_endpt * (C.ρ * C.r) := by ring
      _ ≤ P.sp * (C.ρ * C.r) := mul_le_mul_of_nonneg_right S.spLo hρr
      _ = P.sp * C.ρ * C.r := by ring
  · calc P.sp * C.ρ * C.r = P.sp * (C.ρ * C.r) := by ring
      _ ≤ Real.sqrt C.A_endpt * (C.ρ * C.r) := mul_le_mul_of_nonneg_right S.spHi hρr
      _ = Real.sqrt C.A_endpt * C.ρ * C.r := by ring

 
theorem TubeSelection.small {C : Objects.CorrectedEvent.Constants} {P : Objects.Tube.TubeParams}
    (S : TubeSelection C P) (hSupNar : C.A_sup < C.A_nar) :
    100 * C.A_sup ≤ P.sp * P.ρ ∧ 8 * C.A_nar ≤ P.sp * P.ρ := by
  apply Objects.Tube.TubeParams.small_of_DG P C.lamPos S.lamTiny
    (S.alphaEq ▸ S.annLo) C.endptPos S.spLo
  · rw [S.rhoEq]; exact C.rhoPos
  · exact C.supPos
  · exact hSupNar
  · rw [S.alphaEq, S.rhoEq]
    exact C.narLe

 


structure MaxSelection (C : Objects.CorrectedEvent.Constants) : Prop where
  formula : C.A_max = C.ξ⁻¹ * max
    (Real.log (C.A_internal / (C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)))))
    (Real.log (C.A_internal / (C.lamConst * C.A_across)))

 
private theorem absorb_of_log_le {ξ Amax Aint lam m : ℝ}
    (hAint : 0 < Aint) (hlam : 0 < lam) (hm : 0 < m)
    (hlog : Real.log (Aint / (lam * m)) ≤ ξ * Amax) :
    Real.exp (-ξ * Amax) * Aint ≤ lam * m := by
  have hden : 0 < lam * m := mul_pos hlam hm
  have hratio : 0 < Aint / (lam * m) := div_pos hAint hden
  have he : Real.exp (-(ξ * Amax)) ≤ Real.exp (-Real.log (Aint / (lam * m))) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-ξ * Amax) * Aint ≤
        Real.exp (-Real.log (Aint / (lam * m))) * Aint :=
      mul_le_mul_of_nonneg_right (by simpa only [neg_mul] using he) hAint.le
    _ = lam * m := by
      rw [Real.exp_neg, Real.exp_log hratio]
      field_simp

 
theorem MaxSelection.absorption {C : Objects.CorrectedEvent.Constants} (S : MaxSelection C) :
    Real.exp (-C.ξ * C.A_max) * C.A_internal ≤
      C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)) ∧
    Real.exp (-C.ξ * C.A_max) * C.A_internal ≤ C.lamConst * C.A_across := by
  have hnar : 0 < C.A_nar ^ (C.ξ * (C.Q + 3)) :=
    Real.rpow_pos_of_pos C.narPos _
  have hlog1 : Real.log (C.A_internal /
      (C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)))) ≤ C.ξ * C.A_max := by
    rw [S.formula]
    rw [mul_inv_cancel_left₀ C.ξPos.ne']
    exact le_max_left _ _
  have hlog2 : Real.log (C.A_internal / (C.lamConst * C.A_across)) ≤
      C.ξ * C.A_max := by
    rw [S.formula]
    rw [mul_inv_cancel_left₀ C.ξPos.ne']
    exact le_max_right _ _
  exact ⟨absorb_of_log_le C.internalPos C.lamPos hnar hlog1,
    absorb_of_log_le C.internalPos C.lamPos C.acrossPos hlog2⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.TubeMesh
