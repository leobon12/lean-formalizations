import SupercriticalLQGUniqueness.B2.QPos.DGFFGaussian

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 

def algebraicKilledTransition : Matrix V V ℝ :=
  1 - (Real.pi / 2) • G.precision

theorem algebraicGreen_resolvent (hK : G.precision.PosDef) :
    (1 - G.algebraicKilledTransition) * G.algebraicGreen = 1 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hKunit := hK.isUnit
  have hKinv : G.precision * G.precision⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (G.precision.isUnit_iff_isUnit_det.mp hKunit)
  have hgreen : G.algebraicGreen = (2 / Real.pi) • G.precision⁻¹ := by
    ext i j
    rfl
  unfold algebraicKilledTransition
  rw [sub_sub_cancel, hgreen]
  rw [smul_mul_smul, hKinv]
  have hcoeff : (Real.pi / 2) * (2 / Real.pi) = 1 := by
    field_simp
  simp [hcoeff]

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
