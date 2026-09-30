import QuantumZipper.Proofs.Zipper.AreaWinMkDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINMARKOV (K): covariances and independence against the normalization circle `fc(0,R)`

Source: B. Duplantier, S. Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185
(2011), §3.1 (the circle-average increments inside `B_r(w)` are independent of the field outside
`B_r(w)`), in the kernel form of the repository (`KernelIdentities.lean`): harmonicity of the
Neumann kernel gives zero covariance between an increment `fc(z,ρ) − fc(z,r)` and any folded
circle outside `B_r(z)`.

* `kernelCov_fc_outside_bigCircle`: a circle outside `B(0,R)` against `fc(0,R)`.
* `mkOff R z r` (the disc `B_r(z)` is inside or outside `B(0,R)`) and
  `kernelCov_fc_bigCircle_eq_of_off`: then the covariance with `fc(0,R)` does not depend on the
  radius `ρ ≤ r`.
* `fcPairCov_incr_Zsame_off`, `fcPairCov_incr_Zfar_off`: increments against coarse values.
* `mk_indepFun_self`, `mk_indepFun_far`: independence of countable increment families.
* `fcPairCov_Zself_out`: the variance of the coarse value for a disc outside `B(0,R)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ComplexConjugate

namespace QuantumZipper.E6

open GaussTK KernelId AreaExist

/-- A folded circle outside `B(0,R)` against `fc(0,R)`. -/
theorem kernelCov_fc_outside_bigCircle {a : ℂ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (h : R + r ≤ ‖a‖) :
    kernelCov neumannH (foldedCircle a r) (foldedCircle 0 R) = -2 * Real.log ‖a‖ := by
  have hae : ∀ᵐ x ∂(circleUnif a r), R ≤ ‖x - 0‖ ∧ R ≤ ‖x - conj 0‖ := by
    filter_upwards [ae_norm_sub_center a hr] with x hx
    have h1 := norm_sub_norm_le a (a - x)
    rw [norm_sub_rev a x, hx, sub_sub_cancel] at h1
    simp only [map_zero, sub_zero]
    constructor <;> linarith
  rw [kernelCov_fc_master_out _ _ hr hR hae, map_zero, sub_zero,
    max_eq_right (by linarith : r ≤ ‖a‖)]
  ring

/-- The disc `B_r(z)` lies inside or outside `B(0,R)`. -/
def mkOff (R : ℝ) (z : ℂ) (r : ℝ) : Prop := ‖z‖ + r ≤ R ∨ R + r ≤ ‖z‖

theorem mkOff.mono {R r r' : ℝ} {z : ℂ} (h : mkOff R z r) (hr : r' ≤ r) : mkOff R z r' := by
  rcases h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Off the normalization circle, the covariance with `fc(0,R)` does not depend on the radius. -/
theorem kernelCov_fc_bigCircle_eq_of_off {z : ℂ} {ρ r R : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hR : 0 < R) (h : mkOff R z r) :
    kernelCov neumannH (foldedCircle z ρ) (foldedCircle 0 R) =
      kernelCov neumannH (foldedCircle z r) (foldedCircle 0 R) := by
  have hr : 0 < r := hρ.trans_le hρr
  rcases h with h | h
  · rw [kernelCov_fc_bigCircle_right hρ (by linarith), kernelCov_fc_bigCircle_right hr h]
  · rw [kernelCov_fc_outside_bigCircle hρ hR (by linarith),
      kernelCov_fc_outside_bigCircle hr hR h]

/-- Increment against its own coarse value. -/
theorem fcPairCov_incr_Zsame_off {z : ℂ} {ε ε' R : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hε'z : ε' ≤ z.im) (hR : 0 < R) (h : mkOff R z ε') :
    fcPairCov (z, ε, z, ε') (z, ε', 0, R) = 0 := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_sameCenter hε hε' (hεε'.trans hε'z) hε'z,
    kernelCov_fc_interior_sameCenter hε' hε' hε'z hε'z,
    kernelCov_fc_bigCircle_eq_of_off hε hεε' hR h, max_eq_right hεε', max_self]
  ring

/-- Increment against a far coarse value. -/
theorem fcPairCov_incr_Zfar_off {z u : ℂ} {ε ε' r R : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hε'z : ε' ≤ z.im) (hr : 0 < r) (hru : r ≤ u.im) (hR : 0 < R) (h : mkOff R z ε')
    (htu : ε' + r ≤ ‖z - u‖) :
    fcPairCov (z, ε, z, ε') (u, r, 0, R) = 0 := by
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_separated hε hr (hεε'.trans hε'z) hru (by linarith),
    kernelCov_fc_interior_separated (hε.trans_le hεε') hr hε'z hru htu,
    kernelCov_fc_bigCircle_eq_of_off hε hεε' hR h]
  ring

section Indep

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Increments inside `B_r(z)` are independent of the coarse value `X(fc(z,r)) − X(fc(0,R))`. -/
theorem mk_indepFun_self (hX : IsFreeGFFModConstH X P) {ι : Type} {z : ℂ} {r R : ℝ}
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i ∧ ρ i ≤ r) (hr : 0 < r) (hrz : r ≤ z.im) (hR : 0 < R)
    (h : mkOff R z r) :
    IndepFun (fun ω i => fcPairVal X (z, ρ i, z, r) ω)
      (fun ω (_ : Unit) => fcPairVal X (z, r, 0, R) ω) P := by
  have hzH := mem_Hbar_of_le_im hr hrz
  refine indepFun_fcPair hX
    (fun i => (⟨(z, ρ i, z, r), ⟨hzH, (hρ i).1, hzH, hr⟩⟩ : {p : FcIdx // p.Good}))
    (fun _ => ⟨(z, r, 0, R), good_Z hzH hr hR⟩) ?_
  intro i _
  exact fcPairCov_incr_Zsame_off (hρ i).1 (hρ i).2 hrz hR h

/-- The index family of `(U z, U u, increments at u)`. -/
def mkFarIdx {κ : Type} (z u : ℂ) (r R : ℝ) (ρ' : κ → ℝ) : Unit ⊕ (Unit ⊕ κ) → FcIdx :=
  Sum.elim (fun _ => (z, r, 0, R)) (Sum.elim (fun _ => (u, r, 0, R)) fun k => (u, ρ' k, u, r))

/-- Increments inside `B_r(z)` are independent of `(U z, U u, increments inside B_r(u))` when
`‖z − u‖ ≥ 2r`. -/
theorem mk_indepFun_far (hX : IsFreeGFFModConstH X P) {ι κ : Type} {z u : ℂ} {r R : ℝ}
    (ρ : ι → ℝ) (ρ' : κ → ℝ) (hρ : ∀ i, 0 < ρ i ∧ ρ i ≤ r) (hρ' : ∀ k, 0 < ρ' k ∧ ρ' k ≤ r)
    (hr : 0 < r) (hrz : r ≤ z.im) (hru : r ≤ u.im) (hR : 0 < R) (h : mkOff R z r)
    (hzu : 2 * r ≤ ‖z - u‖) :
    IndepFun (fun ω i => fcPairVal X (z, ρ i, z, r) ω)
      (fun ω (k : Unit ⊕ (Unit ⊕ κ)) => fcPairVal X (mkFarIdx z u r R ρ' k) ω) P := by
  have hzH := mem_Hbar_of_le_im hr hrz
  have huH := mem_Hbar_of_le_im hr hru
  have hg : ∀ k, (mkFarIdx z u r R ρ' k).Good := by
    rintro (_ | _ | k)
    · exact good_Z hzH hr hR
    · exact good_Z huH hr hR
    · exact ⟨huH, (hρ' k).1, huH, hr⟩
  refine indepFun_fcPair hX
    (fun i => (⟨(z, ρ i, z, r), ⟨hzH, (hρ i).1, hzH, hr⟩⟩ : {p : FcIdx // p.Good}))
    (fun k => ⟨mkFarIdx z u r R ρ' k, hg k⟩) ?_
  rintro i (_ | _ | k)
  · exact fcPairCov_incr_Zsame_off (hρ i).1 (hρ i).2 hrz hR h
  · exact fcPairCov_incr_Zfar_off (hρ i).1 (hρ i).2 hrz hr hru hR h (by linarith)
  · exact fcPairCov_incr_incr_far_int (hρ i).1 (hρ i).2 hrz (hρ' k).1 (hρ' k).2 hru
      (by linarith)

end Indep

end QuantumZipper.E6
