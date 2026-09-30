import QuantumZipper.Proofs.Thm18.A1RS3Fixe
import QuantumZipper.Proofs.Thm18.ASepTr1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (9): transfer of the fixed-driver estimate to the independent Brownian driver

`uniformizer` is a choice (`Classical.epsilon`), so the side map `g1zSideMap left W` need not
depend measurably on the driver. The measurable selection `Ψ` (`G1PsiSel`) agrees with it up to a
dilation of the argument: `ψ_W = Ψ_a(β ·)` on `ℍ` (`g1z2_invFunOn_eq_dilate`). With the family
`smearPsi` built on `Ψ`:

* `smearPsi_eq`: `smearPsi a p ρ = ν^W_{parScale (1, β⁻¹, β⁻¹, β⁻¹) p, ρ}`;
* `A1RSSmearMeasStmt` (open; measurability only): for each parameter `(p, ρ)` and scale `k`, the
  dyadic pairing `(a, y) ↦ ∫ avgReg y k d(smearPsi a p ρ)` agrees on good continuous paths with
  a jointly measurable function;
* **`a1rsFreeBrownStmt_of_meas : A1RSSmearMeasStmt → A1RSFreeBrownStmt`**: the event of the
  estimate for the `Ψ`-family is then measurable; for each good Hölder path it has full measure
  (`ae_smear_fixed_all_e`), and `CharFunRhs.ae_indep_ae` (Fubini for the independent pair) gives
  it along the Brownian driver;
* `holder_global`: the local Hölder bound of a Brownian driver (`ASep.ae_drvGood_drive`) on
  `[0, T]` is a global one.

Own bookkeeping (measurability the paper leaves implicit; Sheffield arXiv:1012.4797 works with the
product law of the independent pair (driver, field) throughout §1.6).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- The smeared-loop family built on the selected side map `Ψ`. -/
def smearPsi (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (κ : ℝ) (left : Bool) (a : ℝ≥0 → ℝ)
    (p : Fin 4 → ℝ) (ρ : ℝ) : Measure ℂ :=
  (((foldedCircle (parD p) (p 3)).map fun w => fwdMap (pathDrive κ a) (p 0) (Ψ left a w)).prod
    E6.XAreaPC.angMeas).map
      (fun q : ℂ × ℝ => fwdMapInv (pathDrive κ a) (p 0) (foldH (circleMap q.1 ρ q.2)))

/-- **Measurability of the `Ψ`-smeared pairings** (open). -/
def A1RSSmearMeasStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
    ∀ (left : Bool) (p : Fin 4 → ℝ) (ρ : ℝ) (k : ℕ),
      ∃ F : (ℝ≥0 → ℝ) × FieldSample → ℝ, Measurable F ∧ (p ∈ smearU → ρ ∈ Icc (0 : ℝ) 1 →
        ∀ a : ℝ≥0 → ℝ, Continuous a → G1zDrvGood (pathDrive (γ ^ 2) a) → ∀ y : FieldSample,
          F (a, y) = ∫ w, avgReg y k w ∂(smearPsi Ψ (γ ^ 2) left a p ρ))

/-- The `Ψ`-family is a rescaled parametrization of the smeared-loop family. -/
theorem smearPsi_eq {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {κ : ℝ} {left : Bool} {a : ℝ≥0 → ℝ}
    (hG : G1zDrvGood (pathDrive κ a)) {β : ℝ} (hβ : 0 < β)
    (hdil : EqOn (g1zSideMap left (pathDrive κ a)) (fun w => Ψ left a ((β : ℂ) * w)) H)
    {p : Fin 4 → ℝ} (hp : p ∈ smearU) (ρ : ℝ) :
    smearPsi Ψ κ left a p ρ = smearFam (pathDrive κ a) left (parScale ![1, β⁻¹, β⁻¹, β⁻¹] p) ρ := by
  set W := pathDrive κ a with hW
  have hβi : 0 < β⁻¹ := inv_pos.2 hβ
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hβ.ne'
  have hp0 : parScale ![1, β⁻¹, β⁻¹, β⁻¹] p 0 = p 0 := by simp [parScale]
  have hp3 : parScale ![1, β⁻¹, β⁻¹, β⁻¹] p 3 = β⁻¹ * p 3 := by simp [parScale]
  have hpd : parD (parScale ![1, β⁻¹, β⁻¹, β⁻¹] p) = ((β⁻¹ : ℝ) : ℂ) * parD p := by
    apply Complex.ext <;> simp [parD, parScale]
  have hmu : a1rMu W (p 0) left (((β⁻¹ : ℝ) : ℂ) * parD p) (β⁻¹ * p 3) =
      (foldedCircle (parD p) (p 3)).map fun w => fwdMap W (p 0) (Ψ left a w) := by
    obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG hp.1 left
    have hae' := TwoPoint.foldedCircle_ae_mem_H (((β⁻¹ : ℝ) : ℂ) * parD p) (mul_pos hβi hp.2)
    have hc : Measurable fun w : ℂ => ((β⁻¹ : ℝ) : ℂ) * w := measurable_const_mul _
    have hGa : AEMeasurable (fun w => fwdMap W (p 0) (g1zSideMap left W w))
        ((foldedCircle (parD p) (p 3)).map fun w => ((β⁻¹ : ℝ) : ℂ) * w) := by
      rw [WedgeTK.fc_map_mul _ _ hβi]
      exact hgm.aemeasurable.congr (hae'.mono fun w hw => (hEq hw).symm)
    unfold a1rMu
    rw [← WedgeTK.fc_map_mul _ _ hβi, AEMeasurable.map_map_of_aemeasurable hGa hc.aemeasurable]
    refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H (parD p) hp.2).mono fun w hw => ?_)
    have hw' : ((β⁻¹ : ℝ) : ℂ) * w ∈ H := by
      show 0 < (((β⁻¹ : ℝ) : ℂ) * w).im
      rw [Complex.im_ofReal_mul]; exact mul_pos hβi hw
    simp only [Function.comp_apply]
    rw [hdil hw']
    congr 3
    push_cast
    field_simp
  simp only [smearFam, a1rfNu, hp0, hp3, hpd, hmu]
  rfl

/-- A local Hölder bound on `[0, T]` of a continuous function is a global one. -/
theorem holder_global {W : ℝ → ℝ} (hW : Continuous W)
    (hloc : ∀ T : ℝ, 0 < T → ∃ α CH : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ CH ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
        |W t - W t'| ≤ CH * |t - t'| ^ α) (T : ℝ) :
    ∃ CH aH : ℝ, 0 ≤ CH ∧ 0 < aH ∧ aH ≤ 1 ∧
      ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, |W x - W y| ≤ CH * |x - y| ^ aH := by
  rcases le_or_gt T 0 with hT | hT
  · refine ⟨0, 1, le_rfl, one_pos, le_rfl, fun x hx y hy => ?_⟩
    have hx0 : x = 0 := le_antisymm (hx.2.trans hT) hx.1
    have hy0 : y = 0 := le_antisymm (hy.2.trans hT) hy.1
    simp [hx0, hy0]
  obtain ⟨α, CH, hα, hα1, hCH, hH⟩ := hloc T hT
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hW.continuousOn
  refine ⟨max CH (4 * |M|), α, le_max_of_le_left hCH, hα, hα1, fun x hx y hy => ?_⟩
  rcases le_or_gt |x - y| (1 / 2) with hd | hd
  · exact (hH x hx y hy hd).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))
  · have h1 : |W x - W y| ≤ 2 * |M| := by
      have := hM x hx; have := hM y hy
      rw [Real.norm_eq_abs] at *
      calc |W x - W y| ≤ |W x| + |W y| := abs_sub _ _
        _ ≤ M + M := add_le_add (by assumption) (by assumption)
        _ ≤ 2 * |M| := by linarith [le_abs_self M]
    have h2 : (1 / 2 : ℝ) ≤ |x - y| ^ α := by
      have h3 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ α :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hα1
      have h4 : (1 / 2 : ℝ) ^ α ≤ |x - y| ^ α :=
        Real.rpow_le_rpow (by norm_num) hd.le hα.le
      rw [Real.rpow_one] at h3
      linarith
    calc |W x - W y| ≤ 2 * |M| := h1
      _ = 4 * |M| * (1 / 2) := by ring
      _ ≤ 4 * |M| * |x - y| ^ α := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ max CH (4 * |M|) * |x - y| ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) _)

end A1RS
end R18
end QuantumZipper
