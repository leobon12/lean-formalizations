import QuantumZipper.Proofs.Zipper.XFlowEnergyDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-ENERGY: assembly of `FlowEnergyStmt` from the three moduli

`flowEnergyStmt_of : FlowAdmStmt → FlowE1Stmt → FlowE2Stmt → FlowE3Stmt → FlowEnergyStmt`:
the triangle inequality for the Neumann energy (`RegUnif.kernelCov2_self_triangle`) along
`μ_{p,ρ} → μ_{p,ρ'} → μ_{(u',s',d,r),ρ'} → μ_{p',ρ'}` and the exponent bookkeeping
`RegUnif.rpow_le_of_le_both` (own elementary bookkeeping, as `RegUnif.energyUS_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint RegUnif

/-- Diameter bound of a box. -/
theorem dist_le_of_flowBox {m : ℕ} {p p' : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowBox m)
    (hp' : p' ∈ flowBox m) : dist p p' ≤ 4 * ((m : ℝ) + 2) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hr1 : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
  have hd : dist p.2.2.1 p'.2.2.1 ≤ 4 * ((m : ℝ) + 2) := by
    rw [Complex.dist_eq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]
    have a1 := hp.2.2.1; have a2 := hp'.2.2.1; have a3 := hp.2.2.2.1; have a4 := hp'.2.2.2.1
    have b1 : |p.2.2.1.re - p'.2.2.1.re| ≤ 2 * ((m : ℝ) + 1) := by
      rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    have b2 : |p.2.2.1.im - p'.2.2.1.im| ≤ 2 * ((m : ℝ) + 1) := by
      rw [abs_le]; constructor <;> linarith [a3.1, a3.2, a4.1, a4.2]
    linarith
  rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  refine max_le ?_ (max_le ?_ (max_le hd ?_))
  · rw [abs_le]; constructor <;> linarith [hp.1.1, hp.1.2, hp'.1.1, hp'.1.2]
  · rw [abs_le]; constructor <;> linarith [hp.2.1.1, hp.2.1.2, hp'.2.1.1, hp'.2.1.2]
  · rw [abs_le]; constructor <;>
      linarith [hp.2.2.2.2.1, hp.2.2.2.2.2, hp'.2.2.2.2.1, hp'.2.2.2.2.2]

/-- **`FlowEnergyStmt` from admissibility and the three moduli.** -/
theorem flowEnergyStmt_of (hA : FlowAdmStmt) (h1 : FlowE1Stmt) (h2 : FlowE2Stmt)
    (h3 : FlowE3Stmt) : FlowEnergyStmt := by
  intro m W a CH hWH
  have hW : Continuous W := hWH.1
  have hW0 : W 0 = 0 := hWH.2.1
  obtain ⟨C₁, a₁, hC₁, ha₁, hE1⟩ := h1 m W hW hW0
  obtain ⟨C₂, b₂, hC₂, hb₂, hE2⟩ := h2 m W a CH hWH
  obtain ⟨C₃, b₃, hC₃, hb₃, hE3⟩ := h3 m W a CH hWH
  set c := min (min a₁ b₂) (min b₃ 1) with hc
  have hc0 : 0 < c := lt_min (lt_min ha₁ hb₂) (lt_min hb₃ one_pos)
  have hca : c ≤ a₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hcb : c ≤ b₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hcb3 : c ≤ b₃ := (min_le_right _ _).trans (min_le_left _ _)
  set L : ℝ := 4 * ((m : ℝ) + 2) with hL
  have hL1 : (1 : ℝ) ≤ L := by rw [hL]; have := Nat.cast_nonneg (α := ℝ) m; linarith
  refine ⟨2 * (C₁ * (1 + (L + 1) ^ a₁)) + 4 * (C₂ * (1 + (L + 1) ^ b₂)) +
    4 * (C₃ * (1 + (L + 1) ^ b₃)), c, by positivity, hc0, fun p hp p' hp' ρ hρ ρ' hρ' => ?_⟩
  set q : ℝ × ℝ × ℂ × ℝ := (p'.1, p'.2.1, p.2.2.1, p.2.2.2) with hqdef
  have hq : q ∈ flowBox m := ⟨hp'.1, hp'.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩
  have hpP := flowBox_subset_flowPar m hp
  have hp'P := flowBox_subset_flowPar m hp'
  have hqP := flowBox_subset_flowPar m hq
  obtain ⟨hA1, hm1⟩ := hA W hW hW0 p hpP ρ hρ
  obtain ⟨hA2, hm2⟩ := hA W hW hW0 p hpP ρ' hρ'
  obtain ⟨hA3, hm3⟩ := hA W hW hW0 q hqP ρ' hρ'
  obtain ⟨hA4, hm4⟩ := hA W hW hW0 p' hp'P ρ' hρ'
  rw [abs_of_nonneg (kernelCov2_self_nonneg hA1 hA4 (hm1.trans hm4.symm))]
  have t1 := kernelCov2_self_triangle hA1 hA2 hA4 (hm1.trans hm2.symm) (hm2.trans hm4.symm)
  have t2 := kernelCov2_self_triangle hA2 hA3 hA4 (hm2.trans hm3.symm) (hm3.trans hm4.symm)
  have e1 := (le_abs_self _).trans (hE1 p hp ρ hρ ρ' hρ')
  have e2 := (le_abs_self _).trans (hE2 p hp q hq rfl ρ' hρ')
  have e3 := (le_abs_self _).trans (hE3 q hq p' hp' rfl rfl ρ' hρ')
  have hdpq : dist p q ≤ dist p p' := by
    rw [hqdef, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq (x := p) (y := p'),
      Prod.dist_eq (x := p.2) (y := p'.2), Prod.dist_eq (x := p.2.2) (y := p'.2.2)]
    simp only [dist_self, max_self]
    exact max_le_max le_rfl (max_le_max le_rfl (le_max_of_le_left dist_nonneg))
  have hdqp : dist q p' ≤ dist p p' := by
    rw [hqdef, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Prod.dist_eq (x := p) (y := p'),
      Prod.dist_eq (x := p.2) (y := p'.2), Prod.dist_eq (x := p.2.2) (y := p'.2.2)]
    simp only [dist_self]
    exact max_le (le_max_of_le_left dist_nonneg) (max_le (le_max_of_le_right
      (le_max_of_le_left dist_nonneg)) (le_max_of_le_right (le_max_of_le_right le_rfl)))
  set Δ := dist p p' + |ρ - ρ'| with hΔ
  have hρL : |ρ - ρ'| ≤ L := by
    have : |ρ - ρ'| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hρ.1, hρ.2, hρ'.1, hρ'.2]
    linarith
  have f1 := rpow_le_of_le_both (abs_nonneg _) (show |ρ - ρ'| ≤ Δ by linarith [dist_nonneg (x := p) (y := p')]) hρL hc0 hca
  have f2 := rpow_le_of_le_both dist_nonneg (show dist p q ≤ Δ by linarith [abs_nonneg (ρ - ρ')])
    (hdpq.trans (dist_le_of_flowBox hp hp')) hc0 hcb
  have f3 := rpow_le_of_le_both dist_nonneg (show dist q p' ≤ Δ by linarith [abs_nonneg (ρ - ρ')])
    (hdqp.trans (dist_le_of_flowBox hp hp')) hc0 hcb3
  have g1 := mul_le_mul_of_nonneg_left f1 hC₁
  have g2 := mul_le_mul_of_nonneg_left f2 hC₂
  have g3 := mul_le_mul_of_nonneg_left f3 hC₃
  nlinarith

end F1
end QuantumZipper
