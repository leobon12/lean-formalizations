import QuantumZipper.Proofs.Thm18.G1Side2Wire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (1): the area clause from its form at the selected maps of the representative

`G1Z2SideAreaStmt` (G1Side2Wire.lean) asks, for the Theorem 1.8 wedge `Y` and EVERY normalized
uniformizer of the side domain, for the area limit (along all radii) of the pulled-back field,
of mass `< 1` near real points and infinite in total. As for the boundary clause
(`Thm18Asm.bdryAll_rep`, `ae_sideBdryLim_all`), this follows from the same statement for the
canonical representative `wedgeRep` and the SELECTED side maps, for a.e. path
(`G1Z2SideAreaSelStmt`, decision D88): the good set is measurable (area certificate
`GoodMeas.AreaCert`, the small/top set `G1ZA2.SetST`), the law of `Y` is that of the representative
and the path is independent; any normalized uniformizer is the selected map composed with a
dilation (U6), under which the three clauses are stable (`GoodTransforms.hasAreaLimit_rescale`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- The area clause for one field. -/
def AreaGood (γ : ℝ) (x : FieldSample) : Prop :=
  ∃ μ : Measure ℂ, HasAreaLimit γ x μ ∧
    (∀ p : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) ∧ μ H = ⊤

/-- **Node (D88): the area clause at the selected maps of the representative, a.e. path.** -/
def G1Z2SideAreaSelStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      AreaGood γ (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))

theorem hasAreaLimit_congr_avg {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x')
    {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ) : HasAreaLimit γ x' μ := by
  have hb : ∀ r, areaR γ x r = areaR γ x' r := fun r => by
    unfold areaR areaDens
    simp_rw [Factorization.evalReg_congr h]
  refine ⟨hμ.1, hμ.2.1, fun f hf hfc hfS => ?_⟩
  simp_rw [← hb]
  exact hμ.2.2 f hf hfc hfS

theorem areaGood_congr_avg {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x')
    (hx : AreaGood γ x) : AreaGood γ x' := by
  obtain ⟨μ, hμ, hs, ht⟩ := hx
  exact ⟨μ, hasAreaLimit_congr_avg h hμ, hs, ht⟩

/-- **The area clause survives rescaling.** -/
theorem areaGood_rescale {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsRegularSample x)
    (hg : AreaGood γ x) {b : ℝ} (hb : 0 < b) : AreaGood γ (rescale x (Qc γ) b) := by
  obtain ⟨μ, hμ, hs, ht⟩ := hg
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hm : Measurable fun z : ℂ => z / (b : ℂ) := measurable_id.div_const _
  have hHm : MeasurableSet H :=
    (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hHpre : (fun z : ℂ => z / (b : ℂ)) ⁻¹' H = H := by
    ext z
    show 0 < (z / (b : ℂ)).im ↔ 0 < z.im
    rw [Complex.div_ofReal_im]
    exact div_pos_iff_of_pos_right hb
  refine ⟨_, GoodTransforms.hasAreaLimit_rescale hx hγ hμ hb, fun p => ?_, ?_⟩
  · obtain ⟨a, ha, hμa⟩ := hs (b * p)
    refine ⟨a / b, div_pos ha hb, ?_⟩
    rw [Measure.map_apply hm (measurableSet_ball.inter hHm)]
    refine lt_of_le_of_lt (measure_mono fun z hz => ?_) hμa
    obtain ⟨h1, h2⟩ := hz
    refine ⟨?_, by rw [← hHpre]; exact h2⟩
    rw [Metric.mem_ball] at h1 ⊢
    have e : z - ((b * p : ℝ) : ℂ) = (b : ℂ) * (z / (b : ℂ) - (p : ℂ)) := by
      push_cast; field_simp
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
    rw [dist_eq_norm] at h1
    calc b * ‖z / (b : ℂ) - (p : ℂ)‖ < b * (a / b) := mul_lt_mul_of_pos_left h1 hb
      _ = a := by field_simp
  · rw [Measure.map_apply hm hHm, hHpre]
    exact ht

end Thm18Asm
end QuantumZipper
