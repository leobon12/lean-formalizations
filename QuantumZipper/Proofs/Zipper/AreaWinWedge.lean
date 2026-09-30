import QuantumZipper.Proofs.Zipper.AreaWinTransfer
import QuantumZipper.Proofs.Zipper.AreaWinDefs
import QuantumZipper.Proofs.Zipper.WedgeRC3AllBasic
import QuantumZipper.Proofs.LQG.WedgeCanonical4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINDOW-WEDGE (2): the window limits for the unscaled wedge field from the free field

`wedgeWindowStmt_of_free`: the node `WedgeWindowStmt` (SW, arXiv:1605.06171, proof of Thm 1.1,
p. 9, for the unscaled wedge field) follows from the same statement `FreeWindowStmt` for the
free field `X'` itself.

Route (own elementary bookkeeping, no W-D product extension needed): the wedge field
`W = wedgeField (lateralPart X') A (Qc γ)` is `X' + ofFun g` with the wedge profile
`g = WedgeCan.wedgeProfile X' A (Qc γ)`, continuous on `ℍ`:

* area measures: `μ_W = e^{γ g} μ_{X'}` (`WedgeCan.qAreaMeasure_wedgeField_eq`, Sheffield
  arXiv:1012.4797 (5.1));
* regularized circle values: on every folded circle `fc(w, ρ)` with `w ∈ ℍ`, `ρ < Im w` (hence
  missing `0`), `evalReg W = evalReg X' + ∫ g d fc` (`F1.evalReg_wedgeField_fc_of_gap` and
  `WedgeCan.wedgeField_eq_evalReg_add_ofFun`);
* the deterministic transfer `windowLimits_transfer` (AreaWinTransfer.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

/-- On a folded circle centred in `ℍ` of radius `< Im w`, the regularized value of the wedge
field is that of the free sample plus the circle integral of the wedge profile. -/
theorem evalReg_wedgeField_fc_H {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F)
    (hray : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (Q : ℝ) {w : ℂ} (hw : w ∈ H) {ρ : ℝ} (hρ : 0 < ρ) (hρw : ρ < w.im) :
    evalReg (wedgeField (lateralPart x) A Q) (foldedCircle w ρ) =
      evalReg x (foldedCircle w ρ) + ∫ u, WedgeCan.wedgeProfile x A Q u ∂foldedCircle w ρ := by
  have hne : ‖w‖ ≠ ρ := by
    have := Complex.im_le_norm w
    exact ne_of_gt (by linarith)
  have hwb : w ∈ Hbar := H_subset_Hbar hw
  have h0 := WedgeCan.integrable_radAvgReg_foldedCircle hG hwb hρ hne
  have h1 := WedgeCan.integrable_Alog_foldedCircle hA hwb hρ hne
  rw [F1.evalReg_wedgeField_fc_of_gap hG hray hA Q hρ hne h0 h1]
  exact WedgeCan.wedgeField_eq_evalReg_add_ofFun h0
    (WedgeCan.integrable_logProfile_foldedCircle Q w ρ) h1

/-- **`WedgeWindowStmt` from `FreeWindowStmt`** (SW, arXiv:1605.06171, p. 9; the passage from the
free field to the wedge field is own elementary bookkeeping, see the module docstring). -/
theorem wedgeWindowStmt_of_free
    (h : ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ c c' : ℕ → ℝ, Tendsto c atTop (𝓝 1) ∧
      Tendsto c' atTop (𝓝 1) ∧ FreeWindowStmt (Real.sqrt κ) c c') : WedgeWindowStmt := by
  intro κ hκ hκ4
  obtain ⟨c, c', hc, hc', hfree⟩ := h κ hκ hκ4
  refine ⟨c, c', hc, hc', ?_⟩
  intro Ω _ P _ X' A hX hA _
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX (P := P)
  filter_upwards [hfree P X' hX, hG.ae_good, WedgeCan.ae_raw_dyadic hG,
    WedgeCan4.ae_continuous_wedgeProcess hA,
    AreaExist.ae_isVagueLimitOn_qAreaMeasure hX (P := P) hγ hγ2] with ω hW hgood hraw hAc hv
  exact windowLimits_transfer (WedgeCan.continuousOn_wedgeProfile_H hgood hAc _)
    (WedgeCan.qAreaMeasure_wedgeField_eq hgood hAc hraw ⟨_, hv⟩)
    (fun w hw ρ hρ hρw => evalReg_wedgeField_fc_H hgood hraw hAc _ hw hρ hρw) hW

end QuantumZipper.E6
