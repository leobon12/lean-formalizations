import QuantumZipper.Proofs.Thm18.G1PairQuantMain
import QuantumZipper.Proofs.Thm18.G1RestUnifMain
import QuantumZipper.Proofs.Zipper.D3PlusN2LipMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PAIRLIP (1): the Lipschitz pairing node from a first-circle-mode node

`G1RestPairLipStmt` (G1PairQuantDefs.lean) is the analogue, for the pulled-back wedge field
`x = coordChange (wedgeRep γ X A ω') ψ Q`, of the free-field node `D3Plus.N2ZPairLipStmt` at
scale `1`. That node was proved in two halves: a deterministic implication
`D3Plus.n2Lip_det1` (regular witness `F` + first-circle-mode bound `C/√τ` ⇒ Lipschitz modulus)
and the probabilistic first-mode node `D3Plus.N2ZFirstModeStmt`. We mirror the split:

* `G1RestFirstModeStmt` (stated here): a.s. the first Fourier mode on `∂B(w, τ)` of the
  `s`-circle averages of `x` is `O(τ^{-1/2})`, uniformly for `w` in a compact `K ⊆ H`,
  `τ ∈ (0, τ₀)`, `s ∈ (0, τ)`;
* `g1RestPairLip_of_firstMode : G1RestFirstModeStmt → G1RestPairLipStmt` (proved here), by
  `D3Plus.n2Lip_det1` applied to the regular witness of `x`, which exists a.s. by the proved
  RC2 half (`G1RC.g1RegRepRC2Stmt_of_psiExt`);
* `g1RegRepRestStmt_of_firstMode : G1RestFirstModeStmt → G1RegRepRestStmt`, with the proved
  `g1RestUnifStmt_holds`.

Own elementary argument (bookkeeping only; the deterministic analysis is `D3Plus.n2Lip_det1`).
The expected source for the first-mode bound is the circle-average variance/modulus estimate of
Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann. Probab. 38 (2010), Prop. 2.1,
applied to the pulled-back field (see the report of task G1-PAIRLIP).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal Topology Real

namespace QuantumZipper
namespace Thm18Asm

/-- **Node G1-REST-FIRSTMODE** (probabilistic half of `G1RestPairLipStmt`): for a.e. path and
both sides, almost surely the pulled-back representative `x` satisfies: for every compact
`K ⊆ H` there are `C` and `τ₀ > 0` with
`‖∫_0^{2π} ⟨x, σ_s(w + τ e^{iθ})⟩ e^{iθ} dθ‖ ≤ C / √τ` for `w ∈ K`, `τ ∈ (0, τ₀)`,
`s ∈ (0, τ)` (`σ_s(v)` = folded circle measure). This is `D3Plus.N2ZFirstModeStmt` for the
pulled-back wedge field, stated through `evalReg` instead of a regular witness. -/
def G1RestFirstModeStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
      ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ,
          ‖∫ θ in (0 : ℝ)..(2 * π),
              ((evalReg (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))
                  (foldedCircle (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) s) : ℝ) :
                ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ C / Real.sqrt τ

namespace G1PairLip

/-- The first-mode bound through `evalReg` gives the witness form `D3Plus.N2LipModeHyp F`. -/
theorem modeHyp_of_evalReg {x : FieldSample} {F : ℂ × ℝ → ℝ} (hFx : IsRegularWith x F)
    (h : ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ,
        ‖∫ θ in (0 : ℝ)..(2 * π),
            ((evalReg x (foldedCircle (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) s) :
              ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ C / Real.sqrt τ) :
    D3Plus.N2LipModeHyp F := by
  intro K hK hKH
  obtain ⟨C, τ₀, hτ₀, hb⟩ := h K hK hKH
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 1, one_pos, fun w hw => absurd hw (notMem_empty w)⟩
  obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hm : 0 < z0.im := hKH hz0
  refine ⟨C, min τ₀ z0.im, lt_min hτ₀ hm, fun w hw τ hτ s hs => ?_⟩
  have hτ1 : τ < τ₀ := hτ.2.trans_le (min_le_left _ _)
  have hτ2 : τ < z0.im := hτ.2.trans_le (min_le_right _ _)
  have hs0 : 0 < s := hs.1
  have e : (∫ θ in (0 : ℝ)..(2 * π),
        ((F (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I), s) : ℝ) : ℂ) *
          Complex.exp ((θ : ℂ) * Complex.I)) =
      ∫ θ in (0 : ℝ)..(2 * π),
        ((evalReg x (foldedCircle (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) s) :
          ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hmem : w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Hbar := by
      show (0 : ℝ) ≤ (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im
      rw [Complex.add_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      have hw' : z0.im ≤ w.im := hmin hw
      have hsin : -1 ≤ Real.sin θ := Real.neg_one_le_sin θ
      nlinarith [hτ.1]
    rw [hFx.evalReg_fc_of_mem hmem hs0]
  rw [e]
  exact hb w hw τ ⟨hτ.1, hτ1⟩ s hs

end G1PairLip

/-- **G1-PAIRLIP from the first-mode node.** -/
theorem g1RestPairLip_of_firstMode (hFM : G1RestFirstModeStmt) : G1RestPairLipStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  filter_upwards [G1RC.g1RegRepRC2Stmt_of_psiExt
      (G1RC.g1PsiExtStmt_of_holder_α G1RC.g1GoodBMStmt_sideHolderGood)
      γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
    hFM γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a h2 hfm left
  filter_upwards [h2 left, hfm left] with ω' hreg hmode
  set x := coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ) with hx
  obtain ⟨F, hFx⟩ := hreg
  intro K hK hKH
  obtain ⟨C, δ, hδ, hb⟩ := D3Plus.n2Lip_det1 hFx.1 hFx.2.2
    (G1PairLip.modeHyp_of_evalReg hFx hmode) hK hKH
  refine ⟨C, δ, hδ, fun L f hf hf0 t ht s hs => ?_⟩
  have e : (∫ u, (evalReg x (foldedCircle u t) - evalReg x (foldedCircle u s)) * f u) =
      ∫ u, (F (u, t) - F (u, s)) * f u := by
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    by_cases hu : u ∈ K
    · have hu' : u ∈ Hbar := show (0 : ℝ) ≤ u.im from le_of_lt (hKH hu)
      simp only
      rw [hFx.evalReg_fc_of_mem hu' ht.1, hFx.evalReg_fc_of_mem hu' hs.1]
    · simp [hf0 u hu]
  rw [e]
  exact hb L f hf hf0 t ht s hs

/-- **`G1RegRepRestStmt` from the first-mode node** (with the proved uniform Cauchy input). -/
theorem g1RegRepRestStmt_of_firstMode (hFM : G1RestFirstModeStmt) : G1RegRepRestStmt :=
  g1RegRepRestStmt_of_pairLip_unif (g1RestPairLip_of_firstMode hFM) g1RestUnifStmt_holds

end Thm18Asm
end QuantumZipper
