import QuantumZipper.Proofs.Zipper.WedgeFlowWDBasic
import QuantumZipper.Proofs.Zipper.WedgeDecompCore
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.WedgeXContReg
import QuantumZipper.Proofs.Thm12.CharFun

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# WEDGE-FLOW-WD (part 2): the wedge flow nodes from the free-field flow nodes

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 rule (5.1) and §5.4;
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1.

By the proved radial resampling W-D (`WedgeUnzip.WDec.wedgeDecompStmt_holds`), on a product
extension the unscaled wedge field agrees on every folded circle with `x + G`, where
`x = X'' + α₀(−log|·|)` with `X''` a free field independent of the driver and `G` continuous. With
the proved global Carathéodory core (`WedgeUnzip.globalCaraStmt_holds`) and the deterministic
transfers of `WedgeFlowWDBasic.lean`, the two wedge flow nodes of `WedgeCocycleCore.lean` reduce
to their free-field (`x`) forms plus the single-time free-field nodes X-G and X-C already used by
the single-time wedge chain (`WedgeUnzip.wedgeExactAll_of_x`):

* `wedgeFlowRC3Stmt_of_x : XGoodAllStmt → XContinuumStmt → XFlowRC3Stmt → XFlowContStmt →
  WedgeFlowRC3Stmt`;
* `wedgeFlowContStmt_of_x : XGoodAllStmt → XContinuumStmt → XFlowContStmt → WedgeFlowContStmt`.
* `xExactAll_of_xFlowRC3`: X-X (`WedgeUnzip.XExactAllStmt`) is the case `s = 0` of `XFlowRC3Stmt`;
* `unscaledFlowCoreStmt_of_xFlow`, `unscaledFlowRegStmt_of_xFlow`: hence `UnscaledFlowCoreStmt`
  (and `UnscaledFlowRegStmt`) from X-G, X-C, `XFlowRC3Stmt` and `XFlowContStmt` alone.

The new inputs `XFlowRC3Stmt` and `XFlowContStmt` are the exact analogues, for the free field with
the log singularity, of the two wedge flow nodes (RC3 at the pushed circles along the flow, and
the continuum limit along the flow; the integrability half of the latter is proved from X-G).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- **(Free-field flow node, RC3)** For `x = X + α₀(−log|·|)`, `X` a free field independent of the
driver: a.s., for all `u, s ≥ 0` and folded circles centred in `ℍ̄`, `x_u` is regularized exactly
at `R_* fc(d, r)`, `R` the unzipping map of the flow from `u` to `u + s` (the `x`-analogue of
`WedgeFlowRC3Stmt`; at all circles and horizons, of the `Γ⁰` node `RegUnif.UnifRC3Stmt`). -/
def XFlowRC3Stmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (F2.unzX κ (X ω) (drive κ B ω) u)
          ((foldedCircle d r).map (revMap (B2.vrev (drive κ B ω) (u + s)) s)) =
        F2.unzX κ (X ω) (drive κ B ω) u
          ((foldedCircle d r).map (revMap (B2.vrev (drive κ B ω) (u + s)) s))

/-- **(Free-field flow node, continuum limit)** For `x = X + α₀(−log|·|)`: a.s., for all
`u, t ≥ 0`, `c` and `r > 0`, the smoothed pairings of `x_u` against the image of `fc(c, r)` under
the unzipping map of the shifted driver at time `t` converge as the smoothing radius tends to `0⁺`
(the `x`-analogue of the limit clause of `WedgeFlowContStmt`; flow form of X-C). The integrability
clause is not assumed: it follows from X-G (`integrable_smoothed_of_regular`). -/
def XFlowContStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ u t : ℝ, 0 ≤ u → 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (F2.unzX κ (X ω) (drive κ B ω) u)
          (foldedCircle v ρ) ∂((foldedCircle c r).map (fwdMapInv (shiftDrv (drive κ B ω) u) t)))
        (𝓝[>] 0) (𝓝 L)

/-- Smoothed pairings of a regular sample against a pushed folded circle are integrable (the
witness is continuous and the pushed circle is carried by a bounded part of `ℍ`; as
`WedgeUnzip.ae_integrable_smoothed_pairing`). -/
theorem integrable_smoothed_of_regular {x : FieldSample} (hx : IsRegularSample x) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (c : ℂ) {r : ℝ} (hr : 0 < r)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun v => evalReg x (foldedCircle v ρ)) ((foldedCircle c r).map (fwdMapInv W t)) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨_C, Bc, _hC, _hBc, hfacts⟩ := RegCont.νT_facts hW hW0 t c hr
  obtain ⟨hνP, -, hνB⟩ := hfacts t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure ((foldedCircle c r).map (fwdMapInv W t)) := hνP
  have hνH : ∀ᵐ w ∂((foldedCircle c r).map (fwdMapInv W t)), w ∈ Hbar ∧ ‖w‖ ≤ Bc :=
    hνB.mono fun w hw => ⟨mem_Hbar_of_H hw.1, hw.2⟩
  have hg : ContinuousOn (fun u : ℂ => F (u, ρ)) Hbar :=
    hF.1.comp (Continuous.continuousOn (continuous_id.prodMk continuous_const))
      (fun u hu => ⟨hu, hρ⟩)
  refine (WedgeUnzip.integrable_of_continuousOn_of_carried hg hνH).congr ?_
  filter_upwards [hνH] with u hu
  exact (hF.evalReg_fc_of_mem hu.1 hρ).symm

/-- **X-X is the case `s = 0` of the free-field flow node** (`revMap _ 0 = id` on `ℍ`). -/
theorem xExactAll_of_xFlowRC3 (h : XFlowRC3Stmt) : WedgeUnzip.XExactAllStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [h κ hκ hκ4 P B X hB hX hind, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hω hc h0 t ht d hd r hr
  have hW : Continuous (drive κ B ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hV : Continuous (B2.vrev (drive κ B ω) (t + 0)) := B2.continuous_vrev hW _
  have hV0 : B2.vrev (drive κ B ω) (t + 0) 0 = 0 := B2.vrev_zero (by linarith)
  have hmap : (foldedCircle d r).map (revMap (B2.vrev (drive κ B ω) (t + 0)) 0) =
      foldedCircle d r := by
    rw [Measure.map_congr (show revMap (B2.vrev (drive κ B ω) (t + 0)) 0 =ᵐ[foldedCircle d r] id
      from (TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz =>
        CharFun.revMap_zero_eq hV hV0 hz), Measure.map_id]
  have := hω t 0 ht le_rfl d hd r hr
  rwa [hmap] at this

end F1
end QuantumZipper
