import QuantumZipper.Proofs.Thm18.A1RFLoopY

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RF (wiring): the A1b input from the full smoothing node

The A1b chain reads the far node only at `t = lenTimeArc γ ℓ c₀` (`A1RG.ae_sideRTXArc`). There
it follows from `A1RFFullYStmt` (`A1RF.ae_farArc`, A1RFCut.lean). Copies of the A1RG wiring
(A1RGWire.lean) with `hfar` replaced:

* `A1RF.ae_sideRTXArcF : A1RFFullYStmt → (SideRTX at lenTimeArc, a.s.)`;
* `A1RF.g1ZA1bSideExactArcStmt_of_full : A1RFFullYStmt → G1ZA1bSideExactArcStmt`;
* `theorem1_8PaperMO_of_leaves5`: `theorem1_8PaperMO` from `A1RFFullYStmt` and the other five
  leaves of `theorem1_8PaperMO_of_leaves6`;
* `theorem1_8PaperMO_of_leaves5s`: the same with `A1RFFullYStmt` replaced by `A1RFSmearContStmt`
  (`a1rfFullYStmt_of` with the proved per-loop node `A1RF.a1rfLoopUCStmt_holds`, A1RFLoopY.lean).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

namespace A1RF

/-- **SideRTX at the open-arc unzipping time**, from the full smoothing node (cut-off argument of
`g1A1b2SideTendstoStmt_of_cut` at `t = lenTimeArc`). -/
theorem ae_sideRTXArcF (hFull : A1RFFullYStmt) {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (left : Bool) :
    ∀ᵐ ω ∂P, 0 < unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) →
      G1A1b.SideRTXAt (Y ω) (Qc γ) (drive (γ ^ 2) B ω) (lenTimeArc γ ℓ (wedgeConfig γ B Y ω))
        (g1zSideMap left (drive (γ ^ 2) B ω)) := by
  filter_upwards [A1RG.ae_arcGrowthNear hS hIn hℓ, ae_farArc hFull hS hIn hℓ left,
    ae_g1zDrvGood hS hIn,
    ae_isRegularSample_unzipped hS, ae_lenTimeArc_pos hS hIn hℓ]
    with ω hgr hfar hG hreg ht ha
  set W := drive (γ ^ 2) B ω with hW
  set t := lenTimeArc γ ℓ (wedgeConfig γ B Y ω) with htdef
  obtain ⟨F, hF⟩ := hreg t ht.le
  refine ⟨F, hF, fun d hd s hs =>
    ⟨fun ρ hρ => G1A1b.integrable_sideFamily hG ht left hF.1 d hs hρ, ?_⟩⟩
  obtain ⟨Rr, hsupp⟩ := A1R.exists_ae_bdd_a1rMu hG ht left d hs
  obtain ⟨C, hC, hCb⟩ := hgr ha F hF Rr
  obtain ⟨Cm, β, hβ, hmass⟩ := a1rMassStmt_holds W hG t ht left d hd s hs
  have : IsFiniteMeasure (a1rMu W t left d s) := by
    unfold a1rMu; infer_instance
  exact A1R.tendsto_integral_of_cutoff (μ := a1rMu W t left d s) (F := F)
    (half_pos hβ) hC a1rNear A1R.measurableSet_a1rNear
    (fun ρ hρ => G1A1b.integrable_sideFamily hG ht left hF.1 d hs hρ)
    (fun ρ hρ hρ1 => hsupp.mono fun z hz hzN => hCb ρ hρ hρ1 z hz.1 hz.2 hzN)
    (fun ρ hρ hρ1 => by
      have h1 : Real.sqrt ρ < 1 := by
        rw [Real.sqrt_lt' one_pos]; simpa using hρ1
      have := hmass (Real.sqrt ρ) (Real.sqrt_pos.2 hρ) h1
      rwa [A1R.sqrt_rpow_eq hρ.le] at this)
    (hfar ha F hF d hd s hs)

/-- **The headline input `hA1b` from the full smoothing node** (copy of
`g1ZA1bSideExactArcStmt_of_sideRTX` with SideRTX read at `lenTimeArc` only). -/
theorem g1ZA1bSideExactArcStmt_of_full (hFull : A1RFFullYStmt) : G1ZA1bSideExactArcStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ left
  have hRx : G1RegExSide γ P B Y left := by
    have := g1RegExStmt_of_rest g1RegRepRestStmt_holds γ P B Y hS hIn
    cases left
    · exact this.2
    · exact this.1
  filter_upwards [ae_sideRTXArcF hFull hS hIn hℓ left, ae_lenTimeArc_pos hS hIn hℓ,
    ae_g1zDrvGood hS hIn, hRx, hIn.2.2] with ω hRω ht hW hRxω hin
  intro ha e he r hr
  set W := drive (γ ^ 2) B ω with hWdef
  set t := lenTimeArc γ ℓ (wedgeConfig γ B Y ω) with htdef
  set a := unzipScaleArc γ ℓ (wedgeConfig γ B Y ω) with hadef
  obtain ⟨hW', lam, β, hlam, -, hEq, -⟩ := G1ZA1a.g1RerootAffineStmt_holds W hW t a ht ha left
  obtain ⟨φ, hφ, hcore⟩ := hRxω
  have hU : IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)
      (uniformizer (sideDom (sleTrace (γ ^ 2) B ω) left)) := by
    cases left
    · exact hin.2.2.2
    · exact hin.2.2.1
  have hcore' : G1.ChoiceRegularCore γ (Y ω) (g1zSideMap left W) :=
    G1.choiceRegularCore_invFunOn_of_normalized hin.1 left hφ hU hcore
  obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props (G1.isOpen_component hin.1 left) hU
  have hψi := G1.injOn_invFunOn_of_uniformizer hU
  have hη' := hW'.2.2.2.1
  have hU' := G1ZA1a.isNormalizedUniformizer_sideDom hη' left
  obtain ⟨hψ'd, -, hψ'm, hψ'D⟩ := G1.invFunOn_props (G1ZA1a.isOpen_sideDom hη' left) hU'
  have hψ'i := G1.injOn_invFunOn_of_uniformizer hU'
  have hψ'H : MapsTo (g1zSideMap left (g1zNewDrv W t a)) H H :=
    fun w hw => G1ZA1a.sideDom_subset_H _ left (hψ'D hw)
  exact G1A1b.exact_of_sideRTX hW.1 hW.2.1 ht.le ha hcore'.1 hcore'.2.1 hlam hψm hψd hψ0
    (fun d s hs => G1.integrable_log_norm_deriv_foldedCircle_of_injOn hψd hψi d hs)
    hEq hψ'm hψ'd hψ'i hψ'H (hRω ha) e he r hr

end A1RF

/-- **The full smoothing node from continuity along the smeared family** (the per-loop node is
proved). -/
theorem a1rfFullYStmt_of_smear (hCs : A1RFSmearContStmt) : A1RFFullYStmt :=
  a1rfFullYStmt_of A1RF.a1rfLoopUCStmt_holds hCs

end R18
end QuantumZipper
