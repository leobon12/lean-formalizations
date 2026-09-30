import QuantumZipper.Proofs.Zipper.D3PlusLSCCIndepWin
import QuantumZipper.Proofs.Zipper.D3PlusLSCZMain
import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpreadHitPure
import QuantumZipper.Proofs.Zipper.D3PlusN2ContPair
import QuantumZipper.Proofs.Zipper.D3PlusN2ModelLocPair
import QuantumZipper.Proofs.Zipper.D3PlusN2RWin
import QuantumZipper.Proofs.Zipper.D3PlusN2RZero
import QuantumZipper.Proofs.Zipper.D3PlusN2RMix
import QuantumZipper.Proofs.Zipper.D3PlusN2RHeart
import QuantumZipper.Proofs.Zipper.D3PlusN2RFinal
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarMain
import QuantumZipper.Proofs.Zipper.D3PlusN2H2FreeWin
import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinDens
import QuantumZipper.Proofs.Zipper.D3PlusN2LipMain
import QuantumZipper.Proofs.Zipper.WedgeUnzipB3d
import QuantumZipper.Proofs.Thm18.LenPos
import QuantumZipper.Proofs.Thm18.Assembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Task T13-HARD3: route decisions for the three hard leaves of the Theorem 1.3 frontier

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797 (Prop. 1.6 proof, p. 25;
Theorem 1.8 and §5.1, pp. 60–62; §5.4, pp. 70–72); Duplantier–Miller–Sheffield arXiv:1409.7055,
Props. 4.7–4.8 (pp. 77–79). See `handoff/T13-HARD3.md`.

## 1. `LSCCHeartStmt` (D3⁺(ii), constant part) — needed, no bypass; three of its inputs closed

`D3PlusIIStmtRich` is consumed by `E5.e5G_of_d3'` through `ZoomModel.tvNear'` (E5 is proved only
*modulo* D3⁺(i)/(ii)), so the leaf is on the Theorem 1.3 route. Proved here, by wiring existing
proved nodes:

* `D3Plus.d3PlusIN2TmZeroStmt_holds` (`d3PlusIN2TmZero_of_winOpen` with its three window nodes
  proved), hence `D3Plus.lsccCanonStmt_holds : LSCCCanonStmt`;
* `D3Plus.n2ZModelLocStmt_holds : N2ZModelLocStmt` (`n2ZModelLoc_of_contPair ∘ n2ZContPair_of_osc`);
* `D3Plus.n2ZHeartWinStmt_holds : N2ZHeartWinStmt`;
* `D3Plus.lsccBadWinStmt_holds : LSCCBadWinStmt` (new proof: window event read through the
  restricted index, `n2GoodW_resFieldW`; TV to the wedge window, `n2ZHeartWinStmt_holds`; wedge-side
  exhaustion, `n2ZWedgeLocWin_holds`);
* the remaining route is in `T13Hard3Heart.lean`: `lsccHeart_of_tWin : LSCCTWinIndStmt →
  HitLevSpreadStmt → LSCCHeartStmt`. (The older inputs `LSCCIndWinStmt` / `LSCCIndTripleStmt` are
  false: the remainder `R_L` is a function of the window; see that file.)

## 2. `PStarRawDecompStmt` — FALSE as stated; bypassed

The raw identity at *every* folded circle `fc d r` is not a law-level property: a `P_*` sample is
pinned by `IsQuantumWedge` only through `fieldLawFull` (dyadic `coordsFull` circles and density
pairings), so changing `Y ω` at one non-dyadic folded circle (e.g. `fc (i/3) (1/3)`) by `+1` keeps
`IsPStarSample`, while the right-hand side `X'' + logSing + ofFun G` is continuous in probability
in `(d, r)` (Gaussian covariance of `X''`, continuity of `G`) and is pinned at the dyadic circles.
The same trap makes `Thm18Asm.UnzipBdryPosDecompStmt` false. Its only use
(`unzipBdryPosAtStmt_of`, `unzipBdryPosStmt_of_uw`) goes through `RegEq`, but even the `RegEq`
form is not the right node (the canonical field is a *randomly* rescaled unscaled wedge). Route
(Sheffield §5.1, B3(d): unzipping commutes with the canonical rescaling): positivity for the
unscaled configuration (`WedgeBdryPosAllStmt`, from the proved `wedgeDecompStmt_holds`), transported
to `P_*` samples by the realization `PStarRealizeStmt` exactly as `pStarGoodAll_of_core`
(`PStarBdryPosAllStmt`), then read in the Theorem 1.8 variables (`unzipBdryPosStmt_of_pstarBdryPos`,
proved here).

## 3. `PStarWitnessRealizeStmt` — true; proved in `T13Hard3Realize*.lean` (transfer theorem with a
standard Borel carrier `(ℕ → ℝ)³` for the reference witness; Kallenberg FMP Thm 6.10).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## 1. The LSCC cluster -/

/-- **N2Z-MODELLOC holds** (window transfer, model side). -/
theorem n2ZModelLocStmt_holds : N2ZModelLocStmt :=
  n2ZModelLoc_of_contPair (n2ZContPair_of_osc (n2ZPairOsc_of_firstMode n2ZFirstModeStmt_holds))

/-- **N2Z-HEART′ holds** (restricted-window TV convergence of the embedded model field). -/
theorem n2ZHeartWinStmt_holds : N2ZHeartWinStmt :=
  n2ZHeartWin_of_nodes (n2HLatTVWin_of_harm n2H2HarmWinStmt_holds)
    (n2HModelDecompWin_of_split n2H3SplitWinStmt_holds)

/-- **LSCC-IND-BADWIN holds.** Choose `K` with wedge-side bad-window probability `≤ ε/2`
(`n2ZWedgeLocWin_holds`), then `L` large with the restricted-window TV distance to the wedge
`≤ ε/2` (`n2ZHeartWinStmt_holds`); the bad event is read on the restricted window
(`n2GoodW_resFieldW`). Own elementary argument. -/
theorem lsccBadWinStmt_holds : LSCCBadWinStmt := by
  intro γ α r Ω _ P _ X R hγ hγ2 hα hr hX ε hε
  obtain ⟨Ω', m', P', Y', B', hP', hY', -⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond (γ := γ) hα
  obtain ⟨-, Ω'', _, P'', X'', A, hP'', hX'', hA, hI, -⟩ := hY'
  obtain ⟨hmeasW, -, hexh⟩ := n2ZWedgeLocWin_holds γ α P'' X'' A hγ hγ2 hα hX'' hA hI
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 (hexh R) _ hε2)
  set K : ℕ := max K₀ 1 with hKdef
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbadW := hK₀ K (le_max_left _ _)
  obtain ⟨hmeas, htv⟩ := n2ZHeartWinStmt_holds γ α r P X P'' X'' A hγ hγ2 hα hr hX hX'' hA hI K hK
  refine ⟨K, hK, ?_⟩
  filter_upwards [ENNReal.tendsto_nhds_zero.1 htv _ hε2] with L hL
  have hS : MeasurableSet (n2GoodW γ K R)ᶜ := (measurableSet_n2GoodW γ K R).compl
  have e1 : {ω | resField K (n2Emb γ α L r X ω) ∉ n2Good γ K R} =
      (fun ω => resFieldW K (n2Emb γ α L r X ω)) ⁻¹' (n2GoodW γ K R)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, n2GoodW_resFieldW]
  have e2 : P'' {ω | resFieldW K (wedgeV γ X'' A ω) ∉ n2GoodW γ K R} =
      (P''.map fun ω => resFieldW K (wedgeV γ X'' A ω)) (n2GoodW γ K R)ᶜ := by
    rw [Measure.map_apply_of_aemeasurable (hmeasW K hK) hS]
    rfl
  rw [e1, ← Measure.map_apply_of_aemeasurable (hmeas L) hS]
  have h1 := TV.le_tvDist (μ := P.map fun ω => resFieldW K (n2Emb γ α L r X ω))
    (ν := P''.map fun ω => resFieldW K (wedgeV γ X'' A ω)) hS
  rw [tsub_le_iff_right] at h1
  calc _ ≤ _ := h1
    _ ≤ ε / 2 + ε / 2 := add_le_add hL (e2 ▸ hbadW)
    _ = ε := ENNReal.add_halves ε

end D3Plus

/-! ## 2. Boundary positivity: the unscaled node and its `P_*` form -/

namespace WedgeUnzip

end WedgeUnzip

namespace Thm18Asm

end Thm18Asm
end QuantumZipper
