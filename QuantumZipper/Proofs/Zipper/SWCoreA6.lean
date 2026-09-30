import QuantumZipper.Proofs.Zipper.SWCoreA6Fam
import QuantumZipper.Proofs.Zipper.PStarAreaAll
import QuantumZipper.Proofs.Zipper.WedgeUnzipB3d

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A6: `E6.WedgeAreaMergeUnifStmt` from the class-uniform distortion bound for the wedge field

`E6.WedgeAreaMergeUnifStmt` (AreaCoord.lean) follows from the deterministic
`SWCore.mergeUnif_of_sample` applied to the unscaled wedge field `x₀ = F2.zU √κ X' A ω`, with
* window limits: `E6.WedgeWindowStmt` (proved: `wedgeWindowStmt_of_splitR` +
  `swWindowSplitStmtR_holds`, constants `swC → 1`);
* local finiteness of the area measure: `E6.ae_areaAll_wedgeField` (proved);
* regularity of `x₀`: the D29 core `WedgeUnzip.WedgeContinuumStmt` (first conjunct);
* the distortion bound for `x₀` along the flow maps only: `WedgeFlowErrStmt` below (D64: the
  finite-parameter primed core suffices; `mergeUnif_of_flowErr`). Own bookkeeping (Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4,
(3.5)–(3.7), for the flow `φ = f_t⁻¹`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open E6

/-- **The distortion bound for the unscaled wedge field along the Loewner flow** (a.s.): for
every horizon `T`, rational rectangle `K ⊂ ℍ` and `η > 0`, eventually in `k`, for all
`t ∈ [0,T]` and `z ∈ K`, the pushed average of `x₀ ∘ f_t⁻¹ + Q log|(f_t⁻¹)'|` at `(z, 2^{-k})` is
`η`-close to `Q log|(f_t⁻¹)'(z)|` plus the round average of `x₀` at
`(f_t⁻¹ z, 2^{-k}|(f_t⁻¹)'(z)|)`. This is what the finite-parameter primed core
`swcNA2I_primed` (family `(t, z)`, D64) gives at a fixed driver, after the add-on
`areaDistClassGood_add_ofFun`-type step for `x₀ = X' + (continuous function near K)` and Fubini
over the independent driver. -/
def WedgeFlowErrStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∀ a b c d : ℚ, (0 : ℝ) < c → ∀ η : ℝ, 0 < η →
      ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) T, ∀ z ∈ rectC a b c d,
        |pushErr (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (fwdMapInv (drive κ B'' ω) t) k z|
          ≤ η

/-- `AreaAll` gives finiteness on compact subsets of `ℍ`. -/
theorem lt_top_of_areaAll {γ : ℝ} {x : FieldSample} (h : AreaAll γ x) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) : qAreaMeasure γ x K < ⊤ := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  exact (measure_mono (show K ⊆ ball 0 R ∩ H from fun z hz => ⟨hR hz, hKH hz⟩)).trans_lt (h.1 R)

/-- **SWC-A6**: `E6.WedgeAreaMergeUnifStmt` from the D29 regularity core and the wedge-field
distortion bound. -/
theorem wedgeAreaMergeUnifStmt_of_flowErr (hC : WedgeUnzip.WedgeContinuumStmt)
    (hD : WedgeFlowErrStmt) : WedgeAreaMergeUnifStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hInd hB hIB
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hWS : WedgeWindowStmt := wedgeWindowStmt_of_splitR fun κ hκ hκ4 => by
    have h2 : Real.sqrt κ < 2 := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
    exact ⟨swC (Real.sqrt κ), swC' (Real.sqrt κ), tendsto_swC _, tendsto_swC' _,
      swWindowSplitStmtR_holds (Real.sqrt_pos.2 hκ) h2⟩
  obtain ⟨c, c', hc, hc', hWin⟩ := hWS κ hκ hκ4
  filter_upwards [hWin P X' A hX hA hInd, hC κ hκ hκ4 P X' A B'' hX hA hInd hB hIB,
    hD κ hκ hκ4 P X' A B'' hX hA hInd hB hIB,
    ae_areaAll_wedgeField hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hInd,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hWω hCω hDω hAω hcω h0
  intro f hf T ε hε
  obtain ⟨F, hF⟩ := hCω.1
  have hWc : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hcω.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  obtain ⟨K, hK⟩ := mergeUnif_of_flowErr hγ hc hc' hWω
    (fun K hK hKH => lt_top_of_areaAll hAω hK hKH) hF hWc hW0 T (hDω T) hf (half_pos hε)
  exact ⟨K, fun k hk t ht htT => (hK k hk t ht htT).trans (by linarith)⟩

end SWCore
end QuantumZipper
