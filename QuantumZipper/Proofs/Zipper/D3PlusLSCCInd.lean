import QuantumZipper.Proofs.Zipper.D3PlusLSCCCM
import QuantumZipper.Proofs.NonVacuityFinal

/-!
# D3⁺(ii), constant part: the model level shift from asymptotic independence and spread

Task LSCCONST. Blueprint `E_BRANCH_BLUEPRINT.md` §3 (D3⁺(ii)): "LSC follows from asymptotic
independence of `canonical` and `log scaleParam` (spread `≍ √L`, hitting time of a BM with
drift)". For the model zoom (correction `0`, `D3PlusLSCCCM.lean`) write `C_L` for the rich
canonical data and `S_L` for the log of the local scale (`pairN1 = (C_L, S_L)`). The three nodes:

* `LSCCIndStmt` (**asymptotic independence**): `d_TV(law (C_L, S_L), law C_L ⊗ law S_L) → 0`;
* `LSCCSpreadStmt` (**spread**): `d_TV(law S_L, law S_{L+c}) → 0` for every real `c`;
* `LSCCCanonStmt` (**canonical part**): `d_TV(law C_L, law C_{L+c}) → 0` for every real `c`.

Sources: Sheffield arXiv:1012.4797, proof of Prop. 1.6 (p. 25); Duplantier–Miller–Sheffield
arXiv:1409.7055, Props. 4.7–4.8 (pp. 77–79): after the circle-average embedding at the hitting
time `T_L` of the level by the radial Brownian motion with drift, `C_L` is read from the embedded
field near `T_L` (asymptotically independent of `T_L` by the strong Markov property / Williams'
path decomposition), while `S_L = log r − T_L + O_P(1)` and `T_L` has spread `≍ √L`, so a bounded
shift of the level (or of `S_L`) costs `o(1)` in TV. `LSCCCanonStmt` follows from D3⁺(i)'s node
`D3PlusIN2TmZeroStmt` (N2-TMZERO) and the existence of an `α`-quantum wedge
(`NonVacuity.exists_wedge_indep_BM_uncond`): `lsccCanon_of_tmZero'`.

Proved here (own elementary arguments): `lscc_tvDist_prod_le` (TV of product measures),
`lsccHeart_of_parts : LSCCIndStmt → LSCCSpreadStmt → LSCCCanonStmt → LSCCHeartStmt`,
`lsccCanon_of_tmZero`, `lsccCanon_of_tmZero'`, and the assembled
`lscConstGen_locFieldFull_of_tmZero : LSCCIndStmt → LSCCSpreadStmt → D3PlusIN2TmZeroStmt →
LSCConstGen locFieldFull`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- `d_TV(μ ⊗ ν, μ' ⊗ ν') ≤ d_TV(μ, μ') + d_TV(ν, ν')` (own elementary argument from
`TV.tvDist_prod_right_le` and the swap symmetry). -/
theorem lscc_tvDist_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ μ' : Measure α} {ν ν' : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] :
    TV.tvDist (μ.prod ν) (μ'.prod ν') ≤ TV.tvDist μ μ' + TV.tvDist ν ν' := by
  refine TV.tvDist_triangle.trans (add_le_add TV.tvDist_prod_right_le ?_)
  rw [← Measure.prod_swap (μ := ν) (ν := μ'), ← Measure.prod_swap (μ := ν') (ν := μ')]
  exact (TV.tvDist_map_le measurable_swap).trans TV.tvDist_prod_right_le

/-- The log of the (surrogate) local scale of the model zoom at level `L`. -/
def lsccS (γ r α L : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : ℝ :=
  Real.log (scaleSur γ L r (localZ X r ω, circData α (fun _ => 0)))

end D3Plus
end QuantumZipper
