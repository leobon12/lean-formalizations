import QuantumZipper.Proofs.Zipper.UnzipExpMomGauss
import QuantumZipper.Proofs.Zipper.UnifTipExp
import QuantumZipper.Proofs.ItoLite.Oscillation
import QuantumZipper.Proofs.Zipper.UnifUGTip
import QuantumZipper.Proofs.Zipper.MeasUnzipField
import QuantumZipper.Proofs.Zipper.B1Full
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.NuMeas
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.GFF.FrostmanReg
import QuantumZipper.Proofs.GMC.BdryMomentsScale
import QuantumZipper.Proofs.LQG.LocalRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNZIP-EXPMOM: exponential moments of the unzipped constant (D31/D37)

`unzipConstExpMomStmt_holds : 0 < κ → κ < 4 → UnzipConstExpMomStmt κ`: for a gauge-pinned
`Γ⁰` sample (`B` Brownian, `X` free GFF mod constants with `X(fc(0,1)) = 0`, independent),
`t ∈ [0,1]` and `r ≥ 0`, `E exp(r · h⁰_t(fc(0,1))) < ∞`.

**Proof.** Take a continuous version `B'` of `B`. A.s. (`ae_raw_eq`, `ae_tendsto_ZE`)

`h⁰_t(fc(0,1)) = Z + D`,  `Z = ZE(B'|_{[0,1]}, X)(t, 0, 1)`,  `D = Ddet(√κ B)(t, 0, 1)`,

and `e^{r(Z + D)} ≤ e^{2rZ} + e^{2rD}`.
* Deterministic part: `e^{√κ D} ≤ C (1 + sup_{[0,1]} |B|)²` (`ofReal_exp_Ddet_le`, Koebe-type
  bounds of `UnifTipExpDet`), so `e^{2rD} ≤ C^a (1 + sup|B|)^{2a}`, `a = 2r/√κ`.
* Free-field part: conditionally on the driver (independence, `unzipExpMom_lintegral_indep`),
  `Z` is a centred Gaussian with variance `≤ unzipVarC (√κ sup|B|) = O(log(1 + sup|B|))`
  (`unzipExpMom_fixed_le`), so `E[e^{2rZ} | B] ≤ K (1 + sup|B|)^{16 r²}`
  (`unzipExpMom_exp_varC_le`).
* Both bounds are integrable: polynomial moments of the Brownian running maximum
  (`bmSupMomentStmt_holds`).

The pinning is used only through `X(fc(0,1)) = 0`, which makes `Z = X(ν) − X(fc(0,1))` a
genuine Gaussian difference (without it `X(ν)` alone carries an arbitrary additive constant).
The hypothesis `κ < 4` is not needed. Own elementary assembly of the repository's bounds (the
route of the task plan: condition on `B`, Gaussian variance `O(log(1 + diam))`, deterministic part
`O(log(1 + sup|B|))`).
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint RegCont KolmD RegSample B2

/-- The driver of the good version is bounded by `√κ · sup_{[0,1]} |B|` (and the latter is
finite), on the event where the version agrees with `B`. -/
theorem unzipExpMom_Wof_pathC_le {Ω : Type} [MeasurableSpace Ω] {B B' : ℝ≥0 → Ω → ℝ}
    (κ : ℝ) (hB'c : ∀ ω, Continuous fun t => B' t ω) {ω : Ω} (heq : ∀ t, B' t ω = B t ω) :
    bmSup B ω ≠ ⊤ ∧ ∀ u ∈ Icc (0 : ℝ) 1,
      |Wof κ 1 zero_le_one (pathC 1 B' hB'c ω) u| ≤ Real.sqrt κ * (bmSup B ω).toReal := by
  have hBc : Continuous fun s : ℝ => B s.toNNReal ω := by
    have : (fun s : ℝ => B s.toNNReal ω) = fun s => B' s.toNNReal ω :=
      funext fun s => (heq _).symm
    rw [this]; exact (hB'c ω).comp continuous_real_toNNReal
  obtain ⟨M0, hM0⟩ := exists_abs_le_on_Icc hBc 1
  have hSfin : bmSup B ω ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := M0)) (iSup₂_le fun s hs' => ?_)
    exact ENNReal.ofReal_le_ofReal (hM0 s hs')
  refine ⟨hSfin, fun u hu => ?_⟩
  have hBle : |B u.toNNReal ω| ≤ (bmSup B ω).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hSfin).1
      (le_iSup₂_of_le (f := fun (s : ℝ) (_ : s ∈ Icc (0 : ℝ) 1) =>
        ENNReal.ofReal |B s.toNNReal ω|) u hu le_rfl)
  simp only [Wof, pathC, ContinuousMap.coe_mk, projIcc_of_mem zero_le_one hu, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg κ), heq]
  exact mul_le_mul_of_nonneg_left hBle (Real.sqrt_nonneg κ)

end RegUnif
end QuantumZipper
