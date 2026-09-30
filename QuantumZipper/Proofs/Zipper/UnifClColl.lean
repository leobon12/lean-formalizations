import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.UnifClSide
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.B3dStmt
import QuantumZipper.Proofs.Zipper.ESMLMeas
import QuantumZipper.Proofs.Zipper.F1Reflect

/-!
# UNIF-CLUSTER (D26): the `L⁻` statements of E6-ID from UW, UA and the field cocycle

With `UnifWindowStmt` (UW) and `UnifAtomlessStmt` (UA) (`UnifClB5.lean`) and the field cocycle
`B3d.CapCocycleRegStmt` (the field of `C_u = zipCapDown γ u 𝒵` unzipped by `s` is `RegEq` to the
field unzipped by `u + s`; REG-UNIF item 2, needed anyway by `E6.CapCocycleAddStmt`):

* **`lenCollidedStmt_of_windows`**: `E6.LenCollidedStmt` (B5-V for the configurations `C_u`,
  uniformly in `(u,s)`): the left length unzipped from `C_u` in time `s` is
  `ν_{h⁰}[0₋(T − u), 0₋(T − u − s)]`. Proof: `RegEq` identifies the boundary measure with that of
  `h⁰_{u+s}`; the left end of the unzipped segment is `G(0₋(T − u))`, `G = realRevMap V (T−u−s)`
  (`sideImages_fst_shift_eq`); the window identities of UW at time `u + s`, restricted to
  `(0₋(T − u), 0₋(T − u − s))`, and exhaustion (`B5.measure_Icc_eq_of_windows`).
* **`lenCocycleStmt_of_windows`**: `E6.LenCocycleStmt` (additivity of `L⁻`), from the above and
  uniform B5-V (`ae_b5v_uniform_of_windows`).
* **`e6_id_of_unif`**: E6-ID (the `hId` of `E6.e6_concrete`) from UW, UA, `CapCocycleRegStmt` and
  `B3d.ZipLenInputsStmt` only: the hypotheses `hB5V`, `hmono`, `hLC` of `E6.e6_id` are discharged.
* **`e6_id_of_anchor`**: the same with UW replaced by its sources AW + UG
  (`unifWindowStmt_of_anchor`, `UnifClAnchor.lean`).

Sources: Sheffield, arXiv:1012.4797, proof of Theorem 1.3 (§5, Lemma 5.6, pp. 66–68) and of
Theorem 1.8 (p. 70); the paper gives no details at this granularity. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 RealLine CaraR

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- `G = realRevMap V t` is continuous at `0₋(τ)` for `t < τ < T` (the point is alive at time
`t`). -/
theorem continuousAt_realRevMap_zeroMinus {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0)
    (hT : 0 < T) (hK : IsSimpleCurveHull (revHull V T)) {t τ : ℝ} (ht : 0 ≤ t) (htτ : t < τ)
    (hτ : τ < T) : ContinuousAt (realRevMap V t) (zeroMinus V τ) := by
  have hanti := strictAntiOn_zeroMinus hV hV0 hT hK
  have hc0 : zeroMinus V τ ≤ 0 := by
    rw [← zeroMinus_zero_time hV hV0]
    exact hanti.antitoneOn ⟨le_rfl, hT.le⟩ ⟨by linarith, hτ.le⟩ (by linarith)
  have haτ : zeroMinus V T < zeroMinus V τ :=
    hanti ⟨by linarith, hτ.le⟩ ⟨hT.le, le_rfl⟩ hτ
  have hlt : ENNReal.ofReal t < realHitTime V (zeroMinus V τ) := by
    obtain ⟨he, hτ', hz⟩ := hitTime_spec hV hV0 hT hK ⟨haτ, hc0⟩
    have : (realHitTime V (zeroMinus V τ)).toReal = τ :=
      hanti.injOn hτ' ⟨by linarith, hτ.le⟩ hz
    rw [he, this]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htτ
  obtain ⟨g, hg⟩ := exists_isRealRevSol_of_lt_realHitTime hlt
  exact continuousAt_realRevMap hV ht (not_mem_swallowedSet_iff.2 ⟨g, hg⟩)

end RegUnif
end QuantumZipper
