import QuantumZipper.Proofs.Thm18.G4Read2Core
import QuantumZipper.Proofs.Thm18.G4ReadZip

/-!
# Theorem 1.8, node G4: `G4LenDrvReadStmt` from a Borel good set at the unzipping time

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). Task
G4-READ2.

`g4LenDrvReadStmt_of_nodes` proves the measurable length-welding driver reading
`G4LenDrvReadStmt` from
* `G4RoundUpStmt` (proved from the round-trip core nodes in the G4 headline): a.s. the rescaled
  time reversal `revDrv W t' a` of the SLE driver at the unzipping time `t'` is a good
  length-`ℓ` welding driver of the unzipped field;
* `G4UnzipGoodSetStmt` (new explicit hypothesis): the pair (path on `[0,1]`, time)
  `((W(t'(1−u)) − W t')/√t', t'/a²)` representing that driver lies a.s. in a *Borel* set of good
  pairs. This is the random-time version of `Cor15Group.exists_goodPathRSet` /
  `Thm14GoodDriverSet.exists_goodDriverSet`; there the Borel set comes from a fixed-time law
  (`toMeasurable` of the bad set), which does not apply at the random time `t'`;
* `G4WedgeCertStmt` (new explicit hypothesis): a.s. the wedge field has the countable boundary
  certificates `BCert`, `AtomQ`, `InfQ` (transferred to the unzipped field by E6, using the
  a.e.-measurability `E6.UnzipMeasStmt` of the unzipped data, already a G4 input).

The deterministic core is `exists_lenDrvReading_of_good` (`G4Read2Core.lean`, Lusin–Souslin:
Kechris, *Classical Descriptive Set Theory*, Thm 15.1). **Own assembly.**
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The rescaled time reversal of `W` at time `t'`, as a function on `[0,1]`. -/
def gStarVal (W : ℝ → ℝ) (t' u : ℝ) : ℝ := (W (t' * (1 - u)) - W t') / Real.sqrt t'

/-- **Boundary certificates of the wedge field** (explicit hypothesis): a.s. the field rebuilt
from the circle coordinates of the wedge field has a vague boundary limit (`BCert`), no atoms on
`(−∞,0]` (`AtomQ`) and infinite boundary mass on `[0,∞)` (`InfQ`). -/
def G4WedgeCertStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ᵐ ω ∂P, CertC γ (CoordsFull.coordsFull (Y ω))

/-- A length-welding driver only depends on the driver on `[0,T]`. -/
theorem isLenWeldingDriver_of_eqOn {γ ℓ : ℝ} {x : FieldSample} {T : ℝ} {V V' : ℝ → ℝ}
    (h : IsLenWeldingDriver γ x ℓ (T, V)) (hV' : Continuous V') (hV'0 : V' 0 = 0)
    (hEq : EqOn V V' (Icc 0 T)) : IsLenWeldingDriver γ x ℓ (T, V') := by
  have hr : revMap V T = revMap V' T := funext fun z => ReverseFlow.revMap_congr_drive z hEq
  have hh : revHull V T = revHull V' T := by unfold revHull; rw [hr]
  have hz : zeroMinus V T = zeroMinus V' T := by unfold zeroMinus revMapBdry; rw [hr]
  have hw : weldingHom V T = weldingHom V' T := by
    funext s
    unfold weldingHom revMapBdry
    rw [hr]
  obtain ⟨h1, -, -, h4, h5, h6⟩ := h
  have h4' : T = 0 ∨ IsSimpleCurveHull (revHull V T) := h4
  have h5' : zeroMinus V T = lenWeldPoint γ x ℓ := h5
  have h6' : ∀ s ∈ Icc (zeroMinus V T) 0, weldingHom V T s = weldHomR γ x s := h6
  rw [hh] at h4'
  rw [hz] at h5' h6'
  rw [hw] at h6'
  exact ⟨h1, hV', hV'0, h4', h5', h6'⟩

theorem sclDrv_eqOn_revDrv {W : ℝ → ℝ} {t' a : ℝ} (ht : 0 < t') (ha : 0 < a) {p : PathT}
    (hT : p.2 = t' / a ^ 2) (hg : ∀ u : Icc (0 : ℝ) 1, p.1 u = gStarVal W t' u) :
    EqOn (revDrv W t' a).2 (sclDrv p) (Icc 0 p.2) := by
  intro s hs
  have hT0 : 0 < p.2 := by rw [hT]; positivity
  have hu : s / p.2 ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hs.1 hT0.le, (div_le_one hT0).2 hs.2⟩
  have hsq : Real.sqrt p.2 = Real.sqrt t' / a := by
    rw [hT, Real.sqrt_div' _ (sq_nonneg a), Real.sqrt_sq ha.le]
  have harg : t' * (1 - s / p.2) = t' - a ^ 2 * s := by
    rw [hT]
    field_simp
  have hst : Real.sqrt t' ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  show (W (t' - a ^ 2 * s) - W t') / a = Real.sqrt p.2 * extIccPath zero_le_one p.1 (s / p.2)
  rw [extIccPath_of_mem _ _ hu, hg, gStarVal, hsq, harg]
  field_simp

end Thm18Asm
end QuantumZipper
