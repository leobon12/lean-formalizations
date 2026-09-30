import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Loewner.WeldingConsistency
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.CoreArc3e
import QuantumZipper.Proofs.Zipper.WeldingUniqueness
import QuantumZipper.Proofs.Zipper.B5ZeroMinus

/-!
# Theorem 1.8, node G4: uniqueness of length-welding drivers (G4-WELD, first half)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1)
("`Z^LEN_t` for `t > 0` is a.s. uniquely defined via conformal welding") and the proof of
Theorem 1.4 (§1.4): a conformal welding of a simple arc with conformally removable doubled hull
determines the reverse Loewner map, hence the capacity time and the driver.

Proved here (deterministic):

* `isLenWeldingDriver_eq_of_good`: if `p` is a length-welding driver of `x` for length `ℓ`
  with `p.1 > 0` whose doubled hull `closure K ∪ conj (closure K)`, `K = revHull p.2 p.1`, is
  conformally removable, then every length-welding driver `q` of `x` for `ℓ` has `q.1 = p.1`
  and `q.2 = p.2` on `[0, p.1]`. Route: `revMap_eq_of_welding_eq` (the welding identifies the
  reverse maps, two possibly different capacity times allowed; this is Sheffield's proof of
  Theorem 1.4, formalized in `Proofs/Zipper/WeldingUniqueness.lean`),
  `drive_and_time_eq_of_revMap_eq` (equal reverse maps have equal capacity times: `hcap`), and
  `WeldingConsistency.eqOn_of_revMap_eq_general` (equal reverse maps give equal drivers).
  Removability is needed only for the hull of `p`, not of `q`.
* `isLenWeldingDriver_unique_of_good`: the uniqueness conjunct of `G4WeldStmt` follows.

Reduction:

* `g4WeldStmt_of_good`: `G4WeldStmt` from `G4WeldGoodStmt` (a.s. existence of one length-welding
  driver with positive time and removable doubled hull).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

/-- **Uniqueness against a good length-welding driver** (deterministic). -/
theorem isLenWeldingDriver_eq_of_good {γ ℓ : ℝ} {x : FieldSample} {p q : ℝ × (ℝ → ℝ)}
    (hp : IsLenWeldingDriver γ x ℓ p) (hp0 : 0 < p.1)
    (hrem : IsConformallyRemovable
      (closure (revHull p.2 p.1) ∪ conj '' closure (revHull p.2 p.1)))
    (hq : IsLenWeldingDriver γ x ℓ q) :
    q.1 = p.1 ∧ EqOn p.2 q.2 (Icc 0 p.1) := by
  have hCar := CaraR.revMapCaratheodory
  have hArc := CoreArc.loewnerSubhullsOfArc
  obtain ⟨-, hpc, hp00, hpK', hpz, hpw⟩ := hp
  obtain ⟨hq1, hqc, hq00, hqK', hqz, hqw⟩ := hq
  have hpK : IsSimpleCurveHull (revHull p.2 p.1) := hpK'.resolve_left hp0.ne'
  obtain ⟨F, hF⟩ := hCar p.2 hpc hp00 p.1 hp0 hpK
  have hneg : zeroMinus p.2 p.1 < 0 :=
    (WeldingConsistency.car_basic hpc hp0 hF (WeldingConsistency.simpleCurveHull_nonempty hpK)).1
  have hzm : zeroMinus p.2 p.1 = zeroMinus q.2 q.1 := hpz.trans hqz.symm
  have hq0 : 0 < q.1 := by
    rcases hq1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, B5.zeroMinus_zero_time hqc hq00] at hzm
      linarith
  have hqK : IsSimpleCurveHull (revHull q.2 q.1) := hqK'.resolve_left hq0.ne'
  have hweld : EqOn (weldingHom p.2 p.1) (weldingHom q.2 q.1) (Icc (zeroMinus p.2 p.1) 0) := by
    intro s hs
    rw [hpw s hs, hqw s (hzm ▸ hs)]
  have hrev := revMap_eq_of_welding_eq hCar hpc hqc hp00 hq00 hp0 hq0 hpK hqK hzm hweld hrem
  obtain ⟨-, hT⟩ := WeldingUniqueness.drive_and_time_eq_of_revMap_eq hpc hqc hp0.le hq0.le hrev
  refine ⟨hT.symm, ?_⟩
  rw [← hT] at hrev
  exact WeldingConsistency.eqOn_of_revMap_eq_general hCar hArc hpc hqc hp00 hq00 hp0 hpK hrev

/-- **Uniqueness of length-welding drivers**, given one good driver. -/
theorem isLenWeldingDriver_unique_of_good {γ ℓ : ℝ} {x : FieldSample} {p₀ : ℝ × (ℝ → ℝ)}
    (hp₀ : IsLenWeldingDriver γ x ℓ p₀) (hp₀0 : 0 < p₀.1)
    (hrem : IsConformallyRemovable
      (closure (revHull p₀.2 p₀.1) ∪ conj '' closure (revHull p₀.2 p₀.1)))
    (p q : ℝ × (ℝ → ℝ)) (hp : IsLenWeldingDriver γ x ℓ p) (hq : IsLenWeldingDriver γ x ℓ q) :
    p.1 = q.1 ∧ ∀ s ∈ Icc 0 p.1, p.2 s = q.2 s := by
  obtain ⟨h1, h2⟩ := isLenWeldingDriver_eq_of_good hp₀ hp₀0 hrem hp
  obtain ⟨h1', h2'⟩ := isLenWeldingDriver_eq_of_good hp₀ hp₀0 hrem hq
  refine ⟨h1.trans h1'.symm, fun s hs => ?_⟩
  rw [h1] at hs
  exact (h2 hs).symm.trans (h2' hs)

end Thm18Asm
end QuantumZipper
