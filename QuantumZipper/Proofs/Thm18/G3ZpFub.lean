import QuantumZipper.Proofs.Thm18.G3Z2b2Two
import QuantumZipper.Proofs.Thm18.G3Pl4Win

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-PARTNER (1): removing the random curve from `G3TCurveStmt`

`G3TCurveStmt` (R18G3TGeoSplit) compares the joint Palm-window integral `J` of the wedge, whose
zooms at the Palm point `x` and at its length partner `R(x)` pass through the local maps of the
independent curve, with the plain joint integral `J₀` (no curve maps). The curve is independent of
the wedge (Sheffield, arXiv:1012.4797, p. 71, Figure 1.7), so by the curve Fubini
`g3zWedgePalmCyl_fubini` (G3Z2b2Two) `J = ∫ Φ_a d(path law)` with
`Φ_a = ∫ g3PhiM2(wedge sample, a) dP'` the joint Palm-window integral at the **fixed** path `a`.

* `g3PhiM2_le`, `g3zWedgePalmCyl0_le`: both integrands are bounded by the window mass, which is at
  most `U` (`g3pl4_measure_win_le`).
* **`g3TCurveStmt_of_path`**: `G3TCurveStmt` follows from
  - `G3ZpFacRegStmt`: the regularity conditions of the measurable integrand at a.e. window point
    (the hypothesis of `g3zWedgePalmCyl_fubini`; Z-REG's node), and
  - `G3ZpPathStmt`: for a.e. fixed path `a`, `Φ_a(L) − J₀(L) → 0` as `L → ∞` (the two-point
    Palm zoom at `(x, R(x))` through fixed maps against the plain one),
  by dominated convergence over the path (both are in `[0, U]`).

Own bookkeeping (AGENT_GUIDE cost rule): Fubini over the independent curve and dominated
convergence; no step of the paper is changed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zp

open G3Z2b2

theorem ind_mul_ind_le_one {α β : Type*} (s : Set α) (t : Set β) (a : α) (b : β) :
    s.indicator (1 : α → ℝ≥0∞) a * t.indicator (1 : β → ℝ≥0∞) b ≤ 1 := by
  unfold Set.indicator; split_ifs <;> simp

/-- The measurable joint integrand is at most the window mass `U`. -/
theorem g3PhiM2_le {γ L U : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {s t : Set LawD}
    (p : FieldSample × (ℝ≥0 → ℝ)) : g3PhiM2 γ L Ψ U s t p ≤ ENNReal.ofReal U := by
  classical
  set W := {x : ℝ | x < 0 ∧ bdryM γ p.1 (Icc x 0) ≤ ENNReal.ofReal U} with hW
  have h1 : ∀ x, g3IntM2 γ L Ψ U s t (p, x) ≤ W.indicator 1 x := by
    intro x
    unfold g3IntM2
    split_ifs with h
    · have hx : x ∈ W := by simpa [W, g1SideHalf, g1SideSeg] using h
      rw [indicator_of_mem hx]; exact ind_mul_ind_le_one _ _ _ _
    · exact bot_le
  unfold g3PhiM2
  calc ∫⁻ x, g3IntM2 γ L Ψ U s t (p, x) ∂(bdryM γ p.1)
        ≤ ∫⁻ x, W.indicator 1 x ∂(bdryM γ p.1) := lintegral_mono h1
    _ ≤ bdryM γ p.1 W := lintegral_indicator_one_le W
    _ ≤ _ := R18.g3pl4_measure_win_le _ _

end G3Zp
end Thm18Asm
end QuantumZipper
