import QuantumZipper.Proofs.Zipper.E6
import QuantumZipper.Proofs.Zipper.E6MeasShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E6 without Palm-side measurability (2): the abstract core

Theorem 1.3, node E6 (Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.4, proof of Thm 1.8, pp. 70–72; blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §E6).
Task E6-AEMEAS.

`e6_core_rel_nm` is `E6.e6_core_rel` (`LocRichCore.lean`) **without** the Palm-side
measurability hypotheses `hHm` (measurability of `{(ω,x) : x ∈ hit ω}`) and `hzcm` (joint
measurability of `(ω,x) ↦ loc R (zc C ω x)`). The argument is the same ε-argument, with one
change of bookkeeping: the locality error is merged into a single measurable function of the
`R'`-local data before it is compared on the Palm side,
* `Ψ := min(Γ ∘ F + 1_{Aᶜ}, 1)` (so `Γ(loc_R(zip y)) ≤ Ψ(loc_{R'} y)` on `Reg`), and
* `Φ₀ := 1_A · Γ ∘ F` (so `Φ₀(loc_{R'} y) ≤ Γ(loc_R(zip y))` on `Reg`),
so that the only additions of Palm integrals are with the measurable error `badB` (`ω ↦ ν ω`
is a kernel) and constants, and the splitting `∫(f + g) = ∫f + ∫g` happens only on the `P_*`
side, where the local data are measurable. The fixed-`ω` comparison is
`e6_omega_b_nm`/`e6_omega_a_nm` (`E6MeasShift.lean`), valid for arbitrary integrands.
Own elementary argument (the paper does not discuss measurability).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open PalmShift

variable {Ω : Type*} [MeasurableSpace Ω] {Ω' : Type*} [MeasurableSpace Ω']
  {L : Type*} [MeasurableSpace L]

/-- Integrating a per-`ω` comparison over `ω`, for arbitrary integrands. -/
lemma e6_int_bound_nm (P : Measure Ω) [IsProbabilityMeasure P] (ν : Kernel Ω ℝ)
    [IsSFiniteKernel ν] (δ : ℝ) (hit : Ω → Set ℝ) (ℓ : ℝ≥0) (c : ℝ≥0∞)
    (fX fY : Ω → ℝ → ℝ≥0∞)
    (hper : ∀ᵐ ω ∂P, ∫⁻ x in Icc (-δ) 0, (hit ω).indicator (fX ω) x ∂ν ω ≤
      ∫⁻ x in Icc (-δ) 0, (hit ω).indicator (fY ω) x ∂ν ω + c + badB (ν ω) δ ℓ) :
    ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, (hit ω).indicator (fX ω) x ∂ν ω ∂P ≤
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, (hit ω).indicator (fY ω) x ∂ν ω ∂P + c +
        (ℓ + tailD P ν δ ℓ) := by
  have hbad : (fun ω => badB (ν ω) δ ℓ) = fun ω => (ℓ : ℝ≥0∞) +
      {ω | ν ω (Icc (-δ - 1) (-δ)) ≤ ℓ}.indicator (fun ω => ν ω (Icc (-δ) 0)) ω := by
    funext ω; simp only [badB, indicator, mem_ofPred_eq]
  have hDm : Measurable fun ω =>
      {ω | ν ω (Icc (-δ - 1) (-δ)) ≤ ℓ}.indicator (fun ω => ν ω (Icc (-δ) 0)) ω :=
    (ν.measurable_coe measurableSet_Icc).indicator
      (measurableSet_le (ν.measurable_coe measurableSet_Icc) measurable_const)
  have hBm : Measurable fun ω => badB (ν ω) δ ℓ := by
    rw [hbad]; exact measurable_const.add hDm
  have hB : ∫⁻ ω, badB (ν ω) δ ℓ ∂P = ℓ + tailD P ν δ ℓ := by
    rw [hbad, lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    rfl
  calc ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, (hit ω).indicator (fX ω) x ∂ν ω ∂P
      ≤ ∫⁻ ω, (∫⁻ x in Icc (-δ) 0, (hit ω).indicator (fY ω) x ∂ν ω +
          (c + badB (ν ω) δ ℓ)) ∂P :=
        lintegral_mono_ae (hper.mono fun ω h => h.trans_eq (add_assoc _ _ _))
    _ = ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, (hit ω).indicator (fY ω) x ∂ν ω ∂P +
          ∫⁻ ω, (c + badB (ν ω) δ ℓ) ∂P :=
        lintegral_add_right _ (measurable_const.add hBm)
    _ = _ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, hB,
          add_assoc]

end QuantumZipper.E6
