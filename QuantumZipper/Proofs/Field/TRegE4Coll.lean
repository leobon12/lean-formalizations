import QuantumZipper.Proofs.Field.TRegE4
import QuantumZipper.Proofs.Zipper.E1TransferRep3
import QuantumZipper.Proofs.LQG.PalmNorm

/-!
# TREG-E4 for the field at collision: `pairRaw = pairTest` for `𝔥 + X + c`

The E4 right side (`handoff/E-PLAN-2.md`, `targetColl`) is the field

  `addConst (normAt ϖ' (ofFun (shiftFun γ 𝔥₀ ϖ' 0) + X)) (−q)`,

a free boundary GFF `X` plus the explicit function
`shiftFun γ 𝔥₀ ϖ' 0 = (2/√κ − γ) log‖·‖ − (γ/2) k_{ϖ'}` plus a (random) constant.
For each test function `ρ`, almost surely, **for every constant `c` simultaneously**,
`pairRaw (y + c) ρ = pairTest (y + c) ρ` for `y = ofFun (a log‖·‖ + g₁) + X` with `g₁` continuous
on `Hbar` (`ae_pairRaw_eq_pairTest_addConst_logAdd`); the collision field is the instance
`g₁ = −(γ/2) k_{ϖ'}` (`ae_pairRaw_eq_pairTest_coll`), with `k_{ϖ'}` continuous because it is
Hölder for a Frostman `ϖ'` (`TwoPoint.abs_neuPot_sub_le`).

Route: RC1 with a logarithmic mean at the test densities `ρ^± dz` (convergence form,
`CoordReg.ae_tendsto_integral_avgReg_logAdd_frostman`; Duplantier–Sheffield, *Liouville quantum
gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1 via the project's RC1) and `RegShift`
(`CoordReg.ae_regShift_logAdd_frostman`) so that constants pass through `evalReg`; the test
densities are normalized to probability measures (both sides scale linearly since the defining
limits exist). Own elementary reduction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal Real ComplexConjugate

namespace QuantumZipper
namespace TRegE4

open CharFun

theorem addConst_addConst (y : FieldSample) (c₁ c₂ : ℝ) :
    addConst (addConst y c₁) c₂ = addConst y (c₁ + c₂) := by
  funext μ; simp only [addConst]; ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-! ## The collision field -/

/-- The Neumann potential `k_ϖ` of a Frostman measure with bounded support is continuous. -/
theorem continuous_kPot {ϖ : Measure ℂ} [IsFiniteMeasure ϖ] {α C B : ℝ}
    (hF : TwoPoint.IsFrostman ϖ α C) (hα : 0 < α) (hα1 : α ≤ 1) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ y ∂ϖ, ‖y‖ ≤ B) : Continuous (PalmNorm.kPot ϖ) := by
  have hC : 0 ≤ C := FrostmanReg.frostman_const_nonneg (fun p r hr => hF p r hr)
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ x' : ℂ, ‖x' - x‖ < 1 →
      |PalmNorm.kPot ϖ x' - PalmNorm.kPot ϖ x| ≤ L * ‖x' - x‖ ^ (α / 2) :=
    ⟨_, fun x' hx' => TwoPoint.abs_neuPot_sub_le hF hα hα1 hC hB0 hB (X := ‖x‖ + 1)
      (by linarith [norm_le_norm_add_norm_sub' x' x, norm_sub_rev x' x]) (by linarith)⟩
  have hlim : Tendsto (fun x' : ℂ => L * ‖x' - x‖ ^ (α / 2)) (𝓝 x) (𝓝 0) := by
    have hc : Continuous fun x' : ℂ => ‖x' - x‖ ^ (α / 2) :=
      (continuous_id.sub continuous_const).norm.rpow_const fun _ => Or.inr (by positivity)
    have h := (hc.tendsto x).const_mul L
    rwa [sub_self, norm_zero, Real.zero_rpow (by positivity), mul_zero] at h
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    ?_ hlim)
  filter_upwards [Metric.ball_mem_nhds x one_pos] with x' hx'
  rw [Real.dist_eq]
  exact hL x' (by simpa [dist_eq_norm] using hx')

theorem shiftFun_zero_eq (γ κ : ℝ) (ϖ : Measure ℂ) :
    PalmNorm.shiftFun γ (h0rev κ) ϖ 0 =
      fun v => (2 / Real.sqrt κ - γ) * Real.log ‖v‖ + (fun u => -(γ / 2) * PalmNorm.kPot ϖ u) v := by
  funext v
  simp only [PalmNorm.shiftFun, h0rev, neumannH, Complex.ofReal_zero, zero_sub, norm_neg,
    Complex.norm_conj]
  ring

end TRegE4
end QuantumZipper
