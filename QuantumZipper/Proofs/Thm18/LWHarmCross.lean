import QuantumZipper.Proofs.Thm18.LWHarmCar
import QuantumZipper.Proofs.Thm18.LWExcUpper
import QuantumZipper.Proofs.Thm18.LWHarmCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route (D60): the conformal map onto `bddPart` of a crosscut

Task LW-HARM (B). Lawler–Werness, Ann. Probab. 41 (2013), Lemma 4.5, p. 24, compute
`ℰ_ℍ(η, ξ)` through a conformal map `ψ : ℍ → D₁` onto the bounded component of `ℍ \ ξ`
carrying an interval `(p, q)` onto `ξ` (`LW45Stmt`). Given the Jordan-domain data for
`D₁` (`LWCrosscutJordanStmt`: `D₁ = ψ₀(ℍ)` with frontier the Jordan curve `E = ξ ∪ [a, b]`;
`E` is ULC and `E \ {q}` is connected by `LWHarmCurve.lean`), we construct such a `ψ`
(`lwHarm_crosscut_map`):
by Carathéodory's theorem in the Jordan case (Pommerenke, *Boundary Behaviour of Conformal Maps*,
Thm 2.6, p. 24; repo `CA.Car.isClosedEmbedding_bdryMap`) the extension is a homeomorphism of
`ℝ ∪ {∞}` onto `E`; after the automorphism `w ↦ t₁ − 1/w` sending the preimage of the midpoint
`c = (a + b)/2` of the segment to `∞`, the preimage of the arc is a connected, open, bounded
subset of `ℝ`, i.e. an interval `(p, q)`.

`LWCrosscutJordanStmt` is the one ingredient not proved here: it is the Jordan curve theorem for
`ξ ∪ [a, b]` (the bounded part of `ℍ \ ξ` is the interior of this curve, and is simply connected)
plus the Riemann mapping theorem (repo: `RMT.riemann_mapping_of_hasHoloSqrt`,
`RMT.hasHoloSqrt_of_isSimplyConnected`); the repository has Janiszewski's theorem but not the
Jordan curve theorem.
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

open QuantumZipper.CA

/-- Normalization at `∞`: any frontier point `c` can be made the limit at `∞`. -/
theorem lwHarm_car_normalize {ψ : ℂ → ℂ} {D E : Set ℂ} {R₀ : ℝ} (h : Car.CarHyp ψ D E R₀)
    (hE : Topo.ULC E) {c : ℂ} (hc : c ∈ frontier D) :
    ∃ ψ₁ F₁ : ℂ → ℂ, Car.CarHyp ψ₁ D E R₀ ∧ EqOn F₁ ψ₁ H ∧ ContinuousOn F₁ Hbar ∧
      Tendsto ψ₁ (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 c) := by
  have := Car.neBot_cobounded_inf_H
  obtain ⟨F, hEq, hF, -, wInf, -, hInf⟩ := Car.continuousOn_extension h hE
  rw [Car.frontier_eq_insert_range h hEq hF hInf] at hc
  rcases hc with rfl | ⟨t₁, rfl⟩
  · exact ⟨ψ, F, h, hEq, hF, hInf⟩
  have h1 : Car.CarHyp (ψ ∘ lwHarmMob t₁) D E R₀ :=
    ⟨h.holo.comp (lwHarmMob_diffOn t₁) (lwHarmMob_mapsTo t₁),
      h.bij.comp (lwHarmMob_bijOn t₁), h.isOpen, h.bdd, h.isClosed, h.frontier_sub,
      h.sub_compl, h.E_bdd⟩
  obtain ⟨F₁, hEq₁, hF₁, -, -, -, -⟩ := Car.continuousOn_extension h1 hE
  refine ⟨_, F₁, h1, hEq₁, hF₁, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hcw⟩ := Metric.continuousWithinAt_iff.1
    (hF (t₁ : ℂ) (lwHarm_real_mem_Hbar t₁)) ε hε
  rw [eventually_inf_principal]
  filter_upwards [Bornology.isBounded_def.1
    (isBounded_closedBall (x := (0 : ℂ)) (r := δ⁻¹))] with w hw hwH
  have hwn : δ⁻¹ < ‖w‖ := by simpa [mem_closedBall, dist_zero_right] using hw
  have hMH := lwHarmMob_mapsTo t₁ hwH
  simp only [Function.comp_apply]
  rw [← hEq hMH]
  refine hcw (H_subset_Hbar hMH) ?_
  rw [dist_eq_norm]
  simp only [lwHarmMob, sub_sub_cancel_left, norm_neg, norm_inv]
  calc ‖w‖⁻¹ < (δ⁻¹)⁻¹ := inv_strictAnti₀ (inv_pos.2 hδ) hwn
    _ = δ := inv_inv δ

end LWFar
end Thm18Asm
end QuantumZipper
