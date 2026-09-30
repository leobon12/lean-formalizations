import QuantumZipper.Proofs.Thm18.ASepConj1C
import QuantumZipper.Proofs.Zipper.Cor15RezipRegDist

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP conjunct 1 (d): continuous-radius limit on a box, and conjunct 1 at every good parameter

* `ae_tendsto_Phi_box`: on a rational box inside the box data of `boxData_A0`, almost surely,
  for every `p`, `∫ evalReg x_p (fc(v, ρ)) dν_p(v)` converges as `ρ → 0⁺` over **all** radii
  (GENERIC-UC engine `GenUC.ae_unifConv_all_radii`, radii `ℚ ∩ (0, 1]`; identity
  `ae_ident_fwdMapInv_rho`, deterministic part `det_unif_A0_rho`, joint continuity
  `ae_continuousOn_Phi_rho`);
* `ae_conj1_free_all`: conjunct 1 of A-sep at `τ' = 0` for the free field at every good
  parameter, from `conj1_of_limit`.

Own elementary bookkeeping (mirrors `ae_exact_free_box` / `ae_exact_free_open`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg RegUnif UnzipInvariance RegSample GenUC
open Thm18Asm Thm18Asm.G4Core

/-- Probability and compact support of the centre measures on the box. -/
theorem nuA0_facts {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {d : ℂ} {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) {S : Set (Fin 2 → ℝ)}
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁) {δ : ℝ}
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u) :
    ∃ R₁ : ℝ, 0 ≤ R₁ ∧ ∀ p ∈ S, IsProbabilityMeasure (nuA0 W d r p) ∧
      nuA0 W d r p (CircleFubini.ballH R₁)ᶜ = 0 ∧ ∀ᵐ v ∂nuA0 W d r p, v ∈ H := by
  obtain ⟨m, c, Rb, g, hm, hc, -, hg⟩ := exists_geo_A0 hW hW0 hT ha₀ (hgood0_of_hgood hgood)
  refine ⟨max Rb 0, le_max_right _ _, fun p hp => ?_⟩
  have hgp := hg p (hSb p hp).1 (hSb p hp).2
  have hsrc : ∀ᵐ w ∂foldedCircle d r, w ∈ foldSph d r ∧ w ∈ H ∧ ‖w‖ ≤ ‖d‖ + r := by
    filter_upwards [ae_mem_foldSph d hr.le, foldedCircle_ae_mem_H d hr,
      foldedCircle_ae_norm_le d hr.le] with w h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hmap : (foldedCircle d r).map (g p) = nuA0 W d r p :=
    Measure.map_congr (hsrc.mono fun w hw => hgp.2.2 w hw.1)
  have hmB : MeasurableSet (CircleFubini.ballH (max Rb 0)) :=
    (CircleFubini.isCompact_ballH _).isClosed.measurableSet
  rw [← hmap]
  refine ⟨(Measure.isProbabilityMeasure_map_iff hgp.1.aemeasurable).2 inferInstance, ?_,
    (ae_map_iff hgp.1.aemeasurable isOpen_H.measurableSet).2
      (hsrc.mono fun w hw => (hgp.2.1 w hw.2.1 hw.2.2).1)⟩
  refine ae_iff.1 ((ae_map_iff hgp.1.aemeasurable hmB).2 (hsrc.mono fun w hw => ?_))
  obtain ⟨h1, -, h3⟩ := hgp.2.1 w hw.2.1 hw.2.2
  exact ⟨by rw [mem_closedBall, dist_zero_right]; exact h3.trans (le_max_left _ _),
    le_of_lt (show 0 < (g p w).im from h1)⟩

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end ASep
end QuantumZipper
