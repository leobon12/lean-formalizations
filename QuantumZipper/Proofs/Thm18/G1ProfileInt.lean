import QuantumZipper.Proofs.Thm18.G1ProfileGap
import QuantumZipper.Proofs.Zipper.WedgeRC3All2
import QuantumZipper.Proofs.Zipper.WedgeShiftInt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PROFILE: the integrability part (`G1ProfileIntStmt`)

For a continuous path whose trace is a simple chord, the pushed circle `ν = ψ_* fc(d, r)`
(`ψ = Ψ left a`, the inverse of a normalized uniformizer `φ` of the side component `D`) is carried
by a compact subset of `Hbar`: `fc(d, r)` lives on `ℍ ∩ closedBall 0 (‖d‖ + r)` a.e., and `ψ` maps
bounded subsets of `ℍ` to bounded sets because `‖φ z‖ → ∞` as `z → ∞` in `D` (the normalization
`IsNormalizedUniformizer`, `bdd_invFunOn_of_normalized`). Both integrands are continuous on
`Hbar`: the free part by regularity of the sample (`WedgeGood`), the profile part by the
continuity of circle averages of the log-type wedge profile (`F1.RC3Two.continuous_smoothFun_rp`
with the a.s. bound `F1.RC3Two.bd_wg`). Hence both are integrable. Own elementary argument.

Also: `g1ProfileStmt_of_conv_cont : G1ProfileConvStmt → G1ProfileContStmt → G1ProfileStmt`
(the gap part is `g1ProfileGapStmt`, the integrability part `g1ProfileIntStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK CircleFubini

/-- The inverse of a normalized uniformizer maps bounded subsets of `ℍ` to bounded sets. -/
theorem bdd_invFunOn_of_normalized {D : Set ℂ} {φ : ℂ → ℂ} (hφ : IsNormalizedUniformizer D φ)
    (R : ℝ) : ∃ M : ℝ, ∀ w ∈ H, ‖w‖ ≤ R → ‖invFunOn φ D w‖ ≤ M := by
  have hev : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 D, R < ‖φ z‖ :=
    hφ.2.2.2.eventually (eventually_gt_atTop R)
  rw [eventually_inf_principal] at hev
  have hb : Bornology.IsBounded {z : ℂ | z ∈ D → R < ‖φ z‖}ᶜ :=
    Bornology.isBounded_compl_iff.2 hev
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  refine ⟨M, fun w hw hwR => hM _ ?_⟩
  have hex : ∃ z ∈ D, φ z = w := hφ.1.surjOn hw
  simp only [mem_compl_iff, Set.mem_ofPred_eq, not_imp, not_lt]
  exact ⟨invFunOn_mem hex, by rw [invFunOn_eq hex]; exact hwR⟩

/-- Continuous functions on `Hbar` are integrable against a finite measure carried by a bounded
part of `Hbar`. -/
theorem integrable_of_continuousOn_of_ae_ballH {ν : Measure ℂ} [IsFiniteMeasure ν] {g : ℂ → ℝ}
    (hg : ContinuousOn g Hbar) {M : ℝ} (hν : ∀ᵐ w ∂ν, w ∈ ballH M) : Integrable g ν := by
  have h := (hg.mono inter_subset_right).integrableOn_compact (μ := ν) (isCompact_ballH M)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hν] at h

/-- The pushed circle is carried by a bounded part of `Hbar`. -/
theorem exists_ae_ballH_map_psi {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (hc : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool)
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ M : ℝ, ∀ᵐ w ∂(foldedCircle d r).map (Ψ left a), w ∈ ballH M := by
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hs left
  obtain ⟨M, hM⟩ := bdd_invFunOn_of_normalized hφ (‖d‖ + r)
  have hmaps : MapsTo (Ψ left a) H (sideDom (pathTrace (γ ^ 2) a) left) := by
    rw [hΨa]; exact fun w hw => invFunOn_mem (hφ.1.surjOn hw)
  have hDH : sideDom (pathTrace (γ ^ 2) a) left ⊆ H := by
    cases left
    · exact rightComponent_subset_H _
    · exact leftComponent_subset_H _
  have hψm : Measurable (Ψ left a) :=
    (hΨ.1 left).comp (measurable_const.prodMk measurable_id)
  refine ⟨M, (ae_map_iff hψm.aemeasurable (isCompact_ballH M).isClosed.measurableSet).2 ?_⟩
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr, TwoPoint.foldedCircle_ae_norm_le d hr.le]
    with z hzH hzn
  refine ⟨mem_closedBall_zero_iff.2 ?_, H_subset_Hbar (hDH (hmaps hzH))⟩
  rw [hΨa]; exact hM z hzH hzn

/-- **`G1ProfileIntStmt` holds.** -/
theorem g1ProfileIntStmt : G1ProfileIntStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ a hc hs left G hG
  have hψm : Measurable (Ψ left a) :=
    (hΨ.1 left).comp (measurable_const.prodMk measurable_id)
  filter_upwards [ae_wedgeGood hX hA hXA hG, ae_scale_pos hγ hγ2 hX hA hXA,
    F1.ae_growth_radAvgReg hX, F1.ae_growth_wedge hA] with ω' hW hS hr hw
  obtain ⟨K₁, M₁, hM₁, h₁⟩ := hr
  obtain ⟨K₂, M₂, hM₂, h₂⟩ := hw
  intro d _ r hr
  have : IsProbabilityMeasure ((foldedCircle d r).map (Ψ left a)) :=
    (Measure.isProbabilityMeasure_map_iff hψm.aemeasurable).2 inferInstance
  obtain ⟨M, hM⟩ := exists_ae_ballH_map_psi hΨ hc hs left d hr
  set S := scaleParam γ (wedge0 γ X A ω')
  have hSmaps : MapsTo (fun w : ℂ => (S : ℂ) * w) Hbar Hbar := fun w hw => by
    show 0 ≤ ((S : ℂ) * w).im
    rw [Complex.im_ofReal_mul]; exact mul_nonneg hS.le hw
  refine ⟨fun k => integrable_of_continuousOn_of_ae_ballH ?_ hM,
    fun k => integrable_of_continuousOn_of_ae_ballH ?_ hM⟩
  · have hc' : ContinuousOn (fun u => G ω' (u, S * radius k)) Hbar :=
      hW.good.1.1.comp (continuous_id.prodMk continuous_const).continuousOn
        fun u hu => mk_mem_prod hu (show S * radius k ∈ Ioi 0 from mul_pos hS (radius_pos k))
    exact hc'.comp (continuous_const.mul continuous_id).continuousOn hSmaps
  · have hcont := F1.RC3Two.continuous_smoothFun_rp (F1.RC3Two.measurable_wg hW.cont)
      (F1.RC3Two.continuousOn_wg hW.good hW.cont)
      (F1.RC3Two.bd_wg (Q := Qc γ) (A := fun t => A t ω') hM₁ hM₂ h₁ h₂)
      (mul_pos hS (radius_pos k))
    exact (hcont.comp (continuous_const.mul continuous_id)).continuousOn

/-- **`G1ProfileStmt` from the convergence and continuity parts** (gap and integrability are
proved: `g1ProfileGapStmt`, `g1ProfileIntStmt`). -/
theorem g1ProfileStmt_of_conv_cont (h3 : G1ProfileConvStmt) (h4 : G1ProfileContStmt) :
    G1ProfileStmt :=
  g1ProfileStmt_of_parts g1ProfileGapStmt g1ProfileIntStmt h3 h4

end G1RC
end Thm18Asm
end QuantumZipper
