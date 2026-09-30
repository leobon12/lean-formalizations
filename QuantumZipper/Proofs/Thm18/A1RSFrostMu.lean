import QuantumZipper.Proofs.Thm18.A1RSFrostNu
import QuantumZipper.Proofs.Thm18.G1FrostAlphaMain
import QuantumZipper.Proofs.Thm18.G1RestUnifFree
import QuantumZipper.Proofs.RS.GenerationBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (8): the pushed side circles are Frostman, uniformly on parameter boxes

`μ_t = (f_t ∘ ψ)_* fc(d, s)` (`a1rMu`). The side map `ψ` has a continuous extension `ψe` to `ℍ̄`
whose pushed folded circles are Frostman uniformly on boxes (`fcFrostmanα_of_univalent`, the
Koebe-type bound of G1FrostAlphaKoebe.lean, exponent `koebeFrostExp`). Off the strip
`{Im f_t ∘ ψ ≤ τ}` (mass `≤ C τ^{1/2}` uniformly, `a1rMu_strip_le_unif`) the inverse `f_t⁻¹` is
`√(B² + 4T)/τ`-Lipschitz (two-point upper bound `TwoPoint.norm_revMap_sub_mul_le_upper` for the
time-reversed driver), and `ψ = f_t⁻¹ ∘ (f_t ∘ ψ)` on `ℍ` (`RS.fwdMapInv_fwdMap`), so the chart
lemma `isFrostman_map_of_chart` (A1RSFrost.lean, chart `ψe`) gives

**`isFrostman_a1rMu_unif`**: `μ_t` is `min(1/2, koebeFrostExp)/2`-Frostman with one constant for
`t ∈ (0, T]`, `‖d‖ ≤ 2R`, `s ∈ [e^{-R}, e^R]`.

Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1RC TwoPoint

/-- **Upper two-point bound for `f_t⁻¹` at bounded height.** -/
theorem norm_fwdMapInv_sub_mul_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {u v : ℂ} {τ R : ℝ} (hτ : 0 < τ) (hu : τ ≤ u.im) (hv : τ ≤ v.im)
    (huR : u.im ≤ R) (hvR : v.im ≤ R) :
    τ * ‖fwdMapInv W t u - fwdMapInv W t v‖ ≤ Real.sqrt (R ^ 2 + 4 * t) * ‖u - v‖ := by
  have hu0 : u ∈ H := show 0 < u.im by linarith
  have hv0 : v ∈ H := show 0 < v.im by linarith
  have hV : Continuous fun s => W (t - s) - W t :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hu0,
    UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hv0]
  have := norm_revMap_sub_mul_le_upper hV ht hτ hu hv huR hvR
  linarith

/-- The continuous extension of the side map, with its Frostman bound. -/
theorem exists_sideMap_ext {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) :
    ∃ ψe : ℂ → ℂ, Measurable ψe ∧ ContinuousOn ψe Hbar ∧ EqOn (g1zSideMap left W) ψe H ∧
      FcFrostmanα koebeFrostExp ψe := by
  obtain ⟨-, -, -, hη, -⟩ := hG
  have hφ := G1ZA1a.isNormalizedUniformizer_sideDom hη left
  obtain ⟨ψe, hm, hc, -, heq⟩ := psiExtContStmt_holds _ hη left _ hφ
  have hp := G1.invFunOn_props (isOpen_sideDom_α hη left) hφ
  have hd : DifferentiableOn ℂ ψe H := hp.1.congr fun z hz => (heq hz).symm
  have hi : InjOn ψe H := (G1.injOn_invFunOn_of_uniformizer hφ).congr heq
  exact ⟨ψe, hm, hc, heq, fcFrostmanα_of_univalent hc hd hi⟩

/-- **Uniform Frostman bound for the pushed side circles.** -/
theorem isFrostman_a1rMu_unif {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {T : ℝ}
    (hT : 0 < T) (R : ℕ) :
    ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) T, ∀ d : ℂ, ‖d‖ ≤ 2 * R → ∀ s : ℝ, Real.exp (-R) ≤ s →
      s ≤ Real.exp R → IsFrostman (a1rMu W t left d s) (min (1 / 2) koebeFrostExp / 2) C := by
  obtain ⟨ψe, hψm, hψc, hψeq, hψF⟩ := exists_sideMap_ext hG left
  obtain ⟨Cb, hCb, hball⟩ := hψF R
  set R₂ : ℝ := 2 * R + Real.exp R with hR₂
  have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) R₂) :=
    (isCompact_closedBall (0 : ℂ) R₂).inter_left isClosed_Hbar
  obtain ⟨Bψ, hBψ⟩ := hK.exists_bound_of_continuousOn (hψc.mono inter_subset_left)
  set M : ℝ := Real.sqrt (Bψ ^ 2 + 4 * T) with hMdef
  have hM : 0 < M := Real.sqrt_pos.2 (by positivity)
  have hs₀ : 0 < Real.exp (-(R : ℝ)) := Real.exp_pos _
  obtain ⟨Cm, hCm, hmass⟩ := a1rMu_strip_le_unif hG hT left (R₀ := max (2 * R) (Real.exp R)) hs₀
  refine ⟨Cm + Cb * (2 * M) ^ koebeFrostExp + 1, fun t ht d hd s hs1 hs2 => ?_⟩
  have hs : 0 < s := hs₀.trans_le hs1
  obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG ht.1 left
  set fc := foldedCircle d s with hfc
  have hmapeq : a1rMu W t left d s = fc.map g := by
    unfold a1rMu
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
    exact hEq hu
  rw [hmapeq]
  set bad : ℝ → Set ℂ := fun τ =>
    {w | (g w).im ≤ τ} ∪ (Hᶜ ∪ {w | ‖d‖ + s < ‖w‖}) with hbad
  have hnull : fc (Hᶜ ∪ {w | ‖d‖ + s < ‖w‖}) = 0 := by
    refine measure_union_null ?_ ?_
    · have := TwoPoint.foldedCircle_ae_mem_H d hs
      rwa [ae_iff] at this
    · have := TwoPoint.foldedCircle_ae_norm_le d hs.le
      rw [ae_iff] at this
      simpa [not_le] using this
  refine isFrostman_map_of_chart (m := fc) (X := ψe) (bad := bad) hgm hCm
    (by norm_num : (0 : ℝ) < 1 / 2) hCb koebeFrostExp_pos hM ?_ ?_ ?_
  · intro τ hτ _
    refine (measureReal_union_le _ _).trans ?_
    have h2 : fc.real (Hᶜ ∪ {w | ‖d‖ + s < ‖w‖}) = 0 := by
      rw [measureReal_def, hnull, ENNReal.toReal_zero]
    rw [h2, add_zero]
    have hS : MeasurableSet {z : ℂ | z.im ≤ τ} :=
      measurableSet_le Complex.continuous_im.measurable measurable_const
    have e : fc.real {w | (g w).im ≤ τ} = (fc.map g).real {z : ℂ | z.im ≤ τ} := by
      rw [measureReal_def, measureReal_def, Measure.map_apply hgm hS]; rfl
    rw [e, ← hmapeq]
    exact hmass t ht d (hd.trans (le_max_left _ _)) s hs1 (hs2.trans (le_max_right _ _)) τ hτ
  · intro c r hr
    have hb := hball d hd s hs1 hs2 c r hr
    have hmeas : MeasurableSet {w : ℂ | ψe w ∈ closedBall c r} :=
      hψm isClosed_closedBall.measurableSet
    rw [hfc, foldedCircle_eq_map_circM, measureReal_def,
      Measure.map_apply (show Measurable (fun θ => foldH (circleMap d s θ)) from
        (CircleFubini.continuous_foldH'.measurable).comp (continuous_circleMap d s).measurable)
        hmeas]
    exact hb
  · intro τ hτ _ w w' hw hw'
    simp only [hbad, mem_union, not_or, mem_setOf_eq, not_le, mem_compl_iff, not_not,
      not_lt] at hw hw'
    have key : ∀ v : ℂ, τ < (g v).im → v ∈ H → ‖v‖ ≤ ‖d‖ + s →
        ψe v = fwdMapInv W t (g v) ∧ τ ≤ (g v).im ∧ (g v).im ≤ Bψ := by
      intro v hv1 hv2 hv3
      have hmem := sideMap_mem_compl_fwdHull hG ht.1.le left hv2
      have hgv : g v = fwdMap W t (g1zSideMap left W v) := (hEq hv2).symm
      refine ⟨?_, hv1.le, ?_⟩
      · rw [hgv, RS.fwdMapInv_fwdMap hG.1 hG.2.1 ht.1.le hmem]
        exact (hψeq hv2).symm
      · rw [hgv]
        refine (RS.im_fwdMap_le_im hG.1 ht.1.le hmem).trans ?_
        rw [hψeq hv2]
        refine (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (hBψ v ⟨show 0 ≤ v.im from le_of_lt hv2, ?_⟩))
        rw [mem_closedBall, dist_zero_right]
        have : ‖d‖ + s ≤ R₂ := by rw [hR₂]; linarith
        linarith
    obtain ⟨e1, l1, u1⟩ := key w hw.1 hw.2.1 hw.2.2
    obtain ⟨e2, l2, u2⟩ := key w' hw'.1 hw'.2.1 hw'.2.2
    rw [e1, e2]
    refine (norm_fwdMapInv_sub_mul_le hG.1 hG.2.1 ht.1.le hτ l1 l2 u1 u2).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (norm_nonneg _)
    linarith [ht.2]

end A1RS
end R18
end QuantumZipper
