import QuantumZipper.Statements.Thm18Paper
import QuantumZipper.Proofs.Thm18.G4Read2Bdry
import QuantumZipper.Proofs.LQG.Measurability
import Mathlib.Probability.Kernel.MeasurableLIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Measurability bookkeeping for the zipper factorisation (ZIPFACTOR-SCALE)

* `measurable_areaScale_map`: the scale `areaScale` (Sheffield arXiv:1012.4797, (1.8), p. 26)
  of a pushed-forward area measure depends measurably on a parameter.
* `measurable_rvS_H`: the reverse Loewner map of a path-time pair, extended by `0` off `ℍ`, is
  jointly measurable (a Carathéodory-function argument: continuous in `z ∈ ℍ`, measurable in the
  path; mathlib's `measurable_uncurry_of_continuous_of_measurable`).

Own elementary argument (measure-theoretic bookkeeping the paper leaves implicit): monotone
exhaustion of `ℍ` by relatively compact open sets, normalised finite kernels, and mathlib's
`ProbabilityTheory.Kernel.measurable_kernel_prodMk_left`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm14WeldingData

/-- The scale of a pushed area measure is measurable in a parameter (own elementary argument). -/
theorem measurable_areaScale_map {D : Type*} [MeasurableSpace D] {μ : D → Measure ℂ}
    (hμ : Measurable μ) (hfin : ∀ d (K : Set ℂ), IsCompact K → K ⊆ H → μ d K < ∞)
    {f : D × ℂ → ℂ} (hf : Measurable f) :
    Measurable fun d => areaScale (((μ d).restrict H).map fun z => f (d, z)) := by
  classical
  have hfd : ∀ d, Measurable fun z => f (d, z) := fun d => hf.comp measurable_prodMk_left
  have hsec : ∀ B : Set ℂ, MeasurableSet B →
      Measurable fun d => ((μ d).restrict H).map (fun z => f (d, z)) B := by
    intro B hB
    have hT : MeasurableSet (f ⁻¹' B) := hf hB
    have heq : (fun d => ((μ d).restrict H).map (fun z => f (d, z)) B) =
        fun d => ⨆ N : ℕ, μ d (Prod.mk d ⁻¹' (f ⁻¹' B) ∩ LQGMeas.hExh N) := by
      funext d
      rw [Measure.map_apply (hfd d) hB, Measure.restrict_apply (hfd d hB),
        ← Monotone.measure_iUnion]
      · congr 1
        ext z
        simp only [mem_inter_iff, mem_iUnion, mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨N, hN⟩ := mem_iUnion.1 (LQGMeas.H_subset_iUnion_hExh h2)
          exact ⟨N, h1, hN⟩
        · rintro ⟨N, h1, hN⟩
          exact ⟨h1, LQGMeas.hExhK_subset_H N (LQGMeas.hExh_subset_compact N hN)⟩
      · intro m n hmn
        exact inter_subset_inter_right _ (LQGMeas.hExh_mono hmn)
    rw [heq]
    refine Measurable.iSup fun N => ?_
    have hEN : MeasurableSet (LQGMeas.hExh N) := (LQGMeas.isOpen_hExh N).measurableSet
    set c : D → ℝ≥0∞ := fun d => μ d (LQGMeas.hExh N) with hcdef
    have hc : Measurable c := (Measure.measurable_coe hEN).comp hμ
    have hcfin : ∀ d, c d < ∞ := fun d =>
      lt_of_le_of_lt (measure_mono (LQGMeas.hExh_subset_compact N))
        (hfin d _ (LQGMeas.isCompact_hExhK N) (LQGMeas.hExhK_subset_H N))
    let κ : ProbabilityTheory.Kernel D ℂ :=
      ⟨fun d => (c d)⁻¹ • (μ d).restrict (LQGMeas.hExh N), by
        refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
        simp only [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
        exact hc.inv.mul ((Measure.measurable_coe (hs.inter hEN)).comp hμ)⟩
    have hκ : ∀ d s, MeasurableSet s → κ d s = (c d)⁻¹ * μ d (s ∩ LQGMeas.hExh N) :=
      fun d s hs => by
        show ((c d)⁻¹ • (μ d).restrict (LQGMeas.hExh N)) s = _
        rw [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    have hmul : ∀ d x, x ≤ c d → c d * ((c d)⁻¹ * x) = x := by
      intro d x hx
      by_cases h0 : c d = 0
      · have : x = 0 := le_antisymm (h0 ▸ hx) bot_le
        simp [this]
      · rw [← mul_assoc, ENNReal.mul_inv_cancel h0 (hcfin d).ne, one_mul]
    have : ProbabilityTheory.IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, fun d => by
      rw [hκ d univ MeasurableSet.univ, univ_inter]
      by_cases h0 : c d = 0
      · rw [show μ d (LQGMeas.hExh N) = 0 from h0, mul_zero]; exact bot_le
      · rw [ENNReal.inv_mul_cancel h0 (hcfin d).ne]⟩⟩
    have hrepr : (fun d => μ d (Prod.mk d ⁻¹' (f ⁻¹' B) ∩ LQGMeas.hExh N)) =
        fun d => c d * κ d (Prod.mk d ⁻¹' (f ⁻¹' B)) := by
      funext d
      rw [hκ d _ (measurable_prodMk_left hT), hmul d _ (measure_mono inter_subset_right)]
    rw [hrepr]
    exact hc.mul (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hT)
  refine LQGMeas.measurable_sInf_upClosed _ (fun q => ?_) ?_ ?_
  · by_cases hq : (0 : ℝ) < q
    · simp only [mem_ofPred_eq, hq, true_and]
      exact measurableSet_le measurable_const
        (hsec _ (Metric.isOpen_ball.measurableSet.inter isOpen_H.measurableSet))
    · simp [hq]
  · rintro d a b ⟨ha, h1⟩ hab
    exact ⟨ha.trans_le hab,
      h1.trans (measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball hab)))⟩
  · rintro d a ⟨ha, -⟩
    exact ha

/-- Joint measurability of the reverse map of a path-time pair on `ℍ` (extended by `0`):
continuous in `z ∈ ℍ` for fixed path, measurable in the path for fixed `z`, hence jointly
measurable (mathlib `measurable_uncurry_of_continuous_of_measurable`). Own elementary argument. -/
theorem measurable_rvS_H :
    Measurable fun q : Thm18Asm.PathT × ℂ => if 0 < q.2.im then Thm18Asm.rvS q.1 q.2 else 0 := by
  classical
  let u : H → Thm18Asm.PathT → ℂ := fun w p => Thm18Asm.rvS p w
  have hcont : ∀ p, Continuous fun w : H => u w p := by
    intro p
    by_cases hT : 0 < p.2
    · have hs : (0 : ℝ) < (Real.sqrt p.2)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hT)
      have hmap : ∀ w : H, ((((Real.sqrt p.2)⁻¹ : ℝ) : ℂ) * (w : ℂ)) ∈ H := fun w => by
        show 0 < (_ : ℂ).im
        rw [Complex.im_ofReal_mul]
        exact mul_pos hs w.2
      have hd := differentiableOn_revMap (extIccPath zero_le_one p.1)
        (continuous_extIccPath _ _) zero_le_one
      refine continuous_iff_continuousAt.2 fun w => ?_
      have h1 : ContinuousAt (fun w : H => ((((Real.sqrt p.2)⁻¹ : ℝ) : ℂ) * (w : ℂ))) w :=
        (continuous_const.mul continuous_subtype_val).continuousAt
      exact (ContinuousAt.comp (g := revMap (extIccPath zero_le_one p.1) 1)
        (f := fun w : H => ((((Real.sqrt p.2)⁻¹ : ℝ) : ℂ) * (w : ℂ)))
        (hd.differentiableAt (isOpen_H.mem_nhds (hmap w))).continuousAt h1).div_const _
    · have h0 : Real.sqrt p.2 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hT)
      have : (fun w : H => u w p) = fun _ => 0 := by
        funext w
        simp only [u, Thm18Asm.rvS, h0, inv_zero, Complex.ofReal_zero, div_zero]
      rw [this]
      exact continuous_const
  have hmeas : ∀ w : H, Measurable (u w) := fun w => Thm18Asm.measurable_rvS w.2
  have hU := measurable_uncurry_of_continuous_of_measurable hcont hmeas
  have hS : MeasurableSet (Prod.snd ⁻¹' H : Set (Thm18Asm.PathT × ℂ)) :=
    measurable_snd isOpen_H.measurableSet
  have hf : Measurable fun x : (Prod.snd ⁻¹' H : Set (Thm18Asm.PathT × ℂ)) =>
      Function.uncurry u (⟨x.1.2, x.2⟩, x.1.1) :=
    hU.comp (((measurable_snd.comp measurable_subtype_coe).subtype_mk).prodMk
      (measurable_fst.comp measurable_subtype_coe))
  have hD := Measurable.dite hf
    (measurable_const : Measurable fun _ : ((Prod.snd ⁻¹' H : Set (Thm18Asm.PathT × ℂ))ᶜ :
      Set (Thm18Asm.PathT × ℂ)) => (0 : ℂ)) hS
  convert hD using 1
  funext q
  by_cases h : 0 < q.2.im
  · have h' : q ∈ (Prod.snd ⁻¹' H : Set (Thm18Asm.PathT × ℂ)) := h
    simp only [h, h', ite_true, dite_eq_left, Function.uncurry, u]
  · have h' : q ∉ (Prod.snd ⁻¹' H : Set (Thm18Asm.PathT × ℂ)) := h
    simp only [h, h', ite_false, dite_eq_right, not_false_eq_true]

end R18
end QuantumZipper
