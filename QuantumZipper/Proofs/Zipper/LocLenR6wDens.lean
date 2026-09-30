import QuantumZipper.Proofs.Zipper.LocLenR6fDefs
import QuantumZipper.Proofs.Zipper.LocLenXGood
import QuantumZipper.Proofs.Zipper.LocLenB5ULocal
import QuantumZipper.Proofs.Zipper.LogShiftWRed
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.Section5.Prop17Field
import QuantumZipper.Proofs.Field.Factorization
import QuantumZipper.Proofs.Zipper.LogShiftW2Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6w (1): the open-arc stage density of a log-shifted `Γ⁰` field

Open-arc replacement of `F1.logShiftWDens0Stmt_of_x` (LogShiftWDens0.lean:141). At every stage
`t ≥ 0`, with `y_t` the unzipped `Γ⁰` field, `ν_Y` its local boundary limit off the tip `{0}`
and `Z_t` the unzipped log-shifted field, the local boundary limit of `Z_t` off
`offSet W t = {O⁻_t, 0, O⁺_t}` is `e^{γ φ(E_t ·)/2} · ν_Y` (`φ = −γ log|·| + G`, `E_t` the
boundary extension of `f_t⁻¹`). Proof: the local rule (5.1) (Sheffield arXiv:1012.4797 §5.4,
rule (5.1); Duplantier–Sheffield, Invent. Math. 185 (2011), §6), applied first to the function
`ψ_t = −γ log|E_t|`, continuous off the root images (as in `xGoodOffAll_of_yGoodOff`), and then to
the continuous `G ∘ E_t` (`unzipAddFun`); no TIP-X, since nothing is asked at `O^±_t`.
Moreover `ν_Y` is atomless (`unifLocalStmt_holds`, uniqueness of local limits).

Own bookkeeping (copy of the old proof with the local rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- **Open-arc stage density** (a.s., all stages). -/
theorem ae_stageDensArc (hYO : WedgeUnzip.YMergeOffTipStmt) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {G : Ω → ℂ → ℝ} {Z : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hI : IndepFun (pathOf B) X P)
    (hGZ : ∀ᵐ ω ∂P, Continuous (G ω) ∧ ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z ω (foldedCircle d r) = (X ω + F2.logSingField κ + ofFun (G ω)) (foldedCircle d r)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∃ νY : Measure ℝ, (∀ x, νY {x} = 0) ∧
      IsRegularSample (unzippedField (Real.sqrt κ) (B2.cfg κ B X ω) t) ∧
      HasBdryLimitOn (Real.sqrt κ) (unzippedField (Real.sqrt κ) (B2.cfg κ B X ω) t) {0}ᶜ νY ∧
      IsRegularSample (unzippedField (Real.sqrt κ) (Z ω, drive κ B ω) t) ∧
      HasBdryLimitOn (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Z ω, drive κ B ω) t)
        (offSet (drive κ B ω) t)ᶜ
        ((νY.restrict (offSet (drive κ B ω) t)ᶜ).withDensity
          (lswDens κ (G ω) (fun x => F2.extInv (drive κ B ω) t x))) := by
  have hloc := ae_all_iff.2 fun n : ℕ =>
    unifLocalStmt_holds (T := (n : ℝ) + 1) hκ hκ4 (by positivity) hB hX hI
  filter_upwards [hloc, xGoodOffAll_of_yMergeOffTip hYO κ hκ hκ4 P B X hB hX hI,
    yGoodOffAll_of_yMergeOffTip hYO κ hκ hκ4 P B X hB hX hI,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB,
    WedgeUnzip.extNonvanishStmt_holds κ hκ hκ4 P B hB,
    F2.step3FieldCircDy_holds κ hκ hκ4 P B X hB hX hI,
    WedgeUnzip.xContinuumStmt_holds κ hκ hκ4 P B X hB hX hI, hGZ,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hlocω hxg hyω hCω hNVω hcirc hCo hZ hc h0 t ht
  obtain ⟨hGc, hZfc⟩ := hZ
  set γ := Real.sqrt κ with hγ
  set W := drive κ B ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  -- the `Γ⁰` stage field is `y_t`
  have eΓ : unzippedField γ (B2.cfg κ B X ω) t = F2.unzY κ (X ω) W t := by
    unfold B2.cfg F2.unzY
    rw [F2.h0rev_add_eq]
  obtain ⟨⟨F, hF⟩, ⟨νY, hνY⟩, -⟩ := hyω t ht
  -- atomless: uniqueness against the atomless local limit of `UnifLocalStmt`
  obtain ⟨n, hn⟩ := exists_nat_ge t
  obtain ⟨ν', hν', hat'⟩ := hlocω n t ⟨ht, by linarith⟩
  have hyreg : IsRegularSample (F2.unzY κ (X ω) W t) := ⟨F, hF⟩
  have hνeq : νY = ν' := by
    refine LocalRule.isVagueLimitOnR_unique isOpen_compl_singleton
      (hνY.isVagueLimitOnR hyreg) ?_
    rw [B2.h0f_eq_unzippedField, eΓ] at hν'
    exact hν'
  -- the function `ψ_t` off the root images (as in `xGoodOffAll_of_yGoodOff`)
  have hψ : ContinuousOn (WedgeUnzip.logTipFun κ W t)
      ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet W t)ᶜ ∩ Hbar) := by
    intro u hu
    have hcw : ContinuousWithinAt (F2.extInv W t)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet W t)ᶜ ∩ Hbar) u :=
      (hCω t ht u hu.2).mono inter_subset_right
    have hne : F2.extInv W t u ≠ 0 := hNVω t ht u hu.2 hu.1
    have hlog : ContinuousWithinAt (fun v => Real.log ‖F2.extInv W t v‖)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet W t)ᶜ ∩ Hbar) u :=
      hcw.norm.log (norm_ne_zero_iff.2 hne)
    exact (hlog.const_mul (Real.sqrt κ)).neg
  have hWo : IsOpen ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet W t)ᶜ) :=
    ((WedgeUnzip.isCompact_tipSet _ t).image Complex.continuous_ofReal).isClosed.isOpen_compl
  have hUo : IsOpen (offSet W t)ᶜ := (isClosed_offSet _ t).isOpen_compl
  have hUW : ∀ s ∈ (offSet W t)ᶜ, (s : ℂ) ∈ (((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet W t)ᶜ := by
    rintro s hs ⟨u, hu, hus⟩
    obtain rfl := Complex.ofReal_injective hus
    apply hs
    rcases hu with rfl | rfl <;> simp [offSet]
  have hsub : (offSet W t)ᶜ ⊆ ({0} : Set ℝ)ᶜ :=
    compl_subset_compl.2 (singleton_subset_iff.2 (by simp [offSet]))
  -- step 1: `x_t = y_t + ψ_t` off the root images
  have h2 := (hνY.mono hUo hsub).add_ofFun hyreg hUo hWo hUW hψ
  have havg : avgReg (F2.unzX κ (X ω) W t) =
      avgReg (F2.unzY κ (X ω) W t + ofFun (WedgeUnzip.logTipFun κ W t)) :=
    funext fun k => funext fun z => F2.forall_avgReg_eq_of_lpt (fun n a b k => hcirc t ht n a b k) k z
  have h3 := (hasBdryLimitOn_congr_avg havg).2 h2
  -- step 2: add `G ∘ E_t`
  have hGE : ContinuousOn (G ω ∘ F2.extInv W t) Hbar := hGc.comp_continuousOn (hCω t ht)
  have hxreg : IsRegularSample (F2.unzX κ (X ω) W t) := (hxg t ht).1
  have h4 := h3.add_ofFun hxreg hUo isOpen_univ (fun _ _ => mem_univ _)
    (by rwa [univ_inter])
  have hraw := WedgeUnzip.unzipAddFun γ (X ω + F2.logSingField κ) (G ω) W t ht hW hW0 hGc hCo.1
    (fun d _ r hr => hCo.2 t ht d r hr)
  have hreg := S5.FieldShift.regEq_of_fc hZfc
  have e1 : unzippedField γ (Z ω, W) t =
      unzippedField γ (X ω + F2.logSingField κ + ofFun (G ω), W) t :=
    Factorization.coordChange_congr (funext fun k => funext fun z => hreg k z) _ _
  have hav5 : avgReg (unzippedField γ (X ω + F2.logSingField κ + ofFun (G ω), W) t) =
      avgReg (F2.unzX κ (X ω) W t + ofFun (G ω ∘ F2.extInv W t)) :=
    funext fun k => funext fun z => S5.FieldShift.regEq_of_fc hraw k z
  have h5 := (hasBdryLimitOn_congr_avg hav5).2 h4
  have hE : Continuous (fun x : ℝ => F2.extInv W t x) :=
    (hCω t ht).comp_continuous Complex.continuous_ofReal
      (fun x => show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp)
  have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (γ / 2 *
      WedgeUnzip.logTipFun κ W t x))) := by
    unfold WedgeUnzip.logTipFun
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.mul (Real.measurable_log.comp (measurable_norm.comp hE.measurable))).neg))
  have hm2 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (γ / 2 *
      (G ω ∘ F2.extInv W t) x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (hGc.measurable.comp hE.measurable)))
  have hdens : ((νY.restrict (offSet W t)ᶜ).withDensity (fun x : ℝ => ENNReal.ofReal
      (Real.exp (γ / 2 * WedgeUnzip.logTipFun κ W t x)))).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (γ / 2 * (G ω ∘ F2.extInv W t) x))) =
      (νY.restrict (offSet W t)ᶜ).withDensity (lswDens κ (G ω) (fun x => F2.extInv W t x)) := by
    rw [← withDensity_mul _ hm1 hm2]
    congr 1
    funext x
    simp only [Pi.mul_apply, lswDens, lswPhi, WedgeUnzip.logTipFun, Function.comp]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  refine ⟨νY, fun x => by rw [hνeq]; exact hat' x, by rw [eΓ]; exact hyreg,
    by rw [eΓ]; exact hνY, ?_, ?_⟩
  · rw [e1]
    exact isRegularSample_of_fc_Hbar hraw (GoodSample.gs_add_ofFun_sample hxreg hGE)
  · rw [e1, ← hdens]
    exact h5

end LocLen
end QuantumZipper
