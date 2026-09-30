import QuantumZipper.Proofs.Thm18.G4ZipUp2Psi
import QuantumZipper.Proofs.Loewner.ForwardHolo
import QuantumZipper.Proofs.Thm11.NonSwallowing
import QuantumZipper.Proofs.Thm11.CharFunRhs
import Mathlib.Analysis.Complex.AbsMax

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: joint measurability of `log ‖(revMapInv V 1)'‖`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (3). Task
G4ZIPUP-INPUTS, input (1): `RevInvLogDerivMeasStmt` (`G4ZipUp2Psi.lean`) is **proved**
(`revInvLogDerivMeasStmt_holds`).

Route.
* `revMapInv V 1` is the forward map `g` of the time-reversed driver on the open alive set
  `U = ℍ \ K` and `0` off it (`Cor15Group.revMapInv_eq_fwdMap_trev`), holomorphic on `U`
  with values in `ℍ` (`FwdHolo.differentiableOn_fwdMap`, `FwdHolo.mapsTo_fwdMap`).
* `deriv_eq_zero_of_notMem_of_mapsTo_H`: for such a function, the (junk-convention) `deriv`
  vanishes at every `w ∉ U`: at an accumulation point of `Uᶜ` a derivative must be `0` (the
  slope is `0` along `Uᶜ`); at an isolated point of `Uᶜ` the function cannot be differentiable,
  since `exp (i f)` would have a local maximum of its modulus there (maximum modulus principle,
  `Complex.eventually_eq_of_isLocalMax_norm`), forcing `Im f ≡ 0` near the point.
* On `U`, `deriv` is the limit of the difference quotients along `h = 1/(n+1)`; the alive set
  is jointly measurable (`NonSwallow.measurableSet_fwdHull_prod`) and `revMapInv` is jointly
  measurable (`Cor15Group.measurable_revMapInv_param`), so `deriv` is a pointwise limit of
  measurable functions (`measurable_of_tendsto_metrizable`).

**Own elementary argument** (measurability bookkeeping plus the maximum modulus principle);
Loewner facts as in Lawler, *Conformally Invariant Processes in the Plane*, Ch. 4, already
formalized in `Proofs/Loewner/ForwardHolo.lean`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- A function holomorphic on an open `U`, `ℍ`-valued there and `0` off `U`, has `deriv = 0`
at every point off `U`. -/
theorem deriv_eq_zero_of_notMem_of_mapsTo_H {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : DifferentiableOn ℂ f U) (hH : MapsTo f U H) (h0 : ∀ z, z ∉ U → f z = 0)
    {w : ℂ} (hw : w ∉ U) : deriv f w = 0 := by
  by_cases hdiff : DifferentiableAt ℂ f w
  swap
  · exact deriv_zero_of_not_differentiableAt hdiff
  have hfw : f w = 0 := h0 w hw
  by_cases hfr : ∃ᶠ z in 𝓝[≠] w, z ∉ U
  · by_contra hc
    have hT := hasDerivAt_iff_tendsto_slope.1 hdiff.hasDerivAt
    have hne := hT.eventually_ne hc
    obtain ⟨z, hzU, hz⟩ := (hfr.and_eventually (hne.and self_mem_nhdsWithin)).exists
    apply hz.1
    rw [slope_def_field, h0 z hzU, hfw, sub_self, zero_div]
  · rw [not_frequently] at hfr
    exfalso
    have hU' : ∀ᶠ z in 𝓝 w, z ≠ w → z ∈ U := by
      filter_upwards [eventually_nhdsWithin_iff.1 hfr] with z hz hzw
      exact not_not.1 (hz hzw)
    set g : ℂ → ℂ := fun z => Complex.exp (Complex.I * f z) with hg
    have hgd : ∀ᶠ z in 𝓝 w, DifferentiableAt ℂ g z := by
      filter_upwards [hU'] with z hz
      have hfz : DifferentiableAt ℂ f z := by
        by_cases hzw : z = w
        · rw [hzw]; exact hdiff
        · exact hd.differentiableAt (hU.mem_nhds (hz hzw))
      exact (hfz.const_mul Complex.I).cexp
    have hnorm : ∀ z, ‖g z‖ = Real.exp (-(f z).im) := by
      intro z
      simp [hg, Complex.norm_exp, Complex.mul_re]
    have hmax : IsLocalMax (norm ∘ g) w := by
      filter_upwards [hU'] with z hz
      show ‖g z‖ ≤ ‖g w‖
      rw [hnorm, hnorm, hfw, Complex.zero_im, neg_zero]
      rcases eq_or_ne z w with rfl | hzw
      · rw [hfw, Complex.zero_im, neg_zero]
      · have h2 : 0 < (f z).im := hH (hz hzw)
        exact Real.exp_le_exp.2 (by linarith)
    have hconst := Complex.eventually_eq_of_isLocalMax_norm hgd hmax
    have hev : ∀ᶠ z in 𝓝[≠] w, False := by
      filter_upwards [nhdsWithin_le_nhds hconst, hfr] with z hz hzU
      have h1 := congrArg norm hz
      rw [hnorm, hnorm, hfw, Complex.zero_im, neg_zero, Real.exp_zero] at h1
      have h2 : 0 < (f z).im := hH (not_not.1 hzU)
      have h3 : Real.exp (-(f z).im) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      rw [Real.exp_zero] at h3
      linarith
    obtain ⟨_, hF⟩ := hev.exists
    exact hF

/-- The structure of `revMapInv V 1` for a continuous driver with `V 0 = 0`. -/
theorem revMapInv_one_structure {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) :
    IsOpen (H \ fwdHull (ArcDriver.trev V 1) 1) ∧
      DifferentiableOn ℂ (revMapInv V 1) (H \ fwdHull (ArcDriver.trev V 1) 1) ∧
      MapsTo (revMapInv V 1) (H \ fwdHull (ArcDriver.trev V 1) 1) H ∧
      ∀ z, z ∉ H \ fwdHull (ArcDriver.trev V 1) 1 → revMapInv V 1 z = 0 := by
  classical
  have e := Cor15Group.revMapInv_eq_fwdMap_trev hV hV0 one_pos
  have hA : Continuous (ArcDriver.trev V 1) := ArcDriver.continuous_trev hV 1
  refine ⟨FwdHolo.isOpen_compl_fwdHull hA zero_le_one,
    (FwdHolo.differentiableOn_fwdMap hA zero_le_one).congr (fun z hz => ?_),
    fun z hz => ?_, fun z hz => ?_⟩
  · rw [e]; exact if_pos hz
  · rw [e]; show (if _ then _ else _) ∈ H
    rw [if_pos hz]; exact FwdHolo.mapsTo_fwdMap hA zero_le_one hz
  · rw [e]; exact if_neg hz

/-- **Input (1) of `g4ZipUpFieldReadStmt_of_zip2`, proved.** -/
theorem revInvLogDerivMeasStmt_holds : RevInvLogDerivMeasStmt := by
  intro α _ Vp hVc hV0 hVm
  classical
  have hf : Measurable fun p : ℂ × α => revMapInv (Vp p.2) 1 p.1 :=
    Cor15Group.measurable_revMapInv_param hVc hV0 hVm one_pos
  set B : ℝ≥0 → α → ℝ := fun r a => ArcDriver.trev (Vp a) 1 r with hBdef
  have hBm : ∀ r, Measurable (B r) := fun r => (hVm (1 - (r : ℝ))).sub (hVm 1)
  have hBc : ∀ a, Continuous fun r => B r a := fun a =>
    (ArcDriver.continuous_trev (hVc a) 1).comp NNReal.continuous_coe
  have hdr : ∀ a, ∀ r ∈ Icc (0 : ℝ) 1, drive 1 B a r = ArcDriver.trev (Vp a) 1 r := by
    intro a r hr
    simp only [drive, Real.sqrt_one, one_mul, hBdef, Real.coe_toNNReal _ hr.1]
  have hdc : ∀ a, Continuous (drive 1 B a) := fun a =>
    continuous_const.mul ((hBc a).comp continuous_real_toNNReal)
  have hK := NonSwallow.measurableSet_fwdHull_prod hBm hBc 1 zero_le_one
  set O : Set (α × ℂ) := {p | p.2 ∈ H \ fwdHull (ArcDriver.trev (Vp p.1) 1) 1} with hOdef
  have hO : MeasurableSet O := by
    have hm : MeasurableSet ({p : ℂ × α | 0 < p.1.im} \
        {p : ℂ × α | p.1 ∈ fwdHull (drive 1 B p.2) 1}) :=
      (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).diff hK
    convert hm.preimage measurable_swap using 1
    ext p
    simp only [hOdef, mem_setOf_eq, mem_preimage, mem_diff, Prod.fst_swap, Prod.snd_swap]
    rw [CharFunRhs.fwdHull_eq_of_eqOn (hdc p.1) (ArcDriver.continuous_trev (hVc p.1) 1)
      zero_le_one (hdr p.1)]
    rfl
  set q : ℕ → α × ℂ → ℂ := fun n p => if p ∈ O then
    ((n : ℂ) + 1) * (revMapInv (Vp p.1) 1 (p.2 + 1 / ((n : ℂ) + 1)) - revMapInv (Vp p.1) 1 p.2)
    else 0 with hqdef
  have hqm : ∀ n, Measurable (q n) := by
    intro n
    refine Measurable.ite hO (measurable_const.mul (Measurable.sub ?_ ?_)) measurable_const
    · exact hf.comp ((measurable_snd.add_const _).prodMk measurable_fst)
    · exact hf.comp (measurable_snd.prodMk measurable_fst)
  have hlim : Tendsto q atTop (𝓝 fun p : α × ℂ => deriv (revMapInv (Vp p.1) 1) p.2) := by
    refine tendsto_pi_nhds.2 fun p => ?_
    obtain ⟨hUo, hUd, hUH, hU0⟩ := revMapInv_one_structure (hVc p.1) (hV0 p.1)
    by_cases hp : p ∈ O
    · have hdiff : HasDerivAt (revMapInv (Vp p.1) 1) (deriv (revMapInv (Vp p.1) 1) p.2) p.2 :=
        (hUd.differentiableAt (hUo.mem_nhds hp)).hasDerivAt
      have hT := hasDerivAt_iff_tendsto_slope.1 hdiff
      have hseq : Tendsto (fun n : ℕ => p.2 + 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] p.2) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
        · simpa using (tendsto_const_nhds (x := p.2)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
        · refine mem_compl_singleton_iff.2 fun h => ?_
          have h2 : (1 : ℂ) / ((n : ℂ) + 1) = 0 := by linear_combination h
          rw [one_div, inv_eq_zero] at h2
          exact Nat.cast_add_one_ne_zero n h2
      refine (hT.comp hseq).congr fun n => ?_
      have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      simp only [Function.comp, slope_def_field, hqdef, if_pos hp, add_sub_cancel_left]
      field_simp
    · have h0 : deriv (revMapInv (Vp p.1) 1) p.2 = 0 :=
        deriv_eq_zero_of_notMem_of_mapsTo_H hUo hUd hUH hU0 hp
      simp only [hqdef, if_neg hp, h0]
      exact tendsto_const_nhds
  exact Real.measurable_log.comp (measurable_norm.comp (measurable_of_tendsto_metrizable hqm hlim))

end Thm18Asm
end QuantumZipper
