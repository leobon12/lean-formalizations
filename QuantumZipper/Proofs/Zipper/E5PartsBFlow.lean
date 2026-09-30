import QuantumZipper.Proofs.Zipper.E5Final5f

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-PARTSB, part 1: measurability of the collision correction for a path-valued parameter

Task E5-PARTSB (Theorem 1.3, node E5, decisions D39/D40; Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72, proof of Lemma 5.6).

`E5Final5e`/`E5Final5f` prove the joint measurability of the reverse maps, the pushed normalizer
`ϖ_τ` and the driver part `locCorrDrv` of the collision correction on the level space, with the
driver `Vr κ T B ω = vrPath κ T (pathIcc T B ω)`. The germ-independent representation of E5 needs
the same facts on a parameter space `E` carrying a **measurable path** `π : E → C([0,T], ℝ)` and a
measurable nonnegative time `τ`, with driver `vrPath κ T (π e)`. The proofs are those of
`E5Final5e`/`E5Final5f` with `pathIcc T B ∘ ofCompl P ∘ snd` replaced by `π`
(`measurable_revMap_pg`, `measurable_varpiT_pg`, `measurable_locCorrDrv_pg`). Own bookkeeping.
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2 E1 E4Grid CoordsFull

section PathParam

variable {E : Type} [MeasurableSpace E] {κ T : ℝ} (hT : 0 ≤ T)
  {π : E → C(Icc (0 : ℝ) T, ℝ)} {τ : E → ℝ} {ϖ : Measure ℂ}

/-- **The reverse maps of a measurable path family at a measurable nonnegative time are jointly
measurable.** -/
theorem measurable_revMap_pg (hπ : Measurable π) (hτm : Measurable τ) (hτ0 : ∀ e, 0 ≤ τ e) :
    Measurable fun p : E × ℂ => revMap (vrPath κ T hT (π p.1)) (τ p.1) p.2 := by
  classical
  set S : Set (E × ℂ) := {p | 0 < p.2.im} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (Complex.measurable_im.comp
    measurable_snd)
  set F : S → ℂ := fun q => revMap (vrPath κ T hT (π q.1.1)) (max (τ q.1.1) 0) q.1.2 with hFdef
  have e : (fun p : E × ℂ => revMap (vrPath κ T hT (π p.1)) (τ p.1) p.2) = fun p =>
      if hp : p ∈ S then F ⟨p, hp⟩ else (0 : ℂ) := by
    funext p
    split_ifs with hp
    · simp only [hFdef, max_eq_left (hτ0 p.1)]
    · exact CharFun.revMap_of_not_mem (hτ0 p.1) hp
  rw [e]
  refine Measurable.dite (f := F) (g := fun _ => (0 : ℂ)) ?_ measurable_const hSm
  have hin : Measurable fun q : S =>
      (((τ q.1.1, ⟨q.1.2, q.2⟩) : ℝ × {z : ℂ // 0 < z.im}), π q.1.1) :=
    ((hτm.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)).prodMk
      (hπ.comp (measurable_fst.comp measurable_subtype_coe))
  exact (measurable_revMap_vrPath_uncurry κ T hT).comp hin

/-- **The pushed normalizer of a measurable path family is a measurable family of measures.** -/
theorem measurable_varpiT_pg (hϖ : IsNormalizer ϖ) (hπ : Measurable π) (hτm : Measurable τ)
    (hτ0 : ∀ e, 0 ≤ τ e) {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable fun e : E => varpiT (vrPath κ T hT (π e)) (τ e) ϖ A := by
  have := hϖ.prob
  have hR := measurable_revMap_pg (κ := κ) hT hπ hτm hτ0
  have e : (fun e : E => varpiT (vrPath κ T hT (π e)) (τ e) ϖ A) =
      fun e => ∫⁻ v, A.indicator 1 (revMap (vrPath κ T hT (π e)) (τ e) v) ∂ϖ := by
    funext e
    have hm := TwoPoint.measurable_revMap (continuous_vrPath κ T hT (π e)) (hτ0 e)
    rw [varpiT, Measure.map_apply hm hA, ← lintegral_indicator_one (hm hA)]
    rfl
  rw [e]
  exact ((measurable_one.indicator hA).comp hR).lintegral_prod_right'

/-- The reverse map of the path family (curried). -/
def revPg (κ T : ℝ) (hT : 0 ≤ T) (π : E → C(Icc (0 : ℝ) T, ℝ)) (τ : E → ℝ) (e : E) (u : ℂ) : ℂ :=
  revMap (vrPath κ T hT (π e)) (τ e) u

/-- Difference-quotient version of `deriv (revMap (vrPath κ T (π e)) (τ e))`. -/
def derivPg (κ T : ℝ) (hT : 0 ≤ T) (π : E → C(Icc (0 : ℝ) T, ℝ)) (τ : E → ℝ) (p : E × ℂ) : ℂ :=
  limUnder atTop fun n => (CharFun.hstep n)⁻¹ •
    (revPg κ T hT π τ p.1 (p.2 + CharFun.hstep n) - revPg κ T hT π τ p.1 p.2)

theorem measurable_derivPg (hπ : Measurable π) (hτm : Measurable τ) (hτ0 : ∀ e, 0 ≤ τ e) :
    Measurable (derivPg κ T hT π τ) := by
  have hR := measurable_revMap_pg (κ := κ) hT hπ hτm hτ0
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  exact ((hR.comp (measurable_fst.prodMk (measurable_snd.add_const _))).sub hR).const_smul
    ((CharFun.hstep n)⁻¹ : ℂ)

theorem derivPg_eq (hτ0 : ∀ e, 0 ≤ τ e) (e : E) {u : ℂ} (hu : u ∈ H) :
    derivPg κ T hT π τ (e, u) = deriv (revMap (vrPath κ T hT (π e)) (τ e)) u := by
  have hd := hasDerivAt_revMap _ (continuous_vrPath κ T hT (π e)) (hτ0 e) hu
  have ht := hd.tendsto_slope_zero
  have hs : Tendsto CharFun.hstep atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      mem_compl_singleton_iff.2 (Complex.ofReal_ne_zero.2 (by positivity))⟩
    have := (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Complex.ofReal_zero] at this
    exact this
  rw [hd.deriv]
  exact (ht.comp hs).limUnder_eq

theorem measurable_qt_pg (hϖ : IsNormalizer ϖ) (hπ : Measurable π) (hτm : Measurable τ)
    (hτ0 : ∀ e, 0 ≤ τ e) :
    Measurable fun e : E => qt κ (vrPath κ T hT (π e)) (τ e) ϖ := by
  have := hϖ.prob
  have e : (fun e : E => qt κ (vrPath κ T hT (π e)) (τ e) ϖ) =
      fun e => Qc (Real.sqrt κ) * ∫ v, Real.log ‖derivPg κ T hT π τ (e, v)‖ ∂ϖ := by
    funext e
    simp only [qt]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hϖ.ae_mem_H] with v hv
    rw [derivPg_eq hT hτ0 e hv]
  rw [e]
  have hm : Measurable fun p : E × ℂ => Real.log ‖derivPg κ T hT π τ p‖ :=
    Real.measurable_log.comp (measurable_derivPg hT hπ hτm hτ0).norm
  exact measurable_const.mul (hm.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_kPot_pg (hϖ : IsNormalizer ϖ) (hπ : Measurable π) (hτm : Measurable τ)
    (hτ0 : ∀ e, 0 ≤ τ e) :
    Measurable fun p : E × ℂ => PalmNorm.kPot (varpiT (vrPath κ T hT (π p.1)) (τ p.1) ϖ) p.2 := by
  have e : (fun p : E × ℂ => PalmNorm.kPot (varpiT (vrPath κ T hT (π p.1)) (τ p.1) ϖ) p.2) =
      fun p => ∫ w, neumannH p.2 (revPg κ T hT π τ p.1 w) ∂ϖ := by
    funext p
    have hm := TwoPoint.measurable_revMap (continuous_vrPath κ T hT (π p.1)) (hτ0 p.1)
    simp only [PalmNorm.kPot, varpiT]
    rw [integral_map hm.aemeasurable]
    · rfl
    · exact (measurable_neumannH.comp (measurable_const.prodMk measurable_id) :
        Measurable fun w => neumannH p.2 w).aestronglyMeasurable
  rw [e]
  have := hϖ.prob
  have hR := measurable_revMap_pg (κ := κ) hT hπ hτm hτ0
  have hF : Measurable fun q : (E × ℂ) × ℂ => neumannH q.1.2 (revPg κ T hT π τ q.1.1 q.2) :=
    measurable_neumannH.comp ((measurable_snd.comp measurable_fst).prodMk
      (hR.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_shiftFun_pg (hϖ : IsNormalizer ϖ) (hπ : Measurable π) (hτm : Measurable τ)
    (hτ0 : ∀ e, 0 ≤ τ e) :
    Measurable fun p : E × ℂ => PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
      (varpiT (vrPath κ T hT (π p.1)) (τ p.1) ϖ) 0 p.2 := by
  unfold PalmNorm.shiftFun
  refine ((UnzipInvariance.measurable_h0rev κ).comp measurable_snd).add
    (measurable_const.mul (Measurable.sub ?_ (measurable_kPot_pg hT hϖ hπ hτm hτ0)))
  exact measurable_neumannH.comp (measurable_const.prodMk measurable_snd)

theorem measurable_ofFun_shiftFun_pg (hϖ : IsNormalizer ϖ) (hπ : Measurable π)
    (hτm : Measurable τ) (hτ0 : ∀ e, 0 ≤ τ e) :
    Measurable fun e : E => ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
      (varpiT (vrPath κ T hT (π e)) (τ e) ϖ) 0) (varpiT (vrPath κ T hT (π e)) (τ e) ϖ) := by
  have hSF := measurable_shiftFun_pg (κ := κ) hT hϖ hπ hτm hτ0
  have hR := measurable_revMap_pg (κ := κ) hT hπ hτm hτ0
  have e : (fun e : E => ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
      (varpiT (vrPath κ T hT (π e)) (τ e) ϖ) 0) (varpiT (vrPath κ T hT (π e)) (τ e) ϖ)) =
      fun e => ∫ w, PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (vrPath κ T hT (π e)) (τ e) ϖ) 0 (revPg κ T hT π τ e w) ∂ϖ := by
    funext e
    have hm := TwoPoint.measurable_revMap (continuous_vrPath κ T hT (π e)) (hτ0 e)
    have hSm : Measurable fun u : ℂ => PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
        (varpiT (vrPath κ T hT (π e)) (τ e) ϖ) 0 u :=
      hSF.comp (measurable_const.prodMk measurable_id)
    exact integral_map hm.aemeasurable hSm.aestronglyMeasurable
  rw [e]
  have := hϖ.prob
  have hF : Measurable fun q : E × ℂ => PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ)
      (varpiT (vrPath κ T hT (π q.1)) (τ q.1) ϖ) 0 (revPg κ T hT π τ q.1 q.2) :=
    hSF.comp (measurable_fst.prodMk hR)
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

/-- **The driver part of the collision correction of a measurable path family is measurable.** -/
theorem measurable_locCorrDrv_pg (hϖ : IsNormalizer ϖ) (hπ : Measurable π) (hτm : Measurable τ)
    (hτ0 : ∀ e, 0 ≤ τ e) (z : ℂ) :
    Measurable fun e : E => locCorrDrv κ (vrPath κ T hT (π e)) (τ e) ϖ z := by
  unfold locCorrDrv
  exact ((measurable_const.mul ((measurable_kPot_pg hT hϖ hπ hτm hτ0).comp
    (measurable_id.prodMk measurable_const))).sub
    (measurable_ofFun_shiftFun_pg hT hϖ hπ hτm hτ0)).sub
    (measurable_qt_pg hT hϖ hπ hτm hτ0)

end PathParam

end E5
end QuantumZipper
