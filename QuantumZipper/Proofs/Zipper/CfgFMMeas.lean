import QuantumZipper.Proofs.Zipper.CfgFMDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE (4): the block events of the free-field part are measurable

On the path × field space, the first modes `fmInt (fZE px t) w τ s` are measurable in `px` for
fixed parameters (Carathéodory: `ZE px` is continuous in the parameter and measurable in `px`)
and continuous in the parameters on the block (`s > 0`). Hence each block event is a countable
union over a dense subset of the block (`CfgFM.measurableSet_fmHBlockEvent`), which is what the
independence transfer `CharFun.ae_indep` needs. Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper.E6
namespace CfgFM

open RegUnif RegCont RegSample

variable {T : ℝ} (hT : 0 ≤ T) (κ : ℝ)

/-- The block parameter set. -/
def blk (T : ℝ) (m n : ℕ) : Set (ℂ × ℝ × ℝ × ℝ) :=
  {a | a.1 ∈ D3Plus.fmBox m ∧ a.2.1 ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n) ∧
    a.2.2.1 ∈ Ioo 0 a.2.1 ∧ a.2.2.2 ∈ Icc (0 : ℝ) T}

/-- The first mode as a function of the parameter. -/
def fmA (px : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (a : ℂ × ℝ × ℝ × ℝ) : ℝ :=
  ‖D3Plus.fmInt (fZE hT κ px a.2.2.2) a.1 a.2.1 a.2.2.1‖

/-- The integrand of the first mode. -/
def fmU (px : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (a : ℂ × ℝ × ℝ × ℝ) (θ : ℝ) : ℂ :=
  ((ZE hT κ px (pr (a.1 + (a.2.1 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) a.2.2.1 a.2.2.2) :
    ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

theorem fmA_eq (px : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (a : ℂ × ℝ × ℝ × ℝ) :
    fmA hT κ px a = ‖∫ θ in (0 : ℝ)..(2 * Real.pi), fmU hT κ px a θ‖ := rfl

theorem continuous_fmU (px : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (a : ℂ × ℝ × ℝ × ℝ) :
    Continuous fun θ => fmU hT κ px a θ := by
  unfold fmU
  refine (Complex.continuous_ofReal.comp ((continuous_ZE hT κ px).comp
    ((continuous_pr_fst a.2.2.1 a.2.2.2).comp ?_))).mul ?_
  · exact continuous_const.add (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))
  · exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem measurable_fmU (a : ℂ × ℝ × ℝ × ℝ) (θ : ℝ) : Measurable fun px => fmU hT κ px a θ := by
  unfold fmU
  exact (Complex.measurable_ofReal.comp (measurable_ZE hT κ _)).mul_const _

theorem measurable_fmU_uncurry (a : ℂ × ℝ × ℝ × ℝ) :
    Measurable (Function.uncurry fun (θ : ℝ) px => fmU hT κ px a θ) :=
  measurable_uncurry_of_continuous_of_measurable (fun px => continuous_fmU hT κ px a)
    (fun θ => measurable_fmU hT κ a θ)

theorem measurable_fmA (a : ℂ × ℝ × ℝ × ℝ) : Measurable fun px => fmA hT κ px a := by
  have h0 := measurable_fmU_uncurry hT κ a
  have hj : Measurable (Function.uncurry fun px (θ : ℝ) => fmU hT κ px a θ) :=
    Measurable.comp (g := Function.uncurry fun (θ : ℝ) px => fmU hT κ px a θ)
      (f := Prod.swap) h0 measurable_swap
  have hI : Measurable fun px => ∫ θ, fmU hT κ px a θ ∂(volume.restrict (Ioc 0 (2 * Real.pi))) :=
    (hj.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))).measurable
  have e : (fun px => fmA hT κ px a) =
      fun px => ‖∫ θ, fmU hT κ px a θ ∂(volume.restrict (Ioc 0 (2 * Real.pi)))‖ := by
    funext px
    rw [fmA_eq, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rw [e]
  exact hI.norm

theorem continuousOn_fmA (px : C(Icc (0 : ℝ) T, ℝ) × FieldSample) (m n : ℕ) :
    ContinuousOn (fmA hT κ px) (blk T m n) := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous (Function.uncurry fun (a : blk T m n) θ => fmU hT κ px a.1 θ) := by
    refine (Complex.continuous_ofReal.comp ((continuous_ZE hT κ px).comp ?_)).mul (by fun_prop)
    refine continuousOn_pr.comp_continuous (f := fun x : blk T m n × ℝ =>
      ((x.1.1.1 + (x.1.1.2.1 : ℂ) * Complex.exp ((x.2 : ℂ) * Complex.I), x.1.1.2.2.1),
        x.1.1.2.2.2)) (by fun_prop) fun x => ?_
    exact x.1.2.2.2.1.1
  have h2 := (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hc 0
    (2 * Real.pi)).norm
  exact h2

/-- **Block events are measurable.** -/
theorem measurableSet_fmHBlockEvent (m n : ℕ) :
    MeasurableSet (fmHBlockEvent (fZE hT κ) T m n) := by
  obtain ⟨D, hDc, hDA, hAD⟩ := TopologicalSpace.exists_countable_dense_subset (blk T m n)
  have e : fmHBlockEvent (fZE hT κ) T m n =
      ⋃ a ∈ D, {px | Real.sqrt ((2 : ℝ) ^ n) < fmA hT κ px a} := by
    ext px
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨w, hw, τ, hτ, s, hs, t, ht, hlt⟩
      have ha : (w, τ, s, t) ∈ blk T m n := ⟨hw, hτ, hs, ht⟩
      have hcw := continuousOn_fmA hT κ px m n _ ha
      have hev : ∀ᶠ b in 𝓝[D] (w, τ, s, t), Real.sqrt ((2 : ℝ) ^ n) < fmA hT κ px b :=
        (hcw.mono hDA).eventually (lt_mem_nhds hlt)
      have hne : (𝓝[D] (w, τ, s, t)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hAD ha)
      obtain ⟨b, hb, hbD⟩ := (hev.and self_mem_nhdsWithin).exists
      exact ⟨b, hbD, hb⟩
    · rintro ⟨a, haD, hlt⟩
      obtain ⟨h1, h2, h3, h4⟩ := hDA haD
      exact ⟨a.1, h1, a.2.1, h2, a.2.2.1, h3, a.2.2.2, h4, hlt⟩
  rw [e]
  exact MeasurableSet.biUnion hDc fun a _ =>
    measurableSet_lt measurable_const (measurable_fmA hT κ a)

end CfgFM
end QuantumZipper.E6
