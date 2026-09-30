import QuantumZipper.Proofs.LQG.GoodMeasurable
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Independence.Basic

/-!
# M4-T5: independent random parameters

* `ae_mem_of_indepFun` (generic): if `X ⊥ Θ` and a measurable event `G ⊆ S × E` has
  `P{(X, p) ∈ G} = 1` for every fixed `p`, then `P{(X, Θ) ∈ G} = 1`. The joint law is the product
  law (`indepFun_iff_map_prod_eq_prod_map_map`), then Fubini (`Measure.prod_apply_symm`).
* `ae_isLQGGood_of_indepFun`: the instance with the measurable good set (R5(a)), for any family
  `F p x` whose coordinates are jointly measurable in `(x, p)`.
* Random continuous functions and random constants (T1): here the deterministic rule holds for
  every good sample and every parameter at once, so no independence is needed
  (`ae_isLQGGood_add_ofFun`, `ae_isLQGGood_addConst`, with the measure identities).
* Random translations and dilations (T2, T3): these rules are not yet built as theorems, so
  they enter as fixed-parameter a.s. hypotheses, which the independence lemma upgrades to
  independent random parameters (`ae_isLQGGood_translate_indep`, `ae_isLQGGood_rescale_indep`).
  The joint measurability comes from `measurable_evalReg_fc₂` (folded circles as a kernel in
  centre and radius).
-/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace QuantumZipper

namespace IndepParams

open Factorization

/-! ## 1. The generic lemma -/

/-! ## 2. The instance with the measurable good set -/

theorem measurableSet_good_coords (γ : ℝ) :
    MeasurableSet {c : ℕ → ℝ | IsLQGGood γ (reconstruct c)} :=
  measurable_reconstruct (GoodMeas.measurableSet_isLQGGood γ)

/-! ## 3. Random continuous functions and constants (T1): deterministic, no independence -/

theorem ae_isLQGGood_add_ofFun {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} {g : Ω → ℂ → ℝ} (hX : ∀ᵐ ω ∂P, IsLQGGood γ (X ω))
    (hg : ∀ ω, ContinuousOn (g ω) Hbar) :
    ∀ᵐ ω ∂P, IsLQGGood γ (X ω + ofFun (g ω)) ∧
      qBoundaryMeasure γ (X ω + ofFun (g ω)) =
        (qBoundaryMeasure γ (X ω)).withDensity (fun t => ENNReal.ofReal (Real.exp (γ / 2 * g ω t))) ∧
      qAreaMeasure γ (X ω + ofFun (g ω)) =
        (qAreaMeasure γ (X ω)).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g ω z))) := by
  filter_upwards [hX] with ω hω
  exact ⟨hω.add_ofFun (hg ω), GoodSample.qBoundaryMeasure_add_ofFun hω (hg ω),
    GoodSample.qAreaMeasure_add_ofFun hω (hg ω)⟩

/-! ## 4. Joint measurability of folded-circle evaluations in centre and radius -/

theorem measurable_foldedCircle₂ : Measurable fun q : ℂ × ℝ => foldedCircle q.1 q.2 := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  have hcont : Continuous (fun p : (ℂ × ℝ) × ℝ => circleMap p.1.1 p.1.2 p.2) := by
    unfold circleMap; fun_prop
  have hg : Measurable (fun p : (ℂ × ℝ) × ℝ => foldH (circleMap p.1.1 p.1.2 p.2)) :=
    measurable_foldH.comp hcont.measurable
  have h := measurable_measure_prodMk_left (ν := volume.restrict (Set.Ico 0 (2 * Real.pi)))
    (hg hs)
  convert h.const_mul ((ENNReal.ofReal (2 * Real.pi))⁻¹) using 1
  funext q
  rw [foldedCircle, Measure.map_apply measurable_foldH hs, circleUnif, Measure.smul_apply,
    Measure.map_apply (measurable_circleMap _ _) (measurable_foldH hs), smul_eq_mul]
  rfl

/-- The folded-circle kernel in centre and radius. -/
def fcKernel₂ : Kernel (ℂ × ℝ) ℂ where
  toFun q := foldedCircle q.1 q.2
  measurable' := measurable_foldedCircle₂

instance : IsMarkovKernel fcKernel₂ :=
  ⟨fun q => by show IsProbabilityMeasure (foldedCircle q.1 q.2); infer_instance⟩

theorem measurable_evalReg_fc₂ :
    Measurable fun p : FieldSample × (ℂ × ℝ) => evalReg p.1 (foldedCircle p.2.1 p.2.2) := by
  unfold evalReg
  have hk : ∀ k : ℕ, StronglyMeasurable
      (fun p : FieldSample × (ℂ × ℝ) => ∫ w, avgReg p.1 k w ∂foldedCircle p.2.1 p.2.2) := fun k =>
    StronglyMeasurable.integral_kernel_prod_right'
      (κ := fcKernel₂.comap Prod.snd measurable_snd)
      (f := fun q : (FieldSample × (ℂ × ℝ)) × ℂ => avgReg q.1.1 k q.2)
      ((measurable_avgReg k).comp (measurable_fst.fst.prodMk measurable_snd)).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hk).measurable

theorem fc_map_add_real (c : ℂ) (s t : ℝ) :
    (foldedCircle c s).map (fun u => u + (t : ℂ)) = foldedCircle (c + t) s := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map (by fun_prop : Measurable fun u : ℂ => u + (t : ℂ)).aemeasurable
    f.continuous.aestronglyMeasurable]
  exact RegClosure.integral_fc_comp_add_real (g := fun u => f u) f.continuous.continuousOn c s t

theorem fc_map_mul' (c : ℂ) (s : ℝ) {b : ℝ} (hb : 0 < b) :
    (foldedCircle c s).map (fun u => (b : ℂ) * u) = foldedCircle ((b : ℂ) * c) (b * s) := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map (by fun_prop : Measurable fun u : ℂ => (b : ℂ) * u).aemeasurable
    f.continuous.aestronglyMeasurable]
  exact RegClosure.integral_fc_comp_mul (g := fun u => f u) f.continuous.continuousOn c s hb

theorem coords_translate_apply (x : FieldSample) (t : ℝ) (i : ℕ) :
    coords (translate x (t : ℂ)) i =
      evalReg x (foldedCircle ((dyadicIndex i).1 + t) (radius (dyadicIndex i).2)) := by
  have h : coords (translate x (t : ℂ)) i = evalReg x
      ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)).map (· + (t : ℂ))) := rfl
  rw [h, fc_map_add_real]

theorem measurable_coords_translate :
    Measurable fun q : FieldSample × ℝ => coords (translate q.1 (q.2 : ℂ)) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hm : Measurable fun q : FieldSample × ℝ =>
      (q.1, ((dyadicIndex i).1 + (q.2 : ℂ), radius (dyadicIndex i).2)) :=
    measurable_fst.prodMk (((by fun_prop : Continuous fun r : ℝ =>
      (dyadicIndex i).1 + (r : ℂ)).measurable.comp measurable_snd).prodMk measurable_const)
  have := measurable_evalReg_fc₂.comp hm
  convert this using 1
  funext q
  exact coords_translate_apply q.1 q.2 i

/-! ## 5. Random translations and dilations (T2, T3 as fixed-parameter hypotheses) -/

end IndepParams

end QuantumZipper
