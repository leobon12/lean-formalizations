import QuantumZipper.Proofs.Section5.Prop17PalmCAgree
import QuantumZipper.Proofs.Section5.Prop17PalmCLog
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame

/-!
# Proposition 1.7, Palm-zoom node C: the regularity node is proved (PALM-C)

`prop17PalmCRegStmt_holds : Prop17PalmCRegStmt γ`. For real `x` the Palm-shifted field is
*exactly* `ofFun F + X̃ ω` with `F v = −γ log‖v − x‖ + γ(log 3 + log⁺(‖v‖/3))` (`G` continuous,
by the closed form of `kPot (foldedCircle 0 3)`) and `X̃ ω = addConst (X ω) (c ω)`, a free field
with a random additive constant (`isFreeGFFModConstH_addConst`: the balanced increments do not
see the constant). Folded circles are Frostman (`Cor15Group.isFrostman_fc`), and translating a
folded circle by a real number gives a folded circle (`palmC_fc_map_add_real`), so RC1 with a
logarithmic singularity at the real point `x` (`palmC_ae_evalReg_logAdd`) gives regularity at each
translated dyadic folded circle; there are countably many. Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift PalmNorm

/-- A random additive constant does not change the free field modulo constants. -/
theorem isFreeGFFModConstH_addConst {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} (hX : IsFreeGFFModConstH X P) {c : Ω → ℝ} (hc : Measurable c) :
    IsFreeGFFModConstH (fun ω => addConst (X ω) (c ω)) P := by
  have hdiff : ∀ μ ν : Measure ℂ, μ Set.univ = ν Set.univ → ∀ ω,
      addConst (X ω) (c ω) μ - addConst (X ω) (c ω) ν = X ω μ - X ω ν := by
    intro μ ν h ω
    simp only [addConst, h]
    ring
  refine
    { measurable_coord := fun μ => (hX.measurable_coord μ).add (hc.mul_const _)
      gaussian := ?_
      centered := fun μ ν hμ hν h => by
        simp_rw [hdiff μ ν h]
        exact hX.centered μ ν hμ hν h
      covariance_eq := fun p q hp1 hp2 hp hq1 hq2 hq => by
        have e1 : (fun ω => addConst (X ω) (c ω) p.1 - addConst (X ω) (c ω) p.2) =
            fun ω => X ω p.1 - X ω p.2 := funext (hdiff p.1 p.2 hp)
        have e2 : (fun ω => addConst (X ω) (c ω) q.1 - addConst (X ω) (c ω) q.2) =
            fun ω => X ω q.1 - X ω q.2 := funext (hdiff q.1 q.2 hq)
        rw [e1, e2]
        exact hX.covariance_eq p q hp1 hp2 hp hq1 hq2 hq
      linear := fun μ ν hμ hν a b => ?_ }
  · have e : (fun (p : {p : Measure ℂ × Measure ℂ //
          IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}) (ω : Ω) =>
        addConst (X ω) (c ω) p.1.1 - addConst (X ω) (c ω) p.1.2) =
        fun p ω => X ω p.1.1 - X ω p.1.2 := by
      funext p ω; exact hdiff _ _ p.2.2.2 ω
    rw [e]
    exact hX.gaussian
  · have := hμ.1
    have := hν.1
    filter_upwards [hX.linear μ ν hμ hν a b] with ω hω
    simp only [addConst, hω, Measure.add_apply, Measure.smul_apply]
    rw [show a • μ univ = (a : ℝ≥0∞) * μ univ from rfl,
      show b • ν univ = (b : ℝ≥0∞) * ν univ from rfl]
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
    ring

theorem palmC_foldH_add_real (w : ℂ) (t : ℝ) : foldH (w + t) = foldH w + t := by
  unfold foldH
  have him : (w + (t : ℂ)).im = w.im := by simp
  rw [him]
  split_ifs
  · rfl
  · rw [map_add, Complex.conj_ofReal]

theorem palmC_fc_map_add_real (d : ℂ) (r t : ℝ) :
    (foldedCircle d r).map (· + (t : ℂ)) = foldedCircle (d + t) r := by
  unfold foldedCircle
  rw [Measure.map_map (measurable_add_const _) measurable_foldH]
  have e : ((· + (t : ℂ)) ∘ foldH) = foldH ∘ (· + (t : ℂ)) := by
    funext w; simp only [Function.comp, palmC_foldH_add_real]
  rw [e, ← Measure.map_map measurable_foldH (measurable_add_const _)]
  congr 1
  unfold circleUnif
  rw [Measure.map_smul, Measure.map_map (measurable_add_const _) (measurable_circleMap _ _)]
  swap; · exact (measurable_add_const _).aemeasurable
  congr 2
  funext θ
  simp only [Function.comp, circleMap]
  ring

/-- The continuous part `G v = γ(log 3 + log⁺(‖v‖/3))` of the Palm shift. -/
def palmCG (γ : ℝ) (v : ℂ) : ℝ := γ * (Real.log 3 + Real.posLog (3⁻¹ * ‖v‖))

theorem continuous_palmCG (γ : ℝ) : Continuous (palmCG γ) := by
  unfold palmCG; fun_prop

theorem shiftFun_eq_logAdd (γ x : ℝ) :
    shiftFun γ (0 : ℂ → ℝ) (foldedCircle 0 3) x =
      fun v => -γ * Real.log ‖v - (x : ℂ)‖ + palmCG γ v := by
  funext v
  have h1 : ‖(x : ℂ) - conj v‖ = ‖v - (x : ℂ)‖ := by
    rw [show (x : ℂ) - conj v = conj ((x : ℂ) - v) by rw [map_sub, Complex.conj_ofReal],
      Complex.norm_conj, norm_sub_rev]
  simp only [shiftFun, Pi.zero_apply, neumannH, kPot_foldedCircle_three_eq, palmCG, h1,
    norm_sub_rev (x : ℂ) v]
  ring

/-- The random constant of the Palm field. -/
def palmCConst (γ x : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : ℝ :=
  -((ofFun (shiftFun γ (0 : ℂ → ℝ) (foldedCircle 0 3) x) + X ω) (foldedCircle 0 3))

theorem palmFreeField_eq_logAdd (γ x : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) :
    palmFreeField γ (foldedCircle 0 3) X x ω =
      ofFun (fun v => -γ * Real.log ‖v - (x : ℂ)‖ + palmCG γ v) +
        addConst (X ω) (palmCConst γ x X ω) := by
  funext μ
  simp only [palmFreeField, normAt, palmCConst, addConst, Pi.add_apply]
  rw [shiftFun_eq_logAdd]
  ring

/-- **The regularity node holds.** -/
theorem prop17PalmCRegStmt_holds (γ : ℝ) : Prop17PalmCRegStmt γ := by
  intro Ω' _ P' X hP hX x _
  have hc : Measurable (palmCConst γ x X) :=
    ((hX.measurable_coord _).const_add _).neg
  have hX' := isFreeGFFModConstH_addConst hX hc
  -- countably many centres
  set S : Set ℂ := ⋃ n : ℕ, Set.range (dyadicRoundC n) with hS
  have hSc : S.Countable := by
    refine Set.countable_iUnion fun n => ?_
    refine (Set.countable_range
      (fun p : ℤ × ℤ => (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ))).mono ?_
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
  have key : ∀ d : ℂ, ∀ k : ℕ, ∀ᵐ ω ∂P',
      evalReg (palmFreeField γ (foldedCircle 0 3) X x ω)
        ((foldedCircle d (radius k)).map (· + (x : ℂ))) =
      palmFreeField γ (foldedCircle 0 3) X x ω
        ((foldedCircle d (radius k)).map (· + (x : ℂ))) := by
    intro d k
    have hr := radius_pos k
    rw [palmC_fc_map_add_real]
    have hsupp : foldedCircle (d + x) (radius k)
        (Metric.closedBall 0 (‖d + (x : ℂ)‖ + radius k) ∩ Hbar)ᶜ = 0 :=
      CircleFubini.foldedCircle_support hr.le le_rfl
    filter_upwards [palmC_ae_evalReg_logAdd hX' hsupp (Cor15Group.isFrostman_fc _ hr) one_pos
      (-γ) x (continuous_palmCG γ).continuousOn] with ω hω
    rw [palmFreeField_eq_logAdd, hω]
    rfl
  have hall : ∀ᵐ ω ∂P', ∀ d ∈ S, ∀ k : ℕ,
      evalReg (palmFreeField γ (foldedCircle 0 3) X x ω)
        ((foldedCircle d (radius k)).map (· + (x : ℂ))) =
      palmFreeField γ (foldedCircle 0 3) X x ω
        ((foldedCircle d (radius k)).map (· + (x : ℂ))) :=
    (ae_ball_iff hSc).2 fun d _ => ae_all_iff.2 fun k => key d k
  filter_upwards [hall] with ω hω n k z
  exact hω _ (Set.mem_iUnion.2 ⟨n, z, rfl⟩) k

end Raw
end FieldLaw
end S5
end QuantumZipper
