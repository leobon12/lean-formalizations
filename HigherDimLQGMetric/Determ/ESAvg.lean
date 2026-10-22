import HigherDimLQGMetric.Determ.L53Joint
import LQGMetric.Papers.LM.T1_7V14

/-! Efron–Stein averaged over translated grids. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

def determES (ε R : ℝ) (F : ContMetric dim → ℝ)
    (Φ : (Fin dim → ℝ) × (determFixedBox (d := dim) ε R → ℕ → ℝ≥0∞) → ℝ) (ν : Measure (ContMetric dim)) (θ : Fin dim → ℝ)
    (d : ContMetric dim) : ℝ≥0∞ :=
  ∑ k, ∫⁻ d', ENNReal.ofReal (max (Φ (θ, Function.update (determY ε θ (determFixedBox (d := dim) ε R) d) k
    (determY ε θ (determFixedBox (d := dim) ε R) d' k)) - F d) 0 ^ 2) ∂ν

lemma determ_measurable_ES (ε R : ℝ) {F : ContMetric dim → ℝ} (hF : Measurable F)
    {Φ : (Fin dim → ℝ) × (determFixedBox (d := dim) ε R → ℕ → ℝ≥0∞) → ℝ} (hΦ : Measurable Φ) (ν : Measure (ContMetric dim))
    [IsFiniteMeasure ν] :
    Measurable fun p : (Fin dim → ℝ) × ContMetric dim => determES ε R F Φ ν p.1 p.2 := by
  unfold determES
  refine Finset.measurable_sum _ fun k _ => ?_
  have hY := determ_measurable_gridY ε (determFixedBox (d := dim) ε R)
  have h1 : Measurable fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim =>
      Function.update (determY ε q.1.1 (determFixedBox (d := dim) ε R) q.1.2) k (determY ε q.1.1 (determFixedBox (d := dim) ε R) q.2 k) :=
    (LQGMetric.LM.t17v_measurable_update k).comp ((hY.comp measurable_fst).prodMk
      (hY.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  have h2 : Measurable fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim => ENNReal.ofReal
      (max (Φ (q.1.1, Function.update (determY ε q.1.1 (determFixedBox (d := dim) ε R) q.1.2) k
        (determY ε q.1.1 (determFixedBox (d := dim) ε R) q.2 k)) - F q.1.2) 0 ^ 2) :=
    ENNReal.measurable_ofReal.comp ((((hΦ.comp ((measurable_fst.comp measurable_fst).prodMk h1)).sub
      (hF.comp (measurable_snd.comp measurable_fst))).max measurable_const).pow_const 2)
  exact h2.lintegral_prod_right'

/-- **Step 1 averaged over `θ`** -/
theorem determ_es_avg (ν : Measure (ContMetric dim)) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 ≤ C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd dim, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    {m : ℕ} {R : ℝ} (hmR : (m : ℝ) ≤ R) {z w : Rd dim} (hz : ‖z‖ < m) (hw : ‖w‖ < m)
    {ε : ℝ} (hε : 0 < ε)
    (hprod : ∀ᵐ θ ∂(volume : Measure (Fin dim → ℝ)), ν.map (determY ε θ (determFixedBox (d := dim) ε R)) =
      Measure.pi fun k : determFixedBox (d := dim) ε R => ν.map (determ_enc (determCube ε θ k)))
    (hF2 : MemLp (fun d => (determF m z w d).toReal) 2 ν) :
    ∃ Φ : (Fin dim → ℝ) × (determFixedBox (d := dim) ε R → ℕ → ℝ≥0∞) → ℝ, Measurable Φ ∧
      (∀ᵐ θ ∂(determShiftLaw dim), ∀ᵐ d ∂ν, (determF m z w d).toReal = Φ (θ, determY ε θ (determFixedBox (d := dim) ε R) d)) ∧
      ∃ K : Kernel ((Fin dim → ℝ) × (determFixedBox (d := dim) ε R → ℕ → ℝ≥0∞)) (ContMetric dim), IsMarkovKernel K ∧
        (∀ᵐ θ ∂(determShiftLaw dim), (ν.map (determY ε θ (determFixedBox (d := dim) ε R))) ⊗ₘ
            (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) =
          ν.map fun d => (determY ε θ (determFixedBox (d := dim) ε R) d, d)) ∧
        ENNReal.ofReal (∫ d, ((determF m z w d).toReal -
            ∫ d', (determF m z w d').toReal ∂ν) ^ 2 ∂ν) ≤
          ∫⁻ d, ∫⁻ θ, determES ε R (fun d => (determF m z w d).toReal) Φ ν θ d ∂(determShiftLaw dim) ∂ν := by
  letI : Nonempty (ContMetric dim) := nonempty_of_isProbabilityMeasure ν
  set s := determFixedBox (d := dim) ε R
  set F : ContMetric dim → ℝ := fun d => (determF m z w d).toReal with hFdef
  have hFm : Measurable F := (determ_measurableF m z w).ennreal_toReal
  have hY := determ_measurable_gridY ε s
  set Ŷ : (Fin dim → ℝ) × ContMetric dim → (Fin dim → ℝ) × (s → ℕ → ℝ≥0∞) := fun p => (p.1, determY ε p.1 s p.2)
  have hŶ : Measurable Ŷ := measurable_fst.prodMk hY
  obtain ⟨Φ, hΦ, hFΦ⟩ := determ_l53_joint ν hL hC hcopy hmR hz hw hε
  have h1 : ∀ᵐ θ ∂(determShiftLaw dim), ∀ᵐ d ∂ν, F d = Φ (θ, determY ε θ s d) :=
    Measure.ae_ae_of_ae_prod hFΦ
  set K := condDistrib Prod.snd Ŷ ((determShiftLaw dim).prod ν)
  have hK : ((determShiftLaw dim).prod ν).map (fun p => ((p.1, determY ε p.1 s p.2), p.2)) =
      (((determShiftLaw dim).prod ν).map fun p => (p.1, determY ε p.1 s p.2)) ⊗ₘ K :=
    (compProd_map_condDistrib hŶ.aemeasurable measurable_snd.aemeasurable).symm
  have h2 := LQGMetric.LM.t17v_slice (determShiftLaw dim) ν (Y := fun p : (Fin dim → ℝ) × ContMetric dim => determY ε p.1 s p.2) hY K hK
  refine ⟨Φ, hΦ, h1, K, inferInstance, h2, ?_⟩
  -- Efron–Stein for a.e. `θ`, then average
  have hθ : ∀ᵐ θ ∂(determShiftLaw dim), ENNReal.ofReal (∫ d, (F d - ∫ d', F d' ∂ν) ^ 2 ∂ν) ≤
      ∫⁻ d, determES ε R F Φ ν θ d ∂ν := by
    filter_upwards [h1, ae_restrict_of_ae hprod] with θ hθ1 hθ2
    have hYθ : Measurable (determY ε θ s) := determ_measurable_Y ε θ s
    have hΦθ : Measurable fun y : s → ℕ → ℝ≥0∞ => Φ (θ, y) :=
      hΦ.comp (measurable_const.prodMk measurable_id)
    have hFθ : F =ᵐ[ν] (fun y : s → ℕ → ℝ≥0∞ => Φ (θ, y)) ∘ determY ε θ s := hθ1
    have key := LQGMetric.LM.t17v_es (ι := s) (E := ℕ → ℝ≥0∞) ν (Y := determY ε θ s) hYθ hθ2
      (F := F) (Φ := fun y => Φ (θ, y)) hΦθ hFm hFθ hF2
    exact key
  have hm := determ_measurable_ES ε R hFm hΦ ν
  calc ENNReal.ofReal (∫ d, (F d - ∫ d', F d' ∂ν) ^ 2 ∂ν)
      = ∫⁻ _θ, ENNReal.ofReal (∫ d, (F d - ∫ d', F d' ∂ν) ^ 2 ∂ν) ∂(determShiftLaw dim) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ θ, ∫⁻ d, determES ε R F Φ ν θ d ∂ν ∂(determShiftLaw dim) := lintegral_mono_ae hθ
    _ = ∫⁻ d, ∫⁻ θ, determES ε R F Φ ν θ d ∂(determShiftLaw dim) ∂ν :=
        lintegral_lintegral_swap (f := fun θ d => determES ε R F Φ ν θ d) hm.aemeasurable

end HigherDimLQGMetric
