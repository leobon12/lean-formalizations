import QuantumZipper.Proofs.Thm18.G3Pl4Sep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): `G3PlPhiUnscaledStmt` holds

The two boundary-length inputs of `g3pl4_unscaled_of_sep`, proved by transfer to `h_C`:

* (I3) `g3pl4_hC_sepBad_small`: for `h_C`, `P(ν[−δ, 0] ≥ ν[−1/2, 0] or ν[−δ, 0] > ν[0, 1/4]) → 0` as
  `δ → 0` (a.s. `ν_C` has no atom at `0` and positive mass on `(−1/2, 0)`, `(0, 1/4)`; dominated
  convergence);
* (I4) `g3pl_exists_U₀` (G3PlMain).

Both events only read the boundary measure on `[−1/2, 1/2]`, where the unscaled wedge and the
coupled field `V + log` agree a.s.; `V + log` and `h_C` have the same law of circle coordinates
(`g3pl4_coordsLaw_eq`). Sheffield, arXiv:1012.4797, §5.1 p. 61 (positivity) and pp. 71–72.
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

open Classical in
/-- The indicator that the separation conditions fail. -/
def g3pl4SepBad (δ : ℝ) (ν : Measure ℝ) : ℝ≥0∞ :=
  if ν (Icc (-δ) 0) < ν (Icc (-(1 / 2)) 0) ∧ ν (Icc (-δ) 0) ≤ ν (Icc 0 (1 / 4)) then 0 else 1

theorem measurable_g3pl4SepBad (δ : ℝ) : Measurable (g3pl4SepBad δ) := by
  classical
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt (Measure.measurable_coe measurableSet_Icc)
    (Measure.measurable_coe measurableSet_Icc)).inter
    (measurableSet_le (Measure.measurable_coe measurableSet_Icc)
      (Measure.measurable_coe measurableSet_Icc))

theorem g3pl4SepBad_01 (δ : ℝ) (ν : Measure ℝ) : g3pl4SepBad δ ν = 0 ∨ g3pl4SepBad δ ν = 1 := by
  unfold g3pl4SepBad; split_ifs <;> simp

theorem g3pl4SepBad_le_one (δ : ℝ) (ν : Measure ℝ) : g3pl4SepBad δ ν ≤ 1 := by
  rcases g3pl4SepBad_01 δ ν with h | h <;> rw [h]; exact zero_le_one

theorem g3pl4BadE_01 (δ U : ℝ) (ν : Measure ℝ) : g3plBadE δ U ν = 0 ∨ g3plBadE δ U ν = 1 := by
  unfold g3plBadE; split_ifs <;> simp

/-- **(I3) for `h_C`.** -/
theorem g3pl4_hC_sepBad_small {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ∫⁻ ω, g3pl4SepBad δ (g3plV γ ω) ∂gffBase.P ≤ ENNReal.ofReal η := by
  have := gffBase.prob
  set d : ℕ → ℝ := fun n => 3 * ((1 / 12) / ((n : ℝ) + 1)) with hd
  have hT : Tendsto (fun n => ∫⁻ ω, g3pl4SepBad (d n) (g3plV γ ω) ∂gffBase.P) atTop
      (𝓝 (∫⁻ _ω, (0 : ℝ≥0∞) ∂gffBase.P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => 1)
      (Eventually.of_forall fun n =>
        (measurable_g3pl4SepBad _).comp_aemeasurable (aemeasurable_g3plV hγ hγ2))
      (Eventually.of_forall fun n => ae_of_all _ fun ω => g3pl4SepBad_le_one _ _) ?_ ?_
    · rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.one_ne_top
    · filter_upwards [ae_g3pField_good hγ hγ2, ae_g3plV_Ioo_pos hγ hγ2] with ω hgood hpos
      set ν := g3plV γ ω with hν
      have hfin : ∀ a b : ℝ, ν (Icc a b) ≠ ⊤ := fun a b =>
        (qBoundaryMeasure_Icc_lt_top γ _ a b).ne
      have h0 : ν {0} = 0 := hgood.2.2.1 0
      have hsm := (g3pl_tendsto_small ν hfin h0 (c := 1 / 12) (by norm_num)).1
      have hp1 : 0 < ν (Ioo (-(1 / 2)) 0) := hpos _ _ (by norm_num) (Or.inr le_rfl)
      have hp2 : 0 < ν (Ioo 0 (1 / 4)) := hpos _ _ (by norm_num) (Or.inl le_rfl)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_order.1 hsm).2 _ (lt_min hp1 hp2)] with n hn
      have hn' : ν (Icc (-d n) 0) < min (ν (Ioo (-(1 / 2)) 0)) (ν (Ioo 0 (1 / 4))) := hn
      have h1 : ν (Icc (-d n) 0) < ν (Icc (-(1 / 2)) 0) :=
        (hn'.trans_le (min_le_left _ _)).trans_le (measure_mono Ioo_subset_Icc_self)
      have h2 : ν (Icc (-d n) 0) ≤ ν (Icc 0 (1 / 4)) :=
        (hn'.le.trans (min_le_right _ _)).trans (measure_mono Ioo_subset_Icc_self)
      unfold g3pl4SepBad
      rw [if_pos ⟨h1, h2⟩]
  rw [lintegral_zero] at hT
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hT).2 _ (ENNReal.ofReal_pos.2 hη)).exists
  refine ⟨d n, by positivity, ?_, hn.le⟩
  have : (0 : ℝ) ≤ n := n.cast_nonneg
  simp only [hd]
  rw [div_div, mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end R18
end QuantumZipper
