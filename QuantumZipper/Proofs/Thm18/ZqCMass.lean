import QuantumZipper.Proofs.Thm18.ZqCAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (4): the window length as a functional of the circle averages in the unit disc

The Palm identity of the wedge (`ZqCPalmFor`) only accepts functionals of countably many folded
circle averages `h(fc(c_j, r_j))` with `fc(c_j, r_j)` inside the unit disc. Here:

* `recF`: the field rebuilt from the dyadic folded circles inside the unit disc (the other
  dyadic circles read `0`), `vOf y` the values of `y` on the circles `fc(cJ j, rJ j)`;
* `avgReg_recF`: at real points `|t| ≤ 3/4` and small radii the regularized circle averages of
  `recF (vOf y)` are those of `y` (only the tail of the dyadic roundings matters);
* `locLen_recF`: hence the local boundary length `G2PalmLoc.locLen` of a segment inside
  `[−3/4, 3/4]` is the same for `y` and `recF (vOf y)`;
* `winLen_eq_locLen`: the restriction to the circles missing `B(x, δ/4)` does not change the
  local length of the shifted window segment (for every sample; `lintegral_trap_restrict_eq`);
* `measurable_locLen_recF`: the length is jointly measurable in (circle data, endpoints).

Duplantier–Sheffield, arXiv:0808.1560, §3 (the boundary measure is a limit of functionals of
the circle averages near the segment). Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open Factorization G2PalmLoc

/-- The dyadic folded circle of index `j` lies in the closed upper unit disc. -/
def fitJ (j : ℕ) : Prop :=
  (dyadicIndex j).1 ∈ Hbar ∧ ‖(dyadicIndex j).1‖ + radius (dyadicIndex j).2 < 1

open Classical in
/-- The centres of the Palm circles. -/
def cJ (j : ℕ) : ℂ := if fitJ j then (dyadicIndex j).1 else 0

open Classical in
/-- The radii of the Palm circles. -/
def rJ (j : ℕ) : ℝ := if fitJ j then radius (dyadicIndex j).2 else 1 / 2

theorem cJ_mem (j : ℕ) : cJ j ∈ Hbar := by
  classical
  unfold cJ
  split_ifs with h
  · exact h.1
  · show (0 : ℝ) ≤ (0 : ℂ).im; simp

theorem rJ_pos (j : ℕ) : 0 < rJ j := by
  classical
  unfold rJ
  split_ifs
  · exact radius_pos _
  · norm_num

theorem cJ_ball (j : ℕ) : closedBall (cJ j) (rJ j) ∩ Hbar ⊆ ball (0 : ℂ) 1 := by
  classical
  intro z hz
  have hz1 := hz.1
  rw [mem_closedBall, dist_eq_norm] at hz1
  rw [mem_ball, dist_zero_right]
  have h := norm_sub_norm_le z (cJ j)
  unfold cJ rJ at *
  split_ifs at hz1 h with hf
  · linarith [hf.2]
  · simp only [norm_zero, sub_zero] at hz1 h; linarith

open Classical in
/-- The field rebuilt from the values on the dyadic folded circles inside the unit disc. -/
def recF (v : ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ j, fitJ j ∧ foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2) = μ
  then v (Nat.find h) else 0

theorem measurable_recF : Measurable recF := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  unfold recF
  by_cases h : ∃ j, fitJ j ∧ foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2) = μ
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

/-- The values of a field on the Palm circles. -/
def vOf (y : FieldSample) : ℕ → ℝ := fun j => y (foldedCircle (cJ j) (rJ j))

theorem recF_vOf_apply (y : FieldSample) {j : ℕ} (hj : fitJ j) :
    recF (vOf y) (foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2)) =
      y (foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2)) := by
  classical
  have h : ∃ i, fitJ i ∧ foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) =
      foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2) := ⟨j, hj, rfl⟩
  unfold recF
  rw [dif_pos h]
  have hs := Nat.find_spec h
  unfold vOf cJ rJ
  rw [if_pos hs.1, if_pos hs.1, hs.2]

theorem avgReg_recF (y : FieldSample) {k : ℕ} (hk : radius k ≤ 1 / 8) {t : ℝ}
    (ht : |t| ≤ 3 / 4) : avgReg (recF (vOf y)) k (t : ℂ) = avgReg y k (t : ℂ) := by
  have hev : ∀ᶠ n in atTop, recF (vOf y) (foldedCircle (dyadicRoundC n (t : ℂ)) (radius k)) =
      y (foldedCircle (dyadicRoundC n (t : ℂ)) (radius k)) := by
    filter_upwards [eventually_ge_atTop 5] with n hn
    obtain ⟨j, hj⟩ := dyadicIndex_surj n k (t : ℂ)
    have hdz := CircleCont.norm_dyadicRoundC_sub_le n (t : ℂ)
    have hpow : (2 : ℝ) ^ 5 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have h2 : 2 * (1 / 2 ^ n : ℝ) ≤ 1 / 16 := by
      have : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ 5 := one_div_le_one_div_of_le (by positivity) hpow
      norm_num at this ⊢; linarith
    have hnorm : ‖dyadicRoundC n (t : ℂ)‖ ≤ 3 / 4 + 1 / 16 := by
      have := norm_sub_norm_le (dyadicRoundC n (t : ℂ)) (t : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have hfit : fitJ j := by
      unfold fitJ
      rw [hj]
      exact ⟨Positivity.dyadicRoundC_mem_Hbar n (by simp [Hbar]), by simp only; linarith⟩
    have := recF_vOf_apply y hfit
    rw [hj] at this
    exact this
  unfold avgReg limUnder
  rw [Filter.map_congr hev]

theorem locLen_recF (γ : ℝ) (y : FieldSample) {a b w : ℝ} (hw : 0 < w)
    (ha : -(3 / 4) ≤ a - w) (hb : b + w ≤ 3 / 4) :
    locLen γ (recF (vOf y)) a b w = locLen γ y a b w := by
  unfold locLen
  refine iInf_congr fun j => ?_
  have hδ : 0 < w / (j + 1) := div_pos hw (Nat.cast_add_one_pos j)
  have hδw : w / (j + 1) ≤ w :=
    div_le_self hw.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hr : ∀ᶠ k in atTop, radius k ≤ 1 / 8 :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (ge_mem_nhds (by norm_num))
  refine liminf_congr ?_
  filter_upwards [hr] with k hk
  rw [G3Fid.bdryApprox_eq_bDens, G3Fid.bdryApprox_eq_bDens,
    lintegral_withDensity_eq_lintegral_mul _ (G3Fid.measurable_bDens _ _ _)
      (measurable_ofReal_trap _ a b),
    lintegral_withDensity_eq_lintegral_mul _ (G3Fid.measurable_bDens _ _ _)
      (measurable_ofReal_trap _ a b)]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ Ioo (a - w / (j + 1)) (b + w / (j + 1))
  · have ht' : |t| ≤ 3 / 4 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp only [Pi.mul_apply, G3Fid.bDens, avgReg_recF y hk ht']
  · simp only [Pi.mul_apply, trap_eq_zero hδ ht, ENNReal.ofReal_zero, mul_zero]

/-- **The restriction to the circles missing `B(x, δ/4)` does not change the window length.** -/
theorem winLen_eq_locLen (γ : ℝ) (left : Bool) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) (y : FieldSample) :
    winLen γ left δ x y = locLen γ y (segLo left δ x) (segHi left δ x) (δ / 4) := by
  unfold winLen locLen
  refine iInf_congr fun j => ?_
  have hw : 0 < δ / 4 := by positivity
  have hδ' : 0 < δ / 4 / (j + 1) := div_pos hw (Nat.cast_add_one_pos j)
  have hδw : δ / 4 / (j + 1) ≤ δ / 4 :=
    div_le_self hw.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hr : ∀ᶠ k in atTop, radius k ≤ δ / 4 :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds hw)
  refine liminf_congr ?_
  filter_upwards [hr] with k hk
  exact lintegral_trap_restrict_eq γ y hδ' hδw (seg_far left hδ) hk

theorem continuous_trap_joint (w : ℝ) :
    Continuous fun p : ℝ × ℝ × ℝ => trap w p.1 p.2.1 p.2.2 := by
  unfold trap; fun_prop

/-- **The window length is jointly measurable in (circle data, endpoints).** -/
theorem measurable_locLen_recF (γ w : ℝ) :
    Measurable fun q : (ℕ → ℝ) × ℝ × ℝ => locLen γ (recF q.1) q.2.1 q.2.2 w := by
  unfold locLen
  refine Measurable.iInf fun j => Measurable.liminf fun k => ?_
  have e : (fun q : (ℕ → ℝ) × ℝ × ℝ => ∫⁻ t, ENNReal.ofReal (trap (w / (j + 1)) q.2.1 q.2.2 t)
      ∂bdryApprox γ (recF q.1) k) = fun q => ∫⁻ t, G3Fid.bDens γ (recF q.1) k t *
        ENNReal.ofReal (trap (w / (j + 1)) q.2.1 q.2.2 t) := by
    funext q
    rw [G3Fid.bdryApprox_eq_bDens, lintegral_withDensity_eq_lintegral_mul _
      (G3Fid.measurable_bDens _ _ _) (measurable_ofReal_trap _ _ _)]
    rfl
  rw [e]
  refine Measurable.lintegral_prod_right' (f := fun p : ((ℕ → ℝ) × ℝ × ℝ) × ℝ =>
    G3Fid.bDens γ (recF p.1.1) k p.2 * ENNReal.ofReal (trap (w / (j + 1)) p.1.2.1 p.1.2.2 p.2)) ?_
  refine (show Measurable fun p : ((ℕ → ℝ) × ℝ × ℝ) × ℝ => G3Fid.bDens γ (recF p.1.1) k p.2
    from ?_).mul (show Measurable fun p : ((ℕ → ℝ) × ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (trap (w / (j + 1)) p.1.2.1 p.1.2.2 p.2) from ?_)
  · unfold G3Fid.bDens
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul ?_)))
    exact (measurable_avgReg k).comp ((measurable_recF.comp (measurable_fst.comp measurable_fst)).prodMk
      (Complex.measurable_ofReal.comp measurable_snd))
  · refine ENNReal.measurable_ofReal.comp ?_
    exact (continuous_trap_joint _).measurable.comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))

end ZqC
end Thm18Asm
end QuantumZipper
