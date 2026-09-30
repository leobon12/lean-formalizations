import QuantumZipper.Proofs.LQG.RegularSampleKolmogorov

/-!
# JOINTMOD, step 3 (deterministic): continuous extension from the dyadic points of `ℝ⁴`

A function `g : ℝ⁴ → ℝ` whose values at the dyadic points `lptD j a` are uniformly continuous on
every box (`UCD g`, a countable condition, hence a measurable event when `g` depends measurably
on a parameter) has the continuous extension `extD g q = lim_m g(rndD m q)` (`continuous_extD`).
If `g` agrees on the dyadic points with a continuous `Y`, then `UCD g` holds and `extD g = Y`
(`UCD_of_continuous`, `extD_eq_of_continuous`). Measurability in a parameter:
`measurableSet_UCD`, `measurable_extD`.

This is the transfer device of task JOINTMOD (as `RegCont.measurableSet_UCm` for REG-CONT): the
continuity of the modification is recorded as a measurable property of the values at countably
many parameters. **Own elementary argument** (uniform continuity on a dense set; standard).
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace QuantumZipper
namespace RegUnif

open KolmD

/-- Uniform continuity of `g` on the dyadic points of every box. -/
def UCD (g : (Fin 4 → ℝ) → ℝ) : Prop :=
  ∀ R n : ℕ, ∃ N : ℕ, ∀ (j j' : ℕ) (a a' : Fin 4 → ℤ), ‖lptD j a‖ ≤ R → ‖lptD j' a'‖ ≤ R →
    ‖lptD j a - lptD j' a'‖ ≤ 1 / 2 ^ N → |g (lptD j a) - g (lptD j' a')| ≤ 1 / ((n : ℝ) + 1)

/-- The extension along the dyadic roundings. -/
def extD (g : (Fin 4 → ℝ) → ℝ) (q : Fin 4 → ℝ) : ℝ := limUnder atTop fun m => g (rndD m q)

theorem one_div_two_pow_le_one (m : ℕ) : (1 : ℝ) / 2 ^ m ≤ 1 :=
  div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)

theorem one_div_two_pow_anti {m m' : ℕ} (h : m ≤ m') : (1 : ℝ) / 2 ^ m' ≤ 1 / 2 ^ m :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) h)

theorem norm_rndD_le (m : ℕ) (q : Fin 4 → ℝ) : ‖rndD m q‖ ≤ ‖q‖ + 1 := by
  have h1 := norm_rndD_sub_le m q
  have h2 := one_div_two_pow_le_one m
  calc ‖rndD m q‖ = ‖(rndD m q - q) + q‖ := by rw [sub_add_cancel]
    _ ≤ ‖rndD m q - q‖ + ‖q‖ := norm_add_le _ _
    _ ≤ ‖q‖ + 1 := by linarith

theorem norm_rndD_sub_rndD_le (m m' : ℕ) (q q' : Fin 4 → ℝ) :
    ‖rndD m q - rndD m' q'‖ ≤ ‖q - q'‖ + 1 / 2 ^ m + 1 / 2 ^ m' := by
  have h1 := norm_rndD_sub_le m q
  have h2 := norm_rndD_sub_le m' q'
  calc ‖rndD m q - rndD m' q'‖ = ‖(rndD m q - q) + (q - q') - (rndD m' q' - q')‖ := by
        congr 1; abel
    _ ≤ ‖(rndD m q - q) + (q - q')‖ + ‖rndD m' q' - q'‖ := norm_sub_le _ _
    _ ≤ ‖rndD m q - q‖ + ‖q - q'‖ + ‖rndD m' q' - q'‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖q - q'‖ + 1 / 2 ^ m + 1 / 2 ^ m' := by linarith

/-- The basic estimate behind the extension. -/
theorem UCD_step {g : (Fin 4 → ℝ) → ℝ} {R n N : ℕ}
    (hN : ∀ (j j' : ℕ) (a a' : Fin 4 → ℤ), ‖lptD j a‖ ≤ R → ‖lptD j' a'‖ ≤ R →
      ‖lptD j a - lptD j' a'‖ ≤ 1 / 2 ^ N → |g (lptD j a) - g (lptD j' a')| ≤ 1 / ((n : ℝ) + 1))
    {q q' : Fin 4 → ℝ} (hq : ‖q‖ + 1 ≤ R) (hq' : ‖q'‖ + 1 ≤ R) (hqq : ‖q - q'‖ ≤ 1 / 2 ^ (N + 1))
    {m m' : ℕ} (hm : N + 2 ≤ m) (hm' : N + 2 ≤ m') :
    |g (rndD m q) - g (rndD m' q')| ≤ 1 / ((n : ℝ) + 1) := by
  refine hN m m' _ _ ((norm_rndD_le m q).trans hq) ((norm_rndD_le m' q').trans hq') ?_
  have e1 := one_div_two_pow_anti (show N + 2 ≤ m from hm)
  have e2 := one_div_two_pow_anti (show N + 2 ≤ m' from hm')
  have e3 : (1 : ℝ) / 2 ^ (N + 1) = 1 / 2 ^ N / 2 := by rw [pow_succ]; field_simp
  have e4 : (1 : ℝ) / 2 ^ (N + 2) = 1 / 2 ^ N / 4 := by
    rw [pow_add]; norm_num; field_simp
  have := norm_rndD_sub_rndD_le m m' q q'
  show ‖rndD m q - rndD m' q'‖ ≤ _
  have hpos : (0 : ℝ) ≤ 1 / 2 ^ N := by positivity
  linarith

theorem exists_nat_lt_of_pos {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, 1 / ((n : ℝ) + 1) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact ⟨n, hn⟩

theorem tendsto_extD {g : (Fin 4 → ℝ) → ℝ} (hg : UCD g) (q : Fin 4 → ℝ) :
    Tendsto (fun m => g (rndD m q)) atTop (𝓝 (extD g q)) := by
  have hc : CauchySeq fun m => g (rndD m q) := by
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_lt_of_pos hε
    obtain ⟨R, hR⟩ := exists_nat_ge (‖q‖ + 1)
    obtain ⟨N, hN⟩ := hg R n
    refine ⟨N + 2, fun m hm => ?_⟩
    rw [Real.dist_eq]
    exact (UCD_step hN hR hR (by rw [sub_self, norm_zero]; positivity) hm le_rfl).trans_lt hn
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  rw [extD, hL.limUnder_eq]
  exact hL

theorem continuous_extD {g : (Fin 4 → ℝ) → ℝ} (hg : UCD g) : Continuous (extD g) := by
  refine Metric.continuous_iff.2 fun q ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_lt_of_pos hε
  obtain ⟨R, hR⟩ := exists_nat_ge (‖q‖ + 2)
  obtain ⟨N, hN⟩ := hg R n
  refine ⟨min 1 (1 / 2 ^ (N + 1)), by positivity, fun q' hq' => ?_⟩
  rw [dist_eq_norm] at hq'
  have hq'1 : ‖q' - q‖ < 1 := hq'.trans_le (min_le_left _ _)
  have hq'2 : ‖q' - q‖ ≤ 1 / 2 ^ (N + 1) := hq'.le.trans (min_le_right _ _)
  have hnq' : ‖q'‖ + 1 ≤ R := by
    have := norm_le_insert' q' q
    linarith [norm_sub_rev q' q]
  have hnq : ‖q‖ + 1 ≤ R := by linarith
  have hlim := ((tendsto_extD hg q').sub (tendsto_extD hg q)).abs
  have hle : |extD g q' - extD g q| ≤ 1 / ((n : ℝ) + 1) :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨N + 2, fun m hm =>
      UCD_step hN hnq' hnq hq'2 hm hm⟩)
  rw [Real.dist_eq]
  exact hle.trans_lt hn

theorem tendsto_rndD (q : Fin 4 → ℝ) : Tendsto (fun m => rndD m q) atTop (𝓝 q) := by
  have h2 : Tendsto (fun m : ℕ => (1 : ℝ) / 2 ^ m) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    exact this.congr fun m => by rw [one_div_pow]
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun m => norm_nonneg _)
    (fun m => norm_rndD_sub_le m q) h2)

theorem extD_eq_of_continuous {g Y : (Fin 4 → ℝ) → ℝ} (hY : Continuous Y)
    (h : ∀ (j : ℕ) (a : Fin 4 → ℤ), g (lptD j a) = Y (lptD j a)) (q : Fin 4 → ℝ) :
    extD g q = Y q := by
  have ht : Tendsto (fun m => g (rndD m q)) atTop (𝓝 (Y q)) :=
    ((hY.tendsto q).comp (tendsto_rndD q)).congr fun m => (h m (flr m q)).symm
  exact ht.limUnder_eq

theorem UCD_of_continuous {g Y : (Fin 4 → ℝ) → ℝ} (hY : Continuous Y)
    (h : ∀ (j : ℕ) (a : Fin 4 → ℤ), g (lptD j a) = Y (lptD j a)) : UCD g := by
  intro R n
  have hUC := (isCompact_closedBall (0 : Fin 4 → ℝ) R).uniformContinuousOn_of_continuous
    hY.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 hUC (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun j j' a a' ha ha' hd => ?_⟩
  rw [h, h]
  have hlt : (1 : ℝ) / 2 ^ N < δ := by rw [one_div, ← inv_pow]; exact hN
  have := hδ' _ (mem_closedBall_zero_iff.2 ha) _ (mem_closedBall_zero_iff.2 ha')
    (by rw [dist_eq_norm]; exact hd.trans_lt hlt)
  rw [Real.dist_eq] at this
  exact this.le

theorem measurableSet_UCD {α : Type*} [MeasurableSpace α] {G : α → (Fin 4 → ℝ) → ℝ}
    (hG : ∀ q, Measurable fun p => G p q) : MeasurableSet {p | UCD (G p)} := by
  have e : {p | UCD (G p)} = ⋂ R : ℕ, ⋂ n : ℕ, ⋃ N : ℕ, ⋂ j : ℕ, ⋂ j' : ℕ, ⋂ a : Fin 4 → ℤ,
      ⋂ a' : Fin 4 → ℤ, ⋂ (_ : ‖lptD j a‖ ≤ R), ⋂ (_ : ‖lptD j' a'‖ ≤ R),
        ⋂ (_ : ‖lptD j a - lptD j' a'‖ ≤ 1 / 2 ^ N),
          {p | |G p (lptD j a) - G p (lptD j' a')| ≤ 1 / ((n : ℝ) + 1)} := by
    ext p
    simp only [UCD, mem_ofPred_eq, mem_iInter, mem_iUnion]
  rw [e]
  refine MeasurableSet.iInter fun R => MeasurableSet.iInter fun n => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun j' => MeasurableSet.iInter fun a =>
    MeasurableSet.iInter fun a' => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => ?_
  exact measurableSet_le (continuous_abs.measurable.comp ((hG _).sub (hG _))) measurable_const

theorem measurable_extD {α : Type*} [MeasurableSpace α] {G : α → (Fin 4 → ℝ) → ℝ}
    (hG : ∀ q, Measurable fun p => G p q) (q : Fin 4 → ℝ) : Measurable fun p => extD (G p) q := by
  unfold extD
  exact (StronglyMeasurable.limUnder fun m => (hG (rndD m q)).stronglyMeasurable).measurable

end RegUnif
end QuantumZipper
