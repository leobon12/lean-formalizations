/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux4EntranceState
import InteractingSLE.Spec.Sec2.JacobiExistsPath
import BrownianMotion.Continuity.KolmogorovChentsovInequality

/-!
# Aux. lemma 4, V: a uniform Hölder bound for the Jacobi angle (Kolmogorov–Chentsov)

Packet PROVE-T14-DS3. Aux. lemma 4 (spec p. 28): "The fourth-moment estimate for stochastic integrals gives
`E|U_v − U_u|⁴ ≤ C(|v − u|² + |v − u|⁴)`. Consequently these stationary path laws are tight". For every solution of the
Jacobi martingale problem the quartic bound has the explicit constant `quartC κ a b` (`Aux4EntranceMoments`), so

* `jmp_isKolmogorovProcess`: the angle is a Kolmogorov process with exponents `(4, 2)` and constant `quartC`;
* `lintegral_holderSup_le`: on the interval `J_n = (−(n+1), n+1)`, the vendored Kolmogorov–Chentsov inequality
  (`countable_kolmogorov_chentsov`) bounds `E sup_{s,t ∈ J_n ∩ ℚ} |U_s − U_t|⁴ / |s − t|^{1/2}` by
  `quartC · L_n`, uniformly in the parameters through `quartC`;
* `abs_sub_le_of_holderSup_le`: on the event `{sup ≤ K}`, `|U_s − U_t| ≤ K^{1/4} |s − t|^{1/8}` on all of `J_n`
  (continuity of the paths).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace Aux4

open Sec2.Jacobi

variable {Ω : Type*} [MeasurableSpace Ω] {κ a b : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {U : ℝ → Ω → ℝ}

theorem quartC_nonneg (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ quartC κ a b := by
  unfold quartC; positivity

/-- The angle is a Kolmogorov process with exponents `(4, 2)` and constant `quartC κ a b`. -/
theorem jmp_isKolmogorovProcess (hU : IsJacobiMP κ a b P U) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsKolmogorovProcess U P 4 2 (quartC κ a b).toNNReal := by
  refine ⟨fun s t => ?_, fun s t => ?_, by norm_num, by norm_num⟩
  · rw [← BorelSpace.measurable_eq (α := ℝ × ℝ)]
    exact (hU.measurable s).prodMk (hU.measurable t)
  · have hint : Integrable (fun ω => (U t ω - U s ω) ^ 4) P := by
      refine Integrable.of_bound (((hU.measurable t).sub (hU.measurable s)).pow_const 4).aestronglyMeasurable
        1 (ae_of_all _ fun ω => ?_)
      have h1 := hU.mem_Icc t ω
      have h2 := hU.mem_Icc s ω
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩)
    have e : ∀ ω, edist (U s ω) (U t ω) ^ (4 : ℝ) = ENNReal.ofReal ((U t ω - U s ω) ^ 4) := by
      intro ω
      rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_abs, abs_of_nonneg (by positivity)]
      congr 1
      ring
    simp only [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)]
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hMe : (((quartC κ a b).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (quartC κ a b) := rfl
    rw [hMe, ← ENNReal.ofReal_mul (quartC_nonneg hκ ha hb)]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_total s t with hst | hst
    · exact (jmp_integral_pow_four_sub_le hU hκ ha hb hst).trans (le_of_eq (by ring))
    · have := jmp_integral_pow_four_sub_le hU hκ ha hb hst
      calc ∫ ω, (U t ω - U s ω) ^ 4 ∂P = ∫ ω, (U s ω - U t ω) ^ 4 ∂P := by
            congr 1; funext ω; ring
        _ ≤ quartC κ a b * (s - t) ^ 2 := this
        _ = _ := by ring

/-- The rational points of `J_n = (−(n+1), n+1)`. -/
def ratPts (n : ℕ) : Set ℝ := {x | x ∈ Ioo (-((n : ℝ) + 1)) (n + 1) ∧ x ∈ range ((↑) : ℚ → ℝ)}

instance (n : ℕ) : Countable (ratPts n) :=
  ((countable_range ((↑) : ℚ → ℝ)).mono fun _ h => h.2).to_subtype

/-- The Hölder supremum of exponent `1/8` (in the `4`-th power) over the rational points of `J_n`. -/
def holderSup (U : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ (s : ratPts n) (t : ratPts n), edist (U s ω) (U t ω) ^ (4 : ℝ) / edist s t ^ ((1 / 8 : ℝ) * 4)

/-- The constant of the Kolmogorov–Chentsov inequality on `J_n`. -/
def kcConst (n : ℕ) : ℝ≥0∞ := constL (3 * (2 * ((n : ℝ≥0∞) + 1))) 1 4 2 (1 / 8)

theorem kcConst_lt_top (n : ℕ) : kcConst n < ⊤ := by
  have hc : (3 * (2 * ((n : ℝ≥0∞) + 1))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
  exact constL_lt_top (c := 3 * (2 * ((n : ℝ≥0∞) + 1))) (d := 1) (p := 4) (q := 2) (β := 1 / 8) hc one_pos
    (by norm_num) (by norm_num) (by norm_num)

/-- **The Kolmogorov–Chentsov inequality for the angle on `J_n`.** -/
theorem lintegral_holderSup_le (hU : IsJacobiMP κ a b P U) (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ∫⁻ ω, holderSup U n ω ∂P ≤ (quartC κ a b).toNNReal * kcConst n :=
  countable_kolmogorov_chentsov (U := Ioo (-((n : ℝ) + 1)) (n + 1)) (c := 3 * (2 * ((n : ℝ≥0∞) + 1)))
    (d := 1) (X := U) (P := P) (p := 4) (q := 2) (M := (quartC κ a b).toNNReal) (β := 1 / 8)
    (Sec2.JacobiExists.isCoverWithBoundedCoveringNumber_Ioo_real.hasBoundedCoveringNumber n)
    (jmp_isKolmogorovProcess hU hκ ha hb).IsAEKolmogorovProcess one_pos (by norm_num) (by norm_num)
    (ratPts n) (fun _ h => h.1)

omit [IsProbabilityMeasure P] in
theorem measurable_holderSup (hU : IsJacobiMP κ a b P U) (n : ℕ) : Measurable (holderSup U n) := by
  refine Measurable.iSup fun s => Measurable.iSup fun t => ?_
  exact ((((hU.measurable s).edist (hU.measurable t)).pow_const _)).div_const _

omit [IsProbabilityMeasure P] in
/-- **The Hölder bound on the event `{sup ≤ K}`**, at all points of `J_n`. -/
theorem abs_sub_le_of_holderSup_le (hU : IsJacobiMP κ a b P U) {n : ℕ} {ω : Ω} {K : ℝ≥0}
    (hK : holderSup U n ω ≤ K) {s t : ℝ} (hs : s ∈ Ioo (-((n : ℝ) + 1)) (n + 1))
    (ht : t ∈ Ioo (-((n : ℝ) + 1)) (n + 1)) :
    |U s ω - U t ω| ^ 4 ≤ K * |s - t| ^ (1 / 2 : ℝ) := by
  -- at rational points
  have hrat : ∀ s' t' : ratPts n, |U s' ω - U t' ω| ^ 4 ≤ K * |(s' : ℝ) - t'| ^ (1 / 2 : ℝ) := by
    intro s' t'
    have h1 : edist (U s' ω) (U t' ω) ^ (4 : ℝ) / edist s' t' ^ ((1 / 8 : ℝ) * 4) ≤ K :=
      (le_iSup₂ (f := fun (s t : ratPts n) => edist (U s ω) (U t ω) ^ (4 : ℝ) /
        edist s t ^ ((1 / 8 : ℝ) * 4)) s' t').trans hK
    by_cases hst : (s' : ℝ) = t'
    · have : U s' ω = U t' ω := by rw [hst]
      rw [this, sub_self, abs_zero, zero_pow (by norm_num)]
      exact mul_nonneg (NNReal.coe_nonneg K) (Real.rpow_nonneg (abs_nonneg _) _)
    have hpos : 0 < edist s' t' := edist_pos.2 fun h => hst (congrArg Subtype.val h)
    have hfin : edist s' t' ≠ ⊤ := edist_ne_top _ _
    rw [ENNReal.div_le_iff (ENNReal.rpow_pos hpos hfin).ne' (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin)]
      at h1
    rw [Subtype.edist_eq, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), show (1 / 8 : ℝ) * 4 = 1 / 2 by norm_num,
      show ((K : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal K from (ENNReal.ofReal_coe_nnreal).symm,
      ← ENNReal.ofReal_mul (NNReal.coe_nonneg K), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  -- density and continuity
  set S : Set (ℝ × ℝ) := {p | |U p.1 ω - U p.2 ω| ^ 4 ≤ K * |p.1 - p.2| ^ (1 / 2 : ℝ)} with hS
  have hc : Continuous fun u => U u ω := hU.continuous ω
  have hScl : IsClosed S := isClosed_le (by fun_prop) (continuous_const.mul
    ((continuous_abs.comp (continuous_fst.sub continuous_snd)).rpow_const fun _ => Or.inr (by norm_num)))
  set J := Ioo (-((n : ℝ) + 1)) (n + 1)
  have hD : Dense (range fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ))) := by
    have := (Rat.denseRange_cast (𝕜 := ℝ)).prodMap (Rat.denseRange_cast (𝕜 := ℝ))
    exact this
  have hsub : J ×ˢ J ⊆ closure ((J ×ˢ J) ∩ range fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ))) :=
    hD.open_subset_closure_inter (isOpen_Ioo.prod isOpen_Ioo)
  have hinS : (J ×ˢ J) ∩ (range fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ))) ⊆ S := by
    rintro _ ⟨⟨h1, h2⟩, ⟨q, rfl⟩⟩
    exact hrat ⟨q.1, h1, q.1, rfl⟩ ⟨q.2, h2, q.2, rfl⟩
  exact hScl.closure_subset_iff.2 hinS (hsub (show (s, t) ∈ J ×ˢ J from ⟨hs, ht⟩))

/-! ### Tightness of the laws of the entrance paths -/

section Tight

open scoped DSReach.PathMeas

variable {R : ℝ≥0}

theorem abs_clamp01_sub_le (x x' : ℝ) : |clamp01 x - clamp01 x'| ≤ |x - x'| := by
  unfold clamp01
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

theorem measurable_vPath {Ω' : Type*} [MeasurableSpace Ω'] {V : ℝ → Ω' → ℝ} (hm : ∀ u, Measurable (V u))
    (hc : ∀ ω, Continuous fun u => V u ω) :
    Measurable fun ω => vPath (R := R) (fun u => V u ω) (hc ω) :=
  DSReach.measurable_to_pathSpace _ fun _ => measurable_const.mul
    (continuous_clamp01.measurable.comp (hm _))

/-- The modulus bound of an entrance path at two levels, in terms of a Hölder bound for the angle on the
logarithmic interval `[log ρ, log R]`. -/
theorem abs_vPath_sub_le {U : ℝ → ℝ} (hU : Continuous U) {ρ K h : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hHol : ∀ s ∈ Icc (Real.log ρ) (Real.log R), ∀ t ∈ Icc (Real.log ρ) (Real.log R),
      |U s - U t| ^ 4 ≤ K * |s - t| ^ (1 / 2 : ℝ))
    {y y' : Icc (0 : ℝ≥0) R} (hyy : dist y y' ≤ h) :
    dist (vPath U hU y) (vPath U hU y') ≤ max (2 * (ρ + h)) (h + R * (K * (h / ρ) ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ)) := by
  have hy0 : (0 : ℝ) ≤ (y : ℝ≥0) := NNReal.coe_nonneg _
  have hy'0 : (0 : ℝ) ≤ (y' : ℝ≥0) := NNReal.coe_nonneg _
  have hyR : ((y : ℝ≥0) : ℝ) ≤ R := by exact_mod_cast y.2.2
  have hy'R : ((y' : ℝ≥0) : ℝ) ≤ R := by exact_mod_cast y'.2.2
  have hd : |((y : ℝ≥0) : ℝ) - (y' : ℝ≥0)| ≤ h := by
    rw [Subtype.dist_eq, NNReal.dist_eq] at hyy; exact hyy
  have hh : 0 ≤ h := (abs_nonneg _).trans hd
  simp only [vPath, ContinuousMap.coe_mk, Real.dist_eq]
  set c := clamp01 (U (Real.log (y : ℝ≥0)))
  set c' := clamp01 (U (Real.log (y' : ℝ≥0)))
  have hc := clamp01_mem (U (Real.log (y : ℝ≥0)))
  have hc' := clamp01_mem (U (Real.log (y' : ℝ≥0)))
  by_cases hsmall : ((y : ℝ≥0) : ℝ) < ρ ∨ ((y' : ℝ≥0) : ℝ) < ρ
  · refine le_max_of_le_left ?_
    have h1 : |((y : ℝ≥0) : ℝ) * c| ≤ (y : ℝ≥0) := by
      rw [abs_mul, abs_of_nonneg hy0]; exact mul_le_of_le_one_right hy0 (abs_clamp01_le _)
    have h2 : |((y' : ℝ≥0) : ℝ) * c'| ≤ (y' : ℝ≥0) := by
      rw [abs_mul, abs_of_nonneg hy'0]; exact mul_le_of_le_one_right hy'0 (abs_clamp01_le _)
    rw [abs_le] at hd
    rcases hsmall with hs | hs
    · calc |((y : ℝ≥0) : ℝ) * c - (y' : ℝ≥0) * c'| ≤ |((y : ℝ≥0) : ℝ) * c| + |((y' : ℝ≥0) : ℝ) * c'| :=
            abs_sub _ _
        _ ≤ 2 * (ρ + h) := by linarith
    · calc |((y : ℝ≥0) : ℝ) * c - (y' : ℝ≥0) * c'| ≤ |((y : ℝ≥0) : ℝ) * c| + |((y' : ℝ≥0) : ℝ) * c'| :=
            abs_sub _ _
        _ ≤ 2 * (ρ + h) := by linarith
  · push Not at hsmall
    obtain ⟨hyρ, hy'ρ⟩ := hsmall
    refine le_max_of_le_right ?_
    have hlog : |Real.log (y : ℝ≥0) - Real.log (y' : ℝ≥0)| ≤ h / ρ := by
      have hyp : (0 : ℝ) < (y : ℝ≥0) := by linarith
      have hy'p : (0 : ℝ) < (y' : ℝ≥0) := by linarith
      rw [← Real.log_div hyp.ne' hy'p.ne']
      rw [abs_le] at hd
      rcases le_total ((y' : ℝ≥0) : ℝ) (y : ℝ≥0) with hle | hle
      · have h0 : 0 ≤ Real.log (((y : ℝ≥0) : ℝ) / (y' : ℝ≥0)) :=
          Real.log_nonneg ((one_le_div hy'p).2 hle)
        rw [abs_of_nonneg h0]
        refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
        rw [div_sub_one hy'p.ne', div_le_div_iff₀ hy'p hρ]
        nlinarith
      · have h0 : Real.log (((y : ℝ≥0) : ℝ) / (y' : ℝ≥0)) ≤ 0 :=
          Real.log_nonpos (by positivity) ((div_le_one hy'p).2 hle)
        rw [abs_of_nonpos h0, ← Real.log_inv, inv_div]
        refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
        rw [div_sub_one hyp.ne', div_le_div_iff₀ hyp hρ]
        nlinarith
    have hUd : |c - c'| ≤ (K * (h / ρ) ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) := by
      have hmem : ∀ z : Icc (0 : ℝ≥0) R, ρ ≤ (z : ℝ≥0) → Real.log (z : ℝ≥0) ∈ Icc (Real.log ρ) (Real.log R) :=
        fun z hz => ⟨Real.log_le_log hρ hz, Real.log_le_log (by linarith) (by exact_mod_cast z.2.2)⟩
      have h4 := hHol _ (hmem y hyρ) _ (hmem y' hy'ρ)
      refine (abs_clamp01_sub_le _ _).trans ?_
      have hroot : |U (Real.log (y : ℝ≥0)) - U (Real.log (y' : ℝ≥0))| =
          (|U (Real.log (y : ℝ≥0)) - U (Real.log (y' : ℝ≥0))| ^ 4) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; norm_num
      rw [hroot]
      refine Real.rpow_le_rpow (by positivity) (h4.trans ?_) (by norm_num)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hlog (by norm_num)) hK
    calc |((y : ℝ≥0) : ℝ) * c - (y' : ℝ≥0) * c'| = |(((y : ℝ≥0) : ℝ) - (y' : ℝ≥0)) * c + (y' : ℝ≥0) * (c - c')| := by
          ring_nf
      _ ≤ |((y : ℝ≥0) : ℝ) - (y' : ℝ≥0)| * 1 + R * |c - c'| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_clamp01_le _) (abs_nonneg _)
          · rw [abs_mul, abs_of_nonneg hy'0]; exact mul_le_mul_of_nonneg_right hy'R (abs_nonneg _)
      _ ≤ h + R * (K * (h / ρ) ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ) := by
          rw [mul_one]; exact add_le_add hd (mul_le_mul_of_nonneg_left hUd (NNReal.coe_nonneg R))

/-- The `j`-th modulus candidate at scale `h`. -/
def modC (R : ℝ≥0) (K : ℕ → ℝ≥0) (j : ℕ) (h : ℝ) : ℝ :=
  max (2 * (R * Real.exp (-(j : ℝ)) + h)) (h + R * (K j * (h / (R * Real.exp (-(j : ℝ)))) ^ (1 / 2 : ℝ)) ^ (1 / 4 : ℝ))

theorem modC_nonneg (R : ℝ≥0) (K : ℕ → ℝ≥0) (j : ℕ) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ modC R K j h :=
  le_max_of_le_left (by positivity)

theorem tendsto_iInf_modC (hR : 0 < R) (K : ℕ → ℝ≥0) :
    Tendsto (fun k : ℕ => ⨅ j, modC R K j (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
  have hR' : (0 : ℝ) < R := hR
  have hbdd : ∀ k : ℕ, BddBelow (range fun j => modC R K j (1 / ((k : ℝ) + 1))) := fun k =>
    ⟨0, by rintro _ ⟨j, rfl⟩; exact modC_nonneg R K j (by positivity)⟩
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun k => lt_of_lt_of_le ha (le_ciInf fun j =>
    modC_nonneg R K j (by positivity)), fun a ha => ?_⟩
  -- choose `j` with `2 R e^{-j} < a`
  have hexp : Tendsto (fun j : ℕ => 2 * (R * Real.exp (-(j : ℝ)))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul (R : ℝ)
    simpa using this.const_mul 2
  obtain ⟨j, hj⟩ := (hexp.eventually (gt_mem_nhds ha)).exists
  have hρ : 0 < (R : ℝ) * Real.exp (-(j : ℝ)) := by positivity
  have hcont : ContinuousAt (fun h : ℝ => modC R K j h) 0 := by
    unfold modC
    refine ((continuous_const.mul (continuous_const.add continuous_id)).continuousAt).max ?_
    refine continuousAt_id.add (continuousAt_const.mul ?_)
    refine ContinuousAt.rpow_const (continuousAt_const.mul ?_) (Or.inr (by norm_num))
    exact ContinuousAt.rpow_const (continuousAt_id.div_const _) (Or.inr (by norm_num))
  have h0 : modC R K j 0 = 2 * (R * Real.exp (-(j : ℝ))) := by
    unfold modC
    simp only [add_zero, zero_div, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero,
      Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)]
    exact max_eq_left (by positivity)
  have hk : Tendsto (fun k : ℕ => modC R K j (1 / ((k : ℝ) + 1))) atTop (𝓝 (2 * (R * Real.exp (-(j : ℝ))))) := by
    rw [← h0]; exact hcont.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hk.eventually (gt_mem_nhds hj)] with k hk'
  exact lt_of_le_of_lt (ciInf_le (hbdd k) j) hk'

/-- **Tightness of the laws of the entrance paths** of Jacobi angles with a common quartic constant. -/
theorem isTightMeasureSet_vLaw (hR : 0 < R) {κ : ℝ} (hκ : 0 ≤ κ) {ι : Type*} {Ω' : ι → Type*}
    [∀ i, MeasurableSpace (Ω' i)] {P' : ∀ i, Measure (Ω' i)} [∀ i, IsProbabilityMeasure (P' i)] {a' b' : ι → ℝ}
    (ha : ∀ i, 0 ≤ a' i) (hb : ∀ i, 0 ≤ b' i) {U' : ∀ i, ℝ → Ω' i → ℝ}
    (hU : ∀ i, IsJacobiMP κ (a' i) (b' i) (P' i) (U' i)) {Mq : ℝ} (hMq : ∀ i, quartC κ (a' i) (b' i) ≤ Mq) :
    IsTightMeasureSet (range fun i => (P' i).map fun ω => vPath (R := R) (U' i · ω) ((hU i).continuous ω)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hR' : (0 : ℝ) < R := hR
  obtain ⟨ε', hε'0, hε'ε⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ENNReal.ofReal ε' ≤ ε := by
    rcases eq_or_ne ε ⊤ with h | h
    · exact ⟨1, one_pos, by rw [h]; exact le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h, by rw [ENNReal.ofReal_toReal h]⟩
  set N₀ : ℕ := ⌈|Real.log R|⌉₊ with hN₀
  set n : ℕ → ℕ := fun j => j + N₀ with hn
  set Mq' : ℝ≥0 := (max Mq 0).toNNReal with hMq'
  set L : ℕ → ℝ≥0 := fun j => (kcConst (n j)).toNNReal with hL
  have hLe : ∀ j, kcConst (n j) = L j := fun j => (ENNReal.coe_toNNReal (kcConst_lt_top _).ne).symm
  set K : ℕ → ℝ≥0 := fun j => (Mq' * L j + 1) * 2 ^ (j + 1) / ε'.toNNReal with hK
  have hε'nn : 0 < ε'.toNNReal := Real.toNNReal_pos.2 hε'0
  have hKpos : ∀ j, 0 < K j := fun j => div_pos (by positivity) hε'nn
  -- the bad events
  have hbad : ∀ i j, P' i {ω | (K j : ℝ≥0∞) < holderSup (U' i) (n j) ω} ≤
      ENNReal.ofReal ε' * 2⁻¹ ^ (j + 1) := by
    intro i j
    have hM : ((quartC κ (a' i) (b' i)).toNNReal : ℝ≥0∞) ≤ Mq' :=
      ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ((hMq i).trans (le_max_left _ _)))
    calc P' i {ω | (K j : ℝ≥0∞) < holderSup (U' i) (n j) ω}
        ≤ P' i {ω | (K j : ℝ≥0∞) ≤ holderSup (U' i) (n j) ω} :=
          measure_mono fun ω h => by simp only [mem_ofPred_eq] at h ⊢; exact h.le
      _ ≤ (∫⁻ ω, holderSup (U' i) (n j) ω ∂(P' i)) / K j :=
          meas_ge_le_lintegral_div (measurable_holderSup (hU i) _).aemeasurable
            (by exact_mod_cast (hKpos j).ne') ENNReal.coe_ne_top
      _ ≤ ((Mq' * L j : ℝ≥0) : ℝ≥0∞) / K j := by
          gcongr
          refine (lintegral_holderSup_le (hU i) hκ (ha i) (hb i) (n j)).trans ?_
          rw [hLe, ENNReal.coe_mul]
          gcongr
      _ ≤ ENNReal.ofReal ε' * 2⁻¹ ^ (j + 1) := by
          rw [← ENNReal.coe_div (hKpos j).ne', ← ENNReal.ofReal_coe_nnreal]
          rw [show (2⁻¹ : ℝ≥0∞) ^ (j + 1) = ENNReal.ofReal ((2⁻¹ : ℝ) ^ (j + 1)) by
            rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num,
            ← ENNReal.ofReal_mul hε'0.le]
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [hK, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_pow, NNReal.coe_one,
            NNReal.coe_ofNat, Real.coe_toNNReal _ hε'0.le]
          have hA : (0 : ℝ) ≤ (Mq' : ℝ) * L j := by positivity
          rw [div_div_eq_mul_div, div_le_iff₀ (by positivity), inv_pow]
          field_simp
          nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (j + 1)]
  -- the compact set
  set ω : ℕ → ℝ := fun k => ⨅ j, modC R K j (1 / ((k : ℝ) + 1)) with hω
  set C : Set C(Icc (0 : ℝ≥0) R, ℝ) := {f | (∀ x, f x ∈ Icc (-(R : ℝ)) R) ∧
    ∀ (k : ℕ) x y, dist x y ≤ 1 / ((k : ℝ) + 1) → dist (f x) (f y) ≤ ω k} with hC
  have hCc : IsCompact C :=
    DSReach.isCompact_modulusSet isCompact_Icc (fun k => by positivity) (tendsto_iInf_modC hR K)
  refine ⟨C, hCc, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hmeas := measurable_vPath (R := R) (hU i).measurable (hU i).continuous
  rw [Measure.map_apply hmeas hCc.isClosed.measurableSet.compl]
  have hincl : (fun ω => vPath (R := R) (U' i · ω) ((hU i).continuous ω)) ⁻¹' Cᶜ ⊆
      ⋃ j, {ω | (K j : ℝ≥0∞) < holderSup (U' i) (n j) ω} := by
    intro ω hω
    by_contra hcon
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hcon
    apply hω
    refine ⟨fun x => ?_, fun k x y hxy => ?_⟩
    · have hx0 : (0 : ℝ) ≤ (x : ℝ≥0) := NNReal.coe_nonneg _
      have hxR : ((x : ℝ≥0) : ℝ) ≤ R := by exact_mod_cast x.2.2
      have hc := clamp01_mem (U' i (Real.log (x : ℝ≥0)) ω)
      simp only [vPath, ContinuousMap.coe_mk]
      constructor <;> nlinarith [hc.1, hc.2]
    · refine le_ciInf fun j => ?_
      have hρ : 0 < (R : ℝ) * Real.exp (-(j : ℝ)) := by positivity
      refine abs_vPath_sub_le ((hU i).continuous ω) hρ (NNReal.coe_nonneg (K j)) (fun s hs t ht => ?_) hxy
      have hlogρ : Real.log ((R : ℝ) * Real.exp (-(j : ℝ))) = Real.log R - j := by
        rw [Real.log_mul hR'.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
      have habs : |Real.log R| ≤ N₀ := Nat.le_ceil _
      have hmemJ : ∀ u ∈ Icc (Real.log ((R : ℝ) * Real.exp (-(j : ℝ)))) (Real.log R),
          u ∈ Ioo (-((n j : ℕ) + 1 : ℝ)) ((n j : ℕ) + 1) := fun u hu => by
        rw [hlogρ] at hu
        simp only [hn, Nat.cast_add]
        constructor <;> linarith [hu.1, hu.2, neg_abs_le (Real.log R), le_abs_self (Real.log R)]
      exact abs_sub_le_of_holderSup_le (hU i) (hcon j) (hmemJ s hs) (hmemJ t ht)
  calc P' i ((fun ω => vPath (R := R) (U' i · ω) ((hU i).continuous ω)) ⁻¹' Cᶜ)
      ≤ ∑' j, P' i {ω | (K j : ℝ≥0∞) < holderSup (U' i) (n j) ω} :=
        (measure_mono hincl).trans (measure_iUnion_le _)
    _ ≤ ∑' j, ENNReal.ofReal ε' * 2⁻¹ ^ (j + 1) := ENNReal.tsum_le_tsum (hbad i)
    _ = ENNReal.ofReal ε' := by
        have hgeo : ∑' i : ℕ, (2⁻¹ : ℝ≥0∞) ^ (i + 1) = 1 := by
          simp_rw [pow_succ]
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
            ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
        rw [ENNReal.tsum_mul_left, hgeo, mul_one]
    _ ≤ ε := hε'ε

end Tight

end Aux4

end Supp12

end InteractingSLE
