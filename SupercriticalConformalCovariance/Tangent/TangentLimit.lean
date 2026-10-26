import SupercriticalConformalCovariance.Tangent.Barrier
import SupercriticalConformalCovariance.Tangent.Normalize
import SupercriticalConformalCovariance.Tangent.GM24Discharge
import LQGMetric.Field.HarmLocA

/-!
# Lemma 3.3 (tangent limit), paper l. 190–236

`tangent_limit`: Suppose `U_n` eventually contains every compact subset of `ℂ`, `ψ_n : U_n → V_n` are
conformal bijections with `ψ_n(0) = 0` and `ψ_n′(0) → a ≠ 0`, `R_n → ∞` with `B_{2R_n} ⊆ U_n`,
`K_n = B̄_{R_n}`, and `h` is a whole-plane GFF (any additive constant). For realizations
`(h̄_n, f_n)` of the transformed fields `h^{ψ_n} = h ∘ ψ_n⁻¹ + Q log |(ψ_n⁻¹)′|` on `V_n`, put
`d_n = D_h(·,·;K_n)` and `e_n = ψ_n^* D_{h^{ψ_n}}(·,·;ψ_n(K_n))`, both `+∞` off `K_n × K_n`. Then
`d_n → D_h` and `e_n → D_h` in probability for the topology of DG Definition 1.2 (every subsequence
has a further subsequence converging almost surely). Since the limit is a function of `h`, this is
(5) on the original space, and it implies the joint convergence in law (5)
(`tangent_limit_law`).

No hypotheses beyond the paper's setting (and `0 < Q`, part of `Q = Q(ξ) ∈ (0, 2)`, l. 17). Inputs:
GM Lemma 2.4 (2.6) from the proof of Gwynne–Miller Lemma 2.4 (`tendsto_tvDist_gm24_closed`, built on the total-variation module); Lemma 3.2 from SupercriticalLQGUniqueness
Koebe from the Koebe estimates; affine covariance from the affine-covariance modules; the domain layer from the domain-metric layer;
the Lemma 3.1 repair's confined-metric measurability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric Function
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open LQGMetric (DistC DistOn TestOn TestC restrictTo addFun addConst ofCont IsGFFPlusCont
  IsWholePlaneGFF)
open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric LSCTendsto IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization
  weylScaleOn)
open SupercriticalConformalCovariance.Domain (confined resC cutF exW exW_subset cutF_eq exists_subset_exW
  ae_weylScaleOn_eq_internal isGFFPlusCont_addFun_of_measurable measurable_cutExt)
open SupercriticalConformalCovariance.GM24 (isConformalBijection_invFunOn dilDist)

/-- The radial normalizing test function `𝐟` (a normalized radial bump, `∫ 𝐟 = 1`). -/
def normBump : TestC := LQGMetric.HarmLoc.unitBump 1 one_pos 0

theorem integral_normBump : ∫ x, normBump x = 1 := LQGMetric.HarmLoc.integral_unitBump 1 one_pos 0

theorem normBump_rot (u : ℂ) (hu : ‖u‖ = 1) (z : ℂ) : normBump (u * z) = normBump z := by
  simp only [normBump, LQGMetric.HarmLoc.unitBump_apply, sub_zero]
  congr 1
  simp only [LQGMetric.GM.radProf, norm_mul, hu, one_mul]

theorem addFun_addConst (x : DistC) (c : ℝ) (F : C(ℂ, ℝ)) :
    addFun (addConst x c) F = addConst (addFun x F) c := by
  simp only [addConst, addFun, add_right_comm]

/-- `e_n` as the coercion of an `ℝ≥0∞`-valued function. -/
def tangentEval (ξ : ℝ) (D : DistC → LSCMetric) {Ω : Type} (V : ℕ → Opens ℂ) (ψ : ℕ → ℂ → ℂ)
    (R : ℕ → ℝ) (hY : ∀ n, ψ n '' closedBall (0 : ℂ) (R n) ⊆ (V n : Set ℂ))
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ)) (n : ℕ) (ω : Ω) (q : ℂ × ℂ) : ℝ≥0∞ :=
  open Classical in
  if q.1 ∈ closedBall (0 : ℂ) (R n) ∧ q.2 ∈ closedBall (0 : ℂ) (R n) then
    confined ξ (D (hbar n ω)) (hY n) (fr n ω) (ψ n q.1, ψ n q.2) else ⊤

theorem tangentE_eq (ξ : ℝ) (D : DistC → LSCMetric) {Ω : Type} (V : ℕ → Opens ℂ) (ψ : ℕ → ℂ → ℂ)
    (R : ℕ → ℝ) (hY : ∀ n, ψ n '' closedBall (0 : ℂ) (R n) ⊆ (V n : Set ℂ))
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ)) (n : ℕ) (ω : Ω) (q : ℂ × ℂ) :
    tangentE ξ D V ψ R hY hbar fr n ω q = (tangentEval ξ D V ψ R hY hbar fr n ω q : EReal) := by
  unfold tangentE tangentEval extendTop
  split_ifs <;> simp

/-- **Lemma 3.3 (tangent limit)**, strong form (convergence in probability on the original space). -/
theorem tangent_limit {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q) (hQpos : 0 < Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n)) :
    SubseqLSC P (fun n ω q => (extInternal (D (h ω)) (closedBall 0 (R n)) q : EReal))
        (fun ω q => (D (h ω) q : EReal)) ∧
      SubseqLSC P (tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr)
        (fun ω q => (D (h ω) q : EReal)) := by
  classical
  have hY := tangentImage_subset hψ hRU
  have hcl : ∀ n, closedBall (0 : ℂ) (R n) ⊆ (U n : Set ℂ) := fun n =>
    (closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2
  have hzeroU : ∀ n, (0 : ℂ) ∈ U n := fun n => hcl n (mem_closedBall_self (hRU n).1.le)
  have hweak := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  -- step 1: the normalization `(h, 𝐟) = 0`
  set f : TestC := normBump with hf
  set c : Ω → ℝ := fun ω => h ω f with hcdef
  have hc : Measurable c := (LQGMetric.measurable_distOn_apply f).comp hh.measurable
  set h₀ : Ω → DistC := fun ω => addConst (h ω) (-c ω) with hh₀def
  have hh₀ : IsWholePlaneGFF h₀ P := hh.addConst hc.neg
  have hnorm₀ : ∀ᵐ ω ∂P, h₀ ω f = 0 := Eventually.of_forall fun ω => by
    simp only [hh₀def, LQGMetric.GFFInv.addConst_apply, hf, integral_normBump, hcdef]
    ring
  set hbar₀ : ℕ → Ω → DistC := fun n ω => addConst (hbar n ω) (-c ω) with hbar₀def
  have hreal₀ : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h₀ ω)))
      (hbar₀ n) (fr n) := fun n =>
    isDomainRealization_addConst Q (isConformalBijection_invFunOn (hψ n)) hh.measurable (hreal n)
      hc.neg
  have hmain := tangent_limit_normalized hQ hD gmLemma24TV_holds hψ hexhaust hzero ha0 ha hR hRU P
    hh₀ integral_normBump normBump_rot hnorm₀ hbar₀ fr hreal₀
    (targetBarrier_holds hQpos hD gmLemma24TV_holds hψ hzeroU hexhaust hzero ha0 ha P hh₀
      integral_normBump normBump_rot hnorm₀ hbar₀ fr hreal₀)
  -- undo the normalization: all metrics are multiplied by `κ = e^{-ξ c}`
  set κ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp ((ξ : ℝ) * -c ω)) with hκ
  have hκ0 : ∀ ω, κ ω ≠ 0 ∧ κ ω ≠ ⊤ := fun ω =>
    ⟨(ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne', ENNReal.ofReal_ne_top⟩
  have hhc : IsGFFPlusCont h P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh
  have hscale := SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul P h hhc
    ξ Q D hweak (fun ω => -c ω)
  have hDlim : ∀ᵐ ω ∂P, ∀ q, D (h₀ ω) q = κ ω * D (h ω) q := hscale
  constructor
  · refine subseqLSC_of_mul κ (Eventually.of_forall hκ0) ?_
    refine hmain.1.congr_ae (fun n => ?_) ?_
    · filter_upwards [hscale] with ω hω
      funext q
      congr 1
      unfold extInternal
      split_ifs
      · exact SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.internal_eq_mul_of_dist_scale
          _ _ (κ ω) (hκ0 ω).1 (hκ0 ω).2 (fun x y => hω (x, y)) _ _
      · rw [ENNReal.mul_top (hκ0 ω).1]
    · filter_upwards [hDlim] with ω hω
      funext q
      rw [hω q]
  · have hcoe : tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr =
        fun n ω q => (tangentEval (ξ : ℝ) D V ψ R hY hbar fr n ω q : EReal) := by
      funext n ω q
      exact tangentE_eq _ _ _ _ _ _ _ _ _ _ _
    rw [hcoe]
    refine subseqLSC_of_mul (F := tangentEval (ξ : ℝ) D V ψ R hY hbar fr) κ
      (Eventually.of_forall hκ0) ?_
    -- the target metrics scale by `κ`
    have hT : ∀ n, ∀ᵐ ω ∂P, ∀ q, tangentEval (ξ : ℝ) D V ψ R hY hbar₀ fr n ω q =
        κ ω * tangentEval (ξ : ℝ) D V ψ R hY hbar fr n ω q := by
      intro n
      have hYc : IsCompact (ψ n '' closedBall (0 : ℂ) (R n)) :=
        (isCompact_closedBall _ _).image_of_continuousOn ((hψ n).1.continuousOn.mono (hcl n))
      obtain ⟨m, hm⟩ := exists_subset_exW (V n).isOpen hYc (hY n)
      have hFm : Measurable fun ω => cutF (V n) m (fr n ω) :=
        measurable_cutExt (V n).isOpen _ (hreal n).2.2.1
      have hGc : IsGFFPlusCont (fun ω => addFun (hbar n ω) (cutF (V n) m (fr n ω))) P :=
        isGFFPlusCont_addFun_of_measurable (hreal n).2.1 hFm
      filter_upwards [ae_weylScaleOn_eq_internal hD P (hreal n).2.1,
        ae_weylScaleOn_eq_internal hD P (hreal₀ n).2.1,
        SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul P _ hGc ξ Q D
          hweak (fun ω => -c ω)] with ω h1 h2 h3 q
      unfold tangentEval
      split_ifs with hq
      · have hpY : ψ n q.1 ∈ ψ n '' closedBall (0 : ℂ) (R n) ∧
            ψ n q.2 ∈ ψ n '' closedBall (0 : ℂ) (R n) :=
          ⟨mem_image_of_mem _ hq.1, mem_image_of_mem _ hq.2⟩
        have hext : ∀ z (hz : z ∈ ψ n '' closedBall (0 : ℂ) (R n)),
            cutF (V n) m (fr n ω) z = resC (hY n) (fr n ω) ⟨z, hz⟩ := fun z hz => by
          rw [cutF_eq (V n) m (fr n ω) z (hm hz)]; rfl
        unfold confined
        rw [dif_pos hpY, dif_pos hpY, h2 _ _ _ hext, h1 _ _ _ hext]
        simp only [hbar₀def]
        rw [addFun_addConst]
        exact SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.internal_eq_mul_of_dist_scale
          _ _ (κ ω) (hκ0 ω).1 (hκ0 ω).2 (fun x y => h3 (x, y)) _ _
      · rw [ENNReal.mul_top (hκ0 ω).1]
    refine hmain.2.congr_ae (fun n => ?_) ?_
    · filter_upwards [hT n] with ω hω
      funext q
      rw [tangentE_eq, hω q]
    · filter_upwards [hDlim] with ω hω
      funext q
      rw [hω q]

end SupercriticalConformalCovariance.Tangent
