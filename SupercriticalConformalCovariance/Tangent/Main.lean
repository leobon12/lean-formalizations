import SupercriticalConformalCovariance.Tangent.Fixed
import SupercriticalConformalCovariance.Tangent.Expanding
import SupercriticalConformalCovariance.Tangent.Source
import SupercriticalConformalCovariance.Rotation.Affine

/-!
# Lemma 3.3, assembly for a normalized field

Paper l. 190–236. `tangent_limit_normalized`: for `h` a whole-plane GFF normalized by `(h, 𝐟) = 0`
(`𝐟` radial, `∫ 𝐟 = 1`), realizations `(h̄_n, f_n)` of the transformed fields `h^{ψ_n}` on `V_n`, the
source metrics `d_n = D_h(·,·; K_n)` and the pulled-back target metrics
`e_n = ψ_n^* D_{h^{ψ_n}}(·,·; ψ_n(K_n))` (both `+∞` off `K_n × K_n`, `K_n = B̄_{R_n}`) converge in
probability to `D_h`, in the topology of DG Definition 1.2 (subsequence form `SubseqLSC`).

Hypotheses beyond the paper's: `GMLemma24TV` (input (I4), GM (2.6); discharged by `SupercriticalConformalCovariance.Tangent.gmLemma24TV_holds`) and
`TargetBarrier` (Lemma 3.2 transferred to the transformed fields, l. 224–228; discharged in
`SupercriticalConformalCovariance.Tangent.Barrier`).
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
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (closedBallPathInf)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open SupercriticalConformalCovariance.Domain (confined)
open SupercriticalConformalCovariance.GM24 (isConformalBijection_invFunOn dilDist)

/-- The pulled-back target metric `e_n = ψ_n^* D_{h^{ψ_n}}(·, ·; ψ_n(K_n))`, `+∞` off
`K_n × K_n`, `K_n = B̄_{R_n}` (paper l. 194–196), for the realization `(h̄_n, f_n)`. -/
def tangentE (ξ : ℝ) (D : DistC → LSCMetric) {Ω : Type} (V : ℕ → Opens ℂ) (ψ : ℕ → ℂ → ℂ)
    (R : ℕ → ℝ) (hY : ∀ n, ψ n '' closedBall (0 : ℂ) (R n) ⊆ (V n : Set ℂ))
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ)) (n : ℕ) (ω : Ω) (q : ℂ × ℂ) : EReal :=
  extendTop (closedBall 0 (R n))
    (fun q => ((confined ξ (D (hbar n ω)) (hY n) (fr n ω) (ψ n q.1, ψ n q.2) : ℝ≥0∞) : EReal)) q

/-- **The barrier estimate for the transformed fields** (paper l. 224–228: Lemma 3.2 and "the same
barrier event transfers to the transformed field by the preceding total-variation comparison"):
for every inner radius `b` and `δ > 0` there is `S₀ > b` such that, for large `n`, outside an event
of probability at most `δ`, the target metric internal to any compact `Y` with `B̄_{S₀} ⊆ Y ⊆ V_n` agrees
on `B̄_b × B̄_b` with the target metric internal to `B̄_{S₀}`. -/
def TargetBarrier (ξ : ℝ) (D : DistC → LSCMetric) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (V : ℕ → Opens ℂ) (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ)) : Prop :=
  ∀ b : ℝ, 0 < b → ∀ δ : ℝ, 0 < δ → ∃ S₀ : ℝ, b < S₀ ∧ ∀ᶠ n in atTop,
    P {ω | ¬ ∀ (Y : Set ℂ), IsCompact Y → ∀ (hY : closedBall (0 : ℂ) S₀ ⊆ Y)
      (hYV : Y ⊆ (V n : Set ℂ)), ∀ x ∈ closedBall (0 : ℂ) b, ∀ y ∈ closedBall (0 : ℂ) b,
        confined ξ (D (hbar n ω)) hYV (fr n ω) (x, y) =
          confined ξ (D (hbar n ω)) (hY.trans hYV) (fr n ω) (x, y)} ≤ ENNReal.ofReal δ

/-- The constant `+∞` lower semicontinuous function. -/
def topLSC : LSCFun := ⟨fun _ => ⊤, lowerSemicontinuous_const⟩

/-- Complex-affine covariance in the form used at l. 223: `D_{h^a}(a u, a v) = D_h(u, v)` with
`h^a = h(a⁻¹·) − Q log |a|`. -/
theorem ae_affine_tangent {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusCont h P)
    {a : ℂ} (ha0 : a ≠ 0) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      D (addConst (dilDist (inv_ne_zero ha0) (h ω)) (-(Q * Real.log ‖a‖))) (a * u, a * v) =
        D (h ω) (u, v) := by
  have hα : a⁻¹ ≠ 0 := inv_ne_zero ha0
  filter_upwards [SupercriticalConformalCovariance.Rotation.ae_complex_affine_covariance ξ Q hQ D hD P h hh a⁻¹ hα 0]
    with ω hω u v
  have e1 := hω (a * u) (a * v)
  simp only [add_zero, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul] at e1
  rw [e1]
  congr 2
  rw [SupercriticalConformalCovariance.GM24.dilDist_eq_rotDist_affineComp hα, norm_inv, Real.log_inv, mul_neg]
  congr 2
  rw [div_eq_inv_mul]

/-- Monotonicity of the confined metric in the confining set. -/
theorem confined_le_of_subset {ξ : ℝ} {D₀ : LSCMetric} {V K K' : Set ℂ} (hKK' : K ⊆ K')
    (hK'V : K' ⊆ V) (f : C(V, ℝ)) {q : ℂ × ℂ} (hq : q.1 ∈ K ∧ q.2 ∈ K) :
    confined ξ D₀ hK'V f q ≤ confined ξ D₀ (hKK'.trans hK'V) f q := by
  unfold confined
  rw [dif_pos hq, dif_pos ⟨hKK' hq.1, hKK' hq.2⟩]
  unfold SupercriticalConformalCovariance.weylScaleOn
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hU => le_iInf fun h0 =>
    le_iInf fun h1 => ?_
  refine iInf_le_of_le (fun t => ⟨(P t : ℂ), hKK' (P t).2⟩) <| iInf_le_of_le L <|
    iInf_le_of_le hP <| iInf_le_of_le hU <|
    iInf_le_of_le (by
      have := congrArg Subtype.val h0
      exact Subtype.ext this) <|
    iInf_le_of_le (by
      have := congrArg Subtype.val h1
      exact Subtype.ext this) le_rfl

theorem tangentImage_subset {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ}
    (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n)) {R : ℕ → ℝ}
    (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n) (n : ℕ) :
    ψ n '' closedBall (0 : ℂ) (R n) ⊆ (V n : Set ℂ) := by
  have hcl : closedBall (0 : ℂ) (R n) ⊆ (U n : Set ℂ) :=
    (closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2
  rintro _ ⟨z, hz, rfl⟩
  exact (hψ n).2.mapsTo (hcl hz)

/-- **Lemma 3.3 for a normalized field** (paper (5), strong form: convergence in probability on the
original space, which implies the joint convergence in law (5) since both limits are `D_h`). -/
theorem tangent_limit_normalized {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : IsLFPPExponent ξ Q)
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (hTV : GMLemma24TV)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hRU : ∀ n, 0 < R n ∧ ball (0 : ℂ) (2 * R n) ⊆ U n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {f : TestC} (hf1 : ∫ x, f x = 1)
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) (hnorm : ∀ᵐ ω ∂P, h ω f = 0)
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n))
    (hbarrier : TargetBarrier (ξ : ℝ) D P V hbar fr) :
    SubseqLSC P (fun n ω q => (extInternal (D (h ω)) (closedBall 0 (R n)) q : EReal))
        (fun ω q => (D (h ω) q : EReal)) ∧
      SubseqLSC P (tangentE (ξ : ℝ) D V ψ R (tangentImage_subset hψ hRU) hbar fr)
        (fun ω q => (D (h ω) q : EReal)) := by
  classical
  have hY := tangentImage_subset hψ hRU
  have hcl : ∀ n, closedBall (0 : ℂ) (R n) ⊆ (U n : Set ℂ) := fun n =>
    (closedBall_subset_ball (by linarith [(hRU n).1])).trans (hRU n).2
  have hzeroU : ∀ n, (0 : ℂ) ∈ U n := fun n => hcl n (mem_closedBall_self (hRU n).1.le)
  have hopen : ∀ n, IsOpen (U n : Set ℂ) := fun n => (U n).isOpen
  have hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n) := fun n => (hψ n).1
  have hinj : ∀ n, InjOn (ψ n) (U n) := fun n => (hψ n).2.injOn
  have hhc : IsGFFPlusCont h P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh
  refine ⟨SubseqLSC.of_ae (ae_lscTendsto_source hD P hhc hR), ?_⟩
  set ℓ : ℝ := -(Q * Real.log ‖a‖) with hℓ
  set hA : Ω → DistC := fun ω => addConst (dilDist (inv_ne_zero ha0) (h ω)) ℓ with hAdef
  have hAc : IsGFFPlusCont hA P :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst
      (LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF
        (SupercriticalConformalCovariance.GM24.isWholePlaneGFF_dilDist hh (inv_ne_zero ha0))) measurable_const
  letI : MeasurableSpace LSCFun := borel LSCFun
  haveI : BorelSpace LSCFun := ⟨rfl⟩
  -- the fixed-confinement metrics, as measurable `LSCFun`-valued maps
  set T' : ℕ → ℕ → Ω → LSCFun := fun S n ω =>
    if hS : closedBall (0 : ℂ) ((S : ℝ) + 1) ⊆ (V n : Set ℂ) then
      SupercriticalConformalCovariance.Lemma31.confinedLSC D 0 (by positivity : (0 : ℝ) < (S : ℝ) + 1) hS (hbar n ω) (fr n ω)
    else topLSC with hT'
  set TL : ℕ → Ω → LSCFun := fun S ω => diskMetric ((S : ℝ) + 1) (D (hA ω)) with hTL
  set Tinf : Ω → LSCFun := fun ω => (D (hA ω)).toLSCFun with hTinf
  have hT'eq : ∀ S n, ∀ᵐ ω ∂P, (T' S n ω).1 =
      fun q => (targetFixed (ξ : ℝ) D V hbar fr ((S : ℝ) + 1) n ω q : EReal) := by
    intro S n
    by_cases hS : closedBall (0 : ℂ) ((S : ℝ) + 1) ⊆ (V n : Set ℂ)
    · filter_upwards [SupercriticalConformalCovariance.Lemma31.ae_confinedLSC_eq hD 0 (by positivity : (0 : ℝ) < (S : ℝ) + 1)
        hS P (hreal n).2.1] with ω hω
      simp only [hT', dif_pos hS, hω (fr n ω), targetFixed]
    · refine Eventually.of_forall fun ω => ?_
      funext q
      simp only [hT']
      rw [dif_neg hS]
      simp only [targetFixed, dif_neg hS, topLSC]
      rfl
  have hTm : ∀ S n, AEStronglyMeasurable (T' S n) P := by
    intro S n
    by_cases hS : closedBall (0 : ℂ) ((S : ℝ) + 1) ⊆ (V n : Set ℂ)
    · have hm0 := SupercriticalConformalCovariance.Lemma31.measurable_confinedLSC hD.1 0
        (by positivity : (0 : ℝ) < (S : ℝ) + 1) hS
      have hm := hm0.comp ((hreal n).2.1.1.prodMk (hreal n).2.2.1)
      have e : T' S n = fun ω => SupercriticalConformalCovariance.Lemma31.confinedLSC D 0
          (by positivity : (0 : ℝ) < (S : ℝ) + 1) hS (hbar n ω) (fr n ω) := by
        funext ω; simp only [hT', dif_pos hS]
      rw [e]
      exact hm.aestronglyMeasurable
    · have e : T' S n = fun _ => topLSC := by funext ω; simp only [hT', dif_neg hS]
      rw [e]
      exact aestronglyMeasurable_const
  have hTLm : ∀ S, AEStronglyMeasurable (TL S) P := fun S =>
    ((measurable_diskMetric _).comp (hD.1.comp hAc.1)).aestronglyMeasurable
  have hfix : ∀ S : ℕ, SubseqLSC P (fun n ω => (T' S n ω).1) (fun ω => (TL S ω).1) := by
    intro S
    have hfx := subseqLSC_fixed hD hTV hψ hzeroU hexhaust hzero ha0 ha P hh hf1 hrot hnorm hbar fr
      hreal (S := (S : ℝ) + 1) (by positivity)
    refine hfx.congr_ae (fun n => ?_) (Eventually.of_forall fun ω => ?_)
    · filter_upwards [hT'eq S n] with ω hω
      exact hω.symm
    · funext q
      simp only [hTL, diskMetric_apply, closedBallPathInf_eq_extInternal]
      rfl
  have hlimS : ∀ᵐ ω ∂P, LSCTendsto (fun S => (TL S ω).1) (Tinf ω).1 := by
    filter_upwards [SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P hA hAc] with ω hω
    obtain ⟨hf, hL, _⟩ := hω
    have hRS : Tendsto (fun S : ℕ => (S : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have := lscTendsto_extInternal_of_sample (D (hA ω)) hf hL hRS
    convert this using 2 with S q
    · funext q
      simp only [hTL, diskMetric_apply, closedBallPathInf_eq_extInternal]
    · rfl
  -- the geometric threshold: `B̄_{S+1} ⊆ ψ_n(K_n)`
  have hev : ∀ S : ℕ, ∀ᶠ n in atTop,
      closedBall (0 : ℂ) ((S : ℝ) + 1) ⊆ ψ n '' closedBall (0 : ℂ) (R n) := by
    intro S
    have hnorm' : Tendsto (fun n => ‖deriv (ψ n) 0‖) atTop (𝓝 ‖a‖) := ha.norm
    have hc : Tendsto (fun n => QuantumZipper.CA.Koebe.koebeCovConst * R n * ‖deriv (ψ n) 0‖)
        atTop atTop :=
      (hR.const_mul_atTop QuantumZipper.CA.Koebe.koebeCovConst_pos).atTop_mul_pos
        (norm_pos_iff.2 ha0) hnorm'
    filter_upwards [hc.eventually_gt_atTop ((S : ℝ) + 1)] with n hn z hz
    have hk := QuantumZipper.CA.Koebe.ball_subset_image_koebe
      ((hd n).mono (ball_subset_closedBall.trans (hcl n)))
      ((hinj n).mono (ball_subset_closedBall.trans (hcl n)))
    rw [hzero n] at hk
    exact image_mono ball_subset_closedBall
      (hk (mem_ball.2 ((mem_closedBall.1 hz).trans_lt hn)))
  choose M hM using fun S => eventually_atTop.1 (hev S)
  -- the barrier, in the form used by the expanding-confinement assembly
  have hbarE : ∀ ρ : ℝ, ∀ δ : ℝ, 0 < δ → ∃ S₀ N : ℕ, ∀ S n, S₀ ≤ S → N ≤ n → M S ≤ n →
      P {ω | ¬ ∀ p : ℂ × ℂ, ‖p.1‖ < ρ → ‖p.2‖ < ρ →
        tangentE (ξ : ℝ) D V ψ R hY hbar fr n ω p = extendTop (closedBall 0 (R n))
          (fun q => (T' S n ω).1 (ψ n q.1, ψ n q.2)) p} ≤ ENNReal.ofReal δ := by
    intro ρ δ hδ
    set b : ℝ := ‖a‖ * |ρ| + 1 with hb
    obtain ⟨S₀', hbS, hevb⟩ := hbarrier b (by positivity) δ hδ
    obtain ⟨S₀, hS₀⟩ := exists_nat_ge S₀'
    obtain ⟨hψu, -, -, -, -⟩ :=
      SupercriticalConformalCovariance.Univalent.exhausting_univalent_limits 0 hopen hzeroU hexhaust hd hinj hzero ha ha0
    have hun := Metric.tendstoUniformlyOn_iff.1 ((tendstoLocallyUniformlyOn_iff_forall_isCompact
      isOpen_univ).1 hψu (closedBall (0 : ℂ) |ρ|) (subset_univ _) (isCompact_closedBall _ _)) 1
      one_pos
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hevb.and (hun.and (hR.eventually_ge_atTop |ρ|)))
    refine ⟨S₀, N, fun S n hS hn hMn => ?_⟩
    obtain ⟨hPn, hunn, hRn⟩ := hN n hn
    have hS1V : closedBall (0 : ℂ) ((S : ℝ) + 1) ⊆ (V n : Set ℂ) := (hM S n hMn).trans (hY n)
    have hS₀S : S₀' ≤ (S : ℝ) + 1 := hS₀.trans (by exact_mod_cast Nat.le_succ_of_le hS)
    set Bad1 : Set Ω := {ω | ¬ ∀ (Y : Set ℂ), IsCompact Y → ∀ (hY' : closedBall (0 : ℂ) S₀' ⊆ Y)
        (hYV : Y ⊆ (V n : Set ℂ)), ∀ x ∈ closedBall (0 : ℂ) b, ∀ y ∈ closedBall (0 : ℂ) b,
          confined (ξ : ℝ) (D (hbar n ω)) hYV (fr n ω) (x, y) =
            confined (ξ : ℝ) (D (hbar n ω)) (hY'.trans hYV) (fr n ω) (x, y)} with hBad1
    set Bad2 : Set Ω := {ω | ¬ (T' S n ω).1 =
        fun q => (targetFixed (ξ : ℝ) D V hbar fr ((S : ℝ) + 1) n ω q : EReal)} with hBad2
    refine (measure_mono (t := Bad1 ∪ Bad2) ?_).trans ((measure_union_le Bad1 Bad2).trans ?_)
    · intro ω hω
      by_contra hcon
      simp only [mem_union, not_or] at hcon
      obtain ⟨hgood0, hTω0⟩ := hcon
      have hgood : ∀ (Y : Set ℂ), IsCompact Y → ∀ (hY' : closedBall (0 : ℂ) S₀' ⊆ Y)
          (hYV : Y ⊆ (V n : Set ℂ)),
          ∀ x ∈ closedBall (0 : ℂ) b, ∀ y ∈ closedBall (0 : ℂ) b,
            confined (ξ : ℝ) (D (hbar n ω)) hYV (fr n ω) (x, y) =
              confined (ξ : ℝ) (D (hbar n ω)) (hY'.trans hYV) (fr n ω) (x, y) :=
        Classical.not_not.1 hgood0
      have hTω : (T' S n ω).1 =
          fun q => (targetFixed (ξ : ℝ) D V hbar fr ((S : ℝ) + 1) n ω q : EReal) :=
        Classical.not_not.1 hTω0
      apply hω
      intro p hp1 hp2
      have hp1K : p.1 ∈ closedBall (0 : ℂ) (R n) :=
        mem_closedBall_zero_iff.2 (hp1.le.trans ((le_abs_self ρ).trans hRn))
      have hp2K : p.2 ∈ closedBall (0 : ℂ) (R n) :=
        mem_closedBall_zero_iff.2 (hp2.le.trans ((le_abs_self ρ).trans hRn))
      have hxb : ψ n p.1 ∈ closedBall (0 : ℂ) b := by
        have h1 := hunn p.1 (mem_closedBall_zero_iff.2 (hp1.le.trans (le_abs_self ρ)))
        rw [dist_eq_norm] at h1
        rw [mem_closedBall_zero_iff]
        calc ‖ψ n p.1‖ ≤ ‖a * p.1‖ + ‖a * p.1 - ψ n p.1‖ := by
              have := norm_sub_norm_le (ψ n p.1) (a * p.1)
              rw [norm_sub_rev] at this
              linarith [norm_sub_rev (a * p.1) (ψ n p.1)]
          _ ≤ ‖a‖ * |ρ| + 1 := by
              rw [norm_mul]
              gcongr
              exact hp1.le.trans (le_abs_self ρ)
      have hyb : ψ n p.2 ∈ closedBall (0 : ℂ) b := by
        have h1 := hunn p.2 (mem_closedBall_zero_iff.2 (hp2.le.trans (le_abs_self ρ)))
        rw [dist_eq_norm] at h1
        rw [mem_closedBall_zero_iff]
        calc ‖ψ n p.2‖ ≤ ‖a * p.2‖ + ‖a * p.2 - ψ n p.2‖ := by
              have := norm_sub_norm_le (ψ n p.2) (a * p.2)
              rw [norm_sub_rev] at this
              linarith [norm_sub_rev (a * p.2) (ψ n p.2)]
          _ ≤ ‖a‖ * |ρ| + 1 := by
              rw [norm_mul]
              gcongr
              exact hp2.le.trans (le_abs_self ρ)
      have hY₁ : closedBall (0 : ℂ) S₀' ⊆ ψ n '' closedBall (0 : ℂ) (R n) :=
        (closedBall_subset_closedBall hS₀S).trans (hM S n hMn)
      have hY₂ : closedBall (0 : ℂ) S₀' ⊆ closedBall (0 : ℂ) ((S : ℝ) + 1) :=
        closedBall_subset_closedBall hS₀S
      have hYc : IsCompact (ψ n '' closedBall (0 : ℂ) (R n)) :=
        (isCompact_closedBall _ _).image_of_continuousOn ((hd n).continuousOn.mono (hcl n))
      have e1 := hgood _ hYc hY₁ (hY n) _ hxb _ hyb
      have e2 := hgood _ (isCompact_closedBall _ _) hY₂ hS1V _ hxb _ hyb
      unfold tangentE extendTop
      rw [if_pos ⟨hp1K, hp2K⟩, if_pos ⟨hp1K, hp2K⟩, hTω]
      simp only [targetFixed, dif_pos hS1V]
      rw [e1, e2]
    · rw [show P Bad2 = 0 from ae_iff.1 (hT'eq S n), add_zero]
      exact hPn
  have hexp := subseqLSC_expanding P hopen hzeroU hexhaust hd hinj hzero ha0 ha hR T' TL Tinf
    hTm hTLm hfix hlimS (tangentE (ξ : ℝ) D V ψ R hY hbar fr) M hbarE
  refine hexp.congr_ae (fun n => Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [ae_affine_tangent hQ hD P hhc ha0] with ω hω
  funext q
  simp only [hTinf, LSCMetric.toLSCFun]
  rw [hω q.1 q.2]

end SupercriticalConformalCovariance.Tangent
