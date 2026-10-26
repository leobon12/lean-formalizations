import SupercriticalConformalCovariance.Tangent.FixedCore
import SupercriticalConformalCovariance.Tangent.Realize
import SupercriticalConformalCovariance.Tangent.WeylSandwich
import SupercriticalConformalCovariance.Tangent.EpigraphPullback
import SupercriticalConformalCovariance.GM24.Law
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LQGMetric.Papers.GM.S1.Subseq

/-!
# Lemma 3.3, steps 1–3: fixed confinement for the transformed fields

Paper l. 206–221, for one fixed target radius `S`. With `h` normalized by `(h, 𝐟) = 0` (step 1)
and `α = a⁻¹`, the target metrics `T^S_n = D_{h^{ψ_n}}(·,·; B̄_S)` (realized, `confined`, `+∞` off
`B̄_S × B̄_S`) converge in probability to `T^S = D_{h^a}(·,·; B̄_S)`, `h^a = h(a⁻¹·) − Q log |a|`
(`subseqLSC_fixed`).

Inputs: GM Lemma 2.4 (2.6) on centred disks, consumed as the explicit hypothesis `GMLemma24TV`
(discharged by the proof of Gwynne–Miller Lemma 2.4's input-free `tendsto_tvDist_gm24_closed`); GM (2.5) and the constants; Koebe (the Koebe estimates,
proved); the realization plumbing (`ae_restrictTo_normField`); the Weyl sandwich
(`ae_sandwich_confined`); the abstract core (`subseqLSC_fixedCore`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric Function
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open LQGMetric (DistC DistOn TestOn TestC restrictTo addFun addConst ofCont IsGFFPlusCont
  IsWholePlaneGFF pairJ CoordJ)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric LSCTendsto)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (closedBallPathInf)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open SupercriticalConformalCovariance.Domain (confined cutF exW exWO exWO_le exW_subset exists_subset_exW)
open SupercriticalConformalCovariance.GM24 (invPullDist isConformalBijection_invFunOn dilDist nrm frOn smoothTest smoothAvg
  invPullSmoothAvg)
open QuantumZipper.TV (tvDist)
open SmallGammaGeodesics.CC (intDist intDist_apply)

open scoped Classical in
/-- **Input (I4), GM Lemma 2.4 display (2.6)**, repaired scale `|α|⁻¹`, on centred disks, as
consumed by Lemma 3.3 (paper l. 212–214). This is the conclusion of the proof of Gwynne–Miller Lemma 2.4's
input-free `SupercriticalConformalCovariance.GM24.tendsto_tvDist_gm24_closed` (`GM24/Closed.lean`), quantified over its
setting. -/
def GMLemma24TV : Prop :=
  ∀ {U : ℕ → Set ℂ} {φ : ℕ → ℂ → ℂ} {α : ℂ} (hopen : ∀ n, IsOpen (U n)),
    (∀ n, (0 : ℂ) ∈ U n) → (∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n) →
    ∀ (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n)) (hinj : ∀ n, InjOn (φ n) (U n)),
    (∀ n, φ n 0 = 0) → ∀ (hα : α ≠ 0), Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹) →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC},
    IsWholePlaneGFF h P → ∀ {f : TestC}, ∫ x, f x = 1 →
    (∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) → (∀ᵐ ω ∂P, h ω f = 0) →
    ∀ {B : Opens ℂ} {R : ℝ}, (B : Set ℂ) = ball 0 R → 0 < R →
    ∀ (hFB : tsupport (smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f : ℂ → ℝ) ⊆ B),
    Tendsto (fun n => tvDist
      (P.map fun ω => if hn : (B : Set ℂ) ⊆ φ n '' U n then
        nrm (frOn hα f hFB) (invPullDist (hopen n) (hd n) (hinj n) B hn (h ω)) else 0)
      (P.map fun ω => restrictTo B (dilDist hα (h ω)))) atTop (𝓝 0)

/-- Uniform smallness of the Weyl correction on a closed disk, as an explicit sequence `ε_n → 0`
(paper l. 216: `Q log |(ψ_n⁻¹)′| + Q log |a| → 0` uniformly on compact sets). -/
theorem exists_eps_logDerivInv {U : ℕ → Set ℂ} {ψ : ℕ → ℂ → ℂ} {a : ℂ} (Q : ℝ)
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n)) (hinj : ∀ n, InjOn (ψ n) (U n))
    (hzero : ∀ n, ψ n 0 = 0) (ha0 : a ≠ 0) (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    (S : ℝ) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) S,
      |Q * Real.log ‖deriv (invFunOn (ψ n) (U n)) z‖ - -(Q * Real.log ‖a‖)| ≤ ε n := by
  obtain ⟨-, -, -, -, hlog⟩ :=
    SupercriticalConformalCovariance.Univalent.exhausting_univalent_limits Q hopen hzeroU hexhaust hd hinj hzero ha ha0
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).1 hlog
    (closedBall (0 : ℂ) S) (subset_univ _) (isCompact_closedBall _ _)
  set F : ℕ → ℂ → ℝ := fun n z => Q * Real.log ‖deriv (invFunOn (ψ n) (U n)) z‖ +
    Q * Real.log ‖a‖ with hF
  set ε' : ℕ → ℝ≥0∞ := fun n => ⨆ z ∈ closedBall (0 : ℂ) S, ENNReal.ofReal |F n z| with hε'
  have hε'0 : Tendsto ε' atTop (𝓝 0) := by
    refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
    rcases eq_or_ne δ ⊤ with hδt | hδt
    · exact Eventually.of_forall fun _ => hδt ▸ le_top
    have hδr : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu δ.toReal hδr] with n hn
    refine iSup₂_le fun z hz => ?_
    have := hn z hz
    rw [Real.dist_eq, zero_sub, abs_neg] at this
    rw [← ENNReal.ofReal_toReal hδt]
    exact ENNReal.ofReal_le_ofReal this.le
  refine ⟨fun n => (ε' n).toReal, ?_, ?_⟩
  · have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hε'0
    simpa [Function.comp_def] using this
  · filter_upwards [hε'0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))] with n hn z hz
    have hle : ENNReal.ofReal |F n z| ≤ ε' n := le_iSup₂_of_le z hz le_rfl
    have hfin : ε' n ≠ ⊤ := (hn.trans ENNReal.one_lt_top).ne
    have : |F n z| ≤ (ε' n).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 hle
    simpa [hF, sub_neg_eq_add] using this

/-- The target metric `D_{h^{ψ_n}}(·, ·; B̄_S)` of the realized transformed field, `+∞` off
`B̄_S × B̄_S` (and `+∞` everywhere if `B̄_S ⊄ V_n`). -/
def targetFixed (ξ : ℝ) (D : DistC → LSCMetric) {Ω : Type} (V : ℕ → Opens ℂ)
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ)) (S : ℝ) (n : ℕ) (ω : Ω) (q : ℂ × ℂ) :
    ℝ≥0∞ :=
  open Classical in
  if hS : closedBall (0 : ℂ) S ⊆ (V n : Set ℂ) then confined ξ (D (hbar n ω)) hS (fr n ω) q else ⊤

/-- The open disk `B_ρ(0)`. -/
def ballO (ρ : ℝ) : Opens ℂ := ⟨ball 0 ρ, isOpen_ball⟩

theorem measurable_nrm_invPullDist {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W)
    (hd : DifferentiableOn ℂ φ W) (hi : InjOn φ W) {B : Opens ℂ} (hB : (B : Set ℂ) ⊆ φ '' W)
    (fr : TestOn B) {Ω : Type} [MeasurableSpace Ω] {h : Ω → DistC} (hh : Measurable h) :
    Measurable fun ω => nrm fr (invPullDist hW hd hi B hB (h ω)) := by
  refine LQGMetric.measurable_distOn_iff.2 fun g => ?_
  simp only [SupercriticalConformalCovariance.GM24.nrm_apply]
  have h1 : ∀ k : TestOn B, Measurable fun ω => invPullDist hW hd hi B hB (h ω) k := fun k =>
    (LQGMetric.measurable_distOn_apply
      (SmallGammaGeodesics.CC.confPullOnCLM hW hd hi B hB k)).comp hh
  exact (h1 g).sub ((h1 fr).mul_const _)

/-- **The normalized transformed fields** near a fixed disk (paper l. 206–215): whole-plane
representatives `G n` of `(h ∘ ψ_n⁻¹ − c_n)` near `B̄_ρ`, their coordinates converging to those of
`h(a⁻¹·)` almost surely (GM (2.5)) and in total variation (GM (2.6)). -/
theorem exists_normField_package {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (hTV : GMLemma24TV)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {f : TestC} (hf1 : ∫ x, f x = 1)
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) (hnorm : ∀ᵐ ω ∂P, h ω f = 0)
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n))
    {S : ℝ} (hS : 0 < S) :
    ∃ (ρ : ℝ) (N₀ : ℕ) (m : ℕ → ℕ) (c : ℕ → Ω → ℝ) (G : ℕ → Ω → DistC),
      S < ρ ∧ (∀ n, Measurable (c n)) ∧ (∀ᵐ ω ∂P, Tendsto (fun n => c n ω) atTop (𝓝 0)) ∧
      (∀ n, IsGFFPlusCont (G n) P) ∧
      (∀ n, N₀ ≤ n → closedBall (0 : ℂ) ρ ⊆ (V n : Set ℂ) ∧
        closedBall (0 : ℂ) ρ ⊆ exW (V n) (m n) ∧ ∀ ω, G n ω = addFun (hbar n ω)
          (cutF (V n) (m n) (fr n ω) - cutF (V n) (m n) (logDerivInv Q (hψ n)) -
            ContinuousMap.const ℂ (c n ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => locCoord (ballO ρ) (G n ω)) atTop
        (𝓝 (locCoord (ballO ρ) (dilDist (inv_ne_zero ha0) (h ω))))) ∧
      Tendsto (fun n => tvDist (P.map fun ω => locCoord (ballO ρ) (G n ω))
        (P.map fun ω => locCoord (ballO ρ) (dilDist (inv_ne_zero ha0) (h ω)))) atTop (𝓝 0) := by
  classical
  set α : ℂ := a⁻¹ with hαdef
  have hα : α ≠ 0 := inv_ne_zero ha0
  have hder : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 α⁻¹) := by rw [hαdef, inv_inv]; exact ha
  have hopen : ∀ n, IsOpen (U n : Set ℂ) := fun n => (U n).isOpen
  have hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n) := fun n => (hψ n).1
  have hinj : ∀ n, InjOn (ψ n) (U n) := fun n => (hψ n).2.injOn
  have himg : ∀ n, ψ n '' (U n : Set ℂ) = V n := fun n => (hψ n).2.image_eq
  have hr : (0 : ℝ) < ‖α‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hα)
  set ℓ : ℝ := -(Q * Real.log ‖a‖) with hℓ
  -- the disk `B`
  obtain ⟨ρf, hρf⟩ := (smoothTest hr f).hasCompactSupport.isCompact.isBounded.subset_ball 0
  set ρ : ℝ := max (S + 1) ρf with hρ
  have hSρ : S < ρ := lt_of_lt_of_le (lt_add_one S) (le_max_left _ _)
  have hρpos : 0 < ρ := hS.trans hSρ
  set B : Opens ℂ := ballO ρ with hBdef
  have hSB : closedBall (0 : ℂ) S ⊆ B := closedBall_subset_ball hSρ
  have hFB : tsupport (smoothTest hr f : ℂ → ℝ) ⊆ B :=
    hρf.trans (ball_subset_ball (le_max_right _ _))
  -- geometry
  have hgeo : ∀ᶠ n in atTop, closedBall (0 : ℂ) ρ ⊆ (V n : Set ℂ) := by
    filter_upwards [eventually_closedBall_subset_image (U := fun n => (U n : Set ℂ)) hopen hzeroU
      hexhaust hd hinj hzero ha0 ha ρ] with n hn
    rwa [himg n] at hn
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hgeo
  have hmex : ∀ n, ∃ m : ℕ, closedBall (0 : ℂ) ρ ⊆ (V n : Set ℂ) →
      closedBall (0 : ℂ) ρ ⊆ exW (V n) m := by
    intro n
    by_cases hn : closedBall (0 : ℂ) ρ ⊆ (V n : Set ℂ)
    · obtain ⟨m, hm⟩ := exists_subset_exW (V n).isOpen (isCompact_closedBall 0 ρ) hn
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h' => absurd h' hn⟩
  choose m hm using hmex
  have hBn : ∀ n, N₀ ≤ n → (B : Set ℂ) ⊆ ψ n '' U n := fun n hn => by
    rw [himg n]; exact ball_subset_closedBall.trans (hN₀ n hn)
  -- the smooth averages
  set c : ℕ → Ω → ℝ := fun n ω => invPullSmoothAvg (U n) (ψ n) (h ω) f hr with hcdef
  have hcm : ∀ n, Measurable (c n) := by
    intro n
    simp only [hcdef, invPullSmoothAvg, SupercriticalConformalCovariance.GM24.invPullPair]
    split_ifs
    · exact (LQGMetric.measurable_distOn_apply _).comp hh.measurable
    · exact measurable_const
  have hc0 : ∀ᵐ ω ∂P, Tendsto (fun n => c n ω) atTop (𝓝 0) := by
    filter_upwards [hnorm] with ω hω
    have := SupercriticalConformalCovariance.GM24.tendsto_invPullSmoothAvg hopen hzeroU hexhaust hd hinj hzero hα hder (h ω)
      f hr
    rwa [SupercriticalConformalCovariance.GM24.dilDist_smoothAvg_inv_norm hα (h ω) hrot, SupercriticalConformalCovariance.GM24.smoothAvg_one, hω] at this
  -- the fields
  set G : ℕ → Ω → DistC := fun n ω =>
    if closedBall (0 : ℂ) ρ ⊆ (V n : Set ℂ) then addFun (hbar n ω)
      (cutF (V n) (m n) (fr n ω) - cutF (V n) (m n) (logDerivInv Q (hψ n)) -
        ContinuousMap.const ℂ (c n ω))
    else dilDist hα (h ω) with hGdef
  set Glim : Ω → DistC := fun ω => dilDist hα (h ω) with hGlimdef
  have hGlimW : IsWholePlaneGFF Glim P := SupercriticalConformalCovariance.GM24.isWholePlaneGFF_dilDist hh hα
  have hGlim : IsGFFPlusCont Glim P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hGlimW
  have hG : ∀ n, IsGFFPlusCont (G n) P := by
    intro n
    by_cases hn : closedBall (0 : ℂ) ρ ⊆ (V n : Set ℂ)
    · simp only [hGdef, if_pos hn]
      exact SupercriticalConformalCovariance.Domain.isGFFPlusCont_addFun_of_measurable (hreal n).2.1
        (measurable_cutF_sub (hreal n).2.2.1 _ _ (hcm n))
    · simp only [hGdef, if_neg hn]
      exact hGlim
  -- the restricted fields are GM's normalized fields
  have hrestr : ∀ᵐ ω ∂P, ∀ n, N₀ ≤ n → ∀ hB' : (B : Set ℂ) ⊆ ψ n '' U n,
      restrictTo B (G n ω) =
        nrm (frOn hα f hFB) (invPullDist (hopen n) (hd n) (hinj n) B hB' (h ω)) := by
    rw [ae_all_iff]
    intro n
    by_cases hn : N₀ ≤ n
    · have hVn := hN₀ n hn
      have hBm : B ≤ exWO (V n) (m n) := fun z hz => hm n hVn (ball_subset_closedBall hz)
      filter_upwards [ae_restrictTo_normField Q (hψ n) (hreal n) (m n) hBm (hBn n hn) (c n)]
        with ω hω _ hB'
      simp only [hGdef, if_pos hVn]
      rw [hω]
      ext g
      rw [SupercriticalConformalCovariance.GM24.nrm_invPullDist_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, intDist_apply, smul_eq_mul]
    · exact Eventually.of_forall fun ω hn' => absurd hn' hn
  -- (2.5) and the constants: the coordinates converge
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => locCoord B (G n ω)) atTop (𝓝 (locCoord B (Glim ω))) := by
    filter_upwards [hrestr, hc0] with ω hω hcω
    rw [tendsto_pi_nhds]
    intro j
    obtain ⟨-, hconvg⟩ := SupercriticalConformalCovariance.GM24.tendsto_invPullDist hopen hzeroU hexhaust hd hinj hzero hα hder
      (h ω) B isBounded_ball
    set g : TestOn B := LQGMetric.comb B j with hg
    have h3 := (hconvg g).sub (hcω.mul_const (∫ x, g x))
    rw [zero_mul, sub_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop N₀] with n hn
    rw [dif_pos (hBn n hn)]
    show _ = restrictTo B (G n ω) g
    rw [hω n hn (hBn n hn), SupercriticalConformalCovariance.GM24.nrm_invPullDist_apply]
  -- (2.6): the coordinate laws converge in total variation
  have hTVc : Tendsto (fun n => tvDist (P.map fun ω => locCoord B (G n ω))
      (P.map fun ω => locCoord B (Glim ω))) atTop (𝓝 0) := by
    have hgm := hTV hopen hzeroU hexhaust hd hinj hzero hα hder P hh hf1 hrot hnorm
      (B := B) (R := ρ) rfl hρpos hFB
    set X : ℕ → Ω → DistOn B := fun n ω => if hn : (B : Set ℂ) ⊆ ψ n '' U n then
      nrm (frOn hα f hFB) (invPullDist (hopen n) (hd n) (hinj n) B hn (h ω)) else 0 with hX
    have hXm : ∀ n, Measurable (X n) := by
      intro n
      by_cases hn : (B : Set ℂ) ⊆ ψ n '' U n
      · simp only [hX, dif_pos hn]
        exact measurable_nrm_invPullDist _ _ _ _ _ hh.measurable
      · simp only [hX, dif_neg hn]
        exact measurable_const
    have hYm : Measurable fun ω => restrictTo B (dilDist hα (h ω)) :=
      (LQGMetric.measurable_restrictTo B).comp hGlimW.measurable
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgm
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop N₀] with n hn
    have e1 : P.map (fun ω => locCoord B (G n ω)) = (P.map (X n)).map (pairJ B) := by
      rw [Measure.map_map (LQGMetric.measurable_pairJ B) (hXm n)]
      refine Measure.map_congr ?_
      filter_upwards [hrestr] with ω hω
      simp only [Function.comp_apply, hX, dif_pos (hBn n hn), locCoord]
      rw [hω n hn (hBn n hn)]
    have e2 : P.map (fun ω => locCoord B (Glim ω)) =
        (P.map fun ω => restrictTo B (dilDist hα (h ω))).map (pairJ B) := by
      rw [Measure.map_map (LQGMetric.measurable_pairJ B) hYm]
      rfl
    rw [e1, e2]
    exact QuantumZipper.TV.tvDist_map_le (LQGMetric.measurable_pairJ B)
  refine ⟨ρ, N₀, m, c, G, hSρ, hcm, hc0, hG, fun n hn => ⟨hN₀ n hn, hm n (hN₀ n hn), fun ω => ?_⟩,
    hconv, hTVc⟩
  simp only [hGdef, if_pos (hN₀ n hn)]

/-- **Fixed confinement** (paper l. 206–221) for one target radius `S`: the realized target
metrics on `B̄_S` converge in probability, in the topology of DG Definition 1.2, to the metric of
`h^a = h(a⁻¹·) − Q log |a|` on `B̄_S`. -/
theorem subseqLSC_fixed {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (hTV : GMLemma24TV)
    {U V : ℕ → Opens ℂ} {ψ : ℕ → ℂ → ℂ} (hψ : ∀ n, IsConformalBijection (ψ n) (U n) (V n))
    (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ (U n : Set ℂ))
    (hzero : ∀ n, ψ n 0 = 0) {a : ℂ} (ha0 : a ≠ 0)
    (ha : Tendsto (fun n => deriv (ψ n) 0) atTop (𝓝 a))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {f : TestC} (hf1 : ∫ x, f x = 1)
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) (hnorm : ∀ᵐ ω ∂P, h ω f = 0)
    (hbar : ℕ → Ω → DistC) (fr : ∀ n, Ω → C(V n, ℝ))
    (hreal : ∀ n, IsDomainRealization (V n) P
      (fun ω => confPullbackField Q (isConformalBijection_invFunOn (hψ n)) (restrictTo (U n) (h ω)))
      (hbar n) (fr n))
    {S : ℝ} (hS : 0 < S) :
    SubseqLSC P (fun n ω q => (targetFixed (ξ : ℝ) D V hbar fr S n ω q : EReal))
      (fun ω q => (extInternal (D (addConst (dilDist (inv_ne_zero ha0) (h ω))
        (-(Q * Real.log ‖a‖)))) (closedBall 0 S) q : EReal)) := by
  classical
  set α : ℂ := a⁻¹ with hαdef
  have hα : α ≠ 0 := inv_ne_zero ha0
  have hopen : ∀ n, IsOpen (U n : Set ℂ) := fun n => (U n).isOpen
  have hd : ∀ n, DifferentiableOn ℂ (ψ n) (U n) := fun n => (hψ n).1
  have hinj : ∀ n, InjOn (ψ n) (U n) := fun n => (hψ n).2.injOn
  set ℓ : ℝ := -(Q * Real.log ‖a‖) with hℓ
  obtain ⟨ρ, N₀, m, c, G, hSρ, hcm, hc0, hG, hGn, hconv, hTVc⟩ :=
    exists_normField_package hD hTV hψ hzeroU hexhaust hzero ha0 ha P hh hf1 hrot hnorm hbar fr
      hreal hS
  set B : Opens ℂ := ballO ρ with hBdef
  have hSB : closedBall (0 : ℂ) S ⊆ B := closedBall_subset_ball hSρ
  set Glim : Ω → DistC := fun ω => dilDist hα (h ω) with hGlimdef
  have hGlimW : IsWholePlaneGFF Glim P := SupercriticalConformalCovariance.GM24.isWholePlaneGFF_dilDist hh hα
  have hGlim : IsGFFPlusCont Glim P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hGlimW
  have hN₀ : ∀ n, N₀ ≤ n → closedBall (0 : ℂ) ρ ⊆ (V n : Set ℂ) := fun n hn => (hGn n hn).1
  -- the Weyl sandwich
  obtain ⟨ε, hε0, hεb⟩ := exists_eps_logDerivInv Q hopen hzeroU hexhaust hd hinj hzero ha0 ha S
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hεb
  set aF : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Real.exp ((ξ : ℝ) * (c n ω + ℓ - ε n)))
    with haF
  set bF : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Real.exp ((ξ : ℝ) * (c n ω + ℓ + ε n)))
    with hbF
  set cl : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * ℓ)) with hcl
  have hcl0 : cl ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hcltop : cl ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsandn : ∀ n, ∀ᵐ ω ∂P, max N₀ N₁ ≤ n → ∀ q : ℂ × ℂ,
      aF n ω * closedBallPathInf (D (G n ω)) 0 S q.1 q.2 ≤
          targetFixed (ξ : ℝ) D V hbar fr S n ω q ∧
        targetFixed (ξ : ℝ) D V hbar fr S n ω q ≤
          bF n ω * closedBallPathInf (D (G n ω)) 0 S q.1 q.2 := by
    intro n
    by_cases hn : max N₀ N₁ ≤ n
    · have hSm : closedBall (0 : ℂ) S ⊆ exW (V n) (m n) :=
        (closedBall_subset_closedBall hSρ.le).trans (hGn n (le_of_max_le_left hn)).2.1
      have hLε : ∀ z (hz : z ∈ closedBall (0 : ℂ) S),
          |logDerivInv Q (hψ n) ⟨z, exW_subset (V n) (m n) (hSm hz)⟩ - ℓ| ≤ ε n :=
        fun z hz => hN₁ n (le_of_max_le_right hn) z hz
      filter_upwards [ae_sandwich_confined hD P (hreal n).2.1 (hreal n).2.2.1 (m n) hSm
        (logDerivInv Q (hψ n)) (hcm n) ℓ (ε n) hLε] with ω hω _ q
      have hT : targetFixed (ξ : ℝ) D V hbar fr S n ω q =
          confined (ξ : ℝ) (D (hbar n ω)) (hSm.trans (exW_subset (V n) (m n))) (fr n ω) q := by
        simp only [targetFixed, dif_pos (hSm.trans (exW_subset (V n) (m n)))]
      rw [hT, (hGn n (le_of_max_le_left hn)).2.2 ω]
      exact hω q
    · exact Eventually.of_forall fun ω hn' => absurd hn' hn
  have hsand : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ q : ℂ × ℂ,
      aF n ω * closedBallPathInf (D (G n ω)) 0 S q.1 q.2 ≤
          targetFixed (ξ : ℝ) D V hbar fr S n ω q ∧
        targetFixed (ξ : ℝ) D V hbar fr S n ω q ≤
          bF n ω * closedBallPathInf (D (G n ω)) 0 S q.1 q.2 := by
    filter_upwards [ae_all_iff.2 hsandn] with ω hω
    filter_upwards [eventually_ge_atTop (max N₀ N₁)] with n hn
    exact hω n hn
  have hab : ∀ᵐ ω ∂P, Tendsto (fun n => aF n ω) atTop (𝓝 cl) ∧
      Tendsto (fun n => bF n ω) atTop (𝓝 cl) := by
    filter_upwards [hc0] with ω hcω
    have hcont : Continuous fun t : ℝ => ENNReal.ofReal (Real.exp ((ξ : ℝ) * t)) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
        continuous_id))
    have h1 : Tendsto (fun n => c n ω + ℓ - ε n) atTop (𝓝 ℓ) := by
      simpa using (hcω.add_const ℓ).sub hε0
    have h2 : Tendsto (fun n => c n ω + ℓ + ε n) atTop (𝓝 ℓ) := by
      simpa using (hcω.add_const ℓ).add hε0
    exact ⟨(hcont.tendsto ℓ).comp h1, (hcont.tendsto ℓ).comp h2⟩
  -- the limit
  have hweak := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  have hlim : ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
      extInternal (D (addConst (dilDist hα (h ω)) ℓ)) (closedBall 0 S) q =
        cl * closedBallPathInf (D (Glim ω)) 0 S q.1 q.2 := by
    filter_upwards [SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul
      P Glim hGlim ξ Q D hweak (fun _ => ℓ)] with ω hω q
    rw [closedBallPathInf_eq_extInternal]
    unfold extInternal
    split_ifs with hq
    · exact SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.internal_eq_mul_of_dist_scale
        _ _ cl hcl0 hcltop (fun x y => hω (x, y)) _ _
    · rw [ENNReal.mul_top hcl0]
  exact subseqLSC_fixedCore hD B hSB P G Glim hG hGlim hconv hTVc _ _ aF bF (fun _ => cl)
    (Eventually.of_forall fun _ => ⟨hcl0, hcltop⟩) hab hsand hlim

end SupercriticalConformalCovariance.Tangent
