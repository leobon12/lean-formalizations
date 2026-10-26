import SupercriticalConformalCovariance.BiLip.Step2Sample
import SupercriticalConformalCovariance.BiLip.Step2
import SupercriticalConformalCovariance.GM24.Closed
import LQGMetric.Field.MarkovWeyl2Rad
import LQGMetric.Field.CircleAvgAffine
import LQGMetric.Field.CircleAvgRate
import LQGMetric.Field.MeasurableAvg
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.B2.Strong.Annulus
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.Bridges

/-!
# Lemma 2.1, step 2: the sequential tightness `TargetTightSeq`

Paper l. 112–125. Along a sequence of instances `(U_n, φ_n, h_n, …)` and pairs `(z_n, r_n)` with
`r_n / s_n → 0`, `B_{s_n}(z_n) ⊆ U_n`:
* per instance (`ae_tail_bound`, from `ae_rescaled`): almost surely the two normalized target quantities
  are bounded by `e^{ξ(W_n(ĥ_n) ± 2|Q|ε)}` times a fixed measurable local functional of the GM-normalized
  transformed field `Φ_n(ĥ_n) = (ĥ_n ∘ F_n⁻¹ − c₀)|_{B_3(0)}`, where `ĥ_n` is the `𝐟`-normalized rescaled
  source field and `W_n = c₀ − (ĥ_n)_1(0)`;
* every `ĥ_n` has one law (`map_eq_of_normalized`), so all probabilities move to one canonical field `ĥ₀`;
* GM Lemma 2.4 (2.6) (`tendsto_tvDist_gm24_open`, `α = 1`): `law Φ_n(ĥ₀) → law ĥ₀(1 ·)|_{B_3(0)}` in total
  variation; the local functionals are a.s. finite and positive along the sequence, hence on the limit law;
* `c₀(ĥ₀) → 0` pointwise (`tendsto_invPullSmoothAvg`) and `(ĥ₀)_1(0)` is one real random variable.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric weylScale aroundDist EuclideanAnnulus IsStrongLQGMetric
  IsLFPPExponent)
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (acr)
open SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails (nrm)
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField IsDomainRealization)
open LQGMetric (DistC DistOn TestC restrictTo addFun addConst affineComp IsGFFPlusCont
  IsWholePlaneGFF CoordJ)
open SupercriticalConformalCovariance.Domain (exW exWO cutF)
open SmallGammaGeodesics.CC (intDist)
open SupercriticalConformalCovariance.GM24 (invPullDist invPullSmoothAvg)
open SupercriticalConformalCovariance.BiLip.PortTan (locCoord)

section Instance

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

theorem isGFFPlusCont_rescG {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h g₀ : Ω → DistC}
    {k : Ω → C(V, ℝ)} (hI : IsInstance Q U V hφ P h g₀ k) (m : ℕ) (z : ℂ) (r s : ℝ) (f : TestC) :
    IsGFFPlusCont (fun ω => rescG Q hφ m z r s f (h ω) (g₀ ω) (k ω)) P := by
  obtain ⟨hhn, hR⟩ := hI
  have hCm : Measurable fun ω => rescConst Q φ z r s f (h ω) :=
    (measurable_rescConst Q φ z r s f).comp hhn.1.measurable
  have hFgm : Measurable fun ω => cutF V m (k ω) - cutF V m (SupercriticalConformalCovariance.BiLip.PortTan.logDerivInv Q hφ) -
      ContinuousMap.const ℂ (rescConst Q φ z r s f (h ω)) := by
    have hk := SupercriticalConformalCovariance.Domain.measurable_cutExt V.isOpen (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset (V : Set ℂ) m)
      hR.2.2.1
    rw [ContinuousMap.measurable_iff_eval] at hk ⊢
    intro x
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
    exact ((hk x).sub measurable_const).sub hCm
  exact SupercriticalConformalCovariance.Domain.isGFFPlusCont_addFun_of_measurable hR.2.1 hFgm

theorem isGFFPlusCont_rescG' {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h g₀ : Ω → DistC}
    {k : Ω → C(V, ℝ)} (hI : IsInstance Q U V hφ P h g₀ k) (m : ℕ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hφz : deriv φ z ≠ 0) (s : ℝ) (f : TestC) :
    IsGFFPlusCont (fun ω => rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω)) P := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : (r : ℂ) * deriv φ z ≠ 0 := mul_ne_zero hrC hφz
  have h1 := LQGMetric.GM.isGFFPlusCont_affineComp (isGFFPlusCont_rescG hφ hI m z r s f)
    (norm_pos_iff.2 ha) (φ z)
  have h2 := SupercriticalConformalCovariance.Rotation.isGFFPlusCont_rotDist h1 (GaussianLQG.norm_div_norm_eq_one ha)
  exact SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.isGFFPlusCont_addConst h2
    measurable_const

/-- the shift `W(ĥ) = c₀(ĥ) − ĥ_1(0)` -/
def wShift (φ : ℂ → ℂ) (z : ℂ) (r s : ℝ) (f : TestC) (u : DistC) : ℝ :=
  gmConst φ z r s f u - LQGMetric.circleAvg u 1 0

/-- GM's normalized transformed field `Φ(ĥ) = (ĥ ∘ F⁻¹ − c₀(ĥ))|_{B_3(0)}` -/
def phiN {φ : ℂ → ℂ} {z : ℂ} {r s : ℝ} (f : TestC)
    (hFd : DifferentiableOn ℂ (normMap φ z r) (ball 0 (s / r)))
    (hFi : InjOn (normMap φ z r) (ball 0 (s / r)))
    (hOimg : (ballO 0 3 : Set ℂ) ⊆ normMap φ z r '' ball 0 (s / r)) (u : DistC) : DistOn (ballO 0 3) :=
  invPullDist isOpen_ball hFd hFi (ballO 0 3) hOimg u - gmConst φ z r s f u • intDist (ballO 0 3)

theorem measurable_wShift (φ : ℂ → ℂ) (z : ℂ) (r s : ℝ) (f : TestC) :
    Measurable (wShift φ z r s f) :=
  (measurable_gmConst φ z r s f).sub (LQGMetric.measurable_circleAvg_left 1 0)

theorem measurable_phiN {φ : ℂ → ℂ} {z : ℂ} {r s : ℝ} (f : TestC)
    (hFd : DifferentiableOn ℂ (normMap φ z r) (ball 0 (s / r)))
    (hFi : InjOn (normMap φ z r) (ball 0 (s / r)))
    (hOimg : (ballO 0 3 : Set ℂ) ⊆ normMap φ z r '' ball 0 (s / r)) :
    Measurable (phiN f hFd hFi hOimg) := by
  refine LQGMetric.measurable_distOn_iff.2 fun g => ?_
  have e : (fun u => phiN f hFd hFi hOimg u g) = fun u =>
      u (SmallGammaGeodesics.CC.confPullOnCLM isOpen_ball hFd hFi (ballO 0 3) hOimg g) -
        gmConst φ z r s f u * intDist (ballO 0 3) g := by
    funext u; rfl
  rw [e]
  exact (LQGMetric.measurable_distOn_apply _).sub ((measurable_gmConst φ z r s f).mul measurable_const)

theorem exp_split {ξ' Q r R g c ca : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (Real.exp (ξ' * (Q * Real.log r + R + g + c))) =
      ENNReal.ofReal (r ^ (ξ' * Q) * Real.exp (ξ' * ca)) *
        ENNReal.ofReal (Real.exp (ξ' * (g - (ca - R) + c))) := by
  rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_def_of_pos hr, mul_assoc, ← Real.exp_add,
    ← Real.exp_add]
  congr 2
  ring

/-- the fixed target annulus `A_{9/8,15/8}(0)` of the rescaled picture -/
def annA : EuclideanAnnulus := ⟨((0 : ℂ), 9 / 8, 15 / 8), by norm_num, by norm_num⟩

/-- **One instance, normalized** (l. 112–123): almost surely the two target quantities, divided by the
source normalization `m_{z,r} = r^{ξQ} e^{ξ h_r(z)}`, are bounded through `W(ĥ)` and local functionals
of `Φ(ĥ)`. -/
theorem ae_tail_bound (hQ : IsLFPPExponent ξ Q) (hD : IsStrongLQGMetric ξ Q D)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h g₀ : Ω → DistC} {k : Ω → C(V, ℝ)}
    (hI : IsInstance Q U V hφ P h g₀ k) {z : ℂ} {r s ε : ℝ} (hs : 0 < s) (hzs : ball z s ⊆ U)
    (hG : GeomGood φ U z r ε) (hε : ε ≤ 1 / 32) (h4 : 4 * r < s) {m : ℕ}
    (hm : closedBall (φ z) (3 * (r * ‖deriv φ z‖)) ⊆ exW V m) (f : TestC)
    (hFd : DifferentiableOn ℂ (normMap φ z r) (ball 0 (s / r)))
    (hFi : InjOn (normMap φ z r) (ball 0 (s / r)))
    (hOimg : (ballO 0 3 : Set ℂ) ⊆ normMap φ z r '' ball 0 (s / r))
    {Fa Fc : (CoordJ → ℝ) → ℝ≥0∞}
    (hFa : ∀ᵐ ω ∂P, aroundDist (D (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω))) annA =
      Fa (locCoord (ballO 0 3) (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω))))
    (hFc : ∀ᵐ ω ∂P, acr (D (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω))) 0 (5 / 8) (7 / 8) =
      Fc (locCoord (ballO 0 3) (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω)))) :
    ∀ᵐ ω ∂P,
      tAround (D (g₀ ω)) ξ (k ω) (φ z) (9 / 8 * (r * ‖deriv φ z‖)) (15 / 8 * (r * ‖deriv φ z‖)) ≤
          nrm ξ Q (h ω) r z *
            (ENNReal.ofReal (Real.exp (ξ * (wShift φ z r s f (normField f (h ω) z r) + 2 * |Q| * ε))) *
              Fa (LQGMetric.pairJ (ballO 0 3) (phiN f hFd hFi hOimg (normField f (h ω) z r)))) ∧
      nrm ξ Q (h ω) r z *
          (ENNReal.ofReal (Real.exp (ξ * (wShift φ z r s f (normField f (h ω) z r) - 2 * |Q| * ε))) *
            Fc (LQGMetric.pairJ (ballO 0 3) (phiN f hFd hFi hOimg (normField f (h ω) z r)))) ≤
        tAcr (D (g₀ ω)) ξ (k ω) (φ z) (5 / 8 * (r * ‖deriv φ z‖)) (7 / 8 * (r * ‖deriv φ z‖)) := by
  have hr := hG.1
  have hh : IsWholePlaneGFF h P := hI.1.1
  filter_upwards [ae_rescaled hQ hD hφ hI hs hzs hG hε h4 hm f hFd hFi hOimg, hFa, hFc,
    LQGMetric.CircleAvg.ae_circleAvg_affineComp hh hr z,
    LQGMetric.CircleAvg.ae_circleAvg_addConst (hh.affineComp hr z) 0 one_pos]
    with ω ⟨h1, h2, h3⟩ ea ec ca1 ca2
  have hloc : locCoord (ballO 0 3) (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω)) =
      LQGMetric.pairJ (ballO 0 3) (phiN f hFd hFi hOimg (normField f (h ω) z r)) := by
    unfold locCoord; rw [h1]; rfl
  have hca : LQGMetric.circleAvg (normField f (h ω) z r) 1 0 =
      LQGMetric.circleAvg (h ω) r z - rescaledField (h ω) z r f := by
    unfold normField rescaledField; rw [ca2, ca1]; ring
  have hW : ∀ c, wShift φ z r s f (normField f (h ω) z r) + c =
      gmConst φ z r s f (normField f (h ω) z r) -
        (LQGMetric.circleAvg (h ω) r z - rescaledField (h ω) z r f) + c := by
    intro c; unfold wShift; rw [hca]
  replace h2 : tAround (D (g₀ ω)) ξ (k ω) (φ z) (9 / 8 * (r * ‖deriv φ z‖))
      (15 / 8 * (r * ‖deriv φ z‖)) ≤
      ENNReal.ofReal (Real.exp (ξ * (Q * Real.log r + rescaledField (h ω) z r f +
        gmConst φ z r s f (normField f (h ω) z r) + 2 * |Q| * ε))) *
        aroundDist (D (rescG' Q hφ m z r s f (h ω) (g₀ ω) (k ω))) annA := h2
  rw [ea, hloc] at h2
  rw [ec, hloc] at h3
  have hn : nrm ξ Q (h ω) r z = ENNReal.ofReal (r ^ ((ξ : ℝ) * Q) *
      Real.exp (ξ * LQGMetric.circleAvg (h ω) r z)) := rfl
  constructor
  · rw [exp_split (ca := LQGMetric.circleAvg (h ω) r z) hr] at h2
    rw [hn, hW]; exact h2.trans_eq (mul_assoc _ _ _)
  · rw [sub_eq_add_neg _ (2 * |Q| * ε)] at h3 ⊢
    rw [exp_split (ca := LQGMetric.circleAvg (h ω) r z) hr] at h3
    rw [hn, hW]; exact (mul_assoc _ _ _).symm.trans_le h3

end Instance

section Helpers

theorem lt_or_lt_of_ofReal_mul_lt {M₁ M₂ : ℝ} (h₁ : 0 ≤ M₁) {x y : ℝ≥0∞}
    (h : ENNReal.ofReal (M₁ * M₂) < x * y) : ENNReal.ofReal M₁ < x ∨ ENNReal.ofReal M₂ < y := by
  by_contra hc
  push_neg at hc
  rw [ENNReal.ofReal_mul h₁] at h
  exact absurd (mul_le_mul' hc.1 hc.2) (not_le.2 h)

theorem lt_or_lt_of_mul_lt_ofReal_inv {M₁ M₂ : ℝ} (h₁ : 0 < M₁) (h₂ : 0 < M₂) {x y : ℝ≥0∞}
    (h : x * y < ENNReal.ofReal (M₁ * M₂)⁻¹) : x < ENNReal.ofReal M₁⁻¹ ∨ y < ENNReal.ofReal M₂⁻¹ := by
  by_contra hc
  push_neg at hc
  rw [mul_inv, ENNReal.ofReal_mul (inv_nonneg.2 h₁.le)] at h
  exact absurd (mul_le_mul' hc.1 hc.2) (not_le.2 h)

/-- law transfer of an event of a measurable function -/
theorem measure_preimage_eq_of_map_eq {Ω Ω' α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β] {P : Measure Ω} {P' : Measure Ω'} {X : Ω → α}
    {X' : Ω' → α} (hlaw : P.map X = P'.map X') (hX : Measurable X) (hX' : Measurable X')
    {ψ : α → β} (hψ : Measurable ψ) {S : Set β} (hS : MeasurableSet S) :
    P {ω | ψ (X ω) ∈ S} = P' {ω | ψ (X' ω) ∈ S} := by
  have e₁ : {ω | ψ (X ω) ∈ S} = X ⁻¹' (ψ ⁻¹' S) := rfl
  have e₂ : {ω | ψ (X' ω) ∈ S} = X' ⁻¹' (ψ ⁻¹' S) := rfl
  rw [e₁, e₂, ← Measure.map_apply hX (hψ hS), hlaw, Measure.map_apply hX' (hψ hS)]

/-- a decreasing sequence of events with null intersection eventually has small probability -/
theorem exists_measure_le_of_iInter {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {S : ℕ → Set α} (hS : ∀ n, MeasurableSet (S n)) (hanti : Antitone S)
    (h0 : μ (⋂ n, S n) = 0) {δ : ℝ} (hδ : 0 < δ) : ∃ n, μ (S n) ≤ ENNReal.ofReal δ := by
  have ht := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hS n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [h0] at ht
  obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).2 _ (ENNReal.ofReal_pos.2 hδ)).exists
  exact ⟨n, hn.le⟩

theorem tail_real_small {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {X : α → ℝ} (hX : Measurable X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, μ {a | K < |X a|} ≤ ENNReal.ofReal δ := by
  obtain ⟨n, hn⟩ := exists_measure_le_of_iInter (μ := μ) (S := fun n : ℕ => {a | (n : ℝ) < |X a|})
    (fun n => measurableSet_lt measurable_const hX.abs)
    (fun i j hij a ha => lt_of_le_of_lt (show (i : ℝ) ≤ j by exact_mod_cast hij) ha)
    (by
      rw [show (⋂ n : ℕ, {a | (n : ℝ) < |X a|}) = ∅ from ?_, measure_empty]
      ext a
      simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge |X a|
      exact ⟨n, hn⟩) hδ
  exact ⟨n, hn⟩

theorem tvDist_le_add {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {S : Set α}
    (hS : MeasurableSet S) : ν S ≤ μ S + QuantumZipper.TV.tvDist μ ν := by
  have := QuantumZipper.TV.le_tvDist' (μ := μ) (ν := ν) hS
  rw [tsub_le_iff_left] at this
  exact this

end Helpers

section Pieces

open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (cann)

theorem annA_subset : annA.toSet ⊆ (ballO 0 3 : Set ℂ) := by
  intro y hy
  rw [annA, annulus_toSet_mem (by norm_num) (by norm_num), Set.mem_sdiff, Metric.mem_ball] at hy
  show y ∈ ball (0 : ℂ) 3
  exact ball_subset_ball (by norm_num) hy.1

theorem cann_subset_ballO : cann (0 : ℂ) (5 / 8) (7 / 8) ⊆ (ballO 0 3 : Set ℂ) := by
  intro y hy
  have hy' : 5 / 8 ≤ dist y 0 ∧ dist y 0 ≤ 7 / 8 := hy
  show y ∈ ball (0 : ℂ) 3
  rw [mem_ball]; linarith [hy'.2]

/-- the radial test function `𝐟` (`∫ 𝐟 = 1`, supported in `B̄_1(0)`) -/
def radF : TestC := LQGMetric.MarkovWeyl2.rbTest (V := ⊤) (z := 0) one_pos (fun x _ => Set.mem_univ x)

theorem integral_radF : ∫ x, radF x = 1 := by
  have e : (fun x => radF x) = fun x => LQGMetric.MarkovWeyl2.rbump 1 x := by
    funext x; show LQGMetric.MarkovWeyl2.rbump 1 (x - 0) = _; rw [sub_zero]
  rw [e]; exact LQGMetric.MarkovWeyl2.integral_rbump one_pos

theorem radF_rot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, radF (u * z) = radF z := by
  intro u hu z
  show LQGMetric.MarkovWeyl2.rbump 1 (u * z - 0) = LQGMetric.MarkovWeyl2.rbump 1 (z - 0)
  simp [LQGMetric.MarkovWeyl2.rbump, LQGMetric.MarkovWeyl2.rbump0, norm_mul, hu]

theorem closedBall_subset_target {φ : ℂ → ℂ} {U V : Set ℂ} {z : ℂ} {r ε : ℝ}
    (hφ : IsConformalBijection φ U V) (hG : GeomGood φ U z r ε) :
    closedBall (φ z) (3 * (r * ‖deriv φ z‖)) ⊆ V := by
  intro y hy
  obtain ⟨hxB, hφx, -⟩ := geom_inv hG hφ.2.injOn hy
  rw [← hφx]
  exact hφ.2.mapsTo (hG.2.2.1 hxB)

theorem event_up {ξ' Q ε K M₂ gm ca : ℝ} (hξ : 0 < ξ') (hεQ : 2 * |Q| * ε ≤ 1) (hM₂ : 0 ≤ M₂)
    {n₀ T Y : ℝ≥0∞} (hn0 : n₀ ≠ 0) (hnt : n₀ ≠ ⊤)
    (hT : T ≤ n₀ * (ENNReal.ofReal (Real.exp (ξ' * (gm - ca + 2 * |Q| * ε))) * Y))
    (hlt : ENNReal.ofReal (Real.exp (ξ' * (K + 2)) * M₂) * n₀ < T) :
    1 ≤ |gm| ∨ K < |ca| ∨ ENNReal.ofReal M₂ < Y := by
  have h1 : n₀ * ENNReal.ofReal (Real.exp (ξ' * (K + 2)) * M₂) <
      n₀ * (ENNReal.ofReal (Real.exp (ξ' * (gm - ca + 2 * |Q| * ε))) * Y) := by
    rw [mul_comm]; exact hlt.trans_le hT
  have h2 := (ENNReal.mul_lt_mul_iff_right hn0 hnt).1 h1
  rcases lt_or_lt_of_ofReal_mul_lt (Real.exp_pos _).le h2 with h | h
  · have h' := (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).1 h
    rw [Real.exp_lt_exp] at h'
    have h'' : K + 2 < gm - ca + 2 * |Q| * ε := lt_of_mul_lt_mul_left h' hξ.le
    by_contra hc
    push_neg at hc
    have := neg_abs_le gm; have := le_abs_self gm; have := neg_abs_le ca; have := le_abs_self ca
    linarith [hc.1, hc.2.1]
  · exact Or.inr (Or.inr h)

theorem event_down {ξ' Q ε K M₂ gm ca : ℝ} (hξ : 0 < ξ') (hεQ : 2 * |Q| * ε ≤ 1) (hM₂ : 0 < M₂)
    {n₀ T Y : ℝ≥0∞} (hn0 : n₀ ≠ 0) (hnt : n₀ ≠ ⊤)
    (hT : n₀ * (ENNReal.ofReal (Real.exp (ξ' * (gm - ca - 2 * |Q| * ε))) * Y) ≤ T)
    (hlt : T < ENNReal.ofReal (Real.exp (ξ' * (K + 2)) * M₂)⁻¹ * n₀) :
    1 ≤ |gm| ∨ K < |ca| ∨ Y < ENNReal.ofReal M₂⁻¹ := by
  have h1 : n₀ * (ENNReal.ofReal (Real.exp (ξ' * (gm - ca - 2 * |Q| * ε))) * Y) <
      n₀ * ENNReal.ofReal (Real.exp (ξ' * (K + 2)) * M₂)⁻¹ := by
    rw [mul_comm n₀ (ENNReal.ofReal _)]; exact hT.trans_lt hlt
  have h2 := (ENNReal.mul_lt_mul_iff_right hn0 hnt).1 h1
  rcases lt_or_lt_of_mul_lt_ofReal_inv (Real.exp_pos _) hM₂ h2 with h | h
  · rw [← Real.exp_neg] at h
    have h' := (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).1 h
    rw [Real.exp_lt_exp] at h'
    have h'' : gm - ca - 2 * |Q| * ε < -(K + 2) := by
      have : ξ' * (gm - ca - 2 * |Q| * ε) < ξ' * (-(K + 2)) := by linarith
      exact lt_of_mul_lt_mul_left this hξ.le
    by_contra hc
    push_neg at hc
    have := neg_abs_le gm; have := le_abs_self gm; have := neg_abs_le ca; have := le_abs_self ca
    have : 0 ≤ 2 * |Q| * ε ∨ 2 * |Q| * ε < 0 := le_or_gt 0 _
    linarith [hc.1, hc.2.1]
  · exact Or.inr (Or.inr h)

theorem tvDist_le_add' {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {S : Set α}
    (hS : MeasurableSet S) : μ S ≤ ν S + QuantumZipper.TV.tvDist μ ν := by
  have := QuantumZipper.TV.le_tvDist (μ := μ) (ν := ν) hS
  rw [tsub_le_iff_left] at this
  exact this

end Pieces

section Seq

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

open scoped Classical in
/-- **Step 2, sequential form, PROVED** (l. 112–125). -/
theorem targetTightSeq_proved (hQ : IsLFPPExponent ξ Q) (hD : IsStrongLQGMetric ξ Q D) :
    TargetTightSeq ξ Q D := by
  intro U V φ hφ Ω mΩ P hP h g₀ k hI z r s hr hs hzs hrs δ hδ
  have hξ : (0 : ℝ) < ξ := ξ.2
  -- the Koebe precision `ε` with `2 |Q| ε ≤ 1`
  set ε : ℝ := 1 / (32 * (2 * |Q| + 1)) with hεdef
  have hQ0 : 0 ≤ |Q| := abs_nonneg Q
  have hε0 : 0 < ε := by positivity
  have hε32 : ε ≤ 1 / 32 := by
    rw [hεdef]; exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hεQ : 2 * |Q| * ε ≤ 1 := by
    rw [hεdef, mul_one_div, div_le_one (by positivity)]; nlinarith
  obtain ⟨c₀, hc₀, hgeom⟩ := geomGood_of_ball hε0
  set f : TestC := radF with hfdef
  set O : Opens ℂ := ballO (0 : ℂ) 3 with hOdef
  set Us : ℕ → Set ℂ := fun n => ball (0 : ℂ) (s n / r n) with hUsdef
  set Fs : ℕ → ℂ → ℂ := fun n => normMap (φ n) (z n) (r n) with hFsdef
  have hdB : ∀ n, DifferentiableOn ℂ (φ n) (ball (z n) (s n)) := fun n => (hφ n).1.mono (hzs n)
  have hiB : ∀ n, InjOn (φ n) (ball (z n) (s n)) := fun n => (hφ n).2.injOn.mono (hzs n)
  have NP := fun n => normalized_props (hs n) (hr n) (hdB n) (hiB n)
  have hφz : ∀ n, deriv (φ n) (z n) ≠ 0 := fun n => (NP n).1
  have hFd : ∀ n, DifferentiableOn ℂ (Fs n) (Us n) := fun n => (NP n).2.2.1
  have hFi : ∀ n, InjOn (Fs n) (Us n) := fun n => (NP n).2.2.2.1
  have hF0 : ∀ n, Fs n 0 = 0 := fun n => (NP n).2.2.2.2.1
  have hFder : ∀ n, deriv (Fs n) 0 = 1 := fun n => (NP n).2.2.2.2.2.1
  have hzeroU : ∀ n, (0 : ℂ) ∈ Us n := fun n => mem_ball_self (div_pos (hs n) (hr n))
  have hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ Us n := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    have hR1 : 0 < 1 / (|R| + 1) := by positivity
    filter_upwards [(tendsto_order.1 hrs).2 _ hR1] with n hn
    refine hR.trans (closedBall_subset_ball ?_)
    rw [div_lt_div_iff₀ (hs n) (by positivity), one_mul] at hn
    rw [lt_div_iff₀ (hr n)]
    nlinarith [le_abs_self R, hr n]
  have hder : Tendsto (fun n => deriv (Fs n) 0) atTop (𝓝 ((1 : ℂ)⁻¹)) := by
    simp only [hFder, inv_one]; exact tendsto_const_nhds
  -- the `𝐟`-normalized rescaled fields: one law
  have hh : ∀ n, IsWholePlaneGFF (h n) (P n) := fun n => (hI n).1.1
  set hhat : ∀ n, Ω n → DistC := fun n ω => normField f (h n ω) (z n) (r n) with hhatdef
  have hf1 : ∫ x, f x = 1 := integral_radF
  have hNm : Measurable fun g : DistC => g f := LQGMetric.GFFInv.measurable_pair f
  have hN : ∀ g c, (addConst g c) f = g f + c := by
    intro g c; rw [LQGMetric.GFFInv.addConst_apply, hf1, one_mul]
  have hhatW : ∀ n, IsWholePlaneGFF (hhat n) (P n) := fun n =>
    ((hh n).affineComp (hr n) (z n)).addConst
      ((hNm.comp ((hh n).affineComp (hr n) (z n)).measurable).neg)
  have hhatm : ∀ n, Measurable (hhat n) := fun n => (hhatW n).measurable
  have hhat0 : ∀ n, ∀ ω, hhat n ω f = 0 := fun n ω => by
    simp only [hhatdef, normField]; rw [hN]; exact add_neg_cancel _
  have hlaw : ∀ n, (P n).map (hhat n) = (P 0).map (hhat 0) := fun n =>
    LQGMetric.GFFLaw.map_eq_of_normalized (N := fun g : DistC => g f) hf1 hNm hN (hhatW n) (hhatW 0)
      (ae_of_all _ (hhat0 n)) (ae_of_all _ (hhat0 0))
  -- GM Lemma 2.4 (2.6) along the normalized maps, `α = 1`
  set Φ : ℕ → DistC → DistOn O := fun n u =>
    if hn : (O : Set ℂ) ⊆ Fs n '' Us n then phiN f (hFd n) (hFi n) hn u else 0 with hΦdef
  have hΦm : ∀ n, Measurable (Φ n) := by
    intro n
    by_cases hn : (O : Set ℂ) ⊆ Fs n '' Us n
    · simp only [hΦdef, dif_pos hn]; exact measurable_phiN f (hFd n) (hFi n) hn
    · simp only [hΦdef, dif_neg hn]; exact measurable_const
  set ν : Measure (DistOn O) :=
    (P 0).map (fun ω => restrictTo O (SupercriticalConformalCovariance.GM24.dilDist one_ne_zero (hhat 0 ω))) with hνdef
  set μ : ℕ → Measure (DistOn O) := fun n => (P 0).map (fun ω => Φ n (hhat 0 ω)) with hμdef
  have hνm : Measurable fun ω => restrictTo O (SupercriticalConformalCovariance.GM24.dilDist one_ne_zero (hhat 0 ω)) :=
    (LQGMetric.measurable_restrictTo O).comp
      (SupercriticalConformalCovariance.GM24.isWholePlaneGFF_dilDist (hhatW 0) one_ne_zero).measurable
  have : IsProbabilityMeasure ν := by rw [hνdef]; infer_instance
  have hTV : Tendsto (fun n => QuantumZipper.TV.tvDist (μ n) ν) atTop (𝓝 0) := by
    have := SupercriticalConformalCovariance.GM24.tendsto_tvDist_gm24_open (U := Us) (φ := Fs) (α := 1) (fun n => isOpen_ball)
      hzeroU hexhaust hFd hFi hF0 one_ne_zero hder (hhatW 0) hf1 radF_rot
      (ae_of_all _ (hhat0 0)) (O := O) (by exact Metric.isBounded_ball)
    exact this
  have hK1 : ∀ n (S : Set (DistOn O)), MeasurableSet S →
      P n {ω | Φ n (hhat n ω) ∈ S} = μ n S := by
    intro n S hS
    show (P n) _ = ((P 0).map (fun ω => Φ n (hhat 0 ω))) S
    rw [Measure.map_apply (f := fun ω => Φ n (hhat 0 ω)) ((hΦm n).comp (hhatm 0)) hS]
    exact measure_preimage_eq_of_map_eq (hlaw n) (hhatm n) (hhatm 0) (hΦm n) hS
  -- one measurable local functional for all the rescaled target fields
  set mseq : ℕ → ℕ := fun n =>
    if hK : closedBall (φ n (z n)) (3 * (r n * ‖deriv (φ n) (z n)‖)) ⊆ (V n : Set ℂ) then
      Classical.choose (SupercriticalConformalCovariance.Domain.exists_subset_exW (V n).isOpen (isCompact_closedBall _ _) hK)
    else 0 with hmseqdef
  set G' : ∀ n, Ω n → DistC := fun n ω =>
    rescG' Q (hφ n) (mseq n) (z n) (r n) (s n) f (h n ω) (g₀ n ω) (k n ω) with hG'def
  have hG'c : ∀ n, IsGFFPlusCont (G' n) (P n) := fun n =>
    isGFFPlusCont_rescG' (hφ n) (hI n) (mseq n) (z n) (hr n) (hφz n) (s n) f
  obtain ⟨Fa, hFam, hFa⟩ := SupercriticalConformalCovariance.BiLip.PortTan.exists_universal_local_functional O
    (measurable_aroundDist_comp hD annA) (isPathwiseLocal_aroundDist hD O annA annA_subset)
    ℕ Ω P G' hG'c
  obtain ⟨Fc, hFcm, hFc⟩ := SupercriticalConformalCovariance.BiLip.PortTan.exists_universal_local_functional O
    (measurable_acr_comp hD 0 (5 / 8) (7 / 8))
    (isPathwiseLocal_acr hD O 0 (5 / 8) (7 / 8) cann_subset_ballO) ℕ Ω P G' hG'c
  have hFam' : Measurable fun u : DistOn O => Fa (LQGMetric.pairJ O u) :=
    hFam.comp (LQGMetric.measurable_pairJ O)
  have hFcm' : Measurable fun u : DistOn O => Fc (LQGMetric.pairJ O u) :=
    hFcm.comp (LQGMetric.measurable_pairJ O)
  -- the good indices
  have hgood : ∀ᶠ n in atTop, r n ≤ c₀ * s n ∧ 4 * r n < s n := by
    filter_upwards [(tendsto_order.1 hrs).2 _ (lt_min hc₀ (by norm_num : (0 : ℝ) < 1 / 4))]
      with n hn
    have h1 := lt_of_lt_of_le hn (min_le_left _ _)
    have h2 := lt_of_lt_of_le hn (min_le_right _ _)
    rw [div_lt_iff₀ (hs n)] at h1 h2
    constructor <;> linarith
  -- at a good index: the geometry, the field identity and the normalized bounds
  have hAt : ∀ n, r n ≤ c₀ * s n → 4 * r n < s n →
      ∃ hOimg : (O : Set ℂ) ⊆ Fs n '' Us n,
        (∀ u, Φ n u = phiN f (hFd n) (hFi n) hOimg u) ∧
        (∀ᵐ ω ∂P n, Fa (LQGMetric.pairJ O (Φ n (hhat n ω))) = aroundDist (D (G' n ω)) annA ∧
          Fc (LQGMetric.pairJ O (Φ n (hhat n ω))) = acr (D (G' n ω)) 0 (5 / 8) (7 / 8)) ∧
        (∀ᵐ ω ∂P n,
          tAround (D (g₀ n ω)) ξ (k n ω) (φ n (z n)) (9 / 8 * (r n * ‖deriv (φ n) (z n)‖))
              (15 / 8 * (r n * ‖deriv (φ n) (z n)‖)) ≤
            nrm ξ Q (h n ω) (r n) (z n) *
              (ENNReal.ofReal (Real.exp (ξ * (wShift (φ n) (z n) (r n) (s n) f (hhat n ω) +
                2 * |Q| * ε))) * Fa (LQGMetric.pairJ O (Φ n (hhat n ω)))) ∧
          nrm ξ Q (h n ω) (r n) (z n) *
              (ENNReal.ofReal (Real.exp (ξ * (wShift (φ n) (z n) (r n) (s n) f (hhat n ω) -
                2 * |Q| * ε))) * Fc (LQGMetric.pairJ O (Φ n (hhat n ω)))) ≤
            tAcr (D (g₀ n ω)) ξ (k n ω) (φ n (z n)) (5 / 8 * (r n * ‖deriv (φ n) (z n)‖))
              (7 / 8 * (r n * ‖deriv (φ n) (z n)‖))) := by
    intro n hle h4
    have hG : GeomGood (φ n) (U n) (z n) (r n) ε :=
      hgeom (hs n) (hzs n) (hdB n) (hiB n) (hr n) hle
    have hOimg : (O : Set ℂ) ⊆ Fs n '' Us n :=
      ballO_zero_subset_normMap_image hG (hφ n).2.injOn h4
    have hK := closedBall_subset_target (hφ n) hG
    have hm : closedBall (φ n (z n)) (3 * (r n * ‖deriv (φ n) (z n)‖)) ⊆ exW (V n) (mseq n) := by
      simp only [hmseqdef, dif_pos hK]
      exact Classical.choose_spec
        (SupercriticalConformalCovariance.Domain.exists_subset_exW (V n).isOpen (isCompact_closedBall _ _) hK)
    have hΦn : ∀ u, Φ n u = phiN f (hFd n) (hFi n) hOimg u := fun u => by
      simp only [hΦdef, dif_pos hOimg]
    refine ⟨hOimg, hΦn, ?_, ?_⟩
    · filter_upwards [ae_rescaled hQ hD (hφ n) (hI n) (hs n) (hzs n) hG hε32 h4 hm f (hFd n)
        (hFi n) hOimg, hFa n, hFc n] with ω hω ea ec
      have hloc : locCoord O (G' n ω) = LQGMetric.pairJ O (Φ n (hhat n ω)) := by
        rw [hΦn]; unfold locCoord; rw [hG'def]; dsimp only; rw [hω.1]; rfl
      rw [← hloc]
      exact ⟨ea.symm, ec.symm⟩
    · filter_upwards [ae_tail_bound hQ hD (hφ n) (hI n) (hs n) (hzs n) hG hε32 h4 hm f (hFd n)
        (hFi n) hOimg (hFa n) (hFc n)] with ω hω
      simp only [hΦn]
      exact hω
  -- the limit law sees finite around-costs and positive crossings
  have hTVev : ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ n in atTop, QuantumZipper.TV.tvDist (μ n) ν ≤ η :=
    fun η hη => ENNReal.tendsto_nhds_zero.1 hTV η hη
  have hνnull : ∀ S : Set (DistOn O), MeasurableSet S →
      (∀ n, r n ≤ c₀ * s n → 4 * r n < s n → P n {ω | Φ n (hhat n ω) ∈ S} = 0) → ν S = 0 := by
    intro S hS hzero
    refine le_antisymm (ge_of_tendsto hTV ?_) bot_le
    filter_upwards [hgood] with n ⟨hle, h4⟩
    have := tvDist_le_add (μ := μ n) (ν := ν) hS
    rwa [← hK1 n S hS, hzero n hle h4, zero_add] at this
  have hνtop : ν {u | Fa (LQGMetric.pairJ O u) = ⊤} = 0 := by
    refine hνnull _ (hFam' (measurableSet_singleton ⊤)) fun n hle h4 => ?_
    obtain ⟨-, -, hloc, -⟩ := hAt n hle h4
    have hae : ∀ᵐ ω ∂P n, Fa (LQGMetric.pairJ O (Φ n (hhat n ω))) ≠ ⊤ := by
      filter_upwards [hloc, SupercriticalLQGUniqueness.B2.Strong.ae_aroundDist_lt_top hD (P n) (G' n)
        (hG'c n) annA] with ω e hlt
      rw [e.1]; exact hlt.ne
    exact measure_mono_null (fun ω hω => not_not.2 hω) (ae_iff.1 hae)
  have hνzero : ν {u | Fc (LQGMetric.pairJ O u) = 0} = 0 := by
    refine hνnull _ (hFcm' (measurableSet_singleton 0)) fun n hle h4 => ?_
    obtain ⟨-, -, hloc, -⟩ := hAt n hle h4
    have hae : ∀ᵐ ω ∂P n, Fc (LQGMetric.pairJ O (Φ n (hhat n ω))) ≠ 0 := by
      filter_upwards [hloc] with ω e
      rw [e.2]
      exact (lt_of_lt_of_le (SupercriticalLQGUniqueness.B2.Strong.acrossDist_pos (D (G' n ω))
        ⟨((0 : ℂ), 5 / 8, 7 / 8), by norm_num, by norm_num⟩)
        (SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.ambientAcross_le_acr
          (D (G' n ω)) 0 (5 / 8) (7 / 8))).ne'
    exact measure_mono_null (fun ω hω => not_not.2 hω) (ae_iff.1 hae)
  -- the level `M₂` of the local functionals
  have hδ8 : 0 < δ / 8 := by positivity
  have hδ4 : 0 < δ / 4 := by positivity
  obtain ⟨j₁, hj₁⟩ := exists_measure_le_of_iInter (μ := ν)
    (S := fun j : ℕ => {u | ENNReal.ofReal j < Fa (LQGMetric.pairJ O u)})
    (fun j => measurableSet_lt measurable_const hFam')
    (fun i j hij u hu => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by exact_mod_cast hij)) hu)
    (by
      refine measure_mono_null (fun u hu => ?_) hνtop
      simp only [mem_iInter, mem_setOf_eq] at hu ⊢
      by_contra hne
      obtain ⟨j, hj⟩ := ENNReal.exists_nat_gt hne
      have := hu j
      rw [ENNReal.ofReal_natCast] at this
      exact lt_irrefl _ (this.trans hj)) hδ8
  obtain ⟨j₂, hj₂⟩ := exists_measure_le_of_iInter (μ := ν)
    (S := fun j : ℕ => {u | Fc (LQGMetric.pairJ O u) < ENNReal.ofReal ((j : ℝ) + 1)⁻¹})
    (fun j => measurableSet_lt hFcm' measurable_const)
    (fun i j hij u hu => lt_of_lt_of_le hu (ENNReal.ofReal_le_ofReal
      (inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1))))
    (by
      refine measure_mono_null (fun u hu => ?_) hνzero
      simp only [mem_iInter, mem_setOf_eq] at hu ⊢
      by_contra hne
      have hpos : 0 < Fc (LQGMetric.pairJ O u) := pos_iff_ne_zero.2 hne
      by_cases htop : Fc (LQGMetric.pairJ O u) = ⊤
      · have := hu 0; rw [htop] at this; exact not_top_lt this
      have hreal : 0 < (Fc (LQGMetric.pairJ O u)).toReal := ENNReal.toReal_pos hne htop
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hreal
      have h1 : ENNReal.ofReal ((j : ℝ) + 1)⁻¹ < Fc (LQGMetric.pairJ O u) := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop, ← one_div]; exact hj
      exact lt_asymm (hu j) h1) hδ8
  set M₂ : ℝ := max (j₁ : ℝ) ((j₂ : ℝ) + 1) with hM₂def
  have hM₂ : 0 < M₂ := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hν1 : ν {u | ENNReal.ofReal M₂ < Fa (LQGMetric.pairJ O u)} ≤ ENNReal.ofReal (δ / 8) :=
    (measure_mono fun u hu => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hu).trans
      hj₁
  have hν2 : ν {u | Fc (LQGMetric.pairJ O u) < ENNReal.ofReal M₂⁻¹} ≤ ENNReal.ofReal (δ / 8) :=
    (measure_mono fun u hu => lt_of_lt_of_le hu (ENNReal.ofReal_le_ofReal
      (inv_anti₀ (by positivity) (le_max_right _ _)))).trans hj₂
  -- the level `K` of the circle average
  obtain ⟨K, hK⟩ := tail_real_small (μ := P 0) (X := fun ω => LQGMetric.circleAvg (hhat 0 ω) 1 0)
    ((LQGMetric.measurable_circleAvg_left 1 0).comp (hhatm 0)) hδ4
  -- GM's constants `c₀(ĥ₀) → 0` pointwise, hence in probability
  have hgm_ae : ∀ᵐ ω ∂P 0, Tendsto (fun n => gmConst (φ n) (z n) (r n) (s n) f (hhat 0 ω)) atTop
      (𝓝 0) := ae_of_all _ fun ω => by
    have := SupercriticalConformalCovariance.GM24.tendsto_invPullSmoothAvg (U := Us) (φ := Fs) (α := 1) (fun n => isOpen_ball)
      hzeroU hexhaust hFd hFi hF0 one_ne_zero hder (hhat 0 ω) f
      (inv_pos.2 (norm_pos_iff.2 (one_ne_zero : (1 : ℂ) ≠ 0)))
    rw [SupercriticalConformalCovariance.GM24.dilDist_smoothAvg_inv_norm one_ne_zero _ radF_rot, SupercriticalConformalCovariance.GM24.smoothAvg_one,
      hhat0 0 ω] at this
    exact this
  have hgm_meas := tendstoInMeasure_of_tendsto_ae (μ := P 0)
    (f := fun n ω => gmConst (φ n) (z n) (r n) (s n) f (hhat 0 ω)) (g := fun _ => (0 : ℝ))
    (fun n => ((measurable_gmConst (φ n) (z n) (r n) (s n) f).comp (hhatm 0)).aestronglyMeasurable)
    hgm_ae
  have hgm_ev : ∀ᶠ n in atTop,
      P 0 {ω | (1 : ℝ≥0∞) ≤ edist (gmConst (φ n) (z n) (r n) (s n) f (hhat 0 ω)) 0} ≤
      ENNReal.ofReal (δ / 4) :=
    ENNReal.tendsto_nhds_zero.1 (hgm_meas 1 one_pos) _ (ENNReal.ofReal_pos.2 hδ4)
  -- assembly
  refine ⟨Real.exp (ξ * (K + 2)) * M₂, by positivity, ?_⟩
  filter_upwards [hgood, hgm_ev, hTVev _ (ENNReal.ofReal_pos.2 hδ8)] with n ⟨hle, h4⟩ hgmn htvn
  obtain ⟨hOimg, hΦn, -, htail⟩ := hAt n hle h4
  have hS1 : MeasurableSet {x : ℝ | (1 : ℝ≥0∞) ≤ edist x 0} :=
    measurableSet_le measurable_const (measurable_id.edist measurable_const)
  have hS2 : MeasurableSet {x : ℝ | K < |x|} := measurableSet_lt measurable_const measurable_abs
  have hA1 : P n {ω | (1 : ℝ≥0∞) ≤ edist (gmConst (φ n) (z n) (r n) (s n) f (hhat n ω)) 0} ≤
      ENNReal.ofReal (δ / 4) := by
    have := measure_preimage_eq_of_map_eq (hlaw n) (hhatm n) (hhatm 0)
      (measurable_gmConst (φ n) (z n) (r n) (s n) f) hS1
    exact this.trans_le hgmn
  have hA2 : P n {ω | K < |LQGMetric.circleAvg (hhat n ω) 1 0|} ≤ ENNReal.ofReal (δ / 4) := by
    have := measure_preimage_eq_of_map_eq (hlaw n) (hhatm n) (hhatm 0)
      (LQGMetric.measurable_circleAvg_left 1 0) hS2
    exact this.trans_le hK
  have hA3 : P n {ω | ENNReal.ofReal M₂ < Fa (LQGMetric.pairJ O (Φ n (hhat n ω)))} ≤
      ENNReal.ofReal (δ / 8) + ENNReal.ofReal (δ / 8) := by
    have hS : MeasurableSet {u : DistOn O | ENNReal.ofReal M₂ < Fa (LQGMetric.pairJ O u)} :=
      measurableSet_lt measurable_const hFam'
    rw [show {ω | ENNReal.ofReal M₂ < Fa (LQGMetric.pairJ O (Φ n (hhat n ω)))} =
      {ω | Φ n (hhat n ω) ∈ {u : DistOn O | ENNReal.ofReal M₂ < Fa (LQGMetric.pairJ O u)}} from rfl,
      hK1 n _ hS]
    exact (tvDist_le_add' hS).trans (add_le_add hν1 htvn)
  have hA3' : P n {ω | Fc (LQGMetric.pairJ O (Φ n (hhat n ω))) < ENNReal.ofReal M₂⁻¹} ≤
      ENNReal.ofReal (δ / 8) + ENNReal.ofReal (δ / 8) := by
    have hS : MeasurableSet {u : DistOn O | Fc (LQGMetric.pairJ O u) < ENNReal.ofReal M₂⁻¹} :=
      measurableSet_lt hFcm' measurable_const
    rw [show {ω | Fc (LQGMetric.pairJ O (Φ n (hhat n ω))) < ENNReal.ofReal M₂⁻¹} =
      {ω | Φ n (hhat n ω) ∈ {u : DistOn O | Fc (LQGMetric.pairJ O u) < ENNReal.ofReal M₂⁻¹}} from rfl,
      hK1 n _ hS]
    exact (tvDist_le_add' hS).trans (add_le_add hν2 htvn)
  have hsum : ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) +
      (ENNReal.ofReal (δ / 8) + ENNReal.ofReal (δ / 8)) ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add hδ4.le hδ4.le, ← ENNReal.ofReal_add hδ8.le hδ8.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hnrm := fun ω => nrm_pos_lt_top (ξ : ℝ) Q (h n ω) (hr n) (z n)
  constructor
  · refine le_trans (measure_mono_ae ?_) ((measure_union_le _ _).trans
      ((add_le_add (measure_union_le _ _) hA3).trans ((add_le_add (add_le_add hA1 hA2) le_rfl).trans
        hsum)))
    filter_upwards [htail] with ω hω hlt
    have := event_up (gm := gmConst (φ n) (z n) (r n) (s n) f (hhat n ω))
      (ca := LQGMetric.circleAvg (hhat n ω) 1 0) hξ hεQ hM₂.le (hnrm ω).1.ne' (hnrm ω).2.ne
      hω.1 hlt
    rcases this with h1 | h1 | h1
    · left; left
      show (1 : ℝ≥0∞) ≤ edist _ _
      rw [edist_dist, Real.dist_eq, sub_zero, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal h1
    · left; right; exact h1
    · right; exact h1
  · refine le_trans (measure_mono_ae ?_) ((measure_union_le _ _).trans
      ((add_le_add (measure_union_le _ _) hA3').trans ((add_le_add (add_le_add hA1 hA2) le_rfl).trans
        hsum)))
    filter_upwards [htail] with ω hω hlt
    have := event_down (gm := gmConst (φ n) (z n) (r n) (s n) f (hhat n ω))
      (ca := LQGMetric.circleAvg (hhat n ω) 1 0) hξ hεQ hM₂ (hnrm ω).1.ne' (hnrm ω).2.ne
      hω.2 hlt
    rcases this with h1 | h1 | h1
    · left; left
      show (1 : ℝ≥0∞) ≤ edist _ _
      rw [edist_dist, Real.dist_eq, sub_zero, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal h1
    · left; right; exact h1
    · right; exact h1


end Seq

end SupercriticalConformalCovariance.BiLip
