import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Field.HeatVersion
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.B2.Polylog.P2HeatAnnulusTight
import SupercriticalLQGUniqueness.B2.Polylog.P4LFPPCompare
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1Crossing
import SupercriticalLQGUniqueness.B2.Median.PathSelection
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.LawTransport
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX9
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

/-!
# Annular tightness for the limit metric and localized LFPP

Packet TI proves `Core.AnnTightStmt` from the uniform localization estimate. The D tails use V′
of the proved weak LQG metric on a canonical normalized field law and law transport. The Y tails
compare localization to the canonical joint heat version on a bounded neighborhood of the annulus.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC circleAvg IsPiecewiseC1Path)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Tightness

private theorem packetTI_D_tails_uniform (S : Core.Setup) (A : EuclideanAnnulus) (ϑ : ℝ)
    (hϑ : 0 < ϑ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
        P {ω | acrossDist (S.D (h ω)) A < ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal ϑ ∧
        P {ω | ENNReal.ofReal M < aroundDist (S.D (h ω)) A} ≤ ENNReal.ofReal ϑ := by
  obtain ⟨μ, hμp, hμ⟩ := Uniqueness.Positivity.Witnesses.exists_canonical_normalized_law
  letI : IsProbabilityMeasure μ := hμp
  let r : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  let a : Set.Ioi (0 : ℝ) → DistC → ℝ := fun s g => circleAvg g s 0
  have ha : ∀ s : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂μ, IsCircleAverage ((id : DistC → DistC) ω)
      s 0 (a s ((id : DistC → DistC) ω)) := by
    intro s
    simpa only [a] using
      (Uniqueness.Toolkit.AnnulusIteration.ae_isCircleAverage_circleAvg hμ.1 s 0)
  have hweak : IsWeakLQGMetric S.ξ S.Q S.D :=
    SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric S.hD
  have htight := hweak.2.2.2.2.2 μ (id : DistC → DistC) hμ a ha A
  obtain ⟨Ma, hMa, hAtail⟩ := htight.1.2 ϑ hϑ
  obtain ⟨Mr, hMr, hRtail⟩ := htight.2.2 ϑ hϑ
  let M : ℝ := max Ma Mr
  have hM : 0 < M := lt_max_of_lt_left hMa
  have hrnorm : ∀ᵐ ω ∂μ, circleAvg ((id : DistC → DistC) ω) 1 0 = 0 := by
    filter_upwards [hμ.2] with ω hω
    exact Uniqueness.Toolkit.AnnulusIteration.circleAvg_eq_of_isCircleAverage ω r 0 0 hω
  have hAeq : (fun ω =>
      ENNReal.ofReal ((1 : ℝ) ^ (-((S.ξ : ℝ) * S.Q)) *
        Real.exp (-((S.ξ : ℝ) * a r ((id : DistC → DistC) ω)))) *
        acrossDist (S.D ((id : DistC → DistC) ω)) (A.dilate 1 one_pos)) =ᵐ[μ]
      (fun ω => acrossDist (S.D ((id : DistC → DistC) ω)) A) := by
    filter_upwards [hrnorm] with ω hω
    have hω' : circleAvg ω 1 0 = 0 := by simpa using hω
    change ENNReal.ofReal (1 ^ (-((S.ξ : ℝ) * S.Q)) *
      Real.exp (-((S.ξ : ℝ) * circleAvg ω 1 0))) *
        acrossDist (S.D ω) (A.dilate 1 one_pos) = acrossDist (S.D ω) A
    rw [hω', Uniqueness.Positivity.Witnesses.dilate_one]
    simp
  have hReq : (fun ω =>
      ENNReal.ofReal ((1 : ℝ) ^ (-((S.ξ : ℝ) * S.Q)) *
        Real.exp (-((S.ξ : ℝ) * a r ((id : DistC → DistC) ω)))) *
        aroundDist (S.D ((id : DistC → DistC) ω)) (A.dilate 1 one_pos)) =ᵐ[μ]
      (fun ω => aroundDist (S.D ((id : DistC → DistC) ω)) A) := by
    filter_upwards [hrnorm] with ω hω
    have hω' : circleAvg ω 1 0 = 0 := by simpa using hω
    change ENNReal.ofReal (1 ^ (-((S.ξ : ℝ) * S.Q)) *
      Real.exp (-((S.ξ : ℝ) * circleAvg ω 1 0))) *
        aroundDist (S.D ω) (A.dilate 1 one_pos) = aroundDist (S.D ω) A
    rw [hω', Uniqueness.Positivity.Witnesses.dilate_one]
    simp
  have hAevent : {ω |
      ENNReal.ofReal ((1 : ℝ) ^ (-((S.ξ : ℝ) * S.Q)) *
        Real.exp (-((S.ξ : ℝ) * a r ((id : DistC → DistC) ω)))) *
        acrossDist (S.D ((id : DistC → DistC) ω)) (A.dilate 1 one_pos) <
          ENNReal.ofReal Ma⁻¹} =ᵐ[μ]
      {ω | acrossDist (S.D ((id : DistC → DistC) ω)) A < ENNReal.ofReal Ma⁻¹} :=
    hAeq.mono fun ω hω => by
      have he : ENNReal.ofReal ((1 : ℝ) ^ (-((S.ξ : ℝ) * S.Q)) *
          Real.exp (-((S.ξ : ℝ) * a r ((id : DistC → DistC) ω)))) *
          acrossDist (S.D ((id : DistC → DistC) ω)) (A.dilate 1 one_pos) =
          acrossDist (S.D ((id : DistC → DistC) ω)) A := by
        change _ = _ at hω
        exact hω
      exact propext (Iff.of_eq (congrArg (fun x : ℝ≥0∞ => x < ENNReal.ofReal Ma⁻¹) he))
  have hRevent : {ω |
      ENNReal.ofReal Mr < ENNReal.ofReal ((1 : ℝ) ^ (-((S.ξ : ℝ) * S.Q)) *
        Real.exp (-((S.ξ : ℝ) * a r ((id : DistC → DistC) ω)))) *
        aroundDist (S.D ((id : DistC → DistC) ω)) (A.dilate 1 one_pos)} =ᵐ[μ]
      {ω | ENNReal.ofReal Mr < aroundDist (S.D ((id : DistC → DistC) ω)) A} :=
    hReq.mono fun ω hω => by
      have he : ENNReal.ofReal ((1 : ℝ) ^ (-((S.ξ : ℝ) * S.Q)) *
          Real.exp (-((S.ξ : ℝ) * a r ((id : DistC → DistC) ω)))) *
          aroundDist (S.D ((id : DistC → DistC) ω)) (A.dilate 1 one_pos) =
          aroundDist (S.D ((id : DistC → DistC) ω)) A := by
        change _ = _ at hω
        exact hω
      exact propext (Iff.of_eq (congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal Mr < x) he))
  have hA : μ {ω | acrossDist (S.D ((id : DistC → DistC) ω)) A < ENNReal.ofReal M⁻¹} ≤
      ENNReal.ofReal ϑ := by
    have hle : ENNReal.ofReal M⁻¹ ≤ ENNReal.ofReal Ma⁻¹ :=
      ENNReal.ofReal_le_ofReal ((inv_le_inv₀ hM hMa).2 (le_max_left _ _))
    calc
      _ ≤ μ {ω | acrossDist (S.D ((id : DistC → DistC) ω)) A < ENNReal.ofReal Ma⁻¹} :=
        measure_mono (fun _ h => lt_of_lt_of_le h hle)
      _ = μ {ω |
          ENNReal.ofReal ((1 : ℝ) ^ (-((S.ξ : ℝ) * S.Q)) *
            Real.exp (-((S.ξ : ℝ) * a r ((id : DistC → DistC) ω)))) *
            acrossDist (S.D ((id : DistC → DistC) ω)) (A.dilate 1 one_pos) <
              ENNReal.ofReal Ma⁻¹} := by
          rw [measure_congr hAevent]
      _ ≤ ENNReal.ofReal ϑ := by simpa [a, r] using (hAtail r).2
  have hR : μ {ω | ENNReal.ofReal M < aroundDist (S.D ((id : DistC → DistC) ω)) A} ≤
      ENNReal.ofReal ϑ := by
    have hle : ENNReal.ofReal Mr ≤ ENNReal.ofReal M :=
      ENNReal.ofReal_le_ofReal (le_max_right _ _)
    calc
      _ ≤ μ {ω | ENNReal.ofReal Mr < aroundDist (S.D ((id : DistC → DistC) ω)) A} :=
        measure_mono (fun _ h => lt_of_le_of_lt hle h)
      _ = μ {ω | ENNReal.ofReal Mr <
          ENNReal.ofReal ((1 : ℝ) ^ (-((S.ξ : ℝ) * S.Q)) *
            Real.exp (-((S.ξ : ℝ) * a r ((id : DistC → DistC) ω)))) *
            aroundDist (S.D ((id : DistC → DistC) ω)) (A.dilate 1 one_pos)} := by
          rw [measure_congr hRevent]
      _ ≤ ENNReal.ofReal ϑ := by simpa [a, r] using (hRtail r).1
  refine ⟨M, hM, ?_⟩
  intro Ω _ P _ h hh
  have hAset : MeasurableSet {g : DistC |
      acrossDist (S.D g) A < ENNReal.ofReal M⁻¹} :=
    measurableSet_lt ((measurable_acrossDist A).comp S.hD.1) measurable_const
  have hRset : MeasurableSet {g : DistC |
      ENNReal.ofReal M < aroundDist (S.D g) A} :=
    measurableSet_lt measurable_const
      ((Uniqueness.TwoScale.S36.measurable_aroundDist_fixed A).comp S.hD.1)
  have hAprob := Uniqueness.TwoScale.S36.prob_preimage_eq_of_normalized P μ hh hμ
    (LQGMetric.UMeasurableSet.of_measurableSet hAset)
  have hRprob := Uniqueness.TwoScale.S36.prob_preimage_eq_of_normalized P μ hh hμ
    (LQGMetric.UMeasurableSet.of_measurableSet hRset)
  constructor
  · simpa using hAprob ▸ hA
  · simpa using hRprob ▸ hR

private theorem packetTI_across_lfpp_close_lt_two_mul (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ ψ : C(ℂ, ℝ)) (A : EuclideanAnnulus) (V : Set ℂ) (hV : IsOpen V)
    (hAnnV : ∀ z, dist z A.center ≤ A.outerRadius → z ∈ V)
    {K : ℝ} (hfac : Real.exp (|ξ| * K) ≤ 2)
    (hclose : ∀ z ∈ V, |ψ z - φ z| ≤ K)
    {t : ℝ≥0∞} (ht : acrossDist (B2.Median.lfppMetric ξ a φ) A < t) :
    acrossDist (B2.Median.lfppMetric ξ a ψ) A < ENNReal.ofReal 2 * t := by
  unfold acrossDist at ht
  simp only [iInf_lt_iff] at ht
  obtain ⟨x, hx, y, hy, hxy⟩ := ht
  have hxy' : ENNReal.ofReal ((a : ℝ)⁻¹) * lfppDistance ξ φ (x, y) < t := by
    simpa only [B2.Median.lfppMetric_apply] using hxy
  have hset : B2.Iface.setDistance (lfppDistance ξ φ) {x} {y} ≤
      lfppDistance ξ φ (x, y) := by
    unfold B2.Iface.setDistance
    exact iInf_le_of_le x (iInf_le_of_le (by simp) (iInf_le_of_le y
      (iInf_le_of_le (by simp) le_rfl)))
  have hpathCost : ENNReal.ofReal ((a : ℝ)⁻¹) *
      B2.Iface.setDistance (lfppDistance ξ φ) {x} {y} < t := by
    exact (mul_le_mul_right hset _).trans_lt hxy'
  obtain ⟨z, hz, w, hw, P, hP, hlen⟩ :=
    B2.Median.exists_lfpp_path_of_scaled_setDistance_lt ξ a φ {x} {y} hpathCost
  have hz' : z = x := by simpa using hz
  have hw' : w = y := by simpa using hw
  subst z
  subst w
  have hxrad : dist x A.center = A.innerRadius := by
    have hx' : ‖x - A.center‖ = A.innerRadius := by
      simpa [EuclideanAnnulus.innerBoundary, Metric.mem_sphere] using hx
    rw [dist_eq_norm]
    exact hx'
  have hyrad : dist y A.center = A.outerRadius := by
    have hy' : ‖y - A.center‖ = A.outerRadius := by
      simpa [EuclideanAnnulus.outerBoundary, Metric.mem_sphere] using hy
    rw [dist_eq_norm]
    exact hy'
  have hf : ContinuousOn (fun u => dist (P u) A.center) (Icc (0 : ℝ) 1) :=
    continuous_dist.comp_continuousOn (hP.continuousOn.prodMk continuousOn_const)
  have hstart : dist (P 0) A.center ≤ A.innerRadius := by
    rw [hP.source]
    exact hxrad.le
  have hfinish : A.outerRadius ≤ dist (P 1) A.center := by
    rw [hP.target]
    exact hyrad.symm.le
  obtain ⟨s, u, hs, hsu, hu, hPs, hPu, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing (f := fun v => dist (P v) A.center)
      zero_le_one hf A.innerRadius_lt_outerRadius.le hstart hfinish
  have hPc : ContinuousOn P (Icc s u) := hP.continuousOn.mono
    (Icc_subset_Icc hs hu)
  have hPV : ∀ v ∈ Icc s u, P v ∈ V := by
    intro v hv
    have hrad : dist (P v) A.center ≤ A.outerRadius := (hbetween v hv).2
    exact hAnnV (P v) hrad
  have hcompare := B2.Polylog.lfppMetric_len_le_of_abs_sub_le ξ a hV hclose hPc hPV
  have hseg := B2.PfeWeyl.len_mono_Icc (B2.Median.lfppMetric ξ a φ) P hs hu
  have hwhole := B2.Median.lfppMetric_len_le_lfppLen ξ a φ hP
  have hcross := B2.PfeWeyl.acrossDist_le_len_of_crossing
    (B2.Median.lfppMetric ξ a ψ) A hsu hPc hPs.le hPu.symm.le
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * K))
  have hc0 : c ≠ 0 := by
    change ENNReal.ofReal (Real.exp (|ξ| * K)) ≠ 0
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hwhole' : c * (B2.Median.lfppMetric ξ a φ).len P 0 1 ≤
      c * (ENNReal.ofReal ((a : ℝ)⁻¹) * LQGMetric.lfppLen ξ φ P) := by
    simpa only [mul_comm] using mul_le_mul_right hwhole c
  have hlen' : c * (ENNReal.ofReal ((a : ℝ)⁻¹) * LQGMetric.lfppLen ξ φ P) < c * t := by
    simpa only [mul_comm] using ENNReal.mul_lt_mul_left hc0 hctop hlen
  have hfac' : c ≤ ENNReal.ofReal 2 := by
    change ENNReal.ofReal (Real.exp (|ξ| * K)) ≤ ENNReal.ofReal 2
    exact ENNReal.ofReal_le_ofReal hfac
  calc
    acrossDist (B2.Median.lfppMetric ξ a ψ) A ≤
        (B2.Median.lfppMetric ξ a ψ).len P s u := hcross
    _ ≤ c * (B2.Median.lfppMetric ξ a φ).len P s u := hcompare
    _ ≤ c * (B2.Median.lfppMetric ξ a φ).len P 0 1 :=
      mul_le_mul_right hseg _
    _ ≤ c *
        (ENNReal.ofReal ((a : ℝ)⁻¹) * LQGMetric.lfppLen ξ φ P) := hwhole'
    _ < c * t := hlen'
    _ ≤ ENNReal.ofReal 2 * t :=
      by simpa only [mul_comm] using mul_le_mul_right hfac' t

private theorem packetTI_around_lfpp_close_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ ψ : C(ℂ, ℝ)) (A : EuclideanAnnulus) (V : Set ℂ) (hV : IsOpen V)
    {K : ℝ} (hfac : Real.exp (|ξ| * K) ≤ 2)
    (hclose : ∀ z ∈ V, |ψ z - φ z| ≤ K) (hAV : A.toSet ⊆ V) :
    aroundDist (B2.Median.lfppMetric ξ a φ) A ≤
      ENNReal.ofReal 2 * aroundDist (B2.Median.lfppMetric ξ a ψ) A := by
  have hclose' : ∀ z ∈ V, |φ z - ψ z| ≤ K := fun z hz => by
    simpa only [abs_sub_comm] using hclose z hz
  have hfac' : ENNReal.ofReal (Real.exp (|ξ| * K)) ≤ ENNReal.ofReal 2 :=
    ENNReal.ofReal_le_ofReal hfac
  calc
    aroundDist (B2.Median.lfppMetric ξ a φ) A ≤
        ENNReal.ofReal (Real.exp (|ξ| * K)) *
          aroundDist (B2.Median.lfppMetric ξ a ψ) A := by
      exact B2.Polylog.aroundDist_lfppMetric_le ξ a (φ := ψ) (φ' := φ) hV hclose' hAV
    _ ≤ ENNReal.ofReal 2 * aroundDist (B2.Median.lfppMetric ξ a ψ) A :=
      by simpa only [mul_comm] using
        mul_le_mul_right hfac' (aroundDist (B2.Median.lfppMetric ξ a ψ) A)

theorem annTight_of (S : Core.Setup) (hU : Core.UnifLocStmt) : Core.AnnTightStmt S := by
  intro A ϑ hϑ
  obtain ⟨MD, hMD, hDtails⟩ := packetTI_D_tails_uniform S A (ϑ / 2) (by linarith)
  obtain ⟨μ, hμp, hμ⟩ := Uniqueness.Positivity.Witnesses.exists_canonical_normalized_law
  letI : IsProbabilityMeasure μ := hμp
  obtain ⟨X, hX, hXjoint⟩ := Field.exists_jointHeatVersion_core μ (id : DistC → DistC) hμ
  have hXjoint' : Core.IsJointHeatVersion μ (id : DistC → DistC) X := ⟨hX, hXjoint⟩
  let K : Set ℂ := closedBall A.center (A.outerRadius + 1)
  let V : Set ℂ := ball A.center (A.outerRadius + 1 / 2)
  have hK : IsCompact K := isCompact_closedBall A.center (A.outerRadius + 1)
  have hV : IsOpen V := isOpen_ball
  have hVK : V ⊆ K := by
    intro z hz
    have hz' : dist z A.center < A.outerRadius + 1 / 2 := by
      simpa [V, Metric.mem_ball] using hz
    have hz'' : dist z A.center ≤ A.outerRadius + 1 := le_of_lt (lt_of_lt_of_le hz' (by linarith))
    simpa [K, Metric.mem_closedBall] using hz''
  have hAV : A.toSet ⊆ V := by
    intro z hz
    have hz' : dist z A.center < A.outerRadius := by
      simpa [EuclideanAnnulus.toSet, Metric.mem_ball] using hz.1
    have hz'' : dist z A.center < A.outerRadius + 1 / 2 := lt_trans hz' (by linarith)
    simpa [V, Metric.mem_ball] using hz''
  have hAnnV : ∀ z, dist z A.center ≤ A.outerRadius → z ∈ V := by
    intro z hz
    have hz' : dist z A.center < A.outerRadius + 1 / 2 := lt_of_le_of_lt hz (by linarith)
    simpa [V, Metric.mem_ball] using hz'
  have hξ : 0 < (S.ξ : ℝ) := S.ξ.2
  let σ : ℝ := Real.log 2 / (|(S.ξ : ℝ)| + 1)
  have hσ : 0 < σ := div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hσfac : Real.exp (|(S.ξ : ℝ)| * σ) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    dsimp [σ]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hratio : |(S.ξ : ℝ)| / (|(S.ξ : ℝ)| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc
      |(S.ξ : ℝ)| * (Real.log 2 / (|(S.ξ : ℝ)| + 1)) =
          Real.log 2 * (|(S.ξ : ℝ)| / (|(S.ξ : ℝ)| + 1)) := by ring
      _ ≤ Real.log 2 := mul_le_of_le_one_right hlog.le hratio
      _ = Real.log 2 := rfl
  have hUlim := hU μ (id : DistC → DistC) hμ X hXjoint' K hK σ hσ
  rw [ENNReal.tendsto_nhds_zero] at hUlim
  have hUev := hUlim (ENNReal.ofReal (ϑ / 2))
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < ϑ / 2))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hUev
  obtain ⟨ε₀, hε₀, hUev⟩ := hUev
  let δ₀ : ℝ := ε₀ / 2
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hbadBound : ∀ δ₁ : ℝ, δ₁ = δ₀ →
      μ {ω | ∃ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δ₁ ∧
        ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧ ∃ z ∈ K,
          σ < |Core.locFieldC δ L hδ ((id : DistC → DistC) ω) z - X ⟨δ, hδ.1⟩ ω z|} ≤
        ENNReal.ofReal (ϑ / 2) := by
    intro δ₁ hδ₁
    subst δ₁
    have hd : dist δ₀ 0 < ε₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ₀]
      dsimp [δ₀]
      linarith
    exact hUev hd (Set.mem_Ioi.mpr hδ₀)
  have hPL := B2.Polylog.plHeatAnnulusTight_of_inputs
    B2.Final.dg20Interfaces_proved.2.1 B2.Final.dg20Interfaces_proved.1
  have hPLA := hPL S.ξ S.Q S.hQ S.m S.hm μ (id : DistC → DistC) hμ X hX A
  obtain ⟨MH, hMH, hheat⟩ := hPLA.2 (ϑ / 2) (by linarith)
  let MT : ℝ := max MD (4 * MH)
  have hMT : 0 < MT := lt_max_of_lt_left hMD
  have hMTD : MD ≤ MT := le_max_left _ _
  have hMTH : 4 * MH ≤ MT := le_max_right _ _
  have hheatThreshold : ENNReal.ofReal 2 * ENNReal.ofReal MT⁻¹ ≤ ENNReal.ofReal MH⁻¹ := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    have hdiv : (2 : ℝ) / MT ≤ 1 / MH := by
      rw [div_le_div_iff₀ hMT hMH]
      nlinarith
    simpa [div_eq_mul_inv] using hdiv
  have hheatAroundThreshold : ENNReal.ofReal 2 * ENNReal.ofReal MH ≤ ENNReal.ofReal MT := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  refine ⟨MT, δ₀, hMT, hδ₀, ?_⟩
  intro Ω _ P _ h hh
  have hDA : P {ω | acrossDist (S.D (h ω)) A < ENNReal.ofReal MT⁻¹} ≤ ENNReal.ofReal ϑ := by
    have h0 := hDtails P h hh |>.1
    have hle : ENNReal.ofReal MT⁻¹ ≤ ENNReal.ofReal MD⁻¹ :=
      ENNReal.ofReal_le_ofReal ((inv_le_inv₀ hMT hMD).2 hMTD)
    calc
      _ ≤ P {ω | acrossDist (S.D (h ω)) A < ENNReal.ofReal MD⁻¹} :=
        measure_mono (fun _ hω => lt_of_lt_of_le hω hle)
      _ ≤ ENNReal.ofReal (ϑ / 2) := h0
      _ ≤ ENNReal.ofReal ϑ := ENNReal.ofReal_le_ofReal (by linarith)
  have hDR : P {ω | ENNReal.ofReal MT < aroundDist (S.D (h ω)) A} ≤ ENNReal.ofReal ϑ := by
    have h0 := hDtails P h hh |>.2
    have hle : ENNReal.ofReal MD ≤ ENNReal.ofReal MT := ENNReal.ofReal_le_ofReal hMTD
    calc
      _ ≤ P {ω | ENNReal.ofReal MD < aroundDist (S.D (h ω)) A} :=
        measure_mono (fun _ hω => lt_of_le_of_lt hle hω)
      _ ≤ ENNReal.ofReal (ϑ / 2) := h0
      _ ≤ ENNReal.ofReal ϑ := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨⟨hDA, hDR⟩, ?_⟩
  intro δ hδ hδ₀ L hL
  let δI : Set.Ioi (0 : ℝ) := ⟨δ, hδ.1⟩
  have hδIle : (δI : ℝ) ≤ 1 := hδ.2.le
  let Bad : Set DistC := {ω | ∃ (δ' : ℝ) (hδ' : δ' ∈ Ioo (0 : ℝ) 1), δ' < δ₀ ∧
      ∃ L' : ℝ, Real.log δ'⁻¹ ≤ L' ∧ ∃ z ∈ K,
        σ < |Core.locFieldC δ' L' hδ' ω z - X ⟨δ', hδ'.1⟩ ω z|}
  have hbadProb : μ Bad ≤ ENNReal.ofReal (ϑ / 2) := by
    change μ {ω | ∃ (δ' : ℝ) (hδ' : δ' ∈ Ioo (0 : ℝ) 1), δ' < δ₀ ∧
      ∃ L' : ℝ, Real.log δ'⁻¹ ≤ L' ∧ ∃ z ∈ K,
        σ < |Core.locFieldC δ' L' hδ' ((id : DistC → DistC) ω) z - X ⟨δ', hδ'.1⟩ ω z|} ≤ _
    exact hbadBound δ₀ rfl
  have hheatA := (hheat δI hδIle).1
  have hheatR := (hheat δI hδIle).2
  have hVclose_of_good (ω : DistC) (hgood : ω ∉ Bad) :
      ∀ z ∈ V, |X δI ω z - Core.locFieldC δ L hδ ((id : DistC → DistC) ω) z| ≤ σ := by
    intro z hz
    have hzK : z ∈ K := hVK hz
    have hnot : ¬ σ < |Core.locFieldC δ L hδ ((id : DistC → DistC) ω) z - X δI ω z| := by
      intro hlarge
      apply hgood
      exact ⟨δ, hδ, hδ₀, L, hL, z, hzK, by simpa [δI, abs_sub_comm] using hlarge⟩
    have := le_of_not_gt hnot
    simpa [abs_sub_comm] using this
  have hYAcrossCanonical : μ {ω | acrossDist (Core.locMetricY S δ L hδ ((id : DistC → DistC) ω)) A <
        ENNReal.ofReal MT⁻¹} ≤ ENNReal.ofReal ϑ := by
    have hsubset : {ω : DistC | acrossDist (Core.locMetricY S δ L hδ ω) A < ENNReal.ofReal MT⁻¹} ⊆
        {ω | acrossDist (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δI)
          (X δI ω)) A < ENNReal.ofReal MH⁻¹} ∪ Bad := by
      intro ω hω
      by_cases hbad : ω ∈ Bad
      · exact Or.inr hbad
      ·
        have hclose := hVclose_of_good ω hbad
        have hcost : acrossDist (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δI)
            (Core.locFieldC δ L hδ ω)) A < ENNReal.ofReal MT⁻¹ := by
          simpa [Core.locMetricY, Core.locFieldC, B2.Polylog.plLocMetric, δI] using hω
        have hcompare := packetTI_across_lfpp_close_lt_two_mul (S.ξ : ℝ) (S.m δI)
          (Core.locFieldC δ L hδ ω) (X δI ω) A V hV hAnnV (K := σ) hσfac
          (fun z hz => by simpa [abs_sub_comm] using hclose z hz) hcost
        have hbound := lt_of_lt_of_le hcompare hheatThreshold
        exact Or.inl (by simpa using hbound)
    calc
      _ ≤ μ ({ω | acrossDist (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δI)
          (X δI ω)) A < ENNReal.ofReal MH⁻¹} ∪ Bad) :=
          measure_mono hsubset
      _ ≤ μ {ω | acrossDist (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δI)
          (X δI ω)) A < ENNReal.ofReal MH⁻¹} + μ Bad := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ϑ / 2) + ENNReal.ofReal (ϑ / 2) := add_le_add hheatA hbadProb
      _ = ENNReal.ofReal ϑ := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring
  have hYRoundCanonical : μ {ω | ENNReal.ofReal MT <
        aroundDist (Core.locMetricY S δ L hδ ((id : DistC → DistC) ω)) A} ≤ ENNReal.ofReal ϑ := by
    have hsubset : {ω : DistC | ENNReal.ofReal MT <
        aroundDist (Core.locMetricY S δ L hδ ω) A} ⊆
        {ω | ENNReal.ofReal MH < aroundDist (B2.Median.lfppMetric (S.ξ : ℝ)
          (S.m δI) (X δI ω)) A} ∪ Bad := by
      intro ω hω
      by_cases hbad : ω ∈ Bad
      · exact Or.inr hbad
      ·
        have hclose := hVclose_of_good ω hbad
        have hcmp := packetTI_around_lfpp_close_le (S.ξ : ℝ) (S.m δI)
          (Core.locFieldC δ L hδ ω) (X δI ω) A V hV (K := σ) hσfac
          (fun z hz => by simpa [abs_sub_comm] using hclose z hz) hAV
        by_cases hheat : ENNReal.ofReal MH <
            aroundDist (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δI) (X δI ω)) A
        · exact Or.inl hheat
        · have hh : aroundDist (B2.Median.lfppMetric (S.ξ : ℝ)
              (S.m δI) (X δI ω)) A ≤ ENNReal.ofReal MH := le_of_not_gt hheat
          have hbound : aroundDist (Core.locMetricY S δ L hδ ω) A ≤ ENNReal.ofReal MT := by
            calc
              _ ≤ ENNReal.ofReal 2 * aroundDist (B2.Median.lfppMetric (S.ξ : ℝ)
                (S.m δI) (X δI ω)) A := by
                  simpa [Core.locMetricY, Core.locFieldC, B2.Polylog.plLocMetric] using hcmp
              _ ≤ ENNReal.ofReal MT := (mul_le_mul_right hh _).trans hheatAroundThreshold
          exact False.elim ((not_lt_of_ge hbound) hω)
    calc
      _ ≤ μ ({ω | ENNReal.ofReal MH <
          aroundDist (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δI)
            (X δI ω)) A} ∪ Bad) := measure_mono hsubset
      _ ≤ μ {ω | ENNReal.ofReal MH <
          aroundDist (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δI) (X δI ω)) A} + μ Bad :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal (ϑ / 2) + ENNReal.ofReal (ϑ / 2) := add_le_add hheatR hbadProb
      _ = ENNReal.ofReal ϑ := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring
  have hYAcross : P {ω | acrossDist (Core.locMetricY S δ L hδ (h ω)) A < ENNReal.ofReal MT⁻¹} ≤
      ENNReal.ofReal ϑ := by
    have hmeas := B2.Polylog.measurable_plLocMetric (S.ξ : ℝ)
      (Field.uniformLocalizationExponent δ L) S.m δ hδ
    have hset : MeasurableSet {g : DistC |
        acrossDist (Core.locMetricY S δ L hδ g) A < ENNReal.ofReal MT⁻¹} :=
      measurableSet_lt ((measurable_acrossDist A).comp hmeas) measurable_const
    have hprob := Uniqueness.TwoScale.S36.prob_preimage_eq_of_normalized P μ hh hμ
      (LQGMetric.UMeasurableSet.of_measurableSet hset)
    simpa using hprob ▸ hYAcrossCanonical
  have hYRound : P {ω | ENNReal.ofReal MT < aroundDist (Core.locMetricY S δ L hδ (h ω)) A} ≤
      ENNReal.ofReal ϑ := by
    have hmeas := B2.Polylog.measurable_plLocMetric (S.ξ : ℝ)
      (Field.uniformLocalizationExponent δ L) S.m δ hδ
    have hset : MeasurableSet {g : DistC |
        ENNReal.ofReal MT < aroundDist (Core.locMetricY S δ L hδ g) A} :=
      measurableSet_lt measurable_const ((Uniqueness.TwoScale.S36.measurable_aroundDist_fixed A).comp hmeas)
    have hprob := Uniqueness.TwoScale.S36.prob_preimage_eq_of_normalized P μ hh hμ
      (LQGMetric.UMeasurableSet.of_measurableSet hset)
    simpa using hprob ▸ hYRoundCanonical
  exact ⟨hYAcross, hYRound⟩

end SupercriticalLFPPAS.Tightness
