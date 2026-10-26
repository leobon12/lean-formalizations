import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import LQGMetric.Metric.WeylBasic

/-!
# Geodesics of continuous-field LFPP metrics on confinement events

On compact Euclidean balls, a continuous LFPP density is bounded above and below.  This makes
near-minimizing paths compact after constant-speed reparametrization and yields a minimizing path.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLFPPAS.Geodesic

theorem geo_trace_subset_ball_of_len_lt_setDist
    (D : SupercriticalLQGUniqueness.LSCMetric) {z : ℂ} {R T : ℝ} {P : ℝ → ℂ}
    (hz : ‖z‖ < R) (hP0 : P 0 = z)
    (hcont : ContinuousOn P (Icc 0 T))
    (hlen : D.len P 0 T < SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
      D {z} (Metric.sphere 0 R)) :
    ∀ t ∈ Icc 0 T, P t ∈ Metric.ball (0 : ℂ) R := by
  intro t ht
  have hnotSphere : ∀ s ∈ Icc 0 T, P s ∉ Metric.sphere (0 : ℂ) R := by
    intro s hs hsphere
    have hboundary :
        SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
          D {z} (Metric.sphere 0 R) ≤ D (z, P s) := by
      unfold SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
      exact iInf₂_le_of_le z (by simp) (iInf₂_le_of_le (P s) hsphere le_rfl)
    have hpoint : D (z, P s) ≤ D.len P 0 s := by
      calc
        D (z, P s) = edist (D.pt z) (D.pt (P s)) := (D.edist_pt z (P s)).symm
        _ = edist ((D.pt ∘ P) 0) ((D.pt ∘ P) s) := by
          simp only [Function.comp_apply, hP0]
        _ ≤ LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) 0 s :=
          LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ P) hs.1
        _ = D.len P 0 s := rfl
    have hmono : D.len P 0 s ≤ D.len P 0 T := by
      change LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) 0 s ≤
        LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) 0 T
      exact LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) le_rfl hs.2
    have hstrict : D (z, P s) <
        SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
          D {z} (Metric.sphere 0 R) := by
      calc
        D (z, P s) ≤ D.len P 0 s := hpoint
        _ ≤ D.len P 0 T := hmono
        _ < _ := hlen
    exact (not_lt_of_ge hboundary) hstrict
  have hnorm : ‖P t‖ ≤ R := by
    by_contra hnot
    have hgt : R < ‖P t‖ := lt_of_not_ge hnot
    have hseg : ContinuousOn (fun s : ℝ => ‖P s‖) (Icc 0 t) :=
      hcont.norm.mono (Icc_subset_Icc le_rfl ht.2)
    obtain ⟨s, hs, hsR⟩ := intermediate_value_Icc ht.1 hseg
      (show R ∈ Icc (‖P 0‖) (‖P t‖) from ⟨by rw [hP0]; exact hz.le, hgt.le⟩)
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have hsphere : P s ∈ Metric.sphere (0 : ℂ) R := by
      rw [Metric.mem_sphere, dist_zero_right]
      exact hsR
    exact hnotSphere s hsT hsphere
  by_contra hnot
  have hge : R ≤ ‖P t‖ := by
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hnot
  have hsphere : P t ∈ Metric.sphere (0 : ℂ) R := by
    rw [Metric.mem_sphere, dist_zero_right]
    exact le_antisymm hnorm hge
  exact hnotSphere t ht hsphere

private theorem geo_scaled_error (a e : ℝ) (ha : 0 < a) :
    ENNReal.ofReal (a⁻¹) * ENNReal.ofReal (a * e) = ENNReal.ofReal e := by
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
  congr 1
  calc
    a⁻¹ * (a * e) = (a⁻¹ * a) * e := by ring
    _ = e := by rw [inv_mul_cancel₀ ha.ne', one_mul]

theorem lfppGeodesic_holds : Core.LFPPGeodesicStmt := by
  intro ξ a φ z w R hz hdist
  classical
  let D := SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a φ
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  let rawD : ℝ≥0∞ := LQGMetric.LFPP.lfppD ξ φ z w
  let d : ℝ≥0∞ := D (z, w)
  let b : ℝ≥0∞ :=
    SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
      D {z} (Metric.sphere 0 R)
  have ha : 0 < (a : ℝ) := a.property
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg z) hz
  have hrawTop : rawD ≠ ∞ := LQGMetric.LFPP.lfppD_ne_top φ.continuous z w
  have hd_eq : d = c * rawD := by
    simp [d, D, c, rawD, SupercriticalLQGUniqueness.B2.Median.lfppMetric_apply,
      SupercriticalLQGUniqueness.B2.LscTop.lfppDistance_eq_lfppD]
  have hdTop : d ≠ ∞ := by
    rw [hd_eq]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hrawTop
  have hsphere : (R : ℂ) ∈ Metric.sphere (0 : ℂ) R := by
    rw [Metric.mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
  have hbLe : b ≤ D (z, (R : ℂ)) := by
    dsimp [b, SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist]
    exact iInf₂_le_of_le z (by simp) (iInf₂_le_of_le (R : ℂ) hsphere le_rfl)
  have hbPointTop : D (z, (R : ℂ)) ≠ ∞ := by
    change SupercriticalLQGUniqueness.B2.Median.lfppMetric ξ a φ
      (z, (R : ℂ)) ≠ ∞
    rw [SupercriticalLQGUniqueness.B2.Median.lfppMetric_apply]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (SupercriticalLQGUniqueness.B2.LscTop.lfppDistance_ne_top ξ φ (z, (R : ℂ)))
  have hbTop : b ≠ ∞ := ne_top_of_le_ne_top hbPointTop hbLe
  have hdbReal : d.toReal < b.toReal := (ENNReal.toReal_lt_toReal hdTop hbTop).2 hdist
  have hbRealPos : 0 < b.toReal := lt_of_le_of_lt ENNReal.toReal_nonneg hdbReal
  let η : ℝ := (b.toReal - d.toReal) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hηgap : d + ENNReal.ofReal η < b := by
    rw [← ENNReal.ofReal_toReal hdTop,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hη.le,
      ← ENNReal.ofReal_toReal hbTop]
    apply (ENNReal.ofReal_lt_ofReal_iff hbRealPos).2
    dsimp [η]
    linarith
  let ε : ℕ → ℝ := fun n => η * (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεle (n : ℕ) : ε n ≤ η := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_iff₀ hn).2 (by linarith)
    dsimp [ε]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac (le_of_lt hη)
  have hεtend : Tendsto ε atTop (𝓝 0) := by
    have hrecip := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hconst : Tendsto (fun _ : ℕ => η) atTop (𝓝 η) := tendsto_const_nhds
    simpa only [ε, mul_zero] using hconst.mul hrecip
  have hεENN : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    have hcomp := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hεtend)
    have hcomp0 : Tendsto (ENNReal.ofReal ∘ ε) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using hcomp
    convert hcomp0 using 1
    rfl
  have hgap (n : ℕ) : d + ENNReal.ofReal (ε n) < b := by
    calc
      d + ENNReal.ofReal (ε n) ≤ d + ENNReal.ofReal η :=
        add_le_add_right (ENNReal.ofReal_le_ofReal (hεle n)) d
      _ < b := hηgap
  have hcostStrict (n : ℕ) : rawD < rawD + ENNReal.ofReal (a * ε n) := by
    conv_lhs => rw [← add_zero rawD]
    rw [ENNReal.add_lt_add_iff_left hrawTop]
    exact ENNReal.ofReal_pos.mpr (mul_pos ha (hεpos n))
  have hnearExists (n : ℕ) : ∃ P : ℝ → ℂ,
      LQGMetric.IsPiecewiseC1Path P z w ∧
        LQGMetric.lfppLen ξ φ P < rawD + ENNReal.ofReal (a * ε n) := by
    have hraw : LQGMetric.LFPP.lfppD ξ φ z w <
        LQGMetric.LFPP.lfppD ξ φ z w + ENNReal.ofReal (a * ε n) := by
      simpa only [rawD] using hcostStrict n
    rw [LQGMetric.LFPP.lfppD, LQGMetric.LFPP.lfppDOn] at hraw
    simp only [iInf_lt_iff] at hraw
    obtain ⟨p, hp⟩ := hraw
    refine ⟨p.1, p.2.1, ?_⟩
    simpa [rawD, LQGMetric.LFPP.lfppD, LQGMetric.LFPP.lfppDOn] using hp
  choose P hP hcost using hnearExists

  have hlenBound (n : ℕ) : D.len (P n) 0 1 ≤ d + ENNReal.ofReal (ε n) := by
    calc
      D.len (P n) 0 1 ≤ c * LQGMetric.lfppLen ξ φ (P n) := by
        simpa only [c] using
          SupercriticalLQGUniqueness.B2.Median.lfppMetric_len_le_lfppLen ξ a φ (hP n)
      _ ≤ c * (rawD + ENNReal.ofReal (a * ε n)) :=
        by simpa [mul_comm] using (mul_le_mul_left (hcost n).le c)
      _ = c * rawD + c * ENNReal.ofReal (a * ε n) := by rw [mul_add]
      _ = d + c * ENNReal.ofReal (a * ε n) := by rw [← hd_eq]
      _ = d + ENNReal.ofReal (ε n) := by
        rw [geo_scaled_error a (ε n) ha]

  have hlenUniform (n : ℕ) : D.len (P n) 0 1 ≤ d + ENNReal.ofReal η := by
    exact (hlenBound n).trans (add_le_add_right (ENNReal.ofReal_le_ofReal (hεle n)) d)
  have hlenUpperTop : d + ENNReal.ofReal η ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hdTop, ENNReal.ofReal_ne_top⟩
  have hcurve (n : ℕ) : D.IsCurve (P n) 0 1 :=
    SupercriticalLQGUniqueness.B2.Median.lfppMetric_isCurve ξ a φ (hP n)
  have hfinite (n : ℕ) : D.len (P n) 0 1 ≠ ∞ :=
    ne_top_of_le_ne_top hlenUpperTop (hlenUniform n)
  have htrace (n : ℕ) : P n '' Icc (0 : ℝ) 1 ⊆ Metric.closedBall (0 : ℂ) R := by
    have hlenlt : D.len (P n) 0 1 < b := (hlenBound n).trans_lt (hgap n)
    have hball := geo_trace_subset_ball_of_len_lt_setDist D hz (hP n).source
      (hP n).continuousOn (by simpa only [b] using hlenlt)
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact Metric.ball_subset_closedBall (hball t ht)

  let K : Set ℂ := Metric.closedBall 0 R
  let M : NNReal := (d + ENNReal.ofReal η).toNNReal
  choose γ hγlen hγtrace hγlip using fun n =>
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.CompactPathInfimum.exists_lipschitz_reparam
      D (P n) (hcurve n) (hfinite n) (htrace n)
  let Q : ℕ → unitInterval → ℂ := fun n => γ n
  let G : ℕ → SupercriticalLQGUniqueness.LSCMetric := fun _ => D
  have hG : Tendsto G atTop (𝓝 D) := tendsto_const_nhds
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_closedBall 0 R
  have hQtrace : ∀ n t, Q n t ∈ K := fun n t => hγtrace n t
  have hQlip : ∀ n, LipschitzWith M (D.pt ∘ Q n) := by
    intro n
    have hcoef : (D.len (P n) 0 1).toNNReal ≤ M := by
      dsimp [M]
      exact ENNReal.toNNReal_mono hlenUpperTop (hlenUniform n)
    change LipschitzWith M (γ n)
    exact (hγlip n).weaken hcoef
  obtain ⟨ψ, P₀, hψ, hlim, hP₀trace⟩ :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.CompactPathInfimum.compact_trace_path_subseq
      hG hK hQtrace hQlip

  have hP₀lip : LipschitzWith M (D.pt ∘ P₀) :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.lipschitz_limit_of_epi
      hG hlim (fun n => hQlip (ψ n))
  let Q : ℝ → ℂ := fun t => P₀ (projIcc 0 1 zero_le_one t)
  have hQcurve : D.IsCurve Q 0 1 :=
    ⟨zero_le_one, (hP₀lip.continuous.comp continuous_projIcc).continuousOn⟩
  have hQ0 : Q 0 = z := by
    change P₀ (projIcc 0 1 zero_le_one 0) = z
    rw [projIcc_left]
    refine tendsto_nhds_unique (hlim.tendsto_at 0) ?_
    refine tendsto_const_nhds.congr fun n => ?_
    change z = (γ (ψ n)) 0
    rw [(γ (ψ n)).source]
    change z = P (ψ n) 0
    exact (hP (ψ n)).source.symm
  have hQ1 : Q 1 = w := by
    change P₀ (projIcc 0 1 zero_le_one 1) = w
    rw [projIcc_right]
    refine tendsto_nhds_unique (hlim.tendsto_at 1) ?_
    refine tendsto_const_nhds.congr fun n => ?_
    change w = (γ (ψ n)) 1
    rw [(γ (ψ n)).target]
    change w = P (ψ n) 1
    exact (hP (ψ n)).target.symm
  let Qseq : ℕ → unitInterval → ℂ := fun n => γ (ψ n)
  have hlenSubseq (n : ℕ) :
      D.len (fun t => Qseq n (projIcc 0 1 zero_le_one t)) 0 1 ≤
        d + ENNReal.ofReal (ε (ψ n)) := by
    have he : D.len (fun t => Qseq n (projIcc 0 1 zero_le_one t)) 0 1 =
        LQGMetric.MetricGeometry.pathLength (γ (ψ n)) := rfl
    rw [he, hγlen]
    exact hlenBound (ψ n)
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => Qseq n (projIcc 0 1 zero_le_one t)) atTop (𝓝 (Q t)) := by
    intro t ht
    simpa [Qseq, Q] using hlim.tendsto_at (projIcc 0 1 zero_le_one t)
  have hliminf :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.CompactPathInfimum.joint_len_le_liminf
      hG (P := fun n t => Qseq n (projIcc 0 1 zero_le_one t)) (P₀ := Q) hpoint
  have hlimit : Tendsto (fun n => d + ENNReal.ofReal (ε (ψ n))) atTop (𝓝 d) := by
    have h0 : Tendsto (fun n => ENNReal.ofReal (ε (ψ n))) atTop (𝓝 0) :=
      hεENN.comp hψ.tendsto_atTop
    simpa only [add_zero] using tendsto_const_nhds.add h0
  have hQle : D.len Q 0 1 ≤ d := by
    refine hliminf.trans ?_
    rw [← hlimit.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hlenSubseq)
  have hQge : d ≤ D.len Q 0 1 := by
    have h := SupercriticalLQGUniqueness.LSCMetric.apply_le_len D Q zero_le_one
    rwa [hQ0, hQ1] at h
  have hQlen : D.len Q 0 1 = d := le_antisymm hQle hQge

  have hQtraceLimit : ∀ t ∈ Icc (0 : ℝ) 1, Q t ∈ K := by
    intro t ht
    change P₀ (projIcc 0 1 zero_le_one t) ∈ K
    exact hP₀trace (projIcc 0 1 zero_le_one t)
  obtain ⟨γlim, hγlen, hγrange⟩ :=
    LQGMetric.MetricGeometry.exists_path_of_curve hQcurve.1 hQcurve.2
  have hγpathlen : LQGMetric.MetricGeometry.pathLength γlim = d := by
    rw [hγlen]
    exact hQlen
  have hγfin : LQGMetric.MetricGeometry.pathLength γlim ≠ ∞ := by
    rw [hγpathlen]
    exact hdTop
  have hγtrace : ∀ t, (γlim t : ℂ) ∈ K := by
    intro t
    obtain ⟨s, hs, hEq⟩ := hγrange (Set.mem_range_self t)
    rw [← hEq]
    change Q s ∈ K
    exact hQtraceLimit s hs
  obtain ⟨P, hunit, hcontD, hP0, hPT, hPrange⟩ :=
    LQGMetric.MetricGeometry.exists_unitSpeed_of_path γlim hγfin
  let T : ℝ := (LQGMetric.MetricGeometry.pathLength γlim).toReal
  let Pℂ : ℝ → ℂ := fun t => P t
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hP0' : Pℂ 0 = z := by
    change P 0 = z
    change P 0 = Q 0 at hP0
    rw [hQ0] at hP0
    exact hP0
  have hPT' : Pℂ T = w := by
    dsimp [Pℂ, T]
    have hPTq : P (LQGMetric.MetricGeometry.pathLength γlim).toReal = Q 1 := by
      exact hPT
    rw [hQ1] at hPTq
    exact hPTq
  have hPtrace : ∀ t ∈ Icc 0 T, Pℂ t ∈ K := by
    intro t ht
    dsimp [Pℂ]
    obtain ⟨s, hs⟩ := hPrange t (by simpa [T] using ht)
    rw [← hs]
    exact hγtrace s
  have hPcurve : D.IsCurve Pℂ 0 T := by
    refine ⟨hT0, ?_⟩
    change ContinuousOn P (Icc 0 T)
    exact hcontD
  have hPunit : HasUnitSpeedOn (D.pt ∘ Pℂ) (Icc 0 T) := by
    change HasUnitSpeedOn P (Icc 0 T)
    simpa [T] using hunit
  have hPcontEuclid : ContinuousOn Pℂ (Icc 0 T) := by
    exact SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.continuousOn_euclidean_of_compact_trace
      D Pℂ hPcurve hK (by
        intro x hx
        obtain ⟨t, ht, rfl⟩ := hx
        exact hPtrace t ht)
  have hPlen : D.len Pℂ 0 T = d := by
    change LQGMetric.MetricGeometry.curveLength (D.pt ∘ Pℂ) 0 T = d
    rw [LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hPunit
      (left_mem_Icc.mpr hT0) (right_mem_Icc.mpr hT0), sub_zero]
    dsimp [T]
    rw [hγpathlen]
    exact (ENNReal.ofReal_toReal hdTop)
  have hgeo : LQGMetric.MetricGeometry.IsGeodesicCurve (D.pt ∘ Pℂ) 0 T := by
    refine ⟨hT0, hPcurve.2, ?_⟩
    calc
      LQGMetric.MetricGeometry.curveLength (D.pt ∘ Pℂ) 0 T = d := hPlen
      _ = edist (D.pt z) (D.pt w) := (D.edist_pt z w).symm
      _ = edist ((D.pt ∘ Pℂ) 0) ((D.pt ∘ Pℂ) T) := by
        simp only [Function.comp_apply]
        have hP0pt : D.pt z = D.pt (Pℂ 0) := congrArg D.pt hP0'.symm
        have hPTpt : D.pt w = D.pt (Pℂ T) := congrArg D.pt hPT'.symm
        rw [← hP0pt, ← hPTpt]
  have hfinalLenLt : D.len P 0 T <
      SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
        D {z} (Metric.sphere 0 R) := by
    rw [hPlen]
    exact hdist
  have hball := geo_trace_subset_ball_of_len_lt_setDist D hz hP0' hPcontEuclid hfinalLenLt
  refine ⟨Pℂ, T, hP0', hPT', ?_⟩
  exact ⟨hgeo, hPunit, hPcontEuclid, hball⟩

end Geodesic

end SupercriticalLFPPAS
