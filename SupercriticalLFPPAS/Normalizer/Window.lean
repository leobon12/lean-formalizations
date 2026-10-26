import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Field.HeatVersion
import SupercriticalLFPPAS.Inputs.RationalCircles
import SupercriticalLFPPAS.Inputs.RationalCirclePositive
import SupercriticalLFPPAS.Inputs.RationalLFPPFinite
import SupercriticalLFPPAS.Inputs.CircleSetDistance
import SupercriticalLQGUniqueness.B2.Polylog.P4LFPPCompare
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3Circle
import SupercriticalLQGUniqueness.B2.Polylog.P2HeatBasic
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import SupercriticalLFPPAS.Inputs.ENNRealConvergenceInMeasure
import NV1Evidence

/-!
# The corrected normalizer interpolation window (Lemma 6.1)

The proof compares two nearby heat fields on a compact ball, confines short
circle-to-circle paths to that ball, and uses convergence of rational-circle
distances to the same positive finite limiting distance.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Normalizer

private theorem exists_curve_lt {L : LSCMetric} (hL : L.IsLengthSpace)
    {x y : ℂ} {c : ℝ≥0∞} (hxy : L (x, y) < c) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), L.IsCurve P a b ∧ P a = x ∧ P b = y ∧ L.len P a b < c := by
  obtain ⟨r, hr, hrc⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hxy
  obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hL x y (lt_of_lt_of_le hxy le_top) (r : ℝ)
    (NNReal.coe_pos.2 hr)
  refine ⟨P, a, b, hP, ha, hb, lt_of_le_of_lt hlen ?_⟩
  rwa [ENNReal.ofReal_coe_nnreal]

/-- A short LFPP path between two compact sets cannot reach a sphere whose
distance from the first set is larger than the path length. -/
private theorem circleDistance_le_of_escape {ξ : ℝ} (a : Set.Ioi (0 : ℝ))
    {φ ψ : C(ℂ, ℝ)} {κ R : ℝ} {K O O' : Set ℂ}
    (hOK : O ⊆ K) (hKR : ∀ z ∈ K, ‖z‖ < R)
    (hclose : ∀ z ∈ ball (0 : ℂ) (R + 1), |ψ z - φ z| ≤ κ)
    (hlt : B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 O O' <
      B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 K (sphere (0 : ℂ) R)) :
    B2.Iface.setDistance (B2.Median.lfppMetric ξ a ψ).1 O O' ≤
      ENNReal.ofReal (Real.exp (|ξ| * κ)) *
        B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 O O' := by
  set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * κ)) with he
  have he0 : e ≠ 0 := by simpa [he] using Real.exp_pos (|ξ| * κ)
  have het : e ≠ ⊤ := ENNReal.ofReal_ne_top
  set A := B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 O O' with hA
  set Bd := B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 K (sphere (0 : ℂ) R) with hBd
  have hc : ∀ c, A < c → c < Bd →
      B2.Iface.setDistance (B2.Median.lfppMetric ξ a ψ).1 O O' ≤ e * c := by
    intro c hAc hcB
    have hlt' := hAc
    unfold A B2.Iface.setDistance at hlt'
    obtain ⟨x, hlt'⟩ := iInf_lt_iff.1 hlt'
    obtain ⟨hx, hlt'⟩ := iInf_lt_iff.1 hlt'
    obtain ⟨y, hlt'⟩ := iInf_lt_iff.1 hlt'
    obtain ⟨hy, hxy⟩ := iInf_lt_iff.1 hlt'
    have hL : (B2.Median.lfppMetric ξ a φ).IsLengthSpace := by
      rw [B2.Polylog.lfppMetric_eq_normalizedLFPPMetric]
      exact B2.PfeWeyl.isLengthSpace_normalizedLFPPMetric ξ a φ
    obtain ⟨P, s, t, hP, hPs, hPt, hlen⟩ := exists_curve_lt hL hxy
    have hPc := ((B2.Polylog.lfppMetric_isCurve_iff ξ a φ).1 hP).2
    have hstart : ‖P s‖ < R := by rw [hPs]; exact hKR x (hOK hx)
    have hstay : ∀ u ∈ Icc s t, ‖P u‖ ≤ R := by
      intro u hu
      by_contra hout
      have hout' : R < ‖P u‖ := not_le.mp hout
      have hnormc : ContinuousOn (fun v : ℝ => ‖P v‖) (Icc s u) :=
        continuous_norm.comp_continuousOn
          (hPc.mono (Icc_subset_Icc le_rfl hu.2))
      obtain ⟨v, hv, hvR⟩ := intermediate_value_Icc hu.1 hnormc
        ⟨hstart.le, hout'.le⟩
      have hvOrder : v ≤ u := hv.2
      have hBdle : Bd ≤ (B2.Median.lfppMetric ξ a φ) (x, P v) := by
        unfold Bd B2.Iface.setDistance
        exact iInf₂_le_of_le x (hOK hx) (iInf₂_le (P v) (by
          simpa [Metric.mem_sphere, dist_zero_right] using hvR))
      have hdistlen : (B2.Median.lfppMetric ξ a φ) (x, P v) ≤
          (B2.Median.lfppMetric ξ a φ).len P s t := by
        rw [← hPs]
        calc
          (B2.Median.lfppMetric ξ a φ) (P s, P v) ≤
              (B2.Median.lfppMetric ξ a φ).len P s v :=
            LSCMetric.apply_le_len _ P hv.1
          _ ≤ (B2.Median.lfppMetric ξ a φ).len P s t :=
            B2.PfeWeyl.len_mono_Icc _ P (a := s) (b := t) (s := s) (t := v)
              le_rfl (hvOrder.trans hu.2)
      exact (not_lt_of_ge (hBdle.trans hdistlen)) (hlen.trans hcB)
    have hPU : ∀ u ∈ Icc s t, P u ∈ ball (0 : ℂ) (R + 1) := fun u hu => by
      rw [mem_ball, dist_zero_right]
      linarith [hstay u hu]
    have hcmp := B2.Polylog.lfppMetric_len_le_of_abs_sub_le ξ a isOpen_ball hclose hPc hPU
    calc B2.Iface.setDistance (B2.Median.lfppMetric ξ a ψ).1 O O'
        ≤ B2.Median.lfppMetric ξ a ψ (x, y) := by
          unfold B2.Iface.setDistance
          exact iInf₂_le_of_le x hx (iInf₂_le y hy)
      _ ≤ (B2.Median.lfppMetric ξ a ψ).len P s t := by
          rw [← hPs, ← hPt]
          exact LSCMetric.apply_le_len _ P hP.1
      _ ≤ e * (B2.Median.lfppMetric ξ a φ).len P s t := hcmp
      _ ≤ e * c := by gcongr
  refine le_of_forall_gt_imp_ge_of_dense fun w hw => ?_
  have hAw : A < w / e := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl he0) (Or.inl het), mul_comm]
    exact hw
  obtain ⟨c, hc1, hc2⟩ := exists_between (lt_min hAw hlt)
  calc _ ≤ e * c := hc c hc1 (lt_of_lt_of_le hc2 (min_le_right _ _))
    _ ≤ e * (w / e) := by gcongr; exact (lt_of_lt_of_le hc2 (min_le_left _ _)).le
    _ = w := ENNReal.mul_div_cancel he0 het

private theorem median_setDistance_scale (ξ : ℝ) (a b : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) (A B : Set ℂ) :
    B2.Iface.setDistance (B2.Median.lfppMetric ξ b φ).1 A B =
      ENNReal.ofReal ((a : ℝ) / (b : ℝ)) *
        B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 A B := by
  rw [B2.Polylog.lfppMetric_eq_normalizedLFPPMetric ξ b φ,
    B2.Polylog.lfppMetric_eq_normalizedLFPPMetric ξ a φ,
    B2.PfeWeyl.setDistance_normalizedLFPPMetric,
    B2.PfeWeyl.setDistance_normalizedLFPPMetric]
  have hfac : ENNReal.ofReal ((b : ℝ)⁻¹) =
      ENNReal.ofReal ((a : ℝ) / (b : ℝ)) * ENNReal.ofReal ((a : ℝ)⁻¹) := by
    have ha : (a : ℝ) ≠ 0 := ne_of_gt a.property
    have hb : (b : ℝ) ≠ 0 := ne_of_gt b.property
    have hdiv : 0 ≤ (a : ℝ) / (b : ℝ) := div_nonneg a.property.le b.property.le
    calc
      ENNReal.ofReal ((b : ℝ)⁻¹) = ENNReal.ofReal (((a : ℝ) / (b : ℝ)) * (a : ℝ)⁻¹) := by
        congr 1
        field_simp [ha, hb]
      _ = ENNReal.ofReal ((a : ℝ) / (b : ℝ)) * ENNReal.ofReal ((a : ℝ)⁻¹) :=
        (ENNReal.ofReal_mul (p := (a : ℝ) / (b : ℝ)) (q := (a : ℝ)⁻¹)
          hdiv)
  rw [hfac, mul_assoc]

private theorem ratio_lt_of_pos {g : ℝ≥0∞} (hg0 : 0 < g) (hgt : g < ⊤)
    {θ : ℝ} (hθ : 0 < θ) :
    ENNReal.ofReal (Real.exp (-θ)) * g < g ∧
      g < ENNReal.ofReal (Real.exp θ) * g := by
  have hlow : ENNReal.ofReal (Real.exp (-θ)) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2
      (Real.exp_lt_one_iff.2 (by linarith))
  have hhigh : 1 < ENNReal.ofReal (Real.exp θ) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos θ)).2
      (Real.one_lt_exp_iff.2 hθ)
  constructor
  · calc
      ENNReal.ofReal (Real.exp (-θ)) * g < 1 * g :=
        (ENNReal.mul_lt_mul_iff_left hg0.ne' hgt.ne).2 hlow
      _ = g := one_mul g
  · calc
      g = 1 * g := (one_mul g).symm
      _ < ENNReal.ofReal (Real.exp θ) * g :=
        (ENNReal.mul_lt_mul_iff_left hg0.ne' hgt.ne).2 hhigh

private theorem measure_tendsto_zero_of_ae_eventually_avoids
    {Ω ι : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {l : Filter ι} [l.IsCountablyGenerated] {A : ι → Set Ω}
    (hA : ∀ i, NullMeasurableSet (A i) P)
    (hae : ∀ᵐ ω ∂P, ∀ᶠ i in l, ω ∉ A i) :
    Tendsto (fun i => P (A i)) l (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro x hx
  let B : ℕ → Set Ω := fun N => ⋃ n, ⋃ (_ : N ≤ n), A (x n)
  have hBm : ∀ N, NullMeasurableSet (B N) P := fun N =>
    NullMeasurableSet.iUnion fun n => NullMeasurableSet.iUnion fun _ => hA (x n)
  have hBanti : Antitone B := by
    intro N N' hNN' ω hω
    simp only [B, mem_iUnion] at hω ⊢
    obtain ⟨n, hn, hωn⟩ := hω
    exact ⟨n, hNN'.trans hn, hωn⟩
  have hlim := tendsto_measure_iInter_atTop hBm hBanti ⟨0, measure_ne_top P _⟩
  have hzero : P (⋂ N, B N) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hx.eventually hω)
    intro hmem
    have hωN := mem_iInter.1 hmem N
    simp only [B, mem_iUnion] at hωN
    obtain ⟨n, hn, hωn⟩ := hωN
    exact hN n hn hωn
  rw [hzero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun N => ?_)
  refine measure_mono fun ω hω => ?_
  simp only [B, mem_iUnion]
  exact ⟨N, le_rfl, hω⟩

private theorem exists_nat_tail_bound {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ≥0∞}
    (hf : Measurable f) (hfinite : ∀ᵐ ω ∂P, f ω < ⊤)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ N : ℕ, P {ω | (N : ℝ≥0∞) < f ω} ≤ η := by
  have hlim : Tendsto (fun n : ℕ => P {ω | (n : ℝ≥0∞) < f ω}) atTop (𝓝 0) :=
    measure_tendsto_zero_of_ae_eventually_avoids
      (fun n => (measurableSet_lt measurable_const hf).nullMeasurableSet) (by
        filter_upwards [hfinite] with ω hω
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hω.ne
        filter_upwards [eventually_ge_atTop N] with n hn hlt
        have hNle : (N : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
        exact (lt_asymm hN) (lt_of_le_of_lt hNle hlt))
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_le_nhds hη)).exists
  exact ⟨N, hN⟩

/-- The deterministic, symmetric normalizer window from the confinement and mesh oscillation
interfaces (corrected Lemma 6.1, SB3 §5(a)). -/
theorem normalizerWindow_of (S : Core.Setup) (hConf : Core.ConfinementStmt S)
    (hM : Core.MeshOscStmt) : Core.NormalizerWindowStmt S := by
  classical
  unfold Core.NormalizerWindowStmt
  intro a ha η hη
  by_contra hEvent
  have hfreq : ∃ᶠ n : ℕ in atTop, ¬ ∀ ε δ : Set.Ioi (0 : ℝ),
      ((n : ℝ) + 1) ^ (-a) ≤ (ε : ℝ) → (ε : ℝ) ≤ (n : ℝ) ^ (-a) →
      ((n : ℝ) + 1) ^ (-a) ≤ (δ : ℝ) → (δ : ℝ) ≤ (n : ℝ) ^ (-a) →
      |Real.log ((S.m ε : ℝ) / (S.m δ : ℝ))| ≤ η :=
    (Filter.not_eventually).1 hEvent
  obtain ⟨ns, hns, hbad⟩ := extraction_of_frequently_atTop hfreq
  have hsel (k : ℕ) : ∃ ε δ : Set.Ioi (0 : ℝ),
      ((ns k : ℝ) + 1) ^ (-a) ≤ (ε : ℝ) ∧ (ε : ℝ) ≤ (ns k : ℝ) ^ (-a) ∧
      ((ns k : ℝ) + 1) ^ (-a) ≤ (δ : ℝ) ∧ (δ : ℝ) ≤ (ns k : ℝ) ^ (-a) ∧
      η < |Real.log ((S.m ε : ℝ) / (S.m δ : ℝ))| := by
    have hk := hbad k
    push_neg at hk
    rcases hk with ⟨ε, δ, helo, hehi, hdlo, hdhi, hlog⟩
    exact ⟨ε, δ, helo, hehi, hdlo, hdhi, hlog⟩
  choose ε δ helo hehi hdlo hdhi hdev using hsel

  obtain ⟨Ω, mΩ, P, hP, h, hhOld⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hh : IsNormalizedWholePlaneGFF h P :=
    SupercriticalLQGUniqueness.isNormalizedWholePlaneGFF_iff_old.mpr hhOld
  obtain ⟨X, hX, hXjoint⟩ := Field.exists_jointHeatVersion_core P h hh
  have hXj : Core.IsJointHeatVersion P h X := ⟨hX, hXjoint⟩

  let O : Set ℂ := rationalCircle (0, 0) 1
  let O' : Set ℂ := rationalCircle (0, 0) 2
  have hOstd : O = sphere (0 : ℂ) (1 : ℝ) := by
    ext z
    simp [O, rationalCircle]
  have hO'std : O' = sphere (0 : ℂ) (2 : ℝ) := by
    ext z
    simp [O', rationalCircle]
  have hO : B2.Iface.IsRationalCircle O := by
    refine ⟨0, 0, 1, by norm_num, ?_⟩
    dsimp [O, rationalCircle]
    change sphere (((0 : ℚ) : ℂ) + ((0 : ℚ) : ℂ) * Complex.I)
        ((1 : ℚ) : ℝ) =
      sphere (Complex.mk ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ)) ((1 : ℚ) : ℝ)
    congr 1
    · apply Complex.ext <;> norm_num
  have hO' : B2.Iface.IsRationalCircle O' := by
    refine ⟨0, 0, 2, by norm_num, ?_⟩
    dsimp [O', rationalCircle]
    change sphere (((0 : ℚ) : ℂ) + ((0 : ℚ) : ℂ) * Complex.I)
        ((2 : ℚ) : ℝ) =
      sphere (Complex.mk ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ)) ((2 : ℚ) : ℝ)
    congr 1
    · apply Complex.ext <;> norm_num
  have hdisStd : Disjoint (sphere (0 : ℂ) (1 : ℝ)) (sphere (0 : ℂ) (2 : ℝ)) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz1
    have h2 : ‖z‖ = 2 := by simpa [Metric.mem_sphere, dist_zero_right] using hz2
    norm_num [h1] at h2
  have hdis : Disjoint O O' := by rw [hOstd, hO'std]; exact hdisStd
  let K : Set ℂ := O ∪ O'
  have hK : IsCompact K :=
    (B2.PfeLocal.l4_isCompact_rationalCircle hO).union
      (B2.PfeLocal.l4_isCompact_rationalCircle hO')
  let d : Ω → ℝ≥0∞ := fun ω => B2.Iface.setDistance (S.D (h ω)).1 O O'
  have hdmeas : Measurable d := by
    exact (B2.PfeLocal.l4_measurable_setDistance
      (B2.PfeLocal.l4_isCompact_rationalCircle hO)
      (B2.PfeLocal.l4_isCompact_rationalCircle hO')).comp (S.hD.1.comp hh.1.measurable)
  have hdpos : ∀ᵐ ω ∂P, 0 < d ω ∧ d ω < ⊤ := by
    filter_upwards [Inputs.ae_setDist_rationalCircle_pos_lt_top S.hD P h hh
      (0, 0) (0, 0) 1 2 (by norm_num) (by norm_num) (by
        simpa [O, O', rationalCircle] using hdis)] with ω hω
    change 0 < B2.Iface.setDistance (S.D (h ω)).1 O O' ∧
      B2.Iface.setDistance (S.D (h ω)).1 O O' < ⊤
    rw [iface_setDistance_eq_setDist]
    exact hω
  have hDfinite : ∀ᵐ ω ∂P, d ω < ⊤ := hdpos.mono fun _ hω => hω.2
  have hDne : ∀ᵐ ω ∂P, d ω ≠ ⊤ := hDfinite.mono fun _ hω => ne_of_lt hω
  obtain ⟨N, htail⟩ := exists_nat_tail_bound hdmeas
    (hDfinite) (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 16))
  let M : ℝ := N

  have hnTop : Tendsto (fun k => (ns k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop
  have hpow : Tendsto (fun k => (ns k : ℝ) ^ (-a)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha).comp hnTop
  have hε0 : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun k => (ε k).property.le) (fun k => hehi k) hpow
  have hδ0 : Tendsto (fun k => (δ k : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun k => (δ k).property.le) (fun k => hdhi k) hpow
  let fε : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    B2.Iface.setDistance
      (B2.Median.lfppMetric (S.ξ : ℝ) (S.m (ε k)) (X (ε k) ω)).1 O O'
  let fδ : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    B2.Iface.setDistance
      (B2.Median.lfppMetric (S.ξ : ℝ) (S.m (δ k)) (X (δ k) ω)).1 O O'
  have hfε : ∀ k ω, fε k ω < ⊤ := by
    intro k ω
    change B2.Iface.setDistance
      (B2.PfeWeyl.normalizedLFPPMetric (S.ξ : ℝ) (S.m (ε k)) (X (ε k) ω)).1 O O' < ⊤
    rw [← B2.Polylog.lfppMetric_eq_normalizedLFPPMetric]
    exact setDistance_normalizedLFPPMetric_lt_top (S.ξ : ℝ)
      (S.m (ε k)) (X (ε k) ω) hO hO'
  have hfδ : ∀ k ω, fδ k ω < ⊤ := by
    intro k ω
    change B2.Iface.setDistance
      (B2.PfeWeyl.normalizedLFPPMetric (S.ξ : ℝ) (S.m (δ k)) (X (δ k) ω)).1 O O' < ⊤
    rw [← B2.Polylog.lfppMetric_eq_normalizedLFPPMetric]
    exact setDistance_normalizedLFPPMetric_lt_top (S.ξ : ℝ)
      (S.m (δ k)) (X (δ k) ω) hO hO'
  have hconvεraw := rationalCircleDistance_tendstoInMeasure_seq_of_limit
    S.hQ S.D S.hD S.hlim S.m S.hm P h hh X hX ε hε0 O O' hO hO' hDfinite hfε
  have hconvε : TendstoInMeasure P fε atTop d := by
    simpa [fε, B2.Polylog.lfppMetric_eq_normalizedLFPPMetric] using hconvεraw
  have hconvδraw := rationalCircleDistance_tendstoInMeasure_seq_of_limit
    S.hQ S.D S.hD S.hlim S.m S.hm P h hh X hX δ hδ0 O O' hO hO' hDfinite hfδ
  have hconvδ : TendstoInMeasure P fδ atTop d := by
    simpa [fδ, B2.Polylog.lfppMetric_eq_normalizedLFPPMetric] using hconvδraw
  have hconvεNN := tendstoInMeasure_toNNReal_of_ennreal fε d
    (fun k ω => (hfε k ω).ne) hDne hconvε
  obtain ⟨φ, hφ, haeε⟩ := hconvεNN.exists_seq_tendsto_ae
  let δ' : ℕ → Set.Ioi (0 : ℝ) := fun k => δ (φ k)
  have hδ'0 : Tendsto (fun k => (δ' k : ℝ)) atTop (𝓝 0) :=
    hδ0.comp hφ.tendsto_atTop
  have hconvδ' := rationalCircleDistance_tendstoInMeasure_seq_of_limit
    S.hQ S.D S.hD S.hlim S.m S.hm P h hh X hX δ' hδ'0 O O' hO hO' hDfinite
    (fun k ω => hfδ (φ k) ω)
  let fδ' : ℕ → Ω → ℝ≥0∞ := fun k ω => fδ (φ k) ω
  have hconvδ' : TendstoInMeasure P fδ' atTop d := by
    simpa [fδ', fδ, B2.Polylog.lfppMetric_eq_normalizedLFPPMetric] using hconvδ'
  have hconvδ'NN := tendstoInMeasure_toNNReal_of_ennreal fδ' d
    (fun k ω => (hfδ (φ k) ω).ne) hDne hconvδ'
  obtain ⟨ψ, hψ, haeδ⟩ := hconvδ'NN.exists_seq_tendsto_ae
  let j : ℕ → ℕ := fun k => φ (ψ k)
  have hj : StrictMono j := hφ.comp hψ
  have hidx : Tendsto (fun k => ns (j k)) atTop atTop :=
    hns.tendsto_atTop.comp hj.tendsto_atTop
  have hθ : 0 < η / 8 := by positivity
  have hξ : (0 : ℝ) < (S.ξ : ℝ) := S.ξ.property
  have hκ : 0 < η / (4 * (S.ξ : ℝ)) := by positivity
  have hκexp : |(S.ξ : ℝ)| * (η / (4 * (S.ξ : ℝ))) = η / 4 := by
    rw [abs_of_pos S.ξ.2]
    field_simp [ne_of_gt hξ]
  have hratioAE : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-(η / 8))) * d ω ≤ fε (j k) ω ∧
        fε (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 8)) * d ω ∧
      ENNReal.ofReal (Real.exp (-(η / 8))) * d ω ≤ fδ (j k) ω ∧
        fδ (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 8)) * d ω := by
    filter_upwards [haeε, haeδ, hdpos] with ω hωε hωδ hωd
    have hωε' : Tendsto (fun k => (fε (j k) ω).toNNReal) atTop
        (𝓝 ((d ω).toNNReal)) := by
      change Tendsto (fun k => (fε (φ (ψ k)) ω).toNNReal) atTop _
      exact hωε.comp hψ.tendsto_atTop
    have hωδ' : Tendsto (fun k => (fδ (j k) ω).toNNReal) atTop
        (𝓝 ((d ω).toNNReal)) := by
      change Tendsto (fun k => (fδ' (ψ k) ω).toNNReal) atTop _
      exact hωδ
    have hωε'' : Tendsto (fun k => fε (j k) ω) atTop (𝓝 (d ω)) := by
      have h := (ENNReal.tendsto_toNNReal_iff' (f := fun k => fε (j k) ω)
        (fun k => (hfε (j k) ω).ne)).1 hωε'
      rwa [ENNReal.coe_toNNReal hωd.2.ne] at h
    have hωδ'' : Tendsto (fun k => fδ (j k) ω) atTop (𝓝 (d ω)) := by
      have h := (ENNReal.tendsto_toNNReal_iff' (f := fun k => fδ (j k) ω)
        (fun k => (hfδ (j k) ω).ne)).1 hωδ'
      rwa [ENNReal.coe_toNNReal hωd.2.ne] at h
    obtain ⟨hlo, hhi⟩ := ratio_lt_of_pos hωd.1 hωd.2 hθ
    filter_upwards [hωε''.eventually (Ioo_mem_nhds hlo hhi),
      hωδ''.eventually (Ioo_mem_nhds hlo hhi)] with k hkε hkδ
    exact ⟨hkε.1.le, hkε.2.le, hkδ.1.le, hkδ.2.le⟩

  let Mlarge : ℝ := Real.exp (η / 8) * ((N : ℝ) + 1)
  have hMlarge : 0 < Mlarge := by positivity
  have hConf' := hConf P h hh X hX K hK Mlarge (1 / 16 : ℝ) (by norm_num)
  obtain ⟨R0, hConfR⟩ := hConf'
  let R : ℝ := max R0 4
  have hRR0 : R0 ≤ R := le_max_left _ _
  have hR4 : 4 ≤ R := le_max_right _ _
  have hOK : O ⊆ K := fun _ hz => Or.inl hz
  have hKR : ∀ z ∈ K, ‖z‖ < R := by
    intro z hz
    rcases hz with hz | hz
    · have hn : ‖z‖ = 1 := by
        have hz' : z ∈ sphere (0 : ℂ) (1 : ℝ) := by rwa [← hOstd]
        simpa [Metric.mem_sphere, dist_zero_right] using hz'
      linarith
    · have hn : ‖z‖ = 2 := by
        have hz' : z ∈ sphere (0 : ℂ) (2 : ℝ) := by rwa [← hO'std]
        simpa [Metric.mem_sphere, dist_zero_right] using hz'
      linarith
  let escapeε : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    B2.Iface.setDistance (Core.lfppM S (ε (j k)) (X (ε (j k)) ω)).1 K (sphere 0 R)
  let escapeδ : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    B2.Iface.setDistance (Core.lfppM S (δ (j k)) (X (δ (j k)) ω)).1 K (sphere 0 R)
  have hεj0 : Tendsto (fun k => (ε (j k) : ℝ)) atTop (𝓝 0) :=
    hε0.comp hj.tendsto_atTop
  have hδj0 : Tendsto (fun k => (δ (j k) : ℝ)) atTop (𝓝 0) :=
    hδ0.comp hj.tendsto_atTop
  have hεjWithin : Tendsto (fun k => (ε (j k) : ℝ)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hεj0, Eventually.of_forall fun k => (ε (j k)).property⟩
  have hδjWithin : Tendsto (fun k => (δ (j k) : ℝ)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hδj0, Eventually.of_forall fun k => (δ (j k)).property⟩
  have hConfEev := hεjWithin.eventually (hConfR R hRR0)
  have hConfDev := hδjWithin.eventually (hConfR R hRR0)
  have hεjlt1 : ∀ᶠ k : ℕ in atTop, (ε (j k) : ℝ) < 1 :=
    hεj0.eventually (eventually_lt_nhds one_pos)
  have hδjlt1 : ∀ᶠ k : ℕ in atTop, (δ (j k) : ℝ) < 1 :=
    hδj0.eventually (eventually_lt_nhds one_pos)
  have hconfE : ∀ᶠ k : ℕ in atTop,
      P {ω | escapeε k ω ≤ ENNReal.ofReal Mlarge} ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
    filter_upwards [hConfEev, hεjlt1] with k hC hk
    have hcut : (ε (j k) : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨(ε (j k)).property, hk⟩
    have hc := (hC hcut).2
    simpa [escapeε, Core.lfppM, iface_setDistance_eq_setDist] using hc
  have hconfD : ∀ᶠ k : ℕ in atTop,
      P {ω | escapeδ k ω ≤ ENNReal.ofReal Mlarge} ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
    filter_upwards [hConfDev, hδjlt1] with k hC hk
    have hcut : (δ (j k) : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨(δ (j k)).property, hk⟩
    have hc := (hC hcut).2
    simpa [escapeδ, Core.lfppM, iface_setDistance_eq_setDist] using hc

  let Kf : Set ℂ := closedBall (0 : ℂ) (R + 1)
  have hKf : IsCompact Kf := isCompact_closedBall _ _
  let fieldGood : ℕ → Set Ω := fun k => {ω | ∀ z ∈ Kf,
    |X (ε (j k)) ω z - X (δ (j k)) ω z| ≤ η / (4 * (S.ξ : ℝ))}
  have hfieldGood : ∀ k, NullMeasurableSet (fieldGood k) P := by
    intro k
    obtain ⟨T, hTK, hTc, hTdense⟩ :=
      (TopologicalSpace.IsSeparable.of_separableSpace Kf).exists_countable_dense_subset
    letI : Countable T := hTc.to_subtype
    have hEq : fieldGood k = ⋂ z : ↥T,
        {ω | |X (ε (j k)) ω z.1 - X (δ (j k)) ω z.1| ≤ η / (4 * (S.ξ : ℝ))} := by
      ext ω
      simp only [fieldGood, mem_setOf_eq, mem_iInter]
      constructor
      · intro h z
        exact h z.1 (hTK z.2)
      · intro h z hz
        have hclosed : IsClosed {w : ℂ |
            |X (ε (j k)) ω w - X (δ (j k)) ω w| ≤ η / (4 * (S.ξ : ℝ))} :=
          isClosed_le (continuous_abs.comp
            ((X (ε (j k)) ω).continuous.sub (X (δ (j k)) ω).continuous)) continuous_const
        have hsubset : T ⊆
            {w : ℂ | |X (ε (j k)) ω w - X (δ (j k)) ω w| ≤ η / (4 * (S.ξ : ℝ))} := by
          intro w hw
          exact h ⟨w, hw⟩
        have hcl : closure T ⊆
            {w : ℂ | |X (ε (j k)) ω w - X (δ (j k)) ω w| ≤ η / (4 * (S.ξ : ℝ))} :=
          closure_minimal hsubset hclosed
        exact hcl (hTdense hz)
    rw [hEq]
    refine NullMeasurableSet.iInter fun z => ?_
    have hXε : AEMeasurable (X (ε (j k))) P :=
      B2.PfeAxioms.aemeasurable_heat_smoothing_version P h hh
        (ε (j k)) (X (ε (j k))) (hX (ε (j k)))
    have hXδ : AEMeasurable (X (δ (j k))) P :=
      B2.PfeAxioms.aemeasurable_heat_smoothing_version P h hh
        (δ (j k)) (X (δ (j k))) (hX (δ (j k)))
    have heε : AEMeasurable (fun ω => X (ε (j k)) ω z.1) P :=
      (continuous_eval_const z.1).measurable.comp_aemeasurable hXε
    have heδ : AEMeasurable (fun ω => X (δ (j k)) ω z.1) P :=
      (continuous_eval_const z.1).measurable.comp_aemeasurable hXδ
    exact (nullMeasurableSet_le (heε.sub heδ).abs aemeasurable_const)

  have hfieldAE : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∈ fieldGood k := by
    have hM' := hM P h hh X hXj a ha
    filter_upwards [hM'] with ω hMω
    have hEv := hidx.eventually (hMω Kf hKf _ hκ)
    filter_upwards [hEv] with k hk
    intro z hz
    exact hk (ε (j k)) (δ (j k))
      (helo (j k)) (hehi (j k)) (hdlo (j k)) (hdhi (j k)) z hz
  have hfieldBad : Tendsto (fun k => P (fieldGood k)ᶜ) atTop (𝓝 0) :=
    measure_tendsto_zero_of_ae_eventually_avoids
      (fun k => (hfieldGood k).compl) (by
        filter_upwards [hfieldAE] with ω hω
        filter_upwards [hω] with k hk
        exact fun hc => hc hk)

  let ratioGoodε : ℕ → Set Ω := fun k => {ω |
    ENNReal.ofReal (Real.exp (-(η / 8))) * d ω ≤ fε (j k) ω ∧
      fε (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 8)) * d ω}
  let ratioGoodδ : ℕ → Set Ω := fun k => {ω |
    ENNReal.ofReal (Real.exp (-(η / 8))) * d ω ≤ fδ (j k) ω ∧
      fδ (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 8)) * d ω}
  have hfεae : ∀ k, AEMeasurable (fε k) P := by
    intro k
    have hm : AEMeasurable (fun ω =>
        B2.Median.lfppMetric (S.ξ : ℝ) (S.m (ε k)) (X (ε k) ω)) P :=
      B2.Polylog.aemeasurable_lfppMetric_heat P h hh (S.ξ : ℝ) (S.m (ε k))
        (ε k) (X (ε k)) (hX (ε k))
    have hs : Measurable fun g : LSCMetric =>
        B2.Iface.setDistance g.1 O O' :=
      B2.PfeLocal.l4_measurable_setDistance
        (B2.PfeLocal.l4_isCompact_rationalCircle hO)
        (B2.PfeLocal.l4_isCompact_rationalCircle hO')
    change AEMeasurable (fun ω =>
      B2.Iface.setDistance
        (B2.Median.lfppMetric (S.ξ : ℝ) (S.m (ε k)) (X (ε k) ω)).1 O O') P
    exact hs.comp_aemeasurable hm
  have hfδae : ∀ k, AEMeasurable (fδ k) P := by
    intro k
    have hm : AEMeasurable (fun ω =>
        B2.Median.lfppMetric (S.ξ : ℝ) (S.m (δ k)) (X (δ k) ω)) P :=
      B2.Polylog.aemeasurable_lfppMetric_heat P h hh (S.ξ : ℝ) (S.m (δ k))
        (δ k) (X (δ k)) (hX (δ k))
    have hs : Measurable fun g : LSCMetric =>
        B2.Iface.setDistance g.1 O O' :=
      B2.PfeLocal.l4_measurable_setDistance
        (B2.PfeLocal.l4_isCompact_rationalCircle hO)
        (B2.PfeLocal.l4_isCompact_rationalCircle hO')
    change AEMeasurable (fun ω =>
      B2.Iface.setDistance
        (B2.Median.lfppMetric (S.ξ : ℝ) (S.m (δ k)) (X (δ k) ω)).1 O O') P
    exact hs.comp_aemeasurable hm
  have hratioGoodε : ∀ k, NullMeasurableSet (ratioGoodε k) P := by
    intro k
    exact (nullMeasurableSet_le (aemeasurable_const.mul hdmeas.aemeasurable)
      (hfεae (j k))).inter
      (nullMeasurableSet_le (hfεae (j k))
        (aemeasurable_const.mul hdmeas.aemeasurable))
  have hratioGoodδ : ∀ k, NullMeasurableSet (ratioGoodδ k) P := by
    intro k
    exact (nullMeasurableSet_le (aemeasurable_const.mul hdmeas.aemeasurable)
      (hfδae (j k))).inter
      (nullMeasurableSet_le (hfδae (j k))
        (aemeasurable_const.mul hdmeas.aemeasurable))
  have hratioGoodεAE : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∈ ratioGoodε k := by
    filter_upwards [hratioAE] with ω hω
    filter_upwards [hω] with k hk
    exact ⟨hk.1, hk.2.1⟩
  have hratioGoodδAE : ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∈ ratioGoodδ k := by
    filter_upwards [hratioAE] with ω hω
    filter_upwards [hω] with k hk
    exact ⟨hk.2.2.1, hk.2.2.2⟩
  have hratioBadε : Tendsto (fun k => P (ratioGoodε k)ᶜ) atTop (𝓝 0) :=
    measure_tendsto_zero_of_ae_eventually_avoids
      (fun k => (hratioGoodε k).compl) (by
        filter_upwards [hratioGoodεAE] with ω hω
        filter_upwards [hω] with k hk
        exact fun hc => hc hk)
  have hratioBadδ : Tendsto (fun k => P (ratioGoodδ k)ᶜ) atTop (𝓝 0) :=
    measure_tendsto_zero_of_ae_eventually_avoids
      (fun k => (hratioGoodδ k).compl) (by
        filter_upwards [hratioGoodδAE] with ω hω
        filter_upwards [hω] with k hk
        exact fun hc => hc hk)

  have hsmallField : ∀ᶠ k : ℕ in atTop,
      P (fieldGood k)ᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ) :=
    hfieldBad.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr (by norm_num)))
  have hsmallRatioE : ∀ᶠ k : ℕ in atTop,
      P (ratioGoodε k)ᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ) :=
    hratioBadε.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr (by norm_num)))
  have hsmallRatioD : ∀ᶠ k : ℕ in atTop,
      P (ratioGoodδ k)ᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ) :=
    hratioBadδ.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr (by norm_num)))

  have hsmallAll : ∀ᶠ k : ℕ in atTop,
      P (ratioGoodε k)ᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ) ∧
      P (ratioGoodδ k)ᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ) ∧
      P (fieldGood k)ᶜ ≤ ENNReal.ofReal (1 / 16 : ℝ) ∧
      P {ω | escapeε k ω ≤ ENNReal.ofReal Mlarge} ≤ ENNReal.ofReal (1 / 16 : ℝ) ∧
      P {ω | escapeδ k ω ≤ ENNReal.ofReal Mlarge} ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
    filter_upwards [hsmallRatioE, hsmallRatioD, hsmallField, hconfE, hconfD]
      with k h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨k, hk⟩ := hsmallAll.exists
  let posBad : Set Ω := {ω | ¬ (0 < d ω ∧ d ω < ⊤)}
  have hposBad : P posBad = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hdpos] with ω hω
    intro hbad
    exact hbad hω
  let bad : Fin 7 → Set Ω :=
    ![(ratioGoodε k)ᶜ, (ratioGoodδ k)ᶜ, (fieldGood k)ᶜ,
      {ω | escapeε k ω ≤ ENNReal.ofReal Mlarge},
      {ω | escapeδ k ω ≤ ENNReal.ofReal Mlarge},
      {ω | (N : ℝ≥0∞) < d ω}, posBad]
  have hbadBound : ∀ i : Fin 7, P (bad i) ≤ ENNReal.ofReal (1 / 16 : ℝ) := by
    intro i
    fin_cases i
    · simpa [bad] using hk.1
    · simpa [bad] using hk.2.1
    · simpa [bad] using hk.2.2.1
    · simpa [bad] using hk.2.2.2.1
    · simpa [bad] using hk.2.2.2.2
    · exact htail
    · change P posBad ≤ ENNReal.ofReal (1 / 16 : ℝ)
      rw [hposBad]
      norm_num
  let Bad : Set Ω := ⋃ i : Fin 7, bad i
  have hBadlt : P Bad < 1 := by
    calc
      P Bad ≤ ∑' i : Fin 7, P (bad i) := measure_iUnion_le _
      _ ≤ ∑' _i : Fin 7, ENNReal.ofReal (1 / 16 : ℝ) :=
        ENNReal.tsum_le_tsum fun i => hbadBound i
      _ < 1 := by
        rw [tsum_fintype]
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast 7, ← ENNReal.ofReal_mul (by positivity)]
        rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
        norm_num
  have hBadne : Bad ≠ Set.univ := by
    intro hEq
    have hUniv : P Bad = 1 := by simpa [hEq] using hP.measure_univ
    rw [hUniv] at hBadlt
    exact (lt_irrefl 1) hBadlt
  have hωexists : ∃ ω, ω ∉ Bad := by
    by_contra hn
    apply hBadne
    ext ω
    constructor
    · intro _
      simp
    · intro _
      by_contra hω
      exact hn ⟨ω, hω⟩
  obtain ⟨ω, hωBad⟩ := hωexists
  have hωi : ∀ i : Fin 7, ω ∉ bad i := by
    simpa [Bad] using hωBad
  have hωratioε : ω ∈ ratioGoodε k := by
    by_contra hnot
    exact hωi 0 (by simp [bad, hnot])
  have hωratioδ : ω ∈ ratioGoodδ k := by
    by_contra hnot
    exact hωi 1 (by simp [bad, hnot])
  have hωfield : ω ∈ fieldGood k := by
    by_contra hnot
    exact hωi 2 (by simp [bad, hnot])
  have hωescε : ENNReal.ofReal Mlarge < escapeε k ω := by
    have hnot := hωi 3
    exact not_le.mp (by simpa [bad] using hnot)
  have hωescδ : ENNReal.ofReal Mlarge < escapeδ k ω := by
    have hnot := hωi 4
    exact not_le.mp (by simpa [bad] using hnot)
  have hωtail : d ω ≤ (N : ℝ≥0∞) := by
    have hnot := hωi 5
    exact le_of_not_gt (by simpa [bad] using hnot)
  have hωpos : 0 < d ω ∧ d ω < ⊤ := by
    have hnot := hωi 6
    have hnotPos : ω ∉ posBad := by simpa [bad] using hnot
    have hpos' : 0 < d ω ∧ d ω ≠ ⊤ := by simpa [posBad] using hnotPos
    exact ⟨hpos'.1, lt_top_iff_ne_top.mpr hpos'.2⟩

  let α := S.m (ε (j k))
  let β := S.m (δ (j k))
  let φε := X (ε (j k)) ω
  let φδ := X (δ (j k)) ω
  let r : ℝ := (α : ℝ) / (β : ℝ)
  have hr : 0 < r := div_pos α.property β.property
  have hrInv : (β : ℝ) / (α : ℝ) = r⁻¹ := by
    dsimp [r]
    field_simp [ne_of_gt (show (0 : ℝ) < (α : ℝ) from α.property),
      ne_of_gt (show (0 : ℝ) < (β : ℝ) from β.property)]

  have hprod : ENNReal.ofReal (Real.exp (η / 8)) * (N : ℝ≥0∞) <
      ENNReal.ofReal Mlarge := by
    rw [← ENNReal.ofReal_natCast N,
      ← ENNReal.ofReal_mul (p := Real.exp (η / 8)) (Real.exp_nonneg _)]
    apply (ENNReal.ofReal_lt_ofReal_iff hMlarge).2
    dsimp [Mlarge]
    nlinarith [Real.exp_pos (η / 8)]
  have hfεlarge : fε (j k) ω < ENNReal.ofReal Mlarge := by
    calc
      fε (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 8)) * d ω := hωratioε.2
      _ ≤ ENNReal.ofReal (Real.exp (η / 8)) * (N : ℝ≥0∞) :=
        by gcongr
      _ < ENNReal.ofReal Mlarge := hprod
  have hfδlarge : fδ (j k) ω < ENNReal.ofReal Mlarge := by
    calc
      fδ (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 8)) * d ω := hωratioδ.2
      _ ≤ ENNReal.ofReal (Real.exp (η / 8)) * (N : ℝ≥0∞) :=
        by gcongr
      _ < ENNReal.ofReal Mlarge := hprod
  have hltε : fε (j k) ω < escapeε k ω := by
    exact hfεlarge.trans hωescε
  have hltδ : fδ (j k) ω < escapeδ k ω := by
    exact hfδlarge.trans hωescδ

  have hcloseε : ∀ z ∈ ball (0 : ℂ) (R + 1),
      |φε z - φδ z| ≤ η / (4 * (S.ξ : ℝ)) := by
    intro z hz
    have hz' : z ∈ Kf := by
      rw [Metric.mem_ball, dist_zero_right] at hz
      change z ∈ closedBall (0 : ℂ) (R + 1)
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz.le
    exact hωfield z hz'
  have hcloseδ : ∀ z ∈ ball (0 : ℂ) (R + 1),
      |φδ z - φε z| ≤ η / (4 * (S.ξ : ℝ)) := by
    intro z hz
    simpa [abs_sub_comm] using hcloseε z hz

  have hωδlt : fδ (j k) ω <
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φδ).1 K (sphere 0 R) := by
    simpa [fδ, escapeδ, Core.lfppM, β, φδ] using hltδ
  have hωεlt : fε (j k) ω <
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φε).1 K (sphere 0 R) := by
    simpa [fε, escapeε, Core.lfppM, α, φε] using hltε
  have hscaleδ :
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φδ).1 O O' =
        ENNReal.ofReal ((β : ℝ) / (α : ℝ)) * fδ (j k) ω := by
    have hs := median_setDistance_scale (S.ξ : ℝ) β α φδ O O'
    simpa [fδ, β, φδ] using hs
  have hscaleε :
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φε).1 O O' =
        ENNReal.ofReal r * fε (j k) ω := by
    have hs := median_setDistance_scale (S.ξ : ℝ) α β φε O O'
    simpa [fε, α, φε, r] using hs
  have hscaleEscδ :
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φδ).1 K (sphere 0 R) =
        ENNReal.ofReal ((β : ℝ) / (α : ℝ)) * escapeδ k ω := by
    have hs := median_setDistance_scale (S.ξ : ℝ) β α φδ K (sphere 0 R)
    simpa [escapeδ, Core.lfppM, β, φδ] using hs
  have hscaleEscε :
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φε).1 K (sphere 0 R) =
        ENNReal.ofReal ((α : ℝ) / (β : ℝ)) * escapeε k ω := by
    have hs := median_setDistance_scale (S.ξ : ℝ) α β φε K (sphere 0 R)
    simpa [escapeε, Core.lfppM, α, φε] using hs
  have hltδα : B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φδ).1 O O' <
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φδ).1 K (sphere 0 R) := by
    rw [hscaleδ, hscaleEscδ]
    have hcoef : 0 < ENNReal.ofReal ((β : ℝ) / (α : ℝ)) :=
      ENNReal.ofReal_pos.mpr (div_pos β.property α.property)
    have hcoef0 : ENNReal.ofReal ((β : ℝ) / (α : ℝ)) ≠ 0 := hcoef.ne'
    have hcoefTop : ENNReal.ofReal ((β : ℝ) / (α : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal ((β : ℝ) / (α : ℝ)) * fδ (j k) ω =
          fδ (j k) ω * ENNReal.ofReal ((β : ℝ) / (α : ℝ)) := mul_comm _ _
      _ < escapeδ k ω * ENNReal.ofReal ((β : ℝ) / (α : ℝ)) :=
        (ENNReal.mul_lt_mul_iff_left hcoef0 hcoefTop).2 hωδlt
      _ = ENNReal.ofReal ((β : ℝ) / (α : ℝ)) * escapeδ k ω := mul_comm _ _
  have hltεβ : B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φε).1 O O' <
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φε).1 K (sphere 0 R) := by
    rw [hscaleε, hscaleEscε]
    have hcoef : 0 < ENNReal.ofReal ((α : ℝ) / (β : ℝ)) :=
      ENNReal.ofReal_pos.mpr (div_pos α.property β.property)
    have hcoef0 : ENNReal.ofReal ((α : ℝ) / (β : ℝ)) ≠ 0 := hcoef.ne'
    have hcoefTop : ENNReal.ofReal ((α : ℝ) / (β : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal ((α : ℝ) / (β : ℝ)) * fε (j k) ω =
          fε (j k) ω * ENNReal.ofReal ((α : ℝ) / (β : ℝ)) := mul_comm _ _
      _ < escapeε k ω * ENNReal.ofReal ((α : ℝ) / (β : ℝ)) :=
        (ENNReal.mul_lt_mul_iff_left hcoef0 hcoefTop).2 hωεlt
      _ = ENNReal.ofReal ((α : ℝ) / (β : ℝ)) * escapeε k ω := mul_comm _ _
  have hcmp1 := @circleDistance_le_of_escape (S.ξ : ℝ) α φδ φε
    (η / (4 * (S.ξ : ℝ))) R K O O' hOK hKR hcloseε hltδα
  have hcmp2 := @circleDistance_le_of_escape (S.ξ : ℝ) β φε φδ
    (η / (4 * (S.ξ : ℝ))) R K O O' hOK hKR hcloseδ hltεβ

  have hratioε' :
      ENNReal.ofReal (Real.exp (-(η / 8))) * d ω ≤ fε (j k) ω ∧
        fε (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 8)) * d ω := by
    simpa [ratioGoodε] using hωratioε
  have hratioδ' :
      ENNReal.ofReal (Real.exp (-(η / 8))) * d ω ≤ fδ (j k) ω ∧
        fδ (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 8)) * d ω := by
    simpa [ratioGoodδ] using hωratioδ
  have hdRpos : 0 < (d ω).toReal :=
    ENNReal.toReal_pos (ne_of_gt hωpos.1) hωpos.2.ne
  have hratioεloR : Real.exp (-(η / 8)) * (d ω).toReal ≤ (fε (j k) ω).toReal := by
    have h := ENNReal.toReal_mono (hfε (j k) ω).ne hratioε'.1
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have hratioεhiR : (fε (j k) ω).toReal ≤ Real.exp (η / 8) * (d ω).toReal := by
    have hfin : ENNReal.ofReal (Real.exp (η / 8)) * d ω ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωpos.2.ne
    have h := ENNReal.toReal_mono hfin hratioε'.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have hratioδloR : Real.exp (-(η / 8)) * (d ω).toReal ≤ (fδ (j k) ω).toReal := by
    have h := ENNReal.toReal_mono (hfδ (j k) ω).ne hratioδ'.1
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h
  have hratioδhiR : (fδ (j k) ω).toReal ≤ Real.exp (η / 8) * (d ω).toReal := by
    have hfin : ENNReal.ofReal (Real.exp (η / 8)) * d ω ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωpos.2.ne
    have h := ENNReal.toReal_mono hfin hratioδ'.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using h

  have hcmp1exp :
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φε).1 O O' ≤
        ENNReal.ofReal (Real.exp (η / 4)) *
          B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φδ).1 O O' := by
    simpa [hκexp] using hcmp1
  have hcmp2exp :
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φδ).1 O O' ≤
        ENNReal.ofReal (Real.exp (η / 4)) *
          B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φε).1 O O' := by
    simpa [hκexp] using hcmp2
  have hcrossδ :
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φδ).1 O O' < ⊤ := by
    rw [B2.Polylog.lfppMetric_eq_normalizedLFPPMetric]
    exact setDistance_normalizedLFPPMetric_lt_top (S.ξ : ℝ) α φδ hO hO'
  have hcrossε :
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φε).1 O O' < ⊤ := by
    rw [B2.Polylog.lfppMetric_eq_normalizedLFPPMetric]
    exact setDistance_normalizedLFPPMetric_lt_top (S.ξ : ℝ) β φε hO hO'
  have hcmp1f : fε (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 4)) *
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) α φδ).1 O O' := by
    simpa [fε, α, φε] using hcmp1exp
  have hcmp2f : fδ (j k) ω ≤ ENNReal.ofReal (Real.exp (η / 4)) *
      B2.Iface.setDistance (B2.Median.lfppMetric (S.ξ : ℝ) β φε).1 O O' := by
    simpa [fδ, β, φδ] using hcmp2exp
  have hcmp1R : (fε (j k) ω).toReal ≤
      Real.exp (η / 4) * r⁻¹ * (fδ (j k) ω).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcrossδ.ne) hcmp1f
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      hscaleδ, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg β.property.le α.property.le)] at h
    simpa [hrInv, mul_assoc] using h
  have hcmp2R : (fδ (j k) ω).toReal ≤
      Real.exp (η / 4) * r * (fε (j k) ω).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcrossε.ne) hcmp2f
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      hscaleε, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg α.property.le β.property.le)] at h
    simpa [mul_assoc] using h

  have hθeq : η / 4 + 2 * (η / 8) = η / 2 := by ring
  have hExpEq : Real.exp (η / 4) * Real.exp (η / 8) =
      Real.exp (η / 2) * Real.exp (-(η / 8)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hbase1 : Real.exp (-(η / 8)) ≤
      Real.exp (η / 4) * r⁻¹ * Real.exp (η / 8) := by
    have h := hratioεloR.trans (hcmp1R.trans
      (mul_le_mul_of_nonneg_left hratioδhiR
        (mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hr.le))))
    have h' : Real.exp (-(η / 8)) * (d ω).toReal ≤
        (Real.exp (η / 4) * r⁻¹ * Real.exp (η / 8)) * (d ω).toReal := by
      simpa [mul_assoc] using h
    exact le_of_mul_le_mul_right h' hdRpos
  have hbase2 : Real.exp (-(η / 8)) ≤
      Real.exp (η / 4) * r * Real.exp (η / 8) := by
    have h := hratioδloR.trans (hcmp2R.trans
      (mul_le_mul_of_nonneg_left hratioεhiR
        (mul_nonneg (Real.exp_pos _).le hr.le)))
    have h' : Real.exp (-(η / 8)) * (d ω).toReal ≤
        (Real.exp (η / 4) * r * Real.exp (η / 8)) * (d ω).toReal := by
      simpa [mul_assoc] using h
    exact le_of_mul_le_mul_right h' hdRpos
  have hrUpper : r ≤ Real.exp (η / 2) := by
    have hmul := mul_le_mul_of_nonneg_right hbase1 hr.le
    have hcancel :
        (Real.exp (η / 4) * r⁻¹ * Real.exp (η / 8)) * r =
          Real.exp (η / 4) * Real.exp (η / 8) := by
      calc
        (Real.exp (η / 4) * r⁻¹ * Real.exp (η / 8)) * r =
            (Real.exp (η / 4) * Real.exp (η / 8)) * (r⁻¹ * r) := by ring
        _ = Real.exp (η / 4) * Real.exp (η / 8) := by rw [inv_mul_cancel₀ hr.ne', mul_one]
    have hcancel' :
        (Real.exp (η / 4) * Real.exp (η / 8)) =
          Real.exp (η / 2) * Real.exp (-(η / 8)) := by simpa [hθeq] using hExpEq
    have hmul' : Real.exp (-(η / 8)) * r ≤
        Real.exp (η / 2) * Real.exp (-(η / 8)) := by
      calc
        Real.exp (-(η / 8)) * r ≤
            (Real.exp (η / 4) * r⁻¹ * Real.exp (η / 8)) * r := hmul
        _ = Real.exp (η / 2) * Real.exp (-(η / 8)) := hcancel.trans hcancel'
    have hmul'' : r * Real.exp (-(η / 8)) ≤
        Real.exp (η / 2) * Real.exp (-(η / 8)) := by
      calc
        r * Real.exp (-(η / 8)) = Real.exp (-(η / 8)) * r := mul_comm _ _
        _ ≤ Real.exp (η / 2) * Real.exp (-(η / 8)) := hmul'
    exact le_of_mul_le_mul_right hmul'' (Real.exp_pos _)
  have hrInvUpper : r⁻¹ ≤ Real.exp (η / 2) := by
    have hmul := mul_le_mul_of_nonneg_right hbase2 (inv_nonneg.mpr hr.le)
    have hcancel :
        (Real.exp (η / 4) * r * Real.exp (η / 8)) * r⁻¹ =
          Real.exp (η / 4) * Real.exp (η / 8) := by
      calc
        (Real.exp (η / 4) * r * Real.exp (η / 8)) * r⁻¹ =
            (Real.exp (η / 4) * Real.exp (η / 8)) * (r * r⁻¹) := by ring
        _ = Real.exp (η / 4) * Real.exp (η / 8) := by rw [mul_inv_cancel₀ hr.ne', mul_one]
    have hcancel' :
        (Real.exp (η / 4) * Real.exp (η / 8)) =
          Real.exp (η / 2) * Real.exp (-(η / 8)) := by simpa [hθeq] using hExpEq
    have hmul' : Real.exp (-(η / 8)) * r⁻¹ ≤
        Real.exp (η / 2) * Real.exp (-(η / 8)) := by
      calc
        Real.exp (-(η / 8)) * r⁻¹ ≤
            (Real.exp (η / 4) * r * Real.exp (η / 8)) * r⁻¹ := hmul
        _ = Real.exp (η / 2) * Real.exp (-(η / 8)) := hcancel.trans hcancel'
    have hmul'' : r⁻¹ * Real.exp (-(η / 8)) ≤
        Real.exp (η / 2) * Real.exp (-(η / 8)) := by
      calc
        r⁻¹ * Real.exp (-(η / 8)) = Real.exp (-(η / 8)) * r⁻¹ := mul_comm _ _
        _ ≤ Real.exp (η / 2) * Real.exp (-(η / 8)) := hmul'
    exact le_of_mul_le_mul_right hmul'' (Real.exp_pos _)
  have hlogUpper : Real.log r ≤ η / 2 :=
    (Real.log_le_iff_le_exp hr).2 hrUpper
  have hlogLower : -(η / 2) ≤ Real.log r := by
    have h := (Real.log_le_iff_le_exp (inv_pos.mpr hr)).2 hrInvUpper
    rw [Real.log_inv] at h
    linarith
  have hlogAbs : |Real.log r| ≤ η / 2 := (abs_le).2 ⟨hlogLower, hlogUpper⟩
  have hdev' : η < |Real.log r| := by
    simpa [α, β, r] using hdev (j k)
  linarith

end SupercriticalLFPPAS.Normalizer
