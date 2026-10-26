import SupercriticalLFPPAS.Local.Confinement
import SupercriticalLFPPAS.Inputs.RationalCircles
import SupercriticalLFPPAS.Inputs.RationalCirclePositive
import NV1Evidence

/-!
# (2.9): localized LFPP distances between rational circles (packet P32)

Paper `source/almost-sure-supercritical-lfpp.txt`, Lemma 2.2, (2.9) (l. 199–212): for two fixed
disjoint rational circles `O, O'`, `X̂_ε(O, O') → D(O, O')` in probability. Planning audit
`planning/audits/SB1-sections-1-3.md` A10, "(2.9)", and A5 (circles of positive radius).

* `tendsto_measure_not_ratio`: convergence in probability of finite `ℝ≥0∞`-valued variables to an
  almost surely positive finite limit, in ratio form (subsequence criterion).
* `setDistance_circle_le_of_lt_escape` (deterministic): nearly minimizing paths between the circles
  of length below the escape distance `X(K, ∂B_R)` stay in `B̄_R`, where the two fields are close.
* `circle_localized_ratio_of_comparison`: (2.9) in ratio form: for every `θ > 0`,
  `P[¬ (e^{−θ} D(O, O') ≤ X̂_ε(O, O') ≤ e^θ D(O, O'))] → 0`.
* `circle_localized_subseq_of_comparison`: (2.9) in subsequence form: every sequence `ε_n → 0` has a
  subsequence along which `X̂_ε(O, O') → D(O, O')` almost surely.

The comparison (2.8) (packet D6) enters as the hypothesis `hcomp` (as in
`lemma_2_2_of_comparison`); the rational-circle convergence (1.5) is D2's
`rationalCircleDistance_tendstoInMeasure_seq_of_limit`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
open LQGMetric (DistC heatMollify)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-! ### Convergence in probability in ratio form -/

/-- `e^{−θ} g < g < e^θ g` for `0 < g < ∞`. -/
theorem ratio_lt_of_pos {g : ℝ≥0∞} (hg0 : 0 < g) (hgt : g < ⊤) {θ : ℝ} (hθ : 0 < θ) :
    ENNReal.ofReal (Real.exp (-θ)) * g < g ∧ g < ENNReal.ofReal (Real.exp θ) * g := by
  have h1 : ENNReal.ofReal (Real.exp (-θ)) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (Real.exp_lt_one_iff.2 (by linarith))
  have h2 : 1 < ENNReal.ofReal (Real.exp θ) := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos θ)).2 (Real.one_lt_exp_iff.2 hθ)
  constructor
  · calc ENNReal.ofReal (Real.exp (-θ)) * g < 1 * g :=
          (ENNReal.mul_lt_mul_iff_left hg0.ne' hgt.ne).2 h1
      _ = g := one_mul g
  · calc g = 1 * g := (one_mul g).symm
      _ < ENNReal.ofReal (Real.exp θ) * g := (ENNReal.mul_lt_mul_iff_left hg0.ne' hgt.ne).2 h2

/-- **Convergence in probability, ratio form.** If finite `f ε → g` in measure along every
sequence `ε_n → 0`, with `0 < g < ∞` almost surely, then for every `θ > 0`,
`P[¬ (e^{−θ} g ≤ f ε ≤ e^θ g)] → 0`. -/
theorem tendsto_measure_not_ratio {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Set.Ioi (0 : ℝ) → Ω → ℝ≥0∞} {g : Ω → ℝ≥0∞}
    (hf : ∀ ε, AEMeasurable (f ε) P) (hg : AEMeasurable g P) (hfin : ∀ ε ω, f ε ω ≠ ⊤)
    (hgpos : ∀ᵐ ω ∂P, 0 < g ω ∧ g ω < ⊤)
    (hconv : ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      TendstoInMeasure P (fun n => f (ε n)) atTop g)
    {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun ε => P {ω | ¬ (ENNReal.ofReal (Real.exp (-θ)) * g ω ≤ f ε ω ∧
        f ε ω ≤ ENNReal.ofReal (Real.exp θ) * g ω)}) (comap Subtype.val (𝓝 (0 : ℝ))) (𝓝 0) := by
  set E : Set.Ioi (0 : ℝ) → Set Ω := fun ε => {ω | ENNReal.ofReal (Real.exp (-θ)) * g ω ≤ f ε ω ∧
    f ε ω ≤ ENNReal.ofReal (Real.exp θ) * g ω} with hE
  have hEm : ∀ ε, NullMeasurableSet (E ε) P := fun ε =>
    (nullMeasurableSet_le (aemeasurable_const.mul hg) (hf ε)).inter
      (nullMeasurableSet_le (hf ε) (aemeasurable_const.mul hg))
  have h := tendsto_measure_compl_of_subseq hEm fun ε hε => by
    have hNN := tendstoInMeasure_toNNReal_of_ennreal (fun n ω => f (ε n) ω) g
      (fun n ω => hfin (ε n) ω) (by filter_upwards [hgpos] with ω hω; exact hω.2.ne) (hconv ε hε)
    obtain ⟨ns, hns, hae⟩ := hNN.exists_seq_tendsto_ae
    refine ⟨ns, hns, ?_⟩
    filter_upwards [hae, hgpos] with ω hω hgω
    have hω' : Tendsto (fun i => f (ε (ns i)) ω) atTop (𝓝 (g ω)) := by
      have := (ENNReal.tendsto_toNNReal_iff' (f := fun i => f (ε (ns i)) ω)
        (fun i => hfin _ ω)).1 hω
      rwa [ENNReal.coe_toNNReal hgω.2.ne] at this
    obtain ⟨hlo, hhi⟩ := ratio_lt_of_pos hgω.1 hgω.2 hθ
    filter_upwards [hω'.eventually (Ioo_mem_nhds hlo hhi)] with k hk
    exact ⟨hk.1.le, hk.2.le⟩
  simpa only [hE, compl_ofPred] using h

/-! ### Deterministic comparison of circle distances -/

/-- **Circle distances of nearby fields.** If `O ⊆ K ⊂ B_R`, the two continuous fields are
`s`-close on `B_{R+1}(0)`, and `X_φ(O, O') < X_φ(K, ∂B_R)`, then
`X_ψ(O, O') ≤ e^{|ξ| s} X_φ(O, O')`: nearly minimizing paths stay in `B̄_R`. -/
theorem setDistance_circle_le_of_lt_escape {ξ : ℝ} (a : Set.Ioi (0 : ℝ)) {φ ψ : C(ℂ, ℝ)}
    {s R : ℝ} {K O O' : Set ℂ} (hOK : O ⊆ K) (hKR : ∀ z ∈ K, ‖z‖ < R)
    (hclose : ∀ z ∈ ball (0 : ℂ) (R + 1), |ψ z - φ z| ≤ s)
    (hlt : B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 O O' <
      B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 K (sphere (0 : ℂ) R)) :
    B2.Iface.setDistance (B2.Median.lfppMetric ξ a ψ).1 O O' ≤
      ENNReal.ofReal (Real.exp (|ξ| * s)) * B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 O O' := by
  set e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * s)) with he
  have he0 : e ≠ 0 := by simpa [he] using Real.exp_pos (|ξ| * s)
  have het : e ≠ ⊤ := ENNReal.ofReal_ne_top
  set A := B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 O O'
  set Bd := B2.Iface.setDistance (B2.Median.lfppMetric ξ a φ).1 K (sphere (0 : ℂ) R)
  -- the bound for every level `c` strictly between `A` and the escape distance
  have hc : ∀ c, A < c → c < Bd →
      B2.Iface.setDistance (B2.Median.lfppMetric ξ a ψ).1 O O' ≤ e * c := by
    intro c hAc hcB
    have hlt' := hAc
    unfold A B2.Iface.setDistance at hlt'
    obtain ⟨x, hlt'⟩ := iInf_lt_iff.1 hlt'
    obtain ⟨hx, hlt'⟩ := iInf_lt_iff.1 hlt'
    obtain ⟨y, hlt'⟩ := iInf_lt_iff.1 hlt'
    obtain ⟨hy, hxy⟩ := iInf_lt_iff.1 hlt'
    obtain ⟨P, a', b', hP, hPa, hPb, hlen⟩ := exists_curve_lt (lfppMetric_isLengthSpace ξ a φ) hxy
    have hPc := ((B2.Polylog.lfppMetric_isCurve_iff ξ a φ).1 hP).2
    -- the path stays in `B̄_R`
    have hin : ∀ u ∈ Icc a' b', ‖P u‖ ≤ R := by
      intro u hu
      by_contra hout
      rw [not_le] at hout
      have hxa : ‖P a'‖ < R := by rw [hPa]; exact hKR x (hOK hx)
      obtain ⟨t, ht, hPt, -⟩ := exists_first_hit hu.1 (continuous_norm.comp_continuousOn
        (hPc.mono (Icc_subset_Icc le_rfl hu.2))) hxa.le hout.le
      have h1 : Bd ≤ B2.Median.lfppMetric ξ a φ (x, P t) := by
        unfold Bd B2.Iface.setDistance
        exact iInf₂_le_of_le x (hOK hx) (iInf₂_le (P t) (by simpa using hPt))
      have h2 : B2.Median.lfppMetric ξ a φ (x, P t) ≤ (B2.Median.lfppMetric ξ a φ).len P a' b' := by
        rw [← hPa]
        exact (LSCMetric.apply_le_len _ P ht.1).trans
          (B2.PfeWeyl.len_mono_Icc _ P le_rfl (ht.2.trans hu.2))
      exact (not_lt.2 (h1.trans h2)) (hlen.trans hcB)
    have hPU : ∀ u ∈ Icc a' b', P u ∈ ball (0 : ℂ) (R + 1) := fun u hu => by
      rw [mem_ball, dist_zero_right]
      linarith [hin u hu]
    have hcmp := B2.Polylog.lfppMetric_len_le_of_abs_sub_le ξ a isOpen_ball hclose hPc hPU
    calc B2.Iface.setDistance (B2.Median.lfppMetric ξ a ψ).1 O O'
        ≤ B2.Median.lfppMetric ξ a ψ (x, y) := by
          unfold B2.Iface.setDistance
          exact iInf₂_le_of_le x hx (iInf₂_le y hy)
      _ ≤ (B2.Median.lfppMetric ξ a ψ).len P a' b' := by
          rw [← hPa, ← hPb]
          exact LSCMetric.apply_le_len _ P hP.1
      _ ≤ e * (B2.Median.lfppMetric ξ a φ).len P a' b' := hcmp
      _ ≤ e * c := by gcongr
  refine le_of_forall_gt_imp_ge_of_dense fun w hw => ?_
  have hAw : A < w / e := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl he0) (Or.inl het), mul_comm]
    exact hw
  obtain ⟨c, hc1, hc2⟩ := exists_between (lt_min hAw hlt)
  calc _ ≤ e * c := hc c hc1 (lt_of_lt_of_le hc2 (min_le_right _ _))
    _ ≤ e * (w / e) := by gcongr; exact (lt_of_lt_of_le hc2 (min_le_left _ _)).le
    _ = w := ENNReal.mul_div_cancel he0 het

/-! ### (2.9) -/

theorem isRationalCircle_rationalCircle (q : ℚ × ℚ) (r : ℚ) (hr : 0 < r) :
    B2.Iface.IsRationalCircle (rationalCircle q r) := by
  refine ⟨q.1, q.2, r, le_of_lt hr, ?_⟩
  change Metric.sphere ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) (r : ℝ) =
    Metric.sphere (Complex.mk (q.1 : ℝ) (q.2 : ℝ)) (r : ℝ)
  congr 1
  apply Complex.ext <;> simp

/-- An LFPP limit for one normalizer is an LFPP limit for every normalizer: the median normalizer
is unique (`existsUnique_isLFPPNormalizer`). -/
theorem isLFPPLimit_of_unique {ξ : Set.Ioi (0 : ℝ)} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {D : DistC → LSCMetric} (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) (hDlim : IsLFPPLimit ξ m D)
    (m' : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm' : ∀ ε, IsLFPPNormalizer ξ ε (m' ε)) :
    IsLFPPLimit ξ m' D := by
  obtain rfl : m' = m := funext fun ε =>
    (existsUnique_isLFPPNormalizer ξ ε).unique (hm' ε) (hm ε)
  exact hDlim

/-- The ratio-failure event of (2.9) for the localized metric (empty if `ε ∉ (0, 1)`). -/
def circleRatioFailure {Ω : Type*} (D : DistC → LSCMetric) (ξ : ℝ)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (h : Ω → DistC) (O O' : Set ℂ) (θ ε : ℝ) : Set Ω :=
  {ω | ∃ hε : ε ∈ Ioo (0 : ℝ) 1, ¬ (ENNReal.ofReal (Real.exp (-θ)) *
      B2.Iface.setDistance (D (h ω)).1 O O' ≤
      B2.Iface.setDistance (B2.Polylog.plLocMetric ξ 1 m ε hε (h ω)).1 O O' ∧
    B2.Iface.setDistance (B2.Polylog.plLocMetric ξ 1 m ε hε (h ω)).1 O O' ≤
      ENNReal.ofReal (Real.exp θ) * B2.Iface.setDistance (D (h ω)).1 O O')}

/-- **(2.9), ratio form** (from (2.8), hypothesis `hcomp`): for disjoint rational circles of
positive radius and every `θ > 0`, `P[¬ (e^{−θ} D(O, O') ≤ X̂_ε(O, O') ≤ e^θ D(O, O'))] → 0` as
`ε → 0`. -/
theorem circle_localized_ratio_of_comparison (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hQ : IsLFPPExponent ξ Q) (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (hDlim : IsLFPPLimit ξ m D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) {ζ : ℝ} (hζ1 : ζ < 1)
    (hcomp : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
          P {ω | ¬ B2.Polylog.compareHolds (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω))
            (D (h ω)) (ε ^ (1 - ζ)) U C₀} ≤ ENNReal.ofReal (c₀ * ε ^ p₀))
    (q₁ q₂ : ℚ × ℚ) (r₁ r₂ : ℚ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun ε => P (circleRatioFailure D (ξ : ℝ) m h (rationalCircle q₁ r₁)
      (rationalCircle q₂ r₂) θ ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hhm : Measurable h := hh.1.measurable
  set O := rationalCircle q₁ r₁ with hOdef
  set O' := rationalCircle q₂ r₂ with hO'def
  have hOr := isRationalCircle_rationalCircle q₁ r₁ hr₁
  have hO'r := isRationalCircle_rationalCircle q₂ r₂ hr₂
  have hOc : IsCompact O := isCompact_sphere _ _
  have hO'c : IsCompact O' := isCompact_sphere _ _
  set K := O ∪ O' with hKdef
  have hKc : IsCompact K := hOc.union hO'c
  -- canonical heat versions
  have hver : ∀ ε : Set.Ioi (0 : ℝ), ∃ Y : Ω → C(ℂ, ℝ),
      (∀ᵐ ω ∂P, ∀ z : ℂ, Y ω z = heatMollify (ε : ℝ) (h ω) z) ∧ IsHeatSmoothing P h ε Y :=
    fun ε => exists_heatVersion hh (ε : ℝ) ε.2
  choose X hXeq hX using hver
  -- the limit distance
  set Dist : Ω → ℝ≥0∞ := fun ω => B2.Iface.setDistance (D (h ω)).1 O O' with hDist
  have hDistm : Measurable Dist :=
    (B2.PfeLocal.l4_measurable_setDistance hOc hO'c).comp (hD.1.comp hhm)
  have hpos : ∀ᵐ ω ∂P, 0 < Dist ω ∧ Dist ω < ⊤ := by
    filter_upwards [Inputs.ae_setDist_rationalCircle_pos_lt_top hD P h hh q₁ q₂ r₁ r₂ hr₁ hr₂
      hdisj] with ω hω
    show 0 < B2.Iface.setDistance (D (h ω)).1 O O' ∧ B2.Iface.setDistance (D (h ω)).1 O O' < ⊤
    rw [iface_setDistance_eq_setDist]
    exact hω
  -- ordinary LFPP circle distances and their convergence (1.5)
  set Xd : Set.Ioi (0 : ℝ) → Ω → ℝ≥0∞ := fun ε ω =>
    B2.Iface.setDistance (B2.Median.lfppMetric (ξ : ℝ) (m ε) (X ε ω)).1 O O' with hXd
  have hXdm : ∀ ε, AEMeasurable (Xd ε) P := fun ε =>
    (B2.PfeLocal.l4_measurable_setDistance hOc hO'c).comp_aemeasurable
      (B2.Polylog.aemeasurable_lfppMetric_heat P h hh (ξ : ℝ) (m ε) ε (X ε) (hX ε))
  have hXdfin : ∀ ε ω, Xd ε ω ≠ ⊤ := fun ε ω => by
    simp only [hXd, B2.Polylog.lfppMetric_eq_normalizedLFPPMetric]
    exact (setDistance_normalizedLFPPMetric_lt_top (ξ : ℝ) (m ε) (X ε ω) hOr hO'r).ne
  have hXdconv : ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      TendstoInMeasure P (fun n => Xd (ε n)) atTop Dist := by
    intro ε hε
    have h0 := rationalCircleDistance_tendstoInMeasure_seq_of_limit hQ D hD
      (fun m' hm' => isLFPPLimit_of_unique hm hDlim m' hm') m hm P h hh X hX ε hε O O' hOr hO'r
      (by filter_upwards [hpos] with ω hω; exact hω.2)
      (fun n ω => setDistance_normalizedLFPPMetric_lt_top (ξ : ℝ) (m (ε n)) (X (ε n) ω) hOr hO'r)
    convert h0 using 3 with n ω
    simp only [hXd, B2.Polylog.lfppMetric_eq_normalizedLFPPMetric]
  have hratioX := tendsto_measure_not_ratio hXdm hDistm.aemeasurable hXdfin hpos hXdconv
    (half_pos hθ)
  rw [ENNReal.tendsto_nhds_zero]
  intro τ hτ
  obtain ⟨τ', hτ', hττ'⟩ : ∃ τ' : ℝ, 0 < τ' ∧ ENNReal.ofReal (5 * τ') ≤ τ := by
    by_cases htop : τ = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · refine ⟨τ.toReal / 5, by have := ENNReal.toReal_pos hτ.ne' htop; positivity, ?_⟩
      rw [show 5 * (τ.toReal / 5) = τ.toReal by ring, ENNReal.ofReal_toReal htop]
  have hτ'0 : (0 : ℝ≥0∞) < ENNReal.ofReal τ' := ENNReal.ofReal_pos.2 hτ'
  -- a height cutoff for the limit
  obtain ⟨M, hM0, hMP⟩ : ∃ M : ℝ, 0 ≤ M ∧ P {ω | ENNReal.ofReal M < Dist ω} ≤ ENNReal.ofReal τ' := by
    have hlim := tendsto_measure_of_ae_eventually_not_mem (P := P) (l := atTop)
      (A := fun n : ℕ => {ω | ENNReal.ofReal n < Dist ω})
      (fun n => (measurableSet_lt measurable_const hDistm).nullMeasurableSet) (by
        filter_upwards [hpos] with ω hω
        obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hω.2.ne
        filter_upwards [eventually_ge_atTop N] with n hn hlt
        have : (N : ℝ≥0∞) ≤ ENNReal.ofReal n := by
          rw [ENNReal.ofReal_natCast]
          exact_mod_cast hn
        exact (lt_asymm hN) (lt_of_le_of_lt this hlt))
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_le_nhds hτ'0)).exists
    exact ⟨n, Nat.cast_nonneg n, hn⟩
  -- the ratio event for ordinary LFPP, in the `𝓝[>] 0` form
  obtain ⟨r₁, hr₁0, hr₁P⟩ := exists_pos_of_eventually_comap
    (hratioX.eventually (eventually_le_nhds hτ'0))
  set M' : ℝ := Real.exp (θ / 2) * M + 1 with hM'
  have hM'0 : 0 ≤ M' := by positivity
  -- confinement (Lemma 2.2)
  obtain ⟨R₁, hR₁⟩ := lemma_2_2_of_comparison ξ Q D hD m P h hh X hX hζ1 hcomp K hKc M' τ' hτ'
  obtain ⟨R₂, hR₂⟩ := lemma_2_2_of_comparison ξ Q D hD m P h hh X hX hζ1 hcomp K hKc (2 * M')
    τ' hτ'
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ‖z‖ ≤ B := by
    obtain ⟨r, hr⟩ := hKc.isBounded.subset_closedBall 0
    exact ⟨max r 0, le_max_right _ _, fun z hz =>
      le_trans (by simpa using hr hz) (le_max_left _ _)⟩
  set R : ℝ := max (max R₁ R₂) (B + 1) with hRdef
  have hKR : ∀ z ∈ K, ‖z‖ < R := fun z hz => by
    linarith [hB z hz, le_max_right (max R₁ R₂) (B + 1)]
  -- the field comparison (2.1)
  set s : ℝ := min (Real.log 2) (θ / 2) / ξ with hsdef
  have hs : 0 < s := div_pos (lt_min (Real.log_pos (by norm_num)) (half_pos hθ)) hξ
  have hξs : |(ξ : ℝ)| * s = min (Real.log 2) (θ / 2) := by
    rw [abs_of_pos hξ, hsdef, mul_div_cancel₀ _ hξ.ne']
  have hs2 : Real.exp (|(ξ : ℝ)| * s) ≤ 2 := by
    rw [hξs]
    calc Real.exp (min (Real.log 2) (θ / 2)) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.2 (min_le_left _ _)
      _ = 2 := Real.exp_log (by norm_num)
  have hsθ : Real.exp (|(ξ : ℝ)| * s) ≤ Real.exp (θ / 2) := by
    rw [hξs]
    exact Real.exp_le_exp.2 (min_le_right _ _)
  have hF := (tendsto_measure_heatLocFailure P h hh R hs).eventually (eventually_le_nhds hτ'0)
  filter_upwards [hR₁ R (le_trans (le_max_left _ _) (le_max_left _ _)),
    hR₂ R (le_trans (le_max_right _ _) (le_max_left _ _)), hF, Ioo_mem_nhdsGT hr₁0]
    with ε h1 h2 h3 hεr
  by_cases hε : ε ∈ Ioo (0 : ℝ) 1
  swap
  · have hempty : circleRatioFailure D (ξ : ℝ) m h O O' θ ε = ∅ := by
      ext ω
      simp only [circleRatioFailure, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨hε', -⟩
      exact hε hε'
    rw [hempty, measure_empty]
    exact zero_le
  set ε' : Set.Ioi (0 : ℝ) := ⟨ε, hε.1⟩
  have hP1 := hr₁P ε' hεr.2
  set N : Set Ω := {ω | ¬ ∀ z : ℂ, X ε' ω z = heatMollify ε (h ω) z}
  have hN : P N = 0 := by
    rw [← ae_iff]
    exact hXeq ε'
  set Npos : Set Ω := {ω | ¬ (0 < Dist ω ∧ Dist ω < ⊤)}
  have hNpos : P Npos = 0 := by
    rw [← ae_iff]
    exact hpos
  set E1 := {ω | ENNReal.ofReal M < Dist ω}
  set E2 := {ω | ¬ (ENNReal.ofReal (Real.exp (-(θ / 2))) * Dist ω ≤ Xd ε' ω ∧
    Xd ε' ω ≤ ENNReal.ofReal (Real.exp (θ / 2)) * Dist ω)}
  set E3 := {ω | B2.Iface.setDistance (B2.Median.lfppMetric (ξ : ℝ) (m ⟨ε, hε.1⟩)
    (X ⟨ε, hε.1⟩ ω)).1 K (sphere (0 : ℂ) R) ≤ ENNReal.ofReal M'}
  set E4 := {ω | B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω)).1 K
    (sphere (0 : ℂ) R) ≤ ENNReal.ofReal (2 * M')}
  set E5 := heatLocFailure h R s ε
  have hsub : circleRatioFailure D (ξ : ℝ) m h O O' θ ε ⊆
      E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 ∪ N ∪ Npos := by
    intro ω hω
    obtain ⟨hε', hbad⟩ := hω
    by_contra hnot
    simp only [mem_union, not_or, mem_ofPred_eq, not_lt, not_le, not_not, E1, E2, E3, E4, E5, N,
      Npos] at hnot
    obtain ⟨⟨⟨⟨⟨⟨hE1, hE2⟩, hE3⟩, hE4⟩, hE5⟩, hXω⟩, hposω⟩ := hnot
    apply hbad
    -- the two fields are close on `B_{R+1}`
    have hclose : ∀ z ∈ ball (0 : ℂ) (R + 1),
        |B2.Polylog.plMollifyC 1 ε hε' (h ω) z - X ε' ω z| ≤ s := by
      refine abs_sub_le_of_forall_denseSeq isOpen_ball
        ((ContinuousMap.continuous _).sub (X ε' ω).continuous) fun k hk => ?_
      by_contra hcon
      apply hE5
      unfold heatLocFailure
      rw [dite_eq_left hε']
      refine ⟨k, hk, ?_⟩
      rw [abs_sub_comm, ← hXω]
      exact not_le.1 hcon
    have hclose' : ∀ z ∈ ball (0 : ℂ) (R + 1),
        |X ε' ω z - B2.Polylog.plMollifyC 1 ε hε' (h ω) z| ≤ s := fun z hz => by
      rw [abs_sub_comm]; exact hclose z hz
    -- notation
    set Xh := B2.Iface.setDistance (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε' (h ω)).1 O O'
    have hXdM : Xd ε' ω < ENNReal.ofReal M' := by
      calc Xd ε' ω ≤ ENNReal.ofReal (Real.exp (θ / 2)) * Dist ω := hE2.2
        _ ≤ ENNReal.ofReal (Real.exp (θ / 2)) * ENNReal.ofReal M := by gcongr
        _ = ENNReal.ofReal (Real.exp (θ / 2) * M) := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
        _ < ENNReal.ofReal M' := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
    -- (a) the localized distance is at most `e^{|ξ| s}` times the ordinary one
    have ha : Xh ≤ ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * s)) * Xd ε' ω :=
      setDistance_circle_le_of_lt_escape (ξ := (ξ : ℝ)) (m ε') (φ := X ε' ω)
        (ψ := B2.Polylog.plMollifyC 1 ε hε' (h ω)) subset_union_left hKR hclose
        (lt_of_lt_of_le hXdM hE3.le)
    -- (b) and conversely
    have hXh2 : Xh < ENNReal.ofReal (2 * M') := by
      calc Xh ≤ ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * s)) * Xd ε' ω := ha
        _ ≤ ENNReal.ofReal 2 * Xd ε' ω := by gcongr
        _ < ENNReal.ofReal 2 * ENNReal.ofReal M' :=
            (ENNReal.mul_lt_mul_iff_right (by norm_num) ENNReal.ofReal_ne_top).2 hXdM
        _ = ENNReal.ofReal (2 * M') := (ENNReal.ofReal_mul (by norm_num)).symm
    have hb : Xd ε' ω ≤ ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * s)) * Xh :=
      setDistance_circle_le_of_lt_escape (ξ := (ξ : ℝ)) (m ε')
        (φ := B2.Polylog.plMollifyC 1 ε hε' (h ω)) (ψ := X ε' ω) subset_union_left hKR hclose'
        (lt_of_lt_of_le hXh2 hE4.le)
    -- the ratio bounds
    have hexp : ∀ x : ℝ, ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp x) =
        ENNReal.ofReal (Real.exp (2 * x)) := fun x => by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    refine ⟨?_, ?_⟩
    · -- lower bound
      have hb' : ENNReal.ofReal (Real.exp (-(θ / 2))) * Xd ε' ω ≤ Xh := by
        calc ENNReal.ofReal (Real.exp (-(θ / 2))) * Xd ε' ω
            ≤ ENNReal.ofReal (Real.exp (-(θ / 2))) *
                (ENNReal.ofReal (Real.exp (θ / 2)) * Xh) := by
              gcongr
              exact hb.trans (by gcongr)
          _ = Xh := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
                neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      calc ENNReal.ofReal (Real.exp (-θ)) * Dist ω
          = ENNReal.ofReal (Real.exp (-(θ / 2))) *
              (ENNReal.ofReal (Real.exp (-(θ / 2))) * Dist ω) := by
            rw [← mul_assoc, hexp]
            congr 3
            ring
        _ ≤ ENNReal.ofReal (Real.exp (-(θ / 2))) * Xd ε' ω := by gcongr; exact hE2.1
        _ ≤ Xh := hb'
    · -- upper bound
      calc Xh ≤ ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * s)) * Xd ε' ω := ha
        _ ≤ ENNReal.ofReal (Real.exp (θ / 2)) *
              (ENNReal.ofReal (Real.exp (θ / 2)) * Dist ω) := by
            gcongr
            exact hE2.2
        _ = ENNReal.ofReal (Real.exp θ) * Dist ω := by
            rw [← mul_assoc, hexp]
            congr 3
            ring
  calc P (circleRatioFailure D (ξ : ℝ) m h O O' θ ε)
      ≤ P (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E5 ∪ N ∪ Npos) := measure_mono hsub
    _ ≤ P E1 + P E2 + P E3 + P E4 + P E5 + P N + P Npos := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal τ' + ENNReal.ofReal τ' + ENNReal.ofReal τ' + ENNReal.ofReal τ' +
          ENNReal.ofReal τ' + 0 + 0 := by
        rw [hN, hNpos]
        exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hMP hP1)
          (h1 hε).2) (h2 hε).1) h3) le_rfl) le_rfl
    _ = ENNReal.ofReal (5 * τ') := by
        simp only [add_zero]
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ τ := hττ'

/-- **(2.9), subsequence form**: every sequence `ε_n → 0` in `(0, 1)` has a subsequence along which,
almost surely, `X̂_ε(O, O') → D(O, O')`. -/
theorem circle_localized_subseq_of_comparison (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hQ : IsLFPPExponent ξ Q) (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (hDlim : IsLFPPLimit ξ m D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) {ζ : ℝ} (hζ1 : ζ < 1)
    (hcomp : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
          P {ω | ¬ B2.Polylog.compareHolds (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω))
            (D (h ω)) (ε ^ (1 - ζ)) U C₀} ≤ ENNReal.ofReal (c₀ * ε ^ p₀))
    (q₁ q₂ : ℚ × ℚ) (r₁ r₂ : ℚ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (rationalCircle q₁ r₁) (rationalCircle q₂ r₂))
    (ε : ℕ → ℝ) (hε01 : ∀ n, ε n ∈ Ioo (0 : ℝ) 1) (hεlim : Tendsto ε atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, Tendsto (fun k => B2.Iface.setDistance
        (B2.Polylog.plLocMetric (ξ : ℝ) 1 m (ε (φ k)) (hε01 (φ k)) (h ω)).1
        (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)) atTop
      (𝓝 (B2.Iface.setDistance (D (h ω)).1 (rationalCircle q₁ r₁) (rationalCircle q₂ r₂))) := by
  set O := rationalCircle q₁ r₁
  set O' := rationalCircle q₂ r₂
  have hεW : Tendsto ε atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hεlim, Eventually.of_forall fun n => (hε01 n).1⟩
  set θ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hθdef
  have hθ : ∀ j, 0 < θ j := fun j => Nat.one_div_pos_of_nat
  -- probabilities of the ratio failures along the sequence
  have hev : ∀ j : ℕ, ∀ᶠ n in atTop,
      P (circleRatioFailure D (ξ : ℝ) m h O O' (θ j) (ε n)) ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j
    have hlim := (circle_localized_ratio_of_comparison ξ Q hQ D hD m hm hDlim P h hh hζ1 hcomp
      q₁ q₂ r₁ r₂ hr₁ hr₂ hdisj (hθ j)).comp hεW
    exact hlim.eventually (eventually_le_nhds (ENNReal.pow_pos (by norm_num) j))
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_eventually hev
  have hsum : ∑' j, P (circleRatioFailure D (ξ : ℝ) m h O O' (θ j) (ε (φ j))) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hφP)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hBC := ae_eventually_notMem hsum
  have hpos : ∀ᵐ ω ∂P, 0 < B2.Iface.setDistance (D (h ω)).1 O O' ∧
      B2.Iface.setDistance (D (h ω)).1 O O' < ⊤ := by
    filter_upwards [Inputs.ae_setDist_rationalCircle_pos_lt_top hD P h hh q₁ q₂ r₁ r₂ hr₁ hr₂
      hdisj] with ω hω
    rw [iface_setDistance_eq_setDist]
    exact hω
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hBC, hpos] with ω hω hposω
  set g := B2.Iface.setDistance (D (h ω)).1 O O'
  have hθlim : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlo : Tendsto (fun j => ENNReal.ofReal (Real.exp (-θ j)) * g) atTop (𝓝 g) := by
    have h1 : Tendsto (fun j => ENNReal.ofReal (Real.exp (-θ j))) atTop (𝓝 1) := by
      have hneg : Tendsto (fun j => -θ j) atTop (𝓝 0) := by
        simpa using hθlim.neg
      have := (Real.continuous_exp.tendsto 0).comp hneg
      rw [Real.exp_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hposω.2.ne)
  have hhi : Tendsto (fun j => ENNReal.ofReal (Real.exp (θ j)) * g) atTop (𝓝 g) := by
    have h1 : Tendsto (fun j => ENNReal.ofReal (Real.exp (θ j))) atTop (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp hθlim
      rw [Real.exp_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hposω.2.ne)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hω] with j hj
    by_contra hcon
    exact hj ⟨hε01 (φ j), fun hb => hcon hb.1⟩
  · filter_upwards [hω] with j hj
    by_contra hcon
    exact hj ⟨hε01 (φ j), fun hb => hcon hb.2⟩

end SupercriticalLFPPAS.Local
