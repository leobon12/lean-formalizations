import SupercriticalLFPPAS.Separating.Lemma35Canonical
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.LocalEventToolkit
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

/-!
# Lemma 3.5′ (`Core.Lemma35Stmt`): assembly

Packet P35, final target `lemma35_of` (`planning/packets/P35-targets.md`; ruling P8):
`Core.Lemma35Stmt S` from `Core.KappaBoundsStmt S`, `Core.ScalingDStmt S`, `Core.DilationStmt S`
and `Core.AnnTightStmt S`. Constants (SB2 D3, with the scale ratio `1/16` of the annulus iteration
`annulus_iteration_ae_translated_open (1/16) (1/2)`): rate `a = 2 log 16 (q + 2)`, fraction `1/2`,
marginal `p`; tightness failure `ϑ = (1 - p)/4` at `A_{1,2}(0)` and `A_{2,3}(0)`; the event constant
`C_ev = max(M_t, 1)`; `θ = log(1 + 2/C_ev²)/(4 log 16)`; `C = max(C_ev² C_κ (1 + 2/C_ev²)², 32400 c₀ e^a)`;
`η₀ = 1/256`; `δ₀ = min(4η δ_T, 4η e⁻², ε_κ, (η/25)²)`; `ℓ₀ = 2η`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn plEventLoc plLocMetric annAround annAt plRad)
open LQGMetric (DistC DistOn addConst restrictTo circleAvg TestC)
open LQGMetric.Blueprint (AEEventIn fieldSigma fieldSigma0On countOcc annulus)

/-! ### Locality modulo constants in the form `fieldSigma0On` -/

/-- A test function of mass one supported in a nonempty open set (as
`LQGMetric.GermSplit.exists_test_unit`). -/
theorem p35_exists_unit_test {V : TopologicalSpace.Opens ℂ} (hV : (V : Set ℂ).Nonempty) :
    ∃ ψ : TestC, tsupport (ψ : ℂ → ℝ) ⊆ V ∧ ∫ x, ψ x = 1 := by
  obtain ⟨c, hc⟩ := hV
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 V.2 c hc
  let b : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨⟨b.normed volume, b.contDiff_normed (n := ⊤), b.hasCompactSupport_normed,
    subset_univ _⟩, ?_, b.integral_normed⟩
  change tsupport (b.normed volume) ⊆ V
  rw [b.tsupport_normed_eq]
  exact (closedBall_subset_ball (by change r / 2 < r; linarith)).trans hrV

/-- **From arbitrary recentrings to mean-zero pairings.** An event that is almost surely an event
of the restriction to `U` of `h - X` for every `X` is almost surely an event of the mean-zero
pairings of `h` supported in `U` (recentre by the pairing with a unit test function in `U`). -/
theorem p35_aeEventIn_fieldSigma0On {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (h : Ω → DistC) (U : TopologicalSpace.Opens ℂ) (hU : (U : Set ℂ).Nonempty) {E : Set Ω}
    (hE : ∀ X : Ω → ℝ, AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-X ω)) U) E) :
    AEEventIn P (fieldSigma0On h U) E := by
  obtain ⟨ψ, hψU, hψ1⟩ := p35_exists_unit_test hU
  exact Uniqueness.Toolkit.LocalEvents.aeEventIn_fieldSigma0On_of_normIn h ψ hψ1 U hψU
    (hE fun ω => h ω ψ)

/-! ### Small facts -/

/-- `κ_ε(1) = 1`. -/
theorem p35_kappa_one (ξ Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (ε : Set.Ioi (0 : ℝ)) :
    Compare.kappa ξ Q m ε ⟨1, (one_pos : (0 : ℝ) < 1)⟩ = 1 := by
  unfold Compare.kappa
  have harg : (⟨(ε : ℝ) / (1 : ℝ), Set.mem_Ioi.mpr (div_pos ε.2 one_pos)⟩ : Set.Ioi (0 : ℝ)) = ε :=
    Subtype.ext (div_one _)
  simp only [harg, Real.one_rpow, one_mul]
  exact div_self (ne_of_gt (m ε).2)

theorem p35_norm_bounds_of_subset {K : Set ℂ}
    (hK : K ⊆ (annulus 0 (3 / 4) (5 / 2) : Set ℂ)) : ∀ k ∈ K, 3 / 4 ≤ ‖k‖ ∧ ‖k‖ ≤ 5 / 2 := by
  intro k hk
  have h := hK hk
  change 3 / 4 < ‖k - 0‖ ∧ ‖k - 0‖ < 5 / 2 at h
  rw [sub_zero] at h
  exact ⟨h.1.le, h.2.le⟩

/-- For `η < 1/256` there is at least one scale. -/
theorem p35_count_pos {η : ℝ} (hη : 0 < η) (hη0 : η < 1 / 256) : 1 ≤ p35ScaleCount η := by
  unfold p35ScaleCount
  rw [Nat.one_le_floor_iff]
  have hl := log_sixteen_pos
  rw [le_div_iff₀ (by positivity), one_mul]
  have h256 : Real.log 256 = 2 * Real.log 16 := by
    rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [← h256]
  apply Real.log_le_log (by norm_num)
  rw [le_inv_comm₀ (by norm_num) hη]
  exact hη0.le.trans (by norm_num)

theorem p35_sqrt_lt {η : ℝ} {x : ℝ} (hx : 0 < x) (hηx : η < x ^ 2) :
    Real.sqrt η < x := by
  rw [Real.sqrt_lt' hx]
  exact hηx

/-- `e^{-a N} ≤ e^{a} η^{q+2}` for `a = 2 log 16 (q + 2)`. -/
theorem p35_exp_count_le {η q : ℝ} (hη : 0 < η) (hq : 0 < q) :
    Real.exp (-(2 * Real.log 16 * (q + 2)) * p35ScaleCount η) ≤
      Real.exp (2 * Real.log 16 * (q + 2)) * η ^ (q + 2) := by
  have hl := log_sixteen_pos
  have hcount := p35_count_gt (η := η)
  have hpow : η ^ (q + 2) = Real.exp (-(q + 2) * Real.log η⁻¹) := by
    rw [Real.rpow_def_of_pos hη, Real.log_inv]
    ring_nf
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h2 : 0 < 2 * Real.log 16 * (q + 2) := by positivity
  have key : Real.log η⁻¹ / (2 * Real.log 16) * (2 * Real.log 16 * (q + 2)) =
      (q + 2) * Real.log η⁻¹ := by
    field_simp
  nlinarith [mul_lt_mul_of_pos_right hcount h2]

/-- The cutoff ratios at the scales `s ∈ [4η, 1]`. -/
theorem p35_ratio_facts {η δ s δT : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hs4 : 4 * η ≤ s) (hs1 : s ≤ 1)
    (hδ1 : δ < 4 * η * δT) (hδ2 : δ < 4 * η * Real.exp (-2)) :
    δ / s ∈ Ioo (0 : ℝ) 1 ∧ δ / s < δT ∧ 1 < Real.log (δ / s)⁻¹ ∧
      Real.log (δ / s)⁻¹ ≤ Real.log δ⁻¹ := by
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hs4
  have he2 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hle : δ / s ≤ δ / (4 * η) := div_le_div_of_nonneg_left hδ.le (by positivity) hs4
  have h4η : 0 < 4 * η := by positivity
  have hlt2 : δ / s < Real.exp (-2) := by
    refine lt_of_le_of_lt hle ?_
    rw [div_lt_iff₀ h4η]
    linarith
  have hpos : 0 < δ / s := div_pos hδ hs
  refine ⟨⟨hpos, lt_trans hlt2 he2⟩, ?_, ?_, ?_⟩
  · refine lt_of_le_of_lt hle ?_
    rw [div_lt_iff₀ h4η]
    linarith
  · rw [Real.lt_log_iff_exp_lt (inv_pos.2 hpos)]
    have : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.2 (by norm_num)
    have hinv : Real.exp 2 < (δ / s)⁻¹ := by
      rw [lt_inv_comm₀ (Real.exp_pos 2) hpos, ← Real.exp_neg]
      exact hlt2
    linarith
  · apply Real.log_le_log (inv_pos.2 hpos)
    rw [inv_div]
    calc s / δ ≤ 1 / δ := div_le_div_of_nonneg_right hs1 hδ.le
      _ = δ⁻¹ := one_div δ

theorem P35SeparatingCurve.mono {d' : LSCMetric} {p : ℂ} {ρ R : ℝ} {ℓ ℓ' : ℝ≥0∞}
    (h : P35SeparatingCurve d' p ρ R ℓ) (hℓ : ℓ ≤ ℓ') : P35SeparatingCurve d' p ρ R ℓ' := by
  obtain ⟨σ, a, b, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨σ, a, b, h1, h2, h3, h4, h5, h6.trans hℓ⟩

/-- **Conversion to the interface form `Core.SurroundProp`.** -/
theorem p35_surroundProp_of {d d' : LSCMetric} {Kp : Set ℂ} {r η b : ℝ} (hηr : 0 < η * r)
    (H : ∀ (P : ℝ → ℂ) (α β : ℝ) (p : ℂ), p ∈ Kp →
      P35GeodesicThrough d P α β p (2 * Real.sqrt η * r) →
      P35SeparatingCurve d' p (η * r) (2 * Real.sqrt η * r) (ENNReal.ofReal b * d.len P α β)) :
    Core.SurroundProp d d' Kp r η b := by
  intro P α β hgeo hPc p hp hpP hα hβ
  obtain ⟨σ, a, b', hσ, hσc, htr, hin, hout, hlen⟩ := H P α β p hp ⟨hgeo, hPc, hpP, hα, hβ⟩
  refine ⟨σ, a, b', hσ, hσc, htr, ?_, hin, isBounded_ball.subset hout, hlen⟩
  intro hmem
  have hpU : p ∈ connectedComponentIn (σ '' Icc a b')ᶜ p := hin (mem_ball_self hηr)
  exact connectedComponentIn_subset _ _ hpU hmem

/-- `∑_{c ∈ s} ofReal x = ofReal (#s · x)`. -/
theorem p35_sum_ofReal_const {ι : Type*} (s : Finset ι) (x : ℝ) :
    ∑ _c ∈ s, ENNReal.ofReal x = ENNReal.ofReal ((s.card : ℝ) * x) := by
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-! ### The assembly -/

/-- **Lemma 3.5′ (SB2 D3), interface form.** For every compact `K ⊂ A_{3/4,5/2}(0)` and `q > 0`
there are `θ, C, η₀ > 0` such that for `η < η₀` there are `δ₀, ℓ₀ > 0` with: for `δ < δ₀`,
`L ≥ log δ⁻¹`, `δL < ℓ₀` and every normalized whole-plane GFF `h`, an event `F`, almost surely an event
of `h|_{A_{1/2,3}(0)}` modulo additive constants, with `P(F) ≥ 1 - Cη^q`, on which every point of
`K` on a Euclidean-continuous `D`-geodesic (resp. `Y_{δ,L}`-geodesic) segment with endpoints outside
`B_{2η^{1/2}}(p)` is surrounded inside `B_{2η^{1/2}}(p)` by a `Y_{δ,L}`-curve (resp. `D`-curve) around
`B_η(p)` of length at most `Cη^θ` times the length of the segment. -/
theorem lemma35_of (S : Core.Setup) (hK : Core.KappaBoundsStmt S) (hS : Core.ScalingDStmt S)
    (hD : Core.DilationStmt S) (hT : Core.AnnTightStmt S) : Core.Lemma35Stmt S := by
  intro K _hKc hKsub q hq
  have hKn := p35_norm_bounds_of_subset hKsub
  have hDw : B2.Iface.IsPfeWeakMetric S.ξ S.D (Compare.powScale S.ξ S.Q) :=
    Compare.isPfeWeakMetric_of_isStrongLQGMetric S.hD
  have hl := log_sixteen_pos
  -- (1.6): rate `a`, fraction `1/2`, marginal `p`
  set a : ℝ := 2 * Real.log 16 * (q + 2) with ha_def
  have ha : 0 < a := by positivity
  obtain ⟨p, c₀, hp0, hp1, hc₀, hconc⟩ :=
    Uniqueness.Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open (1 / 16) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) a ha (1 / 2) (by norm_num) (by norm_num)
  -- annular tightness at `A_{1,2}(0)` and `A_{2,3}(0)` with failure `ϑ = (1 - p)/4`
  set ϑ : ℝ := (1 - p) / 4 with hϑ_def
  have hϑ : 0 < ϑ := by rw [hϑ_def]; linarith
  obtain ⟨M₁, δ₁, hM₁, hδ₁, hT₁⟩ := hT p35A12 ϑ hϑ
  obtain ⟨M₂, δ₂, hM₂, hδ₂, hT₂⟩ := hT p35A23 ϑ hϑ
  set Mt : ℝ := max M₁ M₂ with hMt_def
  set δT : ℝ := min δ₁ δ₂ with hδT_def
  have hMt : 0 < Mt := lt_max_of_lt_left hM₁
  have hδT : 0 < δT := lt_min hδ₁ hδ₂
  have hinv1 : ENNReal.ofReal Mt⁻¹ ≤ ENNReal.ofReal M₁⁻¹ :=
    ENNReal.ofReal_le_ofReal (inv_anti₀ hM₁ (le_max_left _ _))
  have hle2 : ENNReal.ofReal M₂ ≤ ENNReal.ofReal Mt := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have hTD : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        P {ω | acrossDist (S.D (h ω)) p35A12 < ENNReal.ofReal Mt⁻¹} ≤ ENNReal.ofReal ϑ ∧
        P {ω | ENNReal.ofReal Mt < aroundDist (S.D (h ω)) p35A23} ≤ ENNReal.ofReal ϑ := by
    intro Ω _ P _ h hh
    refine ⟨(measure_mono fun ω hω => lt_of_lt_of_le hω hinv1).trans (hT₁ P h hh).1.1,
      (measure_mono fun ω hω => lt_of_le_of_lt hle2 hω).trans (hT₂ P h hh).1.2⟩
  have hTY : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δT → ∀ L : ℝ, Real.log δ⁻¹ ≤ L →
          P {ω | acrossDist (Core.locMetricY S δ L hδ (h ω)) p35A12 < ENNReal.ofReal Mt⁻¹} ≤
              ENNReal.ofReal ϑ ∧
          P {ω | ENNReal.ofReal Mt < aroundDist (Core.locMetricY S δ L hδ (h ω)) p35A23} ≤
              ENNReal.ofReal ϑ := by
    intro Ω _ P _ h hh δ hδ hδδ L hL
    refine ⟨(measure_mono fun ω hω => lt_of_lt_of_le hω hinv1).trans
        ((hT₁ P h hh).2 δ hδ (lt_of_lt_of_le hδδ (min_le_left _ _)) L hL).1,
      (measure_mono fun ω hω => lt_of_le_of_lt hle2 hω).trans
        ((hT₂ P h hh).2 δ hδ (lt_of_lt_of_le hδδ (min_le_right _ _)) L hL).2⟩
  -- (2.6) with `ζ = 1/2`
  obtain ⟨Cκ, hCκ, εκ, hεκ, hκb⟩ := hK (1 / 2) (by norm_num) (by norm_num)
  have hCκpos : 0 < Cκ := lt_trans zero_lt_one hCκ
  -- constants
  set Cev : ℝ := max Mt 1 with hCev_def
  have hCev : 0 < Cev := lt_max_of_lt_right one_pos
  have hMtC : Mt ≤ Cev := le_max_left _ _
  set Cf : ℝ := max (p35Const Cev Cκ) (32400 * c₀ * Real.exp a) with hCf_def
  refine ⟨p35Theta Cev, Cf, 1 / 256, p35Theta_pos hCev,
    lt_max_of_lt_left (p35Const_pos hCev hCκpos), by norm_num, ?_⟩
  intro η hη hη0
  set δ₀ : ℝ := min (min (4 * η * δT) (4 * η * Real.exp (-2))) (min εκ ((η / 25) ^ 2))
    with hδ₀_def
  have hδ₀ : 0 < δ₀ := lt_min (lt_min (by positivity) (by positivity)) (lt_min hεκ (by positivity))
  refine ⟨δ₀, 2 * η, hδ₀, by positivity, ?_⟩
  intro δ hδ L hδδ₀ hL hδL Ω _ P _ h hh
  -- facts about `η` and `δ`
  have hη1 : η < 1 := lt_trans hη0 (by norm_num)
  have hsq : Real.sqrt η < 1 / 16 := p35_sqrt_lt (by norm_num) (by linarith)
  have hsmall : Real.sqrt η + η / 20 ≤ 1 / 4 := by linarith
  have hδ1 : δ < 4 * η * δT := lt_of_lt_of_le hδδ₀ ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ < 4 * η * Real.exp (-2) :=
    lt_of_lt_of_le hδδ₀ ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3 : δ ≤ εκ := (lt_of_lt_of_le hδδ₀ ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδ4 : δ ≤ (η / 25) ^ 2 :=
    (lt_of_lt_of_le hδδ₀ ((min_le_right _ _).trans (min_le_right _ _))).le
  have he2 : Real.exp (-2) < Real.exp (-1) := Real.exp_lt_exp.2 (by norm_num)
  have hδe : δ < Real.exp (-1) := by
    have : 4 * η * Real.exp (-2) < Real.exp (-2) := by
      have := Real.exp_pos (-2)
      nlinarith
    linarith
  have h1δ : 1 < Real.log δ⁻¹ := by
    rw [Real.lt_log_iff_exp_lt (inv_pos.2 hδ.1)]
    rw [lt_inv_comm₀ (Real.exp_pos 1) hδ.1, ← Real.exp_neg]
    exact hδe
  set qp : ℝ := Field.uniformLocalizationExponent δ L with hqp_def
  have hrad : plRad qp δ = δ * L := Field.plRad_uniform_eq δ L h1δ hL
  have hloc : 2 * plRad qp δ < 4 * η * 1 := by rw [hrad]; linarith
  have hNpos : 1 ≤ p35ScaleCount η := p35_count_pos hη hη0
  -- scale facts
  have hscale : ∀ k, 1 ≤ k → k ≤ p35ScaleCount η →
      4 * η ≤ 1 * p35Scale η k ∧ 1 * p35Scale η k ≤ 1 := by
    intro k hk1 hkN
    have h1 := p35Scale_ge hη hkN
    have h2 := p35Scale_le hη hη1 hk1
    constructor <;> nlinarith [Real.sqrt_nonneg η]
  set F := p35Event35 S.ξ S.Q S.D S.m qp h 0 (one_pos : (0 : ℝ) < 1) δ hδ hη Cev K with hF_def
  refine ⟨F, ?_, ?_, ?_⟩
  · -- locality modulo constants in `A_{1/2,3}(0)`
    refine p35_aeEventIn_fieldSigma0On h (annulus 0 (1 / 2) 3) ⟨(7 / 4 : ℂ), ?_⟩ fun X => ?_
    · change 1 / 2 < ‖(7 / 4 : ℂ) - 0‖ ∧ ‖(7 / 4 : ℂ) - 0‖ < 3
      rw [sub_zero]
      have : ‖(7 / 4 : ℂ)‖ = 7 / 4 := by
        rw [show (7 / 4 : ℂ) = ((7 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by norm_num)]
      rw [this]
      norm_num
    · have := p35_event35_aeEventIn S.ξ S.Q S.D S.m qp h 0 (one_pos : (0 : ℝ) < 1) δ hδ hη Cev
        P hh hDw hKn hη1 hsmall hloc X
      simpa only [mul_one] using this
  · -- probability
    have hFm : MeasurableSet F := p35_event35_measurable S.ξ S.Q S.D S.m qp h 0
      (one_pos : (0 : ℝ) < 1) δ hδ hη Cev S.hD.1 hh.1.measurable K
    have hCq : 0 ≤ Cf * η ^ q := by
      have : 0 ≤ Cf := le_trans (p35Const_pos hCev hCκpos).le (le_max_left _ _)
      positivity
    refine p35_prob_ge_of_compl_le hFm (by linarith) ?_
    rw [show 1 - (1 - Cf * η ^ q) = Cf * η ^ q by ring]
    -- one lattice point
    have hterm : ∀ c ∈ p35Lattice K (η / 20),
        P {ω | (countOcc (p35AnnEvent S.ξ S.Q S.D S.m qp h 0 (one_pos : (0 : ℝ) < 1) δ hδ hη Cev c)
          (p35ScaleCount η) ω : ℝ) < 1 / 2 * p35ScaleCount η} ≤
          ENNReal.ofReal (c₀ * Real.exp (-a * p35ScaleCount η)) := by
      intro c _
      refine p35_countOcc_lt_prob S.ξ S.Q S.D S.m qp h 0 (one_pos : (0 : ℝ) < 1) δ hδ hη Cev P hh
        hDw hp1 (fun w R E hR hanti hratio hE hpE N => hconc P h hh.1 w R E hR hanti hratio hE hpE N)
        c ?_ hloc
      intro k hk1 hkN
      obtain ⟨hs4, hs1⟩ := hscale k hk1 hkN
      obtain ⟨hδs, hδsT, h1s, hLs⟩ := p35_ratio_facts hη hδ.1 hs4 hs1 hδ1 hδ2
      refine p35_prob_ge_of_compl_le
        (hh.1.measurable (B2.Polylog.measurableSet_plEventLoc (S.ξ : ℝ) S.hD.1 _ S.m qp _ δ hδ _ Cev))
        hp1.le ?_
      refine (p35_canEvent_compl_le S hS hD hMt hTD hTY P h hh _
        ⟨1 * p35Scale η k, mul_pos one_pos (p35Scale_pos hη k)⟩ δ L hδ hδs hδsT h1δ hL h1s
        (hLs.trans hL) hMtC).trans (le_of_eq ?_)
      rw [hϑ_def, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    have hcompl : Fᶜ = ⋃ c ∈ p35Lattice K (η / 20),
        {ω | (countOcc (p35AnnEvent S.ξ S.Q S.D S.m qp h 0 (one_pos : (0 : ℝ) < 1) δ hδ hη Cev c)
          (p35ScaleCount η) ω : ℝ) < 1 / 2 * p35ScaleCount η} := by
      ext ω
      simp only [hF_def, p35Event35, mem_compl_iff, mem_iInter, mem_iUnion, mem_ofPred_eq, not_forall,
        not_le, exists_prop]
    rw [hcompl]
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [p35_sum_ofReal_const]
    apply ENNReal.ofReal_le_ofReal
    have hcard := p35_card_lattice_le K (a := η / 20) (by positivity) (by linarith)
    have hexp := p35_exp_count_le hη hq
    have hpow : η ^ (q + 2) = η ^ q * η ^ 2 := by
      rw [Real.rpow_add hη, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hηq : 0 ≤ η ^ q := Real.rpow_nonneg hη.le q
    have hexpa : 0 < Real.exp a := Real.exp_pos a
    calc ((p35Lattice K (η / 20)).card : ℝ) * (c₀ * Real.exp (-a * p35ScaleCount η))
        ≤ (81 / (η / 20) ^ 2) * (c₀ * (Real.exp a * η ^ (q + 2))) := by
          apply mul_le_mul hcard _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hexp hc₀.le
      _ = 32400 * c₀ * Real.exp a * η ^ q := by
          rw [hpow]
          field_simp
          ring
      _ ≤ Cf * η ^ q := mul_le_mul_of_nonneg_right (le_max_right _ _) hηq
  · -- the deterministic conclusion
    refine Filter.Eventually.of_forall fun ω hω => ?_
    -- both directions at every point of `K`
    have hmain : ∀ k ∈ K,
        (∀ (Pc : ℝ → ℂ) (α β : ℝ),
          P35GeodesicThrough (S.D (h ω)) Pc α β k (2 * Real.sqrt η * 1) →
          P35SeparatingCurve (Core.locMetricY S δ L hδ (h ω)) k (η * 1) (2 * Real.sqrt η * 1)
            (ENNReal.ofReal (Cf * η ^ p35Theta Cev) * (S.D (h ω)).len Pc α β)) ∧
        (∀ (Pc : ℝ → ℂ) (α β : ℝ),
          P35GeodesicThrough (Core.locMetricY S δ L hδ (h ω)) Pc α β k (2 * Real.sqrt η * 1) →
          P35SeparatingCurve (S.D (h ω)) k (η * 1) (2 * Real.sqrt η * 1)
            (ENNReal.ofReal (Cf * η ^ p35Theta Cev) *
              (Core.locMetricY S δ L hδ (h ω)).len Pc α β)) := by
      intro k hk
      set c := p35LatticePt (η / 20) k with hc_def
      have hcΛ : c ∈ p35Lattice K (η / 20) :=
        p35_latticePt_mem (fun k hk => (hKn k hk).2.trans (by norm_num)) (by positivity) hk
      have hck : dist k c ≤ η / 20 := p35_dist_latticePt_le (by positivity) k
      have hωc : (1 / 2 : ℝ) * p35ScaleCount η ≤
          (countOcc (p35AnnEvent S.ξ S.Q S.D S.m qp h 0 (one_pos : (0 : ℝ) < 1) δ hδ hη Cev c)
            (p35ScaleCount η) ω : ℝ) := by
        have := hω
        simp only [hF_def, p35Event35, mem_iInter, mem_ofPred_eq] at this
        exact this c hcΛ
      classical
      set G : Finset ℕ := (Finset.Icc 1 (p35ScaleCount η)).filter
        (fun j => ω ∈ p35AnnEvent S.ξ S.Q S.D S.m qp h 0 (one_pos : (0 : ℝ) < 1) δ hδ hη Cev c j)
        with hG_def
      have hGcount : (G.card : ℝ) = (countOcc (p35AnnEvent S.ξ S.Q S.D S.m qp h 0
          (one_pos : (0 : ℝ) < 1) δ hδ hη Cev c) (p35ScaleCount η) ω : ℝ) := by
        unfold countOcc
        rw [hG_def]
      have hGsub : G ⊆ Finset.Icc 1 (p35ScaleCount η) := Finset.filter_subset _ _
      have hGcard : (p35ScaleCount η : ℝ) / 2 ≤ G.card := by rw [hGcount]; linarith
      have hG0 : 0 < G.card := by
        have h1 : (1 : ℝ) ≤ p35ScaleCount η := by exact_mod_cast hNpos
        have h2 : (0 : ℝ) < G.card := by linarith
        exact_mod_cast h2
      have hgood : ∀ j ∈ G, h ω ∈ plEventLoc (S.ξ : ℝ) S.D (Compare.powScale S.ξ S.Q) S.m qp
          (0 + ((1 : ℝ) : ℂ) * c) δ hδ ⟨1 * p35Scale η j, mul_pos one_pos (p35Scale_pos hη j)⟩ Cev := by
        intro j hj
        have hj' := Finset.mem_filter.1 hj
        have hjr := Finset.mem_Icc.1 hj'.1
        have hmem := hj'.2
        unfold p35AnnEvent at hmem
        simp only [hjr.1, hjr.2, and_self, ↓reduceIte] at hmem
        exact hmem
      have hκ : ∀ j ∈ G,
          Compare.kappa S.ξ S.Q S.m ⟨δ, hδ.1⟩ ⟨1 * p35Scale η j, mul_pos one_pos (p35Scale_pos hη j)⟩ ≤
              Cκ * Compare.kappa S.ξ S.Q S.m ⟨δ, hδ.1⟩ ⟨1, (one_pos : (0 : ℝ) < 1)⟩ ∧
            (Compare.kappa S.ξ S.Q S.m ⟨δ, hδ.1⟩ ⟨1 * p35Scale η j,
              mul_pos one_pos (p35Scale_pos hη j)⟩)⁻¹ ≤
              Cκ * (Compare.kappa S.ξ S.Q S.m ⟨δ, hδ.1⟩ ⟨1, (one_pos : (0 : ℝ) < 1)⟩)⁻¹ := by
        intro j hj
        have hjr := Finset.mem_Icc.1 (hGsub hj)
        obtain ⟨hs4, hs1⟩ := hscale j hjr.1 hjr.2
        have hroot : 100 * δ ^ (1 - 1 / 2 : ℝ) ≤ 1 * p35Scale η j := by
          have hsqrtδ : δ ^ (1 - 1 / 2 : ℝ) ≤ η / 25 := by
            rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
            calc Real.sqrt δ ≤ Real.sqrt ((η / 25) ^ 2) := Real.sqrt_le_sqrt hδ4
              _ = η / 25 := Real.sqrt_sq (by positivity)
          linarith
        obtain ⟨hlow, hupp⟩ := hκb ⟨δ, hδ.1⟩ ⟨1 * p35Scale η j, mul_pos one_pos (p35Scale_pos hη j)⟩
          hδ3 hroot hs1
        rw [p35_kappa_one, mul_one, inv_one, mul_one]
        refine ⟨hupp, ?_⟩
        have hpos := p35_kappa_pos' (S.ξ : ℝ) S.Q S.m ⟨δ, hδ.1⟩
          ⟨1 * p35Scale η j, mul_pos one_pos (p35Scale_pos hη j)⟩
        rw [inv_le_comm₀ hpos hCκpos]
        exact hlow
      obtain ⟨hdir1, hdir2⟩ := p35_separator_of_goodFinset S.ξ S.Q S.D S.m qp (h ω) 0
        (one_pos : (0 : ℝ) < 1) δ hδ hη hη1 hCev hCκpos c k hck G hGsub hGcard hG0 hgood hκ
      have hpt : (0 : ℂ) + ((1 : ℝ) : ℂ) * k = k := by simp
      rw [p35_kappa_one, hpt] at hdir1
      rw [p35_kappa_one, inv_one, hpt] at hdir2
      have hbound : ENNReal.ofReal (p35Const Cev Cκ * 1 * η ^ p35Theta Cev) ≤
          ENNReal.ofReal (Cf * η ^ p35Theta Cev) := by
        rw [mul_one]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hη.le _))
      exact ⟨fun Pc α β hg => (hdir1 Pc α β hg).mono (mul_le_mul_left hbound _),
        fun Pc α β hg => (hdir2 Pc α β hg).mono (mul_le_mul_left hbound _)⟩
    refine ⟨p35_surroundProp_of (by positivity) fun Pc α β k hk hg => (hmain k hk).1 Pc α β hg,
      p35_surroundProp_of (by positivity) fun Pc α β k hk hg => (hmain k hk).2 Pc α β hg⟩

end SupercriticalLFPPAS.Separating
