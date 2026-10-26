import SupercriticalLFPPAS.Separating.Lemma35Final
import SupercriticalLFPPAS.Separating.EventAB
import LQGMetric.Papers.CONF.S3D114S4

/-!
# The good root event at the unit scale: `Core.UnitGoodStmt`

Packet P35, final target `unitGood_of` (`planning/packets/P35-targets.md`; ruling P8): §3.3 at the
unit scale (SB2 D4 items 1–2, M4), from Lemma 3.2 (localized, uniform in `L`; `Core.Lemma32LocStmt`
and its locality `Core.Lemma32LocalityStmt`), Lemma 3.5 (`Core.Lemma35Stmt`) and annular tightness
(`Core.AnnTightStmt`).

The event is the intersection of four events, each failing with probability at most `(1 - p₀)/6`
(tightness: `D` and `Y_{δ,L}`, across `Ā_{1,2}` and around `A_{7,8}`, as the field-local event
`p35EventAB` in canonical units `e^{ξ h_1(0)}`; Lemma 3.2 with endpoint radius `η/2`, cutoff `M`
and error `ν = d₀ m/40`; Lemma 3.5 with `K = ∂B₁ ∪ ∂B₂`, `q = 1`); constants in the order of SB2 D4:
`p₀ → M → A = M² → d₀ → η → ν`, with `m = 1/M`. Its deterministic consequences are the three
clauses of `Core.GoodScale` at `(0, 1)` with `K = 1`, in both directions:

* `ratio`: `d(around A_{7,8}) ≤ M ≤ M² · M⁻¹ ≤ A · acrossIn(d; 0, 1, 2)`;
* `cross`: `d(u,v; V) ≤ d(around A_{7,8}) ≤ M`, so Lemma 3.2 gives
  `d'(B_{η/2}(u), B_{η/2}(v); U) ≤ d(u,v; V) + ν`, and `d(u,v; V) ≥ acrossIn(d; 0,1,2) ≥ m` (every
  curve in `V` from `∂B₁` to `∂B₂` crosses `Ā_{1,2}`) turns `ν` into `(d₀/40) d(u,v; V)`;
* `surround`: Lemma 3.5 with `Cη^θ ≤ d₀/10`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn plEventLoc plLocMetric annAround annAt plRad
  closedAnn acrossIn_le_len_of_crossing)
open LQGMetric (DistC DistOn addConst restrictTo circleAvg TestC)
open LQGMetric.Blueprint (AEEventIn fieldSigma fieldSigma0On countOcc annulus)

/-! ### Small lemmas -/

theorem p35_aeEventIn0_inter {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    (V : Set ℂ) {A B : Set Ω} (hA : AEEventIn P (fieldSigma0On h V) A)
    (hB : AEEventIn P (fieldSigma0On h V) B) : AEEventIn P (fieldSigma0On h V) (A ∩ B) := by
  obtain ⟨F, hF, hAF⟩ := hA
  obtain ⟨G, hG, hBG⟩ := hB
  exact ⟨F ∩ G, hF.inter hG, hAF.inter hBG⟩

theorem p35_aeEventIn0_mono {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    {V W : Set ℂ} (hVW : V ⊆ W) {A : Set Ω} (hA : AEEventIn P (fieldSigma0On h V) A) :
    AEEventIn P (fieldSigma0On h W) A := by
  obtain ⟨F, hF, hAF⟩ := hA
  exact ⟨F, LQGMetric.CONF.conf36_fieldSigma0On_mono h hVW F hF, hAF⟩

/-- The mean-zero field σ-algebra of an open set is contained in the ambient σ-algebra. -/
theorem p35_fieldSigma0On_le {Ω : Type} [mΩ : MeasurableSpace Ω] {h : Ω → DistC}
    (hhm : Measurable h) (U : TopologicalSpace.Opens ℂ) : fieldSigma0On h U ≤ mΩ := by
  refine (LQGMetric.CONF.fieldSigma0On_le_fieldSigma h U.2).trans ?_
  exact ((LQGMetric.measurable_restrictTo _).comp hhm).comap_le

/-- Internal metrics on equal sets agree at the same points. -/
theorem p35_internal_congr_set (d : LSCMetric) {Y Y' : Set ℂ} (hY : Y = Y') (p : Y × Y) :
    d.internal Y p = d.internal Y' (⟨p.1.1, hY ▸ p.1.2⟩, ⟨p.2.1, hY ▸ p.2.2⟩) := by
  subst hY
  rfl

/-- Internal set distances on equal sets agree for the same balls. -/
theorem p35_internalSetDist_congr_set (d : LSCMetric) {Y Y' : Set ℂ} (hY : Y = Y') (u v : ℂ)
    (ρ : ℝ) :
    d.internalSetDist Y {x | (x : ℂ) ∈ ball u ρ} {x | (x : ℂ) ∈ ball v ρ} =
      d.internalSetDist Y' {x | (x : ℂ) ∈ ball u ρ} {x | (x : ℂ) ∈ ball v ρ} := by
  subst hY
  rfl

/-- **Internal distances between the two circles pay the local across cost.** For a bounded set
`Y` and `|u| = 1`, `|v| = 2`, every curve in `Y` from `u` to `v` contains a crossing of `Ā_{1,2}(0)`. -/
theorem p35_acrossIn_le_internal (d : LSCMetric) {Y : Set ℂ} (hYb : Bornology.IsBounded Y)
    (u v : Y) (hu : ‖(u : ℂ)‖ = 1) (hv : ‖(v : ℂ)‖ = 2) :
    acrossIn d 0 1 (2 * 1) ≤ d.internal Y (u, v) := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPY => le_iInf fun hPa => le_iInf fun hPb => ?_
  have hPc : ContinuousOn P (Icc a b) :=
    Uniqueness.Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded d P hP
      (hYb.subset (by rintro _ ⟨t, ht, rfl⟩; exact hPY t ht))
  exact acrossIn_le_len_of_crossing d 0 one_pos hP hPc (by rw [hPa, sub_zero, hu])
    (by rw [hPb, sub_zero, hv]; norm_num)

theorem p35_surroundProp_mono {d d' : LSCMetric} {Kp : Set ℂ} {r η b b' : ℝ} (hbb : b ≤ b')
    (h : Core.SurroundProp d d' Kp r η b) : Core.SurroundProp d d' Kp r η b' := by
  intro P α β hgeo hPc p hp hpP hα hβ
  obtain ⟨σ, a, b₁, h1, h2, h3, h4, h5, h6, h7⟩ := h P α β hgeo hPc p hp hpP hα hβ
  exact ⟨σ, a, b₁, h1, h2, h3, h4, h5, h6, h7.trans (mul_le_mul_left
    (ENNReal.ofReal_le_ofReal hbb) _)⟩

/-- At the unit root of a field with `g_1(0) = 0` both normalizations are `1`. -/
theorem p35_norms_unit (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : Set.Ioi (0 : ℝ)) {g : DistC} (hg : circleAvg g 1 0 = 0) :
    B2.Polylog.normD (ξ : ℝ) (Compare.powScale ξ Q) g 0 ⟨1, (one_pos : (0 : ℝ) < 1)⟩ = 1 ∧
    B2.Polylog.normL (ξ : ℝ) m ε g 0 ⟨1, (one_pos : (0 : ℝ) < 1)⟩ = 1 := by
  have hsf : B2.Polylog.lfppScaleFactor m ε ⟨1, (one_pos : (0 : ℝ) < 1)⟩ = 1 := by
    unfold B2.Polylog.lfppScaleFactor
    have harg : (⟨(ε : ℝ) / (1 : ℝ), Set.mem_Ioi.mpr (div_pos ε.2 one_pos)⟩ : Set.Ioi (0 : ℝ)) =
        ε := Subtype.ext (div_one _)
    simp only [harg, one_mul]
    exact div_self (ne_of_gt (m ε).2)
  constructor
  · unfold B2.Polylog.normD
    simp only [Compare.powScale, Real.one_rpow, inv_one, one_mul, hg, mul_zero, neg_zero,
      Real.exp_zero, ENNReal.ofReal_one]
  · unfold B2.Polylog.normL
    rw [hsf]
    simp only [inv_one, one_mul, hg, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one]

theorem p35_srcV_eq : closedAnn (0 : ℂ) (1 / 2) (3 * 1) = Core.srcV := by
  ext w
  simp only [closedAnn, Core.srcV, mem_ofPred_eq, sub_zero, mul_one]

theorem p35_tgtU_eq : closedAnn (0 : ℂ) (1 / 8) (16 * 1) = Core.tgtU := by
  ext w
  simp only [closedAnn, Core.tgtU, mem_ofPred_eq, sub_zero, mul_one]

theorem p35_srcV_bounded : Bornology.IsBounded Core.srcV :=
  (isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset fun w hw => by
    rw [mem_closedBall, dist_zero_right]
    exact hw.2

/-- `1 - ofReal (1 - x) ≤ ofReal x`. -/
theorem p35_one_sub_ofReal_le {x : ℝ} (hx : 0 ≤ x) :
    1 - ENNReal.ofReal (1 - x) ≤ ENNReal.ofReal x := by
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [ENNReal.ofReal_sub 1 hx, ENNReal.ofReal_one,
      ENNReal.sub_sub_cancel ENNReal.one_ne_top (by simpa using hx1)]
  · rw [ENNReal.ofReal_of_nonpos (by linarith), tsub_zero]
    exact le_of_lt (by simpa using hx1)

/-- **The cross clause from Lemma 3.2.** If `d(u,v; V) ≤ M`, `d(u,v; V) ≥ M⁻¹` and Lemma 3.2 holds
with error `ν = d₀/(40 M)`, the target distance between the `η/2`-balls is at most
`(1 + d₀/10) d(u,v; V)`. -/
theorem p35_cross_bound {I T : ℝ≥0∞} {M d₀ : ℝ} (hM : 0 < M) (hd₀ : 0 < d₀)
    (hIlow : ENNReal.ofReal M⁻¹ ≤ I) (hT : T ≤ I + ENNReal.ofReal (d₀ / (40 * M))) :
    T ≤ ENNReal.ofReal ((1 + d₀ / 10) * 1) * I := by
  refine hT.trans ?_
  have hν : ENNReal.ofReal (d₀ / (40 * M)) ≤ ENNReal.ofReal (d₀ / 10) * I := by
    calc ENNReal.ofReal (d₀ / (40 * M)) = ENNReal.ofReal (d₀ / 40) * ENNReal.ofReal M⁻¹ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (d₀ / 40) * I := mul_le_mul_right hIlow _
      _ ≤ ENNReal.ofReal (d₀ / 10) * I :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
  calc I + ENNReal.ofReal (d₀ / (40 * M)) ≤ I + ENNReal.ofReal (d₀ / 10) * I := add_le_add le_rfl hν
    _ = ENNReal.ofReal ((1 + d₀ / 10) * 1) * I := by
        rw [mul_one, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, add_mul,
          one_mul]

/-- **The good scale at the unit root from the four events** (deterministic). -/
theorem p35_goodScale_of_events (d d' : LSCMetric) {η d₀ M : ℝ} (hM1 : 1 ≤ M) (hd₀ : 0 < d₀)
    (hacr : ENNReal.ofReal M⁻¹ ≤ acrossIn d 0 1 (2 * 1))
    (haro : aroundDist d (annAt 0 (7 * 1) (8 * 1) (by norm_num) (by norm_num)) ≤ ENNReal.ofReal M)
    (h32 : Core.OneWayCompare d d' (η * 1 / 2) (d₀ / (40 * M)) M)
    (hsur : Core.SurroundProp d d' (sphere (0 : ℂ) 1 ∪ sphere 0 (2 * 1)) 1 η (d₀ / 10 * 1)) :
    Core.GoodScale d d' 0 1 one_pos η d₀ (M ^ 2) 1 := by
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  refine ⟨?_, ?_, hsur⟩
  · -- ratio
    calc aroundDist d (annAt 0 (7 * 1) (8 * 1) _ _) ≤ ENNReal.ofReal M := haro
      _ = ENNReal.ofReal (M ^ 2) * ENNReal.ofReal M⁻¹ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (M ^ 2) * acrossIn d 0 1 (2 * 1) := mul_le_mul_right hacr _
  · -- cross
    intro u v hu hv hle
    set u' : Core.srcV := ⟨u.1, p35_srcV_eq ▸ u.2⟩
    set v' : Core.srcV := ⟨v.1, p35_srcV_eq ▸ v.2⟩
    have hI : d.internal (closedAnn 0 (1 / 2) (3 * 1)) (u, v) = d.internal Core.srcV (u', v') :=
      p35_internal_congr_set d p35_srcV_eq (u, v)
    have hu' : ‖(u' : ℂ)‖ = 1 := by
      have := hu
      rwa [dist_zero_right] at this
    have hv' : ‖(v' : ℂ)‖ = 2 := by
      have := hv
      rw [dist_zero_right] at this
      simpa using this
    rw [hI] at hle ⊢
    rw [p35_internalSetDist_congr_set d' p35_tgtU_eq]
    have hleM : d.internal Core.srcV (u', v') ≤ ENNReal.ofReal M := hle.trans haro
    have hlow : ENNReal.ofReal M⁻¹ ≤ d.internal Core.srcV (u', v') :=
      hacr.trans (p35_acrossIn_le_internal d p35_srcV_bounded u' v' hu' hv')
    exact p35_cross_bound hMpos hd₀ hlow (h32 u' v' hu' hv' hleM)

/-- For a normalized field, `h_1(0) = 0` almost surely. -/
theorem p35_ae_circleAvg_one_zero {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, circleAvg (h ω) 1 0 = 0 := by
  filter_upwards [hh.2] with ω hω
  have := Uniqueness.Toolkit.AnnulusIteration.circleAvg_eq_of_isCircleAverage (h ω) _ 0 0 hω
  exact this

/-! ### The assembly -/

/-- **§3.3 at the unit scale (SB2 D4 items 1–2), interface form.** For every `p₀ < 1` there is
`A ≥ 1` (so `λ = 1/(5A)` is fixed before `d₀`) such that for every `d₀ > 0` there is `η > 0` with
`2√η < 1/10` and thresholds `δ₀, ℓ₀` such that for `δ < δ₀`, `L ≥ log δ⁻¹`, `δL < ℓ₀` and every
normalized whole-plane GFF there is an event, almost surely an event of `h|_{A_{1/16,32}(0)}`
modulo additive constants, of probability at least `p₀`, on which (a.s.) `(D, Y_{δ,L})` and
`(Y_{δ,L}, D)` are good scales at `(0, 1)` with `K = 1`. -/
theorem unitGood_of (S : Core.Setup) (h32 : Core.Lemma32LocStmt S)
    (hloc : Core.Lemma32LocalityStmt S) (h35 : Core.Lemma35Stmt S) (hT : Core.AnnTightStmt S) :
    Core.UnitGoodStmt S := by
  intro p₀ hp₀
  have hDw : B2.Iface.IsPfeWeakMetric S.ξ S.D (Compare.powScale S.ξ S.Q) :=
    Compare.isPfeWeakMetric_of_isStrongLQGMetric S.hD
  set ϑ : ℝ := (1 - p₀) / 6 with hϑ_def
  have hϑ : 0 < ϑ := by rw [hϑ_def]; linarith
  -- annular tightness at `Ā_{1,2}(0)` (across) and `A_{7,8}(0)` (around)
  set A12 : EuclideanAnnulus := annAt 0 1 (2 * 1) one_pos (by norm_num) with hA12
  set A78 : EuclideanAnnulus := p35AnnAB 0 ⟨1, (one_pos : (0 : ℝ) < 1)⟩ 7 8 (by norm_num)
    (by norm_num) with hA78
  obtain ⟨Ma, δa, hMa, hδa, hTa⟩ := hT A12 ϑ hϑ
  obtain ⟨Mb, δb, hMb, hδb, hTb⟩ := hT A78 ϑ hϑ
  set M : ℝ := max (max Ma Mb) 1 with hM_def
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMaM : Ma ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMbM : Mb ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨M ^ 2, by nlinarith, ?_⟩
  intro d₀ hd₀
  -- Lemma 3.5 for `K = ∂B₁ ∪ ∂B₂`, `q = 1`
  set K35 : Set ℂ := sphere (0 : ℂ) 1 ∪ sphere 0 (2 * 1) with hK35
  have hK35c : IsCompact K35 := (isCompact_sphere _ _).union (isCompact_sphere _ _)
  have hK35s : K35 ⊆ (annulus 0 (3 / 4) (5 / 2) : Set ℂ) := by
    intro x hx
    change 3 / 4 < ‖x - 0‖ ∧ ‖x - 0‖ < 5 / 2
    rw [sub_zero]
    rcases hx with hx | hx
    · rw [mem_sphere, dist_zero_right] at hx
      rw [hx]
      norm_num
    · rw [mem_sphere, dist_zero_right] at hx
      rw [hx]
      norm_num
  obtain ⟨θ, C, η₀, hθ, hC, hη₀, h35η⟩ := h35 K35 hK35c hK35s 1 one_pos
  -- the choice of `η`
  set η : ℝ := min (min (η₀ / 2) (ϑ / (2 * C))) (min ((d₀ / (10 * C)) ^ (1 / θ)) (1 / 800))
    with hη_def
  have hd₀C : 0 < d₀ / (10 * C) := by positivity
  have hη : 0 < η := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (Real.rpow_pos_of_pos hd₀C _) (by norm_num))
  have hηη₀ : η < η₀ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hCη : C * η ≤ ϑ := by
    have h1 : η ≤ ϑ / (2 * C) := (min_le_left _ _).trans (min_le_right _ _)
    calc C * η ≤ C * (ϑ / (2 * C)) := mul_le_mul_of_nonneg_left h1 hC.le
      _ = ϑ / 2 := by field_simp
      _ ≤ ϑ := by linarith
  have hCηθ : C * η ^ θ ≤ d₀ / 10 * 1 := by
    have h1 : η ≤ (d₀ / (10 * C)) ^ (1 / θ) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : η ^ θ ≤ ((d₀ / (10 * C)) ^ (1 / θ)) ^ θ :=
      Real.rpow_le_rpow hη.le h1 hθ.le
    rw [← Real.rpow_mul hd₀C.le, one_div_mul_cancel hθ.ne', Real.rpow_one] at h2
    calc C * η ^ θ ≤ C * (d₀ / (10 * C)) := mul_le_mul_of_nonneg_left h2 hC.le
      _ = d₀ / 10 * 1 := by field_simp
  have hη800 : η ≤ 1 / 800 := (min_le_right _ _).trans (min_le_right _ _)
  have hsqrt : 2 * Real.sqrt η < 1 / 10 := by
    have : Real.sqrt η < 1 / 20 := p35_sqrt_lt (by norm_num) (by linarith)
    linarith
  refine ⟨η, hη, hsqrt, ?_⟩
  -- thresholds
  obtain ⟨δ35, ℓ35, hδ35, hℓ35, h35δ⟩ := h35η η hη hηη₀
  set ν : ℝ := d₀ / (40 * M) with hν_def
  have hν : 0 < ν := by positivity
  obtain ⟨δ32, hδ32, h32δ⟩ := h32 M (η * 1 / 2) ν (by positivity) hν ϑ hϑ
  set δ₀ : ℝ := min (min δ35 δ32) (min (min δa δb) (Real.exp (-2))) with hδ₀_def
  set ℓ₀ : ℝ := min ℓ35 (1 / 16) with hℓ₀_def
  refine ⟨δ₀, ℓ₀, lt_min (lt_min hδ35 hδ32) (lt_min (lt_min hδa hδb) (Real.exp_pos _)),
    lt_min hℓ35 (by norm_num), ?_⟩
  intro δ hδ L hδδ₀ hL hδL Ω _ P _ h hh
  have hδ35' : δ < δ35 := lt_of_lt_of_le hδδ₀ ((min_le_left _ _).trans (min_le_left _ _))
  have hδ32' : δ < δ32 := lt_of_lt_of_le hδδ₀ ((min_le_left _ _).trans (min_le_right _ _))
  have hδa' : δ < δa :=
    lt_of_lt_of_le hδδ₀ ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδb' : δ < δb :=
    lt_of_lt_of_le hδδ₀ ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδe : δ < Real.exp (-2) :=
    lt_of_lt_of_le hδδ₀ ((min_le_right _ _).trans (min_le_right _ _))
  have hℓ35' : δ * L < ℓ35 := lt_of_lt_of_le hδL (min_le_left _ _)
  have hℓ16 : δ * L < 1 / 16 := lt_of_lt_of_le hδL (min_le_right _ _)
  have h1δ : 1 < Real.log δ⁻¹ := by
    rw [Real.lt_log_iff_exp_lt (inv_pos.2 hδ.1), lt_inv_comm₀ (Real.exp_pos 1) hδ.1,
      ← Real.exp_neg]
    exact lt_trans hδe (Real.exp_lt_exp.2 (by norm_num))
  set qp : ℝ := Field.uniformLocalizationExponent δ L with hqp_def
  have hrad : plRad qp δ = δ * L := Field.plRad_uniform_eq δ L h1δ hL
  -- the normalization `h_1(0) = 0`
  have hnorm : ∀ᵐ ω ∂P, circleAvg (h ω) 1 0 = 0 := p35_ae_circleAvg_one_zero hh
  -- the four events
  set U16 : TopologicalSpace.Opens ℂ := annulus 0 (1 / 16) 32 with hU16
  set T : Set Ω := {ω | h ω ∈ p35EventAB (S.ξ : ℝ) S.D (Compare.powScale S.ξ S.Q) S.m qp 0 δ hδ
    ⟨1, (one_pos : (0 : ℝ) < 1)⟩ 7 8 (by norm_num) (by norm_num) M} with hT_def
  set E32 : Set Ω := {ω | Core.Lemma32EventU (S.D (h ω)) (Core.locMetricY S δ L hδ (h ω))
    (η * 1 / 2) ν M (Real.exp ((S.ξ : ℝ) * circleAvg (h ω) 1 0))} with hE32_def
  obtain ⟨F, hFloc, hFprob, hFsur⟩ := h35δ δ hδ L hδ35' hL hℓ35' P h hh
  -- locality
  have hTloc : AEEventIn P (fieldSigma0On h U16) T := by
    refine p35_aeEventIn_fieldSigma0On h U16 ⟨(1 : ℂ), ?_⟩ fun X => ?_
    · change 1 / 16 < ‖(1 : ℂ) - 0‖ ∧ ‖(1 : ℂ) - 0‖ < 32
      rw [sub_zero, norm_one]
      norm_num
    · refine p35_eventAB_aeEventIn P h hh hDw S.m qp 0 δ hδ _ 7 8 _ _ (by norm_num) M U16 ?_ ?_ X
      · intro w hw
        obtain ⟨hw1, hw2⟩ := hw
        change 1 / 16 < ‖w - 0‖ ∧ ‖w - 0‖ < 32
        change (1 : ℝ) / 2 < ‖w - 0‖ at hw1
        change ‖w - 0‖ < (8 + 1) * (1 : ℝ) at hw2
        constructor <;> linarith
      · show 2 * plRad qp δ < 1
        rw [hrad]
        linarith
  have hEloc : AEEventIn P (fieldSigma0On h U16) E32 :=
    hloc M (η * 1 / 2) ν (by positivity) (by nlinarith [Real.sqrt_nonneg η]) δ hδ L h1δ hL hℓ16
      P h hh
  have hFloc' : AEEventIn P (fieldSigma0On h U16) F := by
    refine p35_aeEventIn0_mono h ?_ hFloc
    intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    exact ⟨by linarith, by linarith⟩
  obtain ⟨T', hT'm, hTT'⟩ := hTloc
  obtain ⟨E', hE'm, hEE'⟩ := hEloc
  obtain ⟨F', hF'm, hFF'⟩ := hFloc'
  have hhm := hh.1.measurable
  have hle := p35_fieldSigma0On_le hhm U16
  refine ⟨T' ∩ E' ∩ F', ⟨T' ∩ E' ∩ F', (hT'm.inter hE'm).inter hF'm, Filter.EventuallyEq.rfl⟩,
    ?_, ?_⟩
  · -- probability
    have hGm : MeasurableSet (T' ∩ E' ∩ F') := hle _ ((hT'm.inter hE'm).inter hF'm)
    refine p35_prob_ge_of_compl_le hGm (by linarith) ?_
    -- the tightness event
    have hTc : P Tᶜ ≤ 4 * ENNReal.ofReal ϑ := by
      set B₁ := {ω | acrossDist (S.D (h ω)) A12 < ENNReal.ofReal Ma⁻¹}
      set B₂ := {ω | ENNReal.ofReal Mb < aroundDist (S.D (h ω)) A78}
      set B₃ := {ω | acrossDist (Core.locMetricY S δ L hδ (h ω)) A12 < ENNReal.ofReal Ma⁻¹}
      set B₄ := {ω | ENNReal.ofReal Mb < aroundDist (Core.locMetricY S δ L hδ (h ω)) A78}
      have hinv : ENNReal.ofReal M⁻¹ ≤ ENNReal.ofReal Ma⁻¹ :=
        ENNReal.ofReal_le_ofReal (inv_anti₀ hMa hMaM)
      have hle' : ENNReal.ofReal Mb ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal hMbM
      have hsub : Tᶜ ≤ᵐ[P] B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
        filter_upwards [hnorm] with ω hω hnot
        by_contra hbad
        simp only [mem_union, not_or] at hbad
        obtain ⟨⟨⟨h1', h2'⟩, h3'⟩, h4'⟩ := hbad
        simp only [B₁, B₂, B₃, B₄, mem_ofPred_eq, not_lt] at h1' h2' h3' h4'
        apply hnot
        obtain ⟨hnD, hnL⟩ := p35_norms_unit S.ξ S.Q S.m ⟨δ, hδ.1⟩ hω
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hnD, one_mul]
          exact hinv.trans (h1'.trans (B2.Polylog.acrossDist_le_acrossIn _ _ _ _))
        · rw [hnD, one_mul]
          exact h2'.trans hle'
        · rw [hnL, one_mul]
          exact hinv.trans (h3'.trans (B2.Polylog.acrossDist_le_acrossIn _ _ _ _))
        · rw [hnL, one_mul]
          exact h4'.trans hle'
      calc P Tᶜ ≤ P (B₁ ∪ B₂ ∪ B₃ ∪ B₄) := measure_mono_ae hsub
        _ ≤ P B₁ + P B₂ + P B₃ + P B₄ := by
            refine (measure_union_le _ _).trans ?_
            gcongr
            refine (measure_union_le _ _).trans ?_
            gcongr
            exact measure_union_le _ _
        _ ≤ ENNReal.ofReal ϑ + ENNReal.ofReal ϑ + ENNReal.ofReal ϑ + ENNReal.ofReal ϑ := by
            gcongr
            · exact (hTa P h hh).1.1
            · exact (hTb P h hh).1.2
            · exact ((hTa P h hh).2 δ hδ hδa' L hL).1
            · exact ((hTb P h hh).2 δ hδ hδb' L hL).2
        _ = 4 * ENNReal.ofReal ϑ := by ring
    -- the Lemma 3.2 event
    have hEc : P E32ᶜ ≤ ENNReal.ofReal ϑ := by
      refine le_trans (measure_mono_ae ?_) (h32δ δ hδ hδ32' P h hh)
      filter_upwards [hnorm] with ω hω hnot
      refine ⟨L, hL, fun hev => hnot ?_⟩
      show Core.Lemma32EventU (S.D (h ω)) (Core.locMetricY S δ L hδ (h ω)) (η * 1 / 2) ν M
        (Real.exp ((S.ξ : ℝ) * circleAvg (h ω) 1 0))
      rw [hω, mul_zero, Real.exp_zero]
      unfold Core.Lemma32EventU
      rw [mul_one ν, mul_one M]
      exact hev
    -- the Lemma 3.5 event
    have hFc : P F'ᶜ ≤ ENNReal.ofReal ϑ := by
      have hF'meas : MeasurableSet F' := hle _ hF'm
      have hPF : P F' = P F := (measure_congr hFF').symm
      have h1 : P F'ᶜ = 1 - P F := by rw [prob_compl_eq_one_sub hF'meas, hPF]
      have hpow : C * η ^ (1 : ℝ) = C * η := by rw [Real.rpow_one]
      rw [hpow] at hFprob
      calc P F'ᶜ = 1 - P F := h1
        _ ≤ 1 - ENNReal.ofReal (1 - C * η) := tsub_le_tsub_left hFprob 1
        _ ≤ ENNReal.ofReal (C * η) := p35_one_sub_ofReal_le (by positivity)
        _ ≤ ENNReal.ofReal ϑ := ENNReal.ofReal_le_ofReal hCη
    have hcompl : (T' ∩ E' ∩ F')ᶜ = T'ᶜ ∪ E'ᶜ ∪ F'ᶜ := by
      ext ω
      simp only [mem_compl_iff, mem_inter_iff, mem_union, not_and_or]
    rw [hcompl]
    calc P (T'ᶜ ∪ E'ᶜ ∪ F'ᶜ) ≤ P T'ᶜ + P E'ᶜ + P F'ᶜ := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ = P Tᶜ + P E32ᶜ + P F'ᶜ := by
          rw [measure_congr hTT'.compl, measure_congr hEE'.compl]
      _ ≤ 4 * ENNReal.ofReal ϑ + ENNReal.ofReal ϑ + ENNReal.ofReal ϑ := by gcongr
      _ = ENNReal.ofReal (1 - p₀) := by
          rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) hϑ.le, ← ENNReal.ofReal_add (by positivity) hϑ.le]
          congr 1
          rw [hϑ_def]
          ring
  · -- the deterministic consequences
    filter_upwards [hnorm, hTT', hEE', hFF', hFsur] with ω hω hTω hEω hFω hsurω hG
    obtain ⟨⟨hωT', hωE'⟩, hωF'⟩ := hG
    have hωT : ω ∈ T := by
      have := hTω
      simp only [eq_iff_iff] at this
      exact this.2 hωT'
    have hωE : ω ∈ E32 := by
      have := hEω
      simp only [eq_iff_iff] at this
      exact this.2 hωE'
    have hωF : ω ∈ F := by
      have := hFω
      simp only [eq_iff_iff] at this
      exact this.2 hωF'
    obtain ⟨hs1, hs2⟩ := hsurω hωF
    obtain ⟨hnD, hnL⟩ := p35_norms_unit S.ξ S.Q S.m ⟨δ, hδ.1⟩ hω
    obtain ⟨t1, t2, t3, t4⟩ := hωT
    rw [hnD, one_mul] at t1 t2
    rw [hnL, one_mul] at t3 t4
    have hev : Core.Lemma32Event (S.D (h ω)) (Core.locMetricY S δ L hδ (h ω)) (η * 1 / 2) ν M := by
      have h' : Core.Lemma32EventU (S.D (h ω)) (Core.locMetricY S δ L hδ (h ω)) (η * 1 / 2) ν M
          (Real.exp ((S.ξ : ℝ) * circleAvg (h ω) 1 0)) := hωE
      rw [hω, mul_zero, Real.exp_zero] at h'
      unfold Core.Lemma32EventU at h'
      rwa [mul_one ν, mul_one M] at h'
    refine ⟨p35_goodScale_of_events _ _ hM1 hd₀ t1 t2 hev.1 (p35_surroundProp_mono hCηθ hs1),
      p35_goodScale_of_events _ _ hM1 hd₀ t3 t4 hev.2 (p35_surroundProp_mono hCηθ hs2)⟩

end SupercriticalLFPPAS.Separating
