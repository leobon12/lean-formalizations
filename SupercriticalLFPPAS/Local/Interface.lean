import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Local.CircleLocalized
import SupercriticalLFPPAS.Local.Lemma32Loc
import SupercriticalLFPPAS.Local.Locality
import SupercriticalLFPPAS.Local.ExponentContinuity
import SupercriticalLFPPAS.Field.HeatVersion
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.LawTransport
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable

/-!
# Packet P32 in the interface forms of `Core/Interfaces.lean`

The five targets of `planning/packets/P32-targets.md`, for an arbitrary `S : Core.Setup`, with exactly
the interface hypotheses listed there:

* `lemma32Loc_of S (hM : Core.Lemma32MeasStmt S) (hU : Core.UnifLocStmt) : Core.Lemma32LocStmt S`
  (Lemma 3.2 for `Y_{δ,L}`, simultaneously for all `L ≥ log δ⁻¹`, threshold uniform over normalized
  fields: per field from `lemma_3_2`, (2.3) and `lemma32Event_transfer`; uniformity by the law
  transfer `prob_preimage_eq_of_normalized` of the universally measurable failure set);
* `lemma32Locality_holds S : Core.Lemma32LocalityStmt S` (`aeEventIn_lemma32EventU_loc`);
* `lemma32Meas_holds S : Core.Lemma32MeasStmt S` (A13: null-measurability of the ordinary event via
  a measurable continuous version of `h*_δ` on the canonical field space, and universal
  measurability of the localized failure set via joint measurability in `(g, L)`);
* `confinement_of S (hC : Core.LocCompareStmt S) (hA : Core.LocApproxStmt) : Core.ConfinementStmt S`
  (Lemma 2.2, `lemma_2_2_of_comparison`; `hA` is not needed, the landed (2.1) is used directly);
* `locCircle_of S hC hA : Core.LocCircleStmt S` ((2.9), `circle_localized_ratio_of_comparison`).

`Core.srcV`, `Core.tgtU`, `Core.OneWayCompare`, `Core.Lemma32Event`, `Core.Lemma32EventU` have the same
bodies as the `Local` ones, and `Core.locMetricY S δ L hδ` is the term `Local.locMetric (S.ξ : ℝ) S.m δ L hδ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC heatMollify)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-! ### Dictionary -/

theorem core_lemma32Event_iff (S T : LSCMetric) (η ν M : ℝ) :
    Core.Lemma32Event S T η ν M ↔ Lemma32Event S T η ν M := Iff.rfl

theorem core_lemma32EventU_iff (S T : LSCMetric) (η ν M t : ℝ) :
    Core.Lemma32EventU S T η ν M t ↔ Lemma32EventU S T η ν M t := Iff.rfl

theorem core_locMetricY_eq (S : Core.Setup) (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) (g : DistC) :
    Core.locMetricY S δ L hδ g = locMetric (S.ξ : ℝ) S.m δ L hδ g := rfl

theorem isLFPPLimit_of_setup (S : Core.Setup) : IsLFPPLimit S.ξ S.m S.D :=
  fun P _ h hh X hX => S.hlim S.m S.hm P h hh X hX

/-- (2.8) for one normalized field and `ζ = 1/2`, from the interface. -/
theorem comparison_of_locCompare (S : Core.Setup) (hC : Core.LocCompareStmt S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
      ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
        ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
          P {ω | ¬ B2.Polylog.compareHolds (B2.Polylog.plLocMetric (S.ξ : ℝ) 1 S.m ε hε (h ω))
            (S.D (h ω)) (ε ^ (1 - (1 / 2 : ℝ))) U C₀} ≤ ENNReal.ofReal (c₀ * ε ^ p₀) := by
  obtain ⟨C₀, hC₀, hU⟩ := hC (1 / 2) (by norm_num) (by norm_num)
  refine ⟨C₀, hC₀, fun U hU1 hU2 hU3 => ?_⟩
  obtain ⟨p₀, c₀, ε₀, h1, h2, h3, h4, h5⟩ := hU U hU1 hU2 hU3
  exact ⟨p₀, c₀, ε₀, h1, h2, h3, h4, fun ε hε hε₀ => h5 P h hh ε hε hε₀⟩

/-! ### Lemma 2.2 and (2.9) -/

/-- **Lemma 2.2** in the interface form `Core.ConfinementStmt`. -/
theorem confinement_of (S : Core.Setup) (hC : Core.LocCompareStmt S) (_hA : Core.LocApproxStmt) :
    Core.ConfinementStmt S := by
  intro Ω _ P _ h hh X hX K hK M η hη
  obtain ⟨R₀, hR₀⟩ := lemma_2_2_of_comparison S.ξ S.Q S.D S.hD S.m P h hh X hX
    (ζ := 1 / 2) (by norm_num) (comparison_of_locCompare S hC P h hh) K hK M η hη
  refine ⟨R₀, fun R hR => ?_⟩
  filter_upwards [hR₀ R hR] with ε hε hεI
  exact hε hεI

/-- **(2.9)** in the interface form `Core.LocCircleStmt`. -/
theorem locCircle_of (S : Core.Setup) (hC : Core.LocCompareStmt S) (_hA : Core.LocApproxStmt) :
    Core.LocCircleStmt S := by
  intro Ω _ P _ h hh q₁ q₂ r₁ r₂ hr₁ hr₂ hdisj θ hθ
  have h0 := circle_localized_ratio_of_comparison S.ξ S.Q S.hQ S.D S.hD S.m S.hm
    (isLFPPLimit_of_setup S) P h hh (ζ := 1 / 2) (by norm_num)
    (comparison_of_locCompare S hC P h hh) q₁ q₂ r₁ r₂ hr₁ hr₂ hdisj hθ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
    (fun ε => measure_mono ?_)
  rintro ω ⟨hε, hbad⟩
  refine ⟨hε, fun hgood => hbad ⟨hgood.2, ?_⟩⟩
  have h1 := hgood.1
  set Dd := B2.Iface.setDistance (S.D (h ω)).1 (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)
  set Xh := B2.Iface.setDistance (B2.Polylog.plLocMetric (S.ξ : ℝ) 1 S.m ε hε (h ω)).1
    (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)
  change Dd ≤ ENNReal.ofReal (Real.exp θ) * Xh
  calc Dd = ENNReal.ofReal (Real.exp θ) * (ENNReal.ofReal (Real.exp (-θ)) * Dd) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          add_neg_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp θ) * Xh := by gcongr

/-! ### The locality clause -/

/-- **Locality clause of Lemma 3.2** (Remark 3.3) in the interface form `Core.Lemma32LocalityStmt`. -/
theorem lemma32Locality_holds (S : Core.Setup) : Core.Lemma32LocalityStmt S := by
  intro M η ν _ _ δ hδ L hδ1 hL hδL Ω _ P _ h hh
  exact aeEventIn_lemma32EventU_loc S.ξ S.Q S.D S.hD S.m P h hh hδ hδ1 hL hδL η ν M

/-! ### Measurability -/

/-- The localized LFPP metric depends jointly measurably on the field and on `t`, with
`L = log δ⁻¹ + |t|`. -/
theorem measurable_locMetric_param (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (δ : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) :
    Measurable fun p : DistC × ℝ => locMetric ξ m δ (Real.log δ⁻¹ + |p.2|) hδ p.1 := by
  have hq : Continuous fun t : ℝ => Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |t|) := by
    unfold Field.uniformLocalizationExponent
    have hpos : ∀ t : ℝ, Real.log δ⁻¹ + |t| ≠ 0 := fun t =>
      (add_pos_of_pos_of_nonneg (B2.Polylog.log_inv_pos hδ) (abs_nonneg t)).ne'
    exact ((continuous_const.add continuous_abs).log hpos).div_const _
  have hcoord : ∀ z : ℂ, Measurable fun p : DistC × ℝ =>
      B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |p.2|)) δ hδ
        p.1 z := by
    intro z
    have hcont : ∀ g : DistC, Continuous fun t : ℝ =>
        B2.Polylog.plMollify (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |t|)) δ hδ g z := by
      intro g
      have h1 := (continuous_plMollify_exponent hδ g z).comp hq
      exact h1
    have hmeas : ∀ t : ℝ, Measurable fun g : DistC =>
        B2.Polylog.plMollify (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |t|)) δ hδ g z :=
      fun t => measurable_const.mul (LQGMetric.measurable_distOn_apply _)
    have h : Measurable (Function.uncurry fun (t : ℝ) (g : DistC) =>
        B2.Polylog.plMollify (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |t|)) δ hδ g z) :=
      measurable_uncurry_of_continuous_of_measurable hcont hmeas
    have h2 := h.comp measurable_swap
    have h' : Measurable fun p : DistC × ℝ =>
        B2.Polylog.plMollify (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |p.2|)) δ hδ
          p.1 z := h2
    have e : (fun p : DistC × ℝ =>
        B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |p.2|)) δ hδ
          p.1 z) = fun p : DistC × ℝ =>
        B2.Polylog.plMollify (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |p.2|)) δ hδ
          p.1 z := rfl
    rw [e]
    exact h'
  have h := B2.PfeAxioms.measurable_normalizedLFPPMetric_comp ξ (m ⟨δ, hδ.1⟩)
    (X := fun p : DistC × ℝ =>
      B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |p.2|)) δ hδ p.1)
    hcoord
  have e : (fun p : DistC × ℝ => locMetric ξ m δ (Real.log δ⁻¹ + |p.2|) hδ p.1) =
      fun p : DistC × ℝ => B2.PfeWeyl.normalizedLFPPMetric ξ (m ⟨δ, hδ.1⟩)
        (B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ (Real.log δ⁻¹ + |p.2|)) δ hδ
          p.1) :=
    funext fun p => B2.Polylog.lfppMetric_eq_normalizedLFPPMetric _ _ _
  rw [e]
  exact h

/-- **Measurability clause of Lemma 3.2** (Remark 3.3, SB1 A13) in the interface form
`Core.Lemma32MeasStmt`. -/
theorem lemma32Meas_holds (S : Core.Setup) : Core.Lemma32MeasStmt S := by
  intro M η ν
  refine ⟨@fun Ω _ P _ h hh X hX δ => ?_, fun δ hδ => ?_⟩
  · -- the ordinary event, for an arbitrary heat version
    have hhm : Measurable h := hh.1.measurable
    set μ : Measure DistC := P.map h
    have hμgff : LQGMetric.IsWholePlaneGFF id μ := LQGMetric.GM.isWholePlaneGFF_id_map hh.1
    have hcont : ∀ᵐ g ∂μ, Continuous (heatMollify (δ : ℝ) g) :=
      (hμgff.ae_tendstoLocallyUniformly_heatMollify (δ : ℝ) δ.property.ne').mono fun _ hg => hg.2
    obtain ⟨Φ, hΦm, hΦeq⟩ := B2.PfeAxioms.exists_measurable_continuous_real_version μ
      (fun g => heatMollify (δ : ℝ) g)
      (measurable_pi_iff.2 fun z => LQGMetric.measurable_heatMollify_left (δ : ℝ) z) hcont
    have hΦP : ∀ᵐ ω ∂P, (Φ (h ω) : ℂ → ℝ) = heatMollify (δ : ℝ) (h ω) :=
      ae_of_ae_map hhm.aemeasurable hΦeq
    have hXΦ : ∀ᵐ ω ∂P, X δ ω = Φ (h ω) := by
      filter_upwards [hΦP, B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh δ (X δ) (hX δ)]
        with ω h1 h2
      ext z
      rw [h2 z, h1]
    have hYm : Measurable fun g => B2.Median.lfppMetric (S.ξ : ℝ) (S.m δ) (Φ g) := by
      have h := B2.PfeAxioms.measurable_normalizedLFPPMetric_comp (S.ξ : ℝ) (S.m δ) (X := Φ)
        fun z => (continuous_eval_const z).measurable.comp hΦm
      convert h using 2 with g
      exact B2.Polylog.lfppMetric_eq_normalizedLFPPMetric _ _ _
    have hUM := umeasurableSet_lemma32EventU S.hD.1 hYm (τ := fun _ => (1 : ℝ)) measurable_const
      η ν M
    have hB := LQGMetric.UMeasurableSet.nullMeasurableSet_preimage (P := P) hUM hhm.aemeasurable
    refine hB.congr ?_
    filter_upwards [hXΦ] with ω hω
    change Lemma32EventU (S.D (h ω)) (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δ) (Φ (h ω))) η ν M 1 =
      Core.Lemma32Event (S.D (h ω)) (Core.lfppM S δ (X δ ω)) η ν M
    rw [hω]
    exact propext (lemma32EventU_one _ _ η ν M)
  · -- the localized failure set, for all `L ≥ log δ⁻¹` at once
    set ℓ : ℝ := Real.log δ⁻¹
    set Y : DistC × ℝ → LSCMetric := fun p => locMetric (S.ξ : ℝ) S.m δ (ℓ + |p.2|) hδ p.1
      with hYdef
    have hYm : Measurable Y := measurable_locMetric_param (S.ξ : ℝ) S.m δ hδ
    have hDm : Measurable fun p : DistC × ℝ => S.D p.1 := S.hD.1.comp measurable_fst
    have hR1 := measurableSet_oneWayAt hDm hYm (ν := fun _ => ν) (M := fun _ => M)
      measurable_const measurable_const η
    have hR2 := measurableSet_oneWayAt hYm hDm (ν := fun _ => ν) (M := fun _ => M)
      measurable_const measurable_const η
    set R : Set ((DistC × ℝ) × (ℂ × ℂ)) :=
      {q | OneWayAt (S.D q.1.1) (Y q.1) η ν M q.2.1 q.2.2}ᶜ ∪
        {q | OneWayAt (Y q.1) (S.D q.1.1) η ν M q.2.1 q.2.2}ᶜ with hRdef
    have hRm : MeasurableSet R := hR1.compl.union hR2.compl
    set R' : Set (DistC × (ℝ × (ℂ × ℂ))) := MeasurableEquiv.prodAssoc.symm ⁻¹' R
    have hR'm : MeasurableSet R' := MeasurableEquiv.prodAssoc.symm.measurable hRm
    have hUM := LQGMetric.UMeasurableSet.setOf_exists hR'm
    convert hUM using 1
    ext g
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨L, hL, hbad⟩
      have hbad' : ¬ Lemma32Event (S.D g) (locMetric (S.ξ : ℝ) S.m δ L hδ g) η ν M := hbad
      rw [Lemma32Event, oneWayCompare_iff_forall, oneWayCompare_iff_forall, not_and_or] at hbad'
      have hLeq : ℓ + |L - ℓ| = L := by
        rw [abs_of_nonneg (by linarith)]
        ring
      rcases hbad' with hb | hb
      · push Not at hb
        obtain ⟨p, hp⟩ := hb
        refine ⟨(L - ℓ, p), ?_⟩
        show ((g, L - ℓ), p) ∈ R
        left
        simp only [mem_compl_iff, mem_ofPred_eq, hYdef, hLeq]
        exact hp
      · push Not at hb
        obtain ⟨p, hp⟩ := hb
        refine ⟨(L - ℓ, p), ?_⟩
        show ((g, L - ℓ), p) ∈ R
        right
        simp only [mem_compl_iff, mem_ofPred_eq, hYdef, hLeq]
        exact hp
    · rintro ⟨⟨t, p⟩, hgp⟩
      change ((g, t), p) ∈ R at hgp
      refine ⟨ℓ + |t|, le_add_of_nonneg_right (abs_nonneg t), ?_⟩
      show ¬ Lemma32Event (S.D g) (locMetric (S.ξ : ℝ) S.m δ (ℓ + |t|) hδ g) η ν M
      rw [Lemma32Event, oneWayCompare_iff_forall, oneWayCompare_iff_forall, not_and_or]
      rcases hgp with hb | hb
      · left
        exact fun hall => hb (hall p)
      · right
        exact fun hall => hb (hall p)

/-! ### Lemma 3.2 for `Y_{δ,L}`, simultaneously in `L` -/

/-- **Lemma 3.2 for `Y_{δ,L}` for one field, simultaneously for all `L ≥ log δ⁻¹`**, from (2.3) in
the form `Core.UnifLocStmt`. -/
theorem lemma_3_2_loc_simul (S : Core.Setup) (hU : Core.UnifLocStmt)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (M η ν : ℝ) (hη : 0 < η) (hν : 0 < ν) :
    ∀ ϑ : ℝ, 0 < ϑ → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δ₀ →
      P {ω | ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧
        ¬ Lemma32Event (S.D (h ω)) (locMetric (S.ξ : ℝ) S.m δ L hδ (h ω)) η ν M} ≤
          ENNReal.ofReal ϑ := by
  intro ϑ hϑ
  have hξ : (0 : ℝ) < S.ξ := S.ξ.2
  -- normalized parameters
  set η' : ℝ := min η (1 / 10)
  set ν' : ℝ := min ν 1
  set M' : ℝ := max M 0
  have hη' : 0 < η' := lt_min hη (by norm_num)
  have hν' : 0 < ν' := lt_min hν one_pos
  have hν'1 : ν' ≤ 1 := min_le_right _ _
  have hM' : 0 ≤ M' := le_max_right _ _
  -- the closeness threshold
  set σ : ℝ := Real.log (1 + ν' / (4 * (M' + 1))) / S.ξ with hσdef
  have hσ : 0 < σ := div_pos (Real.log_pos (by
    have : 0 < ν' / (4 * (M' + 1)) := by positivity
    linarith)) hξ
  have he : Real.exp (|(S.ξ : ℝ)| * σ) = 1 + ν' / (4 * (M' + 1)) := by
    rw [abs_of_pos hξ, hσdef, mul_div_cancel₀ _ hξ.ne', Real.exp_log (by positivity)]
  have hσ2 : Real.exp (|(S.ξ : ℝ)| * σ) ≤ 2 := by
    rw [he]
    have : ν' / (4 * (M' + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hσν : (Real.exp (|(S.ξ : ℝ)| * σ) - 1) * (M' + 1) ≤ ν' / 4 := by
    rw [he, add_sub_cancel_left, div_mul_eq_mul_div, mul_comm 4 (M' + 1), ← div_div,
      mul_div_cancel_right₀ _ (by positivity : M' + 1 ≠ 0)]
  -- a jointly continuous heat version
  obtain ⟨X, hX, hXc⟩ := Field.exists_jointHeatVersion_core P h hh
  -- Lemma 3.2 for `X_δ`, error `ν'/2`, height `2M'`
  have hL32 := lemma_3_2 S.ξ S.Q S.hQ S.D S.hD S.m S.hm (isLFPPLimit_of_setup S) P h hh X hX
    (2 * M') η' (ν' / 2) hη' (by positivity)
  obtain ⟨r₁, hr₁, hr₁P⟩ := exists_pos_of_eventually_comap
    (hL32.eventually (eventually_le_nhds (ENNReal.ofReal_pos.2 (half_pos hϑ))))
  -- (2.3)
  have hUL := hU P h hh X ⟨hX, hXc⟩ (closedBall (0 : ℂ) 17) (isCompact_closedBall _ _) σ hσ
  obtain ⟨δ₁, hδ₁P, hδ₁pos⟩ := ((hUL.eventually (eventually_le_nhds
    (ENNReal.ofReal_pos.2 (half_pos hϑ)))).and self_mem_nhdsWithin).exists
  refine ⟨min r₁ δ₁, lt_min hr₁ hδ₁pos, fun δ hδ hδ₀ => ?_⟩
  set δ' : Set.Ioi (0 : ℝ) := ⟨δ, hδ.1⟩
  have hP1 := hr₁P δ' (lt_of_lt_of_le hδ₀ (min_le_left _ _))
  set A : Set Ω := {ω | ∃ (δ'' : ℝ) (hδ'' : δ'' ∈ Ioo (0 : ℝ) 1), δ'' < δ₁ ∧ ∃ L : ℝ,
    Real.log δ''⁻¹ ≤ L ∧ ∃ z ∈ closedBall (0 : ℂ) 17,
      σ < |Core.locFieldC δ'' L hδ'' (h ω) z - X ⟨δ'', hδ''.1⟩ ω z|}
  have hsub : {ω | ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧
      ¬ Lemma32Event (S.D (h ω)) (locMetric (S.ξ : ℝ) S.m δ L hδ (h ω)) η ν M} ⊆
      {ω | ¬ Lemma32Event (S.D (h ω)) (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δ') (X δ' ω)) η'
        (ν' / 2) (2 * M')} ∪ A := by
    rintro ω ⟨L, hL, hbad⟩
    by_contra hnot
    simp only [mem_union, not_or, mem_ofPred_eq, not_not] at hnot
    obtain ⟨hE, hAω⟩ := hnot
    apply hbad
    have hclose : ∀ z ∈ nbhdU, |B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ
        (h ω) z - X δ' ω z| ≤ σ := by
      intro z hz
      by_contra hcon
      apply hAω
      refine ⟨δ, hδ, lt_of_lt_of_le hδ₀ (min_le_right _ _), L, hL, z, ?_, not_le.1 hcon⟩
      rw [mem_closedBall, dist_zero_right]
      exact hz.2.le
    have hT := lemma32Event_transfer (ξ := (S.ξ : ℝ)) (S.m δ') (φ := X δ' ω)
      (ψ := B2.Polylog.plMollifyC (Field.uniformLocalizationExponent δ L) δ hδ (h ω))
      hν' hν'1 hM' hσ.le hσ2 hσν hclose hE
    exact hT.mono (min_le_left _ _) (min_le_left _ _) (le_max_left _ _)
  calc _ ≤ P ({ω | ¬ Lemma32Event (S.D (h ω)) (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δ') (X δ' ω))
        η' (ν' / 2) (2 * M')} ∪ A) := measure_mono hsub
    _ ≤ P {ω | ¬ Lemma32Event (S.D (h ω)) (B2.Median.lfppMetric (S.ξ : ℝ) (S.m δ') (X δ' ω))
        η' (ν' / 2) (2 * M')} + P A := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ϑ / 2) + ENNReal.ofReal (ϑ / 2) := add_le_add hP1 hδ₁P
    _ = ENNReal.ofReal ϑ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- **Lemma 3.2 for `Y_{δ,L}`** in the interface form `Core.Lemma32LocStmt`: simultaneously for all
`L ≥ log δ⁻¹`, with the threshold uniform over normalized fields. -/
theorem lemma32Loc_of (S : Core.Setup) (hM : Core.Lemma32MeasStmt S) (hU : Core.UnifLocStmt) :
    Core.Lemma32LocStmt S := by
  intro M η ν hη hν ϑ hϑ
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, h₀, hh₀⟩ := exists_normalizedGFF
  obtain ⟨δ₀, hδ₀, hb⟩ := lemma_3_2_loc_simul S hU P₀ h₀ hh₀ M η ν hη hν ϑ hϑ
  refine ⟨δ₀, hδ₀, fun δ hδ hδδ₀ Ω _ P _ h hh => ?_⟩
  have hUM := (hM M η ν).2 δ hδ
  have heq := Uniqueness.TwoScale.S36.prob_preimage_eq_of_normalized P P₀ hh hh₀ hUM
  calc P {ω | ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧
        ¬ Core.Lemma32Event (S.D (h ω)) (Core.locMetricY S δ L hδ (h ω)) η ν M}
      = P (h ⁻¹' {g | ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧
        ¬ Core.Lemma32Event (S.D g) (Core.locMetricY S δ L hδ g) η ν M}) := rfl
    _ = P₀ (h₀ ⁻¹' {g | ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧
        ¬ Core.Lemma32Event (S.D g) (Core.locMetricY S δ L hδ g) η ν M}) := heq
    _ ≤ ENNReal.ofReal ϑ := hb δ hδ hδδ₀

end SupercriticalLFPPAS.Local
