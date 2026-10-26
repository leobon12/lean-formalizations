import SupercriticalLFPPAS.Local.Lemma32Det
import SupercriticalLFPPAS.Inputs.EuclideanRegularity
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2GFFPlusCont
import SupercriticalLQGUniqueness.B2.PfeAxioms.BoundedShiftField
import SupercriticalLQGUniqueness.B2.Final.Assembly3
import SupercriticalLQGUniqueness.B2.Polylog.P2HeatAnnulusTight
import SupercriticalLQGUniqueness.B2.Strong.Annulus

/-!
# Lemma 3.2 (packet P32)

Paper `source/almost-sure-supercritical-lfpp.txt`, Lemma 3.2 (l. 246–278), first statement: for
each `M < ∞` and `η, ν > 0`, with probability tending to one as `δ → 0`, simultaneously for
`|u| = 1`, `|v| = 2`, (3.1) and (3.2) hold for `D` and `X_δ = 𝔞_δ⁻¹ D^δ_h`.

Proof (planning audit `planning/audits/SB1-sections-1-3.md` A12, step 7): for `ϑ > 0` choose `B` so
that both collar events fail with probability at most `ϑ` (positivity of `D`-crossings; tightness of
normalized LFPP crossings away from zero, `PLHeatAnnulusTight`, uniformly in `δ ≤ 1`). Lemma 3.1
for the field `h + f` (`IsLFPPLimit`, GFF plus a bounded continuous function) makes its event fail
with probability tending to zero. On the intersection, for small `δ`, the deterministic
`lemma32Event_of_collars` gives the event of Lemma 3.2. The failure event is contained in a union
of three null-measurable events and a null set, so its (outer) probability tends to zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC heatMollify ofCont addFun)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-- A heat version plus a fixed continuous function gives an a.e.-measurable normalized LFPP
metric. -/
theorem aemeasurable_lfppMetric_heat_add {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (a δ : Set.Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ)) (hX : IsHeatSmoothing P h δ X)
    (g : C(ℂ, ℝ)) :
    AEMeasurable (fun ω => B2.Median.lfppMetric ξ a (X ω + g)) P := by
  have hXm := B2.PfeAxioms.aemeasurable_heat_smoothing_version P h hh δ X hX
  have hG : Measurable (fun ω => B2.PfeWeyl.normalizedLFPPMetric ξ a (hXm.mk X ω + g)) :=
    B2.PfeAxioms.measurable_normalizedLFPPMetric_comp ξ a fun z =>
      ((continuous_eval_const z).measurable.comp hXm.measurable_mk).add_const (g z)
  refine ⟨_, hG, ?_⟩
  filter_upwards [hXm.ae_eq_mk] with ω hω
  rw [B2.Polylog.lfppMetric_eq_normalizedLFPPMetric, hω]

/-- Positive real numbers `θ` with `3θ ≤ ε`. -/
theorem exists_pos_three_mul_le {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ENNReal.ofReal (3 * θ) ≤ ε := by
  by_cases htop : ε = ⊤
  · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
  · refine ⟨ε.toReal / 3, by
      have := ENNReal.toReal_pos hε.ne' htop
      positivity, ?_⟩
    rw [show 3 * (ε.toReal / 3) = ε.toReal by ring, ENNReal.ofReal_toReal htop]

/-- **The LQG collar event has probability close to one for `B` large.** -/
theorem eventually_measure_collarD_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Dω : Ω → LSCMetric} (hDω : Measurable Dω) (ξ M : ℝ) (hξ : 0 < ξ)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P {ω | ¬ (ENNReal.ofReal (M + 2) ≤
        ENNReal.ofReal (Real.exp (ξ * n)) * acrossDist (Dω ω) collarIn ∧
      ENNReal.ofReal (M + 2) ≤
        ENNReal.ofReal (Real.exp (ξ * n)) * acrossDist (Dω ω) collarOut)} ≤ ENNReal.ofReal θ := by
  set A : ℕ → Set Ω := fun n => {ω | ¬ (ENNReal.ofReal (M + 2) ≤
      ENNReal.ofReal (Real.exp (ξ * n)) * acrossDist (Dω ω) collarIn ∧
    ENNReal.ofReal (M + 2) ≤
      ENNReal.ofReal (Real.exp (ξ * n)) * acrossDist (Dω ω) collarOut)} with hA
  have hAm : ∀ n, NullMeasurableSet (A n) P := by
    intro n
    have h1 := (Uniqueness.Toolkit.PathInfimum.measurable_acrossDist collarIn).comp hDω
    have h2 := (Uniqueness.Toolkit.PathInfimum.measurable_acrossDist collarOut).comp hDω
    refine (MeasurableSet.compl ?_).nullMeasurableSet
    exact (measurableSet_le measurable_const (measurable_const.mul h1)).inter
      (measurableSet_le measurable_const (measurable_const.mul h2))
  -- for each sample the event eventually holds
  have hev : ∀ ω, ∀ᶠ n in atTop, ω ∉ A n := by
    intro ω
    have hlarge : ∀ (c : ℝ≥0∞), 0 < c → ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * n)) * c := by
      intro c hc
      by_cases hct : c = ⊤
      · refine Eventually.of_forall fun n => ?_
        rw [hct, ENNReal.mul_top (by simpa using Real.exp_pos (ξ * n))]
        exact le_top
      · have hcr : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hct
        have htend : Tendsto (fun n : ℕ => Real.exp (ξ * n) * c.toReal) atTop atTop :=
          (Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop).const_mul_atTop hξ)).atTop_mul_const
            hcr
        filter_upwards [htend.eventually_ge_atTop (M + 2)] with n hn
        rw [← ENNReal.ofReal_toReal hct, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal hn
    filter_upwards [hlarge _ (B2.Strong.acrossDist_pos (Dω ω) collarIn),
      hlarge _ (B2.Strong.acrossDist_pos (Dω ω) collarOut)] with n h1 h2
    exact fun hn => hn ⟨h1, h2⟩
  have hlim := tendsto_measure_of_ae_eventually_not_mem (P := P) (l := atTop) hAm
    (Eventually.of_forall hev)
  have hθ' : (0 : ℝ≥0∞) < ENNReal.ofReal θ := ENNReal.ofReal_pos.2 hθ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (eventually_le_nhds hθ'))
  exact ⟨N, hN⟩

/-- **Lemma 3.2 for `X_δ`, with the parameters normalized** (`η ≤ 1/10`, `ν ≤ 1`, `M ≥ 0`). -/
theorem lemma_3_2_core (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (hDlim : IsLFPPLimit ξ m D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) {M η ν : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (hη1 : η ≤ 1 / 10) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    Tendsto (fun δ : Set.Ioi (0 : ℝ) =>
        P {ω | ¬ Lemma32Event (D (h ω)) (B2.Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) η ν M})
      (comap Subtype.val (𝓝 (0 : ℝ))) (𝓝 0) := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hhm : Measurable h := hh.1.measurable
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨θ, hθ, hθε⟩ := exists_pos_three_mul_le hε
  -- the LQG collar event
  obtain ⟨N₁, hN₁⟩ := eventually_measure_collarD_le P (hD.1.comp hhm) (ξ : ℝ) M hξ hθ
  -- the LFPP collar event, uniformly in `δ ≤ 1`
  have hT := B2.Polylog.plHeatAnnulusTight_of_inputs B2.Final.dg20Interfaces_proved.2.1
    B2.Final.dg20Interfaces_proved.1
  obtain ⟨Mi, hMi, hti⟩ := (hT ξ Q hQ m hm P h hh X hX collarIn).2 (θ / 2) (by positivity)
  obtain ⟨Mo, hMo, hto⟩ := (hT ξ Q hQ m hm P h hh X hX collarOut).2 (θ / 2) (by positivity)
  set c : ℝ := min Mi⁻¹ Mo⁻¹ with hc
  have hc0 : 0 < c := lt_min (inv_pos.2 hMi) (inv_pos.2 hMo)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (1 + Real.log ((M + 2) / c) / ξ)
  set n : ℕ := max N₁ N₂ with hn
  set B : ℝ := (n : ℝ) with hBdef
  have hB : 0 ≤ B := Nat.cast_nonneg n
  have hBlarge : M + 2 ≤ Real.exp ((ξ : ℝ) * (B - 1)) * c := by
    have h1 : ((N₂ : ℕ) : ℝ) ≤ B := by
      rw [hBdef]
      exact_mod_cast le_max_right N₁ N₂
    have h2 : Real.log ((M + 2) / c) < (ξ : ℝ) * (B - 1) := by
      have := (div_lt_iff₀' hξ).1 (by linarith : Real.log ((M + 2) / c) / ξ < B - 1)
      linarith
    have h3 : (M + 2) / c < Real.exp ((ξ : ℝ) * (B - 1)) := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < (M + 2) / c)]
      exact Real.exp_lt_exp.2 h2
    have := (div_lt_iff₀ hc0).1 h3
    linarith
  -- the collar function and the field `h + f`
  set f : C(ℂ, ℝ) := collarFn B with hf
  have hfb : ∀ z, |f z| ≤ 2 * B := collarFn_abs_le hB
  let hfield : Ω → DistC := fun ω => addFun (h ω) f
  have hfieldB : LQGMetric.IsGFFPlusBddCont hfield P :=
    B2.PfeAxioms.isGFFPlusBddCont_addFun_of_normalized P h hh (fun _ => f) measurable_const
      (fun _ => ⟨2 * B, hfb⟩)
  have hfieldC : LQGMetric.IsGFFPlusCont hfield P := by
    obtain ⟨h1, g, h2, -, h3⟩ := hfieldB
    exact ⟨h1, g, h2, h3⟩
  let Xf : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun ε ω =>
    X ε ω + LQGMetric.LFPP.mollCont ε ε.property.ne' f (2 * B) hfb
  have hXf : ∀ ε, IsHeatSmoothing P hfield ε (Xf ε) := fun ε =>
    B2.Median.isHeatSmoothing_addFun P h ε (X ε) (hX ε) f (2 * B) hfb
  -- Lemma 3.1 for `h + f`
  let G : Set.Ioi (0 : ℝ) → Ω → LSCMetric := fun ε ω =>
    B2.Median.lfppMetric (ξ : ℝ) (m ε) (Xf ε ω)
  have hconv : LSCTendstoInProbability P (fun ε ω => (G ε ω).toLSCFun.1)
      (fun ω => (D (hfield ω)).toLSCFun.1) := by
    have h0 := hDlim P hfield hfieldB Xf hXf
    have e : (fun ε ω => (G ε ω).toLSCFun.1) =
        (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (Xf ε ω)) := by
      funext ε ω
      exact B2.Median.lfppMetric_toLSCFun _ _ _
    rw [e]
    exact h0
  have hGm : ∀ ε, AEMeasurable (G ε) P := fun ε =>
    aemeasurable_lfppMetric_heat_add P h hh (ξ : ℝ) (m ε) ε (X ε) (hX ε) _
  have hDfm : AEMeasurable (fun ω => D (hfield ω)) P :=
    (hD.1.comp ((LQGMetric.measurable_addFun_left f).comp hhm)).aemeasurable
  have hL31 := nearCompare_tendsto_measure hGm hDfm hconv isCompact_endpointPairs (M + 1) hη
    (by positivity : (0 : ℝ) < ν / 4)
  -- the heat facts
  set β : ℝ := Real.log (1 + ν / (8 * (M + 1))) / ξ with hβdef
  have hβ : 0 < β := div_pos (Real.log_pos (by
    have : 0 < ν / (8 * (M + 1)) := by positivity
    linarith)) hξ
  have hβM : (Real.exp ((ξ : ℝ) * β) - 1) * M ≤ ν / 8 := by
    have he : Real.exp ((ξ : ℝ) * β) = 1 + ν / (8 * (M + 1)) := by
      rw [hβdef, mul_div_cancel₀ _ hξ.ne', Real.exp_log (by positivity)]
    rw [he, add_sub_cancel_left, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
      (by norm_num)]
    nlinarith
  have hheat := collar_heat_eventually hB hβ
  -- the almost sure facts
  have hae : ∀ᵐ ω ∂P, Continuous (Uniqueness.BiLipschitz.Barrier.forget (D (h ω))) ∧
      (D (hfield ω)).IsLengthSpace ∧ ∀ p, D (hfield ω) p = weylScale (ξ : ℝ) f (D (h ω)) p := by
    filter_upwards [Inputs.ae_strongLQGMetric_euclideanRegularity hD P h hh,
      hD.2.1 P hfield hfieldC,
      hD.2.2.2.1 P h (B2.PfeAxioms.isGFFPlusCont_of_normalized hh)] with ω h1 h2 h3
    refine ⟨h1.1, h2, fun p => ?_⟩
    rw [h3 f]
  -- assembling the bound
  have hδ1 : ∀ᶠ δ : Set.Ioi (0 : ℝ) in comap Subtype.val (𝓝 (0 : ℝ)), (δ : ℝ) ≤ 1 :=
    tendsto_comap.eventually (eventually_le_nhds one_pos)
  have hθ3 : (0 : ℝ≥0∞) < ENNReal.ofReal θ := ENNReal.ofReal_pos.2 hθ
  filter_upwards [hheat, hδ1, hL31.eventually (eventually_le_nhds hθ3)] with δ hδheat hδ1' hδL
  -- the events
  set E1 := {ω | ¬ (NearCompare (G δ ω) (D (hfield ω)) endpointPairs (M + 1) η (ν / 4) ∧
      NearCompare (D (hfield ω)) (G δ ω) endpointPairs (M + 1) η (ν / 4))} with hE1
  set E2 := {ω | ¬ (ENNReal.ofReal (M + 2) ≤
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * n)) * acrossDist (D (h ω)) collarIn ∧
    ENNReal.ofReal (M + 2) ≤
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * n)) * acrossDist (D (h ω)) collarOut)} with hE2
  set E3 := {ω | acrossDist (B2.Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) collarIn <
      ENNReal.ofReal Mi⁻¹} with hE3
  set E4 := {ω | acrossDist (B2.Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) collarOut <
      ENNReal.ofReal Mo⁻¹} with hE4
  set E0 := {ω | ¬ (Continuous (Uniqueness.BiLipschitz.Barrier.forget (D (h ω))) ∧
      (D (hfield ω)).IsLengthSpace ∧
        ∀ p, D (hfield ω) p = weylScale (ξ : ℝ) f (D (h ω)) p)} with hE0def
  have hE0 : P E0 = 0 := by
    rw [hE0def, ← ae_iff]
    exact hae
  have hsub : {ω | ¬ Lemma32Event (D (h ω)) (B2.Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) η ν M}
      ⊆ E1 ∪ E2 ∪ E3 ∪ E4 ∪ E0 := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h0⟩ := hnot
    simp only [hE1, hE2, hE3, hE4, hE0def, mem_ofPred_eq, not_not, not_lt] at h1 h2 h3 h4 h0
    obtain ⟨hforget, hDflen, hDf⟩ := h0
    apply hω
    refine lemma32Event_of_collars hξ (m δ) (φ := X δ ω)
      (g := LQGMetric.LFPP.mollCont δ δ.property.ne' f (2 * B) hfb) hB hη1 hν hν1 hM
      hforget hDf hDflen (fun z => collar_heat_nonneg hB δ z) (fun z hz => hδheat.1 z hz)
      (fun z hz1 hz2 => hδheat.2 z hz1 hz2) hβM h2 ⟨?_, ?_⟩ h1.1 h1.2
    · calc ENNReal.ofReal (M + 2)
          ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * (B - 1)) * Mi⁻¹) :=
            ENNReal.ofReal_le_ofReal (hBlarge.trans (mul_le_mul_of_nonneg_left (min_le_left _ _)
              (Real.exp_pos _).le))
        _ = ENNReal.ofReal (Real.exp ((ξ : ℝ) * (B - 1))) * ENNReal.ofReal Mi⁻¹ :=
            ENNReal.ofReal_mul (Real.exp_pos _).le
        _ ≤ _ := by gcongr
    · calc ENNReal.ofReal (M + 2)
          ≤ ENNReal.ofReal (Real.exp ((ξ : ℝ) * (B - 1)) * Mo⁻¹) :=
            ENNReal.ofReal_le_ofReal (hBlarge.trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
              (Real.exp_pos _).le))
        _ = ENNReal.ofReal (Real.exp ((ξ : ℝ) * (B - 1))) * ENNReal.ofReal Mo⁻¹ :=
            ENNReal.ofReal_mul (Real.exp_pos _).le
        _ ≤ _ := by gcongr
  have hP2 : P E2 ≤ ENNReal.ofReal θ := hN₁ n (le_max_left _ _)
  have hP3 : P E3 ≤ ENNReal.ofReal (θ / 2) := (hti δ hδ1').1
  have hP4 : P E4 ≤ ENNReal.ofReal (θ / 2) := (hto δ hδ1').1
  calc P {ω | ¬ Lemma32Event (D (h ω)) (B2.Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) η ν M}
      ≤ P (E1 ∪ E2 ∪ E3 ∪ E4 ∪ E0) := measure_mono hsub
    _ ≤ P E1 + P E2 + P E3 + P E4 + P E0 := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal θ + ENNReal.ofReal θ + ENNReal.ofReal (θ / 2) +
          ENNReal.ofReal (θ / 2) + 0 := by
        rw [hE0]
        gcongr
    _ = ENNReal.ofReal (3 * θ) := by
        rw [add_zero, ← ENNReal.ofReal_add hθ.le hθ.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ε := hθε

/-- **Lemma 3.2** (paper l. 246–252, first statement): for each `M < ∞` and `η, ν > 0`, with
probability tending to one as `δ → 0`, simultaneously for `|u| = 1`, `|v| = 2`,
`X_δ(B_η(u), B_η(v); U) ≤ D(u, v; V) + ν` if `D(u, v; V) ≤ M` (3.1) and
`D(B_η(u), B_η(v); U) ≤ X_δ(u, v; V) + ν` if `X_δ(u, v; V) ≤ M` (3.2). Here `D` is the LQG
metric identified as the LFPP limit (`IsLFPPLimit`) and `X δ` is any family of heat versions. -/
theorem lemma_3_2 (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (hDlim : IsLFPPLimit ξ m D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) (M η ν : ℝ) (hη : 0 < η) (hν : 0 < ν) :
    Tendsto (fun δ : Set.Ioi (0 : ℝ) =>
        P {ω | ¬ Lemma32Event (D (h ω)) (B2.Median.lfppMetric (ξ : ℝ) (m δ) (X δ ω)) η ν M})
      (comap Subtype.val (𝓝 (0 : ℝ))) (𝓝 0) := by
  have hcore := lemma_3_2_core ξ Q hQ D hD m hm hDlim P h hh X hX (M := max M 0)
    (η := min η (1 / 10)) (ν := min ν 1) (le_max_right _ _) (lt_min hη (by norm_num))
    (min_le_right _ _) (lt_min hν one_pos) (min_le_right _ _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcore (fun _ => zero_le)
    (fun δ => measure_mono ?_)
  intro ω hω hE
  exact hω (hE.mono (min_le_left _ _) (min_le_left _ _) (le_max_left _ _))

end SupercriticalLFPPAS.Local
