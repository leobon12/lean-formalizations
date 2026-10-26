import SupercriticalLFPPAS.GoodRoot.Affine
import SupercriticalLFPPAS.Concentration.AnnulusConcentration
import SupercriticalLQGUniqueness.B2.Strong.Bridge
import LQGMetric.Papers.CONF.S3L35B5
import LQGMetric.Papers.CONF.S3D114S4

/-!
# The good root events `E_{ε,r}(z)` at centre `z` and radius `r` (§3.3)

Packet REP (`planning/packets/REP.md`): `rootEvent_of` proves `Core.RootEventStmt S` from
`Core.UnitGoodStmt S` (§3.3 at the unit scale), `Core.ScalingDStmt S` ((1.3)) and
`Core.DilationStmt S` ((2.4)). Paper §3.3, l. 386–394 ("At center z and physical radius r, define the
event E_{ε,r}(z) …"); SB2 §2.3 items 6–8, D4 item 3 and M5.

Construction. For `(ε, r)` in the regime `δ := ε/r ∈ (0, 1)`, `L := log ε⁻¹`, `1 < log ε⁻¹`,
`1 < log δ⁻¹ ≤ L` (i.e. `r ≤ 1`), `δ < δ₀`, `δL < ℓ₀` (the thresholds of `UnitGoodStmt`), the unit
statement applied to the normalized field `h^{z,r} = h(z + r·) − h_r(z)` (first conjunct of (1.3))
gives an event `G`; `E_{ε,r}(z)` is a measurable representative of `G`, and `∅` outside the regime.
* σ-algebra transfer (`rep_sigma_transfer`): a zero-mean test function supported in `A_{1/16,32}(0)`
  pushed forward by `u ↦ z + r u` is zero-mean and supported in `A_{r/16,32r}(z)`, and the additive
  constant of `h^{z,r}` is invisible to it, so `σ(h^{z,r}|_{A_{1/16,32}(0)} mod const)` is contained in
  the closed-annulus σ-algebra of `h − h_r(z)` on `Ā_{r/16,32r}(z)` modulo constants (D3's
  `Concentration.modConstSigma_addRandomConstant` removes the recentring);
* physical units (`rep_goodScale_affine`, `GoodRoot/Affine.lean`): a.s. `D_h(z + r·, z + r·) =
  r^{ξQ} e^{ξ h_r(z)} D_{h^{z,r}}` ((1.3)) and deterministically `X̂_ε[h](z + r·, z + r·) =
  (r 𝔞_{ε/r}/𝔞_ε) e^{ξ h_r(z)} Y_{ε/r, log ε⁻¹}[h^{z,r}]` ((2.4) (i), (iii)); the ratio of the two
  factors is `κ_ε(r)` (`rep_factor_ratio`);
* the band `ε^t ≤ r ≤ ε^s`, `t < 1`, lies in the regime for small `ε`, uniformly in the field
  (`rep_band_regime`, SB2 §2.3 item 8).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLFPPAS.GoodRoot

open SupercriticalLQGUniqueness
open LQGMetric (DistC addConst circleAvg)
open LQGMetric.Blueprint (AEEventIn fieldSigma0On fieldSigmaClosed0 annulus)

/-! ### σ-algebra transfer -/

/-- Zero-mean pairings of the affine pullback `h(r · + z)` against test functions supported in `V`
are zero-mean pairings of `h` against test functions supported in `{y | (y − z)/r ∈ V}`. -/
theorem rep_fieldSigma0On_affineComp_le {Ω : Type} (h : Ω → DistC) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (V : Set ℂ) :
    fieldSigma0On (fun ω => LQGMetric.affineComp r z (h ω)) V ≤
      fieldSigma0On h {y | (y - z) / r ∈ V} := by
  let _ : MeasurableSpace Ω := fieldSigma0On h {y | (y - z) / r ∈ V}
  apply measurable_iff_comap_le.mp
  refine measurable_pi_iff.mpr fun ψ => ?_
  let φ : {φ : LQGMetric.TestC0 // tsupport (φ.1 : ℂ → ℝ) ⊆ {y | (y - z) / r ∈ V}} :=
    ⟨⟨LQGMetric.CONF.affPush r z ψ.1.1, by rw [LQGMetric.CONF.integral_affPush hr z, ψ.1.2]⟩,
      LQGMetric.CONF.tsupport_affPush_subset hr z ψ.1.1 ψ.2⟩
  have hgen : Measurable (fun ω => fun φ : {φ : LQGMetric.TestC0 //
      tsupport (φ.1 : ℂ → ℝ) ⊆ {y | (y - z) / r ∈ V}} => h ω φ.1.1) :=
    Measurable.of_comap_le le_rfl
  convert (measurable_pi_apply φ).comp hgen using 1
  funext ω
  exact LQGMetric.CONF.affineComp_apply_eq_affPush r z (h ω) ψ.1.1

/-- `(y − z)/r ∈ A_{1/16,32}(0)` implies `r/16 ≤ |y − z| ≤ 32 r`. -/
theorem rep_mem_closedAnnulus_of_div {r : ℝ} (hr : 0 < r) (z y : ℂ)
    (hy : (y - z) / (r : ℂ) ∈ (annulus 0 (1 / 16) 32 : Set ℂ)) :
    r / 16 ≤ dist y z ∧ dist y z ≤ 32 * r := by
  have hy' : 1 / 16 < ‖(y - z) / (r : ℂ) - 0‖ ∧ ‖(y - z) / (r : ℂ) - 0‖ < 32 := hy
  have hn : ‖(y - z) / (r : ℂ) - 0‖ = dist y z / r := by
    rw [sub_zero, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, dist_eq_norm]
  rw [hn] at hy'
  obtain ⟨h1, h2⟩ := hy'
  rw [lt_div_iff₀ hr] at h1
  rw [div_lt_iff₀ hr] at h2
  constructor <;> linarith

/-- **σ-algebra transfer** (SB2 §2.3 item 7, M5): the unit-scale locality `σ(h^{z,r}|_{A_{1/16,32}(0)})`
modulo constants is contained in the closed-annulus σ-algebra modulo constants of `h − h_r(z)` on
`Ā_{r/16,32r}(z)`, the form consumed by the annulus concentration (1.6). -/
theorem rep_sigma_transfer {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    fieldSigma0On (fun ω => Core.recentred ⟨r, hr⟩ z (h ω)) (annulus 0 (1 / 16) 32 : Set ℂ) ≤
      fieldSigmaClosed0 (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
        {x | r / 16 ≤ dist x z ∧ dist x z ≤ 32 * r} := by
  rw [Concentration.modConstSigma_addRandomConstant h (fun ω => -circleAvg (h ω) r z)]
  change fieldSigma0On (fun ω => addConst (scaleTranslateDist ⟨r, hr⟩ z (h ω))
    (-circleAvg (h ω) r z)) _ ≤ _
  rw [LQGMetric.CONF.fieldSigma0On_addConst]
  simp only [B2.Strong.scaleTranslateDist_eq_affineComp]
  refine (rep_fieldSigma0On_affineComp_le h hr z _).trans ?_
  refine le_iInf₂ fun δ hδ => LQGMetric.CONF.conf36_fieldSigma0On_mono h ?_
  intro y hy
  exact self_subset_thickening hδ _ (rep_mem_closedAnnulus_of_div hr z y hy)

/-! ### The band lies in the regime -/

/-- **Band ⇒ regime** (SB2 §2.3 item 8): for `0 < s < t < 1` and thresholds `δ₀, ℓ₀ > 0`, there is
`ε₀ > 0` such that every `ε ∈ (0, ε₀)` and every `r ∈ [ε^t, ε^s]` satisfy the hypotheses of
`UnitGoodStmt` and `DilationStmt` with `δ = ε/r`, `L = log ε⁻¹`. -/
theorem rep_band_regime {s t : ℝ} (hs : 0 < s) (_hst : s < t) (ht : t < 1) {δ₀ ℓ₀ : ℝ}
    (hδ₀ : 0 < δ₀) (hℓ₀ : 0 < ℓ₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ r : ℝ, ε ^ t ≤ r → r ≤ ε ^ s →
      ε < 1 ∧ 0 < r ∧ ε / r < 1 ∧ 1 < Real.log ε⁻¹ ∧ 1 < Real.log (ε / r)⁻¹ ∧
        Real.log (ε / r)⁻¹ ≤ Real.log ε⁻¹ ∧ ε / r < δ₀ ∧ ε / r * Real.log ε⁻¹ < ℓ₀ := by
  have hu : 0 < 1 - t := by linarith
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  have e2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.log ε < -(1 - t)⁻¹ :=
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
  have hcont : Tendsto (fun ε : ℝ => ε ^ (1 - t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 (1 - t) (Or.inr hu.le)).tendsto
    rw [Real.zero_rpow hu.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 - t) < δ₀ := hcont.eventually (eventually_lt_nhds hδ₀)
  have hlm : Tendsto (fun ε : ℝ => -(Real.log ε * ε ^ (1 - t))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [neg_zero] using (tendsto_log_mul_rpow_nhdsGT_zero hu).neg
  have e4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), -(Real.log ε * ε ^ (1 - t)) < ℓ₀ :=
    hlm.eventually (eventually_lt_nhds hℓ₀)
  obtain ⟨ε₀, hε₀, hall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 (((e1.and e2).and e3).and e4)
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ r hr1 hr2 => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hall ⟨hε, hεε₀⟩
  have hεt : 0 < ε ^ t := Real.rpow_pos_of_pos hε t
  have hr : 0 < r := hεt.trans_le hr1
  have hr1' : r ≤ 1 := hr2.trans (Real.rpow_le_one hε.le h1.le hs.le)
  have hlogε : 0 < -Real.log ε := by
    have : (0 : ℝ) < (1 - t)⁻¹ := inv_pos.2 hu
    linarith
  have hLε : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
  have hdiv : ε / r ≤ ε ^ (1 - t) := by
    calc ε / r ≤ ε / ε ^ t := div_le_div_of_nonneg_left hε.le hεt hr1
      _ = ε ^ (1 - t) := by rw [Real.rpow_sub hε, Real.rpow_one]
  have hlogδ : Real.log (ε / r)⁻¹ = Real.log r - Real.log ε := by
    rw [inv_div, Real.log_div hr.ne' hε.ne']
  have hlogr : t * Real.log ε ≤ Real.log r := by
    rw [← Real.log_rpow hε]
    exact Real.log_le_log hεt hr1
  have hlogr0 : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1'
  -- `(1 - t) (- log ε) > 1`
  have hkey : 1 < (1 - t) * -Real.log ε := by
    have h := mul_lt_mul_of_pos_left (show (1 - t)⁻¹ < -Real.log ε by linarith) hu
    rwa [mul_inv_cancel₀ hu.ne'] at h
  refine ⟨h1, hr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hdiv.trans_lt (Real.rpow_lt_one hε.le h1 hu)
  · rw [hLε]
    nlinarith
  · rw [hlogδ]
    nlinarith
  · rw [hlogδ, hLε]
    linarith
  · exact hdiv.trans_lt h3
  · calc ε / r * Real.log ε⁻¹ ≤ ε ^ (1 - t) * Real.log ε⁻¹ :=
          mul_le_mul_of_nonneg_right hdiv (by rw [hLε]; exact hlogε.le)
      _ = -(Real.log ε * ε ^ (1 - t)) := by rw [hLε]; ring
      _ < ℓ₀ := h4

/-! ### The factor ratio -/

/-- The ratio of the target and source factors is `κ_ε(r)`:
`(r 𝔞_{ε/r}/𝔞_ε) e^{ξc} / (r^{ξQ} e^{ξc}) = κ_ε(r)`. -/
theorem rep_factor_ratio (S : Core.Setup) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (hδ : 0 < ε / r)
    (c : ℝ) :
    1 * ((r : ℝ) * (S.m ⟨ε / r, hδ⟩ : ℝ) / (S.m ⟨ε, hε⟩ : ℝ) * Real.exp ((S.ξ : ℝ) * c)) /
        (r ^ ((S.ξ : ℝ) * S.Q) * Real.exp ((S.ξ : ℝ) * c)) =
      Core.kappaS S ⟨ε, hε⟩ ⟨r, hr⟩ := by
  have hm1 : (0 : ℝ) < S.m ⟨ε / r, hδ⟩ := (S.m ⟨ε / r, hδ⟩).2
  have hm2 : (0 : ℝ) < S.m ⟨ε, hε⟩ := (S.m ⟨ε, hε⟩).2
  have hrp : 0 < r ^ ((S.ξ : ℝ) * S.Q) := Real.rpow_pos_of_pos hr _
  have he : 0 < Real.exp ((S.ξ : ℝ) * c) := Real.exp_pos _
  show _ = (r : ℝ) * (S.m ⟨ε / r, _⟩ : ℝ) / (r ^ ((S.ξ : ℝ) * S.Q) * (S.m ⟨ε, hε⟩ : ℝ))
  field_simp

/-! ### The event at one centre and radius -/

/-- **The good root event at `(z, r)`** (SB2 D4 item 3): from a unit-scale good event `G` of the
normalized field `h^{z,r}` with `δ = ε/r`, `L = log ε⁻¹`, a representative measurable for the
closed-annulus σ-algebra of `h − h_r(z)` on `Ā_{r/16,32r}(z)` modulo constants, of the same
probability, on which (a.s.) `(D, X̂_ε)` is a good scale at `(z, r)` with `K = κ_ε(r)` and `(X̂_ε, D)`
with `K = κ_ε(r)⁻¹`. -/
theorem rep_event_at (S : Core.Setup) (hS : Core.ScalingDStmt S) (hD : Core.DilationStmt S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) {η d₀ A p₀ : ℝ} {ε r : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (z : ℂ) (hδ : ε / r ∈ Ioo (0 : ℝ) 1) (h1 : 1 < Real.log ε⁻¹)
    (h1r : 1 < Real.log (ε / r)⁻¹) (hLr : Real.log (ε / r)⁻¹ ≤ Real.log ε⁻¹) {G : Set Ω}
    (hGm : AEEventIn P (fieldSigma0On (fun ω => Core.recentred ⟨r, hr⟩ z (h ω))
      (annulus 0 (1 / 16) 32 : Set ℂ)) G)
    (hGp : ENNReal.ofReal p₀ ≤ P G)
    (hGg : ∀ᵐ ω ∂P, ω ∈ G →
      Core.GoodScale (S.D (Core.recentred ⟨r, hr⟩ z (h ω)))
          (Core.locMetricY S (ε / r) (Real.log ε⁻¹) hδ (Core.recentred ⟨r, hr⟩ z (h ω)))
          0 1 one_pos η d₀ A 1 ∧
        Core.GoodScale (Core.locMetricY S (ε / r) (Real.log ε⁻¹) hδ (Core.recentred ⟨r, hr⟩ z (h ω)))
          (S.D (Core.recentred ⟨r, hr⟩ z (h ω))) 0 1 one_pos η d₀ A 1) :
    ∃ F : Set Ω, (MeasurableSet[fieldSigmaClosed0 (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
        {x | r / 16 ≤ dist x z ∧ dist x z ≤ 32 * r}] F ∧ ENNReal.ofReal p₀ ≤ P F) ∧
      ∀ᵐ ω ∂P, ω ∈ F →
        Core.GoodScale (S.D (h ω)) (Core.locMetric S ε hε (h ω)) z r hr η d₀ A
          (Core.kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩) ∧
        Core.GoodScale (Core.locMetric S ε hε (h ω)) (S.D (h ω)) z r hr η d₀ A
          (Core.kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩)⁻¹ := by
  obtain ⟨F, hFm, hGF⟩ := hGm
  refine ⟨F, ⟨rep_sigma_transfer h hr z F hFm, ?_⟩, ?_⟩
  · rw [← measure_congr hGF]
    exact hGp
  · filter_upwards [(hS P h hh ⟨r, hr⟩ z).2, hGF, hGg] with ω hω hωF hωG hF
    have hG : ω ∈ G := by
      rw [hωF]
      exact hF
    obtain ⟨g1, g2⟩ := hωG hG
    set h' := Core.recentred ⟨r, hr⟩ z (h ω)
    set c := circleAvg (h ω) r z
    set a : ℝ := r ^ ((S.ξ : ℝ) * S.Q) * Real.exp ((S.ξ : ℝ) * c)
    set b : ℝ := r * (S.m ⟨ε / r, hδ.1⟩ : ℝ) / (S.m ⟨ε, hε.1⟩ : ℝ) * Real.exp ((S.ξ : ℝ) * c)
    have ha : 0 < a := mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
    have hb : 0 < b := by
      have hm1 : (0 : ℝ) < S.m ⟨ε / r, hδ.1⟩ := (S.m ⟨ε / r, hδ.1⟩).2
      have hm2 : (0 : ℝ) < S.m ⟨ε, hε.1⟩ := (S.m ⟨ε, hε.1⟩).2
      have := Real.exp_pos ((S.ξ : ℝ) * c)
      positivity
    have hdD : ∀ u v : ℂ, S.D (h ω) (z + r • u, z + r • v) = ENNReal.ofReal a * S.D h' (u, v) := hω
    have hdil := (hD.2 ε (Real.log ε⁻¹) hε ⟨r, hr⟩ hδ h1 le_rfl h1r hLr z c (h ω)).2
    have hdX : ∀ u v : ℂ, Core.locMetric S ε hε (h ω) (z + r • u, z + r • v) =
        ENNReal.ofReal b * Core.locMetricY S (ε / r) (Real.log ε⁻¹) hδ h' (u, v) := by
      intro u v
      rw [hD.1 ε hε h1 (h ω)]
      exact hdil u v
    have k1 := rep_goodScale_affine ha hb z hr hdD hdX g1
    have k2 := rep_goodScale_affine hb ha z hr hdX hdD g2
    have hκ : 1 * b / a = Core.kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩ := rep_factor_ratio S hε.1 hr hδ.1 c
    have hκ' : 1 * a / b = (Core.kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩)⁻¹ := by
      rw [← hκ]
      field_simp
    rw [hκ] at k1
    rw [hκ'] at k2
    exact ⟨k1, k2⟩

/-! ### The root events -/

/-- **§3.3 at centre `z` and radius `r`** (packet REP target; SB2 D4 item 3, M5): the root events
`E_{ε,r}(z)` from the unit-scale good event, (1.3) and (2.4). -/
theorem rootEvent_of (S : Core.Setup) (hU : Core.UnitGoodStmt S) (hS : Core.ScalingDStmt S)
    (hD : Core.DilationStmt S) : Core.RootEventStmt S := by
  intro p₀ hp₀
  obtain ⟨A, hA, hU'⟩ := hU p₀ hp₀
  refine ⟨A, hA, fun d₀ hd₀ => ?_⟩
  obtain ⟨η, hη, hη2, δ₀, ℓ₀, hδ₀, hℓ₀, hG⟩ := hU' d₀ hd₀
  refine ⟨η, hη, hη2, fun s t hs hst ht => ?_⟩
  obtain ⟨ε₀, hε₀, hband⟩ := rep_band_regime hs hst ht hδ₀ hℓ₀
  refine ⟨ε₀, hε₀, fun {Ω} _ P _ h hh => ?_⟩
  -- the regime of `(ε, r)` in which the unit statement and (2.4) apply
  let Reg : ℝ → ℝ → Prop := fun ε r => 0 < ε ∧ ε < 1 ∧ 0 < r ∧ ε / r < 1 ∧ 1 < Real.log ε⁻¹ ∧
    1 < Real.log (ε / r)⁻¹ ∧ Real.log (ε / r)⁻¹ ≤ Real.log ε⁻¹ ∧ ε / r < δ₀ ∧
    ε / r * Real.log ε⁻¹ < ℓ₀
  have hex : ∀ (ε r : ℝ) (z : ℂ), Reg ε r → ∃ F : Set Ω,
      (MeasurableSet[fieldSigmaClosed0 (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
          {x | r / 16 ≤ dist x z ∧ dist x z ≤ 32 * r}] F ∧ ENNReal.ofReal p₀ ≤ P F) ∧
        ∀ (hε : ε ∈ Ioo (0 : ℝ) 1) (hr : 0 < r), ∀ᵐ ω ∂P, ω ∈ F →
          Core.GoodScale (S.D (h ω)) (Core.locMetric S ε hε (h ω)) z r hr η d₀ A
            (Core.kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩) ∧
          Core.GoodScale (Core.locMetric S ε hε (h ω)) (S.D (h ω)) z r hr η d₀ A
            (Core.kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩)⁻¹ := by
    rintro ε r z ⟨hε0, hε1, hr, hδ1, h1, h1r, hLr, hδδ₀, hδℓ₀⟩
    have hε : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, hε1⟩
    have hδ : ε / r ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hε0 hr, hδ1⟩
    have hh' : IsNormalizedWholePlaneGFF (fun ω => Core.recentred ⟨r, hr⟩ z (h ω)) P :=
      (hS P h hh ⟨r, hr⟩ z).1
    obtain ⟨G, hGm, hGp, hGg⟩ := hG (ε / r) hδ (Real.log ε⁻¹) hδδ₀ hLr hδℓ₀ P _ hh'
    obtain ⟨F, hF, hFg⟩ := rep_event_at S hS hD P h hh hε hr z hδ h1 h1r hLr hGm hGp hGg
    exact ⟨F, hF, fun _ _ => hFg⟩
  choose F hF using hex
  classical
  refine ⟨fun ε r z => if hreg : Reg ε r then F ε r z hreg else ∅, ?_, ?_⟩
  · intro ε hε hεε₀ r hr1 hr2 z
    have hreg : Reg ε r := ⟨hε, hband ε hε hεε₀ r hr1 hr2⟩
    simp only [hreg, ↓reduceDIte]
    exact (hF ε r z hreg).1
  · intro ε hε r hr z
    by_cases hreg : Reg ε r
    · simp only [hreg, ↓reduceDIte]
      exact (hF ε r z hreg).2 hε hr
    · simp only [hreg, ↓reduceDIte]
      exact Filter.Eventually.of_forall fun ω hω => absurd hω (Set.notMem_empty ω)

end SupercriticalLFPPAS.GoodRoot
