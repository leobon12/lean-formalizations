import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer
import SupercriticalLQGUniqueness.Frozen.RescaledLFPP
import SupercriticalLQGUniqueness.Frozen.LSCMetricToLSCFun
import SupercriticalLQGUniqueness.Frozen.LSCTendsto
import SupercriticalLQGUniqueness.Frozen.LSCTendstoInProbability
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalLQGUniqueness.Frozen.Lfpp_tendstoInProbability
import SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPNormalizer
import SupercriticalLQGUniqueness.B2.LscTop.InProbability
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd
import SupercriticalLQGUniqueness.Exponent.HeatVersion
import NV1Evidence
import LQGMetric.Papers.DFGPS.T12P0

/-!
# Joint heat versions: uniqueness at every `ε` at once, and the refuted version v1 (ruling P6)

Supporting results for the frozen statement surface (not frozen; S1 §5.3 and condition C4 of ruling P7):
* `ae_eq_of_jointHeatVersions`: two families of continuous heat versions (`IsHeatSmoothing` at every `ε`) that are
  almost surely jointly continuous in `(ε, z)` agree almost surely at every `ε > 0` at once. So the families admitted
  by `lfpp_ae_lscTendsto` (binders #11–#13 of S1 §2) are the paper's `h*_ε`, up to one null set; existence is the
  frozen `exists_jointHeatVersion`.
* `RefutedV1.not_thm11v1`: the P6 erratum, kept as a durable regression. `RefutedV1.Thm11v1` is the type of the
  **refuted** candidate v1 (`planning/drafts/S0Surface.lean.txt`, which lacks the joint-continuity hypothesis),
  written out verbatim. It is false, and it is never an anchor.

The proofs are those of the S1 evidence (`planning/audits/S1-statement-audit.md` §4).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric (DistC)

namespace SupercriticalLFPPAS

open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF IsHeatSmoothing IsLFPPNormalizer
  rescaledLFPP LSCMetric LSCTendsto LSCTendstoInProbability lfppDistance lfpp_tendstoInProbability
  existsUnique_isLFPPNormalizer)
open SupercriticalConformalCovariance (xiCrit)

/-! ### Uniqueness of jointly continuous heat versions -/

/-- **Jointly continuous heat versions are unique at every `ε` at once.** Two a.s. jointly continuous families of
continuous heat versions agree, almost surely, at every `ε > 0` simultaneously (per-`ε` uniqueness on a countable
dense set of scales, then joint continuity). -/
theorem ae_eq_of_jointHeatVersions {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} {X Y : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)}
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) (hY : ∀ ε, IsHeatSmoothing P h ε (Y ε))
    (hXc : ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2)
    (hYc : ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => Y p.1 ω p.2) :
    ∀ᵐ ω ∂P, ∀ ε, X ε ω = Y ε ω := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Set.Ioi (0 : ℝ))
  have hS : ∀ᵐ ω ∂P, ∀ ε ∈ S, X ε ω = Y ε ω := by
    rw [ae_ball_iff hSc]
    intro ε _
    exact SupercriticalLQGUniqueness.Exponent.HeatVersion.ae_eq_continuous_heat_versions
      (ε : ℝ) ε.2 (X ε) (Y ε) (hX ε) (hY ε)
  filter_upwards [hS, hXc, hYc] with ω hω hcX hcY
  have hEq : (fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2) = fun p => Y p.1 ω p.2 :=
    Continuous.ext_on (hSd.prod dense_univ) hcX hcY fun p hp => by
      simp only [hω p.1 hp.1]
  intro ε
  ext z
  exact congrFun hEq (ε, z)

/-! ### The refuted version v1 (ruling P6) -/

namespace RefutedV1

/-- **REFUTED candidate v1 — false, never an anchor.** The type of the S0 candidate v1 of Theorem 1.1
(`planning/drafts/S0Surface.lean.txt`, sha256 `d1d1f18b…c600e`), verbatim. It quantifies over every family of
per-`ε` heat versions, without the joint-continuity hypothesis of the frozen v2; `not_thm11v1` proves it false. -/
def Thm11v1 : Prop :=
    ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) →
      ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
        ∀ L : Ω → LSCMetric,
          LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
            (fun ω => (L ω).toLSCFun.1) →
          ∀ᵐ ω ∂P, ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
            LSCTendsto (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)) (L ω).toLSCFun.1

theorem xiCrit_nonneg : 0 ≤ xiCrit :=
  Real.sInf_nonneg fun _ hx => hx.1.le

theorem exists_gt_xiCrit : ∃ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) :=
  ⟨⟨xiCrit + 1, by have := xiCrit_nonneg; simp only [mem_Ioi]; linarith⟩, by
    simp only; linarith⟩

theorem exists_normalizer (ξ : Set.Ioi (0 : ℝ)) :
    ∃ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), ∀ ε, IsLFPPNormalizer ξ ε (m ε) :=
  ⟨fun ε => (existsUnique_isLFPPNormalizer ξ ε).exists.choose,
    fun ε => (existsUnique_isLFPPNormalizer ξ ε).exists.choose_spec⟩

theorem exists_heat {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), ∀ ε, IsHeatSmoothing P h ε (X ε) :=
  ⟨fun ε => (SupercriticalLQGUniqueness.B2.PfeAxioms.exists_heatVersion_bdd
      (LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1) ε).choose,
    fun ε => (SupercriticalLQGUniqueness.B2.PfeAxioms.exists_heatVersion_bdd
      (LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1) ε).choose_spec.2⟩

/-- The straight segment `[0, 1]` bounds the LFPP distance of a constant field. -/
theorem lfppDistance_const_le (ξ c : ℝ) :
    lfppDistance ξ (ContinuousMap.const ℂ c) ((0 : ℂ), (1 : ℂ)) ≤
      ENNReal.ofReal (Real.exp (ξ * c)) := by
  let γ : ℝ → ℂ := fun t => (t : ℂ)
  have hγ : LQGMetric.IsPiecewiseC1Path γ (0 : ℂ) (1 : ℂ) :=
    { source := by simp [γ]
      target := by simp [γ]
      continuousOn := Complex.continuous_ofReal.continuousOn
      piecewise := ⟨1, fun i => ((i : ℕ) : ℝ), fun a b hab => by
          show ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ); exact_mod_cast hab, by simp,
        by simp, fun _ => Complex.ofRealCLM.contDiff.contDiffOn⟩ }
  refine (iInf₂_le γ hγ).trans (le_of_eq ?_)
  show LQGMetric.lfppLen ξ (⇑(ContinuousMap.const ℂ c)) γ = _
  have hd : ∀ t : ℝ, deriv γ t = 1 := fun t => by
    simpa [γ] using ((hasDerivAt_id t).ofReal_comp).deriv
  simp only [LQGMetric.lfppLen, ContinuousMap.const_apply, hd, norm_one, mul_one,
    setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- The rescaled LFPP distance from `0` to `1` of the constant field `-(-log a + e)/ξ` is at most `exp (-e)`. -/
theorem rescaledLFPP_badField_le (ξ : Set.Ioi (0 : ℝ)) (a : Set.Ioi (0 : ℝ)) (e : ℝ) :
    rescaledLFPP (ξ : ℝ) a
        (ContinuousMap.const ℂ (-((-Real.log (a : ℝ) + e) / (ξ : ℝ)))) ((0 : ℂ), (1 : ℂ)) ≤
      ((ENNReal.ofReal (Real.exp (-e)) : ENNReal) : EReal) := by
  unfold rescaledLFPP
  rw [EReal.coe_ennreal_le_coe_ennreal_iff]
  have ha : 0 < (a : ℝ) := a.2
  have hξ : (ξ : ℝ) ≠ 0 := ξ.2.ne'
  have hexp : Real.exp ((ξ : ℝ) * -((-Real.log (a : ℝ) + e) / (ξ : ℝ))) =
      (a : ℝ) * Real.exp (-e) := by
    rw [show (ξ : ℝ) * -((-Real.log (a : ℝ) + e) / (ξ : ℝ)) = Real.log (a : ℝ) + -e by
      field_simp; ring, Real.exp_add, Real.exp_log ha]
  calc ENNReal.ofReal ((a : ℝ)⁻¹) *
        lfppDistance (ξ : ℝ) (ContinuousMap.const ℂ (-((-Real.log (a : ℝ) + e) / (ξ : ℝ))))
          ((0 : ℂ), (1 : ℂ))
      ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * ENNReal.ofReal ((a : ℝ) * Real.exp (-e)) := by
        gcongr
        rw [← hexp]
        exact lfppDistance_const_le _ _
    _ = ENNReal.ofReal (Real.exp (-e)) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 ha.le), ← mul_assoc, inv_mul_cancel₀ ha.ne',
          one_mul]

/-- **The refuted version v1 is false** (ruling P6; S1 §4.1). On `Ω × ℝ` (a normalized GFF `h ∘ fst` and an
independent uniform `u`), the family that equals the constant field `-(-log 𝔞_ε + ε⁻¹)/ξ` when `ε = eᵘ/(k+1)` for
some `k`, and the heat version `X ε` otherwise, is still a heat version at every `ε` (the exceptional set at a fixed
`ε` is countable in `u`) and has the same limit in probability; but along `ε_k = eᵘ/(k+1) → 0` its rescaled distance
from `0` to `1` is at most `exp(-ε_k⁻¹) → 0 < D_h(0, 1)`, so the lower-limit property (1.2) fails at every sample. -/
theorem not_thm11v1 : ¬ Thm11v1 := by
  classical
  intro H
  obtain ⟨ξ, hξ⟩ := exists_gt_xiCrit
  obtain ⟨m, hm⟩ := exists_normalizer ξ
  obtain ⟨Ω, mΩ, P, hP, h, hh⟩ := SupercriticalLQGUniqueness.exists_normalizedGFF
  obtain ⟨X, hX⟩ := exists_heat hh
  obtain ⟨L, -, hL⟩ := lfpp_tendstoInProbability ξ m hm P h (LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1)
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  let P' : Measure (Ω × ℝ) := P.prod ν
  have hfst : Measure.QuasiMeasurePreserving Prod.fst P' P := Measure.quasiMeasurePreserving_fst
  have hsnd : Measure.QuasiMeasurePreserving Prod.snd P' ν := Measure.quasiMeasurePreserving_snd
  let h' : Ω × ℝ → DistC := fun x => h x.1
  have hh' : IsNormalizedWholePlaneGFF h' P' := by
    refine SupercriticalLQGUniqueness.isNormalizedWholePlaneGFF_iff_old.2
      (LQGMetric.DFGPS.T12.isNormalizedWPGFF_of_map_eq (hh.1.measurable.comp measurable_fst)
        (SupercriticalLQGUniqueness.isNormalizedWholePlaneGFF_iff_old.1 hh) ?_)
    show P'.map (h ∘ Prod.fst) = P.map h
    rw [← Measure.map_map hh.1.measurable measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul]
  let bad : Set.Ioi (0 : ℝ) → ℝ → Prop := fun ε u => ∃ k : ℕ, (ε : ℝ) = Real.exp u / (k + 1)
  have hnull : ∀ ε, ∀ᵐ u ∂ν, ¬ bad ε u := by
    intro ε
    have hsub : {u : ℝ | ¬¬ bad ε u} ⊆ Set.range fun k : ℕ => Real.log ((ε : ℝ) * (k + 1)) := by
      rintro u hu
      obtain ⟨k, hk⟩ := not_not.1 hu
      refine ⟨k, ?_⟩
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      simp only
      rw [hk, div_mul_cancel₀ _ hk1.ne', Real.log_exp]
    rw [ae_iff]
    exact measure_mono_null hsub ((Set.countable_range _).measure_zero ν)
  let K : Set.Ioi (0 : ℝ) → ℝ := fun ε => -((-Real.log (m ε : ℝ) + (ε : ℝ)⁻¹) / (ξ : ℝ))
  let X' : Set.Ioi (0 : ℝ) → Ω × ℝ → C(ℂ, ℝ) := fun ε x =>
    if bad ε x.2 then ContinuousMap.const ℂ (K ε) else X ε x.1
  have hagree : ∀ ε, ∀ᵐ x ∂P', X' ε x = X ε x.1 := by
    intro ε
    filter_upwards [hsnd.ae (hnull ε)] with x hx
    simp [X', hx]
  have hX' : ∀ ε, IsHeatSmoothing P' h' ε (X' ε) := by
    intro ε z
    filter_upwards [hfst.ae (hX ε z), hagree ε] with x hx hx'
    rw [hx']
    exact hx
  let L' : Ω × ℝ → LSCMetric := fun x => L x.1
  have hL' : LSCTendstoInProbability P' (fun ε x => rescaledLFPP (ξ : ℝ) (m ε) (X' ε x))
      (fun x => (L' x).toLSCFun.1) := by
    have h0 : LSCTendstoInProbability P' (fun ε x => rescaledLFPP (ξ : ℝ) (m ε) (X ε x.1))
        (fun x => (L' x).toLSCFun.1) := by
      intro εs hεs
      obtain ⟨φ, hφ, hae⟩ := hL X hX εs hεs
      exact ⟨φ, hφ, hfst.ae hae⟩
    refine SupercriticalLQGUniqueness.B2.LscTop.LSCTendstoInProbability.congr h0 fun ε => ?_
    filter_upwards [hagree ε] with x hx
    simp only [hx]
  obtain ⟨x, hx⟩ := (H ξ hξ m hm P' h' hh' X' hX' L' hL').exists
  -- the random sequence `ε_k = eᵘ / (k + 1)`
  have hpos : ∀ k : ℕ, 0 < Real.exp x.2 / ((k : ℝ) + 1) := fun k => by positivity
  let εs : ℕ → Set.Ioi (0 : ℝ) := fun k => ⟨Real.exp x.2 / ((k : ℝ) + 1), hpos k⟩
  have hεs : Tendsto (fun k => (εs k : ℝ)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Real.exp x.2)
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    simp only [εs, mul_one_div]
  have hbad : ∀ k, X' (εs k) x = ContinuousMap.const ℂ (K (εs k)) := fun k => by
    simp [X', show bad (εs k) x.2 from ⟨k, rfl⟩]
  have hle : ∀ k, rescaledLFPP (ξ : ℝ) (m (εs k)) (X' (εs k) x) ((0 : ℂ), (1 : ℂ)) ≤
      ((ENNReal.ofReal (Real.exp (-(εs k : ℝ)⁻¹)) : ENNReal) : EReal) := fun k => by
    rw [hbad k]
    exact rescaledLFPP_badField_le ξ (m (εs k)) _
  have hlim : Tendsto (fun k => ((ENNReal.ofReal (Real.exp (-(εs k : ℝ)⁻¹)) : ENNReal) : EReal))
      atTop (𝓝 0) := by
    have hw : Tendsto (fun k => (εs k : ℝ)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hεs, Eventually.of_forall fun k => (εs k).2⟩
    have h1 : Tendsto (fun k => Real.exp (-(εs k : ℝ)⁻¹)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_inv_nhdsGT_zero.comp hw)
    have h2 : Tendsto (fun k => ENNReal.ofReal (Real.exp (-(εs k : ℝ)⁻¹))) atTop
        (𝓝 (ENNReal.ofReal 0)) := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    rw [ENNReal.ofReal_zero] at h2
    have h3 : Tendsto (fun k => ((ENNReal.ofReal (Real.exp (-(εs k : ℝ)⁻¹)) : ENNReal) : EReal))
        atTop (𝓝 ((0 : ENNReal) : EReal)) := (continuous_coe_ennreal_ereal.tendsto 0).comp h2
    rwa [EReal.coe_ennreal_zero] at h3
  have hlow := (hx εs hεs).1 (fun _ => ((0 : ℂ), (1 : ℂ))) ((0 : ℂ), (1 : ℂ)) tendsto_const_nhds
  have hzero : ((L x.1).1 ((0 : ℂ), (1 : ℂ)) : EReal) ≤ 0 := by
    calc ((L x.1).1 ((0 : ℂ), (1 : ℂ)) : EReal)
        ≤ liminf (fun k => rescaledLFPP (ξ : ℝ) (m (εs k)) (X' (εs k) x) ((0 : ℂ), (1 : ℂ)))
            atTop := hlow
      _ ≤ liminf (fun k => ((ENNReal.ofReal (Real.exp (-(εs k : ℝ)⁻¹)) : ENNReal) : EReal))
            atTop := liminf_le_liminf (Eventually.of_forall hle)
      _ = 0 := hlim.liminf_eq
  have h01 : (L x.1).1 ((0 : ℂ), (1 : ℂ)) = 0 := by
    rw [← EReal.coe_ennreal_zero, EReal.coe_ennreal_le_coe_ennreal_iff] at hzero
    exact le_antisymm hzero bot_le
  exact zero_ne_one ((L x.1).2.1.2.1 0 1 h01)

end RefutedV1

end SupercriticalLFPPAS
