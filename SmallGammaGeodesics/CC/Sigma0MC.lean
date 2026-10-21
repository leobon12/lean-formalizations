import SmallGammaGeodesics.CC.Sigma0
import SmallGammaGeodesics.CC.ExtensionMobius

/-!
# The CC12b assembly of the (MC) export from `ConfCov` (packet CC12a, extra)

Source: planning audit `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D17**
item 2.

This file is not a target of packet CC12a. It checks that T1 (`exists_isSigma0Metric`) and T4
(`exists_confCoupling_extension`) are stated so that `CC.MCInput` follows from **one** application
of the master interface `CC.ConfCov`, given the local law of the pulled-back GFF (GA4's A3) for the
map at hand, and discharges that law for every Möbius map (`map_confPull_eq_of_isMobius`,
`CC/ExtensionMobius.lean`):

* `mcInput_ae_of_confCov` (one map): on the extension `Ω × DistC` of T4, `ConfCov` applied to the
  coupling `(h ∘ fst, h̄, G − c)` gives `D_h(·,·;V) = D_{h̄ + G − c}(ϕ·, ϕ·; ϕ(V))`; Weyl scaling by
  the constant `−c` and the `σ₀` validity of `d` for `h̄ + G` (T1) turn the right side into
  `e^{−ξc} c₂ · d(pair0On (h̄ + G))(ϕ·, ϕ·)`, and `pair0On (h̄ + G) = confPair0 γ ϕ W V h` (T4); the
  a.s. statement about `h` transfers back to `Ω`;
* `mcInput_of_confCov_of_law`: `MCInput D γ` from `IsStrongLQGMetric γ D`, `ConfCov γ D` and the
  law hypothesis for every Möbius map with `IsConfNbhd ϕ W V`;
* **`mcInput_of_confCov`**: `MCInput D γ` from `IsStrongLQGMetric γ D` and `ConfCov γ D` alone (the
  law hypothesis is GA4's A3, proved for every Möbius map in `CC/ExtensionMobius.lean`).

So CC12b reduces to `mcInput_of_confCov hD (ConfCov from CC11)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Function
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- `x + (F − c) = (x + F) + (−c)`. -/
theorem addFun_sub_const (x : DistC) (F : C(ℂ, ℝ)) (c : ℝ) :
    addFun x (F - ContinuousMap.const ℂ c) = addFun (addFun x F) (ContinuousMap.const ℂ (-c)) := by
  refine DFunLike.ext _ _ fun φ => ?_
  show x φ + ofCont (F - ContinuousMap.const ℂ c) φ =
    (x φ + ofCont F φ) + ofCont (ContinuousMap.const ℂ (-c)) φ
  rw [ofCont_apply, ofCont_apply, ofCont_apply]
  have hF : Integrable fun y => φ y * F y :=
    (φ.continuous.mul F.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hc : Integrable fun y => φ y * c :=
    (φ.continuous.mul continuous_const).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right
  have e1 : (fun y => φ y * (F - ContinuousMap.const ℂ c) y) = fun y => φ y * F y - φ y * c := by
    funext y
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
    ring
  have e2 : (fun y => φ y * (ContinuousMap.const ℂ (-c)) y) = fun y => -(φ y * c) := by
    funext y
    simp only [ContinuousMap.const_apply]
    ring
  rw [e1, e2, integral_sub hF hc, integral_neg]
  ring

/-- **(MC) for one map, from one application of `ConfCov`** (CC12b assembly). Let `D` be a strong
γ-LQG metric satisfying `ConfCov γ D`, `IsConfNbhd ϕ W V`, and `d` a `σ₀(ϕ(V))` functional. If the
pulled-back GFF has the local law of the GFF (GA4's A3, hypothesis `hlaw`), then a.s.
`D_h(z, w; V) = c · d(confPair0 γ ϕ W V h)(ϕ z, ϕ w)` on `V × V` for some `c ∈ (0, ∞)`. -/
theorem mcInput_ae_of_confCov {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    (hCC : ConfCov γ D) {ϕ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V)
    {d : (TestC0On (ϕ '' V) → ℝ) → ℂ → ℂ → ℝ≥0∞} (hd : IsSigma0Metric D (ϕ '' V) d)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P)
    (hlaw : P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull ϕ W g.1.1)) =
      P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1)) :
    ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ ∀ z ∈ V, ∀ w ∈ V,
      (D (h ω)).internal V z w = c * d (confPair0 γ ϕ W V (h ω)) (ϕ z) (ϕ w) := by
  obtain ⟨P', G, c, hP', -, htr, hhG, hbG, hcm, -, hcoup, hpair⟩ :=
    exists_confCoupling_extension hϕ γ P hh hlaw
  set f : Ω × DistC → C(ℂ, ℝ) := fun p => testCont G - ContinuousMap.const ℂ (c p) with hfdef
  have hconst : Continuous fun a : ℝ => ContinuousMap.const ℂ a :=
    ContinuousMap.continuous_const'
  have hfm : Measurable f :=
    (continuous_const.sub hconst).measurable.comp hcm
  -- the one application of `ConfCov`
  have hcc := hCC ϕ W V hϕ P' (fun p => h p.1) (fun p => p.2) f hhG hbG hfm hcoup
  -- `σ₀` validity of `d` for `h̄ + G`
  have hval := hd.2 P' (fun p => p.2) G hbG
  -- Weyl scaling by constants for `h̄ + G`
  have hweyl := hD.ae_internal_addFun_of_eq_const
    (isGFFPlusCont_addFun_of_wp hbG (measurable_const : Measurable fun _ : Ω × DistC => testCont G))
  refine htr _ ?_
  filter_upwards [hcc, hval, hweyl, hpair] with p hp hv hw hpr
  obtain ⟨c₂, hc₂0, hc₂T, hc₂⟩ := hv
  refine ⟨ENNReal.ofReal (Real.exp (xiGamma γ * -c p)) * c₂,
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hc₂0.ne',
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc₂T, fun z hz w hw' => ?_⟩
  have hzU : ϕ z ∈ ϕ '' V := mem_image_of_mem ϕ hz
  have hwU : ϕ w ∈ ϕ '' V := mem_image_of_mem ϕ hw'
  rw [hp z hz w hw', confMetric_def]
  show (D (addFun p.2 (testCont G - ContinuousMap.const ℂ (c p)))).internal (ϕ '' V) (ϕ z) (ϕ w) = _
  rw [addFun_sub_const, hw (ContinuousMap.const ℂ (-c p)) (ϕ '' V) (xiGamma γ * -c p)
    hϕ.isOpen_image (fun _ _ => rfl) (ϕ z) (ϕ w), hc₂ (ϕ z) hzU (ϕ w) hwU, ← hpr, mul_assoc]

/-- **`MCInput` from `ConfCov` and the Möbius law** (CC12b assembly). -/
theorem mcInput_of_confCov_of_law {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    (hCC : ConfCov γ D)
    (hA3 : ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsMobius ϕ → IsConfNbhd ϕ W V →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P →
        P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull ϕ W g.1.1)) =
          P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1)) :
    MCInput D γ := by
  intro ϕ W V hM hϕ
  obtain ⟨d, hd⟩ := exists_isSigma0Metric hD hϕ.isOpen_image
  refine ⟨d, hd, ?_⟩
  intro Ω _ P _ h hh
  exact mcInput_ae_of_confCov hD hCC hϕ hd P hh (hA3 ϕ W V hM hϕ P h hh)

/-- **`MCInput` from `ConfCov`** (CC12b): for a strong γ-LQG metric `D`, the master interface
`ConfCov γ D` implies the Möbius covariance modulo constants `MCInput D γ`. -/
theorem mcInput_of_confCov {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    (hCC : ConfCov γ D) : MCInput D γ := by
  refine mcInput_of_confCov_of_law hD hCC ?_
  intro ϕ W V hM hϕ Ω _ P _ h hh
  exact map_confPull_eq_of_isMobius hM hϕ hh

/-- `MCInput` for every canonical γ-LQG metric, from the master keystone `MasterCC` (CC11); this is
the form consumed by §7 (`lowerBound71_of_MC`, hypothesis `∀ γ ∈ (0,2), MCInput (D γ) γ`). -/
theorem mcInput_of_masterCC (hM : MasterCC) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} (hD : GaussianLQG.IsCanonicalLQGMetric γ D) : MCInput D γ :=
  mcInput_of_confCov hD.1 (hM γ hγ hγ2 D hD)

/-- `MCInput` for every strong γ-LQG metric, from `MasterCCStrong`. -/
theorem mcInput_of_masterCCStrong (hM : MasterCCStrong) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) : MCInput D γ :=
  mcInput_of_confCov hD (hM γ hγ hγ2 D hD)

end SmallGammaGeodesics.CC
