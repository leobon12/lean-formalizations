/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Energy

/-!
# The local comparison of Aux. lemma 55: the conditional law of the pairing `(h, v)` before the local stop

Packet PROVE-LOCEXT-A2, step 3. Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L163–L180, p. 248): "The
original coupling and the source support in (HL2) give `E[Z | 𝓕_t] = …`"; "The same source approximation proves (HL4)
for `v`."

Fix a coupling `(h, W, V)` with the frozen optional hull specification (`IsOptionalHullCoupling`), an ordered word with
admissible seed, a seed radius `r`, and a stopping time `τ` of the frozen driving filtration with `τ ≤ S` (the local
stop) almost surely. Along the path of `ω`, at time `t`:

* `bheAt`: the explicit bounded harmonic extension of the force data (`Impl.forceExt`);
* `srcMeanAt … t ω = ∫ 𝔥_t(z) v(z) dz` (the tested mean, with the frozen `couplingMean`);
* `srcEnergyAt … t ω = E_t(v)` (the frozen `loewnerGreenEnergy` of the source).

**`condExp_cexp_srcPair`**: for every real `λ`,
`E[exp(i λ (h, v)) | 𝓖_τ] = exp(i λ (𝔥_τ, v) − ½ λ² E_τ(v))` almost surely: conditionally on the stopped driving history,
the pairing `(h, v) = srcPair (h)` of the field with the source is Gaussian with mean `(𝔥_τ, v)` and variance `E_τ(v)`.
The proof applies the frozen kernel to the test functions `λ v_{n_k}` (their supports avoid `K_τ ⊆ B̄(0, 5r/8)`,
`tsupport_vApprox_subset_norm`) and passes to the limit (`ae_condExp_cexp_of_tendsto`), with the deterministic
convergences of `LocalExtA2Energy` along each good path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull greenH logDerivFwd chiC)
open LQGMetric (TestOn DistOn)

/-! ### The tested mean and energy along a path -/

section Defs

variable {nL nR : ℕ} {Ω : Type*}

/-- The explicit bounded harmonic extension of the force data at centred positions `(vL; vR)`. -/
def bheAt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) : ℂ → ℝ :=
  Impl.forceExt κ (Ito.weightWord ρL ρR) vL vR

theorem isBoundedHarmonicExtension_bheAt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) :
    IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) (bheAt κ ρL ρR vL vR) :=
  Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) vL vR

theorem continuousOn_of_isBoundedHarmonicExtension {g : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) : ContinuousOn u H := fun z hz =>
  ((hu.1 z hz).1.continuousAt).continuousWithinAt

/-- **The tested mean** `(𝔥_t, v) = ∫ 𝔥_t(z) v(z) dz` along the path of `ω`, with the explicit harmonic extension of
the centred data at time `t`. -/
def srcMeanAt (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) t
    (bheAt κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) z * vSrc κ xL xR ρL ρR r z

/-- **The conditional variance** `E_t(v) = G_{ℍ∖K_t}(v, v)` along the path of `ω`. -/
def srcEnergyAt (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) t (vSrc κ xL xR ρL ρR r)

theorem couplingMean_clampDrv_of_le (κ : ℝ) (W : ℝ → ℝ) {T s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (u : ℂ → ℝ) :
    couplingMean κ (Ito.clampDrv W T) s u = couplingMean κ W s u := by
  funext z
  simp only [couplingMean, Ito.fwdMap_clampDrv_of_le hsT, Ito.logDerivFwd_clampDrv_of_le hs hsT]

end Defs

/-! ### Along a good path, through the stop -/

section PathLimits

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- Through the stop, a good path is (after clamping) in the local regime up to a time `T ≥ t`, `T < T₂ < ζ`. -/
theorem exists_regime_of_le_localStopPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) :
    ∃ T T₂ : ℝ≥0, t ≤ T ∧ T < T₂ ∧ (T₂ : ℝ≥0∞) < ζ ∧ (T : WithTop ℝ≥0) ≤ localStopPath r ζ w ∧
      IsLocalRegime (Ito.clampDrv (Ito.rpath w) T₂) r T := by
  obtain ⟨T, T₂, hS, -, hTT₂, hT₂⟩ := exists_stop_lt hp hterm hF hr hseed
  refine ⟨T, T₂, WithTop.coe_le_coe.1 (ht.trans hS.le), hTT₂, hT₂, hS.ge,
    isLocalRegime_of_le_localStopPath hp hr.1 hS.ge hTT₂.le hT₂⟩

/-- **The tested means of the approximations converge along a good path** at every `t ≤ S`. -/
theorem tendsto_integral_couplingMean_vApprox_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) {u : ℂ → ℝ} {g : ℝ → ℝ} {S : Set ℝ}
    (hu : IsBoundedHarmonicExtension g S u) {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => ∫ z, couplingMean κ (Ito.rpath w) t u z * vApprox κ xL xR ρL ρR r (n k) z) atTop
      (𝓝 (∫ z, couplingMean κ (Ito.rpath w) t u z * vSrc κ xL xR ρL ρR r z)) := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  obtain ⟨C, hC⟩ := hu.2.1
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  have h := tendsto_integral_couplingMean_mul_vApprox (κ := κ) (ρL := ρL) (ρR := ρR) hreg hF hr
    (continuousOn_of_isBoundedHarmonicExtension hu) hC ⟨t.coe_nonneg, by exact_mod_cast htT⟩ hn
  rwa [couplingMean_clampDrv_of_le κ _ t.coe_nonneg htT₂] at h

/-- **The energies of the approximations converge along a good path** at every `t ≤ S`. -/
theorem tendsto_loewnerGreenEnergy_vApprox_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => loewnerGreenEnergy (Ito.rpath w) t (vApprox κ xL xR ρL ρR r (n k))) atTop
      (𝓝 (loewnerGreenEnergy (Ito.rpath w) t (vSrc κ xL xR ρL ρR r))) := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  have h := tendsto_loewnerGreenEnergy_vApprox (κ := κ) (ρL := ρL) (ρR := ρR) hreg hF hr
    ⟨t.coe_nonneg, by exact_mod_cast htT⟩ hn
  simp only [Coupling.loewnerGreenEnergy_clampDrv_of_le htT₂] at h
  exact h

/-- **The energy identity along a good path** at every `t ≤ S`: `E_t(v) = ‖f‖²_∇ − ∫₀ᵗ A²`. -/
theorem loewnerGreenEnergy_vSrc_eq_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) :
    loewnerGreenEnergy (Ito.rpath w) t (vSrc κ xL xR ρL ρR r) =
      srcNorm κ xL xR ρL ρR r - ∫ u in (0 : ℝ)..t, srcDrift κ xL xR ρL ρR r (Ito.rpath w) u ^ 2 := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  have h := loewnerGreenEnergy_vSrc_eq (κ := κ) (ρL := ρL) (ρR := ρR) hreg hF hr
    ⟨t.coe_nonneg, by exact_mod_cast htT⟩
  rw [Coupling.loewnerGreenEnergy_clampDrv_of_le htT₂] at h
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le t.coe_nonneg] at hu
  simp only [srcDrift_clampDrv (hu.2.trans htT₂)]

/-- The supports of the approximations avoid the hull at every `t ≤ S` along a good path. -/
theorem disjoint_tsupport_vApprox_fwdHull (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) (n : ℕ) :
    Disjoint (tsupport (vApprox κ xL xR ρL ρR r n)) (fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  have hp' := hp.isSLEPathUpTo le_rfl
  have htζ : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt ht (localStopPath_lt hp hF hr hseed hterm)
  exact disjoint_tsupport_vApprox hF hr n
    (fwdHull_subset_closedBall_of_le_localStopPath hp'.continuousOn_w hp'.w_zero hr.1 ht htζ)

end PathLimits

/-! ### The conditional characteristic function of the pairing -/

section Process

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

theorem coe_untopD_le {x y : WithTop ℝ≥0} (hxy : x ≤ y) (hy : y ≠ ⊤) :
    ((x.untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ y := by
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top hy hxy
  lift x to ℝ≥0 using hx
  rw [WithTop.untopD_coe]; exact hxy

theorem coe_untopD_le_localStopPath {x : WithTop ℝ≥0} {ζ' : ℝ≥0∞} {w : ℝ≥0 → ℝ} (hx : x ≤ localStopPath r ζ' w) :
    ((x.untopD 0 : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r ζ' w :=
  coe_untopD_le hx (ne_top_of_le_ne_top WithTop.coe_ne_top localStopPath_le_stopHorizon)

/-- **The conditional law of the pairing with the source before the local stop** (p. 248, (HL4); "The same source
approximation proves (HL4) for `v`"): for a stopping time `τ ≤ S` of the frozen driving filtration and every real `c`,
`E[exp(i c (h, v)) | 𝓖_τ] = exp(i c (𝔥_τ, v) − ½ c² E_τ(v))`. -/
theorem condExp_cexp_srcPair (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) (c : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((c * srcPair κ ρL ρR hF hr (h ω) : ℝ) : ℂ)) | hτ.measurableSpace] =ᵐ[P]
      fun ω => cfVal (c * srcMeanAt κ xL xR ρL ρR r W VL VR ((τ ω).untopD 0) ω)
        (c ^ 2 * srcEnergyAt κ xL xR ρL ρR r W ((τ ω).untopD 0) ω) := by
  obtain ⟨hE, hhm, hgff, hX', hker⟩ := hC
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hgood := ae_isGoodPath hE hκ
  have hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hgood, hτS] with ω hg hτω
    exact lt_of_le_of_lt hτω (localStopPath_lt hg.1 hF hr hseed hg.2)
  obtain ⟨-, hK⟩ := hker τ hτ hτζ
  set u : Ω → ℂ → ℝ := fun ω => bheAt κ ρL ρR
    (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
    (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω) with hu_def
  have hK' := hK u fun ω => isBoundedHarmonicExtension_bheAt κ ρL ρR _ _
  have hY := hgff (bheAt κ ρL ρR xL xR) (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR)
  obtain ⟨C0, hC0⟩ := (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR).2.1
  have hconv := ae_tendsto_srcPair (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
    (continuousOn_of_isBoundedHarmonicExtension (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR)) hC0 hY
  set φ : ℕ → TestOn upperHalfPlaneOpens := fun k => c • srcTest κ ρL ρR hF hr k with hφ
  have hφapp : ∀ k z, φ k z = c * vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k) z := fun k z => rfl
  have hk : ∀ k, P[fun ω => Complex.exp (Complex.I * (h ω (φ k) : ℂ)) | hτ.measurableSpace] =ᵐ[P]
      fun ω => cfVal (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ k z)
        (loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (φ k)) := by
    intro k
    filter_upwards [hK' (φ k), hgood, hτS] with ω h1 hg hτω
    refine h1 (Disjoint.mono_left ?_ (disjoint_tsupport_vApprox_fwdHull (κ := κ) (ρL := ρL) (ρR := ρR) hg.1 hg.2
      hF hr hseed (coe_untopD_le_localStopPath hτω) (pairSeq κ ρL ρR hF hr k)))
    exact tsupport_smul_subset_right (fun _ => c) (vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k))
  refine ae_condExp_cexp_of_tendsto hτ.measurableSpace_le
    (fun k => ((measurable_pi_apply (φ k)).comp ((LQGMetric.measurable_distEval _).comp hhm)).aemeasurable)
    hk ?_ ?_ ?_
  · filter_upwards [hconv] with ω hω
    have e : ∀ k, h ω (φ k) = c * h ω (srcTest κ ρL ρR hF hr k) := fun k => by
      rw [hφ, map_smul, smul_eq_mul]
    exact (hω.const_mul c).congr fun k => (e k).symm
  · filter_upwards [hgood, hτS] with ω hg hτω
    have e : ∀ k, (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ k z) =
        c * ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z *
          vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k) z := fun k => by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hφapp]
      ring
    simp only [e, srcMeanAt]
    refine Tendsto.const_mul c ?_
    exact tendsto_integral_couplingMean_vApprox_of_isGoodPath hg.1 hg.2 hF hr hseed
      (coe_untopD_le_localStopPath hτω) (isBoundedHarmonicExtension_bheAt κ ρL ρR _ _) (tendsto_pairSeq hF hr)
  · filter_upwards [hgood, hτS] with ω hg hτω
    have e : ∀ k, loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (φ k) =
        c ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
          (vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr k)) := fun k => by
      rw [← Coupling.MartMeans.loewnerGreenEnergy_smul]
      rfl
    simp only [e, srcEnergyAt]
    refine Tendsto.const_mul _ ?_
    exact tendsto_loewnerGreenEnergy_vApprox_of_isGoodPath hg.1 hg.2 hF hr hseed
      (coe_untopD_le_localStopPath hτω) (tendsto_pairSeq hF hr)

end Process

/-! ### The Cameron–Martin density and its conditional expectations (HL3)–(HL4) -/

section Density

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

/-- `(𝔥₀, v) = ∫ 𝔥₀ v`: the initial mean paired with the source. -/
def srcCentre (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) : ℝ :=
  ∫ z, bheAt κ ρL ρR xL xR z * vSrc κ xL xR ρL ρR r z

variable (κ ρL ρR) in
/-- **The Cameron–Martin density (HL3)** as a Borel function of the field:
`Z = exp(−(h − 𝔥₀, v) − ½ ‖f‖²_∇)` (`(h, v) = srcPair`, `‖f‖²_∇ = srcNorm`). -/
def srcDensity (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (T : DistOn upperHalfPlaneOpens) : ℝ :=
  Real.exp (-(srcPair κ ρL ρR hF hr T - srcCentre κ xL xR ρL ρR r) - srcNorm κ xL xR ρL ρR r / 2)

theorem srcDensity_pos (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (T : DistOn upperHalfPlaneOpens) :
    0 < srcDensity κ ρL ρR hF hr T := Real.exp_pos _

theorem measurable_srcDensity (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Measurable (srcDensity κ ρL ρR hF hr) :=
  Real.measurable_exp.comp (((measurable_srcPair hF hr).sub_const _).neg.sub_const _)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The density martingale (HL4)** along the path of `ω` at time `t`:
`N_t = exp(−((𝔥_t, v) − (𝔥₀, v)) − ½ ∫₀ᵗ A(u)² du)`, `A = srcDrift`. -/
def srcMart (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(srcMeanAt κ xL xR ρL ρR r W VL VR t ω - srcCentre κ xL xR ρL ρR r) -
    (∫ u in (0 : ℝ)..t, srcDrift κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) u ^ 2) / 2)

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The first line of (HL4)** in integrated form: for a stopping time `τ ≤ S` of the frozen driving filtration and
every event `A ∈ 𝓖_τ`, `E[Z; A] = E[N_τ; A]`. -/
theorem setLIntegral_srcDensity (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) {A : Set Ω}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ∫⁻ ω in A, ENNReal.ofReal (srcDensity κ ρL ρR hF hr (h ω)) ∂P =
      ∫⁻ ω in A, ENNReal.ofReal (srcMart κ xL xR ρL ρR r W VL VR ((τ ω).untopD 0) ω) ∂P := by
  have hP : IsProbabilityMeasure P := hC.1.1.isProbabilityMeasure'
  have hcf := condExp_cexp_srcPair hκ hC hF hr hseed hX hτ hτS
  have hXm : Measurable fun ω => srcPair κ ρL ρR hF hr (h ω) := (measurable_srcPair hF hr).comp hC.2.1
  set k := Real.exp (srcCentre κ xL xR ρL ρR r - srcNorm κ xL xR ρL ρR r / 2) with hk
  have hW : Measurable[hτ.measurableSpace] (A.indicator fun _ => ENNReal.ofReal k) :=
    measurable_const.indicator hA
  have key := lintegral_mul_exp_of_condGauss hτ.measurableSpace_le hXm hcf hW (-1)
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  rw [← lintegral_indicator hAm, ← lintegral_indicator hAm]
  have e1 : ∀ ω, A.indicator (fun _ => ENNReal.ofReal k) ω *
      ENNReal.ofReal (Real.exp (-1 * srcPair κ ρL ρR hF hr (h ω))) =
      A.indicator (fun ω => ENNReal.ofReal (srcDensity κ ρL ρR hF hr (h ω))) ω := fun ω => by
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, srcDensity]
      congr 2; ring
    · simp [Set.indicator_of_notMem hω]
  simp only [e1] at key
  rw [key]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_isGoodPath hC.1 hκ, hτS] with ω hg hτω
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, srcMart]
    have hE := loewnerGreenEnergy_vSrc_eq_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) hg.1 hg.2 hF hr hseed
      (coe_untopD_le_localStopPath hτω)
    simp only [srcEnergyAt]
    rw [show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl, hE]
    congr 2
    ring
  · simp [Set.indicator_of_notMem hω]

/-- At time `0` the density martingale is `1` along every good path. -/
theorem srcMart_zero_of_isGoodPath {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    srcMart κ xL xR ρL ρR r W VL VR 0 ω = 1 := by
  have hp := hg.isSLEPathUpTo
  have hw0 : W 0 ω = 0 := hp.w_zero
  have hm : srcMeanAt κ xL xR ρL ρR r W VL VR 0 ω = srcCentre κ xL xR ρL ρR r := by
    unfold srcMeanAt srcCentre
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : vSrc κ xL xR ρL ρR r z = 0
    · simp [hz]
    have hz0 : z ≠ 0 := fun h0 => by
      have := (mem_srcSet_of_vSrc_ne_zero hF hr hz).2.1
      rw [h0, norm_zero] at this
      linarith [hr.1]
    have hvL : (fun i => VL i 0 ω - W 0 ω) = xL := funext fun i => by rw [hp.vL_zero i, hw0, sub_zero]
    have hvR : (fun i => VR i 0 ω - W 0 ω) = xR := funext fun i => by rw [hp.vR_zero i, hw0, sub_zero]
    simp only [NNReal.coe_zero]
    rw [Coupling.MartMeans2.couplingMean_zero κ (by simpa using hw0) _ hz0, hvL, hvR]
  rw [srcMart, hm, sub_self, neg_zero, NNReal.coe_zero, intervalIntegral.integral_same, zero_div, sub_zero,
    Real.exp_zero]

/-- **`E Z = 1`.** -/
theorem lintegral_srcDensity (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∫⁻ ω, ENNReal.ofReal (srcDensity κ ρL ρR hF hr (h ω)) ∂P = 1 := by
  have hP : IsProbabilityMeasure P := hC.1.1.isProbabilityMeasure'
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hτ : IsStoppingTime (drivingFiltration P hX) fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0) :=
    isStoppingTime_const _ _
  have hset := setLIntegral_srcDensity hκ hC hF hr hseed hX hτ (ae_of_all _ fun ω => by simp)
    (MeasurableSet.univ (m := hτ.measurableSpace))
  simp only [Measure.restrict_univ] at hset
  rw [hset]
  calc ∫⁻ ω, ENNReal.ofReal (srcMart κ xL xR ρL ρR r W VL VR (((0 : ℝ≥0) : WithTop ℝ≥0).untopD 0) ω) ∂P
      = ∫⁻ _, 1 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_isGoodPath hC.1 hκ] with ω hg
        rw [WithTop.untopD_coe, srcMart_zero_of_isGoodPath hg hF hr, ENNReal.ofReal_one]
    _ = 1 := by rw [lintegral_const, measure_univ, one_mul]

variable (κ ρL ρR) in
/-- **The Cameron–Martin measure** `Q = Z · P` of (HL3). -/
def srcMeasure (P : Measure Ω) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (h : Ω → DistOn upperHalfPlaneOpens) : Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (srcDensity κ ρL ρR hF hr (h ω))

theorem isProbabilityMeasure_srcMeasure (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    IsProbabilityMeasure (srcMeasure κ ρL ρR P hF hr h) :=
  ⟨by rw [srcMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_srcDensity hκ hC hF hr hseed]⟩

theorem srcMeasure_absolutelyContinuous (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    srcMeasure κ ρL ρR P hF hr h ≪ P :=
  withDensity_absolutelyContinuous _ _

theorem absolutelyContinuous_srcMeasure (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    P ≪ srcMeasure κ ρL ρR P hF hr h :=
  withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp ((measurable_srcDensity hF hr).comp
    hC.2.1)).aemeasurable (ae_of_all _ fun ω => by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact srcDensity_pos hF hr _)

/-- **`Q = N_τ · P` on `𝓖_τ`** for every stopping time `τ ≤ S` of the frozen driving filtration. -/
theorem srcMeasure_apply_of_measurableSet (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    srcMeasure κ ρL ρR P hF hr h A =
      ∫⁻ ω in A, ENNReal.ofReal (srcMart κ xL xR ρL ρR r W VL VR ((τ ω).untopD 0) ω) ∂P := by
  rw [srcMeasure, withDensity_apply _ (hτ.measurableSpace_le _ hA),
    setLIntegral_srcDensity hκ hC hF hr hseed hX hτ hτS hA]

end Density

end LocalExt

end InteractingSLE
