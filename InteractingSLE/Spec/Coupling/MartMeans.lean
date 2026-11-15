/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.MartMeansCond
import InteractingSLE.Spec.Coupling.MartMeansPath
import InteractingSLE.Spec.Coupling.Assembly11Drv
import InteractingSLE.Spec.Sec7.Lemma71Reduce
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling

/-!
# The coupling specification gives martingale means (forward direction, generic)

Packet PROVE-CPL-MART (`planning/handoffs/PROVE-LEMMA71.md` item 3; Specification p. 225, proof of Lemma 7.1: "The
joint pair with `h_ψ` has the original coupling specification"). Suppose a random distribution `h` on `ℍ` is coupled
with a driving process `(W, V^L, V^R)` so that the conditional-law clause of the optional hull specification holds
(`IsCouplingCharFun`, the last conjunct of the frozen `IsOptionalHullCoupling` without locality, for an arbitrary
filtration): for every stopping time `τ`, almost surely on `{supp φ ∩ K_τ = ∅}`,

  `E[exp(i (h, φ)) | 𝓖_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))`.

Then the coupling means are local martingales before swallowing: for every `z ∈ ℍ`, `t ↦ 𝔥_t(z)` is a local
martingale before the swallowing time of `z`, localized at the times `locTime z n` at which the hull reaches the
ball `B̄(z, Im z/(n+2))` at level `(Im z/2)/(n+1)` (`isLocalMartingaleBefore_couplingMean_of_charFun`). This is the
hypothesis of Theorem 2.4's converse (`MartChar.isFilteredBrownianReal_of_couplingMean`) and of Lemma 7.1's reduction
(`hasTwoSeedMartingaleMeans_of_charFun`).

Proof, for the `n`-th localizing time `σ_n` and the bump `φ_n` of radius `Im z/(2(n+2))` at `z`:

* **mean value**: up to `σ_n` the closed ball `B̄(z, Im z/(n+2))` is outside the hull, the coupling mean is the
  explicit harmonic function `meanCan` there, and `𝔥_s(z) = (𝔥_s, φ_n)/∫ φ_n` (`IsSafeAt.integral_meanCan_mul_bumpFun`);
* **conditional mean**: the clause at `σ_n ∧ t`, applied to the multiples `c φ_n`, is a Gaussian conditional
  characteristic function, so `(𝔥_{σ_n∧t}, φ_n) = E[(h, φ_n) | 𝓖_{σ_n∧t}]` (`condExp_ae_eq_of_condCharFun`; this needs
  `(h, φ_n)` integrable);
* **martingale**: conditional means at `σ_n ∧ t` of one integrable variable form a martingale
  (`martingale_of_ae_eq_condExp_min_const`), adapted by `measurable_stoppedPair`.

## Main results

* `IsCouplingCharFun`: the conditional-law clause, for a filtration `𝓖` and a lifetime `ζ`;
* `IsOptionalHullCoupling.exists_isCouplingCharFun`: the frozen specification satisfies it for the driving filtration;
* **`isLocalMartingaleBefore_couplingMean_of_charFun`**: the coupling means are local martingales before swallowing;
* `hasTwoSeedMartingaleMeans_of_charFun`: the martingale clause `HasTwoSeedMartingaleMeans` of Lemma 7.1's reduction.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Complex Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

namespace MartMeans

open Ito

variable {nL nR : ℕ}

/-! ### The conditional-law clause -/

/-- **The conditional-law clause of the optional hull specification** (the last conjunct of the frozen
`IsOptionalHullCoupling`, without the locality of `K_τ`), for a filtration `𝓖` and a lifetime `ζ`: for every stopping
time `τ < ζ` of `𝓖`, every choice `u` of the bounded harmonic extensions of the force-word data at the centred
positions at `τ`, and every test function `φ`, almost surely on `{supp φ ∩ K_τ = ∅}`,
`E[e^{i (h, φ)} | 𝓖_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))`. -/
def IsCouplingCharFun (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓖 τ), (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
    ∀ u : Ω → ℂ → ℝ,
      (∀ ω, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
            (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
          (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
            (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
          (u ω)) →
      ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
        Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0)) →
          condExp hτ.measurableSpace P
              (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
            Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
                ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
                ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ))

/-- **The frozen optional hull specification satisfies the conditional-law clause** for its driving filtration. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.exists_isCouplingCharFun {κ : ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ hX : IsMeasurableKilledDriving W VL VR ζ,
      IsCouplingCharFun κ ρL ρR P (drivingFiltration P hX) W VL VR ζ h := by
  obtain ⟨-, -, -, hX, hcl⟩ := hC
  exact ⟨hX, fun τ hτ hζ u hu φ => (hcl τ hτ hζ).2 u hu φ⟩

/-! ### Scaling the test function -/

theorem loewnerGreenEnergy_smul (w : ℝ → ℝ) (t c : ℝ) (φ : ℂ → ℝ) :
    loewnerGreenEnergy w t (c • φ) = c ^ 2 * loewnerGreenEnergy w t φ := by
  simp only [loewnerGreenEnergy, Pi.smul_apply, smul_eq_mul]
  have e : ∀ y z, c * φ y * greenH (fwdMap w t y) (fwdMap w t z) * (c * φ z) =
      c ^ 2 * (φ y * greenH (fwdMap w t y) (fwdMap w t z) * φ z) := fun y z => by ring
  simp_rw [e, integral_const_mul]

theorem integral_mul_smul (g : ℂ → ℝ) (c : ℝ) (φ : ℂ → ℝ) :
    ∫ z, g z * (c • φ) z = c * ∫ z, g z * φ z := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext z; ring

/-! ### The mean at the point is the normalized bump pairing up to the localizing time -/

section Path

variable {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin nR → ℝ≥0 → ℝ} {z : ℂ}

/-- The radius `Im z/(2(n+2))` of the `n`-th bump at `z`. -/
def bumpRadius (z : ℂ) (n : ℕ) : ℝ := locRad z n / 2

/-- The mass `ε² ∫ e(1 − |y|²)` of the `n`-th bump at `z`. -/
def bumpNorm (z : ℂ) (n : ℕ) : ℝ := bumpRadius z n ^ 2 * GFF.bumpMass

theorem bumpRadius_pos (hz : 0 < z.im) (n : ℕ) : 0 < bumpRadius z n := by
  unfold bumpRadius; have := locRad_pos hz n; positivity

theorem bumpRadius_le (hz : 0 < z.im) (n : ℕ) : bumpRadius z n ≤ locRad z n := by
  unfold bumpRadius; have := locRad_pos hz n; linarith

theorem bumpNorm_pos (hz : 0 < z.im) (n : ℕ) : 0 < bumpNorm z n := by
  unfold bumpNorm; have := bumpRadius_pos hz n; have := GFF.bumpMass_pos; positivity

theorem tsupport_bumpFun_subset_locBall (hz : 0 < z.im) (n : ℕ) :
    tsupport (GFF.bumpFun z (bumpRadius z n)) ⊆ closedBall z (locRad z n) :=
  (GFF.tsupport_bumpFun_subset (bumpRadius_pos hz n)).trans
    (closedBall_subset_closedBall (bumpRadius_le hz n))

section Safe

variable {ζ : ℝ≥0∞} {N : ℝ} {σ₀ r : ℝ≥0}

/-- While the localizing ball is safe, it is outside the hull of the driver. -/
theorem disjoint_locBall_fwdHull_of_safe (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hz : 0 < z.im)
    (n : ℕ) (hsafe : IsSafeAt (closedBall z (locRad z n)) (locLevel z n) N σ₀ ζ w r) {s : ℝ≥0}
    (hs : s ≤ r) : Disjoint (closedBall z (locRad z n)) (fwdHull (rpath w) s) := by
  refine Set.disjoint_left.2 fun y hy => ?_
  exact notMem_fwdHull_of_alive hw (lt_of_le_of_lt (by exact_mod_cast hs) hsafe.1)
    (closedBall_locRad_subset hz n hy) (hsafe.alive (closedBall_locRad_subset hz n) hw hs hy)

/-- While the localizing ball is safe, the coupling mean is the explicit mean on it. -/
theorem couplingMean_eq_meanCan_of_safe (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hz : 0 < z.im)
    (n : ℕ) (hsafe : IsSafeAt (closedBall z (locRad z n)) (locLevel z n) N σ₀ ζ w r) {s : ℝ≥0}
    (hs : s ≤ r) (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s))
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) {y : ℂ}
    (hy : y ∈ closedBall z (locRad z n)) :
    couplingMean κ (rpath w) s u y = meanCan κ ρL ρR w vL vR s y :=
  couplingMean_eq_meanCan hw (closedBall_locRad_subset hz n) hsafe (locLevel_pos hz n) hs hy hvL hvR hu

/-- While the localizing ball is safe, the explicit mean at `z` is its normalized bump pairing. -/
theorem meanCan_eq_integral_div_of_safe (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hz : 0 < z.im)
    (n : ℕ) (hsafe : IsSafeAt (closedBall z (locRad z n)) (locLevel z n) N σ₀ ζ w r) {s : ℝ≥0}
    (hs : s ≤ r) :
    meanCan κ ρL ρR w vL vR s z =
      (∫ y, meanCan κ ρL ρR w vL vR s y * GFF.bumpFun z (bumpRadius z n) y) / bumpNorm z n := by
  rw [hsafe.integral_meanCan_mul_bumpFun hw (closedBall_locRad_subset hz n) hs (bumpRadius_pos hz n)
    (bumpRadius_le hz n)]
  exact (mul_div_cancel_right₀ _ (bumpNorm_pos hz n).ne').symm

/-- While the localizing ball is safe, the bump pairings of the coupling mean and of the explicit mean agree. -/
theorem integral_couplingMean_mul_bumpFun_of_safe (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hz : 0 < z.im) (n : ℕ) (hsafe : IsSafeAt (closedBall z (locRad z n)) (locLevel z n) N σ₀ ζ w r)
    {s : ℝ≥0} (hs : s ≤ r) (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s))
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) :
    ∫ y, couplingMean κ (rpath w) s u y * GFF.bumpFun z (bumpRadius z n) y =
      ∫ y, meanCan κ ρL ρR w vL vR s y * GFF.bumpFun z (bumpRadius z n) y := by
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  by_cases hy : y ∈ closedBall z (locRad z n)
  · rw [couplingMean_eq_meanCan_of_safe hw hz n hsafe hs hvL hvR hu hy]
  · have h0 : GFF.bumpFun z (bumpRadius z n) y = 0 := by
      refine GFF.bumpFun_eq_zero (bumpRadius_pos hz n) ?_
      rw [mem_closedBall, not_le] at hy
      exact (bumpRadius_le hz n).trans hy.le
    simp only [h0, mul_zero]

end Safe

/-- Up to the localizing time, the localizing ball is outside the hull of the driver. -/
theorem disjoint_locBall_fwdHull (hw : Continuous w) (hw0 : w 0 = 0) (hz : 0 < z.im) (n : ℕ) {s : ℝ≥0}
    (hs : s ≤ locTime z n w) : Disjoint (closedBall z (locRad z n)) (fwdHull (rpath w) s) :=
  disjoint_locBall_fwdHull_of_safe hw.continuousOn hz n (isSafeAt_locTime hw hw0 hz n) hs

/-- **Up to the localizing time, the coupling mean at `z` is the explicit mean.** -/
theorem couplingMean_eq_meanCan_of_le_locTime (hw : Continuous w) (hw0 : w 0 = 0) (hz : 0 < z.im) (n : ℕ)
    {s : ℝ≥0} (hs : s ≤ locTime z n w) (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s))
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) {y : ℂ}
    (hy : y ∈ closedBall z (locRad z n)) :
    couplingMean κ (rpath w) s u y = meanCan κ ρL ρR w vL vR s y :=
  couplingMean_eq_meanCan_of_safe hw.continuousOn hz n (isSafeAt_locTime hw hw0 hz n) hs hvL hvR hu hy

theorem meanCan_eq_integral_div (hw : Continuous w) (hw0 : w 0 = 0) (hz : 0 < z.im) (n : ℕ) {s : ℝ≥0}
    (hs : s ≤ locTime z n w) :
    meanCan κ ρL ρR w vL vR s z =
      (∫ y, meanCan κ ρL ρR w vL vR s y * GFF.bumpFun z (bumpRadius z n) y) / bumpNorm z n :=
  meanCan_eq_integral_div_of_safe hw.continuousOn hz n (isSafeAt_locTime hw hw0 hz n) hs

theorem integral_couplingMean_mul_bumpFun (hw : Continuous w) (hw0 : w 0 = 0) (hz : 0 < z.im) (n : ℕ)
    {s : ℝ≥0} (hs : s ≤ locTime z n w) (hvL : ∀ i, vL i s ≤ w s) (hvR : ∀ i, w s ≤ vR i s) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i s - w s) (fun i => vR i s - w s))
      (forceJumpSet (fun i => vL i s - w s) (fun i => vR i s - w s)) u) :
    ∫ y, couplingMean κ (rpath w) s u y * GFF.bumpFun z (bumpRadius z n) y =
      ∫ y, meanCan κ ρL ρR w vL vR s y * GFF.bumpFun z (bumpRadius z n) y :=
  integral_couplingMean_mul_bumpFun_of_safe hw.continuousOn hz n (isSafeAt_locTime hw hw0 hz n) hs hvL hvR hu

end Path

/-! ### The coupling means are local martingales -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

theorem stoppedProcess_coe_apply {X : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ≥0} (t : ℝ≥0) (ω : Ω) :
    stoppedProcess X (fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) t ω = X (min t (σ ω)) ω := by
  simp only [stoppedProcess, ← WithTop.coe_min]
  rfl

/-- The `n`-th bump at `z` as a test function on `ℍ`. -/
def bumpTestAt (z : ℂ) (hz : 0 < z.im) (n : ℕ) : LQGMetric.TestOn upperHalfPlaneOpens :=
  GFF.bumpTest z (bumpRadius_pos hz n)
    ((closedBall_subset_closedBall (bumpRadius_le hz n)).trans (closedBall_locRad_subset hz n))

theorem coe_bumpTestAt {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    ⇑(bumpTestAt z hz n) = GFF.bumpFun z (bumpRadius z n) := rfl

/-- The coupling-mean process `t ↦ 𝔥_t(z)` (frozen `couplingMean`, bounded harmonic extensions `u ω t`). -/
def meanProc (κ : ℝ) (W : ℝ≥0 → Ω → ℝ) (u : Ω → ℝ≥0 → ℂ → ℝ) (z : ℂ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z

/-- The `n`-th localizing stopping time of `z` along the driver `W`. -/
def locStop (z : ℂ) (n : ℕ) (W : ℝ≥0 → Ω → ℝ) : Ω → WithTop ℝ≥0 :=
  fun ω => ((locTime z n (W · ω) : ℝ≥0) : WithTop ℝ≥0)

/-- **The coupling mean of `z`, stopped at the `n`-th localizing time, is a martingale.** -/
theorem martingale_stoppedProcess_meanProc [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ i ω, Continuous fun t => VR i t ω)
    (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓖 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hint : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR (fun _ => ⊤) h) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t))
    {z : ℂ} (hz : 0 < z.im) (n : ℕ) :
    Martingale (stoppedProcess (meanProc κ W u z) (locStop z n W)) 𝓖 P := by
  have hσst : IsStoppingTime 𝓖 (locStop z n W) := isStoppingTime_locTime hWa hWc hz n
  have hC0 : 0 < bumpNorm z n := bumpNorm_pos hz n
  -- the stopped process is the normalized tested explicit mean
  have hval : ∀ t ω, stoppedProcess (meanProc κ W u z) (locStop z n W) t ω =
      (∫ y, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
        (min (locTime z n (W · ω)) t) y * GFF.bumpFun z (bumpRadius z n) y) / bumpNorm z n := by
    intro t ω
    rw [show locStop z n W = fun ω => ((locTime z n (W · ω) : ℝ≥0) : WithTop ℝ≥0) from rfl,
      stoppedProcess_coe_apply (σ := fun ω => locTime z n (W · ω)) t ω, min_comm]
    have hs : min (locTime z n (W · ω)) t ≤ locTime z n (W · ω) := min_le_left _ _
    have e1 : meanProc κ W u z (min (locTime z n (W · ω)) t) ω =
        couplingMean κ (rpath (W · ω)) (min (locTime z n (W · ω)) t : ℝ≥0)
          (u ω (min (locTime z n (W · ω)) t)) z := rfl
    rw [e1, couplingMean_eq_meanCan_of_le_locTime (ρL := ρL) (ρR := ρR) (vL := fun i t => VL i t ω)
      (vR := fun i t => VR i t ω) (hWc ω) (hW0 ω) hz n hs (fun i => hordL ω _ i)
      (fun i => hordR ω _ i) (hu ω (min (locTime z n (W · ω)) t))
      (mem_closedBall_self (locRad_pos hz n).le)]
    exact meanCan_eq_integral_div (hWc ω) (hW0 ω) hz n hs
  -- adaptedness
  have hadapt : StronglyAdapted 𝓖 (stoppedProcess (meanProc κ W u z) (locStop z n W)) := by
    intro t
    have hρt : IsStoppingTime 𝓖 fun ω => ((min (locTime z n (W · ω)) t : ℝ≥0) : WithTop ℝ≥0) := by
      have h1 := hσst.min_const t
      have e : (fun ω => min (locStop z n W ω) (t : WithTop ℝ≥0)) =
          fun ω => ((min (locTime z n (W · ω)) t : ℝ≥0) : WithTop ℝ≥0) := by
        funext ω; rw [WithTop.coe_min]; rfl
      rw [e] at h1
      exact h1
    have hm := measurable_stoppedPair (κ := κ) (ρL := ρL) (ρR := ρR) (W := W) (VL := VL) (VR := VR)
      (ζ := fun _ => ⊤) (G := univ) (φ := GFF.bumpFun z (bumpRadius z n)) (δ := locLevel z n)
      (adaptedBefore_top_of_stronglyAdapted hWa)
      (fun i => adaptedBefore_top_of_stronglyAdapted (hVLa i))
      (fun i => adaptedBefore_top_of_stronglyAdapted (hVRa i)) (fun ω _ => (hWc ω).continuousOn)
      (fun ω _ => ⟨fun i => (hVLc i ω).continuousOn, fun i => (hVRc i ω).continuousOn⟩)
      MeasurableSet.univ (GFF.contDiff_bumpFun z _).continuous
      (GFF.hasCompactSupport_bumpFun (bumpRadius_pos hz n))
      ((tsupport_bumpFun_subset_locBall hz n).trans (closedBall_locRad_subset hz n))
      (locLevel_pos hz n) hρt (N := n) (σ₀ := fun _ => (n : ℝ≥0))
      (fun ω _ => ((isSafeAt_locTime (hWc ω) (hW0 ω) hz n).anti (hWc ω).continuousOn
        (closedBall_locRad_subset hz n) (min_le_left _ _)).subset (tsupport_bumpFun_subset_locBall hz n))
    have h3 := (measurable_fst.comp hm).mono
      (hρt.measurableSpace_le_of_le_const fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)) le_rfl
    simp only [mem_univ, ↓reduceIte, Function.comp_def] at h3
    rw [funext (hval t)]
    exact (h3.div_const _).stronglyMeasurable
  -- conditional means at `σ_n ∧ t`
  have hcond : ∀ t, stoppedProcess (meanProc κ W u z) (locStop z n W) t =ᵐ[P]
      P[fun ω => h ω (bumpTestAt z hz n) / bumpNorm z n | (hσst.min_const t).measurableSpace] := by
    intro t
    have hτu : ∀ ω, (min (locStop z n W ω) (t : WithTop ℝ≥0)).untopD 0 =
        min (locTime z n (W · ω)) t := fun ω => by
      rw [show locStop z n W ω = ((locTime z n (W · ω) : ℝ≥0) : WithTop ℝ≥0) from rfl,
        ← WithTop.coe_min, WithTop.untopD_coe]
    have key : ∀ c : ℝ, P[fun ω => cexp (I * ((c * h ω (bumpTestAt z hz n) : ℝ) : ℂ)) |
        (hσst.min_const t).measurableSpace] =ᵐ[P] fun ω => cexp (I * ((c *
          (∫ y, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min (locTime z n (W · ω)) t : ℝ≥0)
            (u ω (min (locTime z n (W · ω)) t)) y * GFF.bumpFun z (bumpRadius z n) y) : ℝ) : ℂ) -
          (((1 / 2) * (c ^ 2 * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
            (min (locTime z n (W · ω)) t : ℝ≥0) (GFF.bumpFun z (bumpRadius z n))) : ℝ) : ℂ)) := by
      intro c
      have hlt : ∀ᵐ ω ∂P, ((min (locStop z n W ω) (t : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) <
          (fun _ : Ω => (⊤ : ℝ≥0∞)) ω := ae_of_all _ fun ω =>
        lt_of_le_of_lt (min_le_right _ _) (WithTop.coe_lt_top t)
      have hcl := hcf (fun ω => min (locStop z n W ω) (t : WithTop ℝ≥0)) (hσst.min_const t) hlt
        (fun ω => u ω ((min (locStop z n W ω) (t : WithTop ℝ≥0)).untopD 0)) (fun ω => hu ω _)
        (c • bumpTestAt z hz n)
      simp only [hτu] at hcl
      have e1 : (fun ω' => cexp (I * ((h ω' (c • bumpTestAt z hz n) : ℝ) : ℂ))) =
          fun ω' => cexp (I * ((c * h ω' (bumpTestAt z hz n) : ℝ) : ℂ)) := by
        funext ω'; simp
      rw [e1] at hcl
      filter_upwards [hcl] with ω hω
      have hcoe : (⇑(c • bumpTestAt z hz n) : ℂ → ℝ) = c • GFF.bumpFun z (bumpRadius z n) := by
        funext y; simp [coe_bumpTestAt]
      have hdisj : Disjoint (tsupport ⇑(c • bumpTestAt z hz n))
          (fwdHull (fun s : ℝ => W s.toNNReal ω) (min (locTime z n (W · ω)) t : ℝ≥0)) := by
        refine Disjoint.mono_left ?_ (disjoint_locBall_fwdHull (hWc ω) (hW0 ω) hz n (min_le_left _ _))
        rw [hcoe]
        exact (tsupport_smul_subset_right (fun _ : ℂ => c) (GFF.bumpFun z (bumpRadius z n))).trans
          (tsupport_bumpFun_subset_locBall hz n)
      rw [hω hdisj, hcoe, integral_mul_smul, loewnerGreenEnergy_smul]
    have hA := condExp_ae_eq_of_condCharFun (hint (bumpTestAt z hz n)) key
    have hs := condExp_smul (μ := P) (bumpNorm z n)⁻¹ (fun ω => h ω (bumpTestAt z hz n))
      (hσst.min_const t).measurableSpace
    have e2 : (fun ω => h ω (bumpTestAt z hz n) / bumpNorm z n) =
        (bumpNorm z n)⁻¹ • fun ω => h ω (bumpTestAt z hz n) := by
      funext ω; simp [div_eq_inv_mul]
    rw [e2]
    filter_upwards [hA, hs] with ω h1 h2
    rw [h2, Pi.smul_apply, h1, hval t ω, smul_eq_mul]
    have h4 := integral_couplingMean_mul_bumpFun (κ := κ) (ρL := ρL) (ρR := ρR)
      (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) (hWc ω) (hW0 ω) hz n
      (min_le_left (locTime z n (W · ω)) t) (fun i => hordL ω _ i) (fun i => hordR ω _ i)
      (hu ω (min (locTime z n (W · ω)) t))
    rw [show (fun s : ℝ => W s.toNNReal ω) = rpath (W · ω) from rfl, h4, div_eq_inv_mul]
  exact martingale_of_ae_eq_condExp_min_const hσst ((hint _).div_const _) hadapt hcond

/-- **The coupling specification gives martingale means.** Let `(W, V^L, V^R)` be continuous adapted driving
coordinates of a right-continuous filtration `𝓖` (`W₀ = 0`, `V^L ≤ W ≤ V^R`), and let the random distribution `h` on
`ℍ` have integrable pairings and satisfy the conditional-law clause of the optional hull specification at every
stopping time (`IsCouplingCharFun` with lifetime `∞`). Then for every choice `u` of the bounded harmonic extensions
and every `z ∈ ℍ`, the coupling mean `t ↦ 𝔥_t(z)` is a local martingale before `z` is swallowed, localized at the
times `locTime z n` at which the hull reaches the ball `B̄(z, Im z/(n+2))`. -/
theorem isLocalMartingaleBefore_couplingMean_of_charFun [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ i ω, Continuous fun t => VR i t ω)
    (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓖 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hint : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR (fun _ => ⊤) h) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t))
    {z : ℂ} (hz : z ∈ H) :
    MartChar.IsLocalMartingaleBefore 𝓖 P
      (fun ω => (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0))
      (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z) := by
  have hz' : 0 < z.im := hz
  refine ⟨fun n => locStop z n W, fun n => isStoppingTime_locTime hWa hWc hz' n, fun n ω => ?_,
    ae_of_all _ fun ω r hr => ?_, fun n => martingale_stoppedProcess_meanProc hW0 hWc hWa hVLc hVRc
      hVLa hVRa hordL hordR hint hcf u hu hz' n⟩
  · exact locTime_le_swallowTime (hWc ω) (hW0 ω) hz' n
  · exact (eventually_lt_locTime (hWc ω) hz' hr).mono fun n hn => WithTop.coe_lt_coe.2 hn

end Main

/-! ### Lemma 7.1's martingale clause -/

section TwoSeed

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

theorem geomL_le (hWc : ∀ ω, Continuous fun t => W t ω) (xL : Fin nL → ℝ) (ω : Ω) (t : ℝ≥0)
    (i : Fin nL) : MartChar.geomL W xL i t ω ≤ W t ω := by
  have hw' : Continuous (Bessel.realPath (fun t ω => -W t ω) ω) :=
    Bessel.continuous_realPath (fun ω => (hWc ω).neg) ω
  have h := MartChar.RealFlow.le_rightImg hw' (-xL i) t.coe_nonneg
  rw [MartChar.realPath_coe] at h
  simp only [MartChar.geomL]
  linarith

theorem le_geomR (hWc : ∀ ω, Continuous fun t => W t ω) (xR : Fin nR → ℝ) (ω : Ω) (t : ℝ≥0)
    (i : Fin nR) : W t ω ≤ MartChar.geomR W xR i t ω := by
  have h := MartChar.RealFlow.le_rightImg (Bessel.continuous_realPath hWc ω) (xR i) t.coe_nonneg
  rw [MartChar.realPath_coe] at h
  exact h

/-- **The martingale clause of Lemma 7.1's reduction from the coupling specification.** If the mapped driver `W`
(continuous, adapted to a right-continuous filtration, `W₀ = 0`) is coupled with a random distribution `h` on `ℍ` with
integrable pairings so that the conditional-law clause of the optional hull specification holds for the two-seed word
`(0⁻; 0⁺)` with weights `(rL; rR)` and the geometric force points (p. 225: "The joint pair with `h_ψ` has the
original coupling specification"), then its two-seed coupling means are local martingales
(`HasTwoSeedMartingaleMeans`). -/
theorem hasTwoSeedMartingaleMeans_of_charFun [IsProbabilityMeasure P] [𝓖.IsRightContinuous] {κ rL rR : ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    (hint : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P)
    (hcf : IsCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P 𝓖 W
      (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) (fun _ => ⊤) h) :
    Sec7.Lemma71.HasTwoSeedMartingaleMeans κ rL rR P 𝓖 W := fun u hu _ hz =>
  isLocalMartingaleBefore_couplingMean_of_charFun hW0 hWc hWa
    (fun i ω => (MartChar.isForcePath_geomL hWc LP.twoSeedXL ω i).1)
    (fun i ω => (MartChar.isForcePath_geomR hWc LP.twoSeedXR ω i).1)
    (MartChar.stronglyAdapted_geomL hWa hWc LP.twoSeedXL)
    (MartChar.stronglyAdapted_geomR hWa hWc LP.twoSeedXR)
    (fun ω t i => geomL_le hWc LP.twoSeedXL ω t i) (fun ω t i => le_geomR hWc LP.twoSeedXR ω t i)
    hint hcf u hu hz

end TwoSeed

end MartMeans

end Coupling

end InteractingSLE
