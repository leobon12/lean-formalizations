import InteractingSLE.Spec.Ito.Martingale
import InteractingSLE.Spec.Ito.TwoPoint
import InteractingSLE.Spec.Coupling.GreenEnergy
import InteractingSLE.Foundations.Complex.DerivLog
import InteractingSLE.Spec.Coupling.ExpMartingale

/-!
# The tested mean `(𝔥_t, φ)` and its bracket at protected stops ((3.19)–(3.20))

Packet PROVE-T11-L311 (Specification §3.3, L529–L552; graph nodes `SPEC.eq-3.19`, `SPEC.thm-1.1#charfn-martingale`).
Fix an integrated `SLE_κ(ρ)` evolution, a continuous compactly supported `φ` with `supp φ ⊆ ℍ`, and a stopping time
`σ` of the null-augmented filtration that *protects* `supp φ` (`IsTestProtected`): almost surely `σ < ζ`, `σ ≤ N`,
the driving coordinates are bounded by `R` on `[0, σ]`, and every `z ∈ supp φ` is unswallowed at `σ` with
`Im f_σ(z) ≥ δ > 0`. With `𝔥_t(z)` the frozen `couplingMean` and `E_t(φ)` the frozen `loewnerGreenEnergy`:

* `martingale_testMean`: `(𝔥_{t∧σ}, φ) = ∫ 𝔥_{t∧σ}(z) φ(z) dz` agrees a.s. with a martingale (integrated (3.15));
* `martingale_testMean_sq_add_energy`: `(𝔥_{t∧σ}, φ)² + E_{t∧σ}(φ)` agrees a.s. with a martingale ((3.20));
* `loewnerGreenEnergy` along the path is nonincreasing and Lipschitz (`GreenEnergy`).

The proofs integrate PROVE-T11-ITO's one- and two-point martingales ((3.15), (3.17)) against `φ` and `φ ⊗ φ`
(`Fubini.martingale_integral_of_forall`); the two-point martingale needs the separation bound of `Separation`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {φ : ℂ → ℝ} {σ : Ω → ℝ≥0} {δ R N : ℝ}

/-- **Protection of the support of a test function by a stopping time** (Specification L546: "localize so that
`inf_{z ∈ supp φ} Im g_t(z)` is bounded below by a positive constant and the relevant continuous driving quantities
are bounded"): at `ω`, `σ < ζ`, `σ ≤ N`, `|W|, |B|, |V| ≤ R` on `[0, σ]`, and every `z ∈ supp φ` has a forward
solution on `[0, σ]` with `δ ≤ Im f_σ(z)`. -/
def IsTestProtected (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (φ : ℂ → ℝ) (σ : Ω → ℝ≥0) (δ R N : ℝ) (ω : Ω) : Prop :=
  (σ ω : ℝ≥0∞) < ζ ω ∧ (σ ω : ℝ) ≤ N ∧
    (∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R) ∧
    ∀ z ∈ tsupport φ, (∃ u, IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (fwdMap (rpath (W · ω)) (σ ω) z).im

/-- The good event at `ω`: the path properties, a continuous Brownian path, and the protection. -/
def IsGoodTest (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (φ : ℂ → ℝ) (σ : Ω → ℝ≥0) (δ R N : ℝ) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
    (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω) ∧ IsTestProtected W VL VR B ζ φ σ δ R N ω

/-- A measurable good set of full measure, in `𝓖₀` of the null augmentation. -/
theorem exists_goodSet (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hσp : ∀ᵐ ω ∂P, IsTestProtected W VL VR B ζ φ σ δ R N ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ MeasurableSet[nullAugmented 𝓕 P 0] G ∧
      ∀ ω ∈ G, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω := by
  obtain ⟨hB, -, -, -, hpath⟩ := hE
  have hae : ∀ᵐ ω ∂P, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω := by
    filter_upwards [hpath, hB.1.cont, hσp] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  refine ⟨(toMeasurable P {ω | ¬ IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · have h0 : P (toMeasurable P {ω | ¬ IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω}) = 0 := by
      rw [measure_toMeasurable]; exact ae_iff.1 hae
    exact (measurableSet_nullAugmented_of_null (𝓕 := 𝓕) (measurableSet_toMeasurable _ _) h0 0).compl
  · by_contra h; exact hω (subset_toMeasurable _ _ h)

/-! ### The clamped driver of a good path -/

section Clamp

variable {ω : Ω}

/-- The driver of a good path, clamped to `[0, σ]`: a continuous driver with the same flow up to `σ`. -/
def clampPath (W : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (ω : Ω) : ℝ → ℝ :=
  clampDrv (rpath (W · ω)) (σ ω)

theorem IsGoodTest.continuousOn_rpath (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) :
    ContinuousOn (rpath (W · ω)) (Icc 0 (σ ω : ℝ)) :=
  Ito.continuousOn_rpath hg.1.2.2.2.1 hg.2.2.1

theorem IsGoodTest.continuous_clampPath (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) :
    Continuous (clampPath W σ ω) :=
  continuous_clampDrv (σ ω).coe_nonneg hg.continuousOn_rpath

theorem IsGoodTest.isProtected (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω)
    (hφH : tsupport φ ⊆ H) : IsProtected (clampPath W σ ω) (σ ω) δ (tsupport φ) := fun z hz =>
  ⟨mem_diff_fwdHull_clampDrv (σ ω).coe_nonneg hg.continuousOn_rpath (hφH hz) (hg.2.2.2.2.2 z hz).1,
    by rw [clampPath, fwdMap_clampDrv_of_le le_rfl]; exact (hg.2.2.2.2.2 z hz).2⟩

theorem fwdMap_clampPath {r : ℝ} (hr : r ≤ σ ω) :
    fwdMap (clampPath W σ ω) r = fwdMap (rpath (W · ω)) r :=
  funext fun _ => fwdMap_clampDrv_of_le hr

theorem logDerivFwd_clampPath {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ σ ω) :
    logDerivFwd (clampPath W σ ω) r = logDerivFwd (rpath (W · ω)) r :=
  funext fun _ => logDerivFwd_clampDrv_of_le hr0 hr

theorem loewnerGreenEnergy_clampPath {r : ℝ} (hr : r ≤ σ ω) :
    loewnerGreenEnergy (clampPath W σ ω) r φ = loewnerGreenEnergy (rpath (W · ω)) r φ := by
  simp only [loewnerGreenEnergy, fwdMap_clampPath hr]

end Clamp

/-! ### The mean as an observable of the coordinates -/

section MeanVal

/-- The mean `𝔥_r(z)` as the observable `meanObs` of the coordinates at time `r` (the frozen `couplingMean`
along good paths, `couplingMean_eq_meanVal`). -/
def meanVal (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (z : ℂ) (r : ℝ≥0)
    (ω : Ω) : ℝ :=
  meanObs κ ρL ρR (coordProc κ z W VL VR B r ω, B r ω)

theorem measurable_meanObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Measurable (meanObs κ ρL ρR) := by
  unfold meanObs coordF
  fun_prop

variable {ω : Ω}

theorem IsGoodTest.couplingMean_eq_meanVal (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω)
    (hφH : tsupport φ ⊆ H) {z : ℂ} (hz : z ∈ tsupport φ) {r : ℝ≥0} (hr : r ≤ σ ω) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => VL i r ω - W r ω)
      (fun i => VR i r ω - W r ω)) (forceJumpSet (fun i => VL i r ω - W r ω)
        (fun i => VR i r ω - W r ω)) u) :
    couplingMean κ (fun s : ℝ => W s.toNNReal ω) (r : ℝ) u z = meanVal κ ρL ρR W VL VR B z r ω :=
  couplingMean_eq_meanObs hg.1 hg.2.2.1 (hφH hz) (hg.2.2.2.2.2 z hz).1 hr hu

/-- The coordinates at times `≤ σ` of a point of `supp φ` lie in a fixed compact subset of `obsRegion`. -/
theorem IsGoodTest.mem_obsCompact (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω)
    (hφH : tsupport φ ⊆ H) (hδ : 0 < δ) {Rk : ℝ} (hRk : ∀ z ∈ tsupport φ, ‖z‖ ≤ Rk) {z : ℂ}
    (hz : z ∈ tsupport φ) {r : ℝ≥0} (hr : r ≤ σ ω) :
    ((coordProc κ z W VL VR B r ω, B r ω) : Coord nL nR × ℝ) ∈
      obsCompact κ δ (Rk + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2) := by
  obtain ⟨hP, -, hσζ, hN, hR, hK⟩ := hg
  have h := coordAt_mem_obsCompact hP hσζ (hφH hz) (hK z hz).1 hδ (hK z hz).2 hN hR hr
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans ?_⟩
  linarith [hRk z hz]

/-- `𝔥` is bounded on the protected region. -/
theorem exists_abs_meanObs_le (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hδ : 0 < δ) (R' : ℝ) :
    ∃ C, ∀ p ∈ (obsCompact κ δ R' : Set (Coord nL nR × ℝ)), |meanObs κ ρL ρR p| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_obsCompact κ δ R').exists_bound_of_continuousOn
    ((contDiffOn_meanObs κ ρL ρR (n := 0)).continuousOn.mono (obsCompact_subset hδ))
  exact ⟨C, fun p hp => by simpa [Real.norm_eq_abs] using hC p hp⟩

/-- Continuity of `z ↦ 𝔥_r(z)` on `supp φ` along a good path, `r ≤ σ`. -/
theorem IsGoodTest.continuousOn_meanVal (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω)
    (hφH : tsupport φ ⊆ H) {r : ℝ≥0} (hr : r ≤ σ ω) :
    ContinuousOn (fun z => meanVal κ ρL ρR W VL VR B z r ω) (tsupport φ) := by
  have hprot := hg.isProtected hφH
  have hc := hg.continuous_clampPath
  have hrI : (r : ℝ) ∈ Icc 0 (σ ω : ℝ) := ⟨r.coe_nonneg, by exact_mod_cast hr⟩
  have hf : ContinuousOn (fun z => fwdMap (rpath (W · ω)) r z) (tsupport φ) := by
    rw [← fwdMap_clampPath (W := W) (σ := σ) hrI.2]
    exact hprot.continuousOn_fwdMap hc hrI
  have hL : ContinuousOn (fun z => logDerivFwd (rpath (W · ω)) r z) (tsupport φ) := by
    rw [← logDerivFwd_clampPath (W := W) (σ := σ) hrI.1 hrI.2]
    exact fun z hz => (continuousAt_logDerivFwd hc hrI.1
      (hprot.mem_of_le hrI hz)).continuousWithinAt
  have hco : ContinuousOn (fun z => ((coordProc κ z W VL VR B r ω, B r ω) : Coord nL nR × ℝ))
      (tsupport φ) := by
    refine ContinuousOn.prodMk ?_ continuousOn_const
    refine ((hf.add continuousOn_const).prodMk ((continuousOn_pi.2 fun i =>
      hf.sub continuousOn_const).prodMk ((continuousOn_pi.2 fun i =>
      hf.sub continuousOn_const).prodMk hL)))
  refine ((contDiffOn_meanObs κ ρL ρR (n := 0)).continuousOn).comp hco fun z hz => ?_
  exact mem_obsRegion_coordAt hg.1 hg.2.2.1 (hφH hz) (hg.2.2.2.2.2 z hz).1 hr

end MeanVal

/-! ### Joint measurability of the tested mean -/

section Measurability

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
  (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
  {G : Set Ω} (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G)
  (hGgood : ∀ ω ∈ G, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) (hφH : tsupport φ ⊆ H)
include hE hσ hG0 hGgood hφH

/-- The stopped coordinates and Brownian value at a point of `supp φ` are `𝓖_t`-measurable on `G`. -/
theorem measurable_coordProc_stopped {z : ℂ} (hz : z ∈ tsupport φ) (t : ℝ≥0) :
    Measurable[nullAugmented 𝓕 P t] (fun ω => if ω ∈ G then
      coordProc κ z W VL VR B (min t (σ ω)) ω else coordBase z) ∧
    Measurable[nullAugmented 𝓕 P t] (fun ω => if ω ∈ G then B (min t (σ ω)) ω else 0) := by
  obtain ⟨hB, hWa, hVLa, hVRa, -⟩ := hE
  have hWc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGgood ω hω).1.2.2.2.1
  have hBm : ∀ t, Measurable[nullAugmented 𝓕 P t] (B t) := fun t =>
    (hB.2.1 t).mono (le_nullAugmented 𝓕 P t) le_rfl
  have hK := fun s => measurable_killedCoord κ (adaptedBefore_mono (le_nullAugmented 𝓕 P) hWa)
    (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVLa i))
    (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVRa i)) hBm hWc hG0 (hφH hz)
    (VL := VL) (VR := VR) (B := B) s
  refine ⟨measurable_stopped_of_agree (X := coordProc κ z W VL VR B) hσ hK hG0 (coordBase z)
    (fun ω hω s hs => ?_) (fun ω hω => ?_) t,
    measurable_stopped_of_agree (K := B) (X := B) hσ hBm hG0 0 (fun _ _ _ _ => rfl)
      (fun ω hω => (hGgood ω hω).2.1.continuousOn) t⟩
  · obtain ⟨-, -, hσζ, -, -, hKs⟩ := hGgood ω hω
    obtain ⟨u, hu⟩ := (hKs z hz).1
    have halive : ω ∈ aliveSet W ζ G z s := ⟨hω, lt_of_le_of_lt (by exact_mod_cast hs) hσζ, u,
      isForwardSol_of_le hu s.coe_nonneg (by exact_mod_cast hs)⟩
    simp only [killedCoord, halive, ↓reduceIte]
  · obtain ⟨hPω, hBω, hσζ, -, -, hKs⟩ := hGgood ω hω
    exact continuousOn_coordAt hPω hσζ (hφH hz) (hKs z hz).1 hBω

theorem measurable_meanVal_stopped {z : ℂ} (hz : z ∈ tsupport φ) (t : ℝ≥0) :
    Measurable[nullAugmented 𝓕 P t] (fun ω => if ω ∈ G then
      meanVal κ ρL ρR W VL VR B z (min t (σ ω)) ω else 0) := by
  obtain ⟨hΛ, hBs⟩ := measurable_coordProc_stopped hE hσ hG0 hGgood hφH hz t
  have hGt : MeasurableSet[nullAugmented 𝓕 P t] G := (nullAugmented 𝓕 P).mono (zero_le (a := t)) G hG0
  have e : (fun ω => if ω ∈ G then meanVal κ ρL ρR W VL VR B z (min t (σ ω)) ω else 0) =
      G.piecewise (meanObs κ ρL ρR ∘ fun ω => ((if ω ∈ G then
        coordProc κ z W VL VR B (min t (σ ω)) ω else coordBase z),
          (if ω ∈ G then B (min t (σ ω)) ω else 0))) fun _ => 0 := by
    funext ω
    by_cases hω : ω ∈ G <;> simp [hω, meanVal, Set.piecewise]
  rw [e]
  exact Measurable.piecewise hGt ((measurable_meanObs κ ρL ρR).comp (hΛ.prodMk hBs))
    measurable_const

/-- The integrand `1_G φ(z) 𝔥_{t∧σ}(z)` of the tested mean. -/
def meanIntegrand (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (φ : ℂ → ℝ)
    (σ : Ω → ℝ≥0) (G : Set Ω) (t : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  if ω ∈ G then meanVal κ ρL ρR W VL VR B z (min t (σ ω)) ω * φ z else 0

theorem measurable_meanIntegrand (hφc : Continuous φ) (t : ℝ≥0) :
    Measurable[(borel ℂ).prod (nullAugmented 𝓕 P t)]
      (fun p : ℂ × Ω => meanIntegrand κ ρL ρR W VL VR B φ σ G t p.1 p.2) := by
  refine @measurable_uncurry_of_continuousOn ℂ Ω ℝ _ _ _ (borel ℂ) _ (nullAugmented 𝓕 P t) _ _ _ _
    _ (isClosed_tsupport φ) (fun z ω => meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω) 0
    (fun ω => ?_) (fun z hz => ?_) (fun z hz ω => ?_)
  · by_cases hω : ω ∈ G
    · simp only [meanIntegrand, hω, ↓reduceIte]
      exact ((hGgood ω hω).continuousOn_meanVal hφH (min_le_right _ _)).mul hφc.continuousOn
    · simp only [meanIntegrand, hω, ↓reduceIte]; exact continuousOn_const
  · have h := (measurable_meanVal_stopped hE hσ hG0 hGgood hφH hz t).mul_const (φ z)
    convert h using 1
    funext ω
    by_cases hω : ω ∈ G <;> simp [meanIntegrand, hω]
  · simp [meanIntegrand, eq_zero_of_notMem_tsupport' hz]

end Measurability

/-! ### The tested mean is a bounded continuous martingale -/

section TestMart

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
  (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
  {G : Set Ω} (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G)
  (hGgood : ∀ ω ∈ G, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) (hφH : tsupport φ ⊆ H)
  (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hδ : 0 < δ)

include hφH hδ hφs in
/-- A uniform bound on `𝔥_{t∧σ}` over `supp φ` along good paths. -/
theorem exists_abs_meanVal_le : ∃ C, ∀ ω, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω →
    ∀ z ∈ tsupport φ, ∀ r ≤ σ ω, |meanVal κ ρL ρR W VL VR B z r ω| ≤ C := by
  obtain ⟨Rk, hRk⟩ := hφs.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := exists_abs_meanObs_le κ ρL ρR (nL := nL) (nR := nR) hδ
    (Rk + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2)
  refine ⟨C, fun ω hg z hz r hr => hC _ (hg.mem_obsCompact hφH hδ (Rk := Rk) (fun z hz => ?_) hz hr)⟩
  simpa using hRk hz

include hGgood in
theorem abs_meanIntegrand_le {C : ℝ}
    (hC : ∀ ω, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω →
      ∀ z ∈ tsupport φ, ∀ r ≤ σ ω, |meanVal κ ρL ρR W VL VR B z r ω| ≤ C) (t : ℝ≥0) (z : ℂ) (ω : Ω) :
    |meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω| ≤ |C| * |φ z| := by
  by_cases hω : ω ∈ G
  · by_cases hz : z ∈ tsupport φ
    · simp only [meanIntegrand, hω, ↓reduceIte, abs_mul]
      exact mul_le_mul_of_nonneg_right ((hC ω (hGgood ω hω) z hz _ (min_le_right _ _)).trans
        (le_abs_self C)) (abs_nonneg _)
    · simp [meanIntegrand, eq_zero_of_notMem_tsupport' hz]
  · simp only [meanIntegrand, hω, ↓reduceIte, abs_zero]
    positivity

include hE hσ hG0 hGgood hφH hφc hφs hδ in
/-- **The tested mean is a martingale** (integrated (3.15)): `t ↦ ∫ 1_G φ(z) 𝔥_{t∧σ}(z) dz`. -/
theorem martingale_meanIntegral (hκ : 0 < κ) (hGc : P Gᶜ = 0) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    Martingale (fun t ω => ∫ z, meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω)
      (nullAugmented 𝓕 P) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  obtain ⟨C, hC⟩ := exists_abs_meanVal_le hφH hφs hδ (κ := κ) (ρL := ρL) (ρR := ρR)
    (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (xL := xL) (xR := xR) (σ := σ) (R := R) (N := N)
  refine martingale_integral_of_forall (μ := volume)
    (fun t => measurable_meanIntegrand hE hσ hG0 hGgood hφH hφc t)
    ((hφc.integrable_of_hasCompactSupport hφs).abs.const_mul |C|)
    (ae_of_all _ fun z t ω => abs_meanIntegrand_le hGgood hC t z ω)
    (ae_of_all _ fun z s t hst S hS => ?_)
  by_cases hz : z ∈ tsupport φ
  · have hσpz : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
        (∃ u, IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
        δ ≤ (fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
        ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R := by
      filter_upwards [hGae] with ω hω
      obtain ⟨-, -, hσζ, hN, hR, hK⟩ := hGgood ω hω
      exact ⟨hσζ, (hK z hz).1, (hK z hz).2, hN, hR⟩
    obtain ⟨M, hM, hMae⟩ := exists_martingale_couplingMean hE hκ (hφH hz) hσ hδ hσpz u hu
    have hY : ∀ r, (fun ω => meanIntegrand κ ρL ρR W VL VR B φ σ G r z ω) =ᵐ[P]
        fun ω => M r ω * φ z := fun r => by
      filter_upwards [hMae, hGae] with ω hω hωG
      simp only [meanIntegrand, hωG, ↓reduceIte]
      rw [hω r, (hGgood ω hωG).couplingMean_eq_meanVal hφH hz (min_le_right _ _) (hu ω _)]
    rw [integral_congr_ae (ae_restrict_of_ae (hY s)), integral_congr_ae (ae_restrict_of_ae (hY t)),
      integral_mul_const, integral_mul_const, hM.setIntegral_eq hst hS]
  · simp [meanIntegrand, eq_zero_of_notMem_tsupport' hz]

include hE hσ hG0 hGgood hφH hφc hφs hδ in
/-- Every path of the tested mean `t ↦ ∫ 1_G φ 𝔥_{t∧σ}` is continuous. -/
theorem continuous_meanIntegral (ω : Ω) :
    Continuous fun t => ∫ z, meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω := by
  by_cases hω : ω ∈ G
  · obtain ⟨C, hC⟩ := exists_abs_meanVal_le hφH hφs hδ (κ := κ) (ρL := ρL) (ρR := ρR)
      (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (xL := xL) (xR := xR) (σ := σ) (R := R)
      (N := N)
    refine continuous_of_dominated (bound := fun z => |C| * |φ z|) (fun t => ?_)
      (fun t => ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact abs_meanIntegrand_le hGgood hC t z ω)
      ((hφc.integrable_of_hasCompactSupport hφs).abs.const_mul |C|) (ae_of_all _ fun z => ?_)
    · have hm := measurable_meanIntegrand hE hσ hG0 hGgood hφH hφc t
      exact (hm.comp (@measurable_prodMk_right ℂ Ω _ (nullAugmented 𝓕 P t) ω)).aestronglyMeasurable
    · by_cases hz : z ∈ tsupport φ
      · obtain ⟨hPω, hBω, hσζ, -, -, hK⟩ := hGgood ω hω
        simp only [meanIntegrand, hω, ↓reduceIte, meanVal]
        refine Continuous.mul ?_ continuous_const
        have hco := continuousOn_coordAt (κ := κ) hPω hσζ (hφH hz) (hK z hz).1 hBω
        have hst : Continuous fun t : ℝ≥0 => min t (σ ω) := continuous_id.min continuous_const
        refine ((contDiffOn_meanObs κ ρL ρR (n := 0)).continuousOn).comp_continuous
          ((hco.comp_continuous hst fun t => mem_Iic.2 (min_le_right _ _)).prodMk (hBω.comp hst)) fun t => ?_
        exact mem_obsRegion_coordAt hPω hσζ (hφH hz) (hK z hz).1 (min_le_right _ _)
      · simp only [meanIntegrand, eq_zero_of_notMem_tsupport' hz, mul_zero, ite_self]
        exact continuous_const
  · simp only [meanIntegrand, hω, ↓reduceIte, integral_zero]
    exact continuous_const

end TestMart

/-! ### The two-point integrand -/

section Pair

/-- The forward map at `t ∧ σ` on `G × supp φ`, and the constant `i` elsewhere. -/
def fwdOn (W : ℝ≥0 → Ω → ℝ) (φ : ℂ → ℝ) (σ : Ω → ℝ≥0) (G : Set Ω) (t : ℝ≥0) (y : ℂ) (ω : Ω) : ℂ :=
  if ω ∈ G ∧ y ∈ tsupport φ then fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) y else Complex.I

/-- The energy part `1_G φ(y) G(f_{t∧σ} y, f_{t∧σ} z) φ(z)`. -/
def energyPart (W : ℝ≥0 → Ω → ℝ) (φ : ℂ → ℝ) (σ : Ω → ℝ≥0) (G : Set Ω) (t : ℝ≥0) (q : ℂ × ℂ)
    (ω : Ω) : ℝ :=
  if ω ∈ G then φ q.1 * greenH (fwdOn W φ σ G t q.1 ω) (fwdOn W φ σ G t q.2 ω) * φ q.2 else 0

/-- The two-point integrand `1_G φ(y) φ(z) (𝔥(y) 𝔥(z) + G(f y, f z))` at time `t ∧ σ`. -/
def pairIntegrand (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (φ : ℂ → ℝ)
    (σ : Ω → ℝ≥0) (G : Set Ω) (t : ℝ≥0) (q : ℂ × ℂ) (ω : Ω) : ℝ :=
  meanIntegrand κ ρL ρR W VL VR B φ σ G t q.1 ω * meanIntegrand κ ρL ρR W VL VR B φ σ G t q.2 ω +
    energyPart W φ σ G t q ω

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
  (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
  {G : Set Ω} (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G)
  (hGgood : ∀ ω ∈ G, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) (hφH : tsupport φ ⊆ H)
  (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hδ : 0 < δ)

include hE hσ hG0 hGgood hφH in
theorem measurable_fwdOn (t : ℝ≥0) :
    Measurable[(borel ℂ).prod (nullAugmented 𝓕 P t)]
      (fun p : ℂ × Ω => fwdOn W φ σ G t p.1 p.2) := by
  refine @measurable_uncurry_of_continuousOn ℂ Ω ℂ _ _ _ (borel ℂ) _ (nullAugmented 𝓕 P t) _ _ _ _
    _ (isClosed_tsupport φ) (fun y ω => fwdOn W φ σ G t y ω) Complex.I
    (fun ω => ?_) (fun y hy => ?_) (fun y hy ω => by simp [fwdOn, hy])
  · by_cases hω : ω ∈ G
    · have hg := hGgood ω hω
      have hrI : ((min t (σ ω) : ℝ≥0) : ℝ) ∈ Icc 0 (σ ω : ℝ) :=
        ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_right _ _⟩
      have h := (hg.isProtected hφH).continuousOn_fwdMap hg.continuous_clampPath hrI
      rw [fwdMap_clampPath (W := W) (σ := σ) hrI.2] at h
      exact h.congr fun y hy => by simp [fwdOn, hω, hy]
    · exact (continuousOn_const (c := Complex.I)).congr fun y _ => by simp [fwdOn, hω]
  · obtain ⟨hΛ, hBs⟩ := measurable_coordProc_stopped hE hσ hG0 hGgood hφH hy t
    have hGt : MeasurableSet[nullAugmented 𝓕 P t] G :=
      (nullAugmented 𝓕 P).mono (zero_le (a := t)) G hG0
    have e : (fun ω => fwdOn W φ σ G t y ω) = G.piecewise (coordF κ ∘ fun ω => ((if ω ∈ G then
        coordProc κ y W VL VR B (min t (σ ω)) ω else coordBase y),
          (if ω ∈ G then B (min t (σ ω)) ω else 0))) fun _ => Complex.I := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [fwdOn, hω, hy, and_self, ↓reduceIte, Set.piecewise, Function.comp_apply]
        rw [coordProc, coordF_coordAt]
      · simp [fwdOn, hω, Set.piecewise]
    rw [e]
    exact Measurable.piecewise hGt ((contDiff_coordF κ (n := 0)).continuous.measurable.comp
      (hΛ.prodMk hBs)) measurable_const

include hE hσ hG0 hGgood hφH hφc in
theorem measurable_pairIntegrand (t : ℝ≥0) :
    Measurable[(inferInstance : MeasurableSpace (ℂ × ℂ)).prod (nullAugmented 𝓕 P t)]
      (fun q : (ℂ × ℂ) × Ω => pairIntegrand κ ρL ρR W VL VR B φ σ G t q.1 q.2) := by
  set m𝓖 := nullAugmented 𝓕 P t
  have hfst : @Measurable ((ℂ × ℂ) × Ω) (ℂ × Ω)
      ((inferInstance : MeasurableSpace (ℂ × ℂ)).prod m𝓖) ((borel ℂ).prod m𝓖)
      (fun q => (q.1.1, q.2)) := Measurable.prodMk measurable_fst.fst measurable_snd
  have hsnd : @Measurable ((ℂ × ℂ) × Ω) (ℂ × Ω)
      ((inferInstance : MeasurableSpace (ℂ × ℂ)).prod m𝓖) ((borel ℂ).prod m𝓖)
      (fun q => (q.1.2, q.2)) := Measurable.prodMk measurable_fst.snd measurable_snd
  have hm := measurable_meanIntegrand hE hσ hG0 hGgood hφH hφc t (κ := κ) (ρL := ρL) (ρR := ρR)
  have hf := measurable_fwdOn hE hσ hG0 hGgood hφH t (κ := κ) (ρL := ρL) (ρR := ρR)
  have hGt : MeasurableSet[m𝓖] G := (nullAugmented 𝓕 P).mono (zero_le (a := t)) G hG0
  have hS : MeasurableSet[(inferInstance : MeasurableSpace (ℂ × ℂ)).prod m𝓖]
      {q : (ℂ × ℂ) × Ω | q.2 ∈ G} := measurable_snd hGt
  have hE' : Measurable[(inferInstance : MeasurableSpace (ℂ × ℂ)).prod m𝓖]
      (fun q : (ℂ × ℂ) × Ω => energyPart W φ σ G t q.1 q.2) := by
    have e : (fun q : (ℂ × ℂ) × Ω => energyPart W φ σ G t q.1 q.2) =
        {q : (ℂ × ℂ) × Ω | q.2 ∈ G}.piecewise (fun q => φ q.1.1 *
          greenH (fwdOn W φ σ G t q.1.1 q.2) (fwdOn W φ σ G t q.1.2 q.2) * φ q.1.2) fun _ => 0 := by
      funext q; by_cases hq : q.2 ∈ G <;> simp [energyPart, hq, Set.piecewise]
    rw [e]
    refine Measurable.piecewise hS ?_ measurable_const
    exact ((hφc.measurable.comp measurable_fst.fst).mul (measurable_greenH.comp
      ((hf.comp hfst).prodMk (hf.comp hsnd)))).mul (hφc.measurable.comp measurable_fst.snd)
  exact ((hm.comp hfst).mul (hm.comp hsnd)).add hE'

include hGgood hφH hδ in
/-- `0 ≤ G(f y, f z) ≤ G(y, z)` for the energy part along good paths. -/
theorem abs_energyPart_le (t : ℝ≥0) {q : ℂ × ℂ} (hq : q.1 ≠ q.2) (ω : Ω) :
    |energyPart W φ σ G t q ω| ≤ |φ q.1| * |φ q.2| * greenH q.1 q.2 := by
  by_cases h1 : q.1 ∈ tsupport φ
  · by_cases h2 : q.2 ∈ tsupport φ
    · have hG0 : 0 ≤ greenH q.1 q.2 :=
        greenH_nonneg (show (0:ℝ) ≤ q.1.im from le_of_lt (hφH h1)) (show (0:ℝ) ≤ q.2.im from le_of_lt (hφH h2)) hq
      by_cases hω : ω ∈ G
      · have hg := hGgood ω hω
        have hrI : ((min t (σ ω) : ℝ≥0) : ℝ) ∈ Icc 0 (σ ω : ℝ) :=
          ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_right _ _⟩
        obtain ⟨g0, g1⟩ := greenH_fwdMap_mem_Icc (hg.isProtected hφH) hg.continuous_clampPath
          (σ ω).coe_nonneg hδ h1 h2 hq hrI
        rw [fwdMap_clampPath (W := W) (σ := σ) hrI.2] at g0 g1
        simp only [energyPart, fwdOn, hω, h1, h2, and_self, ↓reduceIte, abs_mul, abs_of_nonneg g0]
        calc |φ q.1| * greenH (fwdMap (rpath (W · ω)) ↑(min t (σ ω)) q.1)
              (fwdMap (rpath (W · ω)) ↑(min t (σ ω)) q.2) * |φ q.2|
            = |φ q.1| * |φ q.2| * greenH (fwdMap (rpath (W · ω)) ↑(min t (σ ω)) q.1)
              (fwdMap (rpath (W · ω)) ↑(min t (σ ω)) q.2) := by ring
          _ ≤ |φ q.1| * |φ q.2| * greenH q.1 q.2 :=
              mul_le_mul_of_nonneg_left g1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · simp only [energyPart, hω, ↓reduceIte, abs_zero]; positivity
    · simp [energyPart, eq_zero_of_notMem_tsupport' h2]
  · simp [energyPart, eq_zero_of_notMem_tsupport' h1]

include hE hσ hG0 hGgood hφH hφc hφs hδ in
/-- **(3.20) integrated**: `t ↦ ∬ 1_G φ(y) φ(z) (𝔥_{t∧σ}(y) 𝔥_{t∧σ}(z) + G(f_{t∧σ} y, f_{t∧σ} z))` is a martingale. -/
theorem martingale_pairIntegral (hκ : 0 < κ) (hGc : P Gᶜ = 0) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    Martingale (fun t ω => ∫ q, pairIntegrand κ ρL ρR W VL VR B φ σ G t q ω
      ∂((volume : Measure ℂ).prod volume)) (nullAugmented 𝓕 P) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  obtain ⟨ω₀, hω₀⟩ : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have : P Gᶜ = 1 := by rw [h, compl_empty, measure_univ]
    rw [hGc] at this; exact zero_ne_one this
  have hρδ : ∀ a : ℂ, a.im < δ → φ a = 0 := fun a ha => eq_zero_of_notMem_tsupport' fun h =>
    absurd (((hGgood ω₀ hω₀).isProtected hφH).le_im_self (hGgood ω₀ hω₀).continuous_clampPath
      (σ ω₀).coe_nonneg h) (not_le.2 ha)
  obtain ⟨C, hC⟩ := exists_abs_meanVal_le hφH hφs hδ (κ := κ) (ρL := ρL) (ρR := ρR)
    (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (xL := xL) (xR := xR) (σ := σ) (R := R) (N := N)
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  refine martingale_integral_of_forall (μ := (volume : Measure ℂ).prod volume)
    (fun t => measurable_pairIntegrand hE hσ hG0 hGgood hφH hφc t)
    (g := fun q => |C| ^ 2 * (|φ q.1| * |φ q.2|) + |φ q.1| * |φ q.2| * greenH q.1 q.2)
    (((hφi.abs.mul_prod hφi.abs).const_mul _).add
      (FieldMart.integrable_rho_rho_greenH hφc hφs hδ hρδ)) ?_ ?_
  · filter_upwards [FieldMart.ae_ne_diag] with q hq t ω
    have h1 := abs_meanIntegrand_le hGgood hC t q.1 ω
    have h2 := abs_meanIntegrand_le hGgood hC t q.2 ω
    have h3 := abs_energyPart_le hGgood hφH hδ t hq ω
    simp only [pairIntegrand]
    calc |meanIntegrand κ ρL ρR W VL VR B φ σ G t q.1 ω * meanIntegrand κ ρL ρR W VL VR B φ σ G t q.2 ω +
          energyPart W φ σ G t q ω|
        ≤ |meanIntegrand κ ρL ρR W VL VR B φ σ G t q.1 ω| *
            |meanIntegrand κ ρL ρR W VL VR B φ σ G t q.2 ω| + |energyPart W φ σ G t q ω| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |C| * |φ q.1| * (|C| * |φ q.2|) + |φ q.1| * |φ q.2| * greenH q.1 q.2 :=
          add_le_add (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3
      _ = |C| ^ 2 * (|φ q.1| * |φ q.2|) + |φ q.1| * |φ q.2| * greenH q.1 q.2 := by ring
  · filter_upwards [FieldMart.ae_ne_diag] with q hq s t hst S hS
    obtain ⟨y, z⟩ := q
    dsimp only at hq
    by_cases h1 : y ∈ tsupport φ
    · by_cases h2 : z ∈ tsupport φ
      · set ε := ‖y - z‖ * δ / Real.sqrt (y.im * z.im) with hε
        have hy : 0 < y.im := hφH h1
        have hz : 0 < z.im := hφH h2
        have hε0 : 0 < ε := by
          have : 0 < ‖y - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hq)
          have : 0 < Real.sqrt (y.im * z.im) := Real.sqrt_pos.2 (mul_pos hy hz)
          positivity
        have hσp2 : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
            (∃ u, IsForwardSol (rpath (W · ω)) y (σ ω) u) ∧
            (∃ u, IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
            δ ≤ (fwdMap (rpath (W · ω)) (σ ω) y).im ∧
            δ ≤ (fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
            (∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R) ∧
            ∀ s ≤ σ ω, ε ≤ ‖fwdMap (rpath (W · ω)) s y - fwdMap (rpath (W · ω)) s z‖ := by
          filter_upwards [hGae] with ω hω
          have hg := hGgood ω hω
          obtain ⟨-, -, hσζ, hN, hR, hK⟩ := hg
          refine ⟨hσζ, (hK y h1).1, (hK z h2).1, (hK y h1).2, (hK z h2).2, hN, hR, fun s hs => ?_⟩
          have hsI : (s : ℝ) ∈ Icc 0 (σ ω : ℝ) := ⟨s.coe_nonneg, by exact_mod_cast hs⟩
          have hwc := (hGgood ω hω).continuousOn_rpath
          have ha := fun x (hx : x ∈ tsupport φ) =>
            (antitoneOn_im_fwdMap_of_continuousOn (σ ω).coe_nonneg hwc (hφH hx) (hK x hx).1) hsI
              ⟨(σ ω).coe_nonneg, le_rfl⟩ hsI.2
          exact le_norm_fwdMap_sub_of_continuousOn (σ ω).coe_nonneg hwc hy hz (hK y h1).1
            (hK z h2).1 hsI hδ.le ((hK y h1).2.trans (ha y h1)) ((hK z h2).2.trans (ha z h2))
        obtain ⟨M, hM, hMae⟩ := exists_martingale_couplingMean_mul_add_greenH hE hκ hy hz hσ hδ hε0
          hσp2 u hu
        have hY : ∀ r, (fun ω => pairIntegrand κ ρL ρR W VL VR B φ σ G r (y, z) ω) =ᵐ[P]
            fun ω => φ y * φ z * M r ω := fun r => by
          filter_upwards [hMae, hGae] with ω hω hωG
          have hg := hGgood ω hωG
          simp only [pairIntegrand, meanIntegrand, energyPart, fwdOn, hωG, h1, h2, and_self,
            ↓reduceIte]
          rw [hω r, hg.couplingMean_eq_meanVal hφH h1 (min_le_right _ _) (hu ω _),
            hg.couplingMean_eq_meanVal hφH h2 (min_le_right _ _) (hu ω _)]
          rw [show (rpath fun x => W x ω) = (fun s : ℝ => W s.toNNReal ω) from rfl]
          ring
        rw [integral_congr_ae (ae_restrict_of_ae (hY s)), integral_congr_ae (ae_restrict_of_ae (hY t)),
          integral_const_mul, integral_const_mul, hM.setIntegral_eq hst hS]
      · simp [pairIntegrand, meanIntegrand, energyPart, eq_zero_of_notMem_tsupport' h2]
    · simp [pairIntegrand, meanIntegrand, energyPart, eq_zero_of_notMem_tsupport' h1]

end Pair

/-! ### Identification with the frozen objects along good paths -/

section Ident

variable {G : Set Ω} {ω : Ω} (hφH : tsupport φ ⊆ H) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
  (hδ : 0 < δ)

/-- `E₀(φ) = ∬ φ(y) G(y, z) φ(z)`, the variance of `(h̃, φ)` for the zero-boundary GFF `h̃` on `ℍ`. -/
def greenEnergy0 (φ : ℂ → ℝ) : ℝ := ∫ y, ∫ z, φ y * greenH y z * φ z

include hφH in
theorem IsGoodTest.fwdMap_zero (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) {z : ℂ}
    (hz : z ∈ tsupport φ) : fwdMap (fun s : ℝ => W s.toNNReal ω) 0 z = z := by
  have h := fwdMap_zero_of_mem hg.continuous_clampPath (σ ω).coe_nonneg
    ((hg.isProtected hφH) z hz).1
  rw [fwdMap_clampPath (W := W) (σ := σ) (σ ω).coe_nonneg] at h
  have h0 : clampPath W σ ω 0 = 0 := by
    rw [clampPath, clampDrv_eqOn ⟨le_rfl, (σ ω).coe_nonneg⟩]
    simpa [rpath] using hg.1.1
  rw [h0, Complex.ofReal_zero, sub_zero] at h
  exact h

include hφH in
theorem IsGoodTest.loewnerGreenEnergy_zero (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) :
    loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) 0 φ = greenEnergy0 φ := by
  unfold loewnerGreenEnergy greenEnergy0
  congr 1; funext y; congr 1; funext z
  by_cases hy : y ∈ tsupport φ
  · by_cases hz : z ∈ tsupport φ
    · rw [hg.fwdMap_zero hφH hy, hg.fwdMap_zero hφH hz]
    · simp [eq_zero_of_notMem_tsupport' hz]
  · simp [eq_zero_of_notMem_tsupport' hy]

include hφH in
theorem integral_meanIntegrand_eq (hω : ω ∈ G)
    (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) (t : ℝ≥0) :
    ∫ z, meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
        (u ω (min t (σ ω))) z * φ z := by
  congr 1; funext z
  by_cases hz : z ∈ tsupport φ
  · simp only [meanIntegrand, hω, ↓reduceIte]
    rw [hg.couplingMean_eq_meanVal hφH hz (min_le_right _ _) (hu ω _)]
  · simp [meanIntegrand, eq_zero_of_notMem_tsupport' hz]

end Ident

section Ident2

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
  (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
  {G : Set Ω} (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G)
  (hGgood : ∀ ω ∈ G, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) (hφH : tsupport φ ⊆ H)
  (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hδ : 0 < δ)

include hE hσ hG0 hGgood hφH hφc hφs hδ in
theorem integrable_meanIntegrand (t : ℝ≥0) (ω : Ω) :
    Integrable fun z => meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω := by
  obtain ⟨C, hC⟩ := exists_abs_meanVal_le hφH hφs hδ (κ := κ) (ρL := ρL) (ρR := ρR)
    (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (xL := xL) (xR := xR) (σ := σ) (R := R) (N := N)
  have hm := measurable_meanIntegrand hE hσ hG0 hGgood hφH hφc t
  refine Integrable.mono' ((hφc.integrable_of_hasCompactSupport hφs).abs.const_mul |C|)
    (hm.comp (@measurable_prodMk_right ℂ Ω _ (nullAugmented 𝓕 P t) ω)).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]; exact abs_meanIntegrand_le hGgood hC t z ω

include hE hσ hG0 hGgood hφH hφc hφs hδ in
/-- Along good paths, `∬ pairIntegrand = (∫ meanIntegrand)² + E_{t∧σ}(φ)`. -/
theorem integral_pairIntegrand_eq {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    ∫ q, pairIntegrand κ ρL ρR W VL VR B φ σ G t q ω ∂((volume : Measure ℂ).prod volume) =
      (∫ z, meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω) ^ 2 +
        loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) φ := by
  have hg := hGgood ω hω
  have hrI : ((min t (σ ω) : ℝ≥0) : ℝ) ∈ Icc 0 (σ ω : ℝ) :=
    ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_right _ _⟩
  have hmi := integrable_meanIntegrand hE hσ hG0 hGgood hφH hφc hφs hδ t ω
  have heP : (fun q => energyPart W φ σ G t q ω) =
      energyIntegrand (clampPath W σ ω) (min t (σ ω) : ℝ≥0) φ := by
    funext q
    by_cases h1 : q.1 ∈ tsupport φ
    · by_cases h2 : q.2 ∈ tsupport φ
      · simp only [energyPart, fwdOn, hω, h1, h2, and_self, ↓reduceIte, energyIntegrand,
          fwdMap_clampPath (W := W) (σ := σ) hrI.2]
      · simp [energyPart, energyIntegrand, eq_zero_of_notMem_tsupport' h2]
    · simp [energyPart, energyIntegrand, eq_zero_of_notMem_tsupport' h1]
  have hei := integrable_energyIntegrand hφc hφs (hg.isProtected hφH) hg.continuous_clampPath
    (σ ω).coe_nonneg hδ hrI
  rw [← heP] at hei
  simp only [pairIntegrand]
  rw [integral_add (hmi.mul_prod hmi) hei,
    integral_prod_mul (fun z => meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω)
      (fun z => meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω), sq, heP,
    ← loewnerGreenEnergy_eq_integral_prod hφc hφs (hg.isProtected hφH) hg.continuous_clampPath
      (σ ω).coe_nonneg hδ hrI, loewnerGreenEnergy_clampPath (W := W) (σ := σ) hrI.2]
  rfl

end Ident2

/-! ### The energy along good paths: monotone and Lipschitz -/

section EnergyClock

variable {ω : Ω} (hφH : tsupport φ ⊆ H) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
  (hδ : 0 < δ)

theorem min_sub_min_le {p q a : ℝ≥0} (hpq : p ≤ q) :
    ((min q a : ℝ≥0) : ℝ) - (min p a : ℝ≥0) ≤ (q : ℝ) - p := by
  rcases le_total q a with hqa | hqa
  · rw [min_eq_left hqa, min_eq_left (hpq.trans hqa)]
  · rw [min_eq_right hqa]
    rcases le_total p a with hpa | hpa
    · rw [min_eq_left hpa]; linarith [(show (a : ℝ) ≤ q from by exact_mod_cast hqa)]
    · rw [min_eq_right hpa]; simp only [sub_self]; exact sub_nonneg.2 (by exact_mod_cast hpq)

include hφH hφc hφs hδ in
/-- Along a good path, `t ↦ E_{t∧σ}(φ)` is nonincreasing with `E_{p∧σ} − E_{q∧σ} ≤ c (q − p)`,
`c = ((2/δ) ∫ |φ|)²`. -/
theorem IsGoodTest.energy_sub_mem (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω)
    {p q : ℝ≥0} (hpq : p ≤ q) :
    0 ≤ loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (min p (σ ω) : ℝ≥0) φ -
        loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (min q (σ ω) : ℝ≥0) φ ∧
      loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (min p (σ ω) : ℝ≥0) φ -
        loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (min q (σ ω) : ℝ≥0) φ ≤
          (2 / δ * ∫ z, |φ z|) ^ 2 * ((q : ℝ) - p) := by
  have hprot := hg.isProtected hφH
  have hc := hg.continuous_clampPath
  have ha : ((min p (σ ω) : ℝ≥0) : ℝ) ≤ (min q (σ ω) : ℝ≥0) := by
    exact_mod_cast min_le_min_right _ hpq
  have hbσ : ((min q (σ ω) : ℝ≥0) : ℝ) ≤ σ ω := by exact_mod_cast min_le_right _ _
  have h := loewnerGreenEnergy_sub_eq_integral hφc hφs hprot hc (σ ω).coe_nonneg hδ
    (NNReal.coe_nonneg _) ha hbσ
  rw [loewnerGreenEnergy_clampPath (W := W) (σ := σ) (ha.trans hbσ),
    loewnerGreenEnergy_clampPath (W := W) (σ := σ) hbσ] at h
  rw [show (fun s : ℝ => W s.toNNReal ω) = rpath (W · ω) from rfl, h]
  have hφi : 0 ≤ ∫ z, |φ z| := integral_nonneg fun _ => abs_nonneg _
  constructor
  · exact intervalIntegral.integral_nonneg ha fun s _ => sq_nonneg _
  · have hb : ∀ s ∈ Set.uIoc ((min p (σ ω) : ℝ≥0) : ℝ) (min q (σ ω) : ℝ≥0),
        ‖(∫ z, φ z * kCoef (clampPath W σ ω) s z) ^ 2‖ ≤ (2 / δ * ∫ z, |φ z|) ^ 2 := by
      intro s hs
      rw [Set.uIoc_of_le ha] at hs
      have hsI : s ∈ Icc 0 (σ ω : ℝ) :=
        ⟨(NNReal.coe_nonneg _).trans hs.1.le, hs.2.trans hbσ⟩
      have h1 := abs_integral_mul_kCoef_le hφc hφs hprot hc (σ ω).coe_nonneg hδ hsI
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine (le_abs_self _).trans ((intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_)
    rw [abs_of_nonneg (sub_nonneg.2 ha)]
    exact mul_le_mul_of_nonneg_left (min_sub_min_le hpq) (sq_nonneg _)

end EnergyClock

/-! ### The characteristic-function martingale at protected stops -/

section CharFun

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
  (hσp : ∀ᵐ ω ∂P, IsTestProtected W VL VR B ζ φ σ δ R N ω) (hφH : tsupport φ ⊆ H)
  (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hδ : 0 < δ) (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
include hE hκ hσ hσp hφH hφc hφs hδ hu

/-- **The characteristic-function martingale of the tested mean** (Specification L550–L552, node
`SPEC.thm-1.1#charfn-martingale`): at a stopping time `σ` protecting `supp φ`, for `s ≤ t`, `S ∈ 𝓖_s` and real `θ`,
`∫_S exp(iθ (𝔥_{t∧σ}, φ) − θ² E_{t∧σ}(φ)/2) = ∫_S exp(iθ (𝔥_{s∧σ}, φ) − θ² E_{s∧σ}(φ)/2)`. -/
theorem setIntegral_cexp_testMean_eq {s t : ℝ≥0} (hst : s ≤ t) {S : Set Ω}
    (hS : MeasurableSet[nullAugmented 𝓕 P s] S) (θ : ℝ) :
    ∫ ω in S, Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (min t (σ ω) : ℝ≥0)
          (u ω (min t (σ ω))) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (min t (σ ω) : ℝ≥0) φ : ℝ) : ℂ)
          / 2) ∂P =
    ∫ ω in S, Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (min s (σ ω) : ℝ≥0)
          (u ω (min s (σ ω))) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (min s (σ ω) : ℝ≥0) φ : ℝ) : ℂ)
          / 2) ∂P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨G, -, hGc, hG0, hGgood⟩ := exists_goodSet hE hσp
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  obtain ⟨C, hC⟩ := exists_abs_meanVal_le hφH hφs hδ (κ := κ) (ρL := ρL) (ρR := ρR)
    (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (xL := xL) (xR := xR) (σ := σ) (R := R) (N := N)
  set M : ℝ≥0 → Ω → ℝ := fun t ω => ∫ z, meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω with hMdef
  set Q : ℝ≥0 → Ω → ℝ := fun t ω => ∫ q, pairIntegrand κ ρL ρR W VL VR B φ σ G t q ω
    ∂((volume : Measure ℂ).prod volume) with hQdef
  set E₀ := greenEnergy0 φ with hE₀
  set A : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then E₀ - (Q t ω - M t ω ^ 2) else 0 with hAdef
  have hM : Martingale M (nullAugmented 𝓕 P) P :=
    martingale_meanIntegral hE hσ hG0 hGgood hφH hφc hφs hδ hκ hGc u hu
  have hQ : Martingale Q (nullAugmented 𝓕 P) P :=
    martingale_pairIntegral hE hσ hG0 hGgood hφH hφc hφs hδ hκ hGc u hu
  have hAG : ∀ ω ∈ G, ∀ t, A t ω =
      E₀ - loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (min t (σ ω) : ℝ≥0) φ := by
    intro ω hω t
    simp only [hAdef, hω, ↓reduceIte, hQdef, hMdef]
    rw [integral_pairIntegrand_eq hE hσ hG0 hGgood hφH hφc hφs hδ hω t]
    ring
  have hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) (nullAugmented 𝓕 P) P := by
    refine FieldMart.martingale_of_ae_eq (hQ.sub (martingale_const _ P E₀)) (fun t => ?_)
      (fun t => ?_)
    · have hMt := (hM.stronglyAdapted t).measurable
      have hQt := (hQ.stronglyAdapted t).measurable
      have hGt : MeasurableSet[nullAugmented 𝓕 P t] G :=
        (nullAugmented 𝓕 P).mono (zero_le (a := t)) G hG0
      have hAt : Measurable[nullAugmented 𝓕 P t] (A t) := by
        have e : A t = G.piecewise (fun ω => E₀ - (Q t ω - M t ω ^ 2)) (fun _ => 0) := by
          funext ω; by_cases hω : ω ∈ G <;> simp [hAdef, hω, Set.piecewise]
        rw [e]
        exact Measurable.piecewise hGt (measurable_const.sub (hQt.sub (hMt.pow_const 2)))
          measurable_const
      exact ((hMt.pow_const 2).sub hAt).stronglyMeasurable
    · filter_upwards [hGae] with ω hω
      simp only [hAdef, hω, ↓reduceIte, Pi.sub_apply]
      ring
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  have hK : ∀ t ω, |M t ω| ≤ |C| * ∫ z, |φ z| := fun t ω => by
    rw [hMdef, ← Real.norm_eq_abs, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hφi.abs.const_mul _) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact abs_meanIntegrand_le hGgood hC t z ω)
  have hcont : ∀ ω, Continuous fun t => M t ω := fun ω =>
    continuous_meanIntegral hE hσ hG0 hGgood hφH hφc hφs hδ ω
  set c : ℝ := (2 / δ * ∫ z, |φ z|) ^ 2 with hc
  have hA0 : ∀ ω, A 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [hAG ω hω 0, min_eq_left (zero_le (a := σ ω)), NNReal.coe_zero,
        (hGgood ω hω).loewnerGreenEnergy_zero hφH, sub_self]
    · simp [hAdef, hω]
  have hAmono : ∀ ⦃p q : ℝ≥0⦄, p ≤ q → ∀ ω, A p ω ≤ A q ω := fun p q hpq ω => by
    by_cases hω : ω ∈ G
    · rw [hAG ω hω p, hAG ω hω q]
      have := ((hGgood ω hω).energy_sub_mem hφH hφc hφs hδ hpq).1
      linarith
    · simp [hAdef, hω]
  have hAlip : ∀ ⦃p q : ℝ≥0⦄, p ≤ q → ∀ ω, A q ω - A p ω ≤ c * ((q : ℝ) - p) :=
    fun p q hpq ω => by
    by_cases hω : ω ∈ G
    · rw [hAG ω hω p, hAG ω hω q]
      have := ((hGgood ω hω).energy_sub_mem hφH hφc hφs hδ hpq).2
      linarith
    · simp only [hAdef, hω, ↓reduceIte, sub_self]
      exact mul_nonneg (sq_nonneg _) (sub_nonneg.2 (by exact_mod_cast hpq))
  have key := setIntegral_cexp_eq_of_bracket hM hM2 hK hcont hA0 hAmono hAlip hst hS θ
  have hconv : ∀ r : ℝ≥0, ∫ ω in S, Complex.exp (Complex.I * θ * M r ω + θ ^ 2 * A r ω / 2) ∂P =
      (∫ ω in S, Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r' : ℝ => W r'.toNNReal ω) (min r (σ ω) : ℝ≥0)
          (u ω (min r (σ ω))) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r' : ℝ => W r'.toNNReal ω) (min r (σ ω) : ℝ≥0) φ : ℝ) : ℂ)
          / 2) ∂P) * Complex.exp (θ ^ 2 * (E₀ : ℂ) / 2) := by
    intro r
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hGae] with ω hω
    rw [hAG ω hω r, hMdef]
    simp only
    rw [integral_meanIntegrand_eq hφH hω (hGgood ω hω) u hu r, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hconv t, hconv s] at key
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) key

omit hE hκ hσ hσp hφc hφs hδ in
/-- At time `0` the tested mean is `(𝔥₀, φ) = ∫ u₀ φ` for any bounded harmonic extension `u₀` of the time-zero
boundary data. -/
theorem IsGoodTest.testMean_zero {ω : Ω} (hg : IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) ((0 : ℝ≥0) : ℝ) (u ω 0) z * φ z =
      ∫ z, u₀ z * φ z := by
  have hP := hg.1
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by simp) hg.2.2.1
  have hW0 : W 0 ω = 0 := hP.1
  have hdata : (fun i => VL i 0 ω - W 0 ω) = xL ∧ (fun i => VR i 0 ω - W 0 ω) = xR := by
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · rw [hW0, sub_zero]; exact hP.2.1 i
    · rw [hW0, sub_zero]; exact hP.2.2.1 i
  have hu0 := hu ω 0
  rw [hdata.1, hdata.2] at hu0
  have hxL : ∀ i, xL i ≤ 0 := fun i => by
    have := hP.2.2.2.2.2.2.2.1 0 hζ0 i
    simpa [hP.2.1 i, hW0] using this
  have hxR : ∀ i, 0 ≤ xR i := fun i => by
    have := hP.2.2.2.2.2.2.2.2.1 0 hζ0 i
    simpa [hP.2.2.1 i, hW0] using this
  have heq : EqOn (u ω 0) u₀ H := fun z hz => by
    rw [eqOn_meanHarmonic hxL hxR hu0 hz, eqOn_meanHarmonic hxL hxR hu₀ hz]
  congr 1; funext z
  by_cases hz : z ∈ tsupport φ
  · have hf : fwdMap (fun r : ℝ => W r.toNNReal ω) 0 z = z := hg.fwdMap_zero hφH hz
    simp only [couplingMean, NNReal.coe_zero, hf, logDerivFwd, intervalIntegral.integral_same,
      neg_zero, Complex.zero_im, mul_zero, sub_zero, heq (hφH hz)]
  · simp [eq_zero_of_notMem_tsupport' hz]

/-- **Optional stopping of the characteristic-function martingale at a protected stop** (Specification L550–L552,
used in the proof of Lemma 3.11 "(by (3.19))"):
`E[exp(iθ (𝔥_σ, φ) − θ² E_σ(φ)/2)] = exp(iθ (𝔥₀, φ) − θ² E₀(φ)/2)`, with `(𝔥₀, φ) = ∫ u₀ φ` and
`E₀(φ) = ∬ φ G φ`. -/
theorem integral_cexp_testMean_stopped {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (θ : ℝ) :
    ∫ ω, Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (σ ω) (u ω (σ ω)) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (σ ω) φ : ℝ) : ℂ) / 2) ∂P =
      Complex.exp (Complex.I * θ * ((∫ z, u₀ z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((greenEnergy0 φ : ℝ) : ℂ) / 2) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨G, -, hGc, -, hGgood⟩ := exists_goodSet hE hσp
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have h := setIntegral_cexp_testMean_eq hE hκ hσ hσp hφH hφc hφs hδ u hu
    (zero_le (a := N.toNNReal)) (S := univ) MeasurableSet.univ θ
  rw [setIntegral_univ, setIntegral_univ] at h
  have hl : ∀ᵐ ω ∂P, min N.toNNReal (σ ω) = σ ω := by
    filter_upwards [hGae] with ω hω
    have h1 := Real.toNNReal_le_toNNReal (hGgood ω hω).2.2.2.1
    rw [Real.toNNReal_coe] at h1
    exact min_eq_right h1
  refine (integral_congr_ae (hl.mono fun ω hω => by simp only [hω])).trans (h.trans ?_)
  have hr : ∀ᵐ ω ∂P, Complex.exp (Complex.I * θ *
        ((∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (min 0 (σ ω) : ℝ≥0)
          (u ω (min 0 (σ ω))) z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (min 0 (σ ω) : ℝ≥0) φ : ℝ) : ℂ)
          / 2) = Complex.exp (Complex.I * θ * ((∫ z, u₀ z * φ z : ℝ) : ℂ) -
        θ ^ 2 * ((greenEnergy0 φ : ℝ) : ℂ) / 2) := by
    filter_upwards [hGae] with ω hω
    have hg := hGgood ω hω
    rw [min_eq_left (zero_le (a := σ ω)), hg.testMean_zero hφH u hu hu₀, NNReal.coe_zero,
      hg.loewnerGreenEnergy_zero hφH]
  rw [integral_congr_ae hr, integral_const, probReal_univ, one_smul]

/-- The tested mean and the energy at `t ∧ σ` are almost everywhere measurable. -/
theorem aemeasurable_testMean_energy (t : ℝ≥0) :
    AEMeasurable (fun ω => ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (min t (σ ω) : ℝ≥0)
      (u ω (min t (σ ω))) z * φ z) P ∧
    AEMeasurable (fun ω => loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (min t (σ ω) : ℝ≥0) φ)
      P := by
  obtain ⟨G, -, hGc, hG0, hGgood⟩ := exists_goodSet hE hσp
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hM := martingale_meanIntegral hE hσ hG0 hGgood hφH hφc hφs hδ hκ hGc u hu
  have hQ := martingale_pairIntegral hE hσ hG0 hGgood hφH hφc hφs hδ hκ hGc u hu
  have hMm := ((hM.stronglyAdapted t).mono ((nullAugmented 𝓕 P).le t)).measurable
  have hQm := ((hQ.stronglyAdapted t).mono ((nullAugmented 𝓕 P).le t)).measurable
  constructor
  · refine hMm.aemeasurable.congr ?_
    filter_upwards [hGae] with ω hω
    exact integral_meanIntegrand_eq hφH hω (hGgood ω hω) u hu t
  · refine (hQm.sub (hMm.pow_const 2)).aemeasurable.congr ?_
    filter_upwards [hGae] with ω hω
    simp only [Pi.sub_apply]
    rw [integral_pairIntegrand_eq hE hσ hG0 hGgood hφH hφc hφs hδ hω t]
    ring

end CharFun

end Coupling

end InteractingSLE
