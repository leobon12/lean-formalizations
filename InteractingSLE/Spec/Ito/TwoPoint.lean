import InteractingSLE.Spec.Ito.TwoPointGen

/-!
# (3.17): `d⟨𝔥(y), 𝔥(z)⟩_t = −dG_t(y, z)`

Packet PROVE-T11-ITO (Specification L515–L527). For two points `y ≠ z` of `ℍ` and a stopping time `σ` protected for
both (as in `exists_martingale_couplingMean`, plus a separation `‖f_s(y) − f_s(z)‖ ≥ ε > 0` on `[0, σ]`),
`exists_martingale_couplingMean_mul_add_greenH`: `𝔥_{t∧σ}(y) 𝔥_{t∧σ}(z) + G(f_{t∧σ}(y), f_{t∧σ}(z))` agrees almost
surely, at every time, with a martingale. With (3.16) (`greenH_fwdMap_eq_sub_integral`) this is
`d⟨𝔥(y), 𝔥(z)⟩_t = −dG_t(y, z) = Im(2/f_t y) Im(2/f_t z) dt`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal Classical ComplexConjugate

namespace InteractingSLE

namespace Ito

variable {nL nR : ℕ}

/-! ### The two-point region and compact set -/

/-- Both points in `obsRegion` and `Γ_y ≠ Γ_z`. -/
def twoRegion (κ : ℝ) : Set ((Coord nL nR × Coord nL nR) × ℝ) :=
  {p | (p.1.1, p.2) ∈ obsRegion κ ∧ (p.1.2, p.2) ∈ obsRegion κ ∧ p.1.1.1 ≠ p.1.2.1}

theorem continuous_pairFst : Continuous fun p : (Coord nL nR × Coord nL nR) × ℝ => (p.1.1, p.2) :=
  continuous_fst.fst.prodMk continuous_snd

theorem continuous_pairSnd : Continuous fun p : (Coord nL nR × Coord nL nR) × ℝ => (p.1.2, p.2) :=
  continuous_fst.snd.prodMk continuous_snd

theorem isOpen_twoRegion (κ : ℝ) : IsOpen (twoRegion κ : Set ((Coord nL nR × Coord nL nR) × ℝ)) :=
  ((isOpen_obsRegion κ).preimage continuous_pairFst).inter
    (((isOpen_obsRegion κ).preimage continuous_pairSnd).inter
      (isOpen_ne_fun continuous_fst.fst.fst continuous_fst.snd.fst))

theorem sub_conj_ne_zero_of_mem {κ : ℝ} {p : (Coord nL nR × Coord nL nR) × ℝ}
    (hp : p ∈ twoRegion κ) : p.1.1.1 - conj p.1.2.1 ≠ 0 := by
  intro h
  have h1 := hp.1.1
  have h2 := hp.2.1.1
  have := congrArg Complex.im h
  simp only [coordF, Complex.sub_im, Complex.conj_im, Complex.zero_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero] at this h1 h2
  linarith

theorem contDiffOn_twoObs (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (twoObs κ ρL ρR) (twoRegion κ) := fun _ hp =>
  (((contDiffAt_onFst (contDiffAt_meanObs κ ρL ρR hp.1)).mul
    (contDiffAt_onSnd (contDiffAt_meanObs κ ρL ρR hp.2.1))).add
    (contDiffAt_greenObs (sub_conj_ne_zero_of_mem hp) (sub_ne_zero.2 hp.2.2))).contDiffWithinAt

/-- The two-point compact set. -/
def twoCompact (κ δ R ε : ℝ) : Set ((Coord nL nR × Coord nL nR) × ℝ) :=
  {p | (p.1.1, p.2) ∈ obsCompact κ δ R ∧ (p.1.2, p.2) ∈ obsCompact κ δ R ∧ ε ≤ ‖p.1.1.1 - p.1.2.1‖}

theorem isCompact_twoCompact (κ δ R ε : ℝ) :
    IsCompact (twoCompact κ δ R ε : Set ((Coord nL nR × Coord nL nR) × ℝ)) := by
  have hcl : IsClosed (twoCompact κ δ R ε : Set ((Coord nL nR × Coord nL nR) × ℝ)) :=
    ((isCompact_obsCompact κ δ R).isClosed.preimage continuous_pairFst).inter
      (((isCompact_obsCompact κ δ R).isClosed.preimage continuous_pairSnd).inter
        (isClosed_le continuous_const (continuous_fst.fst.fst.sub continuous_fst.snd.fst).norm))
  refine (isCompact_closedBall 0 R).of_isClosed_subset hcl fun p hp => ?_
  rw [mem_closedBall_zero_iff]
  have h1 := norm_prod_le_iff.1 hp.1.2.2.2
  have h2 := norm_prod_le_iff.1 hp.2.1.2.2.2
  exact norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨h1.1, h2.1⟩, h1.2⟩

theorem twoCompact_subset {κ δ R ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    (twoCompact κ δ R ε : Set ((Coord nL nR × Coord nL nR) × ℝ)) ⊆ twoRegion κ := fun p hp =>
  ⟨obsCompact_subset hδ hp.1, obsCompact_subset hδ hp.2.1, fun h => by
    have := hp.2.2; rw [h, sub_self, norm_zero] at this; linarith⟩

theorem obsCompact_mono {κ δ R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    (obsCompact κ δ R₁ : Set (Coord nL nR × ℝ)) ⊆ obsCompact κ δ R₂ := fun _ hp =>
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans h⟩

/-- Along the path, almost every time has no force point on the driver. -/
theorem ae_noCollision {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {T : ℝ≥0} (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hT : (T : ℝ≥0∞) < ζ) :
    ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) T → (∀ i, vL i s.toNNReal - w s.toNNReal ≠ 0) ∧
      ∀ i, vR i s.toNNReal - w s.toNNReal ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcolL, hcolR, -⟩ := hP
  have hL : ∀ i, ∀ᵐ s : ℝ, ¬ (0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
      w s.toNNReal = vL i s.toNNReal) := fun i => measure_eq_zero_iff_ae_notMem.1 (hcolL i)
  have hR : ∀ i, ∀ᵐ s : ℝ, ¬ (0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
      w s.toNNReal = vR i s.toNNReal) := fun i => measure_eq_zero_iff_ae_notMem.1 (hcolR i)
  filter_upwards [ae_all_iff.2 hL, ae_all_iff.2 hR] with s hsL hsR hs
  have hs0 : 0 ≤ s := hs.1.le
  have hsζ : (s.toNNReal : ℝ≥0∞) < ζ :=
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hT
  exact ⟨fun i => sub_ne_zero.2 fun h => hsL i ⟨hs0, hsζ, h.symm⟩,
    fun i => sub_ne_zero.2 fun h => hsR i ⟨hs0, hsζ, h.symm⟩⟩

/-! ### The martingale -/

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **(3.17)**: for `y ≠ z` in `ℍ` and a stopping time `σ` protected for both points (and separating them),
`𝔥_{t∧σ}(y) 𝔥_{t∧σ}(z) + G(f_{t∧σ}(y), f_{t∧σ}(z))` agrees almost surely, at every time, with a martingale. -/
theorem exists_martingale_couplingMean_mul_add_greenH
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {y z : ℂ}
    (hy : 0 < y.im) (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) y (σ ω) u) ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) y).im ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      (∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R) ∧
      ∀ s ≤ σ ω, ε ≤ ‖QuantumZipper.fwdMap (rpath (W · ω)) s y -
        QuantumZipper.fwdMap (rpath (W · ω)) s z‖)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
          (u ω (min t (σ ω))) y *
          couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
            (u ω (min t (σ ω))) z +
        QuantumZipper.greenH
          (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) y)
          (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) z) := by
  obtain ⟨hB, hWa, hVLa, hVRa, hpath⟩ := id hE
  have hP := hB.isProbabilityMeasure'
  set 𝓖 := nullAugmented 𝓕 P with h𝓖
  set good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω) ∧
    ((σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) y (σ ω) u) ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) y).im ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      (∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R) ∧
      ∀ s ≤ σ ω, ε ≤ ‖QuantumZipper.fwdMap (rpath (W · ω)) s y -
        QuantumZipper.fwdMap (rpath (W · ω)) s z‖) with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, hB.1.cont, hσp] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (measurableSet_nullAugmented_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
    rwa [compl_compl] at this
  obtain ⟨ω₀, hω₀⟩ : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have : P Gᶜ = 1 := by rw [h, compl_empty, measure_univ]
    rw [hGc] at this; exact zero_ne_one this
  obtain ⟨hP₀, -, hσ₀, hsoly₀, hsolz₀, hδy₀, hδz₀, hN₀, hR₀, hε₀⟩ := hGgood ω₀ hω₀
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR₀ 0 bot_le).1
  have hN0 : 0 ≤ N := (σ ω₀).coe_nonneg.trans hN₀
  -- the values at time `0`
  have hf0 : ∀ x : ℂ, 0 < x.im → (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω₀)) x (σ ω₀) u) →
      QuantumZipper.fwdMap (rpath (W · ω₀)) 0 x = x := fun x hx hsol => by
    obtain ⟨hwc, -, -, -⟩ := fwdMap_facts hP₀ hσ₀ hx hsol
    have h0 := fwdMap_eq_sub_add_integral_of_continuousOn (σ ω₀).coe_nonneg hwc hx hsol
      (s := 0) ⟨le_rfl, (σ ω₀).coe_nonneg⟩
    rw [intervalIntegral.integral_same, add_zero] at h0
    have hw0 : rpath (fun t => W t ω₀) 0 = 0 := by simpa [rpath] using hP₀.1
    rw [h0, hw0]; simp
  have hδb : ∀ x : ℂ, 0 < x.im → (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω₀)) x (σ ω₀) u) →
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω₀)) (σ ω₀) x).im → δ ≤ x.im := fun x hx hsol hδx => by
    obtain ⟨-, -, -, hanti⟩ := fwdMap_facts hP₀ hσ₀ hx hsol
    have := hanti ⟨le_rfl, (σ ω₀).coe_nonneg⟩ ⟨(σ ω₀).coe_nonneg, le_rfl⟩ (σ ω₀).coe_nonneg
    simp only at this
    rw [hf0 x hx hsol] at this
    exact hδx.trans this
  have hδy := hδb y hy hsoly₀ hδy₀
  have hδz := hδb z hz hsolz₀ hδz₀
  have hεyz : ε ≤ ‖y - z‖ := by
    have := hε₀ 0 bot_le
    rwa [NNReal.coe_zero, hf0 y hy hsoly₀, hf0 z hz hsolz₀] at this
  set R' := ‖y‖ + ‖z‖ + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2 with hR'
  have hRy : ‖y‖ + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2 ≤ R' := by
    rw [hR']; linarith [norm_nonneg z]
  have hRz : ‖z‖ + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2 ≤ R' := by
    rw [hR']; linarith [norm_nonneg y]
  have hR'y : ‖y‖ ≤ R' := by
    have : 0 ≤ (3 + Real.sqrt κ) * R := mul_nonneg (by positivity) hR0
    have : 0 ≤ 2 * N / δ := by positivity
    have : 0 ≤ 2 * N / δ ^ 2 := by positivity
    linarith
  have hR'z : ‖z‖ ≤ R' := by
    have : 0 ≤ (3 + Real.sqrt κ) * R := mul_nonneg (by positivity) hR0
    have : 0 ≤ 2 * N / δ := by positivity
    have : 0 ≤ 2 * N / δ ^ 2 := by positivity
    linarith
  have hKb0 : 0 ≤ varBound xL xR ρL ρR δ R N := by unfold varBound; positivity
  -- the modified Brownian motion and processes
  obtain ⟨hB', hB'c⟩ := isFilteredBrownianReal_modify hB hGm hGc fun ω hω => (hGgood ω hω).2.1
  set B' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then B t ω else 0 with hB'def
  set Λ : ℝ≥0 → Ω → Coord nL nR × Coord nL nR := fun t ω =>
    if ω ∈ G then (coordProc κ y W VL VR B t ω, coordProc κ z W VL VR B t ω)
    else (coordBase y, coordBase z) with hΛdef
  set lam : ℝ → Ω → Coord nL nR × Coord nL nR := fun s ω =>
    if ω ∈ G then (densityAt y ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s,
      densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s) else 0
    with hlamdef
  have hWc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGgood ω hω).1.2.2.2.1
  have hWa' := adaptedBefore_mono (le_nullAugmented 𝓕 P) hWa
  have hVLa' := fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVLa i)
  have hVRa' := fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVRa i)
  have hBm' := fun t => (hB.2.1 t).mono (le_nullAugmented 𝓕 P t) le_rfl
  have hΛm : ∀ t, Measurable[𝓖 t] fun ω => Λ (min t (σ ω)) ω := by
    intro t
    have hK : ∀ s, Measurable[𝓖 s] fun ω => (killedCoord κ y W VL VR B ζ G s ω,
        killedCoord κ z W VL VR B ζ G s ω) := fun s =>
      (measurable_killedCoord κ hWa' hVLa' hVRa' hBm' hWc hG0 hy s).prodMk
        (measurable_killedCoord κ hWa' hVLa' hVRa' hBm' hWc hG0 hz s)
    simp only [hΛdef]
    refine measurable_stopped_of_agree
      (X := fun s ω => (coordProc κ y W VL VR B s ω, coordProc κ z W VL VR B s ω)) hσ hK hG0
      (coordBase y, coordBase z) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
    · obtain ⟨-, -, hσζ, ⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩, -⟩ := hGgood ω hω
      have hsζ : (s : ℝ≥0∞) < ζ ω :=
        lt_of_le_of_lt (by exact_mod_cast hs : (s : ℝ≥0∞) ≤ σ ω) hσζ
      have h1 : ω ∈ aliveSet W ζ G y s := ⟨hω, hsζ, u₁,
        isForwardSol_of_le hu₁ s.coe_nonneg (by exact_mod_cast hs)⟩
      have h2 : ω ∈ aliveSet W ζ G z s := ⟨hω, hsζ, u₂,
        isForwardSol_of_le hu₂ s.coe_nonneg (by exact_mod_cast hs)⟩
      simp only [killedCoord, h1, h2, ↓reduceIte]
    · obtain ⟨hPω, hBω, hσζ, hsoly, hsolz, -⟩ := hGgood ω hω
      exact (continuousOn_coordAt hPω hσζ hy hsoly hBω).prodMk
        (continuousOn_coordAt hPω hσζ hz hsolz hBω)
  have hlam : ∀ ω, IntervalIntegrable (lam · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · obtain ⟨hPω, -, hσζ, hsoly, hsolz, -⟩ := hGgood ω hω
      have h1 := intervalIntegrable_densityAt (κ := κ) hPω hσζ hy hsoly
      have h2 := intervalIntegrable_densityAt (κ := κ) hPω hσζ hz hsolz
      simp only [hlamdef, hω, ↓reduceIte]
      rw [intervalIntegrable_iff] at h1 h2 ⊢
      exact h1.prodMk h2
    · simp only [hlamdef, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · obtain ⟨hPω, -, hσζ, hsoly, hsolz, -⟩ := hGgood ω hω
      have h1 := intervalIntegrable_densityAt (κ := κ) hPω hσζ hy hsoly
      have h2 := intervalIntegrable_densityAt (κ := κ) hPω hσζ hz hsolz
      have hT : (t : ℝ) ≤ σ ω := by exact_mod_cast ht
      have h1t := h1.mono_set (uIcc_subset_uIcc_left (by
        rw [uIcc_of_le (σ ω).coe_nonneg]; exact ⟨t.coe_nonneg, hT⟩))
      have h2t := h2.mono_set (uIcc_subset_uIcc_left (by
        rw [uIcc_of_le (σ ω).coe_nonneg]; exact ⟨t.coe_nonneg, hT⟩))
      have hpair : IntervalIntegrable (fun s => (densityAt y ρL ρR (W · ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) s, densityAt z ρL ρR (W · ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) s)) volume 0 t := by
        rw [intervalIntegrable_iff] at h1t h2t ⊢; exact h1t.prodMk h2t
      simp only [hΛdef, hlamdef, hω, ↓reduceIte, coordProc]
      have hfst := ((ContinuousLinearMap.fst ℝ (Coord nL nR) (Coord nL nR)).intervalIntegral_comp_comm
        hpair).symm
      have hsnd := ((ContinuousLinearMap.snd ℝ (Coord nL nR) (Coord nL nR)).intervalIntegral_comp_comm
        hpair).symm
      simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at hfst hsnd
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_add, hfst]
        exact coordAt_eq_add_integral hPω hσζ hy hsoly ht
      · rw [Prod.snd_add, hsnd]
        exact coordAt_eq_add_integral hPω hσζ hz hsolz ht
    · simp only [hΛdef, hlamdef, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖lam s ω‖ ≤
      varBound xL xR ρL ρR δ R N + varBound xL xR ρL ρR δ R N := by
    intro ω
    by_cases hω : ω ∈ G
    · obtain ⟨hPω, -, hσζ, hsoly, hsolz, hδyω, hδzω, hNω, hRω, -⟩ := hGgood ω hω
      have h1 := intervalIntegrable_densityAt (κ := κ) hPω hσζ hy hsoly
      have h2 := intervalIntegrable_densityAt (κ := κ) hPω hσζ hz hsolz
      have hb1 := integral_norm_densityAt_le (κ := κ) hPω hσζ hy hsoly hδ hδyω hNω
        fun s hs => ⟨(hRω s hs).2.2.1, (hRω s hs).2.2.2⟩
      have hb2 := integral_norm_densityAt_le (κ := κ) hPω hσζ hz hsolz hδ hδzω hNω
        fun s hs => ⟨(hRω s hs).2.2.1, (hRω s hs).2.2.2⟩
      simp only [hlamdef, hω, ↓reduceIte]
      refine (intervalIntegral.integral_mono_on (σ ω).coe_nonneg ?_ (h1.norm.add h2.norm)
        fun s _ => ?_).trans ?_
      · have hpair : IntervalIntegrable (fun s => (densityAt y ρL ρR (W · ω) (fun i t => VL i t ω)
            (fun i t => VR i t ω) s, densityAt z ρL ρR (W · ω) (fun i t => VL i t ω)
            (fun i t => VR i t ω) s)) volume 0 (σ ω) := by
          rw [intervalIntegrable_iff] at h1 h2 ⊢; exact h1.prodMk h2
        exact hpair.norm
      · exact norm_prod_le_iff.2 ⟨le_add_of_nonneg_right (norm_nonneg _),
          le_add_of_nonneg_left (norm_nonneg _)⟩
      · rw [intervalIntegral.integral_add h1.norm h2.norm]
        exact add_le_add hb1 hb2
    · simp only [hlamdef, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      linarith
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω → (Λ t ω, B' t ω) ∈ twoCompact κ δ R' ε := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · obtain ⟨hPω, -, hσζ, hsoly, hsolz, hδyω, hδzω, hNω, hRω, hεω⟩ := hGgood ω hω
      have hRb := fun s (hs : s ≤ σ ω) =>
        (⟨(hRω s hs).1, (hRω s hs).2.1, (hRω s hs).2.2.1, (hRω s hs).2.2.2⟩ :
          |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
      simp only [hΛdef, hB'def, hω, ↓reduceIte, coordProc]
      refine ⟨obsCompact_mono hRy (coordAt_mem_obsCompact hPω hσζ hy hsoly hδ hδyω hNω hRb ht),
        obsCompact_mono hRz (coordAt_mem_obsCompact hPω hσζ hz hsolz hδ hδzω hNω hRb ht), ?_⟩
      have e : (coordAt κ y (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
          (fun t => B t ω) t).1 - (coordAt κ z (fun t => W t ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (fun t => B t ω) t).1 =
          QuantumZipper.fwdMap (rpath (W · ω)) t y - QuantumZipper.fwdMap (rpath (W · ω)) t z := by
        simp only [coordAt]; ring
      rw [e]; exact hεω t ht
    · simp only [hΛdef, hB'def, hω, ↓reduceIte]
      have hR'0 : 0 ≤ R' := (norm_nonneg y).trans hR'y
      have hbase : ∀ x : ℂ, δ ≤ x.im → ‖x‖ ≤ R' →
          ((coordBase x, (0 : ℝ)) : Coord nL nR × ℝ) ∈ obsCompact κ δ R' := fun x hδx hx => by
        refine ⟨by simpa [coordF, coordBase] using hδx, fun i => by simpa [coordBase] using hδx,
          fun i => by simpa [coordBase] using hδx, ?_⟩
        rw [norm_prod_le_iff]
        refine ⟨?_, by simp only [norm_zero]; exact hR'0⟩
        simp only [coordBase]
        rw [norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
        exact ⟨hx, (pi_norm_le_iff_of_nonneg hR'0).2 fun _ => hx,
          (pi_norm_le_iff_of_nonneg hR'0).2 fun _ => hx, by simpa using hR'0⟩
      exact ⟨hbase y hδy hR'y, hbase z hδz hR'z, by simpa [coordBase] using hεyz⟩
  have _ : BorelSpace (Coord nL nR × Coord nL nR) := Prod.borelSpace
  obtain ⟨hMart⟩ := (⟨martingale_itoLocalized hB' hB'c (isOpen_twoRegion κ)
    (contDiffOn_twoObs κ ρL ρR) (isCompact_twoCompact κ δ R' ε) (twoCompact_subset hδ hε) hσ hΛm
    hlam hΛ hKb (by simpa only [hB'def] using hK)⟩ : Nonempty (Martingale _ 𝓖 P))
  refine ⟨_, hMart, ?_⟩
  filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω t
  obtain ⟨hPω, -, hσζ, hsoly, hsolz, -, -, -, -, hεω⟩ := hGgood ω hω
  simp only [hΛdef, hlamdef, hB'def, hω, ↓reduceIte]
  have hint0 : (∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen (twoObs κ ρL ρR)
      ((coordProc κ y W VL VR B s.toNNReal ω, coordProc κ z W VL VR B s.toNNReal ω), B s.toNNReal ω)
      (densityAt y ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s,
        densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s)) = 0 := by
    refine integral_eq_zero_of_ae (min t (σ ω)).coe_nonneg
      (by exact_mod_cast min_le_right t (σ ω)) ?_
    filter_upwards [ae_noCollision hPω hσζ] with s hs hsI
    obtain ⟨hcL, hcR⟩ := hs hsI
    have hs0 : 0 ≤ s := hsI.1.le
    have hsT : s.toNNReal ≤ σ ω := Real.toNNReal_le_iff_le_coe.2 hsI.2
    have hmy := mem_obsRegion_coordAt (κ := κ) (b := fun t => B t ω) hPω hσζ hy hsoly hsT
    have hmz := mem_obsRegion_coordAt (κ := κ) (b := fun t => B t ω) hPω hσζ hz hsolz hsT
    have hsep := hεω s.toNNReal hsT
    have hdy : densityAt y ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s =
        coordDensity ρL ρR (fun i => VL i s.toNNReal ω - W s.toNNReal ω)
          (fun i => VR i s.toNNReal ω - W s.toNNReal ω)
          (coordF κ ((coordProc κ y W VL VR B s.toNNReal ω, B s.toNNReal ω) : Coord nL nR × ℝ)) := by
      simp only [coordProc]; rw [coordF_coordAt, Real.coe_toNNReal _ hs0]; rfl
    have hdz : densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s =
        coordDensity ρL ρR (fun i => VL i s.toNNReal ω - W s.toNNReal ω)
          (fun i => VR i s.toNNReal ω - W s.toNNReal ω)
          (coordF κ ((coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω) : Coord nL nR × ℝ)) := by
      simp only [coordProc]; rw [coordF_coordAt, Real.coe_toNNReal _ hs0]; rfl
    rw [hdy, hdz]
    refine itoGen_twoObs_eq_zero hκ ρL ρR
      (p := ((coordProc κ y W VL VR B s.toNNReal ω, coordProc κ z W VL VR B s.toNNReal ω),
        B s.toNNReal ω)) hmy hmz ?_ (fun i => ?_) (fun i => ?_) (fun i => ?_) (fun i => ?_) hcL hcR
    · show coordF κ ((coordAt κ y (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
          (fun t => B t ω) s.toNNReal, B s.toNNReal ω) : Coord nL nR × ℝ) ≠
        coordF κ ((coordAt κ z (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
          (fun t => B t ω) s.toNNReal, B s.toNNReal ω) : Coord nL nR × ℝ)
      rw [coordF_coordAt, coordF_coordAt]
      intro h; rw [h, sub_self, norm_zero] at hsep; linarith
    all_goals
      show _ = coordF κ ((coordAt κ _ (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
        (fun t => B t ω) s.toNNReal, B s.toNNReal ω) : Coord nL nR × ℝ) - _
      rw [coordF_coordAt]; rfl
  rw [hint0, sub_zero]
  have hmy : meanObs κ ρL ρR (coordProc κ y W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) =
      couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) (u ω (min t (σ ω))) y :=
    (couplingMean_eq_meanObs hPω hσζ hy hsoly (min_le_right t (σ ω)) (hu ω _)).symm
  have hmz : meanObs κ ρL ρR (coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) =
      couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) (u ω (min t (σ ω))) z :=
    (couplingMean_eq_meanObs hPω hσζ hz hsolz (min_le_right t (σ ω)) (hu ω _)).symm
  have hG : QuantumZipper.greenH (coordProc κ y W VL VR B (min t (σ ω)) ω).1
      (coordProc κ z W VL VR B (min t (σ ω)) ω).1 =
      QuantumZipper.greenH
        (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) y)
        (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) z) := by
    have h := QuantumZipper.FwdClock.greenH_sub_ofReal
      ((coordProc κ y W VL VR B (min t (σ ω)) ω).1) ((coordProc κ z W VL VR B (min t (σ ω)) ω).1)
      (Real.sqrt κ * B (min t (σ ω)) ω)
    rw [← h]
    simp only [coordProc, coordAt, Complex.ofReal_mul, add_sub_cancel_right]
    rfl
  simp only [twoObs, onFst, onSnd, greenObs]
  rw [hmy, hmz, hG]

end Martingale

end Ito

end InteractingSLE
