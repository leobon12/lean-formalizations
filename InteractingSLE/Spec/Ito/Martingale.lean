import InteractingSLE.Spec.Ito.Localize
import InteractingSLE.Spec.Ito.Measurability
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension

/-!
# (3.15): the mean `𝔥_t(z)` is a continuous local martingale

Packet PROVE-T11-ITO (Specification §3.3 L500–L505, graph nodes `SPEC.thm-1.1#ito-derivatives`, `SPEC.eq-3.15`,
`SPEC.thm-2.4#converse`). For a solution of the frozen `IsIntegratedSLEEvolution` (any filtration `𝓕`, weak solution)
and a point `z ∈ ℍ`:

* `exists_martingale_coordObs` (**Itô's formula for the Loewner coordinates**): for every function `Φ` that is `C³`
  on `obsRegion` and every *protected* stopping time `σ` of the null-augmented filtration (`σ < ζ`, `z` has a forward
  solution on `[0, σ]` with `Im f_σ(z) ≥ δ > 0`, `σ ≤ N`, `|W|, |B|, |V| ≤ R` on `[0, σ]`, almost surely),
  `Φ(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} (∂_Λ Φ · λ_s + ½ ∂²_x Φ)(Λ_s, B_s) ds` agrees almost surely, at all times, with
  a martingale. With `Φ = log (Γ − √κ x)` this is `d log f_t(z) = ((4−κ)/(2f²) − μ/f) dt − (√κ/f) dB` (the
  generator is computed in the handoff); it is the Itô-derivative step (a) of the packet.
* `exists_martingale_couplingMean` (**(3.15)**): the frozen mean `𝔥_{t∧σ}(z) = couplingMean …` (with any bounded
  harmonic extensions of the boundary data) agrees almost surely, at all times, with a martingale; the drift vanishes
  (`itoGen_meanObs_eq_zero`). Every bounded stopping time strictly before `ζ ∧ τ(z)` is a limit of protected ones
  (the protections are bounds on continuous quantities over a compact time interval inside `[0, ζ ∧ τ(z))`), so this
  is the statement "`𝔥_t(z)` is a continuous local martingale up to `ζ ∧ τ(z)`" in the form used by the proof of
  Theorem 1.1. The coefficient of `dB_t` is `∂_x meanObs = Im(2/f_t(z))` (`partialSnd_meanObs_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Itô's formula for the Loewner coordinates of an integrated `SLE_κ(ρ)` evolution**, localized at a protected
stopping time `σ` of the null-augmented filtration: for `Φ` of class `C³` on `obsRegion`, the process
`Φ(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} itoGen Φ (Λ_s, B_s) λ_s ds` agrees almost surely, at every time, with a martingale. -/
theorem exists_martingale_coordObs
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {z : ℂ} (hz : 0 < z.im)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    {δ R N : ℝ} (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    {Φ : Coord nL nR × ℝ → ℝ} (hΦ : ContDiffOn ℝ 3 Φ (obsRegion κ)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = Φ (coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen Φ
          (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
          (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s) := by
  obtain ⟨hB, hWa, hVLa, hVRa, hpath⟩ := hE
  have hP := hB.isProbabilityMeasure'
  set 𝓖 := nullAugmented 𝓕 P with h𝓖
  -- the good event
  set good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω) ∧
    ((σ ω : ℝ≥0∞) < ζ ω ∧ (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    with hgood
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
  -- the constants
  obtain ⟨hP₀, -, hσ₀, hsol₀, hδ₀, hN₀, hR₀⟩ := hGgood ω₀ hω₀
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR₀ 0 bot_le).1
  have hN0 : 0 ≤ N := (σ ω₀).coe_nonneg.trans hN₀
  have hδz : δ ≤ z.im := by
    obtain ⟨hwc, -, -, hanti⟩ := fwdMap_facts hP₀ hσ₀ hz hsol₀
    have h0 := fwdMap_eq_sub_add_integral_of_continuousOn (σ ω₀).coe_nonneg hwc hz hsol₀
      (s := 0) ⟨le_rfl, (σ ω₀).coe_nonneg⟩
    rw [intervalIntegral.integral_same, add_zero] at h0
    have hw0 : rpath (fun t => W t ω₀) 0 = 0 := by simpa [rpath] using hP₀.1
    have := hanti ⟨le_rfl, (σ ω₀).coe_nonneg⟩ ⟨(σ ω₀).coe_nonneg, le_rfl⟩ (σ ω₀).coe_nonneg
    simp only at this
    rw [h0, hw0] at this
    simp only [Complex.ofReal_zero, sub_zero] at this
    exact hδ₀.trans this
  set R' := ‖z‖ + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2 with hR'
  have hR'z : ‖z‖ ≤ R' := by
    have : 0 ≤ (3 + Real.sqrt κ) * R := mul_nonneg (by positivity) hR0
    have : 0 ≤ 2 * N / δ := by positivity
    have : 0 ≤ 2 * N / δ ^ 2 := by positivity
    linarith
  have hKb0 : 0 ≤ varBound xL xR ρL ρR δ R N := by unfold varBound; positivity
  -- the modified Brownian motion and processes
  obtain ⟨hB', hB'c⟩ := isFilteredBrownianReal_modify hB hGm hGc fun ω hω => (hGgood ω hω).2.1
  set B' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then B t ω else 0 with hB'def
  set Λ : ℝ≥0 → Ω → Coord nL nR := fun t ω =>
    if ω ∈ G then coordProc κ z W VL VR B t ω else coordBase z with hΛdef
  set lam : ℝ → Ω → Coord nL nR := fun s ω =>
    if ω ∈ G then densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s else 0
    with hlamdef
  have hWc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGgood ω hω).1.2.2.2.1
  -- adaptedness of the stopped coordinates
  have hΛm : ∀ t, Measurable[𝓖 t] fun ω => Λ (min t (σ ω)) ω := by
    intro t
    have hK := fun s => measurable_killedCoord κ (adaptedBefore_mono (le_nullAugmented 𝓕 P) hWa)
      (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVLa i))
      (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVRa i))
      (fun t => (hB.2.1 t).mono (le_nullAugmented 𝓕 P t) le_rfl) hWc hG0 hz (VL := VL) (VR := VR)
      (B := B) s
    simp only [hΛdef]
    refine measurable_stopped_of_agree (X := coordProc κ z W VL VR B) hσ hK hG0 (coordBase z)
      (fun ω hω s hs => ?_) (fun ω hω => ?_) t
    · obtain ⟨-, -, hσζ, ⟨u, hu⟩, -⟩ := hGgood ω hω
      have halive : ω ∈ aliveSet W ζ G z s := ⟨hω, lt_of_le_of_lt (by exact_mod_cast hs) hσζ, u,
        isForwardSol_of_le hu s.coe_nonneg (by exact_mod_cast hs)⟩
      simp only [killedCoord, halive, ↓reduceIte]
    · obtain ⟨hPω, hBω, hσζ, hsol, -⟩ := hGgood ω hω
      exact continuousOn_coordAt hPω hσζ hz hsol hBω
  -- pathwise hypotheses
  have hlam : ∀ ω, IntervalIntegrable (lam · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · obtain ⟨hPω, -, hσζ, hsol, -⟩ := hGgood ω hω
      simpa only [hlamdef, hω, ↓reduceIte] using intervalIntegrable_densityAt (κ := κ) hPω hσζ hz hsol
    · simp only [hlamdef, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · obtain ⟨hPω, -, hσζ, hsol, -⟩ := hGgood ω hω
      simp only [hΛdef, hlamdef, hω, ↓reduceIte, coordProc]
      exact coordAt_eq_add_integral hPω hσζ hz hsol ht
    · simp only [hΛdef, hlamdef, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖lam s ω‖ ≤ varBound xL xR ρL ρR δ R N := by
    intro ω
    by_cases hω : ω ∈ G
    · obtain ⟨hPω, -, hσζ, hsol, hδω, hNω, hRω⟩ := hGgood ω hω
      simpa only [hlamdef, hω, ↓reduceIte] using integral_norm_densityAt_le hPω hσζ hz hsol hδ hδω
        hNω fun s hs => ⟨(hRω s hs).2.2.1, (hRω s hs).2.2.2⟩
    · simp only [hlamdef, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact hKb0
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω → (Λ t ω, B' t ω) ∈ obsCompact κ δ R' := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · obtain ⟨hPω, -, hσζ, hsol, hδω, hNω, hRω⟩ := hGgood ω hω
      simp only [hΛdef, hB'def, hω, ↓reduceIte, coordProc]
      exact coordAt_mem_obsCompact hPω hσζ hz hsol hδ hδω hNω
        (fun s hs => ⟨(hRω s hs).1, (hRω s hs).2.1, (hRω s hs).2.2.1, (hRω s hs).2.2.2⟩) ht
    · simp only [hΛdef, hB'def, hω, ↓reduceIte]
      refine ⟨by simpa [coordF, coordBase] using hδz, fun i => by simpa [coordBase] using hδz,
        fun i => by simpa [coordBase] using hδz, ?_⟩
      rw [norm_prod_le_iff]
      refine ⟨?_, by simp only [norm_zero]; exact (norm_nonneg z).trans hR'z⟩
      simp only [coordBase]
      rw [norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
      have hR'0 : 0 ≤ R' := (norm_nonneg z).trans hR'z
      refine ⟨hR'z, (pi_norm_le_iff_of_nonneg hR'0).2 fun _ => hR'z,
        (pi_norm_le_iff_of_nonneg hR'0).2 fun _ => hR'z, by simpa using hR'0⟩
  obtain ⟨hMart⟩ := (⟨martingale_itoLocalized hB' hB'c (isOpen_obsRegion κ) hΦ
    (isCompact_obsCompact κ δ R') (obsCompact_subset hδ) hσ hΛm hlam hΛ hKb
      (by simpa only [hB'def] using hK)⟩ :
      Nonempty (Martingale _ 𝓖 P))
  refine ⟨_, hMart, ?_⟩
  filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω t
  simp only [hΛdef, hlamdef, hB'def, hω, ↓reduceIte]

/-- The integral of the generator along the path vanishes when the generator vanishes a.e. on `(0, σ]`. -/
theorem integral_eq_zero_of_ae {g : ℝ → ℝ} {T a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (h : ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) T → g s = 0) : ∫ s in (0 : ℝ)..a, g s = 0 := by
  calc ∫ s in (0 : ℝ)..a, g s = ∫ _ in (0 : ℝ)..a, (0 : ℝ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [h] with s hs hsa
        rw [uIoc_of_le ha] at hsa
        exact hs ⟨hsa.1, hsa.2.trans haT⟩
    _ = 0 := intervalIntegral.integral_zero

/-- **(3.15): the mean `𝔥_t(z)` is a continuous local martingale.** Let `(W, V, B, ζ)` solve the frozen
`IsIntegratedSLEEvolution` with `κ > 0`, `z ∈ ℍ`, and let `σ` be a protected stopping time of the null-augmented
filtration (`σ < ζ`, a forward solution for `z` on `[0, σ]` with `Im f_σ(z) ≥ δ > 0`, `σ ≤ N`, `|W|, |B|, |V| ≤ R`
on `[0, σ]`, almost surely). For any bounded harmonic extensions `u ω s` of the boundary data at the centred
positions, the stopped frozen mean `𝔥_{t∧σ}(z) = couplingMean κ W (t∧σ) (u ω (t∧σ)) z` agrees almost surely, at
every time, with a martingale. (The martingale part is `∫ Im(2/f_s(z)) dB_s`: see
`exists_martingale_couplingMean_sq` and `exists_martingale_couplingMean_mul_B`.) -/
theorem exists_martingale_couplingMean
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ}
    (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
        (u ω (min t (σ ω))) z := by
  obtain ⟨M, hM, hae⟩ := exists_martingale_coordObs hE hz hσ hδ hσp
    (contDiffOn_meanObs κ ρL ρR (n := 3))
  refine ⟨M, hM, ?_⟩
  filter_upwards [hae, hE.2.2.2.2, hσp] with ω hMω hPω hσω t
  obtain ⟨hσζ, hsol, -⟩ := hσω
  have h0 : (∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen (meanObs κ ρL ρR)
      (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
      (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s)) = 0 :=
    integral_eq_zero_of_ae (min t (σ ω)).coe_nonneg (by exact_mod_cast min_le_right t (σ ω))
      (ae_itoGen_meanObs_coordAt hκ hPω hσζ hz hsol)
  rw [hMω t, h0, sub_zero]
  exact (couplingMean_eq_meanObs hPω hσζ hz hsol (min_le_right t (σ ω)) (hu ω _)).symm

end Ito

end InteractingSLE
