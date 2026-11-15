/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Bracket
import InteractingSLE.Spec.Sec2.RestartEvolution

/-!
# Itô's formula for an evolution started from a random state

Packet PROVE-LOCEXT-M. The Itô results of PROVE-T11-ITO (`Ito.exists_martingale_coordObs`, (3.15)
`Ito.exists_martingale_couplingMean`, the cross bracket `Ito.exists_martingale_couplingMean_mul_B`) are stated for the frozen
`IsIntegratedSLEEvolution`, whose force points start at deterministic positions. After a restart at a stopping time the
positions are random (`IsIntegratedSLEEvolutionFrom`, PROVE-RESTART). The proofs only use the start pathwise and through
the bounded-variation constant `varBound`, which is monotone in the positions and bounded by its value at positions of
size `R` on the protection event (`|V_0| ≤ R`). This file restates the three results for a random start:

* `varBound_le_of_abs_le`: `varBound x y … ≤ varBound R R …` when `|x|, |y| ≤ R`;
* `exists_martingale_coordObs_on`: Itô's formula for the Loewner coordinates at a stopping time that protects `z` on an
  event `E` of time `0` and vanishes off `E` (a random start is localized by such events, e.g. `{|x| < k}`);
* `exists_martingale_couplingMean_on`: (3.15), `𝔥_{t∧σ}(z)` agrees a.s. on `E` with a martingale;
* `exists_martingale_couplingMean_mul_B_on`: `𝔥_{t∧σ}(z) B_{t∧σ} − ∫₀^{t∧σ} Im(2/f_s(z)) ds` agrees a.s. on `E` with
  a martingale.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace LocalExt

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The bounded-variation constant is bounded by its value at positions of size `R`. -/
theorem varBound_le_of_abs_le {x : Fin nL → ℝ} {y : Fin nR → ℝ} {δ R N : ℝ} (hx : ∀ i, |x i| ≤ R)
    (hy : ∀ j, |y j| ≤ R) :
    varBound x y ρL ρR δ R N ≤ varBound (fun _ : Fin nL => R) (fun _ : Fin nR => R) ρL ρR δ R N := by
  unfold varBound
  refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)) (Finset.sum_le_sum fun j _ => ?_)
  · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (add_le_add_left ((hx i).trans (le_abs_self R)) _)
      zero_le_two) (by positivity)
  · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (add_le_add_left ((hy j).trans (le_abs_self R)) _)
      zero_le_two) (by positivity)

/-- **Itô's formula for the Loewner coordinates of an evolution from a random start, on an initial event.** Let `E` be an
event of the null-augmented filtration at time `0` and `σ` a stopping time with `σ = 0` off `E` that protects `z` on `E`
(`σ < ζ`, `z` alive at `σ` with `Im f_σ(z) ≥ δ > 0`, `σ ≤ N`, `|W|, |B|, |V| ≤ R` on `[0, σ]`). Then
`Φ(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} itoGen Φ (Λ_s, B_s) λ_s ds` agrees almost surely on `E`, at every time, with a martingale
(`Ito.exists_martingale_coordObs` for `IsIntegratedSLEEvolutionFrom`; the bounded-variation constant is taken at
positions of size `R`). -/
theorem exists_martingale_coordObs_on
    (hE : IsIntegratedSLEEvolutionFrom κ ρL ρR P 𝓕 xL xR W VL VR B ζ) {z : ℂ}
    {E : Set Ω} (hE0 : MeasurableSet[nullAugmented 𝓕 P 0] E)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσE : ∀ ω ∉ E, σ ω = 0)
    {δ R N : ℝ} (hδ : 0 < δ) (hδz : δ ≤ z.im) (hR0 : 0 ≤ R) (hN0 : 0 ≤ N)
    (hσp : ∀ᵐ ω ∂P, ω ∈ E → (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    {Φ : Coord nL nR × ℝ → ℝ} (hΦ : ContDiffOn ℝ 3 Φ (obsRegion κ)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ω ∈ E → ∀ t,
      M t ω = Φ (coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen Φ
          (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
          (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s) := by
  obtain ⟨hB, -, -, hWa, hVLa, hVRa, hpath⟩ := hE
  have hP := hB.isProbabilityMeasure'
  have hz : 0 < z.im := lt_of_lt_of_le hδ hδz
  set 𝓖 := nullAugmented 𝓕 P with h𝓖
  -- the good event
  set good : Ω → Prop := fun ω => IsIntegratedSLEPath κ (xL ω) (xR ω) ρL ρR (fun t => W t ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω) ∧ B 0 ω = 0 ∧
    (ω ∈ E → (σ ω : ℝ≥0∞) < ζ ω ∧ (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, hB.1.cont, hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero, hσp] with ω h1 h2 h0 h3
      using ⟨h1, h2, h0, h3⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (measurableSet_nullAugmented_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
    rwa [compl_compl] at this
  have hGE0 : MeasurableSet[𝓖 0] (G ∩ E) := hG0.inter hE0
  set R' := ‖z‖ + (3 + Real.sqrt κ) * R + 2 * N / δ + 2 * N / δ ^ 2 with hR'
  have hR'z : ‖z‖ ≤ R' := by
    have : 0 ≤ (3 + Real.sqrt κ) * R := mul_nonneg (by positivity) hR0
    have : 0 ≤ 2 * N / δ := by positivity
    have : 0 ≤ 2 * N / δ ^ 2 := by positivity
    linarith
  have hKb0 : 0 ≤ varBound (fun _ : Fin nL => R) (fun _ : Fin nR => R) ρL ρR δ R N := by
    unfold varBound; positivity
  -- the modified Brownian motion and processes
  obtain ⟨hB', hB'c⟩ := isFilteredBrownianReal_modify hB hGm hGc fun ω hω => (hGgood ω hω).2.1
  set B' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then B t ω else 0 with hB'def
  set Λ : ℝ≥0 → Ω → Coord nL nR := fun t ω =>
    if ω ∈ G ∩ E then coordProc κ z W VL VR B t ω else coordBase z with hΛdef
  set lam : ℝ → Ω → Coord nL nR := fun s ω =>
    if ω ∈ G ∩ E then densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s else 0
    with hlamdef
  have hWc : ∀ ω ∈ G ∩ E, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGgood ω hω.1).1.2.2.2.1
  have hBG : ∀ ω ∈ G, B 0 ω = 0 := fun ω hω => (hGgood ω hω).2.2.1
  have hprot := fun ω (hω : ω ∈ G ∩ E) => (hGgood ω hω.1).2.2.2 hω.2
  -- adaptedness of the stopped coordinates
  have hΛm : ∀ t, Measurable[𝓖 t] fun ω => Λ (min t (σ ω)) ω := by
    intro t
    have hK := fun s => measurable_killedCoord κ (adaptedBefore_mono (le_nullAugmented 𝓕 P) hWa)
      (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVLa i))
      (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVRa i))
      (fun t => (hB.2.1 t).mono (le_nullAugmented 𝓕 P t) le_rfl) hWc hGE0 hz (VL := VL) (VR := VR)
      (B := B) s
    simp only [hΛdef]
    have h1 : ∀ ω ∈ G ∩ E, ∀ s : ℝ≥0, s ≤ σ ω → killedCoord κ z W VL VR B ζ (G ∩ E) s ω =
        coordProc κ z W VL VR B s ω := by
      intro ω hω s hs
      obtain ⟨hσζ, ⟨u, hu⟩, -⟩ := hprot ω hω
      have halive : ω ∈ aliveSet W ζ (G ∩ E) z s := ⟨hω, lt_of_le_of_lt (by exact_mod_cast hs) hσζ, u,
        isForwardSol_of_le hu s.coe_nonneg (by exact_mod_cast hs)⟩
      simp only [killedCoord, halive, ↓reduceIte]
    have h2 : ∀ ω ∈ G ∩ E, ContinuousOn (fun s => coordProc κ z W VL VR B s ω) (Iic (σ ω)) := by
      intro ω hω
      obtain ⟨hσζ, hsol, -⟩ := hprot ω hω
      exact continuousOn_coordAt (hGgood ω hω.1).1 hσζ hz hsol (hGgood ω hω.1).2.1
    have h := measurable_stopped_of_agree (X := coordProc κ z W VL VR B) hσ hK hGE0 (coordBase z) h1 h2 t
    convert h using 3
  -- pathwise hypotheses
  have hlam : ∀ ω, IntervalIntegrable (lam · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G ∩ E
    · obtain ⟨hσζ, hsol, -⟩ := hprot ω hω
      simpa only [hlamdef, hω, ↓reduceIte] using
        intervalIntegrable_densityAt (κ := κ) (hGgood ω hω.1).1 hσζ hz hsol
    · simp only [hlamdef, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G ∩ E
    · obtain ⟨hσζ, hsol, -⟩ := hprot ω hω
      simp only [hΛdef, hlamdef, hω, ↓reduceIte, coordProc]
      exact coordAt_eq_add_integral (hGgood ω hω.1).1 hσζ hz hsol ht
    · simp only [hΛdef, hlamdef, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖lam s ω‖ ≤
      varBound (fun _ : Fin nL => R) (fun _ : Fin nR => R) ρL ρR δ R N := by
    intro ω
    by_cases hω : ω ∈ G ∩ E
    · have hPω := (hGgood ω hω.1).1
      obtain ⟨hσζ, hsol, hδω, hNω, hRω⟩ := hprot ω hω
      have h1 := integral_norm_densityAt_le hPω hσζ hz hsol hδ hδω
        hNω fun s hs => ⟨(hRω s hs).2.2.1, (hRω s hs).2.2.2⟩
      have h2 := varBound_le_of_abs_le (x := xL ω) (y := xR ω) (ρL := ρL) (ρR := ρR) (δ := δ) (N := N)
        (fun i => by rw [← hPω.2.1 i]; exact (hRω 0 bot_le).2.2.1 i)
        (fun i => by rw [← hPω.2.2.1 i]; exact (hRω 0 bot_le).2.2.2 i)
      simpa only [hlamdef, hω, ↓reduceIte] using h1.trans h2
    · simp only [hlamdef, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact hKb0
  have hbase : ∀ b : ℝ, b = 0 → ((coordBase z, b) : Coord nL nR × ℝ) ∈ obsCompact κ δ R' := by
    intro b hb
    subst hb
    refine ⟨by simpa [coordF, coordBase] using hδz, fun i => by simpa [coordBase] using hδz,
      fun i => by simpa [coordBase] using hδz, ?_⟩
    rw [norm_prod_le_iff]
    refine ⟨?_, by simp only [norm_zero]; exact (norm_nonneg z).trans hR'z⟩
    simp only [coordBase]
    rw [norm_prod_le_iff, norm_prod_le_iff, norm_prod_le_iff]
    have hR'0 : 0 ≤ R' := (norm_nonneg z).trans hR'z
    exact ⟨hR'z, (pi_norm_le_iff_of_nonneg hR'0).2 fun _ => hR'z,
      (pi_norm_le_iff_of_nonneg hR'0).2 fun _ => hR'z, by simpa using hR'0⟩
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω → (Λ t ω, B' t ω) ∈ obsCompact κ δ R' := by
    intro ω t ht
    by_cases hω : ω ∈ G ∩ E
    · obtain ⟨hσζ, hsol, hδω, hNω, hRω⟩ := hprot ω hω
      simp only [hΛdef, hB'def, hω, hω.1, ↓reduceIte, coordProc]
      exact coordAt_mem_obsCompact (hGgood ω hω.1).1 hσζ hz hsol hδ hδω hNω
        (fun s hs => ⟨(hRω s hs).1, (hRω s hs).2.1, (hRω s hs).2.2.1, (hRω s hs).2.2.2⟩) ht
    · simp only [hΛdef, hω, ↓reduceIte]
      refine hbase _ ?_
      by_cases hωG : ω ∈ G
      · have hωE : ω ∉ E := fun h => hω ⟨hωG, h⟩
        have ht0 : t = 0 := le_antisymm (ht.trans (hσE ω hωE).le) bot_le
        simp only [hB'def, hωG, ↓reduceIte, ht0, hBG ω hωG]
      · simp only [hB'def, hωG, ↓reduceIte]
  obtain ⟨hMart⟩ := (⟨martingale_itoLocalized hB' hB'c (isOpen_obsRegion κ) hΦ
    (isCompact_obsCompact κ δ R') (obsCompact_subset hδ) hσ hΛm hlam hΛ hKb
      (by simpa only [hB'def] using hK)⟩ :
      Nonempty (Martingale _ 𝓖 P))
  refine ⟨_, hMart, ?_⟩
  filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω hωE t
  have hωGE : ω ∈ G ∩ E := ⟨hω, hωE⟩
  simp only [hΛdef, hlamdef, hB'def, hω, hωGE, ↓reduceIte]

/-- **(3.15) for an evolution from a random start, on an initial event**: the stopped mean `𝔥_{t∧σ}(z)` agrees a.s. on
`E` with a martingale. -/
theorem exists_martingale_couplingMean_on
    (hE : IsIntegratedSLEEvolutionFrom κ ρL ρR P 𝓕 xL xR W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    {E : Set Ω} (hE0 : MeasurableSet[nullAugmented 𝓕 P 0] E)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσE : ∀ ω ∉ E, σ ω = 0)
    {δ R N : ℝ} (hδ : 0 < δ) (hδz : δ ≤ z.im) (hR0 : 0 ≤ R) (hN0 : 0 ≤ N)
    (hσp : ∀ᵐ ω ∂P, ω ∈ E → (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ω ∈ E → ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
        (u ω (min t (σ ω))) z := by
  have hz : 0 < z.im := lt_of_lt_of_le hδ hδz
  obtain ⟨M, hM, hae⟩ := exists_martingale_coordObs_on hE hE0 hσ hσE hδ hδz hR0 hN0 hσp
    (contDiffOn_meanObs κ ρL ρR (n := 3))
  refine ⟨M, hM, ?_⟩
  filter_upwards [hae, hE.2.2.2.2.2.2, hσp] with ω hMω hPω hσω hωE t
  obtain ⟨hσζ, hsol, -⟩ := hσω hωE
  have h0 : (∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen (meanObs κ ρL ρR)
      (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
      (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s)) = 0 :=
    integral_eq_zero_of_ae (min t (σ ω)).coe_nonneg (by exact_mod_cast min_le_right t (σ ω))
      (ae_itoGen_meanObs_coordAt hκ hPω hσζ hz hsol)
  rw [hMω hωE t, h0, sub_zero]
  exact (couplingMean_eq_meanObs hPω hσζ hz hsol (min_le_right t (σ ω)) (hu ω _)).symm

/-- **The cross bracket for an evolution from a random start, on an initial event**:
`𝔥_{t∧σ}(z) B_{t∧σ} − ∫₀^{t∧σ} Im(2/f_s(z)) ds` agrees a.s. on `E` with a martingale. -/
theorem exists_martingale_couplingMean_mul_B_on
    (hE : IsIntegratedSLEEvolutionFrom κ ρL ρR P 𝓕 xL xR W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    {E : Set Ω} (hE0 : MeasurableSet[nullAugmented 𝓕 P 0] E)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσE : ∀ ω ∉ E, σ ω = 0)
    {δ R N : ℝ} (hδ : 0 < δ) (hδz : δ ≤ z.im) (hR0 : 0 ≤ R) (hN0 : 0 ≤ N)
    (hσp : ∀ᵐ ω ∂P, ω ∈ E → (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ω ∈ E → ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
          (u ω (min t (σ ω))) z * B (min t (σ ω)) ω -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          (2 / QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im := by
  have hz : 0 < z.im := lt_of_lt_of_le hδ hδz
  obtain ⟨M, hM, hae⟩ := exists_martingale_coordObs_on hE hE0 hσ hσE hδ hδz hR0 hN0 hσp
    (Φ := fun q => meanObs κ ρL ρR q * obsX q)
    ((contDiffOn_meanObs κ ρL ρR (n := 3)).mul contDiff_obsX.contDiffOn)
  refine ⟨M, hM, ?_⟩
  filter_upwards [hae, hE.2.2.2.2.2.2, hσp] with ω hMω hPω hσω hωE t
  obtain ⟨hσζ, hsol, -⟩ := hσω hωE
  have h0 := integral_congr_of_ae_Ioc (min t (σ ω)).coe_nonneg
    (by exact_mod_cast min_le_right t (σ ω))
    (ae_itoGen_meanObs_mul_obsX_coordAt hκ hPω hσζ hz hsol)
  rw [hMω hωE t]
  rw [show (∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen (fun q => meanObs κ ρL ρR q * obsX q)
      (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
      (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s)) = _ from h0]
  have hm : couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
      (u ω (min t (σ ω))) z =
      meanObs κ ρL ρR (coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) :=
    couplingMean_eq_meanObs hPω hσζ hz hsol (min_le_right t (σ ω)) (hu ω _)
  rw [hm]
  rfl

end LocalExt

end InteractingSLE
