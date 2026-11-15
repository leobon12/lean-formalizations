/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawSndRect
import InteractingSLE.Spec.ZhanGT4.A1G3LawSnd
import InteractingSLE.Spec.ZhanGT4.A1FamilySample

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the per-sample laws at unprotected frozen times

Packet PROVE-A1-G3LAW (R83). For the small direction's `hlaw` (`hasFamilyLawC_g3_of_inputs`):

* **`g3SndD_eq_of_lt`**: at a frozen time `σ` past the large exit `S₂ᵏ(y)` the family density is the exit density;
* **`g3SndCap_eq_zero_of_lt`**: there the raw cap `k` vanishes at every small sample (own time `0`);
* **`g3Snd_isSeedSampleLaw_of_lt`**: the one-sample law at such `σ`, for any image data whose noise starts at `0`:
  the cap vanishes (FAMILY's `isSeedSampleLaw_of_cap_zero`), and the tilted measure is the seeded measure of the
  column at the positive height `S₂ᵏ(y)`, under which the column's Girsanov process is a Brownian motion.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw Girsanov

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

omit mX mY in
/-- Past the large exit the family density is the exit density. -/
theorem g3SndD_eq_of_lt (κ x y : ℝ) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 3 → ℝ≥0 → X → ℝ)
    (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) {σ : ℝ≥0} {k : ℕ} {y' : Y}
    (hσ : g3S₂ x y W₂' ζ₂' k y' < σ) (x' : X) :
    g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' σ k (x', y') =
      ENNReal.ofReal (g3M κ x y W₁' VL₁' VR₁' ζ₁' W₂' k (x', y') (g3S₁ x y W₁' ζ₁' k x') (g3S₂ x y W₂' ζ₂' k y')) := by
  simp only [g3SndD, min_eq_right hσ.le]

omit mX mY in
/-- Past the large exit the raw cap vanishes at every small sample. -/
theorem g3SndCap_eq_zero_of_lt (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ)
    (ζ₂' : Y → ℝ≥0∞) {σ : ℝ≥0} {k : ℕ} {y' : Y} (hσ : g3S₂ x y W₂' ζ₂' k y' < σ) (x' : X) :
    g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k (x', y') = 0 := by
  unfold g3SndCap
  refine capSnd_of_nonpos ?_
  have hn : ¬ σ ≤ g3S₂ x y W₂' ζ₂' k y' := not_le.2 hσ
  simp only [g3SndOwn, hn, ↓reduceIte, le_refl]

/-- **The one-sample law of the small direction at an unprotected frozen time** (`σ > S₂ᵏ(y)`): for the patched G3
marginals, any image data with noise `0` at time `0` satisfy `IsSeedSampleLaw` under the family density, with the raw
caps of the original data (the cap `k` is `0`). -/
theorem g3Snd_isSeedSampleLaw_of_lt {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    {P₁ : Measure X} [IsProbabilityMeasure P₁] {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hB₂ : ∀ ω, Continuous (B₂ · ω))
    {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
    (k : ℕ) (y' : Y) {σ : ℝ≥0} (hσ : g3S₂ x y W₂ ζ₂ k y' < σ)
    {W : ℝ≥0 → X → ℝ} {ζ : X → ℝ≥0∞} {VL : Fin 1 → ℝ≥0 → X → ℝ} {VR : Fin 3 → ℝ≥0 → X → ℝ} {N : ℝ≥0 → X → ℝ}
    (hN0 : ∀ x', N 0 x' = 0) :
    IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y')) W ζ VL VR N
      (fun k' x' => g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k' (x', y')) k := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, -, -, -, -, -, -, -, hS₂pos, -⟩ := g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨hpp, -, hcol⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y' (hS₂pos k y') le_rfl
  obtain ⟨Bq, hBq, hBqc⟩ := exists_brownian_seedMeasure_of_column hpp hk hcol
  have hQ : (P₁.withDensity fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y')) =
      seedMeasure P₁ (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k (g3S₂ x y W₂ ζ₂ k y') y') (g3S₁ x y W₁ ζ₁ k) := by
    rw [seedMeasure_g3Col]
    congr 1
    funext x'
    exact g3SndD_eq_of_lt κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ hσ x'
  rw [hQ]
  exact isSeedSampleLaw_of_cap_zero hBq hBqc hN0
    (fun x' => g3SndCap_eq_zero_of_lt x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ hσ x')

/-- **The small direction's `hlaw` from the protected frozen times alone**: for the patched G3 marginals (`W₁ … ζ₂`,
the data of the densities and of the cap gates) and the original data (`W₁o … ζ₂o`, the canonical image data and the
raw caps), the one-sample laws of `hasFamilyLawC_g3_of_inputs` at every frozen time follow from those at the frozen
times protected by the large exit (`σ ≤ S₂ᵏ(y)`); past it the cap vanishes (`g3Snd_isSeedSampleLaw_of_lt`). -/
theorem g3Snd_hlaw_of_protected {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    {P₁ : Measure X} [IsProbabilityMeasure P₁] {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hB₂ : ∀ ω, Continuous (B₂ · ω))
    {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
    {G₂ : Set Y}
    (hprot : ∀ k, ∀ᵐ y' ∂P₂, y' ∈ G₂ → ∀ σ : ℝ≥0, σ ≤ g3S₂ x y W₂ ζ₂ k y' →
      IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y'))
        (fun t x' => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => σ) t (x', y'))
        (fun x' => rLife (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => σ) (x', y'))
        (fun i t x' => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o σ i t (x', y')) (fun j t x' => g3SndVR y W₁o ζ₁o W₂o VL₂o ζ₂o σ
            j t (x', y'))
        (fun t x' => seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
          (fun s => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => σ) s (x', y'))
          (fun i s => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o σ i s (x', y')) (fun j s => g3SndVR y W₁o ζ₁o W₂o VL₂o ζ₂o σ j s
              (x', y')) t)
        (fun k' x' => g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k' (x', y')) k) :
    ∀ k, ∀ᵐ y' ∂P₂, y' ∈ G₂ → ∀ σ : ℝ≥0,
      IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ k (x', y'))
        (fun t x' => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => σ) t (x', y'))
        (fun x' => rLife (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => σ) (x', y'))
        (fun i t x' => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o σ i t (x', y')) (fun j t x' => g3SndVR y W₁o ζ₁o W₂o VL₂o ζ₂o σ
            j t (x', y'))
        (fun t x' => seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
          (fun s => rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => σ) s (x', y'))
          (fun i s => g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o σ i s (x', y')) (fun j s => g3SndVR y W₁o ζ₁o W₂o VL₂o ζ₂o σ j s
              (x', y')) t)
        (fun k' x' => g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ σ k' (x', y')) k := by
  intro k
  filter_upwards [hprot k] with y' hy' hG σ
  rcases le_or_gt σ (g3S₂ x y W₂ ζ₂ k y') with hσ | hσ
  · exact hy' hG σ hσ
  · refine g3Snd_isSeedSampleLaw_of_lt hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y' hσ fun x' => ?_
    rw [A1RLaw.seedCapacityNoise_zero]
    have h0 := A1RLaw.cImgDrvM_zero (fun t (z : X × Y) => g3SndLive W₂o VL₂o ζ₂o t z.2) y (fun t (z : X × Y) => W₁o t
        z.1)
      (fun z : X × Y => ζ₁o z.1) 0 (fun t (z : X × Y) => W₂o t z.2) (fun _ => σ) (x', y')
    simp only [rDrv, h0, zero_div]

end InteractingSLE.ZhanGT4.A1G3Law
