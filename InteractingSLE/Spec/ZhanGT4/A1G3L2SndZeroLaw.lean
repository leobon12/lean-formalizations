/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndZeroId

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the frozen time `σ = 0`, the one-sample law

Packet PROVE-A1-G3LAW2. For the patched G3 marginals at the frozen time `0`:

* `g3SndD_zero`: the family density is `1` (the seeded logarithm of the record at height `0` is constant on the
  rectangle, A1-G3CALC's `normEll_g3Rec_zero`);
* `g3Snd0_noise`: the compensated residual of the canonical data is the small marginal's Brownian motion up to the
  exit (the driving equation `w_eq` of the small path);
* **`g3Snd_isSeedSampleLaw_zero`**: the one-sample law at `σ = 0` in the small marginal's own filtration, with its own
  Brownian motion.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

section ZeroLaw

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- **At the frozen time `0` the family density is `1`.** -/
theorem g3SndD_zero (k : ℕ) (y₀ : Y) (x₀ : X) :
    g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x₀, y₀) = 1 := by
  obtain ⟨hR1, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hc₂ : ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 0) := by
    rw [Icc_self]; exact continuousOn_singleton _ _
  have h0₂ : W₂ 0 y₀ = 0 := (h₂.path y₀).1
  have hWf := continuous_frzPath (W₂ := W₂) (p := -y) hc₂ le_rfl
  have hex : ∃ a W', OwnData (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀) (fwdHull (frzPath W₂ (-y) 0 y₀) 0)
      (frzChart (frzPath W₂ (-y) 0 y₀) 0) (g3S₁ x y W₁ ζ₁ k x₀) a W' := by
    refine exists_ownData (continuous_eightDrv (h₁.path x₀).2.2.2.1 (hR1 k x₀).1) (eightDrv_zero (h₁.path x₀).1)
      (hR1 k x₀).2 (isHPHull_fwdHull hWf le_rfl) (isMapOut_fwdMap_gen hWf le_rfl) ?_
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty hWf, closure_empty]
    exact empty_disjoint _
  have hn := normEll_g3Rec_zero (κ := κ) (VL₁ := VL₁) (VR₁ := VR₁) hc₂ h0₂ hex (NNReal.coe_nonneg _) le_rfl
  simp only [g3SndD, seedHeightField, min_eq_left (zero_le (a := g3S₂ x y W₂ ζ₂ k y₀)), NNReal.coe_zero, hn,
    sub_self, Real.exp_zero, ENNReal.ofReal_one]

/-- **At the frozen time `0` the compensated residual of the canonical data is the small Brownian motion** up to the
exit. -/
theorem g3Snd0_noise (k : ℕ) (y₀ : Y) (x₀ : X) {t : ℝ≥0} (ht : t ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
      (fun s => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) s (x₀, y₀))
      (fun i s => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x₀, y₀)) (fun j s => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s (x₀, y₀)) t =
      B₁ t x₀ := by
  obtain ⟨hR1, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have htζ : (t : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) (hR1 k x₀).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, -⟩ := h₁.path x₀
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  have hs : ∀ s ∈ uIcc (0 : ℝ) t, s.toNNReal ≤ g3S₁ x y W₁ ζ₁ k x₀ := fun s hs =>
    (Real.toNNReal_le_iff_le_coe.2 (by rw [uIcc_of_le t.coe_nonneg] at hs; exact hs.2)).trans ht
  have eL : ∀ i, (∫ s in (0 : ℝ)..t, smallG3RhoL κ i / (rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0)
      s.toNNReal (x₀, y₀) - g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s.toNNReal (x₀, y₀))) =
      ∫ s in (0 : ℝ)..t, smallG3RhoL κ i / (W₁ s.toNNReal x₀ - VL₁ i s.toNNReal x₀) := fun i =>
    intervalIntegral.integral_congr fun s hs' => by
      simp only [g3Snd0_rDrv hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ (hs s hs'),
        g3Snd0_VL hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ i (hs s hs')]
  have eR : ∀ j, (∫ s in (0 : ℝ)..t, smallG3RhoR κ j / (rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0)
      s.toNNReal (x₀, y₀) - g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s.toNNReal (x₀, y₀))) =
      ∫ s in (0 : ℝ)..t, smallG3RhoR κ j / (W₁ s.toNNReal x₀ - VR₁ j s.toNNReal x₀) := fun j =>
    intervalIntegral.integral_congr fun s hs' => by
      simp only [g3Snd0_rDrv hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ (hs s hs'),
        g3Snd0_VR hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ j (hs s hs')]
  have hw := hweq t htζ
  simp only at hw
  unfold seedCapacityNoise
  beta_reduce
  rw [g3Snd0_rDrv hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ ht]
  simp only [eL, eR]
  rw [hw]
  have hsq : Real.sqrt (kh κ) ≠ 0 := (Real.sqrt_pos.2 hk).ne'
  field_simp
  ring

/-- **The one-sample law of the small direction at the frozen time `0`** (patched data, raw caps): in the small
marginal's own filtration with its own Brownian motion (the density is `1`, the canonical data are the small curve's,
the residual is the Brownian motion). -/
theorem g3Snd_isSeedSampleLaw_zero [𝓖₁.IsRightContinuous] (k : ℕ) (y₀ : Y) :
    IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x', y₀))
      (fun t x' => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) t (x', y₀))
      (fun x' => rLife (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) (x', y₀))
      (fun i t x' => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x', y₀))
      (fun j t x' => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j t (x', y₀))
      (fun t x' => seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
        (fun s => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) s (x', y₀))
        (fun i s => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x', y₀))
        (fun j s => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s (x', y₀)) t)
      (fun k' x' => g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k' (x', y₀)) k := by
  have hD : (fun x' => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x', y₀)) = fun _ => 1 :=
    funext fun x' => g3SndD_zero hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x'
  rw [hD, show (fun _ : X => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]
  have hcap : ∀ k' x', g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k' (x', y₀) = g3S₁ x y W₁ ζ₁ k' x' :=
    fun k' x' => g3Snd0_cap hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ x'
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  have hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun x' => (g3S₁ x y W₁ ζ₁ m x' : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (cofGN (-y) (x - y) ![x - y]) m
  set C : ℝ≥0 → Set X := fun s => {x' | s < g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x', y₀)} with hCdef
  have hCe : ∀ s, C s = {x' | (g3S₁ x y W₁ ζ₁ k x' : WithTop ℝ≥0) ≤ s}ᶜ := fun s => by
    ext x'
    simp only [hCdef, mem_ofPred_eq, mem_compl_iff, hcap, WithTop.coe_le_coe, not_le]
  have hC : ∀ s : ℝ≥0, MeasurableSet[𝓖₁ s] (C s) := fun s => by
    rw [hCe s]; exact ((hs₁ k).measurableSet_le s).compl
  have hCS : ∀ s x', x' ∈ C s → s < g3S₁ x y W₁ ζ₁ k x' := fun s x' hx' => by
    have h := hx'; simp only [hCdef, mem_ofPred_eq, hcap] at h; exact h
  have key : ∀ s (g g' : Set X), MeasurableSet[𝓖₁ s] g' → (∀ x' ∈ C s, (x' ∈ g ↔ x' ∈ g')) →
      MeasurableSet[𝓖₁ s] (g ∩ C s) := fun s g g' hg' hgg => by
    have e : g ∩ C s = g' ∩ C s := by
      ext x'
      exact ⟨fun h => ⟨(hgg x' h.2).1 h.1, h.2⟩, fun h => ⟨(hgg x' h.2).2 h.1, h.2⟩⟩
    rw [e]; exact hg'.inter (hC s)
  have hB := h₁.evol.1
  refine ⟨𝓖₁, B₁, hB, hB₁, hC, fun s => ?_, Eventually.of_forall fun x' t ht => ?_⟩
  · refine forall_imageGen (p := fun g => MeasurableSet[𝓖₁ s] (g ∩ C s))
      (fun r hr U hU => key s _ (W₁ r ⁻¹' U) (𝓖₁.mono hr _ ((h₁.progW.stronglyAdapted r).measurable hU))
        fun x' hx' => ?_)
      (fun r hr U hU i => key s _ (VL₁ i r ⁻¹' U) (𝓖₁.mono hr _ (((h₁.progVL i).stronglyAdapted r).measurable hU))
        fun x' hx' => ?_)
      (fun r hr U hU j => key s _ (VR₁ j r ⁻¹' U) (𝓖₁.mono hr _ (((h₁.progVR j).stronglyAdapted r).measurable hU))
        fun x' hx' => ?_)
      (fun r hr U hU => key s _ (B₁ r ⁻¹' U) (𝓖₁.mono hr _ ((hB.2.1 r) hU)) fun x' hx' => ?_)
      (fun r hr k' => key s _ {x' | (g3S₁ x y W₁ ζ₁ k' x' : WithTop ℝ≥0) ≤ r}
        (𝓖₁.mono hr _ ((hs₁ k').measurableSet_le r)) fun x' _ => ?_)
      (fun r hr => key s _ univ MeasurableSet.univ fun x' hx' => ?_)
    · have hrS : r ≤ g3S₁ x y W₁ ζ₁ k x' := hr.trans (hCS s x' hx').le
      simp only [mem_preimage, g3Snd0_rDrv hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' hrS]
    · have hrS : r ≤ g3S₁ x y W₁ ζ₁ k x' := hr.trans (hCS s x' hx').le
      simp only [mem_preimage, g3Snd0_VL hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' i hrS]
    · have hrS : r ≤ g3S₁ x y W₁ ζ₁ k x' := hr.trans (hCS s x' hx').le
      simp only [mem_preimage, g3Snd0_VR hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' j hrS]
    · have hrS : r ≤ g3S₁ x y W₁ ζ₁ k x' := hr.trans (hCS s x' hx').le
      simp only [mem_preimage, g3Snd0_noise hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' hrS]
    · simp only [mem_ofPred_eq, hcap, WithTop.coe_le_coe]
    · simp only [mem_univ, iff_true, mem_ofPred_eq]
      have h1 := capSnd_le_rLife (live := g3SndLive W₂ VL₂ ζ₂) (xj := y) (Wj := W₁) (ζj := ζ₁) (xk := 0) (Wk := W₂)
        (τ := fun _ => 0) (g3SndOwn x y W₁ ζ₁ W₂ ζ₂ 0 k) (x', y₀)
      have h2 : (r : ℝ≥0∞) < g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x', y₀) := by
        have := hx'
        simp only [hCdef, mem_ofPred_eq] at this
        exact ENNReal.coe_lt_coe.2 (hr.trans_lt this)
      exact h2.trans_le h1
  · have ht' : t ≤ g3S₁ x y W₁ ζ₁ k x' := by rw [← hcap k x']; exact ht
    exact (g3Snd0_noise hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' ht').symm

end ZeroLaw

end InteractingSLE.ZhanGT4.A1G3L2
