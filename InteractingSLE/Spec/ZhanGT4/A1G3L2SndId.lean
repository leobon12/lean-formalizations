/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2Force
import InteractingSLE.Spec.ZhanGT4.A1G3L2Clock
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndFam
import InteractingSLE.Spec.ZhanGT4.A1G3LawSnd

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the canonical data are the seeded capacity coordinates

Packet PROVE-A1-G3LAW2 (the identification step). For the patched G3 marginals, at a frozen sample `y₀`, a protected
frozen time `σ ∈ (0, S₂ᵏ(y₀)]` and every small sample `x₀`, the seeded record `g3Col … k σ y₀ x₀` (A1-G3CALC's
`g3Rec`, driver stopped at the small exit `S₁ᵏ(x₀)`) is an image chain of the small curve in the physical frame, and:

* `fwdHull_frzPath_eq`, `frzChart_frzPath_eq`: the frozen hull and chart of the records are A2X's physical hull and
  map of the large curve (in the small curve's frame);
* **`g3Col_facts`**: `OwnData` in the physical frame, agreement of the record's driver with the small driver on
  `[0, S₁ᵏ]`, and **`S₁ᵏ(x₀)` is a good horizon** (PROVE-A1-GOODTIME's `isGoodTime_of_disjoint_loc`);
* **`g3Snd_rDrv_eq`**: up to the capacity horizon the masked canonical image driver is the seeded capacity driver;
* **`g3Snd_cap_eq`**, `g3Snd_cap_eq_clk`, **`g3Snd_cap_le_cap`**: the raw caps are the capacity horizon, the clock of
  the record at the own times of the other rectangles, and are monotone in those own times.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens

/-! ### The frozen hull and chart of the records in the physical frame -/

section Frame

variable {Y : Type*}

/-- The frozen hull of the records is the physical hull of the large curve (frame of the small curve). -/
theorem fwdHull_frzPath_eq (W₂ : ℝ≥0 → Y → ℝ) (p : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (y' : Y)
    (hk : ∃ τ', σ < τ' ∧ ContinuousOn (Strip.extPath (W₂ · y')) (Icc 0 τ')) :
    fwdHull (frzPath W₂ p σ y') σ = physHull p (Strip.extPath (W₂ · y')) σ := by
  obtain ⟨τ', hστ', hc⟩ := hk
  have h1 : fwdHull (frzPath W₂ p σ y') σ = physHull p (stopDrv (Strip.extPath (W₂ · y')) σ) σ :=
    (physHull_eq_fwdHull p _ σ).symm
  rw [h1]
  exact A1SeedGeom.physHull_congr_of_continuousOn
    (continuous_stopDrv (hc.mono (Icc_subset_Icc_right hστ'.le)) hσ).continuousOn hc hσ hστ' (stopDrv_eqOn _ σ)

/-- The frozen chart of the records is the physical map of the large curve (frame of the small curve). -/
theorem frzChart_frzPath_eq (W₂ : ℝ≥0 → Y → ℝ) (p : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (y' : Y) :
    frzChart (frzPath W₂ p σ y') σ = physMap p (Strip.extPath (W₂ · y')) σ := by
  funext z
  have e1 : frzPath W₂ p σ y' = fun u => stopDrv (Strip.extPath (W₂ · y')) σ u + p := rfl
  have e2 : stopDrv (Strip.extPath (W₂ · y')) σ σ = Strip.extPath (W₂ · y') σ := stopDrv_eqOn _ σ ⟨hσ, le_rfl⟩
  show fwdMap (frzPath W₂ p σ y') σ z + ((frzPath W₂ p σ y' σ : ℝ) : ℂ) = _
  rw [e1, ConformalImageFull.fwdMap_add_const,
    Ito.fwdMap_congr_of_eqOn (stopDrv_eqOn (Strip.extPath (W₂ · y')) σ), physMap]
  simp only [e2]
  push_cast
  ring

end Frame

/-! ### The per-sample facts of the column -/

section Col

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The per-sample facts of the column** at a protected frozen time `σ ∈ (0, S₂ᵏ(y₀)]`: the record is an image chain
of the small curve in the physical frame (`OwnData` against `physHull (0 − y) …`, `physMap (0 − y) …`), its driver is
the small driver on `[0, S₁ᵏ]`, `S₁ᵏ(x₀)` is a good horizon, and the large driver is continuous a little beyond `σ`. -/
theorem g3Col_facts (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀) (x₀ : X) :
    OwnData (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W (physHull (0 - y) (Strip.extPath (W₂ · y₀)) σ)
        (physMap (0 - y) (Strip.extPath (W₂ · y₀)) σ) (g3S₁ x y W₁ ζ₁ k x₀)
        (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' ∧
      EqOn (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W (Strip.extPath (W₁ · x₀)) (Icc 0 (g3S₁ x y W₁ ζ₁ k x₀)) ∧
      A1Ref.IsGoodTime y (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ (g3S₁ x y W₁ ζ₁ k x₀) ∧
      ∃ τ', (σ : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 τ') := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, hgood₁, -, -, -, -, -, -, -, hS₂ζ⟩ := g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  obtain ⟨-, hrec, -⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ))
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  have hσζ : (σ : ℝ≥0∞) < ζ₂ y₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσS) (hS₂ζ k y₀)
  have hk := A1Ref.exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 hσζ
  have r := hrec x₀
  have hown0 := r.own
  have hφ : (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).φ = frzChart (frzPath W₂ (-y) σ y₀) σ :=
    congrArg SeedData.φ r.source
  rw [hφ, fwdHull_frzPath_eq W₂ (-y) σ.coe_nonneg y₀ hk, frzChart_frzPath_eq W₂ (-y) σ.coe_nonneg y₀] at hown0
  have hown : OwnData (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W (physHull (0 - y) (Strip.extPath (W₂ · y₀)) σ)
      (physMap (0 - y) (Strip.extPath (W₂ · y₀)) σ) (g3S₁ x y W₁ ζ₁ k x₀)
      (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' := by
    rw [zero_sub]
    exact hown0
  have hWj : EqOn (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W (Strip.extPath (W₁ · x₀))
      (Icc 0 (g3S₁ x y W₁ ζ₁ k x₀)) := eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀
  obtain ⟨hlt₁, hSpos, -, -⟩ := hgood₁ k x₀
  obtain ⟨T', hST', hcT'⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₁.path x₀).2.2.2.1 hlt₁
  refine ⟨hown, hWj, A1Marg.isGoodTime_sub.2 ?_, hk⟩
  refine A1Good.isGoodTime_of_disjoint_loc hST' hcT' hSpos (by rw [ENNReal.ofReal_coe_nnreal]; exact hlt₁) ?_
  have hEq : physHull 0 (Strip.extPath (W₁ · x₀)) (g3S₁ x y W₁ ζ₁ k x₀) =
      physHull 0 (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W (g3S₁ x y W₁ ζ₁ k x₀) :=
    A1SeedGeom.physHull_congr_of_continuousOn hcT' hown.cont.continuousOn (NNReal.coe_nonneg _) hST' hWj.symm
  show Disjoint (closure (physHull 0 (Strip.extPath (W₁ · x₀)) (g3S₁ x y W₁ ζ₁ k x₀)))
    (closure (physHull (0 - y) (Strip.extPath (W₂ · y₀)) σ))
  rw [hEq, A1Ref.physHull_zero]
  exact hown.disj.symm

/-- The own time of the raw cap `k'` as a function of the small sample (`g3SndOwn` at the frozen sample `y₀`). -/
def g3SndTk (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (y₀ : Y)
    (k' : ℕ) (x₀ : X) : ℝ≥0 :=
  if σ ≤ g3S₂ x y W₂ ζ₂ k' y₀ then g3S₁ x y W₁ ζ₁ k' x₀ else 0

omit mX mY [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] in
omit hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ in
theorem coe_g3SndTk (σ : ℝ≥0) (y₀ : Y) (k' : ℕ) (x₀ : X) :
    (g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ : ℝ) = g3SndOwn x y W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) := by
  unfold g3SndTk g3SndOwn
  split_ifs <;> simp

/-- **The masked canonical image driver is the seeded capacity driver** up to the capacity horizon (live frozen
sample, protected frozen time). -/
theorem g3Snd_rDrv_eq [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀) (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀) :
    rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) t (x₀, y₀) =
      seedCapacityDriver (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) t x₀ := by
  obtain ⟨hown, hWj, hgood, hk⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  obtain ⟨hpp, hrec, hcol⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ))
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  obtain ⟨hCc, hCs, c, hc, hClb⟩ := clock_facts_of_column hpp hcol
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ x₀ → ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT
  have ht' : (t : ℝ) ≤ (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (g3S₁ x y W₁ ζ₁ k x₀) := by
    rw [← coe_seedCapacityHorizon (fun ω => (hrec ω).own) x₀]
    exact_mod_cast ht
  rw [seedCapacityDriver_eq_sub (fun ω => (hrec ω).own) hCc hCs hc hClb x₀ ht,
    ← imgDrv_sub_eq_of_ownData hown hWj hj (A1Ref.extPath_zero_of (h₁.path x₀).1) hk
      (A1Ref.extPath_zero_of (h₂.path y₀).1) σ.coe_nonneg hgood t.coe_nonneg ht']
  simp only [rDrv, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive]

/-- **The raw cap `k'` at a good own time is the clock there** (any rectangle `k'` with an open gate). -/
theorem g3Snd_cap_eq_imgClk (k' : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k' y₀)
    (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) :
    g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) =
      (A1Ref.imgClk y (Strip.extPath (W₁ · x₀)) 0 (Strip.extPath (W₂ · y₀)) σ (g3S₁ x y W₁ ζ₁ k' x₀)).toNNReal := by
  obtain ⟨-, -, hgood, hk⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ hσ hσS x₀
  have hT : g3SndOwn x y W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) = (g3S₁ x y W₁ ζ₁ k' x₀ : ℝ) := by
    simp only [g3SndOwn, hσS, ↓reduceIte]
  unfold g3SndCap
  rw [capSnd_congr_pt (T' := fun _ => (g3S₁ x y W₁ ζ₁ k' x₀ : ℝ)) hT]
  exact capSnd_eq_of_isGoodTime (T := fun _ => (g3S₁ x y W₁ ζ₁ k' x₀ : ℝ)) hlive
    (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT) (h₁.path x₀).1 hk (h₂.path y₀).1 hgood

/-- **The raw cap `k` is the capacity horizon of the column** (live frozen sample, protected frozen time). -/
theorem g3Snd_cap_eq (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀)
    (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) :
    g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) =
      seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀ := by
  obtain ⟨hown, hWj, hgood, hk⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  rw [g3Snd_cap_eq_imgClk hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀,
    (imgClk_imgDrv_eqOn_of_ownData hown hWj (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT)
      (A1Ref.extPath_zero_of (h₁.path x₀).1) hk (A1Ref.extPath_zero_of (h₂.path y₀).1) σ.coe_nonneg hgood).1
      ⟨NNReal.coe_nonneg _, le_rfl⟩]
  rfl

/-- **The other raw caps below the horizon are the clock of the column** (A1-FAMILY's `hcap₁`). -/
theorem g3Snd_cap_eq_clk (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀)
    (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (k' : ℕ) (x₀ : X)
    (hle : g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) : ℝ) =
      (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀) := by
  obtain ⟨hown, hWj, hgood, hk⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  have hclk := (imgClk_imgDrv_eqOn_of_ownData hown hWj
    (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT) (A1Ref.extPath_zero_of (h₁.path x₀).1) hk
    (A1Ref.extPath_zero_of (h₂.path y₀).1) σ.coe_nonneg hgood).1
  by_cases hg : σ ≤ g3S₂ x y W₂ ζ₂ k' y₀
  · have hTk : g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ = g3S₁ x y W₁ ζ₁ k' x₀ := by
      simp only [g3SndTk, hg, ↓reduceIte]
    rw [hTk] at hle ⊢
    have hmem : ((g3S₁ x y W₁ ζ₁ k' x₀ : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (g3S₁ x y W₁ ζ₁ k x₀) :=
      ⟨NNReal.coe_nonneg _, by exact_mod_cast hle⟩
    rw [g3Snd_cap_eq_imgClk hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ hσ hg hlive x₀, hclk hmem]
    have h0 : 0 ≤ (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).a (g3S₁ x y W₁ ζ₁ k' x₀) := by
      rw [← hown.a0]
      exact hown.mono.monotoneOn ⟨le_rfl, hown.pos.le⟩ hmem hmem.1
    exact Real.coe_toNNReal _ h0
  · have hTk : g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ = 0 := by simp only [g3SndTk, hg, ↓reduceIte]
    rw [hTk, NNReal.coe_zero, hown.a0]
    unfold g3SndCap
    rw [capSnd_of_nonpos]
    · rfl
    · simp only [g3SndOwn, hg, ↓reduceIte, le_refl]

/-- **The raw caps are monotone in the own times** (A1-FAMILY's `hcap₂`). -/
theorem g3Snd_cap_le_cap (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀)
    (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (k' : ℕ) (x₀ : X)
    (hle : g3S₁ x y W₁ ζ₁ k x₀ ≤ g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀) :
    g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y₀) ≤
      g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k' (x₀, y₀) := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  obtain ⟨-, hgood₁, -⟩ := g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cofG hne)
  by_cases hg : σ ≤ g3S₂ x y W₂ ζ₂ k' y₀
  · have hTk : g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ = g3S₁ x y W₁ ζ₁ k' x₀ := by
      simp only [g3SndTk, hg, ↓reduceIte]
    rw [hTk] at hle
    obtain ⟨-, -, hgood', hk⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ hσ hg x₀
    rw [g3Snd_cap_eq_imgClk hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀,
      g3Snd_cap_eq_imgClk hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ hσ hg hlive x₀]
    obtain ⟨-, hmono, -⟩ := exists_isImgDrvOn (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT)
      (A1Ref.extPath_zero_of (h₁.path x₀).1) hk (A1Ref.extPath_zero_of (h₂.path y₀).1) σ.coe_nonneg hgood'
    exact Real.toNNReal_le_toNNReal (hmono.monotoneOn ⟨NNReal.coe_nonneg _, by exact_mod_cast hle⟩
      ⟨NNReal.coe_nonneg _, le_rfl⟩ (by exact_mod_cast hle))
  · have hTk : g3SndTk x y W₁ ζ₁ W₂ ζ₂ σ y₀ k' x₀ = 0 := by simp only [g3SndTk, hg, ↓reduceIte]
    rw [hTk] at hle
    have hpos : (0 : ℝ) < g3S₁ x y W₁ ζ₁ k x₀ := (hgood₁ k x₀).2.1
    exact absurd (le_antisymm hle (zero_le (a := g3S₁ x y W₁ ζ₁ k x₀)))
      (fun h => by rw [h] at hpos; exact lt_irrefl 0 hpos)

end Col

end InteractingSLE.ZhanGT4.A1G3L2
