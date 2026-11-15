/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawEightFam
import InteractingSLE.Spec.ZhanGT4.A1G3LawRect

/-!
# Zhan's A.1 under R83, (G3), large-curve direction: the concrete families

Packet PROVE-A1-G3LAW (R83). The data of `G3RectLawFstC`'s family law (image curve the large curve on `Y`,
conditioning curve the small curve on `X`, frozen time `σ` of the small curve), mirroring A1-RECTLAW2's (Eight)
`A1RLawEightFam`:

* **`g3FstWord`**: the initial image word (the small curve's marks `x`, `y⁺`, tip, `y⁻` relative to the image of the
  large curve's start);
* **`g3FstVL`**: the image forces — the initial word at time `0` and FORCES's canonical forces `rForceFst` of the
  frozen-chart marks `largeG3Marks` afterwards;
* **`g3FstOwn`**, **`g3FstCap`**: the raw caps — FORCES's `capFst` at the large curve's rectangle exit `g3S₂`, gated
  by the protection `σ ≤ g3S₁` of the frozen small curve;
* **`g3FstD`**: the rectangle density at the stop, `M(σ ∧ S₁ᵏ, S₂ᵏ)` of the patched G3 records;
* measurability of the forces and raw caps, initial values, admissibility of the initial word (`largeG3_isSeedWord`);
* **`hasFamilyLawFstC_g3_of_inputs`**: `G3RectLawFstC`'s conclusion (verbatim, the original marginals) from four named
  inputs `hD`, `hgeo`, `hlaw`, `hstop` (A1-RECTLAW2's `hasFamilyLawFstC_of_masked`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open A2X A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom A1Forces A1MultiMark A1Marg A1Asm A1EightSeed A1RLaw
  A1G3Calc

/-! ### The concrete families -/

section Fam

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The (G3) large direction's initial image word** at the frozen time `σ` (`G3RectLawFstC`'s `ΘL`). -/
def g3FstWord (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ) (σ : ℝ≥0) (x : X) :
    Fin 4 → ℝ :=
  ![VR₁ 1 σ x - VR₁ 2 σ x, VR₁ 0 σ x - VR₁ 2 σ x, W₁ σ x - VR₁ 2 σ x, VL₁ 0 σ x - VR₁ 2 σ x]

/-- **The (G3) large direction's image forces**: the initial word at time `0`, and FORCES's canonical forces of the
frozen-chart marks `largeG3Marks` at positive times. -/
def g3FstVL (ys : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
    (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (i : Fin 4)
    (t : ℝ≥0) (z : X × Y) : ℝ :=
  if t = 0 then g3FstWord W₁ VL₁ VR₁ σ z.1 i else
    rForceFst (fun t x => (t : ℝ≥0∞) < ζ₁ x) 0 W₂ (fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) ys W₁
      (fun _ => σ) (fun x => largeG3Marks (ys - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) σ i)
      t z

/-- **The image curve's own time of the raw cap `k`**: the large curve's rectangle exit when the frozen small curve is
protected (`σ ≤ g3S₁ᵏ`), `0` otherwise (patched records). -/
def g3FstOwn (x y : ℝ) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0)
    (k : ℕ) (z : X × Y) : ℝ :=
  if σ ≤ g3S₁ x y W₁' ζ₁' k z.1 then (g3S₂ x y W₂' ζ₂' k z.2 : ℝ) else 0

/-- **The raw caps** of the (G3) large direction: the image capacity (`capFst`) at the own time `g3FstOwn`. -/
def g3FstCap (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0)
    (k : ℕ) : X × Y → ℝ≥0 :=
  capFst (fun t x => (t : ℝ≥0∞) < ζ₁ x) 0 W₂ (fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) y W₁ (fun _ => σ)
    (g3FstOwn x y W₁' ζ₁' W₂' ζ₂' σ k)

/-- **The rectangle densities at the stop**: `M(σ ∧ S₁ᵏ, S₂ᵏ)` of the patched G3 records. -/
def g3FstD (κ x y : ℝ) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 3 → ℝ≥0 → X → ℝ)
    (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0) (k : ℕ) (z : X × Y) : ℝ≥0∞ :=
  ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁' VL₁' VR₁' W₂' (g3S₁ x y W₁' ζ₁') k) z
    (min σ (g3S₁ x y W₁' ζ₁' k z.1) : ℝ≥0) (g3S₂ x y W₂' ζ₂' k z.2))

omit mX mY in
/-- The forces start at the initial word. -/
theorem g3FstVL_zero (ys : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
    (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (i : Fin 4)
    (z : X × Y) : g3FstVL ys W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i 0 z = g3FstWord W₁ VL₁ VR₁ σ z.1 i := by
  simp only [g3FstVL, ↓reduceIte]

omit mX mY in
/-- **The initial word is admissible on the live event** (SEEDGEOM's `largeG3_isSeedWord`). -/
theorem isSeedWord_g3FstWord {κ x y : ℝ} (hx : x < 0) {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (hP : ∀ x', IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · x')
      (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') (B₁ · x') (ζ₁ x')) (σ : ℝ≥0) (x' : X)
    (hσ : (σ : ℝ≥0∞) < ζ₁ x') :
    IsSeedWord (g3FstWord W₁ VL₁ VR₁ σ x') (![] : Fin 0 → ℝ) (largeG3ImgRhoL κ) ![] :=
  largeG3_isSeedWord hx (hP x') hσ

end Fam

/-! ### Measurability of the forces and the raw caps -/

section Meas

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

variable {κ x y : ℝ} {P₁ : Measure X} {𝓕₁ : Filtration ℝ≥0 mX} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {P₂ : Measure Y} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
  {ζ₂ : Y → ℝ≥0∞}

/-- The standing pathwise and measurability facts of the two regular G3 marginals used by FORCES's lemmas. -/
theorem g3Fst_facts
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    MeasurableSet {q : ℝ≥0 × X | (q.1 : ℝ≥0∞) < ζ₁ q.2} ∧
    (∀ y', ContinuousOn (W₂ · y') {t | (t : ℝ≥0∞) < lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')}) ∧
    (∀ y', W₂ 0 y' = 0) ∧
    (∀ x', ContinuousOn (W₁ · x') {t | (t : ℝ≥0∞) < ζ₁ x'}) ∧ (∀ x', W₁ 0 x' = 0) ∧
    (∀ t, Measurable (W₂ t)) ∧ (∀ t, Measurable (W₁ t)) ∧
    Measurable (fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) ∧ Measurable ζ₁ := by
  have hcW : ∀ y', ContinuousOn (W₂ · y') {s | (s : ℝ≥0∞) < ζ₂ y'} := fun y' => (h₂.path y').2.2.2.1
  have hcV : ∀ y', ContinuousOn (VL₂ 0 · y') {s | (s : ℝ≥0∞) < ζ₂ y'} := fun y' => (h₂.path y').2.2.2.2.1 0
  have hS := measurableSet_live_of_isStronglyProgressive
    (isStronglyProgressive_indicator_isStripLife h₂.evol.2.1 h₂.progW (h₂.progVL 0) hcW hcV)
  have hζ₁ := measurable_lifetime h₁.evol.2.1
  exact ⟨measurableSet_lt measurable_fst.coe_nnreal_ennreal (hζ₁.comp measurable_snd),
    fun y' => (hcW y').mono fun t ht => lt_of_lt_of_le ht (lifeEnd_le _ _ _), fun y' => (h₂.path y').1,
    fun x' => (h₁.path x').2.2.2.1, fun x' => (h₁.path x').1, measurable_of_isStronglyProgressive h₂.progW,
    measurable_of_isStronglyProgressive h₁.progW, measurable_lifeEnd hS, hζ₁⟩

/-- **The forces are jointly measurable in the frozen time and the sample** (`hVL` of the masked assembly). -/
theorem measurable_g3FstVL
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (i : Fin 4) (t : ℝ≥0) :
    Measurable fun p : ℝ≥0 × (X × Y) => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ p.1 i t p.2 := by
  have hW := measurable_uncurry_of_isStronglyProgressive h₁.progW
  have hL := fun i => measurable_uncurry_of_isStronglyProgressive (h₁.progVL i)
  have hR := fun j => measurable_uncurry_of_isStronglyProgressive (h₁.progVR j)
  have hπ : Measurable fun p : ℝ≥0 × (X × Y) => (p.1, p.2.1) := measurable_fst.prodMk measurable_snd.fst
  by_cases ht : t = 0
  · simp only [g3FstVL, ht, ↓reduceIte, g3FstWord]
    fin_cases i
    · exact ((hR 1).comp hπ).sub ((hR 2).comp hπ)
    · exact ((hR 0).comp hπ).sub ((hR 2).comp hπ)
    · exact (hW.comp hπ).sub ((hR 2).comp hπ)
    · exact ((hL 0).comp hπ).sub ((hR 2).comp hπ)
  · have e : (fun p : ℝ≥0 × (X × Y) => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ p.1 i t p.2) = fun p =>
        rForceFst (fun t x => (t : ℝ≥0∞) < ζ₁ x) 0 W₂ (fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) y W₁
          (fun _ => p.1) (fun x' => largeG3Marks (y - 0) (W₁ · x') (fun i t => VL₁ i t x')
            (fun j t => VR₁ j t x') p.1 i) t p.2 :=
      funext fun p => by unfold g3FstVL; exact ite_eq_right_of_eq_false _ _ (eq_false ht)
    rw [e]
    obtain ⟨hlive, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Fst_facts h₁ h₂
    exact measurable_rForceFst (live := fun t x => (t : ℝ≥0∞) < ζ₁ x) (Wj := W₂)
      (ζj := fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) (Wk := W₁) (ζk := ζ₁)
      (p := fun σ x' => largeG3Marks (y - 0) (W₁ · x') (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') σ i)
      hlive (fun _ _ h => h) hjc hj0 hkc hk0 hjm hkm hζj hζk 0 y
      (measurable_largeG3Marks hW hL hR (y - 0) i) t

/-- **The raw caps are jointly measurable in the frozen time and the sample** (`hS₀` of the masked assembly). -/
theorem measurable_g3FstCap {W₁' : ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞} {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hS₁ : ∀ k, Measurable (g3S₁ x y W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (g3S₂ x y W₂' ζ₂' k)) (k : ℕ) :
    Measurable fun p : ℝ≥0 × (X × Y) => g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' p.1 k p.2 := by
  obtain ⟨hlive, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Fst_facts h₁ h₂
  have hT : Measurable fun q : ℝ≥0 × (X × Y) => g3FstOwn x y W₁' ζ₁' W₂' ζ₂' q.1 k q.2 :=
    Measurable.ite (measurableSet_le measurable_fst ((hS₁ k).comp measurable_snd.fst))
      ((hS₂ k).comp measurable_snd.snd).coe_nnreal_real measurable_const
  unfold g3FstCap
  exact measurable_capFst (live := fun t x => (t : ℝ≥0∞) < ζ₁ x) (Wj := W₂)
    (ζj := fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) (Wk := W₁) (ζk := ζ₁) (xj := 0) (xk := y)
    (T := fun σ => g3FstOwn x y W₁' ζ₁' W₂' ζ₂' σ k) hlive (fun _ _ h => h) hjc hj0 hkc hk0 hjm hkm hζj hζk hT

end Meas

end InteractingSLE.ZhanGT4.A1G3Law
