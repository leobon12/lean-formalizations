/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawMasked
import InteractingSLE.Spec.ZhanGT4.A1ForcesSnd

/-!
# Zhan's A.1 under R83, (Eight), large-curve direction: the concrete families

Packet PROVE-A1-RECTLAW2 (R83). The data of `EightRectLawFstC`'s family law (image curve the large curve on `Y`,
conditioning curve the small curve on `X`, frozen time `σ` of the small curve):

* `measurable_uncurry_of_isStronglyProgressive`: a strongly progressive process is jointly measurable in `(t, ω)`;
* **`eightFstWord`**: the initial image word (the small curve's seeds and tip relative to the large curve's start);
* **`eightFstVL`**: the image forces — the initial word at time `0` (FROZEN's `path` field asks `vL_zero` even where
  the image lifetime vanishes) and FORCES's measurable canonical forces `rForceFst` of the frozen-chart marks
  `largeEightMarks` afterwards;
* **`eightFstOwn`**, **`eightFstCap`**: the raw caps — FORCES's `capFst` (image capacity) at the large curve's rectangle
  exit `eightS₂`, gated by the protection `σ ≤ eightS₁` of the frozen small curve (own time `0` otherwise);
* **`eightFstD`**: the rectangle density at the stop, `M(σ ∧ S₁ᵏ, S₂ᵏ)` of the patched records;
* measurability of the forces and of the raw caps, the initial values and the admissibility of the initial word on
  the live event (SEEDGEOM's `largeEight_isSeedWord`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open A2X A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom A1Forces A1MultiMark A1Marg A1Asm A1EightSeed

/-! ### Joint measurability of progressive processes -/

section Joint

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **A strongly progressive real process is jointly measurable in `(t, ω)`.** -/
theorem measurable_uncurry_of_isStronglyProgressive {u : ℝ≥0 → Ω → ℝ} (h : IsStronglyProgressive 𝓕 u) :
    Measurable fun q : ℝ≥0 × Ω => u q.1 q.2 := by
  have hn : ∀ n : ℕ, Measurable fun q : ℝ≥0 × Ω => u (min q.1 n) q.2 := fun n => by
    have h1 := measurable_prod_of_isStronglyProgressive h (n : ℝ≥0)
    have hle : (inferInstance : MeasurableSpace (Iic (n : ℝ≥0))).prod (𝓕 n) ≤
        (inferInstance : MeasurableSpace (Iic (n : ℝ≥0) × Ω)) :=
      sup_le_sup le_rfl (MeasurableSpace.comap_mono (𝓕.le n))
    have h2 : Measurable fun p : Iic (n : ℝ≥0) × Ω => u p.1 p.2 := h1.mono hle le_rfl
    have hm : Measurable fun q : ℝ≥0 × Ω => ((⟨min q.1 n, mem_Iic.2 (min_le_right _ _)⟩ : Iic (n : ℝ≥0)), q.2) :=
      (measurable_fst.min measurable_const).subtype_mk.prodMk measurable_snd
    exact h2.comp hm
  refine measurable_of_tendsto_metrizable hn (tendsto_pi_nhds.2 fun q => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈(q.1 : ℝ)⌉₊] with n hn'
  have hq : q.1 ≤ (n : ℝ≥0) := by
    have := (Nat.le_ceil (q.1 : ℝ)).trans (Nat.cast_le.2 hn')
    exact_mod_cast this
  simp only [min_eq_left hq]

end Joint

/-! ### The concrete families -/

section Fam

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The large direction's initial image word** at the frozen time `σ`: the small curve's seeds `x⁺`, `x⁻` and tip,
relative to the image of the large curve's start (`A1Asm.EightRectLaw`'s `ΘL`). -/
def eightFstWord (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ) (σ : ℝ≥0) (x : X) :
    Fin 3 → ℝ :=
  ![VR₁ 0 σ x - VR₁ 1 σ x, W₁ σ x - VR₁ 1 σ x, VL₁ 0 σ x - VR₁ 1 σ x]

/-- **The large direction's image forces**: the initial word at time `0`, and FORCES's canonical forces of the
frozen-chart marks `largeEightMarks` at positive times. -/
def eightFstVL (xs : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (i : Fin 3)
    (t : ℝ≥0) (z : X × Y) : ℝ :=
  if t = 0 then eightFstWord W₁ VL₁ VR₁ σ z.1 i else
    rForceFst (fun t x => (t : ℝ≥0∞) < ζ₁ x) 0 W₂ (fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) xs W₁
      (fun _ => σ) (fun x => largeEightMarks (xs - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) σ i)
      t z

/-- **The image curve's own time of the raw cap `k`**: the large curve's rectangle exit when the frozen small curve is
protected (`σ ≤ eightS₁ᵏ`), `0` otherwise (patched records). -/
def eightFstOwn (xs : ℝ) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0)
    (k : ℕ) (z : X × Y) : ℝ :=
  if σ ≤ eightS₁ xs W₁' ζ₁' k z.1 then (eightS₂ xs W₂' ζ₂' k z.2 : ℝ) else 0

/-- **The raw caps** of the large direction: the image capacity (`capFst`) at the own time `eightFstOwn`. -/
def eightFstCap (xs : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0)
    (k : ℕ) : X × Y → ℝ≥0 :=
  capFst (fun t x => (t : ℝ≥0∞) < ζ₁ x) 0 W₂ (fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) xs W₁ (fun _ => σ)
    (eightFstOwn xs W₁' ζ₁' W₂' ζ₂' σ k)

/-- **The rectangle densities at the stop**: `M(σ ∧ S₁ᵏ, S₂ᵏ)` of the patched Eight records. -/
def eightFstD (κ xs : ℝ) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 2 → ℝ≥0 → X → ℝ)
    (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0) (k : ℕ) (z : X × Y) : ℝ≥0∞ :=
  ENNReal.ofReal (seedHeightField (eightRec κ (-xs) W₁' VL₁' VR₁' W₂' (eightS₁ xs W₁' ζ₁') k) z
    (min σ (eightS₁ xs W₁' ζ₁' k z.1) : ℝ≥0) (eightS₂ xs W₂' ζ₂' k z.2))

omit mX mY in
/-- The forces start at the initial word. -/
theorem eightFstVL_zero (xs : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (i : Fin 3)
    (z : X × Y) : eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i 0 z = eightFstWord W₁ VL₁ VR₁ σ z.1 i := by
  simp only [eightFstVL, ↓reduceIte]

omit mX mY in
/-- **The initial word is admissible on the live event** (SEEDGEOM's `largeEight_isSeedWord`). -/
theorem isSeedWord_eightFstWord {κ xs : ℝ} (hxs : xs < 0) {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (hP : ∀ x, IsIntegratedSLEPath (kh κ) ![0] ![0, -xs] (smallEightRhoL κ) (smallEightRhoR κ) (W₁ · x)
      (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (B₁ · x) (ζ₁ x)) (σ : ℝ≥0) (x : X)
    (hσ : (σ : ℝ≥0∞) < ζ₁ x) :
    IsSeedWord (eightFstWord W₁ VL₁ VR₁ σ x) (![] : Fin 0 → ℝ) (largeEightImgRhoL κ) ![] :=
  largeEight_isSeedWord hxs (hP x) hσ

end Fam

/-! ### Measurability of the forces and the raw caps -/

section Meas

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

variable {κ xs : ℝ} {P₁ : Measure X} {𝓕₁ : Filtration ℝ≥0 mX} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {P₂ : Measure Y} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
  {ζ₂ : Y → ℝ≥0∞}

/-- The standing pathwise and measurability facts of the two regular Eight marginals used by FORCES's lemmas. -/
theorem eightFst_facts
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -xs] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![xs] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    MeasurableSet {q : ℝ≥0 × X | (q.1 : ℝ≥0∞) < ζ₁ q.2} ∧
    (∀ y, ContinuousOn (W₂ · y) {t | (t : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)}) ∧ (∀ y, W₂ 0 y = 0) ∧
    (∀ x, ContinuousOn (W₁ · x) {t | (t : ℝ≥0∞) < ζ₁ x}) ∧ (∀ x, W₁ 0 x = 0) ∧
    (∀ t, Measurable (W₂ t)) ∧ (∀ t, Measurable (W₁ t)) ∧
    Measurable (fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) ∧ Measurable ζ₁ := by
  have hcW : ∀ y, ContinuousOn (W₂ · y) {s | (s : ℝ≥0∞) < ζ₂ y} := fun y => (h₂.path y).2.2.2.1
  have hcV : ∀ y, ContinuousOn (VL₂ 0 · y) {s | (s : ℝ≥0∞) < ζ₂ y} := fun y => (h₂.path y).2.2.2.2.1 0
  have hS := measurableSet_live_of_isStronglyProgressive
    (isStronglyProgressive_indicator_isStripLife h₂.evol.2.1 h₂.progW (h₂.progVL 0) hcW hcV)
  have hζ₁ := measurable_lifetime h₁.evol.2.1
  exact ⟨measurableSet_lt measurable_fst.coe_nnreal_ennreal (hζ₁.comp measurable_snd),
    fun y => (hcW y).mono fun t ht => lt_of_lt_of_le ht (lifeEnd_le _ _ _), fun y => (h₂.path y).1,
    fun x => (h₁.path x).2.2.2.1, fun x => (h₁.path x).1, measurable_of_isStronglyProgressive h₂.progW,
    measurable_of_isStronglyProgressive h₁.progW, measurable_lifeEnd hS, hζ₁⟩

/-- **The forces are jointly measurable in the frozen time and the sample** (`hVL` of the masked assembly). -/
theorem measurable_eightFstVL
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -xs] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![xs] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (i : Fin 3) (t : ℝ≥0) :
    Measurable fun p : ℝ≥0 × (X × Y) => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ p.1 i t p.2 := by
  have hW := measurable_uncurry_of_isStronglyProgressive h₁.progW
  have hL := fun i => measurable_uncurry_of_isStronglyProgressive (h₁.progVL i)
  have hR := fun j => measurable_uncurry_of_isStronglyProgressive (h₁.progVR j)
  have hπ : Measurable fun p : ℝ≥0 × (X × Y) => (p.1, p.2.1) := measurable_fst.prodMk measurable_snd.fst
  by_cases ht : t = 0
  · simp only [eightFstVL, ht, ↓reduceIte, eightFstWord]
    fin_cases i
    · exact ((hR 0).comp hπ).sub ((hR 1).comp hπ)
    · exact (hW.comp hπ).sub ((hR 1).comp hπ)
    · exact ((hL 0).comp hπ).sub ((hR 1).comp hπ)
  · have e : (fun p : ℝ≥0 × (X × Y) => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ p.1 i t p.2) = fun p =>
        rForceFst (fun t x => (t : ℝ≥0∞) < ζ₁ x) 0 W₂ (fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) xs W₁
          (fun _ => p.1) (fun x => largeEightMarks (xs - 0) (W₁ · x) (fun i t => VL₁ i t x)
            (fun j t => VR₁ j t x) p.1 i) t p.2 :=
      funext fun p => by unfold eightFstVL; exact ite_eq_right_of_eq_false _ _ (eq_false ht)
    rw [e]
    obtain ⟨hlive, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := eightFst_facts h₁ h₂
    exact measurable_rForceFst (live := fun t x => (t : ℝ≥0∞) < ζ₁ x) (Wj := W₂)
      (ζj := fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) (Wk := W₁) (ζk := ζ₁)
      (p := fun σ x => largeEightMarks (xs - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) σ i)
      hlive (fun _ _ h => h) hjc hj0 hkc hk0 hjm hkm hζj hζk 0 xs
      (measurable_largeEightMarks hW hL hR (xs - 0) i) t

/-- **The raw caps are jointly measurable in the frozen time and the sample** (`hS₀` of the masked assembly). -/
theorem measurable_eightFstCap {W₁' : ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞} {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -xs] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![xs] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hS₁ : ∀ k, Measurable (eightS₁ xs W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (eightS₂ xs W₂' ζ₂' k)) (k : ℕ) :
    Measurable fun p : ℝ≥0 × (X × Y) =>
      eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' p.1 k p.2 := by
  obtain ⟨hlive, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := eightFst_facts h₁ h₂
  have hT : Measurable fun q : ℝ≥0 × (X × Y) => eightFstOwn xs W₁' ζ₁' W₂' ζ₂' q.1 k q.2 :=
    Measurable.ite (measurableSet_le measurable_fst ((hS₁ k).comp measurable_snd.fst))
      ((hS₂ k).comp measurable_snd.snd).coe_nnreal_real measurable_const
  unfold eightFstCap
  exact measurable_capFst (live := fun t x => (t : ℝ≥0∞) < ζ₁ x) (Wj := W₂)
    (ζj := fun y => lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) (Wk := W₁) (ζk := ζ₁) (xj := 0) (xk := xs)
    (T := fun σ => eightFstOwn xs W₁' ζ₁' W₂' ζ₂' σ k) hlive (fun _ _ h => h) hjc hj0 hkc hk0 hjm hkm hζj hζk hT

end Meas

/-! ### The Eight large-direction family law from its remaining inputs -/

section Assembly

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **`EightRectLawFstC`'s conclusion from the concrete families** (`hasFamilyLawFstC_of_masked` with the forces
`eightFstVL`, the raw caps `eightFstCap`, the densities `eightFstD`, masked off the good sets `G₁`, `G₂` of the
patches). Proved here: the joint measurability of the canonical driver, the forces and the raw caps, the admissibility
of the initial word and the initial forces. The remaining inputs are named: `hD` (the densities), `hgeo` (the geometry
at good samples with a positive raw cap), `hlaw` (the one-sample laws at good small samples, with the raw caps and the
residual as the noise) and `hstop` (the per-stop record inputs). -/
theorem hasFamilyLawFstC_eight_of_inputs {κ xs : ℝ} (hκ : 0 < κ) (hxs : xs < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)} [IsProbabilityMeasure μ]
    {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (h₂ : IsRegMarginal κ ![xs] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -xs] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁' : Fin 2 → ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (hS₁ : ∀ k, Measurable (eightS₁ xs W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (eightS₂ xs W₂' ζ₂' k))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0)
    (hG₂0 : P₂ G₂ᶜ = 0)
    (hD : ∀ k, Measurable fun p : ℝ≥0 × (X × Y) => eightFstD κ xs W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' p.1 k p.2)
    (hgeo : ∀ σ k z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z →
      SeedImageGeometry (eightFstWord W₁ VL₁ VR₁ σ z.1) ![] (largeEightImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs
          W₁ (fun _ => σ) (min t (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun i t => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i
          (min t (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun j _ => (j.elim0 : ℝ)) (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z))
    (hlaw : ∀ k, ∀ᵐ x ∂P₁, x ∈ G₁ → ∀ σ : ℝ≥0,
      IsSeedSampleLaw (P₂.withDensity fun y => eightFstD κ xs W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' σ k (x, y))
        (fun t y => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs
          W₁ (fun _ => σ) t (x, y))
        (fun y => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs
          W₁ (fun _ => σ) (x, y))
        (fun i t y => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x, y)) (fun j _ _ => (j.elim0 : ℝ))
        (fun t y => seedCapacityNoise κ (largeEightImgRhoL κ) ![]
          (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω))
            xs W₁ (fun _ => σ) s (x, y))
          (fun i s => eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x, y)) (fun j _ => (j.elim0 : ℝ)) t)
        (fun k' y => eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k' (x, y)) k)
    (hstop : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (ResStopInputFst P₁ P₂ μ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs W₁ (eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂)
        (fun _ j _ _ => (j.elim0 : ℝ)) (maskCap G₁ G₂ (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (eightFstD κ xs W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
      (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs W₁
      (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
      (fun _ _ => ![]) (largeEightImgRhoL κ) ![] := by
  obtain ⟨hlive, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := eightFst_facts h₁ h₂
  have hm3 := (measurable_rDrvFst_rLifeFst (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) hlive (fun _ _ h => h) hjc hj0
    hkc hk0 hjm hkm hζj hζk 0 xs).1
  exact hasFamilyLawFstC_of_masked hκ (eightFstVL xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂) (fun _ j _ _ => (j.elim0 : ℝ))
    (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (eightFstD κ xs W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') hG₁ hG₂ hG₁0 hG₂0
    hm3 (fun i t => measurable_eightFstVL h₁ h₂ i t) (fun j => j.elim0)
    (fun k => measurable_eightFstCap h₁ h₂ hS₁ hS₂ k) hD hgeo
    (fun σ x hσ => isSeedWord_eightFstWord hxs h₁.path σ x hσ)
    (fun σ z _ i => eightFstVL_zero xs W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i z) (fun _ _ _ j => j.elim0) hlaw hstop

end Assembly

end InteractingSLE.ZhanGT4.A1RLaw
