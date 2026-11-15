/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESRecDrv
import InteractingSLE.Spec.ZhanGT4.A1ERecCov

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the clock exhaustion `hcov`

Packet PROVE-A1-EIGHTSNDREC (the (Eight) mirror of PROVE-A1-G3LAW2's `g3_cover`, `g3Stop_hcov`).

* **`eight_cover`**: for a live large sample at the frozen time `σ` (any `σ`, `σ = 0` included), every own time `s`
  of the small curve before contact is below the own time of some rectangle (A1-COMMON's `exists_rect_le` at a time
  `s' ∈ (s, contact)`): the closed prefixes are disjoint before contact; the large curve's mark `x` (the small source)
  is off the closed large hull (strip life, `largeEight_force_facts`); the large source `0`, i.e. `−x` in the small
  frame, is off the closed small hull because the small curve's force point started at `−x` never meets its driver
  before `ζ₁` (A1-COMMON's `smallEight_sepP_of_good`: the order `W₁ < V_R⁰ ≤ V_R¹` of the real flow);
* **`eightStop_hcov`**: the record fact `hcov` of `ResStopInput` (masked caps; a.e. on the good pairs).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESRec

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1SeedGeom A1G3L2 A1ESnd

section Cover

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)

include hx h₁ hg₁ h₂

/-- **The rectangles exhaust the own times before contact** (live large sample at the frozen time `σ`, `σ = 0`
included). -/
theorem eight_cover (y₀ : Y) (x₀ : X) {σ : ℝ≥0} (hl : eightSndLive W₂ VL₂ ζ₂ σ y₀) (s : ℝ≥0)
    (hs : (s : ℝ≥0∞) < contactTime x (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ) :
    ∃ m, (s : ℝ) < eightSndOwn x W₁ ζ₁ W₂ ζ₂ σ m (x₀, y₀) := by
  have hx₂ : 0 < -x := by linarith
  obtain ⟨s', hss', hs'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hs'ζ : (s' : ℝ≥0∞) < ζ₁ x₀ := hs'c.trans_le (min_le_left _ _)
  -- the closed prefixes are disjoint before contact
  have hd0 : Disjoint (closure (physHull x (Strip.extPath (W₁ · x₀)) s'))
      (closure (physHull 0 (Strip.extPath (W₂ · y₀)) σ)) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    have hle : contactTime x (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ ≤ (s' : ℝ≥0∞) :=
      (min_le_right _ _).trans (iInf₂_le s' hne)
    exact lt_irrefl _ (hs'c.trans_le hle)
  -- translate by `-x` (the small curve's frame)
  have hsh : ∀ A : Set ℂ, closure ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' A) =
      (fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' closure A :=
    fun A => ((Homeomorph.addRight ((-x : ℝ) : ℂ)).image_closure A).symm
  have hK₁ : closure (fwdHull (Strip.extPath (W₁ · x₀)) s') =
      (fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' closure (physHull x (Strip.extPath (W₁ · x₀)) s') := by
    rw [← hsh]
    congr 1
    ext z
    simp only [physHull, mem_image, exists_exists_and_eq_and]
    constructor
    · intro hz
      exact ⟨z, hz, by push_cast; ring⟩
    · rintro ⟨w, hw, rfl⟩
      convert hw using 1
      push_cast
      ring
  have hK₂ : closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -x) σ) =
      (fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' closure (physHull 0 (Strip.extPath (W₂ · y₀)) σ) := by
    have e1 : (Strip.extPath fun u => W₂ u y₀ + -x) = fun s => Strip.extPath (W₂ · y₀) s + -x := rfl
    rw [e1, ConformalImageFull.fwdHull_add_const, physHull_zero, hsh]
  have hinj : Function.Injective (fun z : ℂ => z + ((-x : ℝ) : ℂ)) := add_left_injective _
  -- the mark `x` of the large curve is off the closed large hull (strip life)
  obtain ⟨-, -, hx₀n⟩ := largeEight_force_facts (h₂.path y₀) hl 0
  simp only [Matrix.cons_val_zero, add_zero] at hx₀n
  rw [physHull_zero] at hx₀n
  -- the large source `−x` (small frame) is off the closed small hull: the force point `VR₁ 1` is alive
  obtain ⟨-, -, -, hcw, -, hcR, -, -, -, -, -, -, -, -, hReq, -⟩ := h₁.path x₀
  have hm1 : (((![0, -x] : Fin 2 → ℝ) 1 : ℝ) : ℂ) ∉ closure (fwdHull (Strip.extPath (W₁ · x₀)) s') :=
    A1ERec.notMem_closure_fwdHull_of_force hcw (hcR 1) (fun t ht => hReq t ht 1) hs'ζ fun r hr =>
      smallEight_sepP_of_good hx (h₁.path x₀) (hg₁ x₀) r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hs'ζ)
  simp only [Matrix.cons_val_one] at hm1
  have hx0 : x ≠ 0 := hx.ne
  have hdisj : Disjoint (closure (fwdHull (Strip.extPath (W₁ · x₀)) s') ∪ {0})
      (closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -x) σ) ∪ {((-x : ℝ) : ℂ)}) := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨?_, ?_⟩, Set.disjoint_union_right.2 ⟨?_, ?_⟩⟩
    · rw [hK₁, hK₂]
      exact (disjoint_image_iff hinj).2 hd0
    · exact Set.disjoint_singleton_right.2 hm1
    · refine Set.disjoint_singleton_left.2 ?_
      intro hmem
      rw [hK₂, physHull_zero] at hmem
      obtain ⟨z, hz, hze⟩ := hmem
      have hzx : z = (x : ℂ) := by
        have h1 : z + ((-x : ℝ) : ℂ) = 0 := hze
        push_cast at h1
        linear_combination h1
      exact hx₀n (hzx ▸ hz)
    · refine Set.disjoint_singleton.2 ?_
      intro h
      have := congrArg Complex.re h
      simp only [zero_re, ofReal_re] at this
      exact hx0 (by linarith)
  obtain ⟨m, hm₁, hm₂⟩ := exists_rect_le (pm := (![] : Fin 0 → ℝ)) hx₂ (h₁.path x₀).2.2.2.1
    (h₂.path y₀).2.2.2.1 hs'ζ hl.1 hdisj fun j => j.elim0
  have hm₁' : s' ≤ eightS₁ x W₁ ζ₁ m x₀ := hm₁
  have hm₂' : σ ≤ eightS₂ x W₂ ζ₂ m y₀ := hm₂
  refine ⟨m, ?_⟩
  have hown : eightSndOwn x W₁ ζ₁ W₂ ζ₂ σ m (x₀, y₀) = eightS₁ x W₁ ζ₁ m x₀ := by
    simp only [eightSndOwn, hm₂', ↓reduceIte]
  rw [hown]
  exact lt_of_lt_of_le (by exact_mod_cast hss') (NNReal.coe_le_coe.2 hm₁')

end Cover

section Cov

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0)
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂

/-- **`hcov`**: the masked caps exhaust the canonical clock before contact, a.e. under a coupling of the marginals. -/
theorem eightStop_hcov (τ : Y → ℝ≥0) {μ : Measure (X × Y)} (hμ₁ : μ.map Prod.fst = P₁)
    (hμ₂ : μ.map Prod.snd = P₂) :
    ∀ᵐ z ∂μ, eightSndLive W₂o VL₂o ζ₂o (τ z.2) z.2 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime x
        (Strip.extPath (W₁o · z.1)) (ζ₁o z.1) 0 (Strip.extPath (W₂o · z.2)) (τ z.2) →
      ∃ m, A1Ref.imgClk x (Strip.extPath (W₁o · z.1)) 0 (Strip.extPath (W₂o · z.2)) (τ z.2) s ≤
        maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) (τ z.2) m z := by
  have hae₁ : ∀ᵐ z ∂μ, z.1 ∈ G₁ := by
    rw [ae_iff]
    have h : μ (Prod.fst ⁻¹' G₁ᶜ) = 0 := by
      rw [← Measure.map_apply measurable_fst hG₁.compl, hμ₁]
      exact hG₁0
    exact h
  have hae₂ : ∀ᵐ z ∂μ, z.2 ∈ G₂ := by
    rw [ae_iff]
    have h : μ (Prod.snd ⁻¹' G₂ᶜ) = 0 := by
      rw [← Measure.map_apply measurable_snd hG₂.compl, hμ₂]
      exact hG₂0
    exact h
  filter_upwards [hae₁, hae₂] with z h1 h2 hlo s hs
  obtain ⟨hW₁a, hζ₁a⟩ := hag₁ z.1 h1
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ z.2 h2
  have eW₁ : (W₁o · z.1) = (W₁ · z.1) := funext hW₁a
  have eW₂ : (W₂o · z.2) = (W₂ · z.2) := funext hW₂a
  have eV₂ : (VL₂o 0 · z.2) = (VL₂ 0 · z.2) := funext (hV₂a 0)
  have hl : eightSndLive W₂ VL₂ ζ₂ (τ z.2) z.2 := by
    have h := hlo
    simp only [eightSndLive, eW₂, eV₂, hζ₂a] at h
    exact h
  rw [eW₁, hζ₁a, eW₂] at hs
  rw [eW₁, eW₂]
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ z.1 → ContinuousOn (Strip.extPath (W₁ · z.1)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path z.1).2.2.2.1 hT
  have hk : ∃ τ' : ℝ, ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂ · z.2)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (h₂.path z.2).2.2.2.1 hl.1
  obtain ⟨m, hm⟩ := cover_capSnd (z := z) (τ := fun _ => τ z.2) (live := eightSndLive W₂ VL₂ ζ₂) (xj := x)
    (Wj := W₁) (ζj := ζ₁) (xk := 0) (Wk := W₂) (Tm := fun m => eightSndOwn x W₁ ζ₁ W₂ ζ₂ (τ z.2) m) hl hj
    (h₁.path z.1).1 hk (h₂.path z.2).1 (fun s' hs' => eight_cover hx h₁ hg₁ h₂ z.2 z.1 hl s' hs')
    (fun m => eightStop_fin hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m hl) s hs
  refine ⟨m, hm.trans_eq ?_⟩
  rw [eightStop_mask_eq hag₁ hag₂ m h1 h2]
  rfl

end Cov

end InteractingSLE.ZhanGT4.A1ESRec
