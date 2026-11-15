/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2FstStopDrv
import InteractingSLE.Spec.ZhanGT4.A2Part3Pull

/-!
# Zhan's A.1 under R83, (G3), large-curve direction: `hcov` and the per-stop input `ResStopInputFst`

Packet PROVE-A1-G3LAW2.

* **`g3Fst_cover`**: for a live small sample at the frozen time `σ`, every own time `s` of the large curve before
  contact is below the own time of some rectangle (ASSEMBLE's `exists_rect_leG_of_marks` at `s' ∈ (s, contact)`: the
  large curve is strip-alive before `lifeEnd`, so `x`, `y` are off its closed hull (`large_force_facts`); `x − y`,
  `−y` are off the closed small hull (`notMem_closure_fwdHull_of_force`));
* **`g3FstStop_hcov`**: the record fact `hcov` (a.e. on the good pairs);
* **`g3FstStop_of_good`**: the per-stop input `hstop` of the large direction (`Nonempty (ResStopInputFst …)` for the
  original data, the forces `g3FstVL` and the masked caps — exactly the input `hstop` of PROVE-A1-G3LARGE's
  `hasFamilyLawFstC_g3_of_inputsC` and of G3LAW's `hasFamilyLawFstC_g3_of_inputs`), via G3LAW's `g3FstResStop`. It is a
  conditional helper: the per-sample facts of the patched large curve `hlife` (`S₂ᵏ < lifeEnd`) and `hgood` (`S₂ᵏ` good
  at `0 < σ ≤ S₁ᵏ`) are PROVE-A1-G3LARGE's `g3Fst_lt_lifeEnd` and `g3Fst_isGoodTime`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom A1MultiMark

section Cover

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

/-- **The rectangles exhaust the large own times before contact** (live small sample at the frozen time `σ`). -/
theorem g3Fst_cover (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hl : (σ : ℝ≥0∞) < ζ₁ x₀) (s : ℝ≥0)
    (hs : (s : ℝ≥0∞) < contactTime 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
      (Strip.extPath (W₁ · x₀)) σ) :
    ∃ m, (s : ℝ) < g3FstOwn x y W₁ ζ₁ W₂ ζ₂ σ m (x₀, y₀) := by
  obtain ⟨-, -, hR1, hR2, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  obtain ⟨s', hss', hs'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hs'l : (s' : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) := hs'c.trans_le (min_le_left _ _)
  have hlive₂ := A2X.P3.isStripLife_of_lt_lifeEnd hs'l
  have hs'ζ : (s' : ℝ≥0∞) < ζ₂ y₀ := hlive₂.1
  -- the closed prefixes are disjoint before contact
  have hd0 : Disjoint (closure (physHull y (Strip.extPath (W₁ · x₀)) σ))
      (closure (physHull 0 (Strip.extPath (W₂ · y₀)) s')) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    have hne' : (closure (physHull 0 (Strip.extPath (W₂ · y₀)) s') ∩
        closure (physHull y (Strip.extPath (W₁ · x₀)) σ)).Nonempty := by
      rw [Set.inter_comm]; exact hne
    have hle : contactTime 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
        (Strip.extPath (W₁ · x₀)) σ ≤ (s' : ℝ≥0∞) :=
      (min_le_right _ _).trans (iInf₂_le s' hne')
    exact lt_irrefl _ (hs'c.trans_le hle)
  -- translate by `-y`
  have hsh : ∀ A : Set ℂ, closure ((fun z : ℂ => z + ((-y : ℝ) : ℂ)) '' A) =
      (fun z : ℂ => z + ((-y : ℝ) : ℂ)) '' closure A :=
    fun A => ((Homeomorph.addRight ((-y : ℝ) : ℂ)).image_closure A).symm
  have hK₁ : closure (fwdHull (Strip.extPath (W₁ · x₀)) σ) =
      (fun z : ℂ => z + ((-y : ℝ) : ℂ)) '' closure (physHull y (Strip.extPath (W₁ · x₀)) σ) := by
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
  have hK₂ : closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -y) s') =
      (fun z : ℂ => z + ((-y : ℝ) : ℂ)) '' closure (physHull 0 (Strip.extPath (W₂ · y₀)) s') := by
    have e1 : (Strip.extPath fun u => W₂ u y₀ + -y) = fun s => Strip.extPath (W₂ · y₀) s + -y := rfl
    rw [e1, ConformalImageFull.fwdHull_add_const, physHull_zero, hsh]
  have hinj : Function.Injective (fun z : ℂ => z + ((-y : ℝ) : ℂ)) := add_left_injective _
  -- the marks
  obtain ⟨-, -, hy₀n⟩ := large_force_facts (h₂.path y₀) hlive₂ 1 0
  obtain ⟨-, -, hx₀n⟩ := large_force_facts (h₂.path y₀) hlive₂ 0 0
  obtain ⟨-, -, -, hcw, -, hcR, -, -, -, -, -, -, -, -, hReq, -⟩ := h₁.path x₀
  have hsmall : ∀ j : Fin 3, (∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ₁ x₀ → VR₁ j r x₀ ≠ W₁ r x₀) →
      (((![0, x - y, -y] : Fin 3 → ℝ) j : ℝ) : ℂ) ∉ closure (fwdHull (Strip.extPath (W₁ · x₀)) σ) :=
    fun j hne => notMem_closure_fwdHull_of_force (hcR j) hcw (fun t ht => hReq t ht j) hl
      fun r hr => hne r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hl)
  have hm1 := hsmall 1 fun r hr => hR1 x₀ r hr
  have hm2 := hsmall 2 fun r hr => hR2 x₀ r hr
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hm1 hm2
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, add_zero] at hy₀n hx₀n
  rw [physHull_zero] at hy₀n hx₀n
  have hoff₂ : ∀ q : ℝ, (q : ℂ) ∉ closure (fwdHull (Strip.extPath (W₂ · y₀)) s') →
      ((q - y : ℝ) : ℂ) ∉ closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -y) s') := by
    intro q hq hmem
    rw [hK₂, physHull_zero] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have : z = (q : ℂ) := by
      have h1 : z + ((-y : ℝ) : ℂ) = ((q - y : ℝ) : ℂ) := hze
      push_cast at h1
      linear_combination h1
    exact hq (this ▸ hz)
  have hy0 : y ≠ 0 := (hyx.trans hx).ne
  have hdisj : Disjoint (closure (fwdHull (Strip.extPath (W₁ · x₀)) σ) ∪ {0})
      (closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -y) s') ∪ {((-y : ℝ) : ℂ)}) := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨?_, ?_⟩, Set.disjoint_union_right.2 ⟨?_, ?_⟩⟩
    · rw [hK₁, hK₂]
      exact (disjoint_image_iff hinj).2 hd0
    · exact Set.disjoint_singleton_right.2 (by exact_mod_cast hm2)
    · refine Set.disjoint_singleton_left.2 ?_
      have h := hoff₂ y hy₀n
      rwa [sub_self, ofReal_zero] at h
    · refine Set.disjoint_singleton.2 ?_
      intro h
      have := congrArg Complex.re h
      simp only [zero_re, ofReal_re] at this
      exact hy0 (by linarith)
  have hp : ∀ j, (((![x - y] : Fin 1 → ℝ) j : ℝ) : ℂ) ∉ (closure (fwdHull (Strip.extPath (W₁ · x₀)) σ) ∪ {0}) ∪
      (closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -y) s') ∪ {((-y : ℝ) : ℂ)}) := by
    intro j
    fin_cases j
    simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rintro ((h | h) | (h | h))
    · exact hm1 (by exact_mod_cast h)
    · have := congrArg Complex.re h
      simp only [zero_re, ofReal_re, mem_singleton_iff] at this h
      have := congrArg Complex.re h
      simp only [zero_re, ofReal_re] at this
      linarith
    · exact hoff₂ x hx₀n h
    · have := congrArg Complex.re h
      simp only [ofReal_re, mem_singleton_iff] at this h
      have := congrArg Complex.re h
      simp only [ofReal_re] at this
      linarith
  obtain ⟨m, hm₁, hm₂⟩ := exists_rect_leG_of_marks hyx hx (h₁.path x₀).2.2.2.1 (h₂.path y₀).2.2.2.1
    (h₂.path y₀).1 hl hs'ζ hdisj hp
  refine ⟨m, ?_⟩
  have hown : g3FstOwn x y W₁ ζ₁ W₂ ζ₂ σ m (x₀, y₀) = g3S₂ x y W₂ ζ₂ m y₀ := by
    simp only [g3FstOwn, show σ ≤ g3S₁ x y W₁ ζ₁ m x₀ from hm₁, ↓reduceIte]
  rw [hown]
  exact lt_of_lt_of_le (by exact_mod_cast hss') (NNReal.coe_le_coe.2 hm₂)

end Cover

section Cov

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {VL₁o : Fin 1 → ℝ≥0 → X → ℝ} {VR₁o : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞}
  {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hlife : ∀ (k : ℕ) (_ : X) (y₀ : Y),
    (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀))
  (hgood : ∀ (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0}, 0 < σ → σ ≤ g3S₁ x y W₁ ζ₁ k x₀ →
    A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
      (Strip.extPath (W₁ · x₀)) σ (g3S₂ x y W₂ ζ₂ k y₀))
  (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0)
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ (∀ i t, VL₁o i t x' = VL₁ i t x') ∧
    (∀ j t, VR₁o j t x' = VR₁ j t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂

/-- **`hcov`** (large direction): the masked caps exhaust the canonical clock before contact, a.e. under a coupling
of the marginals. -/
theorem g3FstStop_hcov (τ : X → ℝ≥0) {μ : Measure (X × Y)} (hμ₁ : μ.map Prod.fst = P₁)
    (hμ₂ : μ.map Prod.snd = P₂) :
    ∀ᵐ z ∂μ, (τ z.1 : ℝ≥0∞) < ζ₁o z.1 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime 0
        (Strip.extPath (W₂o · z.2)) (lifeEnd (W₂o · z.2) (VL₂o 0 · z.2) (ζ₂o z.2)) y (Strip.extPath (W₁o · z.1))
        (τ z.1) →
      ∃ m, A1Ref.imgClk 0 (Strip.extPath (W₂o · z.2)) y (Strip.extPath (W₁o · z.1)) (τ z.1) s ≤
        maskCap G₁ G₂ (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) (τ z.1) m z := by
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
  obtain ⟨hW₁a, -, -, hζ₁a⟩ := hag₁ z.1 h1
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ z.2 h2
  have eW₁ : (W₁o · z.1) = (W₁ · z.1) := funext hW₁a
  have eW₂ : (W₂o · z.2) = (W₂ · z.2) := funext hW₂a
  have eV₂ : (VL₂o 0 · z.2) = (VL₂ 0 · z.2) := funext (hV₂a 0)
  have hl : (τ z.1 : ℝ≥0∞) < ζ₁ z.1 := by rw [← hζ₁a]; exact hlo
  rw [eW₁, eW₂, eV₂, hζ₂a] at hs
  rw [eW₁, eW₂]
  have hj : ∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2) →
      ContinuousOn (Strip.extPath (W₂ · z.2)) (Icc 0 T) := fun T hT => A1Ref.continuousOn_extPath_Icc
    ((h₂.path z.2).2.2.2.1.mono fun t ht => lt_of_lt_of_le ht (lifeEnd_le _ _ _)) hT
  have hk : ∃ τ' : ℝ, ((τ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · z.1)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (h₁.path z.1).2.2.2.1 hl
  obtain ⟨m, hm⟩ := cover_capFst (z := z) (τ := fun _ => τ z.1) (live := fun t x' => (t : ℝ≥0∞) < ζ₁ x')
    (xj := 0) (Wj := W₂) (ζj := fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) (xk := y) (Wk := W₁)
    (Tm := fun m => g3FstOwn x y W₁ ζ₁ W₂ ζ₂ (τ z.1) m) hl hj (h₂.path z.2).1 hk (h₁.path z.1).1
    (fun s' hs' => g3Fst_cover hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ z.1 z.2 hl s' hs')
    (fun m => g3FstStop_fin hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood m hl) s hs
  refine ⟨m, hm.trans_eq ?_⟩
  rw [g3FstStop_mask_eq (g3Fst_hag₁ hag₁) hag₂ m h1 h2]
  rfl

end Cov

/-- **The per-stop input `hstop` of the large direction from the per-sample facts of the patched large curve**
(conditional helper: `hlife'`, `hgood'` are PROVE-A1-G3LARGE's `g3Fst_lt_lifeEnd`, `g3Fst_isGoodTime` for the patch).
Binders as `hasFamilyLawC_g3_sndC` (original marginals unprimed, patches primed). -/
theorem g3FstStop_of_good {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    {X Y : Type} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] [StandardBorelSpace X] [StandardBorelSpace Y]
    {P₁ : Measure X} {P₂ : Measure Y} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)}
    {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂' : ℝ≥0 → Y → ℝ} {VL₂' : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂' : Fin 0 → ℝ≥0 → Y → ℝ} {B₂' : ℝ≥0 → Y → ℝ}
    {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ} {VR₁' : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁' : ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (h₂' : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂' VL₂' VR₂' B₂' ζ₂')
    (hB₂' : ∀ ω, Continuous (B₂' · ω))
    (h₁' : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
      W₁' VL₁' VR₁' B₁' ζ₁')
    (hB₁' : ∀ ω, Continuous (B₁' · ω))
    (hg₁' : ∀ ω, GoodSmallG3 (W₁' · ω) (fun i t => VL₁' i t ω) (fun i t => VR₁' i t ω) (B₁' · ω) (ζ₁' ω))
    (hlife' : ∀ (k : ℕ) (_ : X) (y₀ : Y),
      (g3S₂ x y W₂' ζ₂' k y₀ : ℝ≥0∞) < lifeEnd (W₂' · y₀) (VL₂' 0 · y₀) (ζ₂' y₀))
    (hgood' : ∀ (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0}, 0 < σ → σ ≤ g3S₁ x y W₁' ζ₁' k x₀ →
      A1Ref.IsGoodTime 0 (Strip.extPath (W₂' · y₀)) (lifeEnd (W₂' · y₀) (VL₂' 0 · y₀) (ζ₂' y₀)) y
        (Strip.extPath (W₁' · x₀)) σ (g3S₂ x y W₂' ζ₂' k y₀))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0)
    (hG₂0 : P₂ G₂ᶜ = 0)
    (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁ t x' = W₁' t x') ∧ (∀ i t, VL₁ i t x' = VL₁' i t x') ∧
      (∀ j t, VR₁ j t x' = VR₁' j t x') ∧ ζ₁ x' = ζ₁' x')
    (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂ t y' = W₂' t y') ∧ (∀ i t, VL₂ i t y' = VL₂' i t y') ∧ ζ₂ y' = ζ₂' y')
    (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁' ζ₁' m ω : WithTop ℝ≥0))
    (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂' ζ₂' m ω : WithTop ℝ≥0))
    (hμ₁ : μ.map Prod.fst = P₁) (hμ₂ : μ.map Prod.snd = P₂)
    (hd : ∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
      ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁' VL₁' VR₁' W₂' (g3S₁ x y W₁' ζ₁') m) ω
        (g3S₁ x y W₁' ζ₁' m ω.1) (g3S₂ x y W₂' ζ₂' m ω.2))) :
    ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (ResStopInputFst P₁ P₂ μ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂)
        (fun _ j _ _ => (j.elim0 : ℝ)) (maskCap G₁ G₂ (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B}) :=
  fun τ hτ => ⟨g3FstResStop hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hd hτ
    (g3FstStop_hSm hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hlife' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂)
    (g3FstStop_hstop hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hlife' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂)
    (g3FstStop_hgW hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hlife' hgood' hs₁ hs₂ hτ hag₁ hag₂)
    (g3FstStop_hgVL hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hlife' hgood' hs₁ hs₂ hτ hag₁ hag₂)
    (fun _ j _ => j.elim0)
    (g3FstStop_hgS hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hlife' hgood' hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂)
    (fun m z => g3Fst_hgζ x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' G₁ G₂ τ m z)
    (g3FstStop_hcov hκ4 hκ8 hyx hx h₁' hB₁' hg₁' h₂' hB₂' hlife' hgood' hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ τ hμ₁ hμ₂)⟩

end InteractingSLE.ZhanGT4.A1G3L2
