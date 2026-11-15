/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopDrv
import InteractingSLE.Spec.ZhanGT4.A1AsmSeg

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the clock exhaustion `hcov`

Packet PROVE-A1-G3LAW2.

* **`notMem_closure_fwdHull_of_force`**: a force point whose force process has not met the driver by time `T`
  (before the lifetime) is off the closed hull at `T`;
* **`g3_cover`**: for a live large sample at the frozen time `σ`, every own time `s` before contact is below the own
  time of some rectangle (A1-ASSEMBLE's `exists_rect_leG_of_marks` at a time `s' ∈ (s, contact)`: the closed prefixes
  are disjoint before contact, the marks `x`, `y` are off the closed large hull (strip life), the large start and the
  mark `x` are off the closed small hull (`GoodSmallG3`));
* **`g3Stop_hcov`**: the record fact `hcov` of `ResStopInput` (masked caps; a.e. on the good pairs).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

/-- **A force point whose force process has not met the driver is off the closed hull.** -/
theorem notMem_closure_fwdHull_of_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ T, v r ≠ w r) :
    (p : ℂ) ∉ closure (fwdHull (Strip.extPath w) T) := by
  have hu := isForwardSol_extPath_of_force hv hw hveq hT hsep
  obtain ⟨τ', hTτ', hcτ⟩ := A1Ref.exists_continuousOn_extPath_beyond hw hT
  set V := stopDrv (Strip.extPath w) τ' with hVdef
  have hVc : Continuous V := continuous_stopDrv hcτ (T.coe_nonneg.trans hTτ'.le)
  have hVe : EqOn (Strip.extPath w) V (Icc 0 τ') := (stopDrv_eqOn _ τ').symm
  have hu' : IsForwardSol V (p : ℂ) T _ :=
    QuantumZipper.isForwardSol_congr_drive (fun r hr => hVe ⟨hr.1, hr.2.trans hTτ'.le⟩) hu
  rw [LocalExt.fwdHull_congr_of_eqOn_of_lt T.coe_nonneg hTτ' hVe]
  exact A2TipSep.not_mem_closure_fwdHull_of_isForwardSol hVc T.coe_nonneg hu'

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

/-- **The rectangles exhaust the own times before contact** (live large sample at the frozen time `σ`). -/
theorem g3_cover (y₀ : Y) (x₀ : X) {σ : ℝ≥0} (hl : g3SndLive W₂ VL₂ ζ₂ σ y₀) (s : ℝ≥0)
    (hs : (s : ℝ≥0∞) < contactTime y (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ) :
    ∃ m, (s : ℝ) < g3SndOwn x y W₁ ζ₁ W₂ ζ₂ σ m (x₀, y₀) := by
  obtain ⟨-, -, hR1, hR2, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  obtain ⟨s', hss', hs'c⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hs'ζ : (s' : ℝ≥0∞) < ζ₁ x₀ := hs'c.trans_le (min_le_left _ _)
  -- the closed prefixes are disjoint before contact
  have hd0 : Disjoint (closure (physHull y (Strip.extPath (W₁ · x₀)) s'))
      (closure (physHull 0 (Strip.extPath (W₂ · y₀)) σ)) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    have hle : contactTime y (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ ≤ (s' : ℝ≥0∞) :=
      (min_le_right _ _).trans (iInf₂_le s' hne)
    exact lt_irrefl _ (hs'c.trans_le hle)
  -- translate by `-y`
  have hsh : ∀ A : Set ℂ, closure ((fun z : ℂ => z + ((-y : ℝ) : ℂ)) '' A) =
      (fun z : ℂ => z + ((-y : ℝ) : ℂ)) '' closure A :=
    fun A => ((Homeomorph.addRight ((-y : ℝ) : ℂ)).image_closure A).symm
  have hK₁ : closure (fwdHull (Strip.extPath (W₁ · x₀)) s') =
      (fun z : ℂ => z + ((-y : ℝ) : ℂ)) '' closure (physHull y (Strip.extPath (W₁ · x₀)) s') := by
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
  have hK₂ : closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -y) σ) =
      (fun z : ℂ => z + ((-y : ℝ) : ℂ)) '' closure (physHull 0 (Strip.extPath (W₂ · y₀)) σ) := by
    have e1 : (Strip.extPath fun u => W₂ u y₀ + -y) = fun s => Strip.extPath (W₂ · y₀) s + -y := rfl
    rw [e1, ConformalImageFull.fwdHull_add_const, physHull_zero, hsh]
  have hinj : Function.Injective (fun z : ℂ => z + ((-y : ℝ) : ℂ)) := add_left_injective _
  -- the marks
  obtain ⟨hy₀, -, hy₀n⟩ := large_force_facts (h₂.path y₀) hl 1 0
  obtain ⟨hx₀, -, hx₀n⟩ := large_force_facts (h₂.path y₀) hl 0 0
  obtain ⟨-, -, hR0, hcw, -, hcR, -, -, hwR, -, -, -, -, -, hReq, -⟩ := h₁.path x₀
  have hsmall : ∀ j : Fin 3, (∀ r : ℝ≥0, (r : ℝ≥0∞) < ζ₁ x₀ → VR₁ j r x₀ ≠ W₁ r x₀) →
      (((![0, x - y, -y] : Fin 3 → ℝ) j : ℝ) : ℂ) ∉ closure (fwdHull (Strip.extPath (W₁ · x₀)) s') :=
    fun j hne => notMem_closure_fwdHull_of_force (hcR j) hcw (fun t ht => hReq t ht j) hs'ζ
      fun r hr => hne r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hs'ζ)
  have hm1 := hsmall 1 fun r hr => hR1 x₀ r hr
  have hm2 := hsmall 2 fun r hr => hR2 x₀ r hr
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hm1 hm2
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, add_zero] at hy₀n hx₀n
  rw [physHull_zero] at hy₀n hx₀n
  have hoff₂ : ∀ q : ℝ, (q : ℂ) ∉ closure (fwdHull (Strip.extPath (W₂ · y₀)) σ) →
      ((q - y : ℝ) : ℂ) ∉ closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -y) σ) := by
    intro q hq hmem
    rw [hK₂, physHull_zero] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have : z = (q : ℂ) := by
      have h1 : z + ((-y : ℝ) : ℂ) = ((q - y : ℝ) : ℂ) := hze
      push_cast at h1
      linear_combination h1
    exact hq (this ▸ hz)
  have hy0 : y ≠ 0 := (hyx.trans hx).ne
  have hdisj : Disjoint (closure (fwdHull (Strip.extPath (W₁ · x₀)) s') ∪ {0})
      (closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -y) σ) ∪ {((-y : ℝ) : ℂ)}) := by
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
  have hp : ∀ j, (((![x - y] : Fin 1 → ℝ) j : ℝ) : ℂ) ∉ (closure (fwdHull (Strip.extPath (W₁ · x₀)) s') ∪ {0}) ∪
      (closure (fwdHull (Strip.extPath fun u => W₂ u y₀ + -y) σ) ∪ {((-y : ℝ) : ℂ)}) := by
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
    (h₂.path y₀).1 hs'ζ hl.1 hdisj hp
  refine ⟨m, ?_⟩
  have hown : g3SndOwn x y W₁ ζ₁ W₂ ζ₂ σ m (x₀, y₀) = g3S₁ x y W₁ ζ₁ m x₀ := by
    simp only [g3SndOwn, show σ ≤ g3S₂ x y W₂ ζ₂ m y₀ from hm₂, ↓reduceIte]
  rw [hown]
  exact lt_of_lt_of_le (by exact_mod_cast hss') (NNReal.coe_le_coe.2 hm₁)

end Cover

end InteractingSLE.ZhanGT4.A1G3L2
