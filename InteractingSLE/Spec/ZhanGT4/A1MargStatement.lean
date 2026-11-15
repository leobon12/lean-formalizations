/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MargRect
import InteractingSLE.Spec.ZhanGT4.A1CoreStatement

/-!
# A.1's Rect statements from regular marginals and the law parts

Packet PROVE-A1-MARG (R76). `A1Core.A1DualCoupling{G3,Eight}RectStatement` asks for two standard Borel path spaces
with the two complete marginal evolutions, a coupling `μ`, and the two directional rectangle cores
`IsRectImageCore` / `IsRectImageCoreFst`, each the conjunction of the measurability clauses (m1)–(m4) and a law part.
This file proves the marginal and measurability content:

* `RectLawPart`, `RectLawPartFst`: the law parts (the last conjunct of the cores, verbatim), with
  `isRectImageCore_iff`, `isRectImageCoreFst_iff` (`Iff.rfl`);
* **`isRectImageCore_strip_of_reg`**, **`isRectImageCoreFst_lt_of_reg`**: for regular marginals (`IsRegMarginal`)
  and the live events and image words of A.1, (m1)–(m4) hold, so each core is its law part;
* **`A1DualCoupling{G3,Eight}MargStatement`**: the Rect statements with `IsRegMarginal` for the two marginals and
  only the law parts of the cores; **`a1DualCoupling{G3,Eight}RectStatement_of_marg`**;
* **`exists_regMarginals_G3`**, **`exists_regMarginals_Eight`**: the two complete marginal laws exist on standard Borel
  spaces as regular marginals, and **`a1DualCoupling{G3,Eight}RectStatement_of_law`**: the Rect statements follow
  as soon as every pair of regular marginals admits a coupling with the two law parts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Marg

open A2X A1Ref A1Canon A1Core

/-! ### Measurability from progressiveness -/

section Meas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The lifetime of a process adapted before it is measurable. -/
theorem measurable_lifetime {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (ha : AdaptedBefore 𝓕 ζ W) : Measurable ζ := by
  refine measurable_of_Ioi fun c => ?_
  induction c using ENNReal.recTopCoe with
  | top => simp
  | coe t =>
    have h := ha t univ MeasurableSet.univ
    simp only [mem_univ, and_true] at h
    exact 𝓕.le t _ h

/-- A strongly progressive real process has measurable evaluations. -/
theorem measurable_of_isStronglyProgressive {u : ℝ≥0 → Ω → ℝ} (h : IsStronglyProgressive 𝓕 u) (t : ℝ≥0) :
    Measurable (u t) :=
  (IsStronglyProgressive.stronglyAdapted h t).measurable.mono (𝓕.le t) le_rfl

/-- **A progressive live event is jointly measurable** in time and sample. -/
theorem measurableSet_live_of_isStronglyProgressive {live : ℝ≥0 → Ω → Prop}
    (h : IsStronglyProgressive 𝓕 fun t ω => {ω | live t ω}.indicator (fun _ => (1 : ℝ)) ω) :
    MeasurableSet {q : ℝ≥0 × Ω | live q.1 q.2} := by
  have hn : ∀ n : ℕ, MeasurableSet {q : ℝ≥0 × Ω | q.1 ≤ n ∧ live q.1 q.2} := fun n => by
    have hm := (measurable_prod_of_isStronglyProgressive h (n : ℝ≥0)).mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono (𝓕.le n))) le_rfl
    set g : ℝ≥0 × Ω → Iic (n : ℝ≥0) × Ω := fun q => (⟨min q.1 n, mem_Iic.2 (min_le_right _ _)⟩, q.2) with hg
    have hc : Measurable fun s : ℝ≥0 => (⟨min s n, mem_Iic.2 (min_le_right _ _)⟩ : Iic (n : ℝ≥0)) :=
      ((continuous_id.min continuous_const).subtype_mk _).measurable
    have hgm : Measurable g := (hc.comp measurable_fst).prodMk measurable_snd
    have e : {q : ℝ≥0 × Ω | q.1 ≤ n ∧ live q.1 q.2} = {q : ℝ≥0 × Ω | q.1 ≤ n} ∩
        g ⁻¹' ((fun p : Iic (n : ℝ≥0) × Ω => {ω | live p.1.val ω}.indicator (fun _ => (1 : ℝ)) p.2) ⁻¹' {1}) := by
      ext q
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, hg]
      refine and_congr_right fun hq => ?_
      rw [min_eq_left hq]
      by_cases hl : live q.1 q.2
      · simp only [hl, indicator_of_mem (show q.2 ∈ {ω | live q.1 ω} from hl)]
      · simp only [hl, false_iff, indicator_of_notMem (show q.2 ∉ {ω | live q.1 ω} from hl)]
        exact zero_ne_one
    rw [e]
    exact (measurableSet_le measurable_fst measurable_const).inter (hgm (hm (measurableSet_singleton 1)))
  have e : {q : ℝ≥0 × Ω | live q.1 q.2} = ⋃ n : ℕ, {q : ℝ≥0 × Ω | q.1 ≤ n ∧ live q.1 q.2} := by
    ext q
    simp only [mem_ofPred_eq, mem_iUnion]
    exact ⟨fun h => ⟨⌈q.1⌉₊, Nat.le_ceil _, h⟩, fun ⟨_, _, h⟩ => h⟩
  rw [e]
  exact MeasurableSet.iUnion hn

/-- **The end of the strip life is measurable** when the strip life is jointly measurable. -/
theorem measurable_lifeEnd {W V : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hS : MeasurableSet {q : ℝ≥0 × Ω | Strip.IsStripLife (W · q.2) (V · q.2) (ζ q.2) q.1}) :
    Measurable fun ω => lifeEnd (W · ω) (V · ω) (ζ ω) := by
  classical
  have hq : ∀ q : ℚ, MeasurableSet {ω | Strip.IsStripLife (W · ω) (V · ω) (ζ ω) (Real.toNNReal q)} := fun q =>
    hS.preimage (measurable_const.prodMk measurable_id)
  have e : (fun ω => lifeEnd (W · ω) (V · ω) (ζ ω)) = fun ω => ⨅ q : ℚ,
      if Strip.IsStripLife (W · ω) (V · ω) (ζ ω) (Real.toNNReal q) then ⊤ else ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) := by
    funext ω
    apply le_antisymm
    · refine le_iInf fun q => ?_
      split_ifs with h
      · exact le_top
      · exact iInf₂_le (Real.toNNReal q) h
    · refine le_iInf₂ fun t ht => le_of_forall_gt fun c hc => ?_
      obtain ⟨q, hq0, htq, hqc⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc
      have hnot : ¬ Strip.IsStripLife (W · ω) (V · ω) (ζ ω) (Real.toNNReal q) := fun h =>
        ht (h.mono (le_of_lt (by exact_mod_cast htq)))
      refine lt_of_le_of_lt (iInf_le _ q) ?_
      simp only [hnot, ↓reduceIte]
      exact hqc
  rw [e]
  exact Measurable.iInf fun q => Measurable.ite (hq q) measurable_const measurable_const

end Meas

/-! ### The law parts of the cores -/

section Law

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The law part of `A1Core.IsRectImageCore`** (its last conjunct, verbatim): at every stopping time of the usual
augmentation of the conditioning curve's filtration under its marginal, the density form (1.7), the frozen-hull fibre
law and the local image path. -/
def RectLawPart (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
    (𝓕k : Filtration ℝ≥0 mY) (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Y → ℝ) (ΘL : ℝ≥0 → Y → Fin nL → ℝ) (ΘR : ℝ≥0 → Y → Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
    ∃ (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))) (VL' : Fin nL → ℝ≥0 → X × Y → ℝ)
      (VR' : Fin nR → ℝ≥0 → X × Y → ℝ) (N : ℝ≥0 → X × Y → ℝ) (S : ℕ → X × Y → ℝ≥0)
      (𝓐 : ℕ → MeasurableSpace X) (𝓑 : ℕ → MeasurableSpace Y) (D : ℕ → X × Y → ℝ≥0∞),
      AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.snd) (comap_snd_le (stoppedSigma_le hτ)) 𝓖)
        (rLife live xj Wj ζj xk Wk τ) (rDrv live xj Wj ζj xk Wk τ) ∧
      (∀ i, AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.snd)
        (comap_snd_le (stoppedSigma_le hτ)) 𝓖) (rLife live xj Wj ζj xk Wk τ) (VL' i)) ∧
      (∀ i, AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.snd)
        (comap_snd_le (stoppedSigma_le hτ)) 𝓖) (rLife live xj Wj ζj xk Wk τ) (VR' i)) ∧
      (∀ i t, Measurable (VL' i t)) ∧ (∀ i t, Measurable (VR' i t)) ∧
      (∀ z, Continuous (N · z)) ∧ (∀ z, N 0 z = 0) ∧ (∀ t, Measurable[𝓖 t] (N t)) ∧
      (∀ m, IsStoppingTime 𝓖 fun z => (S m z : WithTop ℝ≥0)) ∧
      (∀ m, 𝓐 m ≤ mX) ∧ (∀ m, 𝓑 m ≤ mY) ∧ (∀ m, Measurable (D m)) ∧
      (∀ m (f : X × Y → ℝ≥0∞), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
        ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D m z ∂(P₁.prod P₂)) ∧
      (∀ m (a' : ℝ) (t : ℝ≥0), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (stopExp a' N (S m) t)) ∧
      (∀ m (s : ℝ≥0) (B : Set Y) (A : Set (X × Y)), MeasurableSet[hτ.measurableSpace] B →
        MeasurableSet[𝓖 s] A →
        MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S m z})) ∧
      (∀ m, ∀ᵐ y ∂P₂, ∀ (a' : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
        ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a' N (S m) t z)) (x, y) * D m (x, y) ∂P₁ =
          ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a' N (S m) s z)) (x, y) * D m (x, y) ∂P₁) ∧
      ∀ᵐ z ∂μ, live (τ z.2) z.2 →
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < rLife live xj Wj ζj xk Wk τ z → ∃ m, t ≤ S m z) ∧
        Sec2.IsSLEPathUpTo a (ΘL (τ z.2) z.2) (ΘR (τ z.2) z.2) ρL ρR (fun t => rDrv live xj Wj ζj xk Wk τ t z)
          (fun i t => VL' i t z) (fun i t => VR' i t z) (fun t => N t z) (rLife live xj Wj ζj xk Wk τ z)

/-- **The law part of `A1Core.IsRectImageCoreFst`** (its last conjunct, verbatim). -/
def RectLawPartFst (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
    (𝓕k : Filtration ℝ≥0 mX) (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (ΘL : ℝ≥0 → X → Fin nL → ℝ) (ΘR : ℝ≥0 → X → Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
    ∃ (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))) (VL' : Fin nL → ℝ≥0 → X × Y → ℝ)
      (VR' : Fin nR → ℝ≥0 → X × Y → ℝ) (N : ℝ≥0 → X × Y → ℝ) (S : ℕ → X × Y → ℝ≥0)
      (𝓐 : ℕ → MeasurableSpace X) (𝓑 : ℕ → MeasurableSpace Y) (D : ℕ → X × Y → ℝ≥0∞),
      AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.fst) (comap_fst_le (stoppedSigma_le hτ)) 𝓖)
        (rLifeFst live xj Wj ζj xk Wk τ) (rDrvFst live xj Wj ζj xk Wk τ) ∧
      (∀ i, AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.fst)
        (comap_fst_le (stoppedSigma_le hτ)) 𝓖) (rLifeFst live xj Wj ζj xk Wk τ) (VL' i)) ∧
      (∀ i, AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.fst)
        (comap_fst_le (stoppedSigma_le hτ)) 𝓖) (rLifeFst live xj Wj ζj xk Wk τ) (VR' i)) ∧
      (∀ i t, Measurable (VL' i t)) ∧ (∀ i t, Measurable (VR' i t)) ∧
      (∀ z, Continuous (N · z)) ∧ (∀ z, N 0 z = 0) ∧ (∀ t, Measurable[𝓖 t] (N t)) ∧
      (∀ m, IsStoppingTime 𝓖 fun z => (S m z : WithTop ℝ≥0)) ∧
      (∀ m, 𝓐 m ≤ mX) ∧ (∀ m, 𝓑 m ≤ mY) ∧ (∀ m, Measurable (D m)) ∧
      (∀ m (f : X × Y → ℝ≥0∞), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
        ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D m z ∂(P₁.prod P₂)) ∧
      (∀ m (a' : ℝ) (t : ℝ≥0), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (stopExp a' N (S m) t)) ∧
      (∀ m (s : ℝ≥0) (B : Set X) (A : Set (X × Y)), MeasurableSet[hτ.measurableSpace] B →
        MeasurableSet[𝓖 s] A →
        MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S m z})) ∧
      (∀ m, ∀ᵐ x ∂P₁, ∀ (a' : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
        ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a' N (S m) t z)) (x, y) * D m (x, y) ∂P₂ =
          ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a' N (S m) s z)) (x, y) * D m (x, y) ∂P₂) ∧
      ∀ᵐ z ∂μ, live (τ z.1) z.1 →
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < rLifeFst live xj Wj ζj xk Wk τ z → ∃ m, t ≤ S m z) ∧
        Sec2.IsSLEPathUpTo a (ΘL (τ z.1) z.1) (ΘR (τ z.1) z.1) ρL ρR (fun t => rDrvFst live xj Wj ζj xk Wk τ t z)
          (fun i t => VL' i t z) (fun i t => VR' i t z) (fun t => N t z) (rLifeFst live xj Wj ζj xk Wk τ z)

theorem isRectImageCore_iff (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
    (𝓕k : Filtration ℝ≥0 mY) (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Y → ℝ) (ΘL : ℝ≥0 → Y → Fin nL → ℝ) (ΘR : ℝ≥0 → Y → Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) :
    IsRectImageCore a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR ↔
      (IsStronglyProgressive (usualAugmentation 𝓕k P₂) fun t y => {y | live t y}.indicator (fun _ => (1 : ℝ)) y) ∧
      IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘL ∧ IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘR ∧
      (∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2) ∧
      Measurable (fun p : ℝ≥0 × (X × Y) => rLife live xj Wj ζj xk Wk (fun _ => p.1) p.2) ∧
      RectLawPart a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR :=
  Iff.rfl

theorem isRectImageCoreFst_iff (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
    (𝓕k : Filtration ℝ≥0 mX) (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (ΘL : ℝ≥0 → X → Fin nL → ℝ) (ΘR : ℝ≥0 → X → Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) :
    IsRectImageCoreFst a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR ↔
      (IsStronglyProgressive (usualAugmentation 𝓕k P₁) fun t x => {x | live t x}.indicator (fun _ => (1 : ℝ)) x) ∧
      IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘL ∧ IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘR ∧
      (∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2) ∧
      Measurable (fun p : ℝ≥0 × (X × Y) => rLifeFst live xj Wj ζj xk Wk (fun _ => p.1) p.2) ∧
      RectLawPartFst a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR :=
  Iff.rfl

end Law

/-! ### Vectors of progressive processes -/

section Vec

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem isStronglyProgressive_nil : IsStronglyProgressive 𝓕 fun (_ : ℝ≥0) (_ : Ω) => (![] : Fin 0 → ℝ) :=
  isStronglyProgressive_const _ _

theorem isStronglyProgressive_cons {n : ℕ} {u : ℝ≥0 → Ω → ℝ} {v : ℝ≥0 → Ω → Fin n → ℝ}
    (hu : IsStronglyProgressive 𝓕 u) (hv : IsStronglyProgressive 𝓕 v) :
    IsStronglyProgressive 𝓕 fun t ω => Matrix.vecCons (u t ω) (v t ω) := by
  refine isStronglyProgressive_vec fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Matrix.cons_val_zero] using hu
  · simp only [Matrix.cons_val_succ]
    exact isStronglyProgressive_of_measurable fun t => (measurable_pi_apply j).comp (hv t).measurable

end Vec

/-! ### The cores of regular marginals are their law parts -/

section Cores

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **Conditioning curve on `Y`, live event the strip life of its mark `i₀`**: for regular marginals and progressive
image words, (m1)–(m4) hold, so the core is its law part. -/
theorem isRectImageCore_strip_of_reg {ak aj a : ℝ} {nLk nRk nLj nRj nL nR : ℕ}
    {xLk : Fin nLk → ℝ} {xRk : Fin nRk → ℝ} {ρLk : Fin nLk → ℝ} {ρRk : Fin nRk → ℝ}
    {xLj : Fin nLj → ℝ} {xRj : Fin nRj → ℝ} {ρLj : Fin nLj → ℝ} {ρRj : Fin nRj → ℝ}
    {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓕k : Filtration ℝ≥0 mY} {𝓕j : Filtration ℝ≥0 mX}
    {Wk : ℝ≥0 → Y → ℝ} {VLk : Fin nLk → ℝ≥0 → Y → ℝ} {VRk : Fin nRk → ℝ≥0 → Y → ℝ} {Bk : ℝ≥0 → Y → ℝ}
    {ζk : Y → ℝ≥0∞} {Wj : ℝ≥0 → X → ℝ} {VLj : Fin nLj → ℝ≥0 → X → ℝ} {VRj : Fin nRj → ℝ≥0 → X → ℝ}
    {Bj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞}
    (hk : IsRegMarginal ak xLk xRk ρLk ρRk P₂ 𝓕k Wk VLk VRk Bk ζk)
    (hj : IsRegMarginal aj xLj xRj ρLj ρRj P₁ 𝓕j Wj VLj VRj Bj ζj) (i₀ : Fin nLk) (xj xk : ℝ)
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hΘL : IsStronglyProgressive 𝓕k ΘL) (hΘR : IsStronglyProgressive 𝓕k ΘR)
    (hlaw : RectLawPart a P₁ P₂ μ 𝓕k (fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) xj Wj ζj xk Wk
      ΘL ΘR ρL ρR) :
    IsRectImageCore a P₁ P₂ μ 𝓕k (fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) xj Wj ζj xk Wk
      ΘL ΘR ρL ρR := by
  have hcW : ∀ y, ContinuousOn (Wk · y) {s | (s : ℝ≥0∞) < ζk y} := fun y => (hk.path y).2.2.2.1
  have hcV : ∀ y, ContinuousOn (VLk i₀ · y) {s | (s : ℝ≥0∞) < ζk y} := fun y => (hk.path y).2.2.2.2.1 i₀
  have hm1 := isStronglyProgressive_indicator_isStripLife hk.evol.2.1 hk.progW (hk.progVL i₀) hcW hcV
  have hlive := measurableSet_live_of_isStronglyProgressive hm1
  obtain ⟨hm3, hm4⟩ := measurable_rDrv_rLife
    (live := fun t ω => Strip.IsStripLife (Wk · ω) (VLk i₀ · ω) (ζk ω) t) hlive (fun _ _ h => h.1)
    (fun x => (hj.path x).2.2.2.1)
    (fun x => (hj.path x).1) hcW (fun y => (hk.path y).1) (measurable_of_isStronglyProgressive hj.progW)
    (measurable_of_isStronglyProgressive hk.progW) (measurable_lifetime hj.evol.2.1)
    (measurable_lifetime hk.evol.2.1) xj xk
  exact (isRectImageCore_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2
    ⟨isStronglyProgressive_usualAugmentation hm1 P₂, isStronglyProgressive_usualAugmentation hΘL P₂,
      isStronglyProgressive_usualAugmentation hΘR P₂, hm3, hm4, hlaw⟩

/-- **Conditioning curve on `X`, live event `t < ζ`, image lifetime the end of the strip life of the image curve's
mark `i₀`**: for regular marginals and progressive image words, (m1)–(m4) hold. -/
theorem isRectImageCoreFst_lt_of_reg {ak aj a : ℝ} {nLk nRk nLj nRj nL nR : ℕ}
    {xLk : Fin nLk → ℝ} {xRk : Fin nRk → ℝ} {ρLk : Fin nLk → ℝ} {ρRk : Fin nRk → ℝ}
    {xLj : Fin nLj → ℝ} {xRj : Fin nRj → ℝ} {ρLj : Fin nLj → ℝ} {ρRj : Fin nRj → ℝ}
    {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓕k : Filtration ℝ≥0 mX} {𝓕j : Filtration ℝ≥0 mY}
    {Wk : ℝ≥0 → X → ℝ} {VLk : Fin nLk → ℝ≥0 → X → ℝ} {VRk : Fin nRk → ℝ≥0 → X → ℝ} {Bk : ℝ≥0 → X → ℝ}
    {ζk : X → ℝ≥0∞} {Wj : ℝ≥0 → Y → ℝ} {VLj : Fin nLj → ℝ≥0 → Y → ℝ} {VRj : Fin nRj → ℝ≥0 → Y → ℝ}
    {Bj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞}
    (hk : IsRegMarginal ak xLk xRk ρLk ρRk P₁ 𝓕k Wk VLk VRk Bk ζk)
    (hj : IsRegMarginal aj xLj xRj ρLj ρRj P₂ 𝓕j Wj VLj VRj Bj ζj) (i₀ : Fin nLj) (xj xk : ℝ)
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hΘL : IsStronglyProgressive 𝓕k ΘL) (hΘR : IsStronglyProgressive 𝓕k ΘR)
    (hlaw : RectLawPartFst a P₁ P₂ μ 𝓕k (fun t ω => (t : ℝ≥0∞) < ζk ω) xj Wj
      (fun ω => lifeEnd (Wj · ω) (VLj i₀ · ω) (ζj ω)) xk Wk ΘL ΘR ρL ρR) :
    IsRectImageCoreFst a P₁ P₂ μ 𝓕k (fun t ω => (t : ℝ≥0∞) < ζk ω) xj Wj
      (fun ω => lifeEnd (Wj · ω) (VLj i₀ · ω) (ζj ω)) xk Wk ΘL ΘR ρL ρR := by
  have hm1 := isStronglyProgressive_indicator_lt hk.evol.2.1
  have hlive := measurableSet_live_of_isStronglyProgressive hm1
  have hcW : ∀ y, ContinuousOn (Wj · y) {s | (s : ℝ≥0∞) < ζj y} := fun y => (hj.path y).2.2.2.1
  have hcV : ∀ y, ContinuousOn (VLj i₀ · y) {s | (s : ℝ≥0∞) < ζj y} := fun y => (hj.path y).2.2.2.2.1 i₀
  have hS := measurableSet_live_of_isStronglyProgressive
    (isStronglyProgressive_indicator_isStripLife hj.evol.2.1 hj.progW (hj.progVL i₀) hcW hcV)
  obtain ⟨hm3, hm4⟩ := measurable_rDrvFst_rLifeFst
    (live := fun t ω => (t : ℝ≥0∞) < ζk ω) hlive (fun _ _ h => h)
    (fun y => (hcW y).mono fun t ht => lt_of_lt_of_le ht (lifeEnd_le _ _ _)) (fun y => (hj.path y).1)
    (fun x => (hk.path x).2.2.2.1) (fun x => (hk.path x).1) (measurable_of_isStronglyProgressive hj.progW)
    (measurable_of_isStronglyProgressive hk.progW) (measurable_lifeEnd hS) (measurable_lifetime hk.evol.2.1) xj xk
  exact (isRectImageCoreFst_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2
    ⟨isStronglyProgressive_usualAugmentation hm1 P₁, isStronglyProgressive_usualAugmentation hΘL P₁,
      isStronglyProgressive_usualAugmentation hΘR P₁, hm3, hm4, hlaw⟩

end Cores

/-! ### The two configurations of A.1 -/

section Config

theorem antitone_two {a b : ℝ} (h : b ≤ a) : Antitone ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem monotone_two {a b : ℝ} (h : a ≤ b) : Monotone ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem monotone_three {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : Monotone ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> (simp_all; try linarith)

theorem isOrderedForceWord_largeG3 {x y : ℝ} (hyx : y < x) (hx : x < 0) :
    IsOrderedForceWord ![x, y] (![] : Fin 0 → ℝ) :=
  ⟨antitone_two hyx.le, fun i => by fin_cases i <;> simp <;> linarith, fun i => Fin.elim0 i,
    fun i => Fin.elim0 i⟩

theorem isOrderedForceWord_smallG3 {x y : ℝ} (hyx : y < x) (hx : x < 0) :
    IsOrderedForceWord ![(0 : ℝ)] ![0, x - y, -y] :=
  ⟨fun i j _ => by fin_cases i; fin_cases j; exact le_rfl, fun i => by fin_cases i; simp,
    monotone_three (by linarith) (by linarith), fun i => by fin_cases i <;> simp <;> linarith⟩

theorem isOrderedForceWord_largeEight {x : ℝ} (hx : x < 0) : IsOrderedForceWord ![x] (![] : Fin 0 → ℝ) :=
  ⟨fun i j _ => by fin_cases i; fin_cases j; exact le_rfl, fun i => by fin_cases i; simp; linarith,
    fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem isOrderedForceWord_smallEight {x : ℝ} (hx : x < 0) : IsOrderedForceWord ![(0 : ℝ)] ![0, -x] :=
  ⟨fun i j _ => by fin_cases i; fin_cases j; exact le_rfl, fun i => by fin_cases i; simp,
    monotone_two (by linarith), fun i => by fin_cases i <;> (simp; try linarith)⟩

/-- **A.1 (G3), marginal form**: the Rect statement with **regular** marginals (`IsRegMarginal`, which contains the
integrated evolutions) and only the **law parts** of the two cores — the clauses (m1)–(m4) are proved here. -/
def A1DualCouplingG3MargStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (μ : Measure (X × Y)) (_ : IsProbabilityMeasure μ)
      (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      RectLawPart (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
        W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
        (smallG3RhoR κ) ∧
      RectLawPartFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
        (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
        (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight), marginal form.** -/
def A1DualCouplingEightMargStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (μ : Measure (X × Y)) (_ : IsProbabilityMeasure μ)
      (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      RectLawPart (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
        W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
      RectLawPartFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
        (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **The marginal form gives the Rect statement (G3)**: (m1)–(m4) for regular marginals. -/
theorem a1DualCouplingG3RectStatement_of_marg {κ : ℝ} (h : A1DualCouplingG3MargStatement κ) :
    A1DualCouplingG3RectStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, hl₁, hl₂⟩ := h hκ4 hκ8 y x hyx hx
  refine ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂.evol, h₁.evol, ?_, ?_⟩
  · exact isRectImageCore_strip_of_reg h₂ h₁ 0 y 0 (isStronglyProgressive_const _ _)
      (isStronglyProgressive_cons (isStronglyProgressive_const _ _)
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₂.progVL 0) (h₂.progVL 1))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₂.progW (h₂.progVL 1))
            isStronglyProgressive_nil))) hl₁
  · exact isRectImageCoreFst_lt_of_reg h₁ h₂ 0 0 y
      (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 1) (h₁.progVR 2))
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 0) (h₁.progVR 2))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₁.progW (h₁.progVR 2))
            (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVL 0) (h₁.progVR 2))
              isStronglyProgressive_nil))))
      (isStronglyProgressive_const _ _) hl₂

/-- **The marginal form gives the Rect statement (Eight).** -/
theorem a1DualCouplingEightRectStatement_of_marg {κ : ℝ} (h : A1DualCouplingEightMargStatement κ) :
    A1DualCouplingEightRectStatement κ := by
  intro hκ8 x hx
  obtain ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂, h₁, hl₁, hl₂⟩ := h hκ8 x hx
  refine ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁,
    hm₁, hm₂, h₂.evol, h₁.evol, ?_, ?_⟩
  · exact isRectImageCore_strip_of_reg h₂ h₁ 0 x 0 (isStronglyProgressive_const _ _)
      (isStronglyProgressive_cons (isStronglyProgressive_const _ _)
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₂.progW (h₂.progVL 0))
          isStronglyProgressive_nil)) hl₁
  · exact isRectImageCoreFst_lt_of_reg h₁ h₂ 0 0 x
      (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVR 0) (h₁.progVR 1))
        (isStronglyProgressive_cons (isStronglyProgressive_sub_real h₁.progW (h₁.progVR 1))
          (isStronglyProgressive_cons (isStronglyProgressive_sub_real (h₁.progVL 0) (h₁.progVR 1))
            isStronglyProgressive_nil)))
      (isStronglyProgressive_const _ _) hl₂

end Config

/-! ### The marginals exist; the law form -/

section Exist

theorem kh_pos {κ : ℝ} (hκ : 0 < κ) : 0 < kh κ := div_pos (by norm_num) hκ

/-- **The two complete marginal laws of A.1 (G3) exist as regular marginals on standard Borel spaces**: the large
curve (`SLE_κ(κ − 4, −4)` from `0`, marks `x, y`) and the small curve (`SLE_κ̂` from `y`, its word). -/
theorem exists_regMarginals_G3 {κ : ℝ} (hκ4 : 4 < κ) {y x : ℝ} (hyx : y < x) (hx : x < 0) :
    (∃ (Y : Type) (mY : MeasurableSpace Y) (_ : StandardBorelSpace Y) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₂ : Filtration ℝ≥0 mY) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
      (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) ∧
    (∃ (X : Type) (mX : MeasurableSpace X) (_ : StandardBorelSpace X) (P₁ : Measure X)
      (_ : IsProbabilityMeasure P₁) (𝓕₁ : Filtration ℝ≥0 mX) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ)
      (VR₁ : Fin 3 → ℝ≥0 → X → ℝ) (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁) :=
  ⟨exists_isRegMarginal (by linarith) _ _ (isOrderedForceWord_largeG3 hyx hx),
    exists_isRegMarginal (kh_pos (by linarith)) _ _ (isOrderedForceWord_smallG3 hyx hx)⟩

/-- **The two complete marginal laws of A.1 (Eight) exist as regular marginals on standard Borel spaces.** -/
theorem exists_regMarginals_Eight {κ : ℝ} (hκ8 : 8 ≤ κ) {x : ℝ} (hx : x < 0) :
    (∃ (Y : Type) (mY : MeasurableSpace Y) (_ : StandardBorelSpace Y) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₂ : Filtration ℝ≥0 mY) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ)
      (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) ∧
    (∃ (X : Type) (mX : MeasurableSpace X) (_ : StandardBorelSpace X) (P₁ : Measure X)
      (_ : IsProbabilityMeasure P₁) (𝓕₁ : Filtration ℝ≥0 mX) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ)
      (VR₁ : Fin 2 → ℝ≥0 → X → ℝ) (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁) :=
  ⟨exists_isRegMarginal (by linarith) _ _ (isOrderedForceWord_largeEight hx),
    exists_isRegMarginal (kh_pos (by linarith)) _ _ (isOrderedForceWord_smallEight hx)⟩

/-- **A.1 (G3), law form**: every pair of regular marginals on standard Borel spaces admits a coupling with the two
law parts. (With `exists_regMarginals_G3` this gives the marginal form, hence the Rect statement.) -/
def A1DualCouplingG3LawStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      ∃ (μ : Measure (X × Y)) (_ : IsProbabilityMeasure μ), μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧
        RectLawPart (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
          (smallG3RhoR κ) ∧
        RectLawPartFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
          (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
          (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight), law form.** -/
def A1DualCouplingEightLawStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      ∃ (μ : Measure (X × Y)) (_ : IsProbabilityMeasure μ), μ.map Prod.fst = P₁ ∧ μ.map Prod.snd = P₂ ∧
        RectLawPart (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
          W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
        RectLawPartFst κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
          (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
          (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

theorem a1DualCouplingG3MargStatement_of_law {κ : ℝ} (h : A1DualCouplingG3LawStatement κ) :
    A1DualCouplingG3MargStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨⟨Y, mY, hY, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂⟩, ⟨X, mX, hX, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁⟩⟩ :=
    exists_regMarginals_G3 hκ4 hyx hx
  obtain ⟨μ, hμ, hm₁, hm₂, hl₁, hl₂⟩ := h hκ4 hκ8 y x hyx hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
    W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hm₁,
    hm₂, h₂, h₁, hl₁, hl₂⟩

theorem a1DualCouplingEightMargStatement_of_law {κ : ℝ} (h : A1DualCouplingEightLawStatement κ) :
    A1DualCouplingEightMargStatement κ := by
  intro hκ8 x hx
  obtain ⟨⟨Y, mY, hY, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, h₂⟩, ⟨X, mX, hX, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, h₁⟩⟩ :=
    exists_regMarginals_Eight hκ8 hx
  obtain ⟨μ, hμ, hm₁, hm₂, hl₁, hl₂⟩ := h hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
    W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁
  exact ⟨X, Y, mX, mY, hX, hY, P₁, hP₁, P₂, hP₂, μ, hμ, 𝓕₁, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hm₁,
    hm₂, h₂, h₁, hl₁, hl₂⟩

/-- **The law form gives the Rect statement (G3).** -/
theorem a1DualCouplingG3RectStatement_of_law {κ : ℝ} (h : A1DualCouplingG3LawStatement κ) :
    A1DualCouplingG3RectStatement κ :=
  a1DualCouplingG3RectStatement_of_marg (a1DualCouplingG3MargStatement_of_law h)

/-- **The law form gives the Rect statement (Eight).** -/
theorem a1DualCouplingEightRectStatement_of_law {κ : ℝ} (h : A1DualCouplingEightLawStatement κ) :
    A1DualCouplingEightRectStatement κ :=
  a1DualCouplingEightRectStatement_of_marg (a1DualCouplingEightMargStatement_of_law h)

/-- R72's Canon statement (G3) from the marginal form. -/
theorem a1DualCouplingG3CanonStatement_of_marg {κ : ℝ} (h : A1DualCouplingG3MargStatement κ) :
    A1Ref.A1DualCouplingG3CanonStatement κ :=
  a1DualCouplingG3CanonStatement_of_rect (a1DualCouplingG3RectStatement_of_marg h)

/-- R72's Canon statement (Eight) from the marginal form. -/
theorem a1DualCouplingEightCanonStatement_of_marg {κ : ℝ} (h : A1DualCouplingEightMargStatement κ) :
    A1Ref.A1DualCouplingEightCanonStatement κ :=
  a1DualCouplingEightCanonStatement_of_rect (a1DualCouplingEightRectStatement_of_marg h)

end Exist

end InteractingSLE.ZhanGT4.A1Marg
