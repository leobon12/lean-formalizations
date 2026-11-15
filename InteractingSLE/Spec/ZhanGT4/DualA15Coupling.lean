/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA15Block
import InteractingSLE.Spec.ZhanGT4.DualA15Lim

/-!
# A.1.5: one coupling of the two curves with every stopped rectangle law

Packet PROVE-ZHAN-GT4-A18. Source: Astra, *Follow-up proofs*, §A.1.5 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L409–L425, R38): "Enumerate a countable … family of separated polygonal enclosure pairs. For its first `n` pairs use
(D11) to obtain a coupling … Enlarge each path coordinate by the stopped path … for every enclosure in the enumeration.
… hence the family of couplings is tight. A weak limit … For each fixed enclosure pair, all sufficiently late couplings
have exactly the same joint law of its two recorded stopped histories, namely the density from (D6). This equality
passes to the limit by continuous cylinder tests. … Thus every stopped rectangle has the required law."

Set-up: a countable family `k ↦ (H₁ k, H₂ k)` of protected enclosure pairs with stopping times `S₁ k`, `S₂ k` such that
the first `n + 1` pairs satisfy A16's `DualHyp` (bound `Tm n`). The recorded coordinate of rectangle `k` for curve `j`
is the stopped Brownian path at the enumerated rational times `recTime j` together with the stopping time (`recPath`,
values in the Polish space `RecSpace = (ℕ → ℝ) × ℝ`).

* `DualHyp.restrict`: a subfamily of a protected family is protected;
* `measurable_recPath`: the recorded coordinate is measurable for the stopped σ-algebra;
* `DualHyp.map_recPath_eq`: the joint law of the two recorded coordinates of a rectangle under the stopped dual
  coupling of any family containing it is the law under the coupling of that rectangle alone (A18's
  `dualCoupling_congr_of_rect`);
* **`exists_dualCoupling_lim`** (A.1.5): there is one probability measure on
  `RecPair = (ℕ → RecSpace) × (ℕ → RecSpace)` under
  which, for every `k`, the pair of recorded coordinates of rectangle `k` has exactly the law of the stopped dual
  coupling of rectangle `k` (density `rectDens`, A17's `dualCoupling_rect`).
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-! ### Restriction of a protected family -/

section Restrict

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {ι ι' : Type*} {n : ℕ} {κ : ℝ}
  {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂}
  {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {p : Fin n → ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {Tm : ℝ}
  {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}

/-- **A subfamily of a protected family of rectangles is protected.** -/
theorem DualHyp.restrict (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂) (f : ι' → ι) :
    DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ (H₁ ∘ f) (H₂ ∘ f) (δ ∘ f) (q ∘ f) (d ∘ f) p Tm (S₁ ∘ f) (S₂ ∘ f) where
  κpos := h.κpos
  bm₁ := h.bm₁
  cont₁ := h.cont₁
  zero₁ := h.zero₁
  bm₂ := h.bm₂
  cont₂ := h.cont₂
  zero₂ := h.zero₂
  hull₁ i := h.hull₁ (f i)
  hull₂ i := h.hull₂ (f i)
  δpos i := h.δpos (f i)
  sep i := h.sep (f i)
  dpos i := h.dpos (f i)
  qpos i := h.qpos (f i)
  qH i := h.qH (f i)
  pH i := h.pH (f i)
  pinj := h.pinj
  x₂H i := h.x₂H (f i)
  qx i := h.qx (f i)
  Tmpos := h.Tmpos
  stop₁ i := h.stop₁ (f i)
  pos₁ i := h.pos₁ (f i)
  le₁ i := h.le₁ (f i)
  K₁ i := h.K₁ (f i)
  stop₂ i := h.stop₂ (f i)
  pos₂ i := h.pos₂ (f i)
  le₂ i := h.le₂ (f i)
  K₂ i := h.K₂ (f i)

end Restrict

/-! ### The recorded coordinates -/

/-- The recorded coordinate space of one stopped path: its values at the enumerated rational times (`recTime`) and
the stopping time. -/
abbrev RecSpace : Type := (ℕ → ℝ) × ℝ

/-- The recorded coordinates of both curves at every rectangle. -/
abbrev RecPair : Type := (ℕ → RecSpace) × (ℕ → RecSpace)

/-- The pair of recorded coordinate sequences is Polish (instance search does not find this product by itself). -/
instance polishSpace_recPair : PolishSpace RecPair :=
  @instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace _ _ inferInstance inferInstance

/-- The pair of recorded coordinate sequences has outer approximations of closed sets (it is metrizable). -/
instance hasOuterApproxClosed_recPair : HasOuterApproxClosed RecPair := by
  have : TopologicalSpace.PseudoMetrizableSpace RecPair := by
    let _ := TopologicalSpace.upgradeIsCompletelyMetrizable RecPair
    infer_instance
  infer_instance

/-- An enumeration of the nonnegative rational times: `j ↦ a / (b + 1)` with `(a, b) = Nat.unpair j`. -/
def recTime (j : ℕ) : ℝ≥0 := ((Nat.unpair j).1 : ℝ≥0) / ((Nat.unpair j).2 + 1)

section Rec

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The recorded coordinate of a path stopped at `S`**: `(j ↦ B (recTime j ∧ S), S)`. -/
def recPath (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ω : Ω) : RecSpace :=
  (fun j => B (min (recTime j) (S ω)) ω, (S ω : ℝ))

/-- **The recorded coordinate is measurable for the stopped σ-algebra.** -/
theorem measurable_recPath {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hBa : Adapted 𝓕 B)
    (hBc : ∀ ω, Continuous (B · ω)) {S : Ω → ℝ≥0} (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    Measurable[hS.measurableSpace] (recPath B S) := by
  let _ : MeasurableSpace Ω := hS.measurableSpace
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_) ?_
  · have hX : IsStronglyProgressive 𝓕 (fun t ω => B (min (recTime q) t) ω) :=
      StronglyAdapted.isStronglyProgressive_of_continuous
        (fun t => ((hBa (min (recTime q) t)).mono (𝓕.mono (min_le_right _ _)) le_rfl).stronglyMeasurable)
        (fun ω => (hBc ω).comp (continuous_const.min continuous_id))
    exact measurable_stoppedValue hX hS
  · have h1 : Measurable fun ω => ((S ω : WithTop ℝ≥0)).untopA := WithTop.measurable_untopA.comp hS.measurable
    exact measurable_subtype_coe.comp h1

end Rec

/-! ### The law of the recorded coordinates of one rectangle -/

section Law

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {ι ι' : Type*} [Fintype ι]
  [Fintype ι'] {n : ℕ} {κ : ℝ} {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ}
  {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂} {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {p : Fin n → ℝ}
  {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {Tm : ℝ} {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}
  {H₁' H₂' : ι' → Set ℂ} {δ' q' d' : ι' → ℝ} {Tm' : ℝ} {S₁' : ι' → Ω₁ → ℝ≥0} {S₂' : ι' → Ω₂ → ℝ≥0}

/-- **The joint law of the recorded coordinates of a common rectangle is the same in both families.** -/
theorem DualHyp.map_recPath_eq [Nonempty ι] [Nonempty ι']
    (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
    (h' : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁' H₂' δ' q' d' p Tm' S₁' S₂') (rr : Fin n → ℝ) {i : ι} {i' : ι'}
    (h₁ : S₁' i' = S₁ i) (h₂ : S₂' i' = S₂ i) :
    (dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁' S₂' Tm').map (fun ω => (recPath B₁ (S₁ i) ω.1, recPath B₂ (S₂ i) ω.2)) =
      (dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm).map
        (fun ω => (recPath B₁ (S₁ i) ω.1, recPath B₂ (S₂ i) ω.2)) := by
  have hm₁ := measurable_recPath h.bm₁.2.1 h.cont₁ (h.stop₁ i)
  have hm₂ := measurable_recPath h.bm₂.2.1 h.cont₂ (h.stop₂ i)
  have hR : Measurable[(h.stop₁ i).measurableSpace.prod (h.stop₂ i).measurableSpace]
      (fun ω : Ω₁ × Ω₂ => (recPath B₁ (S₁ i) ω.1, recPath B₂ (S₂ i) ω.2)) :=
    (hm₁.comp (@measurable_fst _ _ (h.stop₁ i).measurableSpace (h.stop₂ i).measurableSpace)).prodMk
      (hm₂.comp (@measurable_snd _ _ (h.stop₁ i).measurableSpace (h.stop₂ i).measurableSpace))
  have hle : (h.stop₁ i).measurableSpace.prod (h.stop₂ i).measurableSpace ≤ mΩ₁.prod mΩ₂ :=
    sup_le_sup (MeasurableSpace.comap_mono ((h.stop₁ i).measurableSpace_le))
      (MeasurableSpace.comap_mono ((h.stop₂ i).measurableSpace_le))
  have hR' : Measurable (fun ω : Ω₁ × Ω₂ => (recPath B₁ (S₁ i) ω.1, recPath B₂ (S₂ i) ω.2)) := hR.mono hle le_rfl
  ext C hC
  rw [Measure.map_apply hR' hC, Measure.map_apply hR' hC]
  exact h.dualCoupling_congr_of_rect h' rr h₁ h₂ (hR hC)

end Law

/-! ### A.1.5 -/

section Lim

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {n : ℕ} {κ : ℝ}
  {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂}
  {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {p : Fin n → ℝ} {H₁ H₂ : ℕ → Set ℂ} {δ q d : ℕ → ℝ} {Tm : ℕ → ℝ}
  {S₁ : ℕ → Ω₁ → ℝ≥0} {S₂ : ℕ → Ω₂ → ℝ≥0}

/-- The stopped dual coupling of the first `m + 1` rectangles of a countable family. -/
def dualCouplingFirst (κ : ℝ) (rr p : Fin n → ℝ) (P₁ : Measure Ω₁) (B₁ : ℝ≥0 → Ω₁ → ℝ) (P₂ : Measure Ω₂)
    (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ℕ → Ω₁ → ℝ≥0) (S₂ : ℕ → Ω₂ → ℝ≥0) (Tm : ℕ → ℝ) (m : ℕ) :
    Measure (Ω₁ × Ω₂) :=
  dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ (fun k : Fin (m + 1) => S₁ k) (fun k : Fin (m + 1) => S₂ k) (Tm m)

/-- The stopped dual coupling of the single rectangle `k` (bound `Tm k`). -/
def dualCouplingOne (κ : ℝ) (rr p : Fin n → ℝ) (P₁ : Measure Ω₁) (B₁ : ℝ≥0 → Ω₁ → ℝ) (P₂ : Measure Ω₂)
    (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ℕ → Ω₁ → ℝ≥0) (S₂ : ℕ → Ω₂ → ℝ≥0) (Tm : ℕ → ℝ) (k : ℕ) :
    Measure (Ω₁ × Ω₂) :=
  dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ (fun _ : Unit => S₁ k) (fun _ : Unit => S₂ k) (Tm k)

/-- The recorded coordinates of all rectangles of one curve. -/
def recAll {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (S : ℕ → Ω → ℝ≥0) (ω : Ω) : ℕ → RecSpace := fun k => recPath B (S k) ω

/-- The first `k + 1` recorded coordinates of a curve (the others replaced by `0`). -/
def truncRec (k : ℕ) (x : ℕ → RecSpace) : ℕ → RecSpace := fun j => if j ≤ k then x j else 0

theorem continuous_truncRec (k : ℕ) : Continuous (truncRec k) := by
  refine continuous_pi fun j => ?_
  by_cases hj : j ≤ k
  · simp only [truncRec, hj, ite_true]
    exact continuous_apply j
  · simp only [truncRec, hj, ite_false]
    exact continuous_const

/-- The block of the first `k + 1` recorded coordinates is measurable at the last exit of the first `k + 1`
rectangles. -/
theorem measurable_truncRec_recAll {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hBa : Adapted 𝓕 B) (hBc : ∀ ω, Continuous (B · ω)) {S : ℕ → Ω → ℝ≥0} (k : ℕ)
    (hS : ∀ i : Fin (k + 1), IsStoppingTime 𝓕 fun ω => (S i ω : WithTop ℝ≥0)) :
    Measurable[(isStoppingTime_lastExit hS).measurableSpace] fun ω => truncRec k (recAll B S ω) := by
  refine @measurable_pi_iff _ _ _ (isStoppingTime_lastExit hS).measurableSpace _ _ |>.2 fun j => ?_
  by_cases hj : j ≤ k
  · simp only [truncRec, hj, ite_true, recAll]
    have hle : ∀ ω, ((S (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1)) ω : ℝ≥0) : WithTop ℝ≥0) ≤
        (lastExit (fun i : Fin (k + 1) => S i) ω : WithTop ℝ≥0) := fun ω =>
      WithTop.coe_le_coe.2 (le_lastExit (fun i : Fin (k + 1) => S i) ω ⟨j, Nat.lt_succ_of_le hj⟩)
    exact (measurable_recPath hBa hBc (hS ⟨j, Nat.lt_succ_of_le hj⟩)).mono
      ((hS ⟨j, Nat.lt_succ_of_le hj⟩).measurableSpace_mono (isStoppingTime_lastExit hS) hle) le_rfl
  · simp only [truncRec, hj, ite_false]
    exact measurable_const

/-- **A.1.5 for a countable family of protected rectangles.** If the first `m + 1` rectangles of the family form a
protected family for every `m` (A16's `DualHyp`, bound `Tm m`), there is one probability measure on
`RecPair` (the recorded coordinates of the two curves at every rectangle) such that

* for every `k`, the recorded coordinates of rectangle `k` (the two stopped paths at the enumerated rational times and
  the two stopping times) have exactly their law under the stopped dual coupling of rectangle `k` alone (density
  `rectDens`, A17's `dualCoupling_rect`; equivalently of any finite family containing it, `DualHyp.map_recPath_eq`);
* for every `k`, the first `k + 1` recorded coordinates of curve `1` (resp. curve `2`) have their law under the stopped
  dual coupling of the first `k + 1` rectangles, i.e. under the curve marginal `m₁ · P₁` (resp. `m₂ · P₂`, A16's
  `map_fst_dualCoupling`), the force-point law up to the last exit (A17's `exists_forceLaw₁/₂`). In particular the
  recorded coordinates of each curve come from one path. -/
theorem exists_dualCoupling_lim
    (hfam : ∀ m, DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ (fun k : Fin (m + 1) => H₁ k) (fun k : Fin (m + 1) => H₂ k)
      (fun k : Fin (m + 1) => δ k) (fun k : Fin (m + 1) => q k) (fun k : Fin (m + 1) => d k) p (Tm m)
      (fun k : Fin (m + 1) => S₁ k) (fun k : Fin (m + 1) => S₂ k)) (rr : Fin n → ℝ) :
    ∃ μ : Measure RecPair, IsProbabilityMeasure μ ∧
      (∀ k, μ.map (fun z => (z.1 k, z.2 k)) =
        (dualCouplingOne κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map
          (fun ω => (recPath B₁ (S₁ k) ω.1, recPath B₂ (S₂ k) ω.2))) ∧
      (∀ k, μ.map (fun z => truncRec k z.1) =
        (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map (fun ω => truncRec k (recAll B₁ S₁ ω.1))) ∧
      ∀ k, μ.map (fun z => truncRec k z.2) =
        (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map (fun ω => truncRec k (recAll B₂ S₂ ω.2)) := by
  -- the single-rectangle families
  have hone : ∀ k, DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ (fun _ : Unit => H₁ k) (fun _ : Unit => H₂ k)
      (fun _ : Unit => δ k) (fun _ : Unit => q k) (fun _ : Unit => d k) p (Tm k) (fun _ : Unit => S₁ k)
      (fun _ : Unit => S₂ k) := fun k =>
    (hfam k).restrict (fun _ : Unit => (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)))
  have hm₁ : Measurable (recAll B₁ S₁) := measurable_pi_iff.2 fun k =>
    (measurable_recPath (hone k).bm₁.2.1 (hone k).cont₁ ((hone k).stop₁ ())).mono
      ((hone k).stop₁ ()).measurableSpace_le le_rfl
  have hm₂ : Measurable (recAll B₂ S₂) := measurable_pi_iff.2 fun k =>
    (measurable_recPath (hone k).bm₂.2.1 (hone k).cont₂ ((hone k).stop₂ ())).mono
      ((hone k).stop₂ ()).measurableSpace_le le_rfl
  have hR : Measurable fun ω : Ω₁ × Ω₂ => (recAll B₁ S₁ ω.1, recAll B₂ S₂ ω.2) :=
    (hm₁.comp measurable_fst).prodMk (hm₂.comp measurable_snd)
  have hPm : ∀ m, IsProbabilityMeasure (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm m) := fun m =>
    (hfam m).isProbabilityMeasure_dualCoupling rr
  -- the pushed couplings
  let μP : ℕ → ProbabilityMeasure RecPair := fun m =>
    ⟨(dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm m).map fun ω => (recAll B₁ S₁ ω.1, recAll B₂ S₂ ω.2),
      inferInstance⟩
  -- the pair tests and their eventual laws
  let f : ∀ k : ℕ, RecPair → RecSpace × RecSpace := fun k z => (z.1 k, z.2 k)
  have hf : ∀ k, Continuous (f k) := fun k =>
    ((continuous_apply k).comp continuous_fst).prodMk ((continuous_apply k).comp continuous_snd)
  set lam : ∀ k : ℕ, Measure (RecSpace × RecSpace) := fun k =>
    (dualCouplingOne κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map
      (fun ω => (recPath B₁ (S₁ k) ω.1, recPath B₂ (S₂ k) ω.2)) with hlam
  have hev : ∀ k, ∀ᶠ m in atTop, (μP m : Measure RecPair).map (f k) = lam k := by
    intro k
    refine eventually_atTop.2 ⟨k, fun m hkm => ?_⟩
    show ((dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm m).map _).map (f k) = _
    rw [Measure.map_map (hf k).measurable hR]
    exact (hone k).map_recPath_eq (hfam m) rr (i := ()) (i' := (⟨k, Nat.lt_succ_of_le hkm⟩ : Fin (m + 1))) rfl rfl
  -- the block tests and their eventual laws
  have hblock₁ : ∀ k, ∀ᶠ m in atTop,
      (μP m : Measure RecPair).map (fun z => truncRec k z.1) =
        (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map (fun ω => truncRec k (recAll B₁ S₁ ω.1)) := by
    intro k
    refine eventually_atTop.2 ⟨k, fun m hkm => ?_⟩
    have hT := (continuous_truncRec k).measurable
    have hb := measurable_truncRec_recAll (hfam k).bm₁.2.1 (hfam k).cont₁ k (hfam k).stop₁
    have hb' : Measurable fun ω : Ω₁ × Ω₂ => truncRec k (recAll B₁ S₁ ω.1) :=
      (hb.mono (isStoppingTime_lastExit (hfam k).stop₁).measurableSpace_le le_rfl).comp measurable_fst
    show ((dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm m).map _).map _ = _
    rw [Measure.map_map (show Measurable fun z : RecPair => truncRec k z.1 from hT.comp measurable_fst) hR]
    show Measure.map (fun ω : Ω₁ × Ω₂ => truncRec k (recAll B₁ S₁ ω.1)) _ = _
    ext C hC
    rw [Measure.map_apply hb' hC, Measure.map_apply hb' hC]
    have e : (fun ω : Ω₁ × Ω₂ => truncRec k (recAll B₁ S₁ ω.1)) ⁻¹' C =
        ((fun ω => truncRec k (recAll B₁ S₁ ω)) ⁻¹' C) ×ˢ (univ : Set Ω₂) := by
      ext ω; simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    rw [e]
    exact (hfam k).dualCoupling_fst_congr (hfam m) rr (Fin.castLE (by omega)) (fun i => rfl) (fun i => rfl) (hb hC)
  have hblock₂ : ∀ k, ∀ᶠ m in atTop,
      (μP m : Measure RecPair).map (fun z => truncRec k z.2) =
        (dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map (fun ω => truncRec k (recAll B₂ S₂ ω.2)) := by
    intro k
    refine eventually_atTop.2 ⟨k, fun m hkm => ?_⟩
    have hT := (continuous_truncRec k).measurable
    have hb := measurable_truncRec_recAll (hfam k).bm₂.2.1 (hfam k).cont₂ k (hfam k).stop₂
    have hb' : Measurable fun ω : Ω₁ × Ω₂ => truncRec k (recAll B₂ S₂ ω.2) :=
      (hb.mono (isStoppingTime_lastExit (hfam k).stop₂).measurableSpace_le le_rfl).comp measurable_snd
    show ((dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm m).map _).map _ = _
    rw [Measure.map_map (show Measurable fun z : RecPair => truncRec k z.2 from hT.comp measurable_snd) hR]
    show Measure.map (fun ω : Ω₁ × Ω₂ => truncRec k (recAll B₂ S₂ ω.2)) _ = _
    ext C hC
    rw [Measure.map_apply hb' hC, Measure.map_apply hb' hC]
    have e : (fun ω : Ω₁ × Ω₂ => truncRec k (recAll B₂ S₂ ω.2)) ⁻¹' C =
        (univ : Set Ω₁) ×ˢ ((fun ω => truncRec k (recAll B₂ S₂ ω)) ⁻¹' C) := by
      ext ω; simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    rw [e]
    exact (hfam k).dualCoupling_snd_congr (hfam m) rr (Fin.castLE (by omega)) (fun i => rfl) (fun i => rfl) (hb hC)
  -- tightness
  have hT : IsTightMeasureSet (range fun m => (μP m : Measure RecPair)) := by
    have hcoord : ∀ (g : RecSpace × RecSpace → RecSpace), Continuous g → ∀ k,
        IsTightMeasureSet (range fun m => ((μP m : Measure RecPair).map (f k)).map g) :=
      fun g hg k => isTightMeasureSet_range_of_eventually_eq _ ((hev k).mono fun m hm => by rw [hm])
    refine IsTightMeasureSet.prodMk ?_ ?_
    · refine isTightMeasureSet_pi_of_coord fun k => ?_
      refine (hcoord Prod.fst continuous_fst k).subset ?_
      rintro _ ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩
      refine ⟨m, ?_⟩
      show ((μP m : Measure RecPair).map (f k)).map Prod.fst =
        ((μP m : Measure RecPair).fst).map fun x : ℕ → RecSpace => x k
      rw [Measure.map_map measurable_fst (hf k).measurable, Measure.fst,
        Measure.map_map (measurable_pi_apply k) measurable_fst]
      rfl
    · refine isTightMeasureSet_pi_of_coord fun k => ?_
      refine (hcoord Prod.snd continuous_snd k).subset ?_
      rintro _ ⟨_, ⟨_, ⟨m, rfl⟩, rfl⟩, rfl⟩
      refine ⟨m, ?_⟩
      show ((μP m : Measure RecPair).map (f k)).map Prod.snd =
        ((μP m : Measure RecPair).snd).map fun x : ℕ → RecSpace => x k
      rw [Measure.map_map measurable_snd (hf k).measurable, Measure.snd,
        Measure.map_map (measurable_pi_apply k) measurable_snd]
      rfl
  -- all tests, valued in one space
  let g : ℕ ⊕ ℕ ⊕ ℕ → RecPair → RecPair
    | Sum.inl k => fun z => (fun j => if j = k then z.1 k else 0, fun j => if j = k then z.2 k else 0)
    | Sum.inr (Sum.inl k) => fun z => (truncRec k z.1, 0)
    | Sum.inr (Sum.inr k) => fun z => (0, truncRec k z.2)
  have hpairC : ∀ k, Continuous fun w : RecSpace × RecSpace =>
      ((fun j => if j = k then w.1 else 0, fun j => if j = k then w.2 else 0) : RecPair) := fun k => by
    refine (continuous_pi fun j => ?_).prodMk (continuous_pi fun j => ?_)
    · by_cases hj : j = k
      · simp only [hj, ite_true]; exact continuous_fst
      · simp only [hj, ite_false]; exact continuous_const
    · by_cases hj : j = k
      · simp only [hj, ite_true]; exact continuous_snd
      · simp only [hj, ite_false]; exact continuous_const
  have hg : ∀ i, Continuous (g i) := by
    rintro (k | k | k)
    · exact (hpairC k).comp (hf k)
    · exact ((continuous_truncRec k).comp continuous_fst).prodMk continuous_const
    · exact continuous_const.prodMk ((continuous_truncRec k).comp continuous_snd)
  let lamT : ℕ ⊕ ℕ ⊕ ℕ → Measure RecPair
    | Sum.inl k => (lam k).map fun w =>
        ((fun j => if j = k then w.1 else 0, fun j => if j = k then w.2 else 0) : RecPair)
    | Sum.inr (Sum.inl k) => ((dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map
        (fun ω => truncRec k (recAll B₁ S₁ ω.1))).map fun x => ((x, 0) : RecPair)
    | Sum.inr (Sum.inr k) => ((dualCouplingFirst κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map
        (fun ω => truncRec k (recAll B₂ S₂ ω.2))).map fun x => ((0, x) : RecPair)
  have hevT : ∀ i, ∀ᶠ m in atTop, (μP m : Measure RecPair).map (g i) = lamT i := by
    rintro (k | k | k)
    · refine (hev k).mono fun m hm => ?_
      show _ = (lam k).map _
      rw [← hm, Measure.map_map (hpairC k).measurable (hf k).measurable]
      rfl
    · refine (hblock₁ k).mono fun m hm => ?_
      show _ = (Measure.map _ _).map _
      rw [← hm, Measure.map_map (show Measurable fun x : ℕ → RecSpace => ((x, 0) : RecPair) from
        measurable_id.prodMk measurable_const) (show Measurable fun z : RecPair => truncRec k z.1 from
        (continuous_truncRec k).measurable.comp measurable_fst)]
      rfl
    · refine (hblock₂ k).mono fun m hm => ?_
      show _ = (Measure.map _ _).map _
      rw [← hm, Measure.map_map (show Measurable fun x : ℕ → RecSpace => ((0, x) : RecPair) from
        measurable_const.prodMk measurable_id) (show Measurable fun z : RecPair => truncRec k z.2 from
        (continuous_truncRec k).measurable.comp measurable_snd)]
      rfl
  obtain ⟨μ', -, hμ'⟩ := exists_limit_of_eventually_map_eq μP hT (Z := fun _ => RecPair) g hg lamT hevT
  refine ⟨μ', inferInstance, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · -- recover the pair law from its embedding
    have hback : Measurable fun w : RecPair => (w.1 k, w.2 k) :=
      ((measurable_pi_apply k).comp measurable_fst).prodMk ((measurable_pi_apply k).comp measurable_snd)
    have h1 := congrArg (fun ν : Measure RecPair => ν.map fun w : RecPair => (w.1 k, w.2 k)) (hμ' (Sum.inl k))
    rw [Measure.map_map hback (hg (Sum.inl k)).measurable, Measure.map_map hback (hpairC k).measurable] at h1
    have e1 : ((fun w : RecPair => (w.1 k, w.2 k)) ∘ g (Sum.inl k)) = f k := by
      funext z; simp only [Function.comp_apply, g, f, ite_true]
    have e2 : ((fun w : RecPair => (w.1 k, w.2 k)) ∘ fun w : RecSpace × RecSpace =>
        ((fun j => if j = k then w.1 else 0, fun j => if j = k then w.2 else 0) : RecPair)) = id := by
      funext w; simp only [Function.comp_apply, ite_true, id]
    rw [e1, e2, Measure.map_id] at h1
    exact h1
  · have h1 := congrArg (fun ν : Measure RecPair => ν.map Prod.fst) (hμ' (Sum.inr (Sum.inl k)))
    rw [Measure.map_map measurable_fst (hg (Sum.inr (Sum.inl k))).measurable,
      Measure.map_map measurable_fst (show Measurable fun x : ℕ → RecSpace => ((x, 0) : RecPair) from
        measurable_id.prodMk measurable_const)] at h1
    have e : (Prod.fst ∘ fun x : ℕ → RecSpace => ((x, 0) : RecPair)) = id := rfl
    rw [e, Measure.map_id] at h1
    exact h1
  · have h1 := congrArg (fun ν : Measure RecPair => ν.map Prod.snd) (hμ' (Sum.inr (Sum.inr k)))
    rw [Measure.map_map measurable_snd (hg (Sum.inr (Sum.inr k))).measurable,
      Measure.map_map measurable_snd (show Measurable fun x : ℕ → RecSpace => ((0, x) : RecPair) from
        measurable_const.prodMk measurable_id)] at h1
    have e : (Prod.snd ∘ fun x : ℕ → RecSpace => ((0, x) : RecPair)) = id := rfl
    rw [e, Measure.map_id] at h1
    exact h1

/-- **The (D10) disintegration of rectangle `k` under any measure with the rectangle law** (e.g. the A.1.5 coupling of
`exists_dualCoupling_lim`): the probability that the recorded coordinates of rectangle `k` lie in `A × B` is
`∫_{rec₂ ∈ B} Q_{ω₂}(rec₁ ∈ A) · Ñ_t(0, S₂ k)/Ñ_t(0, 0) dP₂`, where `Q_{ω₂}` (`condMeasure₁`) is the conditional law of
curve `1` given the curve-`2` prefix, the force-point law of the image word (A17's `DualHyp.exists_condLaw₁`). -/
theorem map_rect_apply_prod_eq
    (hfam : ∀ m, DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ (fun k : Fin (m + 1) => H₁ k) (fun k : Fin (m + 1) => H₂ k)
      (fun k : Fin (m + 1) => δ k) (fun k : Fin (m + 1) => q k) (fun k : Fin (m + 1) => d k) p (Tm m)
      (fun k : Fin (m + 1) => S₁ k) (fun k : Fin (m + 1) => S₂ k)) (rr : Fin n → ℝ) {μ : Measure RecPair} {k : ℕ}
    (hμ : μ.map (fun z => (z.1 k, z.2 k)) = (dualCouplingOne κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm k).map
      (fun ω => (recPath B₁ (S₁ k) ω.1, recPath B₂ (S₂ k) ω.2))) {A B : Set RecSpace} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    μ {z | z.1 k ∈ A ∧ z.2 k ∈ B} =
      ∫⁻ ω₂ in recPath B₂ (S₂ k) ⁻¹' B, condMeasure₁ κ rr p P₁ B₁ B₂ x₂ (fun _ : Unit => S₁ k)
          (fun _ : Unit => S₂ k) () ω₂ (recPath B₁ (S₁ k) ⁻¹' A) *
        ENNReal.ofReal (Real.exp (pairT κ rr p B₁ B₂ x₂ (fun _ : Unit => S₁ k) (fun _ : Unit => S₂ k)
          (nonempty_of_isFilteredBrownianReal (hfam k).bm₁).some ω₂ 0 (S₂ k ω₂) -
          pairT κ rr p B₁ B₂ x₂ (fun _ : Unit => S₁ k) (fun _ : Unit => S₂ k)
          (nonempty_of_isFilteredBrownianReal (hfam k).bm₁).some ω₂ 0 0)) ∂P₂ := by
  have hone : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ (fun _ : Unit => H₁ k) (fun _ : Unit => H₂ k)
      (fun _ : Unit => δ k) (fun _ : Unit => q k) (fun _ : Unit => d k) p (Tm k) (fun _ : Unit => S₁ k)
      (fun _ : Unit => S₂ k) :=
    (hfam k).restrict (fun _ : Unit => (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)))
  have hm₁ := measurable_recPath hone.bm₁.2.1 hone.cont₁ (hone.stop₁ ())
  have hm₂ := measurable_recPath hone.bm₂.2.1 hone.cont₂ (hone.stop₂ ())
  have hpk : Measurable fun z : RecPair => (z.1 k, z.2 k) :=
    ((measurable_pi_apply k).comp measurable_fst).prodMk ((measurable_pi_apply k).comp measurable_snd)
  have hrec : Measurable fun ω : Ω₁ × Ω₂ => (recPath B₁ (S₁ k) ω.1, recPath B₂ (S₂ k) ω.2) :=
    ((hm₁.mono (hone.stop₁ ()).measurableSpace_le le_rfl).comp measurable_fst).prodMk
      ((hm₂.mono (hone.stop₂ ()).measurableSpace_le le_rfl).comp measurable_snd)
  have e1 : {z : RecPair | z.1 k ∈ A ∧ z.2 k ∈ B} = (fun z : RecPair => (z.1 k, z.2 k)) ⁻¹' (A ×ˢ B) := rfl
  rw [e1, ← Measure.map_apply hpk (hA.prod hB), hμ, Measure.map_apply hrec (hA.prod hB)]
  have e2 : (fun ω : Ω₁ × Ω₂ => (recPath B₁ (S₁ k) ω.1, recPath B₂ (S₂ k) ω.2)) ⁻¹' (A ×ˢ B) =
      (recPath B₁ (S₁ k) ⁻¹' A) ×ˢ (recPath B₂ (S₂ k) ⁻¹' B) := rfl
  rw [e2]
  exact hone.dualCoupling_rect_eq rr () (hm₁ hA) (hm₂ hB)

end Lim

end InteractingSLE.ZhanGT4
