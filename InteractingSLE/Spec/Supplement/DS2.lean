/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS1

/-!
# Lemma DS2 (stability away from the initial double entrance): the statement, and the inverse-gap step (DS2.1)

Packet PROVE-T14-TIP2. Specification supplement §12, **Lemma DS2** (`source/spec/p529-576.md` L577–L594, p. 553):

> Under the uniform hypotheses of DS1, let the weights and initial ordered positions converge within a fixed initial
> grouping. Initially coincident labels are amalgamated first, and distinct nonseed groups are initially separated
> uniformly. The integrated driving and force-coordinate laws converge weakly, in the topology of uniform convergence
> on compact time intervals before the prescribed far-buffer exit, to the integrated law with the limiting weights and
> positions. … The initial states may have `X₁ = 0` or `Y₁ = 0` (but not both when `D ≥ a`), and nearby states may
> differ on that coincidence.

and its proof's last paragraph: "The phrase *before the far-buffer exit* is understood by increasing compact
sub-buffers. Equivalently, stop strictly inside each bound and then exhaust it. For applications to a crossing event,
select strict time, driver and gap margins first; only the open event that the desired driver level is exceeded before
those margins fail is used."

## The statement (`DS2Statement`)

Weak convergence is stated in Portmanteau's open-set form, restricted to state paths strictly inside the far buffer:
for every horizon `T` and every set `U` of continuous state paths on `[0, T]` that is open in the uniform topology and
keeps every far gap above `g`, the limiting probability of "alive through `T` with state path in `U`" is at most the
`liminf` of the approximating probabilities. Open sets inside the buffer are exactly the "increasing compact
sub-buffers" with strict margins of the source, and the crossing events of DS4 and CS3 are of this form. The
evolutions of the sequence may live on different probability spaces (the conclusion concerns laws only).

DS1's uniform hypotheses (`IsDS1Word`): ordered word, weights bounded by `Rw`, every inner partial sum satisfies
(DS1.1) `S + 2 ≥ ε` (the inner block is the labels before the first far label `m_L`, `m_R`, as in `DS1.ds1`), and the
cross gap `X₁ + Y₁ ≥ a` at the start.

## Proved here

* `integral_inv_gap_le` (**(DS2.1)**, pathwise): for every right label `i` (so `X_i ≥ X₁`) and times
  `s ≤ t ≤ T < ζ`, `∫ₛᵗ du/X_i ≤ ∫₀ᵀ 1{0 < X₁ < δ} du/X₁ + (t − s)/δ`.

The remaining steps of the proof (joint tightness on `C([0, T])`, identification of subsequential limits — the
integrated equations, the absence of a sticky part, the Brownian martingale property in the limiting filtration —
and integrated weak uniqueness) are not formalized here; see the handoff `planning/handoffs/PROVE-T14-TIP2.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace DS2

/-! ### The statement -/

section Statement

variable {nL nR : ℕ}

/-- **DS1's uniform hypotheses on one word**: ordered, weights bounded by `Rw`, and (DS1.1) `S_i + 2 ≥ ε` at every
inner label (labels before the first far label `m_L` on the left, `m_R` on the right). -/
def IsDS1Word (mL mR : ℕ) (Rw ε : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Prop :=
  IsOrderedForceWord xL xR ∧ (∀ i, |ρL i| ≤ Rw) ∧ (∀ j, |ρR j| ≤ Rw) ∧
    (∀ i : Fin nL, (i : ℕ) < mL → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l + 2) ∧
    ∀ j : Fin nR, (j : ℕ) < mR → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l + 2

/-- A state **strictly inside the far buffer**: every far gap (right labels `≥ m_R`, left labels `≥ m_L`) exceeds
`g`. -/
def InFarBuffer (mL mR : ℕ) (g : ℝ) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop :=
  (∀ j : Fin nR, mR ≤ (j : ℕ) → g < p.2.2 j - p.1) ∧ ∀ i : Fin nL, mL ≤ (i : ℕ) → g < p.1 - p.2.1 i

/-- The event that the evolution is alive through `T` and its state path on `[0, T]` is in `U`. -/
def pathEvent (T : ℝ≥0) (U : Set C(Set.Icc (0 : ℝ≥0) T, ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | (T : ℝ≥0∞) < ζ ω ∧ ∃ f ∈ U, ∀ t : Set.Icc (0 : ℝ≥0) T, f t = Coupling.stateAt W VL VR t ω}

/-- Two position vectors of one side have the **same coincidence pattern** (the same initial grouping). -/
def SameGrouping {n : ℕ} (x x' : Fin n → ℝ) : Prop :=
  ∀ i i', x i = x i' ↔ x' i = x' i'

end Statement

/-- **Named statement: Lemma DS2** (p. 553), open-set (Portmanteau) form before the far-buffer exit. A sequence of
DS1 words with cross gap at least `a`, converging weights and initial positions in a fixed grouping with nonseed
groups uniformly `η`-separated, and any integrated evolutions of them and of the limiting word: for every horizon `T`
and every open set `U` of continuous state paths on `[0, T]` inside the far buffer,
`P₀(alive through T, path ∈ U) ≤ liminf_m P_m(alive through T, path ∈ U)`. -/
def DS2Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) (mL mR : ℕ) (Rw ε a g η : ℝ),
    0 < ε → 0 < a → 0 < g → 0 < η →
    ∀ (xL : ℕ → Fin nL → ℝ) (xR : ℕ → Fin nR → ℝ) (ρL : ℕ → Fin nL → ℝ) (ρR : ℕ → Fin nR → ℝ)
      (xL₀ : Fin nL → ℝ) (xR₀ : Fin nR → ℝ) (ρL₀ : Fin nL → ℝ) (ρR₀ : Fin nR → ℝ),
      (∀ m, IsDS1Word mL mR Rw ε (xL m) (xR m) (ρL m) (ρR m)) → IsDS1Word mL mR Rw ε xL₀ xR₀ ρL₀ ρR₀ →
      -- the cross gap `X₁ + Y₁ = x_{R,0} − x_{L,0} ≥ a` at the start
      (∀ m, a ≤ xR m ⟨0, hnR⟩ - xL m ⟨0, hnL⟩) → a ≤ xR₀ ⟨0, hnR⟩ - xL₀ ⟨0, hnL⟩ →
      -- weights and initial positions converge within a fixed grouping
      Tendsto xL atTop (𝓝 xL₀) → Tendsto xR atTop (𝓝 xR₀) → Tendsto ρL atTop (𝓝 ρL₀) →
      Tendsto ρR atTop (𝓝 ρR₀) →
      (∀ m, SameGrouping (xL m) xL₀) → (∀ m, SameGrouping (xR m) xR₀) →
      -- distinct groups are initially separated uniformly
      (∀ m i i', xL m i ≠ xL m i' → η ≤ |xL m i - xL m i'|) →
      (∀ m j j', xR m j ≠ xR m j' → η ≤ |xR m j - xR m j'|) →
      ∀ (Ω : ℕ → Type u) [mΩ : ∀ m, MeasurableSpace (Ω m)] (P : ∀ m, Measure (Ω m))
        (𝓕 : ∀ m, Filtration ℝ≥0 (mΩ m)) (W : ∀ m, ℝ≥0 → Ω m → ℝ) (VL : ∀ m, Fin nL → ℝ≥0 → Ω m → ℝ)
        (VR : ∀ m, Fin nR → ℝ≥0 → Ω m → ℝ) (B : ∀ m, ℝ≥0 → Ω m → ℝ) (ζ : ∀ m, Ω m → ℝ≥0∞),
        (∀ m, IsIntegratedSLEEvolution κ (xL m) (xR m) (ρL m) (ρR m) (P m) (𝓕 m) (W m) (VL m) (VR m) (B m)
          (ζ m)) →
      ∀ {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀)
        (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ)
        (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞),
        IsIntegratedSLEEvolution κ xL₀ xR₀ ρL₀ ρR₀ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ →
      ∀ (T : ℝ≥0) (U : Set C(Set.Icc (0 : ℝ≥0) T, ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))), IsOpen U →
        (∀ f ∈ U, ∀ t, InFarBuffer mL mR g (f t)) →
        P₀ (pathEvent T U W₀ VL₀ VR₀ ζ₀) ≤
          liminf (fun m => P m (pathEvent T U (W m) (VL m) (VR m) (ζ m))) atTop

/-! ### (DS2.1) -/

section InvGap

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The truncated inverse gap `1{0 < x < δ}/x`. -/
def invCut (δ x : ℝ) : ℝ := {y : ℝ | 0 < y ∧ y < δ}.indicator (fun y => 1 / y) x

theorem invCut_nonneg (δ x : ℝ) : 0 ≤ invCut δ x := by
  unfold invCut
  by_cases h : x ∈ {y : ℝ | 0 < y ∧ y < δ}
  · rw [Set.indicator_of_mem h]; exact one_div_nonneg.2 h.1.le
  · rw [Set.indicator_of_notMem h]

theorem invCut_le (δ x : ℝ) : invCut δ x ≤ |x⁻¹| := by
  unfold invCut
  by_cases h : x ∈ {y : ℝ | 0 < y ∧ y < δ}
  · rw [Set.indicator_of_mem h, one_div]; exact le_abs_self _
  · rw [Set.indicator_of_notMem h]; exact abs_nonneg _

theorem measurable_invCut (δ : ℝ) : Measurable (invCut δ) :=
  (measurable_const.div measurable_id).indicator
    ((measurableSet_lt measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const))

/-- Pointwise: if `0 < X₁ ≤ X_i`, then `1/X_i ≤ 1{0 < X₁ < δ}/X₁ + 1/δ`. -/
theorem inv_le_invCut_add {X1 Xi δ : ℝ} (hδ : 0 < δ) (h1 : 0 < X1) (h1i : X1 ≤ Xi) :
    Xi⁻¹ ≤ invCut δ X1 + 1 / δ := by
  have hi : Xi⁻¹ ≤ X1⁻¹ := inv_anti₀ h1 h1i
  unfold invCut
  by_cases h : X1 < δ
  · rw [Set.indicator_of_mem (show X1 ∈ {y : ℝ | 0 < y ∧ y < δ} from ⟨h1, h⟩), one_div]
    have : 0 ≤ 1 / δ := one_div_nonneg.2 hδ.le
    linarith
  · rw [Set.indicator_of_notMem (fun hm => h hm.2), zero_add]
    exact hi.trans (by rw [one_div]; exact inv_anti₀ hδ (not_lt.1 h))

/-- **(DS2.1)** (p. 553): "For any inner right label, `X_i ≥ X_1`. For a time interval of length at most `h`,
`∫ₛᵗ du/X_i(u) ≤ ∫₀ᵀ 1{0 < X₁ < δ} du/X₁(u) + h/δ`." Along an integrated path, for a right label `i`, times
`s ≤ t ≤ T < ζ` and `δ > 0` (the nearest right label is `0`; collision times are Lebesgue-null). -/
theorem integral_inv_gap_le (hnR : 0 < nR) (hp : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (i : Fin nR)
    {s t T : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) (hT : (T : ℝ≥0∞) < ζ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ u in (s : ℝ)..t, (vR i u.toNNReal - w u.toNNReal)⁻¹ ≤
      (∫ u in (0 : ℝ)..T, invCut δ (vR ⟨0, hnR⟩ u.toNNReal - w u.toNNReal)) + ((t : ℝ) - s) / δ := by
  set i₀ : Fin nR := ⟨0, hnR⟩
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hlt : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) T → (u.toNNReal : ℝ≥0∞) < ζ := fun u hu =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hu.2) hT
  -- the gaps are integrable
  have hgi : IntervalIntegrable (fun u : ℝ => (vR i u.toNNReal - w u.toNNReal)⁻¹) MeasureTheory.volume 0 T := by
    have := (hp.integrable_gapR hT i).neg
    refine this.congr fun u _ => ?_
    simp only [Pi.neg_apply]
    rw [← inv_neg, neg_sub]
  have hg0 : IntervalIntegrable (fun u : ℝ => (vR i₀ u.toNNReal - w u.toNNReal)⁻¹) MeasureTheory.volume 0 T := by
    have := (hp.integrable_gapR hT i₀).neg
    refine this.congr fun u _ => ?_
    simp only [Pi.neg_apply]
    rw [← inv_neg, neg_sub]
  have hmeas0 : AEStronglyMeasurable (fun u : ℝ => vR i₀ u.toNNReal - w u.toNNReal)
      (MeasureTheory.volume.restrict (Set.uIoc 0 (T : ℝ))) := by
    have hc : ContinuousOn (fun u : ℝ => vR i₀ u.toNNReal - w u.toNNReal) (Set.Icc 0 T) :=
      ((hp.continuousOn_vR i₀).comp continuous_real_toNNReal.continuousOn hlt).sub
        (hp.continuousOn_w.comp continuous_real_toNNReal.continuousOn hlt)
    rw [Set.uIoc_of_le (NNReal.coe_nonneg T)]
    exact (hc.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hcut : IntervalIntegrable (fun u : ℝ => invCut δ (vR i₀ u.toNNReal - w u.toNNReal))
      MeasureTheory.volume 0 T := by
    refine (intervalIntegrable_iff.2 ?_)
    refine Integrable.mono' (intervalIntegrable_iff.1 hg0).norm
      ((measurable_invCut δ).comp_aemeasurable hmeas0.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (invCut_nonneg _ _)]
    exact invCut_le _ _
  have hsT : Set.uIcc (s : ℝ) t ⊆ Set.uIcc 0 (T : ℝ) := by
    rw [Set.uIcc_of_le hst', Set.uIcc_of_le (NNReal.coe_nonneg T)]
    exact Set.Icc_subset_Icc (NNReal.coe_nonneg s) (by exact_mod_cast htT)
  have hgi' := hgi.mono_set hsT
  have hcut' := hcut.mono_set hsT
  -- pointwise, off the collision set of the nearest label
  have hae : ∀ᵐ u ∂MeasureTheory.volume, u ∈ Set.Ioc (s : ℝ) t →
      (vR i u.toNNReal - w u.toNNReal)⁻¹ ≤ invCut δ (vR i₀ u.toNNReal - w u.toNNReal) + 1 / δ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hp.volume_collisionR i₀)] with u hu hus
    have hu0 : u ∈ Set.Icc (0 : ℝ) T :=
      ⟨(NNReal.coe_nonneg s).trans hus.1.le, hus.2.trans (by exact_mod_cast htT)⟩
    have hζ := hlt u hu0
    have hne : w u.toNNReal ≠ vR i₀ u.toNNReal := fun he => hu ⟨hu0.1, hζ, he⟩
    have h1 : 0 < vR i₀ u.toNNReal - w u.toNNReal := sub_pos.2 (lt_of_le_of_ne (hp.w_le_vR hζ i₀) hne)
    have h1i : vR i₀ u.toNNReal - w u.toNNReal ≤ vR i u.toNNReal - w u.toNNReal :=
      sub_le_sub_right (hp.monotone_vR hζ (Fin.le_def.2 (Nat.zero_le _))) _
    exact inv_le_invCut_add hδ h1 h1i
  calc ∫ u in (s : ℝ)..t, (vR i u.toNNReal - w u.toNNReal)⁻¹
      ≤ ∫ u in (s : ℝ)..t, (invCut δ (vR i₀ u.toNNReal - w u.toNNReal) + 1 / δ) :=
        intervalIntegral.integral_mono_ae_restrict hst' hgi' (hcut'.add intervalIntegrable_const)
          ((ae_restrict_iff' measurableSet_Icc).2 (by
            filter_upwards [hae, Measure.ae_ne volume (s : ℝ)] with u hu hus hmem
            exact hu ⟨lt_of_le_of_ne hmem.1 (Ne.symm hus), hmem.2⟩))
    _ = (∫ u in (s : ℝ)..t, invCut δ (vR i₀ u.toNNReal - w u.toNNReal)) + ((t : ℝ) - s) / δ := by
        rw [intervalIntegral.integral_add hcut' intervalIntegrable_const, intervalIntegral.integral_const,
          smul_eq_mul, mul_one_div]
    _ ≤ (∫ u in (0 : ℝ)..T, invCut δ (vR i₀ u.toNNReal - w u.toNNReal)) + ((t : ℝ) - s) / δ := by
        gcongr
        exact intervalIntegral.integral_mono_interval (NNReal.coe_nonneg s) hst' (by exact_mod_cast htT)
          (Eventually.of_forall fun u => invCut_nonneg _ _) hcut

end InvGap

end DS2

end Supp12

end InteractingSLE
