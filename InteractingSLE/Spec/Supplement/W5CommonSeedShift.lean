/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Restart.Datum
import InteractingSLE.Spec.Supplement.S10Order

/-!
# Recentering a flow line at its seed

Packet PROVE-AUX97 (the translation step of W5's common-seed comparison: "For a common seed, use the joint local
comparison in Aux. lemma 97", `source/spec/p529-576.md` L133, p. 534, where the common seed is an arbitrary real point
`x` while Aux. lemma 97 is stated for flow lines from `0`).

For a GFF `h` on `ℍ` with piecewise-constant data `b` and a flow line `η` from `x` (frozen `IsFlowLine`), the translated
field `h(· + x)` (PROVE-FLOWEXIST's `Exist.flowField x 0 h`) is a GFF with data `b(· + x)` (jump candidates `J − x`),
and `η − x` is its flow line from `0`, with the same angle, lifetime, driving evolution and coupled field
`h(· + x) + θχ`:

* `jumpSet_comp_add`: the genuine jumps of `b(· + x)` are those of `b`, shifted by `−x`;
* `orderEmbOfFin_filter_lt_image_sub`, `orderEmbOfFin_filter_gt_image_sub`: the sorted marks of the shifted word;
* `isOptionalHullCoupling_comp_cast`: the frozen coupling predicate is invariant under reindexing the marks along an
  equality of their numbers;
* **`IsFlowLine.recenter`**, **`IsGFFWithBoundaryData.recenter`**;
* `HasOrderedProperCompletions.of_sub_real`: ordered proper completions of the recentered prefixes give those of the
  original prefixes (S10Order's translation of closed left sides and proper completions).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp9

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### The shifted force word -/

/-- The genuine jumps of `b(· + x)` (jump candidates `J − x`) are the genuine jumps of `b`, shifted by `−x`. -/
theorem jumpSet_comp_add (b : ℝ → ℝ) (J : Finset ℝ) (x : ℝ) :
    jumpSet (fun y => b (y + x)) (J.image (· - x)) = (jumpSet b J).image (· - x) := by
  unfold PiecewiseConstantBoundaryData.jumpSet
  rw [Finset.filter_image]
  congr 1
  refine Finset.filter_congr fun z _ => ?_
  rw [Exist.leftLim_comp_add, Exist.rightLim_comp_add, sub_add_cancel]

theorem filter_lt_image_sub (S : Finset ℝ) (x : ℝ) :
    (S.image (· - x)).filter (· < 0) = (S.filter (· < x)).image (· - x) := by
  rw [Finset.filter_image]
  congr 1
  exact Finset.filter_congr fun z _ => sub_neg

theorem filter_gt_image_sub (S : Finset ℝ) (x : ℝ) :
    (S.image (· - x)).filter (0 < ·) = (S.filter (x < ·)).image (· - x) := by
  rw [Finset.filter_image]
  congr 1
  exact Finset.filter_congr fun z _ => sub_pos

theorem card_filter_lt_image_sub (S : Finset ℝ) (x : ℝ) :
    ((S.image (· - x)).filter (· < 0)).card = (S.filter (· < x)).card := by
  rw [filter_lt_image_sub, Finset.card_image_of_injective _ (sub_left_injective)]

theorem card_filter_gt_image_sub (S : Finset ℝ) (x : ℝ) :
    ((S.image (· - x)).filter (0 < ·)).card = (S.filter (x < ·)).card := by
  rw [filter_gt_image_sub, Finset.card_image_of_injective _ (sub_left_injective)]

/-- The sorted left marks of the shifted word are the shifted sorted left marks. -/
theorem orderEmbOfFin_filter_lt_image_sub (S : Finset ℝ) (x : ℝ)
    (i : Fin ((S.image (· - x)).filter (· < 0)).card) :
    ((S.image (· - x)).filter (· < 0)).orderEmbOfFin rfl i =
      (S.filter (· < x)).orderEmbOfFin rfl (Fin.cast (card_filter_lt_image_sub S x) i) - x := by
  have hu := Finset.orderEmbOfFin_unique (s := (S.image (· - x)).filter (· < 0)) rfl
    (f := fun i => (S.filter (· < x)).orderEmbOfFin rfl (Fin.cast (card_filter_lt_image_sub S x) i) - x)
    (fun i => by
      have hm := Finset.orderEmbOfFin_mem (S.filter (· < x)) rfl (Fin.cast (card_filter_lt_image_sub S x) i)
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_image_of_mem _ hm.1, sub_neg.2 hm.2⟩)
    (fun i j hij => sub_lt_sub_right (((S.filter (· < x)).orderEmbOfFin rfl).strictMono
      (show Fin.cast (card_filter_lt_image_sub S x) i < Fin.cast (card_filter_lt_image_sub S x) j from hij)) x)
  exact (congrFun hu i).symm

/-- The sorted right marks of the shifted word are the shifted sorted right marks. -/
theorem orderEmbOfFin_filter_gt_image_sub (S : Finset ℝ) (x : ℝ)
    (i : Fin ((S.image (· - x)).filter (0 < ·)).card) :
    ((S.image (· - x)).filter (0 < ·)).orderEmbOfFin rfl i =
      (S.filter (x < ·)).orderEmbOfFin rfl (Fin.cast (card_filter_gt_image_sub S x) i) - x := by
  have hu := Finset.orderEmbOfFin_unique (s := (S.image (· - x)).filter (0 < ·)) rfl
    (f := fun i => (S.filter (x < ·)).orderEmbOfFin rfl (Fin.cast (card_filter_gt_image_sub S x) i) - x)
    (fun i => by
      have hm := Finset.orderEmbOfFin_mem (S.filter (x < ·)) rfl (Fin.cast (card_filter_gt_image_sub S x) i)
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_image_of_mem _ hm.1, sub_pos.2 hm.2⟩)
    (fun i j hij => sub_lt_sub_right (((S.filter (x < ·)).orderEmbOfFin rfl).strictMono
      (show Fin.cast (card_filter_gt_image_sub S x) i < Fin.cast (card_filter_gt_image_sub S x) j from hij)) x)
  exact (congrFun hu i).symm

/-- The frozen coupling predicate is invariant under reindexing the marks along an equality of their numbers. -/
theorem isOptionalHullCoupling_comp_cast {κ : ℝ} {nL nR mL mR : ℕ} (eL : mL = nL) (eR : mR = nR)
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hc : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    IsOptionalHullCoupling κ (fun i => xL (Fin.cast eL i)) (fun i => xR (Fin.cast eR i))
      (fun i => ρL (Fin.cast eL i)) (fun i => ρR (Fin.cast eR i)) P 𝓕 W (fun i => VL (Fin.cast eL i))
      (fun i => VR (Fin.cast eR i)) B ζ h := by
  subst eL eR
  exact hc

/-! ### Recentering -/

variable {κ θ : ℝ}

/-- **Recentering the explicit flow-line predicate** (`Restart.flowLineOf`, the unfolded frozen `IsFlowLine`) at its
seed: the flow line `η` from `x` of `h` is, after subtracting `x`, the flow line from `0` of `h(· + x)`, with the jump
set, one-sided limits and positions shifted by `−x`; the coupled field `h(· + x) + θχ`, the driving evolution (marks
reindexed) and the lifetime are unchanged. -/
theorem flowLineOf_recenter {S : Finset ℝ} {L R : ℝ → ℝ} {x : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : Restart.flowLineOf κ S L R x θ P h η ζ) :
    Restart.flowLineOf κ (S.image (· - x)) (fun z => L (z + x)) (fun z => R (z + x)) 0 θ P
      (fun ω => Exist.flowField x 0 (h ω)) (fun ω t => η ω t - x) ζ := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hcpl, htrace⟩ := hfl
  have eL : ((S.image (· - x)).filter (· < 0)).card + 1 = (S.filter (· < x)).card + 1 := by
    rw [card_filter_lt_image_sub]
  have eR : ((S.image (· - x)).filter (0 < ·)).card + 1 = (S.filter (x < ·)).card + 1 := by
    rw [card_filter_gt_image_sub]
  refine ⟨h', 𝓕, W, fun i => VL (Fin.cast eL i), fun i => VR (Fin.cast eR i), B, fun ω => ?_, ?_, ?_⟩
  · intro φ φ' hφ
    rw [Exist.flowField_apply, zero_mul, add_zero]
    refine htr ω _ φ' fun z => ?_
    rw [Exist.pushTest_shiftChart_apply, add_sub_cancel_right, hφ, Complex.ofReal_zero, add_zero]
  · convert isOptionalHullCoupling_comp_cast eL eR hcpl using 2 with j j j j
    · refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ, orderEmbOfFin_filter_lt_image_sub, sub_zero,
          Fin.cast_rev]
    · refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ, orderEmbOfFin_filter_gt_image_sub, sub_zero]
    · refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero, Fin.cast_zero, zero_add]
      · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ]
        simp only [orderEmbOfFin_filter_lt_image_sub, sub_add_cancel, Fin.cast_rev]
    · refine Fin.cases ?_ (fun i => ?_) j
      · simp only [Fin.cons_zero, Fin.cast_zero, zero_add]
      · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ]
        simp only [orderEmbOfFin_filter_gt_image_sub, sub_add_cancel]
  · filter_upwards [htrace] with ω hω
    simpa only [Complex.ofReal_zero, sub_zero] using hω

/-- **Recentering a flow line at its seed**: if `η` is the angle-`θ` flow line from `x` of `h` (data `b`, jump
candidates `J`), then `η − x` is the angle-`θ` flow line from `0` of `h(· + x)` (data `b(· + x)`, candidates `J − x`),
with the same lifetime. -/
theorem IsFlowLine.recenter {b : ℝ → ℝ} {J : Finset ℝ} {x : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b J x θ P h η ζ) :
    IsFlowLine κ (fun y => b (y + x)) (J.image (· - x)) 0 θ P (fun ω => Exist.flowField x 0 (h ω))
      (fun ω t => η ω t - x) ζ := by
  rw [Restart.isFlowLine_eq_flowLineOf] at hη ⊢
  have hL : leftLim (fun y => b (y + x)) = fun z => leftLim b (z + x) := funext (Exist.leftLim_comp_add b x)
  have hR : rightLim (fun y => b (y + x)) = fun z => rightLim b (z + x) := funext (Exist.rightLim_comp_add b x)
  rw [jumpSet_comp_add, hL, hR]
  exact flowLineOf_recenter hη

/-- **Recentering a GFF**: if `h` is a GFF on `ℍ` with piecewise-constant data `b` (candidates `J`), then `h(· + x)`
is a GFF with data `b(· + x)` (candidates `J − x`). -/
theorem IsGFFWithBoundaryData.recenter {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (x : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) :
    IsGFFWithBoundaryData P (fun ω => Exist.flowField x 0 (h ω)) (fun y => b (y + x)) (J.image (· - x)) := by
  refine ⟨(Exist.measurable_flowField x 0).comp hh.1, fun u hu => ?_⟩
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hmi : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun w => u₀ (w + x) * φ w) := fun φ =>
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H)
      ((hu₀.1.continuousOn).comp (continuousOn_id.add continuousOn_const) fun z hz => Exist.add_real_mem_H hz x) φ
      φ.tsupport_subset
  have hX := Exist.isZBGFFProcess_flowField (hh.2 u₀ hu₀) x 0 hmi
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => u₀ (z + x)) H :=
    fun z hz => Exist.harmonicAt_comp_add_const (hu₀.1 _ (Exist.add_real_mem_H hz x))
  have hbdd : ∀ {v : ℂ → ℝ}, (∃ C : ℝ, ∀ z ∈ H, |v z| ≤ C) → Bornology.IsBounded (v '' H) := by
    rintro v ⟨C, hC⟩
    exact isBounded_iff_forall_norm_le.2 ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact (hC z hz)⟩
  obtain ⟨C₀, hC₀⟩ := hu₀.2.1
  have heq : EqOn u (fun z => u₀ (z + x)) H := by
    refine eqOn_of_tendsto_sub_H (J.image (· - x)) hu.1 hharm (hbdd hu.2.1)
      (hbdd ⟨C₀, fun z hz => hC₀ _ (Exist.add_real_mem_H hz x)⟩) fun t ht => ?_
    have htx : t + x ∉ J := fun h' => ht (Finset.mem_image.2 ⟨t + x, h', by ring⟩)
    have h1 := hu.2.2 t (by exact_mod_cast ht)
    have h2 := (hu₀.2.2 (t + x) (by exact_mod_cast htx)).comp (Exist.tendsto_add_real_nhdsWithin_H t x)
    have h3 := h1.sub h2
    rw [sub_self] at h3
    exact h3
  convert hX using 4 with φ ω
  congr 1
  funext z
  by_cases hz : z ∈ H
  · rw [heq hz, add_zero]
  · have h0 : φ z = 0 := φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
    rw [h0, mul_zero, mul_zero]

/-- **Translating ordered proper completions back**: ordered proper completions of the recentered prefixes
`(α − x)[0, a]`, `(β − x)[0, c]` give ordered proper completions of `α[0, a]`, `β[0, c]`. -/
theorem HasOrderedProperCompletions.of_sub_real {α β : ℝ≥0 → ℂ} {a c : ℝ≥0} (x : ℝ)
    (hc : HasOrderedProperCompletions (fun t => α t - x) a (fun t => β t - x) c) :
    HasOrderedProperCompletions α a β c := by
  obtain ⟨α', β', hα', hβ', hsub⟩ := hc
  have e : ∀ γ : ℝ≥0 → ℂ, (fun t => (fun t => γ t - (x : ℂ)) t + ((-(-x) : ℝ) : ℂ)) = γ := fun γ => by
    funext t
    push_cast
    ring
  refine ⟨fun t => α' t + ((-(-x) : ℝ) : ℂ), fun t => β' t + ((-(-x) : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have := Supp10.IsProperCompletion.sub_real hα' (-x)
    rwa [e α] at this
  · have := Supp10.IsProperCompletion.sub_real hβ' (-x)
    rwa [e β] at this
  · rw [Supp10.closedLeftSide_add_real]
    rintro _ ⟨u, rfl⟩
    exact ⟨β' u, hsub ⟨u, rfl⟩, rfl⟩

end Supp9

end InteractingSLE
