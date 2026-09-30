import QuantumZipper.Proofs.Complex.JSArea
import QuantumZipper.Proofs.Complex.JSMorera
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# EXT-JS node B1, step 2: finite energy of a homeomorphism holomorphic off `K`

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 step 2 of "(C0: SH ⇒ removable.)".

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2, proof of Proposition 1, p. 270: for a
function `f ∈ W^{1,2}` on bounded subsets of `Kᶜ`, "the identity (8) means that on almost every
line `l` parallel to `λ` the total variation of `f` is equal to `∫_{Ω∩U}|∂_λ f|`". The
`W^{1,2}`-input is replaced here by the area formula (node A2,
`volume_image_eq_lintegral_normSq_deriv`), which applies because `e` is *injective* (it is a
homeomorphism): `∫_{Kᶜ ∩ B}|e'|² = area (e '' (Kᶜ ∩ B)) ≤ area (e '' B) < ∞` for bounded `B`.

Let `K ⊆ ℂ` be compact, `e` a homeomorphism of `ℂ` holomorphic on the open set `Kᶜ`, and put
`g := Kᶜ.indicator (deriv e)`. Then:

* `‖x‖ ≤ 1 + ‖x‖²` turns the `L²`-bound into `L¹`-integrability on bounded sets, hence
  `LocallyIntegrable g volume` (hypothesis `hg` of node A4, `differentiable_of_acl`);
* Tonelli (Fubini) turns the planar `L¹`-bound into: for almost every `y`, the restriction of `g`
  to the line at height `y` has finite `L¹`-norm on every bounded interval. This is the "step 2"
  input of the chain argument of blueprint §2 steps 4–5, and it is what makes the right-hand side
  of the a.e. line identity a genuine integral.

Main results: `lintegral_enormSq_deriv_compl_le`, `integrableOn_indicator_deriv_of_isBounded`,
`locallyIntegrable_indicator_deriv`, `ae_lintegral_sliceH_lt_top`,
`ae_forall_lintegral_sliceH_lt_top`.
-/

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

variable {K : Set ℂ}

/-- In `ℝ≥0∞`, `x ≤ 1 + x²` (used to compare the `L¹`- and `L²`-norms of `e'`). -/
lemma le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  by_cases h : x ≤ 1
  · exact h.trans (le_add_right le_rfl)
  · have h1 : 1 ≤ x := le_of_lt (not_le.1 h)
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (pow_two x).symm
      _ ≤ 1 + x ^ 2 := le_add_left le_rfl

/-! ### Step 2a: the area formula bounds the energy of `e` on bounded pieces of `Kᶜ` -/

/-- **Area bound (A2 applied to the open set `Kᶜ ∩ ball 0 M`).** For a homeomorphism `e`
holomorphic on `Kᶜ`,
`∫⁻ z in Kᶜ ∩ ball 0 M, ‖e' z‖² ≤ area (e '' closedBall 0 M)`. -/
theorem lintegral_enormSq_deriv_compl_le {e : ℂ ≃ₜ ℂ} (hK : IsCompact K)
    (he : DifferentiableOn ℂ e Kᶜ) (M : ℝ) :
    ∫⁻ z in Kᶜ ∩ Metric.ball (0 : ℂ) M, ‖deriv e z‖ₑ ^ 2 ≤
      volume (e '' Metric.closedBall (0 : ℂ) M) := by
  have hU : IsOpen (Kᶜ ∩ Metric.ball (0 : ℂ) M) :=
    hK.isClosed.isOpen_compl.inter isOpen_ball
  rw [← volume_image_eq_lintegral_normSq_deriv hU (he.mono inter_subset_left)
    e.injective.injOn]
  exact measure_mono (image_mono (inter_subset_right.trans ball_subset_closedBall))

/-- **Step 2a, `L¹` form.** `∫⁻_{Kᶜ ∩ ball 0 M} ‖e'‖ < ⊤`. -/
theorem lintegral_enorm_deriv_compl_lt_top {e : ℂ ≃ₜ ℂ} (hK : IsCompact K)
    (he : DifferentiableOn ℂ e Kᶜ) (M : ℝ) :
    ∫⁻ z in Kᶜ ∩ Metric.ball (0 : ℂ) M, ‖deriv e z‖ₑ < ⊤ := by
  have hsplit : ∫⁻ z in Kᶜ ∩ Metric.ball (0 : ℂ) M, ‖deriv e z‖ₑ ≤
      ∫⁻ z in Kᶜ ∩ Metric.ball (0 : ℂ) M, (1 + ‖deriv e z‖ₑ ^ 2) :=
    lintegral_mono fun z => le_one_add_sq _
  have hadd : ∫⁻ z in Kᶜ ∩ Metric.ball (0 : ℂ) M, (1 + ‖deriv e z‖ₑ ^ 2) =
      volume (Kᶜ ∩ Metric.ball (0 : ℂ) M) +
        ∫⁻ z in Kᶜ ∩ Metric.ball (0 : ℂ) M, ‖deriv e z‖ₑ ^ 2 := by
    rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
      Measure.restrict_apply MeasurableSet.univ, univ_inter]
  have hfin : volume (Kᶜ ∩ Metric.ball (0 : ℂ) M) < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_right) measure_ball_lt_top
  rw [hadd] at hsplit
  refine lt_of_le_of_lt hsplit (ENNReal.add_lt_top.2 ⟨hfin, ?_⟩)
  refine lt_of_le_of_lt (lintegral_enormSq_deriv_compl_le hK he M) ?_
  exact ((isCompact_closedBall (0 : ℂ) M).image e.continuous).isBounded.measure_lt_top

/-- **Step 2a, integrability form.** For a bounded set `L`, `Kᶜ.indicator (deriv e)` is integrable
on `L`. -/
theorem integrableOn_indicator_deriv_of_isBounded {e : ℂ ≃ₜ ℂ} (hK : IsCompact K)
    (he : DifferentiableOn ℂ e Kᶜ) {L : Set ℂ} (hL : Bornology.IsBounded L) :
    IntegrableOn (Kᶜ.indicator (deriv e)) L volume := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, L ⊆ Metric.closedBall (0 : ℂ) M :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hL
  rw [integrableOn_indicator_iff (hK.isClosed.isOpen_compl).measurableSet]
  have hsub : Kᶜ ∩ L ⊆ Kᶜ ∩ Metric.ball (0 : ℂ) (M + 1) :=
    fun z hz => ⟨hz.1, Metric.closedBall_subset_ball (by linarith) (hM hz.2)⟩
  refine ⟨?_, ?_⟩
  · have hcs : ContinuousOn (deriv e) (Kᶜ ∩ Metric.ball (0 : ℂ) (M + 1)) :=
      (he.deriv hK.isClosed.isOpen_compl).continuousOn.mono inter_subset_left
    have haesm : AEStronglyMeasurable (deriv e)
        (volume.restrict (Kᶜ ∩ Metric.ball (0 : ℂ) (M + 1))) :=
      hcs.aestronglyMeasurable
        ((hK.isClosed.isOpen_compl).measurableSet.inter measurableSet_ball)
    exact haesm.mono_measure (Measure.restrict_mono_set volume hsub)
  · rw [hasFiniteIntegral_iff_enorm]
    exact lt_of_le_of_lt (lintegral_mono_set hsub)
      (lintegral_enorm_deriv_compl_lt_top hK he (M + 1))

/-- **Step 2 (blueprint §2 step 2), first output.** For `K` compact and `e` a homeomorphism of `ℂ`
holomorphic on `Kᶜ`, the function `Kᶜ.indicator (deriv e)` is locally integrable (hypothesis `hg`
of node A4). -/
theorem locallyIntegrable_indicator_deriv {e : ℂ ≃ₜ ℂ} (hK : IsCompact K)
    (he : DifferentiableOn ℂ e Kᶜ) :
    LocallyIntegrable (Kᶜ.indicator (deriv e)) volume := by
  rw [locallyIntegrable_iff]
  exact fun L hL => integrableOn_indicator_deriv_of_isBounded hK he hL.isBounded

/-! ### Step 2b: almost every horizontal line carries an integrable density -/

/-- Slice of `g` along the horizontal line at height `y`. -/
def sliceH (g : ℂ → ℂ) (y : ℝ) : ℝ → ℂ := fun t => g (t + y * I)

/-- **Step 2b (Tonelli / Fubini).** For any rectangle of heights `(-N, N]` and any horizontal
range `(-M, M]`, almost every height in the rectangle carries a slice with finite `L¹`-norm on the
range. -/
theorem ae_lintegral_sliceH_lt_top {e : ℂ ≃ₜ ℂ} (hK : IsCompact K)
    (he : DifferentiableOn ℂ e Kᶜ) (M N : ℕ) :
    ∀ᵐ y : ℝ, y ∈ uIoc (-(N : ℝ)) (N : ℝ) →
      ∫⁻ t in uIoc (-(M : ℝ)) (M : ℝ),
        ‖sliceH (Kᶜ.indicator (deriv e)) y t‖ₑ < ⊤ := by
  set g := Kᶜ.indicator (deriv e) with hg
  set A : Set ℝ := uIoc (-(M : ℝ)) (M : ℝ) with hA
  set B : Set ℝ := uIoc (-(N : ℝ)) (N : ℝ) with hB
  have hgint : LocallyIntegrable g volume := locallyIntegrable_indicator_deriv hK he
  have h2 : IntegrableOn (fun p : ℝ × ℝ => g (p.1 + p.2 * I)) (A ×ˢ B) volume :=
    integrableOn_uIoc_prod_of_locallyIntegrable hgint _ _ _ _
  have hm : AEMeasurable (fun p : ℝ × ℝ => ‖g (p.1 + p.2 * I)‖ₑ)
      ((volume.restrict A).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact AEMeasurable.enorm (AEStronglyMeasurable.aemeasurable h2.aestronglyMeasurable)
  -- Tonelli in the "real part outer" order
  haveI hSA : SFinite (volume.restrict A) := inferInstance
  haveI hSB : SFinite (volume.restrict B) := inferInstance
  have hprod : ∫⁻ x, ∫⁻ y, ‖g (x + y * I)‖ₑ
      ∂(volume.restrict B) ∂(volume.restrict A) < ⊤ := by
    rw [← lintegral_prod (fun p : ℝ × ℝ => ‖g (p.1 + p.2 * I)‖ₑ) hm,
      Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact h2.hasFiniteIntegral
  -- interchange the two iterated integrals
  have hterm : ∫⁻ y, ∫⁻ t, ‖g (t + y * I)‖ₑ
      ∂(volume.restrict A) ∂(volume.restrict B) < ⊤ := by
    rw [← lintegral_lintegral_swap (μ := volume.restrict A) (ν := volume.restrict B)
      (f := fun x y => ‖g (x + y * I)‖ₑ) (by
        show AEMeasurable (fun p : ℝ × ℝ => ‖g (p.1 + p.2 * I)‖ₑ)
          ((volume.restrict A).prod (volume.restrict B))
        exact hm)]
    exact hprod
  have hmeas : AEMeasurable (fun y : ℝ =>
      ∫⁻ t in uIoc (-(M : ℝ)) (M : ℝ), ‖sliceH g y t‖ₑ)
      (volume.restrict (uIoc (-(N : ℝ)) (N : ℝ))) := by
    refine AEMeasurable.lintegral_prod_left (μ := volume.restrict A)
      (ν := volume.restrict B) (f := fun x y => ‖g (x + y * I)‖ₑ) ?_
    show AEMeasurable (fun p : ℝ × ℝ => ‖g (p.1 + p.2 * I)‖ₑ)
      ((volume.restrict A).prod (volume.restrict B))
    exact hm
  have hae : ∀ᵐ y ∂(volume.restrict (uIoc (-(N : ℝ)) (N : ℝ))),
      ∫⁻ t, ‖sliceH g y t‖ₑ ∂(volume.restrict (uIoc (-(M : ℝ)) (M : ℝ))) < ⊤ :=
    ae_lt_top' hmeas (show (∫⁻ y, ∫⁻ t, ‖g (t + y * I)‖ₑ
      ∂(volume.restrict (uIoc (-(M : ℝ)) (M : ℝ)))
      ∂(volume.restrict (uIoc (-(N : ℝ)) (N : ℝ)))) ≠ ⊤ from hterm.ne)
  exact (ae_restrict_iff' measurableSet_uIoc).1 hae

/-- **Step 2 (blueprint §2 step 2), second output.** For almost every `y ∈ ℝ`, the slice of
`g = Kᶜ.indicator (deriv e)` at height `y` has finite `L¹`-norm on every bounded interval. -/
theorem ae_forall_lintegral_sliceH_lt_top {e : ℂ ≃ₜ ℂ} (hK : IsCompact K)
    (he : DifferentiableOn ℂ e Kᶜ) :
    ∀ᵐ y : ℝ, ∀ M : ℕ,
      ∫⁻ t in uIoc (-(M : ℝ)) (M : ℝ),
        ‖sliceH (Kᶜ.indicator (deriv e)) y t‖ₑ < ⊤ := by
  have hbox := ae_lintegral_sliceH_lt_top (K := K) hK he
  rw [ae_all_iff]
  intro M
  rw [ae_iff]
  set S : Set ℝ := {y : ℝ | ¬ (∫⁻ t in uIoc (-(M : ℝ)) (M : ℝ),
    ‖sliceH (Kᶜ.indicator (deriv e)) y t‖ₑ < ⊤)} with hS
  have hcover : S ⊆ ⋃ N : ℕ, S ∩ uIoc (-(N : ℝ)) (N : ℝ) := by
    intro y hy
    obtain ⟨N, hN⟩ := exists_nat_gt |y|
    refine mem_iUnion.2 ⟨N, hy, ?_⟩
    rw [mem_uIoc]
    exact Or.inl ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  refine measure_mono_null hcover (measure_iUnion_null_iff.2 fun N => ?_)
  have h := ae_iff.1 (hbox M N)
  have hset : {a : ℝ | ¬ (a ∈ uIoc (-(N : ℝ)) (N : ℝ) →
      ∫⁻ t in uIoc (-(M : ℝ)) (M : ℝ),
        ‖sliceH (Kᶜ.indicator (deriv e)) a t‖ₑ < ⊤)} =
      uIoc (-(N : ℝ)) (N : ℝ) ∩ S := by
    rw [hS]
    exact Set.ext fun a => by simp only [Set.mem_setOf_eq, Set.mem_inter_iff, not_imp]
  rw [hset, Set.inter_comm] at h
  exact h

end QuantumZipper.JS
