/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux97
import InteractingSLE.Spec.Sec7.Prop74
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Sec4.Heights

/-!
# Aux. lemma 97 from Proposition 7.4 and the per-angle identification under one common density

Packet PROVE-AUX97-B. Source: Aux. lemma 97 and its proof (`source/spec/p289-336.md` L550–L576, pp. 326–327).

The proof of Aux. lemma 97 has two parts.

1. **Per-angle identification under one common density** (pp. 326–327, "Here are that identification's details"). Put
   `ĥ` = a GFF with the two-height data `b₋` on `ℝ₋`, `b₊` on `ℝ₊` (`prop74Data (−b₋) b₊`), `q` = the difference of the
   harmonic means of `h` and `ĥ` (zero on `(−R, R)`), `f = q · cutoff` (`f = q` near `B̄(0, s)`, `r < s < R`), `Z` the
   Cameron–Martin density for adding `f`. Under the weighted law the recoded field `h + f − q` is a GFF with the
   two-height data, and for each angle the restricted joint field/path law through the exit of `B̄(0, r)` is the
   reference one (Theorem 2.4's local rational-function argument, the uniqueness of the integrated driving equations,
   the retained conditional Gaussian law, Aux. lemma 109); with the reference determination (Proposition 7.3) the actual
   stopped path is the stopped reference flow line of the recoded field. The density is common to both angles because
   `θχ` shifts both harmonic means equally.
2. **Transfer of Proposition 7.4** ("The density `Z_U` is strictly positive. Hence the probability-one ordering
   assertion supplied for the reference pair by Proposition 7.4 transfers to the actual pair"). The angle hypotheses of
   Proposition 7.4 for the reference data are exactly the no-threshold hypotheses of Aux. lemma 97 (`prop74_angles`).

Part 1 is the named input **`Aux97LocalIdentStatement`**, in pathwise form: one probability measure `Q` equivalent to
`P` and one field `X` that is a GFF with the two-height data under `Q`, both chosen before the angle, such that every
flow line `η` of `h` from `0` at a non-threshold angle agrees, `Q`-almost surely up to its exit from `B̄(0, r)`, with
some flow line of `X` under `Q` at the same angle. (From the source's per-angle law identity it follows with
Proposition 7.3's common determining function; see the handoff.) Part 2 is proved here:

* `sum_filter_flowLineXL_eq_zero_seed`, `sum_filter_flowLineXR_eq_zero_seed`: the only flow-line mark at the seed is the
  seed mark, so the threshold sums at the initial state are the two seed weights;
* `seedWeights_gt_of_not_threshold`: no threshold ⇒ both seed weights exceed `−2`;
* **`prop74_angles`**: the angle hypotheses of Proposition 7.4 for `prop74Data (−b₋) b₊` from the no-threshold
  hypotheses;
* `HasOrderedProperCompletions.congr_prefix`: the W0 relation depends only on the two prefixes;
* **`aux97Statement_of_localIdent`**: `Prop74OrderStatement → Aux97LocalIdentStatement → Aux97Statement`.

Conditional helper; it replaces no source theorem. Neither named input is proved here (see the handoff
`planning/handoffs/PROVE-AUX97-B.md`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open PiecewiseConstantBoundaryData (leftLim rightLim)

/-! ### The seed weights of a flow line from `0` -/

/-- The only left mark of the flow-line word at position `0` is the seed mark `0⁻`: the threshold sum on the left at the
initial state is the left seed weight `−(b(0⁻) + θχ)/λ − 1`. -/
theorem sum_filter_flowLineXL_eq_zero_seed (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => flowLineXL b jumps 0 i = 0), flowLineRhoL κ b jumps 0 θ i) =
      -(leftLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_succ _).trans ?_
  rw [Finset.sum_eq_zero, add_zero]
  · exact ite_eq_left rfl
  intro i _
  have hmem := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet b jumps).filter (· < 0)) rfl
    (Fin.rev i)
  rw [Finset.mem_filter] at hmem
  refine ite_eq_right_iff.2 fun hi => absurd ?_ hmem.2.ne
  simp only [flowLineXL, sub_zero] at hi
  exact hi

/-- The only right mark of the flow-line word at position `0` is the seed mark `0⁺`: the threshold sum on the right at
the initial state is the right seed weight `(b(0⁺) + θχ)/λ − 1`. -/
theorem sum_filter_flowLineXR_eq_zero_seed (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => flowLineXR b jumps 0 i = 0), flowLineRhoR κ b jumps 0 θ i) =
      (rightLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_succ _).trans ?_
  rw [Finset.sum_eq_zero, add_zero]
  · exact ite_eq_left rfl
  intro i _
  have hmem := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet b jumps).filter (0 < ·)) rfl i
  rw [Finset.mem_filter] at hmem
  refine ite_eq_right_iff.2 fun hi => absurd ?_ hmem.2.ne'
  simp only [flowLineXR, sub_zero] at hi
  exact hi

/-- **No immediate continuation threshold at the seed** means that both seed weights of the flow-line word exceed
`−2`. -/
theorem seedWeights_gt_of_not_threshold {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}
    (hT : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ) (flowLineRhoR κ b jumps 0 θ) 0
      (flowLineXL b jumps 0) (flowLineXR b jumps 0)) :
    -2 < -(leftLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 ∧
      -2 < (rightLim b 0 + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  unfold ForceWord.ThresholdCondition at hT
  rw [sum_filter_flowLineXL_eq_zero_seed, sum_filter_flowLineXR_eq_zero_seed, not_or, not_le, not_le] at hT
  exact hT

/-- **The angle hypotheses of Proposition 7.4 from Aux. lemma 97's hypotheses.** For `0 < κ < 4` and data equal to `b₋`
just left of `0` and to `b₊` just right of `0`: if neither the angle-`θ₁` nor the angle-`θ₂` flow line from `0` is at
an immediate continuation threshold, then `−(λ + b₊)/χ < θ₁` and `θ₂ < (−b₋ + λ)/χ`, which are Proposition 7.4's
hypotheses for the data `prop74Data (−b₋) b₊` (the right seed weight of `η_{θ₁}` and the left seed weight of `η_{θ₂}`
exceed `−2`). -/
theorem prop74_angles {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {R bm bp : ℝ}
    (hR : 0 < R) (hbm : ∀ y ∈ Ioo (-R) 0, b y = bm) (hbp : ∀ y ∈ Ioo 0 R, b y = bp) {θ₁ θ₂ : ℝ}
    (hT₁ : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ₁) (flowLineRhoR κ b jumps 0 θ₁) 0
      (flowLineXL b jumps 0) (flowLineXR b jumps 0))
    (hT₂ : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ₂) (flowLineRhoR κ b jumps 0 θ₂) 0
      (flowLineXL b jumps 0) (flowLineXR b jumps 0)) :
    -(sleLambda κ + bp) / QuantumZipper.chiC κ < θ₁ ∧
      θ₂ < (-bm + sleLambda κ) / QuantumZipper.chiC κ := by
  have hl : leftLim b 0 = bm := Sec4.leftLim_eq_of_forall (neg_lt_zero.2 hR) hbm
  have hr : rightLim b 0 = bp := Sec4.rightLim_eq_of_forall hR hbp
  have hlam := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  obtain ⟨-, h1⟩ := seedWeights_gt_of_not_threshold hT₁
  obtain ⟨h2, -⟩ := seedWeights_gt_of_not_threshold hT₂
  rw [hr] at h1
  rw [hl] at h2
  -- `(b₊ + θ₁χ)/λ > −1` and `−(b₋ + θ₂χ)/λ > −1`
  have h1' : -sleLambda κ < bp + θ₁ * QuantumZipper.chiC κ := by
    have : -1 < (bp + θ₁ * QuantumZipper.chiC κ) / sleLambda κ := by linarith
    rwa [lt_div_iff₀ hlam, neg_one_mul] at this
  have h2' : bm + θ₂ * QuantumZipper.chiC κ < sleLambda κ := by
    have : -1 < -(bm + θ₂ * QuantumZipper.chiC κ) / sleLambda κ := by linarith
    rw [lt_div_iff₀ hlam, neg_one_mul, neg_lt_neg_iff] at this
    exact this
  constructor
  · rw [div_lt_iff₀ hχ]
    linarith
  · rw [lt_div_iff₀ hχ]
    linarith

/-! ### The W0 relation depends only on the prefixes -/

/-- **Prefix congruence of the W0 relation**: `HasOrderedProperCompletions α a β c` depends only on `α` on `[0, a]` and
`β` on `[0, c]`. -/
theorem HasOrderedProperCompletions.congr_prefix {α α' β β' : ℝ≥0 → ℂ} {a c : ℝ≥0}
    (hα : ∀ t ≤ a, α t = α' t) (hβ : ∀ t ≤ c, β t = β' t) (h : HasOrderedProperCompletions α a β c) :
    HasOrderedProperCompletions α' a β' c := by
  obtain ⟨α₁, β₁, ⟨h1, h2, h3, h4, h5⟩, ⟨g1, g2, g3, g4, g5⟩, hsub⟩ := h
  exact ⟨α₁, β₁, ⟨h1, h2, h3, h4, fun t ht => (h5 t ht).trans (hα t ht)⟩,
    ⟨g1, g2, g3, g4, fun t ht => (g5 t ht).trans (hβ t ht)⟩, hsub⟩

/-! ### The per-angle identification (named input) and the reduction -/

/-- **Named input: Aux. lemma 97's per-angle identification under one common density** (p. 327, "Here are that
identification's details", in pathwise form). Let `0 < κ < 4`, `b` finite piecewise-constant data equal to `b₋` on
`(−R, 0)` and to `b₊` on `(0, R)`, `0 < r < R`, and `h` a GFF with data `b` under `P`. There are one probability
measure `Q` equivalent to `P` (the weighting by the strictly positive Cameron–Martin density of the cut-off mean
difference) and one field `X` (the recoded field `h + f − q`) which is a GFF with the two-height data
`prop74Data (−b₋) b₊` under `Q`, both chosen before the angle, such that for every angle `θ` at which the flow line from
`0` is not at an immediate continuation threshold, every angle-`θ` flow line `η` of `h` from `0` agrees, `Q`-almost
surely up to its exit from `B̄(0, r)` (and strictly before its lifetime), with some angle-`θ` flow line `η'` of `X`
under `Q`, which is alive there.

In the source this is the identification of the restricted joint field/path law of each angle with the reference law
under the weighting (Theorem 2.4's local rational-function argument, integrated driving uniqueness, the retained
conditional Gaussian law, Aux. lemma 109), combined with the reference determination (Proposition 7.3: the reference
curve is one Borel function of its field in every coupling). -/
def Aux97LocalIdentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ R bm bp : ℝ, 0 < R → (∀ y ∈ Ioo (-R) 0, b y = bm) → (∀ y ∈ Ioo 0 R, b y = bp) →
    ∀ r : ℝ, 0 < r → r < R →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∃ (Q : Measure Ω) (X : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsProbabilityMeasure Q ∧ P ≪ Q ∧ Q ≪ P ∧
      IsGFFWithBoundaryData Q X (prop74Data (-bm) bp) {0} ∧
      ∀ θ : ℝ, ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ) (flowLineRhoR κ b jumps 0 θ) 0
          (flowLineXL b jumps 0) (flowLineXR b jumps 0) →
        ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 θ P h η ζ →
        ∃ (η' : Ω → ℝ≥0 → ℂ) (ζ' : Ω → ℝ≥0∞), IsFlowLine κ (prop74Data (-bm) bp) {0} 0 θ Q X η' ζ' ∧
          ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ballExit r (η ω) → (t : ℝ≥0∞) < ζ ω →
            (t : ℝ≥0∞) < ζ' ω ∧ η ω t = η' ω t

/-- **Aux. lemma 97 from Proposition 7.4 and the per-angle identification** (p. 327, last paragraph): under `Q` the two
actual stopped prefixes are prefixes of two flow lines of the one field `X`, whose ordering is Proposition 7.4 (with
the angle hypotheses from `prop74_angles`); the W0 relation depends only on the prefixes, and `P ≪ Q` moves the
`Q`-almost sure ordering to `P`. -/
theorem aux97Statement_of_localIdent (h74 : Prop74OrderStatement.{u}) (hid : Aux97LocalIdentStatement.{u}) :
    Aux97Statement.{u} := by
  intro κ hκ hκ4 b J hb R bm bp hR hbm hbp θ₁ θ₂ hθ hT₁ hT₂ r hr hrR Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨Q, X, hQ, hPQ, -, hX, hloc⟩ := hid κ hκ hκ4 b J hb R bm bp hR hbm hbp r hr hrR P h hh
  have := hQ
  obtain ⟨η₁', ζ₁', hη₁', hag₁⟩ := hloc θ₁ hT₁ η₁ ζ₁ hη₁
  obtain ⟨η₂', ζ₂', hη₂', hag₂⟩ := hloc θ₂ hT₂ η₂ ζ₂ hη₂
  obtain ⟨hA₁, hA₂⟩ := prop74_angles hκ hκ4 hR hbm hbp hT₁ hT₂
  have hord := h74 κ hκ hκ4 (-bm) bp θ₁ θ₂ hθ hA₁ hA₂ Q X hX η₁' η₂' ζ₁' ζ₂' hη₁' hη₂'
  refine hPQ.ae_le ?_
  filter_upwards [hord, hag₁, hag₂] with ω hω g₁ g₂
  intro a c ha ha' hc hc'
  refine HasOrderedProperCompletions.congr_prefix (α := η₁' ω) (β := η₂' ω) ?_ ?_
    (hω a c (g₁ a ha ha').1 (g₂ c hc hc').1)
  · intro t ht
    have ht' : (t : ℝ≥0∞) ≤ a := ENNReal.coe_le_coe.2 ht
    exact (g₁ t (le_trans ht' ha) (lt_of_le_of_lt ht' ha')).2.symm
  · intro t ht
    have ht' : (t : ℝ≥0∞) ≤ c := ENNReal.coe_le_coe.2 ht
    exact (g₂ t (le_trans ht' hc) (lt_of_le_of_lt ht' hc')).2.symm

end Sec7

end InteractingSLE
