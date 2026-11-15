/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.HullDetGen
import InteractingSLE.Spec.Supplement.BR4aPath
import InteractingSLE.Spec.Supplement.GW2JointKernelProofWord
import InteractingSLE.Spec.Supplement.GW1Base

/-!
# BR4a's hull identity from its relative coupling

Packet PROVE-HULLDET. `Theorem14.BR4aPath.BR4aHullDetStatement` (PROVE-BR4A's named input: the counterflow of the
field recentred at a visited point `v` retraces the original counterflow up to the first visit, with infinite
lifetime) is reduced, by the generic retracing theorem `HullDetGen.ae_retrace_of_hasSafeLaw`, to its **relative
coupling** `BR4aRelCouplingStatement`: the original counterflow read through the target change `w ↦ mob v w` in the
relative capacity clock `clock v` is a globally continuous adapted driver `W` for which the transported field `X` (the
`∞`-chart field of the recentred field) satisfies K2's inputs (S) and (L) with the flow-line marks of `X`'s word, the
seed is admissible, the threshold is never reached, and `W` generates the images `mob v (K'_t)` at the relative
times `clock v W' t`, `t < T_v`.

* `exists_sorted_fn_eq`: every finite piecewise-constant datum has a sorted word;
* `isGFF_of_isFlowLineDriver`: the field of a flow-line driver at angle `0` is a GFF with its datum;
* **`BR4aRelCouplingStatement`** (named input) and **`br4aHullDetStatement_of_relCoupling`**.

R48: the reduction takes Theorems 1.2–1.3 (universes `u` and `0`) as hypotheses; BR4a serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Supp8.HullDetGen

open Restart Restart.FCDet Restart.DomainMarkov Restart.DomainMarkov.K2 Sec2.Assembly Sec7.PocketTraversal
  Theorem14.BR4aPath

/-! ### Words of data and fields of flow-line drivers -/

/-- **Every finite piecewise-constant datum has a sorted word** (positions the increasing enumeration of the jumps,
heights read at the midpoints, `GW2JointKernel.fn_ofMid`). -/
theorem exists_sorted_fn_eq {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    ∃ c : BoundaryWord, c.IsSorted ∧ c.jumps = J ∧ ∀ y ∉ J, c.fn y = b y := by
  set n := J.card with hn
  set e := J.orderEmbOfFin rfl with he
  let p : ℕ → ℝ := fun i => if h : i < n then e ⟨i, h⟩ else 0
  have hp : ∀ i (hi : i < n), p i = e ⟨i, hi⟩ := fun i hi => by simp only [p, hi, ↓reduceDIte]
  have hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j := fun i j hij hj => by
    rw [hp i (lt_of_le_of_lt hij hj), hp j hj]
    exact e.monotone (Fin.mk_le_mk.2 hij)
  have himg : (Finset.range n).image p = J := by
    ext y
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hp i hi]
      exact J.orderEmbOfFin_mem rfl _
    · intro hy
      obtain ⟨⟨i, hi⟩, rfl⟩ : y ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hy
      exact ⟨i, hi, hp i hi⟩
  refine ⟨(n, p, fun j => b (Theorem14.GW2JointKernel.midPt n p j)), hmono, himg, fun y hy => ?_⟩
  rw [← himg] at hy hb
  exact Theorem14.GW2JointKernel.fn_ofMid hmono hb hy

/-- **The field of a flow-line driver at angle `0` is a GFF with its datum** (the conditional-law clause of the
coupling at time `0`, read through `Sec7.StripSysField.isGFFWithBoundaryData_of_flowLineGFF`). -/
theorem isGFF_of_isFlowLineDriver {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hW : IsFlowLineDriver κ b J 0 P h W ζ) : IsGFFWithBoundaryData P h b J := by
  obtain ⟨h', 𝓕, VL, VR, B, htr, hC⟩ := hW
  have hh' : h' = h := funext fun ω => Theorem14.BRLeaf.eq_of_isTranslateAddConst_zero_mul (htr ω)
  subst hh'
  exact Sec7.StripSysField.isGFFWithBoundaryData_of_flowLineGFF hκ hb ⟨hC.2.1, hC.2.2.1⟩

/-- A flow-line driver for a datum is a flow-line driver for any word representing it. -/
theorem isFlowLineDriver_word {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {c : BoundaryWord} (hcJ : c.jumps = J)
    (hcb : ∀ y ∉ J, c.fn y = b y) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hW : IsFlowLineDriver κ b J θ P h W ζ) : IsFlowLineDriver κ c.fn c.jumps θ P h W ζ := by
  subst hcJ
  have hcb' : ∀ y ∉ c.jumps, c.fn y = b y := hcb
  exact Theorem14.GW1.isFlowLineDriver_congr (jumpSet_congr hcb').symm (leftLim_congr hcb').symm
    (rightLim_congr hcb').symm hW

/-! ### The relative coupling and the reduction -/

/-- **Named input: BR4a's relative coupling** (supplement p. 610, Corollary BR4a's proof: "the target change … the
original and transformed stopped histories recover each other"; the target-change form of Astra's follow-up 3, Q3).
In BR4a's setting, for the `∞`-chart field `X` of the recentred field `hv` and any sorted word `c` of `X`: there are a
filtration `𝓗` and a globally continuous `𝓗`-adapted driver `W` from `0` (the original counterflow read through
`mob v` in the relative clock `clock v`) such that the flow-line seed of `c` is admissible, `X` satisfies K2's inputs
(S) and (L) for `W` with the geometric images of the flow-line marks of `c` and the threshold lifetime, and almost
surely the threshold is never reached and `W` generates `mob v (K'_t)` at the relative time `clock v W' t` for every
`t` before the first visit `T_v` of `v`. -/
def BR4aRelCouplingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ v : ℝ, v ≠ 0 → (∀ᵐ ω ∂P, (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => W' t ω) ⊤) →
    ∀ hv : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport (Chart.id.recenter v) 1 0 (chiC κ) (h ω) (hv ω)) →
    ∀ X : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (hv ω) (X ω)) →
    ∀ c : BoundaryWord, c.IsSorted → IsGFFWithBoundaryData P X c.fn c.jumps →
      ∃ (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ), (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧
        StronglyAdapted 𝓗 W ∧
        ¬ ForceWord.ThresholdCondition (flowLineRhoL (16 / κ) c.fn c.jumps 0 0)
          (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) 0 (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) ∧
        HasSafeLaw (16 / κ) (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) P 𝓗
          univ (thr (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) W
            (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0)) W
          (geomLW W fun _ => flowLineXL c.fn c.jumps 0) (geomRW W fun _ => flowLineXR c.fn c.jumps 0) X ∧
        HasSafeMembers P 𝓗 univ
          (thr (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) W
            (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0)) W X ∧
        ∀ᵐ ω ∂P, thr (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) W
            (fun _ => flowLineXL c.fn c.jumps 0) (fun _ => flowLineXR c.fn c.jumps 0) ω = ⊤ ∧
          ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) {(v : ℂ)} →
            fwdHull (fun s : ℝ => W s.toNNReal ω) (clock v (fun s : ℝ => W' s.toNNReal ω) t) =
              mob v '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t

/-- **BR4a's hull identity from its relative coupling** (conditional helper with a distinct name; the named input is
`BR4aRelCouplingStatement`; Theorems 1.2–1.3 at universes `u` and `0` are permitted roots of Theorem 1.4, R48).
Every centred counterflow pair `(Wv, ζv)` of `hv` is a flow-line driver of its `∞`-chart field `X`; the generic
retracing theorem identifies it with the relative coupling's driver `W` (`ζv = thr(W) = ∞`, `Wv = W`), whose hulls
are the images `mob v (K'_t)`. -/
theorem br4aHullDetStatement_of_relCoupling (hR : BR4aRelCouplingStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    BR4aHullDetStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' v hv0 hvis hv htr Wv ζv hcfv
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  obtain ⟨F, hF⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ (16 / κ) 0 hκ'
  obtain ⟨bv, Jv, X, hbv, hXtr, hWv⟩ := hcfv
  obtain ⟨c, hcs, hcJ, hcb⟩ := exists_sorted_fn_eq hbv
  have hX : IsGFFWithBoundaryData P X c.fn c.jumps :=
    (BoundaryWord.isGFFWithBoundaryData_fn_iff hcJ hcb P X).2 (isGFF_of_isFlowLineDriver hκ' hbv hWv)
  have hWvc : IsFlowLineDriver (16 / κ) c.fn c.jumps 0 P X Wv ζv := isFlowLineDriver_word hcJ hcb hWv
  obtain ⟨𝓗, W, hW0, hWc, hWa, hseed, hlaw, hmem, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv0 hvis hv htr X hXtr c hcs hX
  have hret := ae_retrace_of_hasSafeLaw h12p h13 hκ' hF hcs hX hWvc hW0 hWc hWa hseed hlaw hmem
  filter_upwards [hret, hpath] with ω ⟨hζ, hagree⟩ ⟨hthr, hhull⟩
  have hζtop : ζv ω = ⊤ := hζ.trans hthr
  refine ⟨hζtop, fun t ht => ?_⟩
  have hfun : (fun s : ℝ => Wv s.toNNReal ω) = fun s : ℝ => W s.toNNReal ω := by
    funext s
    exact hagree _ (by rw [hζtop]; exact ENNReal.coe_lt_top)
  rw [hfun]
  exact hhull t ht

end InteractingSLE.Supp8.HullDetGen
