/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchModel
import InteractingSLE.Spec.Supplement.W5CommonSeedShift

/-!
# Theorem 1.5's leaf 3: the stopped (Det) at a random seed, by recentring

Packet PROVE-T15-ORDDET4. The first continuation of a retained pair starts at the chart point `τ = tipPos` of the
first tip, a random seed, while the stopped K2 runs on standard Borel models whose continuation starts at `0` (the
model's trace is the chart path recentred at `τ`, its field the recentred chart field `h(· + τ)`, its word the
recentred word `shiftW τ c`). This file proves the model-side half of the step from K2 to (Det):

* `IsFlowTypeAt`: the flow-line type of a word from a seed `x`; **`isFlowTypeAt_of_shiftW`**: the type of the
  recentred word `shiftW x c` from `0` is the type of `c` from `x` (the positions, weights and numbers of marks of the
  frozen flow-line word are translation covariant);
* `isTranslateAddConst_flowField_neg`: if `X = H + a` (seed `0`) then `X = (flowField (−x) 0 H)(· + x) + a`;
* **`ae_codeMatch_of_regular_coupling_seed`**: the R79 stopped (Det) of `RetMatch.ae_codeMatch_of_regular_coupling`
  for a coupling of the flow-line type of `(c, x)`, with the canonical code read at the seed `x`;
* `seedMatchSet` and its measurability: the dyadic stopped match of `γ + x` with a code at a parameter `(c, x)`;
* **`ae_codeMatch_of_model_historyRule_seed`**: on a stopped model with a measurable Galmarino history rule (the
  input of `RetMatch.ae_codeMatch_of_model_historyRule`), for every seed `s` measurable at time `0`, almost surely
  the model's trace shifted by `s` is the canonical code of the un-recentred word `shiftW (−s) word` and field
  `flowField (−s) 0 field` from the seed `s`, up to the model's lifetime.

R43/R48: Theorems 1.2–1.3 (a canonical flow code, `Exist.Theorem13Statement`) are used; this serves Theorem 1.5 only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.RLC.OrdLate

open Restart Restart.RetAux79 Restart.StoppedExtend Restart.StoppedExtendWF Restart.FCDet
open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79 Restart.ConverseBefore
open LawUnique Sec2.Assembly Sec7.PocketTraversal
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### The flow-line type of a word from a seed -/

section FlowType

variable {nL nR : ℕ}

/-- **The flow-line type of a boundary word from the seed `x`**: the angle-`θ` flow-line word of `c` from `x` has `nL`
left and `nR` right marks, positions `xL`, `xR` (relative to `x`) and weights `ρL`, `ρR` (after the identification of
the index types). At `x = 0` this is `FCDet.IsFlowType`. -/
def IsFlowTypeAt (κ θ : ℝ) (c : BoundaryWord) (x : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  ∃ (eL : flowLineNL c.fn c.jumps x = nL) (eR : flowLineNR c.fn c.jumps x = nR),
    (fun i => xL (Fin.cast eL i)) = flowLineXL c.fn c.jumps x ∧
    (fun j => xR (Fin.cast eR j)) = flowLineXR c.fn c.jumps x ∧
    (fun i => ρL (Fin.cast eL i)) = flowLineRhoL κ c.fn c.jumps x θ ∧
    (fun j => ρR (Fin.cast eR j)) = flowLineRhoR κ c.fn c.jumps x θ

theorem fn_shiftW_eq (x : ℝ) (c : BoundaryWord) :
    (Exist.StagedLaw.BoundaryWord.shiftW x c).fn = fun y => c.fn (y + x) :=
  funext (Exist.StagedLaw.BoundaryWord.fn_shiftW x c)

theorem jumpSet_shiftW (x : ℝ) (c : BoundaryWord) :
    jumpSet (Exist.StagedLaw.BoundaryWord.shiftW x c).fn (Exist.StagedLaw.BoundaryWord.shiftW x c).jumps =
      (jumpSet c.fn c.jumps).image (· - x) := by
  rw [fn_shiftW_eq, Exist.StagedLaw.BoundaryWord.jumps_shiftW, Supp9.jumpSet_comp_add]

theorem leftLim_shiftW (x : ℝ) (c : BoundaryWord) :
    leftLim (Exist.StagedLaw.BoundaryWord.shiftW x c).fn = fun z => leftLim c.fn (z + x) := by
  rw [fn_shiftW_eq]
  exact funext (Exist.leftLim_comp_add c.fn x)

theorem rightLim_shiftW (x : ℝ) (c : BoundaryWord) :
    rightLim (Exist.StagedLaw.BoundaryWord.shiftW x c).fn = fun z => rightLim c.fn (z + x) := by
  rw [fn_shiftW_eq]
  exact funext (Exist.rightLim_comp_add c.fn x)

theorem flowLineNL_eq_of_jumpSet {b b' : ℝ → ℝ} {J J' : Finset ℝ} {x : ℝ}
    (hS : jumpSet b' J' = (jumpSet b J).image (· - x)) : flowLineNL b J x = flowLineNL b' J' 0 := by
  unfold flowLineNL
  rw [hS, Supp9.card_filter_lt_image_sub]

theorem flowLineNR_eq_of_jumpSet {b b' : ℝ → ℝ} {J J' : Finset ℝ} {x : ℝ}
    (hS : jumpSet b' J' = (jumpSet b J).image (· - x)) : flowLineNR b J x = flowLineNR b' J' 0 := by
  unfold flowLineNR
  rw [hS, Supp9.card_filter_gt_image_sub]

theorem consXL_image {S S' : Finset ℝ} {x : ℝ} (hS : S' = S.image (· - x))
    (e : (S.filter (· < x)).card + 1 = (S'.filter (· < 0)).card + 1) (i : Fin ((S.filter (· < x)).card + 1)) :
    (Fin.cons 0 fun i => (S'.filter (· < 0)).orderEmbOfFin rfl (Fin.rev i) - 0 :
        Fin ((S'.filter (· < 0)).card + 1) → ℝ) (Fin.cast e i) =
      (Fin.cons 0 fun i => (S.filter (· < x)).orderEmbOfFin rfl (Fin.rev i) - x :
        Fin ((S.filter (· < x)).card + 1) → ℝ) i := by
  subst hS
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ, Supp9.orderEmbOfFin_filter_lt_image_sub, sub_zero,
      Fin.cast_rev, Fin.cast_cast, Fin.cast_eq_self]

theorem flowLineXL_eq_of_jumpSet {b b' : ℝ → ℝ} {J J' : Finset ℝ} {x : ℝ}
    (hS : jumpSet b' J' = (jumpSet b J).image (· - x)) (e : flowLineNL b J x = flowLineNL b' J' 0)
    (i : Fin (flowLineNL b J x)) : flowLineXL b' J' 0 (Fin.cast e i) = flowLineXL b J x i :=
  consXL_image hS e i

theorem consXR_image {S S' : Finset ℝ} {x : ℝ} (hS : S' = S.image (· - x))
    (e : (S.filter (x < ·)).card + 1 = (S'.filter (0 < ·)).card + 1) (i : Fin ((S.filter (x < ·)).card + 1)) :
    (Fin.cons 0 fun i => (S'.filter (0 < ·)).orderEmbOfFin rfl i - 0 :
        Fin ((S'.filter (0 < ·)).card + 1) → ℝ) (Fin.cast e i) =
      (Fin.cons 0 fun i => (S.filter (x < ·)).orderEmbOfFin rfl i - x :
        Fin ((S.filter (x < ·)).card + 1) → ℝ) i := by
  subst hS
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ, Supp9.orderEmbOfFin_filter_gt_image_sub, sub_zero,
      Fin.cast_cast, Fin.cast_eq_self]

theorem consRhoL_image {S S' : Finset ℝ} {x : ℝ} {L R L' R' : ℝ → ℝ} (hS : S' = S.image (· - x))
    (hL : L' = fun z => L (z + x)) (hR : R' = fun z => R (z + x)) (a : ℝ) (lam : ℝ)
    (e : (S.filter (· < x)).card + 1 = (S'.filter (· < 0)).card + 1) (i : Fin ((S.filter (· < x)).card + 1)) :
    (Fin.cons (-(L' 0 + a) / lam - 1) fun i =>
        let y := (S'.filter (· < 0)).orderEmbOfFin rfl (Fin.rev i)
        (R' y - L' y) / lam : Fin ((S'.filter (· < 0)).card + 1) → ℝ) (Fin.cast e i) =
      (Fin.cons (-(L x + a) / lam - 1) fun i =>
        let y := (S.filter (· < x)).orderEmbOfFin rfl (Fin.rev i)
        (R y - L y) / lam : Fin ((S.filter (· < x)).card + 1) → ℝ) i := by
  subst hS hL hR
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cast_zero, Fin.cons_zero, zero_add]
  · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ]
    simp only [Supp9.orderEmbOfFin_filter_lt_image_sub, sub_add_cancel, Fin.cast_rev, Fin.cast_cast,
      Fin.cast_eq_self]

theorem consRhoR_image {S S' : Finset ℝ} {x : ℝ} {L R L' R' : ℝ → ℝ} (hS : S' = S.image (· - x))
    (hL : L' = fun z => L (z + x)) (hR : R' = fun z => R (z + x)) (a : ℝ) (lam : ℝ)
    (e : (S.filter (x < ·)).card + 1 = (S'.filter (0 < ·)).card + 1) (i : Fin ((S.filter (x < ·)).card + 1)) :
    (Fin.cons ((R' 0 + a) / lam - 1) fun i =>
        let y := (S'.filter (0 < ·)).orderEmbOfFin rfl i
        (R' y - L' y) / lam : Fin ((S'.filter (0 < ·)).card + 1) → ℝ) (Fin.cast e i) =
      (Fin.cons ((R x + a) / lam - 1) fun i =>
        let y := (S.filter (x < ·)).orderEmbOfFin rfl i
        (R y - L y) / lam : Fin ((S.filter (x < ·)).card + 1) → ℝ) i := by
  subst hS hL hR
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cast_zero, Fin.cons_zero, zero_add]
  · rw [Fin.cast_succ_eq, Fin.cons_succ, Fin.cons_succ]
    simp only [Supp9.orderEmbOfFin_filter_gt_image_sub, sub_add_cancel, Fin.cast_cast, Fin.cast_eq_self]

theorem isFlowTypeAt_of_shiftW {nL nR : ℕ} {κ θ : ℝ} {c : BoundaryWord} {x : ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h : FCDet.IsFlowType κ θ (Exist.StagedLaw.BoundaryWord.shiftW x c) xL xR ρL ρR) :
    IsFlowTypeAt κ θ c x xL xR ρL ρR := by
  obtain ⟨eL, eR, h1, h2, h3, h4⟩ := h
  have hS := jumpSet_shiftW x c
  have eNL := flowLineNL_eq_of_jumpSet hS
  have eNR := flowLineNR_eq_of_jumpSet hS
  refine ⟨eNL.trans eL, eNR.trans eR, funext fun i => ?_, funext fun j => ?_, funext fun i => ?_,
    funext fun j => ?_⟩
  · have hh := congrFun h1 (Fin.cast eNL i)
    simp only [Fin.cast_cast] at hh
    rw [hh]
    exact consXL_image hS eNL i
  · have hh := congrFun h2 (Fin.cast eNR j)
    simp only [Fin.cast_cast] at hh
    rw [hh]
    exact consXR_image hS eNR j
  · have hh := congrFun h3 (Fin.cast eNL i)
    simp only [Fin.cast_cast] at hh
    rw [hh]
    exact consRhoL_image hS (leftLim_shiftW x c) (rightLim_shiftW x c) _ _ eNL i
  · have hh := congrFun h4 (Fin.cast eNR j)
    simp only [Fin.cast_cast] at hh
    rw [hh]
    exact consRhoR_image hS (leftLim_shiftW x c) (rightLim_shiftW x c) _ _ eNR j

end FlowType

/-! ### The stopped (Det) of a coupling of the flow-line type from a seed -/

/-- **The R79 stopped (Det) from a seed** (`RetMatch.ae_codeMatch_of_regular_coupling` with the seed `x` in place of
`0`): a stopped hull coupling of the field `X = Hc(· + x) + θχ` with the flow-line word of `(c, x)`, stopped at a
measurable Galmarino history rule which is regular at the stop, with `γ − x` its generating trace through the stop,
has `γ` equal to the canonical code of `(c, x)` and `Hc` through the stop (Aux. lemma 54 in its R79 form, Theorem 1.3
and the determination clause of the canonical code at the seed `x`). -/
theorem ae_codeMatch_of_regular_coupling_seed
    {κ θ : ℝ} (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) {c : BoundaryWord} {x : ℝ}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hord : IsOrderedForceWord xL xR) (htype : IsFlowTypeAt κ θ c x xL xR ρL ρR)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    (hXH : ∀ ω, IsTranslateAddConst x (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (hSC : IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V X)
    {R : HistorySpace nL nR → ℝ≥0∞} (hRm : Measurable R) (hRg : IsHistGalmarino R)
    (hR : ∀ᵐ ω ∂P, V ω = R (killedHistory W VL VR V ω))
    (hreg : Aux54.IsRegularStop ρL ρR P W VL VR V)
    {γ : Ω → ℝ≥0 → ℂ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (V ω) (fun t => γ ω t - x)) :
    ∀ᵐ ω ∂P, V ω ≤ (Fc ((c, x), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω →
        γ ω t = decPath (Fc ((c, x), Hc ω)) t := by
  obtain ⟨C, mC, K, hK, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ :=
    Aux54.stoppedHullExtendRStatement hκ xL xR ρL ρR hord R hRm hRg
      P 𝓕 W VL VR B V X hSC hR hreg
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := htype
  have hSC' := StoppedK2.isStoppedHullCoupling_cast eL eR hSC
  have hC' := isOptionalHullCoupling_cast eL eR hC
  rw [hxL, hxR, hρL, hρR] at hSC' hC'
  have hag' : ∀ᵐ p ∂(P ⊗ₘ K), V p.1 ≤ ζ' p ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ' p →
        W' t p = W t p.1 ∧
          (∀ i, VL' (Fin.cast eL i) t p = VL (Fin.cast eL i) t p.1) ∧
          ∀ j, VR' (Fin.cast eR j) t p = VR (Fin.cast eR j) t p.1 := by
    filter_upwards [hag] with p hp
    exact ⟨hp.1, fun t ht ht' =>
      ⟨(hp.2 t ht ht').1, fun i => (hp.2 t ht ht').2.1 _,
        fun j => (hp.2 t ht ht').2.2 _⟩⟩
  exact ae_of_ae_compProd_fst (K := K)
    (ae_stopMatch_on_extension (G := fun f => Fc ((c, x), f))
      h13 hκ (IsCanonicalFlowCode.isFlowDet hFc c x) hXH
      hSC'.1.ae_path htr (Measure.fst_compProd P K) hC' hag')

/-! ### Recentred words and fields -/

theorem shiftW_shiftW_neg (x : ℝ) (c : BoundaryWord) :
    Exist.StagedLaw.BoundaryWord.shiftW x (Exist.StagedLaw.BoundaryWord.shiftW (-x) c) = c := by
  unfold Exist.StagedLaw.BoundaryWord.shiftW
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
  change c.2.1 i - -x - x = c.2.1 i
  ring

theorem shiftW_neg_shiftW (x : ℝ) (c : BoundaryWord) :
    Exist.StagedLaw.BoundaryWord.shiftW (-x) (Exist.StagedLaw.BoundaryWord.shiftW x c) = c := by
  unfold Exist.StagedLaw.BoundaryWord.shiftW
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
  change c.2.1 i - x - -x = c.2.1 i
  ring

theorem flowField_neg_flowField (x : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Exist.flowField (-x) 0 (Exist.flowField x 0 f) = f := by
  have h := Sec7.SideHeight.flowField_neg_neg (-x) f
  rwa [neg_neg, neg_neg] at h

/-- **Un-recentring a seed-`0` translate**: if `X = H + a` (seed `0`), then `X = H'(· + x) + a` for the field
`H' = flowField (−x) 0 H` (`H'(·) = H(· − x)`). -/
theorem isTranslateAddConst_flowField_neg {x a : ℝ} {H X : DistOn upperHalfPlaneOpens}
    (h : IsTranslateAddConst 0 a H X) : IsTranslateAddConst x a (Exist.flowField (-x) 0 H) X := by
  intro φ φ' hφ
  rw [h φ' φ' fun z => by rw [Complex.ofReal_zero, add_zero], Exist.flowField_apply, zero_mul, add_zero]
  have e : Chart.pushTest (Exist.isConformal_shiftChart (-x)) φ = φ' := by
    ext z
    rw [Exist.pushTest_shiftChart_apply, hφ, Complex.ofReal_neg, sub_neg_eq_add]
  rw [e]

/-! ### The seeded stopped match -/

/-- The dyadic form of the stopped match of the path `η + x` with a code at a parameter `(c, x)`. -/
def seedMatchSet {C S : Type*} (G : (C × ℝ) × S → (PCode × PCode) × ℝ≥0∞) (η : S → ℝ≥0 → ℂ) (e : S → ℝ≥0∞) :
    Set ((C × ℝ) × S) :=
  {p | e p.2 ≤ (G p).2 ∧ ∀ n k : ℕ, (dyad n k : ℝ≥0∞) ≤ e p.2 →
    η p.2 (dyad n k) + p.1.2 = decPath (G p) (dyad n k)}

theorem measurableSet_seedMatchSet {C S : Type*} [MeasurableSpace C] [MeasurableSpace S]
    {G : (C × ℝ) × S → (PCode × PCode) × ℝ≥0∞} (hG : Measurable G) {η : S → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun s => η s t) {e : S → ℝ≥0∞} (he : Measurable e) :
    MeasurableSet (seedMatchSet G η e) := by
  have he' : Measurable fun p : (C × ℝ) × S => e p.2 := he.comp measurable_snd
  have hl : MeasurableSet {p : (C × ℝ) × S | e p.2 ≤ (G p).2} := measurableSet_le he' (measurable_snd.comp hG)
  have hd : ∀ n k : ℕ, MeasurableSet {p : (C × ℝ) × S | (dyad n k : ℝ≥0∞) ≤ e p.2 →
      η p.2 (dyad n k) + p.1.2 = decPath (G p) (dyad n k)} := fun n k => by
    have h1 : MeasurableSet {p : (C × ℝ) × S | (dyad n k : ℝ≥0∞) ≤ e p.2} := measurableSet_le measurable_const he'
    have h2 : MeasurableSet {p : (C × ℝ) × S | η p.2 (dyad n k) + p.1.2 = decPath (G p) (dyad n k)} :=
      measurableSet_eq_fun (((hη _).comp measurable_snd).add
        (Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst)))
        ((measurable_decPath _).comp hG)
    have e : {p : (C × ℝ) × S | (dyad n k : ℝ≥0∞) ≤ e p.2 →
        η p.2 (dyad n k) + p.1.2 = decPath (G p) (dyad n k)} =
        {p : (C × ℝ) × S | (dyad n k : ℝ≥0∞) ≤ e p.2}ᶜ ∪
          {p : (C × ℝ) × S | η p.2 (dyad n k) + p.1.2 = decPath (G p) (dyad n k)} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    exact h1.compl.union h2
  have e : seedMatchSet G η e = {p : (C × ℝ) × S | e p.2 ≤ (G p).2} ∩ ⋂ n : ℕ, ⋂ k : ℕ,
      {p : (C × ℝ) × S | (dyad n k : ℝ≥0∞) ≤ e p.2 →
        η p.2 (dyad n k) + p.1.2 = decPath (G p) (dyad n k)} := by
    ext p
    simp only [seedMatchSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e]
  exact hl.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => hd n k)

/-- On the seeded dyadic match set, a path continuous on `[0, e]`, shifted by the seed, is the decoded code on
`[0, e]`. -/
theorem seedMatch_of_mem {C S : Type*} {G : (C × ℝ) × S → (PCode × PCode) × ℝ≥0∞} {η : S → ℝ≥0 → ℂ}
    {e : S → ℝ≥0∞} {p : (C × ℝ) × S} (hc : ContinuousOn (η p.2) {t | (t : ℝ≥0∞) ≤ e p.2})
    (hp : p ∈ seedMatchSet G η e) :
    e p.2 ≤ (G p).2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.2 → η p.2 t + p.1.2 = decPath (G p) t := by
  obtain ⟨hle, hd⟩ := hp
  exact ⟨hle, eqOn_of_dyad (hc.add continuousOn_const)
    ((continuousOn_decPath (G p)).mono fun t ht => le_trans ht hle) hd⟩

/-- The code at a parameter `(c, x)` of the un-recentred field `flowField (−x) 0 (f p)` is measurable. -/
theorem measurable_seedCode {S : Type*} [MeasurableSpace S] {f : S → DistOn upperHalfPlaneOpens} (hf : Measurable f)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞} (hFc : Measurable Fc) :
    Measurable fun q : (BoundaryWord × ℝ) × S => Fc (q.1, Exist.flowField (-q.1.2) 0 (f q.2)) := by
  have h1 : Measurable fun q : (BoundaryWord × ℝ) × S => ((-q.1.2, f q.2) : ℝ × DistOn upperHalfPlaneOpens) :=
    (measurable_snd.comp measurable_fst).neg.prodMk (hf.comp measurable_snd)
  have h2 := (Restart.measurable_flowField_uncurry 0).comp h1
  have h3 := hFc.comp (measurable_fst.prodMk h2)
  exact h3

/-! ### The seeded model consumer -/

/-- **The stopped (Det) on a model, from a random seed** (`RetMatch.ae_codeMatch_of_model_historyRule` with the
seed `s` read at time `0`): if the model's stop is a measurable Galmarino history rule, then for every seed `s`
measurable at time `0`, almost surely the model's trace shifted by `s` is, up to the model's lifetime, the decoded
canonical code of the un-recentred word `shiftW (−s) word` and field `flowField (−s) 0 field` from the seed `s`.

Proof: the model's two announcing sequences give, under the regular conditional law given time `0` on the product
with an auxiliary Gaussian space, a stopped hull coupling of the model's shifted field; at a frozen sample `p₀` the
seed `x = s p₀` and the word are constants, the coupling has the flow-line type of the un-recentred word from `x`
(`isFlowTypeAt_of_shiftW`), the shifted field is the translate of the un-recentred field by `x`
(`isTranslateAddConst_flowField_neg`), and `ae_codeMatch_of_regular_coupling_seed` applies; the seeded match set is
then pulled back through the conditional law (`Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param`). -/
theorem ae_codeMatch_of_model_historyRule_seed {κ θ : ℝ} (M : StoppedTypeModel κ θ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc)
    {R : HistorySpace M.data.nL M.data.nR → ℝ≥0∞}
    (hRm : Measurable R) (hRg : IsHistGalmarino R)
    (hR : ∀ᵐ ω ∂M.law, M.data.life ω = R (killedHistory M.data.driver
      (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR) M.data.life ω))
    {s : M.space → ℝ} (hs : Measurable[M.data.filt 0] s) :
    ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((Exist.StagedLaw.BoundaryWord.shiftW (-s ω) (M.data.word ω), s ω),
        Exist.flowField (-s ω) 0 (M.data.field ω))).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
        M.data.trace ω t + s ω = decPath (Fc ((Exist.StagedLaw.BoundaryWord.shiftW (-s ω) (M.data.word ω), s ω),
          Exist.flowField (-s ω) 0 (M.data.field ω))) t := by
  let _ := M.sigma
  let _ := M.borel
  let _ := M.probability
  let D := M.data
  have h𝒢m : D.filt 0 ≤ M.sigma := D.filt.le 0
  have hWa : AdaptedBefore D.filt D.life D.driver :=
    MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop D.driverAdapted
  have hVLa : ∀ i, AdaptedBefore D.filt D.life (geomLW D.driver D.xL i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop
      (stronglyAdapted_geomLW D.driverAdapted D.driverCont D.xLMeas i)
  have hVRa : ∀ j, AdaptedBefore D.filt D.life (geomRW D.driver D.xR j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted D.lifeStop
      (stronglyAdapted_geomRW D.driverAdapted D.driverCont D.xRMeas j)
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => D.shiftedField ω ψ := fun ψ =>
    (LQGMetric.measurable_distOn_apply ψ).comp D.shiftedMeas
  have hcf := isCouplingCharFun_of_hasSafeLaw D.shiftedField hXψ D.safeLaw
    (ae_of_all _ (isForceReg_thr D.driverZero D.driverCont D.xL D.xR D.life))
    (ae_of_all _ fun ω h => absurd (mem_univ ω) h) hWa hVLa hVRa
  have hWaU : StronglyAdapted (usualAugmentation D.filt M.law) D.driver := fun t =>
    (D.driverAdapted t).mono (Ito.le_usualAugmentation D.filt M.law t)
  have hVU : IsStoppingTime (usualAugmentation D.filt M.law)
      fun ω => (D.life ω : WithTop ℝ≥0) := fun t =>
    Ito.le_usualAugmentation D.filt M.law t _ (D.lifeStop t)
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ :=
    StoppedK2.isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
      (𝒢 := D.filt 0) hκ (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
      (Ito.le_usualAugmentation D.filt M.law 0) MeasurableSet.univ D.xLMeas D.xRMeas
      D.xLNonpos D.xRNonneg D.xLAnti D.xRMono D.driverZero D.driverCont hWaU
      hVU D.announcing D.integrable hcf (D.lifeThreshold.mono fun _ h _ => h)
  have hXf : IsMeasurableKilledDriving
      (fun t (p : M.space × (ℕ → ℝ)) => D.driver t p.1)
      (fun i t p => geomLW D.driver D.xL i t p.1)
      (fun j t p => geomRW D.driver D.xR j t p.1) (fun p => D.life p.1) :=
    Coupling.isMeasurableKilledDriving_of_adaptedBefore
      (adaptedBefore_fst (Ω₀ := ℕ → ℝ) (Coupling.adaptedBefore_killedDriving_W D.killedMeas))
      (fun i => adaptedBefore_fst (Coupling.adaptedBefore_killedDriving_VL D.killedMeas i))
      (fun j => adaptedBefore_fst (Coupling.adaptedBefore_killedDriving_VR D.killedMeas j))
  have h𝒢f : (D.filt 0).comap (Prod.fst : M.space × (ℕ → ℝ) → M.space) ≤
      (inferInstance : MeasurableSpace (M.space × (ℕ → ℝ))) :=
    (MeasurableSpace.comap_mono h𝒢m).trans measurable_fst.comap_le
  have hT : ∀ n, Supp8.Q3Stop.IsKernelStop ((D.filt 0).comap Prod.fst)
      (M.law.prod P₀) (Prod.fst ⁻¹' (univ : Set M.space))
      (fun t p => D.driver t p.1) (fun i t p => geomLW D.driver D.xL i t p.1)
      (fun j t p => geomRW D.driver D.xR j t p.1) (fun p => D.life p.1)
      (fun p => D.driveStops n p.1) := fun n =>
    Supp8.Q3Stop.isKernelStop_of_isStoppingTime h𝒢f hXf
      (StoppedK2.isStoppingTime_drivingFiltration_fst D.killedMeas hXf (D.driveStopping n)) _
  have hcont : ∀ᵐ ω ∂M.law, ω ∈ (univ : Set M.space) → D.life ω ≠ ⊤ →
      ContinuousOn (D.driver · ω) (Iic (D.life ω).toNNReal) ∧
        (∀ i, ContinuousOn (geomLW D.driver D.xL i · ω) (Iic (D.life ω).toNNReal)) ∧
        ∀ j, ContinuousOn (geomRW D.driver D.xR j · ω) (Iic (D.life ω).toNNReal) :=
    ae_of_all _ fun ω _ _ => ⟨(D.driverCont ω).continuousOn,
      fun i => (isForcePath_geomLW D.driverCont D.xL ω i).1.continuousOn,
      fun j => (isForcePath_geomRW D.driverCont D.xR ω j).1.continuousOn⟩
  have hK := Supp8.Q3Stop.ae_isStoppedHullCoupling_kk_prod (P₀ := P₀)
    (F := univ) (ΘL := D.xL) (ΘR := D.xR) hE hcont D.shiftedMeas
    (D.lifePos.mono fun _ h _ => h) le_rfl hWa hVLa hVRa D.safeLaw D.safeMembers
    hT (fun p => D.driveMono p.1)
    ((ae_fst_of_ae (P₀ := P₀) D.driveLt).mono fun _ h _ => h)
    ((ae_fst_of_ae (P₀ := P₀) D.driveLimit).mono fun _ h _ => h)
  have hRν := Sec7.Aux122Disint.ae_ae_condExpKernel (P := M.law.prod P₀) h𝒢f
    (ae_fst_of_ae (P₀ := P₀) hR)
  have htrν := Sec7.Aux122Disint.ae_ae_condExpKernel (P := M.law.prod P₀) h𝒢f
    (ae_fst_of_ae (P₀ := P₀) D.generates)
  let η : M.space × (ℕ → ℝ) → ℝ≥0 → ℂ := fun p => D.trace p.1
  let V : M.space × (ℕ → ℝ) → ℝ≥0∞ := fun p => D.life p.1
  let β : M.space × (ℕ → ℝ) → BoundaryWord × ℝ := fun p =>
    (Exist.StagedLaw.BoundaryWord.shiftW (-s p.1) (D.word p.1), s p.1)
  let G : (BoundaryWord × ℝ) × (M.space × (ℕ → ℝ)) → (PCode × PCode) × ℝ≥0∞ :=
    fun q => Fc (q.1, Exist.flowField (-q.1.2) 0 (D.field q.2.1))
  have hGm : Measurable G := measurable_seedCode (D.fieldMeas.comp measurable_fst) hFc.1
  have hηm : ∀ t, Measurable fun p => η p t := fun t => (D.traceMeas t).comp measurable_fst
  have hVm : Measurable V := (measurable_lifetime D.killedMeas).comp measurable_fst
  have hsf : Measurable[(D.filt 0).comap Prod.fst] fun p : M.space × (ℕ → ℝ) => s p.1 :=
    hs.comp (comap_measurable Prod.fst)
  have hβm : Measurable[(D.filt 0).comap Prod.fst] β :=
    (Exist.StagedLaw.BoundaryWord.measurable_shiftW.comp
      (hsf.neg.prodMk (D.wordMeas.comp (comap_measurable Prod.fst)))).prodMk hsf
  have hcond : ∀ᵐ p₀ ∂(M.law.prod P₀), p₀.1 ∈ (univ : Set M.space) →
      ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        (β p₀, p) ∈ seedMatchSet G η V := by
    filter_upwards [hK, hRν, htrν, ae_fst_of_ae (P₀ := P₀) D.typed]
      with p₀ hK₀ hR₀ htr₀ htype₀ _
    obtain ⟨𝓕', W', VL', VR', B', hSC, hag, hfrz⟩ := hK₀ (mem_univ _)
    have htypeX : IsFlowTypeAt κ θ (Exist.StagedLaw.BoundaryWord.shiftW (-s p₀.1) (D.word p₀.1)) (s p₀.1)
        (D.xL p₀.1) (D.xR p₀.1) D.rhoL D.rhoR := by
      refine isFlowTypeAt_of_shiftW ?_
      rw [shiftW_shiftW_neg]
      exact htype₀
    have hRe : ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        V p = R (killedHistory W' VL' VR' V p) := by
      filter_upwards [hag, hR₀] with p hp hRp
      have he : Exist.AgreeBefore
          (fun t (p : M.space × (ℕ → ℝ)) => D.driver t p.1) W'
          (fun i t p => geomLW D.driver D.xL i t p.1) VL'
          (fun j t p => geomRW D.driver D.xR j t p.1) VR' V V p :=
        ⟨rfl, fun t ht => ⟨(hp t ht.le).1,
          fun i => (hp t ht.le).2.1 i, fun j => (hp t ht.le).2.2 j⟩⟩
      rw [Exist.killedHistory_eq_of_agreeBefore he]
      exact hRp
    have hgen : ∀ᵐ p ∂(condExpKernel (M.law.prod P₀) ((D.filt 0).comap Prod.fst) p₀),
        IsGeneratingTrace (fun t => W' t p) (V p) (fun t => (η p t + s p₀.1) - s p₀.1) := by
      filter_upwards [hag, htr₀] with p hp hgp
      simp only [add_sub_cancel_right]
      exact StoppedK2.isGeneratingTrace_congr (fun t ht => ((hp t ht.le).1).symm) hgp
    have hd := ae_codeMatch_of_regular_coupling_seed h13 hκ hFc
      ⟨D.xLAnti p₀.1, D.xLNonpos p₀.1, D.xRMono p₀.1, D.xRNonneg p₀.1⟩
      htypeX (Hc := fun p => Exist.flowField (-s p₀.1) 0 (D.field p.1))
      (fun p => isTranslateAddConst_flowField_neg (D.shifted p.1)) hSC hRm hRg hRe
      (Aux54.isRegularStop_of_frozen hSC hfrz) (γ := fun p t => η p t + s p₀.1) hgen
    filter_upwards [hd] with p hp
    exact ⟨hp.1, fun n k hnk => hp.2 _ hnk⟩
  have hback := Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param
    h𝒢f hβm (measurableSet_seedMatchSet hGm hηm hVm)
    (F := Prod.fst ⁻¹' (univ : Set M.space)) ⟨univ, MeasurableSet.univ, rfl⟩ hcond
  have hall : ∀ᵐ p ∂(M.law.prod P₀),
      D.life p.1 ≤ (Fc ((Exist.StagedLaw.BoundaryWord.shiftW (-s p.1) (D.word p.1), s p.1),
        Exist.flowField (-s p.1) 0 (D.field p.1))).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.life p.1 →
        D.trace p.1 t + s p.1 = decPath (Fc ((Exist.StagedLaw.BoundaryWord.shiftW (-s p.1) (D.word p.1), s p.1),
          Exist.flowField (-s p.1) 0 (D.field p.1))) t := by
    filter_upwards [hback] with p hp
    exact seedMatch_of_mem (G := G) (p := (β p, p)) (D.traceCont p.1) (hp (mem_univ _))
  exact ae_of_ae_fst (P₀ := P₀) hall

end InteractingSLE.RLC.OrdLate
