/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyUnique

/-!
# Solution codes with a variable start

Packet PROVE-RESTART. The uniqueness proof of Theorem 2.2 for separated words (packet PROVE-SEC2-PATCH,
`Sec2.Assembly`) encodes a solution by its dyadic values (`XCode`) and shows that for a fixed separated
start `(xL, xR)` the canonical solution codes `CRel a xL xR ρL ρR` form a Borel set on which the driving
code determines the solution (`injOn_fst_cRel`). A restarted evolution starts from a *random* state, so the
law of the restart is a kernel in the start; this needs the relation jointly in the start and the code.

A canonical code records its start at the dyadic time `0` (`Canon`), so the start can be read off the code
(`startOf`). This file proves:

* `CRelF a ρL ρR`: codes that are canonical solution codes from their own start; it is Borel
  (`measurableSet_cRelF`; the proofs of `measurableSet_mSet` and `measurable_canon` with the constant start
  replaced by the measurable map `startOf`);
* `lawSetF a ρL ρR ts K`: the pairs (start, driving code) of the canonical solution codes from separated
  starts whose killed state at the times `ts` lies in `K`; it is Borel by Lusin–Souslin
  (`measurableSet_lawSetF`), and its section at a separated start `(xL, xR)` is the landed
  `lawSet a xL xR ρL ρR ts K` (`mem_lawSetF_iff`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly

variable {nL nR : ℕ}

/-- The start recorded in a code at the dyadic time `0`. -/
def startOf (x : XCode nL nR) : (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (fun i => x.2.2.2.1 i 0 0, fun j => x.2.2.2.2 j 0 0)

theorem measurable_startOf_fst (i : Fin nL) :
    Measurable fun x : XCode nL nR => (startOf x).1 i :=
  (measurable_code 0 0).comp (measurable_code_vL i)

theorem measurable_startOf_snd (j : Fin nR) :
    Measurable fun x : XCode nL nR => (startOf x).2 j :=
  (measurable_code 0 0).comp (measurable_code_vR j)

theorem measurable_startOf : Measurable (startOf (nL := nL) (nR := nR)) :=
  (measurable_pi_iff.2 measurable_startOf_fst).prodMk (measurable_pi_iff.2 measurable_startOf_snd)

theorem dyad_zero_zero : dyad 0 0 = 0 := by simp [dyad]

/-- A canonical code records its start. -/
theorem startOf_eq_of_canon {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {x : XCode nL nR}
    (h : Canon xL xR x) : startOf x = (xL, xR) := by
  obtain ⟨-, hL, hR⟩ := (h 0 0).1 dyad_zero_zero
  exact Prod.ext (funext hL) (funext hR)

/-! ### Measurability with a variable start -/

theorem measurable_defectF (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (t : ℝ≥0) :
    Measurable fun x : XCode nL nR => defect a (startOf x).1 (startOf x).2 ρL ρR x t := by
  have hL : ∀ i, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, ρL i / (cw x s.toNNReal - cvL x i s.toNNReal) := fun i =>
    measurable_intervalIntegral (g := fun x s => ρL i / (cw x s.toNNReal - cvL x i s.toNNReal))
      (measurable_const.div (measurable_cw_real.sub (measurable_cvL_real i))) t
  have hR : ∀ j, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, ρR j / (cw x s.toNNReal - cvR x j s.toNNReal) := fun j =>
    measurable_intervalIntegral (g := fun x s => ρR j / (cw x s.toNNReal - cvR x j s.toNNReal))
      (measurable_const.div (measurable_cw_real.sub (measurable_cvR_real j))) t
  have fL : ∀ i, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal) := fun i =>
    measurable_intervalIntegral (g := fun x s => 2 / (cvL x i s.toNNReal - cw x s.toNNReal))
      (measurable_const.div ((measurable_cvL_real i).sub measurable_cw_real)) t
  have fR : ∀ j, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal) := fun j =>
    measurable_intervalIntegral (g := fun x s => 2 / (cvR x j s.toNNReal - cw x s.toNNReal))
      (measurable_const.div ((measurable_cvR_real j).sub measurable_cw_real)) t
  refine ((measurable_cw_at t).sub ((measurable_const.mul (measurable_cb_at t)).add
    (Finset.measurable_sum _ fun i _ => hL i) |>.add
    (Finset.measurable_sum _ fun j _ => hR j))).prodMk
    ((measurable_pi_iff.2 fun i => (measurable_cvL_at i t).sub
      ((measurable_startOf_fst i).add (fL i))).prodMk
      (measurable_pi_iff.2 fun j => (measurable_cvR_at j t).sub
        ((measurable_startOf_snd j).add (fR j))))

/-- Codes satisfying the countable conditions `MSet` from their own start. -/
theorem measurableSet_mSetF (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    MeasurableSet {x : XCode nL nR | x ∈ MSet a (startOf x).1 (startOf x).2 ρL ρR} := by
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
    (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_))))))
  · exact (measurable_eq_real (measurable_cw_at 0) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (measurable_cvL_at i 0)
        (measurable_startOf_fst i)).and
        (Measurable.forall fun j => measurable_eq_real (measurable_cvR_at j 0)
          (measurable_startOf_snd j)))
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp
        (measurableSet_setOfPred.1 (measurable_stateAt _ isClosed_ordSet.measurableSet))
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp (measurable_intAt _)
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp
        (measurableSet_setOfPred.1 (measurable_defectF a ρL ρR _ (measurableSet_singleton 0)))
  · exact Measurable.forall fun i => measurable_collision measurable_cw_real (measurable_cvL_real i)
  · exact Measurable.forall fun j => measurable_collision measurable_cw_real (measurable_cvR_real j)
  · exact measurable_nThr ρL ρR
  · have hthr : Measurable fun x : XCode nL nR =>
        ForceWord.ThresholdCondition ρL ρR 0 (startOf x).1 (startOf x).2 :=
      measurableSet_setOfPred.1 ((measurable_const.prodMk measurable_startOf)
        (measurableSet_thr ρL ρR))
    exact (measurableSet_setOfPred.1 (measurable_cζ (measurableSet_singleton 0))).imp hthr

theorem measurable_canonF :
    Measurable fun x : XCode nL nR => Canon (startOf x).1 (startOf x).2 x := by
  have hw : ∀ n k, Measurable fun x : XCode nL nR => x.2.2.1 n k := fun n k =>
    (measurable_code n k).comp measurable_code_w
  have hL : ∀ i n k, Measurable fun x : XCode nL nR => x.2.2.2.1 i n k := fun i n k =>
    (measurable_code n k).comp (measurable_code_vL i)
  have hR : ∀ j n k, Measurable fun x : XCode nL nR => x.2.2.2.2 j n k := fun j n k =>
    (measurable_code n k).comp (measurable_code_vR j)
  unfold Canon
  refine Measurable.forall fun n => Measurable.forall fun k => Measurable.and ?_ ?_
  · exact measurable_const_imp _ ((measurable_eq_real (hw n k) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (hL i n k) (measurable_startOf_fst i)).and
        (Measurable.forall fun j => measurable_eq_real (hR j n k) (measurable_startOf_snd j))))
  · exact measurable_const_imp _ ((measurable_coe_lt _ measurable_cζ).not.imp
      ((measurable_eq_real (hw n k) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (hL i n k) measurable_const).and
        (Measurable.forall fun j => measurable_eq_real (hR j n k) measurable_const))))

/-! ### The relation with a variable start -/

/-- Codes that are canonical solution codes from their own recorded start. -/
def CRelF (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Set (XCode nL nR) :=
  {x | x ∈ CRel a (startOf x).1 (startOf x).2 ρL ρR}

theorem measurableSet_cRelF (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    MeasurableSet (CRelF a ρL ρR (nL := nL) (nR := nR)) := by
  have e : CRelF a ρL ρR (nL := nL) (nR := nR) =
      (({x | Good x} ∩ {x | LimThr ρL ρR x}) ∩
        {x | x ∈ MSet a (startOf x).1 (startOf x).2 ρL ρR}) ∩
        {x | Canon (startOf x).1 (startOf x).2 x} := by
    ext x
    constructor
    · rintro ⟨⟨hg, hl, hp⟩, hc⟩
      exact ⟨⟨⟨hg, hl⟩, (isIntegratedSLEPath_iff_mem_mSet hg hl).1 hp⟩, hc⟩
    · rintro ⟨⟨⟨hg, hl⟩, hm⟩, hc⟩
      exact ⟨⟨hg, hl, (isIntegratedSLEPath_iff_mem_mSet hg hl).2 hm⟩, hc⟩
  rw [e]
  exact ((measurableSet_good.inter (measurableSet_setOfPred.2 (measurable_limThr ρL ρR))).inter
    (measurableSet_mSetF a ρL ρR)).inter (measurableSet_setOfPred.2 measurable_canonF)

theorem mem_cRelF_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {x : XCode nL nR} :
    (x ∈ CRelF a ρL ρR ∧ startOf x = (xL, xR)) ↔ x ∈ CRel a xL xR ρL ρR := by
  constructor
  · rintro ⟨hx, hs⟩
    have : x ∈ CRel a (startOf x).1 (startOf x).2 ρL ρR := hx
    rwa [hs] at this
  · intro hx
    have hs := startOf_eq_of_canon hx.2
    refine ⟨?_, hs⟩
    show x ∈ CRel a (startOf x).1 (startOf x).2 ρL ρR
    rw [hs]
    exact hx

/-- Separated starts: no left mark at or to the right of a right mark. -/
def SepStart (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop := ∀ i j, s.1 i < s.2 j

theorem measurableSet_sepStart : MeasurableSet {s : (Fin nL → ℝ) × (Fin nR → ℝ) | SepStart s} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun i => Measurable.forall fun j => ?_)
  exact measurableSet_setOfPred.1 (measurableSet_lt ((measurable_pi_apply i).comp measurable_fst)
    ((measurable_pi_apply j).comp measurable_snd))

/-- The pairs (start, driving code) of canonical solution codes from separated starts whose killed
state at the times `ts` lies in `K`. -/
def lawSetF (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) :
    Set (((Fin nL → ℝ) × (Fin nR → ℝ)) × PCode) :=
  (fun x : XCode nL nR => (startOf x, x.1)) ''
    ((CRelF a ρL ρR ∩ {x | SepStart (startOf x)}) ∩ KSet ts K)

/-- **Pathwise uniqueness with a variable start**: on canonical solution codes from separated starts,
the start and the driving code determine the code. -/
theorem injOn_startOf_fst (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    InjOn (fun x : XCode nL nR => (startOf x, x.1))
      (CRelF a ρL ρR ∩ {x | SepStart (startOf x)}) := by
  rintro x ⟨hx, hsx⟩ y ⟨hy, -⟩ hxy
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨hs, h1⟩ := hxy
  have hx' : x ∈ CRel a (startOf x).1 (startOf x).2 ρL ρR := hx
  have hy' : y ∈ CRel a (startOf x).1 (startOf x).2 ρL ρR := by
    have : y ∈ CRel a (startOf y).1 (startOf y).2 ρL ρR := hy
    rwa [← hs] at this
  exact injOn_fst_cRel hsx hx' hy' h1

theorem measurableSet_lawSetF {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ}
    (ts : Fin n → ℝ≥0) {K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)}
    (hK : ∀ j, MeasurableSet (K j)) : MeasurableSet (lawSetF a ρL ρR ts K) :=
  (((measurableSet_cRelF a ρL ρR).inter (measurable_startOf measurableSet_sepStart)).inter
    (measurableSet_kSet ts hK)).image_of_measurable_injOn
    (measurable_startOf.prodMk measurable_fst)
    ((injOn_startOf_fst a ρL ρR).mono inter_subset_left)

/-- The section of `lawSetF` at a separated start is the landed `lawSet`. -/
theorem mem_lawSetF_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) (p : PCode) :
    ((xL, xR), p) ∈ lawSetF a ρL ρR ts K ↔ p ∈ lawSet a xL xR ρL ρR ts K := by
  constructor
  · rintro ⟨x, ⟨⟨hx, -⟩, hK⟩, hxp⟩
    simp only [Prod.mk.injEq] at hxp
    exact ⟨x, ⟨mem_cRelF_iff.1 ⟨hx, hxp.1⟩, hK⟩, hxp.2⟩
  · rintro ⟨x, ⟨hx, hK⟩, rfl⟩
    have hs := (mem_cRelF_iff.2 hx).2
    refine ⟨x, ⟨⟨(mem_cRelF_iff.2 hx).1, ?_⟩, hK⟩, ?_⟩
    · show SepStart (startOf x)
      rw [hs]; exact hsep
    · simp only [hs]

end Assembly

end Sec2

end InteractingSLE
