/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Strong

/-!
# Theorem 2.2, existence: codes of local solutions with a free horizon

Packets PROVE-SEC2-PATCH2 (the countable form `MUp`) and PROVE-SEC2-PATCH3 (the rest). A *local
solution* of a separated force word `s` driven by a path `b` up to a horizon `q` is a solution of
every condition of Definition 2.1 before `q`, without maximality (`Sec2.IsSLEPathUpTo`). This file
codes local solutions on the code space `XCode`, with the word read off the code (`wordL`, `wordR`:
the values of the marks at time `0`) and the horizon `cζ`, so that everything is jointly measurable in
the word, the driving path and the horizon:

* `MUp`: countable conditions equivalent, for a good code, to "local solution of its own word
  before its horizon" (`isSLEPathUpTo_iff_mem_mUp`); `measurableSet_mUp`;
* `LRel`: canonical codes of local solutions of separated words; `measurableSet_lRel`;
* `injOn_lProj`: a local solution is determined by its word, its driving path and its horizon
  (local pathwise uniqueness, `Sec2.UpTo.agree_of_lt_min`); so by Lusin–Souslin the set `LSet` of
  triples (word, driving code, horizon) that carry a local solution is Borel and the solution code
  `lInv` is a measurable function of the triple;
* `lCode`, `lCode_mem`: the canonical code of a local solution, and `mem_lSet_of_isSLEPathUpTo`;
* `IsSLEPathUpTo.congr`: the local conditions only see the paths before the horizon;
* `setB_mem_lRel`: a local solution only sees its driving path before the horizon.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly2

open Assembly

variable {nL nR : ℕ}

/-! ### Words read off codes -/

/-- The left word of a code: the left marks at time `0`. -/
def wordL (c : XCode nL nR) : Fin nL → ℝ := fun i => cvL c i 0

/-- The right word of a code: the right marks at time `0`. -/
def wordR (c : XCode nL nR) : Fin nR → ℝ := fun j => cvR c j 0

theorem measurable_wordL : Measurable (wordL : XCode nL nR → Fin nL → ℝ) :=
  measurable_pi_iff.2 fun i => measurable_cvL_at i 0

theorem measurable_wordR : Measurable (wordR : XCode nL nR → Fin nR → ℝ) :=
  measurable_pi_iff.2 fun j => measurable_cvR_at j 0

/-- The defect against the word `(xL, xR)` is the defect against the zero word minus the word. -/
theorem defect_eq_defect_zero_sub (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (x : XCode nL nR) (t : ℝ≥0) :
    defect a xL xR ρL ρR x t = defect a 0 0 ρL ρR x t - (0, xL, xR) := by
  unfold defect
  ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Pi.zero_apply, sub_zero] <;> ring

/-! ### Local solutions in countable form -/

variable (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)

/-- The countable conditions equivalent, on good codes, to "local solution of its own word before
its lifetime". -/
def MUp : Set (XCode nL nR) :=
  {x | cw x 0 = 0 ∧
    (∀ n k, (dyad n k : ℝ≥0∞) < cζ x → stateAt x (dyad n k) ∈ ordSet) ∧
    (∀ n k, (dyad n k : ℝ≥0∞) < cζ x → IntAt x (dyad n k)) ∧
    (∀ n k, (dyad n k : ℝ≥0∞) < cζ x →
      defect a 0 0 ρL ρR x (dyad n k) = ((0 : ℝ), wordL x, wordR x)) ∧
    (∀ i, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧
      cw x s.toNNReal = cvL x i s.toNNReal} = 0) ∧
    (∀ j, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧
      cw x s.toNNReal = cvR x j s.toNNReal} = 0) ∧
    NThr ρL ρR x}

theorem measurableSet_mUp : MeasurableSet (MUp (nL := nL) (nR := nR) a ρL ρR) := by
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
    (Measurable.and ?_ (Measurable.and ?_ ?_)))))
  · exact measurable_eq_real (measurable_cw_at 0) measurable_const
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp
        (measurableSet_setOfPred.1 (measurable_stateAt _ isClosed_ordSet.measurableSet))
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp (measurable_intAt _)
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (measurable_coe_lt _ measurable_cζ).imp (measurableSet_setOfPred.1
        (measurableSet_eq_fun (measurable_defect a 0 0 ρL ρR _)
          (measurable_const.prodMk (measurable_wordL.prodMk measurable_wordR))))
  · exact Measurable.forall fun i => measurable_collision measurable_cw_real (measurable_cvL_real i)
  · exact Measurable.forall fun j => measurable_collision measurable_cw_real (measurable_cvR_real j)
  · exact measurable_nThr ρL ρR

variable {a ρL ρR}

/-- **On good codes, being a local solution of its own word before its lifetime is the countable
condition `MUp`.** -/
theorem isSLEPathUpTo_iff_mem_mUp {x : XCode nL nR} (hx : Good x) :
    IsSLEPathUpTo a (wordL x) (wordR x) ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) ↔
      x ∈ MUp a ρL ρR := by
  constructor
  · intro h
    refine ⟨h.w_zero, fun n k hk => ?_, fun n k hk => ?_, fun n k hk => ?_, h.volume_collisionL,
      h.volume_collisionR, (not_threshold_iff_nThr hx).1 fun t ht => h.not_threshold ht⟩
    · exact ⟨fun i j hij => h.antitone_vL hk hij, h.vL_le_w hk, h.w_le_vR hk,
        fun i j hij => h.monotone_vR hk hij⟩
    · exact ⟨fun i => h.integrable_gapL hk i, fun j => h.integrable_gapR hk j⟩
    · have := defect_eq_zero_iff.2 ⟨h.w_eq hk, fun i => h.vL_eq hk i, fun j => h.vR_eq hk j⟩
      rw [defect_eq_defect_zero_sub a (wordL x) (wordR x), sub_eq_zero] at this
      exact this
  · rintro ⟨h0w, hord, hint, hdef, hcL, hcR, hN⟩
    have hInt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → IntAt x t := fun t ht =>
      ⟨fun i => forall_lt_intervalIntegrable (fun n k hk => (hint n k hk).1 i) ht,
        fun j => forall_lt_intervalIntegrable (fun n k hk => (hint n k hk).2 j) ht⟩
    have hOrd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → stateAt x t ∈ ordSet := fun t ht =>
      forall_lt_of_forall_dyad hx.continuousOn_stateAt isClosed_ordSet hord ht
    have hprimL : ∀ (c : ℝ) (i : Fin nL), ContinuousOn
        (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, c / (cw x s.toNNReal - cvL x i s.toNNReal))
        {t | (t : ℝ≥0∞) < cζ x} := fun c i =>
      continuousOn_primitive fun t ht => by
        simpa only [div_eq_mul_inv, gapL] using ((hInt t ht).1 i).const_mul c
    have hprimR : ∀ (c : ℝ) (j : Fin nR), ContinuousOn
        (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, c / (cw x s.toNNReal - cvR x j s.toNNReal))
        {t | (t : ℝ≥0∞) < cζ x} := fun c j =>
      continuousOn_primitive fun t ht => by
        simpa only [div_eq_mul_inv, gapR] using ((hInt t ht).2 j).const_mul c
    have hfL : ∀ i : Fin nL, ContinuousOn
        (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal))
        {t | (t : ℝ≥0∞) < cζ x} := fun i =>
      continuousOn_primitive fun t ht => by
        simpa only [two_div_sub_eq, gapL] using ((hInt t ht).1 i).const_mul (-2)
    have hfR : ∀ j : Fin nR, ContinuousOn
        (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal))
        {t | (t : ℝ≥0∞) < cζ x} := fun j =>
      continuousOn_primitive fun t ht => by
        simpa only [two_div_sub_eq, gapR] using ((hInt t ht).2 j).const_mul (-2)
    have hdefc : ContinuousOn (defect a 0 0 ρL ρR x) {t | (t : ℝ≥0∞) < cζ x} := by
      unfold defect
      refine (hx.continuousOn_w.sub ((continuousOn_const.mul hx.continuous_b.continuousOn).add
        (continuousOn_finsetSum _ fun i _ => hprimL (ρL i) i) |>.add
        (continuousOn_finsetSum _ fun j _ => hprimR (ρR j) j))).prodMk
        ((continuousOn_pi.2 fun i => (hx.continuousOn_vL i).sub
          (continuousOn_const.add (hfL i))).prodMk
        (continuousOn_pi.2 fun j => (hx.continuousOn_vR j).sub
          (continuousOn_const.add (hfR j))))
    have hEq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x →
        defect a (wordL x) (wordR x) ρL ρR x t = 0 := fun t ht => by
      rw [defect_eq_defect_zero_sub, sub_eq_zero]
      exact forall_lt_of_forall_dyad hdefc isClosed_singleton hdef ht
    exact
      { w_zero := h0w
        vL_zero := fun _ => rfl
        vR_zero := fun _ => rfl
        continuousOn_w := hx.continuousOn_w
        continuousOn_vL := hx.continuousOn_vL
        continuousOn_vR := hx.continuousOn_vR
        antitone_vL := fun {t} ht _ _ hij => (hOrd t ht).1 _ _ hij
        vL_le_w := fun {t} ht => (hOrd t ht).2.1
        w_le_vR := fun {t} ht => (hOrd t ht).2.2.1
        monotone_vR := fun {t} ht _ _ hij => (hOrd t ht).2.2.2 _ _ hij
        integrable_gapL := fun {t} ht => (hInt t ht).1
        integrable_gapR := fun {t} ht => (hInt t ht).2
        w_eq := fun {t} ht => (defect_eq_zero_iff.1 (hEq t ht)).1
        vL_eq := fun {t} ht => (defect_eq_zero_iff.1 (hEq t ht)).2.1
        vR_eq := fun {t} ht => (defect_eq_zero_iff.1 (hEq t ht)).2.2
        volume_collisionL := hcL
        volume_collisionR := hcR
        not_threshold := fun {t} ht => (not_threshold_iff_nThr hx).2 hN t ht }

/-! ### Canonicity with respect to the word read off the code -/

theorem measurable_canonW :
    Measurable fun x : XCode nL nR => Canon (wordL x) (wordR x) x := by
  have hw : ∀ n k, Measurable fun x : XCode nL nR => x.2.2.1 n k := fun n k =>
    (measurable_code n k).comp measurable_code_w
  have hL : ∀ i n k, Measurable fun x : XCode nL nR => x.2.2.2.1 i n k := fun i n k =>
    (measurable_code n k).comp (measurable_code_vL i)
  have hR : ∀ j n k, Measurable fun x : XCode nL nR => x.2.2.2.2 j n k := fun j n k =>
    (measurable_code n k).comp (measurable_code_vR j)
  have hwL : ∀ i, Measurable fun x : XCode nL nR => wordL x i := fun i =>
    (measurable_pi_apply i).comp measurable_wordL
  have hwR : ∀ j, Measurable fun x : XCode nL nR => wordR x j := fun j =>
    (measurable_pi_apply j).comp measurable_wordR
  unfold Canon
  refine Measurable.forall fun n => Measurable.forall fun k => Measurable.and ?_ ?_
  · exact measurable_const_imp _ ((measurable_eq_real (hw n k) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (hL i n k) (hwL i)).and
        (Measurable.forall fun j => measurable_eq_real (hR j n k) (hwR j))))
  · exact measurable_const_imp _ ((measurable_coe_lt _ measurable_cζ).not.imp
      ((measurable_eq_real (hw n k) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (hL i n k) measurable_const).and
        (Measurable.forall fun j => measurable_eq_real (hR j n k) measurable_const))))

/-! ### Local solutions with a free horizon -/

variable (a ρL ρR) in
/-- Canonical codes of local solutions of separated words: the word is read off the code at time
`0`, the horizon is `cζ`. -/
def LRel : Set (XCode nL nR) :=
  {x | Good x ∧ Canon (wordL x) (wordR x) x ∧ (∀ i j, wordL x i < wordR x j) ∧
    IsSLEPathUpTo a (wordL x) (wordR x) ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x)}

theorem measurableSet_lRel : MeasurableSet (LRel (nL := nL) (nR := nR) a ρL ρR) := by
  have e : LRel (nL := nL) (nR := nR) a ρL ρR =
      (({x | Good x} ∩ {x | Canon (wordL x) (wordR x) x}) ∩
        {x | ∀ i j, wordL x i < wordR x j}) ∩ MUp a ρL ρR := by
    ext x
    constructor
    · rintro ⟨hg, hc, hs, hp⟩
      exact ⟨⟨⟨hg, hc⟩, hs⟩, (isSLEPathUpTo_iff_mem_mUp hg).1 hp⟩
    · rintro ⟨⟨⟨hg, hc⟩, hs⟩, hm⟩
      exact ⟨hg, hc, hs, (isSLEPathUpTo_iff_mem_mUp hg).2 hm⟩
  rw [e]
  refine ((measurableSet_good.inter (measurableSet_setOfPred.2 measurable_canonW)).inter ?_).inter
    (measurableSet_mUp a ρL ρR)
  exact measurableSet_setOfPred.2 (Measurable.forall fun i => Measurable.forall fun j =>
    measurable_lt' ((measurable_pi_apply i).comp measurable_wordL)
      ((measurable_pi_apply j).comp measurable_wordR))

/-- A force word: the left and the right mark positions. -/
abbrev MWord (nL nR : ℕ) : Type := (Fin nL → ℝ) × (Fin nR → ℝ)

/-- The projection of a code to its word, its driving code and its horizon. -/
def lProj (x : XCode nL nR) : MWord nL nR × PCode × ℝ≥0∞ := ((wordL x, wordR x), x.1, cζ x)

theorem measurable_lProj : Measurable (lProj (nL := nL) (nR := nR)) :=
  (measurable_wordL.prodMk measurable_wordR).prodMk (measurable_fst.prodMk measurable_cζ)

/-- **A local solution is determined by its word, its driving code and its horizon** (local
pathwise uniqueness). -/
theorem injOn_lProj : InjOn lProj (LRel (nL := nL) (nR := nR) a ρL ρR) := by
  rintro x ⟨hg, hc, hs, hp⟩ x' ⟨hg', hc', -, hp'⟩ hxx
  simp only [lProj, Prod.mk.injEq] at hxx
  obtain ⟨⟨hL, hR⟩, hb, hζ⟩ := hxx
  have hbd : cb x' = cb x := by unfold cb; rw [hb]
  rw [← hL, ← hR, hbd, ← hζ] at hp'
  rw [← hL, ← hR] at hc'
  have hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x →
      UpTo.Agree (cw x) (cvL x) (cvR x) (cw x') (cvL x') (cvR x') t := fun t ht =>
    UpTo.agree_of_lt_min hs hp hp.driverEq hp' hp'.driverEq (by rw [min_self]; exact ht)
  exact code_eq hg hg' hc hc' hb hζ (fun t ht => (hag t ht).1) (fun t ht => (hag t ht).2.1)
    fun t ht => (hag t ht).2.2

variable (a ρL ρR) in
/-- The triples (word, driving code, horizon) that carry a local solution. -/
def LSet : Set (MWord nL nR × PCode × ℝ≥0∞) := lProj '' LRel a ρL ρR

theorem measurableSet_lSet : MeasurableSet (LSet (nL := nL) (nR := nR) a ρL ρR) :=
  measurableSet_lRel.image_of_measurable_injOn measurable_lProj injOn_lProj

/-- The projection on the local solution codes. -/
def lProjR : LRel (nL := nL) (nR := nR) a ρL ρR → MWord nL nR × PCode × ℝ≥0∞ :=
  fun x => lProj x.1

theorem measurableEmbedding_lProjR :
    MeasurableEmbedding (lProjR (nL := nL) (nR := nR) (a := a) (ρL := ρL) (ρR := ρR)) := by
  have := (measurableSet_lRel (a := a) (ρL := ρL) (ρR := ρR) (nL := nL) (nR := nR)).standardBorel
  exact Measurable.measurableEmbedding (measurable_lProj.comp measurable_subtype_coe)
    fun x x' h => Subtype.ext (injOn_lProj x.2 x'.2 h)

variable (a ρL ρR) in
/-- **The local solution code of a triple** (word, driving code, horizon); `0` if there is none. -/
def lInv : MWord nL nR × PCode × ℝ≥0∞ → XCode nL nR :=
  Function.extend (lProjR (a := a) (ρL := ρL) (ρR := ρR)) Subtype.val fun _ => 0

theorem measurable_lInv : Measurable (lInv (nL := nL) (nR := nR) a ρL ρR) :=
  measurableEmbedding_lProjR.measurable_extend measurable_subtype_coe measurable_const

theorem lInv_lProj {x : XCode nL nR} (hx : x ∈ LRel a ρL ρR) : lInv a ρL ρR (lProj x) = x :=
  measurableEmbedding_lProjR.injective.extend_apply Subtype.val (fun _ => 0)
    (⟨x, hx⟩ : LRel a ρL ρR)

theorem lInv_mem {p : MWord nL nR × PCode × ℝ≥0∞} (hp : p ∈ LSet a ρL ρR) :
    lInv a ρL ρR p ∈ LRel a ρL ρR ∧ lProj (lInv a ρL ρR p) = p := by
  obtain ⟨x, hx, rfl⟩ := hp
  rw [lInv_lProj hx]
  exact ⟨hx, rfl⟩

/-- The decoded local solution of a triple of `LSet`. -/
theorem isSLEPathUpTo_lInv {s : MWord nL nR} {c : PCode} {q : ℝ≥0∞}
    (hp : (s, c, q) ∈ LSet a ρL ρR) :
    IsSLEPathUpTo a s.1 s.2 ρL ρR (cw (lInv a ρL ρR (s, c, q))) (cvL (lInv a ρL ρR (s, c, q)))
      (cvR (lInv a ρL ρR (s, c, q))) (dec c) q := by
  obtain ⟨⟨-, -, -, hpath⟩, he⟩ := lInv_mem hp
  simp only [lProj, Prod.mk.injEq] at he
  obtain ⟨hs, hb, hζ⟩ := he
  have hL : wordL (lInv a ρL ρR (s, c, q)) = s.1 := congrArg Prod.fst hs
  have hR : wordR (lInv a ρL ρR (s, c, q)) = s.2 := congrArg Prod.snd hs
  rw [hL, hR, hζ] at hpath
  have hbd : cb (lInv a ρL ρR (s, c, q)) = dec c := by unfold cb; rw [hb]
  rw [hbd] at hpath
  exact hpath

theorem sep_of_mem_lSet {s : MWord nL nR} {c : PCode} {q : ℝ≥0∞}
    (hp : (s, c, q) ∈ LSet a ρL ρR) : ∀ i j, s.1 i < s.2 j := by
  obtain ⟨x, ⟨-, -, hs, -⟩, he⟩ := hp
  simp only [lProj, Prod.mk.injEq] at he
  rw [← congrArg Prod.fst he.1, ← congrArg Prod.snd he.1]
  exact hs

theorem uc_of_mem_lSet {s : MWord nL nR} {c : PCode} {q : ℝ≥0∞}
    (hp : (s, c, q) ∈ LSet a ρL ρR) : ∀ T : ℕ, UC c T := by
  obtain ⟨x, ⟨hg, -⟩, he⟩ := hp
  simp only [lProj, Prod.mk.injEq] at he
  rw [← he.2.1]
  exact hg.1

/-! ### The local conditions only see the paths before the horizon -/

/-- **The local conditions only see the paths before the horizon** (and at `0`). -/
theorem isSLEPathUpTo_congr {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ}
    {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {b b' : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) (h0w : w' 0 = w 0)
    (h0L : ∀ i, vL' i 0 = vL i 0) (h0R : ∀ j, vR' j 0 = vR j 0)
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w' t = w t)
    (hL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → ∀ i, vL' i t = vL i t)
    (hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → ∀ j, vR' j t = vR j t)
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → b' t = b t) :
    IsSLEPathUpTo a xL xR ρL ρR w' vL' vR' b' τ := by
  have hs : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ s ∈ uIcc (0 : ℝ) t, (s.toNNReal : ℝ≥0∞) < τ :=
    fun {t} ht s hs => by
      rw [uIcc_of_le t.coe_nonneg] at hs; exact toNNReal_lt_of_mem_Icc ht hs
  have eqL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ (c : ℝ) (i : Fin nL),
      EqOn (fun s : ℝ => c / (w' s.toNNReal - vL' i s.toNNReal))
        (fun s : ℝ => c / (w s.toNNReal - vL i s.toNNReal)) (uIcc 0 t) :=
    fun ht c i s hs' => by
      simp only; rw [hw _ (hs ht s hs'), hL _ (hs ht s hs') i]
  have eqR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ (c : ℝ) (j : Fin nR),
      EqOn (fun s : ℝ => c / (w' s.toNNReal - vR' j s.toNNReal))
        (fun s : ℝ => c / (w s.toNNReal - vR j s.toNNReal)) (uIcc 0 t) :=
    fun ht c j s hs' => by
      simp only; rw [hw _ (hs ht s hs'), hR _ (hs ht s hs') j]
  have fL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i : Fin nL,
      EqOn (fun s : ℝ => 2 / (vL' i s.toNNReal - w' s.toNNReal))
        (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) (uIcc 0 t) :=
    fun ht i s hs' => by
      simp only; rw [hw _ (hs ht s hs'), hL _ (hs ht s hs') i]
  have fR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ j : Fin nR,
      EqOn (fun s : ℝ => 2 / (vR' j s.toNNReal - w' s.toNNReal))
        (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) (uIcc 0 t) :=
    fun ht j s hs' => by
      simp only; rw [hw _ (hs ht s hs'), hR _ (hs ht s hs') j]
  have gL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i : Fin nL,
      EqOn (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹)
        (fun s : ℝ => (w' s.toNNReal - vL' i s.toNNReal)⁻¹) (uIoc 0 t) :=
    fun {t} ht i s hs' => by
      have hs'' : s ∈ uIcc (0 : ℝ) t := uIoc_subset_uIcc hs'
      simp only; rw [hw _ (hs ht s hs''), hL _ (hs ht s hs'') i]
  have gR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ j : Fin nR,
      EqOn (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹)
        (fun s : ℝ => (w' s.toNNReal - vR' j s.toNNReal)⁻¹) (uIoc 0 t) :=
    fun {t} ht j s hs' => by
      have hs'' : s ∈ uIcc (0 : ℝ) t := uIoc_subset_uIcc hs'
      simp only; rw [hw _ (hs ht s hs''), hR _ (hs ht s hs'') j]
  have hstate : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      (w' t, (fun i => vL' i t), fun j => vR' j t) = (w t, (fun i => vL i t), fun j => vR j t) :=
    fun ht => by rw [hw _ ht, funext (hL _ ht), funext (hR _ ht)]
  exact
    { w_zero := h0w.trans h.w_zero
      vL_zero := fun i => (h0L i).trans (h.vL_zero i)
      vR_zero := fun j => (h0R j).trans (h.vR_zero j)
      continuousOn_w := h.continuousOn_w.congr fun t ht => hw t ht
      continuousOn_vL := fun i => (h.continuousOn_vL i).congr fun t ht => hL t ht i
      continuousOn_vR := fun j => (h.continuousOn_vR j).congr fun t ht => hR t ht j
      antitone_vL := fun {t} ht i j hij => by
        show vL' j t ≤ vL' i t
        rw [hL _ ht, hL _ ht]; exact h.antitone_vL ht hij
      vL_le_w := fun {t} ht i => by rw [hL _ ht, hw _ ht]; exact h.vL_le_w ht i
      w_le_vR := fun {t} ht j => by rw [hR _ ht, hw _ ht]; exact h.w_le_vR ht j
      monotone_vR := fun {t} ht i j hij => by
        show vR' i t ≤ vR' j t
        rw [hR _ ht, hR _ ht]; exact h.monotone_vR ht hij
      integrable_gapL := fun {t} ht i => (h.integrable_gapL ht i).congr (gL ht i)
      integrable_gapR := fun {t} ht j => (h.integrable_gapR ht j).congr (gR ht j)
      w_eq := fun {t} ht => by
        have e1 : ∀ i, (∫ s in (0 : ℝ)..t, ρL i / (w' s.toNNReal - vL' i s.toNNReal)) =
            ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) := fun i =>
          intervalIntegral.integral_congr (eqL ht _ i)
        have e2 : ∀ j, (∫ s in (0 : ℝ)..t, ρR j / (w' s.toNNReal - vR' j s.toNNReal)) =
            ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal) := fun j =>
          intervalIntegral.integral_congr (eqR ht _ j)
        rw [hw _ ht, hb _ ht]
        simp only [e1, e2]
        exact h.w_eq ht
      vL_eq := fun {t} ht i => by
        rw [hL _ ht, intervalIntegral.integral_congr (fL ht i)]; exact h.vL_eq ht i
      vR_eq := fun {t} ht j => by
        rw [hR _ ht, intervalIntegral.integral_congr (fR ht j)]; exact h.vR_eq ht j
      volume_collisionL := fun i => by
        convert h.volume_collisionL i using 2
        ext s
        refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩⟩
        · rw [← hw _ h2, ← hL _ h2 i]; exact h3
        · rw [hw _ h2, hL _ h2 i]; exact h3
      volume_collisionR := fun j => by
        convert h.volume_collisionR j using 2
        ext s
        refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, ?_⟩⟩
        · rw [← hw _ h2, ← hR _ h2 j]; exact h3
        · rw [hw _ h2, hR _ h2 j]; exact h3
      not_threshold := fun {t} ht => by
        have e := hstate ht
        simp only [Prod.mk.injEq] at e
        rw [e.1, e.2.1, e.2.2]; exact h.not_threshold ht }

/-! ### Codes of local solutions -/

/-- The canonical code of a local solution up to the horizon `q`: the driving path, the horizon,
and the state killed at `q` (with its initial value at time `0`). -/
def lCode (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (b w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (q : ℝ≥0∞) : XCode nL nR :=
  codeOf xL xR (fun t (_ : Unit) => b t) (fun t _ => w t) (fun i t _ => vL i t)
    (fun j t _ => vR j t) (fun _ => q) ()

/-- **The canonical code of a local solution of a separated word up to a horizon `q ≤ τ` is a
local solution code**, with projection `(word, enc b, q)`, decoding to the solution before `q`. -/
theorem lCode_mem {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j)
    {b w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hb : Continuous b) (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {q : ℝ≥0∞}
    (hq : q ≤ τ) :
    lCode xL xR b w vL vR q ∈ LRel a ρL ρR ∧
      lProj (lCode xL xR b w vL vR q) = ((xL, xR), enc b, q) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < q → cw (lCode xL xR b w vL vR q) t = w t ∧
        (∀ i, cvL (lCode xL xR b w vL vR q) i t = vL i t) ∧
        ∀ j, cvR (lCode xL xR b w vL vR q) j t = vR j t := by
  have hq' := h.mono hq
  set x := lCode xL xR b w vL vR q with hx
  have hwdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < q → cw x t = w t := fun t ht =>
    dec_killedCode (X := fun t (_ : Unit) => w t) (ζ := fun _ => q) (ω := ()) hq'.w_zero
      hq'.continuousOn_w ht
  have hLdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < q → ∀ i, cvL x i t = vL i t := fun t ht i =>
    dec_killedCode (X := fun t (_ : Unit) => vL i t) (ζ := fun _ => q) (ω := ())
      (hq'.vL_zero i) (hq'.continuousOn_vL i) ht
  have hRdec : ∀ t : ℝ≥0, (t : ℝ≥0∞) < q → ∀ j, cvR x j t = vR j t := fun t ht j =>
    dec_killedCode (X := fun t (_ : Unit) => vR j t) (ζ := fun _ => q) (ω := ())
      (hq'.vR_zero j) (hq'.continuousOn_vR j) ht
  have hw0 : cw x 0 = w 0 := by
    show dec (killedCode (fun t (_ : Unit) => w t) 0 (fun _ => q) ()) 0 = w 0
    rw [dec_zero_of_const (killedCode_zero _ 0 _ ()), hq'.w_zero]
  have hwL : wordL x = xL := funext fun i =>
    dec_zero_of_const (killedCode_zero (fun t (_ : Unit) => vL i t) (xL i) (fun _ => q) ())
  have hwR : wordR x = xR := funext fun j =>
    dec_zero_of_const (killedCode_zero (fun t (_ : Unit) => vR j t) (xR j) (fun _ => q) ())
  have hbdec : cb x = b := funext fun t => dec_enc hb.continuousWithinAt
  have hgood : Good x := by
    refine ⟨fun T => uc_enc hb.continuousOn, fun n k hd => ⟨?_, fun i => ?_, fun j => ?_⟩⟩
    · exact uc_killedCode (X := fun t (_ : Unit) => w t) (ζ := fun _ => q) (ω := ())
        hq'.w_zero hq'.continuousOn_w hd
    · exact uc_killedCode (X := fun t (_ : Unit) => vL i t) (ζ := fun _ => q) (ω := ())
        (hq'.vL_zero i) (hq'.continuousOn_vL i) hd
    · exact uc_killedCode (X := fun t (_ : Unit) => vR j t) (ζ := fun _ => q) (ω := ())
        (hq'.vR_zero j) (hq'.continuousOn_vR j) hd
  have hcanon : Canon xL xR x := by
    intro n k
    constructor
    · intro h0
      simp only [x, lCode, codeOf, killedCode, h0, ↓reduceIte]
      exact ⟨trivial, fun i => trivial, fun j => trivial⟩
    · intro h0 hlt
      have hlt' : ¬ (dyad n k : ℝ≥0∞) < q := hlt
      simp only [x, lCode, codeOf, killedCode, h0, hlt', ↓reduceIte]
      exact ⟨trivial, fun i => trivial, fun j => trivial⟩
  have hpred : IsSLEPathUpTo a xL xR ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
    isSLEPathUpTo_congr hq' hw0 (fun i => (congrFun hwL i).trans (hq'.vL_zero i).symm)
      (fun j => (congrFun hwR j).trans (hq'.vR_zero j).symm) hwdec hLdec hRdec
      fun t _ => by rw [hbdec]
  refine ⟨⟨hgood, ?_, ?_, ?_⟩, ?_, fun t ht => ⟨hwdec t ht, hLdec t ht, hRdec t ht⟩⟩
  · rw [hwL, hwR]; exact hcanon
  · rw [hwL, hwR]; exact hsep
  · rw [hwL, hwR]; exact hpred
  · simp only [lProj, hwL, hwR]
    rfl

/-- A local solution of a separated word driven by a continuous path gives a triple of `LSet` at
every horizon `q ≤ τ`. -/
theorem mem_lSet_of_isSLEPathUpTo {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hsep : ∀ i j, xL i < xR j) {b w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {τ : ℝ≥0∞} (hb : Continuous b)
    (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {q : ℝ≥0∞} (hq : q ≤ τ) :
    ((xL, xR), enc b, q) ∈ LSet a ρL ρR := by
  obtain ⟨hm, hp, -⟩ := lCode_mem hsep hb h hq
  exact ⟨_, hm, hp⟩

/-- A code that is uniformly continuous on every bounded dyadic set is the code of its decoding. -/
theorem enc_dec_of_uc {c : PCode} (hc : ∀ T : ℕ, UC c T) : enc (dec c) = c := by
  funext n k
  show dec c (dyad n k) = c n k
  have hle : dyad n k ≤ ((⌈(dyad n k : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
    have : (dyad n k : ℝ) ≤ ⌈(dyad n k : ℝ)⌉₊ := Nat.le_ceil _
    exact_mod_cast this
  exact (hc _).dec_dyad hle

/-- The decoding of a code that is uniformly continuous on every bounded dyadic set is
continuous. -/
theorem continuous_dec_of_uc {c : PCode} (hc : ∀ T : ℕ, UC c T) : Continuous (dec c) :=
  Good.continuous_b (x := ((c, 0, 0, 0, 0) : XCode 0 0)) ⟨hc, fun n k h => by
    exact absurd h (not_lt.2 bot_le)⟩

/-- **A local solution only sees its driving path before its horizon.** -/
theorem setB_mem_lRel {x : XCode nL nR} (hx : x ∈ LRel a ρL ρR) {c : PCode}
    (hc : ∀ T : ℕ, UC c T) (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → dec c t = cb x t) :
    ((c, x.2) : XCode nL nR) ∈ LRel a ρL ρR := by
  obtain ⟨hg, hcn, hs, hp⟩ := hx
  exact ⟨⟨hc, hg.2⟩, hcn, hs, hp.congr_b heq⟩

/-- A triple of `LSet` with its driving code changed after the horizon is in `LSet`, with the same
state code. -/
theorem lInv_setB {s : MWord nL nR} {c c' : PCode} {q : ℝ≥0∞} (hp : (s, c, q) ∈ LSet a ρL ρR)
    (hc' : ∀ T : ℕ, UC c' T) (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < q → dec c' t = dec c t) :
    (s, c', q) ∈ LSet a ρL ρR ∧ (lInv a ρL ρR (s, c', q)).2 = (lInv a ρL ρR (s, c, q)).2 := by
  obtain ⟨hx, he⟩ := lInv_mem hp
  set x := lInv a ρL ρR (s, c, q)
  simp only [lProj, Prod.mk.injEq] at he
  obtain ⟨hs, hb, hζ⟩ := he
  have hx' := setB_mem_lRel hx hc' fun t ht => by
    rw [heq t (by rw [← hζ]; exact ht)]; unfold cb; rw [hb]
  have hp' : lProj ((c', x.2) : XCode nL nR) = (s, c', q) := by
    simp only [lProj]
    exact Prod.ext hs (Prod.ext rfl hζ)
  refine ⟨⟨_, hx', hp'⟩, ?_⟩
  rw [← hp', lInv_lProj hx']

end Assembly2

end Sec2

end InteractingSLE
