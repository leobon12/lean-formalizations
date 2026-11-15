/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TvLife
import InteractingSLE.Spec.Sec5.Aux61CptThm

/-!
# Claim(k), piece (R2): the prefix candidate has not touched the counterflow by the entry's end

Packet PROVE-GW2-RELDET (round 33), for PROVE-GW2-STAGEMEAN's Claim(k) step (STAGEMEAN's handoff, "For RELDET").
Let `e :: l'` be a history and `a'` a candidate of `e`'s angle whose cap reaches past `e`'s end `T`. On the history's
success, the explored driver of `(e :: l', a)` (any current candidate `a`) and of the prefix `(l', a')` agree on
`[0, T]`: the pieces of `l'` are the same, and the entry's piece is the prefix candidate's canonical piece stopped
earlier (RELDET's `canonDrive_congr_angle`). No time order of the history is needed: a joined driver runs its pieces
for the positive parts of the time increments, whose sum is at least the last time. Hence their traces agree on
`[0, T]`, and the prefix trace, which agrees with a trace that has not touched the (closed) counterflow prefix by `T`
and is continuous past `T`, has not touched it by `T` either:

* `joinedDriver_append_cons_eq`, `joinedRead_append_cons_eq`, `joinedRead_eq_of_split`: joined drivers of programs
  sharing a prefix and differing in the next entry (and in everything after it) agree up to the earlier of the two
  next times (extends round 29's `joinedDriver_append_last_eq`);
* `futureProgram_cons_eq`, **`futureJoined_cons_eq_of_angle`**: the explored drivers of the history and of the prefix
  candidate agree up to the entry's end (every sample with good records; no time order);
* `isGeneratingTrace_schedTr`, **`ae_schedW_schedTr_cons_eq`**: almost surely on the history's success, the explored
  drivers and traces agree on `[0, T]`;
* **`prefixContactStatement`**: `GW2Psm.PrefixContactStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec7.StripSideHeightProb

/-! ### Joined drivers of programs sharing a prefix -/

section Joined

/-- **Two programs sharing a prefix have the same joined driver up to the earlier of their next times**, when the
pieces of the prefix agree and the next pieces agree up to that time (whatever follows). -/
theorem joinedDriver_append_cons_eq {Ω : Type*} {E F : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (ω : Ω) (y y' : ℝ × ℝ≥0)
    (rest rest' : List (ℝ × ℝ≥0)) :
    ∀ (l : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0), (∀ i, j ≤ i → i < j + l.length → E i ω = F i ω) →
      (∀ u : ℝ≥0, u ≤ min y.2 y'.2 - lastTime a l → (E (j + l.length) ω).1 u = (F (j + l.length) ω).1 u) →
      ∀ t : ℝ≥0, t ≤ min y.2 y'.2 - a →
        joinedDriver E j a (l ++ y :: rest) ω t = joinedDriver F j a (l ++ y' :: rest') ω t
  | [], j, a, _, hlast, t, ht => by
    change catPath (E j ω).1 (y.2 - a) (joinedDriver E (j + 1) y.2 rest ω) t =
      catPath (F j ω).1 (y'.2 - a) (joinedDriver F (j + 1) y'.2 rest' ω) t
    have h1 : t ≤ y.2 - a := ht.trans (tsub_le_tsub_right (min_le_left _ _) _)
    have h2 : t ≤ y'.2 - a := ht.trans (tsub_le_tsub_right (min_le_right _ _) _)
    rw [catPath_of_le h1, catPath_of_le h2]
    exact hlast t ht
  | p :: l, j, a, he, hlast, t, ht => by
    change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 (l ++ y :: rest) ω) t =
      catPath (F j ω).1 (p.2 - a) (joinedDriver F (j + 1) p.2 (l ++ y' :: rest') ω) t
    rw [he j le_rfl (by simp only [List.length_cons]; omega)]
    by_cases htp : t ≤ p.2 - a
    · simp only [catPath, htp, ↓reduceIte]
    · simp only [catPath, htp, ↓reduceIte]
      congr 1
      have hlen : j + (p :: l).length = j + 1 + l.length := by simp only [List.length_cons]; omega
      refine joinedDriver_append_cons_eq ω y y' rest rest' l (j + 1) p.2
        (fun i hji hi => he i (by omega) (by simp only [List.length_cons]; omega)) (fun u hu => ?_) _ ?_
      · have h := hlast u hu
        rw [hlen] at h
        exact h
      · exact tsub_le_iff_right.2 (ht.trans tsub_le_tsub_add_tsub)

/-- **ROOT2's joined read of two programs sharing a prefix** agrees up to the earlier of their next times. -/
theorem joinedRead_append_cons_eq (L : List (ℝ × ℝ≥0)) (y y' : ℝ × ℝ≥0) (rest rest' : List (ℝ × ℝ≥0))
    (R : Fin (L ++ y :: rest).length → RecData) (R' : Fin (L ++ y' :: rest').length → RecData)
    (hR : ∀ (i : ℕ) (_ : i < L.length) (hi₁ : i < (L ++ y :: rest).length) (hi₂ : i < (L ++ y' :: rest').length),
      R ⟨i, hi₁⟩ = R' ⟨i, hi₂⟩)
    (hlast : ∀ u : ℝ≥0, u ≤ min y.2 y'.2 - lastTime 0 L → recordDriver R L.length u = recordDriver R' L.length u)
    {t : ℝ≥0} (ht : t ≤ min y.2 y'.2) :
    joinedRead (L ++ y :: rest) R t = joinedRead (L ++ y' :: rest') R' t := by
  unfold joinedRead
  rw [GW2Sde.joinedDriver_eq_const _ R, GW2Sde.joinedDriver_eq_const _ R']
  refine joinedDriver_append_cons_eq () y y' rest rest' L 0 0 (fun i _ _hi => ?_) (fun u hu => ?_) t
    (by rwa [tsub_zero])
  · have hiL : i < L.length := by omega
    have hi₁ : i < (L ++ y :: rest).length := by rw [List.length_append]; omega
    have hi₂ : i < (L ++ y' :: rest').length := by rw [List.length_append]; omega
    simp only [recordDriver, hi₁, hi₂, ↓reduceDIte, hR i hiL hi₁ hi₂]
  · simpa only [zero_add] using hlast u hu

/-- `joinedRead_append_cons_eq` for programs given up to an equality with their split form. -/
theorem joinedRead_eq_of_split {P P' : List (ℝ × ℝ≥0)} (L : List (ℝ × ℝ≥0)) (y y' : ℝ × ℝ≥0)
    (rest rest' : List (ℝ × ℝ≥0)) (hP : P = L ++ y :: rest) (hP' : P' = L ++ y' :: rest')
    (R : Fin P.length → RecData) (R' : Fin P'.length → RecData)
    (hR : ∀ (i : ℕ) (_ : i < L.length) (hi₁ : i < P.length) (hi₂ : i < P'.length), R ⟨i, hi₁⟩ = R' ⟨i, hi₂⟩)
    (hlast : ∀ u : ℝ≥0, u ≤ min y.2 y'.2 - lastTime 0 L → recordDriver R L.length u = recordDriver R' L.length u)
    {t : ℝ≥0} (ht : t ≤ min y.2 y'.2) : joinedRead P R t = joinedRead P' R' t := by
  subst hP hP'
  exact joinedRead_append_cons_eq L y y' rest rest' R R' hR hlast ht

end Joined

/-! ### The explored drivers of a history and of its prefix candidate -/

section Prog

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)

/-- The future program of `e :: l'`: the prefix's history, the entry, the current candidate. -/
theorem futureProgram_cons_eq (θe : c.Θ) (qe : c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    futureProgram c r ((θe, qe) :: l') a = historyProgram c r l' ++ ((θe : ℝ), (qe : ℝ≥0)) ::
      [((candidateAngle c r a : ℝ), historyTime c r ((θe, qe) :: l') + candidateCap c r a)] := by
  unfold futureProgram
  rw [historyProgram_cons c r l' θe qe, List.append_assoc]
  rfl

/-- **The explored drivers of a history and of a prefix candidate of the entry's angle agree up to the entry's end**
(every sample with good records; no time order of the history is needed). -/
theorem futureJoined_cons_eq_of_angle (θe : c.Θ) (qe : c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ)
    (hθ : candidateAngle c r a' = (θe : ℝ))
    (hcap : historyTime c r ((θe, qe) :: l') ≤ historyTime c r l' + candidateCap c r a') (ω : Ω)
    (hg : ∀ (j : ℕ) (hj : j < (futureProgram c r ((θe, qe) :: l') a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r ((θe, qe) :: l') a) ω ⟨j, hj⟩)))
    (hg' : ∀ (j : ℕ) (hj : j < (futureProgram c r l' a').length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l' a') ω ⟨j, hj⟩)))
    {t : ℝ≥0} (ht : t ≤ historyTime c r ((θe, qe) :: l')) :
    Gm.futureJoined c r ((θe, qe) :: l') a ω t = Gm.futureJoined c r l' a' ω t := by
  have hTe : historyTime c r ((θe, qe) :: l') = (qe : ℝ≥0) := Gm.historyTime_cons c r l' θe qe
  have hH := historyProgram_cons c r l' θe qe
  set k := (historyProgram c r l').length with hk
  have hkH : k < (historyProgram c r ((θe, qe) :: l')).length := by
    rw [hH, List.length_append, List.length_singleton]
    exact Nat.lt_succ_self _
  have hkn : k < (futureProgram c r ((θe, qe) :: l') a).length := by
    unfold futureProgram
    rw [List.length_append, List.length_singleton]
    omega
  have hkn' : k < (futureProgram c r l' a').length := by
    unfold futureProgram
    rw [List.length_append, List.length_singleton]
    omega
  -- the entry's record in the history, and the prefix candidate's record
  have hrec : programRecords c (rootPt r.1) (futureProgram c r ((θe, qe) :: l') a) ω ⟨k, hkn⟩ =
      recOf (((historyTime c r ((θe, qe) :: l') - historyTime c r l' : ℝ≥0)) : ℝ≥0∞)
        (GW2Olm.futFam c r l' a' (GW2Olm.curIdx c r l') ω) := by
    change stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r ((θe, qe) :: l') a)) k ω = _
    unfold futureProgram
    rw [stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hkH ω]
    change recOf (specDelta (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l'))) k)
      (canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1)
        (specAngle (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l'))))
        (specDelta (schedSpec (rootPt r.1) (historyProgram c r ((θe, qe) :: l')))) (c.h ω) k) = _
    rw [specDelta_hist_last c r θe qe l', canonDrive_hist_last_eq c r θe qe l' a' hθ ω]
  have hrec' : programRecords c (rootPt r.1) (futureProgram c r l' a') ω ⟨k, hkn'⟩ =
      recOf (candidateCap c r a' : ℝ≥0∞) (GW2Olm.futFam c r l' a' (GW2Olm.curIdx c r l') ω) :=
    nextRecord_eq_of_angle c r l' (a := a') (a' := a') rfl ω
  have hu' : ∀ u : ℝ≥0, u ≤ min (qe : ℝ≥0) (historyTime c r l' + candidateCap c r a') -
      lastTime 0 (historyProgram c r l') → u ≤ historyTime c r ((θe, qe) :: l') - historyTime c r l' := by
    intro u hu
    rwa [← GW2Sde.historyTime_eq_lastTime, ← hTe, min_eq_left hcap] at hu
  have hδcap : historyTime c r ((θe, qe) :: l') - historyTime c r l' ≤ candidateCap c r a' :=
    tsub_le_iff_left.2 hcap
  unfold Gm.futureJoined
  refine joinedRead_eq_of_split (historyProgram c r l') ((θe : ℝ), (qe : ℝ≥0))
    ((candidateAngle c r a' : ℝ), historyTime c r l' + candidateCap c r a')
    [((candidateAngle c r a : ℝ), historyTime c r ((θe, qe) :: l') + candidateCap c r a)] []
    (futureProgram_cons_eq c r θe qe l' a) rfl _ _ (fun i hi hi₁ hi₂ => ?_) (fun u hu => ?_) ?_
  · change stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r ((θe, qe) :: l') a)) i ω =
      stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r l' a')) i ω
    have hiH : i < (historyProgram c r ((θe, qe) :: l')).length := hi.trans hkH
    unfold futureProgram
    rw [stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hiH ω, hH,
      stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hi ω,
      stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hi ω]
  · have hkn'' : k < (historyProgram c r l' ++
        [((candidateAngle c r a' : ℝ), historyTime c r l' + candidateCap c r a')]).length := hkn'
    simp only [recordDriver, ← hk, hkn, hkn'', ↓reduceDIte]
    have hg1 := hg k hkn
    have hg2 := hg' k hkn'
    rw [hrec] at hg1
    rw [hrec'] at hg2
    have hreg : IsRegularDriver (GW2Olm.futFam c r l' a' (GW2Olm.curIdx c r l') ω) :=
      isRegularDriver_canonDrive _ _ _ _ _ _ _ _ _
    have hu1 := hu' u hu
    have e1 : rdrv (programRecords c (rootPt r.1) (futureProgram c r ((θe, qe) :: l') a) ω ⟨k, hkn⟩) u =
        (GW2Olm.futFam c r l' a' (GW2Olm.curIdx c r l') ω).1
          (min (u : ℝ≥0∞) (GW2Olm.futFam c r l' a' (GW2Olm.curIdx c r l') ω).2).toNNReal := by
      rw [hrec, rdrv_recOf_of_good hreg hg1, ← min_assoc, min_eq_left (ENNReal.coe_le_coe.2 hu1)]
    have e2 : rdrv (programRecords c (rootPt r.1) (futureProgram c r l' a') ω ⟨k, hkn'⟩) u =
        (GW2Olm.futFam c r l' a' (GW2Olm.curIdx c r l') ω).1
          (min (u : ℝ≥0∞) (GW2Olm.futFam c r l' a' (GW2Olm.curIdx c r l') ω).2).toNNReal := by
      rw [hrec', rdrv_recOf_of_good hreg hg2, ← min_assoc,
        min_eq_left (ENNReal.coe_le_coe.2 (hu1.trans hδcap))]
    exact e1.trans e2.symm
  · change t ≤ min (qe : ℝ≥0) (historyTime c r l' + candidateCap c r a')
    rw [min_eq_left (hTe ▸ hcap)]
    exact hTe ▸ ht

/-- The trace of the explored curve is a generating trace where one exists. -/
theorem isGeneratingTrace_schedTr (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {ω : Ω}
    (h : ∃ η, IsGeneratingTrace (fun t => schedW c r l a t ω) ⊤ η) :
    IsGeneratingTrace (fun t => schedW c r l a t ω) ⊤ (schedTr c r l a ω) := by
  unfold schedTr
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

end Prog

/-! ### Almost surely: drivers, traces and contacts -/

section Ae

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **On the history's success, the explored drivers and traces of the history and of a prefix candidate of the
entry's angle agree up to the entry's end** (almost surely; no time order). -/
theorem ae_schedW_schedTr_cons_eq (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ),
      candidateAngle c r a' = (e.1 : ℝ) → historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a' →
      oldSuccess c r (e :: l') ω →
        (∀ t ≤ historyTime c r (e :: l'), schedW c r (e :: l') a t ω = schedW c r l' a' t ω) ∧
        (∀ t ≤ historyTime c r (e :: l'), schedTr c r (e :: l') a ω t = schedTr c r l' a' ω t) ∧
        IsGeneratingTrace (fun t => schedW c r (e :: l') a t ω) ⊤ (schedTr c r (e :: l') a ω) ∧
        IsGeneratingTrace (fun t => schedW c r l' a' t ω) ⊤ (schedTr c r l' a' ω) := by
  filter_upwards [Gm.ae_futureJoined_trace h13 c r] with ω hjoin e l' a a' hθ hcap hold
  obtain ⟨θe, qe⟩ := e
  have hold' := GW2Psm.oldSuccess_of_cons c r (θe, qe) l' ω hold
  obtain ⟨hg, γ, hγ⟩ := hjoin _ a hold
  obtain ⟨hg', γ', hγ'⟩ := hjoin l' a' hold'
  have hW := schedW_of_oldSuccess c r ((θe, qe) :: l') a hold
  have hW' := schedW_of_oldSuccess c r l' a' hold'
  have hdrv : ∀ t ≤ historyTime c r ((θe, qe) :: l'),
      schedW c r ((θe, qe) :: l') a t ω = schedW c r l' a' t ω := fun t ht => by
    rw [congrFun hW t, congrFun hW' t]
    exact futureJoined_cons_eq_of_angle c r θe qe l' a a' hθ hcap ω hg hg' ht
  have htr := isGeneratingTrace_schedTr c r _ a ⟨γ, hW ▸ hγ⟩
  have htr' := isGeneratingTrace_schedTr c r l' a' ⟨γ', hW' ▸ hγ'⟩
  have hcont : Continuous (fun t => schedW c r ((θe, qe) :: l') a t ω) ∧
      (fun t => schedW c r ((θe, qe) :: l') a t ω) 0 = 0 := by
    rw [hW]
    exact Gm.continuous_futureJoined c r _ a ω
  have hcont' : Continuous (fun t => schedW c r l' a' t ω) ∧ (fun t => schedW c r l' a' t ω) 0 = 0 := by
    rw [hW']
    exact Gm.continuous_futureJoined c r l' a' ω
  exact ⟨hdrv, fun t ht => GW2Psm.trace_eq_of_drv_eq hcont.1 hcont'.1 hcont.2 hcont'.2 htr htr' hdrv ht, htr, htr'⟩

/-- **(R2) The prefix candidate's trace has not touched the counterflow by the entry's end** when the history's trace
has not (on the history's success, almost surely): `GW2Psm.PrefixContactStatement`. -/
theorem prefixContactStatement : GW2Psm.PrefixContactStatement.{u} := by
  intro Ω _ _ c r e l' a a' hθ hcap
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  filter_upwards [ae_schedW_schedTr_cons_eq h13 c r, c.hα] with ω hcons hα hold hT
  obtain ⟨-, htr, -, htr'⟩ := hcons e l' a a' hθ hcap hold
  set T := historyTime c r (e :: l') with hTdef
  unfold GW2Rz.contactX at hT ⊢
  have hαc : ContinuousOn (fun u => (c.α ω u : OnePoint ℂ)) (Icc 0 c.s) :=
    OnePoint.continuous_coe.comp_continuousOn (hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hA : IsClosed ((fun u => (c.α ω u : OnePoint ℂ)) '' Icc 0 c.s) :=
    (isCompact_Icc.image_of_continuousOn hαc).isClosed
  have hγc : ContinuousOn (schedTr c r l' a' ω) (Icc 0 (T + 1)) :=
    htr'.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top
  refine GW2Psm.lt_firstContactTime_of_forall hA (lt_add_one T)
    (Supp8.GB6.continuous_sphereInv.comp_continuousOn
      (OnePoint.continuous_coe.comp_continuousOn (continuousOn_const.add hγc))) fun u hu => ?_
  have hmiss := Supp8.GB6.notMem_of_lt_firstContactTime ((ENNReal.coe_le_coe.2 hu).trans_lt hT)
  rwa [htr u hu] at hmiss

end Ae

end InteractingSLE.Theorem14.GW2Rd
