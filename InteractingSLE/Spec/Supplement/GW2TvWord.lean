/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TvLive
import InteractingSLE.Spec.Supplement.GW2TuFar

/-!
# Claim(k), piece (R4): the word recursion at the instance records

Packet PROVE-GW2-RELDET (round 33), for PROVE-GW2-STAGEMEAN's Claim(k) step (STAGEMEAN's handoff, "For RELDET").
GEOM2's base word of a root-`x` instance is the stage word of the decoded past of the version
(`GW2Wm.baseWordX_augRecX`). For the history `e :: l'` the decoded past at `N' + 1` stages is the past at `N'`
stages followed by the entry's record, so its stage word is `stopWord` of the stage word at `N'`, at the entry's
angle. At `N'` stages the history's and the prefix's decoded pasts agree: the angles agree before the entry, the stage
boundaries are the same clocks (the explored drivers agree up to the entry's end), and the two versions agree up to
the clock at the entry's end (ROOTX's `version_eq_of_drv_eq`). The entry's record is the history's driver restarted
at the prefix stage start, run for the prefix stage clock at the entry's duration.

* `stageWord_congr_angle`, `pastOf_congr`: the stage word reads the angles before `n` only; `pastOf` reads the
  boundaries up to `n` and the driver up to the last boundary;
* `trueBdX_mono_of`: the decoder's boundaries of a time-ordered history are ordered (any good set);
* `baseWordX_inst_eq`: GEOM2's base word at one sample of an instance (SDE's template);
* **`ae_baseWordX_cons`** (R4, base words): almost surely, at a sample with the history's success, a good record,
  the history time before the current contact and the clock at it below both caps,
  `baseWordX (e :: l') (I.srecX) = stopWord κ (baseWordX l' (I'.srecX), e.1, recOf q (stgDrv R a₀', ⊤))` with
  `a₀'` the prefix stage start and `q` the prefix stage clock at the entry's duration;
* **`ae_beta_cons`** (R4, STAGEMEAN's form): the same for the choices' words `ch.β = upW (θa χ) ∘ baseWordX`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  GW2Rz GW2Wm Sec5.Prop513Schedule

/-! ### Deterministic congruences -/

section Det

/-- **The stage word reads the angles before `n` only.** -/
theorem stageWord_congr_angle {κ : ℝ} {S : Type*} (W₀ : S → BoundaryWord) {θ θ' : ℕ → ℝ} :
    ∀ (n : ℕ) (x : GW2JDetR5.Past S n), (∀ j < n, θ j = θ' j) →
      GW2JDetR5.stageWord (κ := κ) W₀ θ n x = GW2JDetR5.stageWord (κ := κ) W₀ θ' n x
  | 0, _, _ => rfl
  | n + 1, x, h => by
    show stopWord κ (GW2JDetR5.stageWord (κ := κ) W₀ θ n x.1, θ n, x.2) =
      stopWord κ (GW2JDetR5.stageWord (κ := κ) W₀ θ' n x.1, θ' n, x.2)
    rw [stageWord_congr_angle W₀ n x.1 fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)]

/-- **`pastOf` reads the boundaries up to `n` and the driver up to the last boundary** (ordered boundaries). -/
theorem pastOf_congr (cf : RecData) {R R' : ℝ≥0 → ℝ} {b b' : ℕ → ℝ≥0} :
    ∀ n, (∀ j ≤ n, b j = b' j) → (∀ j < n, b j ≤ b (j + 1)) → (∀ u ≤ b n, R u = R' u) →
      GW2Wm.pastOf cf R b n = GW2Wm.pastOf cf R' b' n
  | 0, _, _, _ => rfl
  | n + 1, hb, hmono, hR => by
    have hbn : b n ≤ b (n + 1) := hmono n (Nat.lt_succ_self n)
    have ih := pastOf_congr cf n (fun j hj => hb j (Nat.le_succ_of_le hj))
      (fun j hj => hmono j (Nat.lt_succ_of_lt hj)) (fun u hu => hR u (hu.trans hbn))
    show (GW2Wm.pastOf cf R b n, recOf ((b (n + 1) - b n : ℝ≥0) : ℝ≥0∞) (fun u => stgDrv R (b n) u, ⊤)) =
      (GW2Wm.pastOf cf R' b' n, recOf ((b' (n + 1) - b' n : ℝ≥0) : ℝ≥0∞) (fun u => stgDrv R' (b' n) u, ⊤))
    rw [ih, ← hb n (Nat.le_succ n), ← hb (n + 1) le_rfl]
    congr 1
    refine recOf_congr_top fun u hu => ?_
    have hu' : b n + u ≤ b (n + 1) := (le_tsub_iff_left hbn).1 hu
    simp only [stgDrv]
    rw [hR _ hu', hR _ hbn]

end Det

/-! ### The base word at one sample of an instance -/

section Inst

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)

/-- **The decoder's boundaries of a time-ordered history are ordered** (any good set). -/
theorem trueBdX_mono_of (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {V : Ω → ℝ≥0∞} {ω : Ω} (hV : V ω ≠ ⊤) (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ j < (entryList l).length + 1,
      trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyProgram c r l) ((entryList l).length + 1)
          (historyTime c r l) ω j ≤
        trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyProgram c r l) ((entryList l).length + 1)
          (historyTime c r l) ω (j + 1) := by
  intro j hj
  have hLN : (historyProgram c r l).length = (entryList l).length + 1 := length_historyProgram c r l
  rcases j with _ | j
  · unfold trueBdX
    rw [ite_eq_left rfl]
    exact zero_le
  unfold trueBdX
  rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_left hj, ite_eq_right (Nat.succ_ne_zero _)]
  have hj1 : j < (historyProgram c r l).length := by omega
  by_cases h2 : j + 1 + 1 < (entryList l).length + 1
  · rw [ite_eq_left h2]
    refine stgStartX_mono hGT hs hx hV ?_
    have hj2 : j + 1 < (historyProgram c r l).length := by omega
    rw [Gm.schedTime_succ_eq_getElem hj1, Gm.schedTime_succ_eq_getElem hj2]
    exact List.pairwise_iff_getElem.1 hord.1 j (j + 1) hj1 hj2 (Nat.lt_succ_self j)
  · rw [ite_eq_right h2]
    exact stgStartX_mono hGT hs hx hV (GW2Ru.schedTime_le_historyTime c r l hord (by omega))

/-- **GEOM2's base word at one sample of an instance** (SDE's template of `GW2Sds.ae_baseWord_inputs`): the stage
word of the version's decoded past. -/
theorem baseWordX_inst_eq (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    (cw : BoundaryWord) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) (hord : TimeOrdered 0 (historyProgram c r l)) {ω : Ω} (hω : ω ∈ GT)
    (hold : oldSuccess c r l ω)
    (hTc : (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω) :
    baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r l) ((entryList l).length + 1)
        (length_historyProgram c r l)
        (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V
          (historyTime c r l) R) ω) =
      GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ cw (rootPt r.1) c.s) (progAngle (historyProgram c r l))
        ((entryList l).length + 1)
        (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω)
          (trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyProgram c r l) ((entryList l).length + 1)
            (historyTime c r l) ω) ((entryList l).length + 1)) := by
  set L := historyProgram c r l with hL
  set N := (entryList l).length + 1 with hNdef
  have hLN : L.length = N := length_historyProgram c r l
  have hTj : ∀ j < N, schedTime 0 L j ≤ historyTime c r l := fun j hj =>
    GW2Ru.schedTime_le_historyTime c r l hord (by rw [hLN]; exact hj.le)
  have hjT : ∀ j < N, schedTime 0 L j ≤ lastTime 0 L := fun j hj => by
    rw [← GW2Sde.historyTime_eq_lastTime]
    exact hTj j hj
  have hconj : ∀ j, 0 < j → j < N → (schedTime 0 L j : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
    fun j _ hj => (ENNReal.coe_le_coe.2 (hTj j hj)).trans_lt hTc
  have hagree : ∀ u ≤ historyTime c r l, joinedRead L
      (fun i => (fun j : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) (Fin.cast hLN i)) u =
        schedW c r l a u ω := fun u hu => by
    have e1 : schedW c r l a u ω = Gm.futureJoined c r l a ω u := congrFun (schedW_of_oldSuccess c r l a hold) u
    rw [e1, GW2Bf.futureJoined_eq_histJoined c r l a ω hu]
    rfl
  exact baseWordX_augRecX (x₀ := rootPt r.1) (sp := c.s) (W := schedW c r l a) (Wα := c.W) (ζα := c.ζ)
    (GT := GT) (V := V) (T := historyTime c r l) (R := R) (γ := schedTr c r l a) (α := c.α) c.κ cw hGT hs hx L N
    hLN (xr := stageEncRec c r l) (ω := ω)
    (P := fun j : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) rfl (hA.2.1 ω)
    (hA.2.2.1 ω) hω (hV ω) hTj hjT hconj hagree

end Inst

/-! ### The recursion -/

section Rec

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **(R4) The word recursion at the instance records** (base words): almost surely, at a sample with the history's
success, a good record, the history time before the current contact, and the clocks at it below both caps, the
history's base word is the prefix's base word stopped by the entry's record, at the entry's angle. -/
theorem ae_baseWordX_cons (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (cw : BoundaryWord) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ) (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (hord : TimeOrdered 0 (historyProgram c r (e :: l'))) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
    (hA' : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α R' V')
    (hV' : ∀ ω, V' ω ≠ ⊤) :
    ∀ᵐ ω ∂c.P, oldSuccess c r (e :: l') ω → cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (historyTime c r (e :: l') : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r (e :: l') a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (historyTime c r (e :: l')) ω) <
        V ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (historyTime c r (e :: l')) ω) < V' ω →
      baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r (e :: l')) ((entryList (e :: l')).length + 1)
          (length_historyProgram c r (e :: l'))
          (augRec (stageEncRec c r (e :: l')) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) GT V
            (historyTime c r (e :: l')) R) ω) =
        stopWord c.κ (baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
            (length_historyProgram c r l')
            (augRec (stageEncRec c r l') (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a')
              (schedGTX h13 c r l' a') V' (historyTime c r l') R') ω),
          (e.1 : ℝ),
          recOf (((stgClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') V'
              (historyTime c r l') (historyTime c r (e :: l') - historyTime c r l') ω).toNNReal : ℝ≥0) : ℝ≥0∞)
            (fun u => stgDrv (fun v => R v ω) (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a')
              (schedGTX h13 c r l' a') V' (historyTime c r l') ω) u, ⊤)) := by
  obtain ⟨hGT', -, hGTae'⟩ := schedGTX_spec h13 c r l' a'
  filter_upwards [ae_schedW_schedTr_cons_eq h13 c r, hGT.2.2, hGTae', prefixContactStatement c r e l' a a' hθ hcap,
    GW2Ru.versionAtX_of_isRelVersionX hA, GW2Ru.versionAtX_of_isRelVersionX hA']
    with ω hcons hGTω hGTω' hcont hVA hVA' hold hgood hTc hVT hV'T
  obtain ⟨θe, qe⟩ := e
  set T := historyTime c r ((θe, qe) :: l') with hTdef
  set T' := historyTime c r l' with hT'def
  set L := historyProgram c r ((θe, qe) :: l') with hL
  set L' := historyProgram c r l' with hL'
  set N' := (entryList l').length + 1 with hN'
  have hH : L = L' ++ [((θe : ℝ), (qe : ℝ≥0))] := historyProgram_cons c r l' θe qe
  have hlenL' : L'.length = N' := length_historyProgram c r l'
  have hlenL : L.length = N' + 1 := by rw [hH, List.length_append, List.length_singleton, hlenL']
  have hTT : T' ≤ T := by
    have h := GW2Ru.schedTime_le_historyTime c r ((θe, qe) :: l') hord (j := L'.length)
      (by rw [← hL, hlenL, hlenL']; omega)
    rwa [← hL, hH, schedTime_append 0 _ le_rfl] at h
  have hord' : TimeOrdered 0 L' := by
    have h := hord
    rw [hH] at h
    exact ⟨(List.pairwise_append.1 h.1).1, fun p hp => h.2 p (List.mem_append_left _ hp)⟩
  obtain ⟨hdrv, -, -, -⟩ := hcons (θe, qe) l' a a' hθ hcap hold
  have hω := hGTω.2 hgood
  have hω' := hGTω'.2 hgood
  have hold' := GW2Psm.oldSuccess_of_cons c r (θe, qe) l' ω hold
  have hTc' := hcont hold hTc
  have hclk : ∀ t ≤ T, clockX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) t ω =
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') t ω := fun t ht =>
    GW2Sdo.clockX_congr fun u hu => hdrv u (hu.trans ht)
  obtain ⟨-, hmono, hzero⟩ := clockX_props hGT.1 hs hx hω
  obtain ⟨-, hmono', -⟩ := clockX_props hGT' hs hx hω'
  -- the stage starts of the two schedules agree up to `T`
  have hstartC : ∀ t ≤ T, stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) GT V t ω =
      (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) t ω).toNNReal := fun t ht =>
    GW2Sdo.stgStartX_eq_clockX hGT.1 hs hx hω ((ENNReal.coe_le_coe.2 ht).trans_lt hTc)
      ((hmono ((ENNReal.coe_le_coe.2 ht).trans_lt hTc) hTc ht).trans_lt hVT)
  have hstartP : ∀ t ≤ T, stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') V' t ω =
      (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') t ω).toNNReal := fun t ht =>
    GW2Sdo.stgStartX_eq_clockX hGT' hs hx hω' ((ENNReal.coe_le_coe.2 ht).trans_lt hTc')
      ((hmono' ((ENNReal.coe_le_coe.2 ht).trans_lt hTc') hTc' ht).trans_lt hV'T)
  -- the two base words
  have hbase := baseWordX_inst_eq c r ((θe, qe) :: l') a hx hs cw hGT.1 hA hV hord hω hold hTc
  have hbase' := baseWordX_inst_eq c r l' a' hx hs cw hGT' hA' hV' hord' hω' hold'
    ((ENNReal.coe_le_coe.2 hTT).trans_lt hTc')
  rw [hbase, hbase']
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) GT V L
    ((entryList ((θe, qe) :: l')).length + 1) T ω with hb
  set b' := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') V' L' N' T' ω with hb'
  -- the boundaries
  have hbN' : b N' = (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) T' ω).toNNReal := by
    rw [hb]
    unfold trueBdX
    rw [ite_eq_right (Nat.succ_ne_zero _),
      ite_eq_left (show N' < (entryList ((θe, qe) :: l')).length + 1 from Nat.lt_succ_self _), ← hlenL', hH,
      schedTime_append 0 _ le_rfl]
    exact hstartC T' hTT
  have hb'N' : b' N' = (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T' ω).toNNReal := by
    rw [hb']
    unfold trueBdX
    rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (lt_irrefl _)]
    exact hstartP T' hTT
  have hbN : b (N' + 1) = (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) T ω).toNNReal := by
    rw [hb]
    unfold trueBdX
    rw [ite_eq_right (Nat.succ_ne_zero _),
      ite_eq_right (show ¬ (N' + 1 < (entryList ((θe, qe) :: l')).length + 1) from lt_irrefl _)]
    exact hstartC T le_rfl
  have hbj : ∀ j ≤ N', b j = b' j := by
    intro j hj
    rcases j with _ | j
    · rw [hb, hb']
      unfold trueBdX
      rw [ite_eq_left rfl, ite_eq_left rfl]
    rcases lt_or_eq_of_le hj with hj | hj
    · have hjL' : j + 1 ≤ L'.length := by omega
      have ht : schedTime 0 L' (j + 1) ≤ T := (GW2Ru.schedTime_le_historyTime c r l' hord' hjL').trans hTT
      rw [hb, hb']
      unfold trueBdX
      rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_left (show j + 1 < (entryList ((θe, qe) :: l')).length + 1 by
        change j + 1 < N' + 1
        omega),
        ite_eq_right (Nat.succ_ne_zero _), ite_eq_left hj, hH, schedTime_append 0 _ hjL', hstartC _ ht,
        hstartP _ ht, hclk _ ht]
    · rw [hj, hbN', hb'N', hclk T' hTT]
  have hbmono : ∀ j < N', b j ≤ b (j + 1) := fun j hj =>
    trueBdX_mono_of c r ((θe, qe) :: l') a hx hs hGT.1 (hV ω) hord j (by
      change j < (entryList l').length + 1 + 1
      omega)
  -- the versions agree up to the clock at `T`
  have hRR : ∀ u ≤ b N', R u ω = R' u ω := by
    intro u hu
    have hT'T : (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) T' ω).toNNReal ≤
        (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) T ω).toNNReal :=
      Real.toNNReal_le_toNNReal ((ENNReal.ofReal_le_ofReal_iff (RootJ32.forwardCapacity_nonneg _ _ _ _)).1
        (hmono ((ENNReal.coe_le_coe.2 hTT).trans_lt hTc) hTc hTT))
    rw [hbN'] at hu
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT0 | hT0
    · have hc0 : (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r ((θe, qe) :: l') a) T ω).toNNReal = 0 := by
        rw [← hT0]
        have h0 := hzero
        rw [ENNReal.ofReal_eq_zero] at h0
        exact Real.toNNReal_of_nonpos h0
      have hu0 : u = 0 := le_antisymm (hc0 ▸ hu.trans hT'T) zero_le
      rw [hu0, hA.2.2.1 ω, hA'.2.2.1 ω]
    · exact GW2Ru.version_eq_of_drv_eq hGT.1 hGT' hs hx hω hω' (hVA hgood) (hVA' hgood) hT0 hTc hTc' hdrv hVT
        hV'T u (hu.trans hT'T)
  -- the angles
  have hθj : ∀ j < N', progAngle L j = progAngle L' j := fun j hj => by
    unfold progAngle
    rw [hH, List.getD_append _ _ _ _ (by omega)]
  have hang : progAngle L N' = (θe : ℝ) := by
    unfold progAngle
    rw [hH, List.getD_append_right _ _ _ _ hlenL'.le, hlenL', Nat.sub_self]
    rfl
  -- the entry's record
  have hq : b (N' + 1) - b N' = (stgClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') V'
      T' (T - T') ω).toNNReal := by
    have hphT := physClockX_eq_clockX hGT' hs hx hω' hTc'
    have hphT' := physClockX_eq_clockX hGT' hs hx hω' ((ENNReal.coe_le_coe.2 hTT).trans_lt hTc')
    have hlt' : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T' ω) < V' ω :=
      (hmono' ((ENNReal.coe_le_coe.2 hTT).trans_lt hTc') hTc' hTT).trans_lt hV'T
    unfold stgClockX stgStartMX
    rw [add_tsub_cancel_of_le hTT, hphT, hphT', min_eq_left hV'T.le, min_eq_left hlt'.le, hbN, hbN', hclk T le_rfl,
      hclk T' hTT]
    change _ = ((((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T ω).toNNReal : ℝ≥0) : ℝ≥0∞) -
      (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') T' ω).toNNReal : ℝ≥0) : ℝ≥0∞)).toNNReal
    rw [← ENNReal.coe_sub, ENNReal.toNNReal_coe]
  have ha₀ : b N' = stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedGTX h13 c r l' a') V' T' ω := by
    rw [hbN', hstartP T' hTT, hclk T' hTT]
  -- the recursion
  calc GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ cw (rootPt r.1) c.s) (progAngle L)
        ((entryList ((θe, qe) :: l')).length + 1)
        (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b ((entryList ((θe, qe) :: l')).length + 1))
      = stopWord c.κ (GW2JDetR5.stageWord (κ := c.κ) (rootWordX c.κ cw (rootPt r.1) c.s) (progAngle L) N'
          (pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b N'), progAngle L N',
          recOf ((b (N' + 1) - b N' : ℝ≥0) : ℝ≥0∞) (fun u => stgDrv (fun v => R v ω) (b N') u, ⊤)) := rfl
    _ = _ := by
      rw [stageWord_congr_angle _ N' _ hθj, pastOf_congr _ N' hbj hbmono hRR, hang, hq, ha₀]

/-- **(R4) The word recursion at the instance records**, in STAGEMEAN's form: for choices whose words are GEOM2's
word maps (`ch.β = upW (θa χ) ∘ baseWordX`, e.g. `chL (baseWm cw)` at the two histories), almost surely at such a
sample `ch.β (I.srecX) = upW (θa χ) (stopWord κ (Wd', e.1, recOf q (stgDrv R a₀', ⊤)))` and
`ch'.β (I'.srecX) = upW (e.1 χ) Wd'`, with `Wd'` the prefix's base word. -/
theorem ae_beta_cons (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (cw : BoundaryWord) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ) (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (hord : TimeOrdered 0 (historyProgram c r (e :: l'))) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r (e :: l') a) (schedTr c r (e :: l') a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
    (hA' : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α R' V')
    (hV' : ∀ ω, V' ω ≠ ⊤) (ch ch' : GW2Sdh.SchedChoice Ω)
    (hβ : ch.β = schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r (e :: l'))
      ((entryList (e :: l')).length + 1) (length_historyProgram c r (e :: l')) (candAngle c r (e :: l') a))
    (hβ' : ch'.β = schedWordMapX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
      (length_historyProgram c r l') (candAngle c r l' a')) :
    ∀ᵐ ω ∂c.P, oldSuccess c r (e :: l') ω → cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (historyTime c r (e :: l') : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r (e :: l') a) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r (e :: l') a) (historyTime c r (e :: l')) ω) <
        V ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (historyTime c r (e :: l')) ω) < V' ω →
      ch.β ((GW2Rv.schedInstSX c r (e :: l') a GT hA ch).srecX c r (e :: l') (rootPt r.1) ω) =
          upW (candAngle c r (e :: l') a * chiC c.κ)
            (stopWord c.κ (baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
                (length_historyProgram c r l')
                ((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') hA' ch').srecX c r l' (rootPt r.1) ω),
              (e.1 : ℝ),
              recOf ((((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') hA' ch').clockX c (rootPt r.1)
                  (historyTime c r (e :: l') - historyTime c r l') ω).toNNReal : ℝ≥0) : ℝ≥0∞)
                (fun u => stgDrv (fun v => R v ω) (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a')
                  (schedGTX h13 c r l' a') V' (historyTime c r l') ω) u, ⊤))) ∧
        ch'.β ((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') hA' ch').srecX c r l' (rootPt r.1) ω) =
          upW ((e.1 : ℝ) * chiC c.κ)
            (baseWordX c.κ cw (rootPt r.1) c.s (historyProgram c r l') ((entryList l').length + 1)
              (length_historyProgram c r l')
              ((GW2Rv.schedInstSX c r l' a' (schedGTX h13 c r l' a') hA' ch').srecX c r l' (rootPt r.1) ω)) := by
  filter_upwards [ae_baseWordX_cons h13 c r hx hs cw e l' a a' hθ hcap hord hGT hA.1.1 hV hA'.1.1 hV']
    with ω hω hold hgood hTc hVT hV'T
  have hθ' : candAngle c r l' a' = (e.1 : ℝ) := by
    rw [← hθ]
    exact RootH29.specAngle_last _ _ _ _
  refine ⟨?_, ?_⟩
  · rw [hβ]
    exact congrArg (upW (candAngle c r (e :: l') a * chiC c.κ)) (hω hold hgood hTc hVT hV'T)
  · rw [hβ', hθ']
    rfl

end Rec

end InteractingSLE.Theorem14.GW2Rd
