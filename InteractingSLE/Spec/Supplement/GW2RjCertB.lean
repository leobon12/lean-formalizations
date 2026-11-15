/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjTest

/-!
# Window certificates at a good sample (decision D33)

PROVE-GW2-ROOTX round 9, pathwise. At a good sample (`GoodSample`), for an alive history `l`, a candidate `a` and a
version `n` of `ver` whose cap is beyond the history's clock, every window `1 ≤ j < N` of the decoded past of the slow
record has a certificate (**`winCert_of_goodSample`**). The window `j` is the next piece of the sub-history `l'` with
`l.drop (|l| − j) = x :: l'`, whose passed test `(a', x.2)` is given by D42 (`GoodSample.life`):

* the explored drivers agree up to `x.2` (`schedW_eq_of_drop`), so do the clocks and, below both caps, the versions
  (`GW2Ru.version_eq_of_drv_eq`); the sub-history's version `n' + 1` is chosen with cap beyond a time `v ∈ (x.2,
  T' + buffer)` (`GoodSample.exh`);
* the decoded boundaries of both records are the clocks at the switches (`trueBdX_eq_clock`), so the sub-record decodes
  to the first `j` windows of the main past (`GW2Wm.baseWordX_augRecX`, `pastOf_congr`, `pastOf_congr_bd`);
* the sub-record is on its record event: off `launchBadRec` (D42), successful, alive (`GW2Sdo.mem_aliveRecX`), so its
  stage driver never visits its avoided set nor returns (`GoodSample.safe`);
* the test's tip is J32's joint tip (`jointShiftTip_mem_H_of_jointTipRead`, with the version as the capacity reader).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rq GW2Rv GW2Rz GW2Sde GW2Sdh GW2Sdx GW2Wm
  GW2Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {h13 : Exist.Theorem13Statement.{u}}
  {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}}

/-- The decoded boundaries of the slow record of version `n` at `(l, a)`. -/
abbrev bdX (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) (ω : Ω) : ℕ → ℝ≥0 :=
  trueBdX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V n)
    (RootJ31.historyProgram c r l) ((entryList l).length + 1) (RootJ31.historyTime c r l) ω

/-- **The sub-history's decoded boundaries are the main ones** up to the sub-history's length. -/
theorem sub_trueBdX_eq {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} (h : GoodRoot c r)
    {l l' : List (EntryIdx c.Θ c.Q)}
    {x : EntryIdx c.Θ c.Q} {k : ℕ} (hdrop : l.drop k = x :: l') {a' : ℕ} {V' : Ω → ℝ≥0∞} {ω : Ω}
    (hωG' : ω ∈ schedGTX h13 c r l' a') (hord' : HistOrdered c r l')
    (hT'c' : ((RootJ31.historyTime c r l' : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l' a') c.α ω)
    (hVT' : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') (RootJ31.historyTime c r l') ω) <
      V' ω)
    {cl : ℝ≥0 → ℝ} {b : ℕ → ℝ≥0}
    (hbd : ∀ i : ℕ, 1 ≤ i → i ≤ (entryList l).length + 1 →
      b i = (cl (schedTime 0 (RootJ31.historyProgram c r l) i)).toNNReal) (hb0 : b 0 = 0)
    (hclcl : ∀ t ≤ RootJ31.historyTime c r l',
      clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') t ω = cl t) :
    ∀ i ≤ (entryList l').length + 1,
      trueBdX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') (schedGTX h13 c r l' a') V'
        (RootJ31.historyProgram c r l') ((entryList l').length + 1) (RootJ31.historyTime c r l') ω i = b i := by
  obtain ⟨hGT', -, -⟩ := schedGTX_spec h13 c r l' a'
  have hL'N' : (RootJ31.historyProgram c r l').length = (entryList l').length + 1 := GW2Ru.length_historyProgram c r l'
  have hT'L : schedTime 0 (RootJ31.historyProgram c r l') ((entryList l').length + 1) = RootJ31.historyTime c r l' := by
    rw [← hL'N']; rfl
  obtain ⟨L₂, hLL⟩ := historyProgram_drop c r k l
  rw [hdrop] at hLL
  have hpre : RootJ31.historyProgram c r l = RootJ31.historyProgram c r l' ++ ([((x.1 : ℝ), (x.2 : ℝ≥0))] ++ L₂) := by
    rw [hLL]
    obtain ⟨θ, q'⟩ := x
    rw [RootJ31.historyProgram_cons, List.append_assoc]
  have hlenl : (entryList l').length + 1 ≤ (entryList l).length + 1 := by
    have h1 := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons] at h1
    simp only [entryList, List.length_map]
    omega
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · rw [hb0]
    simp [trueBdX]
  · rw [trueBdX_eq_clock hGT' h.2 h.1 hL'N' hT'L hord' hωG' hT'c' hVT' hi1 hi, hbd i hi1 (hi.trans hlenl),
      hpre, schedTime_append_list 0 _ _ (by rw [hL'N']; exact hi)]
    have hti : schedTime 0 (RootJ31.historyProgram c r l') i ≤ RootJ31.historyTime c r l' :=
      hT'L ▸ schedTime_mono_of_timeOrdered hord' hi (hL'N' ▸ le_rfl)
    rw [hclcl _ hti]

/-- **The certificate of the window of a sub-history.** -/
theorem winCert_of_sub {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {cw : BoundaryWord}
    (hβ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ cw (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (h : GoodRoot c r) {ω : Ω} (hω : GoodSample h13 ver ch c r h ω) {l' : List (EntryIdx c.Θ c.Q)}
    (hl' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l') {a' : ℕ} {q : c.Q}
    (htest : ω ∈ (RootJ32.experiment c r).data.tests l' a' q)
    (hbad : ∀ y : Ω → RecData, GW2Rd.augRec (GW2Rd.stageEncRec c r l') y ω ∉ GW2Rd.launchBadRec c r l' a')
    {n' : ℕ} {v : ℝ≥0} (hqv : (q : ℝ≥0) < v)
    (hvF : v < RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a' ω)
    (hV'v : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') v ω) <
      (ver Ω c r l' a').V (n' + 1) ω)
    {R : ℝ≥0 → ℝ} {b : ℕ → ℝ≥0} (hbmono : Monotone b)
    (hb1 : b 1 = (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') (rootEntry r.1).2 ω).toNNReal)
    (hbj : b (l'.length + 1) =
      (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') (RootJ31.historyTime c r l') ω).toNNReal)
    (hbj1 : b (l'.length + 1 + 1) = (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') q ω).toNNReal)
    (hRR : ∀ u ≤ b (l'.length + 1 + 1), R u = (ver Ω c r l' a').R (n' + 1) u ω)
    (hpast : pastOf (cfRec c.s c.W c.ζ ω) (fun u => (ver Ω c r l' a').R (n' + 1) u ω)
        (trueBdX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') (schedGTX h13 c r l' a')
          ((ver Ω c r l' a').V (n' + 1)) (RootJ31.historyProgram c r l') ((entryList l').length + 1)
          (RootJ31.historyTime c r l') ω) ((entryList l').length + 1) =
      pastOf (cfRec c.s c.W c.ζ ω) R b ((entryList l').length + 1)) :
    WinCert R b (cfRec c.s c.W c.ζ ω) (l'.length + 1) := by
  have hs : 0 < c.s := h.2
  have hx : 0 ≤ rootPt r.1 := h.1
  obtain ⟨hT'q, hqF, hlive, -⟩ := RootJ32.test_spec c r l' a' q ω htest
  have hgood := (hω.good l' hl').1
  have hωG' := (hω.gt l' a').2 hgood
  obtain ⟨hGT', -, -⟩ := schedGTX_spec h13 c r l' a'
  have hord' := RootJ32.timeOrdered_historyProgram_of_alive c r l' ω hl'
  have hold' := RootJ32.oldSuccess_of_test c r l' a' q ω htest
  have hFc' := hω.pair l' a' hlive
  have hvc' : (v : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l' a') c.α ω :=
    (ENNReal.coe_lt_coe.2 hvF).trans hFc'
  have hqc' : ((q : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l' a') c.α ω :=
    (ENNReal.coe_lt_coe.2 hqv).trans hvc'
  have hT'c' : ((RootJ31.historyTime c r l' : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l' a') c.α ω := (ENNReal.coe_lt_coe.2 hT'q).trans hqc'
  have hverA' := hω.vat l' a' (n' + 1) hgood
  have hsm' := clockX_strictMonoOn hGT' hs hx hωG'
  obtain ⟨-, hmono', -⟩ := clockX_props hGT' hs hx hωG'
  set cl' : ℝ≥0 → ℝ := fun t => clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') t ω with hcl'
  have hcl0' : ∀ t, 0 ≤ cl' t := fun t => RootJ32.forwardCapacity_nonneg _ _ _ _
  have hclle' : ∀ {t t' : ℝ≥0}, t ≤ t' →
      (t' : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l' a') c.α ω → cl' t ≤ cl' t' :=
    fun {t t'} htt ht' =>
      (ENNReal.ofReal_le_ofReal_iff (hcl0' t')).1 (hmono' ((ENNReal.coe_le_coe.2 htt).trans_lt ht') ht' htt)
  have hqv' : cl' q < cl' v := hsm' hqc' hvc' hqv
  have hvF' : cl' v < cl' (RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a' ω) := hsm' hvc' hFc' hvF
  have hv₀T' := Gm.rootTime_le_historyTime c r l' hord'
  have hv₀q' : cl' (rootEntry r.1).2 ≤ cl' q := hclle' (hv₀T'.trans hT'q.le) hqc'
  have hVq' : ENNReal.ofReal (cl' q) < (ver Ω c r l' a').V (n' + 1) ω :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hqv'.le) hV'v
  have hVT' : ENNReal.ofReal (cl' (RootJ31.historyTime c r l')) < (ver Ω c r l' a').V (n' + 1) ω :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hclle' hT'q.le hqc')) hVq'
  -- the version's trace and the level
  have hgen := GW2Nt.isGeneratingTrace_versionX hGT' hs hx hωG' hverA' hvc' hV'v.le
  obtain ⟨σ, hσ1, hσ2⟩ := exists_between
    ((Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt (hcl0' q) hqv')).2 hqv')
  have hσB : (σ : ℝ≥0∞) < ENNReal.ofReal (cl' v) := ENNReal.coe_lt_coe.2 hσ2
  -- J32's tip
  have hcap : ∀ t ≤ RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a' ω,
      RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l' a' ω) = cl' t := hω.cap l' a' hlive
  have hread : ∀ c' : ℝ≥0, c' ≤ σ → RootJ32.capacityDriverRead (rootPt r.1) c.s
      (RootJ31.historyTime c r l' + RootJ31.candidateCap c r a') c' (RootJ31.futurePair c r l' a' ω) =
        (ver Ω c r l' a').R (n' + 1) c' ω := by
    intro c' hc'
    have hc'v : (c' : ℝ) < cl' v :=
      lt_of_le_of_lt (NNReal.coe_le_coe.2 hc') (Real.lt_toNNReal_iff_coe_lt.1 hσ2)
    refine hω.read l' a' (n' + 1) hlive c' ?_ ?_
    · rw [← GW2Bf.forwardCapacity_future_eq_exact c r l' a' ω le_rfl, hcap _ le_rfl]
      exact hc'v.trans hvF'
    · exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hc'.trans hσ2.le)) hV'v
  have htip := jointShiftTip_mem_H_of_test htest hgen hverA'.1 hverA'.2.1 hcap hv₀T' hv₀q' (hcl0' _) hσB hσ1 hread
  have htip' : Gm.jointShiftTip (fun u => (ver Ω c r l' a').R (n' + 1) u ω) σ (b 1)
      ((b (l'.length + 1 + 1) : ℝ) - b 1) ∈ H := by
    rw [hb1, hbj1, Real.coe_toNNReal _ (hcl0' _), Real.coe_toNNReal _ (hcl0' _)]
    exact htip
  -- the stage variable: record event, safety, word, driver, cap
  have hstart := GW2Sdo.stgStartX_eq_clockX (V := (ver Ω c r l' a').V (n' + 1)) hGT' hs hx hωG' hT'c' hVT'
  have hE := slowVarG_mem_E (hx := h.1) (n := n') (hE₀ l' a') hbad hold' hgood hverA' (hω.rho l' a' (n' + 1))
    (by rw [hstart]; exact hVT')
  obtain ⟨hnb, hnr⟩ := hω.safe l' a' n' hord' hE
  have hword := slowVarG_word (n := n') (hx := h.1) (hβ l' a') hs hωG' hverA' hord' hold' hT'c'
  have hN'j : (entryList l').length = l'.length := by simp [entryList]
  rw [hpast, hN'j] at hword
  have hw : ∀ u : ℝ≥0, b (l'.length + 1) + u ≤ σ → (slowVarG h13 ver ch c r l' a' h.1 n').R u ω =
      (ver Ω c r l' a').R (n' + 1) (b (l'.length + 1) + u) ω - (ver Ω c r l' a').R (n' + 1) (b (l'.length + 1)) ω :=
    fun u _ => by rw [slowVarG_R, hstart, ← hbj]; rfl
  have hjj : b (l'.length + 1) ≤ b (l'.length + 1 + 1) := hbmono (Nat.le_succ _)
  have hVc : ((b (l'.length + 1 + 1) - b (l'.length + 1) : ℝ≥0) : ℝ≥0∞) <
      (slowVarG h13 ver ch c r l' a' h.1 n').V ω := by
    rw [slowVarG_V, hstart, ← hbj, lt_tsub_iff_right, ← ENNReal.coe_add, tsub_add_cancel_of_le hjj, hbj1]
    exact hVq'
  exact winCert_of_window hbmono (cfRec c.s c.W c.ζ ω) (j := l'.length + 1) (by omega) hgen hverA'.1 hverA'.2.1 hσB
    (by rw [hbj1]; exact hσ1) hRR htip' hw c.hκ c.hκ4 (rootWordX c.κ cw (rootPt r.1) c.s)
    (progAngle (RootJ31.historyProgram c r l')) (GW2Sds.progAngle_mem_Icc c r l') (candAngle_mem_Icc c r l' a')
    hword hVc hnb hnr

/-- **The window certificates at a good sample.** -/
theorem winCert_of_goodSample {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {cw : BoundaryWord}
    (hβ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).β = schedWordMapX c.κ cw (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a))
    (hE₀ : ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), (ch Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ)
    (h : GoodRoot c r) {ω : Ω} (hω : GoodSample h13 ver ch c r h ω) {l : List (EntryIdx c.Θ c.Q)}
    (hl : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l) (a n : ℕ)
    (hV : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
      (ver Ω c r l a).V n ω)
    {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < (entryList l).length + 1) :
    WinCert (fun u => (ver Ω c r l a).R n u ω) (bdX h13 ver c r l a n ω) (cfRec c.s c.W c.ζ ω) j := by
  classical
  have hs : 0 < c.s := h.2
  have hx : 0 ≤ rootPt r.1 := h.1
  have hlenl : (entryList l).length = l.length := by simp [entryList]
  -- the window's sub-history and its passed test
  obtain ⟨x, l', hdrop⟩ : ∃ x l', l.drop (l.length - j) = x :: l' := by
    rcases hd : l.drop (l.length - j) with _ | ⟨x, l'⟩
    · exact absurd (List.drop_eq_nil_iff.1 hd) (by omega)
    · exact ⟨x, l', rfl⟩
  have hl'len : l'.length + 1 = j := by
    have := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons] at this
    omega
  subst hl'len
  obtain ⟨a', hang, htest, hbad⟩ := hω.life l hl _ x l' hdrop
  obtain ⟨hT'q, hqF, hlive, -⟩ := RootJ32.test_spec c r l' a' x.2 ω htest
  have hxl' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) (x :: l') := by
    have := mem_alive_drop c r (l.length - (l'.length + 1)) l hl
    rwa [hdrop] at this
  have hl' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l' := hxl'.1
  -- good event, good sets, contacts, orders
  have hgood := (hω.good l hl).1
  have hTc := (hω.good l hl).2 a
  have hωG := (hω.gt l a).2 hgood
  have hωG' := (hω.gt l' a').2 hgood
  obtain ⟨hGT, -, -⟩ := schedGTX_spec h13 c r l a
  obtain ⟨hGT', -, -⟩ := schedGTX_spec h13 c r l' a'
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω hl
  have hord' := RootJ32.timeOrdered_historyProgram_of_alive c r l' ω hl'
  have hxq : RootJ31.historyTime c r (x :: l') = (x.2 : ℝ≥0) := by
    obtain ⟨θ, q'⟩ := x
    exact Gm.historyTime_cons c r l' θ q'
  have hqT : (x.2 : ℝ≥0) ≤ RootJ31.historyTime c r l := by
    have := historyTime_drop_le c r (l.length - (l'.length + 1)) l hl
    rwa [hdrop, hxq] at this
  have hqc : ((x.2 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω :=
    (ENNReal.coe_le_coe.2 hqT).trans_lt hTc
  have hFc' := hω.pair l' a' hlive
  have hqc' : ((x.2 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l' a') c.α ω :=
    (ENNReal.coe_lt_coe.2 hqF).trans hFc'
  -- explored drivers and clocks
  have hWW : ∀ t ≤ (x.2 : ℝ≥0), GW2Rd.schedW c r l a t ω = GW2Rd.schedW c r l' a' t ω :=
    schedW_eq_of_drop c r hω.cons _ l a hl hdrop hang htest
  set cl : ℝ≥0 → ℝ := fun t => clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) t ω with hcl
  have hclcl : ∀ t ≤ (x.2 : ℝ≥0), clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') t ω = cl t :=
    fun t ht => (GW2Sdo.clockX_congr (fun u hu => hWW u (hu.trans ht))).symm
  have hcl0 : ∀ t, 0 ≤ cl t := fun t => RootJ32.forwardCapacity_nonneg _ _ _ _
  obtain ⟨-, hmono, -⟩ := clockX_props hGT hs hx hωG
  obtain ⟨-, hmono', -⟩ := clockX_props hGT' hs hx hωG'
  have hsm' := clockX_strictMonoOn hGT' hs hx hωG'
  have hVq : ENNReal.ofReal (cl x.2) < (ver Ω c r l a).V n ω :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ((ENNReal.ofReal_le_ofReal_iff (hcl0 _)).1
      (hmono hqc hTc hqT))) hV
  -- the sub-history's version, beyond a time after the switch
  obtain ⟨v, hqv, hvF⟩ := exists_between hqF
  have hvc' : (v : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l' a') c.α ω :=
    (ENNReal.coe_lt_coe.2 hvF).trans hFc'
  have hcap := hω.cap l' a' hlive
  set cl' : ℝ≥0 → ℝ := fun t => clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') t ω with hcl'
  have hcl0' : ∀ t, 0 ≤ cl' t := fun t => RootJ32.forwardCapacity_nonneg _ _ _ _
  have hqv' : cl' x.2 < cl' v := hsm' hqc' hvc' hqv
  have hvF' : cl' v < cl' (RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a' ω) := hsm' hvc' hFc' hvF
  have hT'v : cl' (RootJ31.historyTime c r l') ≤ cl' v :=
    (ENNReal.ofReal_le_ofReal_iff (hcl0' _)).1
      (hmono' ((ENNReal.coe_le_coe.2 (hT'q.le.trans hqv.le)).trans_lt hvc') hvc' (hT'q.le.trans hqv.le))
  obtain ⟨n', hn'⟩ : ∃ n' : ℕ, (((cl' v).toNNReal : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l' a').V n' ω := by
    have hu : (cl' v - cl' (RootJ31.historyTime c r l')).toNNReal < GW2Sdg.rootGain c r l' a' ω := by
      unfold GW2Sdg.rootGain
      rw [hcap _ le_rfl, hcap _ le_self_add]
      exact (Real.toNNReal_lt_toNNReal_iff (by linarith)).2 (by linarith)
    obtain ⟨n', hn'⟩ := (hω.exh l' a' _ hu).exists
    refine ⟨n', ?_⟩
    have e : GW2Sdg.rootHistCap c r l' a' ω + (cl' v - cl' (RootJ31.historyTime c r l')).toNNReal =
        (cl' v).toNNReal := by
      unfold GW2Sdg.rootHistCap
      rw [hcap _ le_self_add, ← Real.toNNReal_add (hcl0' _) (by linarith)]
      congr 1
      ring
    rwa [e] at hn'
  have hV'v : ENNReal.ofReal (cl' v) < (ver Ω c r l' a').V (n' + 1) ω :=
    lt_of_lt_of_le hn' ((ver Ω c r l' a').mono n' ω)
  have hVq' : ENNReal.ofReal (cl' x.2) < (ver Ω c r l' a').V (n' + 1) ω :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hqv'.le) hV'v
  have hVT' : ENNReal.ofReal (cl' (RootJ31.historyTime c r l')) < (ver Ω c r l' a').V (n' + 1) ω :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hT'v) hV'v
  -- the versions agree up to the switch's clock
  have hq0 : 0 < (x.2 : ℝ≥0) := lt_of_le_of_lt zero_le hT'q
  have hRR := GW2Ru.version_eq_of_drv_eq hGT hGT' hs hx hωG hωG' (hω.vat l a n hgood) (hω.vat l' a' (n' + 1) hgood)
    hq0 hqc hqc' hWW hVq hVq'
  -- the boundaries
  have hLN : (RootJ31.historyProgram c r l).length = (entryList l).length + 1 := GW2Ru.length_historyProgram c r l
  have hTL : schedTime 0 (RootJ31.historyProgram c r l) ((entryList l).length + 1) = RootJ31.historyTime c r l := by
    rw [← hLN]; rfl
  have hbd : ∀ i : ℕ, 1 ≤ i → i ≤ (entryList l).length + 1 →
      bdX h13 ver c r l a n ω i = (cl (schedTime 0 (RootJ31.historyProgram c r l) i)).toNNReal :=
    fun i h1 hiN => trueBdX_eq_clock (V := (ver Ω c r l a).V n) hGT hs hx hLN hTL hord hωG hTc hV h1 hiN
  have hb0 : bdX h13 ver c r l a n ω 0 = 0 := by simp [trueBdX]
  have hbmono : Monotone (bdX h13 ver c r l a n ω) := trueBdX_mono hGT hs hx hLN hTL hord hωG hTc hV
  obtain ⟨hst1, hst2⟩ := schedTime_of_drop c r (l := l) hdrop
  have hv₀q : (rootEntry r.1).2 ≤ (x.2 : ℝ≥0) := (Gm.rootTime_le_historyTime c r l' hord').trans hT'q.le
  have hb1 : bdX h13 ver c r l a n ω 1 = (cl' (rootEntry r.1).2).toNNReal := by
    rw [hbd 1 le_rfl (by omega), schedTime_one]
    exact congrArg _ (hclcl _ hv₀q).symm
  have hbj : bdX h13 ver c r l a n ω (l'.length + 1) = (cl' (RootJ31.historyTime c r l')).toNNReal := by
    rw [hbd _ (by omega) (by omega), hst1]
    exact congrArg _ (hclcl _ hT'q.le).symm
  have hbj1 : bdX h13 ver c r l a n ω (l'.length + 1 + 1) = (cl' x.2).toNNReal := by
    rw [hbd _ (by omega) (by omega), hst2]
    exact congrArg _ (hclcl _ le_rfl).symm
  have hRR' : ∀ u ≤ bdX h13 ver c r l a n ω (l'.length + 1 + 1),
      (fun u => (ver Ω c r l a).R n u ω) u = (ver Ω c r l' a').R (n' + 1) u ω := by
    intro u hu
    have e : (cl' x.2).toNNReal = (cl x.2).toNNReal := congrArg _ (hclcl _ le_rfl)
    exact hRR u ((hu.trans_eq hbj1).trans_eq e)
  have hbeq := sub_trueBdX_eq (V' := (ver Ω c r l' a').V (n' + 1)) h hdrop hωG' hord'
    ((ENNReal.coe_lt_coe.2 hT'q).trans hqc') hVT' hbd hb0 (fun t ht => hclcl t (ht.trans hT'q.le))
  have hpast : pastOf (cfRec c.s c.W c.ζ ω) (fun u => (ver Ω c r l' a').R (n' + 1) u ω)
      (trueBdX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l' a') (schedGTX h13 c r l' a')
        ((ver Ω c r l' a').V (n' + 1)) (RootJ31.historyProgram c r l') ((entryList l').length + 1)
        (RootJ31.historyTime c r l') ω) ((entryList l').length + 1) =
      pastOf (cfRec c.s c.W c.ζ ω) (fun u => (ver Ω c r l a).R n u ω) (bdX h13 ver c r l a n ω)
        ((entryList l').length + 1) := by
    rw [pastOf_congr_bd _ _ _ hbeq]
    refine pastOf_congr _ (B := bdX h13 ver c r l a n ω (l'.length + 1 + 1)) (fun u hu => (hRR' u hu).symm) _
      fun i hi => hbmono ?_
    simp only [entryList, List.length_map] at hi
    omega
  exact winCert_of_sub hβ hE₀ h hω hl' htest hbad hqv hvF hV'v hbmono hb1 hbj hbj1 hRR' hpast

end InteractingSLE.Theorem14.GW2Rj
