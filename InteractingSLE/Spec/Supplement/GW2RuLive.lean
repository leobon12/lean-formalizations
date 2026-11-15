/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzPair
import InteractingSLE.Spec.Supplement.GW2BfJ32Shell
import InteractingSLE.Spec.Supplement.GW2SdzPair

/-!
# J32's alive events lie in the good event at every root (decision D24 (2))

PROVE-GW2-ROOTX round 6. SDE's (N1)–(N2) (`GW2Sdo.exists_reindex_nearWords`) and every root-`x` stage instance read
the schedule on the event "good counterflow record at the root, history time before every candidate's root-`x`
contact". Here it contains J32's alive event almost surely:

* `ae_alive_goodX`: the cover event gives the good record (interior counterflow tip, protected root arc);
* `schedTr_eq_of_schedW_eq`, `lt_contactX_iff`: traces of explored drivers that agree up to `q` agree up to `q`, and
  the contact is a separation on `[0, T] × [0, s]`;
* **`ae_cons_lt_contactX`**: after a passed test the history time is before every candidate's contact (the explored
  curve on `[0, q]` is the passed test's live one, `GW2Rz.ae_exactPair_rootX`);
* `historyTime_nil`, **`ae_nil_lt_contactX`**: at the root, the root piece is before its contact
  (`RootCv.ae_coverEvent_spec`);
* `ae_cons_schedW_eq`: after a passed test, every candidate's explored driver is the test's on `[0, q]`;
* **`ae_alive_goodEvent`**, **`ae_alive_goodEvent_scaled`**: the event at every alive history (J32, scaled cover).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Ru

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.ReadD GW2TipSystem GW2TipSystem.RootC24 GW2Rd GW2Rz
  GW2Schedule GW2Tip

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Alive histories have a good counterflow record at their root** (the cover event: interior counterflow tip and
the protected root arc). -/
theorem ae_alive_goodX (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ l : List (EntryIdx c.Θ c.Q),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s := by
  obtain ⟨_, _, _, hfl, hαs⟩ := source_counterflow c
  have hgood := ae_gb6RecGood hfl hαs c.s
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ, hgood] with ξ hcover hα hreg hζ hrg l hl
  obtain ⟨-, hsH, -, -, -, harc⟩ := hcover (RootJ32.alive_subset_G c r l hl)
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hαc : Continuous (c.α ξ) := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hsζ : (c.s : ℝ≥0∞) < c.ζ ξ := by rw [hζ]; exact ENNReal.coe_lt_top
  have hαζ : IsGeneratingTrace (fun t => c.W t ξ) (c.ζ ξ) (c.α ξ) := by rw [hζ]; exact hα
  have hAe : ∀ v ≤ c.s, recordTrace v (cfRec c.s c.W c.ζ ξ) = c.α ξ v := fun v hv =>
    GaugeE.recordTrace_eq (Wα := c.W) (ζα := c.ζ) c.s hW0 (by rw [hζ]; exact hW.continuousOn) hαζ hsζ hv
  have hA : ContinuousOn (fun v => recordTrace v (cfRec c.s c.W c.ζ ξ)) (Iic c.s) :=
    hαc.continuousOn.congr fun v hv => hAe v hv
  refine ⟨(mem_gb6TS_iff hrg).1 ⟨hsζ, hsH⟩, (mem_arcSet_iff hA).2 fun u hu => ?_⟩
  rw [hAe u hu.2]
  exact harc u hu

omit [StandardBorelSpace Ω] in
/-- Two schedule traces agree wherever their explored drivers agree. -/
theorem schedTr_eq_of_schedW_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {l l' : List (EntryIdx c.Θ c.Q)}
    {a a' : ℕ} {ω : Ω} (h : IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω))
    (h' : IsGeneratingTrace (schedW c r l' a' · ω) ⊤ (schedTr c r l' a' ω)) {q : ℝ≥0}
    (hW : ∀ t ≤ q, schedW c r l a t ω = schedW c r l' a' t ω) {t : ℝ≥0} (ht : t ≤ q) :
    schedTr c r l a ω t = schedTr c r l' a' ω t := by
  rw [← LP.traceAt_eq_of_isGeneratingTrace h (continuous_schedW c r l a ω).continuousOn (schedW_zero c r l a ω)
      ENNReal.coe_lt_top,
    ← LP.traceAt_eq_of_isGeneratingTrace h' (continuous_schedW c r l' a' ω).continuousOn
      (schedW_zero c r l' a' ω) ENNReal.coe_lt_top]
  exact LP.traceAt_congr fun u hu => hW u (hu.trans ht)

omit [StandardBorelSpace Ω] in
/-- The root-`x` contact read as separation on `[0, T] × [0, s]`. -/
theorem lt_contactX_iff (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {ω : Ω} (hγ : Continuous (schedTr c r l a ω)) (hα : Continuous (c.α ω)) (T : ℝ≥0) :
    (T : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω ↔
      ∀ t ∈ Icc 0 T, ∀ u ∈ Icc 0 c.s, ((rootPt r.1 : ℂ) + schedTr c r l a ω t) * c.α ω u + 1 ≠ 0 :=
  Gm.lt_firstContactTime_iff_noncontact (continuous_const.add hγ) hα T c.s


/-- **After a passed test the history time is before every candidate's root-`x` contact**: almost surely, after an
alive `l` and a passed test `q` of `(l, a₀)`, the explored curve of every candidate of `(θ_{a₀}, q) :: l` is before
the root-`x` contact at `q`. It is the passed test's live explored curve on `[0, q]`, and that sample is before its
contact up to its buffer (`GW2Rz.ae_exactPair_rootX`). -/
theorem ae_cons_lt_contactX (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a₀ : ℕ) (q : c.Q) (a : ℕ),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ω ∈ (RootJ32.experiment c r).data.tests l a₀ q →
      ((q : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s
        (schedTr c r ((RootJ31.candidateAngle c r a₀, q) :: l) a) c.α ω := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hreg : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) := by
    rw [ae_all_iff]; intro l; rw [ae_all_iff]; intro a
    exact (ae_schedW_regular h13 c r l a).mono fun _ h => h.2.2.1
  have hpair : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      0 < (RootJ31.sourceSample c r l a ω).1 →
      ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω := by
    rw [ae_all_iff]; intro l; rw [ae_all_iff]; intro a
    exact (ae_exactPair_rootX h13 c r l a).mono fun _ h hl => (h hl).2.1
  filter_upwards [hreg, hpair, Gm.ae_futureJoined_trace h13 c r, c.hα] with ω hreg hpair hjoin hα l a₀ q a
    halive htest
  set θ := RootJ31.candidateAngle c r a₀ with hθ
  set l' := (θ, q) :: l with hl'
  obtain ⟨hTq₀, hqv₀, hlive₀, -⟩ := RootJ32.test_spec c r l a₀ q ω htest
  have hold₀ := RootJ32.oldSuccess_of_alive c r l ω halive
  have hord₀ := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  obtain ⟨hgood₀, -⟩ := hjoin l a₀ hold₀
  have halive' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l' :=
    TestEvents.aliveTests_inter_subset l a₀ q ⟨halive, htest⟩
  have hold' := RootJ32.oldSuccess_of_alive c r l' ω halive'
  have hord' := RootJ32.timeOrdered_historyProgram_of_alive c r l' ω halive'
  obtain ⟨hgood', -⟩ := hjoin l' a hold'
  have hT' : RootJ31.historyTime c r l' = q := Gm.historyTime_cons c r l θ q
  have hqcap₀ : (q : ℝ≥0) ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a₀ :=
    hqv₀.le.trans (add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a₀ ω))
  have hJJ : ∀ t ≤ (q : ℝ≥0), Gm.futureJoined c r l' a ω t = Gm.futureJoined c r l a₀ ω t := by
    intro t ht
    have h1 := Gm.futureJoined_eq_joinDrv_hist c r l' a ω hord' hold' hgood' t (by rw [hT']; exact ht)
    have h2 := Gm.futureJoined_eq_joinDrv_query c r l a₀ ω hord₀ hold₀ hgood₀ hTq₀ hqcap₀
      (RootJ32.next_piece_live_of_test c r l a₀ q ω htest) t ht
    rw [h1, h2, hl', RootJ31.historyProgram_cons, List.length_append, List.length_singleton]
  have hWW : ∀ t ≤ (q : ℝ≥0), schedW c r l' a t ω = schedW c r l a₀ t ω := fun t ht => by
    have e1 : schedW c r l' a t ω = Gm.futureJoined c r l' a ω t :=
      congrFun (schedW_of_oldSuccess c r l' a hold') t
    have e2 : schedW c r l a₀ t ω = Gm.futureJoined c r l a₀ ω t :=
      congrFun (schedW_of_oldSuccess c r l a₀ hold₀) t
    rw [e1, e2, hJJ t ht]
  have htr : ∀ t ≤ (q : ℝ≥0), schedTr c r l' a ω t = schedTr c r l a₀ ω t := fun t ht =>
    schedTr_eq_of_schedW_eq c r (hreg l' a) (hreg l a₀) hWW ht
  have hc' : Continuous (schedTr c r l' a ω) := continuousOn_univ.1 ((hreg l' a).2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hc₀ : Continuous (schedTr c r l a₀ ω) := continuousOn_univ.1 ((hreg l a₀).2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous (c.α ω) := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hlt₀ : ((q : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a₀) c.α ω :=
    (ENNReal.coe_le_coe.2 hqv₀.le).trans_lt (hpair l a₀ hlive₀)
  rw [lt_contactX_iff c r l a₀ hc₀ hαc] at hlt₀
  rw [lt_contactX_iff c r l' a hc' hαc]
  intro t ht u hu
  rw [htr t ht.2]
  exact hlt₀ t ht u hu


omit [StandardBorelSpace Ω] in
/-- The empty history ends at the root's time. -/
theorem historyTime_nil (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    RootJ31.historyTime c r [] = (rootEntry r.1).2 := by
  simp [RootJ31.historyTime, RootJ31.historyProgram, entryList, GW2Schedule.schedTime]

/-- **At the root the history time is before every candidate's root-`x` contact**: almost surely on the cover event,
for every candidate. On `[0, q₀]` the explored curve is the root piece, which is before the contact at `q₀` (the cover
event's protected root, `RootCv.ae_coverEvent_spec`). -/
theorem ae_nil_lt_contactX (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ a : ℕ, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) [] →
      ((RootJ31.historyTime c r [] : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r [] a) c.α ω := by
  have hreg : ∀ᵐ ω ∂c.P, ∀ a : ℕ, IsGeneratingTrace (schedW c r [] a · ω) ⊤ (schedTr c r [] a ω) := by
    rw [ae_all_iff]; intro a
    exact (ae_schedW_regular h13 c r [] a).mono fun _ h => h.2.2.1
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, hreg,
    ae_driver_zero_continuousOn (RootCv.isFlowLineDriver_root h13 c r.1),
    Gm.ae_futureJoined_trace h13 c r, c.hα] with ω hcov hreg hE hjoin hα a halive
  obtain ⟨-, -, hγg, -, hlt, -⟩ := hcov (RootJ32.alive_subset_G c r [] halive)
  set E := canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 []) 0 with hEdef
  set γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2) with hγdef
  set q₀ := (rootEntry r.1).2 with hq₀
  have hold := RootJ32.oldSuccess_of_alive c r [] ω halive
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r [] ω halive
  obtain ⟨hgood, -⟩ := hjoin [] a hold
  have hT := historyTime_nil c r
  have hq₀E : (q₀ : ℝ≥0∞) < (E ω).2 := (lt_min_iff.1 hlt).2
  -- the explored driver is the root piece's on `[0, q₀]`
  have hWE : ∀ t ≤ q₀, schedW c r [] a t ω = (E ω).1 t := fun t ht => by
    have e1 : schedW c r [] a t ω = Gm.futureJoined c r [] a ω t :=
      congrFun (schedW_of_oldSuccess c r [] a hold) t
    rw [e1, Gm.futureJoined_eq_joinDrv_hist c r [] a ω hord hold hgood t (by rw [hT]; exact ht)]
    have hL : RootJ31.historyProgram c r [] = [rootEntry r.1] := by
      simp [RootJ31.historyProgram, entryList]
    have hspec : schedSpecOf r.1 [] = schedSpec (rootPt r.1) [rootEntry r.1] := by
      simp [schedSpecOf, entryList]
    have hΔ : specDelta (schedSpec (rootPt r.1) [rootEntry r.1]) 0 = (q₀ : ℝ≥0∞) := by
      rw [Gm.specDelta_schedSpec (rootPt r.1) (by simp)]
      simp [GW2Schedule.schedDelta, GW2Schedule.schedTime, hq₀]
    rw [hL]
    simp only [List.length_singleton, Swc.joinDrv, Swc.joinTime, zero_add]
    rw [hEdef, hspec] at hq₀E ⊢
    split_ifs with h0
    · have : t = 0 := le_antisymm (by exact_mod_cast h0) zero_le
      subst this
      exact hE.1.symm
    · simp only [sub_zero, stopDrv, retOf, hΔ, Real.toNNReal_coe]
      rw [min_eq_left hq₀E.le, min_eq_left (ENNReal.coe_le_coe.2 ht), ENNReal.toNNReal_coe]
  -- so the explored curve is the root piece's trace on `[0, q₀]`
  have hγE : ∀ t ≤ q₀, schedTr c r [] a ω t = γ ω t := fun t ht => by
    rw [← LP.traceAt_eq_of_isGeneratingTrace (hreg a) (continuous_schedW c r [] a ω).continuousOn
        (schedW_zero c r [] a ω) ENNReal.coe_lt_top,
      ← LP.traceAt_eq_of_isGeneratingTrace hγg hE.2 hE.1 ((ENNReal.coe_le_coe.2 ht).trans_lt hq₀E)]
    exact LP.traceAt_congr fun u hu => hWE u (hu.trans ht)
  have hc : Continuous (schedTr c r [] a ω) := continuousOn_univ.1 ((hreg a).2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous (c.α ω) := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  rw [hT, lt_contactX_iff c r [] a hc hαc]
  intro t ht u hu hzero
  have htT := (ENNReal.coe_le_coe.2 ht.2).trans_lt (lt_min_iff.1 hlt).1
  rw [hγE t ht.2] at hzero
  exact notMem_of_lt_firstContactTime htT ⟨u, hu, ((SourceC.sphereInv_eq_iff _ _).2 hzero).symm⟩


/-- **After a passed test the explored drivers agree with the test's on `[0, q]`**: almost surely, after an alive `l`
and a passed test `q` of `(l, a₀)`, every candidate of `(θ_{a₀}, q) :: l` has the explored driver of `(l, a₀)` up to
`q`. -/
theorem ae_cons_schedW_eq (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a₀ : ℕ) (q : c.Q) (a : ℕ),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ω ∈ (RootJ32.experiment c r).data.tests l a₀ q → ∀ t ≤ (q : ℝ≥0),
        schedW c r ((RootJ31.candidateAngle c r a₀, q) :: l) a t ω = schedW c r l a₀ t ω := by
  filter_upwards [Gm.ae_futureJoined_trace h13 c r] with ω hjoin l a₀ q a halive htest t ht
  set θ := RootJ31.candidateAngle c r a₀ with hθ
  set l' := (θ, q) :: l with hl'
  obtain ⟨hTq₀, hqv₀, -, -⟩ := RootJ32.test_spec c r l a₀ q ω htest
  have hold₀ := RootJ32.oldSuccess_of_alive c r l ω halive
  have hord₀ := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive
  obtain ⟨hgood₀, -⟩ := hjoin l a₀ hold₀
  have halive' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l' :=
    TestEvents.aliveTests_inter_subset l a₀ q ⟨halive, htest⟩
  have hold' := RootJ32.oldSuccess_of_alive c r l' ω halive'
  have hord' := RootJ32.timeOrdered_historyProgram_of_alive c r l' ω halive'
  obtain ⟨hgood', -⟩ := hjoin l' a hold'
  have hT' : RootJ31.historyTime c r l' = q := Gm.historyTime_cons c r l θ q
  have hqcap₀ : (q : ℝ≥0) ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a₀ :=
    hqv₀.le.trans (add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a₀ ω))
  have h1 := Gm.futureJoined_eq_joinDrv_hist c r l' a ω hord' hold' hgood' t (by rw [hT']; exact ht)
  have h2 := Gm.futureJoined_eq_joinDrv_query c r l a₀ ω hord₀ hold₀ hgood₀ hTq₀ hqcap₀
    (RootJ32.next_piece_live_of_test c r l a₀ q ω htest) t ht
  have e1 : schedW c r l' a t ω = Gm.futureJoined c r l' a ω t :=
    congrFun (schedW_of_oldSuccess c r l' a hold') t
  have e2 : schedW c r l a₀ t ω = Gm.futureJoined c r l a₀ ω t :=
    congrFun (schedW_of_oldSuccess c r l a₀ hold₀) t
  rw [e1, e2, h1, h2, hl', RootJ31.historyProgram_cons, List.length_append, List.length_singleton]

/-- **J32's alive events lie in the good event at every root** (decision D24 (2); SDE's (N1)–(N2) live-event fact):
almost surely, at every alive history, the counterflow record is good at the root (`goodX`) and the history time is
before every candidate's root-`x` contact. -/
theorem ae_alive_goodEvent (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ l : List (EntryIdx c.Θ c.Q),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s ∧
        ∀ a : ℕ, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω := by
  filter_upwards [ae_alive_goodX h13 c r, ae_nil_lt_contactX h13 c r, ae_cons_lt_contactX h13 c r]
    with ω hgood hnil hcons l hl
  refine ⟨hgood l hl, fun a => ?_⟩
  cases l with
  | nil => exact hnil a hl
  | cons x l =>
    obtain ⟨hl', hx⟩ := hl
    obtain ⟨a₀, ha₀⟩ := mem_iUnion.1 hx
    obtain ⟨hang, htest⟩ := mem_iUnion.1 ha₀
    have hxe : x = (RootJ31.candidateAngle c r a₀, x.2) := Prod.ext hang.symm rfl
    rw [hxe, Gm.historyTime_cons]
    exact hcons l a₀ x.2 a hl' htest

/-- **The same on the scaled cover** (`GW2Sdz.J32S gap`, whose alive histories are J32-alive). -/
theorem ae_alive_goodEvent_scaled (h13 : Theorem13Statement.{u}) (gap : RootCv.GapFamily.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ l : List (EntryIdx c.Θ c.Q),
      ω ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s ∧
        ∀ a : ℕ, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω := by
  filter_upwards [ae_alive_goodEvent h13 c r] with ω h l hl
  exact h l (GW2Sdz.alive_scaled_subset gap Ω c r l hl)

end InteractingSLE.Theorem14.GW2Ru
