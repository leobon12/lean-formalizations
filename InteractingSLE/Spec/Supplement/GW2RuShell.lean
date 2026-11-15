/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RuLive
import InteractingSLE.Spec.Supplement.GW2RuStep
import InteractingSLE.Spec.Supplement.GW2RuRead
import InteractingSLE.Spec.Supplement.GW2RwStart
import InteractingSLE.Spec.Supplement.GW2RwDrift

/-!
# The slow shell's starting word is admissible (`startsU`): the two-sweep at every root

PROVE-GW2-ROOTX round 6 (the open clause of the corrected `shell` field, decision default (A)). For a frame word that
presents the instance's slow stage word in the samples' frame and starts at `GW2Bf.histStart`, `Prop59Stage.startsU`
asks the start in `(−9/4, −7/4)` (`GW2Rw.ae_histStart_mem_of_alive`), an ordered force word
(`GW2Rw.isOrderedForceWord_of_presentsO`), and every right mark other than the first at absolute position `≥ 7/4`.
The last is the two-sweep of p. 146: the base word's positive labels are the record images of the previous stage's
right marks (`GW2Ru.le_add_of_mem_jumps_stageWord_pastOf`), so they lie right of the tip at the last rightward switch,
whose J32 reading is the passed test's, in `(7/4, 9/4)`.

* `versionAtX_of_isRelVersionX`, `length_historyProgram`, `schedTime_le_historyTime`;
* **`ae_rightMark_ge`**: at every alive history of even length `≥ 2`, every positive label `y` of the base word on the
  instance's record has `histStart + 2^{r.2} y ≥ 7/4`. The chain: GEOM2's `baseWordX_augRecX` (the base word is
  flowed through the version's own pieces between the root-`x` clocks at the switches), the two passed tests' J32
  readings through versions of their own schedules (`ae_sourceX_eq_version`), those versions equal to the
  candidate's up to the switch (`version_eq_of_drv_eq`), `ae_histStart_cons_eq`, and D24 (2) (`ae_alive_goodEvent`);
* `rightMarks_ge_of_presentsO`: the clause for any presenting frame word;
* **`ae_startsU_of_presentsO`**: `(histStart, xL, xR) ∈ startsU` for every presenting frame word.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Ru

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2Rd GW2Rz GW2Rv GW2Wm
  GW2Schedule GW2Tip Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- A root-`x` version is a version at every good sample. -/
theorem versionAtX_of_isRelVersionX {x : ℝ} {s : ℝ≥0} {P : Measure Ω} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (h : IsRelVersionX x s P W' ζ' w γ α R V) :
    ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → VersionAtX x s W' ζ' w γ α R V ω := by
  filter_upwards [h.2.2.2.2.2.2] with ω hω hg
  exact ⟨h.2.1 ω, h.2.2.1 ω, (hω hg).2.2⟩

omit [StandardBorelSpace Ω] in
theorem length_historyProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    (RootJ31.historyProgram c r l).length = (entryList l).length + 1 := by
  simp [RootJ31.historyProgram]

omit [StandardBorelSpace Ω] in
/-- The stage times of a time-ordered history are before its end. -/
theorem schedTime_le_historyTime (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) {j : ℕ} (hj : j ≤ (RootJ31.historyProgram c r l).length) :
    schedTime 0 (RootJ31.historyProgram c r l) j ≤ RootJ31.historyTime c r l := by
  rw [GW2Sde.historyTime_eq_lastTime]
  rcases j with _ | j
  · exact zero_le
  · rw [Gm.schedTime_succ_eq_getElem (by omega)]
    exact Gm.le_lastTime_of_mem hord _ (List.getElem_mem _)


/-- **The slow shell's right marks (two-sweep, p. 146)**: almost surely at every alive history of even length `≥ 2`,
for a root-`x` version of a candidate's schedule covering the history's clock, every positive label `y` of the stage
base word on the instance's record lies at absolute position `histStart + 2^{r.2} y ≥ 7/4` (right of the passed
reading of the last rightward sweep). -/
theorem ae_rightMark_ge (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hx : 0 ≤ rootPt r.1) (l : List (EntryIdx c.Θ c.Q)) (hl : Even l.length) (a : ℕ) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (hver : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hfin : ∀ ω, V ω ≠ ⊤) (κ : ℝ) (c' : BoundaryWord) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l → 2 ≤ l.length →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) < V ω →
      ∀ y ∈ (baseWordX κ c' (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
          (length_historyProgram c r l) (augRec (stageEncRec c r l)
            (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V
              (RootJ31.historyTime c r l) R) ω)).jumps,
        0 < y → 7 / 4 ≤ GW2Bf.histStart c r l ω + (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) * y := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hfam := fun (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ) => exists_schedVersionsXA_mono h13 c r l' a' hx
  choose Rn Vn hverN _ _ hcovN using hfam
  have hX : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' n : ℕ),
      0 < (RootJ31.sourceSample c r l' a' ω).1 → (rootEntry r.1).2 ≤ RootJ31.historyTime c r l' →
      ∀ q : ℝ≥0, RootJ31.historyTime c r l' ≤ q →
        q < RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a' ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') q ω) < Vn l' a' n ω →
        RootJ32.sourceX c r l' a' ω q = (-1) ^ l'.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
          (Rn l' a' n (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') q ω).toNNReal ω -
            Rn l' a' n (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (rootEntry r.1).2 ω).toNNReal ω) := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'; rw [ae_all_iff]; intro n
    exact ae_sourceX_eq_version h13 c r l' a' hx (hverN l' a' n).1.1
  have hP : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ), 0 < (RootJ31.sourceSample c r l' a' ω).1 →
      ((RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a' ω : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'
    exact (ae_exactPair_rootX h13 c r l' a').mono fun _ h hl => (h hl).2.1
  have hC : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ),
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') t ω) < Vn l' a' n ω := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'
    exact hcovN l' a'
  have hVA : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' n : ℕ),
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α (Rn l' a' n) (Vn l' a' n) ω := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'; rw [ae_all_iff]; intro n
    exact versionAtX_of_isRelVersionX (hverN l' a' n).1.1
  have hG : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ),
      (ω ∈ schedGTX h13 c r l' a' ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s) := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'
    exact (schedGTX_spec h13 c r l' a').2.2
  filter_upwards [hX, hP, hC, hVA, hG, GW2Rw.ae_histStart_cons_eq h13 c r, ae_alive_goodEvent h13 c r,
    ae_cons_schedW_eq h13 c r, versionAtX_of_isRelVersionX hver] with ω hX hP hC hVA hG hcons hgood hW hR
    halive hl2 hV y hy hy0
  have halive0 := halive
  obtain ⟨hgx, hcon⟩ := hgood l halive0
  -- the last two entries of the history
  rcases l with _ | ⟨⟨θ₁, q₁⟩, _ | ⟨⟨θ₂, q₂⟩, l₂⟩⟩
  · simp at hl2
  · simp at hl2
  obtain ⟨halive₁, hx₁⟩ := halive
  obtain ⟨a₁, ha₁⟩ := mem_iUnion.1 hx₁
  obtain ⟨hang₁, htest₁⟩ := mem_iUnion.1 ha₁
  have halive₁' := halive₁
  obtain ⟨halive₂, hx₂⟩ := halive₁'
  obtain ⟨a₂, ha₂⟩ := mem_iUnion.1 hx₂
  obtain ⟨hang₂, htest₂⟩ := mem_iUnion.1 ha₂
  change RootJ31.candidateAngle c r a₁ = θ₁ at hang₁
  change RootJ31.candidateAngle c r a₂ = θ₂ at hang₂
  subst hang₁ hang₂
  set l₁ := (RootJ31.candidateAngle c r a₂, q₂) :: l₂ with hl₁
  set L := RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a₁, q₁) :: l₁) with hL
  set l := (RootJ31.candidateAngle c r a₁, q₁) :: l₁ with hl0
  -- times and samples
  have hT : RootJ31.historyTime c r l = q₁ := Gm.historyTime_cons c r l₁ _ q₁
  have hT₁ : RootJ31.historyTime c r l₁ = q₂ := Gm.historyTime_cons c r l₂ _ q₂
  obtain ⟨hTq₁, hqF₁, hlive₁, -⟩ := RootJ32.test_spec c r l₁ a₁ q₁ ω htest₁
  obtain ⟨hTq₂, hqF₂, hlive₂, -⟩ := RootJ32.test_spec c r l₂ a₂ q₂ ω htest₂
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive0
  have hord₁ := RootJ32.timeOrdered_historyProgram_of_alive c r l₁ ω halive₁
  have hord₂ := RootJ32.timeOrdered_historyProgram_of_alive c r l₂ ω halive₂
  have hv₁ := Gm.rootTime_le_historyTime c r l₁ hord₁
  have hv₂ := Gm.rootTime_le_historyTime c r l₂ hord₂
  have hq₂q₁ : (q₂ : ℝ≥0) ≤ q₁ := hT₁ ▸ hTq₁.le
  have hq₁0 : (0 : ℝ≥0) < q₁ := lt_of_le_of_lt zero_le hTq₁
  have hq₂0 : (0 : ℝ≥0) < q₂ := lt_of_le_of_lt zero_le hTq₂
  have hv₀q₂ : (rootEntry r.1).2 ≤ (q₂ : ℝ≥0) := hv₂.trans hTq₂.le
  -- the explored drivers
  have hW₁ : ∀ t ≤ (q₁ : ℝ≥0), schedW c r l a t ω = schedW c r l₁ a₁ t ω := hW l₁ a₁ q₁ a halive₁ htest₁
  have hW₂ : ∀ t ≤ (q₂ : ℝ≥0), schedW c r l₁ a₁ t ω = schedW c r l₂ a₂ t ω := hW l₂ a₂ q₂ a₁ halive₂ htest₂
  have hW₀₂ : ∀ t ≤ (q₂ : ℝ≥0), schedW c r l a t ω = schedW c r l₂ a₂ t ω := fun t ht =>
    (hW₁ t (ht.trans hq₂q₁)).trans (hW₂ t ht)
  -- contacts
  have hq₁c : ((q₁ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω := hT ▸ hcon a
  have hq₂c : ((q₂ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
    (ENNReal.coe_le_coe.2 hq₂q₁).trans_lt hq₁c
  have hq₁c₁ : ((q₁ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l₁ a₁) c.α ω :=
    (ENNReal.coe_le_coe.2 hqF₁.le).trans_lt (hP l₁ a₁ hlive₁)
  have hq₂c₂ : ((q₂ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l₂ a₂) c.α ω :=
    (ENNReal.coe_le_coe.2 hqF₂.le).trans_lt (hP l₂ a₂ hlive₂)
  -- good sets
  obtain ⟨hGT, -, -⟩ := schedGTX_spec h13 c r l a
  obtain ⟨hGT₁, -, -⟩ := schedGTX_spec h13 c r l₁ a₁
  obtain ⟨hGT₂, -, -⟩ := schedGTX_spec h13 c r l₂ a₂
  have hωG := (hG l a).2 hgx
  have hωG₁ := (hG l₁ a₁).2 hgx
  have hωG₂ := (hG l₂ a₂).2 hgx
  have hs := pos_of_physGoodX (hGT ω hωG)
  -- covering versions of the two passed tests
  obtain ⟨n₁, hn₁⟩ := (hC l₁ a₁ hgx q₁ hq₁c₁).exists
  obtain ⟨n₂, hn₂⟩ := (hC l₂ a₂ hgx q₂ hq₂c₂).exists
  -- the clock of the candidate
  set cl : ℝ≥0 → ℝ := fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω with hcl
  have hcl₁ : ∀ t ≤ (q₁ : ℝ≥0), clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l₁ a₁) t ω = cl t := fun t ht =>
    (GW2Sdo.clockX_congr fun u hu => hW₁ u (hu.trans ht)).symm
  have hcl₂ : ∀ t ≤ (q₂ : ℝ≥0), clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l₂ a₂) t ω = cl t := fun t ht =>
    (GW2Sdo.clockX_congr fun u hu => hW₀₂ u (hu.trans ht)).symm
  obtain ⟨-, hmono, -⟩ := clockX_props hGT hs hx hωG
  have hcl0 : ∀ t, 0 ≤ cl t := fun t => RootJ32.forwardCapacity_nonneg _ _ _ _
  have hclle : ∀ {t t' : ℝ≥0}, t ≤ t' → t' ≤ q₁ → cl t ≤ cl t' := fun {t t'} htt ht' => by
    have hc' : ((t' : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
      (ENNReal.coe_le_coe.2 ht').trans_lt hq₁c
    have hc : ((t : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
      (ENNReal.coe_le_coe.2 htt).trans_lt hc'
    exact (ENNReal.ofReal_le_ofReal_iff (hcl0 t')).1 (hmono hc hc' htt)
  have hVq₁ : ENNReal.ofReal (cl q₁) < V ω := by rw [← hT]; exact hV
  have hVq₂ : ENNReal.ofReal (cl q₂) < V ω :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hclle hq₂q₁ le_rfl)) hVq₁
  -- the versions agree with the candidate's on the history
  have hRR₁ := version_eq_of_drv_eq hGT hGT₁ hs hx hωG hωG₁ (hR hgx) (hVA l₁ a₁ n₁ hgx) hq₁0 hq₁c hq₁c₁ hW₁ hVq₁
    hn₁
  have hRR₂ := version_eq_of_drv_eq hGT hGT₂ hs hx hωG hωG₂ (hR hgx) (hVA l₂ a₂ n₂ hgx) hq₂0 hq₂c hq₂c₂ hW₀₂ hVq₂
    hn₂
  have hv₀₁ : (cl (rootEntry r.1).2).toNNReal ≤ (cl q₁).toNNReal :=
    Real.toNNReal_le_toNNReal (hclle (hv₀q₂.trans hq₂q₁) le_rfl)
  have hv₀₂ : (cl (rootEntry r.1).2).toNNReal ≤ (cl q₂).toNNReal :=
    Real.toNNReal_le_toNNReal (hclle hv₀q₂ hq₂q₁)
  -- J32's readings at the two switches
  have hX₁ := hX l₁ a₁ n₁ hlive₁ hv₁ q₁ hTq₁.le hqF₁ hn₁
  rw [hcl₁ q₁ le_rfl, hcl₁ _ (hv₀q₂.trans hq₂q₁), ← hRR₁ _ le_rfl, ← hRR₁ _ hv₀₁] at hX₁
  have hX₂ := hX l₂ a₂ n₂ hlive₂ hv₂ q₂ hTq₂.le hqF₂ hn₂
  rw [hcl₂ q₂ le_rfl, hcl₂ _ hv₀q₂, ← hRR₂ _ le_rfl, ← hRR₂ _ hv₀₂] at hX₂
  have hst := hcons l₁ a₁ q₁ halive₁ htest₁
  have hband : RootJ32.sourceX c r l₂ a₂ ω q₂ ∈ Ioo (7 / 4) (9 / 4) := htest₂.2.2.2
  -- the base word on the instance's record is flowed through the version's own pieces
  set N := (entryList l).length + 1 with hNdef
  have hLN : L.length = N := length_historyProgram c r l
  have hTj : ∀ j < N, schedTime 0 L j ≤ RootJ31.historyTime c r l := fun j hj =>
    schedTime_le_historyTime c r l hord (by rw [hLN]; exact hj.le)
  have hjT : ∀ j < N, schedTime 0 L j ≤ lastTime 0 L := fun j hj => by
    rw [← GW2Sde.historyTime_eq_lastTime]
    exact hTj j hj
  have hconj : ∀ j, 0 < j → j < N → (schedTime 0 L j : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω := fun j _ hj =>
    (ENNReal.coe_le_coe.2 ((hTj j hj).trans_eq hT)).trans_lt hq₁c
  have hagree : ∀ u ≤ RootJ31.historyTime c r l, RootJ31.joinedRead L
      (fun i => (fun j : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) (Fin.cast hLN i)) u =
        schedW c r l a u ω := fun u hu => by
    have e1 : schedW c r l a u ω = Gm.futureJoined c r l a ω u :=
      congrFun (schedW_of_oldSuccess c r l a (RootJ32.oldSuccess_of_alive c r l ω halive0)) u
    rw [e1, GW2Bf.futureJoined_eq_histJoined c r l a ω hu]
    rfl
  have hbase := baseWordX_augRecX (x₀ := rootPt r.1) (sp := c.s) (W := schedW c r l a) (Wα := c.W) (ζα := c.ζ)
    (GT := schedGTX h13 c r l a) (V := V) (T := RootJ31.historyTime c r l) (R := R) (γ := schedTr c r l a)
    (α := c.α) κ c' hGT hs hx L N hLN (xr := stageEncRec c r l) (ω := ω)
    (P := fun j : Fin N => stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j ω) rfl (hver.2.1 ω)
    (hver.2.2.1 ω) hωG (hfin ω) hTj hjT hconj hagree
  rw [hbase] at hy
  -- the two last boundaries are the clock at the two switches
  have hlen : (entryList l).length = l₁.length + 1 := by simp [hl0, entryList]
  have hb₁ : trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V L N
      (RootJ31.historyTime c r l) ω ((entryList l).length + 1) = (cl q₁).toNNReal := by
    unfold trueBdX
    rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (lt_irrefl _),
      GW2Sdo.stgStartX_eq_clockX hGT hs hx hωG (hT ▸ hq₁c) hV, hT]
  have hsched : schedTime 0 L (entryList l).length = q₂ := by
    have e : L = RootJ31.historyProgram c r l₁ ++ [((RootJ31.candidateAngle c r a₁ : ℝ), (q₁ : ℝ≥0))] :=
      RootJ31.historyProgram_cons c r l₁ _ q₁
    have hl₁len : (RootJ31.historyProgram c r l₁).length = (entryList l).length := by
      rw [length_historyProgram, hlen]
      simp [entryList]
    rw [e, schedTime_append 0 _ hl₁len.ge, ← hl₁len]
    exact hT₁
  have hb₂ : trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V L N
      (RootJ31.historyTime c r l) ω (entryList l).length = (cl q₂).toNNReal := by
    unfold trueBdX
    rw [ite_eq_right (by rw [hlen]; exact Nat.succ_ne_zero _), ite_eq_left (Nat.lt_succ_self _), hsched,
      GW2Sdo.stgStartX_eq_clockX hGT hs hx hωG hq₂c hVq₂]
  have hsweep := le_add_of_mem_jumps_stageWord_pastOf (R := fun u => R u ω) (hver.2.1 ω)
    (b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V L N
      (RootJ31.historyTime c r l) ω) (by rw [hb₁, hb₂]; exact Real.toNNReal_le_toNNReal (hclle hq₂q₁ le_rfl)) hy hy0
  rw [hb₁, hb₂] at hsweep
  -- the signs: `|l₁|` is odd, `|l₂|` even
  have hev₂ : Even l₂.length := by
    have : l.length = l₂.length + 2 := by simp [hl0, hl₁]
    rw [this] at hl
    exact (Nat.even_add.1 hl).2 (by decide)
  have hs₁ : ((-1 : ℝ) ^ l₁.length) = -1 := by
    rw [hl₁, List.length_cons, pow_succ, hev₂.neg_one_pow, one_mul]
  have hs₂ : ((-1 : ℝ) ^ l₂.length) = 1 := hev₂.neg_one_pow
  rw [hs₁] at hX₁
  rw [hs₂] at hX₂
  have hk : (0 : ℝ) < (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) := by positivity
  rw [hst, hX₁]
  have h2 := hband.1
  rw [hX₂] at h2
  nlinarith


omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
/-- **The right-mark clause of `startsU` for any presenting frame word**: if the frame word presents a raised base word
in the samples' frame (scale `rootScale k`, no reflection), and every positive label of the base word lies at absolute
position `start + 2^k y ≥ 7/4`, then every right mark other than the first does. -/
theorem rightMarks_ge_of_presentsO {κ θ start : ℝ} {k : ℕ} {base : BoundaryWord} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (h : GW2Sdf.PresentsO κ (GW2Rd.upW θ base) (GW2Sdf.rootScale k) false xL ρL xR ρR)
    (hmarks : ∀ y ∈ base.jumps, 0 < y → 7 / 4 ≤ start + (((2 : ℝ≥0) ^ k : ℝ≥0) : ℝ) * y) :
    ∀ j : Fin nR, 0 < (j : ℕ) → 7 / 4 ≤ start + xR j := by
  intro j hj
  obtain ⟨-, eR, -, hxR, -, -⟩ := h
  set β := GW2Rd.upW θ base
  set i : Fin (flowLineNR β.fn β.jumps 0) := Fin.cast eR.symm j with hi
  have hfj : Real.sqrt (GW2Sdf.rootScale k) * xR j = flowLineXR β.fn β.jumps 0 i := by
    simpa [hi] using congrFun hxR i
  have hi0 : 0 < (i : ℕ) := hj
  have hpos : 0 < flowLineXR β.fn β.jumps 0 i := by
    have h0 : flowLineXR β.fn β.jumps 0 ⟨0, Nat.succ_pos _⟩ = 0 := rfl
    have hlt := GW0.flowLineXR_lt β.fn β.jumps 0 (i := ⟨0, Nat.succ_pos _⟩) (j := i) (Fin.lt_def.2 hi0)
    rwa [h0] at hlt
  rcases Restart.RetAux79.flowLineXR_eq_zero_or_mem β i with h0 | ⟨-, hmem⟩
  · exact absurd h0 hpos.ne'
  · have hb := hmarks _ hmem hpos
    have hsq : (Real.sqrt (GW2Sdf.rootScale k))⁻¹ = (((2 : ℝ≥0) ^ k : ℝ≥0) : ℝ) := by
      rw [GW2Sdf.sqrt_rootScale_inv]
      push_cast
      rfl
    have hne : Real.sqrt (GW2Sdf.rootScale k) ≠ 0 := by
      intro h0
      have h1 : (Real.sqrt (GW2Sdf.rootScale k))⁻¹ = 0 := by rw [h0, inv_zero]
      rw [hsq] at h1
      exact absurd h1 (by positivity)
    have hx : xR j = (((2 : ℝ≥0) ^ k : ℝ≥0) : ℝ) * flowLineXR β.fn β.jumps 0 i := by
      rw [← hfj, ← hsq, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [hx]
    exact hb


/-- **The slow shell's starting word is admissible** (`Prop59Stage.startsU`): almost surely at every alive history of
even length `≥ 2`, every frame word presenting the instance's stage word `upW (θ χ) (base)` (GEOM2's map) in the
samples' frame, started at `histStart`, has its start in `(−9/4, −7/4)`, is an ordered force word, and has every right
mark other than the first at absolute position `≥ 7/4`. -/
theorem ae_startsU_of_presentsO (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hx : 0 ≤ rootPt r.1) (l : List (EntryIdx c.Θ c.Q)) (hl : Even l.length) (a : ℕ) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (hver : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hfin : ∀ ω, V ω ≠ ⊤) (κ : ℝ) (c' : BoundaryWord) (θa : ℝ) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l → 2 ≤ l.length →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) < V ω →
      ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
        GW2Sdf.PresentsO κ (schedWordMapX κ c' (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (length_historyProgram c r l) θa (augRec (stageEncRec c r l)
            (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V
              (RootJ31.historyTime c r l) R) ω)) (GW2Sdf.rootScale r.2) false xL ρL xR ρR →
        (GW2Bf.histStart c r l ω, xL, xR) ∈ Sec5.Prop59Stage.startsU := by
  filter_upwards [ae_rightMark_ge h13 c r hx l hl a hver hfin κ c', GW2Rw.ae_histStart_mem_of_alive h13 c r]
    with ω hmark hband halive hl2 hV nL nR xL ρL xR ρR hpres
  have hb : GW2Bf.histStart c r l ω ∈ Ioo (-(9 / 4)) (-(7 / 4)) := by
    rcases l with _ | ⟨x, l'⟩
    · simp at hl2
    · exact hband x l' halive
  exact ⟨hb.1, hb.2, GW2Rw.isOrderedForceWord_of_presentsO (GW2Sdf.rootScale_ne_zero r.2) hpres,
    rightMarks_ge_of_presentsO hpres (hmark halive hl2 hV)⟩

end InteractingSLE.Theorem14.GW2Ru
