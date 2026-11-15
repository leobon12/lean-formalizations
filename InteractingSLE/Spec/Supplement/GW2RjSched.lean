/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjPast
import InteractingSLE.Spec.Supplement.GW2RjWin
import InteractingSLE.Spec.Supplement.GW2RjJoint
import InteractingSLE.Spec.Supplement.GW2RjLife
import InteractingSLE.Spec.Supplement.GW2RuShell
import InteractingSLE.Spec.Supplement.GW2RootJ31Alive
import InteractingSLE.Spec.Supplement.GW2NtInt
import InteractingSLE.Spec.Supplement.GW2RvDrv
import InteractingSLE.Spec.Supplement.GW2SdoNear
import InteractingSLE.Spec.Supplement.GW2SdsN3
import InteractingSLE.Spec.Supplement.GW2RqBand

/-!
# Schedules of sub-histories, strict clocks, and the window transfers (decision D33)

PROVE-GW2-ROOTX round 9. Tools for the window certificates at an alive history:

* `schedTime_append_list`, **`historyProgram_drop`**, **`schedTime_of_drop`**: the program of a history extends the
  program of every sub-history `l.drop k = x :: l'`; its stage times there are `historyTime l'` and `x.2`;
* `historyTime_drop_le`, **`schedW_eq_of_drop`**: along an alive history the explored driver agrees with the passed
  test's candidate of every sub-history up to that test's time (`GW2Ru.ae_cons_schedW_eq`, chained);
* `clockX_strictMonoOn` (`GW2Rz.clock_props`);
* **`ne_of_noBad`**, **`ne_zero_of_noReturn`**: a window trace equal to a stage driver's trace below a cap inherits
  avoidance of the junction interval (round 8's `mem_avoidQ_stageWord`) and no return; `traceAt_eq_shiftTip`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open QuantumZipper.RS (shiftDrive)

universe u

namespace InteractingSLE.Theorem14.GW2Rj

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rq GW2Schedule

/-! ### Programs of sub-histories -/

theorem schedTime_append_list (τ₀ : ℝ≥0) :
    ∀ (l₂ l₁ : List (ℝ × ℝ≥0)) {j : ℕ}, j ≤ l₁.length → schedTime τ₀ (l₁ ++ l₂) j = schedTime τ₀ l₁ j
  | [], l₁, _, _ => by rw [List.append_nil]
  | y :: l₂, l₁, j, hj => by
    have e : l₁ ++ y :: l₂ = (l₁ ++ [y]) ++ l₂ := by simp
    rw [e, schedTime_append_list τ₀ l₂ (l₁ ++ [y]) (by simp; omega), schedTime_append τ₀ y hj]

/-- The schedule times of a time-ordered program are monotone on `[0, length]`. -/
theorem schedTime_mono_of_timeOrdered {L : List (ℝ × ℝ≥0)} (hL : Sec5.Prop513Schedule.TimeOrdered 0 L) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ L.length) : schedTime 0 L i ≤ schedTime 0 L j := by
  rcases i with _ | i
  · exact zero_le
  · rcases j with _ | j
    · omega
    · rw [Gm.schedTime_succ_eq_getElem (by omega), Gm.schedTime_succ_eq_getElem (by omega)]
      rcases eq_or_lt_of_le (Nat.le_of_succ_le_succ hij) with h | h
      · subst h; exact le_rfl
      · exact List.pairwise_iff_getElem.1 hL.1 i j (by omega) (by omega) h

variable {Ω : Type u} [MeasurableSpace Ω]

theorem historyProgram_drop (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), ∃ L₂ : List (ℝ × ℝ≥0),
      RootJ31.historyProgram c r l = RootJ31.historyProgram c r (l.drop k) ++ L₂
  | 0, l => ⟨[], by simp⟩
  | _ + 1, [] => ⟨[], by simp⟩
  | k + 1, x :: l => by
    obtain ⟨L₂, h⟩ := historyProgram_drop c r k l
    refine ⟨L₂ ++ [((x.1 : ℝ), (x.2 : ℝ≥0))], ?_⟩
    obtain ⟨θ, q⟩ := x
    rw [RootJ31.historyProgram_cons, h, List.drop_succ_cons, List.append_assoc]

theorem length_historyProgram' (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    (RootJ31.historyProgram c r l).length = l.length + 1 := by
  rw [GW2Ru.length_historyProgram]
  simp [entryList]

/-- **The stage times of a history at a sub-history.** -/
theorem schedTime_of_drop (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {l l' : List (EntryIdx c.Θ c.Q)} {k : ℕ}
    {x : EntryIdx c.Θ c.Q} (hk : l.drop k = x :: l') :
    schedTime 0 (RootJ31.historyProgram c r l) (l'.length + 1) = RootJ31.historyTime c r l' ∧
      schedTime 0 (RootJ31.historyProgram c r l) (l'.length + 2) = (x.2 : ℝ≥0) := by
  obtain ⟨L₂, hL⟩ := historyProgram_drop c r k l
  rw [hk] at hL
  have hlen := length_historyProgram' c r (x :: l')
  have hlen' := length_historyProgram' c r l'
  simp only [List.length_cons] at hlen
  rw [hL]
  constructor
  · obtain ⟨θ, q⟩ := x
    rw [schedTime_append_list 0 L₂ _ (by rw [hlen]; omega), RootJ31.historyProgram_cons,
      schedTime_append 0 _ (by rw [hlen'])]
    rw [RootJ31.historyTime, hlen']
  · rw [schedTime_append_list 0 L₂ _ (by rw [hlen])]
    obtain ⟨θ, q⟩ := x
    have h := Gm.historyTime_cons c r l' θ q
    rw [RootJ31.historyTime, length_historyProgram' c r ((θ, q) :: l'), List.length_cons] at h
    exact h

/-- The root's entry is the first stage time of every history. -/
theorem schedTime_one (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    schedTime 0 (RootJ31.historyProgram c r l) 1 = (rootEntry r.1).2 := by
  obtain ⟨L₂, hL⟩ := historyProgram_drop c r l.length l
  rw [List.drop_length] at hL
  rw [hL, schedTime_append_list 0 L₂ _ (by rw [length_historyProgram']; simp)]
  have h := GW2Ru.historyTime_nil c r
  rw [RootJ31.historyTime, length_historyProgram'] at h
  simpa using h

/-! ### Alive histories: times and explored drivers along the sub-histories -/

variable [StandardBorelSpace Ω]

/-- The history time does not increase along drops of an alive history. -/
theorem historyTime_drop_le (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {ω : Ω} :
    ∀ (k : ℕ) (l : List (EntryIdx c.Θ c.Q)),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      RootJ31.historyTime c r (l.drop k) ≤ RootJ31.historyTime c r l
  | 0, _, _ => le_rfl
  | _ + 1, [], _ => le_rfl
  | k + 1, x :: l, h => by
    obtain ⟨a, hang, ht⟩ := exists_test_of_alive_cons c r h
    have h1 := historyTime_drop_le c r k l h.1
    have h2 := (RootJ32.test_spec c r l a x.2 ω ht).1
    obtain ⟨θ, q⟩ := x
    rw [List.drop_succ_cons, Gm.historyTime_cons]
    exact h1.trans h2.le

/-- **The explored driver along an alive history** agrees with the passed test's candidate of every sub-history up
to the test's time (given SDE's one-step agreement `GW2Ru.ae_cons_schedW_eq` at the sample). -/
theorem schedW_eq_of_drop (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) {ω : Ω}
    (hW : ∀ (l : List (EntryIdx c.Θ c.Q)) (a₀ : ℕ) (q : c.Q) (a : ℕ),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ω ∈ (RootJ32.experiment c r).data.tests l a₀ q → ∀ t ≤ (q : ℝ≥0),
        GW2Rd.schedW c r ((RootJ31.candidateAngle c r a₀, q) :: l) a t ω = GW2Rd.schedW c r l a₀ t ω) :
    ∀ (k : ℕ) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {x : EntryIdx c.Θ c.Q} {l' : List (EntryIdx c.Θ c.Q)} {a' : ℕ},
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l → l.drop k = x :: l' →
      RootJ31.candidateAngle c r a' = x.1 → ω ∈ (RootJ32.experiment c r).data.tests l' a' x.2 →
      ∀ t ≤ (x.2 : ℝ≥0), GW2Rd.schedW c r l a t ω = GW2Rd.schedW c r l' a' t ω
  | 0, l, a, x, l', a', hl, hk, hang, ht, t, htq => by
    rw [List.drop_zero] at hk
    subst hk
    have e : x = (RootJ31.candidateAngle c r a', x.2) := Prod.ext hang.symm rfl
    have hl' : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l' := hl.1
    rw [e]
    exact hW l' a' x.2 a hl' ht t htq
  | k + 1, [], a, x, l', a', _, hk, _, _, _, _ => by simp at hk
  | k + 1, y :: l, a, x, l', a', hl, hk, hang, ht, t, htq => by
    rw [List.drop_succ_cons] at hk
    obtain ⟨b, hbang, hbt⟩ := exists_test_of_alive_cons c r hl
    have hl₁ : ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l := hl.1
    have hxy : (x.2 : ℝ≥0) ≤ (y.2 : ℝ≥0) := by
      have h1 := historyTime_drop_le c r k l hl₁
      rw [hk] at h1
      have h2 := (RootJ32.test_spec c r l b y.2 ω hbt).1
      obtain ⟨θ, q⟩ := x
      rw [Gm.historyTime_cons] at h1
      exact h1.trans h2.le
    have e : y = (RootJ31.candidateAngle c r b, y.2) := Prod.ext hbang.symm rfl
    have h1 : GW2Rd.schedW c r (y :: l) a t ω = GW2Rd.schedW c r l b t ω := by
      rw [e]
      exact hW l b y.2 a hl₁ hbt t (htq.trans hxy)
    rw [h1]
    exact schedW_eq_of_drop c r hW k l b hl₁ hk hang ht t htq

/-! ### Strict clocks -/

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
theorem clockX_strictMonoOn {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ}
    {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} (hGT : ∀ ω ∈ GT, GW2Rz.PhysGoodX x s W' ζ' w γ α ω) (hs : 0 < s) (hx : 0 ≤ x)
    {ω : Ω} (hω : ω ∈ GT) :
    StrictMonoOn (fun t => GW2Rz.clockX x s W' ζ' w t ω) {t | (t : ℝ≥0∞) < GW2Rz.contactX x s γ α ω} := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
  obtain ⟨-, hm, -⟩ := GW2Rz.clock_props W' ζ' ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  exact hm

/-! ### Window transfers -/

/-- **A window trace avoids the junction interval** if it is a safe stage driver's trace below the cap. -/
theorem ne_of_noBad {κ θa : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {S : Type*} (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hθa : θa ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (j : ℕ)
    (x : GW2JDetR5.Past S j) {β : BoundaryWord}
    (hβ : β = GW2Rd.upW (θa * chiC κ) (GW2JDetR5.stageWord (κ := κ) W₀ θ j x))
    {Γ ψ : ℝ≥0 → ℂ} {V T' : ℝ≥0∞} (hnb : ¬ BadQ κ 0 β Γ V) (hT'V : T' ≤ V)
    (hΓ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' → Γ t = ψ t) (hψc : Continuous ψ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T')
    {z : ℝ} (hzL : GW2Sdp.junctionL j x < z) (hzR : z < GW2Sdp.junctionR j x) (hz0 : z ≠ 0) : ψ t ≠ (z : ℂ) := by
  intro h
  apply hnb
  refine badQ_mono hT'V (badQ_congr (fun t ht => (hΓ t ht).symm) ?_)
  refine badQ_of_mem_avoidQ hψc.continuousOn ht ?_
  rw [h, hβ]
  exact mem_avoidQ_stageWord hκ hκ4 W₀ θ hθ j x hθa hzL hzR hz0

/-- **A window trace never returns to its start** if it is a safe stage driver's trace below the cap. -/
theorem ne_zero_of_noReturn {Γ ψ : ℝ≥0 → ℂ} {V T' : ℝ≥0∞} (hnr : ¬ ReturnQ Γ V) (hT'V : T' ≤ V)
    (hΓ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' → Γ t = ψ t) (hψc : Continuous ψ) {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < T') : ψ t ≠ 0 := by
  intro h
  apply hnr
  refine returnQ_mono hT'V (returnQ_congr (fun t ht => (hΓ t ht).symm) ?_)
  exact (returnQ_iff hψc.continuousOn).2 ⟨t, ht0, ht, h⟩

/-- The trace of a driver equal to a window driver is the window chart's tip. -/
theorem traceAt_eq_shiftTip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {η : ℝ → ℂ} (hη : IsLoewnerTrace U η)
    {a : ℝ} (ha : 0 ≤ a) {w : ℝ≥0 → ℝ} {T : ℝ≥0} (hw : ∀ u : ℝ≥0, u ≤ T → w u = shiftDrive U a u) {t : ℝ≥0}
    (ht : t ≤ T) : LP.traceAt t w = loewnerTip (shiftDrive U a) t := by
  obtain ⟨hψ, -⟩ := hη.isLoewnerTrace_shift_and_extendFrom hU hU0 ha
  have hUa : Continuous (shiftDrive U a) := QuantumZipper.RS.continuous_shiftDrive hU a
  have hψ' : IsLoewnerTrace (fun s : ℝ => (fun u : ℝ≥0 => shiftDrive U a u) s.toNNReal)
      (loewnerTip (shiftDrive U a)) := by
    refine (isLoewnerTrace_congr_drive fun s hs => ?_).1 hψ
    simp only [Real.coe_toNNReal _ hs]
  have hgen := IsLoewnerTrace.isGeneratingTrace (w := fun u : ℝ≥0 => shiftDrive U a u) hψ'
  rw [LP.traceAt_congr fun r hr => hw r (hr.trans ht)]
  exact LP.traceAt_eq_of_isGeneratingTrace hgen (hUa.comp NNReal.continuous_coe).continuousOn
    (by simp only [NNReal.coe_zero, QuantumZipper.RS.shiftDrive_zero]) ENNReal.coe_lt_top

end InteractingSLE.Theorem14.GW2Rj
