/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJoin
import InteractingSLE.Spec.Supplement.GW2GmSlit
import InteractingSLE.Spec.Supplement.GW2RdLife
import InteractingSLE.Spec.Supplement.GW2RootJ31Meas
import InteractingSLE.Spec.Supplement.GW2SdePrefix

/-!
# GW2's stage identity: the explored curve at the schedule instance

Packet PROVE-GW2-RELDET, ruling R106, open item 1 of the handoff (the explored regularity). At a source `c`, root
`r`, retained history `l` and candidate `a`, GB6's explored curve is ROOT2's joined future driver
(`Gm.futureJoined c r l a`: the history's canonical pieces and the candidate's piece, concatenated at their own times).
It generates a trace on `[0, ∞)` almost surely on the event `RootJ31.oldSuccess c r l` that the history's pieces
succeeded (PROVE-GW2-GEOM2's `Gm.ae_futureJoined_trace`). Off that event the explored curve is taken to be the zero
driver (the slit). So:

* `schedW c r l a`: the joined future driver on `oldSuccess`, `0` off it; `schedTr`: a chosen trace;
* `measurable_schedW`, `continuous_schedW`, `schedW_zero`: for every sample;
* `exists_joinedDriver_frozen`: a joined driver is constant after a finite time (it is a finite concatenation);
* **`ae_schedW_trace`**: almost surely `schedTr` is a generating trace of `schedW` on `[0, ∞)` and it is transient
  (`GW2RdLife.tendsto_norm_trace_of_frozen`). These are exactly GB6's explored inputs (`hW`) in
  `GW2SxStage.exists_versionsA_uncapped` / `exists_versionsA_timeCap`;
* **`comap_schedW_le_sigma`**: up to the history's last time, `schedW` is `c.sigma r l`-measurable (the input `hW` of
  PROVE-GW2-SDE's `StageInst.prefix_retained_of_path`, part (II)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule Sec7.StripSideHeightProb GW2Schedule

/-- **A joined driver is constant after a finite positive time.** -/
theorem exists_joinedDriver_frozen {Ω' : Type*} (E : ℕ → Ω' → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω') :
    ∀ (l : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0), ∃ S : ℝ≥0, 0 < S ∧
      ∀ t : ℝ≥0, S ≤ t → joinedDriver E j a l ω t = joinedDriver E j a l ω S
  | [], _, _ => ⟨1, one_pos, fun _ _ => rfl⟩
  | ((_, T) :: l), j, a => by
    obtain ⟨S', -, hS'⟩ := exists_joinedDriver_frozen E ω l (j + 1) T
    have hlt : ∀ u : ℝ≥0, (T - a) + S' + 1 ≤ u → ¬ u ≤ T - a := fun u hu h => by
      have h1 : (((T - a) + S' + 1 : ℝ≥0) : ℝ) ≤ u := by exact_mod_cast hu
      have h2 : (u : ℝ) ≤ ((T - a : ℝ≥0) : ℝ) := by exact_mod_cast h
      push_cast at h1
      linarith [S'.coe_nonneg]
    have hge : ∀ u : ℝ≥0, (T - a) + S' + 1 ≤ u → S' ≤ u - (T - a) := fun u hu =>
      le_tsub_of_add_le_left (le_self_add.trans hu)
    refine ⟨(T - a) + S' + 1, by positivity, fun t ht => ?_⟩
    change catPath (E j ω).1 (T - a) (joinedDriver E (j + 1) T l ω) t =
      catPath (E j ω).1 (T - a) (joinedDriver E (j + 1) T l ω) ((T - a) + S' + 1)
    simp only [catPath, hlt t ht, hlt _ le_rfl, ↓reduceIte]
    rw [hS' _ (hge t ht), hS' _ (hge _ le_rfl)]

variable {Ω : Type u} [MeasurableSpace Ω]

theorem exists_futureJoined_frozen (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (ω : Ω) : ∃ S : ℝ≥0, 0 < S ∧
      ∀ t : ℝ≥0, S ≤ t → Gm.futureJoined c r l a ω t = Gm.futureJoined c r l a ω S :=
  exists_joinedDriver_frozen _ _ _ _ _

theorem measurable_futureJoined (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (t : ℝ≥0) : Measurable fun ω => Gm.futureJoined c r l a ω t := by
  have hR : Measurable (programRecords c (rootPt r.1) (futureProgram c r l a)) :=
    measurable_pi_iff.mpr fun j => measurable_stopRec c.hβA.1 c.hh.1 _ j
  exact ((measurable_pi_apply t).comp (measurable_joinedRead _)).comp hR

open scoped Classical in
/-- **The explored curve at the schedule instance**: the joined future driver where the history's pieces succeeded,
the zero driver elsewhere. -/
def schedW (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω => if oldSuccess c r l ω then Gm.futureJoined c r l a ω t else 0

open scoped Classical in
/-- A generating trace of the explored curve on `[0, ∞)` where one exists (the slit otherwise). -/
def schedTr (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    Ω → ℝ≥0 → ℂ :=
  fun ω => if h : ∃ η, IsGeneratingTrace (fun t => schedW c r l a t ω) ⊤ η then h.choose else Gm.slitTrace

variable (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

theorem schedW_of_oldSuccess {ω : Ω} (h : oldSuccess c r l ω) :
    (fun t => schedW c r l a t ω) = Gm.futureJoined c r l a ω := by
  funext t
  simp only [schedW, h, ↓reduceIte]

theorem schedW_of_not_oldSuccess {ω : Ω} (h : ¬ oldSuccess c r l ω) : (fun t => schedW c r l a t ω) = fun _ => 0 := by
  funext t
  simp only [schedW, h, ↓reduceIte]

theorem measurable_schedW (t : ℝ≥0) : Measurable (schedW c r l a t) := by
  classical
  exact Measurable.ite (measurableSet_oldSuccess c r l) (measurable_futureJoined c r l a t) measurable_const

theorem continuous_schedW (ω : Ω) : Continuous fun t => schedW c r l a t ω := by
  by_cases h : oldSuccess c r l ω
  · rw [schedW_of_oldSuccess c r l a h]
    exact (Gm.continuous_futureJoined c r l a ω).1
  · rw [schedW_of_not_oldSuccess c r l a h]
    exact continuous_const

theorem schedW_zero (ω : Ω) : schedW c r l a 0 ω = 0 := by
  by_cases h : oldSuccess c r l ω
  · simp only [schedW, h, ↓reduceIte]
    exact (Gm.continuous_futureJoined c r l a ω).2
  · simp only [schedW, h, ↓reduceIte]

theorem exists_schedW_frozen (ω : Ω) :
    ∃ S : ℝ≥0, 0 < S ∧ ∀ t : ℝ≥0, S ≤ t → schedW c r l a t ω = schedW c r l a S ω := by
  by_cases h : oldSuccess c r l ω
  · obtain ⟨S, hS, hfr⟩ := exists_futureJoined_frozen c r l a ω
    refine ⟨S, hS, fun t ht => ?_⟩
    simp only [schedW, h, ↓reduceIte]
    exact hfr t ht
  · refine ⟨1, one_pos, fun t _ => ?_⟩
    simp only [schedW, h, ↓reduceIte]

/-- **The explored curve at the schedule instance generates a transient trace on `[0, ∞)`, almost surely.** -/
theorem ae_schedW_trace [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u}) :
    ∀ᵐ ω ∂c.P, IsGeneratingTrace (fun t => schedW c r l a t ω) ⊤ (schedTr c r l a ω) ∧
      Tendsto (fun t => ‖schedTr c r l a ω t‖) atTop atTop := by
  filter_upwards [Gm.ae_futureJoined_trace h13 c r] with ω hω
  have hex : ∃ η, IsGeneratingTrace (fun t => schedW c r l a t ω) ⊤ η := by
    by_cases h : oldSuccess c r l ω
    · obtain ⟨-, η, hη⟩ := hω l a h
      exact ⟨η, by rw [schedW_of_oldSuccess c r l a h]; exact hη⟩
    · exact ⟨Gm.slitTrace, by rw [schedW_of_not_oldSuccess c r l a h]; exact Gm.isGeneratingTrace_zero_slit⟩
  have htr : IsGeneratingTrace (fun t => schedW c r l a t ω) ⊤ (schedTr c r l a ω) := by
    have e : schedTr c r l a ω = hex.choose := by simp only [schedTr, hex, ↓reduceDIte]
    rw [e]
    exact hex.choose_spec
  obtain ⟨S, hS, hfr⟩ := exists_schedW_frozen c r l a ω
  exact ⟨htr, tendsto_norm_trace_of_frozen (continuous_schedW c r l a ω) (schedW_zero c r l a ω) hS hfr htr⟩

/-- **Up to the history's last time, the explored curve is read from the retained history.** -/
theorem comap_schedW_le_sigma {t : ℝ≥0} (ht : t ≤ historyTime c r l) :
    MeasurableSpace.comap (schedW c r l a t) inferInstance ≤ c.sigma r l := by
  classical
  have ht' : t ≤ lastTime 0 (historyProgram c r l) := ht.trans_eq (GW2Sde.historyTime_eq_lastTime c r l)
  have e : schedW c r l a t = fun ω => if oldSuccess c r l ω then
      joinedRead (historyProgram c r l) (programRecords c (rootPt r.1) (historyProgram c r l) ω) t else 0 := by
    funext ω
    by_cases h : oldSuccess c r l ω
    · simp only [schedW, h, ↓reduceIte]
      exact GW2Sde.joinedRead_future_eq_history c r l a ω ht'
    · simp only [schedW, h, ↓reduceIte]
  rw [e]
  exact (Measurable.ite (measurableSet_oldSuccess_rootSigma c r l)
    (GW2Sde.measurable_joinedRead_history_sigma c r l t) measurable_const).comap_le

end InteractingSLE.Theorem14.GW2Rd
