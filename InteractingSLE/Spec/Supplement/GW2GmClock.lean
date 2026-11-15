/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJoin
import InteractingSLE.Spec.Supplement.GW2RootI30Cover
import InteractingSLE.Spec.Supplement.GW2RootI30Capacity
import InteractingSLE.Spec.Supplement.GW2RootK32Active
import InteractingSLE.Spec.Supplement.GB6SourceCContact

/-!
# The switched capacity clock of J31 along the whole live prefix

Packet PROVE-GW2-GEOM2 (step R4 of PROVE-GW2-SWITCH's plan). J31 reads the relative capacity of a
switched prefix from the joined future record, `RootH29.forwardCapacity x s t (RootJ31.futurePair …)`.
I30's reader chain (`RootI30.exists_reader_chain`) is stated for any regular driver with a generating
trace. With the joined driver of `GW2GmJoin` it applies to the whole switched prefix:

* `forwardCapacity_congr`: the capacity reader at time `t` only reads the decoded driver on `[0, t]`;
* `lt_firstContactTime_iff_noncontact`, `lt_translatedContact_iff`: before-contact in pointwise form;
* **`clock_of_joined_trace`** (deterministic): strict continuous growth from `0`, and the identification
  with the capacity of the mapped trace prefix, up to any time before K32's reconstructed contact;
* **`ae_live_clock`**: almost surely, for every history and candidate whose sample is live, the clock
  `t ↦ forwardCapacity x s t (futurePair …)` starts at `0` and is strictly increasing and continuous on
  `[0, T + F]` (`T` the history time, `F` the buffer), equals the capacity of the mapped trace prefix,
  and the joined trace on `[0, T + F]` does not meet the inverted counterflow prefix.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Supp8.GB6

/-- **The capacity reader at time `t` only reads the decoded driver on `[0, t]`.** -/
theorem forwardCapacity_congr (x : ℝ) (s t : ℝ≥0) (p₁ : RecData) {r r' : RecData}
    (h : ∀ y ∈ Icc (0 : ℝ) t, rdrv r y = rdrv r' y) :
    RootH29.forwardCapacity x s t (p₁, r) = RootH29.forwardCapacity x s t (p₁, r') := by
  have hK : QuantumZipper.fwdHull (rdrv r) t = QuantumZipper.fwdHull (rdrv r') t :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_rdrv r) (continuous_rdrv r')
      (NNReal.coe_nonneg t) h
  simp only [RootH29.forwardCapacity, RootH29.forwardHull, RootH29.translatedHull, hK]

/-- Strictly before the first contact of the inverted path with a compact prefix, in pointwise form. -/
theorem lt_firstContactTime_iff_noncontact {γ α : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (hα : Continuous α) (T s : ℝ≥0) :
    (T : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) ↔
      ∀ t ∈ Icc 0 T, ∀ u ∈ Icc 0 s, γ t * α u + 1 ≠ 0 := by
  rw [SourceC.lt_firstContactTime_iff hγ hα, SourceC.prefixGap_pos_iff hγ hα]

/-- A live joined future record is before contact up to `v` iff the joined trace and the counterflow
prefix are separated on `[0, v] × [0, s]`. -/
theorem lt_translatedContact_iff {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α) (hW : Continuous (W · ω))
    (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) (x : ℝ) (s : ℝ≥0) {J : ℝ≥0 → ℝ} (hJ : Continuous J)
    (hJ0 : J 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ) {v L : ℝ≥0} (hvL : v ≤ L) :
    (v : ℝ≥0∞) < RootK32.translatedContact x s L
        (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J) ↔
      ∀ t ∈ Icc 0 v, ∀ u ∈ Icc 0 s, ((x : ℂ) + γ t) * α u + 1 ≠ 0 := by
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous α := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have h2 : RootG28.frozenTraceRead L (StagedEntrance.Strip.recOfDriver L J) =
      fun t => γ (min t L) := frozenTraceRead_recOfDriver hJ hJ0 hγ
  have h1 : RootG28.frozenTraceRead s (cfRec s W ζ ω) = fun t => α (min t s) :=
    RootG28.frozenTraceRead_cfRec_eq W ζ s ω hW hW0 hζ hα
  have himg : (fun u => (RootG28.frozenTraceRead s (cfRec s W ζ ω) u : OnePoint ℂ)) '' Icc 0 s =
      (fun u => (α u : OnePoint ℂ)) '' Icc 0 s := by
    rw [h1]
    exact image_congr fun u hu => by simp only [min_eq_left hu.2]
  unfold RootK32.translatedContact
  change (v : ℝ≥0∞) < firstContactTime
      (fun t => sphereInv (((x : ℂ) + RootG28.frozenTraceRead L
        (StagedEntrance.Strip.recOfDriver L J) t : ℂ) : OnePoint ℂ))
      ((fun u => (RootG28.frozenTraceRead s (cfRec s W ζ ω) u : OnePoint ℂ)) '' Icc 0 s) ↔ _
  rw [himg, h2]
  have hcont : Continuous fun t => (x : ℂ) + γ (min t L) :=
    continuous_const.add (hγc.comp (continuous_id.min continuous_const))
  exact (lt_firstContactTime_iff_noncontact hcont hαc v s).trans
    (forall₂_congr fun t ht => by simp only [min_eq_left (ht.2.trans hvL)])

/-- **The clock of a joined trace before contact.** For a continuous driver `J` from `0` generating `γ`
on `[0, ∞)`, read through its record at a cap `L`, and for `v ≤ L` strictly before the reconstructed
contact with the counterflow prefix, the capacity reader `t ↦ forwardCapacity x s t (cfRec, recOfDriver L J)`
starts at `0`, is strictly increasing and continuous on `[0, v]`, and is the capacity of the mapped trace
prefix there (I30's reader chain). -/
theorem clock_of_joined_trace {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α) (hW : Continuous (W · ω))
    (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) {J : ℝ≥0 → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ) {v L : ℝ≥0} (hvL : v ≤ L)
    (hv : (v : ℝ≥0∞) < RootK32.translatedContact x s L
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) :
    let A := fun t => RootH29.forwardCapacity x s t
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)
    A 0 = 0 ∧ StrictMonoOn A (Icc 0 v) ∧ ContinuousOn A (Icc 0 v) ∧
      ∀ t ∈ Icc 0 v, capOf (relMap (rdrv (cfRec s W ζ ω)) s ''
        ((fun q => (x : ℂ) + γ q) '' Icc 0 t ∩ H)) = A t := by
  intro A
  have he : IsRegularDriver (J, ⊤) := isRegularDriver_top hJ hJ0
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous α := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hnc := (lt_translatedContact_iff W ζ ω hα hW hW0 hζ x s hJ hJ0 hγ hvL).1 hv
  have hv' : (v : ℝ≥0∞) < min (firstContactTime
      (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (J, (⊤ : ℝ≥0∞)).2 := by
    change _ < min _ ⊤
    rw [min_top_right]
    exact (lt_firstContactTime_iff_noncontact (continuous_const.add hγc) hαc v s).2 hnc
  -- the reader record at `v` and the joined record at `L` decode to the same driver on `[0, v]`
  have hag : ∀ t ∈ Icc 0 v, RootH29.forwardCapacity x s t
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (J, ⊤)) = A t := by
    intro t ht
    refine forwardCapacity_congr x s t _ fun y hy => ?_
    have hy0 : 0 ≤ y := hy.1
    have hyv : y.toNNReal ≤ v := Real.toNNReal_le_iff_le_coe.2 (hy.2.trans (NNReal.coe_le_coe.2 ht.2))
    have e1 : rdrv (recOf (v : ℝ≥0∞) (J, ⊤)) y = J (min y.toNNReal v) := by
      have h := rdrv_recOfDriver hJ hJ0 (q₀ := v) y.toNNReal
      rw [Real.coe_toNNReal _ hy0, recOfDriver_eq_recOf] at h
      exact h
    have e2 : rdrv (StagedEntrance.Strip.recOfDriver L J) y = J (min y.toNNReal L) := by
      have h := rdrv_recOfDriver hJ hJ0 (q₀ := L) y.toNNReal
      rw [Real.coe_toNNReal _ hy0] at h
      exact h
    rw [e1, e2, min_eq_left hyv, min_eq_left (hyv.trans hvL)]
  obtain ⟨_, _, h0, hm, hc, _⟩ := RootI30.exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv'
  have hcap := RootI30.capOf_mapped_prefix_eq_reader W ζ ω hα hW hW0 hζ hs hx harc he hγ hv'
  have hv0 : (0 : ℝ≥0) ∈ Icc 0 v := ⟨le_rfl, zero_le⟩
  refine ⟨(hag 0 hv0).symm.trans h0, ?_, ?_, fun t ht => (hcap t ht).trans (hag t ht)⟩
  · intro a ha b hb hab
    rw [← hag a ha, ← hag b hb]
    exact hm ha hb hab
  · exact hc.congr fun t ht => (hag t ht).symm

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- The last time of a future program is the history time plus the candidate's cap. -/
theorem lastTime_futureProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    Sec5.Prop513Schedule.lastTime 0 (RootJ31.futureProgram c r l a) =
      RootJ31.historyTime c r l + RootJ31.candidateCap c r a := by
  rw [Sec5.Prop513Schedule.lastTime_eq_getLast _ _ (by simp [RootJ31.futureProgram])]
  simp only [RootJ31.futureProgram, List.getLast_append, List.isEmpty_cons, Bool.false_eq_true,
    ↓reduceDIte, List.getLast_singleton]

/-- **The switched capacity clock along the live prefix.** Almost surely, for every history `l` and
candidate `a` whose sample is live, the capacity reader of the future record starts at `0`, is strictly
increasing and continuous on `[0, T + F]` (`T` the history time, `F` the physical buffer), and is the
capacity of the mapped prefix of the joined trace there. -/
theorem ae_live_clock (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      0 < (RootJ31.sourceSample c r l a ω).1 →
      let A := fun t => RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ω)
      let v := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω
      ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (futureJoined c r l a ω) ⊤ γ ∧
        A 0 = 0 ∧ StrictMonoOn A (Icc 0 v) ∧ ContinuousOn A (Icc 0 v) ∧
        (∀ t ∈ Icc 0 v, capOf (relMap (rdrv (cfRec c.s c.W c.ζ ω)) c.s ''
          ((fun q => (rootPt r.1 : ℂ) + γ q) '' Icc 0 t ∩ H)) = A t) ∧
        ∀ t ∈ Icc 0 v, ∀ u ∈ Icc 0 c.s, ((rootPt r.1 : ℂ) + γ t) * c.α ω u + 1 ≠ 0 := by
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ, ae_futureJoined_trace h13 c r]
    with ω hcover hα hreg hζ hjoin l a hlive
  intro A v
  obtain ⟨hcov, hold, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ω hlive
  obtain ⟨hseed, hsH, -, -, -, harc⟩ := hcover hcov
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  obtain ⟨-, γ, hγ⟩ := hjoin l a hold
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l a ω
  have hvL : v ≤ Sec5.Prop513Schedule.lastTime 0 (RootJ31.futureProgram c r l a) := by
    rw [lastTime_futureProgram]
    exact add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω)
  have hv := RootK32.sourceSample_live_before_contact c r l a ω hlive
  rw [← lastTime_futureProgram] at hv
  obtain ⟨h0, hm, hc, hcap⟩ := clock_of_joined_trace c.W c.ζ ω hα hW hW0 hζ hs
    (RootH29.rootPt_nonneg_of_seedOK c hseed) harc hJ hJ0 hγ hvL hv
  exact ⟨γ, hγ, h0, hm, hc, hcap,
    (lt_translatedContact_iff c.W c.ζ ω hα hW hW0 hζ (rootPt r.1) c.s hJ hJ0 hγ hvL).1 hv⟩

end InteractingSLE.Theorem14.GW2TipSystem.Gm
