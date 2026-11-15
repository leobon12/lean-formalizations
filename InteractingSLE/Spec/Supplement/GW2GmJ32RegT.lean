/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Tip
import InteractingSLE.Spec.Supplement.GW2GmJ32Reg
import InteractingSLE.Spec.Supplement.GW2GmJ32Iface

/-!
# `regularity` for J32 (ruling R111's successor field), complete

Packet PROVE-GW2-GEOM2 (round 4). With the tip read at lifetime `⊤` (fix F3), J32's tip is continuous on the
window `(S, F)` and spends zero Lebesgue time off `ℍ` there:

* `continuous_orientTip`;
* **`regularity_tip_of_clock`** (deterministic): on `(S, w)`, `S ≥ T ≥ v₀`, the oriented tip is continuous and its
  boundary time is contained in the translate by `v₀` of the boundary time of the physical trace mapped out at
  `v₀`, which is null by Lemma 2.5;
* `ae_regularity_tip_J32`: the last two clauses of `regularity`, almost surely on alive histories;
* **`RootJ32.regularity`**: the full `regularity` field of `Gm.ExperimentGeometryV` for J32 (with
  `ae_regularity_X_J32` for the first three clauses).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open QuantumZipper.RS (shiftDrive)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6
  Supp8.GB6.CoordB Sec5.Prop513Schedule

theorem continuous_orientTip (n : ℕ) : Continuous (RootJ31.orientTip n) := by
  classical
  change Continuous (fun z : ℂ => if Even n then z else -star z)
  by_cases hn : Even n
  · simp only [hn, ↓reduceIte]
    exact continuous_id
  · simp only [hn, ↓reduceIte]
    exact Complex.continuous_conj.neg

/-- **The tip clauses of `regularity`, deterministic.** In the setting of `jointTip_spec`, for a history time
`T ≥ v₀` and an entry `S ≥ T`, J32's oriented tip `q ↦ orientTip n (jointTipRead … (U (T + (q⁺ − T))))` is
continuous on `(S, w)` and spends zero Lebesgue time off `ℍ` there. -/
theorem regularity_tip_of_clock {Ω' : Type*} (W : ℝ≥0 → Ω' → ℝ) (ζ : Ω' → ℝ≥0∞) (ω : Ω')
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α) (hW : Continuous (W · ω))
    (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1) {J : ℝ≥0 → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ) {w L : ℝ≥0} (hwL : w ≤ L)
    (hnc : ∀ t ∈ Icc 0 w, ∀ u ∈ Icc 0 s, ((x : ℂ) + γ t) * α u + 1 ≠ 0)
    (hA00 : RootH29.forwardCapacity x s 0
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J) = 0)
    (hm : StrictMonoOn (fun t => RootH29.forwardCapacity x s t
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t
      (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) (Icc 0 w))
    {k : ℝ≥0} (hk : 0 < k) {v₀ T : ℝ≥0} (hv₀T : v₀ ≤ T) (n : ℕ) {S : ℝ} (hS : (T : ℝ) ≤ S) :
    ContinuousOn (fun q : ℝ => RootJ31.orientTip n (RootJ32.jointTipRead k x s L v₀
        (RootJ31.capacityIncrement k x s v₀ ((T + (q.toNNReal - T)) - v₀)
          (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J))
        (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J))) (Ioo S w) ∧
      volume {q : ℝ | q ∈ Ioo S w ∧ RootJ31.orientTip n (RootJ32.jointTipRead k x s L v₀
        (RootJ31.capacityIncrement k x s v₀ ((T + (q.toNNReal - T)) - v₀)
          (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J))
        (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) ∉ H} = 0 := by
  set p := (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J) with hp
  set Γ₀ : ℝ≥0 → ℂ := fun t' => RootJ32.jointTipRead k x s L v₀
    (RootJ31.capacityIncrement k x s v₀ (t' - v₀) p) p with hΓ₀
  have hspec := fun {t : ℝ≥0} (hv₀t : v₀ ≤ t) (htw : t < w) =>
    jointTip_spec W ζ ω hα hW hW0 hζ hs hx harc hJ hJ0 hγ hwL hnc hA00 hm hc hk hv₀t htw
  -- on `q > T` the history time drops out
  have hfold : ∀ q : ℝ, (T : ℝ) < q →
      RootJ31.orientTip n (RootJ32.jointTipRead k x s L v₀
        (RootJ31.capacityIncrement k x s v₀ ((T + (q.toNNReal - T)) - v₀) p) p) =
        RootJ31.orientTip n (Γ₀ q.toNNReal) := by
    intro q hq
    have hq0 : 0 ≤ q := T.coe_nonneg.trans hq.le
    have hTq : T ≤ q.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
      exact hq.le
    rw [add_tsub_cancel_of_le hTq]
  have hwin : ∀ q ∈ Ioo S (w : ℝ), (T : ℝ) < q ∧ v₀ ≤ q.toNNReal ∧ q.toNNReal < w := by
    intro q hq
    have hTq : (T : ℝ) < q := hS.trans_lt hq.1
    have hq0 : 0 ≤ q := T.coe_nonneg.trans hTq.le
    refine ⟨hTq, ?_, (Real.toNNReal_lt_iff_lt_coe hq0).2 hq.2⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
    exact (NNReal.coe_le_coe.2 hv₀T).trans hTq.le
  refine ⟨fun q hq => ?_, ?_⟩
  · -- continuity
    obtain ⟨hTq, hv₀q, hqw⟩ := hwin q hq
    have hc0 : ContinuousAt (fun q : ℝ => RootJ31.orientTip n (Γ₀ q.toNNReal)) q :=
      (continuous_orientTip n).continuousAt.comp
        ((hspec hv₀q hqw).1.comp continuous_real_toNNReal.continuousAt)
    refine (hc0.congr ?_).continuousWithinAt
    filter_upwards [lt_mem_nhds hTq] with q' hq'
    exact (hfold q' hq').symm
  · -- the boundary time
    have hLJ : IsLoewnerTrace (fun r : ℝ => J r.toNNReal) (fun r : ℝ => γ r.toNNReal) :=
      isLoewnerTrace_of_isGeneratingTrace hγ
    have hJc : Continuous fun r : ℝ => J r.toNNReal := hJ.comp continuous_real_toNNReal
    have hJr0 : (fun r : ℝ => J r.toNNReal) 0 = 0 := by simp [hJ0]
    have hnull := volume_shiftTip_notMem_H hLJ hJc hJr0 v₀.coe_nonneg
    refine measure_mono_null (t := (fun q : ℝ => q + (-(v₀ : ℝ))) ⁻¹'
      {τ : ℝ | 0 ≤ τ ∧ loewnerTip (shiftDrive (fun r : ℝ => J r.toNNReal) v₀) τ ∉ H})
      ?_ (by rw [measure_preimage_add_right]; exact hnull)
    rintro q ⟨hq, hqH⟩
    obtain ⟨hTq, hv₀q, hqw⟩ := hwin q hq
    have hq0 : 0 ≤ q := T.coe_nonneg.trans hTq.le
    have hv₀q' : (v₀ : ℝ) ≤ q := (NNReal.coe_le_coe.2 hv₀T).trans hTq.le
    refine ⟨by simp only; linarith, fun hψ => hqH ?_⟩
    rw [hfold q hTq, RootJ31.orientTip_mem_H_iff]
    refine (hspec hv₀q hqw).2 ?_
    rw [Real.coe_toNNReal _ hq0]
    simpa only [sub_eq_add_neg] using hψ

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The tip clauses of `regularity` for J32**: almost surely, on alive histories with `S < F`, J32's tip is
continuous on `(S, F)` and spends zero Lebesgue time off `ℍ` there. -/
theorem ae_regularity_tip_J32 (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      (RootJ32.experiment c r).data.S l a ω < (RootJ32.experiment c r).data.F l a ω →
      ContinuousOn ((RootJ32.experiment c r).data.γ l a ω)
        (Ioo ((RootJ32.experiment c r).data.S l a ω) ((RootJ32.experiment c r).data.F l a ω)) ∧
      volume {t | t ∈ Ioo ((RootJ32.experiment c r).data.S l a ω)
        ((RootJ32.experiment c r).data.F l a ω) ∧ (RootJ32.experiment c r).data.γ l a ω t ∉ H} = 0 := by
  filter_upwards [ae_live_clock h13 c r, RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ]
    with ω hclock hcover hα hreg hζ halive hSF
  have hlive := RootJ32.live_of_entry_lt_failure c r l a ω hSF
  obtain ⟨hcov, -, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ω hlive
  obtain ⟨hseed, hsH, -, -, -, harc⟩ := hcover hcov
  obtain ⟨_, _, hWc, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  obtain ⟨γ, hγ, hA0, hmono, hcont, -, hnc⟩ := hclock l a hlive
  obtain ⟨hJ, hJ0⟩ := continuous_futureJoined c r l a ω
  obtain ⟨-, -, hord⟩ := RootJ32.alive_spec c r l ω halive
  have hpe := futurePair_eq_recOfDriver c r l a ω
  rw [hpe] at hA0 hmono hcont
  have hFL : RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω ≤
      RootJ31.historyTime c r l + RootJ31.candidateCap c r a :=
    add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω)
  have hk0 : (0 : ℝ≥0) < 2 ^ r.2 := pow_pos (by norm_num) _
  have key := regularity_tip_of_clock c.W c.ζ ω hα hWc hW0 hζ hs
    (RootH29.rootPt_nonneg_of_seedOK c hseed) harc hJ hJ0 hγ hFL hnc hA0 hmono hcont hk0
    (rootTime_le_historyTime c r l hord) l.length
    (RootJ32.sourceEntry_ge_historyTime c r l a ω)
  have hγeq : (RootJ32.experiment c r).data.γ l a ω = fun q : ℝ =>
      RootJ31.orientTip l.length (RootJ32.jointTipRead (2 ^ r.2) (rootPt r.1) c.s
        (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (rootEntry r.1).2
        (RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (rootEntry r.1).2
          ((RootJ31.historyTime c r l + (q.toNNReal - RootJ31.historyTime c r l)) -
            (rootEntry r.1).2)
          (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver
            (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (futureJoined c r l a ω)))
        (cfRec c.s c.W c.ζ ω, StagedEntrance.Strip.recOfDriver
          (RootJ31.historyTime c r l + RootJ31.candidateCap c r a) (futureJoined c r l a ω))) := by
    funext q
    change RootJ32.sourceTip c r l a ω q = _
    unfold RootJ32.sourceTip
    rw [hpe]
  rw [hγeq]
  exact key

/-- **`regularity` for J32**: the `regularity` field of `Gm.ExperimentGeometryV` (ruling R111). -/
theorem _root_.InteractingSLE.Theorem14.GW2TipSystem.RootJ32.regularity
    (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ∀ᵐ ω ∂c.P,
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      (RootJ32.experiment c r).data.S l a ω < (RootJ32.experiment c r).data.F l a ω →
      0 ≤ (RootJ32.experiment c r).data.S l a ω ∧
      ContinuousAt ((RootJ32.experiment c r).data.X l a ω) ((RootJ32.experiment c r).data.S l a ω) ∧
      (RootJ32.experiment c r).data.X l a ω ((RootJ32.experiment c r).data.S l a ω) ∈
        (RootJ32.experiment c r).data.I l a ∧
      ContinuousOn ((RootJ32.experiment c r).data.γ l a ω)
        (Ioo ((RootJ32.experiment c r).data.S l a ω) ((RootJ32.experiment c r).data.F l a ω)) ∧
      volume {t | t ∈ Ioo ((RootJ32.experiment c r).data.S l a ω)
        ((RootJ32.experiment c r).data.F l a ω) ∧ (RootJ32.experiment c r).data.γ l a ω t ∉ H} = 0 := by
  intro l a
  filter_upwards [ae_regularity_X_J32 h13 c r l a, ae_regularity_tip_J32 h13 c r l a]
    with ω hX hT halive hSF
  obtain ⟨h1, h2, h3⟩ := hX halive hSF
  obtain ⟨h4, h5⟩ := hT halive hSF
  exact ⟨h1, h2, h3, h4, h5⟩

end InteractingSLE.Theorem14.GW2TipSystem.Gm
