/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualJointInst
import InteractingSLE.Spec.ZhanGT4.A2TipSepHit
import InteractingSLE.Spec.ZhanGT4.A1RefReg

/-!
# Measurability of Loewner hulls and maps for arbitrary families of continuous drivers

Packet PROVE-A1-MARG (R76), for the measurability clauses (m3)–(m4) of `A1Core.IsRectImageCore`. PROVE-ZHAN-GT4-A13
(`DualJointInst.lean`) proved the inputs of `FrzMeasR` for the Brownian driver `√κ B`. The canonical image of A.1 is
built from the drivers of two integrated evolutions, which are continuous before their lifetimes only. Here:

* `measurable_tamedZ_prod`, `measurableSet_fwdHull_prod`, `measurableSet_alive_prod`, `measurable_fwd_prod`,
  `measurableSet_hit_family`: the tamed flow, the hull, the alive pairs and the forward map of any family of
  continuous drivers with measurable evaluations (jointly in the point and the sample);
* **`frzMeasR_family`**: the inputs of `FrzMeasR` for a growing curve with such a driver family and a random frozen hull
  with measurable compact hits (A13's `frzMeasR_pair` for general drivers);
* **`measurableSet_hit_stop`**: the compact hits of the hull of a driver continuous before its lifetime, **jointly in
  the (deterministic) stop and the sample**, on the event that the stop precedes the lifetime.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Marg

open QuantumZipper (H IsForwardSol fwdMap fwdHull tamedZ extIccPath)

section Family

variable {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℝ → ℝ}

/-- **The tamed flow of a family of continuous drivers is jointly measurable** in the start point and the sample. -/
theorem measurable_tamedZ_prod (hDc : ∀ ω, Continuous (D ω)) {t : ℝ} (ht : 0 ≤ t)
    (hDm : ∀ r ∈ Icc (0 : ℝ) t, Measurable fun ω => D ω r) {c : ℝ} (hc : 0 < c) :
    Measurable fun p : ℂ × Ω => tamedZ (D p.2) c p.1 t := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) t, ℝ) := borel _
  have : BorelSpace C(Icc (0 : ℝ) t, ℝ) := ⟨rfl⟩
  let Φ : Ω → C(Icc (0 : ℝ) t, ℝ) := fun ω => ⟨fun x => D ω x, (hDc ω).comp continuous_subtype_val⟩
  have hΦ : Measurable Φ := QuantumZipper.measurable_to_continuousMap_Icc Φ fun x => hDm x x.2
  have hagree : ∀ ω, ∀ r ∈ Icc (0 : ℝ) t, D ω r = extIccPath ht (Φ ω) r := fun ω r hr => by
    rw [QuantumZipper.extIccPath_of_mem ht _ hr]; rfl
  have e : (fun p : ℂ × Ω => tamedZ (D p.2) c p.1 t) =
      (fun p : ℂ × C(Icc (0 : ℝ) t, ℝ) => tamedZ (extIccPath ht p.2) c p.1 t) ∘ (fun p => (p.1, Φ p.2)) := by
    funext p
    exact QuantumZipper.tamedZ_congr_drive (hDc p.2) (QuantumZipper.continuous_extIccPath ht _) hc ht p.1
      (hagree p.2)
  rw [e]
  exact (QuantumZipper.continuous_tamed_path hc ht).1.measurable.comp
    (measurable_fst.prodMk (hΦ.comp measurable_snd))

/-- The pairs `(z, ω)` with `z` in the hull of `D ω` at time `s` form a measurable set. -/
theorem measurableSet_fwdHull_prod (hDc : ∀ ω, Continuous (D ω)) {s : ℝ} (hs : 0 ≤ s)
    (hDm : ∀ r ∈ Icc (0 : ℝ) s, Measurable fun ω => D ω r) :
    MeasurableSet {p : ℂ × Ω | p.1 ∈ fwdHull (D p.2) s} := by
  have e : {p : ℂ × Ω | p.1 ∈ fwdHull (D p.2) s} = {p : ℂ × Ω | 0 < p.1.im} ∩
      ⋂ k : ℕ, ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ s),
        {p : ℂ × Ω | (tamedZ (D p.2) (1 / ((k : ℝ) + 1)) p.1 q).im < 2 * (1 / ((k : ℝ) + 1))} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop,
      QuantumZipper.NonSwallow.mem_fwdHull_iff_tamed (hDc p.2) hs, and_assoc]
  rw [e]
  refine (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
      measurableSet_lt (Complex.measurable_im.comp (measurable_tamedZ_prod hDc hq.1
        (fun r hr => hDm r ⟨hr.1, hr.2.trans hq.2⟩) (by positivity))) measurable_const)

omit [MeasurableSpace Ω] in
theorem alive_iff_notMem_family (hDc : ∀ ω, Continuous (D ω)) {s : ℝ} (hs : 0 ≤ s) {ω : Ω} {z : ℂ}
    (hz : z ∈ H) : (∃ u, IsForwardSol (D ω) z s u) ↔ z ∉ fwdHull (D ω) s :=
  ⟨fun ⟨_, hu⟩ => Ito.notMem_fwdHull_of_isForwardSol (hDc ω) hz hs hu,
    fun h => QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs hz h⟩

/-- The alive pairs of the family at time `s` (points of `ℍ`) form a measurable set. -/
theorem measurableSet_alive_prod (hDc : ∀ ω, Continuous (D ω)) {s : ℝ} (hs : 0 ≤ s)
    (hDm : ∀ r ∈ Icc (0 : ℝ) s, Measurable fun ω => D ω r) :
    MeasurableSet {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 s u} := by
  have e : {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 s u} =
      {p : ℂ × Ω | 0 < p.1.im} \ {p | p.1 ∈ fwdHull (D p.2) s} := by
    ext p
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    exact ⟨fun h => ⟨h.1, (alive_iff_notMem_family hDc hs h.1).1 h.2⟩,
      fun h => ⟨h.1, (alive_iff_notMem_family hDc hs h.1).2 h.2⟩⟩
  rw [e]
  exact (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).diff
    (measurableSet_fwdHull_prod hDc hs hDm)

/-- The forward map of the family at time `s` is jointly measurable on the alive pairs. -/
theorem measurable_fwd_prod (hDc : ∀ ω, Continuous (D ω)) {s : ℝ} (hs : 0 ≤ s)
    (hDm : ∀ r ∈ Icc (0 : ℝ) s, Measurable fun ω => D ω r) :
    Measurable ({p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 s u}.indicator
      fun p => fwdMap (D p.2) s p.1) := by
  have hD := measurableSet_alive_prod hDc hs hDm
  refine measurable_of_tendsto_metrizable (f := fun k : ℕ =>
    {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 s u}.indicator
      fun p => tamedZ (D p.2) (1 / ((k : ℝ) + 1)) p.1 s) (fun k => ?_) ?_
  · exact (measurable_tamedZ_prod hDc hs hDm (by positivity)).indicator hD
  · rw [tendsto_pi_nhds]
    intro p
    by_cases hp : p ∈ {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 s u}
    · simp only [indicator_of_mem hp]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [QuantumZipper.Thm11Asm.MeasTamed.eventually_tamed_eq_at (hDc p.2) hp.1 hs
        ((alive_iff_notMem_family hDc hs hp.1).1 hp.2)] with k hk
      exact hk.1.symm
    · simp only [indicator_of_notMem hp]
      exact tendsto_const_nhds

/-- The compact hits of the hull of the family at time `s` are measurable. -/
theorem measurableSet_hit_family (hDc : ∀ ω, Continuous (D ω)) {s : ℝ} (hs : 0 ≤ s)
    (hDm : ∀ r ∈ Icc (0 : ℝ) s, Measurable fun ω => D ω r) {L : Set ℂ} (hL : IsCompact L) (hLH : L ⊆ H) :
    MeasurableSet {ω | (L ∩ fwdHull (D ω) s).Nonempty} :=
  measurableSet_hit hDc hs (fun _ q hq0 hqs a => (measurable_tamedZ_prod hDc hq0
    (fun r hr => hDm r ⟨hr.1, hr.2.trans hqs⟩) (by positivity)).comp measurable_prodMk_left) hL hLH

open scoped Classical in
/-- **The inputs of `FrzMeasR` for a family of continuous drivers** (A13's `frzMeasR_pair` for any drivers): the
growing curve has the driver family `D` (continuous at every sample, measurable evaluations on `[0, s]`), the frozen
hull `A` has measurable compact hits and lies in `ℍ` on the measurable event `G`, where `OwnData` holds. -/
theorem frzMeasR_family (hDc : ∀ ω, Continuous (D ω)) {s : ℝ} (hs : 0 ≤ s)
    (hDm : ∀ r ∈ Icc (0 : ℝ) s, Measurable fun ω => D ω r) {W' a : Ω → ℝ → ℝ} {A : Ω → Set ℂ}
    {φ : Ω → ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} (hG : MeasurableSet G)
    (hA : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ A ω).Nonempty})
    (hAH : ∀ ω ∈ G, A ω ⊆ H) (hown : ∀ ω ∈ G, OwnData (D ω) (A ω) (φ ω) (T ω) (a ω) (W' ω))
    (hmem : ∀ ω ∈ G, s ∈ Icc 0 (T ω)) : FrzMeasR D W' a A φ T G s := by
  have hal := measurableSet_alive_prod hDc hs hDm
  have hfw := measurable_fwd_prod hDc hs hDm
  have hdrv : Measurable fun ω => D ω s := hDm s ⟨hs, le_rfl⟩
  have hGp : MeasurableSet {p : ℂ × Ω | p.2 ∈ G} := measurable_snd hG
  have haliveEq : aliveR D G s = {p : ℂ × Ω | p.2 ∈ G} ∩
      {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 s u} := by
    ext p; simp only [aliveR, mem_ofPred_eq, mem_inter_iff]
  have hfix : ∀ z ∈ H, Measurable ({ω : Ω | ∃ u, IsForwardSol (D ω) z s u}.indicator
      fun ω => fwdMap (D ω) s z) := fun z hz => by
    have hm : Measurable fun ω : Ω => (z, ω) := measurable_const.prodMk measurable_id
    have e : ({ω : Ω | ∃ u, IsForwardSol (D ω) z s u}.indicator fun ω => fwdMap (D ω) s z) =
        ({p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 s u}.indicator
          fun p => fwdMap (D p.2) s p.1) ∘ fun ω : Ω => (z, ω) := by
      funext ω
      by_cases h1 : ∃ u, IsForwardSol (D ω) z s u <;> simp [h1, hz]
    rw [e]
    exact hfw.comp hm
  have hhit : Restart.IsDyadicHitMeasurable (fun ω : Ω =>
      if ω ∈ G then closure (imgHull (D ω) (A ω) s) else ∅) :=
    isDyadicHitMeasurable_closure_imgHull hDc hs
      (fun L hL hLH => measurableSet_hit_family hDc hs hDm hL hLH) hfix hdrv hA hG hAH
      fun ω hω => (hown ω hω).disjoint_A_K (hmem ω hω)
  have hfwd : Measurable ((aliveR D G s).indicator fun p => fwdMap (D p.2) s p.1) := by
    have e : ((aliveR D G s).indicator fun p => fwdMap (D p.2) s p.1) =
        {p : ℂ × Ω | p.2 ∈ G}.indicator ({p : ℂ × Ω | p.1 ∈ H ∧
          ∃ u, IsForwardSol (D p.2) p.1 s u}.indicator fun p => fwdMap (D p.2) s p.1) := by
      funext p
      by_cases h1 : p.2 ∈ G <;> by_cases h2 : p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 s u <;>
        simp [aliveR, h1, h2]
    rw [e]
    exact hfw.indicator hGp
  exact ⟨hG, hown, hmem, hdrv, by rw [haliveEq]; exact hGp.inter hal, hfwd, hhit⟩

end Family

/-! ### Hits of the hull of a driver continuous before its lifetime, jointly in the stop -/

section Stop

variable {Y : Type*} [MeasurableSpace Y] {V : ℝ≥0 → Y → ℝ} {ζ : Y → ℝ≥0∞}

open scoped Classical in
/-- The driver read on `ℝ` and stopped at `r` when `0 ≤ r` precedes the lifetime (continuous there), else `0`. -/
def stopFam (V : ℝ≥0 → Y → ℝ) (ζ : Y → ℝ≥0∞) (r : ℝ) (y : Y) : ℝ → ℝ :=
  if 0 ≤ r ∧ ENNReal.ofReal r < ζ y then A1Ref.stopDrv (Strip.extPath (V · y)) r else fun _ => 0

omit [MeasurableSpace Y] in
theorem continuous_stopFam (hVc : ∀ y, ContinuousOn (V · y) {t | (t : ℝ≥0∞) < ζ y}) (r : ℝ) (y : Y) :
    Continuous (stopFam V ζ r y) := by
  unfold stopFam
  split_ifs with h
  · exact A1Ref.continuous_stopDrv (A1Ref.continuousOn_extPath_Icc (hVc y) h.2) h.1
  · exact continuous_const

theorem measurable_stopFam (hVm : ∀ t, Measurable (V t)) (hζ : Measurable ζ) (r u : ℝ) :
    Measurable fun y => stopFam V ζ r y u := by
  have e : (fun y => stopFam V ζ r y u) = fun y =>
      if 0 ≤ r ∧ ENNReal.ofReal r < ζ y then V (max 0 (min u r)).toNNReal y else 0 := by
    funext y
    unfold stopFam
    split_ifs <;> rfl
  rw [e]
  by_cases hr : 0 ≤ r
  · have hs : MeasurableSet {y | 0 ≤ r ∧ ENNReal.ofReal r < ζ y} := by
      simp only [hr, true_and]
      exact measurableSet_lt measurable_const hζ
    exact Measurable.ite hs (hVm _) measurable_const
  · simp only [hr, false_and, ↓reduceIte]
    exact measurable_const

omit [MeasurableSpace Y] in
theorem stopFam_eqOn {r : ℝ} {y : Y} (h : 0 ≤ r ∧ ENNReal.ofReal r < ζ y) :
    EqOn (stopFam V ζ r y) (Strip.extPath (V · y)) (Icc 0 r) := by
  intro u hu
  simp only [stopFam, h, and_self, ↓reduceIte]
  exact A1Ref.stopDrv_eqOn _ r hu

/-- **Compact hits of the hull, jointly in the stop**: for a driver continuous before its lifetime at every sample,
the pairs `(s, y)` with `s` before the lifetime and `K_s(y)` meeting a compact `L ⊆ ℍ` form a measurable set. -/
theorem measurableSet_hit_stop (hVc : ∀ y, ContinuousOn (V · y) {t | (t : ℝ≥0∞) < ζ y})
    (hVm : ∀ t, Measurable (V t)) (hζ : Measurable ζ) {L : Set ℂ} (hL : IsCompact L) (hLH : L ⊆ H) :
    MeasurableSet {q : ℝ≥0 × Y | (q.1 : ℝ≥0∞) < ζ q.2 ∧
      (L ∩ fwdHull (Strip.extPath (V · q.2)) q.1).Nonempty} := by
  rcases L.eq_empty_or_nonempty with hL0 | hLne
  · simp [hL0]
  set e := TopologicalSpace.denseSeq ℂ with he
  have hlt : MeasurableSet {q : ℝ≥0 × Y | (q.1 : ℝ≥0∞) < ζ q.2} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_fst) (hζ.comp measurable_snd)
  have heq : {q : ℝ≥0 × Y | (q.1 : ℝ≥0∞) < ζ q.2 ∧ (L ∩ fwdHull (Strip.extPath (V · q.2)) q.1).Nonempty} =
      {q : ℝ≥0 × Y | (q.1 : ℝ≥0∞) < ζ q.2} ∩ ⋂ k : ℕ, ⋃ j : ℕ, ⋃ r : ℚ,
        {q : ℝ≥0 × Y | (0 ≤ (r : ℝ) ∧ (r : ℝ) ≤ q.1) ∧ 0 < (e j).im ∧ infDist (e j) L < 1 / ((k : ℝ) + 1)} ∩
        {q : ℝ≥0 × Y | (tamedZ (stopFam V ζ r q.2) (1 / ((k : ℝ) + 1)) (e j) r).im < 2 * (1 / ((k : ℝ) + 1))} := by
    ext ⟨s, y⟩
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
    refine and_congr_right fun hs => ?_
    obtain ⟨s', hss', hcs'⟩ := A1Ref.exists_continuousOn_extPath_beyond (hVc y) hs
    set w := A1Ref.stopDrv (Strip.extPath (V · y)) s' with hw
    have hs'0 : 0 ≤ s' := s.coe_nonneg.trans hss'.le
    have hwc : Continuous w := A1Ref.continuous_stopDrv hcs' hs'0
    have hweq : EqOn w (Strip.extPath (V · y)) (Icc 0 s') := A1Ref.stopDrv_eqOn _ s'
    have hK : fwdHull (Strip.extPath (V · y)) s = fwdHull w s :=
      LocalExt.fwdHull_congr_of_eqOn_of_lt s.coe_nonneg hss' fun u hu => (hweq hu).symm
    rw [hK, hit_iff hwc s.coe_nonneg hL hLne hLH]
    refine forall_congr' fun k => exists_congr fun j => exists_congr fun r => ?_
    constructor
    · rintro ⟨hr, hj, hd, hz⟩
      refine ⟨⟨hr, hj, hd⟩, ?_⟩
      have hrζ : 0 ≤ (r : ℝ) ∧ ENNReal.ofReal r < ζ y := ⟨hr.1, lt_of_le_of_lt
        (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hr.2) hs⟩
      rwa [QuantumZipper.tamedZ_congr_drive (continuous_stopFam hVc r y) hwc (by positivity) hr.1 (e j)
        fun u hu => (stopFam_eqOn hrζ hu).trans (hweq ⟨hu.1, hu.2.trans (hr.2.trans hss'.le)⟩).symm]
    · rintro ⟨⟨hr, hj, hd⟩, hz⟩
      refine ⟨hr, hj, hd, ?_⟩
      have hrζ : 0 ≤ (r : ℝ) ∧ ENNReal.ofReal r < ζ y := ⟨hr.1, lt_of_le_of_lt
        (by rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hr.2) hs⟩
      rwa [← QuantumZipper.tamedZ_congr_drive (continuous_stopFam hVc r y) hwc (by positivity) hr.1 (e j)
        fun u hu => (stopFam_eqOn hrζ hu).trans (hweq ⟨hu.1, hu.2.trans (hr.2.trans hss'.le)⟩).symm]
  rw [heq]
  refine hlt.inter (MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun r => ?_)
  refine MeasurableSet.inter ?_ ?_
  · by_cases hj : 0 < (e j).im ∧ infDist (e j) L < 1 / ((k : ℝ) + 1)
    · simp only [hj, and_true]
      have e1 : {q : ℝ≥0 × Y | 0 ≤ (r : ℝ) ∧ (r : ℝ) ≤ q.1} =
          {_q : ℝ≥0 × Y | 0 ≤ (r : ℝ)} ∩ {q : ℝ≥0 × Y | (r : ℝ) ≤ q.1} := rfl
      rw [e1]
      exact (MeasurableSet.const _).inter
        (measurableSet_le measurable_const (measurable_coe_nnreal_real.comp measurable_fst))
    · simp only [hj, and_false]
      exact MeasurableSet.empty
  · by_cases hr : 0 ≤ (r : ℝ)
    · exact measurableSet_lt (Complex.measurable_im.comp ((A2TipSep.measurable_tamedZ_family
        (continuous_stopFam hVc r) hr
        (fun u _ => measurable_stopFam hVm hζ r u) (by positivity) (e j)).comp measurable_snd)) measurable_const
    · have e0 : ∀ y, stopFam V ζ r y = fun _ => 0 := fun y => by simp [stopFam, hr]
      simp only [e0]
      exact measurableSet_lt measurable_const measurable_const

end Stop

end InteractingSLE.ZhanGT4.A1Marg
