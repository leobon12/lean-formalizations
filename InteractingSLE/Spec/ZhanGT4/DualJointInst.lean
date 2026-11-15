/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualJointHit
import InteractingSLE.Spec.ZhanGT4.MTildeMartFrozen
import QuantumZipper.Proofs.Thm11.ExtMeasTamed

/-!
# The factors of `M̃` are measurable functions of both curves

Packet PROVE-ZHAN-GT4-A13. Source: Astra, *Follow-up proofs*, §A.1.2–A.1.4 (`ig1_followup_proofs.txt` L268–L380,
R38). On a product `Ω₁ × Ω₂` carrying curve `1` (driver `√κ B`, growing, time `s`) and curve `2` (any continuous
driver family `V`, frozen at time `t`), the random hull `A = K₂(t)`, its chart `φ = g^{(2)}_t` and the marks satisfy
the inputs of `FrzMeasR` (`DualJoint.lean`):

* `measurableSet_alive_drive`, `measurable_fwd_drive`, `measurableSet_hit_drive`: the alive pairs, the forward map
  (jointly in the point and `ω`) and the compact hits of the hull of `√κ B` at time `s` are measurable for every
  σ-algebra in which `B r`, `r ≤ s`, is measurable (so also for the filtration at time `s`);
* `frzMeasR_pair`: the measurability inputs of `FrzMeasR` on `Ω₁ × Ω₂`, the dyadic hits of `closure (g^{(1)}_s(K₂(t)))`
  from `isDyadicHitMeasurable_closure_imgHull`;
* `markSeq_real` (a real mark `p` alive for curve `2`: points `p + i/(n+1)`) and `markSeq_tip` (the tip `V t` of
  curve `2` in its own chart: a measurable choice of points of the dense sequence mapped near `V t + i/(n+1)`);
* `measurable_ell_pair`: **`log M̃(s, t)` is a measurable function on `Ω₁ × Ω₂`** (on the event where the
  configuration is protected), for any choice of the image data.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull tamedZ drive)

/-! ### One curve driven by `√κ B` -/

section Drive

variable {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous fun r => B r ω)
  {s : ℝ} (hs : 0 ≤ s) (hBm : ∀ r : ℝ≥0, (r : ℝ) ≤ s → Measurable (B r))
include hBc hs hBm

/-- The compact hits of the hull of `√κ B` at time `s` are measurable. -/
theorem measurableSet_hit_drive {L : Set ℂ} (hL : IsCompact L) (hLH : L ⊆ H) :
    MeasurableSet {ω | (L ∩ fwdHull (drive κ B ω) s).Nonempty} :=
  measurableSet_hit (fun ω => QuantumZipper.drive_continuous (hBc ω)) hs
    (fun _ q hq0 hqs a => (QuantumZipper.measurable_tamed_drive κ (by positivity) B hBc hq0
      fun r hr => hBm r (hr.trans hqs)).1.comp measurable_prodMk_left) hL hLH

/-- The pairs `(z, ω)` with `z` in the hull of `√κ B` at time `s` form a measurable set. -/
theorem measurableSet_fwdHull_prod_drive :
    MeasurableSet {p : ℂ × Ω | p.1 ∈ fwdHull (drive κ B p.2) s} := by
  have e : {p : ℂ × Ω | p.1 ∈ fwdHull (drive κ B p.2) s} = {p : ℂ × Ω | 0 < p.1.im} ∩
      ⋂ k : ℕ, ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ s),
        {p : ℂ × Ω | (tamedZ (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 q).im < 2 * (1 / ((k : ℝ) + 1))} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, exists_prop,
      QuantumZipper.NonSwallow.mem_fwdHull_iff_tamed (QuantumZipper.drive_continuous (hBc p.2)) hs, and_assoc]
  rw [e]
  refine (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
      measurableSet_lt (Complex.measurable_im.comp (QuantumZipper.measurable_tamed_drive κ (by positivity) B hBc
        hq.1 fun r hr => hBm r (hr.trans hq.2)).1) measurable_const)

omit [MeasurableSpace Ω] hBm in
theorem alive_iff_notMem {ω : Ω} {z : ℂ} (hz : z ∈ H) :
    (∃ u, IsForwardSol (drive κ B ω) z s u) ↔ z ∉ fwdHull (drive κ B ω) s :=
  ⟨fun ⟨_, hu⟩ => Ito.notMem_fwdHull_of_isForwardSol (QuantumZipper.drive_continuous (hBc ω)) hz hs hu,
    fun h => QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs hz h⟩

/-- The alive pairs of `√κ B` at time `s` (points of `ℍ`) form a measurable set. -/
theorem measurableSet_alive_drive :
    MeasurableSet {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2) p.1 s u} := by
  have e : {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2) p.1 s u} =
      {p : ℂ × Ω | 0 < p.1.im} \ {p | p.1 ∈ fwdHull (drive κ B p.2) s} := by
    ext p
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    exact ⟨fun h => ⟨h.1, (alive_iff_notMem hBc hs h.1).1 h.2⟩,
      fun h => ⟨h.1, (alive_iff_notMem hBc hs h.1).2 h.2⟩⟩
  rw [e]
  exact (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_fst)).diff
    (measurableSet_fwdHull_prod_drive hBc hs hBm)

/-- The forward map of `√κ B` at time `s` is jointly measurable on the alive pairs. -/
theorem measurable_fwd_drive :
    Measurable ({p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2) p.1 s u}.indicator
      fun p => fwdMap (drive κ B p.2) s p.1) := by
  have hD := measurableSet_alive_drive (κ := κ) hBc hs hBm
  refine measurable_of_tendsto_metrizable (f := fun k : ℕ =>
    {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2) p.1 s u}.indicator
      fun p => tamedZ (drive κ B p.2) (1 / ((k : ℝ) + 1)) p.1 s) (fun k => ?_) ?_
  · exact (QuantumZipper.measurable_tamed_drive κ (by positivity) B hBc hs hBm).1.indicator hD
  · rw [tendsto_pi_nhds]
    intro p
    by_cases hp : p ∈ {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2) p.1 s u}
    · simp only [indicator_of_mem hp]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [QuantumZipper.Thm11Asm.MeasTamed.eventually_tamed_eq_at
        (QuantumZipper.drive_continuous (hBc p.2)) hp.1 hs ((alive_iff_notMem hBc hs hp.1).1 hp.2)] with k hk
      exact hk.1.symm
    · simp only [indicator_of_notMem hp]
      exact tendsto_const_nhds

omit hBc in
/-- The driver value `√κ B_s` is measurable. -/
theorem measurable_drive_at : Measurable fun ω => drive κ B ω s := by
  have h := hBm s.toNNReal (by rw [Real.coe_toNNReal _ hs])
  exact measurable_const.mul h

end Drive

/-! ### Two curves on a product space -/

section Pair

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {κ : ℝ} {B : ℝ≥0 → Ω₁ → ℝ}
  (hBc : ∀ ω, Continuous fun r => B r ω) {s : ℝ} (hs : 0 ≤ s) (hBm : ∀ r : ℝ≥0, (r : ℝ) ≤ s → Measurable (B r))
  {V : Ω₂ → ℝ → ℝ} {t : ℝ}
  (hVhit : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ fwdHull (V ω) t).Nonempty})
  (hVfwd : ∀ z ∈ H, Measurable fun ω => fwdMap (V ω) t z) (hVt : Measurable fun ω => V ω t)

/-- The chart `φ = g^{(2)}_t` of the frozen curve (uncentred). -/
def chart2 (V : Ω₂ → ℝ → ℝ) (t : ℝ) (ω : Ω₁ × Ω₂) (z : ℂ) : ℂ := fwdMap (V ω.2) t z + (V ω.2 t : ℂ)

/-- The frozen hull `A = K₂(t)`. -/
def hull2 (V : Ω₂ → ℝ → ℝ) (t : ℝ) (ω : Ω₁ × Ω₂) : Set ℂ := fwdHull (V ω.2) t

open scoped Classical in
include hBc hs hBm hVhit in
/-- **The measurability inputs of `FrzMeasR` for two curves on `Ω₁ × Ω₂`**: curve `1` driven by `√κ B` growing at
time `s`, curve `2` (driver family `V`) frozen at time `t`, on a measurable event `G` where `OwnData` holds. -/
theorem frzMeasR_pair {W' a : Ω₁ × Ω₂ → ℝ → ℝ} {T : Ω₁ × Ω₂ → ℝ} {G : Set (Ω₁ × Ω₂)} (hG : MeasurableSet G)
    (hown : ∀ ω ∈ G, OwnData (drive κ B ω.1) (hull2 V t ω) (chart2 V t ω) (T ω) (a ω) (W' ω))
    (hmem : ∀ ω ∈ G, s ∈ Icc 0 (T ω)) :
    FrzMeasR (fun ω => drive κ B ω.1) W' a (hull2 V t) (chart2 V t) T G s := by
  have hpr : Measurable fun p : ℂ × (Ω₁ × Ω₂) => (p.1, p.2.1) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hal := measurableSet_alive_drive (κ := κ) hBc hs hBm
  have hfw := measurable_fwd_drive (κ := κ) hBc hs hBm
  have hGp : MeasurableSet {p : ℂ × (Ω₁ × Ω₂) | p.2 ∈ G} := measurable_snd hG
  have haliveEq : aliveR (fun ω => drive κ B ω.1) G s = {p : ℂ × (Ω₁ × Ω₂) | p.2 ∈ G} ∩
      (fun p : ℂ × (Ω₁ × Ω₂) => (p.1, p.2.1)) ⁻¹' {p : ℂ × Ω₁ | p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2) p.1 s u} := by
    ext p; simp only [aliveR, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  have hfix : ∀ z ∈ H, Measurable ({ω : Ω₁ × Ω₂ | ∃ u, IsForwardSol (drive κ B ω.1) z s u}.indicator
      fun ω => fwdMap (drive κ B ω.1) s z) := fun z hz => by
    have hm : Measurable fun ω : Ω₁ × Ω₂ => (z, ω.1) := measurable_const.prodMk measurable_fst
    have e : ({ω : Ω₁ × Ω₂ | ∃ u, IsForwardSol (drive κ B ω.1) z s u}.indicator
        fun ω => fwdMap (drive κ B ω.1) s z) = ({p : ℂ × Ω₁ | p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2) p.1 s u}.indicator
          fun p => fwdMap (drive κ B p.2) s p.1) ∘ fun ω : Ω₁ × Ω₂ => (z, ω.1) := by
      funext ω
      by_cases h1 : ∃ u, IsForwardSol (drive κ B ω.1) z s u <;> simp [h1, hz]
    rw [e]
    exact hfw.comp hm
  have hhit : Restart.IsDyadicHitMeasurable (fun ω : Ω₁ × Ω₂ =>
      if ω ∈ G then closure (imgHull (drive κ B ω.1) (hull2 V t ω) s) else ∅) :=
    isDyadicHitMeasurable_closure_imgHull (W := fun ω : Ω₁ × Ω₂ => drive κ B ω.1) (A := hull2 V t)
      (fun ω => QuantumZipper.drive_continuous (hBc ω.1)) hs
      (fun L hL hLH => measurable_fst (measurableSet_hit_drive hBc hs hBm hL hLH)) hfix
      ((measurable_drive_at hs hBm).comp measurable_fst)
      (fun L hL hLH => measurable_snd (hVhit L hL hLH)) hG (fun _ _ _ hz => hz.1)
      fun ω hω => (hown ω hω).disjoint_A_K (hmem ω hω)
  have hfwd : Measurable ((aliveR (fun ω : Ω₁ × Ω₂ => drive κ B ω.1) G s).indicator
      fun p => fwdMap (drive κ B p.2.1) s p.1) := by
    have e : ((aliveR (fun ω : Ω₁ × Ω₂ => drive κ B ω.1) G s).indicator fun p => fwdMap (drive κ B p.2.1) s p.1) =
        {p : ℂ × (Ω₁ × Ω₂) | p.2 ∈ G}.indicator (({p : ℂ × Ω₁ | p.1 ∈ H ∧
          ∃ u, IsForwardSol (drive κ B p.2) p.1 s u}.indicator fun p => fwdMap (drive κ B p.2) s p.1) ∘
            fun p : ℂ × (Ω₁ × Ω₂) => (p.1, p.2.1)) := by
      funext p
      by_cases h1 : p.2 ∈ G <;> by_cases h2 : p.1 ∈ H ∧ ∃ u, IsForwardSol (drive κ B p.2.1) p.1 s u <;>
        simp [aliveR, h1, h2]
    rw [e]
    exact (hfw.comp hpr).indicator hGp
  exact ⟨hG, hown, hmem, (measurable_drive_at hs hBm).comp measurable_fst, by rw [haliveEq]; exact hGp.inter (hpr hal),
    hfwd, hhit⟩

omit [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] in
theorem mem_hull2_iff_hit {ω : Ω₁ × Ω₂} {z : ℂ} : z ∈ hull2 V t ω ↔ ({z} ∩ fwdHull (V ω.2) t).Nonempty :=
  ⟨fun h => ⟨z, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩

include hVhit in
/-- Membership of a fixed point of `ℍ` in the frozen hull is measurable. -/
theorem measurableSet_mem_hull2 {z : ℂ} (hz : z ∈ H) : MeasurableSet {ω : Ω₁ × Ω₂ | z ∈ hull2 V t ω} := by
  have e : {ω : Ω₁ × Ω₂ | z ∈ hull2 V t ω} = Prod.snd ⁻¹' {ω | ({z} ∩ fwdHull (V ω) t).Nonempty} := by
    ext ω; exact mem_hull2_iff_hit
  rw [e]
  exact measurable_snd (hVhit {z} isCompact_singleton (singleton_subset_iff.2 hz))

include hVfwd hVt in
/-- The chart of the frozen curve at a fixed point of `ℍ` is measurable. -/
theorem measurable_chart2 {z : ℂ} (hz : z ∈ H) : Measurable fun ω : Ω₁ × Ω₂ => chart2 V t ω z :=
  ((hVfwd z hz).comp measurable_snd).add (Complex.measurable_ofReal.comp (hVt.comp measurable_snd))

/-- The real mark `g^{(2)}_t(p)` of a real point `p`. -/
def markVal2 (V : Ω₂ → ℝ → ℝ) (t p : ℝ) (ω : Ω₁ × Ω₂) : ℝ := (fwdMap (V ω.2) t p).re + V ω.2 t

include hVhit hVfwd hVt in
/-- **A real force mark `p` alive for the frozen curve** is a mark sequence: the points `p + i/(n+1)` of the original
chart, with `g^{(2)}_t(p + i/(n+1)) → g^{(2)}_t(p)`. -/
theorem markSeq_real (hVc : ∀ ω, Continuous (V ω)) (ht : 0 ≤ t) {G : Set (Ω₁ × Ω₂)} (hG : MeasurableSet G)
    {p : ℝ} (halive : ∀ ω ∈ G, ∃ v, IsForwardSol (V ω.2) (p : ℂ) t v) :
    MarkSeq (hull2 V t) (chart2 V t) G (markVal2 V t p) fun n _ => (p : ℂ) + stepC n * I := by
  refine ⟨fun _ _ n => FrzMeas.markArg_mem_H p n, fun n => measurableSet_mem_hull2 hVhit (FrzMeas.markArg_mem_H p n),
    fun ω hω => ?_, fun _ => measurable_const,
    fun n => (measurable_chart2 hVfwd hVt (FrzMeas.markArg_mem_H p n)).indicator hG, fun ω hω => ?_⟩
  · obtain ⟨v, hv⟩ := halive ω hω
    obtain ⟨δ, hδ, hlow, -⟩ := exists_aliveDisc_self hv ht
    have hconv : Tendsto (fun n => (p : ℂ) + stepC n * I) atTop (𝓝 (p : ℂ)) := by
      simpa using tendsto_const_nhds.add (tendsto_stepC.mul_const I)
    filter_upwards [hconv.eventually (ball_mem_nhds (p : ℂ) (aliveRad_pos hδ))] with n hn
    obtain ⟨v', hv', -⟩ := exists_sol_aliveDisc (hVc ω.2) hv hδ hlow hn
    exact Ito.notMem_fwdHull_of_isForwardSol (hVc ω.2) (FrzMeas.markArg_mem_H p n) ht hv'
  · obtain ⟨v, hv⟩ := halive ω hω
    obtain ⟨δ, hδ, hlow, hmem⟩ := exists_aliveDisc_self hv ht
    have hder := hasDerivAt_fwdMap_aliveDisc (hVc ω.2) hv hδ hlow hmem ⟨ht, le_rfl⟩
    have hconv : Tendsto (fun n => (p : ℂ) + stepC n * I) atTop (𝓝 (p : ℂ)) := by
      simpa using tendsto_const_nhds.add (tendsto_stepC.mul_const I)
    have him := fwdMap_real_im (hVc ω.2) hv ⟨ht, le_rfl⟩
    have hval : ((markVal2 V t p ω : ℝ) : ℂ) = fwdMap (V ω.2) t p + (V ω.2 t : ℂ) := by
      apply Complex.ext <;> simp [markVal2, him]
    rw [hval]
    exact (hder.continuousAt.tendsto.comp hconv).add tendsto_const_nhds

/-- The selection predicate for the tip at step `n`: the dense point `e j` lies in `ℍ \ K₂(t)` and is mapped within
`1/(n+1)` of `V t + i/(n+1)`. -/
def tipSel (V : Ω₂ → ℝ → ℝ) (t : ℝ) (n : ℕ) (ω : Ω₁ × Ω₂) (j : ℕ) : Prop :=
  TopologicalSpace.denseSeq ℂ j ∈ H ∧ TopologicalSpace.denseSeq ℂ j ∉ hull2 V t ω ∧
    dist (chart2 V t ω (TopologicalSpace.denseSeq ℂ j)) ((V ω.2 t : ℂ) + stepC n * I) < 1 / ((n : ℝ) + 1)

omit [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] in
theorem exists_tipSel (hVc : ∀ ω, Continuous (V ω)) (ht : 0 ≤ t) (n : ℕ) (ω : Ω₁ × Ω₂) :
    ∃ j, tipSel V t n ω j := by
  have hφ := isMapOut_fwdMap_gen (hVc ω.2) ht
  have hy : (V ω.2 t : ℂ) + stepC n * I ∈ H := FrzMeas.markArg_mem_H _ n
  obtain ⟨z, hz, hzy⟩ := hφ.1.2.surjOn hy
  have hDo : IsOpen (H \ fwdHull (V ω.2) t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hVc ω.2) ht
  have hc : ContinuousOn (chart2 V t ω) (H \ fwdHull (V ω.2) t) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap (hVc ω.2) ht).continuousOn.add continuousOn_const
  have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hUo := hc.isOpen_inter_preimage hDo (isOpen_ball (x := (V ω.2 t : ℂ) + stepC n * I) (ε := 1 / ((n : ℝ) + 1)))
  have hzU : z ∈ (H \ fwdHull (V ω.2) t) ∩ chart2 V t ω ⁻¹' ball ((V ω.2 t : ℂ) + stepC n * I) (1 / ((n : ℝ) + 1)) :=
    ⟨hz, by rw [mem_preimage, show chart2 V t ω z = (V ω.2 t : ℂ) + stepC n * I from hzy]; exact mem_ball_self hr⟩
  obtain ⟨j, hj⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_mem_open hUo ⟨z, hzU⟩
  exact ⟨j, hj.1.1, hj.1.2, hj.2⟩

open scoped Classical in
/-- The `n`-th approximating point of the tip `V t` of the frozen curve in its own chart: the first dense point
selected by `tipSel`. -/
def tipQ (hVc : ∀ ω, Continuous (V ω)) (ht : 0 ≤ t) (n : ℕ) (ω : Ω₁ × Ω₂) : ℂ :=
  TopologicalSpace.denseSeq ℂ (Nat.find (exists_tipSel hVc ht n ω))

omit [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] in
theorem tipQ_spec (hVc : ∀ ω, Continuous (V ω)) (ht : 0 ≤ t) (n : ℕ) (ω : Ω₁ × Ω₂) :
    tipQ hVc ht n ω ∈ H ∧ tipQ hVc ht n ω ∉ hull2 V t ω ∧
      dist (chart2 V t ω (tipQ hVc ht n ω)) ((V ω.2 t : ℂ) + stepC n * I) < 1 / ((n : ℝ) + 1) := by
  classical
  exact Nat.find_spec (exists_tipSel hVc ht n ω)

include hVhit hVfwd hVt in
/-- **The tip of the frozen curve** in its own chart is a mark sequence (`ζ₀ = V t`, the other source of `M̃`). -/
theorem markSeq_tip (hVc : ∀ ω, Continuous (V ω)) (ht : 0 ≤ t) {G : Set (Ω₁ × Ω₂)} (hG : MeasurableSet G) :
    MarkSeq (hull2 V t) (chart2 V t) G (fun ω => V ω.2 t) (tipQ hVc ht) := by
  classical
  have hsel : ∀ n j, MeasurableSet {ω : Ω₁ × Ω₂ | tipSel V t n ω j} := by
    intro n j
    by_cases hj : TopologicalSpace.denseSeq ℂ j ∈ H
    · have e : {ω : Ω₁ × Ω₂ | tipSel V t n ω j} = {ω | TopologicalSpace.denseSeq ℂ j ∈ hull2 V t ω}ᶜ ∩
          {ω | dist (chart2 V t ω (TopologicalSpace.denseSeq ℂ j)) ((V ω.2 t : ℂ) + stepC n * I) <
            1 / ((n : ℝ) + 1)} := by
        ext ω; simp only [tipSel, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, hj, true_and]
      rw [e]
      exact (measurableSet_mem_hull2 hVhit hj).compl.inter (measurableSet_lt ((measurable_chart2 hVfwd hVt hj).dist
        ((Complex.measurable_ofReal.comp (hVt.comp measurable_snd)).add measurable_const)) measurable_const)
    · have e : {ω : Ω₁ × Ω₂ | tipSel V t n ω j} = ∅ := by
        ext ω; simp only [tipSel, mem_ofPred_eq, hj, false_and, mem_empty_iff_false]
      rw [e]; exact MeasurableSet.empty
  have hN : ∀ n, Measurable fun ω => Nat.find (exists_tipSel hVc ht n ω) := fun n =>
    measurable_find (exists_tipSel hVc ht n) (hsel n)
  have hconv : ∀ ω : Ω₁ × Ω₂, Tendsto (fun n => (V ω.2 t : ℂ) + stepC n * I) atTop (𝓝 (V ω.2 t : ℂ)) := fun ω => by
    simpa using tendsto_const_nhds.add (tendsto_stepC.mul_const I)
  refine ⟨fun ω _ n => (tipQ_spec hVc ht n ω).1, fun n => ?_, fun ω _ => Eventually.of_forall fun n =>
    (tipQ_spec hVc ht n ω).2.1, fun n => measurable_from_nat.comp (hN n), fun n => ?_, fun ω _ => ?_⟩
  · have e : {ω : Ω₁ × Ω₂ | tipQ hVc ht n ω ∈ hull2 V t ω} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; exact (tipQ_spec hVc ht n ω).2.1
    rw [e]; exact MeasurableSet.empty
  · set F : (Ω₁ × Ω₂) × ℕ → ℂ := fun p =>
      if TopologicalSpace.denseSeq ℂ p.2 ∈ H then chart2 V t p.1 (TopologicalSpace.denseSeq ℂ p.2) else 0 with hF
    have hFm : Measurable F := measurable_from_prod_countable_left fun j => by
      by_cases hj : TopologicalSpace.denseSeq ℂ j ∈ H
      · simp only [hF, hj, ↓reduceIte]; exact measurable_chart2 hVfwd hVt hj
      · simp only [hF, hj, ↓reduceIte]; exact measurable_const
    have e : (fun ω => chart2 V t ω (tipQ hVc ht n ω)) = F ∘ fun ω => (ω, Nat.find (exists_tipSel hVc ht n ω)) := by
      funext ω
      have h1 : TopologicalSpace.denseSeq ℂ (Nat.find (exists_tipSel hVc ht n ω)) ∈ H := (tipQ_spec hVc ht n ω).1
      simp only [Function.comp_apply, hF, h1, ↓reduceIte]
      rfl
    rw [e]
    exact (hFm.comp (measurable_id.prodMk (hN n))).indicator hG
  · refine tendsto_of_tendsto_of_dist (hconv ω) (squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [dist_comm]
    exact (tipQ_spec hVc ht n ω).2.2.le

include hBc hs hBm hVhit hVfwd hVt in
/-- **`log M̃(s, t)` is a measurable function of both curves.** On `Ω₁ × Ω₂`, curve `1` driven by `√κ B` grows to
time `s`, curve `2` (continuous driver family `V`) is frozen at time `t`; on a measurable event `G` the configuration
has image data `(W', a)` (`OwnData` up to `T ω ≥ s`), the force marks `p m` are alive for curve `2`, and the other
source `V t` and the marks `g^{(2)}_t(p m)` are alive for the image chain up to `a(T)`. Then
`ω ↦ ℓ(s, W_s)` of the frozen data (A7's `FrzData.ell`; `M̃ = exp ℓ`) is measurable on `G`. -/
theorem measurable_ell_pair (hVc : ∀ ω, Continuous (V ω)) (ht : 0 ≤ t) {n : ℕ} (rr : Fin n → ℝ) (p : Fin n → ℝ)
    {W' a : Ω₁ × Ω₂ → ℝ → ℝ} {T : Ω₁ × Ω₂ → ℝ} {G : Set (Ω₁ × Ω₂)} (hG : MeasurableSet G)
    (hown : ∀ ω ∈ G, OwnData (drive κ B ω.1) (hull2 V t ω) (chart2 V t ω) (T ω) (a ω) (W' ω))
    (hmem : ∀ ω ∈ G, s ∈ Icc 0 (T ω)) (halive : ∀ ω ∈ G, ∀ m, ∃ v, IsForwardSol (V ω.2) (p m : ℂ) t v)
    (hv₀ : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (V ω.2 t : ℂ) (a ω (T ω)) v)
    (hv : ∀ m, ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (markVal2 V t (p m) ω : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => (frzDataR κ rr (fun ω => drive κ B ω.1) W' a (chart2 V t) (fun ω => V ω.2 t)
      (fun m => markVal2 V t (p m)) ω).ell s (drive κ B ω.1 s)) :=
  measurable_ell_R κ rr hs (fun _ hu => frzMeasR_pair hBc hu.1 (fun r hr => hBm r (hr.trans hu.2)) hVhit hG hown
      fun ω hω => ⟨hu.1, hu.2.trans (hmem ω hω).2⟩)
    (markSeq_tip hVhit hVfwd hVt hVc ht hG) (fun m => markSeq_real hVhit hVfwd hVt hVc ht hG fun ω hω => halive ω hω m)
    hv₀ hv

end Pair

end InteractingSLE.ZhanGT4
