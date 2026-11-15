/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Shift
import InteractingSLE.Spec.Supplement.GW2GmTip
import InteractingSLE.Spec.Supplement.GW2GmJ32Agree
import InteractingSLE.Spec.Supplement.GW2RootI30Disjoint

/-!
# J32's tip: continuity and interior visits (deterministic)

Packet PROVE-GW2-GEOM2 (round 4). J32's tip at physical time `t` reads the joint driver's trace
(`LP.traceAt`, lifetime `⊤` since fix F3) at the capacity increment `U(t) = k² (A(t) − A(v₀))`. In I30's setting
(a joined driver `J` with a `⊤`-trace `γ`, before contact up to `w`):

* **`fwdHull_capacityDriver_eq`**: any driver generating the relative capacity tip has, at the capacity `A(t)`,
  the forward hull translated by the real root image `−c₀`;
* **`relBdry_mem_diff_forwardHull`**: the relative chart maps a trace point off the physical hull at `t₀` to a
  point of `ℍ` off the forward hull at `t₀` (the chart is injective on its domain);
* **`jointTip_spec`**: J32's tip is continuous at every `t ∈ [v₀, w)`, and it is in `ℍ` at `t` as soon as the
  physical trace mapped out at `v₀` (the tip `loewnerTip (shiftDrive J v₀)` at `t − v₀`) is in `ℍ`. No time
  change transports a null set: interior visits of the tip are read off interior visits of the physical
  trace mapped out at `v₀`, in physical time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

/-! ### I30's setting: the hull of the capacity driver and the chart -/

section I30

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2)

include hα hW hW0 hζ hs hx harc he hγ hv

/-- **The hull of a capacity driver**: any driver generating the relative capacity tip on
`[0, A(v)]` has, at the capacity `A(t)`, `t < v`, the forward hull at `t` translated by `−Re c₀`, where
`c₀ = relBdry U s x` is the chart image of the root. -/
theorem fwdHull_capacityDriver_eq {V : ℝ≥0 → ℝ}
    (hgen : IsGeneratingTrace V
      (ENNReal.ofReal (RootH29.forwardCapacity x s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)))
      (fun u => RootI30.capacityTipRead x s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)))
    {t : ℝ≥0} (htv : t < v) :
    fwdHull (fun r : ℝ => V r.toNNReal)
        (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) =
      (fun z : ℂ => z + ((-(relBdry (rdrv (cfRec s W ζ ω)) s x).re : ℝ) : ℂ)) ''
        RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
  set p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) with hp
  set a := fun t => RootH29.forwardCapacity x s t p with hadef
  set U := rdrv (cfRec s W ζ ω) with hUdef
  obtain ⟨V', hV', h0', hm', hc', hK⟩ :=
    RootI30.exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv
  have h0 : a 0 = 0 := h0'
  have hm : StrictMonoOn a (Icc 0 v) := hm'
  have hc : ContinuousOn a (Icc 0 v) := hc'
  have hKV : ∀ t ∈ Icc 0 v, fwdHull V' (a t) = RootH29.forwardHull x s t p :=
    fun t ht => (hK t ht).2.1
  have hrec := GaugeE.record_prefix_eq s hW0 hW.continuousOn
    (show (s : ℝ≥0∞) < ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)
  have hmap : relMap U s = relMap (Ito.rpath (W · ω)) s := relMap_eq_of_eqOn s.coe_nonneg hrec
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} = Icc 0 v := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  have ha : IsClockOn a (v : ℝ≥0∞) :=
    ⟨h0, hset ▸ hm, hset ▸ hc, fun h => (ENNReal.coe_ne_top h).elim⟩
  have hsafe : ∀ t ≤ v, (x : ℂ) + γ t ∈ relSafe U s := fun t ht =>
    RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv ht
  set c₀ := relBdry U s x with hc₀
  have hsafe0 : (x : ℂ) ∈ relSafe U s := by
    have h := hsafe 0 zero_le
    rwa [hγ.1, add_zero] at h
  have hc₀im : c₀.im = 0 :=
    im_relBdry_of_real (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsafe0.2
  have hc₀re : ((c₀.re : ℝ) : ℂ) = c₀ := Complex.ext (by simp) (by simp [hc₀im])
  have htip : ∀ t ≤ v, RootH29.rootTipRead x s t p = relBdry U s ((x : ℂ) + γ t) - c₀ :=
    fun t ht => RootH29.rootTipRead_eq W ζ ω hα hW hW0 hζ hx harc he hγ hv ht
  have hcpt : ∀ t ≤ v, IsCompact (relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t)) := by
    intro t ht
    have hpc : ContinuousOn (fun q => (x : ℂ) + γ q) (Icc 0 t) :=
      continuousOn_const.add (hγ.2.1.mono fun q hq =>
        ((ENNReal.coe_le_coe.mpr (hq.2.trans ht)).trans (lt_min_iff.mp hv).2.le))
    have hK1 := isCompact_Icc.image_of_continuousOn hpc
    refine hK1.image_of_continuousOn ((continuousOn_relBdry (continuous_rdrv _) (rdrv_zero _)
      s.coe_nonneg).mono ?_)
    rintro _ ⟨q, hq, rfl⟩
    exact hsafe q (hq.2.trans ht)
  have hfill : ∀ t ∈ Icc 0 v, IsFilling (RootH29.forwardHull x s t p)
      (relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t)) := by
    intro t ht
    have h := (hK t ht).2.2
    rw [← hmap] at h
    have hcomm : (fun q => γ q + (x : ℂ)) = (fun q => (x : ℂ) + γ q) :=
      funext fun q => add_comm _ _
    rw [hcomm] at h
    have hsubA : (fun q => (x : ℂ) + γ q) '' Icc 0 t ⊆ relSafe U s := by
      rintro _ ⟨q, hq, rfl⟩
      exact hsafe q (hq.2.trans ht.2)
    refine (isFilling_congr_inter_H ?_).1 h
    rw [← image_relBdry_inter_H (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsubA,
      inter_assoc, inter_self]
  -- the level `u = A(t)` and the tip image up to it
  have htmem : t ∈ Icc 0 v := ⟨zero_le, htv.le⟩
  have hat0 : 0 ≤ a t := by rw [← h0]; exact hm.monotoneOn ⟨le_rfl, zero_le⟩ htmem zero_le
  set u := (a t).toNNReal with hudef
  have hu : (u : ℝ) = a t := Real.coe_toNNReal _ hat0
  have hult : (u : ℝ≥0∞) < ENNReal.ofReal (a v) := by
    rw [← ENNReal.ofReal_coe_nnreal, hu]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hat0).2 (hm htmem ⟨zero_le, le_rfl⟩ htv)
  have hinv : invClock a (v : ℝ≥0∞) u = t := ha.invClock_apply (ENNReal.coe_le_coe.2 htv.le)
  have hneg : (((-c₀.re : ℝ)) : ℂ) = -c₀ := by rw [ofReal_neg, hc₀re]
  have himg : (fun u => RootI30.capacityTipRead x s v u p) '' Icc 0 u =
      (fun z : ℂ => z + ((-c₀.re : ℝ) : ℂ)) ''
        (relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t)) := by
    rw [image_image, image_image]
    ext z
    constructor
    · rintro ⟨u', hu'm, rfl⟩
      have hu'l : (u' : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞) := by
        rw [capLife, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
        have h1 : (u' : ℝ≥0∞) ≤ u := ENNReal.coe_le_coe.2 hu'm.2
        exact h1.trans hult.le
      obtain ⟨ht'v, hat'⟩ := ha.invClock_spec hu'l
      have ht'v' : invClock a (v : ℝ≥0∞) u' ≤ v := ENNReal.coe_le_coe.mp ht'v
      have hle : invClock a (v : ℝ≥0∞) u' ≤ t := by
        by_contra hlt
        have := hm htmem ⟨zero_le, ht'v'⟩ (lt_of_not_ge hlt)
        rw [hat'] at this
        have hu'u : (u' : ℝ) ≤ u := NNReal.coe_le_coe.2 hu'm.2
        rw [hu] at hu'u
        exact absurd hu'u (not_le.2 this)
      refine ⟨invClock a (v : ℝ≥0∞) u', ⟨zero_le, hle⟩, ?_⟩
      change _ = RootH29.rootTipRead x s (invClock a (v : ℝ≥0∞) u') p
      rw [htip _ ht'v', hneg]
      ring
    · rintro ⟨t', ht', rfl⟩
      have ht'v : t' ≤ v := ht'.2.trans htv.le
      refine ⟨(a t').toNNReal, ⟨zero_le, ?_⟩, ?_⟩
      · have hle : a t' ≤ a t := hm.monotoneOn ⟨zero_le, ht'v⟩ htmem ht'.2
        exact Real.toNNReal_le_toNNReal hle
      · change RootH29.rootTipRead x s (invClock a (v : ℝ≥0∞) (a t').toNNReal) p = _
        rw [ha.invClock_apply (ENNReal.coe_le_coe.2 ht'v), htip t' ht'v, hneg]
        ring
  -- both hulls fill the same compact set
  set A := (fun z : ℂ => z + ((-c₀.re : ℝ) : ℂ)) ''
    (relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t)) with hAdef
  have hAc : IsCompact A := (hcpt t htv.le).image (continuous_id.add continuous_const)
  have hK₁H : fwdHull (fun r : ℝ => V r.toNNReal) (a t) ⊆ H := fun z hz => hz.1
  have hK₂H : (fun z : ℂ => z + ((-c₀.re : ℝ) : ℂ)) '' RootH29.forwardHull x s t p ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    have hzH : z ∈ H := by
      rw [← hKV t htmem] at hz
      exact hz.1
    change 0 < (z + ((-c₀.re : ℝ) : ℂ)).im
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show 0 < z.im from hzH)
  have hf₁ : IsFilling (fwdHull (fun r : ℝ => V r.toNNReal) (a t)) A := by
    have h := hgen.2.2 u hult
    rw [himg, hu] at h
    exact h
  have hHP : IsHPHull (RootH29.forwardHull x s t p) := by
    rw [← hKV t htmem]
    exact isHPHull_fwdHull hV' hat0
  have hf₂ := RootI30.isFilling_image_add_full hHP (-c₀.re) (hfill t htmem)
  rw [(fillH_eq_iff_isFilling_of_isClosed hAc.isBounded hAc.isClosed hK₁H).1 hf₁,
    (fillH_eq_iff_isFilling_of_isClosed hAc.isBounded hAc.isClosed hK₂H).1 hf₂]

omit hs in
/-- **The chart preserves interior visits off the hull**: a trace point in `ℍ` off the physical hull at `t₀` is
mapped by the relative chart to a point of `ℍ` off the forward hull at `t₀`. -/
theorem relBdry_mem_diff_forwardHull {t t₀ : ℝ≥0} (htv : t ≤ v)
    (hγt : γ t ∈ H \ fwdHull (rdrv (recOf (v : ℝ≥0∞) e)) t₀) :
    relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) ∈
      H \ RootH29.forwardHull x s t₀ (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
  set U := rdrv (cfRec s W ζ ω) with hUdef
  have hsafe := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv htv
  have hzH : (x : ℂ) + γ t ∈ H := by
    change 0 < ((x : ℂ) + γ t).im
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using (show 0 < (γ t).im from hγt.1)
  have hU := continuous_rdrv (cfRec s W ζ ω)
  have heq := relBdry_eq hU s.coe_nonneg hzH hsafe.2
  have hdom : ∀ {z : ℂ}, z ∈ relDomain U s → -z⁻¹ ∈ H \ fwdHull U s := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := (mem_relDomain_iff U s z).1 hz
    exact ⟨neg_inv_mem_H hz1, hz2⟩
  have hzdom : (x : ℂ) + γ t ∈ relDomain U s :=
    (mem_relDomain_iff U s _).2 ⟨hzH, fun h => hsafe.2 (subset_closure (by
      exact ⟨-((x : ℂ) + γ t)⁻¹, h, neg_inv_neg_inv _⟩))⟩
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact relMap_mem_H hU s.coe_nonneg hzH ((mem_relDomain_iff U s _).1 hzdom).2
  · rintro ⟨z', ⟨hz'T, hz'D⟩, hz'eq⟩
    rw [heq] at hz'eq
    have hf : fwdMap U s (-z'⁻¹) = fwdMap U s (-((x : ℂ) + γ t)⁻¹) := by
      have h := hz'eq
      unfold relMap at h
      exact inv_inj.1 (neg_inj.1 h)
    have hzz := QuantumZipper.FwdHolo.injOn_fwdMap hU s.coe_nonneg (hdom hz'D) (hdom hzdom) hf
    have hz' : z' = (x : ℂ) + γ t := by
      have := congrArg (fun w : ℂ => -w⁻¹) hzz
      rwa [neg_inv_neg_inv, neg_inv_neg_inv] at this
    obtain ⟨y, hy, hyz⟩ := hz'T
    have hyγ : y = γ t := by
      rw [hz'] at hyz
      exact add_left_cancel hyz
    exact hγt.2 (hyγ ▸ hy)

end I30

/-! ### J32's tip -/

/-- **J32's tip in physical time** (deterministic). For a joined driver `J` with a `⊤`-trace `γ`, before contact
up to `w`, whose capacity reader `A` (record at the cap `L ≥ w`) is a strict continuous clock on `[0, w]` from `0`,
J32's tip `t ↦ jointTipRead k x s L v₀ (U t)`, `U t = capacityIncrement k x s v₀ (t − v₀)`,
* is continuous at every `t ∈ [v₀, w)`;
* is in `ℍ` at `t ∈ [v₀, w)` whenever the physical trace mapped out at `v₀` is in `ℍ` at `t − v₀`. -/
theorem jointTip_spec {Ω' : Type*} (W : ℝ≥0 → Ω' → ℝ) (ζ : Ω' → ℝ≥0∞) (ω : Ω')
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
    {k : ℝ≥0} (hk : 0 < k) {v₀ t : ℝ≥0} (hv₀t : v₀ ≤ t) (htw : t < w) :
    ContinuousAt (fun t' : ℝ≥0 => RootJ32.jointTipRead k x s L v₀
        (RootJ31.capacityIncrement k x s v₀ (t' - v₀)
          (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J))
        (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J)) t ∧
      (loewnerTip (shiftDrive (fun r : ℝ => J r.toNNReal) v₀) ((t : ℝ) - v₀) ∈ H →
        RootJ32.jointTipRead k x s L v₀
          (RootJ31.capacityIncrement k x s v₀ (t - v₀)
            (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J))
          (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J) ∈ H) := by
  set p := (cfRec s W ζ ω, StagedEntrance.Strip.recOfDriver L J) with hp
  set A := fun t => RootH29.forwardCapacity x s t p with hAdef
  set p'' := (cfRec s W ζ ω, recOf (w : ℝ≥0∞) (J, (⊤ : ℝ≥0∞))) with hp''
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous α := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have he := isRegularDriver_top hJ hJ0
  have hv : (w : ℝ≥0∞) < min (firstContactTime
      (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (J, (⊤ : ℝ≥0∞)).2 := by
    change _ < min _ ⊤
    rw [min_top_right]
    exact (lt_firstContactTime_iff_noncontact (continuous_const.add hγc) hαc w s).2 hnc
  -- the capacity readers of the two records agree on `[0, w]`
  have hAA : ∀ t' ≤ w, A t' = RootH29.forwardCapacity x s t' p'' := by
    intro t' ht'
    refine forwardCapacity_congr x s t' _ fun y hy => ?_
    have hy0 : 0 ≤ y := hy.1
    have hyw : y.toNNReal ≤ w := (Real.toNNReal_le_iff_le_coe.2 hy.2).trans ht'
    have e1 := rdrv_recOfDriver hJ hJ0 (q₀ := L) y.toNNReal
    have e2 := rdrv_recOfDriver hJ hJ0 (q₀ := w) y.toNNReal
    rw [Real.coe_toNNReal _ hy0] at e1 e2
    rw [e1, ← recOfDriver_eq_recOf, e2, min_eq_left hyw, min_eq_left (hyw.trans hwL)]
  -- the capacity driver and its tip
  obtain ⟨V, hVc, hV0, hgen⟩ :=
    exists_isGeneratingTrace_capacityTip W ζ ω hα hW hW0 hζ hs hx harc he hγ hv
  have hwmem : w ∈ Icc 0 w := ⟨zero_le, le_rfl⟩
  have hcap : ∀ c : ℝ≥0, (c : ℝ) < A w → RootJ32.capacityDriverRead x s L c p = V c := by
    intro c hcw
    rw [RootJ32.capacityDriverRead_eq_of_clock hJ hJ0 hγ hwL hwL hm.monotoneOn hc hcw.le]
    unfold RootJ31.capacityDriverRead
    refine RootB23.traceDriverRead_eq hgen hVc.continuousOn hV0 ?_
    show ((c : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal (RootH29.forwardCapacity x s w p'')
    rw [← ENNReal.ofReal_coe_nnreal, ← hAA w le_rfl]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg c.2).2 hcw
  -- levels
  have hA0 : ∀ t', 0 ≤ A t' := fun t' => RootH29.forwardCapacity_nonneg x s t' p
  have hv₀w : v₀ < w := hv₀t.trans_lt htw
  have hv₀mem : v₀ ∈ Icc 0 w := ⟨zero_le, hv₀w.le⟩
  have htmem : t ∈ Icc 0 w := ⟨zero_le, htw.le⟩
  have hAv₀t : A v₀ ≤ A t := hm.monotoneOn hv₀mem htmem hv₀t
  have hAtw : A t < A w := hm htmem hwmem htw
  set A₀ := (A v₀).toNNReal with hA₀def
  have hA₀ : (A₀ : ℝ) = A v₀ := Real.coe_toNNReal _ (hA0 v₀)
  obtain ⟨σr, hσ1, hσ2⟩ := exists_between hAtw
  have hσr0 : 0 < σr := lt_of_le_of_lt (hA0 t) hσ1
  set σ := σr.toNNReal with hσdef
  have hσ : (σ : ℝ) = σr := Real.coe_toNNReal _ hσr0.le
  have hσB : (σ : ℝ≥0∞) < ENNReal.ofReal (RootH29.forwardCapacity x s w p'') := by
    rw [← hAA w le_rfl, ← ENNReal.ofReal_coe_nnreal, hσ]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hσr0.le).2 hσ2
  have hA₀σ : A₀ < σ := by
    rw [← NNReal.coe_lt_coe, hA₀, hσ]
    exact hAv₀t.trans_lt hσ1
  obtain ⟨hψc, htr, hbd⟩ := exists_jointShiftTip hgen hVc.continuousOn hV0 hσB hA₀σ hk
  -- the increment
  set U : ℝ≥0 → ℝ≥0 := fun t' => RootJ31.capacityIncrement k x s v₀ (t' - v₀) p with hUdef
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk.ne'
  have hUdiv : ∀ t', U t' / k ^ 2 = (A (max v₀ t') - A v₀).toNNReal := by
    intro t'
    simp only [hUdef, RootJ31.capacityIncrement]
    rw [mul_div_cancel_left₀ _ hk2, add_tsub_eq_max]
  have hUt : A₀ + U t / k ^ 2 = (A t).toNNReal := by
    rw [hUdiv, max_eq_right hv₀t, hA₀def, ← Real.toNNReal_add (hA0 v₀) (sub_nonneg.2 hAv₀t),
      add_sub_cancel]
  have hUtσ : A₀ + U t / k ^ 2 < σ := by
    rw [hUt]
    exact (Real.toNNReal_lt_toNNReal_iff hσr0).2 hσ1
  -- the joint driver below the buffer's capacity
  have hJt : ∀ u : ℝ≥0, A₀ + u / k ^ 2 ≤ σ → ∀ r ≤ u,
      RootJ32.jointDriverRead k x s L v₀ p r = k * (V (A₀ + r / k ^ 2) - V A₀) := by
    intro u hu r hr
    have hr'' : A₀ + r / k ^ 2 ≤ σ :=
      le_trans ((add_le_add_iff_left A₀).2 (div_le_div_of_nonneg_right hr zero_le)) hu
    have hr' : ((A₀ + r / k ^ 2 : ℝ≥0) : ℝ) < A w :=
      lt_of_le_of_lt (NNReal.coe_le_coe.2 hr'') (by rw [hσ]; exact hσ2)
    have h0' : (A₀ : ℝ) < A w := by rw [hA₀]; exact hAv₀t.trans_lt hAtw
    show (1 : ℝ) * (k : ℝ) * (RootJ32.capacityDriverRead x s L (A₀ + r / k ^ 2) p -
      RootJ32.capacityDriverRead x s L A₀ p) = _
    rw [one_mul, hcap _ hr', hcap _ h0']
  have htrace : ∀ u : ℝ≥0, A₀ + u / k ^ 2 ≤ σ →
      LP.traceAt u (RootJ32.jointDriverRead k x s L v₀ p) =
        ((k : ℝ) : ℂ) * jointShiftTip V σ A₀ ((u / k ^ 2 : ℝ≥0) : ℝ) :=
    fun u hu => htr _ u hu (hJt u hu)
  have hψk : Continuous fun u : ℝ≥0 =>
      ((k : ℝ) : ℂ) * jointShiftTip V σ A₀ ((u / k ^ 2 : ℝ≥0) : ℝ) :=
    continuous_const.mul (hψc.comp (continuous_id.div_const _))
  have hcontTrace : ∀ u₀ : ℝ≥0, A₀ + u₀ / k ^ 2 < σ →
      ContinuousAt (fun u => LP.traceAt u (RootJ32.jointDriverRead k x s L v₀ p)) u₀ := by
    intro u₀ hu₀
    have hev : ∀ᶠ u in 𝓝 u₀, A₀ + u / k ^ 2 < σ :=
      ((continuous_const.add (continuous_id.div_const _)).continuousAt (x := u₀)).eventually
        (gt_mem_nhds hu₀)
    refine (hψk.continuousAt (x := u₀)).congr ?_
    filter_upwards [hev] with u hu
    exact (htrace u hu.le).symm
  have htipeq : ∀ t' : ℝ≥0, A₀ + U t' / k ^ 2 < σ →
      RootJ32.jointTipRead k x s L v₀ (U t') p =
        ((k : ℝ) : ℂ) * jointShiftTip V σ A₀ ((U t' / k ^ 2 : ℝ≥0) : ℝ) := by
    intro t' ht'
    unfold RootJ32.jointTipRead RootJ32.jointTraceRead
    rw [drivingTrace_top_snd, endVal_eq_of_continuousAt (hcontTrace _ ht')]
    exact htrace _ ht'.le
  refine ⟨?_, fun hψp => ?_⟩
  · -- continuity
    have hAc : ContinuousAt A t :=
      hc.continuousAt (mem_of_superset (Iic_mem_nhds htw) fun y hy => ⟨zero_le, hy⟩)
    have hcomp : ContinuousAt (fun t' => A (max v₀ t')) t :=
      ContinuousAt.comp (g := A) (f := fun t' => max v₀ t') (by rw [max_eq_right hv₀t]; exact hAc)
        (continuous_const.max continuous_id).continuousAt
    have hlev : ContinuousAt (fun t' => U t' / k ^ 2) t := by
      have h : ContinuousAt (fun t' => (A (max v₀ t') - A v₀).toNNReal) t :=
        continuous_real_toNNReal.continuousAt.comp (hcomp.sub (continuousAt_const (y := A v₀)))
      refine h.congr (Eventually.of_forall fun t' => ?_)
      exact (hUdiv t').symm
    have hev : ∀ᶠ t' in 𝓝 t, A₀ + U t' / k ^ 2 < σ :=
      (continuousAt_const.add hlev).eventually (gt_mem_nhds hUtσ)
    have hf : ContinuousAt (fun t' => ((k : ℝ) : ℂ) *
        jointShiftTip V σ A₀ ((U t' / k ^ 2 : ℝ≥0) : ℝ)) t :=
      continuousAt_const.mul ((hψc.continuousAt).comp hlev)
    refine hf.congr ?_
    filter_upwards [hev] with t' ht'
    exact (htipeq t' ht').symm
  · -- interior visits
    rw [htipeq t hUtσ]
    by_contra hcon
    have hψt : jointShiftTip V σ A₀ ((U t / k ^ 2 : ℝ≥0) : ℝ) ∉ H := by
      intro h
      apply hcon
      change 0 < (((k : ℝ) : ℂ) * _).im
      rw [Complex.im_ofReal_mul]
      exact mul_pos (by exact_mod_cast hk) h
    have h1 := hbd (U t / k ^ 2) hUtσ.le hψt
    rw [hUt] at h1
    -- the capacity tip at `A(t)` is the charted physical tip
    have hclk : IsClockOn (fun t => RootH29.forwardCapacity x s t p'') (w : ℝ≥0∞) := by
      have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (w : ℝ≥0∞)} = Icc 0 w := by
        ext t
        simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
      refine ⟨by rw [← hAA 0 zero_le]; exact hA00, ?_, ?_, fun h => (ENNReal.coe_ne_top h).elim⟩
      · rw [hset]
        intro a ha b hb hab
        show RootH29.forwardCapacity x s a p'' < RootH29.forwardCapacity x s b p''
        rw [← hAA a ha.2, ← hAA b hb.2]
        exact hm ha hb hab
      · rw [hset]
        exact hc.congr fun a ha => (hAA a ha.2).symm
    have hηt : RootI30.capacityTipRead x s w (A t).toNNReal p'' =
        relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) -
          relBdry (rdrv (cfRec s W ζ ω)) s x := by
      unfold RootI30.capacityTipRead RootI30.clockInverse
      rw [hAA t htw.le, hclk.invClock_apply (ENNReal.coe_le_coe.2 htw.le)]
      exact RootH29.rootTipRead_eq W ζ ω hα hW hW0 hζ hx harc he hγ hv htw.le
    have hhull := fwdHull_capacityDriver_eq W ζ ω hα hW hW0 hζ hs hx harc he hγ hv hgen hv₀w
    have hA₀' : ((A₀ : ℝ≥0) : ℝ) = RootH29.forwardCapacity x s v₀ p'' := by
      rw [hA₀, hAA v₀ hv₀w.le]
    rw [hηt, hA₀', hhull] at h1
    -- the chart root is real
    have hsafe0 := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv
      (t := 0) zero_le
    rw [hγ.1, add_zero] at hsafe0
    set c₀ := relBdry (rdrv (cfRec s W ζ ω)) s x with hc₀
    have hc₀im : c₀.im = 0 :=
      im_relBdry_of_real (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsafe0.2
    have hc₀re : ((-c₀.re : ℝ) : ℂ) = -c₀ := by
      rw [ofReal_neg]
      congr 1
      exact Complex.ext (by simp) (by simp [hc₀im])
    -- the physical trace mapped out at `v₀`
    have hLJ : IsLoewnerTrace (fun r : ℝ => J r.toNNReal) (fun r : ℝ => γ r.toNNReal) :=
      isLoewnerTrace_of_isGeneratingTrace hγ
    have hJc : Continuous fun r : ℝ => J r.toNNReal := hJ.comp continuous_real_toNNReal
    have hJr0 : (fun r : ℝ => J r.toNNReal) 0 = 0 := by simp [hJ0]
    have hphys := mem_diff_of_shiftTip_mem_H hLJ hJc hJr0 v₀.coe_nonneg
      (sub_nonneg.2 (NNReal.coe_le_coe.2 hv₀t)) hψp
    have hvt : ((v₀ : ℝ) + ((t : ℝ) - v₀)).toNNReal = t := by
      rw [add_sub_cancel, Real.toNNReal_coe]
    simp only [hvt] at hphys
    have hK : fwdHull (rdrv (recOf (w : ℝ≥0∞) (J, (⊤ : ℝ≥0∞)))) v₀ =
        fwdHull (fun r : ℝ => J r.toNNReal) v₀ := by
      refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_rdrv _) hJc v₀.coe_nonneg
        fun y hy => ?_
      have hy0 : 0 ≤ y := hy.1
      have hyw : y.toNNReal ≤ w := (Real.toNNReal_le_iff_le_coe.2 hy.2).trans hv₀w.le
      have e2 := rdrv_recOfDriver hJ hJ0 (q₀ := w) y.toNNReal
      rw [Real.coe_toNNReal _ hy0] at e2
      rw [← recOfDriver_eq_recOf, e2, min_eq_left hyw]
    rw [← hK] at hphys
    have hchart := relBdry_mem_diff_forwardHull W ζ ω hα hW hW0 hζ hx harc he hγ hv htw.le hphys
    apply h1
    refine ⟨?_, ?_⟩
    · change 0 < (_ - c₀).im
      rw [Complex.sub_im, hc₀im, sub_zero]
      exact hchart.1
    · rintro ⟨z, hz, hzeq⟩
      apply hchart.2
      have : z = relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) := by
        rw [hc₀re] at hzeq
        have := congrArg (· + c₀) hzeq
        simpa only [neg_add_cancel_right, sub_add_cancel] using this
      exact this ▸ hz

end InteractingSLE.Theorem14.GW2TipSystem.Gm
