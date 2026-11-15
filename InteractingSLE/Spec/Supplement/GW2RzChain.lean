/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfDrv
import InteractingSLE.Foundations.Loewner.ConformalImageFull
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# GW2 at a root `x`: the re-centred relative chain (decision D8, layer 1)

Packet PROVE-GW2-ROOTX, round 3 (decision D8 of `planning/reviews/DECISIONS-FABLE-2.md`, option (A)). The stage
instance at a root `x` reads the explored curve `x + γ` in GB6's relative chart re-centred at the root's chart image
`relBase x s rec` (the real boundary value of the relative map at `x`). ROOT2 built the per-sample relative chain at
any root (`RootI30.exists_reader_chain`), with a continuous driver `V` whose hulls are the forward hulls; BUF showed
that J31's measurable capacity reader is EVERY re-centred driver (`GW2Bf.capacityDriverRead_eq_of_hull`). The missing
link was that such a re-centred driver exists: ROOT2's `V` starts at the root's image.

* `fwdHull_subset_closedBall_start` (a hull lies near its driver's start), `fwdHull_nonempty'`,
  `subset_of_isFilling`, `isPreconnected_H`, `nonempty_of_isFilling`;
* **`driver_zero_eq`**: the driver of a chain starts at the start of the curve whose points fill its hulls;
* **`exists_recentred_chain`**: on a sample with a protected root arc and a horizon `0 < v` before the first contact,
  there is a continuous driver from `0` whose hulls at ROOT2's capacity reader are the forward hulls re-centred at
  `relBase` (exactly the hypothesis of `GW2Bf.capacityDriverRead_eq_of_hull`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Rz

/-- **Hull localization around the driver's start.** -/
theorem fwdHull_subset_closedBall_start {V : ℝ → ℝ} (hV : Continuous V) {σ M : ℝ} (hσ : 0 < σ)
    (hM : ∀ r ∈ Icc (0 : ℝ) σ, |V r - V 0| ≤ M) :
    fwdHull V σ ⊆ Metric.closedBall (V 0 : ℂ) (M + 3 * Real.sqrt σ) := by
  have h := QuantumZipper.CaraR.fwdHull_subset_closedBall (A := fun r => V r - V 0)
    (hV.sub continuous_const) hσ hM
  have e := ConformalImageFull.fwdHull_add_const (fun r => V r - V 0) (V 0) σ
  simp only [sub_add_cancel] at e
  rw [e]
  rintro _ ⟨z, hz, rfl⟩
  have hz' := h hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz'
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right]
  exact hz'

/-- A hull of positive capacity of a continuous driver is nonempty. -/
theorem fwdHull_nonempty' {V : ℝ → ℝ} (hV : Continuous V) {σ : ℝ} (hσ : 0 < σ) : (fwdHull V σ).Nonempty := by
  have h := QuantumZipper.CaraR.fwdHull_nonempty (A := fun r => V r - V 0) (hV.sub continuous_const)
    (sub_self _) hσ
  have e := ConformalImageFull.fwdHull_add_const (fun r => V r - V 0) (V 0) σ
  simp only [sub_add_cancel] at e
  rw [e]
  exact h.image _

/-- **A filling contains the points of the filled set in `ℍ`.** -/
theorem subset_of_isFilling {K A : Set ℂ} (hK : IsFilling K A) : A ∩ H ⊆ K := by
  obtain ⟨⟨z, -, hz⟩, -⟩ := hK
  intro w ⟨hwA, hwH⟩
  by_contra hwK
  have hw : w ∈ H \ K := ⟨hwH, hwK⟩
  rw [← hz] at hw
  exact (connectedComponentIn_subset _ _ hw).2 hwA

theorem isPreconnected_H : IsPreconnected H :=
  (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected

/-- **A nonempty hull fills a nonempty set**: a filling of a set missing `ℍ` meets no point of `ℍ`. -/
theorem nonempty_of_isFilling {K A : Set ℂ} (hK : IsFilling K A) (hKH : K ⊆ H) (hne : K.Nonempty) :
    (A ∩ H).Nonempty := by
  by_contra hA
  rw [not_nonempty_iff_eq_empty] at hA
  obtain ⟨⟨z, hz, hcc⟩, -⟩ := hK
  have hHA : H \ A = H := by
    ext w
    refine ⟨fun h => h.1, fun hw => ⟨hw, fun hwA => ?_⟩⟩
    have : w ∈ A ∩ H := ⟨hwA, hw⟩
    rw [hA] at this
    exact this
  rw [hHA, isPreconnected_H.connectedComponentIn hz.1] at hcc
  obtain ⟨w, hw⟩ := hne
  have hwH : w ∈ H \ K := by
    rw [← hcc]
    exact hKH hw
  exact hwH.2 hw

/-- **The driver of a chain starts at the start of the curve filling its hulls.** If the hulls of a continuous
driver `V` at a clock `a` (continuous at `0`, `a 0 = 0`, positive after `0`) are the fillings of sets of points of a
curve `f` (continuous at `0`) taken before the time, then `V 0 = f 0`. -/
theorem driver_zero_eq {V a : ℝ → ℝ} (hV : Continuous V) (ha0 : a 0 = 0) {v : ℝ} (hv : 0 < v)
    (hapos : ∀ t ∈ Ioc 0 v, 0 < a t) (hac : ContinuousWithinAt a (Icc 0 v) 0)
    {f : ℝ → ℂ} (hf : ContinuousWithinAt f (Icc 0 v) 0) {S : ℝ → Set ℂ}
    (hfill : ∀ t ∈ Ioc 0 v, IsFilling (fwdHull V (a t)) (S t))
    (hS : ∀ t ∈ Ioc 0 v, S t ⊆ f '' Icc 0 t) :
    (V 0 : ℂ) = f 0 := by
  by_contra hne
  have hd : 0 < ‖f 0 - (V 0 : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  set ε := ‖f 0 - (V 0 : ℂ)‖ / 2 with hε
  have hεpos : 0 < ε := by positivity
  -- continuity of `V` at `0`
  obtain ⟨δ₁, hδ₁, hV1⟩ := Metric.continuous_iff.1 hV 0 (ε / 3) (by positivity)
  set σ₀ := min (δ₁ / 2) ((ε / 9) ^ 2) with hσ₀
  have hσ₀pos : 0 < σ₀ := lt_min (by positivity) (by positivity)
  -- continuity of `a` at `0`
  obtain ⟨δ₂, hδ₂, ha2⟩ := Metric.continuousWithinAt_iff.1 hac σ₀ hσ₀pos
  -- continuity of `f` at `0`
  obtain ⟨δ₃, hδ₃, hf3⟩ := Metric.continuousWithinAt_iff.1 hf (ε / 3) (by positivity)
  set t := min v (min δ₂ δ₃) / 2 with ht
  have htpos : 0 < t := by positivity
  have htv : t ≤ v := by
    have : min v (min δ₂ δ₃) ≤ v := min_le_left _ _
    linarith
  have htmem : t ∈ Ioc 0 v := ⟨htpos, htv⟩
  have htd : ∀ u ∈ Icc (0 : ℝ) t, dist u 0 < min δ₂ δ₃ := by
    intro u hu
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
    have h1 : min v (min δ₂ δ₃) ≤ min δ₂ δ₃ := min_le_right _ _
    have h2 : 0 < min δ₂ δ₃ := lt_min hδ₂ hδ₃
    linarith [hu.2]
  -- the capacity at `t`
  set σ := a t with hσdef
  have hσpos : 0 < σ := hapos t htmem
  have hσlt : σ < σ₀ := by
    have h := ha2 (x := t) ⟨htpos.le, htv⟩ (lt_of_lt_of_le (htd t ⟨htpos.le, le_rfl⟩) (min_le_left _ _))
    rw [ha0, Real.dist_eq, sub_zero, abs_of_pos hσpos] at h
    exact h
  have hσδ : σ < δ₁ := by
    have : σ₀ ≤ δ₁ / 2 := min_le_left _ _
    linarith
  have hsq : 3 * Real.sqrt σ ≤ ε / 3 := by
    have h1 : σ ≤ (ε / 9) ^ 2 := hσlt.le.trans (min_le_right _ _)
    have h2 : Real.sqrt σ ≤ ε / 9 := by
      rw [Real.sqrt_le_left (by positivity)]
      exact h1
    linarith
  have hM : ∀ r ∈ Icc (0 : ℝ) σ, |V r - V 0| ≤ ε / 3 := by
    intro r hr
    have h := hV1 r (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]; linarith [hr.2])
    rw [Real.dist_eq] at h
    exact h.le
  have hball := fwdHull_subset_closedBall_start hV hσpos hM
  -- a point of the filled set
  have hKH : fwdHull V σ ⊆ H := (isHPHull_fwdHull hV hσpos.le).1
  obtain ⟨w, hwS, hwH⟩ := nonempty_of_isFilling (hfill t htmem) hKH (fwdHull_nonempty' hV hσpos)
  have hwK : w ∈ fwdHull V σ := subset_of_isFilling (hfill t htmem) ⟨hwS, hwH⟩
  obtain ⟨u, hu, rfl⟩ := hS t htmem hwS
  have h1 : ‖f u - (V 0 : ℂ)‖ ≤ ε / 3 + 3 * Real.sqrt σ := by
    have := hball hwK
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have h2 : ‖f u - f 0‖ < ε / 3 := by
    have := hf3 (x := u) ⟨hu.1, hu.2.trans htv⟩ (lt_of_lt_of_le (htd u hu) (min_le_right _ _))
    rwa [dist_eq_norm] at this
  have h3 : ‖f 0 - (V 0 : ℂ)‖ ≤ ‖f u - f 0‖ + ‖f u - (V 0 : ℂ)‖ := by
    calc ‖f 0 - (V 0 : ℂ)‖ = ‖(f u - (V 0 : ℂ)) - (f u - f 0)‖ := by ring_nf
      _ ≤ ‖f u - (V 0 : ℂ)‖ + ‖f u - f 0‖ := norm_sub_le _ _
      _ = ‖f u - f 0‖ + ‖f u - (V 0 : ℂ)‖ := add_comm _ _
  have : ‖f 0 - (V 0 : ℂ)‖ < ‖f 0 - (V 0 : ℂ)‖ := by
    calc ‖f 0 - (V 0 : ℂ)‖ ≤ ‖f u - f 0‖ + ‖f u - (V 0 : ℂ)‖ := h3
      _ < ε / 3 + (ε / 3 + ε / 3) := by linarith
      _ = ‖f 0 - (V 0 : ℂ)‖ / 2 := by rw [hε]; ring
      _ < ‖f 0 - (V 0 : ℂ)‖ := by linarith
  exact lt_irrefl _ this

section Chain

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB GW2TipSystem Complex

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

/-- **The re-centred relative chain at a root `x`**: a continuous driver from `0` whose hulls at ROOT2's capacity
reader are the forward hulls re-centred at the root's chart image `relBase` (the hypothesis of
`GW2Bf.capacityDriverRead_eq_of_hull`). ROOT2's chain driver starts at the root's image (`driver_zero_eq`). -/
theorem exists_recentred_chain (hv0 : 0 < v) : ∃ R : ℝ≥0 → ℝ, Continuous R ∧ R 0 = 0 ∧
    ∀ t ∈ Icc 0 v, fwdHull (fun r : ℝ => R r.toNNReal)
        (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) : ℝ) : ℂ)) ''
        RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
  set p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) with hp
  set a := fun t => RootH29.forwardCapacity x s t p with hadef
  set U := rdrv (cfRec s W ζ ω) with hUdef
  obtain ⟨V, hV, h0', hm', hc', hK⟩ := RootI30.exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv
  have h0 : a 0 = 0 := h0'
  have hm : StrictMonoOn a (Icc 0 v) := hm'
  have hc : ContinuousOn a (Icc 0 v) := hc'
  have hKV : ∀ t ∈ Icc 0 v, fwdHull V (a t) = RootH29.forwardHull x s t p := fun t ht => (hK t ht).2.1
  have hrec := GaugeE.record_prefix_eq s hW0 hW.continuousOn
    (show (s : ℝ≥0∞) < ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)
  have hmap : relMap U s = relMap (Ito.rpath (W · ω)) s := relMap_eq_of_eqOn s.coe_nonneg hrec
  have hsafe : ∀ t ≤ v, (x : ℂ) + γ t ∈ relSafe U s := fun t ht =>
    RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv ht
  set c₀ := relBdry U s x with hc₀
  have hsafe0 : (x : ℂ) ∈ relSafe U s := by
    have h := hsafe 0 zero_le
    rwa [hγ.1, add_zero] at h
  have hc₀im : c₀.im = 0 := im_relBdry_of_real (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsafe0.2
  have hc₀re : ((c₀.re : ℝ) : ℂ) = c₀ := Complex.ext (by simp) (by simp [hc₀im])
  have hbase : GW2Bf.relBase x s p = c₀.re := rfl
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
  -- the chain driver starts at the root's image
  have hγc : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ e.2} := hγ.2.1
  have hvle : (v : ℝ≥0∞) ≤ e.2 := (hv.trans_le (min_le_right _ _)).le
  have hfc : ContinuousOn (fun t : ℝ≥0 => relBdry U s ((x : ℂ) + γ t)) (Icc 0 v) := by
    refine (continuousOn_relBdry (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg).comp
      (continuousOn_const.add (hγc.mono fun t ht => ?_)) fun t ht => hsafe t ht.2
    exact (ENNReal.coe_le_coe.2 ht.2).trans hvle
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv0
  have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) v) (Icc 0 v) := fun r hr =>
    ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hr.2⟩
  have hV0 : (V 0 : ℂ) = c₀ := by
    have h := driver_zero_eq (V := V) (a := fun r : ℝ => a r.toNNReal)
      (f := fun r : ℝ => relBdry U s ((x : ℂ) + γ r.toNNReal))
      (S := fun t : ℝ => relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t.toNNReal)) hV
      (by simpa only [Real.toNNReal_zero] using h0) hvpos
      (fun t ht => by
        have htpos : (0 : ℝ≥0) < t.toNNReal := Real.toNNReal_pos.2 ht.1
        have := hm ⟨le_rfl, zero_le⟩ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 ht.2⟩ htpos
        simpa only [h0] using this)
      ((hc.comp continuous_real_toNNReal.continuousOn hmaps).continuousWithinAt ⟨le_rfl, hvpos.le⟩)
      ((hfc.comp continuous_real_toNNReal.continuousOn hmaps).continuousWithinAt ⟨le_rfl, hvpos.le⟩)
      (fun t ht => by
        have htv : t.toNNReal ∈ Icc 0 v := hmaps ⟨ht.1.le, ht.2⟩
        change IsFilling (fwdHull V (a t.toNNReal)) _
        rw [hKV _ htv]
        exact hfill _ htv)
      (fun t ht => by
        rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
        refine ⟨(q : ℝ), ⟨q.2, ?_⟩, ?_⟩
        · exact (Real.le_toNNReal_iff_coe_le ht.1.le).1 hq.2
        · simp only [Real.toNNReal_coe])
    simpa only [Real.toNNReal_zero, hγ.1, add_zero] using h
  have hV0r : V 0 = c₀.re := by
    have h := congrArg Complex.re hV0
    simpa only [Complex.ofReal_re] using h
  refine ⟨fun r => V r - c₀.re, hV.comp NNReal.continuous_coe |>.sub continuous_const, ?_, fun t ht => ?_⟩
  · simp only [NNReal.coe_zero, hV0r, sub_self]
  · have hat : 0 ≤ a t := by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
      · rw [← h, h0]
      · exact (h0 ▸ hm ⟨le_rfl, zero_le⟩ ⟨zero_le, ht.2⟩ h).le
    have he1 : fwdHull (fun r : ℝ => (fun r : ℝ≥0 => V r - c₀.re) r.toNNReal) (a t) =
        fwdHull (fun r : ℝ => V r + (-c₀.re)) (a t) := by
      refine QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn
        ((hV.comp (NNReal.continuous_coe.comp continuous_real_toNNReal)).sub continuous_const)
        (hV.add continuous_const) hat fun r hr => ?_
      change V (r.toNNReal : ℝ) - c₀.re = V r + -c₀.re
      rw [Real.coe_toNNReal _ hr.1, sub_eq_add_neg]
    change fwdHull _ (a t) = _
    rw [he1, ConformalImageFull.fwdHull_add_const V (-c₀.re) (a t), hKV t ht, hbase]

end Chain

end InteractingSLE.Theorem14.GW2Rz
