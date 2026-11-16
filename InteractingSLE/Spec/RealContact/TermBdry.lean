/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermBuilder
import InteractingSLE.Spec.Restart.ChartDataFibre

/-!
# The boundary extension of the entry chart (builder frame)

Packet PROVE-RC-TERM, second run (ruling R124). For a completed retained path with entry data (`Term.IsEntryData`,
positive tip), the entry chart `entryChart V T d` of `entryDom ξ T d = ℍ ∖ fill(path)` extends continuously to the
closure of its domain:

* `IsEntryData.entryInv_mem_closure`, `entryInv_real_notMem`, `exists_norm_entryInv_sub_le`: the boundary inverse
  `entryInv` maps `ℍ̄` into the closure of the domain, real points off the domain, and moves points boundedly;
* **`IsEntryData.fibre_eq`**: every point of the path has at most one real preimage under `entryInv` (Yuan's fibre
  lemma `Restart.eq_of_apply_eq_of_linked`: the path runs from a real seed to a real tip, so every other point of it
  is joined to the real line inside the path off the given point);
* **`IsEntryData.exists_tendsto_fwd`**: the forward chart has a limit along the domain at every point of its closure
  (interior points; free real points, which are alive; points of the path, `Restart.exists_tendsto_of_fibre`);
* `entryExt`: the extension by limits; **`IsEntryData.continuousOn_entryExt`**, `entryInv_entryExt`,
  `entryExt_mem_Hbar`, `entryExt_of_isFreeAt`, **`IsEntryData.entryExt_zero`** (the explorer's seed goes to `0`,
  also when it is the seed of the path).

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd IsForwardSol)

namespace InteractingSLE.RealContact

namespace Term

open Supp9B HalfPlaneSep Theorem14 Theorem14.SB Theorem14.SB.FinRel
open Exist.StagedLaw (markPos markPosL)

variable {V : ℝ → ℝ} {T : ℝ} {ξ : ℝ → ℂ} {p d : ℝ}

/-- The domain of the entry chart: the complement in `ℍ` of the filled completed path. -/
def entryDom (ξ : ℝ → ℂ) (T d : ℝ) : Set ℂ := H \ fillH (entryPath ξ T d '' Icc 0 1)

/-- The extension by limits of the forward entry chart to the closure of its domain. -/
def entryExt (V : ℝ → ℝ) (ξ : ℝ → ℂ) (T d : ℝ) : ℂ → ℂ := extendFrom (entryDom ξ T d) (entryChart V T d).1

theorem IsEntryData.isDomainChart' (h : IsEntryData V T ξ p d) : IsDomainChart (entryDom ξ T d) (entryChart V T d) :=
  h.isDomainChart

theorem IsEntryData.isCompact_path (h : IsEntryData V T ξ p d) : IsCompact (entryPath ξ T d '' Icc 0 1) :=
  isCompact_Icc.image_of_continuousOn h.continuousOn_entryPath

theorem IsEntryData.path_subset_Hbar (h : IsEntryData V T ξ p d) : entryPath ξ T d '' Icc 0 1 ⊆ Hbar := by
  rintro _ ⟨s, hs, rfl⟩
  exact h.im_entryPath_nonneg hs

theorem IsEntryData.entryPath_one (h : IsEntryData V T ξ p d) : entryPath ξ T d 1 = ((p + d : ℝ) : ℂ) := by
  simp only [entryPath, one_mul, h.tip.tip, ofReal_add]

/-! ### The boundary inverse -/

theorem IsEntryData.entryInv_eq_inv (h : IsEntryData V T ξ p d) {v : ℂ} (hv : v ∈ H) :
    entryInv V T d v = (entryChart V T d).2.1 v :=
  entryInv_eqOn h.tip.cont h.tip.zero h.tip.pos.le d hv

theorem IsEntryData.tendsto_inv (h : IsEntryData V T ξ p d) {v : ℂ} (hv : 0 ≤ v.im) :
    Tendsto (entryChart V T d).2.1 (𝓝[H] v) (𝓝 (entryInv V T d v)) := by
  have hcw : ContinuousWithinAt (entryInv V T d) {w | 0 ≤ w.im} v := h.continuousOn_entryInv v hv
  have h1 : Tendsto (entryInv V T d) (𝓝[H] v) (𝓝 (entryInv V T d v)) :=
    hcw.tendsto.mono_left (nhdsWithin_mono _ fun w (hw : 0 < w.im) => le_of_lt hw)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw using h.entryInv_eq_inv hw

theorem neBot_nhdsWithin_H_of_im_nonneg {v : ℂ} (hv : 0 ≤ v.im) : (𝓝[H] v).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hv)

/-- The boundary inverse maps the closed half-plane into the closure of the domain. -/
theorem IsEntryData.entryInv_mem_closure (h : IsEntryData V T ξ p d) {v : ℂ} (hv : 0 ≤ v.im) :
    entryInv V T d v ∈ closure (entryDom ξ T d) := by
  have : (𝓝[H] v).NeBot := neBot_nhdsWithin_H_of_im_nonneg hv
  exact mem_closure_of_tendsto (h.tendsto_inv hv)
    (eventually_nhdsWithin_of_forall fun w hw => h.isDomainChart'.inv_mem hw)

/-- The boundary inverse maps real points off the domain. -/
theorem IsEntryData.entryInv_real_notMem (h : IsEntryData V T ξ p d) (x : ℝ) :
    entryInv V T d (x : ℂ) ∉ entryDom ξ T d := by
  have hlim := h.tendsto_inv (v := (x : ℂ)) (by rw [ofReal_im])
  have := notMem_image_of_tendsto_inv h.isDomainChart'.1 hlim
  rwa [h.isDomainChart'.image_eq] at this

/-- The boundary inverse moves the points of the closed half-plane by a bounded amount. -/
theorem IsEntryData.exists_norm_entryInv_sub_le (h : IsEntryData V T ξ p d) :
    ∃ C : ℝ, ∀ v : ℂ, 0 ≤ v.im → ‖entryInv V T d v - v‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le h.tip.cont h.tip.zero h.tip.pos.le
  refine ⟨C + |markPosL V T (-d)| + |d|, fun v hv => ?_⟩
  have hH : ∀ w ∈ H, ‖entryInv V T d w - w‖ ≤ C + |markPosL V T (-d)| + |d| := by
    intro w hw
    have hw0 : 0 < w.im := hw
    have hwm : w + (markPosL V T (-d) : ℂ) ∈ H := by
      show 0 < (w + (markPosL V T (-d) : ℂ)).im
      simpa only [add_im, ofReal_im, add_zero] using hw0
    rw [h.entryInv_eq_inv hw, entryChart_inv]
    have h1 := hC _ hwm
    have e : fwdMapInv V T (w + (markPosL V T (-d) : ℂ)) + (d : ℂ) - w =
        (fwdMapInv V T (w + (markPosL V T (-d) : ℂ)) - (w + (markPosL V T (-d) : ℂ))) +
          (markPosL V T (-d) : ℂ) + (d : ℂ) := by ring
    rw [e]
    calc ‖(fwdMapInv V T (w + (markPosL V T (-d) : ℂ)) - (w + (markPosL V T (-d) : ℂ))) +
          (markPosL V T (-d) : ℂ) + (d : ℂ)‖
        ≤ ‖(fwdMapInv V T (w + (markPosL V T (-d) : ℂ)) - (w + (markPosL V T (-d) : ℂ))) +
          (markPosL V T (-d) : ℂ)‖ + ‖(d : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖fwdMapInv V T (w + (markPosL V T (-d) : ℂ)) - (w + (markPosL V T (-d) : ℂ))‖ +
          ‖(markPosL V T (-d) : ℂ)‖ + ‖(d : ℂ)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ C + |markPosL V T (-d)| + |d| := by
          rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          linarith
  have : (𝓝[H] v).NeBot := neBot_nhdsWithin_H_of_im_nonneg hv
  have hcw : ContinuousWithinAt (entryInv V T d) {w | 0 ≤ w.im} v := h.continuousOn_entryInv v hv
  have h1 : Tendsto (entryInv V T d) (𝓝[H] v) (𝓝 (entryInv V T d v)) :=
    hcw.tendsto.mono_left (nhdsWithin_mono _ fun w (hw : 0 < w.im) => le_of_lt hw)
  have h2 : Tendsto (fun w => ‖entryInv V T d w - w‖) (𝓝[H] v) (𝓝 ‖entryInv V T d v - v‖) :=
    (h1.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).norm
  exact le_of_tendsto h2 (eventually_nhdsWithin_of_forall fun w hw => hH w hw)

/-! ### One real preimage over every point of the path -/

/-- **Every point of the completed path has at most one real preimage under the boundary inverse.** -/
theorem IsEntryData.fibre_eq (h : IsEntryData V T ξ p d) {q : ℂ} (hq : q ∈ entryPath ξ T d '' Icc 0 1)
    {x y : ℝ} (hx : entryInv V T d (x : ℂ) = q) (hy : entryInv V T d (y : ℂ) = q) : x = y := by
  set K := entryPath ξ T d '' Icc 0 1 with hK
  set D := entryDom ξ T d with hD
  have hDc := h.isDomainChart'
  have hKc : IsCompact K := h.isCompact_path
  have hFd : DifferentiableOn ℂ (entryInv V T d) H :=
    hDc.1.1.congr fun w hw => h.entryInv_eq_inv hw
  have hFc : ContinuousOn (entryInv V T d) Hbar := h.continuousOn_entryInv
  have hFi : InjOn (entryInv V T d) H := fun w hw w' hw' he => by
    rw [h.entryInv_eq_inv hw, h.entryInv_eq_inv hw'] at he
    exact hDc.1.injOn hw hw' he
  have hFD : MapsTo (entryInv V T d) H D := fun w hw => by
    rw [h.entryInv_eq_inv hw]; exact hDc.inv_mem hw
  have hFs : SurjOn (entryInv V T d) H D := by
    intro z hz
    exact ⟨(entryChart V T d).1 z, hDc.fwd_mem hz, by
      rw [h.entryInv_eq_inv (hDc.fwd_mem hz)]; exact hDc.inv_fwd hz⟩
  have hFbd : MapsTo (entryInv V T d) (Hbar \ H) (frontier D) := by
    intro w hw
    have him : w.im = 0 := le_antisymm (not_lt.1 hw.2) hw.1
    have hwr : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hDc.isOpen.frontier_eq]
    refine ⟨h.entryInv_mem_closure hw.1, ?_⟩
    rw [hwr]
    exact h.entryInv_real_notMem w.re
  have hFinf : Tendsto (entryInv V T d) (cobounded ℂ ⊓ 𝓟 Hbar) (cobounded ℂ) := by
    obtain ⟨C, hC⟩ := h.exists_norm_entryInv_sub_le
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    have hn : Tendsto (fun w : ℂ => ‖w‖ - C) (cobounded ℂ ⊓ 𝓟 Hbar) atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    refine tendsto_atTop_mono' _ ?_ hn
    filter_upwards [mem_inf_of_right (mem_principal_self Hbar)] with w hw
    have h1 := hC w hw
    have h2 := norm_sub_norm_le w (entryInv V T d w)
    rw [norm_sub_rev] at h1
    linarith
  have hDE : Disjoint D ({z : ℂ | z.im = 0} ∪ K) := by
    refine Set.disjoint_left.2 fun z hz hzE => ?_
    rcases hzE with h0 | h0
    · exact (ne_of_gt (show 0 < z.im from hz.1)) h0
    · exact hz.2 ⟨hz.1, Or.inl (subset_closure h0)⟩
  have hfr : frontier D ⊆ {z : ℂ | z.im = 0} ∪ K := by
    have := frontier_H_diff_fillH_subset hKc.isBounded (A := K)
    rwa [hKc.isClosed.closure_eq] at this
  have hlink : Restart.IsUnboundedLinked (({z : ℂ | z.im = 0} ∪ K) \ {q}) := by
    refine Restart.isUnboundedLinked_of_forall fun z hz hzq => ?_
    obtain ⟨s₀, hs₀, rfl⟩ := hq
    obtain ⟨s, hs, rfl⟩ := hz
    have hss₀ : s ≠ s₀ := fun he => hzq (by rw [he])
    rcases lt_or_gt_of_ne hss₀ with hlt | hgt
    · refine ⟨entryPath ξ T d '' Icc 0 s, image_mono (Icc_subset_Icc_right hs.2),
        isPreconnected_Icc.image _ (h.continuousOn_entryPath.mono (Icc_subset_Icc_right hs.2)),
        ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩, ?_, entryPath ξ T d 0, ⟨0, ⟨le_rfl, hs.1⟩, rfl⟩, ?_⟩
      · rintro ⟨u, hu, he⟩
        have := h.injOn_entryPath ⟨hu.1, hu.2.trans hs.2⟩ hs₀ he
        linarith [hu.2]
      · rw [h.entryPath_zero, ofReal_im]
    · refine ⟨entryPath ξ T d '' Icc s 1, image_mono (Icc_subset_Icc_left hs.1),
        isPreconnected_Icc.image _ (h.continuousOn_entryPath.mono (Icc_subset_Icc_left hs.1)),
        ⟨s, ⟨le_rfl, hs.2⟩, rfl⟩, ?_, entryPath ξ T d 1, ⟨1, ⟨hs.2, le_rfl⟩, rfl⟩, ?_⟩
      · rintro ⟨u, hu, he⟩
        have := h.injOn_entryPath ⟨hs.1.trans hu.1, hu.2⟩ hs₀ he
        linarith [hu.1]
      · rw [h.entryPath_one, ofReal_im]
  exact Restart.eq_of_apply_eq_of_linked hDc.isOpen hFd hFc hFi hFD hFs hFbd hFinf hDE hfr hlink hx hy

/-! ### Forward limits on the closure of the domain -/

/-- The forward chart is continuous at every free point other than the seed of the path. -/
theorem IsEntryData.continuousAt_fwd_of_isFreeAt (h : IsEntryData V T ξ p d) {z : ℂ} (hz : 0 ≤ z.im)
    (hzd : z ≠ d) (hf : IsFreeAt (entryPath ξ T d '' Icc 0 1) z) : ContinuousAt (entryChart V T d).1 z := by
  obtain ⟨u, hu⟩ := h.alive_of_isFreeAt hz hzd hf
  have h1 := continuousAt_fwdMap_of_alive h.tip.cont h.tip.pos.le hu
  have h2 : ContinuousAt (fun w : ℂ => w - (d : ℂ)) z := (continuous_id.sub continuous_const).continuousAt
  have h12 : ContinuousAt (fun w : ℂ => fwdMap V T (w - (d : ℂ))) z :=
    ContinuousAt.comp (f := fun w : ℂ => w - (d : ℂ)) (g := fwdMap V T) h1 h2
  exact h12.sub continuousAt_const

/-- **The forward chart has a limit along its domain at every point of the closure of the domain.** -/
theorem IsEntryData.exists_tendsto_fwd (h : IsEntryData V T ξ p d) {z : ℂ} (hz : z ∈ closure (entryDom ξ T d)) :
    ∃ w, Tendsto (entryChart V T d).1 (𝓝[entryDom ξ T d] z) (𝓝 w) := by
  set K := entryPath ξ T d '' Icc 0 1 with hK
  have hDc := h.isDomainChart'
  have hKc : IsCompact K := h.isCompact_path
  by_cases hzD : z ∈ entryDom ξ T d
  · exact ⟨_, (hDc.differentiableOn_fwd.continuousOn z hzD).tendsto⟩
  by_cases hzK : z ∈ K
  · -- a point of the path: one real preimage
    obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le h.tip.cont h.tip.zero h.tip.pos.le
    have hGM : ∀ z' ∈ entryDom ξ T d, ‖(entryChart V T d).1 z' - z'‖ ≤ C + |markPosL V T (-d)| + |d| := by
      intro z' hz'
      have hz'' : z' ∈ (fun w : ℂ => w + (d : ℂ)) '' (H \ fwdHull V T) := by
        have : z' ∈ H \ fillH (entryPath ξ T d '' Icc 0 1) := hz'
        rwa [h.fillH_entryPath, ← image_add_real_H_diff] at this
      obtain ⟨z₀, hz₀, rfl⟩ := hz''
      have h1 := hC z₀ hz₀
      rw [entryChart_fst, add_sub_cancel_right]
      have e : fwdMap V T z₀ - (markPosL V T (-d) : ℂ) - (z₀ + (d : ℂ)) =
          (fwdMap V T z₀ - z₀) - (markPosL V T (-d) : ℂ) - (d : ℂ) := by ring
      rw [e]
      calc ‖(fwdMap V T z₀ - z₀) - (markPosL V T (-d) : ℂ) - (d : ℂ)‖
          ≤ ‖(fwdMap V T z₀ - z₀) - (markPosL V T (-d) : ℂ)‖ + ‖(d : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖fwdMap V T z₀ - z₀‖ + ‖(markPosL V T (-d) : ℂ)‖ + ‖(d : ℂ)‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ C + |markPosL V T (-d)| + |d| := by
            rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
            linarith
    obtain ⟨x₀, -, hx₀⟩ := Restart.exists_tendsto_of_fibre (F := entryInv V T d)
      (G := (entryChart V T d).1) (D := entryDom ξ T d) h.continuousOn_entryInv
      (fun w hw => by rw [h.entryInv_eq_inv hw]; exact hDc.inv_mem hw)
      (fun z' hz' => ⟨hDc.fwd_mem hz', by rw [h.entryInv_eq_inv (hDc.fwd_mem hz')]; exact hDc.inv_fwd hz'⟩)
      hGM hz hzD (fun x y hx hy => h.fibre_eq hzK hx hy)
    exact ⟨_, hx₀⟩
  · -- a point of the closure off the domain and off the path is a free real point
    have hfr : z ∈ frontier (entryDom ξ T d) := by
      rw [hDc.isOpen.frontier_eq]; exact ⟨hz, hzD⟩
    have hzE := frontier_H_diff_fillH_subset hKc.isBounded hfr
    rw [hKc.isClosed.closure_eq] at hzE
    have him : z.im = 0 := hzE.resolve_right hzK
    have hfree : IsFreeAt K z := by
      rcases isFreeAt_or_isTrappedAt hKc.isClosed hzK with hf | ⟨ε, hε, hdisj⟩
      · exact hf
      · exfalso
        obtain ⟨w, hw, hwz⟩ := Metric.mem_closure_iff.1 hz ε hε
        exact Set.disjoint_left.1 hdisj (show w ∈ ball z ε by rw [mem_ball, dist_comm]; exact hwz) hw
    have hzd : z ≠ (d : ℂ) := fun he => hzK ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [h.entryPath_zero, he]⟩
    exact ⟨_, (h.continuousAt_fwd_of_isFreeAt him.ge hzd hfree).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- **The extended forward chart is continuous on the closure of the domain.** -/
theorem IsEntryData.continuousOn_entryExt (h : IsEntryData V T ξ p d) :
    ContinuousOn (entryExt V ξ T d) (closure (entryDom ξ T d)) :=
  continuousOn_extendFrom subset_rfl fun _ hz => h.exists_tendsto_fwd hz

theorem IsEntryData.tendsto_entryExt (h : IsEntryData V T ξ p d) {z : ℂ} (hz : z ∈ closure (entryDom ξ T d)) :
    Tendsto (entryChart V T d).1 (𝓝[entryDom ξ T d] z) (𝓝 (entryExt V ξ T d z)) :=
  tendsto_extendFrom (h.exists_tendsto_fwd hz)

/-- The extended forward chart takes values in the closed half-plane. -/
theorem IsEntryData.entryExt_mem_Hbar (h : IsEntryData V T ξ p d) {z : ℂ} (hz : z ∈ closure (entryDom ξ T d)) :
    0 ≤ (entryExt V ξ T d z).im := by
  have : (𝓝[entryDom ξ T d] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
  have hmem : entryExt V ξ T d z ∈ closure H := mem_closure_of_tendsto (h.tendsto_entryExt hz)
    (eventually_nhdsWithin_of_forall fun w hw => h.isDomainChart'.fwd_mem hw)
  rw [closure_H] at hmem
  exact hmem

/-- **The boundary inverse inverts the extended forward chart.** -/
theorem IsEntryData.entryInv_entryExt (h : IsEntryData V T ξ p d) {z : ℂ} (hz : z ∈ closure (entryDom ξ T d)) :
    entryInv V T d (entryExt V ξ T d z) = z := by
  have hne : (𝓝[entryDom ξ T d] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
  have hw := h.entryExt_mem_Hbar hz
  have hDc := h.isDomainChart'
  have hcw : ContinuousWithinAt (entryInv V T d) {w | 0 ≤ w.im} (entryExt V ξ T d z) :=
    h.continuousOn_entryInv _ hw
  have h1 : Tendsto (entryChart V T d).1 (𝓝[entryDom ξ T d] z) (𝓝[{w | 0 ≤ w.im}] (entryExt V ξ T d z)) :=
    tendsto_nhdsWithin_iff.2 ⟨h.tendsto_entryExt hz, eventually_nhdsWithin_of_forall fun w hw' =>
      show 0 ≤ ((entryChart V T d).1 w).im from le_of_lt (hDc.fwd_mem hw')⟩
  have h2 : Tendsto (fun w => entryInv V T d ((entryChart V T d).1 w)) (𝓝[entryDom ξ T d] z)
      (𝓝 (entryInv V T d (entryExt V ξ T d z))) := hcw.tendsto.comp h1
  have h3 : Tendsto (fun w => entryInv V T d ((entryChart V T d).1 w)) (𝓝[entryDom ξ T d] z) (𝓝 z) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw'
    rw [h.entryInv_eq_inv (hDc.fwd_mem hw'), hDc.inv_fwd hw']
    rfl
  exact tendsto_nhds_unique h2 h3

/-- At a free point other than the seed of the path the extension is the forward chart. -/
theorem IsEntryData.entryExt_of_isFreeAt (h : IsEntryData V T ξ p d) {z : ℂ} (hz : 0 ≤ z.im) (hzd : z ≠ d)
    (hf : IsFreeAt (entryPath ξ T d '' Icc 0 1) z) : entryExt V ξ T d z = (entryChart V T d).1 z :=
  extendFrom_eq (Supp9D.mem_closure_of_isFreeAt hf hz)
    ((h.continuousAt_fwd_of_isFreeAt hz hzd hf).tendsto.mono_left nhdsWithin_le_nhds)

theorem mem_closure_entryDom_of_isFreeAt {z : ℂ} (hz : 0 ≤ z.im)
    (hf : IsFreeAt (entryPath ξ T d '' Icc 0 1) z) : z ∈ closure (entryDom ξ T d) :=
  Supp9D.mem_closure_of_isFreeAt hf hz

/-- Negative real points are free for the path, hence in the closure of the domain. -/
theorem IsEntryData.isFreeAt_of_neg (h : IsEntryData V T ξ p d) {x : ℝ} (hx : x < 0) :
    IsFreeAt (entryPath ξ T d '' Icc 0 1) (x : ℂ) := by
  refine isFreeAt_of_notMem_closure fun hmem => ?_
  obtain ⟨_, ⟨s, hs, rfl⟩, him, hre⟩ :=
    Sec7.R6Fd.exists_real_le_of_mem_closure_fillH h.isCompact_path h.path_subset_Hbar hmem
  have hy : ((entryPath ξ T d s).re : ℂ) ∈ entryPath ξ T d '' Icc 0 1 :=
    ⟨s, hs, Complex.ext (by simp) (by simp [him])⟩
  have := h.real_entryPath_nonneg hy
  linarith

theorem IsEntryData.zero_mem_closure (h : IsEntryData V T ξ p d) : (0 : ℂ) ∈ closure (entryDom ξ T d) := by
  have h1 : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have hlim : Tendsto (fun n : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    have h0 : Tendsto (fun n : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h1
    rwa [ofReal_zero] at h0
  refine isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  have hneg : -(1 / ((n : ℝ) + 1)) < 0 := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact mem_closure_entryDom_of_isFreeAt (by rw [ofReal_im]) (h.isFreeAt_of_neg hneg)

/-- **The extended forward chart sends the explorer's seed to `0`.** -/
theorem IsEntryData.entryExt_zero (h : IsEntryData V T ξ p d) : entryExt V ξ T d 0 = 0 := by
  have hV := h.tip.cont
  have hV0 := h.tip.zero
  have hT := h.tip.pos.le
  have h0cl := h.zero_mem_closure
  -- the boundary values on the negative reals
  have hneg : ∀ x : ℝ, x < 0 → entryExt V ξ T d (x : ℂ) =
      (((fwdMap V T ((x - d : ℝ) : ℂ)).re - markPosL V T (-d) : ℝ) : ℂ) := by
    intro x hx
    have hfree := h.isFreeAt_of_neg hx
    have hne' : ((𝓝[H] (x : ℂ))).NeBot := neBot_nhdsWithin_H_of_im_nonneg (by rw [ofReal_im])
    have hxd : (x : ℂ) ≠ (d : ℂ) := fun he => by
      have : x = d := by exact_mod_cast he
      linarith [h.seed]
    rw [h.entryExt_of_isFreeAt (by rw [ofReal_im]) hxd hfree]
    have hc := h.continuousAt_fwd_of_isFreeAt (z := (x : ℂ)) (by rw [ofReal_im]) hxd hfree
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) (h.tendsto_fwd_real hx)
  -- along the negative reals the extension tends to `0`
  have hto : Tendsto (fun x : ℝ => entryExt V ξ T d (x : ℂ)) (𝓝[<] 0) (𝓝 (0 : ℂ)) := by
    have h1 := (Complex.continuous_ofReal.tendsto 0).comp h.tendsto_entry_zero
    rw [ofReal_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx using (hneg x hx).symm
  -- continuity of the extension on the closure
  have hcont := h.continuousOn_entryExt 0 h0cl
  have hreal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[<] 0) (𝓝[closure (entryDom ξ T d)] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x (hx : x < 0) =>
      mem_closure_entryDom_of_isFreeAt (by rw [ofReal_im]) (h.isFreeAt_of_neg hx)⟩
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    rwa [ofReal_zero] at this
  have hto' : Tendsto (fun x : ℝ => entryExt V ξ T d (x : ℂ)) (𝓝[<] 0) (𝓝 (entryExt V ξ T d 0)) :=
    hcont.tendsto.comp hreal
  exact tendsto_nhds_unique hto' hto

end Term

end InteractingSLE.RealContact
