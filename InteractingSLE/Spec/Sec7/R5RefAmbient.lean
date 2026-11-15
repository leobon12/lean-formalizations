/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5RefFamily
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Spec.ZhanGT4.CrosscutShift
import InteractingSLE.Spec.Restart.FCAux79MeanFlow
import InteractingSLE.Spec.Zhan.StripTailPullback
import InteractingSLE.Spec.Sec5.CfStepGeom
import InteractingSLE.Spec.Sec7.PocketSideInReachLocal
import InteractingSLE.Spec.Sec7.PocketSideInFiniteBound
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# Lemma R.5: the ambient chart at an old access (the geometric part of `R5Same.R7AmbientCover`)

Packet PROVE-R5-REFCHART. PROVE-R5-SAMETIME reads the heights of R.5's original-time references in the AMBIENT chart
`f_s` of the counterflow at the reference time `s` (`R5Same.ae_tendsto_harmRep_ref`); its cover `R7AmbientCover`
needs, at the selected reference, the physical landing `z₀` (a point of the counterflow hull inside the pocket), the
convergence of the ambient chart along the access to a real coordinate `x'`, and `x'` off the jumps of the ambient
force word. This file proves these pathwise:

* `rightImg_sub_mem_exteriorCoords`, `neg_rightImg_neg_sub_mem_exteriorCoords`: the centred geometric images of the
  force points (`MartChar.RealFlow.rightImg`, the infimum of the images of the alive points to the right) are exterior
  coordinates of the Loewner chain (`ZhanGT4.exteriorCoords`);
* **`notMem_forceJumpSet_of_extendFrom`**: a real coordinate at which the inverse extension of the ambient chart is a
  point of `ℍ` other than the tip is not a jump of the centred geometric force word (`F̄_s(0)` is the tip,
  `ZhanGT4.extendFrom_zero_eq`; `F̄_s` is real at exterior coordinates, `ZhanGT4.extendFrom_of_mem_exteriorCoords`);
* **`exists_ambient_access`**: along an old access `old⁻¹ → p` from a real `x`, with `p` in the hull `K_s`, the ambient
  chart `f_s ∘ old⁻¹` converges to a real `x'` with `F̄_s(x') = p` (the bounded-composition limit
  `PocketStopSide.exists_tendsto_of_tendsto_comp_local`, as in POCKET-SIDEIN's transition limits);
* **`exists_ambient_cover`**, **`exists_ambient_coverInf`** (R.7 tests): every real current coordinate whose landing is
  a point of the pocket off `refExc` has a reference of the family `refEvent`/`refChart` with an unfilled collar, the
  landing `z₀ ∈ C ∩ refHull W' ζ' i`, the current approach in the reference complement, and the ambient image `x'`
  (along both the current and the old approach) off the ambient jumps of the coupling's force processes — every
  conjunct of `R5Same.R7AmbientCover` except the lift-difference limit and the word identity (PROVE-R5-LIFT);
* `ae_exists_ambient_cover(Inf)`: the same almost surely, from the coupling's path property.

**Wall landings.** `R7AmbientCover` asks for `z₀ ∈ C ω` at EVERY non-exceptional coordinate; a landing on an unvisited
side of the pocket (a point of `∂C`, never in `C`) has no such `z₀`, and every live current domain has such boundary
points, so the hypothesis "the landing lies in `C`" here is exactly the hull case; see the handoff.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Ref

open ZhanGT4 MartChar.RealFlow

/-! ### Exterior coordinates of the force points -/

section Exterior

variable {w : ℝ → ℝ}

/-- **A centred geometric right image is an exterior coordinate.** -/
theorem rightImg_sub_mem_exteriorCoords (hw : Continuous w) (hw0 : w 0 = 0) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    rightImg w x t - w t ∈ exteriorCoords w t := by
  have hmem : rightImg w x t ∈ closure (imgSet w x t) :=
    csInf_mem_closure (imgSet_nonempty hw x ht) (imgSet_bddBelow hw x ht)
  have hsub : (fun g => g - w t) '' imgSet w x t ⊆
      {r : ℝ | ∃ y : ℝ, (∃ v, IsForwardSol w (y : ℂ) t v) ∧ (fwdMap w t y).re = r} := by
    rintro _ ⟨g, ⟨y, -, hal, rfl⟩, rfl⟩
    obtain ⟨u, hu, hut⟩ := Restart.FCAux79.exists_isForwardSol_of_alive hw hw0 ht hal
    exact ⟨y, ⟨u, hu⟩, by rw [Zhan.fwdMap_ofReal_eq hw ht hu, hut, ofReal_re]⟩
  exact closure_mono hsub (image_closure_subset_closure_image (continuous_sub_right (w t)) ⟨_, hmem, rfl⟩)

/-- **A centred geometric left image is an exterior coordinate** (by reflection). -/
theorem neg_rightImg_neg_sub_mem_exteriorCoords (hw : Continuous w) (hw0 : w 0 = 0) (x : ℝ) {t : ℝ}
    (ht : 0 ≤ t) : -rightImg (fun s => -w s) (-x) t - w t ∈ exteriorCoords w t := by
  have hwn : Continuous fun s => -w s := hw.neg
  have hwn0 : (fun s => -w s) 0 = 0 := by simp only [hw0, neg_zero]
  have h : rightImg (fun s => -w s) (-x) t - -w t ∈ exteriorCoords (fun s => -w s) t :=
    rightImg_sub_mem_exteriorCoords hwn hwn0 (-x) ht
  have h2 := (mem_exteriorCoords_neg_iff hw ht).1 h
  have e : -(rightImg (fun s => -w s) (-x) t - -w t) = -rightImg (fun s => -w s) (-x) t - w t := by ring
  rwa [e] at h2

/-- **Off the jumps of the centred geometric force word**: a real coordinate at which the inverse extension of the
ambient chart is a point of `ℍ` other than the tip is neither `0` (the tip's coordinate) nor a force point image (an
exterior coordinate, where the extension is real). -/
theorem notMem_forceJumpSet_of_extendFrom {η : ℝ → ℂ} (hη : IsLoewnerTrace w η) (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {v : ℝ} {p : ℂ}
    (hvp : extendFrom H (fwdMapInv w t) (v : ℂ) = p) (hpH : p ∈ H) (hptip : p ≠ η t) :
    v ∉ forceJumpSet (fun i => -rightImg (fun s => -w s) (-xL i) t - w t) (fun j => rightImg w (xR j) t - w t) := by
  intro hv
  simp only [forceJumpSet, Set.mem_insert_iff, Set.mem_union, Set.mem_range] at hv
  have hreal : ∀ u ∈ exteriorCoords w t, extendFrom H (fwdMapInv w t) (u : ℂ) ≠ p := fun u hu h => by
    have him := (extendFrom_of_mem_exteriorCoords hη hw hw0 ht hu).1
    rw [h] at him
    exact (show (0 : ℝ) < p.im from hpH).ne' him
  rcases hv with h0 | ⟨i, hi⟩ | ⟨j, hj⟩
  · apply hptip
    rw [← hvp, h0, ofReal_zero, extendFrom_zero_eq hη hw hw0 ht]
  · exact hreal _ (neg_rightImg_neg_sub_mem_exteriorCoords hw hw0 (xL i) ht) (hi ▸ hvp)
  · exact hreal _ (rightImg_sub_mem_exteriorCoords hw hw0 (xR j) ht) (hj ▸ hvp)

end Exterior

/-! ### The ambient chart along an old access -/

section Access

variable {w : ℝ → ℝ}

/-- **The ambient chart converges along an old access to a hull point**: if a conformal chart `old` has its domain in
the complement of `K_s` and its inverse lands at `p ∈ K_s` from the real coordinate `x`, then `f_s ∘ old⁻¹` converges
to a real `x'` with `F̄_s(x') = p`. -/
theorem exists_ambient_access {η : ℝ → ℂ} (hη : IsLoewnerTrace w η) (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) {old : Chart} (hOld : old.IsConformal) (hOldDom : (old.dom : Set ℂ) ⊆ H \ fwdHull w s)
    {x : ℝ} {p : ℂ} (hLanding : Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) (hpK : p ∈ fwdHull w s) :
    ∃ x' : ℝ, extendFrom H (fwdMapInv w s) (x' : ℂ) = p ∧
      Tendsto (fun z => fwdMap w s (old.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  set F := extendFrom H (fwdMapInv w s) with hFdef
  have hFeq : EqOn F (fwdMapInv w s) H := fun z hz => extendFrom_eq_fwdMapInv hw hw0 hs hz
  have hB := isBoundaryMap_extendFrom hη hw hw0 hs
  have hd : DifferentiableOn ℂ F H :=
    (isConformalBijection_fwdMapInv hw hw0 hs).1.congr fun z hz => hFeq hz
  have hR : ∀ z : ℂ, z.im = 0 → F z ∉ F '' H := by
    intro z hz
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
    rw [hz']
    exact extendFrom_not_mem_image hη hw hw0 hs le_rfl z.re
  have hmaps : ∀ z ∈ H, old.2.1 z ∈ H \ fwdHull w s := fun z hz => hOldDom (hOld.inv_mem_dom hz)
  have hGc : ContinuousOn (fun z => fwdMap w s (old.2.1 z)) (H ∩ ball (x : ℂ) 1) :=
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hw hs).continuousOn.comp hOld.1.continuousOn
      fun z hz => hmaps z hz).mono inter_subset_left
  have hGH : MapsTo (fun z => fwdMap w s (old.2.1 z)) (H ∩ ball (x : ℂ) 1) Hbar := fun z hz =>
    QuantumZipper.H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hmaps z hz.1))
  have hbd : ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (x : ℂ), ‖old.2.1 z‖ ≤ M := by
    refine ⟨‖p‖ + 1, ?_⟩
    filter_upwards [hLanding.eventually (ball_mem_nhds p one_pos)] with z hz
    have hn := norm_sub_norm_le (old.2.1 z) p
    rw [dist_eq_norm] at hz
    linarith
  obtain ⟨M, hM⟩ := PocketStopSide.eventually_norm_bounded_loewner_comp hw hw0 hs
    (eventually_nhdsWithin_of_forall fun z hz => hmaps z hz) hbd
  have hFG : Tendsto (fun z => F (fwdMap w s (old.2.1 z))) (𝓝[H] (x : ℂ)) (𝓝 p) :=
    hLanding.congr' (eventually_nhdsWithin_of_forall fun z hz => by
      show old.2.1 z = F (fwdMap w s (old.2.1 z))
      rw [hFeq (QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hmaps z hz)),
        QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hs (hmaps z hz)])
  obtain ⟨y, hy, hFy, hlim⟩ :=
    PocketStopSide.exists_tendsto_of_tendsto_comp_local hd hB.cont hB.inj hR one_pos hGc hGH hM hFG
  have hy0 : y.im = 0 := by
    rcases (show 0 ≤ y.im from hy).lt_or_eq with hpos | h
    · exfalso
      have hyH : y ∈ H := hpos
      have hc := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 hs hyH
      rw [← hFeq hyH, hFy] at hc
      exact hc.2 hpK
    · exact h.symm
  have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [hy0])
  refine ⟨y.re, ?_, ?_⟩
  · rw [← hyr]
    exact hFy
  · rwa [← hyr]

end Access

/-! ### The geometric part of `R5Same.R7AmbientCover` on an R.7 test -/

section Bounded

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
  {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **The geometric part of R.5's ambient cover, pathwise** (bounded change pocket): for a real current coordinate `ξ`
whose landing `p` is a point of the pocket off `refExc`, a reference `i` of the family (an interior visit before
`T⁰(q)`), an unfilled collar at `ξ`, `p ∈ C ∩ refHull W' ζ' i`, the current approach in the reference complement, and
a real ambient coordinate `x'` off the jumps of the ambient force word, reached by `f_s` along the current and along
the old approach. The force processes are the geometric images of the marks (`hVL`, `hVR`). -/
theorem exists_ambient_cover {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζ : ζ' ω = ⊤) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, VL i t ω = -rightImg (fun s : ℝ => -W' s.toNNReal ω) (-xL i) t)
    (hVR : ∀ j t, VR j t ω = rightImg (fun s : ℝ => W' s.toNNReal ω) (xR j) t)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω)
    (hC : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r) :
    ∃ (i : ℕ) (x ε x' : ℝ),
      ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
      IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω ∧
      Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
        H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) ∧
      x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
        (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((refChart c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨hLanding, -, -⟩ :=
    current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq ξ
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h | h
    · exfalso
      subst h
      apply inverse_real_landing_notMem_dom hNow hLanding
      show _ ∈ ((relChart c (travAll R L r η ψ) 0 ω).dom : Set ℂ)
      rw [relChart_zero_dom (c := c) (γ := travAll R L r η ψ) hγ, hdom]
      exact hC
    · exact h
  simp only [refExc, mem_insert_iff, mem_singleton_iff, not_or] at hX
  obtain ⟨s, hs0, hv, hQ, hne, x, ε, hcol⟩ :=
    exists_visit_collar (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq0 hq ξ hX.1 hX.2
  set i := Denumerable.eqv ℚ s with hi
  set t := rationalOriginalTime i with htdef
  have hti : (t : ℝ) = s := coe_rationalOriginalTime_eqv hs0
  have hv' : η ω t ∈ cfPocket (R ω) (L ω) r := by rw [hti]; exact hv
  have hQ' : (visitCap R L r η ψ ω t).toNNReal ≤ q := by rw [hti]; exact hQ
  have hne' : η ω t ≠ extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ := by rw [hti]; exact hne
  have hcol' : IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
      (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
    simp only [refChart, htdef ▸ hti]
    exact hcol
  have hHull : refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    refHull_eq_of_continuous hcfg.continuous_W hζ i
  obtain ⟨hOld0, hIncl0, hOldLive⟩ :=
    reference_chart_at_visit (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hv' hHull hq hQ'
  have hOld : (refChart c R L r η ψ i ω).IsConformal := hOld0
  have hIncl : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ (refChart c R L r η ψ i ω).dom := hIncl0
  obtain ⟨-, -, hOldDom⟩ :=
    visit_chart (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq t.coe_nonneg hv'
  have hfill := hcfg.trace.2.2 t t.coe_nonneg
  have hOldDom' : ((refChart c R L r η ψ i ω).dom : Set ℂ) ⊆ H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
    change ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω t).toNNReal ω).dom : Set ℂ) ⊆ _
    rw [hOldDom, hfill]
    exact fun z hz => hz.2
  have hpK : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈
      fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
    by_contra hK
    apply hcol'.notMem_dom hOld
    change _ ∈ ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω t).toNNReal ω).dom : Set ℂ)
    rw [hOldDom, ← hfill]
    exact ⟨hC, hCH hC, hK⟩
  obtain ⟨x', hx'p, hlimOld⟩ := exists_ambient_access hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg hOld
    hOldDom' (tendsto_nhdsWithin_iff.1 hcol'.2.2.2.1).1 hpK
  have hlimCur : Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) t
      ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr : Tendsto (fun y => (refChart c R L r η ψ i ω).1 ((relChart c (travAll R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcol'.2.2.1, eventually_nhdsWithin_of_forall fun y hy =>
        hOld.fwd_mem (hIncl (hNow.inv_mem_dom hy))⟩
    refine (hlimOld.comp htr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    show fwdMap _ t ((refChart c R L r η ψ i ω).2.1 ((refChart c R L r η ψ i ω).1
      ((relChart c (travAll R L r η ψ) q ω).2.1 y))) = fwdMap _ t ((relChart c (travAll R L r η ψ) q ω).2.1 y)
    rw [hOld.inv_fwd (hIncl (hNow.inv_mem_dom hy))]
  have hjump := notMem_forceJumpSet_of_extendFrom hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg xL xR
    hx'p (hCH hC) (Ne.symm hne')
  have hWt : W' t ω = (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by simp only [Real.toNNReal_coe]
  have hJL : (fun j => VL j t ω - W' t ω) =
      fun j => -rightImg (fun s : ℝ => -(fun s : ℝ => W' s.toNNReal ω) s) (-xL j) (t : ℝ) -
        (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVL j t, hWt]
  have hJR : (fun j => VR j t ω - W' t ω) =
      fun j => rightImg (fun s : ℝ => W' s.toNNReal ω) (xR j) (t : ℝ) - (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVR j t, hWt]
  refine ⟨i, x, ε, x', ⟨hω, hq, Or.inl hv', hQ', hHull⟩, hv', hcol', ⟨hC, hHull ▸ hpK⟩, hLanding,
    eventually_nhdsWithin_of_forall fun y hy => hOldLive ▸ hIncl (hNow.inv_mem_dom hy), ?_, hlimCur, hlimOld⟩
  rw [hJL, hJR]
  exact hjump

/-- **The geometric part of R.5's ambient cover** (bounded change pocket), almost surely: the force processes are the
geometric images of the marks on the coupling's paths (`CfStep.force_eq_geom_of_path_top`). -/
theorem ae_exists_ambient_cover [MeasurableSpace Ω] {P : Measure Ω} {α : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL xR ρL ρR (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∀ ξ : ℝ,
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω →
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
      ∃ (i : ℕ) (x ε x' : ℝ),
        ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
        IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε ∧
        extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω ∧
        Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
          (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) ∧
        (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
          H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) ∧
        x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
          (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
          ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
          ((refChart c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  filter_upwards [hpath] with ω hp hω hq ξ hX hC
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h := (hcfg ω hω).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp (hζ ω hω) hV fun _ => rfl
  exact exists_ambient_cover hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hζ ω hω)
    (fun i t => hL i t) (fun j t => hR j t) hq ξ hX hC

end Bounded

section Inf

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
  {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **The geometric part of R.5's ambient cover, pathwise** (change pocket opening at the flow seed): as
`exists_ambient_cover`, with the exceptional set `refExcInf` (the current tip only). -/
theorem exists_ambient_coverInf {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζ : ζ' ω = ⊤) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, VL i t ω = -rightImg (fun s : ℝ => -W' s.toNNReal ω) (-xL i) t)
    (hVR : ∀ j t, VR j t ω = rightImg (fun s : ℝ => W' s.toNNReal ω) (xR j) t)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω)
    (hC : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r) :
    ∃ (i : ℕ) (x ε x' : ℝ),
      ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω ∧
      Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
        H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) ∧
      x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
        (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((refChartInf c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨hLanding, -, -⟩ :=
    current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq ξ
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h | h
    · exfalso
      subst h
      apply inverse_real_landing_notMem_dom hNow hLanding
      show _ ∈ ((relChart c (travAllInf R L r η ψ) 0 ω).dom : Set ℂ)
      rw [relChart_zero_dom (c := c) (γ := travAllInf R L r η ψ) hγ, hdom]
      exact hC
    · exact h
  simp only [refExcInf, mem_singleton_iff] at hX
  obtain ⟨s, hs0, hv, hQ, hne, x, ε, hcol⟩ :=
    exists_visit_collarInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq0 hq ξ hX
  set i := Denumerable.eqv ℚ s with hi
  set t := rationalOriginalTime i with htdef
  have hti : (t : ℝ) = s := coe_rationalOriginalTime_eqv hs0
  have hv' : η ω t ∈ cfPocket (R ω) (L ω) r := by rw [hti]; exact hv
  have hQ' : (visitCapInf R L r η ψ ω t).toNNReal ≤ q := by rw [hti]; exact hQ
  have hne' : η ω t ≠ extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ := by rw [hti]; exact hne
  have hcol' : IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
      (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
    simp only [refChartInf, htdef ▸ hti]
    exact hcol
  have hHull : refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    refHull_eq_of_continuous hcfg.continuous_W hζ i
  obtain ⟨hOld0, hIncl0, hOldLive⟩ :=
    reference_chart_at_visitInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hv' hHull hq hQ'
  have hOld : (refChartInf c R L r η ψ i ω).IsConformal := hOld0
  have hIncl : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ (refChartInf c R L r η ψ i ω).dom := hIncl0
  obtain ⟨-, -, hOldDom⟩ :=
    visit_chartInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq t.coe_nonneg hv'
  have hfill := hcfg.trace.2.2 t t.coe_nonneg
  have hOldDom' : ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ⊆ H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
    change ((relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω t).toNNReal ω).dom : Set ℂ) ⊆ _
    rw [hOldDom, hfill]
    exact fun z hz => hz.2
  have hpK : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈
      fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
    by_contra hK
    apply hcol'.notMem_dom hOld
    change _ ∈ ((relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω t).toNNReal ω).dom : Set ℂ)
    rw [hOldDom, ← hfill]
    exact ⟨hC, hCH hC, hK⟩
  obtain ⟨x', hx'p, hlimOld⟩ := exists_ambient_access hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg hOld
    hOldDom' (tendsto_nhdsWithin_iff.1 hcol'.2.2.2.1).1 hpK
  have hlimCur : Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) t
      ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr : Tendsto (fun y => (refChartInf c R L r η ψ i ω).1 ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcol'.2.2.1, eventually_nhdsWithin_of_forall fun y hy =>
        hOld.fwd_mem (hIncl (hNow.inv_mem_dom hy))⟩
    refine (hlimOld.comp htr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    show fwdMap _ t ((refChartInf c R L r η ψ i ω).2.1 ((refChartInf c R L r η ψ i ω).1
      ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))) = fwdMap _ t ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)
    rw [hOld.inv_fwd (hIncl (hNow.inv_mem_dom hy))]
  have hjump := notMem_forceJumpSet_of_extendFrom hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg xL xR
    hx'p (hCH hC) (Ne.symm hne')
  have hWt : W' t ω = (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by simp only [Real.toNNReal_coe]
  have hJL : (fun j => VL j t ω - W' t ω) =
      fun j => -rightImg (fun s : ℝ => -(fun s : ℝ => W' s.toNNReal ω) s) (-xL j) (t : ℝ) -
        (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVL j t, hWt]
  have hJR : (fun j => VR j t ω - W' t ω) =
      fun j => rightImg (fun s : ℝ => W' s.toNNReal ω) (xR j) (t : ℝ) - (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVR j t, hWt]
  refine ⟨i, x, ε, x', ⟨hω, hq, Or.inl hv', hQ', hHull⟩, hv', hcol', ⟨hC, hHull ▸ hpK⟩, hLanding,
    eventually_nhdsWithin_of_forall fun y hy => hOldLive ▸ hIncl (hNow.inv_mem_dom hy), ?_, hlimCur, hlimOld⟩
  rw [hJL, hJR]
  exact hjump

/-- **The geometric part of R.5's ambient cover** (change pocket opening at the flow seed), almost surely: the force
    processes are the
geometric images of the marks on the coupling's paths (`CfStep.force_eq_geom_of_path_top`). -/
theorem ae_exists_ambient_coverInf [MeasurableSpace Ω] {P : Measure Ω} {α : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL xR ρL ρR (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ,
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω →
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
      ∃ (i : ℕ) (x ε x' : ℝ),
        ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
        IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε ∧
        extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω ∧
        Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
          (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) ∧
        (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
          H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) ∧
        x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
          (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
          ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
          ((refChartInf c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  filter_upwards [hpath] with ω hp hω hq ξ hX hC
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h := (hcfg ω hω).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp (hζ ω hω) hV fun _ => rfl
  exact exists_ambient_coverInf hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hζ ω hω)
    (fun i t => hL i t) (fun j t => hR j t) hq ξ hX hC

end Inf

end InteractingSLE.Sec7.R5Ref
