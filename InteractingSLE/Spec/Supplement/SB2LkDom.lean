/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYHull
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Foundations.Loewner.YuanCharacterisationLimit

/-!
# The hull of a piece at its lifetime is the filling of its closed trace

Packet PROVE-T14-SB2LIFT (round 6; the run-chart domain identity of handoff §R5.2, step (i-a)). A frozen walk run
stops every finite piece at its lifetime `T` and maps out the Loewner hull `K_T` of the stopped driver. The library
identifies `K_t` with the filling of the trace only strictly before the horizon of a generating trace
(`Sec7.fwdHull_eq_fillH_of_isGeneratingTrace`, from `IsGeneratingTrace`'s `IsFilling` clause). At the horizon itself,
capacity continuity gives `K_T = fill(⋃_{s<T} K_s)` (`Restart.FlowStopIdentCMI.fwdHull_eq_fillH_iUnion`). This file
closes the gap:

* `fillH_fillH_subset`: `fill(fill A) ⊆ fill A` for compact `A`;
* **`fwdHull_eq_fillH_horizon`**: for a continuous driver `w` from `0` and a generating trace `α` on `[0, T]` (finite
  `T`, continuous up to `T`), `K_T = fill(α([0, T]))`;
* `isOpen_image_of_injOn` (open mapping on `ℍ`), `ext_notMem_image` (boundary values of a conformal map of `ℍ` lie
  outside its image) and **`image_H_diff_fillH_of_chart`**: if `g` is holomorphic and injective on `ℍ` with image
  `ℍ \ fill P` (`P` compact), and `ĝ` is a continuous extension to `ℍ̄` within bounded distance of the identity, then
  `g(ℍ \ fill A) = ℍ \ fill(P ∪ ĝ(A))` for every compact `A ⊆ ℍ̄`. This is the step of the run-chart domain identity
  at a launch, with `A` the closed trace in the launch chart and `ĝ(A)` the new physical piece.

Together with the real-point aliveness criterion of the library (`y ∉ closure K_T` iff `y` is alive at `T`,
`notMem_closure_fwdHull_of_isForwardSol` and `exists_isForwardSol_of_notMem_closure`), this gives the stage's hits
and records at the lifetime without GW1's exit classification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Lk

/-- **Filling is idempotent on compact sets** (one inclusion). -/
theorem fillH_fillH_subset {A : Set ℂ} (hA : IsCompact A) : fillH (fillH A) ⊆ fillH A := by
  intro z hz
  by_contra hzA
  have hzX : z ∈ H \ fillH A := ⟨fillH_subset_H _ hz, hzA⟩
  have hopen : IsOpen (H \ fillH A) := isOpen_H_diff_fillH hA.isBounded
  have hXsub : H \ fillH A ⊆ H \ closure (fillH A) := fun w hw => by
    refine ⟨hw.1, fun hwc => ?_⟩
    obtain ⟨y, hy₁, hy₂⟩ := mem_closure_iff.1 hwc _ hopen hw
    exact hy₁.2 hy₂
  have h := HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded isClosed_closure
    (HalfPlaneSep.isPreconnected_H_diff_fillH hA.isClosed hA.isBounded)
    (HalfPlaneSep.not_isBounded_H_diff_fillH hA.isClosed hA.isBounded) hXsub hzX
  have hcl : fillH (closure (fillH A)) = fillH (fillH A) := fillH_congr (by rw [closure_closure])
  rw [hcl] at h
  exact h.2 hz

/-- The approximating times `T (1 − 1/(n+1))` of the horizon. -/
def horizonSeq (T : ℝ≥0) (n : ℕ) : ℝ≥0 := ((T : ℝ) * (1 - 1 / ((n : ℝ) + 1))).toNNReal

theorem horizonSeq_lt {T : ℝ≥0} (hT : 0 < T) (n : ℕ) : horizonSeq T n < T := by
  have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
  have hT' : (0 : ℝ) < T := hT
  rw [horizonSeq, ← NNReal.coe_lt_coe, Real.coe_toNNReal']
  refine max_lt (by nlinarith) hT'

theorem tendsto_horizonSeq_nnreal (T : ℝ≥0) : Tendsto (horizonSeq T) atTop (𝓝 T) := by
  have h : Tendsto (fun n : ℕ => (T : ℝ) * (1 - 1 / ((n : ℝ) + 1))) atTop (𝓝 ((T : ℝ) * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat)
  rw [sub_zero, mul_one] at h
  have h2 := (continuous_real_toNNReal.tendsto _).comp h
  rwa [Real.toNNReal_coe] at h2

theorem tendsto_horizonSeq (T : ℝ≥0) :
    Tendsto (fun n => (horizonSeq T n : ℝ≥0∞)) atTop (𝓝 (T : ℝ≥0∞)) :=
  (ENNReal.continuous_coe.tendsto T).comp (tendsto_horizonSeq_nnreal T)

/-- **The hull of a piece at its lifetime** is the filling of its closed trace. -/
theorem fwdHull_eq_fillH_horizon {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {T : ℝ≥0}
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w T α) :
    fwdHull (fun s : ℝ => w s.toNNReal) T = fillH (α '' Icc 0 T) := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hwc.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp only [hWdef, Real.toNNReal_zero, hw0]
  have hAc : IsCompact (α '' Icc 0 T) := isCompact_Icc.image_of_continuousOn
    (hα.2.1.mono fun r hr => ENNReal.coe_le_coe.2 hr.2)
  rcases eq_zero_or_pos T with hT0 | hTpos
  · subst hT0
    rw [show ((0 : ℝ≥0) : ℝ) = 0 from rfl, QuantumZipper.RS.fwdHull_zero_eq_empty hW]
    refine (YuanCharacterisation.fillH_eq_empty_of_subset ?_).symm
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    rw [hr0, hα.1]
    simp
  · set s := horizonSeq T with hsdef
    have hslt : ∀ n, s n < T := horizonSeq_lt hTpos
    have hK : fwdHull W T = fillH (⋃ n, fwdHull W (s n)) :=
      Restart.FlowStopIdentCMI.fwdHull_eq_fillH_iUnion hW hW0 (fun n => (hslt n).le) (tendsto_horizonSeq T)
    have hKn : ∀ n, fwdHull W (s n) = fillH (α '' Icc 0 (s n)) := fun n =>
      Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hα (ENNReal.coe_lt_coe.2 (hslt n))
    simp only [hKn] at hK
    rw [hK]
    set B := ⋃ n, fillH (α '' Icc 0 (s n)) with hB
    apply Subset.antisymm
    · -- `B ⊆ fill A`, and filling is idempotent
      have hBA : B ⊆ fillH (α '' Icc 0 T) := iUnion_subset fun n =>
        fillH_mono (image_mono (Icc_subset_Icc le_rfl (hslt n).le))
      exact (fillH_mono hBA).trans (fillH_fillH_subset hAc)
    · -- the unbounded domain of `B` avoids the closed trace
      have hApc : IsPreconnected (α '' Icc 0 T ∪ {z : ℂ | z.im ≤ 0}) := by
        refine (isPreconnected_Icc.image _ (hα.2.1.mono fun r hr => ENNReal.coe_le_coe.2 hr.2)).union (0 : ℂ)
          ⟨0, ⟨le_rfl, zero_le⟩, hα.1⟩ (by simp) isPreconnected_lowerHalf
      have hfAb : Bornology.IsBounded (fillH (α '' Icc 0 T)) :=
        (isHPHull_fillH_of_isPreconnected hAc.isBounded hApc).2.1
      have hBb : Bornology.IsBounded B := hfAb.subset (iUnion_subset fun n =>
        fillH_mono (image_mono (Icc_subset_Icc le_rfl (hslt n).le)))
      -- every point of the closed trace in `ℍ` is in the closure of `B`
      have hcl : ∀ t ∈ Icc (0 : ℝ≥0) T, α t ∈ H → α t ∈ closure B := by
        intro t ht hH
        have hr : Tendsto (fun n => min t (s n)) atTop (𝓝 t) := by
          have h1 : Tendsto (fun x : ℝ≥0 => min t x) (𝓝 T) (𝓝 (min t T)) :=
            (continuous_const.min continuous_id).tendsto T
          rw [min_eq_left ht.2] at h1
          exact h1.comp (tendsto_horizonSeq_nnreal T)
        have hrS : ∀ n, ((min t (s n) : ℝ≥0) : ℝ≥0∞) ≤ T := fun n =>
          ENNReal.coe_le_coe.2 ((min_le_right _ _).trans (hslt n).le)
        have hαc : ContinuousWithinAt α {r : ℝ≥0 | (r : ℝ≥0∞) ≤ T} t :=
          hα.2.1 t (ENNReal.coe_le_coe.2 ht.2)
        have hlim : Tendsto (fun n => α (min t (s n))) atTop (𝓝 (α t)) :=
          hαc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hr, Eventually.of_forall hrS⟩)
        refine mem_closure_of_tendsto hlim ?_
        filter_upwards [hlim (QuantumZipper.isOpen_H.mem_nhds hH)] with n hn
        refine mem_iUnion.2 ⟨n, mem_fillH_of_mem_closure hn (subset_closure ⟨_, ⟨zero_le, min_le_right _ _⟩, rfl⟩)⟩
      have hX : H \ fillH B ⊆ H \ fillH (α '' Icc 0 T) := by
        have hcB : fillH (closure B) = fillH B := fillH_congr (by rw [closure_closure])
        refine HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hAc.isClosed ?_ ?_ ?_
        · rw [← hcB]
          exact HalfPlaneSep.isPreconnected_H_diff_fillH isClosed_closure hBb.closure
        · rw [← hcB]
          exact HalfPlaneSep.not_isBounded_H_diff_fillH isClosed_closure hBb.closure
        · rintro z ⟨hzH, hzB⟩
          refine ⟨hzH, ?_⟩
          rintro ⟨t, ht, rfl⟩
          exact hzB (mem_fillH_of_mem_closure hzH (hcl t ht hzH))
      intro z hz
      by_contra hzB
      exact (hX ⟨fillH_subset_H _ hz, hzB⟩).2 hz

/-! ### The domain of a composed chart -/

section Chart

variable {g ĝ : ℂ → ℂ} {P A : Set ℂ}

theorem isPreconnected_H : IsPreconnected H :=
  (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected

/-- **Open mapping on `ℍ`**: a holomorphic map injective on `ℍ` maps open subsets of `ℍ` to open sets. -/
theorem isOpen_image_of_injOn (hg : DifferentiableOn ℂ g H) (hinj : InjOn g H) {U : Set ℂ} (hU : IsOpen U)
    (hUH : U ⊆ H) : IsOpen (g '' U) := by
  rcases (hg.analyticOnNhd QuantumZipper.isOpen_H).is_constant_or_isOpen isPreconnected_H with ⟨w, hw⟩ | h
  · exfalso
    have h1 : Complex.I ∈ H := show (0 : ℝ) < Complex.I.im by simp
    have h2 : (2 * Complex.I) ∈ H := show (0 : ℝ) < (2 * Complex.I).im by simp
    have he := hinj h1 h2 ((hw _ h1).trans (hw _ h2).symm)
    have := congrArg Complex.im he
    simp at this
  · exact h U hUH hU

/-- **Boundary values of a conformal map of `ℍ` lie outside its image.** -/
theorem ext_notMem_image (hg : DifferentiableOn ℂ g H) (hinj : InjOn g H) (hĝ : ContinuousOn ĝ Hbar)
    (hgg : EqOn ĝ g H) {a : ℂ} (ha : a ∈ Hbar) (haH : a ∉ H) : ĝ a ∉ g '' H := by
  rintro ⟨w, hw, hwa⟩
  have hw' : 0 < w.im := hw
  set r := w.im / 2 with hr
  have hr0 : 0 < r := by positivity
  have hV : Metric.ball w r ⊆ H := fun z hz => by
    have h1 := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im, ← dist_eq_norm] at h1
    have h2 : dist z w < r := hz
    show 0 < z.im
    have := abs_lt.1 (lt_of_le_of_lt h1 h2)
    linarith [this.1]
  have hVo := isOpen_image_of_injOn hg hinj Metric.isOpen_ball hV
  have hmem : ĝ a ∈ g '' Metric.ball w r := ⟨w, Metric.mem_ball_self hr0, hwa⟩
  have hev : ∀ᶠ z in 𝓝[H] a, z ∈ Metric.ball w r := by
    have h1 : ∀ᶠ z in 𝓝[Hbar] a, ĝ z ∈ g '' Metric.ball w r := (hĝ a ha) (hVo.mem_nhds hmem)
    have h2 : ∀ᶠ z in 𝓝[H] a, ĝ z ∈ g '' Metric.ball w r :=
      nhdsWithin_mono a QuantumZipper.H_subset_Hbar h1
    filter_upwards [h2, self_mem_nhdsWithin] with z hz hzH
    obtain ⟨v, hv, hgv⟩ := hz
    rw [hgg hzH] at hgv
    rw [← hinj (hV hv) hzH hgv]
    exact hv
  have hne : (𝓝[H] a).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact ha
  have hcl : a ∈ closure (Metric.ball w r) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hU' : ∀ᶠ z in 𝓝[H] a, z ∈ U := mem_nhdsWithin_of_mem_nhds hU
    obtain ⟨z, hzU, hz⟩ := (hU'.and hev).exists
    exact ⟨z, hzU, hz⟩
  have hdist : dist a w ≤ r := Metric.closure_ball_subset_closedBall hcl
  have h1 := Complex.abs_im_le_norm (a - w)
  rw [Complex.sub_im, ← dist_eq_norm] at h1
  have h3 := abs_le.1 (h1.trans hdist)
  exact haH (show 0 < a.im by linarith [h3.1])

/-- **The domain of a composed chart** (deterministic). Let `g` be holomorphic and injective on `ℍ` with image
`ℍ \ fill P` (`P` compact), and let `ĝ` be a continuous extension to `ℍ̄` within bounded distance of the identity.
Then for every compact `A ⊆ ℍ̄`, `g` maps `ℍ \ fill A` onto `ℍ \ fill (P ∪ ĝ(A))`. -/
theorem image_H_diff_fillH_of_chart (hg : DifferentiableOn ℂ g H) (hinj : InjOn g H) (hĝ : ContinuousOn ĝ Hbar)
    (hgg : EqOn ĝ g H) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C) (hP : IsCompact P) (hD : g '' H = H \ fillH P)
    (hA : IsCompact A) (hAH : A ⊆ Hbar) : g '' (H \ fillH A) = H \ fillH (P ∪ ĝ '' A) := by
  have hgA : IsCompact (ĝ '' A) := hA.image_of_continuousOn (hĝ.mono hAH)
  have hF : IsCompact (P ∪ ĝ '' A) := hP.union hgA
  have hPH : ∀ y, y ∈ H \ fillH P → y ∉ P := fun y hy hyP =>
    hy.2 (mem_fillH_of_mem_closure hy.1 (subset_closure hyP))
  have hnorm : ∀ z ∈ H, ‖z‖ ≤ ‖g z‖ + C ∧ ‖g z‖ ≤ ‖z‖ + C := fun z hz => by
    have h := hC z (QuantumZipper.H_subset_Hbar hz)
    rw [hgg hz] at h
    have h1 := norm_sub_le (g z) (g z - z)
    have h2 := norm_add_le z (g z - z)
    rw [sub_sub_cancel] at h1
    rw [add_sub_cancel] at h2
    exact ⟨by linarith, by linarith⟩
  have hbd1 : ∀ S ⊆ H, ¬ Bornology.IsBounded S → ¬ Bornology.IsBounded (g '' S) := by
    intro S hS hSu hB
    obtain ⟨R, hR⟩ := hB.subset_closedBall 0
    refine hSu ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R + C)).subset fun z hz => ?_)
    have h1 := hR ⟨z, hz, rfl⟩
    rw [mem_closedBall_zero_iff] at h1 ⊢
    linarith [(hnorm z (hS hz)).1]
  have hbd2 : ∀ S ⊆ H, ¬ Bornology.IsBounded (g '' S) → ¬ Bornology.IsBounded S := by
    intro S hS hu hB
    obtain ⟨R, hR⟩ := hB.subset_closedBall 0
    refine hu ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R + C)).subset ?_)
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hR hz
    rw [mem_closedBall_zero_iff] at h1 ⊢
    linarith [(hnorm z (hS hz)).2]
  apply Subset.antisymm
  · refine HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hF.isClosed
      ((HalfPlaneSep.isPreconnected_H_diff_fillH hA.isClosed hA.isBounded).image _
        (hg.continuousOn.mono sdiff_subset))
      (hbd1 _ sdiff_subset (HalfPlaneSep.not_isBounded_H_diff_fillH hA.isClosed hA.isBounded)) ?_
    rintro _ ⟨z, hz, rfl⟩
    have hgzD : g z ∈ H \ fillH P := hD ▸ ⟨z, hz.1, rfl⟩
    refine ⟨hgzD.1, ?_⟩
    rintro (hzP | ⟨a, ha, hae⟩)
    · exact hPH _ hgzD hzP
    · by_cases haH : a ∈ H
      · rw [hgg haH] at hae
        have := hinj haH hz.1 hae
        exact hz.2 (mem_fillH_of_mem_closure hz.1 (subset_closure (this ▸ ha)))
      · exact ext_notMem_image hg hinj hĝ hgg (hAH ha) haH ⟨z, hz.1, hae.symm⟩
  · intro y hy
    have hYpc := HalfPlaneSep.isPreconnected_H_diff_fillH hF.isClosed hF.isBounded
    have hYu := HalfPlaneSep.not_isBounded_H_diff_fillH hF.isClosed hF.isBounded
    have hYF : H \ fillH (P ∪ ĝ '' A) ⊆ H \ (P ∪ ĝ '' A) := HalfPlaneSep.H_diff_fillH_subset_H_diff hF.isClosed
    have hYD : H \ fillH (P ∪ ĝ '' A) ⊆ g '' H := by
      rw [hD]
      exact HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hP.isClosed hYpc hYu
        (fun w hw => ⟨(hYF hw).1, fun h => (hYF hw).2 (Or.inl h)⟩)
    let f : H → ℂ := fun w => g w
    have hfinj : Function.Injective f := fun a b h => Subtype.ext (hinj a.2 b.2 h)
    have hfopen : IsOpenMap f := by
      intro U hU
      obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
      have e : f '' (Subtype.val ⁻¹' U') = g '' (U' ∩ H) := by
        ext y
        constructor
        · rintro ⟨⟨w, hwH⟩, hw, rfl⟩
          exact ⟨w, ⟨hw, hwH⟩, rfl⟩
        · rintro ⟨w, ⟨hw, hwH⟩, rfl⟩
          exact ⟨⟨w, hwH⟩, hw, rfl⟩
      rw [e]
      exact isOpen_image_of_injOn hg hinj (hU'.inter QuantumZipper.isOpen_H) inter_subset_right
    have hrange : H \ fillH (P ∪ ĝ '' A) ⊆ range f := fun y hy => by
      obtain ⟨w, hw, hwy⟩ := hYD hy
      exact ⟨⟨w, hw⟩, hwy⟩
    have hpre := hYpc.preimage_of_isOpenMap hfinj hfopen hrange
    set Z := Subtype.val '' (f ⁻¹' (H \ fillH (P ∪ ĝ '' A))) with hZdef
    have hZpc : IsPreconnected Z := hpre.image _ continuous_subtype_val.continuousOn
    have hZH : Z ⊆ H := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hgZ : g '' Z = H \ fillH (P ∪ ĝ '' A) := by
      ext y
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        exact hw
      · intro hy
        obtain ⟨⟨w, hwH⟩, hwy⟩ := hrange hy
        have hmem : (⟨w, hwH⟩ : H) ∈ f ⁻¹' (H \ fillH (P ∪ ĝ '' A)) := by
          show f ⟨w, hwH⟩ ∈ H \ fillH (P ∪ ĝ '' A)
          rw [hwy]
          exact hy
        exact ⟨w, ⟨⟨w, hwH⟩, hmem, rfl⟩, hwy⟩
    have hZu : ¬ Bornology.IsBounded Z := hbd2 Z hZH (by rw [hgZ]; exact hYu)
    have hZA : Z ⊆ H \ A := fun z hz => by
      refine ⟨hZH hz, fun hzA => ?_⟩
      have hgzY : g z ∈ H \ fillH (P ∪ ĝ '' A) := by rw [← hgZ]; exact ⟨z, hz, rfl⟩
      exact (hYF hgzY).2 (Or.inr ⟨z, hzA, hgg (hZH hz)⟩)
    have hZsub := HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hA.isClosed hZpc hZu hZA
    rw [← hgZ] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hZsub hz, rfl⟩

end Chart

end InteractingSLE.Theorem14.SB.Lk
