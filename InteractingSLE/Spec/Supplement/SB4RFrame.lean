/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RChart
import InteractingSLE.Spec.Supplement.SBTail2TraceFrame

/-!
# SB4's sewing frame from the lifted lower tail

Packet PROVE-T14-SB4LEAF. The remaining geometric input of SB4's switch step is the retained-tail frame
`Retain.RetainedTailFrame f S Wrel m` (PROVE-T14-SBTAIL2): it reads the old upper history `A`, the completed lower walk
`B` and the relative lower walk `Wrel` in one reflected plane, calibrated to the launch readout `f`. Here the frame is
built deterministically from

* a path of `A` from `0` (`A` contains the bridge `[u, 0]`), the launch chart `c` with the right entry value `−m` at
  `R = max (A ∩ ℝ)` (SB2(2)'s entry clause), and the launch readout `f`;
* SB2(2)'s lift of the lower tail (supplement p. 631: "Erase `B` through its unique visit to `R` and lift the remaining
  tail into `D_A`. The result is again a finite simple proper lower walk of the retained conditional field"): a proper
  parametrization `β₀` of `B` from `0`, its visit `β₀ t_L = R`, a free real point left of `A ∪ {0}` off `B`, and a
  proper curve `γ` from `0` with range `Wrel` whose chart boundary values are `β₀ (t_L + ·)`;
* `A` on the closed left of `β₀`, and the forbidden side `S` inside the right side of `B`.

The frame is `p = ρ ∘ path`, `β = ρ ∘ β₀`, `γ' = ρ ∘ γ`, the reflected recentred chart `ρ ∘ (c − (−m)) ∘ ρ`, its
boundary map `g = ρ ∘ f ∘ (· − m) ∘ ρ`, and `J = id` (`ρ(z) = −z̄`).

* `refl_image_leftSide_subset`, `refl_image_closedLeftSide_subset` (mirror of `Supp9B.refl_image_rightSide_subset`);
* `eq_of_tendsto_inv` (uniqueness of chart boundary limits);
* `isRightEntryChart_runChart` (the recentred run chart is a right entry chart);
* **`retainedTailFrame_of_lift`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B

/-! ### Sides under the reflection -/

/-- The reflection of the left side of a curve is in the right side of the reflected curve. -/
theorem refl_image_leftSide_subset {γ : ℝ≥0 → ℂ} (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    refl '' leftSide γ ⊆ rightSide (reflectCurve γ) := by
  have hx : γ 0 - 1 - I ∈ (seedRayClosure γ)ᶜ :=
    lowerLeft_subset_compl hγ (left_ref_mem_lowerLeft h0)
  have h1 := continuous_refl.continuousOn.image_connectedComponentIn_subset (s := (seedRayClosure γ)ᶜ) hx
  have h2 : refl '' (seedRayClosure γ)ᶜ ⊆ (seedRayClosure (reflectCurve γ))ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzS
    have := refl_image_seedRayClosure_subset (reflectCurve γ) ⟨_, hzS, rfl⟩
    rw [refl_refl, reflectCurve_reflectCurve] at this
    exact hz this
  have hr : refl (γ 0 - 1 - I) = reflectCurve γ 0 + 1 - I := by
    apply Complex.ext
    · simp [reflectCurve]; ring
    · simp [reflectCurve, h0]
  rw [hr] at h1
  exact h1.trans (connectedComponentIn_mono _ h2)

/-- The reflection of the closed left side of a curve is in the closed right side of the reflected curve. -/
theorem refl_image_closedLeftSide_subset {γ : ℝ≥0 → ℂ} (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) :
    refl '' closedLeftSide γ ⊆ closedRightSide (reflectCurve γ) := by
  rw [closedLeftSide_eq, image_union]
  exact union_subset_union (refl_image_leftSide_subset hγ h0) (refl_image_seedRayClosure_subset γ)

/-! ### Boundary limits -/

/-- Chart boundary limits at a point of `closure ℍ` are unique. -/
theorem eq_of_tendsto_inv {F : ℂ → ℂ} {z a b : ℂ} (hz : z ∈ Hbar) (ha : Tendsto F (𝓝[H] z) (𝓝 a))
    (hb : Tendsto F (𝓝[H] z) (𝓝 b)) : a = b :=
  haveI := GW1P.neBot_nhdsWithin_H hz
  tendsto_nhds_unique ha hb

/-- The boundary readout agrees with the chart inverse in `ℍ`. -/
theorem eqOn_readout {c : Chart} (hcc : c.IsConformal) {f : ℂ → ℂ}
    (hf : ∀ z ∈ Hbar, Tendsto c.2.1 (𝓝[H] z) (𝓝 (f z))) : EqOn f c.2.1 H := by
  intro z hz
  have hzb : z ∈ Hbar := le_of_lt (show 0 < z.im from hz)
  have hcont : ContinuousAt c.2.1 z :=
    (hcc.1 z hz).continuousWithinAt.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)
  exact eq_of_tendsto_inv hzb (hf z hzb) (hcont.tendsto.mono_left nhdsWithin_le_nhds)

/-! ### The recentred run chart -/

open Exist.StagedLaw in
/-- **The recentred run chart is a right entry chart** at the largest real point of a compact `A` with the prefix's
fill, when it has the right entry value `a` there. -/
theorem isRightEntryChart_runChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {a : ℝ}
    (hv : Lx.IsRightEntryValue (stChart (ExplState.run κ b jumps spec D n)) (realMax A) a) :
    IsRightEntryChart A (realMax A) ((stChart (ExplState.run κ b jumps spec D n)).recenter a) := by
  have hD := Lw.isDomainChart_runChart spec D hreg n hnot
  rw [← hAf] at hD
  have hcob := Lw.tendsto_runChart_cobounded spec D hreg n hnot
  rw [← hAf] at hcob
  refine isRightEntryChart_recenter hD hv hcob fun x hx => ?_
  exact tendsto_runChart_lift_zero_right spec D hreg n hnot hAc hAf fun y hy =>
    lt_of_le_of_lt (Lx.le_realMax_of_mem hAc hy) hx

/-! ### The frame -/

/-- **SB4's retained-tail frame from SB2(2)'s lifted lower tail** (deterministic). -/
theorem retainedTailFrame_of_lift {f : ℂ → ℂ} {c : Chart} {A S Wrel : Set ℂ} {m : ℝ} {pA : ℝ → ℂ}
    (hp : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im)
    (hpA : pA '' Icc 0 1 = A) (hcc : c.IsConformal)
    (hrc : IsRightEntryChart A (realMax A) (c.recenter (-m)))
    (hf : ∀ z ∈ Hbar, Tendsto c.2.1 (𝓝[H] z) (𝓝 (f z))) (hfc : ContinuousOn f Hbar) (hm : m ≤ 0)
    {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hAL : A ⊆ closedLeftSide β₀) (htL : β₀ tL = (realMax A : ℂ))
    (hcol : ∃ y : ℝ, y < 0 ∧ y < realMin A ∧ (y : ℂ) ∉ range β₀)
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hγW : range γ = Wrel)
    (hlift : ∀ s : ℝ≥0, Tendsto c.2.1 (𝓝[H] (γ s - m)) (𝓝 (β₀ (tL + s))))
    (hS : S ⊆ rightSideOf (range β₀)) :
    Retain.RetainedTailFrame f S Wrel m := by
  have hβ0im : (β₀ 0).im = 0 := by rw [hβ0]; simp
  have hpimg : (fun s => refl (pA s)) '' Icc 0 1 = refl '' A := by
    rw [← hpA, image_image]
  have hfeq := eqOn_readout hcc hf
  -- the boundary map of the reflected recentred chart
  set g : ℂ → ℂ := fun w => refl (f (refl w + ((-m : ℝ) : ℂ))) with hg
  have hmaps : MapsTo (fun w => refl w + ((-m : ℝ) : ℂ)) Hbar Hbar := fun w hw => by
    have hw' : 0 ≤ w.im := hw
    show 0 ≤ (Supp9B.refl w + ((-m : ℝ) : ℂ)).im
    simpa using hw'
  refine ⟨fun s => refl (pA s), reflectCurve β₀, reflectCurve γ, reflChart (c.recenter (-m)), g, id, tL,
    continuous_refl.comp_continuousOn hp, by simp [hp0, Supp9B.refl], fun s hs => by simpa using hpH s hs,
    isProperCurve_reflectCurve hβ, by simp [reflectCurve, hβ0, Supp9B.refl], ?_, ?_, ?_, ?_, ?_,
    isProperCurve_reflectCurve hγ, by simp [reflectCurve, hγ0, Supp9B.refl], ?_, ?_, hm, ?_,
    Function.injective_id, ?_, ?_⟩
  · -- the old history on the closed right of the reflected walk
    rw [hpimg]
    exact (image_mono hAL).trans (refl_image_closedLeftSide_subset hβ.2.2.1 hβ0im)
  · -- the left entry chart
    rw [hpimg, realMin_refl_image]
    exact isLeftEntryChart_reflChart hrc
  · -- continuity of the boundary map
    exact continuous_refl.comp_continuousOn
      (hfc.comp ((continuous_refl.add continuous_const).continuousOn) hmaps)
  · -- the boundary map extends the chart inverse
    intro w hw
    have hw' : Supp9B.refl w + ((-m : ℝ) : ℂ) ∈ H := by
      show 0 < (Supp9B.refl w + ((-m : ℝ) : ℂ)).im
      simpa using (show 0 < w.im from hw)
    simp only [hg, reflChart_inv, Chart.recenter]
    rw [hfeq hw']
  · -- the visit to the entry point
    rw [hpimg, realMin_refl_image]
    simp [reflectCurve, htL, refl_ofReal]
  · -- the lift
    intro s
    have hz : γ s - (m : ℂ) ∈ Hbar := by
      show 0 ≤ (γ s - (m : ℂ)).im
      simpa using hγ.2.2.1 s
    have hfz := eq_of_tendsto_inv hz (hf _ hz) (hlift s)
    have he : refl (refl (γ s)) + ((-m : ℝ) : ℂ) = γ s - (m : ℂ) := by
      rw [refl_refl]; push_cast; ring
    simp only [hg, reflectCurve]
    rw [he, hfz]
  · -- the free collar
    obtain ⟨y, hy0, hyA, hyB⟩ := hcol
    refine ⟨-y, by linarith, ?_, ?_⟩
    · rw [hpimg, realMax_refl_image]; linarith
    · rintro ⟨t, ht⟩
      apply hyB
      refine ⟨t, ?_⟩
      have := congrArg Supp9B.refl ht
      simp only [reflectCurve, refl_refl] at this
      rw [this, refl_ofReal, neg_neg]
  · -- the relative walk
    rw [reflectCurve_reflectCurve, hγW]
  · -- the calibration
    intro z _
    have he : FlowDilate.aff 1 m z + ((-m : ℝ) : ℂ) = z := by
      simp [FlowDilate.aff]
    simp only [hg, id, refl_refl]
    rw [he]
  · -- the forbidden side
    rw [reflectCurve_reflectCurve, image_id]
    exact hS

end InteractingSLE.Theorem14.SB.Lf
