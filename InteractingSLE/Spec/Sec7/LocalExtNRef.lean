/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLLoc
import InteractingSLE.Spec.Sec7.LocalExtNUniq

/-!
# Aux. lemma 54: time-adapted references for every seed pattern

Packet PROVE-LOCEXT-N. Theorem 1.1's construction on a standard Borel driving space is a time-adapted reference with a
safe locality family (`IsStdReferenceLS`) for **every** seed pattern, also when a seed side is empty. When a side is
empty, the normalized history records the driver in place of the reference's seed mark of that side, so the
coordinates up to `q₂` are not read off the history by a formula. They are nevertheless a.s. determined by it: on the
paths of infinite lifetime, the marks are determined by the driver (`IsIntegratedSLEPath.vL_eq_of_w_eq`: uniqueness for
the singular mark equation), the driver on `[0, t]` by its values at rational times (continuity), and the noise by
the state (`WholeField.IsIntegratedSLEPath.eq_noiseOf`). Lusin separation on the standard Borel driving space
(`exists_measurableSet_preimage_of_saturated`) turns this pathwise determination into a Borel set of histories.

## Main results

* `coordUpTo_eq_of_w_eq`: the coordinates up to `q₂ ≤ t` of a path of infinite lifetime depend only on the driver on
  `[0, t]`;
* `exists_hist_coordUpTo`: every coordinate event up to `q₂ ≤ t` is a.s. a history event at `t`;
* **`isStdReferenceLS_of_stdBorel_all`**: the construction is a time-adapted reference with a safe locality family;
* **`emptySideReferenceLSStatement`**: PROVE-LOCEXT-L's named input `EmptySideReferenceLSStatement κ`;
* **`stdTwoSeedReferenceLSStatement`**: time-adapted references with a safe locality family for every seed pattern.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric LQGMetric.MarkovZB Coupling LocalSets Ito QuantumZipper.K3 QuantumZipper.Thm11Asm
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-! ### The coordinates are determined by the driver -/

section Coord

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {W : ℝ≥0 → Ω₀ → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω₀ → ℝ}
  {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}

theorem dense_range_coe_nnrat : Dense (range ((↑) : ℚ≥0 → ℝ≥0)) := by
  refine Metric.dense_iff.2 fun u δ hδ => ?_
  obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show (u : ℝ) < u + δ by linarith)
  have hr0 : (0 : ℝ) ≤ r := u.2.trans h1.le
  have e : (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = r := by rw [coe_toNNRat_eq, Real.coe_toNNReal _ hr0]
  refine ⟨((r.toNNRat : ℚ≥0) : ℝ≥0), ?_, r.toNNRat, rfl⟩
  rw [Metric.mem_ball, NNReal.dist_eq, e, abs_lt]
  constructor <;> linarith

/-- Two continuous paths agreeing at the rational times of `[0, t]` agree on `[0, t]`. -/
theorem eq_of_eq_nnrat {f g : ℝ≥0 → ℝ} (hf : Continuous f) (hg : Continuous g) {t : ℝ≥0}
    (h : ∀ q : ℚ≥0, f (min (q : ℝ≥0) t) = g (min (q : ℝ≥0) t)) : ∀ s ≤ t, f s = g s := by
  have e : (fun s => f (min s t)) = fun s => g (min s t) :=
    Continuous.ext_on dense_range_coe_nnrat (hf.comp (continuous_id.min continuous_const))
      (hg.comp (continuous_id.min continuous_const)) (by rintro _ ⟨q, rfl⟩; exact h q)
  intro s hs
  have := congrFun e s
  simpa only [min_eq_left hs] using this

/-- **The coordinates up to `q₂ ≤ t` of a two-seed path of infinite lifetime depend only on the driver on `[0, t]`**
(for every seed pattern). -/
theorem coordUpTo_eq_of_w_eq {κ rL rR : ℝ} (hκ : 0 < κ) {ω ω' : Ω₀} (hζ : ζ ω = ⊤) (hζ' : ζ ω' = ⊤)
    (hp : IsIntegratedSLEPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (fun t => W t ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω))
    (hp' : IsIntegratedSLEPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (fun t => W t ω')
      (fun i t => VL i t ω') (fun i t => VR i t ω') (fun t => B t ω') (ζ ω'))
    {q₂ t : ℚ≥0} (hq₂t : q₂ ≤ t) (hw : ∀ s ≤ (t : ℝ≥0), W s ω = W s ω') :
    coordUpTo W VL VR B ζ q₂ ω = coordUpTo W VL VR B ζ q₂ ω' := by
  rw [hζ] at hp
  rw [hζ'] at hp'
  funext q
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, s = min ((q : ℝ)).toNNReal (q₂ : ℝ≥0) := ⟨_, rfl⟩
  have hst : s ≤ (t : ℝ≥0) := hs ▸ (min_le_right _ _).trans (by exact_mod_cast hq₂t)
  have hL : ∀ i, VL i s ω = VL i s ω' := fun i =>
    IsIntegratedSLEPath.vL_eq_of_w_eq hp hp' hw i s hst
  have hR : ∀ i, VR i s ω = VR i s ω' := fun i =>
    IsIntegratedSLEPath.vR_eq_of_w_eq hp hp' hw i s hst
  have hB : B s ω = B s ω' := by
    rw [WholeField.IsIntegratedSLEPath.eq_noiseOf hκ hp ENNReal.coe_lt_top,
      WholeField.IsIntegratedSLEPath.eq_noiseOf hκ hp' ENNReal.coe_lt_top]
    simp only [hw s hst, hL, hR]
  simp only [coordUpTo, ← hs, coordVal, Coupling.killedVal, hζ, hζ', ENNReal.coe_lt_top, ↓reduceIte, hw s hst, hL,
    hR, hB]

/-! ### Coordinate events are history events -/

/-- **Every coordinate event up to `q₂ ≤ t` is a.s. an event of the normalized history truncated at `t`** (every seed
pattern; standard Borel driving space). -/
theorem exists_hist_coordUpTo {κ rL rR : ℝ} (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) {nL nR : ℕ}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {Ω₀ : Type*} [mΩ₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W : ℝ≥0 → Ω₀ → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₀ 𝓕₀ W VL VR B ζ)
    {q₂ t : ℚ≥0} (hq₂t : q₂ ≤ t) {C : Set (CoordSpace 1 1)} (hC : MeasurableSet C) :
    ∃ Γ : Set TwoSeedHist, MeasurableSet Γ ∧
      ∀ᵐ ω ∂P₀, (coordUpTo W VL VR B ζ q₂ ω ∈ C ↔ truncH t (fullRefHist xL xR W VL VR ω) ∈ Γ) := by
  classical
  have hc := measurable_coordVal hE
  -- the good set
  set P : Ω₀ → Prop := fun ω => ζ ω = ⊤ ∧ IsIntegratedSLEPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL)
    (fun _ => rR) (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) with hPdef
  have hP : ∀ᵐ ω ∂P₀, P ω := by
    filter_upwards [Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE hL hR, hE.2.2.2.2] with ω h1 h2
    exact ⟨h1, h2⟩
  set N := toMeasurable P₀ {ω | ¬ P ω} with hNdef
  have hN0 : P₀ N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hP
  have hGm : MeasurableSet Nᶜ := (measurableSet_toMeasurable _ _).compl
  have hGP : ∀ ω ∈ Nᶜ, P ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  -- the driver at the rational times of `[0, t]`
  set f : Ω₀ → (ℚ≥0 → ℝ) := fun ω q => Coupling.killedVal ζ W (min (q : ℝ≥0) t) ω with hfdef
  have hf : Measurable f := measurable_pi_iff.2 fun q => (hc _).snd.fst
  have hcu : Measurable (coordUpTo W VL VR B ζ q₂) := measurable_pi_iff.2 fun q => hc _
  have hfW : ∀ ω ∈ Nᶜ, ∀ q : ℚ≥0, f ω q = W (min (q : ℝ≥0) t) ω := fun ω hω q => by
    simp only [hfdef, Coupling.killedVal, (hGP ω hω).1, ENNReal.coe_lt_top, ↓reduceIte]
  obtain ⟨Γ, hΓ, hΓG⟩ := exists_measurableSet_preimage_of_saturated hf hGm (hcu hC)
    (fun ω hω ω' hω' he hωA => by
      have hw : ∀ s ≤ (t : ℝ≥0), W s ω = W s ω' := by
        refine eq_of_eq_nnrat (continuous_of_continuousOn_top ?_) (continuous_of_continuousOn_top ?_) fun q => ?_
        · have := (hGP ω hω).2.2.2.2.1
          rwa [(hGP ω hω).1] at this
        · have := (hGP ω' hω').2.2.2.2.1
          rwa [(hGP ω' hω').1] at this
        · rw [← hfW ω hω q, ← hfW ω' hω' q, he]
      have := coordUpTo_eq_of_w_eq hκ (hGP ω hω).1 (hGP ω' hω').1 (hGP ω hω).2 (hGP ω' hω').2 hq₂t hw
      simp only [mem_preimage, ← this]
      exact hωA)
  have hπ : Measurable fun y : TwoSeedHist => fun q : ℚ≥0 => (y.2 q).1 :=
    measurable_pi_iff.2 fun q => ((measurable_pi_apply q).comp measurable_snd).fst
  refine ⟨(fun y : TwoSeedHist => fun q : ℚ≥0 => (y.2 q).1) ⁻¹' Γ, hπ hΓ, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  have e : (fun q : ℚ≥0 => ((truncH t (fullRefHist xL xR W VL VR ω)).2 q).1) = f ω := by
    funext q
    rw [hfW ω hω q, truncH_fullRefHist]
    simp only [tsOf, refState]
  rw [mem_preimage, e]
  exact hΓG ω hω

end Coord

/-! ### The construction for every seed pattern -/

/-- **Theorem 1.1's construction on a standard Borel driving space is a time-adapted reference with a safe locality
family**, for every seed pattern (`isStdReferenceLS_of_stdBorel` without the hypothesis that both seed sides are
present). -/
theorem isStdReferenceLS_of_stdBorel_all {κ rL rR : ℝ} (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) {nL nR : ℕ}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    {Ω₀ : Type u} [mΩ₀ : MeasurableSpace Ω₀] [hSB : StandardBorelSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W : ℝ≥0 → Ω₀ → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω₀ → ℝ}
    {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₀ 𝓕₀ W VL VR B ζ) :
    ∃ (Pr : Measure (Ω₀ × DistOn upperHalfPlaneOpens))
      (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω₀ × DistOn upperHalfPlaneOpens))),
      IsStdReferenceLS κ rL rR xL xR Pr 𝓕r (fun t p => W t p.1) (fun i t p => VL i t p.1)
        (fun i t p => VR i t p.1) (fun t p => B t p.1) (fun p => ζ p.1) (fun p => p.2) := by
  have hc := measurable_coordVal hE
  have hE₁ := isIntegratedSLEEvolution_coordFiltration hE
  have hgen := IsAeGen.usualAugmentation (IsAeGen.usualAugmentation (P₀ := P₀)
    (isAeGen_coordFiltration (P₀ := P₀) hc))
  obtain ⟨α, μ, -, hμp, hμ1, hμ2, hαG, hfamS, hfamLS⟩ :=
    exists_locCoupling_safe hκ hE₁ (Sec2.Assembly2.not_thr_twoSeed hL hR 0 _ _) (measurable_coordMap hc) hgen
      (finiteFamilyProjStatement hκ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
  have hfamL := fun u₀ hu₀ => (hfamLS u₀ hu₀).isFamilyLocal
  set u₀ : ℂ → ℝ := Impl.forceExt κ (weightWord (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR))
    LP.twoSeedXL LP.twoSeedXR with hu₀def
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀ :=
    Impl.isBoundedHarmonicExtension_forceExt κ (weightWord (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)) _ _
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hEμ := IsIntegratedSLEEvolution.fst (X := DistOn upperHalfPlaneOpens) hμ1 hE₁
  have hZμ : IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω₀ × DistOn upperHalfPlaneOpens => p.2 - smoothDist upperHalfPlaneOpens u₀) μ :=
    isZeroBoundaryGFF_sub_smoothDist measurable_snd hu₀c (isZBGFFProcess_comp_snd hμ2 (hαG u₀ hu₀))
  have hharm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := isHarmonicDistOn_smoothDist_of hu₀
  have hC := isOptionalHullCoupling_of_isFamilySampled hEμ hκ measurable_snd
    (fun u₀' hu₀' => isZBGFFProcess_comp_snd hμ2 (hαG u₀' hu₀')) hfamS fun hX τ hτ hτζ => by
      have hl := isLocalSet_hull_of_isFamilyLocal hEμ hX hZμ (hfamL u₀ hu₀) hτ hτζ
      have hl' := IsLocalSet.add_dist hl hharm
      have e : (fun p : Ω₀ × DistOn upperHalfPlaneOpens =>
          p.2 - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = fun p => p.2 :=
        funext fun p => sub_add_cancel _ _
      rw [e] at hl'
      exact hl'
  refine ⟨μ, filtrationFst (usualAugmentation (coordFiltration hc) P₀) (DistOn upperHalfPlaneOpens),
    ⟨⟨inferInstance, hμp, hC, hfamS, fun t A hA => ?_, fun u₀' hu₀' => hfamL u₀' hu₀'⟩, ?_⟩,
    fun u₀' hu₀' => hfamLS u₀' hu₀'⟩
  · obtain ⟨A₀, hA₀, hAA₀⟩ := exists_fst_ae_eq_of_measurableSet_usualAugmentation hμ1 hA
    obtain ⟨C, hC', hA₀C⟩ := hgen t A₀ hA₀
    exact ⟨C, hC', hAA₀.trans (preimage_fst_ae_eq hμ1 hA₀C)⟩
  · intro q t hqt A hA
    obtain ⟨q₁, h1, h1t⟩ := exists_between hqt
    obtain ⟨q₂, h12, h2t'⟩ := exists_between h1t
    have h2t : q₂ ≤ t := h2t'.le
    obtain ⟨A₀, hA₀, hAA₀⟩ := exists_fst_ae_eq_of_measurableSet_usualAugmentation hμ1 hA
    obtain ⟨A₁, hA₁, hA₀A₁⟩ :=
      exists_ae_eq_of_measurableSet_usualAugmentation (show (q : ℝ≥0) < q₁ by exact_mod_cast h1) hA₀
    obtain ⟨A₂, hA₂, hA₁A₂⟩ :=
      exists_ae_eq_of_measurableSet_usualAugmentation (show (q₁ : ℝ≥0) < q₂ by exact_mod_cast h12) hA₁
    obtain ⟨C, hCm, hC2⟩ := MeasurableSpace.measurableSet_comap.1 (coordFiltration_le_comap_coordUpTo hc q₂ _ hA₂)
    obtain ⟨Γ, hΓ, hΓae⟩ := exists_hist_coordUpTo hκ hL hR xL xR hE h2t hCm
    refine ⟨Γ, hΓ, ?_⟩
    have hAe : A =ᵐ[μ] Prod.fst ⁻¹' A₂ := hAA₀.trans (preimage_fst_ae_eq hμ1 (hA₀A₁.trans hA₁A₂))
    have hcμ : ∀ᵐ p ∂μ, (coordUpTo W VL VR B ζ q₂ p.1 ∈ C ↔
        truncH t (fullRefHist xL xR W VL VR p.1) ∈ Γ) := by
      rw [← hμ1] at hΓae
      exact ae_of_ae_map measurable_fst.aemeasurable hΓae
    filter_upwards [hAe, hcμ] with p hp1 hp2
    have hp1' : p ∈ A ↔ p.1 ∈ A₂ := iff_of_eq hp1
    rw [hp1', ← hC2]
    exact hp2

/-- **A time-adapted standard reference with a safe locality family exists for every seed pattern** and every pair of
admissible seed weights. -/
theorem exists_isStdReferenceLS {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (rL rR : ℝ) (hL : -2 < rL) (hR : -2 < rR) :
    ∃ (Ωr : Type u) (_ : MeasurableSpace Ωr) (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr))
      (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
      (hr : Ωr → DistOn upperHalfPlaneOpens), IsStdReferenceLS κ rL rR xL xR Pr 𝓕r Wr VLr VRr Br ζr hr := by
  obtain ⟨Ω₀, mΩ₀, hSB, P₀, hP₀, 𝓕₀, W, VL, VR, B, ζ, hE⟩ :=
    thm22StdBorelStatement_of_ordered.{u} (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) hκ
      isOrderedForceWord_twoSeed'
  obtain ⟨Pr, 𝓕r, href⟩ := isStdReferenceLS_of_stdBorel_all hκ hL hR xL xR hE
  exact ⟨Ω₀ × DistOn upperHalfPlaneOpens, inferInstance, Pr, 𝓕r, _, _, _, _, _, _, href⟩

/-- **PROVE-LOCEXT-L's named input `EmptySideReferenceLSStatement κ`**: time-adapted references with a safe locality
family for seed patterns with an empty side. -/
theorem emptySideReferenceLSStatement {κ : ℝ} (hκ : 0 < κ) : EmptySideReferenceLSStatement.{u} κ :=
  fun xL xR rL rR hL hR _ _ _ => exists_isStdReferenceLS hκ xL xR rL rR hL hR

/-- **Time-adapted references with a safe locality family exist for every seed pattern.** -/
theorem stdTwoSeedReferenceLSStatement {κ : ℝ} (hκ : 0 < κ) : StdTwoSeedReferenceLSStatement.{u} κ :=
  fun xL xR rL rR hL hR _ _ => exists_isStdReferenceLS hκ xL xR rL rR hL hR

/-- **Aux. lemma 54 for stopped seed couplings from the post-stop locality identity alone.** -/
theorem stoppedSeedExtensionStatement_of_postLoc {κ : ℝ} (hκ : 0 < κ) (hPost : ExtPostLocalStatement.{u} κ) :
    StoppedSeedExtensionStatement.{u} κ :=
  stoppedSeedExtensionStatement_of_post hκ (emptySideReferenceLSStatement hκ) hPost

end LocalExt

end InteractingSLE
