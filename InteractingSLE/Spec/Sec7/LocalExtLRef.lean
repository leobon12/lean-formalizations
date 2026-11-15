/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtLExt

/-!
# Aux. lemma 54: Theorem 1.1's construction is a time-adapted reference

Packet PROVE-LOCEXT-L. Theorem 1.1's construction on a standard Borel driving space (`isStdReference_of_stdBorel`,
PROVE-LOCEXT-H) uses the usual augmentation of the **coordinate filtration** (`Coupling.coordFiltration`: the killed
driving state and the noise at rational times). Its events have time information: an event of the usual augmentation
at `q` is almost surely an event of the coordinates at rational times `≤ q₂` for any `q₂ > q`
(`exists_ae_eq_of_measurableSet_usualAugmentation`, twice). For a two-seed evolution the lifetime is infinite, the noise
is a function of the current state (`WholeField.IsIntegratedSLEPath.eq_noiseOf`), and — **when both seed sides are
present** — the coordinates are read off the normalized history truncated at any rational `t > q₂`
(`coordUpTo_eq_coordOfHist`). Hence the construction is a time-adapted reference (`IsStdReferenceL`).

## Main results

* `coe_toNNRat_eq`, `coordUpTo`, `coordFiltration_le_comap_coordUpTo`;
* **`isStdReferenceL_of_stdBorel`**: the construction is time-adapted, for a seed pattern with both sides present;
* **`stdTwoSeedReferenceLStatement_of_seeds`**: time-adapted references exist for words with seeds on both sides.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric Coupling Ito LocalSets
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-! ### Coordinates up to a rational time -/

theorem coe_toNNRat_eq (q : ℚ) : ((q.toNNRat : ℚ≥0) : ℝ≥0) = ((q : ℝ)).toNNReal := by
  apply NNReal.eq
  rw [Real.coe_toNNReal']
  rcases le_total 0 q with hq | hq
  · rw [max_eq_left (by exact_mod_cast hq)]
    have h1 : ((q.toNNRat : ℚ≥0) : ℚ) = q := Rat.coe_toNNRat q hq
    calc (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (((q.toNNRat : ℚ≥0) : ℚ) : ℝ) := by norm_cast
      _ = (q : ℝ) := by rw [h1]
  · rw [max_eq_right (by exact_mod_cast hq), Rat.toNNRat_eq_zero.2 hq]
    simp

section Coord

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {nL nR : ℕ} {W : ℝ≥0 → Ω₀ → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}

/-- The coordinates at the rational times, frozen at the rational time `q₂`. -/
def coordUpTo (W : ℝ≥0 → Ω₀ → ℝ) (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ)
    (B : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞) (q₂ : ℚ≥0) (ω : Ω₀) : CoordSpace nL nR :=
  fun q => coordVal W VL VR B ζ (min ((q : ℝ)).toNNReal (q₂ : ℝ≥0)) ω

theorem coordFiltration_le_comap_coordUpTo (hc : ∀ t, Measurable (coordVal W VL VR B ζ t)) (q₂ : ℚ≥0) :
    coordFiltration hc (q₂ : ℝ≥0) ≤ MeasurableSpace.comap (coordUpTo W VL VR B ζ q₂) inferInstance := by
  refine iSup₂_le fun q hq => ?_
  have e : coordVal W VL VR B ζ ((q : ℝ)).toNNReal = (fun f : CoordSpace nL nR => f q) ∘ coordUpTo W VL VR B ζ q₂ := by
    funext ω
    simp only [Function.comp_apply, coordUpTo, min_eq_left hq]
  rw [e]
  exact ((measurable_pi_apply q).comp (comap_measurable (coordUpTo W VL VR B ζ q₂))).comap_le

end Coord

/-! ### Coordinates read off the history -/

section Hist

/-- **The coordinates up to `q₂` read off a two-seed history**: indicator `1`, driver, the two seed marks, and the noise
recovered from the state (`WholeField.noiseOf`). -/
def coordOfHist (κ rL rR : ℝ) (q₂ : ℚ≥0) (y : TwoSeedHist) : CoordSpace 1 1 :=
  fun q => ((1 : ℝ), (y.2 (min q.toNNRat q₂)).1, (y.2 (min q.toNNRat q₂)).2.1, (y.2 (min q.toNNRat q₂)).2.2,
    WholeField.noiseOf κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR
      (y.2 (min q.toNNRat q₂)).1 (y.2 (min q.toNNRat q₂)).2.1 (y.2 (min q.toNNRat q₂)).2.2)

theorem measurable_coordOfHist (κ rL rR : ℝ) (q₂ : ℚ≥0) : Measurable (coordOfHist κ rL rR q₂) := by
  refine measurable_pi_iff.2 fun q => ?_
  have hv : Measurable fun y : TwoSeedHist => y.2 (min q.toNNRat q₂) :=
    (measurable_pi_apply _).comp measurable_snd
  exact measurable_const.prodMk ((measurable_fst.comp hv).prodMk ((measurable_fst.comp (measurable_snd.comp hv)).prodMk
    ((measurable_snd.comp (measurable_snd.comp hv)).prodMk
      ((WholeField.measurable_noiseOf κ _ _ _ _).comp hv))))

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {nL nR : ℕ}

/-- **With both seed sides present, the coordinates up to `q₂ ≤ t` are read off the history truncated at `t`**, on a path
with infinite lifetime. -/
theorem coordUpTo_eq_coordOfHist {κ rL rR : ℝ} (hκ : 0 < κ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (hseeds : (∃ i, xL i = 0) ∧ ∃ j, xR j = 0) {W : ℝ≥0 → Ω₀ → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω₀ → ℝ}
    {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞} {ω : Ω₀} (hζ : ζ ω = ⊤)
    (hp : IsIntegratedSLEPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (fun t => W t ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) {q₂ t : ℚ≥0} (hq₂t : q₂ ≤ t) :
    coordUpTo W VL VR B ζ q₂ ω = coordOfHist κ rL rR q₂ (truncH t (fullRefHist xL xR W VL VR ω)) := by
  classical
  funext q
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, s = min ((q : ℝ)).toNNReal (q₂ : ℝ≥0) := ⟨_, rfl⟩
  have hst : ((min q.toNNRat q₂ : ℚ≥0) : ℝ≥0) = s := by rw [hs, coe_min_nnrat, coe_toNNRat_eq]
  have hs_t : min s (t : ℝ≥0) = s := by
    rw [hs]
    exact min_eq_left ((min_le_right _ _).trans (by exact_mod_cast hq₂t))
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hval : (truncH t (fullRefHist xL xR W VL VR ω)).2 (min q.toNNRat q₂) = refState xL xR W VL VR ω s := by
    rw [truncH_fullRefHist]
    simp only [tsOf, hst, hs_t]
  have hB := WholeField.IsIntegratedSLEPath.eq_noiseOf hκ hp hsζ
  have eL : (fun i : Fin 1 => VL i s ω) = fun _ => VL 0 s ω := funext fun i => by rw [Subsingleton.elim i 0]
  have eR : (fun i : Fin 1 => VR i s ω) = fun _ => VR 0 s ω := funext fun i => by rw [Subsingleton.elim i 0]
  simp only [coordUpTo, coordOfHist, ← hs, hval]
  simp only [coordVal, Coupling.killedVal, hsζ, ↓reduceIte, refState, hseeds.1, hseeds.2, hB, eL, eR]

end Hist

/-! ### The construction -/

/-- **Theorem 1.1's construction on a standard Borel driving space is a time-adapted reference** (both seed sides
present). -/
theorem isStdReferenceL_of_stdBorel {κ rL rR : ℝ} (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) {nL nR : ℕ}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hseeds : (∃ i, xL i = 0) ∧ ∃ j, xR j = 0)
    {Ω₀ : Type u} [mΩ₀ : MeasurableSpace Ω₀] [hSB : StandardBorelSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W : ℝ≥0 → Ω₀ → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω₀ → ℝ}
    {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₀ 𝓕₀ W VL VR B ζ) :
    ∃ (Pr : Measure (Ω₀ × DistOn upperHalfPlaneOpens))
      (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω₀ × DistOn upperHalfPlaneOpens))),
      IsStdReferenceL κ rL rR xL xR Pr 𝓕r (fun t p => W t p.1) (fun i t p => VL i t p.1)
        (fun i t p => VR i t p.1) (fun t p => B t p.1) (fun p => ζ p.1) (fun p => p.2) := by
  have hc := measurable_coordVal hE
  have hE₁ := isIntegratedSLEEvolution_coordFiltration hE
  have hgen := IsAeGen.usualAugmentation (IsAeGen.usualAugmentation (P₀ := P₀)
    (isAeGen_coordFiltration (P₀ := P₀) hc))
  obtain ⟨α, μ, -, hμp, hμ1, hμ2, hαG, hfamS, hfamL⟩ :=
    exists_locCoupling_of_evolution hκ hE₁ (measurable_coordMap hc) hgen
      (finiteFamilyProjStatement hκ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
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
  -- the coordinates are read off the history almost surely
  have hζ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hE hL hR
  have hcoord : ∀ (q₂ t : ℚ≥0), q₂ ≤ t → ∀ᵐ ω ∂P₀,
      coordUpTo W VL VR B ζ q₂ ω = coordOfHist κ rL rR q₂ (truncH t (fullRefHist xL xR W VL VR ω)) := by
    intro q₂ t hq₂t
    filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
    exact coordUpTo_eq_coordOfHist hκ xL xR hseeds hζω hp hq₂t
  refine ⟨μ, filtrationFst (usualAugmentation (coordFiltration hc) P₀) (DistOn upperHalfPlaneOpens),
    ⟨inferInstance, hμp, hC, hfamS, fun t A hA => ?_, fun u₀' hu₀' => hfamL u₀' hu₀'⟩, ?_⟩
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
    refine ⟨coordOfHist κ rL rR q₂ ⁻¹' C, measurable_coordOfHist κ rL rR q₂ hCm, ?_⟩
    have hAe : A =ᵐ[μ] Prod.fst ⁻¹' A₂ := hAA₀.trans (preimage_fst_ae_eq hμ1 (hA₀A₁.trans hA₁A₂))
    have hcμ : ∀ᵐ p ∂μ, coordUpTo W VL VR B ζ q₂ p.1 =
        coordOfHist κ rL rR q₂ (truncH t (fullRefHist xL xR W VL VR p.1)) := by
      have := hcoord q₂ t h2t
      rw [← hμ1] at this
      exact ae_of_ae_map measurable_fst.aemeasurable this
    filter_upwards [hAe, hcμ] with p hp1 hp2
    have hp1' : p ∈ A ↔ p.1 ∈ A₂ := iff_of_eq hp1
    rw [hp1', ← hC2]
    simp only [mem_preimage]
    rw [hp2]
    rfl

/-- **A time-adapted standard reference exists** for every pair of admissible seed weights and every seed pattern with
both sides present. -/
theorem exists_isStdReferenceL_of_seeds {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (hseeds : (∃ i, xL i = 0) ∧ ∃ j, xR j = 0) (rL rR : ℝ) (hL : -2 < rL) (hR : -2 < rR) :
    ∃ (Ωr : Type u) (_ : MeasurableSpace Ωr) (Pr : Measure Ωr) (𝓕r : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ωr))
      (Wr : ℝ≥0 → Ωr → ℝ) (VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ) (Br : ℝ≥0 → Ωr → ℝ) (ζr : Ωr → ℝ≥0∞)
      (hr : Ωr → DistOn upperHalfPlaneOpens), IsStdReferenceL κ rL rR xL xR Pr 𝓕r Wr VLr VRr Br ζr hr := by
  obtain ⟨Ω₀, mΩ₀, hSB, P₀, hP₀, 𝓕₀, W, VL, VR, B, ζ, hE⟩ :=
    thm22StdBorelStatement_of_ordered.{u} (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) hκ
      isOrderedForceWord_twoSeed'
  obtain ⟨Pr, 𝓕r, href⟩ := isStdReferenceL_of_stdBorel hκ hL hR xL xR hseeds hE
  exact ⟨Ω₀ × DistOn upperHalfPlaneOpens, inferInstance, Pr, 𝓕r, _, _, _, _, _, _, href⟩

end LocalExt

end InteractingSLE
