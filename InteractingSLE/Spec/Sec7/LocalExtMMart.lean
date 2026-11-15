/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtMIto
import InteractingSLE.Spec.Sec7.LocalExtKDens
import InteractingSLE.Spec.Sec7.LocalExtA3Noise

/-!
# The tested source of a random word through the local stop: the mean and the cross bracket are martingales

Packet PROVE-LOCEXT-M (clause (a) of `RestartDrivingLocalityInput`; Aux. lemma 55, proof, specification p. 248:
"`(M_t − m, v) = ∫₀ᵗ a_s dB_s`, `0 ≤ t ≤ S`"). PROVE-LOCEXT-A2/A3 proved the two martingale statements behind this
identity for a deterministic force word (`martingale_meanStop_vSrc`, `martingale_crossStop_vSrc`). After a restart the
word is random. Here, for an evolution from a random admissible word `c` (`IsIntegratedSLEEvolutionFrom`, `c` measurable
at time `0`), a good event `G`, the local stop `S` of the good paths, and an event `A` of time `0` on which the source
`v_c` is bounded by a constant:

* `protect_of_le_localStopPath`: pathwise, before the local stop every point `z ∈ ℍ` with `6r ≤ |z|` is alive with
  `Im z / 2 ≤ Im f_t(z) ≤ Im z`;
* `srcMeanW A σ t = ∫ 1_A 𝔥_{t∧σ}(z) v_c(z) dz` and `srcCrossW A σ t = ∫ 1_A v_c(z) (𝔥_{t∧σ}(z) B_{t∧σ} − (Im f_{t∧σ}(z) −
  Im z)) dz`;
* **`martingale_srcMeanW`**, **`martingale_srcCrossW`**: for `A ⊆ G` of time `0` with `|v_c| ≤ m` on `A`, both are
  martingales of the null-augmented filtration (stopped at `σ = S`).

The proofs localize the random word by the events `{|c| < k}` (`exists_martingale_couplingMean_on`), protect every point
of the source by the exit stops of the coordinate size (`exitStop`), integrate the pointwise martingales against the
bounded `𝓖₀`-measurable weight `1_A v_c(z)` (`Coupling.martingale_integral_of_forall`), and let `k → ∞`
(`martingale_of_tendsto_of_null`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open Coupling Ito

/-! ### Protection of the source region before the local stop -/

section Protect

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- **Protection before the local stop**: along a good path, at every `t ≤ S`, every `z ∈ ℍ` with `6r ≤ |z|` has a
forward solution on `[0, t]` and `Im f_t(z) ≥ Im z / 2`. -/
theorem protect_of_le_localStopPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖) :
    (∃ u, IsForwardSol (Ito.rpath w) z t u) ∧ z.im / 2 ≤ (fwdMap (Ito.rpath w) t z).im ∧
      (fwdMap (Ito.rpath w) t z).im ≤ z.im := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  have hr0 := hr.1
  have halive := hreg.mem_of_lt_norm hz (by linarith)
  have htT' : (t : ℝ) ≤ T := by exact_mod_cast htT
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  refine ⟨⟨_, isForwardSol_congr (fun s hs => Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨hs.1, hs.2.trans htT₂⟩)
    (Ito.isForwardSol_fwdMap_of_mem hreg.cont t.coe_nonneg (Ito.mem_diff_fwdHull_of_le halive htT'))⟩, ?_, ?_⟩
  · have h := half_im_le_im_fwdMap hreg hz hz6 ⟨t.coe_nonneg, htT'⟩
    rwa [Ito.fwdMap_clampDrv_of_le htT₂] at h
  · have h := im_fwdMap_le_im hreg halive ⟨t.coe_nonneg, htT'⟩
    rwa [Ito.fwdMap_clampDrv_of_le htT₂] at h

end Protect

/-! ### The source of a word is supported on the source region -/

section Source

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

theorem vSrcW_eq_zero_of_not (x : (Fin nL → ℝ) × (Fin nR → ℝ)) {z : ℂ}
    (hz : ¬ (0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r)) : vSrcW κ ρL ρR r x z = 0 := by
  by_cases hx : IsAdmWord r x
  · rw [vSrcW_of_adm κ ρL ρR r hx]; exact vSrc_eq_zero_of_not hx.1 hx.2 hz
  · simp [vSrcW, vDensW_of_not_adm κ ρL ρR r hx]

end Source

/-! ### Exit stops of the coordinate size for paths continuous before a stop -/

section Exit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {S : Ω → ℝ≥0}

/-- The paths of `G` are continuous before the lifetime, the noise is continuous, and `S < ζ`. -/
def IsContBefore (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (S : Ω → ℝ≥0) (ω : Ω) : Prop :=
  (S ω : ℝ≥0∞) < ζ ω ∧ ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
    (∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧ (∀ j, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
    Continuous (B · ω)

variable (hpath : ∀ ω ∈ G, IsContBefore W VL VR B ζ S ω)
include hpath

theorem continuous_sizeProc_of (ω : Ω) : Continuous fun t => sizeProc W VL VR B S G t ω := by
  by_cases hω : ω ∈ G
  · obtain ⟨hσζ, hWc, hVLc, hVRc, hB⟩ := hpath ω hω
    have hsub : Iic (S ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t ht =>
      lt_of_le_of_lt (by exact_mod_cast ht) hσζ
    have hst : Continuous fun t : ℝ≥0 => min t (S ω) := continuous_id.min continuous_const
    have hmem : ∀ t : ℝ≥0, min t (S ω) ∈ Iic (S ω) := fun t => mem_Iic.2 (min_le_right _ _)
    have cW : Continuous fun t => W (min t (S ω)) ω := (hWc.mono hsub).comp_continuous hst hmem
    have cVL : ∀ i, Continuous fun t => VL i (min t (S ω)) ω := fun i =>
      ((hVLc i).mono hsub).comp_continuous hst hmem
    have cVR : ∀ i, Continuous fun t => VR i (min t (S ω)) ω := fun i =>
      ((hVRc i).mono hsub).comp_continuous hst hmem
    simp only [sizeProc, hω, ↓reduceIte, coordSize]
    exact ((cW.abs.add (hB.comp hst).abs).add (continuous_finsetSum _ fun i _ => (cVL i).abs)).add
      (continuous_finsetSum _ fun i _ => (cVR i).abs)
  · simp only [sizeProc, hω, ↓reduceIte]; exact continuous_const

theorem measurable_sizeProc_of (hWa : AdaptedBefore 𝓕 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVRa : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (hBa : ∀ t, Measurable[𝓕 t] (B t))
    (hS : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (S ω : WithTop ℝ≥0))
    (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G) (t : ℝ≥0) :
    Measurable[nullAugmented 𝓕 P t] (sizeProc W VL VR B S G t) := by
  set 𝓖 := nullAugmented 𝓕 P
  have hsub : ∀ ω ∈ G, Iic (S ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun ω hω t ht =>
    lt_of_le_of_lt (by exact_mod_cast ht) (hpath ω hω).1
  have hstop : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓕 ζ X →
      (∀ ω ∈ G, ContinuousOn (X · ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω}) →
      Measurable[𝓖 t] fun ω => if ω ∈ G then X (min t (S ω)) ω else 0 := fun X hX hXc =>
    measurable_stopped_of_agree (K := Girsanov.killed ζ X) (X := X) hS
      (fun s => Girsanov.measurable_killed (adaptedBefore_mono (le_nullAugmented 𝓕 P) hX) s) hG0 0
      (fun ω hω s hs => Girsanov.killed_of_lt (hsub ω hω hs)) (fun ω hω => (hXc ω hω).mono (hsub ω hω)) t
  have hW' := hstop W hWa fun ω hω => (hpath ω hω).2.1
  have hVL' := fun i => hstop (VL i) (hVLa i) fun ω hω => (hpath ω hω).2.2.1 i
  have hVR' := fun i => hstop (VR i) (hVRa i) fun ω hω => (hpath ω hω).2.2.2.1 i
  have hB' : Measurable[𝓖 t] fun ω => if ω ∈ G then B (min t (S ω)) ω else 0 :=
    measurable_stopped_of_agree (K := B) (X := B) hS
      (fun s => (hBa s).mono (le_nullAugmented 𝓕 P s) le_rfl) hG0 0 (fun _ _ _ _ => rfl)
      (fun ω hω => (hpath ω hω).2.2.2.2.continuousOn) t
  have hGt : MeasurableSet[𝓖 t] G := 𝓖.mono (zero_le (a := t)) G hG0
  have e : sizeProc W VL VR B S G t = G.piecewise (fun ω =>
      |if ω ∈ G then W (min t (S ω)) ω else 0| + |if ω ∈ G then B (min t (S ω)) ω else 0| +
        ∑ i, |if ω ∈ G then VL i (min t (S ω)) ω else 0| +
        ∑ i, |if ω ∈ G then VR i (min t (S ω)) ω else 0|) fun _ => 0 := by
    funext ω; by_cases hω : ω ∈ G <;> simp [sizeProc, coordSize, hω, Set.piecewise]
  rw [e]
  have ha := continuous_abs.measurable (α := ℝ)
  exact Measurable.piecewise hGt ((((ha.comp hW').add (ha.comp hB')).add
    (Finset.measurable_sum (m := 𝓖 t) _ fun i _ => ha.comp (hVL' i))).add
    (Finset.measurable_sum (m := 𝓖 t) _ fun i _ => ha.comp (hVR' i))) measurable_const

theorem isStoppingTime_exitStop_of (hWa : AdaptedBefore 𝓕 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVRa : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (hBa : ∀ t, Measurable[𝓕 t] (B t))
    (hS : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (S ω : WithTop ℝ≥0))
    (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G) (R : ℝ) (T : ℝ≥0) :
    IsStoppingTime (nullAugmented 𝓕 P) fun ω => ((exitStop W VL VR B S G R T ω : ℝ≥0) : WithTop ℝ≥0) := by
  have hτ := QuantumZipper.ItoLite.isStoppingTime_hittingBtwn_of_isClosed (𝓕 := nullAugmented 𝓕 P)
    (U := sizeProc W VL VR B S G) (fun t => measurable_sizeProc_of hpath hWa hVLa hVRa hBa hS hG0 t)
    (continuous_sizeProc_of hpath) (isClosed_Ici (a := R)) T
  have h := hS.min hτ
  convert h using 2 with ω
  simp [exitStop]

/-- Before the exit stop the coordinate size is at most `R` (if it starts below `R`). -/
theorem coordSize_le_of_le_exitStop_of {ω : Ω} (hω : ω ∈ G) {R : ℝ}
    (hR0 : coordSize W VL VR B 0 ω < R) {T : ℝ≥0} {s : ℝ≥0}
    (hs : s ≤ exitStop W VL VR B S G R T ω) : coordSize W VL VR B s ω ≤ R := by
  set D := sizeProc W VL VR B S G
  have hsσ : s ≤ S ω := hs.trans (min_le_left _ _)
  have hsτ : s ≤ hittingBtwn D (Ici R) 0 T ω := hs.trans (min_le_right _ _)
  have hD : ∀ r ≤ S ω, D r ω = coordSize W VL VR B r ω := fun r hr => by
    simp [D, sizeProc, hω, min_eq_left hr]
  have hlt : ∀ r < hittingBtwn D (Ici R) 0 T ω, D r ω < R := fun r hr =>
    not_le.1 fun h => notMem_of_lt_hittingBtwn hr (zero_le (a := r)) (mem_Ici.2 h)
  rcases hsτ.lt_or_eq with h | h
  · rw [← hD s hsσ]; exact (hlt s h).le
  · rcases eq_or_ne s 0 with h0 | h0
    · rw [h0]; exact hR0.le
    · have hcl : IsClosed {r : ℝ≥0 | D r ω ≤ R} :=
        isClosed_le (continuous_sizeProc_of hpath ω) continuous_const
      have hsub : Ico 0 s ⊆ {r : ℝ≥0 | D r ω ≤ R} := fun r hr => (hlt r (h ▸ hr.2)).le
      have hmem : s ∈ closure (Ico 0 s) := by
        rw [closure_Ico (Ne.symm h0)]; exact ⟨zero_le, le_rfl⟩
      rw [← hD s hsσ]
      exact hcl.closure_subset_iff.2 hsub hmem

/-- For a fixed path of `G`, the exit stops at levels `n → ∞` are eventually `S` itself. -/
theorem eventually_exitStop_eq_of {ω : Ω} {T : ℝ≥0} (hST : S ω ≤ T) :
    ∀ᶠ n : ℕ in atTop, exitStop W VL VR B S G (n : ℝ) T ω = S ω := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    (continuous_sizeProc_of hpath ω).continuousOn
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop C] with n hn
  have hno : ¬ ∃ j ∈ Icc (0 : ℝ≥0) T, sizeProc W VL VR B S G j ω ∈ Ici (n : ℝ) := by
    rintro ⟨j, hj, hjn⟩
    have := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hC j hj))
    exact absurd (hjn.trans this) (not_le.2 hn)
  simp only [exitStop, hittingBtwn, hno, ↓reduceIte]
  exact min_eq_left hST

end Exit

/-! ### Helpers: stops vanishing off an initial event, bounded initial weights, measurability of the stopped mean -/

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A stopping time replaced by `0` off an event of time `0` is a stopping time. -/
theorem isStoppingTime_ite_zero {𝓖 : Filtration ℝ≥0 mΩ} {E : Set Ω} (hE : MeasurableSet[𝓖 0] E)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓖 fun ω => ((if ω ∈ E then τ ω else 0 : ℝ≥0) : WithTop ℝ≥0) := by
  intro t
  have e : {ω | ((if ω ∈ E then τ ω else 0 : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      (E ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ t}) ∪ Eᶜ := by
    ext ω
    by_cases hω : ω ∈ E
    · simp [hω]
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, not_false_eq_true,
        or_true, iff_true]
      exact WithTop.coe_le_coe.2 (zero_le (a := t))
  rw [e]
  exact ((𝓖.mono (zero_le (a := t)) E hE).inter (hτ t)).union (𝓖.mono (zero_le (a := t)) E hE).compl

/-- **A martingale times a bounded `𝓖₀`-measurable weight is a martingale.** -/
theorem martingale_mul_of_zero [IsFiniteMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓖 P) {f : Ω → ℝ} (hf : StronglyMeasurable[𝓖 0] f) {C : ℝ} (hfC : ∀ ω, |f ω| ≤ C) :
    Martingale (fun t ω => f ω * M t ω) 𝓖 P := by
  refine ⟨fun t => (hf.mono (𝓖.mono (zero_le (a := t)))).mul (hM.1 t), fun s t hst => ?_⟩
  have h1 := condExp_stronglyMeasurable_mul_of_bound (𝓖.le s) (hf.mono (𝓖.mono (zero_le (a := s))))
    (hM.integrable t) C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfC ω)
  refine h1.trans ?_
  filter_upwards [hM.2 s t hst] with ω hω
  simp only [Pi.mul_apply, hω]

theorem tsupport_indicator_one_subset {K : Set ℂ} (hK : IsClosed K) :
    tsupport (K.indicator fun _ => (1 : ℝ)) ⊆ K :=
  closure_minimal (fun z hz => by
    by_contra h
    exact hz (indicator_of_notMem h _)) hK

end Helpers

section StoppedMean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : Set Ω} {σ : Ω → ℝ≥0}

/-- **The stopped coordinates at a point are measurable on an initial event** on which the point is alive at the stop
and the paths are continuous: `ω ↦ (Λ_{t∧σ}(z), B_{t∧σ})` on `E`, `(Λ_base, 0)` off `E`. -/
theorem measurable_pair_stopped_on (hWa : AdaptedBefore 𝓕 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVRa : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (hBa : ∀ t, Measurable[𝓕 t] (B t))
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hE0 : MeasurableSet[nullAugmented 𝓕 P 0] E) {z : ℂ} (hz : 0 < z.im)
    (hEp : ∀ ω ∈ E, ∃ xL xR, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω) ∧ (σ ω : ℝ≥0∞) < ζ ω ∧
      ∃ u, IsForwardSol (rpath (W · ω)) z (σ ω) u) (t : ℝ≥0) :
    Measurable[nullAugmented 𝓕 P t] (fun ω => if ω ∈ E then
      ((coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) : Coord nL nR × ℝ) else (coordBase z, 0)) := by
  have hWc : ∀ ω ∈ E, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω => by
    obtain ⟨xL, xR, hp, -⟩ := hEp ω hω; exact hp.2.2.2.1
  have hBm : ∀ t, Measurable[nullAugmented 𝓕 P t] (B t) := fun t =>
    (hBa t).mono (le_nullAugmented 𝓕 P t) le_rfl
  have hK := fun s => measurable_killedCoord κ (adaptedBefore_mono (le_nullAugmented 𝓕 P) hWa)
    (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVLa i))
    (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hVRa i)) hBm hWc hE0 hz
    (VL := VL) (VR := VR) (B := B) s
  have h1 : ∀ ω ∈ E, ∀ s : ℝ≥0, s ≤ σ ω → killedCoord κ z W VL VR B ζ E s ω =
      coordProc κ z W VL VR B s ω := by
    intro ω hω s hs
    obtain ⟨xL, xR, -, -, hσζ, u, hu⟩ := hEp ω hω
    have halive : ω ∈ aliveSet W ζ E z s := ⟨hω, lt_of_le_of_lt (by exact_mod_cast hs) hσζ, u,
      isForwardSol_of_le hu s.coe_nonneg (by exact_mod_cast hs)⟩
    simp only [killedCoord, halive, ↓reduceIte]
  have h2 : ∀ ω ∈ E, ContinuousOn (fun s => coordProc κ z W VL VR B s ω) (Iic (σ ω)) := by
    intro ω hω
    obtain ⟨xL, xR, hp, hBc, hσζ, hsol⟩ := hEp ω hω
    exact continuousOn_coordAt hp hσζ hz hsol hBc
  have hΛ := measurable_stopped_of_agree (X := coordProc κ z W VL VR B) hσ hK hE0 (coordBase z) h1 h2 t
  have hBs : Measurable[nullAugmented 𝓕 P t] (fun ω => if ω ∈ E then B (min t (σ ω)) ω else 0) :=
    measurable_stopped_of_agree (K := B) (X := B) hσ hBm hE0 0 (fun _ _ _ _ => rfl)
      (fun ω hω => by obtain ⟨xL, xR, -, hBc, -⟩ := hEp ω hω; exact hBc.continuousOn) t
  have e : (fun ω => if ω ∈ E then
      ((coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) : Coord nL nR × ℝ) else (coordBase z, 0)) =
      fun ω => ((if ω ∈ E then coordProc κ z W VL VR B (min t (σ ω)) ω else coordBase z),
        (if ω ∈ E then B (min t (σ ω)) ω else 0)) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  rw [e]
  exact hΛ.prodMk hBs

end StoppedMean

/-! ### The localized tested source and cross processes of a random word -/

section Defs

variable {Ω : Type*} {nL nR : ℕ}

variable (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
  (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ))

/-- The integrand `1_A 𝔥_{t∧σ}(z) v_c(z)` of the tested source mean. -/
def srcMeanInt (σ : Ω → ℝ≥0) (A : Set Ω) (t : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  if ω ∈ A then couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
    (bheProc κ ρL ρR W VL VR ω (min t (σ ω))) z * vSrcW κ ρL ρR r (c ω) z else 0

/-- The integrand `1_A v_c(z) (𝔥_{t∧σ}(z) B_{t∧σ} − (Im f_{t∧σ}(z) − Im z))` of the cross process. -/
def srcCrossInt (σ : Ω → ℝ≥0) (A : Set Ω) (t : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  if ω ∈ A then vSrcW κ ρL ρR r (c ω) z * (couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
    (bheProc κ ρL ρR W VL VR ω (min t (σ ω))) z * B (min t (σ ω)) ω -
      ((fwdMap (Ito.rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im)) else 0

/-- **The tested source mean of a random word, localized on `A` and stopped at `σ`.** -/
def srcMeanW (σ : Ω → ℝ≥0) (A : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ z, srcMeanInt κ ρL ρR r W VL VR c σ A t z ω

/-- **The cross process of the tested source of a random word, localized on `A` and stopped at `σ`.** -/
def srcCrossW (σ : Ω → ℝ≥0) (A : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ z, srcCrossInt κ ρL ρR r W VL VR B c σ A t z ω

variable (ζ : Ω → ℝ≥0∞) (S : Ω → ℝ≥0)

/-- **A good path of a random word**: a good path of the word `c ω`, a continuous noise from `0`, and `S` its local
stop. -/
def IsWordGood (ω : Ω) : Prop :=
  IsWordPath κ ρL ρR W VL VR B ζ c ω ∧ Continuous (B · ω) ∧ B 0 ω = 0 ∧
    (S ω : WithTop ℝ≥0) = localStopPath r (ζ ω) fun t => W t ω

end Defs

section WordGood

variable {Ω : Type*} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)} {ζ : Ω → ℝ≥0∞} {S : Ω → ℝ≥0} {ω : Ω}

theorem IsWordGood.lt_zeta (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) (hx : IsAdmWord r (c ω)) :
    (S ω : ℝ≥0∞) < ζ ω := by
  have h := localStopPath_lt hg.1.1 hx.1 hx.2 hg.1.2.2 hg.1.2.1 (r := r)
  rw [← hg.2.2.2] at h
  exact_mod_cast h

theorem IsWordGood.le_horizon (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) : S ω ≤ stopHorizon r := by
  have h := localStopPath_le_stopHorizon (r := r) (ζ := ζ ω) (w := fun t => W t ω)
  rw [← hg.2.2.2] at h
  exact WithTop.coe_le_coe.1 h

theorem IsWordGood.isContBefore (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) (hx : IsAdmWord r (c ω)) :
    IsContBefore W VL VR B ζ S ω :=
  ⟨hg.lt_zeta hx, hg.1.1.2.2.2.1, hg.1.1.2.2.2.2.1, hg.1.1.2.2.2.2.2.1, hg.2.1⟩

/-- Protection of the source region at every time `τ ≤ S` along a good path of a random word. -/
theorem IsWordGood.protect (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) (hx : IsAdmWord r (c ω)) {τ : ℝ≥0}
    (hτ : τ ≤ S ω) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖) :
    (∃ u, IsForwardSol (Ito.rpath (W · ω)) z τ u) ∧ z.im / 2 ≤ (fwdMap (Ito.rpath (W · ω)) τ z).im ∧
      (fwdMap (Ito.rpath (W · ω)) τ z).im ≤ z.im := by
  have hle : (τ : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    rw [← hg.2.2.2]; exact WithTop.coe_le_coe.2 hτ
  exact protect_of_le_localStopPath hg.1.1 hg.1.2.1 hx.1 hx.2 hg.1.2.2 hle hz hz6

/-- The coupling mean is bounded on the source region through the local stop. -/
theorem IsWordGood.abs_couplingMean_le (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) (hx : IsAdmWord r (c ω))
    {τ : ℝ≥0} (hτ : τ ≤ S ω) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖) :
    |couplingMean κ (fun s : ℝ => W s.toNNReal ω) (τ : ℝ) (bheProc κ ρL ρR W VL VR ω τ) z| ≤
      meanSrcBound κ ρL ρR r := by
  have hle : (τ : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    rw [← hg.2.2.2]; exact WithTop.coe_le_coe.2 hτ
  exact abs_couplingMean_bheAt_le hg.1.1 hg.1.2.1 hx.1 hx.2 hg.1.2.2 hle hz hz6

end WordGood

/-! ### The localization of a random word -/

section Local

variable {Ω : Type*} {nL nR : ℕ}

/-- The source region cut at height `1/(n+1)`: a closed subset of `ℍ`. -/
def srcCut (r : ℝ) (n : ℕ) : Set ℂ := {z : ℂ | 1 / ((n : ℝ) + 1) ≤ z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r}

theorem isClosed_srcCut (r : ℝ) (n : ℕ) : IsClosed (srcCut r n) :=
  (isClosed_le continuous_const Complex.continuous_im).inter
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))

theorem srcCut_subset_H (r : ℝ) (n : ℕ) : srcCut r n ⊆ H := fun _ hz => lt_of_lt_of_le (by positivity) hz.1

/-- The indicator of the cut source region (a function whose support is exactly `srcCut r n`). -/
def srcCutInd (r : ℝ) (n : ℕ) : ℂ → ℝ := (srcCut r n).indicator fun _ => 1

theorem tsupport_srcCutInd (r : ℝ) (n : ℕ) : tsupport (srcCutInd r n) = srcCut r n := by
  have h : Function.support (srcCutInd r n) = srcCut r n := by
    rw [srcCutInd, Set.support_indicator, Function.support_const one_ne_zero, inter_univ]
  rw [tsupport, h, (isClosed_srcCut r n).closure_eq]

/-- Eventually in `n` a point of the source region lies in the cut region. -/
theorem eventually_mem_srcCut {r : ℝ} {z : ℂ} (hz : 0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r) :
    ∀ᶠ n : ℕ in atTop, z ∈ srcCut r n := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hz.1
  filter_upwards [eventually_ge_atTop N] with n hn
  refine ⟨le_trans ?_ hN.le, hz.2⟩
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)

/-- The localization events `A ∩ {Σ|c| < k}`. -/
def wordEvent (A : Set Ω) (c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (k : ℕ) : Set Ω :=
  A ∩ {ω | ∑ i, |(c ω).1 i| + ∑ j, |(c ω).2 j| < k}

/-- The localized exit stops: the exit stop of the coordinate size at level `k` on the localization event, `0` off it. -/
def wordStop (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (S : Ω → ℝ≥0) (G A : Set Ω) (c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (r : ℝ) (k : ℕ) (ω : Ω) : ℝ≥0 :=
  if ω ∈ wordEvent A c k then exitStop W VL VR B S G (k : ℝ) (stopHorizon r) ω else 0

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {S : Ω → ℝ≥0} {G A : Set Ω} {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)} {r : ℝ}

theorem wordStop_le (k : ℕ) (ω : Ω) : wordStop W VL VR B S G A c r k ω ≤ S ω := by
  unfold wordStop
  split_ifs
  · exact exitStop_le _ _ ω
  · exact zero_le

theorem wordStop_of_mem {k : ℕ} {ω : Ω} (hω : ω ∈ wordEvent A c k) :
    wordStop W VL VR B S G A c r k ω = exitStop W VL VR B S G (k : ℝ) (stopHorizon r) ω := by
  simp [wordStop, hω]

theorem wordStop_of_notMem {k : ℕ} {ω : Ω} (hω : ω ∉ wordEvent A c k) : wordStop W VL VR B S G A c r k ω = 0 := by
  simp [wordStop, hω]

theorem measurableSet_wordEvent {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} (hA : MeasurableSet[𝓖 0] A)
    (hc : Measurable[𝓖 0] c) (k : ℕ) : MeasurableSet[𝓖 0] (wordEvent A c k) := by
  refine hA.inter (measurableSet_lt (mδ := 𝓖 0) ?_ measurable_const)
  refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_) (Finset.measurable_sum _ fun j _ => ?_)
  · exact continuous_abs.measurable.comp ((measurable_pi_apply i).comp (measurable_fst.comp hc))
  · exact continuous_abs.measurable.comp ((measurable_pi_apply j).comp (measurable_snd.comp hc))

end Local

/-! ### The source box -/

section Box

/-- The source box `6r ≤ |z| ≤ 7r`. -/
def srcBox (r : ℝ) : Set ℂ := {z : ℂ | 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r}

theorem measurableSet_srcBox (r : ℝ) : MeasurableSet (srcBox r) :=
  (measurableSet_le measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)

theorem volume_srcBox_lt_top (r : ℝ) : volume (srcBox r) < ⊤ :=
  lt_of_le_of_lt (measure_mono fun _ hz => mem_closedBall_zero_iff.2 hz.2) measure_closedBall_lt_top

theorem integrable_srcBox_indicator (r C : ℝ) : Integrable ((srcBox r).indicator fun _ => C) volume :=
  (integrableOn_const (volume_srcBox_lt_top r).ne).integrable_indicator (measurableSet_srcBox r)

theorem integral_srcBox_indicator (r C : ℝ) :
    ∫ z, (srcBox r).indicator (fun _ => C) z = C * volume.real (srcBox r) := by
  rw [integral_indicator_const C (measurableSet_srcBox r), smul_eq_mul, mul_comm]

end Box

/-! ### The localized processes: stops, protection, joint measurability -/

section Mart

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {S : Ω → ℝ≥0} {A : Set Ω}

variable (hE : IsIntegratedSLEEvolutionFrom κ ρL ρR P 𝓕 (fun ω => (c ω).1) (fun ω => (c ω).2) W VL VR B ζ)
  (hc : Measurable[𝓕 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
  (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G)
  (hG : ∀ ω ∈ G, IsWordGood κ ρL ρR r W VL VR B c ζ S ω)
  (hS : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (S ω : WithTop ℝ≥0))
  (hA0 : MeasurableSet[nullAugmented 𝓕 P 0] A) (hAG : A ⊆ G)

include hc in
theorem measurable_word_null (t : ℝ≥0) : Measurable[nullAugmented 𝓕 P t] c :=
  hc.mono ((le_nullAugmented 𝓕 P 0).trans ((nullAugmented 𝓕 P).mono (zero_le (a := t)))) le_rfl

include hE hc hadm hG0 hG hS hA0 in
theorem isStoppingTime_wordStop (k : ℕ) :
    IsStoppingTime (nullAugmented 𝓕 P) fun ω => (wordStop W VL VR B S G A c r k ω : WithTop ℝ≥0) :=
  isStoppingTime_ite_zero (measurableSet_wordEvent hA0 (measurable_word_null hc 0) k)
    (isStoppingTime_exitStop_of (fun ω hω => (hG ω hω).isContBefore (hadm ω)) hE.2.2.2.1 hE.2.2.2.2.1
      hE.2.2.2.2.2.1 (fun t => hE.1.2.1 t) hS hG0 (k : ℝ) (stopHorizon r))

include hadm hG hAG in
/-- On the localization event, the coordinate size is at most `k` up to the localized stop. -/
theorem coordSize_le_of_le_wordStop {k : ℕ} {ω : Ω} (hω : ω ∈ wordEvent A c k) {s : ℝ≥0}
    (hs : s ≤ wordStop W VL VR B S G A c r k ω) : coordSize W VL VR B s ω ≤ k := by
  have hωG : ω ∈ G := hAG hω.1
  have hg := hG ω hωG
  have hp := hg.1.1
  have h0 : coordSize W VL VR B 0 ω < k := by
    have e : coordSize W VL VR B 0 ω = ∑ i, |(c ω).1 i| + ∑ j, |(c ω).2 j| := by
      simp only [coordSize, hp.1, hg.2.2.1, abs_zero, zero_add, hp.2.1, hp.2.2.1]
    rw [e]; exact hω.2
  rw [wordStop_of_mem hω] at hs
  exact coordSize_le_of_le_exitStop_of (fun ω hω => (hG ω hω).isContBefore (hadm ω)) hωG h0 hs

include hadm hG hAG in
/-- On `A`, the localization event eventually contains `ω` and the localized stop is the local stop. -/
theorem eventually_wordStop_eq {ω : Ω} (hω : ω ∈ A) :
    ∀ᶠ k : ℕ in atTop, ω ∈ wordEvent A c k ∧ wordStop W VL VR B S G A c r k ω = S ω := by
  have hωG : ω ∈ G := hAG hω
  have h1 : ∀ᶠ k : ℕ in atTop, ω ∈ wordEvent A c k :=
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop (∑ i, |(c ω).1 i| + ∑ j, |(c ω).2 j|)).mono
      fun k hk => ⟨hω, hk⟩
  have h2 := eventually_exitStop_eq_of (fun ω hω => (hG ω hω).isContBefore (hadm ω)) (G := G)
    (hG ω hωG).le_horizon
  filter_upwards [h1, h2] with k hk1 hk2
  exact ⟨hk1, by rw [wordStop_of_mem hk1, hk2]⟩

include hadm hG hAG in
/-- **Protection by the localized stop.** -/
theorem protect_wordStop {k : ℕ} {ω : Ω} (hω : ω ∈ wordEvent A c k) {z : ℂ} (hz : 0 < z.im)
    (hz6 : 6 * r ≤ ‖z‖) :
    ((wordStop W VL VR B S G A c r k ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (∃ u, IsForwardSol (rpath (W · ω)) z (wordStop W VL VR B S G A c r k ω) u) ∧
      z.im / 2 ≤ (fwdMap (rpath (W · ω)) (wordStop W VL VR B S G A c r k ω) z).im ∧
      ((wordStop W VL VR B S G A c r k ω : ℝ≥0) : ℝ) ≤ r ^ 2 / 64 ∧
      ∀ s ≤ wordStop W VL VR B S G A c r k ω, |W s ω| ≤ k ∧ |B s ω| ≤ k ∧ (∀ i, |VL i s ω| ≤ k) ∧
        ∀ i, |VR i s ω| ≤ k := by
  have hωG : ω ∈ G := hAG hω.1
  have hg := hG ω hωG
  have hle := wordStop_le (W := W) (VL := VL) (VR := VR) (B := B) (S := S) (G := G) (A := A) (c := c) (r := r) k ω
  obtain ⟨h1, h2, -⟩ := hg.protect (hadm ω) hle hz hz6
  refine ⟨lt_of_le_of_lt (by exact_mod_cast hle) (hg.lt_zeta (hadm ω)), h1, h2, ?_,
    fun s hs => coordSize_bounds (coordSize_le_of_le_wordStop hadm hG hAG hω hs)⟩
  have := NNReal.coe_le_coe.2 (hle.trans hg.le_horizon)
  rwa [coe_stopHorizon] at this

include hadm hG hAG in
/-- **The good test structure of a localized path on the cut source region.** -/
theorem isGoodTest_wordStop {k : ℕ} {ω : Ω} (hω : ω ∈ wordEvent A c k) (n : ℕ) :
    IsGoodTest κ (c ω).1 (c ω).2 ρL ρR W VL VR B ζ (srcCutInd r n) (wordStop W VL VR B S G A c r k)
      (1 / (2 * ((n : ℝ) + 1))) (k : ℝ) (r ^ 2 / 64) ω := by
  have hg := hG ω (hAG hω.1)
  have hr0 := (hadm ω).2.1
  refine ⟨hg.1.1, hg.2.1, ?_⟩
  have h0 := protect_wordStop hadm hG hAG hω (z := (7 * r : ℝ) * Complex.I) (by simp; positivity)
    (by simp [abs_of_pos hr0]; linarith)
  refine ⟨h0.1, h0.2.2.2.1, h0.2.2.2.2, fun z hz => ?_⟩
  rw [tsupport_srcCutInd] at hz
  have hzpos : 0 < z.im := lt_of_lt_of_le (by positivity) hz.1
  obtain ⟨-, h1, h2, -⟩ := protect_wordStop hadm hG hAG hω hzpos hz.2.1
  refine ⟨h1, le_trans ?_ h2⟩
  have : 1 / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 := by rw [div_div, mul_comm]
  rw [this]
  exact div_le_div_of_nonneg_right hz.1 zero_le_two

include hadm hG hAG in
/-- The integrands at a point of the cut source region, read from the stopped coordinates. -/
theorem srcInt_wordStop_eq {k n : ℕ} {z : ℂ} (hz : z ∈ srcCut r n) (t : ℝ≥0) (ω : Ω) :
    srcMeanInt κ ρL ρR r W VL VR c (wordStop W VL VR B S G A c r k) (wordEvent A c k) t z ω =
      (wordEvent A c k).piecewise (fun ω => meanObs κ ρL ρR (coordProc κ z W VL VR B
        (min t (wordStop W VL VR B S G A c r k ω)) ω, B (min t (wordStop W VL VR B S G A c r k ω)) ω) *
          vSrcW κ ρL ρR r (c ω) z) (fun _ => 0) ω ∧
    srcCrossInt κ ρL ρR r W VL VR B c (wordStop W VL VR B S G A c r k) (wordEvent A c k) t z ω =
      (wordEvent A c k).piecewise (fun ω => vSrcW κ ρL ρR r (c ω) z * (meanObs κ ρL ρR (coordProc κ z W VL VR B
        (min t (wordStop W VL VR B S G A c r k ω)) ω, B (min t (wordStop W VL VR B S G A c r k ω)) ω) *
          B (min t (wordStop W VL VR B S G A c r k ω)) ω -
          ((coordF κ ((coordProc κ z W VL VR B (min t (wordStop W VL VR B S G A c r k ω)) ω,
            B (min t (wordStop W VL VR B S G A c r k ω)) ω) : Coord nL nR × ℝ)).im - z.im))) (fun _ => 0) ω := by
  by_cases hω : ω ∈ wordEvent A c k
  · have hgt := isGoodTest_wordStop hadm hG hAG (ρL := ρL) (ρR := ρR) hω n
    have hφH : tsupport (srcCutInd r n) ⊆ H := by rw [tsupport_srcCutInd]; exact srcCut_subset_H r n
    have hz' : z ∈ tsupport (srcCutInd r n) := by rwa [tsupport_srcCutInd]
    have hm := hgt.couplingMean_eq_meanVal hφH hz' (min_le_right t _)
      (isBoundedHarmonicExtension_bheProc κ ρL ρR ω _)
    simp only [srcMeanInt, srcCrossInt, hω, ↓reduceIte, Set.piecewise_eq_of_mem _ _ _ hω]
    rw [hm]
    refine ⟨rfl, ?_⟩
    simp only [meanVal, coordProc, coordF_coordAt]
  · simp only [srcMeanInt, srcCrossInt, hω, ↓reduceIte, Set.piecewise_eq_of_notMem _ _ _ hω, and_self]

include hE hc hadm hG0 hG hS hA0 hAG in
/-- **Joint measurability of the localized integrands** in the point and the path, at every time. -/
theorem measurable_srcInt_wordStop (k : ℕ) (t : ℝ≥0) :
    Measurable[(borel ℂ).prod (nullAugmented 𝓕 P t)] (fun p : ℂ × Ω =>
      srcMeanInt κ ρL ρR r W VL VR c (wordStop W VL VR B S G A c r k) (wordEvent A c k) t p.1 p.2) ∧
    Measurable[(borel ℂ).prod (nullAugmented 𝓕 P t)] (fun p : ℂ × Ω =>
      srcCrossInt κ ρL ρR r W VL VR B c (wordStop W VL VR B S G A c r k) (wordEvent A c k) t p.1 p.2) := by
  set σ := wordStop W VL VR B S G A c r k with hσdef
  set E := wordEvent A c k with hEdef
  have hE0 : MeasurableSet[nullAugmented 𝓕 P 0] E := measurableSet_wordEvent hA0 (measurable_word_null hc 0) k
  have hEt : MeasurableSet[nullAugmented 𝓕 P t] E := (nullAugmented 𝓕 P).mono (zero_le (a := t)) E hE0
  have hσ := isStoppingTime_wordStop hE hc hadm hG0 hG hS hA0 (ρL := ρL) (ρR := ρR) (κ := κ) k
  -- measurability in the path at a point of the cut region
  have hpt : ∀ n, ∀ z ∈ srcCut r n,
      Measurable[nullAugmented 𝓕 P t] (fun ω => srcMeanInt κ ρL ρR r W VL VR c σ E t z ω) ∧
      Measurable[nullAugmented 𝓕 P t] (fun ω => srcCrossInt κ ρL ρR r W VL VR B c σ E t z ω) := by
    intro n z hz
    have hzpos : 0 < z.im := srcCut_subset_H r n hz
    have hpair := measurable_pair_stopped_on (κ := κ) (ρL := ρL) (ρR := ρR) hE.2.2.2.1 hE.2.2.2.2.1
      hE.2.2.2.2.2.1 (fun t => hE.1.2.1 t) hσ hE0 hzpos (fun ω hω => by
        have hgt := isGoodTest_wordStop hadm hG hAG (ρL := ρL) (ρR := ρR) (κ := κ) hω n
        have hz' : z ∈ tsupport (srcCutInd r n) := by rwa [tsupport_srcCutInd]
        exact ⟨_, _, hgt.1, hgt.2.1, hgt.2.2.1, (hgt.2.2.2.2.2 z hz').1⟩) t
    have hv : Measurable[nullAugmented 𝓕 P t] (fun ω => vSrcW κ ρL ρR r (c ω) z) :=
      (measurable_vSrcW κ ρL ρR r).comp ((measurable_word_null hc t).prodMk measurable_const)
    have hpairE : ∀ ω ∈ E, ((coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) : Coord nL nR × ℝ) =
        (fun ω => if ω ∈ E then ((coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) :
          Coord nL nR × ℝ) else (coordBase z, 0)) ω := fun ω hω => by simp [hω]
    have hmo := (measurable_meanObs κ ρL ρR).comp hpair
    have hfo := Complex.measurable_im.comp ((show Measurable (coordF κ (nL := nL) (nR := nR)) by
      unfold coordF; fun_prop).comp hpair)
    have hBo := measurable_snd.comp hpair
    refine ⟨?_, ?_⟩
    · have e : (fun ω => srcMeanInt κ ρL ρR r W VL VR c σ E t z ω) = E.piecewise (fun ω =>
          meanObs κ ρL ρR ((fun ω => if ω ∈ E then ((coordProc κ z W VL VR B (min t (σ ω)) ω,
            B (min t (σ ω)) ω) : Coord nL nR × ℝ) else (coordBase z, 0)) ω) * vSrcW κ ρL ρR r (c ω) z)
          (fun _ => 0) := by
        funext ω
        rw [(srcInt_wordStop_eq hadm hG hAG hz t ω).1, ← hEdef, ← hσdef]
        by_cases hω : ω ∈ E
        · simp only [Set.piecewise_eq_of_mem _ _ _ hω, ← hpairE ω hω]
        · simp only [Set.piecewise_eq_of_notMem _ _ _ hω]
      rw [e]
      exact Measurable.piecewise hEt (hmo.mul hv) measurable_const
    · have e : (fun ω => srcCrossInt κ ρL ρR r W VL VR B c σ E t z ω) = E.piecewise (fun ω =>
          vSrcW κ ρL ρR r (c ω) z * (meanObs κ ρL ρR ((fun ω => if ω ∈ E then ((coordProc κ z W VL VR B
            (min t (σ ω)) ω, B (min t (σ ω)) ω) : Coord nL nR × ℝ) else (coordBase z, 0)) ω) *
            ((fun ω => if ω ∈ E then ((coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) :
              Coord nL nR × ℝ) else (coordBase z, 0)) ω).2 -
            ((coordF κ ((fun ω => if ω ∈ E then ((coordProc κ z W VL VR B (min t (σ ω)) ω,
              B (min t (σ ω)) ω) : Coord nL nR × ℝ) else (coordBase z, 0)) ω)).im - z.im)))
          (fun _ => 0) := by
        funext ω
        rw [(srcInt_wordStop_eq hadm hG hAG hz t ω).2, ← hEdef, ← hσdef]
        by_cases hω : ω ∈ E
        · simp only [Set.piecewise_eq_of_mem _ _ _ hω, ← hpairE ω hω]
        · simp only [Set.piecewise_eq_of_notMem _ _ _ hω]
      rw [e]
      exact Measurable.piecewise hEt (hv.mul ((hmo.mul hBo).sub (hfo.sub measurable_const))) measurable_const
  -- continuity in the point on the cut region
  have hct : ∀ n ω, ContinuousOn (fun z => srcMeanInt κ ρL ρR r W VL VR c σ E t z ω) (srcCut r n) ∧
      ContinuousOn (fun z => srcCrossInt κ ρL ρR r W VL VR B c σ E t z ω) (srcCut r n) := by
    intro n ω
    by_cases hω : ω ∈ E
    · have hgt := isGoodTest_wordStop hadm hG hAG (ρL := ρL) (ρR := ρR) (κ := κ) hω n
      have hφH : tsupport (srcCutInd r n) ⊆ H := by rw [tsupport_srcCutInd]; exact srcCut_subset_H r n
      have hmv := hgt.continuousOn_meanVal hφH (min_le_right t (σ ω))
      rw [tsupport_srcCutInd] at hmv
      have hv : ContinuousOn (fun z => vSrcW κ ρL ρR r (c ω) z) (srcCut r n) :=
        (continuous_vDensW κ ρL ρR r (c ω)).continuousOn.congr fun z hz => by
          simp only [vSrcW, indicator_of_mem (srcCut_subset_H r n hz)]
      have hprot := hgt.isProtected hφH
      have hcl := hgt.continuous_clampPath
      have hrI : ((min t (σ ω) : ℝ≥0) : ℝ) ∈ Icc 0 (σ ω : ℝ) :=
        ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_right t (σ ω)⟩
      have hf : ContinuousOn (fun z => fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z) (srcCut r n) := by
        rw [← fwdMap_clampPath (W := W) (σ := σ) hrI.2, ← tsupport_srcCutInd r n]
        exact hprot.continuousOn_fwdMap hcl hrI
      have h1 : ContinuousOn (fun z => meanVal κ ρL ρR W VL VR B z (min t (σ ω)) ω *
          vSrcW κ ρL ρR r (c ω) z) (srcCut r n) := hmv.mul hv
      have h2 : ContinuousOn (fun z => vSrcW κ ρL ρR r (c ω) z * (meanVal κ ρL ρR W VL VR B z (min t (σ ω)) ω *
          B (min t (σ ω)) ω - ((fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im))) (srcCut r n) :=
        hv.mul ((hmv.mul continuousOn_const).sub
          ((Complex.continuous_im.comp_continuousOn hf).sub Complex.continuous_im.continuousOn))
      refine ⟨h1.congr fun z hz => ?_, h2.congr fun z hz => ?_⟩
      · rw [(srcInt_wordStop_eq hadm hG hAG hz t ω).1, ← hEdef, ← hσdef, Set.piecewise_eq_of_mem _ _ _ hω]; rfl
      · rw [(srcInt_wordStop_eq hadm hG hAG hz t ω).2, ← hEdef, ← hσdef, Set.piecewise_eq_of_mem _ _ _ hω]
        simp only [meanVal, coordProc, coordF_coordAt]
    · simp only [srcMeanInt, srcCrossInt, hω, ↓reduceIte]
      exact ⟨continuousOn_const, continuousOn_const⟩
  -- the cut integrands and their limit
  have hcut : ∀ n, Measurable[(borel ℂ).prod (nullAugmented 𝓕 P t)] (fun p : ℂ × Ω =>
      (srcCut r n).indicator (fun z => srcMeanInt κ ρL ρR r W VL VR c σ E t z p.2) p.1) ∧
      Measurable[(borel ℂ).prod (nullAugmented 𝓕 P t)] (fun p : ℂ × Ω =>
      (srcCut r n).indicator (fun z => srcCrossInt κ ρL ρR r W VL VR B c σ E t z p.2) p.1) := fun n =>
    ⟨measurable_uncurry_of_continuousOn (mα := nullAugmented 𝓕 P t) (isClosed_srcCut r n)
      (g := fun z ω => (srcCut r n).indicator (fun z => srcMeanInt κ ρL ρR r W VL VR c σ E t z ω) z) 0
      (fun ω => (hct n ω).1.congr fun z hz => indicator_of_mem hz _)
      (fun z hz => by simp only [indicator_of_mem hz]; exact (hpt n z hz).1)
      (fun z hz ω => indicator_of_notMem hz _),
    measurable_uncurry_of_continuousOn (mα := nullAugmented 𝓕 P t) (isClosed_srcCut r n)
      (g := fun z ω => (srcCut r n).indicator (fun z => srcCrossInt κ ρL ρR r W VL VR B c σ E t z ω) z) 0
      (fun ω => (hct n ω).2.congr fun z hz => indicator_of_mem hz _)
      (fun z hz => by simp only [indicator_of_mem hz]; exact (hpt n z hz).2)
      (fun z hz ω => indicator_of_notMem hz _)⟩
  have hlim : ∀ p : ℂ × Ω, (∀ᶠ n : ℕ in atTop,
      (srcCut r n).indicator (fun z => srcMeanInt κ ρL ρR r W VL VR c σ E t z p.2) p.1 =
        srcMeanInt κ ρL ρR r W VL VR c σ E t p.1 p.2) ∧ ∀ᶠ n : ℕ in atTop,
      (srcCut r n).indicator (fun z => srcCrossInt κ ρL ρR r W VL VR B c σ E t z p.2) p.1 =
        srcCrossInt κ ρL ρR r W VL VR B c σ E t p.1 p.2 := by
    intro p
    by_cases hz : 0 < p.1.im ∧ 6 * r ≤ ‖p.1‖ ∧ ‖p.1‖ ≤ 7 * r
    · exact ⟨(eventually_mem_srcCut hz).mono fun n hn => indicator_of_mem hn _,
        (eventually_mem_srcCut hz).mono fun n hn => indicator_of_mem hn _⟩
    · have hv : vSrcW κ ρL ρR r (c p.2) p.1 = 0 := vSrcW_eq_zero_of_not _ hz
      have h1 : srcMeanInt κ ρL ρR r W VL VR c σ E t p.1 p.2 = 0 := by simp [srcMeanInt, hv]
      have h2 : srcCrossInt κ ρL ρR r W VL VR B c σ E t p.1 p.2 = 0 := by simp [srcCrossInt, hv]
      refine ⟨Eventually.of_forall fun n => ?_, Eventually.of_forall fun n => ?_⟩
      · rw [h1]; by_cases hn : p.1 ∈ srcCut r n
        · rw [indicator_of_mem hn, h1]
        · rw [indicator_of_notMem hn]
      · rw [h2]; by_cases hn : p.1 ∈ srcCut r n
        · rw [indicator_of_mem hn, h2]
        · rw [indicator_of_notMem hn]
  exact ⟨@measurable_of_tendsto_metrizable (ℂ × Ω) ℝ ((borel ℂ).prod (nullAugmented 𝓕 P t)) _ _ _ _ _ _
    (fun n => (hcut n).1) (tendsto_pi_nhds.2 fun p =>
      tendsto_const_nhds.congr' ((hlim p).1.mono fun n hn => hn.symm)),
    @measurable_of_tendsto_metrizable (ℂ × Ω) ℝ ((borel ℂ).prod (nullAugmented 𝓕 P t)) _ _ _ _ _ _
    (fun n => (hcut n).2) (tendsto_pi_nhds.2 fun p =>
      tendsto_const_nhds.congr' ((hlim p).2.mono fun n hn => hn.symm))⟩

include hadm hG hAG in
/-- The integrand of the source mean is bounded by `meanSrcBound · m` on the source box, before the local stop. -/
theorem abs_srcMeanInt_le {m : ℝ} (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) {σ : Ω → ℝ≥0}
    (hσS : ∀ ω, σ ω ≤ S ω) {E : Set Ω} (hEA : E ⊆ A) (t : ℝ≥0) (z : ℂ) (ω : Ω) :
    |srcMeanInt κ ρL ρR r W VL VR c σ E t z ω| ≤
      (srcBox r).indicator (fun _ => meanSrcBound κ ρL ρR r * |m|) z := by
  have hM0 : 0 ≤ meanSrcBound κ ρL ρR r := by
    unfold meanSrcBound Coupling.meanHarmonicBound; positivity
  have hg0 : 0 ≤ (srcBox r).indicator (fun _ => meanSrcBound κ ρL ρR r * |m|) z :=
    Set.indicator_nonneg (fun _ _ => mul_nonneg hM0 (abs_nonneg m)) z
  by_cases hω : ω ∈ E
  · by_cases hz : 0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r
    · rw [indicator_of_mem (show z ∈ srcBox r from hz.2)]
      simp only [srcMeanInt, hω, ↓reduceIte, abs_mul]
      exact mul_le_mul ((hG ω (hAG (hEA hω))).abs_couplingMean_le (hadm ω)
        ((min_le_right _ _).trans (hσS ω)) hz.1 hz.2.1)
        ((hAm ω (hEA hω) z).trans (le_abs_self m)) (abs_nonneg _) hM0
    · simp only [srcMeanInt, hω, ↓reduceIte, vSrcW_eq_zero_of_not _ hz, mul_zero, abs_zero]
      exact hg0
  · simp only [srcMeanInt, hω, ↓reduceIte, abs_zero]; exact hg0

include hadm hG hAG in
/-- The integrand of the cross process is bounded by `m (meanSrcBound · |B_{t∧σ}| + 7r)` on the source box. -/
theorem abs_srcCrossInt_le {m : ℝ} (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) {σ : Ω → ℝ≥0}
    (hσS : ∀ ω, σ ω ≤ S ω) {E : Set Ω} (hEA : E ⊆ A) (t : ℝ≥0) (z : ℂ) (ω : Ω) :
    |srcCrossInt κ ρL ρR r W VL VR B c σ E t z ω| ≤
      (srcBox r).indicator (fun _ => |m| * (meanSrcBound κ ρL ρR r * |B (min t (σ ω)) ω| + 7 * r)) z := by
  have hM0 : 0 ≤ meanSrcBound κ ρL ρR r := by
    unfold meanSrcBound Coupling.meanHarmonicBound; positivity
  have hr0 : 0 ≤ r := (hadm ω).2.1.le
  have hg0 : 0 ≤ (srcBox r).indicator (fun _ => |m| * (meanSrcBound κ ρL ρR r * |B (min t (σ ω)) ω| + 7 * r)) z :=
    Set.indicator_nonneg (fun _ _ => mul_nonneg (abs_nonneg m) (by positivity)) z
  by_cases hω : ω ∈ E
  · by_cases hz : 0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r
    · rw [indicator_of_mem (show z ∈ srcBox r from hz.2)]
      have hg := hG ω (hAG (hEA hω))
      have hτ : min t (σ ω) ≤ S ω := (min_le_right _ _).trans (hσS ω)
      have hcm := hg.abs_couplingMean_le (hadm ω) hτ hz.1 hz.2.1
      obtain ⟨-, hlo, hhi⟩ := hg.protect (hadm ω) hτ hz.1 hz.2.1
      have hv := (hAm ω (hEA hω) z).trans (le_abs_self m)
      have hf : |(fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im| ≤ 7 * r := by
        rw [abs_le]; constructor <;> linarith [Complex.im_le_norm z]
      simp only [srcCrossInt, hω, ↓reduceIte, abs_mul]
      refine mul_le_mul hv ?_ (abs_nonneg _) (abs_nonneg m)
      calc |couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
            (bheProc κ ρL ρR W VL VR ω (min t (σ ω))) z * B (min t (σ ω)) ω -
            ((fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im)|
          ≤ |couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
            (bheProc κ ρL ρR W VL VR ω (min t (σ ω))) z| * |B (min t (σ ω)) ω| +
            |(fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im| := by
              rw [← abs_mul]; exact abs_sub _ _
        _ ≤ meanSrcBound κ ρL ρR r * |B (min t (σ ω)) ω| + 7 * r :=
              add_le_add (mul_le_mul_of_nonneg_right hcm (abs_nonneg _)) hf
    · simp only [srcCrossInt, hω, ↓reduceIte, vSrcW_eq_zero_of_not _ hz, zero_mul, abs_zero]
      exact hg0
  · simp only [srcCrossInt, hω, ↓reduceIte, abs_zero]; exact hg0

include hE hc hadm hG0 hG hS hA0 hAG in
/-- **The localized stopped source mean at level `k` is a martingale** (integrated (3.15)). -/
theorem martingale_srcMeanW_wordStop [IsProbabilityMeasure P] (hκ : 0 < κ) (hr0 : 0 < r) {m : ℝ}
    (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) (k : ℕ) :
    Martingale (srcMeanW κ ρL ρR r W VL VR c (wordStop W VL VR B S G A c r k) (wordEvent A c k))
      (nullAugmented 𝓕 P) P := by
  set σ := wordStop W VL VR B S G A c r k with hσdef
  set E := wordEvent A c k with hEdef
  have hE0 : MeasurableSet[nullAugmented 𝓕 P 0] E := measurableSet_wordEvent hA0 (measurable_word_null hc 0) k
  have hσ := isStoppingTime_wordStop hE hc hadm hG0 hG hS hA0 (ρL := ρL) (ρR := ρR) (κ := κ) k
  have hM0 : 0 ≤ meanSrcBound κ ρL ρR r := by
    unfold meanSrcBound Coupling.meanHarmonicBound; positivity
  have hg0 : ∀ z, 0 ≤ (srcBox r).indicator (fun _ => meanSrcBound κ ρL ρR r * |m|) z :=
    fun z => Set.indicator_nonneg (fun _ _ => mul_nonneg hM0 (abs_nonneg m)) z
  refine martingale_integral_of_forall (μ := volume) (Y := fun t z ω => srcMeanInt κ ρL ρR r W VL VR c σ E t z ω)
    (fun t => (measurable_srcInt_wordStop hE hc hadm hG0 hG hS hA0 hAG k t).1)
    (integrable_srcBox_indicator r (meanSrcBound κ ρL ρR r * |m|)) (ae_of_all _ fun z t ω => ?_)
    (ae_of_all _ fun z s t hst S' hS' => ?_)
  · -- the bound
    by_cases hω : ω ∈ E
    · by_cases hz : 0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r
      · rw [indicator_of_mem (show z ∈ srcBox r from hz.2)]
        simp only [srcMeanInt, hω, ↓reduceIte, abs_mul]
        exact mul_le_mul ((hG ω (hAG hω.1)).abs_couplingMean_le (hadm ω)
          ((min_le_right _ _).trans (wordStop_le k ω)) hz.1 hz.2.1)
          ((hAm ω hω.1 z).trans (le_abs_self m)) (abs_nonneg _) hM0
      · simp only [srcMeanInt, hω, ↓reduceIte, vSrcW_eq_zero_of_not _ hz, mul_zero, abs_zero]
        exact hg0 z
    · simp only [srcMeanInt, hω, ↓reduceIte, abs_zero]; exact hg0 z
  · -- the martingale property at a point
    by_cases hz : 0 < z.im ∧ 6 * r ≤ ‖z‖
    · obtain ⟨M, hM, hMae⟩ := exists_martingale_couplingMean_on hE hκ hE0 hσ
        (fun ω hω => wordStop_of_notMem hω) (half_pos hz.1) (half_le_self hz.1.le) (Nat.cast_nonneg k)
        (by positivity : (0 : ℝ) ≤ r ^ 2 / 64)
        (ae_of_all _ fun ω hω => protect_wordStop hadm hG hAG hω hz.1 hz.2) (bheProc κ ρL ρR W VL VR)
        (fun ω s => isBoundedHarmonicExtension_bheProc κ ρL ρR ω s)
      have hfm : Measurable[nullAugmented 𝓕 P 0] (fun ω => if ω ∈ E then vSrcW κ ρL ρR r (c ω) z else 0) :=
        Measurable.ite hE0 ((measurable_vSrcW κ ρL ρR r).comp ((measurable_word_null hc 0).prodMk measurable_const))
          measurable_const
      have hfC : ∀ ω, |(fun ω => if ω ∈ E then vSrcW κ ρL ρR r (c ω) z else 0) ω| ≤ |m| := fun ω => by
        by_cases hω : ω ∈ E
        · simp only [hω, ↓reduceIte]; exact (hAm ω hω.1 z).trans (le_abs_self m)
        · simp only [hω, ↓reduceIte, abs_zero]; exact abs_nonneg m
      have hfM := martingale_mul_of_zero hM hfm.stronglyMeasurable hfC
      have hY : ∀ u, (fun ω => srcMeanInt κ ρL ρR r W VL VR c σ E u z ω) =ᵐ[P]
          fun ω => (if ω ∈ E then vSrcW κ ρL ρR r (c ω) z else 0) * M u ω := fun u => by
        filter_upwards [hMae] with ω hω
        by_cases hωE : ω ∈ E
        · simp only [srcMeanInt, hωE, ↓reduceIte, hω hωE u]; ring
        · simp only [srcMeanInt, hωE, ↓reduceIte, zero_mul]
      rw [integral_congr_ae (ae_restrict_of_ae (hY s)), integral_congr_ae (ae_restrict_of_ae (hY t))]
      exact hfM.setIntegral_eq hst hS'
    · have h0 : ∀ u ω, srcMeanInt κ ρL ρR r W VL VR c σ E u z ω = 0 := fun u ω => by
        simp only [srcMeanInt, vSrcW_eq_zero_of_not _ (fun h => hz ⟨h.1, h.2.1⟩), mul_zero, ite_self]
      simp only [h0]

include hadm hG hAG in
/-- On the localization event, `∫₀^{t∧σ} Im(2/f_u(z)) du = Im f_{t∧σ}(z) − Im z` at every point of the source region. -/
theorem integral_im_two_div_wordStop {k : ℕ} {ω : Ω} (hω : ω ∈ wordEvent A c k) {z : ℂ}
    (hz : 0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r) (t : ℝ≥0) :
    ∫ s in (0 : ℝ)..((min t (wordStop W VL VR B S G A c r k ω) : ℝ≥0) : ℝ),
        (2 / fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im =
      (fwdMap (rpath (W · ω)) (min t (wordStop W VL VR B S G A c r k ω) : ℝ≥0) z).im - z.im := by
  set σ := wordStop W VL VR B S G A c r k
  obtain ⟨n, hn⟩ := (eventually_mem_srcCut hz).exists
  have hgt := isGoodTest_wordStop hadm hG hAG (ρL := ρL) (ρR := ρR) (κ := κ) hω n
  have hφH : tsupport (srcCutInd r n) ⊆ H := by rw [tsupport_srcCutInd]; exact srcCut_subset_H r n
  have hz' : z ∈ tsupport (srcCutInd r n) := by rwa [tsupport_srcCutInd]
  have hrI : ((min t (σ ω) : ℝ≥0) : ℝ) ∈ Icc 0 (σ ω : ℝ) :=
    ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_right _ _⟩
  have hint := integral_im_two_div_fwdMap hgt.continuous_clampPath (σ ω).coe_nonneg
    ((hgt.isProtected hφH) z hz').1 hrI
  have hcl : ∀ v : ℝ, v ≤ σ ω → fwdMap (clampPath W σ ω) v z = fwdMap (rpath (W · ω)) v z :=
    fun v hv => by rw [fwdMap_clampPath hv]
  rw [hcl _ hrI.2] at hint
  rw [← hint]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le (NNReal.coe_nonneg _)] at hv
  have h := hcl v (hv.2.trans hrI.2)
  exact congrArg (fun f => (2 / f).im) h.symm

include hE hc hadm hG0 hG hS hA0 hAG in
/-- **The localized stopped cross process at level `k` is a martingale** (integrated `d⟨𝔥(z), B⟩ = Im(2/f(z)) dt`). -/
theorem martingale_srcCrossW_wordStop [IsProbabilityMeasure P] (hκ : 0 < κ) (hr0 : 0 < r) {m : ℝ}
    (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) (k : ℕ) :
    Martingale (srcCrossW κ ρL ρR r W VL VR B c (wordStop W VL VR B S G A c r k) (wordEvent A c k))
      (nullAugmented 𝓕 P) P := by
  set σ := wordStop W VL VR B S G A c r k with hσdef
  set E := wordEvent A c k with hEdef
  have hE0 : MeasurableSet[nullAugmented 𝓕 P 0] E := measurableSet_wordEvent hA0 (measurable_word_null hc 0) k
  have hσ := isStoppingTime_wordStop hE hc hadm hG0 hG hS hA0 (ρL := ρL) (ρR := ρR) (κ := κ) k
  have hM0 : 0 ≤ meanSrcBound κ ρL ρR r := by
    unfold meanSrcBound Coupling.meanHarmonicBound; positivity
  set K := |m| * (meanSrcBound κ ρL ρR r * k + 7 * r) with hK
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg m) (by positivity)
  have hg0 : ∀ z, 0 ≤ (srcBox r).indicator (fun _ => K) z := fun z => Set.indicator_nonneg (fun _ _ => hK0) z
  refine martingale_integral_of_forall (μ := volume)
    (Y := fun t z ω => srcCrossInt κ ρL ρR r W VL VR B c σ E t z ω)
    (fun t => (measurable_srcInt_wordStop hE hc hadm hG0 hG hS hA0 hAG k t).2)
    (integrable_srcBox_indicator r K) (ae_of_all _ fun z t ω => ?_)
    (ae_of_all _ fun z s t hst S' hS' => ?_)
  · -- the bound
    by_cases hω : ω ∈ E
    · by_cases hz : 0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r
      · rw [indicator_of_mem (show z ∈ srcBox r from hz.2)]
        have hg := hG ω (hAG hω.1)
        have hτ : min t (σ ω) ≤ S ω := (min_le_right _ _).trans (wordStop_le k ω)
        have hcm := hg.abs_couplingMean_le (hadm ω) hτ hz.1 hz.2.1
        obtain ⟨-, hlo, hhi⟩ := hg.protect (hadm ω) hτ hz.1 hz.2.1
        have hB := (protect_wordStop hadm hG hAG hω hz.1 hz.2.1).2.2.2.2 _ (min_le_right t (σ ω))
        have hv := (hAm ω hω.1 z).trans (le_abs_self m)
        have hf : |(fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im| ≤ 7 * r := by
          rw [abs_le]; constructor <;> linarith [Complex.im_le_norm z]
        simp only [srcCrossInt, hω, ↓reduceIte, abs_mul]
        refine mul_le_mul hv ?_ (abs_nonneg _) (abs_nonneg m)
        calc |couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
              (bheProc κ ρL ρR W VL VR ω (min t (σ ω))) z * B (min t (σ ω)) ω -
              ((fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im)|
            ≤ |couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
              (bheProc κ ρL ρR W VL VR ω (min t (σ ω))) z| * |B (min t (σ ω)) ω| +
              |(fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im| := by
                rw [← abs_mul]; exact abs_sub _ _
          _ ≤ meanSrcBound κ ρL ρR r * k + 7 * r :=
                add_le_add (mul_le_mul hcm hB.2.1 (abs_nonneg _) hM0) hf
      · simp only [srcCrossInt, hω, ↓reduceIte, vSrcW_eq_zero_of_not _ hz, zero_mul, abs_zero]
        exact hg0 z
    · simp only [srcCrossInt, hω, ↓reduceIte, abs_zero]; exact hg0 z
  · -- the martingale property at a point
    by_cases hz : 0 < z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r
    · obtain ⟨M, hM, hMae⟩ := exists_martingale_couplingMean_mul_B_on hE hκ hE0 hσ
        (fun ω hω => wordStop_of_notMem hω) (half_pos hz.1) (half_le_self hz.1.le) (Nat.cast_nonneg k)
        (by positivity : (0 : ℝ) ≤ r ^ 2 / 64)
        (ae_of_all _ fun ω hω => protect_wordStop hadm hG hAG hω hz.1 hz.2.1) (bheProc κ ρL ρR W VL VR)
        (fun ω s => isBoundedHarmonicExtension_bheProc κ ρL ρR ω s)
      have hfm : Measurable[nullAugmented 𝓕 P 0] (fun ω => if ω ∈ E then vSrcW κ ρL ρR r (c ω) z else 0) :=
        Measurable.ite hE0 ((measurable_vSrcW κ ρL ρR r).comp ((measurable_word_null hc 0).prodMk measurable_const))
          measurable_const
      have hfC : ∀ ω, |(fun ω => if ω ∈ E then vSrcW κ ρL ρR r (c ω) z else 0) ω| ≤ |m| := fun ω => by
        by_cases hω : ω ∈ E
        · simp only [hω, ↓reduceIte]; exact (hAm ω hω.1 z).trans (le_abs_self m)
        · simp only [hω, ↓reduceIte, abs_zero]; exact abs_nonneg m
      have hfM := martingale_mul_of_zero hM hfm.stronglyMeasurable hfC
      have hY : ∀ u, (fun ω => srcCrossInt κ ρL ρR r W VL VR B c σ E u z ω) =ᵐ[P]
          fun ω => (if ω ∈ E then vSrcW κ ρL ρR r (c ω) z else 0) * M u ω := fun u => by
        filter_upwards [hMae] with ω hω
        by_cases hωE : ω ∈ E
        · simp only [srcCrossInt, hωE, ↓reduceIte, hω hωE u]
          rw [integral_im_two_div_wordStop hadm hG hAG hωE hz u]
        · simp only [srcCrossInt, hωE, ↓reduceIte, zero_mul]
      rw [integral_congr_ae (ae_restrict_of_ae (hY s)), integral_congr_ae (ae_restrict_of_ae (hY t))]
      exact hfM.setIntegral_eq hst hS'
    · have h0 : ∀ u ω, srcCrossInt κ ρL ρR r W VL VR B c σ E u z ω = 0 := fun u ω => by
        simp only [srcCrossInt, vSrcW_eq_zero_of_not _ hz, zero_mul, ite_self]
      simp only [h0]

include hadm hG hAG in
/-- On `A`, the localized integrands eventually agree with the integrands at the local stop. -/
theorem eventually_srcInt_wordStop_eq (t : ℝ≥0) (ω : Ω) :
    ∀ᶠ k : ℕ in atTop, (∀ z, srcMeanInt κ ρL ρR r W VL VR c (wordStop W VL VR B S G A c r k) (wordEvent A c k) t z ω =
      srcMeanInt κ ρL ρR r W VL VR c S A t z ω) ∧
      (∀ z, srcCrossInt κ ρL ρR r W VL VR B c (wordStop W VL VR B S G A c r k) (wordEvent A c k) t z ω =
      srcCrossInt κ ρL ρR r W VL VR B c S A t z ω) := by
  by_cases hω : ω ∈ A
  · filter_upwards [eventually_wordStop_eq hadm hG hAG hω] with k hk
    simp only [srcMeanInt, srcCrossInt, hk.1, hω, ↓reduceIte, hk.2, implies_true, and_self]
  · refine Eventually.of_forall fun k => ?_
    have hk : ω ∉ wordEvent A c k := fun h => hω h.1
    simp only [srcMeanInt, srcCrossInt, hk, hω, ↓reduceIte, implies_true, and_self]

include hE hc hadm hG0 hG hS hA0 hAG in
/-- **The tested source mean of a random word through the local stop is a martingale** (localized on `A`, where the
source is bounded). -/
theorem martingale_srcMeanW [IsProbabilityMeasure P] (hκ : 0 < κ) (hr0 : 0 < r) {m : ℝ}
    (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) :
    Martingale (srcMeanW κ ρL ρR r W VL VR c S A) (nullAugmented 𝓕 P) P := by
  set Yk : ℕ → ℝ≥0 → Ω → ℝ := fun k =>
    srcMeanW κ ρL ρR r W VL VR c (wordStop W VL VR B S G A c r k) (wordEvent A c k) with hYk
  have hmart : ∀ k, Martingale (Yk k) (nullAugmented 𝓕 P) P := fun k =>
    martingale_srcMeanW_wordStop hE hc hadm hG0 hG hS hA0 hAG hκ hr0 hAm k
  set K := meanSrcBound κ ρL ρR r * |m| * volume.real (srcBox r) with hK
  have hbd : ∀ k t ω, |Yk k t ω| ≤ K := fun k t ω => by
    have hpt : ∀ z, ‖srcMeanInt κ ρL ρR r W VL VR c (wordStop W VL VR B S G A c r k) (wordEvent A c k) t z ω‖ ≤
        (srcBox r).indicator (fun _ => meanSrcBound κ ρL ρR r * |m|) z := fun z => by
      rw [Real.norm_eq_abs]
      exact abs_srcMeanInt_le hadm hG hAG hAm (wordStop_le (W := W) (VL := VL) (VR := VR) (B := B) (G := G) k)
        (fun _ (h : _ ∈ wordEvent A c k) => h.1) t z ω
    have h := norm_integral_le_of_norm_le (integrable_srcBox_indicator r _) (ae_of_all _ hpt)
    rw [integral_srcBox_indicator, Real.norm_eq_abs] at h
    exact h
  have hconv : ∀ t ω, Tendsto (fun k => Yk k t ω) atTop (𝓝 (srcMeanW κ ρL ρR r W VL VR c S A t ω)) :=
    fun t ω => tendsto_const_nhds.congr' ((eventually_srcInt_wordStop_eq hadm hG hAG t ω).mono fun k hk => by
      simp only [hYk, srcMeanW, hk.1])
  have hYm : ∀ k t, Measurable (Yk k t) := fun k t =>
    (((hmart k).1 t).mono ((nullAugmented 𝓕 P).le t)).measurable
  have hlimm : ∀ t, Measurable (srcMeanW κ ρL ρR r W VL VR c S A t) := fun t =>
    measurable_of_tendsto_metrizable (fun k => hYm k t) (tendsto_pi_nhds.2 (hconv t))
  refine martingale_of_tendsto_of_null (fun t N hN h0 => measurableSet_nullAugmented_of_null hN h0 t)
    hmart (fun k t => MemLp.of_bound (hYm k t).aestronglyMeasurable K (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hbd k t ω))
    (fun t => ⟨K ^ 2, fun k => by
      calc ∫ ω, Yk k t ω ^ 2 ∂P ≤ ∫ _, K ^ 2 ∂P := integral_mono_of_nonneg
            (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _) (ae_of_all _ fun ω => by
              show Yk k t ω ^ 2 ≤ K ^ 2
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd k t ω) 2)
        _ = K ^ 2 := by simp⟩)
    (fun t => ae_of_all _ (hconv t)) hlimm (fun t => Integrable.of_bound (hlimm t).aestronglyMeasurable K
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hconv t ω))
          fun k => hbd k t ω))

include hE hc hadm hG0 hG hS hA0 hAG in
/-- **The cross process of the tested source of a random word through the local stop is a martingale** (localized on
`A`, where the source is bounded). -/
theorem martingale_srcCrossW [IsProbabilityMeasure P] (hκ : 0 < κ) (hr0 : 0 < r) (hGc : P Gᶜ = 0) {m : ℝ}
    (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) :
    Martingale (srcCrossW κ ρL ρR r W VL VR B c S A) (nullAugmented 𝓕 P) P := by
  have hGm : MeasurableSet G := (nullAugmented 𝓕 P).le 0 G hG0
  have hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[nullAugmented 𝓕 P t] N :=
    fun t N hN h0 => measurableSet_nullAugmented_of_null hN h0 t
  obtain ⟨hB', hB'c⟩ := isFilteredBrownianReal_modify hE.1 hGm hGc fun ω hω => (hG ω hω).2.1
  set B' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then B t ω else 0 with hB'def
  have hBB' : ∀ ω ∈ G, ∀ u, B u ω = B' u ω := fun ω hω u => by simp [hB'def, hω]
  have hnoise : ∀ ω, WholeField.noiseOn B' G 0 ω = 0 := fun ω => by
    by_cases hω : ω ∈ G
    · simp [WholeField.noiseOn, hB'def, hω, (hG ω hω).2.2.1]
    · simp [WholeField.noiseOn, hω]
  have hBL2 : ∀ {ρ : Ω → ℝ≥0}, IsStoppingTime (nullAugmented 𝓕 P) (fun ω => (ρ ω : WithTop ℝ≥0)) → ∀ t,
      MemLp (fun ω => B' (min t (ρ ω)) ω) 2 P ∧ ∫ ω, B' (min t (ρ ω)) ω ^ 2 ∂P ≤ t := fun hρ t => by
    obtain ⟨h1, h2⟩ := integral_sq_stoppedNoise_le hB' hnull hGm hGc (fun ω _ => hB'c ω) hρ t
    simp only [hnoise, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero, add_zero] at h2
    exact ⟨h1, h2⟩
  set Yk : ℕ → ℝ≥0 → Ω → ℝ := fun k =>
    srcCrossW κ ρL ρR r W VL VR B c (wordStop W VL VR B S G A c r k) (wordEvent A c k) with hYk
  have hmart : ∀ k, Martingale (Yk k) (nullAugmented 𝓕 P) P := fun k =>
    martingale_srcCrossW_wordStop hE hc hadm hG0 hG hS hA0 hAG hκ hr0 hAm k
  have hM0 : 0 ≤ meanSrcBound κ ρL ρR r := by
    unfold meanSrcBound Coupling.meanHarmonicBound; positivity
  set a := |m| * meanSrcBound κ ρL ρR r * volume.real (srcBox r) with ha
  set b := |m| * (7 * r) * volume.real (srcBox r) with hb
  have ha0 : 0 ≤ a := mul_nonneg (mul_nonneg (abs_nonneg m) hM0) measureReal_nonneg
  have hb0 : 0 ≤ b := mul_nonneg (mul_nonneg (abs_nonneg m) (by positivity)) measureReal_nonneg
  -- the pointwise bound through a stop below the local stop
  have hbdσ : ∀ {σ : Ω → ℝ≥0} {E : Set Ω}, (∀ ω, σ ω ≤ S ω) → E ⊆ A → ∀ t ω,
      |srcCrossW κ ρL ρR r W VL VR B c σ E t ω| ≤ a * |B' (min t (σ ω)) ω| + b := by
    intro σ E hσS hEA t ω
    have hpt : ∀ z, ‖srcCrossInt κ ρL ρR r W VL VR B c σ E t z ω‖ ≤
        (srcBox r).indicator (fun _ => |m| * (meanSrcBound κ ρL ρR r * |B (min t (σ ω)) ω| + 7 * r)) z :=
      fun z => by rw [Real.norm_eq_abs]; exact abs_srcCrossInt_le hadm hG hAG hAm hσS hEA t z ω
    have h := norm_integral_le_of_norm_le (integrable_srcBox_indicator r _) (ae_of_all _ hpt)
    rw [integral_srcBox_indicator, Real.norm_eq_abs] at h
    by_cases hω : ω ∈ E
    · rw [hBB' ω (hAG (hEA hω))] at h
      refine h.trans (le_of_eq ?_)
      rw [ha, hb]; ring
    · have h0 : srcCrossW κ ρL ρR r W VL VR B c σ E t ω = 0 := by
        simp [srcCrossW, srcCrossInt, hω]
      rw [h0, abs_zero]; positivity
  have hbd : ∀ k t ω, |Yk k t ω| ≤ a * |B' (min t (wordStop W VL VR B S G A c r k ω)) ω| + b := fun k =>
    hbdσ (wordStop_le (W := W) (VL := VL) (VR := VR) (B := B) (G := G) k)
      (fun _ (h : _ ∈ wordEvent A c k) => h.1)
  have hconv : ∀ t ω, Tendsto (fun k => Yk k t ω) atTop (𝓝 (srcCrossW κ ρL ρR r W VL VR B c S A t ω)) :=
    fun t ω => tendsto_const_nhds.congr' ((eventually_srcInt_wordStop_eq hadm hG hAG t ω).mono fun k hk => by
      simp only [hYk, srcCrossW, hk.2])
  have hYm : ∀ k t, Measurable (Yk k t) := fun k t =>
    (((hmart k).1 t).mono ((nullAugmented 𝓕 P).le t)).measurable
  have hlimm : ∀ t, Measurable (srcCrossW κ ρL ρR r W VL VR B c S A t) := fun t =>
    measurable_of_tendsto_metrizable (fun k => hYm k t) (tendsto_pi_nhds.2 (hconv t))
  have hσk := fun k => isStoppingTime_wordStop hE hc hadm hG0 hG hS hA0 (ρL := ρL) (ρR := ρR) (κ := κ) k
  have hL2 : ∀ k t, MemLp (Yk k t) 2 P := fun k t => by
    have hg : MemLp (fun ω => a * ‖B' (min t (wordStop W VL VR B S G A c r k ω)) ω‖ + b) 2 P :=
      (((hBL2 (hσk k) t).1.norm.const_mul a).add (memLp_const b))
    refine hg.of_le (hYm k t).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (mul_nonneg ha0 (abs_nonneg _)) hb0)]
    exact hbd k t ω
  have hbound : ∀ t, ∃ M, ∀ k, ∫ ω, Yk k t ω ^ 2 ∂P ≤ M := fun t =>
    ⟨2 * a ^ 2 * t + 2 * b ^ 2, fun k => by
      have hBi : Integrable (fun ω => B' (min t (wordStop W VL VR B S G A c r k ω)) ω ^ 2) P :=
        (hBL2 (hσk k) t).1.integrable_sq
      have hsq : ∀ ω, Yk k t ω ^ 2 ≤
          2 * a ^ 2 * B' (min t (wordStop W VL VR B S G A c r k ω)) ω ^ 2 + 2 * b ^ 2 := fun ω => by
        have h1 := hbd k t ω
        have h2 : Yk k t ω ^ 2 ≤ (a * |B' (min t (wordStop W VL VR B S G A c r k ω)) ω| + b) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        nlinarith [sq_abs (B' (min t (wordStop W VL VR B S G A c r k ω)) ω),
          sq_nonneg (a * |B' (min t (wordStop W VL VR B S G A c r k ω)) ω| - b)]
      calc ∫ ω, Yk k t ω ^ 2 ∂P
          ≤ ∫ ω, (2 * a ^ 2 * B' (min t (wordStop W VL VR B S G A c r k ω)) ω ^ 2 + 2 * b ^ 2) ∂P :=
            integral_mono (hL2 k t).integrable_sq ((hBi.const_mul _).add (integrable_const _)) hsq
        _ = 2 * a ^ 2 * ∫ ω, B' (min t (wordStop W VL VR B S G A c r k ω)) ω ^ 2 ∂P + 2 * b ^ 2 := by
            rw [integral_add (hBi.const_mul _) (integrable_const _), integral_const_mul]; simp
        _ ≤ 2 * a ^ 2 * t + 2 * b ^ 2 := by
            gcongr
            exact (hBL2 (hσk k) t).2⟩
  have hlimi : ∀ t, Integrable (srcCrossW κ ρL ρR r W VL VR B c S A t) P := fun t => by
    have hg : Integrable (fun ω => a * ‖B' (min t (S ω)) ω‖ + b) P :=
      ((((hBL2 hS t).1.integrable one_le_two).norm.const_mul a).add (integrable_const b))
    refine hg.mono' (hlimm t).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hbdσ (fun _ => le_rfl) subset_rfl t ω
  exact martingale_of_tendsto_of_null hnull hmart hL2 hbound (fun t => ae_of_all _ (hconv t)) hlimm hlimi

end Mart

end LocalExt

end InteractingSLE
