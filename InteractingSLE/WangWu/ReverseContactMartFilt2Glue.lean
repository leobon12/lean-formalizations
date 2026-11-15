/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartFilt2Markov
import InteractingSLE.WangWu.ReverseContactBdryGlue
import InteractingSLE.Spec.Coupling.WholeField2Hull
import InteractingSLE.Spec.Sec4.Special4History

/-!
# The two stopped slits on the glued space with both histories retained

Packet PROVE-WW-B18 (step B3 of the contact step, the field side). PROVE-WW-B12 proved that on the glued space
`P ⊗ k(h)` of the contact step the union `A ∪ G` of the forward slit `A = α((0, t])` and the reflected reverse slit
`G = R(β((0, s]))` is a local set of the centred field (`isLocalSet_twoSlit_glue`). The conditional law of the field
given the **filtration of the image word** needs more: the stopped forward history and the stopped reverse history
must be retained in the conditioning (Wang–Wu, proof of Proposition 4.18: "conditionally on the stopped reverse line
the forward line before contact is `SLE₄(ρ)` in `ℍ \ G`"; Astra, shortcut note §4.1: "Let `E` retain the reverse
history used for the slit chart, and let `G_t` be the usual augmentation of `E` together with the mapped forward
history"). This file proves the history-marked version:

* `isHistoryAvoidanceLocal_reflect_hull`: for a frozen coupling, the **reflected** hull `R(K_τ)` satisfies the
  history-marked avoidance criterion (Aux. lemma 18) for the reflected field `R_* h − D` (any harmonic `D`) and the
  marks `𝓕_τ` (the coding theorem `isHistoryAvoidanceLocal_of_capacity` with the reflected clock `hcap(R(·))/2`);
* `stopSigma t`: the σ-algebra of the history stopped at the fixed time `t` (`stopHistory`);
* **`isHistoryAvoidanceLocal_twoSlit_glue`**: on the glued space, the union of the forward slit at the rational
  time `t` and the reflected reverse slit at `s` satisfies the history-marked avoidance criterion for the centred field
  and the marks `σ(forward history stopped at t) ∨ σ(reverse history stopped at s)` (the forward and reverse criteria
  transported along equal joint laws, `isHistoryAvoidanceLocal_of_map_eq`, and glued by the conditional independence of
  the glued sample, `isHistoryAvoidanceLocal_union`);
* **`exists_condExp_twoSlit_glue_history`**: hence (Aux. lemma 18's germ law, `exists_condExp_germSigma_history`) the
  conditional characteristic function of the centred field given the germ of the union and both stopped histories is
  `e^{iM} e^{−σ²_{ℍ∖(A∪G)}(φ)/2}` with a germ-measurable mean `M`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull fwdMap)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open WholeField LocalSets LawUnique Coupling

/-! ### The reflected hull of a frozen coupling -/

section Reflect

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **History marking of the reflected hull** `R(K_τ)` for the reflected field (the reflected form of
`WholeField.isHistoryAvoidanceLocal_hull`): for a frozen coupling with `κ > 0`, a stopping time `τ < ζ` of the
driving filtration, a harmonic `D` and a hitting-measurable version `A` of `R(K_τ)`, the field `R_* h − D` satisfies
the history-marked avoidance criterion for `A` and the marks `𝓕_τ`. -/
theorem isHistoryAvoidanceLocal_reflect_hull (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {D : DistOn upperHalfPlaneOpens} (hD : IsHarmonicDistOn D H)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = negInv '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    IsHistoryAvoidanceLocal hτ.measurableSpace A (fun ω => reflectField (h ω) - D) P := by
  obtain ⟨hE, hhm, -, hX', hker⟩ := hC
  have hh0m : Measurable fun ω => reflectField (h ω) - D :=
    (measurable_sub_dist D).comp (measurable_reflectField.comp hhm)
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτζ] with ω hp hlt
      rw [IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    obtain ⟨_, h⟩ := hF.exists
    exact h
  · have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
    obtain ⟨σ, hσ, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B) (κ := κ)
      (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
      (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
      hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
    refine isHistoryAvoidanceLocal_of_capacity
      (K := fun t ω => negInv '' fwdHull (fun s : ℝ => W s.toNNReal ω) t) hh0m
      (Φ := fun S => hullClock (negInv '' S)) (measurable_hullClock.comp measurable_image_negInv) ?_ hσ ?_ hτ
      hτζ hA hAK
    · filter_upwards [hE.2.2.2.2] with ω hp t ht
      simp only [image_image, negInv_negInv', image_id']
      exact hullClock_fwdHull_rpath hp.2.2.2.1 hp.1 ht
    · intro S hS hSζ
      have hloc := IsLocalSet.sub_dist (IsLocalSet.reflect (hker S hS hSζ).1) hD
      obtain ⟨A', hA'm, hA'e, hA'loc⟩ := IsLocalSet.exists_measurable_version hloc hh0m
      exact ⟨A', hA'm, hA'e, LocalSets.IsLocalSet.isMarkedAvoidanceLocal hh0m hA'm hA'loc⟩

end Reflect

/-! ### The σ-algebra of a history stopped at a fixed time -/

section Stop

/-- **The σ-algebra of the history stopped at the fixed time `t`.** -/
@[instance_reducible]
def stopSigma {nL nR : ℕ} (t : ℝ≥0) : MeasurableSpace (HistorySpace nL nR) :=
  MeasurableSpace.comap (Sec4.stopHistory (fun _ => t)) inferInstance

theorem stopSigma_le {nL nR : ℕ} (t : ℝ≥0) :
    stopSigma (nL := nL) (nR := nR) t ≤ (inferInstance : MeasurableSpace (HistorySpace nL nR)) :=
  (Sec4.measurable_stopHistory measurable_const).comap_le

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The killed history stopped at `t` is known at time `t` of the driving filtration. -/
theorem comap_stopSigma_le (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    MeasurableSpace.comap (killedHistory W VL VR ζ) (stopSigma t) ≤ drivingFiltration P hX t := by
  have hm := Sec4.measurable_stopHistory_killedHistory (s := fun _ => t) hX
    (isStoppingTime_const (drivingFiltration P hX) t)
  have h2 := IsStoppingTime.measurableSpace_const (drivingFiltration P hX) t
  rw [stopSigma, MeasurableSpace.comap_comp]
  exact (hm.mono h2.le le_rfl).comap_le

end Stop

/-! ### The two stopped slits on the glued space -/

section Glue

variable {rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- The marks of the glued space: the forward history stopped at `t` and the reverse history stopped at `s`. -/
@[instance_reducible]
def twoSlitMarks (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (t s : ℚ) :
    MeasurableSpace (Ω × HistorySpace 1 1) :=
  MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => killedHistory W VL VR ζ p.1)
      (stopSigma (t : ℝ).toNNReal) ⊔
    MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => p.2) (stopSigma (s : ℝ).toNNReal)

/-- **The two stopped slits with both stopped histories retained** (Proposition 3.7 with Aux. lemma 18's marks, on the
glued space of the contact step). Let `hC` be a frozen coupling of the two-seed word `(r_L; r_R)`, `r_L, r_R ≥ 0`, and
`hC₂` one of `(r_R; r_L)` whose reflected field has the law of `h`, and let `k` be a regular conditional law of the
reverse killed history given the reflected field. On `P ⊗ k(h)`, for rational `t, s > 0`, the union of the forward slit
at `t` and the reflected reverse slit at `s` (read from the histories) satisfies the history-marked avoidance criterion
for the centred field `h − u₀` and the marks `σ(forward history stopped at t) ∨ σ(reverse history stopped at s)`. -/
theorem isHistoryAvoidanceLocal_twoSlit_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) :
    IsHistoryAvoidanceLocal (twoSlitMarks W VL VR ζ t s)
      (fun p : Ω × HistorySpace 1 1 => histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => centredField h u₀ p.1) (glueMeasure P k h hC.2.1) := by
  set μ := glueMeasure P k h hC.2.1 with hμ
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hhm := hC.2.1
  have hh₂m := hC₂.2.1
  set D := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hD
  have hDh : IsHarmonicDistOn D H := isHarmonicDistOn_smoothDist hu₀.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hY₂m : Measurable (killedHistory W₂ VL₂ VR₂ ζ₂) := measurable_killedHistory hX₂
  have hXm : Measurable (centredField h u₀) := measurable_centredField hhm u₀
  -- the forward slit on `Ω`
  have hτ := isStoppingTime_const (drivingFiltration P hX) (t : ℝ).toNNReal
  have hτζ : ∀ᵐ ω ∂P, ((((t : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1]
      with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hfwd := isHistoryAvoidanceLocal_hull hC (by norm_num) hu₀ hX hτ hτζ
    (A := fun ω => histHull t (killedHistory W VL VR ζ ω)) ((measurable_histHull t).comp hYm)
    (by
      filter_upwards [ae_histHull_eq_fwdHull hL hR hC.1 ht] with ω hω
      rw [hω, WithTop.untopD_coe])
  have hfwd' := IsHistoryAvoidanceLocal.mono_marks hfwd ((comap_stopSigma_le (P := P) hX (t : ℝ).toNNReal).trans
    (IsStoppingTime.measurableSpace_const _ _).symm.le)
  have hlaw₁ : μ.map (fun p : Ω × HistorySpace 1 1 => (centredField h u₀ p.1, killedHistory W VL VR ζ p.1)) =
      P.map (fun ω => (centredField h u₀ ω, killedHistory W VL VR ζ ω)) := by
    rw [show (fun p : Ω × HistorySpace 1 1 => (centredField h u₀ p.1, killedHistory W VL VR ζ p.1)) =
        (fun ω => (centredField h u₀ ω, killedHistory W VL VR ζ ω)) ∘ Prod.fst from rfl,
      ← Measure.map_map (hXm.prodMk hYm) measurable_fst, hμ, glueMeasure_fst k hhm]
  have hA₁ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma (t : ℝ).toNNReal) hXm hYm
    (hXm.comp measurable_fst) (hYm.comp measurable_fst) hlaw₁ (measurable_histHull t) (stopSigma_le _) hfwd'
  -- the reflected reverse slit on `Ω₂`
  have hτ₂ := isStoppingTime_const (drivingFiltration P₂ hX₂) (s : ℝ).toNNReal
  have hτζ₂ : ∀ᵐ ω ∂P₂, ((((s : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by
    filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hR hL)
      hC₂.1] with ω hω
    rw [hω.1]
    exact ENNReal.coe_lt_top
  have hrev := isHistoryAvoidanceLocal_reflect_hull hC₂ (by norm_num) hDh hX₂ hτ₂ hτζ₂
    (A := fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
    ((measurable_image_negInv.comp (measurable_histHull s)).comp hY₂m)
    (by
      filter_upwards [ae_histHull_eq_fwdHull hR hL hC₂.1 hs] with ω hω
      rw [hω, WithTop.untopD_coe])
  have hrev' := IsHistoryAvoidanceLocal.mono_marks hrev ((comap_stopSigma_le (P := P₂) hX₂ (s : ℝ).toNNReal).trans
    (IsStoppingTime.measurableSpace_const _ _).symm.le)
  have hX₂m : Measurable fun ω => reflectField (h₂ ω) - D :=
    (measurable_sub_dist D).comp (measurable_reflectField.comp hh₂m)
  have hlaw₂ : μ.map (fun p : Ω × HistorySpace 1 1 => (centredField h u₀ p.1, p.2)) =
      P₂.map (fun ω => (reflectField (h₂ ω) - D, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
    have hT : Measurable fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1 - D, q.2) :=
      ((measurable_sub_dist D).comp measurable_fst).prodMk measurable_snd
    have hpair : Measurable fun p : Ω × HistorySpace 1 1 => (h p.1, p.2) :=
      (hhm.comp measurable_fst).prodMk measurable_snd
    have hpair₂ : Measurable fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
      (measurable_reflectField.comp hh₂m).prodMk hY₂m
    rw [show (fun p : Ω × HistorySpace 1 1 => (centredField h u₀ p.1, p.2)) =
        (fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1 - D, q.2)) ∘ fun p => (h p.1, p.2) from rfl,
      show (fun ω => (reflectField (h₂ ω) - D, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
        (fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1 - D, q.2)) ∘
          fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω) from rfl,
      ← Measure.map_map hT hpair, ← Measure.map_map hT hpair₂, hμ, glueMeasure_map_pair hhm k, hlaw, hk]
  have hA₂ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma (s : ℝ).toNNReal) hX₂m hY₂m
    (hXm.comp measurable_fst) measurable_snd hlaw₂ (measurable_image_negInv.comp (measurable_histHull s))
    (stopSigma_le _) hrev'
  -- the union
  have hσ : MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => centredField h u₀ p.1) inferInstance =
      MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => h p.1) inferInstance := by
    refine le_antisymm ?_ ?_
    · change MeasurableSpace.comap ((fun f => f - D) ∘ fun p : Ω × HistorySpace 1 1 => h p.1) _ ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_sub_dist D).comap_le
    · calc MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => h p.1) inferInstance
          = MeasurableSpace.comap ((fun f => f + D) ∘ fun p : Ω × HistorySpace 1 1 => centredField h u₀ p.1)
              inferInstance := by
            congr 1; funext p; exact (sub_add_cancel (h p.1) D).symm
        _ ≤ _ := by
            rw [← MeasurableSpace.comap_comp]
            exact MeasurableSpace.comap_mono (Coupling.measurable_add_distOnConst D).comap_le
  have hci := condIndepEv_glue_fst (μ := P) k hhm
  rw [← hσ] at hci
  have hℋ₁ : MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => killedHistory W VL VR ζ p.1)
      (stopSigma (t : ℝ).toNNReal) ≤ MeasurableSpace.comap Prod.fst mΩ := by
    rw [show (fun p : Ω × HistorySpace 1 1 => killedHistory W VL VR ζ p.1) =
      killedHistory W VL VR ζ ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((MeasurableSpace.comap_mono (stopSigma_le _)).trans hYm.comap_le)
  have hℋ₂ : MeasurableSpace.comap (fun p : Ω × HistorySpace 1 1 => p.2) (stopSigma (s : ℝ).toNNReal) ≤
      MeasurableSpace.comap Prod.snd inferInstance :=
    MeasurableSpace.comap_mono (stopSigma_le _)
  exact isHistoryAvoidanceLocal_union measurable_fst.comap_le measurable_snd.comap_le hℋ₁ hℋ₂
    (((measurable_histHull t).comp hYm).comp (comap_measurable Prod.fst))
    (((measurable_image_negInv.comp (measurable_histHull s))).comp (comap_measurable Prod.snd)) hci hA₁ hA₂

theorem twoSlitMarks_le (t s : ℚ) (hX : IsMeasurableKilledDriving W VL VR ζ) :
    twoSlitMarks W VL VR ζ t s ≤ (inferInstance : MeasurableSpace (Ω × HistorySpace 1 1)) := by
  refine sup_le ?_ ?_
  · rw [show (fun p : Ω × HistorySpace 1 1 => killedHistory W VL VR ζ p.1) =
      killedHistory W VL VR ζ ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact (MeasurableSpace.comap_mono ((MeasurableSpace.comap_mono (stopSigma_le _)).trans
      (measurable_killedHistory hX).comap_le)).trans measurable_fst.comap_le
  · exact (MeasurableSpace.comap_mono (stopSigma_le _)).trans measurable_snd.comap_le

/-- **The conditional law of the centred field given the germ of the two stopped slits and both stopped histories**
(Aux. lemma 18's germ law on the glued space): for every test function `φ` there is a germ-measurable `M` with
`M = E[(h − u₀, φ) | 𝒜 ∨ ℋ]` and `E[e^{i (h − u₀, φ)} | 𝒜 ∨ ℋ] = e^{iM} e^{−σ²_{ℍ∖(A∪G)}(φ)/2}`, where `𝒜` is the germ
σ-algebra of `A ∪ G` and `ℋ` the marks `twoSlitMarks`. -/
theorem exists_condExp_twoSlit_glue_history (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) :
    ∃ M : Ω × HistorySpace 1 1 → ℝ,
      Measurable[germSigma (fun p : Ω × HistorySpace 1 1 =>
        histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1)] M ∧
      M =ᵐ[glueMeasure P k h hC.2.1] (glueMeasure P k h hC.2.1)[fun p => centredField h u₀ p.1 φ |
        germSigma (fun p : Ω × HistorySpace 1 1 =>
          histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
          twoSlitMarks W VL VR ζ t s] ∧
      (fun p => Complex.exp (Complex.I * (M p : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (H \ relClosureH
            (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) φ φ) : ℝ) : ℂ))
        =ᵐ[glueMeasure P k h hC.2.1]
        (glueMeasure P k h hC.2.1)[fun p => Complex.exp (Complex.I * (centredField h u₀ p.1 φ : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 1 1 =>
            histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
            twoSlitMarks W VL VR ζ t s] := by
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 1 1 =>
      centredField h u₀ p.1) (glueMeasure P k h hC.2.1) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => centredField h u₀ ω) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hC.2.1) (isZeroBoundaryGFF_centredField hC hu₀)
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2 :=
    measurable_union_hitting (((measurable_histHull t).comp (measurable_killedHistory hX)).comp measurable_fst)
      ((measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd)
  have hAc : ∀ p : Ω × HistorySpace 1 1, histHull t (killedHistory W VL VR ζ p.1) ∪
      negInv '' histHull s p.2 ⊆ H ∧ IsOpen (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪
        negInv '' histHull s p.2)) := by
    intro p
    obtain ⟨h1, h2⟩ := histHull_relClosed t (killedHistory W VL VR ζ p.1)
    obtain ⟨h3, h4⟩ := image_negInv_relClosed (histHull_relClosed s p.2)
    refine ⟨union_subset h1 h3, ?_⟩
    have e : H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) =
        (H \ histHull t (killedHistory W VL VR ζ p.1)) ∩ (H \ negInv '' histHull s p.2) := by
      ext z; simp only [Set.mem_sdiff, mem_inter_iff, mem_union]; tauto
    rw [e]
    exact h2.inter h4
  exact exists_condExp_germSigma_history hF hAm (twoSlitMarks_le t s hX)
    (isHistoryAvoidanceLocal_twoSlit_glue hL hR hC hC₂ hlaw k hk hu₀ ht hs) (Eventually.of_forall hAc) φ

/-- **The conditional characteristic function of the field given the germ of the two stopped slits and both stopped
histories, explicitly** (Proposition 3.7 with retained histories, Proposition 3.8 and PROVE-WW-B14's identification
of the union mean, `ae_union_mean_eq_chartMean_glue`). Almost surely on `{A ∩ G = ∅}`, for `φ` supported in
`ℍ \ (A ∪ G)`, there is an image chain `(W', T)` of `Ψ(A)` (`Ψ = revChart` of the reverse frozen driver) with
`E[e^{i (h, φ)} | 𝒜 ∨ ℋ] = exp(i ∫ chartMean ∘ f'_T ∘ Ψ · φ) · exp(−½ G_{ℍ∖(A∪G)}(φ, φ))`: given the germ of the union
and both stopped histories, the field off the union is the explicit `SLE₄(r_L, −r_L; r_R, −r_R)` mean of the image
slit, pulled back by `Ψ`, plus a zero-boundary GFF on `ℍ \ (A ∪ G)`. -/
theorem ae_condExp_cexp_twoSlit_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
      Disjoint (histHull t (killedHistory W VL VR ζ p.1)) (negInv '' histHull s p.2) →
      tsupport φ ⊆ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) →
      ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
        IsProperArc η' ∧
        fwdHull W' T = revChart (Ito.rpath (frzDrive s p.2)) s '' histHull t (killedHistory W VL VR ζ p.1) ∧
        (glueMeasure P k h hC.2.1)[fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
            germSigma (fun p : Ω × HistorySpace 1 1 =>
              histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
              twoSlitMarks W VL VR ζ t s] p =
          Complex.exp (Complex.I * ((∫ z, chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2)
              (fwdMap W' T (revChart (Ito.rpath (frzDrive s p.2)) s z)) * φ z : ℝ) : ℂ)) *
            ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
              (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) φ φ) : ℝ) : ℂ) := by
  obtain ⟨hX, -⟩ := hC.2.2.2
  set μ := glueMeasure P k h hC.2.1 with hμ
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_twoSlit_glue_history hL hR hC hC₂ hlaw k hk hu₀ ht hs φ
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × HistorySpace 1 1 =>
      centredField h u₀ p.1) μ :=
    isZeroBoundaryGFF_comp_of_map_eq (g := fun ω => centredField h u₀ ω) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hC.2.1) (isZeroBoundaryGFF_centredField hC hu₀)
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2 :=
    measurable_union_hitting (((measurable_histHull t).comp (measurable_killedHistory hX)).comp measurable_fst)
      ((measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd)
  have hloc := isLocalSet_twoSlit_glue hL hR hC hC₂ hlaw k hk hu₀ ht hs
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hF hAm hloc
  have hgM := IsLocalSetMean.ae_eq_condExp_germSigma_sup hF hAm hloc (twoSlitMarks_le t s hX)
    (isHistoryAvoidanceLocal_twoSlit_glue hL hR hC hC₂ hlaw k hk hu₀ ht hs) hg φ
  have hB14 := ae_union_mean_eq_chartMean_glue hL hR hC hC₂ hlaw k hk hu₀ ht hs hg
  -- pulling out the harmonic shift
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have e : (fun p : Ω × HistorySpace 1 1 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (centredField h u₀ p.1 φ : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, centredField_apply h hu₀.1 p.1 φ, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := μ) c (fun p : Ω × HistorySpace 1 1 =>
    Complex.exp (Complex.I * (centredField h u₀ p.1 φ : ℂ))) (germSigma (fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
        twoSlitMarks W VL VR ζ t s)
  rw [← e] at hpull
  filter_upwards [hM1, hM2, hgM, hB14, hpull] with p h1 h2 h3 h4 h5 hdisj hsupp
  obtain ⟨w, hw, hgw, W', hW'c, hW'0, T, hT, η', hη', hprop, hhull, hmean⟩ := h4 hdisj
  refine ⟨W', hW'c, hW'0, T, hT, η', hη', hprop, hhull, ?_⟩
  rw [h5, Pi.smul_apply, ← h2, smul_eq_mul]
  have hMp : M p = ∫ z, w z * φ z := by rw [h1, ← h3, hgw φ hsupp]
  obtain ⟨hsub1, hop1⟩ := histHull_relClosed t (killedHistory W VL VR ζ p.1)
  obtain ⟨hsub2, hop2⟩ := image_negInv_relClosed (histHull_relClosed s p.2)
  have hopen : IsOpen (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) := by
    have e2 : H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) =
        (H \ histHull t (killedHistory W VL VR ζ p.1)) ∩ (H \ negInv '' histHull s p.2) := by
      ext z; simp only [Set.mem_sdiff, mem_inter_iff, mem_union]; tauto
    rw [e2]
    exact hop1.inter hop2
  rw [hMp, relClosureH_eq (union_subset hsub1 hsub2) hopen]
  -- the explicit mean
  have hwi : Integrable fun z => w z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hw z hz).1.continuousAt.continuousWithinAt) φ hsupp
  have hui : Integrable fun z => u₀ z * φ z :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt) φ φ.tsupport_subset
  have hint : (∫ z, chartMean rL rR W' T (frzVL s p.2) (frzVR s p.2)
      (fwdMap W' T (revChart (Ito.rpath (frzDrive s p.2)) s z)) * φ z) =
      (∫ z, w z * φ z) + ∫ z, u₀ z * φ z := by
    rw [← integral_add hwi hui]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · simp only
      rw [← hmean z (hsupp hz)]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero, add_zero]
  rw [hint, hc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Glue

end InteractingSLE.WangWu
