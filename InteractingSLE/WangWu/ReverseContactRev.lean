/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMean
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# The reverse slit mean on the glued space, through the canonical (field, history) space

Packet PROVE-WW-B12. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of
Proposition 4.18 (text dump L1607–1614), step (S3a) for the reverse slit. On the glued space `P ⊗ k(h)` the reverse
history is the second coordinate, while its slit mean is known on the space `Ω₂` of the reverse coupling
(`exists_isLocalSetMean_revSlit_twoSeed`). Both spaces map measure-preservingly onto the canonical space
`RevSpace = (field, history)` (lifted to the universe of the couplings) with the law `law(h) ⊗ k`:

* the glued space by `p ↦ (h p.1, p.2)` (`glueMeasure_map_revProj`), the reverse coupling by
  `ω ↦ (−h₂ ∘ R, killed history)`;
* on `RevSpace` the reflected slit `R(histHull s y)` is a local set of `f − u₀` (law transfer from `Ω₂`), so it has a
  local-set mean `ĝ` (`exists_isLocalSetMean_revSpace`);
* **`exists_isLocalSetMean_revSlit_glue`**: `ĝ` read on the glued space is a local-set mean of the reverse slit
  (`IsLocalSetMean.comp`), and read on `Ω₂` it is, test function by test function, the reflected explicit mean
  `−meanAt(R z) − u₀(z)` (uniqueness of local-set means);
* `ae_glue_of_ae_revSpace`: a **measurable** property of `(ĝ, field, history)` holding almost surely on `Ω₂` holds
  almost surely on the glued space.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open LawUnique
open LocalSets (IsLocalSetMean germSigma)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

/-- **The canonical space of the reverse slit**: a field and a dyadic history, lifted to the universe `u`. -/
abbrev RevSpace : Type u := ULift.{u} (DistOn upperHalfPlaneOpens × HistorySpace 1 1)

/-- The reflected stopped hull read from the history coordinate. -/
def revSlit (s : ℚ) (q : RevSpace.{u}) : Set ℂ := negInv '' histHull s q.down.2

/-- The centred field coordinate. -/
def revField (D : DistOn upperHalfPlaneOpens) (q : RevSpace.{u}) : DistOn upperHalfPlaneOpens := q.down.1 - D

theorem measurable_revSlit (s : ℚ) : Measurable[_, hittingSigma] (revSlit.{u} s) :=
  (measurable_image_negInv.comp (measurable_histHull s)).comp (measurable_snd.comp measurable_down)

theorem measurable_revField (D : DistOn upperHalfPlaneOpens) : Measurable (revField.{u} D) :=
  (WholeField.measurable_sub_dist D).comp (measurable_fst.comp measurable_down)

theorem revSlit_relClosed (s : ℚ) (q : RevSpace.{u}) : revSlit s q ⊆ H ∧ IsOpen (H \ revSlit s q) :=
  image_negInv_relClosed (histHull_relClosed s q.down.2)

section Glue

variable {rL rR : ℝ}
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- The reverse coupling read on the canonical space. -/
def revProj (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞)
    (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (ω : Ω₂) : RevSpace.{u} :=
  ULift.up (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)

/-- The glued space read on the canonical space. -/
def glueProj (h : Ω → DistOn upperHalfPlaneOpens) (p : Ω × HistorySpace 1 1) : RevSpace.{u} :=
  ULift.up (h p.1, p.2)

theorem measurable_revProj (hh₂ : Measurable h₂) (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂) :
    Measurable (revProj W₂ VL₂ VR₂ ζ₂ h₂) :=
  measurable_up.comp ((measurable_reflectField.comp hh₂).prodMk (measurable_killedHistory hX₂))

theorem measurable_glueProj (hh : Measurable h) : Measurable (glueProj.{u} h) :=
  measurable_up.comp ((hh.comp measurable_fst).prodMk measurable_snd)

omit [IsProbabilityMeasure P₂] in
/-- **The glued space and the reverse coupling have the same law on the canonical space.** -/
theorem glueMeasure_map_revProj (hh : Measurable h) (hh₂ : Measurable h₂)
    (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) :
    (glueMeasure P k h hh).map (glueProj h) = P₂.map (revProj W₂ VL₂ VR₂ ζ₂ h₂) := by
  have h1 : glueProj.{u} h = ULift.up ∘ fun p : Ω × HistorySpace 1 1 => (h p.1, p.2) := rfl
  have h2 : revProj.{u} W₂ VL₂ VR₂ ζ₂ h₂ =
      ULift.up ∘ fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω) := rfl
  have hm1 : Measurable fun p : Ω × HistorySpace 1 1 => (h p.1, p.2) :=
    (hh.comp measurable_fst).prodMk measurable_snd
  have hm2 : Measurable fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
    (measurable_reflectField.comp hh₂).prodMk (measurable_killedHistory hX₂)
  rw [h1, h2, ← Measure.map_map measurable_up hm1, ← Measure.map_map measurable_up hm2,
    glueMeasure_map_pair hh k, hk, hlaw]

omit [IsProbabilityMeasure P₂] in
/-- **Almost sure transfer from the reverse coupling to the glued space** for a measurable property of the canonical
coordinates. -/
theorem ae_glue_of_ae_revProj (hh : Measurable h) (hh₂ : Measurable h₂)
    (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂)
    (hlaw : P.map h = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {Q : RevSpace.{u} → Prop} (hQ : MeasurableSet {q | Q q})
    (hQ₂ : ∀ᵐ ω ∂P₂, Q (revProj W₂ VL₂ VR₂ ζ₂ h₂ ω)) :
    ∀ᵐ p ∂(glueMeasure P k h hh), Q (glueProj h p) := by
  have hμ : ∀ᵐ q ∂(P₂.map (revProj W₂ VL₂ VR₂ ζ₂ h₂)), Q q :=
    (ae_map_iff (measurable_revProj hh₂ hX₂).aemeasurable hQ).2 hQ₂
  rw [← glueMeasure_map_revProj hh hh₂ hX₂ hlaw k hk] at hμ
  exact ae_of_ae_map (measurable_glueProj hh).aemeasurable hμ

/-- **Step (S3a) for the reverse slit: its local-set mean on the glued space.** In the setting of
`ReverseTipContactStatement`, there is a mean `ĝ` on the canonical space such that `p ↦ ĝ(h p.1, p.2)` is a local-set
mean of the reflected reverse slit `R(β(0, s])` for the centred field `h − u₀` on the glued space, and
`ω ↦ ĝ(−h₂ ∘ R, history)` is, test function by test function and off the slit, the reflected explicit mean
`−meanAt(R z) − u₀(z)` of the reverse coupling. -/
theorem exists_isLocalSetMean_revSlit_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
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
    {s : ℚ} (hs : 0 < s) :
    ∃ g : RevSpace.{u} → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2)
        (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k h hC.2.1) (fun p => g (glueProj h p)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P₂,
        tsupport φ ⊆ H \ negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) →
        g (revProj W₂ VL₂ VR₂ ζ₂ h₂ ω) φ =
          ∫ z, (-meanAt (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (W₂ · ω) (fun i => (VL₂ i · ω))
            (fun i => (VR₂ i · ω)) (Real.toNNReal s) (negInv z) - u₀ z) * φ z := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set D := smoothDist upperHalfPlaneOpens u₀ with hD
  have hDh : IsHarmonicDistOn D H := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh := hC.2.1
  have hh₂ := hC₂.2.1
  have hπ₂ := measurable_revProj hh₂ hX₂
  set μ := P₂.map (revProj W₂ VL₂ VR₂ ζ₂ h₂) with hμdef
  have hglue := glueMeasure_map_revProj hh hh₂ hX₂ hlaw k hk
  -- the reflected reverse slit is local on `Ω₂`, hence on the canonical space
  have hG₂ : IsLocalSet (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
      (fun ω => reflectField (h₂ ω) - D) P₂ :=
    WholeField.IsLocalSet.sub_dist (IsLocalSet.reflect (isLocalSet_histHull_twoSeed hR hL hC₂ hs)) hDh
  have hpairm : Measurable fun q : RevSpace.{u} => (revSlit s q, revField D q) :=
    (measurable_revSlit s).prodMk (measurable_revField D)
  have hloc : IsLocalSet (revSlit s) (revField D) μ := by
    refine IsLocalSet.of_map_eq hG₂ hpairm.aemeasurable (ae_of_all _ (revSlit_relClosed s)) ?_
    rw [hμdef, Measure.map_map hpairm hπ₂]
    rfl
  -- the centred field is a zero-boundary GFF on the canonical space
  have hZglue : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω × HistorySpace 1 1 => WholeField.centredField h u₀ p.1) (glueMeasure P k h hh) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := WholeField.centredField h u₀) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hh) (WholeField.isZeroBoundaryGFF_centredField hC hu₀)
  have hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (revField D) μ := by
    refine ⟨measurable_revField D, ?_⟩
    rw [hμdef, ← hglue]
    exact Restart.isZBGFFProcess_map (measurable_glueProj hh)
      (fun φ => (LQGMetric.measurable_distOn_apply φ).comp (measurable_revField D)) hZglue.process
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hZ (measurable_revSlit s) hloc
  refine ⟨g, ?_, fun φ => ?_⟩
  · exact IsLocalSetMean.comp (measurable_glueProj hh) hglue (measurable_revSlit s) (measurable_revField D) hg
  · obtain ⟨g', hg', hid'⟩ := exists_isLocalSetMean_revSlit_twoSeed hL hR hC₂ hu₀ hs
    have hg₂ : IsLocalSetMean (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
        (fun ω => reflectField (h₂ ω) - D) P₂ (fun ω => g (revProj W₂ VL₂ VR₂ ζ₂ h₂ ω)) :=
      IsLocalSetMean.comp hπ₂ rfl (measurable_revSlit s) (measurable_revField D) hg
    have hAm : Measurable[mΩ₂, hittingSigma] fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
      fun t ht => hπ₂ (measurable_revSlit s ht)
    have hFm : Measurable fun ω => reflectField (h₂ ω) - D :=
      (WholeField.measurable_sub_dist D).comp (measurable_reflectField.comp hh₂)
    have heq := LocalSets.IsLocalSetMean.ae_apply_eq hAm hFm hg₂ hg' φ
    filter_upwards [heq, hid'] with ω e1 e2 hφ
    exact e1.trans (e2 φ hφ)

end Glue

end InteractingSLE.WangWu
