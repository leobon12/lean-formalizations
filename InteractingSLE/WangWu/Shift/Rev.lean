/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Shift.Basic
import InteractingSLE.WangWu.ReverseContactRevMean

/-!
# The height-shifted two-slit law, part 3: the reverse slit on a glued space with an arbitrary glued field

Packet PROVE-WW-B26. PROVE-WW-B12/B13's reverse-slit results on the glued space `P ⊗ k(h)` take the forward coupling
`hC` only for the measurability of the glued field `h` and for `h − u₀` being a zero-boundary GFF. In the shifted
setting the glued field is `X = h − δλ` (the field of the reverse line), which carries no coupling of its own here.
These are the same results for an arbitrary measurable glued field `X` whose centred field `X − u₀` is a
zero-boundary GFF (`u₀` the harmonic extension of the data of the word `(r_L; r_R)` of `X`; the reverse coupling has
the reflected word `(r_R; r_L)`):

* `exists_isLocalSetMean_revSlit_canonX`, **`ae_revSlitMean_glueX`** (B13's explicit reverse-slit mean);
* `ae_unb_revSlit_glueX`, `ae_goodHist_snd_glueX` (B13's reverse goodness on the glued space).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H fwdHull fwdMap)
open LQGMetric (DistOn TestOn)
open LocalSets (IsLocalSetMean germSigma lowerUnion)
open LawUnique
open Sec4 (regPath regHull posLProc posRProc safePair safeIdx safeUnion histStop)

universe u

section Glue

open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {rL rR : ℝ}
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- **The canonical reverse-slit mean** (PROVE-WW-B12's `exists_isLocalSetMean_revSlit_glue`, with the local-set mean
on the canonical space exported, so that it is measurable). -/
theorem exists_isLocalSetMean_revSlit_canonX (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    (hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField X u₀) P)
    {s : ℚ} (hs : 0 < s) :
    ∃ g : RevSpace.{u} → DistOn upperHalfPlaneOpens, Measurable g ∧
      IsLocalSetMean (fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2)
        (fun p => WholeField.centredField X u₀ p.1) (glueMeasure P k X hXm) (fun p => g (glueProj X p)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P₂,
        tsupport φ ⊆ H \ negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) →
        g (revProj W₂ VL₂ VR₂ ζ₂ h₂ ω) φ =
          ∫ z, (-meanAt (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (W₂ · ω) (fun i => (VL₂ i · ω))
            (fun i => (VR₂ i · ω)) (Real.toNNReal s) (negInv z) - u₀ z) * φ z := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set D := smoothDist upperHalfPlaneOpens u₀ with hD
  have hDh : IsHarmonicDistOn D H := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh := hXm
  have hh₂ := hC₂.2.1
  have hπ₂ := measurable_revProj hh₂ hX₂
  set μ := P₂.map (revProj W₂ VL₂ VR₂ ζ₂ h₂) with hμdef
  have hglue := glueMeasure_map_revProj hh hh₂ hX₂ hlaw k hk
  have hG₂ : IsLocalSet (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
      (fun ω => reflectField (h₂ ω) - D) P₂ :=
    WholeField.IsLocalSet.sub_dist (IsLocalSet.reflect (isLocalSet_histHull_twoSeed hR hL hC₂ hs)) hDh
  have hpairm : Measurable fun q : RevSpace.{u} => (revSlit s q, revField D q) :=
    (measurable_revSlit s).prodMk (measurable_revField D)
  have hloc : IsLocalSet (revSlit s) (revField D) μ := by
    refine IsLocalSet.of_map_eq hG₂ hpairm.aemeasurable (ae_of_all _ (revSlit_relClosed s)) ?_
    rw [hμdef, Measure.map_map hpairm hπ₂]
    rfl
  have hZglue : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : Ω × HistorySpace 1 1 => WholeField.centredField X u₀ p.1) (glueMeasure P k X hh) :=
    isZeroBoundaryGFF_comp_of_map_eq (g := WholeField.centredField X u₀) (f := Prod.fst) measurable_fst
      (glueMeasure_fst (μ := P) k hh) hZ
  have hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (revField D) μ := by
    refine ⟨measurable_revField D, ?_⟩
    rw [hμdef, ← hglue]
    exact Restart.isZBGFFProcess_map (measurable_glueProj hh)
      (fun φ => (LQGMetric.measurable_distOn_apply φ).comp (measurable_revField D)) hZglue.process
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hZ (measurable_revSlit s) hloc
  have hgm : Measurable g := hg.1.mono (LocalSets.germSigma_le (measurable_revSlit s) (measurable_revField D)) le_rfl
  refine ⟨g, hgm, ?_, fun φ => ?_⟩
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

/-- **Item N2 of PROVE-WW-B12: the explicit reverse-slit mean on the glued space.** In the setting of
`ReverseTipContactStatement`, almost surely on the glued space the hull of the regularized driver of `p.2` lies in the
slit read from its trace, and every local-set mean `g_G` of the reflected reverse slit `R(β(0, s])` for the centred
field `h − u₀` is, off that slit, the explicit `revMean`: `g_G(φ) = ∫ (−histMean (R z) − u₀ z) φ(z) dz`. -/
theorem ae_revSlitMean_glueX (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    (hZ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField X u₀) P)
    {s : ℚ} (hs : 0 < s) {gG : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens}
    (hgG : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2)
      (fun p => WholeField.centredField X u₀ p.1) (glueMeasure P k X hXm) gG) :
    (∀ᵐ p ∂(glueMeasure P k X hXm), p.2 ∈ RegSub s) ∧
      ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ negInv '' histHull s p.2 → gG p φ = ∫ z, revMean rL rR u₀ s p.2 z * φ z := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh := hXm
  have hh₂ := hC₂.2.1
  have hharm : InnerProductSpace.HarmonicOnNhd u₀ H := hu₀.1
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hharm z hz).1.continuousAt.continuousWithinAt
  have hgood₂ := ae_revStop_good hR hL hC₂.1 hs
  have hreg : ∀ᵐ p ∂(glueMeasure P k X hh), p.2 ∈ RegSub s := by
    refine ae_glue_snd (X₂ := fun ω => reflectField (h₂ ω)) (D₂ := killedHistory W₂ VL₂ VR₂ ζ₂) hh
      (measurable_reflectField.comp hh₂) (measurable_killedHistory hX₂) hlaw k hk (measurableSet_regSub s) ?_
    filter_upwards [hgood₂] with ω hω
    obtain ⟨hg, -, -, hH⟩ := hω
    show regHull (revStop s _) ⊆ histHull s _
    rw [regHull_revStop_killedHistory hg, hH]
  refine ⟨hreg, ?_⟩
  obtain ⟨g, hgm, hgl, hg₂⟩ := exists_isLocalSetMean_revSlit_canonX hL hR hXm hC₂ hlaw k hk hu₀ hZ hs
  have hAm : Measurable[_, hittingSigma] fun p : Ω × HistorySpace 1 1 => negInv '' histHull s p.2 :=
    (measurable_image_negInv.comp (measurable_histHull s)).comp measurable_snd
  have hFm : Measurable fun p : Ω × HistorySpace 1 1 => WholeField.centredField X u₀ p.1 :=
    (WholeField.measurable_centredField hh u₀).comp measurable_fst
  refine ae_forall_apply_eq_of_forall_ae hgG.2.1
    (ae_of_all _ fun p => (image_negInv_relClosed (histHull_relClosed s p.2)).2) ?_ fun φ => ?_
  · filter_upwards [hreg] with p hp
    intro z hz
    refine harmonicOnNhd_revMean rL rR hharm s p.2 z ⟨hz.1, fun hzF => hz.2 ?_⟩
    obtain ⟨w, hw, hwz⟩ := hzF
    exact ⟨w, hp (fwdHull_subset_regHull s p.2 hw), hwz⟩
  · set Q : RevSpace.{u} → Prop := fun q =>
      Disjoint (tsupport φ) (revSlit s q) → g q φ = revTested rL rR u₀ s φ q.down.2 with hQdef
    have hQm : MeasurableSet {q | Q q} := by
      refine measurableSet_setOfPred.2 (Measurable.imp ?_ ?_)
      · exact measurableSet_setOfPred.1 (measurableSet_disjoint_of_relClosed (measurable_revSlit s)
          (revSlit_relClosed s) φ.hasCompactSupport φ.tsupport_subset)
      · exact measurableSet_setOfPred.1 (measurableSet_eq_fun ((LQGMetric.measurable_distOn_apply φ).comp hgm)
          ((measurable_revTested rL rR u₀ s φ).comp (measurable_snd.comp measurable_down)))
    have hQ₂ : ∀ᵐ ω ∂P₂, Q (revProj W₂ VL₂ VR₂ ζ₂ h₂ ω) := by
      filter_upwards [hg₂ φ, hgood₂] with ω hω hω' hdis
      obtain ⟨hg, hvL, hvR, hH⟩ := hω'
      have hsub : tsupport φ ⊆ H \ negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
        fun z hz => ⟨φ.tsupport_subset hz, Set.disjoint_left.1 hdis hz⟩
      rw [hω hsub]
      have hdis' : Disjoint (tsupport φ) (negInv '' regHull (revStop s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) := by
        rw [regHull_revStop_killedHistory hg, ← hH]
        exact hdis
      show _ = revTested rL rR u₀ s φ (killedHistory W₂ VL₂ VR₂ ζ₂ ω)
      rw [revTested_eq rL rR hu₀c s _ hdis']
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [revMean]
      rw [histMean_killedHistory _ _ hg hvL hvR]
      rfl
    have hQg := ae_glue_of_ae_revProj hh hh₂ hX₂ hlaw k hk hQm hQ₂
    have hagree := LocalSets.IsLocalSetMean.ae_apply_eq hAm hFm hgG hgl φ
    filter_upwards [hQg, hagree, hreg] with p hQp hap hp hφ
    have hdis : Disjoint (tsupport φ) (negInv '' histHull s p.2) :=
      Set.disjoint_left.2 fun z hz hz' => (hφ hz).2 hz'
    rw [hap, hQp hdis]
    exact revTested_eq rL rR hu₀c s p.2 (hdis.mono_right (image_mono hp))

/-- **Proposition 3.8's condition for the reflected reverse slit on the glued space.** -/
theorem ae_unb_revSlit_glueX (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) {s : ℚ} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ z ∈ lowerUnion (negInv '' histHull s p.2),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (negInv '' histHull s p.2)) z) := by
  have hgood := ae_glue_snd (X₂ := fun ω => reflectField (h₂ ω)) (D₂ := killedHistory W₂ VL₂ VR₂ ζ₂) hXm
    (measurable_reflectField.comp hC₂.2.1) (measurable_killedHistory hC₂.2.2.2.1) hlaw k hk
    (measurableSet_goodHist s) (ae_mem_goodHist_twoSeed hR hL hC₂.1 s)
  filter_upwards [hgood] with p hp
  exact not_isBounded_lowerUnion_of_isPreconnected (isPreconnected_image_negInv_histHull hs hp)
    (not_isBounded_image_negInv_histHull hs hp)

/-- The reverse history is good on the glued space. -/
theorem ae_goodHist_snd_glueX (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂
      ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) (s : ℚ) :
    ∀ᵐ p ∂(glueMeasure P k X hXm), p.2 ∈ GoodHist s :=
  ae_glue_snd (X₂ := fun ω => reflectField (h₂ ω)) (D₂ := killedHistory W₂ VL₂ VR₂ ζ₂) hXm
    (measurable_reflectField.comp hC₂.2.1) (measurable_killedHistory hC₂.2.2.2.1) hlaw k hk
    (measurableSet_goodHist s) (ae_mem_goodHist_twoSeed hR hL hC₂.1 s)

end Glue

end InteractingSLE.WangWu
