/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenJunction
import InteractingSLE.Spec.Supplement.GB6Glue

/-!
# Relative images of stopped, possibly boundary-hitting flow hulls

PROVE-CROSSCOND-GEN. The compact restriction construction uses fillings, not a
hull-equals-trace assertion. The original driver need only be continuous before its
lifetime. A clamp strictly beyond the retained interval lets GB6 apply without an
infinite-lifetime assumption. The transformed boundary labels include both junctions.

Selecting these compact drivers measurably, gluing their force coordinates through
boundary collisions, and identifying the surviving boundary heights are separate inputs.
`WangWu.ImgDrv.IsKilledArc` cannot represent these images: its `mem_H` field excludes
positive-time contacts with the original real boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito Supp8.GB6 Word49 Theta

/-- A compact part of a boundary-hitting generating trace has a relative Loewner driver
in the fixed counterflow chart, with its intrinsic capacity clock and filled image hulls.
The cutoff is strictly before the original continuation threshold. -/
theorem exists_relativeImage_Icc {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hα : IsGeneratingTrace w ζ α) {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {s : ℝ} (hs : 0 < s) {p : ℂ}
    (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ)
    (hsep : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (rpath w) T))) :
    ∃ V : ℝ → ℝ, Continuous V ∧ V 0 = 0 ∧ relClock U s (rpath w) 0 = 0 ∧
      StrictMonoOn (relClock U s (rpath w)) (Icc 0 (T : ℝ)) ∧
      ContinuousOn (relClock U s (rpath w)) (Icc 0 (T : ℝ)) ∧
      ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ relClock U s (rpath w) t ∧
        fwdHull V (relClock U s (rpath w) t) = relMap U s '' fwdHull (rpath w) t ∧
        IsFilling (fwdHull V (relClock U s (rpath w) t))
          (relMap U s '' ((fun r : ℝ => α r.toNNReal) '' Icc 0 t ∩ H)) := by
  obtain ⟨T₂, hTT₂, hT₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hT
  have hTT₂' : (T : ℝ) < T₂ := by exact_mod_cast hTT₂
  let W := clampDrv (rpath w) T₂
  have hW : Continuous W := continuous_clampDrv T₂.coe_nonneg (continuousOn_rpath hw hT₂)
  have hW0 : W 0 = 0 := by
    rw [show W 0 = rpath w 0 from clampDrv_eqOn ⟨le_rfl, T₂.coe_nonneg⟩]
    simpa only [rpath, Real.toNNReal_zero] using hw0
  have hK : ∀ t ∈ Icc (0 : ℝ) T, fwdHull W t = fwdHull (rpath w) t := by
    intro t ht
    exact InteractingSLE.fwdHull_eq_of_eqOn ht.1 (ht.2.trans_lt hTT₂')
      (fun r hr => clampDrv_eqOn hr)
  have ha : EqOn (relClock U s W) (relClock U s (rpath w)) (Icc (0 : ℝ) T) :=
    fun t ht => by rw [relClock, relClock, hK t ht]
  have hsep' : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull W T)) := by
    rwa [hK T ⟨T.coe_nonneg, le_rfl⟩]
  obtain ⟨V, hV, hV0, ha0, ham, hac, hVh⟩ :=
    exists_relChain_Icc hW hW0 hU hU0 hs htip T.coe_nonneg hsep' (γ := fun r : ℝ => α r.toNNReal)
      (fun t ht => by
        rw [hK t ht]
        have htt : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 ht.2
        have htζ : (t.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast htt) hT
        have hf := hα.2.2 t.toNNReal htζ
        rw [← Supp8.GB6.image_Icc_toNNReal α t.toNNReal] at hf
        change IsFilling (fwdHull (fun r : ℝ => w r.toNNReal) t)
          ((fun r : ℝ => α r.toNNReal) '' Icc 0 t)
        simpa only [Real.coe_toNNReal t ht.1] using hf)
  refine ⟨V, hV, hV0, ?_, ham.congr ha, hac.congr ha.symm, ?_⟩
  · rwa [← ha ⟨le_rfl, T.coe_nonneg⟩]
  · intro t ht
    have h := hVh t ht
    rwa [ha ht, hK t ht] at h

/-- The chart images of all original left labels, followed by the left junction. -/
def imageMarksL {n : ℕ} (x : Fin n → ℝ) (U : ℝ → ℝ) (s : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (fun i => psiL U s (x i)) (junL U s)

/-- The reflected right labels, followed by the right junction. -/
def imageMarksR {n : ℕ} (x : Fin n → ℝ) (U : ℝ → ℝ) (s : ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (fun i => psiR U s (x i)) (junR U s)

/-- Boundary labels and junctions form an ordered word. No noncollision assumption on
the flow line is used; the two chart-junction gaps are stated explicitly. -/
theorem isOrderedForceWord_imageMarks {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {U : ℝ → ℝ} (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s)
    (hjL : 0 < MartChar.RealFlow.rightImg U 0 s - U s)
    (hjR : -MartChar.RealFlow.rightImg (fun r => -U r) 0 s - U s < 0) :
    IsOrderedForceWord (imageMarksL xL U s) (imageMarksR xR U s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact antitone_snoc (fun i i' hii => psiL_mono hU hs hjL (hF.2.1 i) (hF.1 hii))
      (fun i => junL_le_psiL hU hs hjL (hF.2.1 i))
  · exact snoc_le (fun i => psiL_nonpos hU hs hjL (hF.2.1 i))
      ((junL_le_psiL hU hs hjL le_rfl).trans (psiL_nonpos hU hs hjL le_rfl))
  · exact monotone_snoc (fun j j' hjj => psiR_mono hU hs hjR (hF.2.2.2 j) (hF.2.2.1 hjj))
      (fun j => psiR_le_junR hU hs hjR (hF.2.2.2 j))
  · exact le_snoc (fun j => psiR_nonneg hU hs hjR (hF.2.2.2 j))
      ((psiR_nonneg hU hs hjR le_rfl).trans (psiR_le_junR hU hs hjR le_rfl))

/-- The last left label has the angle-dependent boundary-junction weight. -/
theorem image_junction_weightL {n : ℕ} (θ κ : ℝ) (ρ : Fin n → ℝ) :
    jwL (cLT θ) κ ρ (Fin.last n) =
      (3 / 2 + θ / π) * (κ / 2 - 2) - ∑ i, ρ i := by
  simp only [jwL, Fin.snoc_last, cLT]

/-- The last right label has the reflected boundary-junction weight. -/
theorem image_junction_weightR {n : ℕ} (θ κ : ℝ) (ρ : Fin n → ℝ) :
    jwR (cRT θ) κ ρ (Fin.last n) =
      (3 / 2 - θ / π) * (κ / 2 - 2) - ∑ i, ρ i := by
  simp only [jwR, Fin.snoc_last, cRT]

end InteractingSLE.Sec5.CrossCond.Gen
