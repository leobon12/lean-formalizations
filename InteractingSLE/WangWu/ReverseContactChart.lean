/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactRevMean

/-!
# The union mean of the two stopped slits, compared with both explicit slit means

Packet PROVE-WW-B13. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of
Proposition 4.18 (text dump L1609–1614): "the independent-union lemma makes the two stopped slits a local set. The
union boundary lemma identifies its harmonic mean on every exposed open arc."

This assembles step (S3a) of the contact step in the setting of `ReverseTipContactStatement`: on the glued space
`P ⊗ k(h)`, with the forward slit `A = α(0, t]` (read from the forward history) and the reflected reverse slit
`G = R(β(0, s])` (read from the reverse history `p.2`), `t, s > 0` rational:

* **`ae_union_mean_glue`**: almost surely, every local-set mean of `A ∪ G` for the centred field `h − u₀` has a harmonic
  representative `w` on `ℍ ∖ (A ∪ G)` such that
  - `w − (meanAt^α_t − u₀) → 0` at every point of `A ∪ ℝ` near which `G ⊆ A`, and
  - `w − revMean_s(p.2) → 0` at every point of `G ∪ ℝ` near which `A ⊆ G`,
  where `meanAt^α_t` is the forward coupling's explicit mean (Wang–Wu Corollary 3.9) and `revMean` is the explicit
  reflected reverse mean read from the history (`ReverseContactRevMean`).

Its inputs are PROVE-WW-B11's locality (S2), PROVE-WW-B12's union boundary lemma and forward slit mean, and this
packet's unbounded-components conditions (`ReverseContactGood`) and explicit reverse mean (`ReverseContactRevMean`).
What remains of (S3) is deterministic: the boundary correspondence of the two-slit chart (PROVE-WW-B11's (S3b)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H fwdHull fwdMap)
open LQGMetric (DistOn TestOn)
open LocalSets (IsLocalSetMean germSigma)
open LawUnique
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

section Glue

variable {rL rR : ℝ}
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- **Step (S3a) of the contact step, assembled**: the union mean of the two stopped slits on the glued space, with
its boundary behaviour against the two explicit slit means. -/
theorem ae_union_mean_glue (hL : 0 ≤ rL) (hR : 0 ≤ rR)
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
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) {g : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k h hC.2.1) g) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w
          (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) →
            g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ histHull t (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, negInv '' histHull s p.2 ∩ ball z₀ r ⊆ histHull t (killedHistory W VL VR ζ p.1)) →
          Tendsto (fun z => w z - (meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1)
              (fun i => (VL i · p.1)) (fun i => (VR i · p.1)) (Real.toNNReal t) z - u₀ z))
            (𝓝[H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ negInv '' histHull s p.2 ∪ {z : ℂ | z.im = 0},
          (∃ r > 0, histHull t (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ negInv '' histHull s p.2) →
          Tendsto (fun z => w z - revMean rL rR u₀ s p.2 z)
            (𝓝[H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)] z₀) (𝓝 0)) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  set D := smoothDist upperHalfPlaneOpens u₀ with hD
  have hDh : IsHarmonicDistOn D H := WholeField.isHarmonicDistOn_smoothDist hu₀.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hh := hC.2.1
  have hT : Measurable fun f : DistOn upperHalfPlaneOpens => f - D := WholeField.measurable_sub_dist D
  have hT' : Measurable fun f : DistOn upperHalfPlaneOpens => f + D := Coupling.measurable_add_distOnConst D
  -- the two slits are local on the glued space (PROVE-WW-B11)
  have hA : IsLocalSet (fun ω => histHull t (killedHistory W VL VR ζ ω)) (fun ω => h ω - D) P :=
    WholeField.IsLocalSet.sub_dist (isLocalSet_histHull_twoSeed hL hR hC ht) hDh
  have hAm : Measurable[mΩ, hittingSigma] fun ω => histHull t (killedHistory W VL VR ζ ω) :=
    (measurable_histHull t).comp (measurable_killedHistory hX)
  have hAg := IsLocalSet.glue_fst hh k (T := fun f => f - D) hA
  have hG₂ : IsLocalSet (fun ω => negInv '' histHull s (killedHistory W₂ VL₂ VR₂ ζ₂ ω))
      (fun ω => reflectField (h₂ ω) - D) P₂ :=
    WholeField.IsLocalSet.sub_dist (IsLocalSet.reflect (isLocalSet_histHull_twoSeed hR hL hC₂ hs)) hDh
  have hGm : Measurable[_, hittingSigma] fun y : HistorySpace 1 1 => negInv '' histHull s y :=
    measurable_image_negInv.comp (measurable_histHull s)
  have hGg := IsLocalSet.glue_snd hh k (measurable_reflectField.comp hC₂.2.1)
    (measurable_killedHistory hX₂) hlaw hk hT hGm MeasurableSet.univ
    (fun y _ => image_negInv_relClosed (histHull_relClosed s y)) (Eventually.of_forall fun _ => mem_univ _) hG₂
  -- the two slit means
  obtain ⟨gA, hgA, hidA⟩ := exists_isLocalSetMean_fwdSlit_glue hL hR hC k hu₀ ht
  obtain ⟨gG₀, -, hgG, -⟩ := exists_isLocalSetMean_revSlit_canon hL hR hC hC₂ hlaw k hk hu₀ hs
  obtain ⟨-, hidG⟩ := ae_revSlitMean_glue hL hR hC hC₂ hlaw k hk hu₀ hs hgG
  have hreg := (ae_revSlitMean_glue hL hR hC hC₂ hlaw k hk hu₀ hs hgG).1
  -- the union boundary lemma (PROVE-WW-B12)
  have hU := ae_union_boundary_glue (P := P) hh k hT hT' (fun f => sub_add_cancel f D)
    (WholeField.isZeroBoundaryGFF_centredField hC hu₀) hAm hGm hAg hGg (ae_unb_fwdSlit_glue hL hR hC k ht)
    (ae_unb_revSlit_glue hL hR hC hC₂ hlaw k hk hs) hg hgA hgG
  -- the forward mean is harmonic off the forward slit
  have hseed := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1
  have hfwd : ∀ᵐ p ∂(glueMeasure P k h hh), InnerProductSpace.HarmonicOnNhd
      (fun z => meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1) (fun i => (VL i · p.1))
        (fun i => (VR i · p.1)) (Real.toNNReal t) z - u₀ z) (H \ histHull t (killedHistory W VL VR ζ p.1)) := by
    refine ae_glue_fst (μ := P) k hh (Q := fun ω => InnerProductSpace.HarmonicOnNhd
      (fun z => meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · ω) (fun i => (VL i · ω))
        (fun i => (VR i · ω)) (Real.toNNReal t) z - u₀ z) (H \ histHull t (killedHistory W VL VR ζ ω))) ?_
    filter_upwards [hseed, hC.1.2.2.2.2, ae_histHull_eq_fwdHull hL hR hC.1 ht] with ω hω hp hH
    rw [hH]
    have hlt : ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hω.1]; exact ENNReal.coe_lt_top
    exact (harmonicOnNhd_meanAt_of_lt hp hlt).sub fun z hz => hu₀.1 z hz.1
  filter_upwards [hU, hidA, hidG, hreg, hfwd] with p hUp hAp hGp hregp hfwdp
  have hwG : InnerProductSpace.HarmonicOnNhd (revMean rL rR u₀ s p.2) (H \ negInv '' histHull s p.2) := by
    intro z hz
    refine harmonicOnNhd_revMean rL rR hu₀.1 s p.2 z ⟨hz.1, fun hzF => hz.2 ?_⟩
    obtain ⟨w, hw, hwz⟩ := hzF
    exact ⟨w, hregp (fwdHull_subset_regHull s p.2 hw), hwz⟩
  exact hUp _ _ hfwdp hAp hwG hGp

/-- **Before contact** (`A ∩ G = ∅`): almost surely the union mean has a harmonic representative `w` with
`w − (meanAt^α_t − u₀) → 0` at **every** point of `A ∪ ℝ`, and `w − revMean → 0` at every point of `G` and every
nonzero real point (`G` is closed in `ℂ` and misses `ℝ`; the closure of `A` adds only `0`). -/
theorem ae_union_mean_glue_of_disjoint (hL : 0 ≤ rL) (hR : 0 ≤ rR)
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
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) {g : Ω × HistorySpace 1 1 → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun p : Ω × HistorySpace 1 1 =>
      histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)
      (fun p => WholeField.centredField h u₀ p.1) (glueMeasure P k h hC.2.1) g) :
    ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
      Disjoint (histHull t (killedHistory W VL VR ζ p.1)) (negInv '' histHull s p.2) →
      ∃ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w
          (H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)) ∧
        (∀ φ : TestOn upperHalfPlaneOpens,
          tsupport φ ⊆ H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) →
            g p φ = ∫ z, w z * φ z) ∧
        (∀ z₀ ∈ histHull t (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
          Tendsto (fun z => w z - (meanAt (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (W · p.1)
              (fun i => (VL i · p.1)) (fun i => (VR i · p.1)) (Real.toNNReal t) z - u₀ z))
            (𝓝[H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)] z₀) (𝓝 0)) ∧
        (∀ z₀ ∈ negInv '' histHull s p.2 ∪ ({z : ℂ | z.im = 0} \ {0}),
          Tendsto (fun z => w z - revMean rL rR u₀ s p.2 z)
            (𝓝[H \ (histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2)] z₀) (𝓝 0)) := by
  filter_upwards [ae_union_mean_glue hL hR hC hC₂ hlaw k hk hu₀ ht hs hg,
    ae_goodHist_fst_glue hL hR hC k t, ae_goodHist_snd_glue hL hR hC hC₂ hlaw k hk s] with p hp hA hG hdis
  obtain ⟨w, hw, hrep, hlimA, hlimG⟩ := hp
  set A := histHull t (killedHistory W VL VR ζ p.1) with hAdef
  set G := negInv '' histHull s p.2 with hGdef
  have hGc : IsClosed G := isClosed_image_negInv_histHull hs hG
  have hGH : G ⊆ H := (image_negInv_relClosed (histHull_relClosed s p.2)).1
  have hAcl : closure A ⊆ insert 0 A := closure_histHull_subset ht hA
  refine ⟨w, hw, hrep, fun z₀ hz₀ => hlimA z₀ hz₀ ?_, fun z₀ hz₀ => hlimG z₀ ?_ ?_⟩
  · -- a ball around `z₀` misses `G`
    have hz₀G : z₀ ∉ G := by
      rcases hz₀ with hz | hz
      · exact Set.disjoint_left.1 hdis hz
      · intro hzG
        have : 0 < z₀.im := hGH hzG
        rw [show z₀.im = 0 from hz] at this
        exact lt_irrefl _ this
    obtain ⟨r, hr, hrG⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl z₀ hz₀G
    exact ⟨r, hr, fun z hz => absurd hz.1 (hrG hz.2)⟩
  · rcases hz₀ with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz.1
  · -- a ball around `z₀` misses `A`
    have hz₀A : z₀ ∉ closure A := by
      intro hzc
      rcases hAcl hzc with h0 | hzA
      · rcases hz₀ with hz | hz
        · have : 0 < z₀.im := hGH hz
          rw [h0] at this
          simp at this
        · exact hz.2 h0
      · rcases hz₀ with hz | hz
        · exact Set.disjoint_left.1 hdis hzA hz
        · have : 0 < z₀.im := (histHull_relClosed t _).1 hzA
          rw [show z₀.im = 0 from hz.1] at this
          exact lt_irrefl _ this
    obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z₀ hz₀A
    exact ⟨r, hr, fun z hz => absurd (subset_closure hz.1) (hrA hz.2)⟩

end Glue

end InteractingSLE.WangWu
