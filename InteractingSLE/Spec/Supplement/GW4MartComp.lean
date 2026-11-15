/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4MartLine
import InteractingSLE.Spec.Supplement.GW4MartRead
import InteractingSLE.Spec.Supplement.GW4MartLocal
import InteractingSLE.Spec.Supplement.GW4SafeRAdvanceBefore
import InteractingSLE.Spec.Supplement.GW4SafeRMeanPairing
import InteractingSLE.Spec.Supplement.HullDetGen

/-!
# GW4's protected martingales, part 6: tools for one actual component

Packet PROVE-GW4-MART. The component-level ingredients of `ComponentPhaseBefore` (Astra's follow-up 3, Q3
§§3.4–3.7):

* `pairing_eq_couplingMean_phaseProc`: the actual harmonic representative of the line mean pairs as the coupling
  mean of the explicit phase-word extension (`phaseProc`), by bounded harmonic uniqueness;
* `componentPhaseRepresentation_congr`: the boundary representation transfers to a phase that agrees almost surely
  on every live line with positive clock value (at clock value `0` the seeds coincide and the phase is invisible);
* `meanProc_zero_const`: the time-zero coupling mean of every phase-word extension is one constant;
* `isAnnouncingSeq_of_rules`: the announcing path rules of an announced version give an announcing sequence of
  stopping times of every filtration containing the canonical relative filtration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull fwdMap)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW4Fix.Mart

open Coupling Restart Restart.DomainMarkov Sec7.PhaseSel Sec7.PhaseClause Sec7.PocketTraversal Supp8.Q3Stop

/-! ### The phase-word pairing on a line -/

section Pairing

/-- **The actual harmonic representative pairs as the coupling mean of the explicit phase-word extension.** -/
theorem pairing_eq_couplingMean_phaseProc {Ω : Type*} {k : ℝ} (hk : 0 < k) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {R : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ω : Ω} {q : ℝ≥0} {c : Ω → ℝ}
    {B : Set ℂ} {g : DistOn upperHalfPlaneOpens} {w u₀ G : ℂ → ℝ}
    (hR : Continuous fun s : ℝ => R s.toNNReal ω)
    (hshape : H \ B = H \ fwdHull (fun s : ℝ => R s.toNNReal ω) q)
    (hw : InnerProductSpace.HarmonicOnNhd w (H \ B))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hrep : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ B → g ψ = ∫ z, w z * ψ z)
    (hmean : EqOn (fun z => w z + u₀ z) (couplingMean k (fun s : ℝ => R s.toNNReal ω) q G) (H \ B))
    (hG : IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => VL i q ω - R q ω) (fun j => VR j q ω - R q ω) (c ω))
      (forceJumpSet (fun i => VL i q ω - R q ω) (fun j => VR j q ω - R q ω)) G)
    (hL : VL 0 q ω ≤ R q ω) (hRr : R q ω ≤ VR 0 q ω)
    {ψ : TestOn upperHalfPlaneOpens}
    (hψ : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => R s.toNNReal ω) q)) :
    (g + smoothDist upperHalfPlaneOpens u₀) ψ =
      ∫ z, couplingMean k (fun s : ℝ => R s.toNNReal ω) q (phaseProc k ρL ρR R VL VR c ω q) z * ψ z := by
  have hψB : tsupport ψ ⊆ H \ B := by
    rw [hshape]
    exact fun z hz => ⟨Coupling.tsupport_subset_H ψ hz, Set.disjoint_left.1 hψ hz⟩
  have hwc : ContinuousOn w (H \ B) :=
    fun z hz => (hw z hz).1.continuousAt.continuousWithinAt
  have hu₀c : ContinuousOn u₀ H :=
    fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hi₁ := WholeField.integrable_mul_testOn hwc ψ hψB
  have hi₂ := WholeField.integrable_mul_testOn hu₀c ψ (hψB.trans sdiff_subset)
  rw [_root_.add_apply, hrep ψ hψB, Coupling.smoothDist_apply_eq hu₀c ψ, ← integral_add hi₁ hi₂]
  have hGG : EqOn (phaseProc k ρL ρR R VL VR c ω q) G H :=
    Impl.eqOn_of_isBoundedHarmonicExtension (((Set.finite_range _).union (Set.finite_range _)).insert 0) hG
      (isBoundedHarmonicExtension_phaseProc hk c hL hRr)
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport ψ
  · have hzB := hψB hz
    have hzO : z ∈ H \ fwdHull (fun s : ℝ => R s.toNNReal ω) q := hshape ▸ hzB
    have hfH := QuantumZipper.FwdHolo.mapsTo_fwdMap hR q.coe_nonneg hzO
    have hm : w z + u₀ z = couplingMean k (fun s : ℝ => R s.toNNReal ω) q G z := hmean hzB
    rw [← add_mul, hm]
    simp only [couplingMean, hGG hfH]
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero, add_zero]

end Pairing

/-! ### The component coordinates -/

section Coords

variable {Ω : Type*} {k : ℝ} {c₀ : BoundaryWord} {X : Ω → DistOn upperHalfPlaneOpens} {R : ℝ≥0 → Ω → ℝ}
  {V : Ω → ℝ≥0∞}

theorem continuous_componentVL (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) (ω : Ω)
    (i : Fin (wordType k c₀).1) : Continuous fun t => componentVL k c₀ X R V i t ω := by
  have e : (fun t => componentVL k c₀ X R V i t ω) =
      fun t => geomLW R (fun _ => typedXL k (wordType k c₀) c₀) i t ω :=
    funext fun t => componentVL_eq_geom k c₀ X R V (hRc ω) (hR0 ω) i t
  rw [e]
  exact (isForcePath_geomLW hRc _ ω i).1

theorem continuous_componentVR (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) (ω : Ω)
    (j : Fin (wordType k c₀).2.1) : Continuous fun t => componentVR k c₀ X R V j t ω := by
  have e : (fun t => componentVR k c₀ X R V j t ω) =
      fun t => geomRW R (fun _ => typedXR k (wordType k c₀) c₀) j t ω :=
    funext fun t => componentVR_eq_geom k c₀ X R V (hRc ω) (hR0 ω) j t
  rw [e]
  exact (isForcePath_geomRW hRc _ ω j).1

theorem componentVL_le (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) (ω : Ω) (t : ℝ≥0)
    (i : Fin (wordType k c₀).1) : componentVL k c₀ X R V i t ω ≤ R t ω := by
  rw [componentVL_eq_geom k c₀ X R V (hRc ω) (hR0 ω) i t]
  exact geomLW_le hRc _ ω t i

theorem le_componentVR (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) (ω : Ω) (t : ℝ≥0)
    (j : Fin (wordType k c₀).2.1) : R t ω ≤ componentVR k c₀ X R V j t ω := by
  rw [componentVR_eq_geom k c₀ X R V (hRc ω) (hR0 ω) j t]
  exact le_geomRW hRc _ ω t j

theorem componentSeeds_lt (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) (ω : Ω) {t : ℝ≥0}
    (ht : 0 < t) :
    componentVL k c₀ X R V (componentSeedL k c₀) t ω < componentVR k c₀ X R V (componentSeedR k c₀) t ω := by
  rw [componentVL_eq_geom k c₀ X R V (hRc ω) (hR0 ω), componentVR_eq_geom k c₀ X R V (hRc ω) (hR0 ω)]
  exact Sec7.PhaseClause.geomLW_lt_geomRW_of_pos (T := fun _ => ⊤) (fun ω => (hRc ω).continuousOn) _ _ _ _ ht
    ENNReal.coe_lt_top

/-- The time-zero data of the component word do not depend on the sample. -/
theorem componentVL_zero (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) (ω : Ω)
    (i : Fin (wordType k c₀).1) : componentVL k c₀ X R V i 0 ω = typedXL k (wordType k c₀) c₀ i := by
  rw [componentVL_eq_geom k c₀ X R V (hRc ω) (hR0 ω)]
  exact geomLW_zero hRc hR0 (typedXL_nonpos _ _ _ i)

theorem componentVR_zero (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) (ω : Ω)
    (j : Fin (wordType k c₀).2.1) : componentVR k c₀ X R V j 0 ω = typedXR k (wordType k c₀) c₀ j := by
  rw [componentVR_eq_geom k c₀ X R V (hRc ω) (hR0 ω)]
  exact geomRW_zero hRc hR0 (typedXR_nonneg _ _ _ j)

end Coords

end InteractingSLE.Theorem14.GW4Fix.Mart
