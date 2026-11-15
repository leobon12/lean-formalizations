import InteractingSLE.Spec.Sec5.Aux61RestartGeoSelect
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFinGeom

/-!
# Protection of the original right target by a real Loewner mark

Packet PROVE-AUX61-R1. The physical target 1 corresponds to the real mark -1
before negative inversion. A real forward solution at this mark gives the
required closed-hull clearance by the landed deterministic real-flow lemma.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H fwdHull IsForwardSol)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu WangWu.ImgWord LawUnique GlueCond CrossCond.Word49

/-- Continuity of negative inversion at the physical target transfers real
mark protection to the unbounded reflected hull. -/
theorem original_target_not_mem_closure_negInv_image {A : Set ℂ}
    (hA : (-1 : ℂ) ∉ closure A) :
    (1 : ℂ) ∉ closure (negInv '' A) := by
  intro hcl
  have hm : MapsTo negInv (negInv '' A) A := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [negInv_negInv] using hz
  have h := (continuousAt_negInv (by norm_num : (1 : ℂ) ≠ 0)).continuousWithinAt.mem_closure
    hcl hm
  exact hA (by simpa only [negInv, inv_one] using h)

/-- The existing real-flow clearance theorem supplies protection of 1 in Q.
The real solution is finite-time data, with no trace or endpoint assumption. -/
theorem original_target_protected_of_real_forwardSol {W : ℝ → ℝ}
    (hW : Continuous W) {s : ℝ≥0} {u : ℝ → ℂ}
    (hu : IsForwardSol W (-1 : ℂ) s u) :
    (1 : ℂ) ∉ closure (negInv '' fwdHull W s) := by
  obtain ⟨δ, hδ, hd⟩ := ZhanGT4.A2X.P3.exists_ball_disjoint_closure_fwdHull_of_isForwardSol
    (x := -1) hW s.coe_nonneg (by simpa only [ofReal_neg, ofReal_one] using hu)
  have hd' : Disjoint (ball (-1 : ℂ) δ) (closure (fwdHull W s)) := by
    simpa only [ofReal_neg, ofReal_one] using hd s le_rfl
  apply original_target_not_mem_closure_negInv_image
  exact fun hz => Set.disjoint_left.1 hd' (mem_ball_self hδ) hz

/-- The actual history hull is protected whenever its original target mark
has a real Loewner solution through the retained counterflow time. -/
theorem history_original_target_protected_of_real_mark
    {Ω : Type*} {s : ℝ≥0} {Y : Ω → HistorySpace 0 0}
    (hmarkAlive : ∀ ω, ∃ u : ℝ → ℂ, IsForwardSol (cfDrv0 s (Y ω)) (-1 : ℂ) s u) :
    ∀ ω, (1 : ℂ) ∉ closure (historyHull s Y ω) := by
  intro ω
  obtain ⟨u, hu⟩ := hmarkAlive ω
  exact original_target_protected_of_real_forwardSol (continuous_cfDrv0 s (Y ω)) hu

/-- An actual separated left force at -1, before the counterflow lifetime,
provides the real-mark input. Only driver agreement on the retained horizon is
required; values beyond the lifetime are never inspected. -/
theorem history_original_target_protected_of_left_force
    {s T : ℝ≥0} {y : HistorySpace 0 0} {a : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hTζ : (T : ℝ≥0∞) ≤ ζ) (hsT : s < T) {j : Fin nL} (hx : xL j = -1)
    (hgap : ∀ t : ℝ≥0, t < T → vL j t < w t)
    (hdriver : ∀ r ∈ Icc (0 : ℝ) s, cfDrv0 s y r = w r.toNNReal) :
    (1 : ℂ) ∉ closure (negInv '' fwdHull (cfDrv0 s y) s) := by
  have hu := ZhanGT4.A2X.P3.isForwardSol_gapL_before_horizon hp hTζ hgap
    (U := fun r => w r.toNNReal) (fun _ _ _ => rfl) (NNReal.coe_lt_coe.2 hsT)
  rw [hx] at hu
  have hu' := QuantumZipper.isForwardSol_congr_drive (fun r hr => (hdriver r hr).symm) hu
  exact original_target_protected_of_real_forwardSol (continuous_cfDrv0 s y)
    (by simpa only [ofReal_neg, ofReal_one] using hu')

end InteractingSLE.Sec5.Aux61Restart
