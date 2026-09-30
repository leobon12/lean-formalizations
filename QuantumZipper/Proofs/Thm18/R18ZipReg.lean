import QuantumZipper.Proofs.Thm18.R18RoundDownWire
import QuantumZipper.Proofs.Thm18.R18RoundRaw
import QuantumZipper.Proofs.Thm18.R18UpWeld
import QuantumZipper.Proofs.Thm18.G4ZipRegPair
import QuantumZipper.Proofs.Thm18.G4ASepLog
import QuantumZipper.Proofs.Thm18.G4ASepBackLog
import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Thm18.G4ASepDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 ZIPREG: off-curve regularity of the re-zipped field (`R18.G4ZipRegAStmt`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), (3), p. 26.
Port of `Thm18Asm.g4ZipRegStmt_of_pairCont` (G4ZipRegCore.lean:133) by the R18 substitution rule
(`handoff/R18-PLAN.md` §1). As there, no random-time regularity argument is needed: a coordinate
change reads its input only through the regularization, so on the round-trip event the re-zipped
field is *exactly* `rescale G Q a⁻¹`, where `G` (the zip-up of the rescaled unzipped field) agrees
with `rescale Y Q a` off the re-zipped hull (`coordsFull_rezipUp_off`, from A-sep; this replaces
the old full `RegEq` of `G4RoundUpRezipCoreStmt`). At a coordinate circle, resp. a test function,
that stays off the curve, the pushed circle, resp. the pushed test measure, stays off that hull
(`circleOff_scale`, `far_scale`), so the raw value of the re-zipped field is the one of
`rescale (rescale Y Q a) Q a⁻¹`, i.e. `evalReg Y` (`G1.rescale_rescale_inv_fc`, and
`rescale_rescale_inv_tmeas` with the proved continuum limit `wedgePairContStmt_holds`), which is
also its regularized value (the round trip `g4RoundDownA_of`).

This node exists only because `FieldSample` carries raw values (D25): the paper never reads raw
values. **Own elementary argument** (as the old proof; analytic input Duplantier–Sheffield 2011
Prop 3.1 through `wedgePairContStmt_holds`).

Main results: `zipLenA_zipLenDownA_fld_eq` (deterministic), **`g4ZipRegAStmt_of (hA hU)`**,
**`g4ZipRegAStmt_of_X1 (hX1 hSepRep)`**.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core

/-- **The re-zipped field, exactly** (deterministic; area-carrying, off-hull copy of
`Thm18Asm.zipLenC_zipLenDown_field_eq`). -/
theorem zipLenA_zipLenDownA_fld_eq {γ ℓ : ℝ} (hℓ : 0 ≤ ℓ) {c : AreaConfig}
    (hc : Continuous c.drv) (hc0 : c.drv 0 = 0) (hH : c.area Hᶜ = 0)
    (h1 : areaScale c.area = 1) {t a : ℝ} (htdef : lenTimeOpen γ ℓ c.toPair = t)
    (hadef : areaScale (zipCapDownA γ t c).area = a) (ht : 0 < t) (ha : 0 < a)
    (hK : c.area (fwdHull c.drv t ∩ H) = 0) (hsub : fwdHull c.drv t ⊆ curveOf c.drv)
    (hq : IsLenWeldingDriver γ (zipLenDownA γ ℓ c).fld ℓ (revDrv c.drv t a))
    (hrem : RemHull (revDrv c.drv t a)) (hR : D74R.PushRegOffAt γ c.toPair t 0 a) :
    ∃ (G : FieldSample) (K' : Set ℂ),
      (zipLenA γ ℓ (zipLenDownA γ ℓ c)).fld = rescale G (Qc γ) a⁻¹ ∧
      RegEqOff K' G (rescale c.fld (Qc γ) a) ∧
      {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K'} ⊆ curveOf c.drv := by
  rw [zipLenA_of_nonneg hℓ]
  subst hadef
  set a := areaScale (zipCapDownA γ t c).area with hadef
  set q := revDrv c.drv t a with hqdef
  have hc₃ : zipLenDownA γ ℓ c = canonAConfig γ (zipCapDownA γ t c) := by
    rw [zipLenDownA, htdef]
  have hq0 : 0 < q.1 := by simp only [hqdef, revDrv]; positivity
  have hp' := lenWeldDriver_spec ⟨q, hq⟩
  obtain ⟨hT, hEq⟩ := isLenWeldingDriver_eq_of_good hq hq0 hrem hp'
  have hup : zipLenUpA γ ℓ (zipLenDownA γ ℓ c) =
      canonAConfig γ (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)) := by
    rw [zipLenUpA, hT, zipWeldUpA_congr hq0.le hEq.symm]
  have hW'' : Continuous fun s => c.drv (t - s) - c.drv t :=
    (hc.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hfull : c.area.restrict (H \ fwdHull c.drv t) = c.area := by
    refine Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (measure_mono_null ?_
      (measure_union_null hH hK)))
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_and, not_not] at hz
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hz hzH, hzH⟩
    · exact Or.inl hzH
  have harea : (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area =
      c.area.map fun z => ((a : ℂ))⁻¹ * z := by
    have key := zipWeldUpA_canonAConfig_area (γ := γ) ht.le hW'' ha (W₃ := q.2) (fun u _ => rfl)
    rw [zipWeldUpA_zipCapDownA_area ht.le hc hc0, hfull] at key
    rw [hc₃]
    exact key
  have hb : areaScale (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area = a⁻¹ := by
    rw [harea, areaScale_map_inv_mul _ ha, h1, one_div]
  refine ⟨(zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).fld, revHull q.2 q.1, ?_, ?_, ?_⟩
  · rw [hup]
    show rescale (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).fld (Qc γ)
      (areaScale (zipWeldUpA γ q.1 q.2 (zipLenDownA γ ℓ c)).area) = _
    rw [hb]
  · rw [hc₃]
    exact regEqOff_of_coordsOff fun i hi =>
      coordsFull_rezipUp_off (c := c.toPair) hc hc0 ht.le ha hR i hi
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := revHull_revDrv_subset hc hc0 ht ha hw
    have haC : ((a : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast ha.ne')
    have : z = w := by
      push_cast at hzw
      exact mul_left_cancel₀ haC hzw
    exact hsub (this ▸ hz)

/-- Distances scale: points at distance `≥ r` from `K` are mapped by `w ↦ s w` to points at
distance `≥ s r` from any `K'` with `s⁻¹ K' ⊆ K`. -/
theorem far_scale {K K' : Set ℂ} {s : ℝ} (hs : 0 < s)
    (hsub : {w : ℂ | (s : ℂ) * w ∈ K'} ⊆ K) {u : ℂ} {r : ℝ} (hu : ∀ p ∈ K, r ≤ dist u p) :
    ∀ p ∈ K', s * r ≤ dist ((s : ℂ) * u) p := by
  intro p hp
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have e : (s : ℂ) * ((s : ℂ)⁻¹ * p) = p := by rw [← mul_assoc, mul_inv_cancel₀ hsC, one_mul]
  have hp' : (s : ℂ)⁻¹ * p ∈ K := hsub (by show (s : ℂ) * _ ∈ K'; rw [e]; exact hp)
  have hd : dist ((s : ℂ) * u) p = s * dist u ((s : ℂ)⁻¹ * p) := by
    conv_lhs => rw [← e]
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs]
  rw [hd]
  exact mul_le_mul_of_nonneg_left (hu _ hp') hs.le

/-- Circles off `K` are mapped by `w ↦ s w` to circles off any `K'` with `s⁻¹ K' ⊆ K`. -/
theorem circleOff_scale {K K' : Set ℂ} {s : ℝ} (hs : 0 < s)
    (hsub : {w : ℂ | (s : ℂ) * w ∈ K'} ⊆ K) {z : ℂ} {r : ℝ} (hc : CircleOff K z r) :
    CircleOff K' ((s : ℂ) * z) (s * r) := by
  obtain ⟨δ, hδ, hK⟩ := hc
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  refine ⟨s * δ, mul_pos hs hδ, fun w hw hwK => ?_⟩
  set w' : ℂ := (s : ℂ)⁻¹ * w with hw'
  have hww : (s : ℂ) * w' = w := by rw [hw', ← mul_assoc, mul_inv_cancel₀ hsC, one_mul]
  have hdist : dist w ((s : ℂ) * z) = s * dist w' z := by
    rw [← hww, dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
  have h1 : |dist w' z - r| < δ := by
    rw [hdist, ← mul_sub, abs_mul, abs_of_pos hs] at hw
    exact lt_of_mul_lt_mul_left hw hs.le
  refine hK w' h1 (hsub ?_)
  show (s : ℂ) * foldH w' ∈ K'
  rw [← foldH_mul_ofReal hs, hww]
  exact hwK

/-- Raw values of `rescale G Q s` and `rescale G' Q s` agree at every circle off `K`, when `G`
and `G'` agree off `K'` and `s⁻¹ K' ⊆ K`. -/
theorem rescale_fc_congr_off {K K' : Set ℂ} {G G' : FieldSample} (h : RegEqOff K' G G')
    (Q : ℝ) {s : ℝ} (hs : 0 < s) (hsub : {w : ℂ | (s : ℂ) * w ∈ K'} ⊆ K) {z : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hc : CircleOff K z r) :
    rescale G Q s (foldedCircle z r) = rescale G' Q s (foldedCircle z r) := by
  simp only [rescale, coordChange]
  rw [foldedCircle_map_mul hs]
  congr 1
  exact evalReg_foldedCircle_congr_of_regEqOff h (mul_nonneg hs.le hr) (circleOff_scale hs hsub hc)

/-- Raw values of `rescale G Q s` and `rescale G' Q s` agree at every measure whose pushforward
under `w ↦ s w` stays at positive distance from `K'` in the closed upper half-plane. -/
theorem rescale_far_congr_off {K' : Set ℂ} {G G' : FieldSample} (h : RegEqOff K' G G')
    (Q : ℝ) {s : ℝ} {μ : Measure ℂ} {d : ℝ} (hd : 0 < d)
    (hν : ∀ᵐ w ∂(μ.map fun z => (s : ℂ) * z), 0 ≤ w.im ∧ ∀ p ∈ K', d ≤ dist w p) :
    rescale G Q s μ = rescale G' Q s μ := by
  simp only [rescale, coordChange]
  rw [evalReg_congr_of_regEqOff_far h hd hν]

end R18
end QuantumZipper
