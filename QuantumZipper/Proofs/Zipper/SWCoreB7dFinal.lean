import QuantumZipper.Proofs.Zipper.SWCoreB7dMain
import QuantumZipper.Proofs.RS.TraceShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7d (8): the identifications and `AnchorUnifFamExtAllStmt`

* `ident_zero`, `live_zero`: the anchor `q = 0` (pair `(B, X)`);
* `ident_pos`, `live_pos`: a rational anchor `q > 0` (pair `(B^q, Y_q)`, `B^q = B(q + ·) − B q`,
  `Y_q` the free field of `Cor15Group.cor15UnzipVersionStmt_holds`, independent of the shifted
  path);
* **`anchorUnifFamExtStmt_holds`**, **`anchorUnifFamExtAllStmt_holds`**.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun B2 RevMapExtension

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- The unzipping map of a continuous driver agrees on `ℍ` with the extended reverse map. -/
theorem fwdMapInv_eq_revMapExt {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {σ : ℝ}
    (hσ : 0 ≤ σ) : EqOn (fwdMapInv W σ) (revMapExt (vrev W σ) σ) H := by
  intro w hw
  rw [revMapExt_eq_revMap (continuous_vrev hW _) hσ hw,
    UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hW hW0 hσ hw]
  exact ReverseFlow.revMap_congr_drive w (fun r hr => (vrev_of_mem hr).symm)

theorem ident_zero (κ : ℝ) (hB : IsBrownianReal B P) (T u v : ℝ) (f : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - ((0 : ℚ) : ℝ)) → ∀ k : ℕ,
      RegUnif.awInt κ T B X ω u v f (((0 : ℚ) : ℝ) + σ) k =
        pairJ κ (T - ((0 : ℚ) : ℝ)) B X ω u v f σ k := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc h0 σ hσ k
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  simp only [Rat.cast_zero, zero_add, sub_zero] at hσ ⊢
  unfold RegUnif.awInt pairJ
  rw [h0f_eq_unzippedField]
  have := bdryApprox_coordChange_congr_onH (Real.sqrt κ) (ofFun (h0rev κ) + X ω)
    (fwdMapInv_eq_revMapExt hW hW0 hσ.1) (Qc (Real.sqrt κ)) k
  simp only [unzippedField, cfg] at this ⊢
  rw [this]
  rfl

theorem live_zero {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) {T : ℝ}
    (hT : 0 < T) (v : ℝ) :
    ∀ᵐ ω ∂P, v < zeroMinus (Vr κ T B ω) (T - ((0 : ℚ) : ℝ)) →
      ENNReal.ofReal (T - ((0 : ℚ) : ℝ)) < realHitTime (vrev (drive κ B ω) (T - ((0 : ℚ) : ℝ))) v := by
  filter_upwards [hB.cont, B5.ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hc hK hv
  simp only [Rat.cast_zero, sub_zero] at hv ⊢
  have hVc : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hV0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
  exact (B5.mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK hT.le le_rfl hv).2

/-- The shifted Brownian motion `B(q + ·) − B q`. -/
def shB (q : ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun u ω => B (q.toNNReal + u) ω - B q.toNNReal ω

theorem vrev_shB_eqOn (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) {q : ℝ} (hq : 0 ≤ q) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    EqOn (vrev (drive κ (shB q B) ω) τ) (vrev (drive κ B ω) (q + τ)) (Icc 0 τ) := by
  intro r hr
  rw [vrev_of_mem hr, vrev_of_mem (⟨hr.1, by linarith [hr.2]⟩ : r ∈ Icc (0 : ℝ) (q + τ))]
  have hq' : ((q.toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal q hq
  have e1 := RS.drive_shift κ B q.toNNReal ω (u := τ - r) (by linarith [hr.2])
  have e2 := RS.drive_shift κ B q.toNNReal ω (u := τ) hτ
  rw [show shB q B = fun r ω => B (q.toNNReal + r) ω - B q.toNNReal ω from rfl, e1, e2, hq',
    show q + τ - r = q + (τ - r) by ring]
  ring

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem continuous_drive_shB (κ : ℝ) {ω : Ω} (hc : Continuous fun t : ℝ≥0 => B t ω) (q : ℝ) :
    Continuous (drive κ (shB q B) ω) := by
  refine drive_continuous ?_
  simp only [shB]
  fun_prop

theorem ident_pos (κ : ℝ) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {q : ℚ} (hq : (0 : ℝ) < q) {Y : Ω → FieldSample}
    (hreg : ∀ᵐ ω ∂P, RegEq (h0f κ q B X ω) (ofFun (h0rev κ) + Y ω)) (T u v : ℝ)
    (f : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) → ∀ k : ℕ,
      RegUnif.awInt κ T B X ω u v f ((q : ℝ) + σ) k =
        pairJ κ (T - q) (shB q B) Y ω u v f σ k := by
  filter_upwards [hreg, RegUnif.ae_bdryApprox_h0f_eq_coordChange (κ := κ) hB hX hind hq.le,
    hB.cont] with ω hR hbd hc σ hσ k
  have hs : (q : ℝ) ≤ ((q + σ : ℚ) : ℝ) := by push_cast; linarith [hσ.1]
  have hcast : ((q + σ : ℚ) : ℝ) = (q : ℝ) + σ := by push_cast; ring
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  unfold RegUnif.awInt pairJ
  rw [← hcast, hbd (q + σ) hs, coordChange_congr_regEq hR, hcast]
  have hmap : EqOn (RegUnif.acMap κ B ω q ((q : ℝ) + σ))
      (revMapExt (vrev (drive κ (shB q B) ω) σ) σ) H := by
    intro w hw
    simp only [RegUnif.acMap, Vr]
    rw [show (q : ℝ) + σ - q = σ by ring,
      ← revMapExt_eq_revMap (continuous_vrev hWc _) hσ.1 hw]
    exact revMapExt_congr_drive (fun r hr => (vrev_shB_eqOn κ B ω hq.le hσ.1 hr).symm) w
  rw [bdryApprox_coordChange_congr_onH _ _ hmap]
  have hT0 : 0 ≤ T - q := hσ.1.trans hσ.2
  have hwin : realRevMap (Vr κ T B ω) (T - ((q : ℝ) + σ)) =
      realRevMap (vrev (drive κ (shB q B) ω) (T - q)) (T - q - σ) := by
    funext x
    rw [show T - ((q : ℝ) + σ) = T - q - σ by ring]
    refine B5.realRevMap_congr_drive' (fun r hr => ?_) x
    have h := vrev_shB_eqOn κ B ω hq.le hT0 (⟨hr.1, by linarith [hr.2, hσ.1]⟩ :
      r ∈ Icc (0 : ℝ) (T - q))
    rw [show (q : ℝ) + (T - q) = T by ring] at h
    exact h.symm
  rw [hwin]

theorem live_pos {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) {T : ℝ}
    (hT : 0 < T) {q : ℝ} (hq : 0 ≤ q) (hqT : q < T) (v : ℝ) :
    ∀ᵐ ω ∂P, v < zeroMinus (Vr κ T B ω) (T - q) →
      ENNReal.ofReal (T - q) < realHitTime (vrev (drive κ (shB q B) ω) (T - q)) v := by
  filter_upwards [hB.cont, B5.ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hc hK hv
  have hVc : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hV0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
  have hL := (B5.mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK (by linarith) (by linarith) hv).2
  have hEq : EqOn (Vr κ T B ω) (vrev (drive κ (shB q B) ω) (T - q)) (Icc 0 (T - q)) := by
    intro r hr
    have h := vrev_shB_eqOn κ B ω hq (by linarith : (0 : ℝ) ≤ T - q) hr
    rw [show q + (T - q) = T by ring] at h
    exact h.symm
  exact (isLive_congr_drive hVc (continuous_vrev (continuous_drive_shB κ hc q) _)
    (by linarith) hEq).1 hL

/-- **AC-fam-ext at one horizon** (SWC-B7). -/
theorem anchorUnifFamExtStmt_holds {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {T : ℝ} (hT : 0 < T) : RegUnif.AnchorUnifFamExtStmt κ T P B X := by
  intro q hq hqT u v i a b c d
  by_cases hord : (u : ℝ) < a ∧ (a : ℝ) < b ∧ (b : ℝ) < c ∧ (c : ℝ) < d ∧ (d : ℝ) < v
  swap
  · exact ae_of_all _ fun ω h1 h2 h3 h4 h5 _ => absurd ⟨h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4, h5⟩ hord
  obtain ⟨h1, h2, h3, h4, h5⟩ := hord
  rcases hq.eq_or_lt with hq0 | hq0
  · -- anchor `0`: the pair `(B, X)`
    have hq0' : q = 0 := by exact_mod_cast hq0.symm
    subst hq0'
    filter_upwards [acfam_of_pair hκ hκ4 hqT h1 h2 h3 h4 h5 hB hX hind
      (ident_zero κ hB T u v _) (live_zero hκ hκ4 hB hT v)] with ω hω
    intro _ _ _ _ _ hv
    exact hω hv
  · -- rational anchor `q > 0`: the pair `(B^q, Y_q)`
    obtain ⟨Y, -, hYf, hYind, hreg⟩ :=
      Cor15Group.cor15UnzipVersionStmt_holds κ hκ hκ4 P B X ⟨hB, hX, hind⟩ q hq0
    have hreg' : ∀ᵐ ω ∂P, RegEq (h0f κ q B X ω) (ofFun (h0rev κ) + Y ω) := by
      filter_upwards [hreg] with ω h
      rw [h0f_eq_zipCapDown]; exact h
    have hBq : IsBrownianReal (shB q B) P := hB.shift (q : ℝ).toNNReal
    have hindq : IndepFun (pathOf (shB q B)) Y P := hYind
    filter_upwards [acfam_of_pair hκ hκ4 hqT h1 h2 h3 h4 h5 hBq hYf hindq
      (ident_pos κ hB hX hind hq0 hreg' T u v _) (live_pos hκ hκ4 hB hT hq hqT v)] with ω hω
    intro _ _ _ _ _ hv
    exact hω hv

/-- **`RegUnif.AnchorUnifFamExtAllStmt`** (SWC-B7): AC-fam-ext at every horizon, for the pair
and its reflection. -/
theorem anchorUnifFamExtAllStmt_holds {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    RegUnif.AnchorUnifFamExtAllStmt κ P B X :=
  ⟨fun T hT => anchorUnifFamExtStmt_holds hκ hκ4 hB hX hind hT,
    fun T hT => anchorUnifFamExtStmt_holds hκ hκ4 hB.neg
      (RegUnif.isFreeGFFModConstH_reflRaw hX) (RegUnif.indepFun_neg_reflRaw hind) hT⟩

end SWCore
end QuantumZipper
