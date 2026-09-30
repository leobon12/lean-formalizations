import QuantumZipper.Proofs.Thm18.RT6bFar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6b: zipping up reads only the pieces, test pairings (full N1 from FarPull at `c₀`)

The masked test pairings of `Z^LEN_ℓ` of the pieces and of `Z^LEN_ℓ c₀` agree: a test function
supported off the zipped curve is, after the dilation (1.8), carried by a compact subset of `ℍ`
at positive distance from the (dilated) zipped curve, and the two pulled-back fields agree off it
(`rt6_πd_zipLenUpOA_offConfig`'s regularized identity, from FarPull), so the regularized
evaluations agree (`evalReg_congr_of_regEqOff_far`). With the masked coordinates
(`zipOffExactπAStmt_of_far`) this gives the full node `ZipOffExactAStmt` from `ZipGoodStmt`.
Sheffield arXiv:1012.4797 p. 26 (the zip-up re-welds the two pieces). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- Regularized evaluation of two fields agreeing off `a·K` at the dilation by `a` of a measure
with density supported in a compact subset of `ℍ` disjoint from `K`. -/
theorem rt6b_evalReg_far_support {K : Set ℂ} (hK : IsClosed K) {X Y : FieldSample} {a : ℝ}
    (ha : 0 < a) (h : RegEqOff {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K} X Y) {S : Set ℂ}
    (hS : IsCompact S) (hSH : S ⊆ H) (hSK : Disjoint S K) {g : ℂ → ℝ} (hg : Measurable g)
    (hgS : ∀ z, g z ≠ 0 → z ∈ S) :
    evalReg X ((volume.withDensity fun z => ENNReal.ofReal (g z)).map fun z => (a : ℂ) * z) =
      evalReg Y ((volume.withDensity fun z => ENNReal.ofReal (g z)).map fun z => (a : ℂ) * z) := by
  obtain ⟨r, hr, hsep⟩ := exists_pos_forall_lt_edist hS hK hSK
  have hr' : (0 : ℝ) < r := hr
  have hsep' : ∀ z ∈ S, ∀ q ∈ K, (r : ℝ) ≤ dist z q := fun z hz q hq => by
    have := hsep z hz q hq
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at this
    exact this.1.le
  refine evalReg_congr_of_regEqOff_far h (d := a * r) (by positivity) ?_
  have hm : Measurable fun z : ℂ => (a : ℂ) * z := measurable_const.mul measurable_id
  have hP : MeasurableSet {w : ℂ | 0 ≤ w.im ∧ ∀ p ∈ {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K},
      a * r ≤ dist w p} := by
    refine IsClosed.measurableSet ?_
    have e : {w : ℂ | 0 ≤ w.im ∧ ∀ p ∈ {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K}, a * r ≤ dist w p} =
        {w : ℂ | 0 ≤ w.im} ∩ ⋂ p ∈ {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K}, {w : ℂ | a * r ≤ dist w p} := by
      ext w; simp
    rw [e]
    exact (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_biInter fun p _ => isClosed_le continuous_const (continuous_id.dist continuous_const))
  rw [ae_map_iff hm.aemeasurable hP,
    ae_withDensity_iff (f := fun z => ENNReal.ofReal (g z)) (ENNReal.measurable_ofReal.comp hg)]
  refine ae_of_all _ fun z hz => ?_
  have hzS : z ∈ S := hgS z fun h0 => hz (by simp [h0])
  have hzH : 0 < z.im := hSH hzS
  refine ⟨?_, fun p hp => ?_⟩
  · show 0 ≤ ((a : ℂ) * z).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    positivity
  · have hq := hsep' z hzS _ hp
    have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have e : p = (a : ℂ) * (((a⁻¹ : ℝ) : ℂ) * p) := by
      rw [Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hac, one_mul]
    rw [e, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le,
      ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hq ha.le

/-- **Test pairings of the zip-up of the pieces** (deterministic, from FarPull). -/
theorem rt6b_pair_zipLenUpOA_offConfig {γ ℓ : ℝ} {c : AreaConfig} (hc : Continuous c.drv)
    (hc0 : c.drv 0 = 0)
    (hp : lenWeldDriverO γ (offConfig γ c).fld ℓ = lenWeldDriver γ c.fld ℓ)
    (ha : (offConfig γ c).area = c.area) (hfar : Rt5FarPull γ ℓ c) :
    (offData (zipLenUpOA γ ℓ (offConfig γ c)).toPair).1.2 =
      (offData (zipLenUpA γ ℓ c).toPair).1.2 := by
  classical
  obtain ⟨hD, -⟩ := rt6_zipLenUpOA_offConfig_drv_area hp ha
  obtain ⟨hpos, hgeo⟩ := hfar
  have hreg := regEqOff_offConfig γ hc hc0
  set p := lenWeldDriver γ c.fld ℓ with hpdef
  set a := areaScale (zipWeldUpA γ p.1 p.2 c).area with hadef
  set K := curveOf (zipLenUpA γ ℓ c).drv with hKdef
  have e1 : (zipLenUpOA γ ℓ (offConfig γ c)).fld =
      rescale (coordChange (offConfig γ c).fld (revMapInv p.2 p.1) (Qc γ)) (Qc γ) a := by
    simp only [zipLenUpOA, canonAConfig, zipWeldUpA, zipWeldUp, AreaConfig.toPair, hp, ha, hadef]
  have e2 : (zipLenUpA γ ℓ c).fld =
      rescale (coordChange c.fld (revMapInv p.2 p.1) (Qc γ)) (Qc γ) a := rfl
  have h1 : RegEqOff {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K}
      (coordChange (offConfig γ c).fld (revMapInv p.2 p.1) (Qc γ))
      (coordChange c.fld (revMapInv p.2 p.1) (Qc γ)) :=
    regEqOff_coordChange_of_pull (Qc γ) fun d k hck => by
      obtain ⟨δ, hδ, hν⟩ := hgeo d k hck
      exact evalReg_congr_of_regEqOff_far hreg hδ hν
  have hcur : curveOf (zipLenUpOA γ ℓ (offConfig γ c)).drv = K := by rw [hD]
  funext ρ
  show (if Disjoint (tsupport ρ.1) (curveOf (zipLenUpOA γ ℓ (offConfig γ c)).drv) then
      pairRaw (zipLenUpOA γ ℓ (offConfig γ c)).fld ρ.1 else 0) =
    (if Disjoint (tsupport ρ.1) K then pairRaw (zipLenUpA γ ℓ c).fld ρ.1 else 0)
  rw [hcur]
  split_ifs with hd
  · obtain ⟨hρc, hρs, hρH⟩ := ρ.2
    have hS : IsCompact (tsupport ρ.1) := hρs
    have hmeas : Measurable ρ.1 := hρc.continuous.measurable
    have k1 := rt6b_evalReg_far_support (D74.isClosed_curveOf _) hpos h1 hS hρH hd hmeas
      (g := ρ.1) (fun z hz => subset_tsupport _ hz)
    have k2 := rt6b_evalReg_far_support (D74.isClosed_curveOf _) hpos h1 hS hρH hd
      (g := fun z => -ρ.1 z) hmeas.neg (fun z hz => subset_tsupport _ (neg_ne_zero.mp hz))
    have hres : ∀ (x : FieldSample) (μ : Measure ℂ), rescale x (Qc γ) a μ =
        evalReg x (μ.map fun z => (a : ℂ) * z) +
          Qc γ * ∫ z, Real.log ‖deriv (fun z => (a : ℂ) * z) z‖ ∂μ := fun _ _ => rfl
    unfold pairRaw
    rw [e1, e2, hres, hres, hres, hres, k1, k2]
  · rfl

/-- **Full N1 from the goodness of the zipped driver.** -/
theorem zipOffExactAStmt_of_good (hX1 : BaseFin.BaseFiniteStmt) (hZG : ZipGoodStmt) :
    ZipOffExactAStmt := by
  have hF := zipFarWedgeStmt_of_good hX1 hZG
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  filter_upwards [ae_lenWeldDriverO_offConfig_wedge hS hIn, ae_wedgeAConfig_area_eq hS hIn,
    hF γ P B Y hS hIn ℓ hℓ, D74.ae_wedgeConfig_snd_good hS] with ω hp ha hfar hg
  have hπ := rt6_πd_zipLenUpOA_offConfig hg.1 hg.2 (hp ℓ) ha.symm hfar
  have hpr := rt6b_pair_zipLenUpOA_offConfig hg.1 hg.2 (hp ℓ) ha.symm hfar
  set X := offData (zipLenUpOA γ ℓ (offConfig γ (wedgeAConfig γ B Y ω))).toPair
  set X' := offData (zipLenUpA γ ℓ (wedgeAConfig γ B Y ω)).toPair
  have A : X.1.1 = X'.1.1 := congrArg (fun e : (ℕ → ℝ) × (ℝ≥0 → ℝ) => e.1) hπ
  have C : X.2 = X'.2 := congrArg (fun e : (ℕ → ℝ) × (ℝ≥0 → ℝ) => e.2) hπ
  exact Prod.ext (Prod.ext A hpr) C

end R18
end QuantumZipper
