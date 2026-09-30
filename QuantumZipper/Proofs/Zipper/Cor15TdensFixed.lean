import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame
import QuantumZipper.Proofs.Field.TRegE4
import QuantumZipper.Proofs.Zipper.E1TransferRep

/-!
# COR15-TDENS (1): regularity of the unzipped field at pushed test densities, fixed driver

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
Analogue of `ae_evalReg_coordChange_pushed_fc` (`Cor15RezipRegTame`) for the measures
`σ = tdens a` (`a` one of `±ρ`, bounded continuous density with compact support in `ℍ`) instead
of folded circles, together with the convergence form `E1.RegShift`.

For a deterministic driver `V` with the Hölder bound on `revMap V t` and the polynomial mass bound
of the hull neighbourhoods, a.s. in the free field `X` the field
`y = coordChange (𝔥₀ + X) (revMap V t) Q` satisfies `RegShift y ν` and `evalReg y ν = y ν` for
`ν = (tdens a).map (revMapInv V t)`.

**Analytic input:** RC3 for general measures (`CoordReg.ae_regShift_coordChange_revMap_gen`,
`CoordReg.ae_evalReg_coordChange_revMap_gen`; Duplantier–Sheffield, *Liouville quantum gravity and
KPZ*, Invent. Math. 185 (2011), Prop. 3.1). **Own elementary argument:** the check of its
hypotheses for the normalized measure `ϖ.map (revMapInv V t)`, `ϖ = (tdens a univ)⁻¹ • tdens a`
(Frostman exponent `2β` from the density bound and the Hölder bound, strip masses from
`Im ≥ δ` on the support and the hull-neighbourhood bound), and the linear rescaling back to
`tdens a` (all defining limits exist, so no junk `limUnder`), as in `TRegE4.ae_evalReg_Y1_tdens`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal Real

namespace QuantumZipper
namespace Cor15Group

open CharFun

variable {V : ℝ → ℝ} {t : ℝ}

/-- `RegShift` is stable under multiplying the measure by a finite constant. -/
theorem regShift_smul_measure {y : FieldSample} {ν : Measure ℂ} (h : E1.RegShift y ν)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) : E1.RegShift y (c • ν) := by
  obtain ⟨h1, h2, L, hL⟩ := h
  refine ⟨Measure.ae_smul_measure h1 c, fun k => (h2 k).smul_measure hc, c.toReal * L, ?_⟩
  simp_rw [integral_smul_measure, smul_eq_mul]
  exact hL.const_mul _

section Fixed

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Regularity at a pushed test density, fixed driver.** -/
theorem ae_regShift_evalReg_pushed_tdens (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    (κ Q : ℝ) (hV : Continuous V) (hV0 : V 0 = 0) (ht : 0 < t)
    {a : ℂ → ℝ} {K : Set ℂ} {Md δ : ℝ} (hd : Dens a K Md δ) {R₀ : ℝ}
    (hR₀ : K ⊆ closedBall 0 R₀)
    (hK : tdens a (H \ revMap V t '' H) = 0) {S : Set ℂ}
    (hS : H \ revMap V t '' H ⊆ S) {M : ℝ} (hM : ∀ r ∈ Icc (0 : ℝ) t, |V r| ≤ M) {C β : ℝ}
    (hC : 0 < C) (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ R₀ + (12 * M + 8 * Real.sqrt t) →
      ‖w‖ ≤ R₀ + (12 * M + 8 * Real.sqrt t) →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      tdens a {z | infDist z S ≤ ε} ≤ ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ))) :
    ∀ᵐ ω ∂P,
      E1.RegShift (coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q)
          ((tdens a).map (revMapInv V t)) ∧
      evalReg (coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q)
          ((tdens a).map (revMapInv V t)) =
        coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q
          ((tdens a).map (revMapInv V t)) := by
  have : IsFiniteMeasure (tdens a) := hd.admissible.1
  set m := tdens a univ with hmdef
  by_cases hm0 : m = 0
  · have h0 : tdens a = 0 := Measure.measure_univ_eq_zero.1 hm0
    refine ae_of_all _ fun ω => ?_
    rw [h0, Measure.map_zero]
    refine ⟨⟨by simp, fun k => integrable_zero_measure, 0, by simp⟩, ?_⟩
    simp only [coordChange, Measure.map_zero, TReg.evalReg_zero, integral_zero_measure,
      mul_zero, add_zero]
  have hmt : m ≠ ⊤ := measure_ne_top _ _
  obtain ⟨ϖ, hϖdef⟩ : ∃ ϖ : Measure ℂ, ϖ = m⁻¹ • tdens a := ⟨_, rfl⟩
  have hϖP : IsProbabilityMeasure ϖ := ⟨by
    rw [hϖdef, Measure.smul_apply, smul_eq_mul, ← hmdef, ENNReal.inv_mul_cancel hm0 hmt]⟩
  have htd : tdens a = m • ϖ := by
    rw [hϖdef, smul_smul, ENNReal.mul_inv_cancel hm0 hmt, one_smul]
  have hϖK : ϖ Kᶜ = 0 := by
    rw [hϖdef, Measure.smul_apply, hd.tdens_compl, smul_zero]
  have hϖhull : ϖ (H \ revMap V t '' H) = 0 := by
    rw [hϖdef, Measure.smul_apply, hK, smul_zero]
  have hϖKae : ∀ᵐ z ∂ϖ, z ∈ K := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hϖK] with z hz
    simpa using hz
  have hϖD : ∀ᵐ z ∂ϖ, z ∈ revMap V t '' H := by
    filter_upwards [hϖKae, measure_eq_zero_iff_ae_notMem.1 hϖhull] with z hzK hz
    by_contra hc'
    exact hz ⟨hd.subH hzK, hc'⟩
  set ρ := R₀ + (12 * M + 8 * Real.sqrt t) with hρ
  have hϖρ : ∀ᵐ z ∂ϖ, ‖revMapInv V t z‖ ≤ ρ := by
    filter_upwards [hϖKae, hϖD] with z hzK hz
    have h1 := mem_closedBall_zero_iff.1 (hR₀ hzK)
    exact (norm_revMapInv_le hV hV0 ht hM hz).trans (by rw [hρ]; linarith)
  set ν := ϖ.map (revMapInv V t) with hν
  have hνP : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_revMapInv hV ht.le).aemeasurable).2
      inferInstance
  have hsupp := map_revMapInv_compl_closedBall_Hbar hV ht.le hϖD hϖρ
  have hνH := ae_mem_H_map_revMapInv hV ht.le hϖD
  -- Frostman bounds
  have hle : ϖ ≤ (m⁻¹ * (Md.toNNReal : ℝ≥0∞)) • volume := by
    rw [hϖdef, ← smul_smul]
    intro s
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr
    exact hd.tdens_le
  set K₁ := (m⁻¹ * (Md.toNNReal : ℝ≥0∞)).toReal * π with hK₁
  have hFϖ : IsFrostman ϖ 2 K₁ := TRegE4.isFrostman_of_le_smul_volume
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hm0) ENNReal.coe_ne_top) hle
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hF : IsFrostman ν (β * 2) (K₁ * C ^ (2 : ℝ) * 2 ^ (β * 2)) := by
    intro p s hs
    obtain ⟨z₀, hz₀⟩ := map_revMapInv_closedBall_le hV ht.le hC.le hβ hHol hϖD hϖρ p s
    have h1 := hFϖ z₀ (C * (2 * s) ^ β) (by positivity)
    refine (ENNReal.toReal_mono (measure_ne_top _ _) hz₀).trans (h1.trans (le_of_eq ?_))
    rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul (by positivity),
      Real.mul_rpow (by norm_num) hs.le]
    ring
  have hFf : IsFrostman (ν.map (revMap V t)) 2 K₁ := by
    rw [hν, map_revMap_map_revMapInv hV ht.le hϖD]
    exact hFϖ
  -- strip masses
  set A' := (1 / δ) ^ (1 / 8 : ℝ) + m⁻¹.toReal * c + 1 with hA'
  have hA'1 : 1 ≤ A' := by
    have : 0 ≤ (1 / δ) ^ (1 / 8 : ℝ) := by have := hd.delta; positivity
    have : 0 ≤ m⁻¹.toReal * c := mul_nonneg ENNReal.toReal_nonneg hc0
    linarith
  have hpow : ∀ τ : ℝ, 0 < τ →
      ν {z | z.im < τ} ≤ ENNReal.ofReal (A' * C ^ (1 / 8 : ℝ) * τ ^ (β / 8)) := by
    intro τ hτ
    set x := C * τ ^ β with hx
    have hx0 : 0 < x := by positivity
    have hxe : C ^ (1 / 8 : ℝ) * τ ^ (β / 8) = x ^ (1 / 8 : ℝ) := by
      rw [hx, Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul hτ.le]
      congr 2
      ring
    rw [mul_assoc, hxe]
    have hx8 : 0 ≤ x ^ (1 / 8 : ℝ) := by positivity
    by_cases hx1 : x ≤ 1
    · have hmono : ν {z | z.im < τ} ≤ ν {z | z.im ≤ τ} :=
        measure_mono fun z (hz : z.im < τ) => (le_of_lt hz : z.im ≤ τ)
      refine hmono.trans ((map_revMapInv_im_le hV ht.le hS hC.le hβ hHol hϖD hϖρ τ).trans ?_)
      have h1 : ϖ {z | z.im ≤ x} ≤ ENNReal.ofReal ((1 / δ) ^ (1 / 8 : ℝ) * x ^ (1 / 8 : ℝ)) := by
        by_cases hxδ : x ≤ δ
        · refine le_trans (le_of_eq (measure_mono_null (fun z (hz : z.im ≤ x) => ?_) hϖK)) bot_le
          intro hzK
          have := hd.sub hzK
          change δ < z.im at this
          linarith
        · push Not at hxδ
          refine prob_le_one.trans ?_
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.mul_rpow (by have := hd.delta; positivity) hx0.le]
          exact Real.one_le_rpow (by rw [one_div_mul_eq_div, one_le_div hd.delta]; exact hxδ.le)
            (by norm_num)
      have h2 : ϖ {z | infDist z S ≤ x} ≤ ENNReal.ofReal (m⁻¹.toReal * c * x ^ (1 / 8 : ℝ)) := by
        rw [hϖdef, Measure.smul_apply, smul_eq_mul]
        refine (mul_le_mul_right (hc x hx0 hx1) _).trans (le_of_eq ?_)
        rw [mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hm0)]
      refine (add_le_add h1 h2).trans ?_
      rw [← ENNReal.ofReal_add (by have := hd.delta; positivity)
        (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hc0) hx8)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hA']
      nlinarith
    · push Not at hx1
      refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 1 ≤ x ^ (1 / 8 : ℝ) := Real.one_le_rpow hx1.le (by norm_num)
      nlinarith
  have hA0 : 0 ≤ A' * C ^ (1 / 8 : ℝ) := by
    have := hC.le; positivity
  have hβ8 : 0 < β / 8 := by positivity
  have hSt := stripBound_of_pow hνH hA0 hβ8 hpow
  have hR : ∀ᵐ z ∂ν, z.im ≤ ρ := by
    filter_upwards [(mem_ae_iff.2 hsupp : ∀ᵐ z ∂ν, z ∈ closedBall (0 : ℂ) ρ ∩ Hbar)] with z hz
    have h1 := hz.1
    rw [mem_closedBall, dist_zero_right] at h1
    exact (Complex.im_le_norm z).trans h1
  have hlν := integrable_abs_log_im_of_pow hνH hR hA0 hβ8 hpow
  have hsuppϖ : ϖ (closedBall 0 R₀ ∩ Hbar)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 fun z hz => ⟨hR₀ hz, H_subset_Hbar (hd.subH hz)⟩)
      hϖK
  have hA := CoordReg.ae_regShift_coordChange_revMap_gen hV ht.le hX (P := P)
    (2 / Real.sqrt κ) (g₁ := fun _ => 0) continuous_const Q hsupp hνH hF (by positivity) hlν hSt
    (by positivity) hFf two_pos
  have hB := CoordReg.ae_evalReg_coordChange_revMap_gen hV ht.le hX (P := P)
    (2 / Real.sqrt κ) (g₁ := fun _ => 0) continuous_const Q hsupp hνH hF (by positivity) hlν hSt
    (by positivity) hFf two_pos
  have hCc := CoordReg.ae_tendsto_integral_avgReg_logAdd_frostman hX (P := P) hsuppϖ hFϖ two_pos
    (2 / Real.sqrt κ) (g₁ := fun _ => 0) continuousOn_const
  rw [← CoordReg.h0rev_eq_logAdd κ] at hA hB hCc
  filter_upwards [hA, hB, hCc] with ω hA hB hCc
  obtain ⟨hreg, hint, L, hL⟩ := hA
  have hνeq : (tdens a).map (revMapInv V t) = m • ν := by
    rw [htd, Measure.map_smul]
    exact (measurable_revMapInv hV ht.le).aemeasurable
  rw [hνeq]
  have hRS : E1.RegShift (coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q) ν := by
    refine ⟨hνH.mono fun z hz k => ?_, hint, L, hL⟩
    obtain ⟨F, -, hF2, -⟩ := hreg
    exact ⟨_, hF2 k z (H_subset_Hbar hz)⟩
  refine ⟨regShift_smul_measure hRS hmt, ?_⟩
  have hL' : evalReg (coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q) ν = L :=
    hL.limUnder_eq
  rw [TRegE4.evalReg_smul_of_tendsto hL m, ← hL', hB]
  unfold coordChange
  rw [Measure.map_smul, hν, map_revMap_map_revMapInv hV ht.le hϖD,
    TRegE4.evalReg_smul_of_tendsto hCc m, integral_smul_measure, smul_eq_mul,
    show evalReg (ofFun (h0rev κ) + X ω) ϖ = (ofFun (h0rev κ) + X ω) ϖ from hCc.limUnder_eq]
  · ring
  · exact (TwoPoint.measurable_revMap hV ht.le).aemeasurable

end Fixed

end Cor15Group
end QuantumZipper
