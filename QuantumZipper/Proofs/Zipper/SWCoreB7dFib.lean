import QuantumZipper.Proofs.Zipper.SWCoreB7dEv
import QuantumZipper.Proofs.Zipper.SWCoreB7cBox
import QuantumZipper.Proofs.Zipper.SWCoreB7bIdent
import QuantumZipper.Proofs.Zipper.UnzipInvariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7d (5): the fixed-path fibre of the transfer event

For a good path `e ∈ C([0,T'])` (`Wof κ T' e 0 = 0`, the window `[u,v]`, `v < 0`, live for the
reversed driver up to `T'`) and every free field `Y`, almost surely the countable event
`EvQ` holds (`evQ_fibre`). Proof: `flow_fixed_conv` for the driver `W̃ r = Wof κ T' e (r − q)` with
anchor `q > 0` and horizon `T = T' + q`, identified with the proxies:

* `vrev_shiftW`: `vrev W̃ T = vrev (Wof κ T' e) T'`, and `vrev W̃ s = vrev (Wof κ T' e) (s−q)` on
  `[0, s − q]`;
* `integral_bdryApprox_eq_dens`: the `bdryApprox` integral as a Lebesgue integral with density;
* `avgReg_flow_eq_AvgQ`: the density of `coordChange (𝔥₀ + y) ψ_s Q` is read by `AvgQ`;
* `awProxy_congr`, `awTest_eq_awProxy`, `FmR_eq`: the test function.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun B2 RevMapExtension

/-- The Bochner integral against `bdryApprox` as a Lebesgue integral with density. -/
theorem integral_bdryApprox_eq_dens (γ : ℝ) (z : FieldSample) (k : ℕ) (g : ℝ → ℝ) :
    ∫ t, g t ∂bdryApprox γ z k =
      ∫ t, g t * (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg z k (t : ℂ))) := by
  have hD : Measurable fun t : ℝ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg z k (t : ℂ))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_avgReg_real z k))))
  unfold bdryApprox
  rw [integral_withDensity_eq_integral_toReal_smul₀ hD.aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have hr : 0 ≤ radius k ^ (γ ^ 2 / 4) := Real.rpow_nonneg (radius_pos k).le _
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg hr (Real.exp_pos _).le), mul_comm]

theorem awProxy_congr {F G : ℝ → ℝ} {u v : ℝ} (h : EqOn F G (Icc u v)) (huv : u ≤ v)
    (f : ℝ → ℝ) : awProxy F u v f = awProxy G u v f := by
  have hi : ∀ x, invQ F u v x = invQ G u v x := by
    intro x
    unfold invQ
    congr 1
    funext y
    by_cases hy : (y : ℝ) ∈ Icc u v
    · rw [h hy]
    · simp [hy]
  funext x
  unfold awProxy
  rw [h ⟨le_rfl, huv⟩, h ⟨huv, le_rfl⟩, hi]

/-- The shifted driver on `ℝ`. -/
def shiftW (κ q : ℝ) {T' : ℝ} (hT' : 0 ≤ T') (e : C(Icc (0 : ℝ) T', ℝ)) (r : ℝ) : ℝ :=
  Wof κ T' hT' e (r - q)

theorem Wof_proj_eq {κ T' : ℝ} (hT' : 0 ≤ T') (e : C(Icc (0 : ℝ) T', ℝ)) {a b : ℝ}
    (h : projIcc 0 T' hT' a = projIcc 0 T' hT' b) : Wof κ T' hT' e a = Wof κ T' hT' e b := by
  simp only [Wof, h]

theorem vrev_shiftW (κ q : ℝ) (hq : 0 ≤ q) {T' : ℝ} (hT' : 0 ≤ T') (e : C(Icc (0 : ℝ) T', ℝ)) :
    vrev (shiftW κ q hT' e) (T' + q) = vrev (Wof κ T' hT' e) T' := by
  funext r
  simp only [vrev, shiftW]
  have e1 : T' + q - q = T' := by ring
  rw [e1]
  congr 1
  refine Wof_proj_eq hT' e ?_
  apply Subtype.ext
  simp only [coe_projIcc]
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem vrev_shiftW_eqOn (κ q : ℝ) (hq : 0 ≤ q) {T' : ℝ} (hT' : 0 ≤ T') (e : C(Icc (0 : ℝ) T', ℝ))
    {s : ℝ} (hqs : q ≤ s) :
    EqOn (vrev (shiftW κ q hT' e) s) (vrev (Wof κ T' hT' e) (s - q)) (Icc 0 (s - q)) := by
  intro r hr
  rw [vrev_of_mem (⟨hr.1, by linarith [hr.2]⟩ : r ∈ Icc (0 : ℝ) s), vrev_of_mem hr]
  simp only [shiftW]
  congr 2 <;> ring_nf

theorem continuous_shiftW (κ q : ℝ) {T' : ℝ} (hT' : 0 ≤ T') (e : C(Icc (0 : ℝ) T', ℝ)) :
    Continuous (shiftW κ q hT' e) :=
  (continuous_Wof κ T' hT' e).comp (continuous_id.sub continuous_const)

variable (κ : ℝ) {T' : ℝ} (hT' : 0 ≤ T')

/-- **The density of the transported anchor field is read by `AvgQ`.** -/
theorem avgReg_flow_eq_AvgQ {q : ℝ} (hq : 0 ≤ q) {e : C(Icc (0 : ℝ) T', ℝ)}
    (he : e ∈ MeasUnzip.PZ hT' κ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T') (y : FieldSample) (k : ℕ)
    (t : ℝ) :
    avgReg (coordChange (ofFun (h0rev κ) + y) (flowFam (shiftW κ q hT' e) q
        ![q + σ, shiftW κ q hT' e (q + σ)]) (Qc (Real.sqrt κ))) k (t : ℂ) =
      RegUnif.AvgQ hT' κ (Real.sqrt κ) σ k ((e, y), (t : ℂ)) := by
  rw [RegUnif.AvgQ_eq_avgReg hT' he hσ]
  have hW : Continuous (Wof κ T' hT' e) := continuous_Wof κ T' hT' e
  have hW0 : Wof κ T' hT' e 0 = 0 := he
  have hEq : EqOn (flowFam (shiftW κ q hT' e) q ![q + σ, shiftW κ q hT' e (q + σ)])
      (fwdMapInv (Wof κ T' hT' e) σ) H := by
    intro w hw
    rw [flowFam_diag, show q + σ - q = σ by ring,
      revMapExt_eq_revMap (continuous_vrev (continuous_shiftW κ q hT' e) _) hσ.1 hw,
      UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hW hW0 hσ.1 hw]
    refine ReverseFlow.revMap_congr_drive w (fun r hr => ?_)
    have h1 := vrev_shiftW_eqOn κ q hq hT' e (s := q + σ) (by linarith [hσ.1])
      (show r ∈ Icc (0 : ℝ) (q + σ - q) by rw [show q + σ - q = σ by ring]; exact hr)
    rw [h1, show q + σ - q = σ by ring, vrev_of_mem hr]
  have e2 : avgReg (coordChange (ofFun (h0rev κ) + y) (flowFam (shiftW κ q hT' e) q
      ![q + σ, shiftW κ q hT' e (q + σ)]) (Qc (Real.sqrt κ))) k =
      avgReg (coordChange (ofFun (h0rev κ) + y) (fwdMapInv (Wof κ T' hT' e) σ)
        (Qc (Real.sqrt κ))) k := by
    funext z
    unfold avgReg
    congr 1
    funext n
    exact coordChange_congr_onH _ hEq _ (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))
  rw [e2]
  rfl

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
/-- **The fixed-path fibre of the transfer event.** -/
theorem evQ_fibre {q : ℝ} (hq0 : 0 < q) {e : C(Icc (0 : ℝ) T', ℝ)}
    (he : e ∈ MeasUnzip.PZ hT' κ) {u v : ℝ} (huv : u < v) (hv0 : v < 0)
    (hlive : ENNReal.ofReal T' < realHitTime (vrev (Wof κ T' hT' e) T') v)
    {u₂ v₂ : ℝ} (hu₂ : u < u₂) (hu₂v₂ : u₂ ≤ v₂) (hv₂ : v₂ < v) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc u₂ v₂) (hκ : 0 < κ) (hκ4 : κ < 4)
    (Y : Ω → FieldSample) (hY : IsFreeGFFModConstH Y P) :
    ∀ᵐ ω ∂P, EvQ κ hT' u v f (e, Y ω) := by
  set W := shiftW κ q hT' e with hWdef
  have hWc : Continuous W := continuous_shiftW κ q hT' e
  set V := vrev (Wof κ T' hT' e) T' with hVdef
  have hVc : Continuous V := continuous_vrev (continuous_Wof κ T' hT' e) T'
  have hV0 : V 0 = 0 := vrev_zero hT'
  have hvrev : vrev W (T' + q) = V := vrev_shiftW κ q hq0.le hT' e
  have hLiveV : ∀ x ∈ Icc u v, ENNReal.ofReal T' < realHitTime V x := fun x hx =>
    lt_of_lt_of_le hlive (Collision.realHitTime_anti hVc hx.2 (by rw [hV0]; exact hv0))
  have hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T' + q - q) < realHitTime (vrev W (T' + q)) x := by
    intro x hx; rw [hvrev, show T' + q - q = T' by ring]; exact hLiveV x hx
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  have hmain := flow_fixed_conv (P := P) hWc hq0 (by linarith : q ≤ T' + q)
    (show u < (u + u₂) / 2 by linarith) (show (u + u₂) / 2 < (v₂ + v) / 2 by linarith)
    (show (v₂ + v) / 2 < v by linarith) (show (u + u₂) / 2 < u₂ by linarith) hu₂v₂
    (show v₂ < (v₂ + v) / 2 by linarith) hLive κ hγ hγ2 Y hY
  filter_upwards [hmain] with ω hω
  have hU := hω f hf hfs
  intro n
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.1 hU (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨N, fun j hj j' hj' σ hσ => ?_⟩
  have hs : q + (σ : ℝ) ∈ Icc q (T' + q) := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have key := hN j hj j' hj' _ hs
  rw [Real.dist_eq] at key
  -- identification of the integrals
  have hid : ∀ k : ℕ, IQ κ hT' u v f σ k (e, Y ω) =
      ∫ x, RegUnif.awTest (realRevMap (vrev W (T' + q)) (T' + q - (q + σ))) u v f x ∂bdryApprox
        (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y ω) (flowFam W q ![q + σ, W (q + σ)])
          (Qc (Real.sqrt κ))) k := by
    intro k
    rw [integral_bdryApprox_eq_dens]
    unfold IQ densQ
    have hτ : T' + q - (q + σ) = T' - σ := by ring
    have hσ' : T' - (σ : ℝ) ∈ Icc (0 : ℝ) T' := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    rw [hτ, hvrev]
    have hmono : StrictMonoOn (fun x => realRevMap V (T' - σ) x) (Icc u v) :=
      b7bf_strictMonoOn hVc hLiveV hσ'
    have hcont : ContinuousOn (fun x => realRevMap V (T' - σ) x) (Icc u v) :=
      b7bf_continuousOn_space hVc hT' hLiveV hσ'
    rw [awTest_eq_awProxy huv hcont hmono f]
    have hcg : awProxy (fun y => FmR hT' κ (T' - σ) y e) u v f =
        awProxy (fun x => realRevMap V (T' - σ) x) u v f := by
      refine awProxy_congr (fun x hx => ?_) huv.le f
      refine FmR_eq hT' κ hσ' e ?_ (lt_of_le_of_lt hx.2 hv0)
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith [hσ.1])) (hLiveV x hx)
    rw [hcg]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [avgReg_flow_eq_AvgQ κ hT' hq0.le he (⟨hσ.1, hσ.2⟩) (Y ω) k t]
  rw [hid j, hid j']
  exact key.le

end SWCore
end QuantumZipper
