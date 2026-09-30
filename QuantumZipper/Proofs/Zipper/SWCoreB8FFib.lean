import QuantumZipper.Proofs.Zipper.SWCoreB8FEv
import QuantumZipper.Proofs.Zipper.SWCoreB8FFixed
import QuantumZipper.Proofs.Zipper.SWCoreB7dRand

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8F (5): the fixed-path fibre of the offset event and the transfer to the Brownian path

Offset analogue of SWCoreB7dFib / SWCoreB7dRand (D70, SWC-B8 plan (b)):

* `avgReg_flow_eq_AvgQc`: the density of the dilated transported anchor field is read by `AvgQc`;
* `evQc_fibre`: for a good path, almost surely in the free field, the countable offset event
  `EvQc` holds (from `flow_fixed_conv3`, Cauchy across offsets);
* `IQc_eq`: the proxy integral is the dilated transported test integral along the driver;
* **`rand_uc_off`**: for a Brownian motion `B'` and an independent free field `Y`, a.s. (live
  window), the dilated transported test integrals along the unzipping maps
  `revMapExt (vrev W σ) σ ∘ (c ·)` with test functions `awTest (F_σ) u v f (c ·)` are Cauchy in `k`
  uniformly over rational times and **across rational offsets `c, c' ∈ [1,2]`**.

Same scheme as `evQ_fibre`, `IQ_eq`, `rand_uc`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun B2 RevMapExtension RegCont

variable (κ : ℝ) {T' : ℝ} (hT' : 0 ≤ T')

/-- **The density of the dilated transported anchor field is read by `AvgQc`.** -/
theorem avgReg_flow_eq_AvgQc {q : ℝ} (hq : 0 ≤ q) {e : C(Icc (0 : ℝ) T', ℝ)}
    (he : e ∈ MeasUnzip.PZ hT' κ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T') {c : ℝ} (hc : 0 < c)
    (y : FieldSample) (k : ℕ) (t : ℝ) :
    avgReg (coordChange (ofFun (h0rev κ) + y) (fun z => flowFam (shiftW κ q hT' e) q
        ![q + σ, shiftW κ q hT' e (q + σ)] ((c : ℂ) * z)) (Qc (Real.sqrt κ))) k (t : ℂ) =
      AvgQc κ hT' c σ k ((e, y), (t : ℂ)) := by
  rw [AvgQc_eq_avgReg κ hT' he hσ hc]
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
  have hEqc : EqOn (fun z => flowFam (shiftW κ q hT' e) q ![q + σ, shiftW κ q hT' e (q + σ)]
      ((c : ℂ) * z)) (fun z => fwdMapInv (Wof κ T' hT' e) σ ((c : ℂ) * z)) H :=
    fun w hw => hEq (mul_mem_H_of_pos hc hw)
  unfold avgReg
  congr 1
  funext n
  exact coordChange_congr_onH _ hEqc _ (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
/-- **The fixed-path fibre of the offset event.** -/
theorem evQc_fibre {q : ℝ} (hq0 : 0 < q) {e : C(Icc (0 : ℝ) T', ℝ)}
    (he : e ∈ MeasUnzip.PZ hT' κ) {u v : ℝ} (huv : u < v) (hv0 : v < 0)
    (hlive : ENNReal.ofReal T' < realHitTime (vrev (Wof κ T' hT' e) T') v)
    {u₂ v₂ : ℝ} (hu₂ : u < u₂) (hu₂v₂ : u₂ ≤ v₂) (hv₂ : v₂ < v) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc u₂ v₂) (hκ : 0 < κ) (hκ4 : κ < 4)
    (Y : Ω → FieldSample) (hY : IsFreeGFFModConstH Y P) :
    ∀ᵐ ω ∂P, EvQc κ hT' u v f (e, Y ω) := by
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
  have hmain := flow_fixed_conv3 (P := P) hWc hq0 (by linarith : q ≤ T' + q)
    (show u < (u + u₂) / 2 by linarith) (show (u + u₂) / 2 < (v₂ + v) / 2 by linarith)
    (show (v₂ + v) / 2 < v by linarith) (show (u + u₂) / 2 < u₂ by linarith) hu₂v₂
    (show v₂ < (v₂ + v) / 2 by linarith) hLive κ hγ hγ2 Y hY
  filter_upwards [hmain] with ω hω
  have hU := hω f hf hfs
  intro n
  obtain ⟨N, hN⟩ := hU (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨N, fun j hj j' hj' σ hσ c hc c' hc' => ?_⟩
  have hs : q + (σ : ℝ) ∈ Icc q (T' + q) := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have key := hN j hj j' hj' _ hs c hc c' hc'
  have hid : ∀ c : ℝ, 0 < c → ∀ k : ℕ, IQc κ hT' u v f σ c k (e, Y ω) =
      offInt κ (Real.sqrt κ) W (T' + q) q u v f (Y ω) (q + σ) c k := by
    intro c hc0 k
    unfold offInt
    rw [integral_bdryApprox_eq_dens]
    unfold IQc densQc
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
    rw [avgReg_flow_eq_AvgQc κ hT' hq0.le he (⟨hσ.1, hσ.2⟩) hc0 (Y ω) k t]
  rw [hid c (by linarith [hc.1]) j, hid c' (by linarith [hc'.1]) j']
  exact key.le

/-- **The offset proxy integral is the dilated transported test integral.** -/
theorem IQc_eq {e : C(Icc (0 : ℝ) T', ℝ)} (he : e ∈ MeasUnzip.PZ hT' κ) {u v : ℝ} (huv : u < v)
    (hv0 : v < 0) (hlive : ENNReal.ofReal T' < realHitTime (vrev (Wof κ T' hT' e) T') v)
    (f : ℝ → ℝ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T') {c : ℝ} (hc : 0 < c) (y : FieldSample)
    (k : ℕ) :
    IQc κ hT' u v f σ c k (e, y) =
      ∫ x, RegUnif.awTest (realRevMap (vrev (Wof κ T' hT' e) T') (T' - σ)) u v f (c * x)
        ∂bdryApprox (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + y)
          (fun z => revMapExt (vrev (Wof κ T' hT' e) σ) σ ((c : ℂ) * z))
          (Qc (Real.sqrt κ))) k := by
  set V := vrev (Wof κ T' hT' e) T' with hVdef
  have hW : Continuous (Wof κ T' hT' e) := continuous_Wof κ T' hT' e
  have hW0 : Wof κ T' hT' e 0 = 0 := he
  have hVc : Continuous V := continuous_vrev hW T'
  have hV0 : V 0 = 0 := vrev_zero hT'
  have hLiveV : ∀ x ∈ Icc u v, ENNReal.ofReal T' < realHitTime V x := fun x hx =>
    lt_of_lt_of_le hlive (Collision.realHitTime_anti hVc hx.2 (by rw [hV0]; exact hv0))
  have hσ' : T' - σ ∈ Icc (0 : ℝ) T' := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  rw [integral_bdryApprox_eq_dens]
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
  unfold IQc densQc
  rw [hcg]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  have hEq : EqOn (fun z => revMapExt (vrev (Wof κ T' hT' e) σ) σ ((c : ℂ) * z))
      (fun z => fwdMapInv (Wof κ T' hT' e) σ ((c : ℂ) * z)) H := by
    intro w hw
    have hcw := mul_mem_H_of_pos hc hw
    simp only
    rw [revMapExt_eq_revMap (continuous_vrev hW _) hσ.1 hcw,
      UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hW hW0 hσ.1 hcw]
    exact ReverseFlow.revMap_congr_drive _ (fun r hr => vrev_of_mem hr)
  have e2 : avgReg (coordChange (ofFun (h0rev κ) + y)
      (fun z => revMapExt (vrev (Wof κ T' hT' e) σ) σ ((c : ℂ) * z)) (Qc (Real.sqrt κ))) k =
      avgReg (coordChange (ofFun (h0rev κ) + y)
        (fun z => fwdMapInv (Wof κ T' hT' e) σ ((c : ℂ) * z)) (Qc (Real.sqrt κ))) k := by
    funext z
    unfold avgReg
    congr 1
    funext n
    exact coordChange_congr_onH _ hEq _ (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))
  rw [e2, AvgQc_eq_avgReg κ hT' he hσ hc]

set_option maxHeartbeats 1000000 in
/-- **Transfer to the independent Brownian path, offset form** (one horizon, window and test
function): Cauchy across rational offsets, uniformly over rational times. -/
theorem rand_uc_off {B' : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hB : IsBrownianReal B' P)
    (hY : IsFreeGFFModConstH Y P) (hind : IndepFun (pathOf B') Y P) (hκ : 0 < κ) (hκ4 : κ < 4)
    {T'' : ℝ} (hT'' : 0 < T'') {u v u₂ v₂ : ℝ} (huv : u < v) (hv0 : v < 0) (hu₂ : u < u₂)
    (hu₂v₂ : u₂ ≤ v₂) (hv₂ : v₂ < v) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc u₂ v₂) :
    ∀ᵐ ω ∂P, ENNReal.ofReal T'' < realHitTime (vrev (drive κ B' ω) T'') v →
      ∀ n : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ j' : ℕ, N ≤ j' → ∀ σ : ℚ,
        (σ : ℝ) ∈ Icc (0 : ℝ) T'' → ∀ c : ℚ, (c : ℝ) ∈ Icc (1 : ℝ) 2 →
        ∀ c' : ℚ, (c' : ℝ) ∈ Icc (1 : ℝ) 2 →
        |(∫ x, RegUnif.awTest (realRevMap (vrev (drive κ B' ω) T'') (T'' - σ)) u v f (c * x)
            ∂bdryApprox (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y ω)
              (fun z => revMapExt (vrev (drive κ B' ω) σ) σ (((c : ℝ) : ℂ) * z))
              (Qc (Real.sqrt κ))) j) -
          ∫ x, RegUnif.awTest (realRevMap (vrev (drive κ B' ω) T'') (T'' - σ)) u v f (c' * x)
            ∂bdryApprox (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y ω)
              (fun z => revMapExt (vrev (drive κ B' ω) σ) σ (((c' : ℝ) : ℂ) * z))
              (Qc (Real.sqrt κ))) j'| ≤
          1 / ((n : ℝ) + 1) := by
  have hT0 : (0 : ℝ) ≤ T'' := hT''.le
  set E : Set (C(Icc (0 : ℝ) T'', ℝ) × FieldSample) :=
    {p | p.1 ∉ MeasUnzip.PZ hT0 κ} ∪
      {p | ¬ ENNReal.ofReal T'' < realHitTime (vrev (Wof κ T'' hT0 p.1) T'') v} ∪
      {p | EvQc κ hT0 u v f p} with hE
  have hEm : MeasurableSet E := by
    refine (((MeasUnzip.measurableSet_PZ hT0 κ).compl.preimage measurable_fst).union ?_).union
      (measurableSet_EvQc κ hT0 u v hf.measurable)
    exact (measurableSet_lt measurable_const
      ((measurable_hitGuard hT0 κ hv0).comp measurable_fst)).compl
  have hfib : ∀ e : C(Icc (0 : ℝ) T'', ℝ), ∀ᵐ ω ∂P, (e, Y ω) ∈ E := by
    intro e
    by_cases he : e ∈ MeasUnzip.PZ hT0 κ
    · by_cases hl : ENNReal.ofReal T'' < realHitTime (vrev (Wof κ T'' hT0 e) T'') v
      · filter_upwards [evQc_fibre (P := P) κ hT0 one_pos he huv hv0 hl hu₂ hu₂v₂ hv₂ hf hfs hκ
          hκ4 Y hY] with ω hω using Or.inr hω
      · exact ae_of_all _ fun ω => Or.inl (Or.inr hl)
    · exact ae_of_all _ fun ω => Or.inl (Or.inl he)
  obtain ⟨B'', hB''m, hB''c, hB''eq⟩ := CharFun.exists_good_version hB
  have hYm : Measurable Y := measurable_pi_iff.2 hY.measurable_coord
  have hpath : pathOf B' =ᵐ[P] pathOf B'' := hB''eq.mono fun ω h => funext fun t => (h t).symm
  have hind' : IndepFun (pathC T'' B'' hB''c) Y P :=
    indepFun_pathC T'' (hind.congr hpath (ae_eq_refl _)) hB''c
  have hEae := ae_indep (measurable_pathC T'' hB''m hB''c) hYm hind' hEm hfib
  filter_upwards [hEae, RegUnif.ae_pathC_good hB hB''c hB''eq hT'', hB''eq]
    with ω hω hgood heq hlive
  set e := pathC T'' B'' hB''c ω with hedef
  have hf0 : Wof κ T'' hT0 e 0 = 0 := Wof_zero_of_GoodP hT0 κ hgood
  obtain ⟨hdc, hd0, hEq⟩ := RegUnif.drive_facts κ hB''c hT'' heq hf0
  have hWc : Continuous (Wof κ T'' hT0 e) := continuous_Wof κ T'' hT0 e
  have hvr : ∀ σ ∈ Icc (0 : ℝ) T'', EqOn (vrev (drive κ B' ω) σ) (vrev (Wof κ T'' hT0 e) σ)
      (Icc 0 σ) := by
    intro σ hσ r hr
    rw [vrev_of_mem hr, vrev_of_mem hr, hEq ⟨by linarith [hr.2], by linarith [hr.1, hσ.2]⟩,
      hEq ⟨hσ.1, hσ.2⟩]
  have hVT := hvr T'' ⟨hT0, le_rfl⟩
  have hl' : ENNReal.ofReal T'' < realHitTime (vrev (Wof κ T'' hT0 e) T'') v :=
    (isLive_congr_drive (continuous_vrev hdc _) (continuous_vrev hWc _) hT0 hVT).1 hlive
  rcases hω with (hbad | hbad) | hev
  · exact absurd hf0 hbad
  · exact absurd hl' hbad
  intro n
  obtain ⟨N, hN⟩ := hev n
  refine ⟨N, fun j hj j' hj' σ hσ c hc c' hc' => ?_⟩
  have hid : ∀ d : ℚ, (d : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ k : ℕ,
      (∫ x, RegUnif.awTest (realRevMap (vrev (drive κ B' ω) T'') (T'' - σ)) u v f (d * x)
        ∂bdryApprox (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y ω)
          (fun z => revMapExt (vrev (drive κ B' ω) σ) σ (((d : ℝ) : ℂ) * z))
          (Qc (Real.sqrt κ))) k) =
      IQc κ hT0 u v f σ d k (e, Y ω) := by
    intro d hd k
    rw [IQc_eq κ hT0 hf0 huv hv0 hl' f hσ (by linarith [hd.1]) (Y ω) k]
    have h1 : realRevMap (vrev (drive κ B' ω) T'') (T'' - σ) =
        realRevMap (vrev (Wof κ T'' hT0 e) T'') (T'' - σ) := funext fun x =>
      B5.realRevMap_congr_drive' (fun r hr => hVT ⟨hr.1, by linarith [hr.2, hσ.1]⟩) x
    have h2 : (fun z => revMapExt (vrev (drive κ B' ω) σ) σ (((d : ℝ) : ℂ) * z)) =
        fun z => revMapExt (vrev (Wof κ T'' hT0 e) σ) σ (((d : ℝ) : ℂ) * z) :=
      funext fun z => revMapExt_congr_drive (hvr σ hσ) _
    rw [h1, h2]
  rw [hid c hc j, hid c' hc' j']
  exact hN j hj j' hj' σ hσ c hc c' hc'

end SWCore
end QuantumZipper
