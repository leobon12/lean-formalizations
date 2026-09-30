import QuantumZipper.Proofs.Zipper.SWCoreB7dFib
import QuantumZipper.Proofs.Zipper.JointModRandom
import QuantumZipper.Proofs.Zipper.RegContRandom
import QuantumZipper.Proofs.Zipper.E1TransferMeas
import QuantumZipper.Proofs.Zipper.SWCoreB7dShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7d (6): the transfer to the independent Brownian path

For a Brownian motion `B'` and a free field `Y'` independent of its path, almost surely, for every
horizon `T' > 0` (rational data), every live negative window and every test function of the
countable family, the transported test integrals of the field `𝔥₀ + Y'` along the unzipping maps
`revMapExt (vrev W σ) σ` (`W = drive κ B' ω`) are uniformly Cauchy over the rational times
(`rand_uc`). Proof: the countable event `EvQ` (`measurableSet_EvQ`), its fixed-path fibre
(`evQ_fibre`), conditioning on the good continuous version of the path (`CharFun.ae_indep`,
`exists_good_version`, `pathC`), and the identification of the proxies (`IQ_eq`).
Same scheme as `SWCore.a8_rand_one` (SWCoreA8Rand.lean). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun B2 RevMapExtension RegCont

theorem isLive_congr_drive {V V' : ℝ → ℝ} (hV : Continuous V) (hV' : Continuous V') {t x : ℝ}
    (ht : 0 ≤ t) (h : EqOn V V' (Icc 0 t)) : E1.IsLive V t x ↔ E1.IsLive V' t x := by
  rw [E1.isLive_iff_exists hV ht, E1.isLive_iff_exists hV' ht]
  exact exists_congr fun u => E1.isRealRevSol_congr_drive h

variable (κ : ℝ) {T' : ℝ} (hT' : 0 ≤ T')

/-- **The proxy integral is the transported test integral.** -/
theorem IQ_eq {e : C(Icc (0 : ℝ) T', ℝ)} (he : e ∈ MeasUnzip.PZ hT' κ) {u v : ℝ} (huv : u < v)
    (hv0 : v < 0) (hlive : ENNReal.ofReal T' < realHitTime (vrev (Wof κ T' hT' e) T') v)
    (f : ℝ → ℝ) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T') (y : FieldSample) (k : ℕ) :
    IQ κ hT' u v f σ k (e, y) =
      ∫ x, RegUnif.awTest (realRevMap (vrev (Wof κ T' hT' e) T') (T' - σ)) u v f x ∂bdryApprox
        (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + y) (revMapExt (vrev (Wof κ T' hT' e) σ) σ)
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
  unfold IQ densQ
  rw [hcg]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  have hEq : EqOn (revMapExt (vrev (Wof κ T' hT' e) σ) σ) (fwdMapInv (Wof κ T' hT' e) σ) H := by
    intro w hw
    rw [revMapExt_eq_revMap (continuous_vrev hW _) hσ.1 hw,
      UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hW hW0 hσ.1 hw]
    exact ReverseFlow.revMap_congr_drive w (fun r hr => vrev_of_mem hr)
  have e2 : avgReg (coordChange (ofFun (h0rev κ) + y) (revMapExt (vrev (Wof κ T' hT' e) σ) σ)
      (Qc (Real.sqrt κ))) k = avgReg (coordChange (ofFun (h0rev κ) + y)
        (fwdMapInv (Wof κ T' hT' e) σ) (Qc (Real.sqrt κ))) k := by
    funext z
    unfold avgReg
    congr 1
    funext n
    exact coordChange_congr_onH _ hEq _ (TwoPoint.foldedCircle_ae_mem_H _ (radius_pos k))
  rw [e2, RegUnif.AvgQ_eq_avgReg hT' he hσ]
  rfl

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
/-- **Transfer to the independent Brownian path** (one horizon, window and test function). -/
theorem rand_uc {B' : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hB : IsBrownianReal B' P)
    (hY : IsFreeGFFModConstH Y P) (hind : IndepFun (pathOf B') Y P) (hκ : 0 < κ) (hκ4 : κ < 4)
    {T'' : ℝ} (hT'' : 0 < T'') {u v u₂ v₂ : ℝ} (huv : u < v) (hv0 : v < 0) (hu₂ : u < u₂)
    (hu₂v₂ : u₂ ≤ v₂) (hv₂ : v₂ < v) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc u₂ v₂) :
    ∀ᵐ ω ∂P, ENNReal.ofReal T'' < realHitTime (vrev (drive κ B' ω) T'') v →
      ∀ n : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ j' : ℕ, N ≤ j' → ∀ σ : ℚ,
        (σ : ℝ) ∈ Icc (0 : ℝ) T'' →
        |(∫ x, RegUnif.awTest (realRevMap (vrev (drive κ B' ω) T'') (T'' - σ)) u v f x
            ∂bdryApprox (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y ω)
              (revMapExt (vrev (drive κ B' ω) σ) σ) (Qc (Real.sqrt κ))) j) -
          ∫ x, RegUnif.awTest (realRevMap (vrev (drive κ B' ω) T'') (T'' - σ)) u v f x
            ∂bdryApprox (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y ω)
              (revMapExt (vrev (drive κ B' ω) σ) σ) (Qc (Real.sqrt κ))) j'| ≤
          1 / ((n : ℝ) + 1) := by
  have hT0 : (0 : ℝ) ≤ T'' := hT''.le
  set E : Set (C(Icc (0 : ℝ) T'', ℝ) × FieldSample) :=
    {p | p.1 ∉ MeasUnzip.PZ hT0 κ} ∪
      {p | ¬ ENNReal.ofReal T'' < realHitTime (vrev (Wof κ T'' hT0 p.1) T'') v} ∪
      {p | EvQ κ hT0 u v f p} with hE
  have hEm : MeasurableSet E := by
    refine (((MeasUnzip.measurableSet_PZ hT0 κ).compl.preimage measurable_fst).union ?_).union
      (measurableSet_EvQ κ hT0 u v hf.measurable)
    exact (measurableSet_lt measurable_const
      ((measurable_hitGuard hT0 κ hv0).comp measurable_fst)).compl
  have hfib : ∀ e : C(Icc (0 : ℝ) T'', ℝ), ∀ᵐ ω ∂P, (e, Y ω) ∈ E := by
    intro e
    by_cases he : e ∈ MeasUnzip.PZ hT0 κ
    · by_cases hl : ENNReal.ofReal T'' < realHitTime (vrev (Wof κ T'' hT0 e) T'') v
      · filter_upwards [evQ_fibre (P := P) κ hT0 one_pos he huv hv0 hl hu₂ hu₂v₂ hv₂ hf hfs hκ hκ4
          Y hY] with ω hω using Or.inr hω
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
  -- the reversed drivers agree on `[0, σ]`
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
  refine ⟨N, fun j hj j' hj' σ hσ => ?_⟩
  have hid : ∀ k : ℕ, (∫ x, RegUnif.awTest (realRevMap (vrev (drive κ B' ω) T'') (T'' - σ)) u v f x
      ∂bdryApprox (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y ω)
        (revMapExt (vrev (drive κ B' ω) σ) σ) (Qc (Real.sqrt κ))) k) =
      IQ κ hT0 u v f σ k (e, Y ω) := by
    intro k
    rw [IQ_eq κ hT0 hf0 huv hv0 hl' f hσ (Y ω) k]
    have h1 : realRevMap (vrev (drive κ B' ω) T'') (T'' - σ) =
        realRevMap (vrev (Wof κ T'' hT0 e) T'') (T'' - σ) := funext fun x =>
      B5.realRevMap_congr_drive' (fun r hr => hVT ⟨hr.1, by linarith [hr.2, hσ.1]⟩) x
    have h2 : revMapExt (vrev (drive κ B' ω) σ) σ = revMapExt (vrev (Wof κ T'' hT0 e) σ) σ :=
      funext fun z => revMapExt_congr_drive (hvr σ hσ) z
    rw [h1, h2]
  rw [hid j, hid j']
  exact hN j hj j' hj' σ hσ

end SWCore
end QuantumZipper
