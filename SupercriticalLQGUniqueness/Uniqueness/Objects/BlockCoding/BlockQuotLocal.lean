import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockRawFieldLocal
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockScaleAE
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.BarrierScale
import LQGMetric.Field.GermSplitA




set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open LQGMetric.Blueprint
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

open LQGMetric (DistC addConst)

 


theorem aeEventIn_blockRaw_modConst
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (Cp Ci : ℝ) (hCp : 0 < Cp) (hCi : 0 < Ci)
    (hCmp : ∀ᵐ g ∂μ, (∀ p : ℂ × ℂ,
      E g p ≤ ENNReal.ofReal Cp * D g p) ∧
      (∀ p : ℂ × ℂ, D g p ≤ ENNReal.ofReal Ci * E g p))
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (hR : 0 < T.rho * T.r) (hn : ‖T.orientation‖ = 1)
    (hRad : 0 ≤ T.blockRadius)
    (hLam : C.lamConst < 1)
    (hRatio : ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst *
      ENNReal.ofReal Ci < 1)
    (U : TopologicalSpace.Opens ℂ) (hUne : (U : Set ℂ).Nonempty)
    (hW : ∀ k ∈ Finset.Icc 1 Ksh,
      ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ U)
    (hWin : ∀ k ∈ Finset.Icc 1 Ksh,
      (Objects.ShieldLocality.shieldWindow (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) : Set ℂ) ⊆ U)
    (hKW : closure (Objects.Excursions.blockShape T) ⊆ U)
    (hCU : closedBall (Objects.Excursions.cU T) T.blockRadius ⊆ U)
    (hCV : closedBall (Objects.Excursions.cV T) T.blockRadius ⊆ U) :
    AEEventIn μ (fieldSigma0On id U)
      {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D E g} := by
  obtain ⟨ψ,hψU,hψ1⟩ := LQGMetric.GermSplit.exists_test_unit hUne
  have hwhole : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  let G := LQGMetric.CONF.normIn (id : DistC → DistC) ψ
  have hG : LQGMetric.IsGFFPlusCont G μ :=
    Toolkit.LocalEvents.isGFFPlusCont_normIn hwhole ψ
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hBD := BiLipschitz.Barrier.ae_barrier hD hQ μ id hμ
  have hBE := BiLipschitz.Barrier.ae_barrier hE hQ μ id hμ
  have hScaleD := Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD
    (fun g => -(g ψ))
  have hScaleE := Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q E hE
    (fun g => -(g ψ))
  have hBGD : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (D (G g)) := by
    filter_upwards [hBD,hScaleD] with g hb hs
    let c : ENNReal := ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ)))
    exact Objects.ProbabilityS3.barrier_of_dist_scale (D g) (D (G g)) c
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top (fun x y => hs (x,y)) hb
  have hBGE : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (E (G g)) := by
    filter_upwards [hBE,hScaleE] with g hb hs
    let c : ENNReal := ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ)))
    exact Objects.ProbabilityS3.barrier_of_dist_scale (E g) (E (G g)) c
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top (fun x y => hs (x,y)) hb
  have hCmpG : ∀ᵐ g ∂μ, (∀ p : ℂ × ℂ,
      E (G g) p ≤ ENNReal.ofReal Cp * D (G g) p) ∧
      (∀ p : ℂ × ℂ, D (G g) p ≤ ENNReal.ofReal Ci * E (G g) p) := by
    filter_upwards [hCmp,hScaleD,hScaleE] with g hc hsD hsE
    constructor
    · intro p
      have he : E (G g) p =
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) * E g p := by
        change E (addConst g (-(g ψ))) p = _
        simpa only [id_eq] using hsE p
      have hd : D (G g) p =
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) * D g p := by
        change D (addConst g (-(g ψ))) p = _
        simpa only [id_eq] using hsD p
      rw [he, hd]
      calc
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) * E g p ≤
            ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) *
              (ENNReal.ofReal Cp * D g p) := by gcongr; exact hc.1 p
        _ = _ := by ring
    · intro p
      have hd : D (G g) p =
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) * D g p := by
        change D (addConst g (-(g ψ))) p = _
        simpa only [id_eq] using hsD p
      have he : E (G g) p =
          ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) * E g p := by
        change E (addConst g (-(g ψ))) p = _
        simpa only [id_eq] using hsE p
      rw [hd, he]
      calc
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) * D g p ≤
            ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ))) *
              (ENNReal.ofReal Ci * E g p) := by gcongr; exact hc.2 p
        _ = _ := by ring
  have hLocal := aeEventIn_blockRaw_open μ G hG ξ Q D E hD hE
    hBGD hBGE Cp Ci hCp hCi hCmpG C T Ksh Cmid0 hR hn hRad
    hLam hRatio U hW hWin hKW hCU hCV
  have hLocal0 := Toolkit.LocalEvents.aeEventIn_fieldSigma0On_of_normIn
    (id : DistC → DistC) ψ hψ1 U hψU hLocal
  have hEq := ae_blockRaw_addConst_iff μ hμ ξ Q D E hD hE C T Ksh Cmid0
    (fun g => -(g ψ))
  obtain ⟨R,hRm,hGR⟩ := hLocal0
  refine ⟨R,hRm,?_⟩
  filter_upwards [hEq,hGR] with g he hR
  exact propext (he.symm.trans (Iff.of_eq hR))

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
