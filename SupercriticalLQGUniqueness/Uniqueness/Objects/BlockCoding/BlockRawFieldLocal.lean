import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockRawLocal
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockEventUM
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.LocalEvents.LocalEventToolkit




set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open LQGMetric.Blueprint
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

open LQGMetric (DistC)

 
theorem aeEventIn_blockRaw_open
    (P : Measure DistC) [IsProbabilityMeasure P]
    (h : DistC → DistC) (hh : LQGMetric.IsGFFPlusCont h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    (hBarrierD : ∀ᵐ g ∂P, BiLipschitz.Barrier.Barrier (D (h g)))
    (hBarrierE : ∀ᵐ g ∂P, BiLipschitz.Barrier.Barrier (E (h g)))
    (Cp Ci : ℝ) (hCp : 0 < Cp) (hCi : 0 < Ci)
    (hCmp : ∀ᵐ g ∂P, (∀ p : ℂ × ℂ,
      E (h g) p ≤ ENNReal.ofReal Cp * D (h g) p) ∧
      (∀ p : ℂ × ℂ, D (h g) p ≤ ENNReal.ofReal Ci * E (h g) p))
    (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (hR : 0 < T.rho * T.r) (hn : ‖T.orientation‖ = 1)
    (hRad : 0 ≤ T.blockRadius)
    (hLam : C.lamConst < 1)
    (hRatio : ENNReal.ofReal Cp * ENNReal.ofReal C.lamConst *
      ENNReal.ofReal Ci < 1)
    (U : TopologicalSpace.Opens ℂ)
    (hW : ∀ k ∈ Finset.Icc 1 Ksh,
      ball (0 : ℂ) (3 * (3 * 8 ^ (Ksh - k) * (T.rho * T.r))) ⊆ U)
    (hWin : ∀ k ∈ Finset.Icc 1 Ksh,
      (Objects.ShieldLocality.shieldWindow (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) : Set ℂ) ⊆ U)
    (hKW : closure (Objects.Excursions.blockShape T) ⊆ U)
    (hCU : closedBall (Objects.Excursions.cU T) T.blockRadius ⊆ U)
    (hCV : closedBall (Objects.Excursions.cV T) T.blockRadius ⊆ U) :
    AEEventIn P (fieldSigma h U)
      {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D E (h g)} := by
  let B : Set DistC := {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D E (h g)}
  obtain ⟨FD, -, hLocD⟩ := hD.locality P h hh U
  obtain ⟨FE, -, hLocE⟩ := hE.locality P h hh U
  have hLenD := hD.length P h hh
  have hLenE := hE.length P h hh
  let Wraw : Set DistC := {g |
    BiLipschitz.Barrier.Barrier (D (h g)) ∧ BiLipschitz.Barrier.Barrier (E (h g)) ∧
    (D (h g)).IsLengthSpace ∧ (E (h g)).IsLengthSpace ∧
    (D (h g)).internal U = FD (LQGMetric.restrictTo U (h g)) ∧
    (E (h g)).internal U = FE (LQGMetric.restrictTo U (h g)) ∧
    (∀ p : ℂ × ℂ, E (h g) p ≤ ENNReal.ofReal Cp * D (h g) p) ∧
    (∀ p : ℂ × ℂ, D (h g) p ≤ ENNReal.ofReal Ci * E (h g) p)}
  have hWraw : ∀ᵐ g ∂P, g ∈ Wraw := by
    filter_upwards [hBarrierD,hBarrierE,hLenD,hLenE,hLocD,hLocE,hCmp]
      with g hbD hbE hlD hlE hfD hfE hc
    exact ⟨hbD,hbE,hlD,hlE,hfD,hfE,hc.1,hc.2⟩
  obtain ⟨W,hWae,hWm,hWsub⟩ := hWraw.exists_measurable_mem
  let R : DistC → (LQGMetric.CoordJ → ℝ) :=
    fun g => LQGMetric.pairJ U (LQGMetric.restrictTo U (h g))
  have hRm : Measurable R :=
    (LQGMetric.measurable_pairJ U).comp
      ((LQGMetric.measurable_restrictTo U).comp hh.1)
  have hRfield : Measurable[fieldSigma h U] R :=
    (LQGMetric.measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hSat : ∀ g₁ ∈ W, ∀ g₂ ∈ W,
      R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B := by
    intro g₁ hg₁ g₂ hg₂ hcode hgood
    have hr : LQGMetric.restrictTo U (h g₁) =
        LQGMetric.restrictTo U (h g₂) := LQGMetric.injective_pairJ U hcode
    have hwd₁ := hWsub g₁ hg₁
    have hwd₂ := hWsub g₂ hg₂
    have hintD : (D (h g₁)).internal U = (D (h g₂)).internal U := by
      calc
        _ = FD (LQGMetric.restrictTo U (h g₁)) := hwd₁.2.2.2.2.1
        _ = FD (LQGMetric.restrictTo U (h g₂)) := by rw [hr]
        _ = _ := hwd₂.2.2.2.2.1.symm
    have hintE : (E (h g₁)).internal U = (E (h g₂)).internal U := by
      calc
        _ = FE (LQGMetric.restrictTo U (h g₁)) := hwd₁.2.2.2.2.2.1
        _ = FE (LQGMetric.restrictTo U (h g₂)) := by rw [hr]
        _ = _ := hwd₂.2.2.2.2.2.1.symm
    have hraw := blockRaw_iff_of_internal_eq C T Ksh Cmid0
      (D (h g₁)) (E (h g₁)) (D (h g₂)) (E (h g₂))
      hR hn U hW hWin hKW hCU hCV
      ⟨hwd₁.1,hwd₁.2.1⟩ ⟨hwd₂.1,hwd₂.2.1⟩
      ⟨hwd₁.2.2.1,hwd₁.2.2.2.1⟩
      ⟨hwd₂.2.2.1,hwd₂.2.2.2.1⟩
      Cp Ci hCp hCi
      hwd₁.2.2.2.2.2.2.1 hwd₁.2.2.2.2.2.2.2
      hwd₂.2.2.2.2.2.2.1 hwd₂.2.2.2.2.2.2.2
      hLam hRatio hintD hintE
    exact hraw.mp hgood
  have hBm : NullMeasurableSet B P :=
    (blockRaw_um C T Ksh Cmid0 D E hD.measurable hE.measurable hRad hR hn).nullMeasurableSet_preimage
      hh.1.aemeasurable
  exact LQGMetric.LocalEvent.aeEventIn_of_saturated
    (Y := id) (R := R) (V := R) (B := B) (W := W)
    measurable_id hRm hRfield (Filter.Eventually.of_forall fun _ => rfl)
    hWm (by simpa only [Measure.map_id] using hBm) hWae hSat

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
