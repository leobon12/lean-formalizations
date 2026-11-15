/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinGap
import InteractingSLE.Spec.Sec7.R7GapEqFinClock
import InteractingSLE.Spec.Sec7.R7GapEqGeoCorner
import InteractingSLE.Spec.Sec7.R7StopInWire

/-! # R.7: finite mixed-pocket gaps, attachment and relative traversal

These adapters expose the exact geometry still needed by the outer stopped-reference producer.
They supply geometry only; stopped kernels, side laws and source initialization remain separate.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal
namespace InteractingSLE.Wire
open Sec7 Sec6 Sec7.R7GapEq Sec7.R7GapEqFin Sec7.R7StopIn Sec7.PocketJordan
  Sec7.Aux37Attach Sec7.PocketTraversal Sec7.Lemma71C Sec7.PocketWordAssembly Sec7.PocketCoord Sec7.R7Aux131

/-- The latest finite-gap reduction also provides the attachment law it proves internally. -/
theorem late_finiteGap_and_attachment
    {W : ℝ → ℝ} {η B A α : ℝ → ℂ} {C F K V D : Set ℂ} {τ σ a b : ℝ}
    (hC : IsCfPocket C B A) (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (h42 : ∀ r s : ℝ, 0 ≤ r → r < s → ¬ η '' Icc r s ⊆ K) (hfrK : frontier C ⊆ K)
    (hFo : IsOpen F) (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hinc : ∀ p ∈ A '' Icc 0 1, p ∉ B '' Icc 0 1 → p ∈ closure (F \ closure C))
    (hfr : ∀ p ∈ A '' Icc 0 1, p ∉ B '' Icc 0 1 →
      ∃ ε > 0, frontier F ∩ ball p ε ⊆ closure C)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (hτf : η τ ∉ η '' Ico 0 τ)
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hαrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t)
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hB : ∀ v ∈ Icc (0 : ℝ) 1, B v = α (a + v * (b - a)))
    (hVo : IsOpen V) (hCV : C ⊆ V) (hV : V ⊆ C ∪ F ∪ K)
    (hVK : frontier V ⊆ K) (hD : IsClosed D)
    (hfrV : frontier V ⊆ α '' Icc 0 1 ∪ D) (hpD : α b ∉ D)
    (marks : Finset ℝ) {χ lam lam' ε θ : ℝ}
    (hχ : 0 < χ) (hlam : lam - lam' = Real.pi * χ / 2)
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) ∨
      (ε = -1 ∧ θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)))
    (hcompare : ∀ r s v v₁ v₂ : ℚ, IsAttachWitness η C B τ σ r s v v₁ v₂ →
      (∀ x ∈ marks, x ∉ Icc (v : ℝ) v₂) →
      ∃ (G : Filter ℂ) (M Lf Lc : ℂ → ℝ) (k : ℤ), G.NeBot ∧
        Tendsto (fun z => M z + χ * Lf z) G (𝓝 (ε * lam - θ * χ)) ∧
        Tendsto (fun z => M z + χ * Lc z) G (𝓝 (ε * lam' - Real.pi * χ)) ∧
        Tendsto (fun z => Lf z - Lc z) G (𝓝 (2 * Real.pi * k))) :
    PocketGapEq η C τ σ ∧ BarrierAttachConst η C B τ σ := by
  refine ⟨pocketGapEq_of_extension_and_germs hC hη hW hW0 h42 hfrK hFo havoid
    hinc hfr hτ0 hτ hτf hαc hαi hαrev ha hab hb hB hVo hCV hV hVK hD hfrV hpD
    marks hχ hlam hside hcompare, ?_⟩
  exact barrierAttachConst_of_germs hη.2.1 hC.cont₁ hC.inj₁
    (reverseVisitOrder_affine_subarc hαrev ha hab hb.le hB) hτ0 hτ marks hχ hlam hside hcompare

variable {W : ℝ → ℝ} {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {η : ℝ → ℂ} {ψ : ℂ → ℂ}

/-- The new Jordan-face reduction supplies the relative driver in the STOPIN traversal theorem. -/
theorem late_finiteTraversal_props
    (hP : IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)))
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hψ : IsCfJordan R L r ψ)
    (hmapped : ∀ s ∈ Ico (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)), ∀ a b : ℝ, s < a → a < b → b < (firstHit η (cfArcR R L r 0)) →
      (∀ t ∈ Icc a b, η t ∉ (cfPocket R L r)) →
      a ∈ closure {t | s < t ∧ η t ∈ (cfPocket R L r)} → b ∈ closure {t | a < t ∧ η t ∈ (cfPocket R L r)} →
      trMap W s a 0 = trMap W s b 0)
    (hface : ∀ S ∈ Ioo (0 : ℝ) (pocketClock η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) (firstHit η (cfArcR R L r 0))), ∀ u ∈ Ico (0 : ℝ) S,
      ∃ (Γ : Set ℂ) (q : ℂ), LQGMetric.JordanMap.IsJordanCurve Γ ∧ q ∈ Γᶜ ∧
        IsBounded (connectedComponentIn Γᶜ q) ∧ connectedComponentIn Γᶜ q ⊆ H ∧
        MapsTo (trMap W 0 (pocketFibre η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) u)) (connectedComponentIn Γᶜ q) (cfPocket R L r) ∧
        IsConformalBijection (ψ ∘ trMap W 0 (pocketFibre η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) u))
          (connectedComponentIn Γᶜ q)
          (H \ fillH ((fun v => ψ (erasedPath η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v)) '' Icc 0 u)) ∧
        ∀ v ∈ Icc u S,
          trMap W (pocketFibre η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) u) (pocketFibre η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v) 0 ∈
            closure (connectedComponentIn Γᶜ q))
 :
    IsDrivenCurve (cfTraversal R L r η ψ) ∧
      (∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversal R L r η ψ u ∈ H ∧ M < ‖cfTraversal R L r η ψ u‖) ∧
      Tendsto (fun u => ‖cfTraversal R L r η ψ u‖) atTop atTop ∧
      (capLife (cfTraversal R L r η ψ) = ⊤ → GoodR7 (fun t => segDriver (cfTraversal R L r η ψ) t) ⊤) := by
  have hψ' : IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]
    exact hψ
  exact cfTraversal_props_of_erasure hP hψ
    (relLoewner_of_mapped_faces hP hη hW hW0 hψ' hmapped hface)

end InteractingSLE.Wire
