/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefChartWord

/-!
# The determination input does not depend on the branch or the frame constant

Packet PROVE-LEMMA725REF4, item 3. Specification §7.4, Aux. lemma 125 (`source/spec/p385-432.md` L197–L250,
p. 395: "An invertible deterministic sign or constant recoding of the known field preserves that measurability").

`Lemma725RefChart.PocketHistDet` (the determination companion of `PocketStopWallsInput`) asks, for every
walls-measurable branch integer `n` and every constant `a`, that the killed relative history be a Borel function of a
walls' record and the pocket field `chartTransport (shiftChart c₀ n) 1 a χ(κ) h` (`c₀ = pChart A C ψ`). Shifting the
lift by `−2πn` and adding `a` changes the transported field by the walls-measurable constant `a − 2πχ(κ) n` times the
distribution `1`, which the record can undo. So the input reduces to its canonical form `PocketHistDet0`: the branch
`n = 0` and the constant `a = 0`.

## Main results

* `continuousOn_lift_inv_pChart`: `lift ∘ inv` of the canonical pocket chart is continuous on `ℍ` at every sample;
* **`chartTransport_shiftChart`**: `chartTransport (shiftChart c m) 1 a k X =
  chartTransport c 1 0 k X + (a − 2πkm) • 1`;
* `PocketHistDet0` (the canonical form), **`pocketHistDet_of_zero`**: `PocketHistDet0 → PocketHistDet`.

Ruling R48: nothing here uses Theorem 1.2/1.3 or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma725RefChart

open PocketTraversal Lemma71C LawUnique PocketStopField

universe u

/-! ### Shifting the branch of a chart -/

section Shift

/-- **The transport in a shifted chart** (deterministic): shifting the lift by `−2πm` and adding the frame constant `a`
adds `(a − 2πkm) • 1` to the transported field, when `lift ∘ inv` is continuous on `ℍ`. -/
theorem chartTransport_shiftChart {c : Chart} {m : ℤ} (hc : c.IsConformal) (hc' : (shiftChart c m).IsConformal)
    (hℓ : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H) (a k : ℝ) (X : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport hc' 1 a k X =
      Chart.chartTransport hc 1 0 k X + (a - k * (2 * π * (m : ℝ))) • Chart.oneDist := by
  have hℓ' : ContinuousOn (fun w => (shiftChart c m).2.2 ((shiftChart c m).2.1 w)) H :=
    hℓ.sub continuousOn_const
  have hloc : ∀ {f : ℂ → ℝ}, ContinuousOn f H → LocallyIntegrableOn f H := fun hf =>
    hf.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet
  ext φ
  have hi1 : Integrable fun w => c.2.2 (c.2.1 w) * φ w := by
    have := SupercriticalConformalCovariance.GM24.integrable_test_mul hℓ φ
    simpa only [mul_comm] using this
  have hi2 : Integrable fun w => φ w := by
    have := SupercriticalConformalCovariance.GM24.integrable_test_mul (Y := fun _ => (1 : ℝ))
      continuousOn_const φ
    simpa only [mul_one] using this
  have hlift : Chart.liftDist (shiftChart c m) φ = Chart.liftDist c φ - 2 * π * (m : ℝ) * Chart.oneDist φ := by
    rw [Chart.liftDist_apply (hloc hℓ'), Chart.liftDist_apply (hloc hℓ), Chart.oneDist_apply]
    change ∫ w, (c.2.2 (c.2.1 w) - 2 * π * (m : ℝ)) * φ w = _
    have e : (fun w => (c.2.2 (c.2.1 w) - 2 * π * (m : ℝ)) * φ w) =
        fun w => c.2.2 (c.2.1 w) * φ w - 2 * π * (m : ℝ) * φ w := by
      funext w; ring
    rw [e, integral_sub hi1 (hi2.const_mul _), integral_const_mul]
  have hpush : Chart.pullField hc' X φ = Chart.pullField hc X φ := rfl
  rw [Chart.chartTransport_apply', IsAddApply.add_apply, Chart.chartTransport_apply',
    smul_apply, smul_eq_mul, hlift]
  change 1 * Chart.pullField hc' X φ + a * Chart.oneDist φ + k * _ = _
  rw [hpush, Chart.pullField_apply]
  ring

end Shift

/-! ### The lift of the canonical pocket chart in the coordinate of `ℍ` -/

section Canon

variable {Ω : Type*} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}

/-- `lift ∘ inv` of the canonical pocket chart is `−Im canonLogH (inv)` on `ℍ`, hence continuous there. -/
theorem continuousOn_lift_inv_pChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (ω : Ω) :
    ContinuousOn (fun w => (pChart A C ψ ω).2.2 ((pChart A C ψ ω).2.1 w)) H := by
  obtain ⟨hd, hne, hconf, -⟩ := pChart_props hCo hCH hψ ω
  have hM := (isDerivLog_canonLogH hd hne).1.1
  refine ((Complex.continuous_im.comp_continuousOn hM.continuousOn).neg).congr fun w hw => ?_
  change (pLog A C ψ ω (pInv A C ψ ω w)).im = -(canonLogH (pInv A C ψ ω) w).im
  have hfw : pFwd A ψ ω (pInv A C ψ ω w) = w := hconf.2.2 w hw
  simp only [pLog, hfw, neg_im]

end Canon

/-! ### The canonical determination input -/

section Det

variable {Ω : Type u}

/-- **The determination input in canonical form** (branch `n = 0`, constant `a = 0`): almost surely on `A`, the killed
relative history of `γ` with marks `xL`, `xR` is a Borel function of a walls' record and the pocket field
`chartTransport (pChart A C ψ) 1 0 χ(κ) h`. -/
def PocketHistDet0 (κ : ℝ) {nL nR : ℕ} (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (C : Ω → Set ℂ)
    (ψ : Ω → ℂ → ℂ) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (ε : Type u) (_ : MeasurableSpace ε) (_ : StandardBorelSpace ε) (E : Ω → ε)
    (g : ε × DistOn upperHalfPlaneOpens → HistorySpace (nL + 1) (nR + 1)),
    Measurable[𝓦] E ∧ Measurable g ∧
      ∀ᵐ ω ∂P, ω ∈ A → ∀ hc : (pChart A C ψ ω).IsConformal,
        killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
          (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) ω =
            g (E ω, Chart.chartTransport hc 1 0 (chiC κ) (h ω))

/-- **The determination input from its canonical form**: the record `(E, n)` and the Borel map
`((e, m), X) ↦ g (e, X − (a − 2πχ(κ) m) • 1)`. -/
theorem pocketHistDet_of_zero {κ : ℝ} {nL nR : ℕ} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {C : Ω → Set ℂ}
    {ψ : Ω → ℂ → ℂ} {h : Ω → DistOn upperHalfPlaneOpens} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (h0 : PocketHistDet0 κ 𝓦 P A γ xL xR C ψ h) :
    PocketHistDet κ 𝓦 P A γ xL xR C ψ h := by
  intro n hn a
  obtain ⟨ε, mε, hSB, E, g, hEm, hg, hdet⟩ := h0
  set s : ℤ → ℝ := fun m => a - chiC κ * (2 * π * (m : ℝ)) with hs
  have hsm : Measurable s := measurable_from_top
  have hF : Measurable fun p : (ε × ℤ) × DistOn upperHalfPlaneOpens =>
      (p.1.1, p.2 - s p.1.2 • Chart.oneDist) := by
    refine measurable_fst.fst.prodMk (LQGMetric.measurable_distOn_iff.2 fun φ => ?_)
    have e : (fun p : (ε × ℤ) × DistOn upperHalfPlaneOpens => (p.2 - s p.1.2 • Chart.oneDist) φ) =
        fun p => p.2 φ - s p.1.2 * Chart.oneDist φ := by
      funext p
      rw [sub_apply, smul_apply, smul_eq_mul]
    rw [e]
    exact ((LQGMetric.measurable_distOn_apply φ).comp measurable_snd).sub
      ((hsm.comp measurable_fst.snd).mul_const _)
  refine ⟨ε × ℤ, inferInstance, inferInstance, fun ω => (E ω, n ω),
    fun p => g (p.1.1, p.2 - s p.1.2 • Chart.oneDist), hEm.prodMk hn, hg.comp hF, ?_⟩
  filter_upwards [hdet] with ω hω hωA hc'
  have hc : (pChart A C ψ ω).IsConformal := hc'
  rw [hω hωA hc]
  congr 2
  rw [chartTransport_shiftChart hc hc' (continuousOn_lift_inv_pChart hCo hCH hψ ω), add_sub_cancel_right]

end Det

end InteractingSLE.Sec7.Lemma725RefChart
