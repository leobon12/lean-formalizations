/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxCanon

/-!
# Record matching for the canonical driver on an event determined by the runs

Packet PROVE-GW2-GEOM2, round 16 (decision D70: `Mz.CanonIdentOn` at `relOff`). `Qx.exists_canonRec` gives the record
clause of `Mz.CanonIdentOn` on an event `G` of `Ms.stageMarks (ℓ + 1)`. At the relative root the natural event is the
root event, which involves `R = max (A ∩ ℝ)` (a function of the upper run) and B's runs through `ℓ + 1`, and whose
measurability is not available. Its measurability is used only to keep it under the regular conditional laws; an
event that is a function of B's runs through `ℓ + 1` and the upper run through `k` is kept there as well, because these
runs are frozen under the kernels.

* **`exists_canonRec_det`**: `Qx.exists_canonRec` on `G₁ ∩ G₂`, with `G₁` an event of `Ms.stageMarks (ℓ + 1)` and `G₂`
  determined by B's runs through `ℓ + 1` and the upper run through `k`.

R48: Theorem 1.2 enters only through `Theorem12ParamStatement` (the canonical driver code).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Gi

open Restart Exist Exist.Staged Exist.StagedLaw Lu Mx Mz Qx

/-- `Qx.ae_kernel_const_of_determined` on `G₁ ∩ G₂`, with `G₁` measurable for the marks and `G₂` kept under the
kernels. -/
theorem ae_kernel_const_of_determined_inter {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ) {α X : Type*} {D : Ω → α}
    {f : Ω → X} {G₁ G₂ G₃ : Set Ω} (hG₁ : MeasurableSet[𝓜] G₁)
    (hG₂ : ∀ᵐ ω₀ ∂P, ω₀ ∈ G₂ → ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), ω ∈ G₂) (hG₃ : ∀ᵐ ω ∂P, ω ∈ G₃)
    (hD : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), D ω = D ω₀)
    (hdet : ∀ ω ω', ω ∈ G₁ ∩ G₂ → ω ∈ G₃ → ω' ∈ G₁ ∩ G₂ → ω' ∈ G₃ → D ω = D ω' → f ω = f ω') :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G₁ ∩ G₂ → ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), f ω = f ω₀ := by
  have hκG : ∀ᵐ ω₀ ∂P, ω₀ ∈ G₁ → ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), ω ∈ G₁ := by
    filter_upwards [Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator (P := P) h𝓜 hG₁] with ω₀ h hω₀
    rw [indicator_of_mem hω₀, Pi.one_apply] at h
    exact (prob_compl_eq_zero_iff (h𝓜 _ hG₁)).2 h
  filter_upwards [hD, hκG, hG₂, KernelTower.ae_ae_condExpKernel_of_ae h𝓜 hG₃, hG₃] with ω₀ hD₀ hκ₀ hκ₂ hG₃κ hG₃₀
    hω₀
  filter_upwards [hD₀, hκ₀ hω₀.1, hκ₂ hω₀.2, hG₃κ] with ω hDω hωG₁ hωG₂ hωG₃
  exact hdet ω ω₀ ⟨hωG₁, hωG₂⟩ hωG₃ hω₀ hG₃₀ hDω

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
  {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)

/-- **Record matching for the canonical driver on `G₁ ∩ G₂`** (`Qx.exists_canonRec` with the event split into a part
`G₁` of `Ms.stageMarks (ℓ + 1)` and a part `G₂` determined by B's runs through `ℓ + 1` and the upper run through
`k`). -/
theorem exists_canonRec_det [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hRw : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRu : StagedPiecesRegular κ b jumps P (upperSpec u l) (E (upperSpec u l)))
    (h𝓜 : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {c : Ω → BoundaryWord} (hc : Measurable c) {K : Ω → Set ℂ} {x₀ : Ω → ℝ} (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hK : @IsDyadicHitMeasurable Ω (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) K)
    (hx₀ : Measurable[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] x₀) {G₁ G₂ : Set Ω}
    (hG₁ : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] G₁)
    (hG₂ : ∀ ω ω', (∀ n, n ≤ ℓ + 1 →
        ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) n =
          ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω') n) →
      ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k =
        ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω') k →
      ω ∈ G₂ → ω' ∈ G₂)
    (hfacts : ∀ᵐ ω ∂P, ω ∈ G₁ ∩ G₂ → ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω) :
    ∃ Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] Dr ∧
      (∀ ω, IsRegularDriver (Dr ω)) ∧
      ∀ᵐ ω ∂P, ω ∈ G₁ ∩ G₂ → recOf ⊤ (Dr ω) = recOf ⊤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω) := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  -- measurability of the canonical driver
  have hKΩ : @IsDyadicHitMeasurable Ω mΩ K := fun n j => h𝓜 _ (hK n j)
  have hx₀Ω : Measurable x₀ := hx₀.mono h𝓜 le_rfl
  obtain ⟨-, hliftc, -, hdom, hfwd, hlift⟩ := @Mt.hullChart_k2Inputs Ω mΩ K x₀ hKΩ hKc hKp hx₀Ω
  have hZ : Measurable fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    @Chart.measurable_chartTransport_random' Ω mΩ _ (Mu.isConformal_canon x₀ hKc hKp) hdom hfwd hlift hliftc _ hh
      1 0 (chiC κ)
  have hD : Measurable (canonDrvAt h12p hκ h c x₀ hKc hKp) :=
    (measurable_driverOf h12p hκ (-(Real.pi / 2))).comp (hc.prodMk hZ)
  -- the runs, the hull and the offset are frozen under the kernels
  have hfw : ∀ n, n ≤ ℓ + 1 → ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀),
      ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n =
        ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω₀) n := fun n hn =>
    Retain.ae_ae_run_eq w (WalkLaw.stagedPiecesRegular_regHist hRw) h𝓜
      ((pastSigma_mono w (StagedReg.regFam E w) hn).trans le_sup_right)
  have hfu : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀),
      ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω) k =
        ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω₀) k :=
    Retain.ae_ae_run_eq (upperSpec u l) (WalkLaw.stagedPiecesRegular_regHist hRu) h𝓜 le_sup_left
  have hfwall : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀), ∀ n : Fin (ℓ + 2),
      ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n =
        ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω₀) n := by
    have h1 : ∀ᵐ ω₀ ∂P, ∀ n : Fin (ℓ + 2), ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀),
        ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n =
          ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω₀) n :=
      ae_all_iff.2 fun n => hfw n (by omega)
    filter_upwards [h1] with ω₀ h
    exact ae_all_iff.2 h
  have hrw := StagedReg.ae_run_regHist hRw
  have hru := StagedReg.ae_run_regHist hRu
  have hKfr := Mx.ae_ae_condExpKernel_set_eq (μ := P) h𝓜 hK fun ω => (hKc ω).isClosed
  have hxfr := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝓜 hx₀
  set D : Ω → _ := fun ω =>
    ((fun n : Fin (ℓ + 2) => ExplState.run κ b jumps w (lowerD b jumps E ω) n),
      ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k, K ω, x₀ ω) with hDdef
  have hDc : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀), D ω = D ω₀ := by
    filter_upwards [hfwall, hfu, hrw, hru, hKfr, hxfr,
      KernelTower.ae_ae_condExpKernel_of_ae h𝓜 hrw, KernelTower.ae_ae_condExpKernel_of_ae h𝓜 hru]
      with ω₀ h0 h2 hrw₀ hru₀ hK₀ hx₀₀ hrwκ hruκ
    filter_upwards [h0, h2, hK₀, hx₀₀, hrwκ, hruκ] with ω e0 e2 eK ex erw eru
    simp only [hDdef]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext eK ex))
    · funext n
      change ExplState.run κ b jumps w (fun j => E w j ω) n = ExplState.run κ b jumps w (fun j => E w j ω₀) n
      rw [← erw n, ← hrw₀ n]; exact e0 n
    · change ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k =
        ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k
      rw [← eru k, ← hru₀ k]; exact e2
  -- `G₂` is kept under the kernels
  have hκG₂ : ∀ᵐ ω₀ ∂P, ω₀ ∈ G₂ → ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀), ω ∈ G₂ := by
    filter_upwards [hDc] with ω₀ h hω₀
    filter_upwards [h] with ω e
    simp only [hDdef, Prod.mk.injEq] at e
    obtain ⟨e0, e2, -, -⟩ := e
    refine hG₂ ω₀ ω (fun n hn => ?_) e2.symm hω₀
    have := congrFun e0 ⟨n, by omega⟩
    exact this.symm
  have hconst := ae_kernel_const_of_determined_inter (P := P) h𝓜 (D := D)
    (f := fun ω => recOf ⊤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω))
    (G₃ := {ω | ω ∈ G₁ ∩ G₂ → ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω}) hG₁ hκG₂
    hfacts hDc
    (fun ω ω' hωG hω₁ hω'G hω'₁ hDe => by
      have e := hDe
      simp only [hDdef, Prod.mk.injEq] at e
      obtain ⟨e0, e2, eK, ex⟩ := e
      have e0ℓ := congrFun e0 ⟨ℓ, by omega⟩
      have e1ℓ := congrFun e0 ⟨ℓ + 1, by omega⟩
      exact recOf_canon_eq_of_data h12p hκ E u l k ℓ (hω₁ hωG) (hω'₁ hω'G) e0ℓ e1ℓ e2 eK ex)
  have hcont : ∀ᵐ ω ∂P, ω ∈ G₁ ∩ G₂ → ContinuousOn (canonDrvAt h12p hκ h c x₀ hKc hKp ω).1
      {s | (s : ℝ≥0∞) ≤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω).2} := by
    filter_upwards [hfacts] with ω hω hωG
    exact (hω hωG).2.2.2.2.2
  exact exists_regular_rec_version h𝓜 hD (fun ω => Mz.isRegularDriver_driverOf h12p hκ _ _) hcont hconst

end InteractingSLE.Theorem14.SB.Gi
