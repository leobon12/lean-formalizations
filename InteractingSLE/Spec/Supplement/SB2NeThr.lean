/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeVer

/-!
# F2b′'s (I4) bound: the threshold comes by the relative lifetime

Packet PROVE-AUX61-NOJUMP (round 22, component F). At a finite relative lifetime the relative trace converges to a
bad relative point right of the seed (`Ne.endpoint_bad`). The trace extended by that point generates any continuous
continuation of the frozen drivers through the lifetime, and the threshold comes by it (SB2WORD's
`Wf.thr_le_of_bad_right`): clause (iii) of `Nd.SB2LowerStageVersionStatement5`.

* `continuousOn_capExt_of_tendsto`, `isGeneratingTrace_capExt`, **`StopIn.ae_thr_le`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Vr

/-- `Lk.continuousOn_capExt` from the convergence of the capacity trace. -/
theorem continuousOn_capExt_of_tendsto {ρ : ℝ → ℂ} (hρ : IsDrivenCurve ρ) (hfin : capLife ρ ≠ ⊤) {z : ℂ}
    (hz : Tendsto (capTrace ρ) (𝓝[<] (capLife ρ).toNNReal) (𝓝 z)) :
    ContinuousOn (capExt ρ z) {s | (s : ℝ≥0∞) ≤ capLife ρ} := by
  set T := (capLife ρ).toNNReal with hTdef
  have hset : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ capLife ρ} = Iic T := by
    ext s; exact coe_le_capLife_iff hfin s
  rw [hset]
  intro s hs
  rcases (mem_Iic.1 hs).lt_or_eq with hlt | rfl
  · have hlt' : (s : ℝ≥0∞) < capLife ρ := (coe_lt_capLife_iff hfin s).2 hlt
    have heq : capExt ρ z =ᶠ[𝓝 s] capTrace ρ := by
      filter_upwards [Iio_mem_nhds hlt] with s' hs'
      exact capExt_of_lt ((coe_lt_capLife_iff hfin s').2 hs')
    exact ((hρ.continuousAt_capTrace hlt').congr heq.symm).continuousWithinAt
  · rw [← continuousWithinAt_Iio_iff_Iic]
    have hval : capExt ρ z T = z := by
      unfold capExt
      have : ¬ ((T : ℝ≥0∞) < capLife ρ) := fun h => lt_irrefl _ ((coe_lt_capLife_iff hfin T).1 h)
      simp only [this, ↓reduceIte]
    rw [ContinuousWithinAt, hval]
    refine hz.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s' hs'
    exact (capExt_of_lt ((coe_lt_capLife_iff hfin s').2 hs')).symm

/-- **The extended capacity trace generates every driver that agrees with the relative driver before the lifetime.** -/
theorem isGeneratingTrace_capExt {ρ : ℝ → ℂ} (hρ : IsDrivenCurve ρ) (hfin : capLife ρ ≠ ⊤) {z : ℂ}
    (hz : Tendsto (capTrace ρ) (𝓝[<] (capLife ρ).toNNReal) (𝓝 z)) {Wr : ℝ≥0 → ℝ}
    (hgen : ∀ V : ℝ≥0∞, V < capLife ρ → IsGeneratingTrace Wr V (capTrace ρ)) {Wc : ℝ≥0 → ℝ}
    (hWc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife ρ → Wc t = Wr t) :
    IsGeneratingTrace Wc (capLife ρ) (capExt ρ z) := by
  have hpos := Vk.capLife_pos hρ
  refine Sec5.CrossRestart.isGeneratingTrace_congr_drive ⟨?_, continuousOn_capExt_of_tendsto hρ hfin hz,
    fun t ht => ?_⟩ hWc
  · rw [capExt_of_lt (by simpa using hpos)]
    exact capTrace_zero hρ
  · obtain ⟨V, htV, hVU⟩ := exists_between ht
    have hfill := (hgen V hVU).2.2 t htV
    have himg : capExt ρ z '' Icc 0 t = capTrace ρ '' Icc 0 t :=
      image_congr fun s hs => capExt_of_lt (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)
    rw [himg]
    exact hfill


variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

namespace StopIn

variable (T : StopIn P κ b jumps E u l k ℓ (-(Real.pi / 2)))

/-- **Clause (iii): every continuation of the frozen drivers reaches its threshold by the relative lifetime.** -/
theorem ae_thr_le
    (hend : ∀ ω ∈ T.S.Eg ∩ T.Gr, capLife (T.S.ρM ω) ≠ ⊤ → ∃ y : ℝ, 0 < y ∧
      Tendsto (capTrace (T.S.ρM ω)) (𝓝[<] (capLife (T.S.ρM ω)).toNNReal) (𝓝 (y : ℂ)) ∧
      Vq.IsBadPoint (cellXL κ (-(Real.pi / 2)) T.cw (angleWordType κ (-(Real.pi / 2)) (T.cw ω)) ω)
        (cellXR κ (-(Real.pi / 2)) T.cw (angleWordType κ (-(Real.pi / 2)) (T.cw ω)) ω)
        (typedRhoL (angleWordType κ (-(Real.pi / 2)) (T.cw ω)))
        (typedRhoR (angleWordType κ (-(Real.pi / 2)) (T.cw ω))) (y : ℂ))
    {β : Ω → BoundaryWord} (hβ : ∀ᵐ ω ∂P, T.cw ω = β ω) (w : WordType) (Wc : ℝ≥0 → Ω → ℝ)
    (hWc : ∀ ω, Continuous fun t => Wc t ω) :
    ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β T.S.F w → capLife (T.S.ρM ω) < ⊤ →
      (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T.V m ω → Wc t ω = T.W m t ω) →
      FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ (-(Real.pi / 2)) β w)
        (cellXR κ (-(Real.pi / 2)) β w) ω ≤ capLife (T.S.ρM ω) := by
  filter_upwards [T.ae_mem_Gs, hβ] with ω hG hβω hc hfin hagree
  have hGω := hG hc.1.1
  have hd := T.S.driven_ρM ω
  have hfin' : capLife (T.S.ρM ω) ≠ ⊤ := hfin.ne
  obtain ⟨y, hy, hz, hbad⟩ := hend ω hGω hfin'
  have hw : angleWordType κ (-(Real.pi / 2)) (T.cw ω) = w := by rw [hβω]; exact hc.1.2
  have hWr : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife (T.S.ρM ω) → Wc t ω = T.Wr t ω := fun t ht => by
    rw [← T.V_sup hGω] at ht
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 ht
    rw [hagree m t hm, T.W_eq_Wr hGω (by rw [← T.V_eq hGω]; exact hm.le)]
  have hgen := isGeneratingTrace_capExt hd hfin' hz (Wr := fun t => T.Wr t ω)
    (fun V hV => T.isGeneratingTrace_Wr ω hV) (Wc := fun t => Wc t ω) hWr
  have hpos0 := Vk.capLife_pos hd
  have hT0 : 0 < (capLife (T.S.ρM ω)).toNNReal := ENNReal.toNNReal_pos hpos0.ne' hfin'
  have hTU : (((capLife (T.S.ρM ω)).toNNReal : ℝ≥0) : ℝ≥0∞) = capLife (T.S.ρM ω) := ENNReal.coe_toNNReal hfin'
  have hval : capExt (T.S.ρM ω) (y : ℂ) (capLife (T.S.ρM ω)).toNNReal = y := by
    unfold capExt
    simp only [hTU, lt_irrefl, ↓reduceIte]
  have hW0 : Wc 0 ω = 0 := by
    rw [hWr 0 (by simpa using hpos0), T.Wr_zero]
  obtain ⟨-, hb⟩ := hbad
  rcases hb with ⟨-, hwR⟩ | ⟨hle, -⟩
  · rw [hw, T.cellXR_congr hβω] at hwR
    have h := Wf.thr_le_of_bad_right (W := Wc) (ω := ω) (xL := cellXL κ (-(Real.pi / 2)) β w)
      (xR := cellXR κ (-(Real.pi / 2)) β w) (ρL := typedRhoL w) (ρR := typedRhoR w) (hWc ω) hW0 hgen hT0
      hTU.le (by rw [hval]; simp) (by rw [hval]; simpa using hy) (by rw [hval]; simpa using hwR)
    exact h.trans hTU.le
  · exfalso
    have : (0 : ℝ) < ((y : ℝ) : ℂ).re := by simpa using hy
    linarith

end StopIn

end InteractingSLE.Theorem14.SB.Nd
