/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ClDet
import InteractingSLE.Spec.Supplement.SB2MzTr
import InteractingSLE.Spec.Supplement.SB2NaStmt
import InteractingSLE.Spec.Supplement.WalkSideResumeCap

/-!
# The root time is frozen under the conditional laws given the capped pasts

Packet PROVE-SB2-CONDFIN (round 6; root route, step 1). **`rootTime`**: B's entrance time at `R = max (A ∩ ℝ)` with the
stopping convention (`Ck.entrTime` of piece `ℓ` when instruction `ℓ` launches, `⊤` otherwise).
**`ae_ae_rootTime_frozen`**:
for every cap `s`, almost surely, under the regular conditional law given the capped past `Na.capPast … ℓ s`, the
event `{rootTime ≤ s}` is frozen. The capped pasts fix the runs of the regularized families (upper walk through `k`,
lower walk through `ℓ` and piece `ℓ` capped at `s`, `CondDriverBridge.ae_ae_run_eq_of_le`); almost surely these are
the raw runs (`StagedReg.ae_run_regHist`), the raw pieces are regular, and the regularized piece's record capped at
`s` is the raw one (`StagedReg.canonDrv_regularize`, `retOf_eq_of_canonDrv_eq`); then `Cl.entrTime_le_iff_of_retOf_eq`.

With a measurable event agreeing with `{rootTime ≤ s}` almost surely, `WalkLaw.mem_aeSigma_of_frozen` makes it an event
of the completed capped past — the stopping property of the corrected root variant's filtration (handoff R5.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Cm

open Exist Exist.Staged Exist.StagedLaw Lk GW1W LuM WalkSide

/-- **The record capped at any time is a function of the stopped driver** (`canonDrv ⊤`). -/
theorem retOf_eq_of_canonDrv_eq {e e' : Drv} (h : canonDrv ⊤ e = canonDrv ⊤ e') (s : ℝ≥0∞) :
    retOf s e = retOf s e' := by
  have h2 : e.2 = e'.2 := by
    have := congrArg Prod.snd h
    simpa [canonDrv] using this
  have h1 : ∀ r : ℝ≥0, e.1 (min (r : ℝ≥0∞) e.2).toNNReal = e'.1 (min (r : ℝ≥0∞) e'.2).toNNReal := by
    intro r
    have := congrFun (congrArg Prod.fst h) r
    simpa [canonDrv] using this
  unfold retOf
  refine Prod.ext (funext fun r => ?_) (Prod.ext (by rw [h2]) (by rw [h2]))
  have hr : min (r : ℝ≥0∞) s = ((min (r : ℝ≥0∞) s).toNNReal : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal (lt_of_le_of_lt (min_le_left _ _) ENNReal.coe_lt_top).ne).symm
  have e1 : min (r : ℝ≥0∞) (min s e.2) = min ((min (r : ℝ≥0∞) s).toNNReal : ℝ≥0∞) e.2 := by
    rw [← hr, min_assoc]
  have e2 : min (r : ℝ≥0∞) (min s e'.2) = min ((min (r : ℝ≥0∞) s).toNNReal : ℝ≥0∞) e'.2 := by
    rw [← hr, min_assoc]
  show e.1 (min (r : ℝ≥0∞) (min s e.2)).toNNReal = e'.1 (min (r : ℝ≥0∞) (min s e'.2)).toNNReal
  rw [e1, e2]
  exact h1 _

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

open Classical in
/-- **B's root time at instruction `ℓ`**: the entrance time of piece `ℓ` at `R = max (A ∩ ℝ)` (`Ck.entrTime`) when
instruction `ℓ` launches, `⊤` otherwise. -/
def rootTime (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (ω : Ω) : ℝ≥0∞ :=
  if (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none then
    Ck.entrTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) (realMax (upperPrefix κ b jumps E u l k ω))
  else ⊤

/-- The regularized driver of a regular launched walk piece has the raw piece's record at every cap. -/
theorem retOf_regHist_eq {D : ℕ → Drv} {θ : ℝ}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) (s : ℝ≥0∞) :
    retOf s (StagedReg.regularize (instrTime (boundaryWalkSpec b jumps θ true) n) (D n)) = retOf s (D n) := by
  have hPR := pieceRegular_of_launch hP hl
  rw [GW1W.instrTime_walk hl]
  refine retOf_eq_of_canonDrv_eq (StagedReg.canonDrv_regularize hPR.1 ?_) s
  rw [min_eq_right le_top]
  exact hPR.2.1

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ} {l : List (ℝ × ℝ≥0)}
  {k ℓ : ℕ}

/-- **The root time is frozen under the conditional laws given the capped past at `s`.** -/
theorem ae_ae_rootTime_frozen (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEu : IsStagedHistory κ b jumps P h (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hRu : StagedPiecesRegular κ b jumps P (Lu.upperSpec u l) (E (Lu.upperSpec u l)))
    (hEl : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRl : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hℓ : ℓ ≤ (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (s : ℝ≥0) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Na.capPast κ b jumps E u l k ℓ s) ω₀),
      (rootTime κ b jumps E u l k ℓ ω ≤ s ↔ rootTime κ b jumps E u l k ℓ ω₀ ≤ s) := by
  classical
  set lw := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hlw
  set up := Lu.upperSpec u l with hup
  set cs := capSpec lw ℓ (-(Real.pi / 2)) (s : ℝ≥0∞) with hcs
  set Fl := StagedReg.regHist lw (E lw) with hFl
  set Fu := StagedReg.regHist up (E up) with hFu
  have hFlr : ∀ j ω, IsRegularDriver (Fl j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hFur : ∀ j ω, IsRegularDriver (Fu j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have h𝒢 : Na.capPast κ b jumps E u l k ℓ s ≤ mΩ :=
    sup_le (Mz.pastSigma_le hb up (StagedReg.measurable_regHist hEu.1) hFur k)
      (Mz.pastSigma_le hb cs (StagedReg.measurable_regHist hEl.1) hFlr (ℓ + 1))
  -- frozen runs of the regularized families
  have hfrl : ∀ i, i ≤ ℓ + 1 → ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Na.capPast κ b jumps E u l k ℓ s) ω₀),
      ExplState.run κ b jumps cs (fun j => Fl j ω) i = ExplState.run κ b jumps cs (fun j => Fl j ω₀) i :=
    fun i hi => CondDriverBridge.ae_ae_run_eq_of_le (P := P) cs (E := Fl) (k := i) (fun j _ ω => hFlr j ω) h𝒢
      ((pastSigma_mono cs Fl hi).trans le_sup_right)
  have hfru := CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) up (E := Fu) (k := k)
    (fun j _ ω => hFur j ω) h𝒢 le_sup_left
  -- the good event
  have hG : ∀ᵐ ω ∂P, (∀ n, ExplState.run κ b jumps lw (fun j => Fl j ω) n =
      ExplState.run κ b jumps lw (fun j => E lw j ω) n) ∧
      (∀ n, ExplState.run κ b jumps up (fun j => Fu j ω) n = ExplState.run κ b jumps up (fun j => E up j ω) n) ∧
      RegLaunches κ b jumps lw (fun j => E lw j ω) := by
    filter_upwards [StagedReg.ae_run_regHist hRl, StagedReg.ae_run_regHist hRu,
      GW1W.regLaunches_of_stagedPiecesRegular hRl] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [hfrl ℓ (Nat.le_succ ℓ), hfrl (ℓ + 1) le_rfl, hfru, hG,
    KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hG] with ω₀ hl₀ hs₀ hu₀ hG₀ hGk
  filter_upwards [hl₀, hs₀, hu₀, hGk] with ω hlω hsω huω hGω
  -- the raw lower runs before `ℓ`
  have hrunF : ExplState.run κ b jumps lw (fun j => Fl j ω) ℓ = ExplState.run κ b jumps lw (fun j => Fl j ω₀) ℓ := by
    rw [← run_capSpec_of_le (θ := -(Real.pi / 2)) (τ := (s : ℝ≥0∞)) hℓ _ le_rfl,
      ← run_capSpec_of_le (θ := -(Real.pi / 2)) (τ := (s : ℝ≥0∞)) hℓ _ le_rfl]
    exact hlω
  have hrun : ExplState.run κ b jumps lw (fun j => E lw j ω) ℓ =
      ExplState.run κ b jumps lw (fun j => E lw j ω₀) ℓ := by
    rw [← hGω.1 ℓ, ← hG₀.1 ℓ, hrunF]
  have hlaunch := launches_run_succ_of_run_eq lw hrun
  -- the upper prefix
  have hR : realMax (upperPrefix κ b jumps E u l k ω) = realMax (upperPrefix κ b jumps E u l k ω₀) := by
    have hupr : ExplState.run κ b jumps up (fun j => E up j ω) k =
        ExplState.run κ b jumps up (fun j => E up j ω₀) k := by
      rw [← hGω.2.1 k, ← hG₀.2.1 k, huω]
    show realMax (SB.prefixPhysSet κ b jumps up (fun j => E up j ω) k ∪ _) =
      realMax (SB.prefixPhysSet κ b jumps up (fun j => E up j ω₀) k ∪ _)
    unfold SB.prefixPhysSet
    rw [hupr]
  unfold rootTime
  by_cases hl : (ExplState.run κ b jumps lw (fun j => E lw j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none
  · have hlω' : (ExplState.run κ b jumps lw (fun j => E lw j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [congrFun hlaunch ℓ]; exact hl
    rw [ite_eq_left hlω', ite_eq_left hl, hR]
    -- the records capped at `s`
    have hlF : ∀ ω', ExplState.run κ b jumps lw (fun j => Fl j ω') ℓ =
        ExplState.run κ b jumps lw (fun j => E lw j ω') ℓ →
        ((ExplState.run κ b jumps cs (fun j => Fl j ω') (ℓ + 1)).2.2.2.1 ℓ ≠ none ↔
          (ExplState.run κ b jumps lw (fun j => E lw j ω') (ℓ + 1)).2.2.2.1 ℓ ≠ none) := by
      intro ω' hω'
      have e1 : (ExplState.run κ b jumps cs (fun j => Fl j ω') (ℓ + 1)).2.2.2.1 =
          (ExplState.run κ b jumps lw (fun j => Fl j ω') (ℓ + 1)).2.2.2.1 := by
        rw [WalkSideResume.launches_capSpec_time_indep hℓ _ (s : ℝ≥0∞) ⊤, run_capSpec_succ hℓ,
          show ExplState.run κ b jumps lw (fun j => Fl j ω') (ℓ + 1) =
            ExplState.flowStep κ b lw.2.1 (ExplState.run κ b jumps lw (fun j => Fl j ω') ℓ) ℓ (Fl ℓ ω')
              (-(Real.pi / 2)) ⊤ by rw [run_succ, hwℓ]; rfl]
      rw [e1, launches_run_succ_of_run_eq lw hω']
    have hretF : retOf (s : ℝ≥0∞) (Fl ℓ ω) = retOf (s : ℝ≥0∞) (Fl ℓ ω₀) := by
      have hr := retained_run_succ_self (κ := κ) (b := b) (jumps := jumps) cs (fun j => Fl j ω) ℓ
      have hr₀ := retained_run_succ_self (κ := κ) (b := b) (jumps := jumps) cs (fun j => Fl j ω₀) ℓ
      have hc := (hlF ω (hGω.1 ℓ)).2 hlω'
      have hc₀ := (hlF ω₀ (hG₀.1 ℓ)).2 hl
      rw [ite_eq_right hc, instrTime_capSpec hℓ] at hr
      rw [ite_eq_right hc₀, instrTime_capSpec hℓ] at hr₀
      rw [← hr, ← hr₀, hsω]
    have hret : retOf (s : ℝ≥0∞) (E lw ℓ ω) = retOf (s : ℝ≥0∞) (E lw ℓ ω₀) := by
      rw [← retOf_regHist_eq hGω.2.2 hlω' _, ← retOf_regHist_eq hG₀.2.2 hl _]
      exact hretF
    exact Cl.entrTime_le_iff_of_retOf_eq hGω.2.2 hG₀.2.2 hlω' hrun hret _
  · have hlω' : ¬ (ExplState.run κ b jumps lw (fun j => E lw j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [congrFun hlaunch ℓ]; exact hl
    rw [ite_eq_right hlω', ite_eq_right hl]

end InteractingSLE.Theorem14.SB.Cm
