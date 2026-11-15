/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CfHull
import InteractingSLE.Spec.Supplement.SB2JvV5
import InteractingSLE.Spec.Supplement.SB2MzId
import InteractingSLE.Spec.Supplement.SB2MzOff
import InteractingSLE.Spec.Supplement.SB2JwZero

/-!
# The relative root's record is determined by B's runs (deterministic core)

Packet PROVE-SB2-CONDFIN (Target 1, the root record, steps (a), (c), (d)). Fix B's drivers `D, D'` whose runs agree
up to `n + 1`, on the root event `RootEv n` (`R` entered by stage `n`, offset `n`; it is decided by these runs):

* (a) **`drv_eq_of_run_eq`**: a launched piece's retained datum gives equal lifetimes and agreement up to the lifetime;
* (c) `rootEv_iff`, **`rootEv_congr`** (the root event is decided by the runs up to `n + 1`),
  `not_zeroRoot_of_ent` (no zero root once `R` has entered at the offset);
* (d) `stageFacts_congr`, **`recOf_eq_of_stageFacts`** (two relative drivers with the stage facts of the same piece
  have the same record), **`recOf_root_eq`**: two relative roots with the root facts (D25, `Lk.RootFactsAt`) have the
  same record; `continuousOn_root` (the root is continuous up to its lifetime).

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cf

open Exist Exist.Staged Exist.StagedLaw Lk Mz GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- **(a) The retained datum of a launched piece**: walks with equal runs at `n + 1` and a launch at `n` have pieces
`n` with equal lifetimes, agreeing up to the lifetime. -/
theorem drv_eq_of_run_eq {D D' : ℕ → Drv} {n : ℕ}
    (hrun : wRun κ θ b J D (n + 1) = wRun κ θ b J D' (n + 1))
    (hl : (wRun κ θ b J D (n + 1)).2.2.2.1 n ≠ none) :
    (D n).2 = (D' n).2 ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ (D n).2 → (D n).1 s = (D' n).1 s := by
  have hl' : (wRun κ θ b J D' (n + 1)).2.2.2.1 n ≠ none := by rw [← hrun]; exact hl
  have hr := retained_run_succ_self (κ := κ) (b := b) (jumps := J) (boundaryWalkSpec b J θ true) D n
  have hr' := retained_run_succ_self (κ := κ) (b := b) (jumps := J) (boundaryWalkSpec b J θ true) D' n
  rw [ite_eq_right hl, GW1W.instrTime_walk hl] at hr
  rw [ite_eq_right hl', GW1W.instrTime_walk hl'] at hr'
  have he : retOf ⊤ (D n) = retOf ⊤ (D' n) := by
    rw [← hr, ← hr']
    exact congrArg (fun s : ExplState => s.2.2.1 n) hrun
  have h2 : (D n).2 = (D' n).2 := by
    have h := congrArg (fun r => r.2.1) he
    simp only [retOf, min_eq_right (le_top : (D n).2 ≤ ⊤), min_eq_right (le_top : (D' n).2 ≤ ⊤)] at h
    exact h
  refine ⟨h2, fun s hs => ?_⟩
  have h := congrFun (congrArg Prod.fst he) s
  simp only [retOf, min_eq_right (le_top : (D n).2 ≤ ⊤), min_eq_right (le_top : (D' n).2 ≤ ⊤)] at h
  rw [← h2, min_eq_left hs, ENNReal.toNNReal_coe] at h
  exact h

/-- **The root event**: `R` has entered by stage `n` and the offset is `n`. -/
def RootEv (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (R : ℝ) (D : ℕ → Drv) (n : ℕ) : Prop :=
  Ent κ θ b J R D n ∧ relOff κ θ b J R D = n

/-- The root event as a finite formula of first entries. -/
theorem rootEv_iff (R : ℝ) (D : ℕ → Drv) (n : ℕ) :
    RootEv κ θ b J R D n ↔ ∃ e ≤ n, (Ent κ θ b J R D e ∧ ∀ i < e, ¬ Ent κ θ b J R D i) ∧
      relOffOf κ θ b J R D e = n := by
  constructor
  · rintro ⟨hent, hrel⟩
    obtain ⟨e, he, ⟨h1, h2⟩, h3⟩ := (relOffEvent_iff κ θ b J R D n).1 ⟨hrel, n, Nat.le_succ n, hent⟩
    have hen : e ≤ n := by
      by_contra hlt
      exact h2 n (by omega) hent
    exact ⟨e, hen, ⟨h1, h2⟩, h3⟩
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    have hrel := ((relOffEvent_iff κ θ b J R D n).2 ⟨e, by omega, ⟨h1, h2⟩, h3⟩).1
    refine ⟨?_, hrel⟩
    unfold Ent at h1 ⊢
    exact statePhysicalSet_mono (by omega) h1

/-- **The root event is decided by the runs up to `n + 1`.** -/
theorem rootEv_congr (R : ℝ) {D D' : ℕ → Drv} (n : ℕ)
    (h : ∀ i ≤ n + 1, wRun κ θ b J D i = wRun κ θ b J D' i) :
    RootEv κ θ b J R D n ↔ RootEv κ θ b J R D' n := by
  have hent : ∀ i ≤ n, Ent κ θ b J R D i ↔ Ent κ θ b J R D' i := by
    intro i hi
    unfold Ent
    rw [show ExplState.run κ b J (boundaryWalkSpec b J θ true) D (i + 1) =
      ExplState.run κ b J (boundaryWalkSpec b J θ true) D' (i + 1) from h (i + 1) (by omega)]
  have hof : ∀ e ≤ n, relOffOf κ θ b J R D e = relOffOf κ θ b J R D' e := by
    intro e he
    unfold relOffOf
    rw [show ExplState.run κ b J (boundaryWalkSpec b J θ true) D (2 * (e / 2) + 1) =
      ExplState.run κ b J (boundaryWalkSpec b J θ true) D' (2 * (e / 2) + 1) from h _ (by omega)]
  rw [rootEv_iff, rootEv_iff]
  constructor
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, he, ⟨(hent e he).1 h1, fun i hi h4 => h2 i hi ((hent i (by omega)).2 h4)⟩, (hof e he) ▸ h3⟩
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, he, ⟨(hent e he).2 h1, fun i hi h4 => h2 i hi ((hent i (by omega)).1 h4)⟩, (hof e he).symm ▸ h3⟩

/-- **No zero root once `R` has entered at the offset.** -/
theorem not_zeroRoot_of_ent {R : ℝ} {D : ℕ → Drv} (h : Ent κ θ b J R D (relOff κ θ b J R D)) :
    ¬ ZeroRoot κ θ b J R D := by
  rintro ⟨hA, hM⟩
  have hex : ∃ i, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (i + 1)) :=
    ⟨_, h⟩
  have hs := (startOff_eq κ θ b J R D).1 hA
  have hmin := (entryStage_spec κ θ b J hex).2 (startOff κ θ b J R D) (by omega)
  unfold Ent at h
  rw [relOff_of_not_mark κ θ b J hM] at h
  exact hmin h

/-- Stage facts transfer between pieces with the same points and lifetime. -/
theorem stageFacts_congr {c : Chart} {m : ℝ} {s₁ s₂ : ExplState} {e₁ e₁' e₂ : Drv} {t₀ : ℝ≥0}
    (hp : pcPt s₁ e₁ = pcPt s₁ e₁') (hL : e₁.2 = e₁'.2) (h : Mn.StageFacts c m s₁ e₁ t₀ s₂ e₂) :
    Mn.StageFacts c m s₁ e₁' t₀ s₂ e₂ := by
  unfold Mn.StageFacts at h ⊢
  rw [← hp, ← hL]
  exact h

/-- **Two relative drivers with the stage facts of the same piece have the same record.** -/
theorem recOf_eq_of_stageFacts {c : Chart} {m : ℝ} {s₁ s₂ : ExplState} {e₁ e₂ e₂' : Drv} {t₀ : ℝ≥0}
    (h : Mn.StageFacts c m s₁ e₁ t₀ s₂ e₂) (h' : Mn.StageFacts c m s₁ e₁ t₀ s₂ e₂')
    (hr : IsRegularDriver e₂) (hr' : IsRegularDriver e₂') : recOf ⊤ e₂ = recOf ⊤ e₂' := by
  obtain ⟨-, hL, hG, -, -, -, hPR⟩ := h
  obtain ⟨-, hL', hG', -, -, -, -⟩ := h'
  refine Mz.recOf_eq_of_ident hr hr' ?_ (hL.trans hL'.symm) fun t ht => ?_
  · rw [min_eq_right le_top]
    exact hPR.2.1
  · rw [hL] at ht
    obtain ⟨T, htT, hT⟩ := exists_between ht
    exact Sec7.SideHeight.eq_of_isGeneratingTrace (hG T hT) (hG' T hT) htT

/-- **(d) The relative root's record is determined by B's runs on the root event.** -/
theorem recOf_root_eq {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart} {m : ℝ} {D D' F F' : ℕ → Drv} {n : ℕ}
    (hrun : ∀ i ≤ n + 1, wRun κ θ b J D i = wRun κ θ b J D' i) (hev : RootEv κ θ b J R D n)
    (hl : ¬ ZeroRoot κ θ b J R D →
      (wRun κ θ b J D (relOff κ θ b J R D + 1)).2.2.2.1 (relOff κ θ b J R D) ≠ none)
    (hF : RootFactsAt κ θ b J b₂ J₂ R c m D F) (hF' : RootFactsAt κ θ b J b₂ J₂ R c m D' F')
    (hr : IsRegularDriver (F 0)) (hr' : IsRegularDriver (F' 0)) : recOf ⊤ (F 0) = recOf ⊤ (F' 0) := by
  obtain ⟨hent', hrel'⟩ := (rootEv_congr R n hrun).1 hev
  obtain ⟨hent, hrel⟩ := hev
  have hZ : ¬ ZeroRoot κ θ b J R D := not_zeroRoot_of_ent (by rw [hrel]; exact hent)
  have hZ' : ¬ ZeroRoot κ θ b J R D' := not_zeroRoot_of_ent (by rw [hrel']; exact hent')
  have hln : (wRun κ θ b J D (n + 1)).2.2.2.1 n ≠ none := by
    have h := hl hZ
    rwa [hrel] at h
  obtain ⟨h2, h1⟩ := drv_eq_of_run_eq (hrun (n + 1) le_rfl) hln
  have h1' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 → (D n).1 t = (D' n).1 t := fun t ht => h1 t ht.le
  have hrn : wRun κ θ b J D n = wRun κ θ b J D' n := hrun n (Nat.le_succ n)
  have hpc : pcPt (wRun κ θ b J D n) (D n) = pcPt (wRun κ θ b J D n) (D' n) := pcPt_congr _ h2 h1'
  have hsh : shiftD κ θ b J R D 0 = shiftD κ θ b J R D' 0 := by
    unfold shiftD
    rw [ite_eq_left rfl, ite_eq_left rfl, hrel, hrel', ← hrn, visitTime_congr _ h2 h1' R]
  by_cases hs : (D n).2 - shiftD κ θ b J R D 0 = 0
  · rw [hF.1 (Or.inr (by rw [hrel]; exact hs)),
      hF'.1 (Or.inr (by rw [hrel', ← h2, ← hsh]; exact hs))]
  · obtain ⟨-, hSF⟩ := hF.2.1 hZ (by rw [hrel]; exact hs)
    obtain ⟨-, hSF'⟩ := hF'.2.1 hZ' (by rw [hrel', ← h2, ← hsh]; exact hs)
    rw [hrel] at hSF
    rw [hrel', ← hrn, ← hsh] at hSF'
    have hw : wRun κ θ b₂ J₂ F' 0 = wRun κ θ b₂ J₂ F 0 := rfl
    rw [hw] at hSF'
    exact recOf_eq_of_stageFacts hSF (stageFacts_congr hpc.symm h2.symm hSF') hr hr'

/-- **The relative root is continuous up to its lifetime** (root facts). -/
theorem continuousOn_root {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart} {m : ℝ} {D F : ℕ → Drv}
    (hF : RootFactsAt κ θ b J b₂ J₂ R c m D F) :
    ContinuousOn (F 0).1 {s | (s : ℝ≥0∞) ≤ min ⊤ (F 0).2} := by
  by_cases h : ZeroRoot κ θ b J R D ∨ (D (relOff κ θ b J R D)).2 - shiftD κ θ b J R D 0 = 0
  · rw [hF.1 h]
    exact continuousOn_const
  · push Not at h
    obtain ⟨-, hSF⟩ := hF.2.1 h.1 h.2
    rw [min_eq_right le_top]
    exact hSF.2.2.2.2.2.2.2.1

end InteractingSLE.Theorem14.SB.Cf
