/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJTools
import InteractingSLE.Spec.Sec5.StagedRepLaterMain

/-!
# Prop 5.9's later root stages: the canonical stage objects on `Gam`

Packet PROVE-STAGED-REPJ. PROVE-STAGED-REP2's `gamData r` runs PIECES' root tree construction on
`Gam = DistOn × HistorySpace 0 0` (field in chart `Q`, counterflow history) with a Borel good set. Its candidate family
`gamCand r` carries PIECES' canonical objects of every stage: the past `gamQ r ℓ t` (`canonQ` with the base
`gamPast r`), the reached event `gamR r ℓ t` (`canonR`), the start `canonY` and the killed samples. They are the
common Borel observables of the transfer of a later stage's comparison clause (`compClauseK_transfer`):

* **`gamObsJ`**, **`measurable_gamObsJ`**: (canonical start, killed samples) of the candidate `(ℓ, t)`;
* **`canonQ_le`**: the canonical pasts of a regular family with a sub-σ-algebra base are sub-σ-algebras.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open Prop59Stage Prop59System Prop59Pieces StagedCand StagedKCand StagedKill StagedRepLater
open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart

/-! ### Canonical pasts are sub-σ-algebras -/

section Le

variable {Ω : Type*} {𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL₀ nR₀ : ℕ} {cand : CandFam Ω nL₀ nR₀}
  {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀} {y₀ : Ω → Start (nL₀ + 0) (nR₀ + 0)}

/-- **The canonical pasts of a regular family are sub-σ-algebras** when the base is. -/
theorem canonQ_le (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (h𝓑 : 𝓑 ≤ mΩ) :
    ∀ j t, canonQ 𝓑 cand G hnL hnR y₀ j t ≤ mΩ
  | 0, _ => h𝓑
  | j + 1, t => by
    refine sup_le (canonQ_le hfam hy₀ h𝓑 j (Fin.init t)) (MeasurableSpace.generateFrom_le ?_)
    rintro B ⟨n, m, S, -, hS, rfl⟩
    have hr := isRegStage_candStage (hnL := hnL) (hnR := hnR) hfam hy₀ j (Fin.init t)
    refine MeasurableSet.inter ?_ ((measurable_swT hr n).prodMk (measurable_nextStart hr n) hS)
    exact (measurableSet_succSet hr n).inter (measurable_swIdx hr n (measurableSet_singleton m))

end Le

/-! ### The stage objects on `Gam` -/

section Gam

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')

/-- The candidate family of the root tree on `Gam`. -/
abbrev gamCand (r : ℝ≥0) : CandFam Gam (rootNL (sourceWord (x₀ := x₀) hκ hb)) (rootNR (sourceWord (x₀ := x₀) hκ hb)) :=
  (gamData h44 hκ hκ4 (x₀ := x₀) hb r).cand

/-- The root start on `Gam`: the driver at `0` and the dilated root marks. -/
abbrev gamY0 (r : ℝ≥0) (γ : Gam) :
    Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + 0) (rootNR (sourceWord (x₀ := x₀) hκ hb) + 0) :=
  ((0 : ℝ), (gamData h44 hκ hκ4 (x₀ := x₀) hb r).xL0 γ, (gamData h44 hκ hκ4 (x₀ := x₀) hb r).xR0 γ)

/-- The canonical past of the candidate `(ℓ, t)` on `Gam`. -/
abbrev gamQ (r : ℝ≥0) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : MeasurableSpace Gam :=
  canonQ (gamPast r) (gamCand h44 hκ hκ4 (x₀ := x₀) hb r) ratGrid (rootNL_pos _) (rootNR_pos _)
    (gamY0 h44 hκ hκ4 (x₀ := x₀) hb r) ℓ t

/-- The canonical reached event of the candidate `(ℓ, t)` on `Gam`. -/
abbrev gamR (r : ℝ≥0) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) : Set Gam :=
  canonR (gamCand h44 hκ hκ4 (x₀ := x₀) hb r) ratGrid (rootNL_pos _) (rootNR_pos _)
    (gamY0 h44 hκ hκ4 (x₀ := x₀) hb r) univ ℓ t

/-- **The observable of the candidate `(ℓ, t)` on `Gam`**: its canonical start and its killed samples. -/
def gamObsJ (r : ℝ≥0) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (γ : Gam) :
    Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + ℓ) (rootNR (sourceWord (x₀ := x₀) hκ hb) + ℓ) ×
      Samp (rootNL (sourceWord (x₀ := x₀) hκ hb) + ℓ) (rootNR (sourceWord (x₀ := x₀) hκ hb) + ℓ) :=
  (canonY (gamCand h44 hκ hκ4 (x₀ := x₀) hb r) (gamY0 h44 hκ hκ4 (x₀ := x₀) hb r) ℓ t γ,
    pieceSamp (gamCand h44 hκ hκ4 (x₀ := x₀) hb r ℓ t).W (gamCand h44 hκ hκ4 (x₀ := x₀) hb r ℓ t).VL
      (gamCand h44 hκ hκ4 (x₀ := x₀) hb r ℓ t).VR (gamCand h44 hκ hκ4 (x₀ := x₀) hb r ℓ t).ζ γ)

theorem measurable_gamY0 (r : ℝ≥0) : Measurable (gamY0 h44 hκ hκ4 (x₀ := x₀) hb r) :=
  measurable_const.prodMk ((isReg_gamData h44 hκ hκ4 hb r).xL0.prodMk (isReg_gamData h44 hκ hκ4 hb r).xR0)

theorem isRegFam_gamCand (r : ℝ≥0) : IsRegFam (gamCand h44 hκ hκ4 (x₀ := x₀) hb r) :=
  (isReg_gamData h44 hκ hκ4 hb r).isRegFam

theorem measurable_gamObsJ (r : ℝ≥0) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) :
    Measurable (gamObsJ h44 hκ hκ4 (x₀ := x₀) hb r ℓ t) :=
  (measurable_canonY (isRegFam_gamCand h44 hκ hκ4 hb r) (measurable_gamY0 h44 hκ hκ4 hb r) ℓ t).prodMk
    (measurable_pieceSamp_of_isRegPiece (isRegFam_gamCand h44 hκ hκ4 hb r ℓ t))

theorem gamQ_le (r : ℝ≥0) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) :
    gamQ h44 hκ hκ4 (x₀ := x₀) hb r ℓ t ≤ (inferInstance : MeasurableSpace Gam) :=
  canonQ_le (isRegFam_gamCand h44 hκ hκ4 hb r) (measurable_gamY0 h44 hκ hκ4 hb r) (gamPast_le r) ℓ t

end Gam

end InteractingSLE.Sec5.CrossCond.StagedRepJ
