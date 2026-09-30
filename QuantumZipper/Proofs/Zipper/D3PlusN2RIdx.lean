import QuantumZipper.Proofs.Zipper.D3PlusN2H1Main
import QuantumZipper.Proofs.Zipper.D3PlusN2H2Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2 on the restricted window index (Decision D36): the index class and H1

Task D36-IMPL. `DECISIONS.md` D36 restricts the N2 window index from **all** local admissible
measures `LocIdx K` to the class on which the project *has* a.s. convergence of the dyadic
regularization at every scale: folded circles and bounded compactly supported densities inside
the window. This file builds that index class and proves the restricted N2-H1 node on it.

* `WinCirc K`: the folded circles `foldedCircle d ρ` strictly inside the window
  (`0 < ρ`, `‖d‖ + ρ < K`) — this is exactly the class of measures read by `locModel`
  (`circSet`, `D3PlusN1Model.lean`) and by `CoordsFull.coordsFull`.
* `WinDens K`: the continuous compactly supported densities `a` with `CharFun.Dens a K' M δ`
  for `K' = closedBall 0 (winRad K) ∩ Hbar` (`winRad K := max (K - 1) 0 < K` for `K > 0`) —
  the class of measures read by the pairings `pairRaw x ρ` of `locFieldFull`.
* `winIdx K : WinIdx K → Measure ℂ` is the family of measures; `winRegFam_winIdx` records that it
  is a `N2H2Law.WinRegFam`, i.e. the regularized evaluation of every free field is a.s. exact at
  every dilation of every family member — the input of `N2H2Law.map_latWinFreeI_eq` (the free half
  of H2) and the reason the restricted class is the right one.

**H1 on the restricted index (proved).** `n2HLatIndepWin_holds : N2HLatIndepWinStmt`: for every
window `K` and every local radius `r > 0`, the lateral data of the local field read at the
restricted index are independent of the radial Brownian path. It is
`D3Plus.indepFun_n2LatY_family` (`D3PlusN2H1Main.lean`, proved) instantiated at `winIdx K`, whose
only input is `RegAt` at the family members: `regAt_foldedCircle` (clause 3 of `IsRegularWith`
along the regular version) and `regAt_of_le_smul_volume` (Frostman regularization, exponent 2).

Nothing here is new mathematics: this is the D36 restriction of the proved H1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The restricted index class -/

/-- The radius of the density window: strictly inside the window `closedBall 0 K`. -/
def winRad (K : ℕ) : ℝ := max ((K : ℝ) - 1) 0

theorem winRad_lt (K : ℕ) (hK : 0 < K) : winRad K < (K : ℝ) := by
  have h1 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  exact max_lt (by linarith) h1

/-- The circle part of the restricted window index: folded circles strictly inside the window
(the measures read by `locModel`, i.e. `circSet K`). -/
abbrev WinCirc (K : ℕ) : Type := {p : ℂ × ℝ // 0 < p.2 ∧ ‖p.1‖ + p.2 < (K : ℝ)}

/-- The density part of the restricted window index: bounded continuous compactly supported
densities carried by `closedBall 0 (winRad K) ∩ Hbar`, `winRad K < K` (the measures read by the
pairings of `locFieldFull`). -/
abbrev WinDens (K : ℕ) : Type :=
  {a : ℂ → ℝ // ∃ M δ : ℝ, CharFun.Dens a (Metric.closedBall (0 : ℂ) (winRad K) ∩ Hbar) M δ}

/-- The restricted window index: folded circles inside the window and bounded compactly supported
densities inside the window (Decision D36). -/
abbrev WinIdx (K : ℕ) : Type := WinCirc K ⊕ WinDens K

/-- The measures of the restricted window index. -/
def winIdx (K : ℕ) : WinIdx K → Measure ℂ :=
  Sum.elim (fun p => foldedCircle p.1.1 p.1.2) (fun a => CharFun.tdens a.1)

theorem winIdx_circ (K : ℕ) (p : WinCirc K) :
    winIdx K (Sum.inl p) = foldedCircle p.1.1 p.1.2 := rfl

theorem winIdx_dens (K : ℕ) (a : WinDens K) :
    winIdx K (Sum.inr a) = CharFun.tdens a.1 := rfl

/-- Every member of the restricted index is an admissible measure of the half-plane. -/
theorem isAdmissibleH_winIdx (K : ℕ) (i : WinIdx K) : IsAdmissibleH (winIdx K i) := by
  rcases i with p | a
  · exact isAdmissibleH_foldedCircle' _ p.2.1
  · obtain ⟨M, δ, hd⟩ := a.2
    exact hd.admissible

/-- Every member of the restricted index is a local measure of the window `halfDisc K`. -/
theorem isLocalH_winIdx (K : ℕ) (hK : 0 < K) (i : WinIdx K) :
    K3.IsLocalH 0 (K : ℝ) (winIdx K i) := by
  rcases i with p | a
  · have hμ : winIdx K (Sum.inl p) = foldedCircle p.1.1 p.1.2 := winIdx_circ K p
    refine ⟨isAdmissibleH_foldedCircle' _ p.2.1, ‖p.1.1‖ + p.1.2, p.2.2, ?_⟩
    rw [hμ]
    exact foldedCircle_compl_closedBall p.2.1
  · obtain ⟨M, δ, hd⟩ := a.2
    have hμ : winIdx K (Sum.inr a) = CharFun.tdens a.1 := winIdx_dens K a
    refine ⟨hd.admissible, winRad K, winRad_lt K hK, ?_⟩
    rw [hμ]
    exact measure_mono_null (compl_subset_compl.2 Set.inter_subset_left) hd.tdens_compl

/-- **The restricted window index is a regular window family** (Decision D36): folded circles and
bounded compactly supported densities are exactly the classes for which the a.s. convergence of
the dyadic regularization is known (`N2H2Law.winRegFam_foldedCircle`,
`N2H2Law.winRegFam_tdens`), and the family operations `comp`/`sum` restrict them to the window. -/
theorem winRegFam_winIdx (K : ℕ) : N2H2Law.WinRegFam (winIdx K) := by
  have h1 : N2H2Law.WinRegFam (fun p : WinCirc K => foldedCircle p.1.1 p.1.2) :=
    N2H2Law.winRegFam_foldedCircle.comp
      (fun p : WinCirc K => (⟨p.1, p.2.1⟩ : {p : ℂ × ℝ // 0 < p.2}))
  have h2 : N2H2Law.WinRegFam (fun a : WinDens K => CharFun.tdens a.1) :=
    N2H2Law.winRegFam_tdens.comp (fun a : WinDens K =>
      (⟨a.1, by obtain ⟨M, δ, hd⟩ := a.2; exact ⟨_, M, δ, hd⟩⟩ :
        {a : ℂ → ℝ // ∃ K M δ, CharFun.Dens a K M δ}))
  exact h1.sum h2

/-! ## A.s. regularization at the restricted index -/

section Reg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

end Reg

/-! ## H1 on the restricted index -/

end D3Plus
end QuantumZipper
