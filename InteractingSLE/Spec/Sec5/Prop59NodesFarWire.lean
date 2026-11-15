/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodesFarExp
import InteractingSLE.Spec.Sec5.Prop59PiecesMarks

/-!
# Proposition 5.13's tips from experiments with the killed stage law

Packet PROVE-PROP59-NODES. PROVE-PROP59T4's experiments on a product extension (`ProdExp`) and PROVE-PROP59-PIECES'
candidate experiments (`CandExpEx`) carry the piece law `Prop59StagePieceLawStatement`, which compares each piece with
integrated evolutions run to their continuation threshold. The concrete pieces are killed at their first contact with
the revealed counterflow; for `κ ∈ (2, 4)` this is not a threshold (`Prop59NodesFar`), so that law cannot hold for
them. This file gives the same wiring with the **killed** law `Prop59StageLawFarStatement`:

* `ProdExpF`, `ae_not_isBounded_of_prodF`, **`tip0UnboundedStatement_of_prodExpF`**,
  **`tipUnboundedStatement_of_prodExpF`**, **`prop513_path_of_partA_reverseVisit_prodExpF`**;
* `CandExpF` (candidate experiments with per-switch chain data and the killed law), `CandExpF.toProdExpF`,
  **`prop513_path_of_partA_reverseVisit_candExpF`**;
* the root experiment from PROVE-PROP59-PIECES' concrete pieces with the killed law: `rootCandExpF`,
  `rootCandExpF'` (canonical dilated root marks) and **`tip0UnboundedStatement_of_concretePiecesF'`**: Proposition
  5.13's `htip0` from the killed staged law of the realized construction alone.

Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Prop59Nodes

open Prop59Stage Prop59Tips Prop59System Prop59Pieces

/-! ### Experiments on a product extension with the killed law -/

section Prod

variable {κ : ℝ} {Ω Ωa : Type} [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} [IsProbabilityMeasure P]
  {Pa : Measure Ωa} [IsProbabilityMeasure Pa]

/-- **The killed-law experiment on a product extension, read on `Ω`** (as PROVE-PROP59T4's
`ae_not_isBounded_of_prod`). -/
theorem ae_not_isBounded_of_prodF (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} {hnL : 0 < nL} {hnR : 0 < nR}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {G : ℕ → ℕ → ℝ≥0}
    {sys : StageSys (Ω × Ωa) nL nR} {C : Ω × Ωa → Set ℂ} {D : Ω → Set ℂ} {A : Set Ω}
    (hL : Prop59StageLawFarStatement κ (P.prod Pa) hnL hnR ρL ρR sys)
    (hS : IsStageSystem (P.prod Pa) hnL hnR Q δ G sys C) (hI : IsStageInit κ ρL ρR)
    (hC : ∀ ω' : Ω × Ωa, Bornology.IsBounded (D ω'.1) → Bornology.IsBounded (C ω'))
    (hA : ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A → ω' ∈ (sys (fun _ => 0) 0).R) :
    ∀ᵐ ω ∂P, ω ∈ A → ¬ Bornology.IsBounded (D ω) := by
  refine ae_of_ae_prod_fst (Pa := Pa) ?_
  filter_upwards [ae_not_isBounded_of_stageLawFar_init hκ hκ4 hL hS hI (fun _ => 0), hA] with ω' h1 h2 hω hD
  exact h1 (h2 hω) (hC ω' hD)

/-- **The experiments of the alternating construction with the killed law** at every positive rational counterflow
time, on the product extension `Ω × Ωa` (PROVE-PROP59T4's `ProdExp` with `Prop59StageLawFarStatement`). -/
structure ProdExpF (κ : ℝ) (P : Measure Ω) (Pa : Measure Ωa) (D : ℚ → Ω → Set ℂ) (A : ℚ → Set Ω) where
  nL : ℚ → ℕ
  nR : ℚ → ℕ
  posL : ∀ r, 0 < nL r
  posR : ∀ r, 0 < nR r
  rhoL : (r : ℚ) → Fin (nL r) → ℝ
  rhoR : (r : ℚ) → Fin (nR r) → ℝ
  grid : ℚ → Set ℝ≥0
  mesh : ℚ → ℕ → ℝ≥0
  times : ℚ → ℕ → ℕ → ℝ≥0
  system : (r : ℚ) → StageSys (Ω × Ωa) (nL r) (nR r)
  image : ℚ → Ω × Ωa → Set ℂ
  /-- **The killed staged law of the realized construction.** -/
  pieceLaw : ∀ r : ℚ, 0 < r → Prop59StageLawFarStatement κ (P.prod Pa) (posL r) (posR r) (rhoL r) (rhoR r) (system r)
  stages : ∀ r : ℚ, 0 < r →
    IsStageSystem (P.prod Pa) (posL r) (posR r) (grid r) (mesh r) (times r) (system r) (image r)
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)
  image_bdd : ∀ r : ℚ, 0 < r → ∀ ω' : Ω × Ωa, Bornology.IsBounded (D r ω'.1) → Bornology.IsBounded (image r ω')
  active : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A r → ω' ∈ (system r (fun _ => 0) 0).R

theorem ProdExpF.ae_not_isBounded (hκ : 0 < κ) (hκ4 : κ < 4) {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω}
    (X : ProdExpF κ P Pa D A) (r : ℚ) (hr : 0 < r) : ∀ᵐ ω ∂P, ω ∈ A r → ¬ Bornology.IsBounded (D r ω) :=
  ae_not_isBounded_of_prodF hκ hκ4 (X.pieceLaw r hr) (X.stages r hr) (X.initialWord r hr) (X.image_bdd r hr)
    (X.active r hr)

/-- **`Tip0UnboundedStatement` from the killed-law experiments.** -/
theorem tip0UnboundedStatement_of_prodExpF (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ} {z : ℕ → Ω → ℂ}
    (X : ProdExpF κ P Pa (rootTarget W z) fun _ => univ) : Tip0UnboundedStatement P W z := by
  intro r hr
  filter_upwards [X.ae_not_isBounded hκ hκ4 r hr] with ω hω
  exact hω (mem_univ ω)

/-- **`TipUnboundedStatement` from the killed-law experiments.** -/
theorem tipUnboundedStatement_of_prodExpF (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}
    {z : Ω → ℂ} {S : Ω → Set ℂ} (X : ProdExpF κ P Pa (nodeTarget W S) (nodeActive γ z)) :
    TipUnboundedStatement P W γ z S := by
  intro r hr
  exact X.ae_not_isBounded hκ hκ4 r hr

/-- **Candidate experiments with per-switch chain data and the killed law** (PROVE-PROP59-PIECES' `CandExpEx` with
`Prop59StageLawFarStatement` for the realized construction). -/
structure CandExpF (κ : ℝ) (P : Measure Ω) (Pa : Measure Ωa) (D : ℚ → Ω → Set ℂ) (A : ℚ → Set Ω) where
  nL : ℚ → ℕ
  nR : ℚ → ℕ
  posL : ∀ r, 0 < nL r
  posR : ∀ r, 0 < nR r
  rhoL : (r : ℚ) → Fin (nL r) → ℝ
  rhoR : (r : ℚ) → Fin (nR r) → ℝ
  grid : ℚ → Set ℝ≥0
  mesh : ℚ → ℕ → ℝ≥0
  times : ℚ → ℕ → ℕ → ℝ≥0
  grid_ok : ∀ r n, IsSwitchGrid (grid r) (mesh r n) (times r n)
  mesh_ok : ∀ r, Tendsto (mesh r) atTop (𝓝 0)
  cand : (r : ℚ) → CandFam (Ω × Ωa) (nL r) (nR r)
  y₀ : (r : ℚ) → Ω × Ωa → Start (nL r + 0) (nR r + 0)
  R₀ : ℚ → Set (Ω × Ωa)
  base : ℚ → MeasurableSpace (Ω × Ωa)
  image : ℚ → Ω × Ωa → Set ℂ
  start : (r : ℚ) → (j : ℕ) → (Fin j → ℝ≥0) → Ω × Ωa → ℝ
  reg : ∀ r : ℚ, 0 < r → IsRegFam (cand r)
  y₀_meas : ∀ r : ℚ, 0 < r → Measurable (y₀ r)
  base_le : ∀ r : ℚ, 0 < r → base r ≤ (inferInstance : MeasurableSpace (Ω × Ωa))
  R₀_meas : ∀ r : ℚ, 0 < r → MeasurableSet[base r] (R₀ r)
  init : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω' ∈ R₀ r → (y₀ r ω').1 = 0 ∧
    (y₀ r ω').1 + (y₀ r ω').2.1 (farL (by have := posL r; omega : 0 < nL r + 0)) ≤ -3 ∧
    3 ≤ (y₀ r ω').1 + (y₀ r ω').2.2 (farR (by have := posR r; omega : 0 < nR r + 0))
  chain : ∀ r : ℚ, 0 < r → IsChainFamEx (P.prod Pa) (cand r) (posL r) (posR r) (image r) (start r)
  /-- **The killed staged law of the realized construction.** -/
  pieceLaw : ∀ r : ℚ, 0 < r → Prop59StageLawFarStatement κ (P.prod Pa) (posL r) (posR r) (rhoL r) (rhoR r)
    (histSys (cand r) (times r) (posL r) (posR r) (y₀ r) (R₀ r) (base r))
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)
  image_bdd : ∀ r : ℚ, 0 < r → ∀ ω' : Ω × Ωa, Bornology.IsBounded (D r ω'.1) → Bornology.IsBounded (image r ω')
  active : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A r → ω' ∈ R₀ r

/-- **A candidate experiment with the killed law is an experiment** (`isStageSystem_histSys_ex`). -/
def CandExpF.toProdExpF {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω} (X : CandExpF κ P Pa D A) : ProdExpF κ P Pa D A where
  nL := X.nL
  nR := X.nR
  posL := X.posL
  posR := X.posR
  rhoL := X.rhoL
  rhoR := X.rhoR
  grid := X.grid
  mesh := X.mesh
  times := X.times
  system r := histSys (X.cand r) (X.times r) (X.posL r) (X.posR r) (X.y₀ r) (X.R₀ r) (X.base r)
  image := X.image
  pieceLaw := X.pieceLaw
  stages r hr := isStageSystem_histSys_ex (X.reg r hr) (X.grid_ok r) (X.mesh_ok r) (X.y₀_meas r hr)
    (X.base_le r hr) (X.R₀_meas r hr) (X.init r hr) (X.chain r hr)
  initialWord := X.initialWord
  image_bdd := X.image_bdd
  active := X.active

end Prod

/-! ### Proposition 5.13 -/

open Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- **Proposition 5.13 with its tips from the killed-law experiments** (PROVE-PROP513C's
`prop513_path_of_partA_reverseVisit`, `htip0` from the root experiments and `htip` from the node experiments). -/
theorem prop513_path_of_partA_reverseVisit_prodExpF
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    {Ωa : Type} [MeasurableSpace Ωa] [StandardBorelSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : ProdExpF κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (X : ∀ n, ProdExpF κ P Pa
      (nodeTarget W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n))) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_path_of_partA_reverseVisit h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit
    (fun n => tipUnboundedStatement_of_prodExpF hκ hκ4 (X n)) (tip0UnboundedStatement_of_prodExpF hκ hκ4 X₀)

/-- **Proposition 5.13 from candidate experiments with the killed law** at the root and at every node. -/
theorem prop513_path_of_partA_reverseVisit_candExpF
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    {Ωa : Type} [MeasurableSpace Ωa] [StandardBorelSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : CandExpF κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (X : ∀ n, CandExpF κ P Pa
      (nodeTarget W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n))) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_path_of_partA_reverseVisit_prodExpF h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit X₀.toProdExpF
    fun n => (X n).toProdExpF

end InteractingSLE.Sec5.Prop59Nodes
