/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59SystemStage
import InteractingSLE.Spec.Sec5.Prop59SystemWire

/-!
# Proposition 5.9's experiments from candidate families

Packet PROVE-PROP59T4. Specification §5.2, proof of Proposition 5.9 (pp. 145–146): "For each integer `m ≥ 1`, fix a
locally finite increasing grid `Q_m ⊆ Q` which is unbounded and has successive gaps at most `2^{1−m}`, and whose first
point is at most `2^{1−m}`"; "Although the selected indices depend on the revealed history, the set of all possible
finite lists is countable."

* `ratTimes`, `ratMesh`, `ratGrid`: switching grids in the positive rationals (the switching times of PROVE-PROP513C's
  schedules, `isSchedule_scheduleList`), with `isSwitchGrid_ratGrid` and `tendsto_ratMesh`;
* `CandExp`: the experiments at all positive rational counterflow times built from candidate families — the
  candidates on the product extension, their regularity (`IsRegFam`) and chain data (`IsChainFam`), the initial start,
  reached event and past, the initial dilation, the piece laws of the resulting stage systems `histSys`, the initial
  words, the images and the initial events;
* **`CandExp.toProdExp`**: the stage systems `histSys` of a `CandExp` satisfy `IsStageSystem`
  (`isStageSystem_histSys`), so a `CandExp` is a `ProdExp`;
* **`prop513_path_of_partA_reverseVisit_candExp`**: Proposition 5.13's measurable path version from candidate families
  at the root and at every node.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59System

open QuantumZipper Prop59Stage Prop59Tips

/-! ### Rational switching grids -/

/-- The positive rational times (as nonnegative reals). -/
def ratTimes : Set ℝ≥0 := {t | ∃ q : ℚ, 0 < q ∧ t = (q : ℝ).toNNReal}

/-- The mesh `1/(n + 1)`. -/
def ratMesh (n : ℕ) : ℝ≥0 := ((1 : ℝ) / ((n : ℝ) + 1)).toNNReal

/-- The grid `k ↦ (k + 1)/(n + 1)` of mesh `1/(n + 1)` in the positive rationals. -/
def ratGrid (n k : ℕ) : ℝ≥0 := ((((k : ℚ) + 1) / ((n : ℚ) + 1) : ℚ) : ℝ).toNNReal

theorem ratGrid_eq (n k : ℕ) : ratGrid n k = (((k : ℝ) + 1) / ((n : ℝ) + 1)).toNNReal := by
  simp only [ratGrid, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

theorem isSwitchGrid_ratGrid (n : ℕ) : IsSwitchGrid ratTimes (ratMesh n) (ratGrid n) where
  mem k := ⟨_, by positivity, rfl⟩
  strictMono := by
    intro k k' hk
    rw [ratGrid_eq, ratGrid_eq, Real.toNNReal_lt_toNNReal_iff (by positivity)]
    have : (k : ℝ) < k' := by exact_mod_cast hk
    exact div_lt_div_of_pos_right (by linarith) (by positivity)
  zero_le := by
    rw [ratGrid_eq, ratMesh, Nat.cast_zero, zero_add]
  succ_le k := by
    rw [ratGrid_eq, ratGrid_eq, ratMesh, ← Real.toNNReal_add (by positivity) (by positivity)]
    refine Real.toNNReal_le_toNNReal (le_of_eq ?_)
    push_cast
    ring
  tendsto := by
    refine tendsto_real_toNNReal_atTop.comp ?_
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 := h1.atTop_div_const (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
    refine h2.congr fun k => ?_
    simp only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

theorem tendsto_ratMesh : Tendsto ratMesh atTop (𝓝 0) := by
  have h := (continuous_real_toNNReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  simp only [Real.toNNReal_zero] at h
  exact h

/-! ### Experiments from candidate families -/

section Exp

variable {κ : ℝ} {Ω Ωa : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  [StandardBorelSpace Ωa] {P : Measure Ω} [IsProbabilityMeasure P] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]

/-- **The experiments of the alternating construction from candidate families** at every positive rational
counterflow time, on the product extension `Ω × Ωa`, for target sets `D r` and initial events `A r`. -/
structure CandExp (κ : ℝ) (P : Measure Ω) (Pa : Measure Ωa) (D : ℚ → Ω → Set ℂ) (A : ℚ → Set Ω) where
  nL : ℚ → ℕ
  nR : ℚ → ℕ
  posL : ∀ r, 0 < nL r
  posR : ∀ r, 0 < nR r
  rhoL : (r : ℚ) → Fin (nL r) → ℝ
  rhoR : (r : ℚ) → Fin (nR r) → ℝ
  /-- The allowed original switching times. -/
  grid : ℚ → Set ℝ≥0
  /-- The meshes. -/
  mesh : ℚ → ℕ → ℝ≥0
  /-- The grids. -/
  times : ℚ → ℕ → ℕ → ℝ≥0
  grid_ok : ∀ r n, IsSwitchGrid (grid r) (mesh r n) (times r n)
  mesh_ok : ∀ r, Tendsto (mesh r) atTop (𝓝 0)
  /-- The candidate pieces. -/
  cand : (r : ℚ) → CandFam (Ω × Ωa) (nL r) (nR r)
  /-- The initial start (in the dilated joint chart). -/
  y₀ : (r : ℚ) → Ω × Ωa → Start (nL r + 0) (nR r + 0)
  /-- The initial reached event. -/
  R₀ : ℚ → Set (Ω × Ωa)
  /-- The initial revealed history. -/
  base : ℚ → MeasurableSpace (Ω × Ωa)
  /-- The node images in the dilated joint chart. -/
  image : ℚ → Ω × Ωa → Set ℂ
  start : (r : ℚ) → (j : ℕ) → (Fin j → ℝ≥0) → Ω × Ωa → ℝ
  drv : (r : ℚ) → (j : ℕ) → (Fin j → ℝ≥0) → Ω × Ωa → ℝ → ℝ
  trc : (r : ℚ) → (j : ℕ) → (Fin j → ℝ≥0) → Ω × Ωa → ℝ → ℂ
  life : (r : ℚ) → (j : ℕ) → (Fin j → ℝ≥0) → Ω × Ωa → ℝ
  reg : ∀ r : ℚ, 0 < r → IsRegFam (cand r)
  y₀_meas : ∀ r : ℚ, 0 < r → Measurable (y₀ r)
  base_le : ∀ r : ℚ, 0 < r → base r ≤ (inferInstance : MeasurableSpace (Ω × Ωa))
  R₀_meas : ∀ r : ℚ, 0 < r → MeasurableSet[base r] (R₀ r)
  init : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω' ∈ R₀ r → (y₀ r ω').1 = 0 ∧
    (y₀ r ω').1 + (y₀ r ω').2.1 (farL (by have := posL r; omega : 0 < nL r + 0)) ≤ -3 ∧
    3 ≤ (y₀ r ω').1 + (y₀ r ω').2.2 (farR (by have := posR r; omega : 0 < nR r + 0))
  chain : ∀ r : ℚ, 0 < r →
    IsChainFam (P.prod Pa) (cand r) (posL r) (posR r) (image r) (start r) (drv r) (trc r) (life r)
  /-- **The piece laws of the realized construction** (the staged cross-conditioning law, PROVE-CROSSCOND-STAGED*). -/
  pieceLaw : ∀ r : ℚ, 0 < r → Prop59StagePieceLawStatement κ (P.prod Pa) (rhoL r) (rhoR r)
    (histSys (cand r) (times r) (posL r) (posR r) (y₀ r) (R₀ r) (base r))
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)
  image_bdd : ∀ r : ℚ, 0 < r → ∀ ω' : Ω × Ωa, Bornology.IsBounded (D r ω'.1) → Bornology.IsBounded (image r ω')
  active : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A r → ω' ∈ R₀ r

/-- **A candidate experiment is an experiment**: its stage systems `histSys` satisfy `IsStageSystem`. -/
def CandExp.toProdExp {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω} (X : CandExp κ P Pa D A) : ProdExp κ P Pa D A where
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
  stages r hr := isStageSystem_histSys (X.reg r hr) (X.grid_ok r) (X.mesh_ok r) (X.y₀_meas r hr) (X.base_le r hr)
    (X.R₀_meas r hr) (X.init r hr) (X.chain r hr)
  initialWord := X.initialWord
  image_bdd := X.image_bdd
  active := X.active

end Exp

/-! ### Proposition 5.13 -/

open Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- **Proposition 5.13 from candidate families of the alternating construction** at the root and at every node. -/
theorem prop513_path_of_partA_reverseVisit_candExp
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
    (X₀ : CandExp κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (X : ∀ n, CandExp κ P Pa
      (nodeTarget W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n))) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_path_of_partA_reverseVisit_prodExp h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit X₀.toProdExp
    fun n => (X n).toProdExp

end InteractingSLE.Sec5.Prop59System
