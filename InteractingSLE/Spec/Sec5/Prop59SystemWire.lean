/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59SystemInit
import InteractingSLE.Spec.Sec5.Prop513WireAssembly

/-!
# Proposition 5.9's tips from stage systems on an extension, and Proposition 5.13

Packet PROVE-PROP59T4. Specification §5.2, proof of Proposition 5.9 (pp. 143–148) and proof of Proposition 5.13
(p. 150). The alternating construction may need randomness beyond the original sample space: a stage piece is the
constant-angle continuation **through its continuation threshold** (PROVE-PROP59T3 §5.2, obstruction 1), which after
its first new boundary contact is no longer a physical curve of the original construction. The experiment is
therefore run on a product extension `Ω × Ωa` with law `P ⊗ Pa`; its conclusion transfers back to `Ω` because the
product measure of `N × Ωa` is `P(N)` for every set `N` (`Measure.prod_prod`, no measurability needed). The joint chart
may also be dilated by a random factor ("Rescale it so that the marked points `z₋, z₊` … satisfy `z₋ ≤ −3` and
`z₊ ≥ 3`", p. 143): only "bounded node set ⇒ bounded image" is used (`isBounded_image_mul`).

## Main results

* **`ae_not_isBounded_of_prod`**: the experiment of PROVE-PROP59T3 (`ae_not_isBounded_of_pieceLaw`) on `Ω × Ωa`,
  read on `Ω`;
* `ProdExp`: the data of the experiments at all positive rational counterflow times (piece laws, stage systems,
  initial words, images, initial events), with `ProdExp.ae_not_isBounded`;
* **`tip0UnboundedStatement_of_prodExp`**, **`tipUnboundedStatement_of_prodExp`**: PROVE-PROP59T's tip statements;
* **`prop513_path_of_partA_reverseVisit_prodExp`**: Proposition 5.13's measurable path version (PROVE-PROP513C's
  assembly) with its two tip inputs supplied by these experiments.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59System

open QuantumZipper Prop59Stage Prop59Tips

/-- A bounded set stays bounded under multiplication by a complex constant (the dilation of the joint chart). -/
theorem isBounded_image_mul (c : ℂ) {D : Set ℂ} (h : Bornology.IsBounded D) :
    Bornology.IsBounded ((fun z => c * z) '' D) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 h
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨‖c‖ * R, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hR hz
  simp only [Metric.mem_closedBall, dist_zero_right, norm_mul]
  exact mul_le_mul_of_nonneg_left hz' (norm_nonneg c)

section Prod

variable {κ : ℝ} {Ω Ωa : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  [StandardBorelSpace Ωa] {P : Measure Ω} [IsProbabilityMeasure P] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]

omit [StandardBorelSpace Ω] [StandardBorelSpace Ωa] [IsProbabilityMeasure P] in
/-- **An almost-sure statement for the first coordinate of a product is an almost-sure statement on `Ω`** (for every
predicate: `P ⊗ Pa (N × Ωa) = P(N)` for every set `N`). -/
theorem ae_of_ae_prod_fst {p : Ω → Prop} (h : ∀ᵐ ω' ∂(P.prod Pa), p ω'.1) : ∀ᵐ ω ∂P, p ω := by
  rw [ae_iff] at h ⊢
  have e : {ω' : Ω × Ωa | ¬ p ω'.1} = {ω | ¬ p ω} ×ˢ (univ : Set Ωa) := by
    ext ω'
    simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true]
  rw [e, Measure.prod_prod, measure_univ, mul_one] at h
  exact h

/-- **The alternating construction on a product extension, read on `Ω`**: if the experiment on `Ω × Ωa` has the
delivered piece laws, the structure of a stage system and an initial word with `IsStageInit`, if its images are bounded
whenever the target sets `D` are, and if it is started almost surely on `A`, then almost surely on `A` the set `D` is
unbounded. -/
theorem ae_not_isBounded_of_prod (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} {hnL : 0 < nL} {hnR : 0 < nR}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0} {G : ℕ → ℕ → ℝ≥0}
    {sys : StageSys (Ω × Ωa) nL nR} {C : Ω × Ωa → Set ℂ} {D : Ω → Set ℂ} {A : Set Ω}
    (hL : Prop59StagePieceLawStatement κ (P.prod Pa) ρL ρR sys)
    (hS : IsStageSystem (P.prod Pa) hnL hnR Q δ G sys C) (hI : IsStageInit κ ρL ρR)
    (hC : ∀ ω' : Ω × Ωa, Bornology.IsBounded (D ω'.1) → Bornology.IsBounded (C ω'))
    (hA : ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A → ω' ∈ (sys (fun _ => 0) 0).R) :
    ∀ᵐ ω ∂P, ω ∈ A → ¬ Bornology.IsBounded (D ω) := by
  refine ae_of_ae_prod_fst (Pa := Pa) ?_
  filter_upwards [ae_not_isBounded_of_pieceLaw hκ hκ4 hL hS hI (fun _ => 0), hA] with ω' h1 h2 hω hD
  exact h1 (h2 hω) (hC ω' hD)

/-- **The experiments of the alternating construction at every positive rational counterflow time**, on the product
extension `Ω × Ωa`, for target sets `D r` and initial events `A r`: the piece laws, the stage systems, the initial
words, the images (bounded when the target sets are) and the initial events. -/
structure ProdExp (κ : ℝ) (P : Measure Ω) (Pa : Measure Ωa) (D : ℚ → Ω → Set ℂ) (A : ℚ → Set Ω) where
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
  pieceLaw : ∀ r : ℚ, 0 < r → Prop59StagePieceLawStatement κ (P.prod Pa) (rhoL r) (rhoR r) (system r)
  stages : ∀ r : ℚ, 0 < r →
    IsStageSystem (P.prod Pa) (posL r) (posR r) (grid r) (mesh r) (times r) (system r) (image r)
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)
  image_bdd : ∀ r : ℚ, 0 < r → ∀ ω' : Ω × Ωa, Bornology.IsBounded (D r ω'.1) → Bornology.IsBounded (image r ω')
  active : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A r → ω' ∈ (system r (fun _ => 0) 0).R

theorem ProdExp.ae_not_isBounded (hκ : 0 < κ) (hκ4 : κ < 4) {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω}
    (X : ProdExp κ P Pa D A) (r : ℚ) (hr : 0 < r) : ∀ᵐ ω ∂P, ω ∈ A r → ¬ Bornology.IsBounded (D r ω) :=
  ae_not_isBounded_of_prod hκ hκ4 (X.pieceLaw r hr) (X.stages r hr) (X.initialWord r hr) (X.image_bdd r hr)
    (X.active r hr)

/-- The root targets: the node points off the counterflow hull at time `r`, in the own-component chart. -/
def rootTarget (W : ℝ≥0 → Ω → ℝ) (z : ℕ → Ω → ℂ) (r : ℚ) (ω : Ω) : Set ℂ :=
  (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
    (range (fun n => z n ω) ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal))

/-- The descendant targets of a root `z`. -/
def nodeTarget (W : ℝ≥0 → Ω → ℝ) (S : Ω → Set ℂ) (r : ℚ) (ω : Ω) : Set ℂ :=
  (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
    (S ω ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal))

/-- The event that the root `z` is visited after the counterflow time `r`. -/
def nodeActive (γ : Ω → ℝ≥0 → ℂ) (z : Ω → ℂ) (r : ℚ) : Set Ω := {ω | (r : ℝ) < traceFirstVisit (γ ω) (z ω)}

/-- **`Tip0UnboundedStatement` from the experiments on a product extension.** -/
theorem tip0UnboundedStatement_of_prodExp (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ} {z : ℕ → Ω → ℂ}
    (X : ProdExp κ P Pa (rootTarget W z) fun _ => univ) : Tip0UnboundedStatement P W z := by
  intro r hr
  filter_upwards [X.ae_not_isBounded hκ hκ4 r hr] with ω hω
  exact hω (mem_univ ω)

/-- **`TipUnboundedStatement` from the experiments on a product extension.** -/
theorem tipUnboundedStatement_of_prodExp (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}
    {z : Ω → ℂ} {S : Ω → Set ℂ} (X : ProdExp κ P Pa (nodeTarget W S) (nodeActive γ z)) :
    TipUnboundedStatement P W γ z S := by
  intro r hr
  exact X.ae_not_isBounded hκ hκ4 r hr

end Prod

/-! ### Proposition 5.13 -/

open Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- **Proposition 5.13 with its tips from the alternating construction on a product extension**: PROVE-PROP513C's
`prop513_path_of_partA_reverseVisit` with `htip0` from the root experiments and `htip` from the node experiments. -/
theorem prop513_path_of_partA_reverseVisit_prodExp
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
    (X₀ : ProdExp κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (X : ∀ n, ProdExp κ P Pa
      (nodeTarget W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n))) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_path_of_partA_reverseVisit h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit
    (fun n => tipUnboundedStatement_of_prodExp hκ hκ4 (X n)) (tip0UnboundedStatement_of_prodExp hκ hκ4 X₀)

end InteractingSLE.Sec5.Prop59System
