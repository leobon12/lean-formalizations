/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdfPkg
import InteractingSLE.Spec.Supplement.GW2RootJ31Construction

/-!
# GW2's slow buffer fact in ROOT2's frame

Packet PROVE-GW2-BUF. The comparison family of the SDE half is `comparisonFamilyO K.rootFrame.frame`
(PROVE-GW2-SDE, round 3): its slow dynamics have the driver `(−1)^{|l|} · 2^{r.2} · R(· / 4^{r.2})` (`R` the stage
relative driver of the candidate's instance) and the stop `4^{r.2} · τ` (`τ` the slow stage stop). This file states
JOINTDET's `SlowBufferFact` for that family in terms of these objects and proves the parts that do not depend on the
stage instance:

* **`slowBufferFact_rootFrame`**: `SlowBufferFact` from the three shell clauses, the lifetime domination
  `life ≤ 4^{r.2} · τ` and the affine read `read = start + (−1)^{|l|} 2^{r.2} R(q / 4^{r.2})`;
* **`rootShell`**: the slow shell whose inherited far weights are the root flow-line word at angle `0`; then the
  drift-bound clause is literally J31's (and J32's) `sourceDriftBound` (`sourceDriftBound_eq_rootShell`, `rfl`);
* **`affine_read`**, **`frame_read_of_increment`**: the read of a J31-form sample (`ε a (D(A + u) − D(B))`, any
  reader `D`) is the start plus the comparison driver once the reader's increments after `A` are the stage driver;
* **`ae_ae_condExpKernel_eq_retained`**: a functional of the retained history (`c.sigma r l`-measurable) is frozen
  under the retained kernel (`Sec7.Aux122Disint.ae_ae_condExpKernel_eq`);
* **`ae_slowRead_rootFrame`**: the read clause under the retained kernel from a frozen start and the increment
  identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bf

open GW2JDetR11 GW2Sde GW2Sdf GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 Sec5

/-! ### The slow buffer fact of ROOT2's frame -/

/-- **`SlowBufferFact` for ROOT2's comparison family**: the shell clauses, the sample lifetime below `4^{r.2}` times
the slow stage stop, and the affine read through the stage relative driver. -/
theorem slowBufferFact_rootFrame (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    {μ : Measure Ω} {driftBound : ℝ} {sample : Ω → RootV7.DriverRecord}
    (hφ : ∀ i, ((K Ω c r).slowShell l a ω).φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hy : (((K Ω c r).slowShell l a ω).start, ((K Ω c r).slowShell l a ω).xL,
      ((K Ω c r).slowShell l a ω).xR) ∈ Prop59Stage.startsU)
    (hC : driftBound = Prop59Stage.stageDriftBound c.κ ((K Ω c r).slowShell l a ω).ρL₀
      ((K Ω c r).slowShell l a ω).ρR₀)
    (hlife : ∀ᵐ ξ ∂μ, (sample ξ).1 ≤ (4 : ℝ≥0∞) ^ r.2 * ((K Ω c r).slowStop l a).stop ξ)
    (hread : ∀ᵐ ξ ∂μ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 →
      (sample ξ).2 q = ((K Ω c r).slowShell l a ω).start +
        (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l a).drv c ((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2) ξ)) :
    SlowBufferFact ((comparisonFamilyO K.rootFrame.frame Ω c r).slow l a ω) μ driftBound sample := by
  refine ⟨hφ, hy, hC, ?_, ?_⟩
  · filter_upwards [hlife] with ξ hξ
    rw [rootFrame_slow_stop]
    exact hξ
  · filter_upwards [hread] with ξ hξ q hq
    rw [rootFrame_slow_W]
    exact hξ q hq

/-! ### The slow shell with the root's inherited far weights -/

section Shell

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The slow shell of ROOT2's frame**: angle-change data `mL, mR, φ`, marks `xL, xR`, start, and as inherited far
weights the root flow-line word at angle `0` (both sides, seeds included). -/
def rootShell (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (mL mR : ℕ) (φ : ℕ → ℝ)
    (xL : Fin (mL + flowLineNL c.b c.jumps (rootPt r.1)) → ℝ)
    (xR : Fin (mR + flowLineNR c.b c.jumps (rootPt r.1) + 1) → ℝ) (start : ℝ) : SlowShell where
  nL₀ := flowLineNL c.b c.jumps (rootPt r.1)
  nR₀ := flowLineNR c.b c.jumps (rootPt r.1)
  ρL₀ := flowLineRhoL c.κ c.b c.jumps (rootPt r.1) 0
  ρR₀ := flowLineRhoR c.κ c.b c.jumps (rootPt r.1) 0
  mL := mL
  mR := mR
  φ := φ
  xL := xL
  xR := xR
  start := start

/-- **The drift-bound clause for the root shell** is J31's (and J32's) drift bound, literally. -/
theorem sourceDriftBound_eq_rootShell (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (mL mR : ℕ) (φ : ℕ → ℝ)
    (xL : Fin (mL + flowLineNL c.b c.jumps (rootPt r.1)) → ℝ)
    (xR : Fin (mR + flowLineNR c.b c.jumps (rootPt r.1) + 1) → ℝ) (start : ℝ) :
    RootJ31.sourceDriftBound c r = Prop59Stage.stageDriftBound c.κ (rootShell c r mL mR φ xL xR start).ρL₀
      (rootShell c r mL mR φ xL xR start).ρR₀ := rfl

end Shell

/-! ### The affine read -/

/-- **The affine read**: an absolute read `ε a (D(A + u) − D(B))` is the start `ε a (D(A) − D(B))` plus the dilated
and oriented increment, once `D(A + u) − D(A) = R(u)`. -/
theorem affine_read {ε a : ℝ} {D R : ℝ≥0 → ℝ} {A B u : ℝ≥0} (h : D (A + u) - D A = R u) :
    ε * a * (D (A + u) - D B) = ε * a * (D A - D B) + ε * (a * R u) := by
  rw [← h]
  ring

/-- `(2^k)² = 4^k` in `ℝ≥0`: J31's `u / a²` at `a = 2^k` is the frame's `u / 4^k`. -/
theorem two_pow_sq (k : ℕ) : ((2 : ℝ≥0) ^ k) ^ 2 = (4 : ℝ≥0) ^ k := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

/-- **The read of a J31-form sample in ROOT2's frame**: with `a = 2^k`, `ε = (−1)^n`, the absolute read at the
rational time `q` is the start plus `(−1)^n 2^k R(q / 4^k)`, given the increment identity at `u = q / 4^k`. -/
theorem frame_read_of_increment (n k : ℕ) {D R : ℝ≥0 → ℝ} {A B : ℝ≥0} (q : ℝ≥0)
    (h : D (A + q / (4 : ℝ≥0) ^ k) - D A = R (q / (4 : ℝ≥0) ^ k)) :
    (-1 : ℝ) ^ n * (((2 : ℝ≥0) ^ k : ℝ≥0) : ℝ) * (D (A + q / ((2 : ℝ≥0) ^ k) ^ 2) - D B) =
      (-1 : ℝ) ^ n * (((2 : ℝ≥0) ^ k : ℝ≥0) : ℝ) * (D A - D B) +
        (-1 : ℝ) ^ n * ((2 : ℝ) ^ k * R (q / (4 : ℝ≥0) ^ k)) := by
  rw [two_pow_sq, affine_read h]
  push_cast
  ring

/-! ### Retained functionals are frozen under the retained kernel -/

/-- **A functional of the retained history is frozen under the retained kernel.** -/
theorem ae_ae_condExpKernel_eq_retained {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) {S : Ω → ℝ}
    (hS : Measurable[c.sigma r l] S) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω₀), S ξ = S ω₀ :=
  Sec7.Aux122Disint.ae_ae_condExpKernel_eq (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _) hS

/-- **The slow read clause under the retained kernel** for a J31-form sample: if the sample reads
`(−1)^{|l|} 2^{r.2} (D(A + q/4^{r.2}) − D(B))` on its lifetime, the reader's increments after `A` are the stage
driver, and the start functional `(−1)^{|l|} 2^{r.2} (D(A) − D(B))` is the constant `start` kernel-a.s., then the
read clause of `slowBufferFact_rootFrame` holds. -/
theorem ae_slowRead_rootFrame {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} (n k : ℕ)
    {sample : Ω → RootV7.DriverRecord} {D : Ω → ℝ≥0 → ℝ} {A B : Ω → ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {start : ℝ}
    (hform : ∀ ξ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 →
      (sample ξ).2 q = (-1 : ℝ) ^ n * (((2 : ℝ≥0) ^ k : ℝ≥0) : ℝ) *
        (D ξ (A ξ + (q : ℝ≥0) / ((2 : ℝ≥0) ^ k) ^ 2) - D ξ (B ξ)))
    (hinc : ∀ᵐ ξ ∂μ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 →
      D ξ (A ξ + (q : ℝ≥0) / (4 : ℝ≥0) ^ k) - D ξ (A ξ) = R ((q : ℝ≥0) / (4 : ℝ≥0) ^ k) ξ)
    (hstart : ∀ᵐ ξ ∂μ, (-1 : ℝ) ^ n * (((2 : ℝ≥0) ^ k : ℝ≥0) : ℝ) * (D ξ (A ξ) - D ξ (B ξ)) = start) :
    ∀ᵐ ξ ∂μ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 →
      (sample ξ).2 q = start + (-1 : ℝ) ^ n * ((2 : ℝ) ^ k * R ((q : ℝ≥0) / (4 : ℝ≥0) ^ k) ξ) := by
  filter_upwards [hinc, hstart] with ξ hξ hs q hq
  rw [hform ξ q hq, frame_read_of_increment n k (R := fun u => R u ξ) (q : ℝ≥0) (hξ q hq), hs]

end InteractingSLE.Theorem14.GW2Bf
