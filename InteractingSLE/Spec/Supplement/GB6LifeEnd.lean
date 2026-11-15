/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Life
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# Proposition GB6, step (e): the endpoint argument, reduced to the base of the flow hull

Packet PROVE-GB6D. The deterministic half of GB6's step (e) (`GB6EndpointStatement`) is proved here from one classical
Loewner fact about the flow prefix alone:

* **`GB6BaseStatement`** ("every finite incident image of the flow range lies in its filled real base", GB6's proof,
  p. 519: "Outside `[a, b]`, the inverse chart maps the two real rays monotonically onto untouched original-real rays
  disjoint from the flow range"): if `z_n ∈ ℍ \ K_s` tend to a point of `α([0, s])` and `f_s(z_n)` tends to a real `y`,
  then `V̂^{0,L}_s ≤ y ≤ V̂^{0,R}_s` (`baseL`, `baseR`). Stated here; proved in `GB6LifeBase.lean`.

`gb6EndpointStatement_of_base`: if the relative clock is bounded before the first contact `T_c`, let `ζ` be its
supremum. Dense interior times of the chart path give relative times `v_n ↑ ζ` with `Γ(v_n) ∈ ℍ`; by the intermediate
value theorem they are clock values `v_n = a(s_n)`, `s_n → T_c`, and `Γ(v_n) = Ψ(γ(s_n))` (`relTrace_eq`). The physical
points `z_n = −1/γ(s_n)` tend to a point of `α([0, s])`: the first-contact point if `T_c < ∞`
(`firstContactTime_mem`), and `x = α(0) = 0` if `T_c = ∞` (transience of `γ`). If `L = Γ(ζ) ∈ ℍ`, then
`z_n = f_s⁻¹(−1/Γ(v_n)) → f_s⁻¹(−1/L) ∈ ℍ \ K_s`, which contains no point of `α([0, s])` (filling); so `L` is real.
`L ≠ 0` since `f_s(z_n) = −1/Γ(v_n)` stays bounded (uniform displacement). With `y = −1/L` the base statement gives
`L ≥ junctionR` (if `y < 0`) or `L ≤ junctionL` (if `y > 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp8

namespace GB6

/-! ### The first contact is attained -/

/-- **A finite first contact of a continuous path with a closed set is attained.** -/
theorem firstContactTime_mem {X : Type*} [TopologicalSpace X] {η : ℝ≥0 → X} (hη : Continuous η) {A : Set X}
    (hA : IsClosed A) {T : ℝ≥0} (hT : firstContactTime η A = T) : η T ∈ A := by
  set S : Set ℝ≥0 := {t | η t ∈ A} with hSdef
  have hSc : IsClosed S := hA.preimage hη
  have hne : S.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have : firstContactTime η A = ⊤ := by
      unfold firstContactTime
      refine iInf₂_eq_top.2 fun t ht => absurd (show t ∈ S from ht) (by rw [hne]; exact notMem_empty t)
    rw [this] at hT
    exact ENNReal.top_ne_coe hT
  have hinf : firstContactTime η A = ((sInf S : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_sInf hne]
    rfl
  rw [hinf] at hT
  have hTS : sInf S = T := ENNReal.coe_injective hT
  rw [← hTS]
  exact hSc.csInf_mem hne ⟨0, fun _ _ => zero_le⟩

/-! ### The base statement -/

/-- **The base statement: the finite incident images of the flow range lie in the filled base** (GB6's proof, p. 519).
Let
`α` be the generating trace of the flow driver `wα` (continuous before its lifetime, `wα 0 = 0`) and `s` an own time
before the lifetime. If points `z_n ∈ ℍ \ K_s` tend to a point of `α([0, s])` and the centred maps `f_s(z_n)` tend to a
real `y`, then `y` lies in the filled base `[V̂^{0,L}_s, V̂^{0,R}_s]`. Proved in `GB6LifeBase.lean`
(`gb6BaseStatement`): outside the base, the boundary extension of `f_s⁻¹` lands on real points that are not yet
swallowed, and no point of `α([0, s])` is such a point. -/
def GB6BaseStatement : Prop :=
  ∀ (wα : ℝ≥0 → ℝ) (Tα : ℝ≥0∞) (α : ℝ≥0 → ℂ) (s : ℝ≥0),
    IsGeneratingTrace wα Tα α → ContinuousOn wα {t | (t : ℝ≥0∞) < Tα} → wα 0 = 0 → (s : ℝ≥0∞) < Tα →
    ∀ (z : ℕ → ℂ) (zs : ℂ) (y : ℝ), (∀ n, z n ∈ H \ QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) s) →
      Tendsto z atTop (𝓝 zs) → zs ∈ α '' Icc 0 s →
      Tendsto (fun n => QuantumZipper.fwdMap (fun r : ℝ => wα r.toNNReal) s (z n)) atTop (𝓝 (y : ℂ)) →
      baseL (fun r : ℝ => wα r.toNNReal) s ≤ y ∧ y ≤ baseR (fun r : ℝ => wα r.toNNReal) s

end GB6

end Supp8

end InteractingSLE
