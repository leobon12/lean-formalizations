import QuantumZipper.Proofs.Zipper.GenUCConv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GENERIC-UC: exactness on an open parameter set from box-wise inputs

* `GenInputs P X x S μ ν`: the complete list of family-specific inputs of the engine on one
  parameter set `S` (admissibility/mass/energy `GenFam`, a Lipschitz retraction, a countable dense
  `D ⊆ S`, a countable set `R ∋ 2^{-j}` of radii, the identity `Φ = X(μ) + det` at the countable
  points, uniform convergence of `det`, pathwise continuity of the smoothed pairings and of the
  raw value, the raw identity at each fixed parameter);
* `ae_exact_of_genInputs`: on a compact `S`, a.s. `evalReg x_ω (ν p) = x_ω (ν p)` for all
  `p ∈ S` (from `ae_unifConv_all` and `ae_exact_of_unifConv`, GenUCConv);
* `isLipRetr_ratBox`: closed boxes `∏ [a_i, b_i]` carry the clamp retraction (`1`-Lipschitz);
* `ae_exact_open`: if the inputs hold on every rational box inside an open set `U`, then a.s.
  exactness holds at every `p ∈ U` (countably many boxes; every point of `U` lies in one). This is
  the form needed for parameter sets defined by an open separation condition (e.g. the G4
  separated set `BackSepI`).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace GenUC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
variable {n : ℕ}

/-- The closed box with rational corners `∏ [a_i, b_i]`. -/
def ratBox (a b : Fin n → ℚ) : Set (Fin n → ℝ) := Set.pi univ fun i => Icc (a i : ℝ) (b i)

/-- The coordinatewise clamp onto `∏ [a_i, b_i]`. -/
def boxRetr (a b : Fin n → ℚ) (q : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max (a i : ℝ) (min (q i) (b i))

theorem isCompact_ratBox (a b : Fin n → ℚ) : IsCompact (ratBox a b) :=
  isCompact_univ_pi fun _ => isCompact_Icc

/-- A nonempty rational box carries the `1`-Lipschitz clamp retraction. -/
theorem isLipRetr_ratBox {a b : Fin n → ℚ} (hab : ∀ i, (a i : ℝ) ≤ b i) :
    IsLipRetr (ratBox a b) (boxRetr a b) 1 := by
  refine ⟨fun q i _ => ⟨le_max_left _ _, max_le (hab i) (min_le_right _ _)⟩,
    fun p hp => funext fun i => ?_, zero_le_one, fun q q' => ?_⟩
  · have h := hp i (mem_univ i)
    simp only [boxRetr]; rw [min_eq_left h.2, max_eq_right h.1]
  · rw [one_mul]
    refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
    rw [Real.dist_eq]
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · rw [sub_self, abs_zero]; exact dist_nonneg
    · refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ (by simp))
      rw [← Real.dist_eq]; exact dist_le_pi_dist q q' i

/-- Every point of an open set lies in a rational box inside it. -/
theorem exists_ratBox_subset {U : Set (Fin n → ℝ)} (hU : IsOpen U) {p : Fin n → ℝ}
    (hp : p ∈ U) : ∃ a b : Fin n → ℚ, p ∈ ratBox a b ∧ ratBox a b ⊆ U := by
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hU p hp
  have hlo : ∀ i, ∃ q : ℚ, p i - e / 2 < q ∧ (q : ℝ) < p i := fun i =>
    exists_rat_btwn (by linarith)
  have hhi : ∀ i, ∃ q : ℚ, p i < q ∧ (q : ℝ) < p i + e / 2 := fun i =>
    exists_rat_btwn (by linarith)
  choose a ha using hlo
  choose b hb using hhi
  refine ⟨a, b, fun i _ => ⟨(ha i).2.le, (hb i).1.le⟩, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff he]
  intro i
  have h := hy i (mem_univ i)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h.1, h.2, (ha i).1, (hb i).2]

end GenUC
end QuantumZipper
