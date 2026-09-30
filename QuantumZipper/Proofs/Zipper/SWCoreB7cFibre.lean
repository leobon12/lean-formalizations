import QuantumZipper.Proofs.Zipper.SWCoreB7cFlowSep
import QuantumZipper.Proofs.Zipper.SWCoreB7bWTLem
import QuantumZipper.Proofs.Zipper.SWCoreB7bWTInt
import QuantumZipper.Proofs.Zipper.SWCoreB7Fam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7c (2): the fixed-path fibre over a flow box

Decision D70 (Fubini with independence), fixed-path side. For a **fixed** continuous driver `W`,
an anchor `0 < q ≤ T`, a window live at `q` and a time `s₀ ∈ [q,T]`, the flow box of
`flow_local_class_sep` (a rational class, parameters `(s,w)` in a box `K`, Lipschitz, separated
from `0`) satisfies the hypotheses of the weighted family transport
`ae_transport_family_h0rev`; hence, for every free field `Y`, almost surely, the uniform boundary
transport for `𝔥₀ + Y` holds over the whole box (`flow_fibre`).

* `boxClamp`, `lipschitzWith_boxClamp`: the coordinatewise clamp, a `1`-Lipschitz retraction onto
  a box of `Fin n → ℝ`.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open B2

/-- Coordinatewise clamp onto the box `[lo, hi]`. -/
def boxClamp {n : ℕ} (lo hi : Fin n → ℝ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max (lo i) (min (hi i) (p i))

theorem boxClamp_mem {n : ℕ} {lo hi : Fin n → ℝ} (h : lo ≤ hi) (p : Fin n → ℝ) :
    boxClamp lo hi p ∈ Icc lo hi :=
  ⟨fun i => le_max_left _ _, fun i => max_le (h i) (min_le_left _ _)⟩

theorem boxClamp_of_mem {n : ℕ} {lo hi p : Fin n → ℝ} (hp : p ∈ Icc lo hi) :
    boxClamp lo hi p = p := by
  funext i
  simp only [boxClamp, min_eq_right (hp.2 i), max_eq_right (hp.1 i)]

theorem abs_clampLH_sub_le (l h x y : ℝ) :
    |max l (min h x) - max l (min h y)| ≤ |x - y| := by
  rw [max_comm l, max_comm l]
  refine (abs_max_sub_max_le_abs (min h x) (min h y) l).trans ?_
  refine (abs_min_sub_min_le_max h x h y).trans ?_
  simp

theorem lipschitzWith_boxClamp {n : ℕ} (lo hi : Fin n → ℝ) :
    LipschitzWith 1 (boxClamp lo hi) := by
  refine LipschitzWith.mk_one fun p p' => ?_
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  refine le_trans ?_ (dist_le_pi_dist p p' i)
  simp only [boxClamp, Real.dist_eq]
  exact abs_clampLH_sub_le _ _ _ _

theorem norm_le_of_mem_box {n : ℕ} {lo hi p : Fin n → ℝ} (hp : p ∈ Icc lo hi) :
    ‖p‖ ≤ ‖lo‖ + ‖hi‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  have h1 := norm_le_pi_norm lo i
  have h2 := norm_le_pi_norm hi i
  rw [Real.norm_eq_abs] at h1 h2
  constructor
  · linarith [hp.1 i, neg_abs_le (lo i), norm_nonneg hi]
  · linarith [hp.2 i, le_abs_self (hi i), norm_nonneg lo]

theorem fin2_eta (p : Fin 2 → ℝ) : p = ![p 0, p 1] := by
  funext i; fin_cases i <;> rfl

theorem abs_coord_le_norm (p p' : Fin 2 → ℝ) (i : Fin 2) : |p i - p' i| ≤ ‖p - p'‖ := by
  have := norm_le_pi_norm (p - p') i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at this

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end SWCore
end QuantumZipper
