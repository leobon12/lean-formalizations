import HigherDimLQGContinuity.SiteCert.Constants
import HigherDimLQGContinuity.SiteCert.Metric
import HigherDimLQGContinuity.SiteCert.Bump

/-!
# The profile of a label (packet Q7b; Part B `b:def-bump`, `b:lem-bump`, `b:thm-sitecert`(i))

Source: blueprint Part B `b:def-bump` (`ψ_{U,ς} = 1_{U^{+ς/4}} * φ_{ς/4}`, the bump of a label `M_ξ ψ_{U_ℓ,ς}`) and
`b:lem-bump` (packet Q7a's `plateauBump`, `bump_energy`), for the profile clause of `b:thm-sitecert`(i):
`0 ≤ ψ_ℓ ≤ 1`, `tsupport ψ_ℓ ⊆ int C`, `IsCMBounded ψ_ℓ (C_bump ς^{-k_d})`.

* `labelBump U ς hς`: the plateau profile `ψ_{U,ς}` as a continuous map (the label's profile is
  `labelBump U_ℓ ς`, with the plateau `U_ℓ` of the label network).
* `labelBump_spec`: one constant `C_bump` for every plateau with `U^{+ς} ⊆ int C`, `0 < ς ≤ 1`.
* `labelBump_cm_polyB`: with `ς ≥ c v^K`, the Cameron–Martin constant is `≤ polyB (C_bump c^{-k_d}) (K k_d) 0 v⁻¹`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-- **The profile of a plateau** `ψ_{U,ς}` (Part B `b:def-bump`) as a continuous map. -/
def labelBump (U : Set (Rd d)) (ς : ℝ) (hς : 0 < ς) : C(Rd d, ℝ) :=
  ⟨plateauBump U ς hς, (plateauBump_contDiff U ς hς).continuous⟩

@[simp]
theorem labelBump_apply (U : Set (Rd d)) (ς : ℝ) (hς : 0 < ς) (x : Rd d) :
    labelBump U ς hς x = plateauBump U ς hς x := rfl

/-- The collector lies in the radius-four ball. -/
theorem q7b_siteC_subset_closedBall : siteC d ⊆ closedBall (0 : Rd d) 4 := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  linarith [(q7b_norm_of_mem_siteC hx).2]

/-- **The profile clause of `b:thm-sitecert`(i)** (`b:lem-bump` with `M = 1`): one constant `C_bump` such that for
every plateau `U` with `U^{+ς} ⊆ int C` and `0 < ς ≤ 1`, `0 ≤ ψ_{U,ς} ≤ 1`, `tsupport ψ_{U,ς} ⊆ int C` and
`IsCMBounded ψ_{U,ς} (C_bump ς^{-k_d})`, `k_d = 2(⌊d/2⌋ + 1)`. -/
theorem labelBump_spec (hd : 1 ≤ d) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ (U : Set (Rd d)) (ς : ℝ) (hς : 0 < ς), ς ≤ 1 →
      cthickening ς U ⊆ interior (siteC d) →
      (∀ x, 0 ≤ labelBump U ς hς x ∧ labelBump U ς hς x ≤ 1) ∧
      tsupport (labelBump U ς hς) ⊆ interior (siteC d) ∧
      IsCMBounded (labelBump U ς hς) (Cb * ς ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ))) := by
  obtain ⟨Cb, hCb, hbump⟩ := bump_energy (d := d) hd
  refine ⟨Cb, hCb, fun U ς hς hς1 hU => ⟨fun x => ?_, ?_, ?_⟩⟩
  · exact plateauBump_mem_Icc U ς hς x
  · refine (plateauBump_tsupport_subset U ς hς).trans ((cthickening_mono (by linarith) U).trans hU)
  · have hU4 : U ⊆ closedBall 0 4 :=
      (self_subset_cthickening U).trans (hU.trans (interior_subset.trans q7b_siteC_subset_closedBall))
    have h := (hbump U ς 1 hς hς1 zero_le_one hU4).2.2.2.2.2
    have he : (fun x => 1 * plateauBump U ς hς x) = (labelBump U ς hς : Rd d → ℝ) := by
      funext x
      rw [one_mul, labelBump_apply]
    rw [he, mul_one] at h
    exact h

/-- The Cameron–Martin constant of the profile as a polynomial in `v⁻¹` (`b:lem-order`(d): `ς ≥ c v^K`). -/
theorem labelBump_cm_polyB {U : Set (Rd d)} {ς Cb c K v : ℝ} (hς : 0 < ς) (hCb : 0 ≤ Cb) (hc : 0 < c)
    (hK : 0 ≤ K) (hv : 0 < v) (hςv : c * v ^ K ≤ ς)
    (h : IsCMBounded (labelBump U ς hς) (Cb * ς ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ)))) :
    IsCMBounded (labelBump U ς hς)
      (polyB (Cb * c ^ (-(2 * ((d / 2 : ℕ) + 1) : ℝ))) (K * (2 * ((d / 2 : ℕ) + 1) : ℝ)) 0 v⁻¹) :=
  h.mono (q7b_cm_le_polyB hCb hc hK (by positivity) hv hςv)

end HigherDimLQGContinuity
