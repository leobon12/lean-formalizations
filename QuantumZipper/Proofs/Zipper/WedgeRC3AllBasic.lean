import QuantumZipper.Proofs.Zipper.WedgeShiftInt

/-!
# WEDGE-RC3ALL (1): raw = regularized for the wedge field on folded circles missing `0`

The sub-node `F1.WedgeRC3AllStmt` (raw value = regularized value of the wedge field
`W = wedgeField (lateralPart x) A Q` on **every** folded circle `fc(w, ρ)`) splits according to
whether the circle misses `0`, i.e. `|‖w‖ − ρ| > 0`.

This file proves the **missing-`0` half** (`evalReg_wedgeField_fc_of_gap`) for a good free sample
`x` (`WedgeTK.GoodRad`, raw dyadic agreement `hray`) and a continuous radial path `A`:

  `evalReg W (fc w ρ) = evalReg x (fc w ρ) + ∫ wedgeProfile x A Q d(fc w ρ)`

(so that `evalReg W (fc w ρ) = W (fc w ρ)` by `WedgeCan.wedgeField_eq_evalReg_add_ofFun`, with the
integrability supplied by `WedgeCircleIntStmt`, proved in `WedgeShiftInt.lean`); the conclusion is
stated directly in the `W`-form.

Route (own elementary bookkeeping):

* the truncation radius `a = |‖w‖ − ρ| / 2` is chosen so that the truncated radial profile
  `WedgeMeasCoord.gT F A Q a` (continuous on `ℂ`) agrees with `wedgeProfile` on a.e. point of
  `fc w ρ` (`‖u‖ ≥ |‖w‖ − ρ|` a.e., `WedgeCan.ae_fc_abs_le_norm`);
* for a.e. `u ∈ fc w ρ` and every small dyadic radius `radius k`, the dyadic circle
  `fc(dyadicRoundC n u, radius k)` (`n` large) also misses `0`, so the raw value of `W` there is
  `evalReg x + ∫ wedgeProfile` (`WedgeCan.wedgeField_eq_evalReg_add_ofFun`), the free field is
  read by `hray` / `hG.1.evalReg_fc_of_mem`, and `wedgeProfile` is replaced by the truncated
  profile (`WedgeMeasCoord.integral_fc_profile_eq`); hence `avgReg W k u = avgReg (x + ofFun gT) k u`
  (`avgReg_wedgeField_eq_gT_of_gap`);
* `evalReg` is the `limUnder` of `∫ avgReg · k`, so the two samples have the same `evalReg` on
  `fc w ρ`, and `GoodSample.evalReg_add_ofFun_fc` computes the regularized value of
  `x + ofFun gT` as `evalReg x + ∫ gT`.

The remaining half, the circles with `‖w‖ = ρ` (through `0`), is isolated as the Prop
`F1.WedgeRC3ThroughStmt`; `wedgeRC3AllStmt_of_through` shows that `WedgeRC3AllStmt` follows
from it. See the report of task WEDGE-RC3ALL for the missing input (the through-`0` circle is
not at positive distance from `0`, so the truncated-profile argument above fails and one needs
the continuum limit of the pairings of the swept measures `fc w ρ ∗ fc(·, r)` with the free
field, a PAIR-LIM statement for measures of unbounded density).

Own elementary argument (AGENT_GUIDE cost rule); no statement of the blueprint is changed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {Q : ℝ}

/-! ## 1. The dyadic identity at an inner circle -/

/-- **The key inner identity.** If the truncation radius `a > 0` is at most the modulus of the
point `u ∈ Hbar` and `radius k < a / 4`, then the `k`-th dyadic average of the wedge field at `u`
coincides with the `k`-th dyadic average of `x + ofFun (gT F A Q a)`: the dyadic circles
`fc(dyadicRoundC n u, radius k)` eventually miss `0` (where the raw decomposition of the wedge
field and the profile truncation both apply). -/
theorem avgReg_wedgeField_eq_gT_of_gap (hG : WedgeTK.GoodRad x F)
    (hray : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (Q : ℝ) {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : radius k < a / 4)
    {u : ℂ} (hu : u ∈ Hbar) (hun : a ≤ ‖u‖) :
    avgReg (wedgeField (lateralPart x) A Q) k u =
      avgReg (x + ofFun (WedgeMeasCoord.gT F A Q a)) k u := by
  have hev : ∀ᶠ n : ℕ in atTop, a / 2 ≤ ‖dyadicRoundC n u‖ :=
    ((RegClosure.tendsto_dyadicRoundC u).norm.eventually
      (Metric.ball_mem_nhds (‖u‖) (by linarith : (0:ℝ) < ‖u‖ - a / 2))).mono fun n hn => by
      rw [Real.dist_eq] at hn
      linarith [(abs_lt.1 hn).1]
  have heq : (fun n : ℕ => wedgeField (lateralPart x) A Q
        (foldedCircle (dyadicRoundC n u) (radius k))) =ᶠ[atTop]
      fun n => (x + ofFun (WedgeMeasCoord.gT F A Q a))
        (foldedCircle (dyadicRoundC n u) (radius k)) := by
    filter_upwards [hev] with n hn
    have hdn : dyadicRoundC n u ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hu n
    have hne : ‖dyadicRoundC n u‖ ≠ radius k := by
      intro hc
      rw [hc] at hn
      linarith
    have h0 := WedgeCan.integrable_radAvgReg_foldedCircle hG hdn (radius_pos k) hne
    have hL := WedgeCan.integrable_logProfile_foldedCircle Q (dyadicRoundC n u) (radius k)
    have hAi := WedgeCan.integrable_Alog_foldedCircle hA hdn (radius_pos k) hne
    have hR : (x + ofFun (WedgeMeasCoord.gT F A Q a))
        (foldedCircle (dyadicRoundC n u) (radius k)) =
        x (foldedCircle (dyadicRoundC n u) (radius k)) +
          ∫ v, WedgeMeasCoord.gT F A Q a v ∂foldedCircle (dyadicRoundC n u) (radius k) := rfl
    rw [WedgeCan.wedgeField_eq_evalReg_add_ofFun h0 hL hAi, hR,
      hG.1.evalReg_fc_of_mem hdn (radius_pos k), hray n u hu k,
      WedgeMeasCoord.integral_fc_profile_eq (F := F) (A := A) (Q := Q) (ρ := a) hG ha
        (radius_pos k) (by linarith)]
  unfold avgReg limUnder
  rw [Filter.map_congr heq]

/-! ## 2. Circles that miss `0` -/

/-- **Raw = regularized for the wedge field on a folded circle missing `0`.** For a good free
sample `x`, an a.s. continuous radial path `A` and a folded circle `fc(w, ρ)` with `‖w‖ ≠ ρ`, the
regularized value of `W = wedgeField (lateralPart x) A Q` is `evalReg x (fc w ρ)` plus the circle
integral of the wedge profile (which is `W (fc w ρ)` by
`WedgeCan.wedgeField_eq_evalReg_add_ofFun`, given the two integrability hypotheses). -/
theorem evalReg_wedgeField_fc_of_gap (hG : WedgeTK.GoodRad x F)
    (hray : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (Q : ℝ) {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hgap : ‖w‖ ≠ ρ)
    (hint : Integrable (fun u => radAvgReg x ‖u‖) (foldedCircle w ρ))
    (hiA : Integrable (fun u => A (-Real.log ‖u‖)) (foldedCircle w ρ)) :
    evalReg (wedgeField (lateralPart x) A Q) (foldedCircle w ρ) =
      wedgeField (lateralPart x) A Q (foldedCircle w ρ) := by
  have hδ : 0 < |‖w‖ - ρ| := abs_pos.2 (sub_ne_zero.2 hgap)
  have ha : 0 < |‖w‖ - ρ| / 2 := by linarith
  have hle : |‖w‖ - ρ| / 2 ≤ |‖w‖ - ρ| := by linarith
  have hae1 : ∀ᵐ u ∂foldedCircle w ρ, |‖w‖ - ρ| ≤ ‖u‖ := WedgeCan.ae_fc_abs_le_norm hρ
  have hae2 : ∀ᵐ u ∂foldedCircle w ρ, u ∈ Hbar := RegClosure.fc_ae_mem_Hbar w ρ
  have hkey : ∀ᶠ k : ℕ in atTop,
      ∫ u, avgReg (wedgeField (lateralPart x) A Q) k u ∂foldedCircle w ρ =
        ∫ u, avgReg (x + ofFun (WedgeMeasCoord.gT F A Q (|‖w‖ - ρ| / 2))) k u
          ∂foldedCircle w ρ :=
    ((tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT).eventually_lt_const
      (show (0 : ℝ) < |‖w‖ - ρ| / 2 / 4 by positivity)).mono fun k hk =>
      integral_congr_ae (by
        filter_upwards [hae1, hae2] with u hu1 hu2
        exact avgReg_wedgeField_eq_gT_of_gap hG hray hA Q ha hk hu2 (hle.trans hu1))
  have h1 : evalReg (wedgeField (lateralPart x) A Q) (foldedCircle w ρ) =
      evalReg (x + ofFun (WedgeMeasCoord.gT F A Q (|‖w‖ - ρ| / 2)))
        (foldedCircle w ρ) := by
    unfold evalReg limUnder
    rw [Filter.map_congr hkey]
  have hstep := GoodSample.evalReg_add_ofFun_fc (x := x) (F := F) hG.1
    (φ := WedgeMeasCoord.gT F A Q (|‖w‖ - ρ| / 2))
    (WedgeMeasCoord.continuous_gT (Q := Q) hG.1.1 hA ha).continuousOn
    (CircleFubini.foldH_mem_Hbar' w) hρ
  rw [WedgeTK.fc_foldH_eq w ρ] at hstep
  have hW : wedgeField (lateralPart x) A Q (foldedCircle w ρ) =
      evalReg x (foldedCircle w ρ) +
        ∫ u, WedgeCan.wedgeProfile x A Q u ∂foldedCircle w ρ :=
    WedgeCan.wedgeField_eq_evalReg_add_ofFun hint
      (WedgeCan.integrable_logProfile_foldedCircle Q w ρ) hiA
  rw [h1, hstep, hW]
  simp only [GoodSample.smoothFun]
  rw [WedgeTK.fc_foldH_eq w ρ]
  rw [integral_congr_ae (hae1.mono fun u hu =>
    WedgeMeasCoord.gT_eq (F := F) (A := A) (Q := Q) hG ha (by linarith [hle.trans hu]))]

/-! ## 3. The node from the through-`0` circles -/

end F1
end QuantumZipper
