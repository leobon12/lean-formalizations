import QuantumZipper.Proofs.LQG.ZoomRadialFinal

/-!
# The radial process at a zoom is the wedge radial process: basic ingredients (TASKS.md R6)

Basic tools for the final assembly of the D3 radial comparison `abs_prob_zoomRadial_sub_le`
(TASKS.md row R6, blueprint SECTION5 node D3 / E_BRANCH D3⁺). The main theorem itself, together
with the Williams comparison `prob_Tc_lt_le_prob_wedge_high`, is in `ZoomRadialEnd.lean`, which
imports this file.

* `exists_rat_Icc_le_sub` — rationalization of a continuous function with a general threshold
  (generalization of `ZoomRadialMain.exists_rat_Icc_le_sub_one`, own elementary proof);
* `prob_trunc_Rw_eq_prob_trunc_wedge` — D3-RAD step (ii): the pushforward of
  `WedgeTrans.wedge_translation` to measurable path sets;
* the objects `willX, willYt, willYh, willTc, willZp` of `WilliamsDriftDecomposition` in the
  notation of this development, together with `williams_law`, the law equality of `hW` for them;
* `continuous_willZp` and `measurable_willZp_path` — the pasting path `Zp` is continuous for every
  `ω` (`β 0 = 0`, `β'` continuous with `β' 0 = 0`) and is measurable as a map into path space.

Sources: Sheffield (arXiv:1012.4797) §1.6 and the proof of Prop. 1.6; Williams (1974);
Rogers–Pitman (1981) Thm 1; Revuz–Yor VII.4.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace ZoomRadial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
-- `Ω'` is at universe `0` because `WilliamsDriftDecomposition` only quantifies over `Type`
variable {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-! ## 1. Rationalization with a general threshold -/

/-- **Rationalization (general threshold).** A continuous function with `f u ≥ c` at a point
`u ∈ [0, S]` (`S ≥ 0`) satisfies `f q ≥ c − ε` at some rational point `q ∈ [0, S]`. This
generalizes `ZoomRadialMain.exists_rat_Icc_le_sub_one` (the case `ε = 1`) by the same argument;
own elementary proof. -/
theorem exists_rat_Icc_le_sub {f : ℝ → ℝ} (hf : Continuous f) {S c u ε : ℝ} (hS : 0 ≤ S)
    (hu : u ∈ Set.Icc 0 S) (hcu : c ≤ f u) (hε : 0 < ε) :
    ∃ q : ℚ, (q : ℝ) ∈ Set.Icc 0 S ∧ c - ε ≤ f (q : ℝ) := by
  rcases eq_or_lt_of_le hu.1 with h0 | h0
  · refine ⟨0, by simpa only [Rat.cast_zero, ← h0] using hu, ?_⟩
    have : c ≤ f 0 := by rw [← h0] at hcu; exact hcu
    simp only [Rat.cast_zero]; linarith
  · obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.1
      (hf.continuousAt.eventually (Metric.ball_mem_nhds (f u) hε))
    set r : ℝ := min δ u / 2 with hr
    have hrpos : 0 < r := by
      rw [hr]
      have h1 : 0 < min δ u := lt_min hδpos h0
      linarith
    have hrleδ : r ≤ δ := by
      rw [hr]; linarith [min_le_left δ u]
    have hlt : max 0 (u - r) < min S (u + r) := by
      refine max_lt ?_ ?_
      · exact lt_min (h0.trans_le hu.2) (by linarith)
      · have hrle : r ≤ u / 2 := by
          rw [hr]; linarith [min_le_right δ u]
        exact lt_min (by linarith [hu.2, hrpos]) (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hqu : |(q : ℝ) - u| < δ := by
      have h1 : u - r < (q : ℝ) := lt_of_le_of_lt (le_max_right 0 (u - r)) hq1
      have h2 : (q : ℝ) < u + r := lt_of_lt_of_le hq2 (min_le_right S (u + r))
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    refine ⟨q, ⟨le_of_lt (lt_of_le_of_lt (le_max_left 0 (u - r)) hq1),
      le_of_lt (lt_of_lt_of_le hq2 (min_le_left S (u + r)))⟩, ?_⟩
    have hball : dist (f (q : ℝ)) (f u) < ε :=
      hδ (by rw [Metric.mem_ball, Real.dist_eq]; exact hqu)
    rw [Real.dist_eq, abs_lt] at hball
    linarith [hball.1]

/-! ## 2. Step (ii): the pushforward of wedge translation to path sets -/

/-- **D3-RAD step (ii).** The truncated re-centred wedge path has the law of the truncated wedge
path, on every measurable set of paths: the pushforward of `WedgeTrans.wedge_translation` along
the measurable truncation `trunc S`. -/
theorem prob_trunc_Rw_eq_prob_trunc_wedge (hW : WilliamsDriftDecomposition) {α Q : ℝ}
    (hαQ : α < Q) {A : ℝ → Ω' → ℝ} (hA : IsWedgeProcess α Q A P') {c S : ℝ} (hc : 0 < c)
    {B B' : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hB' : IsBrownianReal B' P')
    (hAB : ∀ ω t, A t ω = wedgePath α Q (fun s => B s ω) (fun s => B' s ω) t)
    {E : Set (ℝ → ℝ)} (hE : MeasurableSet E) :
    P' {ω | trunc S (Rw α Q B B' c ω) ∈ E} = P' {ω | trunc S (fun t => A t ω) ∈ E} := by
  classical
  have hMe : MeasurableSet (trunc S ⁻¹' E) := measurable_trunc S hE
  have hΦa : AEMeasurable
      (fun ω => fun t => A (sInf {s : ℝ | 0 ≤ s ∧ A s ω ≤ -c} + t) ω + c) P' :=
    (aemeasurable_Rw (S := S) hB hB' hαQ hc).congr (by
      filter_upwards with ω
      exact Rw_eq_recentre hAB ω)
  have hΨa : AEMeasurable (fun ω => fun t => A t ω) P' := aemeasurable_wedgePath hA
  have hWtE := congrArg (fun ν : Measure (ℝ → ℝ) => ν (trunc S ⁻¹' E))
    (WedgeTrans.wedge_translation (P := P') hW hA hαQ hc)
  rw [Measure.map_apply_of_aemeasurable hΦa hMe,
    Measure.map_apply_of_aemeasurable hΨa hMe] at hWtE
  calc P' {ω | trunc S (Rw α Q B B' c ω) ∈ E}
      = P' ((fun ω => fun t => A (sInf {s : ℝ | 0 ≤ s ∧ A s ω ≤ -c} + t) ω + c) ⁻¹'
          (trunc S ⁻¹' E)) := by
        congr 1
        ext ω
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        rw [Rw_eq_recentre hAB ω]
    _ = P' ((fun ω => fun t => A t ω) ⁻¹' (trunc S ⁻¹' E)) := hWtE
    _ = P' {ω | trunc S (fun t => A t ω) ∈ E} := rfl

/-! ## 3. The Williams decomposition in the notation of this file

`WilliamsDriftDecomposition` is stated with `let`-bound objects `X, Yt, Yh, Tc, Zp` for
`σ = √2`, `μ = Q − α`. The definitions below have textually the same bodies, so applying `hW`
gives the law equality for these names verbatim (`williams_law`). -/

/-- The drifted path `X t = √2 b t − (Q−α) t` of `WilliamsDriftDecomposition`. -/
abbrev willX (α Q : ℝ) (b : ℝ≥0 → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun t ω => √2 * b t.toNNReal ω - (Q - α) * t

/-- The backward path `Yt = √2 b' + (Q−α)·` of `WilliamsDriftDecomposition`. -/
abbrev willYt (α Q : ℝ) (b' : ℝ≥0 → Ω → ℝ) : Ω → ℝ → ℝ :=
  fun ω s => √2 * b' s.toNNReal ω + (Q - α) * s

/-- The Williams path `Yh u = Yt (u + lastZero Yt)`. -/
abbrev willYh (α Q : ℝ) (b' : ℝ≥0 → Ω → ℝ) : ℝ → Ω → ℝ :=
  fun u ω => willYt α Q b' ω (u + lastZero (willYt α Q b' ω))

/-- The hitting time of `−c` by the drifted path, in the form used by
`WilliamsDriftDecomposition`. -/
abbrev willTc (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) : Ω → ℝ :=
  fun ω => sInf {t : ℝ | 0 ≤ t ∧ willX α Q b t ω ≤ -c}

/-- The Williams pasting path `Zp` of `WilliamsDriftDecomposition`. -/
abbrev willZp (α Q c : ℝ) (b b' : ℝ≥0 → Ω → ℝ) : ℝ → Ω → ℝ := fun u ω =>
  if u ≤ willTc α Q c b ω then willX α Q b (willTc α Q c b ω - u) ω + c
  else c + willYh α Q b' (u - willTc α Q c b ω) ω

/-- `Zp` read as a path-valued map on the path space `ℝ≥0 → ℝ` (the space on which `hW` states
its law equality). -/
abbrev willZpNN (α Q c : ℝ) (b b' : ℝ≥0 → Ω → ℝ) : Ω → ℝ≥0 → ℝ :=
  fun ω u => willZp α Q c b b' (u : ℝ) ω

/-- `Yh` read as a path-valued map on the path space `ℝ≥0 → ℝ`. -/
abbrev willYhNN (α Q : ℝ) (b' : ℝ≥0 → Ω → ℝ) : Ω → ℝ≥0 → ℝ :=
  fun ω u => willYh α Q b' (u : ℝ) ω

/-- The hitting time of the drifted path is the zoom time `Tc`. -/
theorem willTc_eq_Tc (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    willTc α Q c b ω = Tc α Q c b ω := by
  have hset : {t : ℝ | 0 ≤ t ∧ willX α Q b t ω ≤ -c} =
      {s : ℝ | 0 ≤ s ∧ Xdrift α Q (pathOf b ω) s ≤ -c} := rfl
  rw [willTc, hset, sInf_drift_eq_Tc]

/-- `Zp` at the hitting time is `c` (for a path starting at `0`). -/
theorem willZp_Tc (α Q c : ℝ) (b b' : ℝ≥0 → Ω → ℝ) (ω : Ω) (h0 : b 0 ω = 0) :
    willZp α Q c b b' (willTc α Q c b ω) ω = c := by
  rw [willZp, if_pos le_rfl, sub_self]
  simp only [willX, Real.toNNReal_zero, h0, mul_zero, sub_zero, zero_add]

/-- `Yh 0 = 0` (the Williams path starts at its last zero). -/
theorem willYh_zero (α Q : ℝ) (b' : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hb'c : Continuous fun s : ℝ≥0 => b' s ω) (h0 : b' 0 ω = 0) :
    willYh α Q b' 0 ω = 0 := by
  have hYtc : Continuous (willYt α Q b' ω) :=
    (continuous_const.mul (hb'c.comp continuous_real_toNNReal)).add
      (continuous_const.mul continuous_id)
  show willYt α Q b' ω (0 + lastZero (willYt α Q b' ω)) = 0
  rw [zero_add]
  refine apply_lastZero_self hYtc ?_
  simp only [willYt, Real.toNNReal_zero, h0, mul_zero, add_zero]

/-- **`WilliamsDriftDecomposition` in the notation of this file.** -/
theorem williams_law (hW : WilliamsDriftDecomposition) {α Q : ℝ} (hαQ : α < Q) {c : ℝ} (hc : 0 < c)
    {β β' : ℝ≥0 → Ω' → ℝ} (hβ : IsBrownianReal β P') (hβ' : IsBrownianReal β' P')
    (hind : IndepFun (pathOf β) (pathOf β') P') :
    P'.map (willZpNN α Q c β β') = P'.map (willYhNN α Q β') := by
  have hμ : 0 < Q - α := sub_pos.2 hαQ
  have hsqrt : (0 : ℝ) < √2 := by positivity
  exact hW (Q - α) (√2) c hμ hsqrt hc P' β β' hβ hβ' hind

/-! ## 4. Continuity and measurability of the pasting path -/

/-- **The pasting path `Zp` is continuous** whenever the radial path is `√2 · (continuous, 0 at
0)` and the backward path is continuous with value `0` at `0`: the two branches agree at the
junction `u = Tc` (there the first is `willX 0 + c = c` and the second `c + Yh 0 = c`).
Own elementary proof. -/
theorem continuous_willZp {α Q c : ℝ} {β β' : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hβ : Continuous fun s : ℝ≥0 => β s ω) (hβ0 : β 0 ω = 0)
    (hβ' : Continuous fun s : ℝ≥0 => β' s ω) (hβ'0 : β' 0 ω = 0) :
    Continuous (willZp α Q c β β' · ω) := by
  set T : ℝ := willTc α Q c β ω with hT
  set A : ℝ → ℝ := fun u => willX α Q β (T - u) ω + c with hA
  set B : ℝ → ℝ := fun u => c + willYh α Q β' (u - T) ω with hB
  have hAc : Continuous A := by
    rw [show A = fun u : ℝ => willX α Q β (T - u) ω + c from rfl]
    exact (((continuous_const.mul (hβ.comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)).comp (continuous_const.sub continuous_id)).add_const c
  have hYhc : Continuous (willYh α Q β' · ω) := by
    rw [show (willYh α Q β' · ω)
      = fun u : ℝ => willYt α Q β' ω (u + lastZero (willYt α Q β' ω)) from rfl]
    exact ((continuous_const.mul (hβ'.comp continuous_real_toNNReal)).add
      (continuous_const.mul continuous_id)).comp (continuous_id.add continuous_const)
  have hBc : Continuous B := by
    rw [show B = fun u : ℝ => c + willYh α Q β' (u - T) ω from rfl]
    exact (hYhc.const_add c).comp (continuous_id.sub continuous_const)
  have hAT : A T = c := by
    rw [show A T = willX α Q β (T - T) ω + c from rfl, sub_self]
    simp only [willX, Real.toNNReal_zero, hβ0, mul_zero, sub_zero, zero_add]
  have hBT : B T = c := by
    rw [show B T = c + willYh α Q β' (T - T) ω from rfl, sub_self,
      willYh_zero α Q β' ω hβ' hβ'0, add_zero]
  have hkey : ∀ u : ℝ, willZp α Q c β β' u ω = A (min u T) + B (max u T) - c := by
    intro u
    by_cases hu : u ≤ T
    · have h1 : willZp α Q c β β' u ω = A u := by
        rw [show willZp α Q c β β' u ω =
          (if u ≤ willTc α Q c β ω then willX α Q β (willTc α Q c β ω - u) ω + c else
            c + willYh α Q β' (u - willTc α Q c β ω) ω) from rfl, ← hT, if_pos hu]
      rw [h1, min_eq_left hu, max_eq_right hu, hBT]
      ring
    · have h1 : willZp α Q c β β' u ω = B u := by
        rw [show willZp α Q c β β' u ω =
          (if u ≤ willTc α Q c β ω then willX α Q β (willTc α Q c β ω - u) ω + c else
            c + willYh α Q β' (u - willTc α Q c β ω) ω) from rfl, ← hT, if_neg hu]
      rw [h1, min_eq_right (not_le.1 hu).le, max_eq_left (not_le.1 hu).le]
      linarith [hAT]
  rw [funext hkey]
  exact ((hAc.comp (continuous_id.min continuous_const)).add
    (hBc.comp (continuous_id.max continuous_const))).sub continuous_const

/-- **Measurability of the pasting path as a map into path space** (the path space being
`ℝ≥0 → ℝ`, as in `WilliamsDriftDecomposition`). -/
theorem measurable_willZp_path {α Q c : ℝ} {β β' : ℝ≥0 → Ω → ℝ} (hc : 0 < c)
    (hβm : Measurable (Function.uncurry β)) (hβ'm : Measurable (Function.uncurry β'))
    (hβc : ∀ ω, Continuous fun s : ℝ≥0 => β s ω) (hβ0 : ∀ ω, β 0 ω = 0)
    (hβ'c : ∀ ω, Continuous fun s : ℝ≥0 => β' s ω) (hβ'0 : ∀ ω, β' 0 ω = 0)
    (hβh : ∀ ω, ∃ s : ℝ≥0, √2 * β s ω - (Q - α) * s ≤ -c) :
    Measurable (willZpNN α Q c β β') := by
  classical
  have hβ0m : ∀ s : ℝ≥0, Measurable fun ω => β s ω := fun s => hβm.of_uncurry_left
  have hβ'0m : ∀ s : ℝ≥0, Measurable fun ω => β' s ω := fun s => hβ'm.of_uncurry_left
  have hYtc : ∀ ω, Continuous (willYt α Q β' ω) := fun ω =>
    (continuous_const.mul ((hβ'c ω).comp continuous_real_toNNReal)).add
      (continuous_const.mul continuous_id)
  have hYtm : ∀ s : ℝ, Measurable fun ω => willYt α Q β' ω s := fun s =>
    ((hβ'0m s.toNNReal).const_mul (√2)).add_const ((Q - α) * s)
  have hYtJ : Measurable fun p : Ω × ℝ => willYt α Q β' p.1 p.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun r ω => willYt α Q β' ω r) hYtc
      hYtm).comp measurable_swap
  have hLm : Measurable fun ω => lastZero (willYt α Q β' ω) :=
    WedgeMeas.measurable_lastZero hYtc hYtm
  have hYhJ : Measurable fun p : ℝ × Ω => willYh α Q β' p.1 p.2 := by
    rw [show (fun p : ℝ × Ω => willYh α Q β' p.1 p.2) =
      fun p : ℝ × Ω => willYt α Q β' p.2 (p.1 + lastZero (willYt α Q β' p.2)) from rfl]
    exact hYtJ.comp (measurable_snd.prodMk (measurable_fst.add (hLm.comp measurable_snd)))
  have hτm : Measurable fun ω => willTc α Q c β ω := by
    rw [show (fun ω => willTc α Q c β ω) = fun ω => Tc α Q c β ω from
      funext fun ω => willTc_eq_Tc α Q c β ω]
    have hdrift : ∀ ω : Ω, ∃ s : ℝ, 0 ≤ s ∧ Xdrift α Q (pathOf β ω) s ≤ -c := fun ω =>
      exists_drift_le (α := α) (Q := Q) (c := c) (β := β) (ω := ω) (hβh ω)
    have hτ : Measurable fun ω => (Thit α Q c (pathOf β ω)).toReal :=
      ((measurable_Thit α Q c).comp (measurable_pi_iff.2 hβ0m)).ennreal_toReal
    rw [show (fun ω => Tc α Q c β ω) = fun ω => (Thit α Q c (pathOf β ω)).toReal from
      funext fun ω => ((Thit_toReal (hβc ω) (hβ0 ω) hc (hdrift ω)).trans
        (sInf_drift_eq_Tc α Q c β ω)).symm]
    exact hτ
  have hZpm : ∀ u : ℝ, Measurable fun ω => willZp α Q c β β' u ω := by
    intro u
    have hcond : MeasurableSet {ω : Ω | u ≤ willTc α Q c β ω} :=
      measurableSet_le measurable_const hτm
    have hb1 : Measurable fun ω : Ω =>
        √2 * β (willTc α Q c β ω - u).toNNReal ω - (Q - α) * (willTc α Q c β ω - u) + c := by
      have hg : Measurable fun ω : Ω => (willTc α Q c β ω - u).toNNReal :=
        (hτm.sub_const u).real_toNNReal
      have h1 : Measurable fun ω : Ω => √2 * β ((willTc α Q c β ω - u).toNNReal) ω :=
        (hβm.comp (hg.prodMk measurable_id)).const_mul (√2)
      have h2 : Measurable fun ω : Ω => (Q - α) * (willTc α Q c β ω - u) :=
        (hτm.sub_const u).const_mul (Q - α)
      exact (h1.sub h2).add_const c
    have hb2 : Measurable fun ω : Ω => c + willYh α Q β' (u - willTc α Q c β ω) ω := by
      have hu : Measurable fun ω : Ω => u - willTc α Q c β ω := measurable_const.sub hτm
      exact measurable_const.add (hYhJ.comp (hu.prodMk measurable_id))
    rw [show (fun ω => willZp α Q c β β' u ω) = fun ω : Ω =>
      (if u ≤ willTc α Q c β ω then
        √2 * β (willTc α Q c β ω - u).toNNReal ω - (Q - α) * (willTc α Q c β ω - u) + c
      else c + willYh α Q β' (u - willTc α Q c β ω) ω) from rfl]
    exact Measurable.ite hcond hb1 hb2
  rw [show willZpNN α Q c β β'
    = fun ω (u : ℝ≥0) => willZp α Q c β β' (u : ℝ) ω from rfl]
  exact measurable_pi_iff.2 fun u => hZpm (u : ℝ)

end ZoomRadial
end QuantumZipper
