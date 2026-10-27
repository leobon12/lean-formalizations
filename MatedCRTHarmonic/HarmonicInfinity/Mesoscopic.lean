import MatedCRTHarmonic.HarmonicInfinity.Walk
import MatedCRTHarmonic.GoodScales.Bound
import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Adj
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.WalkLaw
import MatedCRTHarmonic.Frozen.VertexPath
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.GoodScales.Times
import MatedCRTHarmonic.CellularFacts.Basic
import MatedCRTHarmonic.Frozen.MesoscopicControlWith
import MatedCRTHarmonic.Frozen.CellularEmbedding
import MatedCRTHarmonic.Frozen.IsConnectedSet

/-!
# Uniform disconnection from recurrence and mesoscopic control

Source: §4, steps **C5** (mesoscopic control implies
uniform disconnection) and **C6** (assembly); the replacement proof of the uniform-disconnection result
, which does not use the cited route [7, §9] / [21, Prop. 1.7] (the recurrence proof).

* `exists_mem_support_sphere`: the crossing lemma along a graph walk (plane data).
* `exists_annulus_scale`: bullets 1 and 3 of mesoscopic control give, for every `ρ`, a centre `z` and a
  radius `r ≈ R ≥ 10ρ` with `|z| ≤ R/100` such that the annular event at `(z, r)` has probability
  `≥ p` from every vertex whose cell meets `∂B_r(z)`.
* `uniformDisconnection_of_mesoscopicControlWith` (**C5**): a connected recurrent graph with a
  cellular embedding satisfying `MesoscopicControlWith p σ ν` has `UD(p)`: a walk from far away
  first reaches `∂B_r(z)`, then with probability `≥ p` closes the annular loop before reaching `F`,
  and that loop separates every far vertex from `F`.
* `harmInfExists_of_recurrent_of_mesoscopic` (**C6**, the target): `G.HarmInfExists o`;
  `hasHarmInf_of_recurrent_of_mesoscopic`: harmonic measure from `∞` exists for every finite `A`,
  and `hasHarmInf_isProbability_of_recurrent_of_mesoscopic`: it is a probability vector on the edge
  boundary for nonempty `A`; `ae_harmInfExists_of_ae`: the random form consumed by
  `polynomial_growth_of_randomCellular` (`hharm`).

Only bullets 1 and 3 of mesoscopic control and the cell fields compact, connected, locally finite,
adjacent ⇒ intersecting (and `⋃ cells = ℂ`, for `V` infinite) are used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace MatedCRTHarmonic.HarmonicInfinity

open Markov Harmonic

variable {V E : Type*} {G : LFMultigraph V E}

/-! ### The crossing lemma along graph walks -/

/-- **Crossing lemma along a walk.** For plane data `J`, a graph walk from `u` to `v`, where `J u`
has a point at distance `≥ ρ` from `z` and `J v` a point at distance `≤ ρ`, visits a vertex whose
plane set meets the circle `∂B_ρ(z)`. -/
theorem exists_mem_support_sphere {J : V → Set ℂ} (hJ : G.IsPlaneData J) {z : ℂ} {ρ : ℝ} {u v : V}
    (w : G.adj.Walk u v) (hu : ∃ q ∈ J u, ρ ≤ dist q z) (hv : ∃ q ∈ J v, dist q z ≤ ρ) :
    ∃ t ∈ w.support, t ∈ verticesMeeting J (sphere z ρ) := by
  induction w with
  | nil =>
    obtain ⟨q₁, hq₁, h₁⟩ := hu
    obtain ⟨q₂, hq₂, h₂⟩ := hv
    exact ⟨_, SimpleGraph.Walk.start_mem_support _,
      GoodScales.inter_sphere_nonempty_of_isPreconnected (hJ.isConnected _).isPreconnected hq₁ hq₂
        h₁ h₂⟩
  | @cons a b c h q ih =>
    obtain ⟨q₁, hq₁, h₁⟩ := hu
    by_cases hnear : ∃ q ∈ J a, dist q z ≤ ρ
    · obtain ⟨q₂, hq₂, h₂⟩ := hnear
      exact ⟨a, SimpleGraph.Walk.start_mem_support _,
        GoodScales.inter_sphere_nonempty_of_isPreconnected (hJ.isConnected _).isPreconnected hq₁
          hq₂ h₁ h₂⟩
    · push Not at hnear
      obtain ⟨q', hqa, hqb⟩ := hJ.inter_of_adj a b h
      obtain ⟨t, ht, hts⟩ := ih ⟨q', hqb, (hnear q' hqa).le⟩ hv
      refine ⟨t, ?_, hts⟩
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ ht

/-! ### A good annulus from mesoscopic control -/

/-- **Choice of scale (C5).** Bullets 1 and 3 of mesoscopic control give, for every `ρ`, a radius
`R > 0` with `ρ ≤ R/10`, a centre `z` with `‖z‖ ≤ R/100` and a radius `r ∈ [R - R/100, R]` such that
from every vertex whose cell meets `∂B_r(z)` the annular event at `(z, r)` has probability `≥ p`. -/
theorem exists_annulus_scale {o : V} {H : CellularEmbedding G o} {p σ ν : ℝ}
    (h19 : H.MesoscopicControlWith p σ ν) (ρ : ℝ) :
    ∃ (z : ℂ) (r R : ℝ), 0 < R ∧ ρ ≤ R / 10 ∧ ‖z‖ ≤ R / 100 ∧ R - R / 100 ≤ r ∧ r ≤ R ∧
      ∀ x ∈ verticesMeeting H.cell (sphere z r),
        ENNReal.ofReal p ≤ G.walkLaw x {ω | G.AnnularEvent H.cell z r (G.vertexPath ω)} := by
  obtain ⟨-, -, hσ, -, R₀, m, e, d, hpos, hm, hlim, -, hnet, -⟩ := h19
  have ev1 : ∀ᶠ R in atTop, R₀ ≤ R := eventually_ge_atTop R₀
  have ev2 : ∀ᶠ R in atTop, (1 : ℝ) ≤ R := eventually_ge_atTop 1
  have ev3 : ∀ᶠ R in atTop, (100 : ℝ) ≤ R ^ σ := (tendsto_rpow_atTop hσ).eventually_ge_atTop 100
  have ev4 : ∀ᶠ R in atTop, (e R + d R) / m R < 1 / 100 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  have ev5 : ∀ᶠ R in atTop, 1000 * ρ ≤ R := eventually_ge_atTop (1000 * ρ)
  obtain ⟨R', h1, h2, h3, h4, h5⟩ := (ev1.and (ev2.and (ev3.and (ev4.and ev5)))).exists
  obtain ⟨hm0, he0, hd0⟩ := hpos R' h1
  have hmR : m R' ≤ R' / 100 := by
    have h := hm R' h1
    rw [Real.rpow_sub (by linarith), Real.rpow_one] at h
    exact h.trans (div_le_div_of_nonneg_left (by linarith) (by norm_num) h3)
  have heR : e R' < m R' / 100 := by
    rw [div_lt_iff₀ hm0] at h4
    linarith
  obtain ⟨Z, Q, -, hZnet, hQ, hQnet, hann⟩ := hnet R' h1
  obtain ⟨z, hzZ, hz⟩ := hZnet 0 (mem_ball_self (by linarith))
  obtain ⟨r, hrQ, hr⟩ := hQnet (R' / 100) ⟨hmR, le_rfl⟩
  have hrI := hQ r hrQ
  rw [dist_zero_left] at hz
  rw [Real.dist_eq] at hr
  have hr' := (abs_le.mp hr).2
  refine ⟨z, r, R' / 100, by positivity, by linarith, by linarith, by linarith, hrI.2,
    hann z hzZ r hrQ⟩

/-! ### C5: mesoscopic control implies uniform disconnection -/

/-- The walk from `x` reaches `V(∂B_r(z))` before (or when) it first hits `F`, if the cell of `x`
lies outside `B_r(z)` and the cells of `F` meet `B̄_r(z)`. -/
theorem hitTime_sphere_le {J : V → Set ℂ} (hJ : G.IsPlaneData J) {X : ℕ → V}
    (hstep : ∀ n, GoodScales.StepOK G (X n) (X (n + 1))) {z : ℂ} {r : ℝ}
    (hfar : ∃ q ∈ J (X 0), r ≤ dist q z) {F : Set V} (hF : ∀ v ∈ F, ∃ q ∈ J v, dist q z ≤ r)
    {n : ℕ} (hn : hitTime F X = n) : hitTime (verticesMeeting J (sphere z r)) X ≤ n := by
  have hXn : X n ∈ F := (hitTime_eq_coe_iff.mp hn).1
  have hnear : ∃ q ∈ J (X (0 + n)), dist q z ≤ r := by
    rw [Nat.zero_add]
    exact hF _ hXn
  obtain ⟨m, -, hmn, hm⟩ := GoodScales.exists_mem_sphere_of_cross hJ hstep n 0 hfar hnear
  rw [Nat.zero_add] at hmn
  exact (hitTime_le_of_mem (A := verticesMeeting J (sphere z r)) hm).trans (by exact_mod_cast hmn)

/-- **C5 (the recurrence argument).** A connected recurrent locally finite multigraph with a cellular embedding
satisfying mesoscopic control (`MesoscopicControlWith p σ ν`) has uniform disconnection `UD(p)`. -/
theorem uniformDisconnection_of_mesoscopicControlWith {o : V} (H : CellularEmbedding G o)
    (hconn : G.adj.Connected) (hrec : G.Recurrent) {p σ ν : ℝ}
    (h19 : H.MesoscopicControlWith p σ ν) : UniformDisconnection G p := by
  classical
  have : Countable V := countable_of_connected G hconn
  have : Countable G.State := GoodScales.countable_state G
  have hJ := CellularFacts.isPlaneData_cell H
  have hp1 : p ≤ 1 := h19.2.1.le
  intro F
  rcases (F : Set V).eq_empty_or_nonempty with hF | hF
  · refine ⟨∅, fun x _ y _ => ?_⟩
    have huniv : {ω | G.Disconnects (walkTrace G F ω) {y} F} = Set.univ := by
      ext ω
      simp only [Set.mem_univ, iff_true]
      intro a _ b hb
      rw [hF] at hb
      exact absurd hb (Set.notMem_empty b)
    rw [huniv, measure_univ]
    exact ENNReal.ofReal_le_one.mpr hp1
  -- the cells of `F` lie in `B̄_ρ(0)`
  obtain ⟨ρ, hρ⟩ := (CellularFacts.isCompact_cellUnion H F).isBounded.subset_closedBall 0
  obtain ⟨z, r, R, hR, hρR, hz, hrlo, hrhi, hann⟩ := exists_annulus_scale h19 ρ
  have hfin := H.locallyFinite_cell.finite_nonempty_inter_compact
    (isCompact_closedBall (0 : ℂ) (2 * R))
  refine ⟨F ∪ hfin.toFinset, fun x hx y hy => ?_⟩
  -- geometry: cells of `F` are near `z`, cells of far vertices are far from `z`
  have gF : ∀ v ∈ F, ∀ w ∈ H.cell v, dist w z < r / 2 := by
    intro v hv w hw
    have hw' : w ∈ closedBall (0 : ℂ) ρ := hρ (Set.mem_biUnion (Finset.mem_coe.mpr hv) hw)
    rw [mem_closedBall, dist_zero_right] at hw'
    calc dist w z ≤ ‖w‖ + ‖z‖ := dist_le_norm_add_norm w z
      _ < r / 2 := by linarith
  have gfar : ∀ u, u ∉ F ∪ hfin.toFinset → ∀ w ∈ H.cell u, 3 * r / 2 < dist w z := by
    intro u hu w hw
    have hw' : 2 * R < ‖w‖ := by
      by_contra hle
      push Not at hle
      refine hu (Finset.mem_union_right _ (hfin.mem_toFinset.mpr ⟨w, hw, ?_⟩))
      rw [mem_closedBall, dist_zero_right]
      exact hle
    calc 3 * r / 2 < ‖w‖ - ‖z‖ := by linarith
      _ ≤ dist w z := by
        rw [dist_eq_norm]
        exact norm_sub_norm_le w z
  have hFnear : ∀ v ∈ (F : Set V), ∃ q ∈ H.cell v, dist q z ≤ r := fun v hv => by
    obtain ⟨q, hq⟩ := (H.isConnected_cell v).nonempty
    exact ⟨q, hq, by linarith [gF v hv q hq]⟩
  have hfarz : ∀ u, u ∉ F ∪ hfin.toFinset → ∀ ρ' ≤ 3 * r / 2, ∃ q ∈ H.cell u, ρ' ≤ dist q z :=
    fun u hu ρ' hρ' => by
      obtain ⟨q, hq⟩ := (H.isConnected_cell u).nonempty
      exact ⟨q, hq, by linarith [gfar u hu q hq]⟩
  have hFann : ∀ v ∈ (F : Set V), v ∉ verticesMeeting H.cell (annulus z (r / 2) (3 * r / 2)) := by
    rintro v hv ⟨w, hw, hwa⟩
    exact hwa.2 (mem_ball.mpr (gF v hv w hw))
  have hr0 : 0 < r := by linarith
  -- probability
  set S₁ : Set V := verticesMeeting H.cell (sphere z r) with hS₁
  set T₁ := hitTime (G.stateVertex ⁻¹' S₁) with hT₁
  set Ann : Set (ℕ → G.State) := {ω | G.AnnularEvent H.cell z r (G.vertexPath ω)} with hAnn
  have hAnnMeas : MeasurableSet Ann :=
    GoodScales.measurableSet_succEvent (G := G) (J := H.cell) (z := z) (r := fun _ => r) 0
  set P := G.walkLaw x with hP
  have hgood : ∀ᵐ ω ∂P, ω 0 = startState G x ∧
      (∀ n, GoodScales.StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1))) ∧
      hitTime (F : Set V) (G.vertexPath ω) ≠ ⊤ := by
    have hF1 := walkLaw_hitTime_ne_top hrec hF x
    have hae : ∀ᵐ ω ∂P, hitTime (F : Set V) (G.vertexPath ω) ≠ ⊤ :=
      (ae_iff_measure_eq (measurableSet_hitTime_ne_top G (F : Set V)).nullMeasurableSet).mpr
        (by rw [hF1, measure_univ])
    filter_upwards [GoodScales.ae_start_and_stepOK G (startState G x), hae] with ω h1 h2
    exact ⟨h1.1, h1.2, h2⟩
  -- `T₁ ≤ T_F < ⊤` almost surely
  have hT₁le : ∀ ω : ℕ → G.State, ω 0 = startState G x →
      (∀ n, GoodScales.StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1))) →
      ∀ n : ℕ, hitTime (F : Set V) (G.vertexPath ω) = n → T₁ ω ≤ n := by
    intro ω h0 hstep n hn
    have hX0 : G.vertexPath ω 0 = x := by
      show G.stateVertex (ω 0) = x
      rw [h0]
      rfl
    exact hitTime_sphere_le hJ hstep (hX0 ▸ hfarz x hx r (by linarith)) hFnear hn
  have hT₁1 : P {ω | T₁ ω < ⊤} = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← measure_univ (μ := P)]
    refine measure_mono_ae ?_
    filter_upwards [hgood] with ω ⟨h0, hstep, hTF⟩ _
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hTF
    exact lt_of_le_of_lt (hT₁le ω h0 hstep n hn.symm) (ENat.natCast_lt_top n)
  -- strong Markov at `T₁`
  have hSM : ENNReal.ofReal p ≤ P ({ω | T₁ ω < ⊤} ∩ stopShift T₁ ⁻¹' Ann) := by
    have h := le_chainLaw_inter_stopShift_preimage G.walkKernel (startState G x)
      (isStoppingTime_hitTime (A := G.stateVertex ⁻¹' S₁) MeasurableSet.of_discrete)
      (F := Set.univ) MeasurableSet.univ hAnnMeas (p := ENNReal.ofReal p) ?_
    · rw [Set.univ_inter] at h
      have h' : ENNReal.ofReal p * P {ω | T₁ ω < ⊤} ≤
          P ({ω | T₁ ω < ⊤} ∩ stopShift T₁ ⁻¹' Ann) := h
      rwa [hT₁1, mul_one] at h'
    · rintro ω ⟨-, hlt⟩
      have hmem : stopState T₁ ω ∈ G.stateVertex ⁻¹' S₁ := stopState_hitTime_mem hlt.ne
      calc ENNReal.ofReal p ≤ G.walkLaw (G.stateVertex (stopState T₁ ω)) Ann := hann _ hmem
        _ = chainLaw G.walkKernel (stopState T₁ ω) Ann :=
          GoodScales.chainLaw_vertexEvent_eq G (s := Sum.inl (G.stateVertex (stopState T₁ ω)))
            (s' := stopState T₁ ω) rfl (Q := fun X => G.AnnularEvent H.cell z r X) hAnnMeas
  -- on the good paths, a closed annular loop separates `y` from `F` before `T_F`
  refine hSM.trans (measure_mono_ae ?_)
  filter_upwards [hgood] with ω ⟨h0, hstep, hTF⟩ ⟨hlt, hAω⟩
  obtain ⟨nF, hnF⟩ := ENat.ne_top_iff_exists.mp hTF
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (show T₁ ω < ⊤ from hlt).ne
  have hsF : s ≤ nF := by
    have := hT₁le ω h0 hstep nF hnF.symm
    rw [← hs] at this
    exact_mod_cast this
  have hA' : G.AnnularEvent H.cell z r (G.vertexPath (walkShift s ω)) := by
    have h := (show stopShift T₁ ω ∈ Ann from hAω)
    rw [stopShift_eq_of_eq hs.symm] at h
    exact h
  obtain ⟨τ, hτ, hdisc, -⟩ := hA'
  set X := G.vertexPath ω with hX
  -- the walk avoids `F` before time `s + τ`
  have hB1 : ∀ j < s + τ, X j ∉ (F : Set V) := by
    intro j hj hjF
    by_cases hjs : j < s
    · have hjT : (j : ℕ∞) < hitTime (F : Set V) X := by
        rw [← hnF]
        exact_mod_cast (show j < nF by omega)
      exact notMem_of_lt_hitTime hjT hjF
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hjs)
      have hm : (m : ℕ∞) < hitTime (verticesMeeting H.cell (annulus z (r / 2) (3 * r / 2)))ᶜ
          (G.vertexPath (walkShift s ω)) := by
        rw [hτ]
        exact_mod_cast (show m < τ by omega)
      have hmem := notMem_of_lt_hitTime hm
      rw [Set.mem_compl_iff, not_not] at hmem
      exact hFann _ hjF hmem
  have hB2 : s + τ ≤ nF := by
    by_contra hlt'
    exact hB1 nF (by omega) (hitTime_eq_coe_iff.mp hnF.symm).1
  -- the loop is in the trace before `T_F`
  have hB3 : {v | ∃ m < τ, G.vertexPath (walkShift s ω) m = v} ⊆ walkTrace G F ω := by
    rintro v ⟨m, hm, rfl⟩
    refine ⟨s + m, ?_, rfl⟩
    rw [← hnF]
    exact_mod_cast (show s + m < nF by omega)
  -- every walk from `y` to `F` crosses the loop
  intro a ha b hb w
  rw [Set.mem_singleton_iff] at ha
  subst ha
  have hbnear : ∀ ρ' : ℝ, r / 2 ≤ ρ' → ∃ q ∈ H.cell b, dist q z ≤ ρ' := fun ρ' hρ' => by
    obtain ⟨q, hq⟩ := (H.isConnected_cell b).nonempty
    exact ⟨q, hq, by linarith [gF b hb q hq]⟩
  obtain ⟨t, ht, htS⟩ := exists_mem_support_sphere hJ w (ρ := 5 * r / 4)
    (hfarz a hy _ (by linarith)) (hbnear _ (by linarith))
  set w₂ := w.dropUntil t ht with hw₂
  have htfar : ∃ q ∈ H.cell t, 3 * r / 4 ≤ dist q z := by
    obtain ⟨q, hq, hqs⟩ := htS
    exact ⟨q, hq, by rw [mem_sphere.mp hqs]; linarith⟩
  obtain ⟨t', ht', ht'S⟩ := exists_mem_support_sphere hJ w₂ (ρ := 3 * r / 4) htfar
    (hbnear _ (by linarith))
  obtain ⟨v, hv, hvK⟩ := hdisc t' ht'S t htS (w₂.takeUntil t' ht').reverse
  refine ⟨v, ?_, hB3 hvK⟩
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
  exact w.support_dropUntil_subset_support ht
    (w₂.support_takeUntil_subset_support ht' hv)

/-! ### C6: assembly -/

end MatedCRTHarmonic.HarmonicInfinity
