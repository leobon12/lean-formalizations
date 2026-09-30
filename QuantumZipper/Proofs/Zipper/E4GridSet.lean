import QuantumZipper.Proofs.Zipper.E4GridDet

/-!
# E4-GRID, G1: the grid event is a measurable set of `(x, V^{t_k}, W⁰)`

`handoff/E4-A.md`, sub-statement G1. For a continuous driver `V` with `V 0 = 0` agreeing with the
continuous path `d.1` on `[0, t_k]` and `x ≤ 0`:

`mem_gridSet_iff : (x, d) ∈ gridSet T ε n k ↔ t_k < T ∧ dyUp n σ_ε(x) = t_k ∧ x live at t_k`,
with `measurableSet_gridSet`.

Route (own bookkeeping): under liveness at `t_k`, `{σ_ε ≤ b}` is the entrance event
`∃ s ∈ [0,b], |realRevMap V s x| ≤ ε` (`E4Grid.sigEps_le_iff`); by continuity of the flow and
compactness of `[0,1]` it is the countable condition `∀ m, ∃ r ∈ ℚ ∩ [0,1],
|realRevMap V (b r) x| < ε + 1/(m+1)` (`exists_le_iff_rat`), and `realRevMap` at live points is
the measurable `E4Meas.Fre` of `(x, stopPath)`; the live set is `M4.measurableSet_liveNeg_Wof`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open E1 CharFun

/-- On `[0,1]`, a continuous function reaches `≤ ε` iff it gets below every `ε + 1/(m+1)` at
rational points. -/
theorem exists_le_iff_rat {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) (ε : ℝ) :
    (∃ ρ ∈ Icc (0 : ℝ) 1, g ρ ≤ ε) ↔
      ∀ m : ℕ, ∃ r : ℚ, (r : ℝ) ∈ Icc (0 : ℝ) 1 ∧ g r < ε + 1 / ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨ρ, hρ, hgρ⟩ m
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨η, hη, hηg⟩ := Metric.continuousWithinAt_iff.1 (hg ρ hρ) _ hm
    obtain ⟨r, hr1, hr2⟩ : ∃ r : ℚ, (r : ℝ) ∈ Icc (0 : ℝ) 1 ∧ dist (r : ℝ) ρ < η := by
      rcases lt_or_eq_of_le hρ.2 with h | h
      · obtain ⟨r, h1, h2⟩ := exists_rat_btwn (lt_min (show ρ < ρ + η by linarith) h)
        refine ⟨r, ⟨hρ.1.trans h1.le, h2.le.trans (min_le_right _ _)⟩, ?_⟩
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith [h2.trans_le (min_le_left _ _)]
      · obtain ⟨r, h1, h2⟩ := exists_rat_btwn
          (max_lt (show ρ - η < ρ by linarith) (show (0 : ℝ) < ρ by rw [h]; norm_num))
        refine ⟨r, ⟨(le_max_right _ _).trans h1.le, h2.le.trans hρ.2⟩, ?_⟩
        rw [Real.dist_eq, abs_of_neg (by linarith)]
        linarith [(le_max_left _ _).trans_lt h1]
    have := hηg hr1 hr2
    rw [Real.dist_eq] at this
    exact ⟨r, hr1, by linarith [le_abs_self (g r - g ρ)]⟩
  · intro h
    choose r hr hgr using h
    obtain ⟨ρ, hρ, φ, hφ, hlim⟩ :=
      isCompact_Icc.tendsto_subseq (x := fun m => (r m : ℝ)) (fun m => hr m)
    refine ⟨ρ, hρ, ?_⟩
    have h1 : Tendsto (fun j => g (r (φ j))) atTop (𝓝 (g ρ)) :=
      (hg ρ hρ).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall
        fun j => hr (φ j)⟩)
    have h2 : Tendsto (fun j => ε + 1 / ((φ j : ℝ) + 1)) atTop (𝓝 ε) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa using (tendsto_const_nhds (x := ε)).add this
    exact le_of_tendsto_of_tendsto' h1 h2 fun j => (hgr (φ j)).le

/-- Measurable version of `realRevMap · s x` read from `(x, path)`. -/
def FreS (s : ℝ) (q : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  if hs : 0 ≤ s then E4Meas.Fre hs (q.1, E4Meas.stopPath s q.2) else 0

theorem measurable_FreS (s : ℝ) : Measurable (FreS s) := by
  unfold FreS
  by_cases hs : 0 ≤ s
  · simp only [hs, ↓reduceDIte]
    exact (E4Meas.measurable_Fre hs).comp
      (measurable_fst.prodMk ((E4Meas.measurable_stopPath s).comp measurable_snd))
  · simp only [hs, ↓reduceDIte]; exact measurable_const

/-- Countable form of the entrance event. -/
def HitM (ε b : ℝ) (q : ℝ × (ℝ≥0 → ℝ)) : Prop :=
  0 ≤ b ∧ ∀ m : ℕ, ∃ r : ℚ, (r : ℝ) ∈ Icc (0 : ℝ) 1 ∧ |FreS (b * r) q| < ε + 1 / ((m : ℝ) + 1)

theorem measurableSet_hitM (ε b : ℝ) : MeasurableSet {q | HitM ε b q} := by
  simp only [HitM, ofPred_and, ofPred_forall, ofPred_exists]
  exact (MeasurableSet.const _).inter (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun r =>
    (MeasurableSet.const _).inter (measurableSet_lt (continuous_abs.measurable.comp (measurable_FreS _)) measurable_const))

variable {V : ℝ → ℝ} {T ε x : ℝ}

theorem isLive_mono {t s : ℝ} (hl : IsLive V t x) (hst : s ≤ t) : IsLive V s x :=
  lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hl

theorem FreS_eq (hV : Continuous V) {f : ℝ≥0 → ℝ} (hf : Continuous f) {t : ℝ}
    (hVf : EqOn V (fun s => f s.toNNReal) (Icc 0 t)) (hl : IsLive V t x) {s : ℝ}
    (hs : s ∈ Icc 0 t) : FreS s (x, f) = realRevMap V s x := by
  rw [FreS, dif_pos hs.1]
  refine E4Meas.Fre_eq hs.1 hV (fun y hy => ?_) (isLive_mono hl hs.2)
  rw [hVf ⟨hy.1, hy.2.trans hs.2⟩]
  exact (E4Meas.eqOn_Wof_stopPath hs.1 hf hy).symm

theorem hitM_iff (hV : Continuous V) {f : ℝ≥0 → ℝ} (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (hVf : EqOn V (fun s => f s.toNNReal) (Icc 0 t)) (hl : IsLive V t x) {b : ℝ} (hbt : b ≤ t) :
    HitM ε b (x, f) ↔ HitBy V ε b x := by
  unfold HitM HitBy
  refine and_congr_right fun hb => ?_
  have hmem : ∀ ρ ∈ Icc (0 : ℝ) 1, b * ρ ∈ Icc 0 t := fun ρ hρ =>
    ⟨mul_nonneg hb hρ.1, (mul_le_of_le_one_right hb hρ.2).trans hbt⟩
  obtain ⟨T', hT't, u, hu, hR, -⟩ := exists_sol_beyond hV ht hl
  have hg : ContinuousOn (fun ρ => |realRevMap V (b * ρ) x|) (Icc 0 1) := by
    have h1 : ContinuousOn (fun ρ => |u (b * ρ)|) (Icc 0 1) :=
      (hu.comp (continuousOn_const.mul continuousOn_id) fun ρ hρ =>
        ⟨(hmem ρ hρ).1, (hmem ρ hρ).2.trans hT't.le⟩).abs
    refine h1.congr fun ρ hρ => ?_
    simp only
    rw [hR _ ⟨(hmem ρ hρ).1, (hmem ρ hρ).2.trans hT't.le⟩]
  have e : ∀ m : ℕ, (∃ r : ℚ, (r : ℝ) ∈ Icc (0 : ℝ) 1 ∧
      |FreS (b * r) (x, f)| < ε + 1 / ((m : ℝ) + 1)) ↔
      ∃ r : ℚ, (r : ℝ) ∈ Icc (0 : ℝ) 1 ∧ |realRevMap V (b * r) x| < ε + 1 / ((m : ℝ) + 1) :=
    fun m => exists_congr fun r => and_congr_right fun hr => by
      rw [FreS_eq hV hf hVf hl (hmem _ hr)]
  simp_rw [e]
  rw [← exists_le_iff_rat hg ε]
  constructor
  · rintro ⟨ρ, hρ, h⟩
    exact ⟨b * ρ, ⟨(hmem ρ hρ).1, mul_le_of_le_one_right hb hρ.2⟩, h⟩
  · rintro ⟨s, hs, h⟩
    rcases eq_or_lt_of_le hb with h0 | h0
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have : s = 0 := le_antisymm (h0 ▸ hs.2) hs.1
      rw [← h0, mul_zero, ← this]; exact h
    · refine ⟨s / b, ⟨div_nonneg hs.1 hb, (div_le_one h0).2 hs.2⟩, ?_⟩
      rw [mul_div_cancel₀ _ h0.ne']; exact h

/-- Paths starting at `0` for which `x` is live and negative at time `t`. -/
def liveW (t : ℝ) (ht : 0 ≤ t) : Set (C(Icc (0 : ℝ) t, ℝ) × ℝ) :=
  {p | p.1 ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ p.2 ∈ liveNeg (Wof 1 t ht p.1) t}

/-- **G1: the grid event** `{t_k < T, dyUp n σ_ε(x) = t_k, x live at t_k}` in `(x, (V^{t_k}, W⁰))`. -/
def gridSet (T ε : ℝ) (n k : ℕ) : Set (ℝ × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))) :=
  {q | tk n k < T ∧ (E4Meas.stopPath (tk n k) q.2.1, q.1) ∈ liveW (tk n k) (tk_nonneg n k) ∧
    HitM ε (tk n k) (q.1, q.2.1) ∧ ¬ HitM ε (tk n k - 1 / (2 : ℝ) ^ n) (q.1, q.2.1)}

theorem measurableSet_gridSet (T ε : ℝ) (n k : ℕ) : MeasurableSet (gridSet T ε n k) := by
  have hL : MeasurableSet {q : ℝ × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) |
      (E4Meas.stopPath (tk n k) q.2.1, q.1) ∈ liveW (tk n k) (tk_nonneg n k)} :=
    (M4.measurableSet_liveNeg_Wof _ _).preimage
      (((E4Meas.measurable_stopPath _).comp (measurable_fst.comp measurable_snd)).prodMk
        measurable_fst)
  have hq : Measurable fun q : ℝ × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) => (q.1, q.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have h1 := (measurableSet_hitM ε (tk n k)).preimage hq
  have h2 := ((measurableSet_hitM ε (tk n k - 1 / (2 : ℝ) ^ n)).preimage hq).compl
  unfold gridSet
  simp only [ofPred_and]
  exact (MeasurableSet.const _).inter (hL.inter (h1.inter h2))

/-- **G1.** Membership in the grid set, for a continuous driver agreeing with `d.1` on `[0,t_k]`. -/
theorem mem_gridSet_iff (hV : Continuous V) (hV0 : V 0 = 0)
    {d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)} (hd : Continuous d.1) {n k : ℕ}
    (hVd : EqOn V (fun s => d.1 s.toNNReal) (Icc 0 (tk n k))) (hT : 0 ≤ T) (hx : x ≤ 0) :
    (x, d) ∈ gridSet T ε n k ↔
      tk n k < T ∧ dyUp n (sigEps V T ε x) = tk n k ∧ IsLive V (tk n k) x := by
  have ht := tk_nonneg n k
  have hlw : (E4Meas.stopPath (tk n k) d.1, x) ∈ liveW (tk n k) ht ↔ IsLive V (tk n k) x := by
    have hW : EqOn (Wof 1 (tk n k) ht (E4Meas.stopPath (tk n k) d.1)) V (Icc 0 (tk n k)) :=
      fun s hs => (E4Meas.eqOn_Wof_stopPath ht hd hs).trans (hVd hs).symm
    have h0 : E4Meas.stopPath (tk n k) d.1 ⟨0, ⟨le_rfl, ht⟩⟩ = 0 := by
      rw [E4Meas.stopPath_apply hd]
      exact (hVd ⟨le_rfl, ht⟩).symm.trans hV0
    show (_ = 0 ∧ x ∈ liveNeg _ _) ↔ _
    rw [liveNeg_congr_drive (continuous_Wof 1 _ ht _) hV ht hW]
    refine ⟨fun h => h.2.2, fun h => ⟨h0, lt_of_le_of_ne hx fun e => ?_, h⟩⟩
    subst e
    exact not_isLive_zero hV0 _ h
  have hb : tk n k - 1 / (2 : ℝ) ^ n ≤ tk n k := by
    have : (0 : ℝ) < 1 / 2 ^ n := by positivity
    linarith
  simp only [gridSet, mem_ofPred_eq]
  constructor
  · rintro ⟨htT, hl, h1, h2⟩
    have hl' := hlw.1 hl
    rw [hitM_iff hV hd ht hVd hl' le_rfl] at h1
    rw [hitM_iff hV hd ht hVd hl' hb] at h2
    exact ⟨htT, (dyUp_sigEps_eq_iff hV hT n k htT).2 ⟨hl', h1, h2⟩⟩
  · rintro ⟨htT, h⟩
    obtain ⟨hl, h1, h2⟩ := (dyUp_sigEps_eq_iff hV hT n k htT).1 h
    exact ⟨htT, hlw.2 hl, (hitM_iff hV hd ht hVd hl le_rfl).2 h1,
      fun h' => h2 ((hitM_iff hV hd ht hVd hl hb).1 h')⟩

end E4Grid
end QuantumZipper
