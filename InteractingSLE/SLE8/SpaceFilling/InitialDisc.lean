import InteractingSLE.SLE8.SpaceFilling.Hit
import InteractingSLE.SLE8.SpaceFilling.ZeroArea
import InteractingSLE.Spec.Dimension.TraceBridge
import QuantumZipper.Proofs.Thm11.AddendumArea

/-!
# Space filling of SLE₈, §4: a neighbourhood of the starting point (Proposition 6)

Source: `source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §4, Proposition 6 ("almost
surely, for every `t > 0`, `0 ∉ \overline{D_t}`"; equivalently `B(0, r) ∩ ℍ ⊆ K_t` for some `r > 0`,
Theorem 1 (i); [RS05, Lemma 7.3] at `κ = 8`). Packet `planning/packets/PROVE-SF8-A.md`.

The zero-one half (scaling, nesting, Blumenthal) is landed: `hullContainsHalfBall_dichotomy`
(`Foundations/SLE/SpaceFilling.lean`). It remains to exclude `δ = 0`, i.e. `ℙ[E_t] = 0` for all
`t > 0`, `E_t = {B(0, r) ∩ ℍ ⊆ K_t for some r > 0}`.

**Deviation from the note's proof (recorded in the handoff).** The note applies the domain Markov
property (1.2) at the random time `σ_z` (first hitting time of `z`), which needs the strong Markov
property, measurability of `σ_z`, and (L1) at a stopping time. We apply (1.2) only at deterministic
rational times `q`, where it needs no independence at all: `B(q + ·) − B(q)` is a Brownian motion,
so (under `δ = 0`) almost surely its hulls `K̃_s` never contain a half-neighbourhood of `0`; points
`w ∈ ℍ \ K̃_s` close to `0` are mapped by `F_q` into `ℍ \ K_{q+s}` (flow identity
`RS.fwdMapInv_add_shift`) and close to `γ(q)` (the tip, `IsLoewnerTrace.tendsto_fwdMapInv_tip`,
which is (L1) at the deterministic time `q`). Hence `γ(q) ∈ \overline{D_t}` for all `t`, for all
rational `q`, and by continuity `γ[0, t] ∩ ℍ ⊆ ∂D_t` for every `t`. By Proposition 5 at integer
times (PROVE-SF8-B), `γ[0, ∞) ∩ ℍ` then has zero area almost surely, while by Lemma 2 each
`z ∈ ℍ` is on `γ[0, ∞)` almost surely; Tonelli gives the contradiction, exactly as in the note.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8

open QuantumZipper QuantumZipper.RS

/-! ### The deterministic step -/

section Deterministic

variable {W : ℝ → ℝ}

/-- The event of Lemma 7.3 only depends on the hull. -/
theorem hullContainsHalfBall_congr {W' : ℝ → ℝ} {t : ℝ} (h : fwdHull W t = fwdHull W' t) :
    HullContainsHalfBall W t ↔ HullContainsHalfBall W' t := by
  unfold HullContainsHalfBall
  rw [h]

/-- **Flow step (1.2) at a deterministic time.** `F_q` maps `ℍ \ K̃_s`, the domain of the chain
driven by `W(q + ·) − W(q)`, into `ℍ \ K_{q+s}`. -/
theorem fwdMapInv_mem_compl_fwdHull_add (hW : Continuous W) (hW0 : W 0 = 0) {q s : ℝ}
    (hq : 0 ≤ q) (hs : 0 ≤ s) {w : ℂ} (hw : w ∈ H \ fwdHull (shiftDrive W q) s) :
    fwdMapInv W q w ∈ H \ fwdHull W (q + s) := by
  rw [← image_fwdMapInv_H (continuous_shiftDrive hW q) (shiftDrive_zero W q) hs] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [← fwdMapInv_add_shift hW hW0 hq hs hv]
  exact fwdMapInv_mem_compl_fwdHull hW hW0 (add_nonneg hq hs) hv

/-- If the hulls of the chain driven by `W(q + ·) − W(q)` never contain a half-neighbourhood of
`0`, the trace point `η(q)` lies in the closure of every domain `ℍ \ K_t`. -/
theorem mem_closure_compl_fwdHull_of_not_hullContainsHalfBall {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hnot : ∀ n : ℕ, ¬ HullContainsHalfBall (shiftDrive W q) n) {t : ℝ} :
    η q ∈ closure (H \ fwdHull W t) := by
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hsub : H \ fwdHull W (q + n) ⊆ H \ fwdHull W t :=
    sdiff_subset_sdiff_right ((QuantumZipper.fwdHull_mono (W := W)).1 (by linarith))
  have hex : ∀ k : ℕ, ∃ w ∈ H \ fwdHull (shiftDrive W q) n, ‖w‖ < 1 / ((k : ℝ) + 1) := by
    intro k
    by_contra hcon
    push Not at hcon
    refine hnot n ⟨1 / ((k : ℝ) + 1), by positivity, fun z hz hzε => ?_⟩
    by_contra hzK
    exact (not_le.2 hzε) (hcon z ⟨hz, hzK⟩)
  choose w hw hwn using hex
  have hwt : Tendsto w atTop (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => (hw k).1⟩
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hwn k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := (hη.tendsto_fwdMapInv_tip hW hW0 hq).comp hwt
  exact mem_closure_of_tendsto hlim (Eventually.of_forall fun k =>
    hsub (fwdMapInv_mem_compl_fwdHull_add hW hW0 hq n.cast_nonneg (hw k)))

/-- If this holds at every nonnegative rational time, then by continuity every trace point `η(s)`
lies in the closure of every domain `ℍ \ K_t`. -/
theorem trace_mem_closure_compl_fwdHull {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0)
    (hnot : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ n : ℕ, ¬ HullContainsHalfBall (shiftDrive W q) n)
    {s : ℝ} (hs : 0 ≤ s) {t : ℝ} :
    η s ∈ closure (H \ fwdHull W t) := by
  have hex : ∀ k : ℕ, ∃ q : ℚ, s < q ∧ (q : ℝ) < s + 1 / ((k : ℝ) + 1) := fun k =>
    exists_rat_btwn (lt_add_of_pos_right s (by positivity))
  choose q hq1 hq2 using hex
  have hqt : Tendsto (fun k => (q k : ℝ)) atTop (𝓝[Ici 0] s) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k =>
      mem_Ici.2 (hs.trans (hq1 k).le)⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun k => (hq1 k).le) (fun k => (hq2 k).le)
    simpa using (tendsto_const_nhds (x := s)).add tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := ((hη.2.1 s (mem_Ici.2 hs)).tendsto).comp hqt
  exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall fun k =>
    mem_closure_compl_fwdHull_of_not_hullContainsHalfBall hη hW hW0
      (hs.trans (hq1 k).le) (hnot (q k) (hs.trans (hq1 k).le)))

/-- Consequently every point of `η[0, t]` in `ℍ` is a boundary point of `ℍ \ K_t`. -/
theorem image_Icc_inter_H_subset_frontier {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0)
    (hnot : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ n : ℕ, ¬ HullContainsHalfBall (shiftDrive W q) n)
    {t : ℝ} (ht : 0 ≤ t) :
    η '' Icc 0 t ∩ H ⊆ frontier (H \ fwdHull W t) := by
  rintro p ⟨⟨s, hs, rfl⟩, hpH⟩
  rw [(FwdHolo.isOpen_compl_fwdHull hW ht).frontier_eq]
  refine ⟨trace_mem_closure_compl_fwdHull hη hW hW0 hnot hs.1, fun hp => hp.2 ?_⟩
  rw [hη.2.2 t ht]
  exact ⟨hpH, Or.inl (subset_closure ⟨s, hs, rfl⟩)⟩

end Deterministic

/-! ### Proposition 6 -/

section Prop6

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Domain Markov step at rational times, under `δ = 0`.** If the event of Lemma 7.3 has
probability zero at every time, then almost surely, for every nonnegative rational `q`, the hulls of
the chain driven by `W(q + ·) − W(q)` never contain a half-neighbourhood of `0`
(`B(q + ·) − B(q)` is a Brownian motion, and the probability is a law quantity). -/
theorem ae_forall_rat_not_hullContainsHalfBall_shift (hB : IsBrownianReal B P)
    (h0 : ∀ t > (0 : ℝ), P {ω | HullContainsHalfBall (drive 8 B ω) t} = 0) :
    ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ n : ℕ,
      ¬ HullContainsHalfBall (shiftDrive (drive 8 B ω) q) n := by
  rw [ae_all_iff]
  intro q
  by_cases hq0 : 0 ≤ (q : ℝ)
  · set q' : ℝ≥0 := ⟨q, hq0⟩ with hq'
    have hBq := hB.shift q'
    have hnull : ∀ n : ℕ, P {ω | HullContainsHalfBall
        (drive 8 (fun t ω => B (q' + t) ω - B q' ω) ω) ((n : ℝ) + 1)} = 0 := fun n => by
      rw [measure_hullContainsHalfBall_eq_of_isBrownianReal hBq hB 8 (by positivity)]
      exact h0 _ (by positivity)
    have hae : ∀ᵐ ω ∂P, ∀ n : ℕ, ¬ HullContainsHalfBall
        (drive 8 (fun t ω => B (q' + t) ω - B q' ω) ω) ((n : ℝ) + 1) :=
      ae_all_iff.2 fun n => measure_eq_zero_iff_ae_notMem.1 (hnull n)
    filter_upwards [hae] with ω hω _ n hn
    have hfw : fwdHull (drive 8 (fun t ω => B (q' + t) ω - B q' ω) ω) ((n : ℝ) + 1) =
        fwdHull (shiftDrive (drive 8 B ω) q) ((n : ℝ) + 1) :=
      fwdHull_eq_of_eqOn (by positivity) (lt_add_one _) fun r hr =>
        drive_shift 8 B q' ω hr.1
    exact hω n ((hullContainsHalfBall_congr hfw).2
      (HullContainsHalfBall.mono hn (by linarith)))
  · exact ae_of_all _ fun _ h => absurd h hq0

/-- **Under `δ = 0`, the trace runs on the boundaries of the domains**: almost surely, for every
`t ≥ 0`, `γ[0, t] ∩ ℍ ⊆ ∂(ℍ \ K_t)`. -/
theorem ae_image_Icc_inter_H_subset_frontier_of_forall_measure_eq_zero (hB : IsBrownianReal B P)
    (h0 : ∀ t > (0 : ℝ), P {ω | HullContainsHalfBall (drive 8 B ω) t} = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      sleTrace 8 B ω '' Icc 0 t ∩ H ⊆ frontier (H \ fwdHull (drive 8 B ω) t) := by
  filter_upwards [ae_forall_rat_not_hullContainsHalfBall_shift hB h0,
    ae_isLoewnerTrace_sleTrace_eight hB, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hnot hη hc h0' t ht
  exact image_Icc_inter_H_subset_frontier hη (drive_continuous hc) (drive_zero h0') hnot ht

/-- **`δ = 0` is impossible** (the contradiction in the proof of Proposition 6), for a Brownian
motion on a probability space in `Type`: by Proposition 5 the set `γ[0, ∞) ∩ ℍ` would have zero
area almost surely, while by Lemma 2 each `z ∈ ℍ` lies on it almost surely; Tonelli. -/
theorem exists_measure_hullContainsHalfBall_eight_ne_zero_of_type {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ t₀ > (0 : ℝ), P {ω | HullContainsHalfBall (drive 8 B ω) t₀} ≠ 0 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  by_contra hcon
  push Not at hcon
  -- a.s. the trace in `ℍ` has zero area
  have hnull : ∀ᵐ ω ∂P, volume (sleTrace 8 B ω '' Ici 0 ∩ H) = 0 := by
    have hP5 : ∀ᵐ ω ∂P, ∀ n : ℕ, volume (frontier (H \ fwdHull (drive 8 B ω) n)) = 0 :=
      ae_all_iff.2 fun n => SpaceFilling.ae_volume_frontier_eq_zero hB n.cast_nonneg
    filter_upwards [ae_image_Icc_inter_H_subset_frontier_of_forall_measure_eq_zero hB hcon, hP5]
      with ω h1 h2
    refine measure_mono_null (t := ⋃ n : ℕ, frontier (H \ fwdHull (drive 8 B ω) n)) ?_
      (measure_iUnion_null h2)
    rintro p ⟨⟨s, hs, rfl⟩, hpH⟩
    obtain ⟨n, hn⟩ := exists_nat_ge s
    exact mem_iUnion.2 ⟨n, h1 n n.cast_nonneg ⟨⟨s, ⟨hs, hn⟩, rfl⟩, hpH⟩⟩
  -- a measurable continuous version of the trace
  have hgood : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => sleTrace 8 B ω t) ∧ ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun y : ℝ => fwdMapInv (drive 8 B ω) t (y * I)) (𝓝[>] 0)
        (𝓝 (trace (drive 8 B ω) t)) :=
    (ae_exists_continuous_trace hB).mono fun _ ⟨_, h1, h2, _⟩ =>
      trace_good_of_tendstoLocallyUniformly h1 h2
  obtain ⟨η, hηm, hηc, hηeq⟩ := exists_measurable_sleTrace_of_tendsto hB hgood
  have himg : ∀ᵐ ω ∂P, η ω '' Ici 0 = sleTrace 8 B ω '' Ici 0 :=
    hηeq.mono fun ω h => h.image_eq
  set S := {p : Ω × ℂ | p.2 ∈ η p.1 '' Ici 0} ∩ {p : Ω × ℂ | p.2 ∈ H} with hSdef
  have hS : MeasurableSet S := (Thm11Area.measurableSet_mem_image_Ici hηm hηc).inter
    (measurable_snd isOpen_H.measurableSet)
  have h1 : (P.prod volume) S = 0 := by
    rw [Measure.prod_apply hS]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hnull, himg] with ω h hi
    have e : Prod.mk ω ⁻¹' S = sleTrace 8 B ω '' Ici 0 ∩ H := by
      ext z
      simp only [hSdef, mem_preimage, mem_inter_iff, mem_ofPred_eq, hi]
    rw [e, h]
  have hpt : ∀ z ∈ H, P ((fun ω => (ω, z)) ⁻¹' S) = 1 := by
    intro z hz
    have hm : MeasurableSet ((fun ω => (ω, z)) ⁻¹' S) := measurable_prodMk_right hS
    have hae : ∀ᵐ ω ∂P, ω ∈ (fun ω => (ω, z)) ⁻¹' S := by
      filter_upwards [ae_mem_sleTrace_image_eight hB hz, himg] with ω h hi
      exact ⟨by rw [mem_ofPred_eq, hi]; exact h, hz⟩
    exact (prob_compl_eq_zero_iff hm).1 (ae_iff.1 hae)
  have h2 : 0 < (P.prod volume) S := by
    rw [Measure.prod_apply_symm hS]
    calc (0 : ℝ≥0∞) < volume H :=
          isOpen_H.measure_pos volume ⟨I, show (0 : ℝ) < I.im by simp⟩
      _ = ∫⁻ z, H.indicator 1 z := (lintegral_indicator_one isOpen_H.measurableSet).symm
      _ ≤ ∫⁻ z, P ((fun ω => (ω, z)) ⁻¹' S) := lintegral_mono fun z => by
          by_cases hz : z ∈ H
          · rw [indicator_of_mem hz, hpt z hz]
            rfl
          · rw [indicator_of_notMem hz]
            exact zero_le
  exact absurd h1 h2.ne'

/-- **Proposition 6** ([RS05, Lemma 7.3] at `κ = 8`; Theorem 1 (i) of the note). For a Brownian
motion `B` and `W = √8 B`, almost surely, for every `t > 0` there is `r > 0` with
`B(0, r) ∩ ℍ ⊆ K_t`. -/
theorem ae_forall_sleHull_halfBall_eight (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ sleHull 8 B ω t := by
  obtain ⟨G, hGm, hGc, -, hGbr, -⟩ := exists_good_version0 hB
  have hcan : IsBrownianReal canonBM (P.map (toCPath G hGc)) :=
    isBrownianReal_canonBM hGbr.toIsPreBrownianReal hGm hGc
  exact ae_forall_sleHull_halfBall_of_measure_ne_zero hB 8
    (exists_measure_hullContainsHalfBall_ne_zero_of hcan hB
      (exists_measure_hullContainsHalfBall_eight_ne_zero_of_type hcan))

/-- **Proposition 6**, the event of [RS05, Lemma 7.3] at `κ = 8`: almost surely every hull `K_t`,
`t > 0`, contains a half-neighbourhood of `0`. -/
theorem ae_forall_hullContainsHalfBall_eight (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), HullContainsHalfBall (drive 8 B ω) t :=
  ae_forall_sleHull_halfBall_eight hB

/-- **Proposition 6, the note's form**: almost surely, for every `t > 0`, `0 ∉ \overline{D_t}`,
`D_t = ℍ \ K_t`. -/
theorem ae_forall_zero_not_mem_closure_eight (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), (0 : ℂ) ∉ closure (H \ sleHull 8 B ω t) := by
  filter_upwards [ae_forall_sleHull_halfBall_eight hB] with ω h t ht h0
  obtain ⟨ε, hε, hball⟩ := h t ht
  obtain ⟨w, hw, hwε⟩ := Metric.mem_closure_iff.1 h0 ε hε
  rw [dist_zero_left] at hwε
  exact hw.2 (hball w hw.1 hwε)

end Prop6

end InteractingSLE.SLE8
