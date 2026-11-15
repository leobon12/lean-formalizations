import InteractingSLE.Foundations.SLE.SpaceFilling
import InteractingSLE.Foundations.Loewner.YuanTrace
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.RS.TipA
import QuantumZipper.Proofs.Thm14.FromThm13

/-!
# The Markov step of [RS05, Lemma 7.3] for `κ > 8`

Packet `planning/packets/PROVE-RS05-74c.md`. [RS05] p. 33 (`SLEcont.tex` lines 2350–2366): "Striving
for a contradiction, we assume that for all `t > 0` a.s. `0 ∈ \overline{H_t}` … Conditioned on
`F_{t_0}`, the set `g_{t_0}(K_{t+t_0} \ K_{t_0})` has the same distribution as `K_t + ξ(t_0)`. It
therefore follows by our above assumption that a.s. `ξ(t_0) ∈ \overline{g_{t_0}(H_{t+t_0})}`.
Mapping by `g_{t_0}^{-1}`, this implies that a.s. `z_0 ∈ \overline{H_{t+t_0}}`."

[RS05] apply this at the random time `t_0 = τ(z_0)`; here it is applied at deterministic times
`s ≥ 0` only, where the shifted motion `B(s + ·) − B(s)` is again a Brownian motion, so no strong
Markov property is needed. "Mapping by `g_s^{-1}`" is the continuity of `F_s = g_s⁻¹(W_s + ·)` at
the tip: `F_s(w) → γ(s)` as `w → 0` in `ℍ` (`IsLoewnerTrace.tendsto_fwdMapInv_tip`, Carathéodory).
Countably many rational times and the continuity of the trace then give: under the assumption,
almost surely `γ(s) ∈ \overline{ℍ \ K_u}` for all `0 ≤ s < u`, i.e. the trace never leaves the
boundary of the later hulls (`ae_forall_trace_mem_closure_of_forall_measure_eq_zero`).

## Main results

* `isLoewnerTrace_of_traceGen`: the component form of the generation of the hulls
  (`QuantumZipper.Blueprint.RohdeSchrammTraceGen`) gives `IsLoewnerTrace` (filling form);
  `ae_isLoewnerTrace_of_eight_lt`.
* `ae_trace_mem_closure_of_forall_measure_eq_zero` (fixed time) and
  `ae_forall_trace_mem_closure_of_forall_measure_eq_zero` (all times).
* `ae_trace_inter_H_subset_of_forall_measure_eq_zero`: under the assumption,
  `γ([0,u)) ∩ ℍ ⊆ \overline{ℍ \ K_u} \ (ℍ \ K_u)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

/-! ### From the component form of trace generation to `IsLoewnerTrace` -/

/-- **Generation of the hulls, component form ⇒ filling form.** If `γ` is continuous on `[0,∞)`,
`γ 0 = 0`, and `ℍ \ K_t` is the component of `ℍ \ γ[0,t]` containing `M i` whenever `|γ| < M` on
`[0,t]`, then `K_t = fill(γ[0,t])` for every `t ≥ 0`. -/
theorem isLoewnerTrace_of_traceGen {W : ℝ → ℝ} {γ : ℝ → ℂ} (h0 : γ 0 = 0)
    (hc : ContinuousOn γ (Ici 0))
    (hgen : ∀ t : ℝ, 0 ≤ t → ∀ M : ℝ, (∀ s ∈ Icc 0 t, ‖γ s‖ < M) →
      H \ fwdHull W t = connectedComponentIn (H \ γ '' Icc 0 t) (M * Complex.I)) :
    IsLoewnerTrace W γ := by
  refine ⟨h0, hc, fun t ht => ?_⟩
  have hA : IsCompact (γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn (hc.mono Icc_subset_Ici_self)
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_ball 0).1 hA.isBounded
  set R : ℝ := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hAR : closure (γ '' Icc 0 t) ⊆ ball 0 R := by
    rw [hA.isClosed.closure_eq]
    exact hR₀.trans (ball_subset_ball (le_max_left _ _))
  have hM : ∀ s ∈ Icc 0 t, ‖γ s‖ < R + 1 := fun s hs => by
    have := hAR (subset_closure (mem_image_of_mem γ hs))
    rw [mem_ball_zero_iff] at this
    linarith
  have h1 := hgen t ht (R + 1) hM
  have h2 := H_diff_fillH hRpos hAR
  rw [hA.isClosed.closure_eq] at h2
  have hcast : ((R + 1 : ℝ) : ℂ) * Complex.I = (R + 1 : ℝ) * Complex.I := rfl
  rw [← h2] at h1
  ext z
  by_cases hz : z ∈ H
  · constructor
    · intro hzK
      by_contra hzF
      have : z ∈ H \ fillH (γ '' Icc 0 t) := ⟨hz, hzF⟩
      rw [← h1] at this
      exact this.2 hzK
    · intro hzF
      by_contra hzK
      have : z ∈ H \ fwdHull W t := ⟨hz, hzK⟩
      rw [h1] at this
      exact this.2 hzF
  · exact ⟨fun h => absurd h.1 hz, fun h => absurd h.1 hz⟩

/-- For `κ > 8`, almost surely the SLE trace is a continuous Loewner trace of its driver. -/
theorem ae_isLoewnerTrace_of_eight_lt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (drive κ B ω) (sleTrace κ B ω) := by
  filter_upwards [rohdeSchrammTraceGen_of_eight_lt hκ P B hB] with ω hg
  exact isLoewnerTrace_of_traceGen hg.1 hg.2.1 hg.2.2

/-! ### The Markov step at a fixed time -/

section Markov

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Deterministic core.** If `γ` is a Loewner trace of `W`, and the shifted chain `Wˢ` never
encloses a half-neighbourhood of its starting point up to time `t`, then `γ(s)` is a limit of
points of `ℍ \ K_{s+t}` (map the points of `ℍ \ K_t(Wˢ)` near `0` by `F_s`). -/
theorem trace_mem_closure_of_not_hullContainsHalfBall {W : ℝ → ℝ} {γ : ℝ → ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hγ : IsLoewnerTrace W γ) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hnot : ¬ HullContainsHalfBall (shiftDrive W s) t) :
    γ s ∈ closure (H \ fwdHull W (s + t)) := by
  have hWs : Continuous (shiftDrive W s) := continuous_shiftDrive hW s
  have hWs0 : shiftDrive W s 0 = 0 := QuantumZipper.RS.shiftDrive_zero W s
  have htip := hγ.tendsto_fwdMapInv_tip hW hW0 hs
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.tendsto_nhdsWithin_nhds.1 htip ε hε
  unfold HullContainsHalfBall at hnot
  push Not at hnot
  obtain ⟨z, hzH, hzδ, hzK⟩ := hnot δ hδ
  have hz : z ∈ H \ fwdHull (shiftDrive W s) t := ⟨hzH, hzK⟩
  rw [← image_fwdMapInv_H hWs hWs0 ht] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  refine ⟨fwdMapInv W s (fwdMapInv (shiftDrive W s) t v), ?_, ?_⟩
  · rw [← fwdMapInv_add_shift hW hW0 hs ht hv]
    exact fwdMapInv_mem_compl_fwdHull hW hW0 (by linarith) hv
  · rw [dist_comm]
    exact hδε hzH (by rwa [dist_zero_right])

/-- **The Markov step at a fixed time `s`** ([RS05] p. 33, at deterministic times). If for every
`t > 0` the hull `K_t` almost surely fails to contain a half-neighbourhood of `0`, then almost surely
`γ(s) ∈ \overline{ℍ \ K_{s+t}}` for every `t > 0`. -/
theorem ae_trace_mem_closure_of_forall_measure_eq_zero (hB : IsBrownianReal B P) {κ : ℝ}
    (hκ : 8 < κ) (hA : ∀ t > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t} = 0)
    (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ),
      sleTrace κ B ω s ∈ closure (H \ fwdHull (drive κ B ω) (s + t)) := by
  obtain ⟨hBs, -, hdrs⟩ := isBrownianReal_shift_indep hB κ s
  set Bs : ℝ≥0 → Ω → ℝ := fun u ω => B (s + u) ω - B s ω with hBsdef
  have hAs : ∀ n : ℕ, ∀ᵐ ω ∂P, ¬ HullContainsHalfBall (drive κ Bs ω) ((n : ℝ) + 1) := by
    intro n
    have h0 : P {ω | HullContainsHalfBall (drive κ Bs ω) ((n : ℝ) + 1)} = 0 := by
      rw [measure_hullContainsHalfBall_eq_of_isBrownianReal hBs hB κ (by positivity)]
      exact hA _ (by positivity)
    exact measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [ae_all_iff.2 hAs, ae_isLoewnerTrace_of_eight_lt hB hκ, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hn hγ hc h0
  intro t ht
  set W := drive κ B ω with hWdef
  have hW : Continuous W := drive_continuous hc
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  have hWs : Continuous (shiftDrive W s) := continuous_shiftDrive hW s
  have hBsc : Continuous fun u => Bs u ω := by
    simp only [hBsdef]
    exact (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hdc : Continuous (drive κ Bs ω) := drive_continuous hBsc
  refine trace_mem_closure_of_not_hullContainsHalfBall hW hW0 hγ s.2 ht.le fun hhalf => ?_
  obtain ⟨n, hn'⟩ := exists_nat_ge t
  have hmono : HullContainsHalfBall (shiftDrive W s) ((n : ℝ) + 1) := hhalf.mono (by linarith)
  have hK : fwdHull (drive κ Bs ω) ((n : ℝ) + 1) = fwdHull (shiftDrive W s) ((n : ℝ) + 1) :=
    Thm14FromThm13.fwdHull_eq_of_eqOn hdc hWs (by positivity) fun u hu => hdrs ω u hu.1
  apply hn n
  unfold HullContainsHalfBall at hmono ⊢
  rw [hK]
  exact hmono

/-- **The Markov step at all times.** Under the same assumption, almost surely
`γ(s) ∈ \overline{ℍ \ K_u}` for all `0 ≤ s < u` (rational times and continuity of `γ`). -/
theorem ae_forall_trace_mem_closure_of_forall_measure_eq_zero (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ) (hA : ∀ t > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t} = 0) :
    ∀ᵐ ω ∂P, ∀ s u : ℝ, 0 ≤ s → s < u →
      sleTrace κ B ω s ∈ closure (H \ fwdHull (drive κ B ω) u) := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), sleTrace κ B ω ((q : ℝ).toNNReal) ∈
      closure (H \ fwdHull (drive κ B ω) (((q : ℝ).toNNReal : ℝ) + t)) := fun q =>
    ae_trace_mem_closure_of_forall_measure_eq_zero hB hκ hA _
  filter_upwards [ae_all_iff.2 hq, ae_isLoewnerTrace_of_eight_lt hB hκ] with ω hω hγ
  intro s u hs hsu
  -- rationals `q_k ∈ (s, min u (s + 1/(k+1)))`
  have hex : ∀ k : ℕ, ∃ q : ℚ, s < q ∧ (q : ℝ) < min u (s + 1 / ((k : ℝ) + 1)) := fun k =>
    exists_rat_btwn (lt_min hsu (lt_add_of_pos_right s (by positivity)))
  choose q hq1 hq2 using hex
  have hmem : ∀ k, sleTrace κ B ω (q k) ∈ closure (H \ fwdHull (drive κ B ω) u) := by
    intro k
    have hq0 : (0 : ℝ) ≤ q k := hs.trans (hq1 k).le
    have h := hω (q k) (u - q k) (by linarith [(hq2 k).trans_le (min_le_left _ _)])
    rwa [Real.coe_toNNReal _ hq0, add_sub_cancel] at h
  have hlim : Tendsto (fun k => (q k : ℝ)) atTop (𝓝[Ici 0] s) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => hs.trans (hq1 k).le⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun k => (hq1 k).le) (fun k => (hq2 k).le.trans (min_le_right _ _))
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add s
    simpa using this
  have hcont := ((hγ.2.1 s hs).tendsto).comp hlim
  exact isClosed_closure.mem_of_tendsto hcont (Eventually.of_forall hmem)

/-- Under the assumption, almost surely every trace point of `ℍ` before time `u` lies on the
boundary of `ℍ \ K_u` and not in `ℍ \ K_u`. -/
theorem ae_trace_inter_H_subset_of_forall_measure_eq_zero (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 8 < κ) (hA : ∀ t > (0 : ℝ), P {ω | HullContainsHalfBall (drive κ B ω) t} = 0) :
    ∀ᵐ ω ∂P, ∀ u : ℝ, sleTrace κ B ω '' Ico 0 u ∩ H ⊆
      closure (H \ fwdHull (drive κ B ω) u) \ (H \ fwdHull (drive κ B ω) u) := by
  filter_upwards [ae_forall_trace_mem_closure_of_forall_measure_eq_zero hB hκ hA,
    ae_isLoewnerTrace_of_eight_lt hB hκ] with ω hω hγ
  rintro u _ ⟨⟨s, ⟨hs0, hsu⟩, rfl⟩, hsH⟩
  refine ⟨hω s u hs0 hsu, fun h => h.2 ?_⟩
  have hKs : sleTrace κ B ω s ∈ fwdHull (drive κ B ω) s := by
    rw [hγ.2.2 s hs0]
    exact ⟨hsH, Or.inl (subset_closure (mem_image_of_mem _ ⟨hs0, le_rfl⟩))⟩
  exact fwdHull_mono.1 hsu.le hKs

end Markov

end InteractingSLE
