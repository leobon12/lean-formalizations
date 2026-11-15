import InteractingSLE.SLE8.SpaceFilling.HitMart
import InteractingSLE.Foundations.SLE.SpaceFilling
import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Frozen.SLE8.ContinuousTrace
import InteractingSLE.SLE8.SpaceFilling.ZeroAreaDet

/-!
# Space filling of SLE₈, §2: every deterministic interior point is hit (Lemma 2)

Source: `source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §2, Lemma 2. Packet
`planning/packets/PROVE-SF8-A.md`.

**Lemma 2.** For each deterministic `z ∈ ℍ`, `ℙ{τ_z < ∞, γ(τ_z) = z} = 1`; consequently the trace is
almost surely dense in `ℍ`.

Here `τ_z = swallowTime W z` is the maximal lifetime of `z` in `ℍ` and `γ = sleTrace 8 B ω` is the
canonical radial limit `γ(t) = lim_{y ↓ 0} F_t(iy)`, which is a continuous Loewner trace by the
proved SLE₈ anchor `InteractingSLE.SLE8.ae_exists_continuous_trace`
(`ae_isLoewnerTrace_sleTrace_eight`).

The two probabilistic inputs are in `HitMart.lean`: `τ_z < ∞` (`ae_exists_mem_fwdHull_eight`) and
`Υ_t(z) → 0` before `τ_z` (`ae_exists_fwdLogCR_lt_eight`). The geometric step is the note's: by the
Schwarz lemma `dist(z, ∂D_t) ≤ 2 Υ_t` ((2.5), `le_two_mul_exp_fwdLogCR`), boundary points of `D_t`
in `ℍ` lie on `γ[0, t]` ((L2), `exists_mem_image_ball_of_not_subset`), so `z` lies in the compact
set `γ[0, τ_z]`, and it is not on `γ[0, s]` for `s < τ_z` since `z ∉ K_s`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8

open QuantumZipper QuantumZipper.RS QuantumZipper.FwdClock

/-! ### The SLE₈ trace is a continuous Loewner trace -/

section Deterministic

variable {W : ℝ → ℝ}

/-- `IsLoewnerTrace` only depends on the trace on `[0, ∞)`. -/
theorem isLoewnerTrace_congr {η η' : ℝ → ℂ} (h : EqOn η η' (Ici 0))
    (hη : IsLoewnerTrace W η) : IsLoewnerTrace W η' := by
  obtain ⟨h0, hc, hK⟩ := hη
  refine ⟨(h (mem_Ici.2 le_rfl)).symm.trans h0, hc.congr fun s hs => (h hs).symm,
    fun t ht => ?_⟩
  rw [hK t ht, (h.mono Icc_subset_Ici_self).image_eq]

/-- The conclusion of the SLE₈ anchor at one sample point makes the canonical trace `trace W` a
continuous Loewner trace (`IsLoewnerTrace`: `K_t` is the filling of `γ[0, t]`); PROVE-SF8-B's
`SpaceFilling.isLoewnerTrace_of_connectedComponentIn` gives it for `s ↦ γ s.toNNReal`, which is
the canonical trace on `[0, ∞)`. -/
theorem isLoewnerTrace_trace_of_tendstoLocallyUniformly {γ : ℝ≥0 → ℂ}
    (hγu : TendstoLocallyUniformly (fun (y : ℝ) (t : ℝ≥0) => fwdMapInv W t (y * I)) γ (𝓝[>] 0))
    (hγc : Continuous γ) (hγ0 : γ 0 = 0)
    (hgen : ∀ t : ℝ≥0, (∃ z ∈ H \ fwdHull W t,
        connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull W t) ∧
      ¬ Bornology.IsBounded (H \ fwdHull W t)) :
    IsLoewnerTrace W (trace W) :=
  isLoewnerTrace_congr (fun s hs => by
      rw [← trace_eq_of_tendstoLocallyUniformly hγu, Real.coe_toNNReal _ (mem_Ici.1 hs)])
    (SpaceFilling.isLoewnerTrace_of_connectedComponentIn hγc hγ0 hgen)

/-- **Density from a small conformal radius, up to a finite time** (variant of
`InteractingSLE.mem_closure_image_of_fwdLogCR`). If `ℍ \ K_t` is a connected component of
`ℍ \ η[0, t]` for `t ≤ T`, and the conformal radius `Υ_t(a)` gets arbitrarily small at times
`t ≤ T` with `a ∉ K_t`, then `a ∈ \overline{η[0, T]}`. -/
theorem mem_closure_image_Icc_of_fwdLogCR {η : ℝ → ℂ} (hW : Continuous W) {T : ℝ}
    (hηc : ContinuousOn η (Icc 0 T))
    (hgen : ∀ t ∈ Icc (0 : ℝ) T,
      ∃ z ∈ H \ fwdHull W t, connectedComponentIn (H \ η '' Icc 0 t) z = H \ fwdHull W t)
    {a : ℂ} (ha : 0 < a.im)
    (hsmall : ∀ ε > (0 : ℝ), ∃ t ∈ Icc (0 : ℝ) T, a ∉ fwdHull W t ∧
      fwdLogCR W t a < Real.log ε) :
    a ∈ closure (η '' Icc 0 T) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set ρ := min ε a.im with hρ
  have hρ0 : 0 < ρ := lt_min hε ha
  obtain ⟨t, ht, haK, hL⟩ := hsmall (ρ / 2) (by positivity)
  have hρH : ball a ρ ⊆ H := fun w hw => by
    rw [mem_ball, Complex.dist_eq] at hw
    have h1 : |(w - a).im| ≤ ‖w - a‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h1
    have : ρ ≤ a.im := min_le_right _ _
    show 0 < w.im
    linarith [neg_abs_le (w.im - a.im)]
  have hnot : ¬ ball a ρ ⊆ H \ fwdHull W t := fun hsub => by
    have h1 := le_two_mul_exp_fwdLogCR hW ht.1 hρ0 hsub
    have h2 : Real.exp (fwdLogCR W t a) < ρ / 2 := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < ρ / 2)]
      exact Real.exp_lt_exp.2 hL
    linarith
  obtain ⟨s, hs, hsB⟩ := exists_mem_image_ball_of_not_subset
    (hηc.mono (Icc_subset_Icc_right ht.2)) (hgen t ht) hW ht.1 ⟨ha, haK⟩ hρH hnot
  refine ⟨η s, ⟨s, ⟨hs.1, hs.2.trans ht.2⟩, rfl⟩, ?_⟩
  rw [mem_ball] at hsB
  rw [dist_comm]
  exact hsB.trans_le (min_le_left _ _)

/-- **Lemma 2, deterministic part.** Along a continuous Loewner trace `η`, if `a ∈ ℍ` is swallowed
at some finite time and its conformal radius becomes arbitrarily small before it is swallowed, then
`τ_a < ∞` and `η(τ_a) = a`. -/
theorem swallowTime_lt_top_and_eq_of_isLoewnerTrace {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) {a : ℂ} (ha : 0 < a.im) {n : ℝ} (hn : a ∈ fwdHull W n)
    (hsmall : ∀ ε > (0 : ℝ), ∃ t ≥ (0 : ℝ), a ∉ fwdHull W t ∧ fwdLogCR W t a < Real.log ε) :
    swallowTime W a < ⊤ ∧ η (swallowTime W a).toReal = a := by
  have hlt : swallowTime W a < ⊤ := lt_of_le_of_lt hn.2 ENNReal.ofReal_lt_top
  refine ⟨hlt, ?_⟩
  set τ := (swallowTime W a).toReal with hτ
  have hτeq : swallowTime W a = ENNReal.ofReal τ := (ENNReal.ofReal_toReal hlt.ne).symm
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hlt_of : ∀ t, 0 ≤ t → a ∉ fwdHull W t → t < τ := fun t ht h => by
    have h1 : ENNReal.ofReal t < swallowTime W a := by
      by_contra hc
      exact h ⟨ha, not_lt.1 hc⟩
    rw [hτeq] at h1
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).1 h1
  have hcpt : ∀ t, IsCompact (η '' Icc 0 t) := fun t =>
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono Icc_subset_Ici_self)
  have hgen : ∀ t ∈ Icc (0 : ℝ) τ,
      ∃ z ∈ H \ fwdHull W t, connectedComponentIn (H \ η '' Icc 0 t) z = H \ fwdHull W t :=
    fun t ht => ((fillH_eq_iff_isFilling_of_isClosed (hcpt t).isBounded (hcpt t).isClosed
      (QuantumZipper.fwdHull_mono.2 _)).2 (hη.2.2 t ht.1)).1
  have hcl := mem_closure_image_Icc_of_fwdLogCR hW (hη.2.1.mono Icc_subset_Ici_self) hgen ha
    fun ε hε => by
      obtain ⟨t, ht, haK, hL⟩ := hsmall ε hε
      exact ⟨t, ⟨ht, (hlt_of t ht haK).le⟩, haK, hL⟩
  rw [(hcpt τ).isClosed.closure_eq] at hcl
  obtain ⟨s, hs, hsa⟩ := hcl
  rcases hs.2.lt_or_eq with hsτ | hsτ
  · exfalso
    have hmem : a ∈ fwdHull W s := by
      rw [hη.2.2 s hs.1]
      exact ⟨ha, Or.inl (subset_closure ⟨s, ⟨hs.1, le_rfl⟩, hsa⟩)⟩
    have h1 : ENNReal.ofReal τ ≤ ENNReal.ofReal s := hτeq ▸ hmem.2
    have h2 := (ENNReal.ofReal_le_ofReal_iff hs.1).1 h1
    linarith
  · rw [← hsτ]
    exact hsa

end Deterministic

/-! ### Lemma 2 -/

section Lemma2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For a Brownian motion, almost surely the canonical SLE₈ trace is a continuous Loewner trace
(from the proved SLE₈ anchor `ae_exists_continuous_trace`). -/
theorem ae_isLoewnerTrace_sleTrace_eight (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (drive 8 B ω) (sleTrace 8 B ω) := by
  filter_upwards [ae_exists_continuous_trace hB] with ω h
  obtain ⟨γ, hγu, hγc, -, hγ0, hgen⟩ := h
  exact isLoewnerTrace_trace_of_tendstoLocallyUniformly hγu hγc hγ0 hgen

/-- **Lemma 2 (every deterministic interior point is hit).** For a Brownian motion `B`,
`W = √8 B`, and a deterministic `z ∈ ℍ`, almost surely the maximal lifetime `τ_z` of `z` is finite
and the canonical SLE₈ trace satisfies `γ(τ_z) = z`. -/
theorem ae_swallowTime_lt_top_and_sleTrace_eq (hB : IsBrownianReal B P) {z : ℂ} (hz : z ∈ H) :
    ∀ᵐ ω ∂P, swallowTime (drive 8 B ω) z < ⊤ ∧
      sleTrace 8 B ω (swallowTime (drive 8 B ω) z).toReal = z := by
  filter_upwards [ae_isLoewnerTrace_sleTrace_eight hB, ae_exists_mem_fwdHull_eight hB hz,
    ae_exists_fwdLogCR_lt_eight hB hz, hB.cont] with ω hη hn hsmall hc
  obtain ⟨n, hn⟩ := hn
  exact swallowTime_lt_top_and_eq_of_isLoewnerTrace hη (drive_continuous hc) hz hn hsmall

/-- Each deterministic `z ∈ ℍ` lies almost surely on the SLE₈ trace `γ[0, ∞)`. -/
theorem ae_mem_sleTrace_image_eight (hB : IsBrownianReal B P) {z : ℂ} (hz : z ∈ H) :
    ∀ᵐ ω ∂P, z ∈ sleTrace 8 B ω '' Ici 0 := by
  filter_upwards [ae_swallowTime_lt_top_and_sleTrace_eq hB hz] with ω h
  exact ⟨_, ENNReal.toReal_nonneg, h.2⟩

/-- **Lemma 2, consequence: the SLE₈ trace is almost surely dense in `ℍ`.** -/
theorem ae_H_subset_closure_sleTrace_eight (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, H ⊆ closure (sleTrace 8 B ω '' Ici 0) := by
  have hden : ∀ᵐ ω ∂P, ∀ m : ℕ, TopologicalSpace.denseSeq ℂ m ∈ H →
      TopologicalSpace.denseSeq ℂ m ∈ closure (sleTrace 8 B ω '' Ici 0) := by
    rw [ae_all_iff]
    intro m
    by_cases hm : TopologicalSpace.denseSeq ℂ m ∈ H
    · exact (ae_mem_sleTrace_image_eight hB hm).mono fun _ h _ => subset_closure h
    · exact ae_of_all _ fun _ h => absurd h hm
  filter_upwards [hden] with ω h
  exact subset_closure_of_denseSeq h

end Lemma2

end InteractingSLE.SLE8
