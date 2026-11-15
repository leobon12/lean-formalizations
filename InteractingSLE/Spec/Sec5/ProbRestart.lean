/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.ProbRestartCrossing

/-!
# Lemma 5.10 at a stopping time: the conditional crossing estimate

Packet PROVE-RESTART (specification §5.2, proof of Proposition 5.9: at the start of each even stage the
crossing event has conditional probability at least `p₀` given the past).

`crossing_lower_bound_restart`: fix `κ > 0`, `C` and a compact `J ⊂ (−2, ∞)`, and let `p₀ = p₀(κ, C, J)`.
For every integrated `SLE_κ(ρ_L; ρ_R)` evolution, every finite stopping time `T` of its filtration and every
`A ∈ 𝓕_T` with `T < ζ` on `A` such that, almost surely on `A`, the process restarted at `T` is defined
through `τ ∧ 1` (`τ` its exit time from `(−1, 1)`) and its remaining drift is bounded by `C` before `τ ∧ 1`,

  `ℙ[A ∩ {|W_{T+t} − W_T| < 1 for all t < 1}] ≥ p₀ ℙ[A]`,

that is, `ℙ[crossing after T | 𝓕_T] ≥ p₀` almost surely on the event where the hypotheses hold.

Proof: restart at `T` under `P[·|A]` (`Sec2.Restart.exists_restart`) and apply the random-start crossing
estimate `crossing_lower_bound_from` to the restarted evolution. The remaining drift `U` depends only on
the gaps `W − V`, so it is the same for the restarted and the original process.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

variable {nL nR : ℕ}

/-- The remaining drift depends only on the gaps `w − v`. -/
theorem otherDrift_sub (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (w c : ℝ) (vL : Fin nL → ℝ)
    (vR : Fin (nR + 1) → ℝ) :
    otherDrift ρL ρR (w - c) (fun i => vL i - c) (fun i => vR i - c) = otherDrift ρL ρR w vL vR := by
  simp only [otherDrift, sub_sub_sub_cancel_right]

/-- If the restarted path is defined through `τ ∧ 1` whenever it agrees with the shifted path, then it
is defined through `τ ∧ 1`: a first failure time `t₀ = ζ − T ≤ t` would be a time before which the two
paths agree. -/
theorem lt_lifetime_of_restart {W' : ℝ≥0 → ℝ} {w : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    (hid : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → W' t = w t)
    (hlife : ∀ t : ℝ≥0, t ≤ 1 → (∀ u < t, |w u| < 1) → (t : ℝ≥0∞) < L) {t : ℝ≥0} (ht : t ≤ 1)
    (hW : ∀ u < t, |W' u| < 1) : (t : ℝ≥0∞) < L := by
  by_contra hnot
  push Not at hnot
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hnot
  set t₀ : ℝ≥0 := L.toNNReal with ht₀
  have hL : (t₀ : ℝ≥0∞) = L := ENNReal.coe_toNNReal hLtop
  have ht₀t : t₀ ≤ t := by
    rw [← ENNReal.coe_le_coe, hL]; exact hnot
  have := hlife t₀ (ht₀t.trans ht) fun u hu => by
    have huL : (u : ℝ≥0∞) < L := by rw [← hL]; exact_mod_cast hu
    rw [← hid u huL]
    exact hW u (hu.trans_le ht₀t)
  rw [hL] at this
  exact lt_irrefl _ this

/-- **Lemma 5.10 at a stopping time** (the conditional crossing estimate that Proposition 5.9 uses).
Fix `κ > 0`, `C`, and a compact `J ⊂ (−2, ∞)`; the constant `p₀ > 0` is that of
`crossing_lower_bound_from`. For every integrated `SLE_κ(ρ_L; ρ_R)` evolution (at least one right force
point, first right weight in `J`), every finite stopping time `T`, and every `A ∈ 𝓕_T` with `T < ζ` on `A`
such that almost surely on `A` the restarted process is defined through `τ ∧ 1` and its remaining drift
`U` is bounded by `C` before `τ ∧ 1`:
`p₀ ℙ[A] ≤ ℙ[A ∩ {|W_{T+t} − W_T| < 1 for all t < 1}]`. -/
theorem crossing_lower_bound_restart {κ C : ℝ} (hκ : 0 < κ) {J : Set ℝ} (hJ : IsCompact J)
    (hJ2 : J ⊆ Set.Ioi (-2)) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) {nL nR : ℕ} (xL : Fin nL → ℝ)
      (xR : Fin (nR + 1) → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
      (A : Set Ω),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → ρR 0 ∈ J →
      MeasurableSet[hT.measurableSpace] A → (∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω) →
      (∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ≥0, t ≤ 1 → (∀ u < t, |W (T ω + u) ω - W (T ω) ω| < 1) →
        ((T ω + t : ℝ≥0) : ℝ≥0∞) < ζ ω) →
      (∀ᵐ ω ∂P, ω ∈ A → ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → r.toNNReal ≤ 1 →
        (∀ u < r.toNNReal, |W (T ω + u) ω - W (T ω) ω| < 1) →
        |otherDrift ρL ρR (W (T ω + r.toNNReal) ω) (fun i => VL i (T ω + r.toNNReal) ω)
          (fun i => VR i (T ω + r.toNNReal) ω)| ≤ C) →
      p₀ * P.real A ≤
        P.real (A ∩ {ω | ∀ t : ℝ≥0, t < 1 → |W (T ω + t) ω - W (T ω) ω| < 1}) := by
  obtain ⟨p₀, hp₀, hcross⟩ := crossing_lower_bound_from (C := C) hκ hJ hJ2
  refine ⟨p₀, hp₀, ?_⟩
  intro Ω mΩ P hP 𝓕 nL nR xL xR ρL ρR W VL VR B ζ T hT A hE hρJ hA hAζ hlife hU
  by_cases hPA : P A = 0
  · rw [measureReal_def, hPA, ENNReal.toReal_zero, mul_zero]
    exact measureReal_nonneg
  obtain ⟨𝓕', xL', xR', W', VL', VR', B', hE', -, hid⟩ :=
    Sec2.Restart.exists_restart hE hT hA hAζ hPA
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hcond : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hPA
  -- the restarted path is defined through `τ ∧ 1`, almost surely on `A`
  have hlife' : ∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ≥0, t ≤ 1 → (∀ u < t, |W' u ω| < 1) →
      (t : ℝ≥0∞) < ζ ω - T ω := by
    filter_upwards [hid, hlife] with ω hω hl hωA t ht hW
    obtain ⟨-, -, hval, -⟩ := hω hωA
    refine lt_lifetime_of_restart (w := fun u => W (T ω + u) ω - W (T ω) ω)
      (fun u hu => (hval u hu).1) (fun t ht h => ?_) ht hW
    exact (Sec2.Restart.coe_lt_sub_iff _ _).2 (hl hωA t ht h)
  have h1 : ∀ᵐ ω ∂(P[|A]), ∀ t : ℝ≥0, t ≤ 1 → (∀ u < t, |W' u ω| < 1) →
      (t : ℝ≥0∞) < ζ ω - T ω := by
    filter_upwards [cond_absolutelyContinuous.ae_le hlife', ae_cond_mem hAm] with ω h hωA
    exact h hωA
  have h2 : ∀ᵐ ω ∂(P[|A]), ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → r.toNNReal ≤ 1 →
      (∀ u < r.toNNReal, |W' u ω| < 1) →
      |otherDrift ρL ρR (W' r.toNNReal ω) (fun i => VL' i r.toNNReal ω)
        (fun i => VR' i r.toNNReal ω)| ≤ C := by
    filter_upwards [cond_absolutelyContinuous.ae_le hid, cond_absolutelyContinuous.ae_le hlife',
      cond_absolutelyContinuous.ae_le hU, ae_cond_mem hAm] with ω hω hl hu hωA
    obtain ⟨-, -, hval, -⟩ := hω hωA
    filter_upwards [hu hωA] with r hr hr0 hr1 hW
    have hrL : (r.toNNReal : ℝ≥0∞) < ζ ω - T ω := hl hωA _ hr1 hW
    obtain ⟨e1, e2, e3⟩ := hval _ hrL
    have hW' : ∀ u < r.toNNReal, |W (T ω + u) ω - W (T ω) ω| < 1 := fun u hu => by
      rw [← (hval u ((ENNReal.coe_lt_coe.2 hu).trans hrL)).1]
      exact hW u hu
    have := hr hr0 hr1 hW'
    rw [e1, funext e2, funext e3, otherDrift_sub]
    exact this
  have hmain := hcross (P[|A]) 𝓕' xL' xR' ρL ρR W' VL' VR' B' (fun ω => ζ ω - T ω) hE' hρJ h1 h2
  -- back to `P`
  have hincl : A ∩ {ω | ∀ t : ℝ≥0, t < 1 → |W' t ω| < 1} ≤ᵐ[P]
      A ∩ {ω | ∀ t : ℝ≥0, t < 1 → |W (T ω + t) ω - W (T ω) ω| < 1} := by
    filter_upwards [hid, hlife'] with ω hω hl ⟨hωA, hW⟩
    refine ⟨hωA, fun t ht => ?_⟩
    obtain ⟨-, -, hval, -⟩ := hω hωA
    have h1L : ((1 : ℝ≥0) : ℝ≥0∞) < ζ ω - T ω := hl hωA 1 le_rfl hW
    rw [← (hval t ((ENNReal.coe_lt_coe.2 ht).trans h1L)).1]
    exact hW t ht
  have hPAr : 0 < P.real A := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hPA (measure_ne_top _ _)
  have hcalc : (P[|A]).real {ω | ∀ t : ℝ≥0, t < 1 → |W' t ω| < 1} =
      P.real (A ∩ {ω | ∀ t : ℝ≥0, t < 1 → |W' t ω| < 1}) / P.real A := by
    rw [measureReal_def, cond_apply hAm, ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def,
      measureReal_def, div_eq_inv_mul]
  rw [hcalc, le_div_iff₀ hPAr] at hmain
  exact hmain.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hincl))

theorem coe_untopA_of_ne_top {x : WithTop ℝ≥0} (hx : x ≠ ⊤) :
    ((x.untopA : ℝ≥0) : WithTop ℝ≥0) = x := by
  induction x with
  | top => exact absurd rfl hx
  | coe a => rfl

/-- **Lemma 5.10 at a general stopping time** (the form Proposition 5.9 uses: the stage times may be
infinite off the event considered). Same constant `p₀` as `crossing_lower_bound_restart`. For every
integrated `SLE_κ(ρ_L; ρ_R)` evolution, every stopping time `τ` (values in `[0, ∞]`) and every `A ∈ 𝓕_τ` with
`τ < ζ` on `A`, under the same hypotheses on the process restarted at `τ`:
`p₀ ℙ[A] ≤ ℙ[A ∩ {|W_{τ+t} − W_τ| < 1 for all t < 1}]`. (On `A` the time `τ` is finite and `W_{τ+t}` means
`W` at `τ.untopA + t`.) Proof: apply `crossing_lower_bound_restart` to the bounded stopping times `τ ∧ N`
and the events `A ∩ {τ ≤ N} ∈ 𝓕_{τ ∧ N}`, and let `N → ∞`. -/
theorem crossing_lower_bound_restart_stoppingTime {κ C : ℝ} (hκ : 0 < κ) {J : Set ℝ}
    (hJ : IsCompact J) (hJ2 : J ⊆ Set.Ioi (-2)) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) {nL nR : ℕ} (xL : Fin nL → ℝ)
      (xR : Fin (nR + 1) → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ) (A : Set Ω),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → ρR 0 ∈ J →
      MeasurableSet[hτ.measurableSpace] A → (∀ ω ∈ A, (τ ω : ℝ≥0∞) < ζ ω) →
      (∀ᵐ ω ∂P, ω ∈ A → ∀ t : ℝ≥0, t ≤ 1 →
        (∀ u < t, |W ((τ ω).untopA + u) ω - W (τ ω).untopA ω| < 1) →
        (((τ ω).untopA + t : ℝ≥0) : ℝ≥0∞) < ζ ω) →
      (∀ᵐ ω ∂P, ω ∈ A → ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → r.toNNReal ≤ 1 →
        (∀ u < r.toNNReal, |W ((τ ω).untopA + u) ω - W (τ ω).untopA ω| < 1) →
        |otherDrift ρL ρR (W ((τ ω).untopA + r.toNNReal) ω)
          (fun i => VL i ((τ ω).untopA + r.toNNReal) ω)
          (fun i => VR i ((τ ω).untopA + r.toNNReal) ω)| ≤ C) →
      p₀ * P.real A ≤ P.real (A ∩ {ω | ∀ t : ℝ≥0, t < 1 →
        |W ((τ ω).untopA + t) ω - W (τ ω).untopA ω| < 1}) := by
  obtain ⟨p₀, hp₀, hfin⟩ := crossing_lower_bound_restart (C := C) hκ hJ hJ2
  refine ⟨p₀, hp₀, ?_⟩
  intro Ω mΩ P hP 𝓕 nL nR xL xR ρL ρR W VL VR B ζ τ hτ A hE hρJ hA hAζ hlife hU
  have hfinA : ∀ ω ∈ A, (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) = τ ω := fun ω hω =>
    coe_untopA_of_ne_top (ne_top_of_lt (hAζ ω hω))
  have hstep : ∀ N : ℕ, p₀ * P.real (A ∩ {ω | τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)}) ≤
      P.real (A ∩ {ω | ∀ t : ℝ≥0, t < 1 → |W ((τ ω).untopA + t) ω - W (τ ω).untopA ω| < 1}) := by
    intro N
    set TN : Ω → ℝ≥0 := fun ω => (min (τ ω) ((N : ℝ≥0) : WithTop ℝ≥0)).untopA with hTNdef
    have hTN_eq : ∀ ω, ((TN ω : ℝ≥0) : WithTop ℝ≥0) = min (τ ω) ((N : ℝ≥0) : WithTop ℝ≥0) :=
      fun ω => coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _))
    have hfun : (fun ω => ((TN ω : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => min (τ ω) ((N : ℝ≥0) : WithTop ℝ≥0) := funext hTN_eq
    have hTN : IsStoppingTime 𝓕 fun ω => ((TN ω : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hfun]; exact hτ.min_const _
    have hAN : MeasurableSet[hTN.measurableSpace] (A ∩ {ω | τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)}) := by
      have h := hτ.measurableSet_inter_le (isStoppingTime_const 𝓕 (N : ℝ≥0)) A hA
      rw [IsStoppingTime.measurableSet] at h ⊢
      refine ⟨h.1, fun i => ?_⟩
      convert h.2 i using 2
      ext ω
      simp only [mem_ofPred_eq, hTN_eq]
    have hTS : ∀ ω ∈ A ∩ {ω | τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)}, TN ω = (τ ω).untopA := by
      rintro ω ⟨-, hω⟩
      simp only [hTNdef, min_eq_left (show τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0) from hω)]
    have hmain := hfin P 𝓕 xL xR ρL ρR W VL VR B ζ TN hTN (A ∩ {ω | τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)})
      hE hρJ hAN (fun ω hω => by
        have h := hAζ ω hω.1
        rw [← hfinA ω hω.1] at h
        rw [hTS ω hω]
        exact h)
      (by
        filter_upwards [hlife] with ω h hω
        rw [hTS ω hω]
        exact h hω.1)
      (by
        filter_upwards [hU] with ω h hω
        rw [hTS ω hω]
        exact h hω.1)
    refine hmain.trans (measureReal_mono ?_ (measure_ne_top _ _))
    rintro ω ⟨hω, hW⟩
    refine ⟨hω.1, ?_⟩
    have := hTS ω hω
    simp only [mem_ofPred_eq, this] at hW ⊢
    exact hW
  have hmono : Monotone fun N : ℕ => A ∩ {ω | τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)} :=
    fun N M hNM ω ⟨h1, h2⟩ => by
      refine ⟨h1, ?_⟩
      have h2' : τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0) := h2
      show τ ω ≤ ((M : ℝ≥0) : WithTop ℝ≥0)
      exact h2'.trans (WithTop.coe_le_coe.2 (by exact_mod_cast hNM))
  have hUn : ⋃ N : ℕ, A ∩ {ω | τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)} = A := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨N, h1, -⟩; exact h1
    · intro h1
      obtain ⟨N, hN⟩ := exists_nat_ge ((τ ω).untopA)
      refine ⟨N, h1, ?_⟩
      rw [← hfinA ω h1]
      exact WithTop.coe_le_coe.2 hN
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hUn] at hlim
  have hlimr : Tendsto (fun N : ℕ => P.real (A ∩ {ω | τ ω ≤ ((N : ℝ≥0) : WithTop ℝ≥0)})) atTop
      (𝓝 (P.real A)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim
  exact le_of_tendsto' (hlimr.const_mul p₀) hstep

end Sec5

end InteractingSLE
