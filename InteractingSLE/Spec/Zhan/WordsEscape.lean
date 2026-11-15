/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsStripReduce
import InteractingSLE.Spec.Zhan.WordsSublinear
import InteractingSLE.Spec.Zhan.StripEndpointEscape

/-!
# Linear escape of the lower left strip gaps and finite strip energy

Packet PROVE-ZHAN-B4. Astra §3, "Linear escape of lower strip gaps" (`source/external/AstraIG1/
ig1_formalization_proofs.txt` L1520–L1556), for the lower left marks of an R36 strip evolution whose end charge
satisfies `q₋ ≥ κ/2 − 2`: in strip time the nearest left gap `Y₀ = ξ − p₀` solves

  `Y₀(t) − Y₀(s) = √κ (B̃_t − B̃_s) + ∫ₛᵗ ((1 + s_L/2) C(Y₀) − (s_R/2) C(X₀) + τd) + (spread terms)`,

`C = coth(·/2)`, `X₀` the nearest right gap, with bounded same-side spreads, `X₀ + Y₀ ≥ 2t + const`, and slope
`Δ = q₋ + 4 − κ/2 ≥ 2`; the landed pathwise barrier lemma (`eventually_mul_le_of_gap_eq`) and Brownian sublinearity
(`ae_abs_le_add_mul`) give `Y₀(t) ≥ α t` eventually. Then every left coth error is `≤ 4 e^{−α t}` and the strip
energy is finite (`stripLeftEnergyStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

open Strip

namespace Strip.IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

/-- **Lower points**: a chordal point path `y` strictly right of the end mark and off the driver on `[0, S]` has
strip coordinate `p_t = p_0 + ∫₀ᵗ coth((p_u − ξ_u)/2) du` on `[0, t(S)]`. -/
theorem stripPoint_eq_add_integral_of_lower (h : IsSepMark w v S) {y : ℝ → ℝ}
    (hy : ContinuousOn y (Icc 0 S)) (hint : IntervalIntegrable (fun u => 2 / (y u - w u)) volume 0 S)
    (heq : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ u in (0 : ℝ)..s, 2 / (y u - w u))
    (hvy : ∀ s ∈ Icc 0 S, v s < y s) (hyw : ∀ s ∈ Icc 0 S, y s ≠ w s) {t : ℝ}
    (ht : t ∈ Icc 0 (stripClock w v S)) :
    stripPoint w v y t = stripPoint w v y 0 +
      ∫ u in (0 : ℝ)..t, Sec4.cothHalf (stripPoint w v y u - stripDriver w v u) := by
  have hsub : Icc 0 t ⊆ Icc 0 (stripClock w v S) := Icc_subset_Icc le_rfl ht.2
  have hp := h.continuousOn_stripPoint hy fun s hs => (hvy s hs).ne'
  have hne : ∀ u ∈ Icc 0 (stripClock w v S), stripPoint w v y u - stripDriver w v u ≠ 0 := fun u hu => by
    have hs := h.chordalTime_mem hu
    rw [stripPoint, stripDriver, abs_of_pos (sub_pos.2 (hvy _ hs))]
    intro h0
    have h1 : Real.log (y (chordalTime w v u) - v (chordalTime w v u)) =
        Real.log (w (chordalTime w v u) - v (chordalTime w v u)) := by linarith
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (sub_pos.2 (hvy _ hs)))
      (Set.mem_Ioi.2 (sub_pos.2 (h.lt _ hs))) h1
    exact hyw _ hs (by linarith)
  have hcont : ContinuousOn (fun u => Sec4.cothHalf (stripPoint w v y u - stripDriver w v u)) (Icc 0 t) :=
    (continuousOn_cothHalf_of_ne.comp (hp.sub h.continuousOn_stripDriver) fun u hu => hne u hu).mono hsub
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hp.mono hsub)
    (fun u hu => h.hasDerivAt_stripPoint_of_lt hy hint heq ⟨hu.1, hu.2.trans_le ht.2⟩
      (hyw _ (h.chordalTime_mem ⟨hu.1.le, hu.2.le.trans ht.2⟩))
      (hvy _ (h.chordalTime_mem ⟨hu.1.le, hu.2.le.trans ht.2⟩)))
    (hcont.intervalIntegrable_of_Icc ht.1)]
  ring

end Strip.IsSepMark

/-- Continuity on `[0, ∞)` from continuity on every `[0, T]`. -/
theorem continuousOn_Ici_of_forall_Icc {f : ℝ → ℝ} (h : ∀ T, 0 ≤ T → ContinuousOn f (Icc 0 T)) :
    ContinuousOn f (Ici 0) := fun x hx =>
  ((h (x + 1) (by linarith [mem_Ici.1 hx])) x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin.2 ⟨Iio (x + 1), isOpen_Iio, by simp, fun y hy => ⟨hy.2, (mem_Iio.1 hy.1).le⟩⟩)

/-! ### `coth(·/2)` -/

theorem cothHalf_neg' (x : ℝ) : Sec4.cothHalf (-x) = -Sec4.cothHalf x := by
  rw [Sec4.cothHalf, Sec4.cothHalf, Real.exp_neg]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 : Real.exp x - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact fun h => hx (Real.exp_eq_one_iff x |>.1 h)
  have h3 : 1 - Real.exp x ≠ 0 := fun h => h1 (by linarith)
  have he : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  rw [show (Real.exp x)⁻¹ + 1 = (1 + Real.exp x) / Real.exp x by field_simp,
    show (Real.exp x)⁻¹ - 1 = (1 - Real.exp x) / Real.exp x by field_simp,
    div_div_div_cancel_right₀ he, div_eq_iff h3, neg_mul, div_mul_eq_mul_div,
    show 1 - Real.exp x = -(Real.exp x - 1) by ring, mul_neg, neg_div, neg_neg,
    mul_div_cancel_right₀ _ h1]
  ring

theorem cothHalf_antitoneOn {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Sec4.cothHalf y ≤ Sec4.cothHalf x := by
  have hy : 0 < y := hx.trans_le hxy
  have ex : 0 < Real.exp x - 1 := by linarith [Real.add_one_lt_exp hx.ne']
  have ey : Real.exp x - 1 ≤ Real.exp y - 1 := by linarith [Real.exp_le_exp.2 hxy]
  rw [Sec4.cothHalf, Sec4.cothHalf, div_le_div_iff₀ (by linarith) ex]
  nlinarith [Real.exp_le_exp.2 hxy, Real.exp_pos x]

/-! ### The pathwise one-sided escape -/

/-- **Linear escape of the nearest lower left strip gap, pathwise** (Astra (3.24)–(3.25), left version). Lower left
points `p i` and lower right points `q j` solve `p_t − p_s = ∫ C(p − ξ)`; the strip driver satisfies
`ξ_t − ξ_s = −(N_t − N_s) − Σ (ρᵢ/2)Δpᵢ − Σ (σⱼ/2)Δqⱼ + τd Δt` with `N` sublinear; the gaps `Yᵢ = ξ − pᵢ`, `Xⱼ = qⱼ − ξ`
are positive, the nearest ones are `Y₀`, `X₀`; `1 + Σρ/2 ≥ 0` and `1 + Σρ/2 − Σσ/2 + τd > 0`. Then `Y₀(t) ≥ α t`
eventually. -/
theorem exists_linear_escape_left {n m : ℕ} {ξ : ℝ → ℝ} {p : Fin (n + 1) → ℝ → ℝ} {q : Fin m → ℝ → ℝ}
    {N : ℝ → ℝ} {ρ : Fin (n + 1) → ℝ} {σ : Fin m → ℝ} {τd : ℝ}
    (hξc : ContinuousOn ξ (Ici 0)) (hpc : ∀ i, ContinuousOn (p i) (Ici 0))
    (hqc : ∀ j, ContinuousOn (q j) (Ici 0))
    (hp : ∀ i s t, 0 ≤ s → s ≤ t → p i t - p i s = ∫ r in s..t, Sec4.cothHalf (p i r - ξ r))
    (hq : ∀ j s t, 0 ≤ s → s ≤ t → q j t - q j s = ∫ r in s..t, Sec4.cothHalf (q j r - ξ r))
    (hξ : ∀ s t, 0 ≤ s → s ≤ t → ξ t - ξ s = -(N t - N s) - (∑ i, ρ i / 2 * (p i t - p i s)) -
      (∑ j, σ j / 2 * (q j t - q j s)) + τd * (t - s))
    (hY : ∀ i u, 0 ≤ u → 0 < ξ u - p i u) (hX : ∀ j u, 0 ≤ u → 0 < q j u - ξ u)
    (hY0 : ∀ i u, 0 ≤ u → ξ u - p 0 u ≤ ξ u - p i u)
    (hX0 : ∀ (hm : 0 < m) j u, 0 ≤ u → q ⟨0, hm⟩ u - ξ u ≤ q j u - ξ u)
    (hN : ∀ ε > 0, ∃ C, ∀ u, 0 ≤ u → |N u| ≤ C + ε * u)
    (hsL : 0 ≤ 1 + (∑ i, ρ i) / 2) (hΔ : 0 < 1 + (∑ i, ρ i) / 2 - (∑ j, σ j) / 2 + τd) :
    ∃ α > 0, ∃ T, ∀ t, T ≤ t → α * t ≤ ξ t - p 0 t := by
  -- continuity of `C` of a positive continuous gap on `[s, t]`
  have hCc : ∀ {g : ℝ → ℝ}, ContinuousOn g (Ici 0) → (∀ u, 0 ≤ u → g u ≠ 0) →
      ContinuousOn (fun r => Sec4.cothHalf (g r)) (Ici 0) := fun hg hpos =>
    continuousOn_cothHalf_of_ne.comp hg fun u hu => hpos u hu
  have hCi : ∀ {g : ℝ → ℝ}, ContinuousOn g (Ici 0) → (∀ u, 0 ≤ u → g u ≠ 0) → ∀ s t, 0 ≤ s → s ≤ t →
      IntervalIntegrable (fun r => Sec4.cothHalf (g r)) volume s t := fun hg hpos s t hs hst =>
    ((hCc hg hpos).mono fun r hr => le_trans hs hr.1).intervalIntegrable_of_Icc hst
  have hIp : ∀ i s t, 0 ≤ s → s ≤ t →
      IntervalIntegrable (fun r => Sec4.cothHalf (p i r - ξ r)) volume s t := fun i =>
    hCi ((hpc i).sub hξc) fun u hu => by linarith [hY i u hu]
  have hIq : ∀ j s t, 0 ≤ s → s ≤ t →
      IntervalIntegrable (fun r => Sec4.cothHalf (q j r - ξ r)) volume s t := fun j =>
    hCi ((hqc j).sub hξc) fun u hu => by linarith [hX j u hu]
  set X : ℝ → ℝ := fun u => ξ u - p 0 u with hXdef
  have hXc : ContinuousOn X (Ici 0) := hξc.sub (hpc 0)
  have hXpos : ∀ u, 0 ≤ u → 0 < X u := hY 0
  have hXne : ∀ u, 0 ≤ u → X u ≠ 0 := fun u hu => (hXpos u hu).ne'
  -- the gap integral of the nearest left point
  have hp0 : ∀ s t, 0 ≤ s → s ≤ t → p 0 t - p 0 s = -∫ r in s..t, Sec4.cothHalf (X r) := fun s t hs hst => by
    rw [hp 0 s t hs hst, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [hXdef]
    rw [show p 0 r - ξ r = -(ξ r - p 0 r) by ring, cothHalf_neg']
  -- monotone spreads on the left: `0 ≤ p₀ − pᵢ ≤ (p₀ − pᵢ)(0)`
  have hspL : ∀ i u, 0 ≤ u → 0 ≤ p 0 u - p i u ∧ p 0 u - p i u ≤ p 0 0 - p i 0 := fun i u hu => by
    refine ⟨by linarith [hY0 i u hu], ?_⟩
    have h1 : (p 0 u - p i u) - (p 0 0 - p i 0) =
        ∫ r in (0 : ℝ)..u, (Sec4.cothHalf (p 0 r - ξ r) - Sec4.cothHalf (p i r - ξ r)) := by
      rw [intervalIntegral.integral_sub (hIp 0 0 u le_rfl hu) (hIp i 0 u le_rfl hu),
        ← hp 0 0 u le_rfl hu, ← hp i 0 u le_rfl hu]
      ring
    have h2 : ∫ r in (0 : ℝ)..u, (Sec4.cothHalf (p 0 r - ξ r) - Sec4.cothHalf (p i r - ξ r)) ≤ 0 := by
      have hle := intervalIntegral.integral_mono_on hu ((hIp 0 0 u le_rfl hu).sub (hIp i 0 u le_rfl hu))
        (intervalIntegrable_const (c := (0 : ℝ))) fun r hr => by
          rw [show p 0 r - ξ r = -(ξ r - p 0 r) by ring, show p i r - ξ r = -(ξ r - p i r) by ring,
            cothHalf_neg', cothHalf_neg']
          linarith [cothHalf_antitoneOn (hY 0 r hr.1) (hY0 i r hr.1)]
      simpa using hle
    linarith
  -- the left spread error
  set El : ℝ → ℝ := fun u => ∑ i, ρ i / 2 * (p i u - p 0 u) with hEl
  have hElbd : ∀ s t, 0 ≤ s → 0 ≤ t → |El t - El s| ≤ ∑ i, |ρ i| / 2 * (p 0 0 - p i 0) := by
    intro s t hs ht
    simp only [hEl, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← mul_sub, abs_mul, abs_div, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    obtain ⟨a1, a2⟩ := hspL i t ht
    obtain ⟨b1, b2⟩ := hspL i s hs
    rw [abs_le]; constructor <;> linarith
  have hleft : ∀ s t, 0 ≤ s → s ≤ t → (∑ i, ρ i / 2 * (p i t - p i s)) =
      (∑ i, ρ i) / 2 * (p 0 t - p 0 s) + (El t - El s) := fun s t _ _ => by
    simp only [hEl, Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the right side: a comparison gap `Yr` and a bounded error `Er`
  obtain ⟨Yr, Er, VR, K, hYrc, hYrpos, hXY, hright, hErbd⟩ : ∃ (Yr Er : ℝ → ℝ) (VR K : ℝ),
      ContinuousOn Yr (Ici 0) ∧ (∀ u, 0 ≤ u → 0 < Yr u) ∧ (∀ u, 0 ≤ u → 2 * u - K ≤ X u + Yr u) ∧
      (∀ s t, 0 ≤ s → s ≤ t → (∑ j, σ j / 2 * (q j t - q j s)) =
        (∑ j, σ j) / 2 * (∫ r in s..t, Sec4.cothHalf (Yr r)) + (Er t - Er s)) ∧
      (∀ s t, 0 ≤ s → 0 ≤ t → |Er t - Er s| ≤ VR) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      refine ⟨fun u => 2 * u + 1, fun _ => 0, 0, 0, (continuous_const.mul continuous_id).add
        continuous_const |>.continuousOn, fun u hu => by linarith, fun u hu => by linarith [hXpos u hu],
        fun s t _ _ => by simp, fun s t _ _ => by simp⟩
    · set j₀ : Fin m := ⟨0, hm⟩
      have hq0 : ∀ s t, 0 ≤ s → s ≤ t → q j₀ t - q j₀ s = ∫ r in s..t, Sec4.cothHalf (q j₀ r - ξ r) :=
        hq j₀
      have hspR : ∀ j u, 0 ≤ u → 0 ≤ q j u - q j₀ u ∧ q j u - q j₀ u ≤ q j 0 - q j₀ 0 := fun j u hu => by
        refine ⟨by linarith [hX0 hm j u hu], ?_⟩
        have h1 : (q j u - q j₀ u) - (q j 0 - q j₀ 0) =
            ∫ r in (0 : ℝ)..u, (Sec4.cothHalf (q j r - ξ r) - Sec4.cothHalf (q j₀ r - ξ r)) := by
          rw [intervalIntegral.integral_sub (hIq j 0 u le_rfl hu) (hIq j₀ 0 u le_rfl hu),
            ← hq j 0 u le_rfl hu, ← hq j₀ 0 u le_rfl hu]
          ring
        have h2 : ∫ r in (0 : ℝ)..u, (Sec4.cothHalf (q j r - ξ r) - Sec4.cothHalf (q j₀ r - ξ r)) ≤ 0 := by
          have hle := intervalIntegral.integral_mono_on hu ((hIq j 0 u le_rfl hu).sub (hIq j₀ 0 u le_rfl hu))
            (intervalIntegrable_const (c := (0 : ℝ))) fun r hr => by
              linarith [cothHalf_antitoneOn (hX j₀ r hr.1) (hX0 hm j r hr.1)]
          simpa using hle
        linarith
      refine ⟨fun u => q j₀ u - ξ u, fun u => ∑ j, σ j / 2 * (q j u - q j₀ u),
        ∑ j, |σ j| / 2 * (q j 0 - q j₀ 0), -(X 0 + (q j₀ 0 - ξ 0)), (hqc j₀).sub hξc, hX j₀,
        fun u hu => ?_, fun s t hs hst => ?_, fun s t hs ht => ?_⟩
      · have h1 : (X u + (q j₀ u - ξ u)) - (X 0 + (q j₀ 0 - ξ 0)) =
            ∫ r in (0 : ℝ)..u, (Sec4.cothHalf (q j₀ r - ξ r) - Sec4.cothHalf (p 0 r - ξ r)) := by
          rw [intervalIntegral.integral_sub (hIq j₀ 0 u le_rfl hu) (hIp 0 0 u le_rfl hu),
            ← hq j₀ 0 u le_rfl hu, ← hp 0 0 u le_rfl hu]
          simp only [hXdef]; ring
        have h2 : 2 * u ≤ ∫ r in (0 : ℝ)..u, (Sec4.cothHalf (q j₀ r - ξ r) - Sec4.cothHalf (p 0 r - ξ r)) := by
          have hle := intervalIntegral.integral_mono_on hu (intervalIntegrable_const (c := (2 : ℝ)))
            ((hIq j₀ 0 u le_rfl hu).sub (hIp 0 0 u le_rfl hu)) fun r hr => by
              rw [show p 0 r - ξ r = -(ξ r - p 0 r) by ring, cothHalf_neg']
              linarith [Sec4.one_le_cothHalf (hX j₀ r hr.1), Sec4.one_le_cothHalf (hY 0 r hr.1)]
          simpa [mul_comm] using hle
        linarith
      · rw [← hq0 s t hs hst, Finset.sum_div, Finset.sum_mul, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp only [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [← mul_sub, abs_mul, abs_div, abs_two]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        obtain ⟨a1, a2⟩ := hspR j t ht
        obtain ⟨b1, b2⟩ := hspR j s hs
        rw [abs_le]; constructor <;> linarith
  -- the gap equation
  have hYrne : ∀ u, 0 ≤ u → Yr u ≠ 0 := fun u hu => (hYrpos u hu).ne'
  have hint : ∀ s t, 0 ≤ s → s ≤ t →
      IntervalIntegrable (fun r => gapDrift (∑ i, ρ i) (∑ j, σ j) τd (X r) (Yr r)) volume s t :=
    fun s t hs hst => (((hCi hXc hXne s t hs hst).const_mul _).sub
      ((hCi hYrc hYrne s t hs hst).const_mul _)).add intervalIntegrable_const
  have heq : ∀ s t, 0 ≤ s → s ≤ t → X t - X s = -(N t - N s) +
      (∫ r in s..t, gapDrift (∑ i, ρ i) (∑ j, σ j) τd (X r) (Yr r)) - ((El t + Er t) - (El s + Er s)) := by
    intro s t hs hst
    have hI : ∫ r in s..t, gapDrift (∑ i, ρ i) (∑ j, σ j) τd (X r) (Yr r) =
        (1 + (∑ i, ρ i) / 2) * (∫ r in s..t, Sec4.cothHalf (X r)) -
          (∑ j, σ j) / 2 * (∫ r in s..t, Sec4.cothHalf (Yr r)) + τd * (t - s) := by
      simp only [gapDrift]
      rw [intervalIntegral.integral_add (((hCi hXc hXne s t hs hst).const_mul _).sub
        ((hCi hYrc hYrne s t hs hst).const_mul _)) intervalIntegrable_const,
        intervalIntegral.integral_sub ((hCi hXc hXne s t hs hst).const_mul _)
          ((hCi hYrc hYrne s t hs hst).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const, smul_eq_mul, mul_comm (t - s)]
    have h1 := hξ s t hs hst
    rw [hleft s t hs hst, hright s t hs hst] at h1
    have h2 := hp0 s t hs hst
    rw [hI]
    have hXt : X t = ξ t - p 0 t := rfl
    have hXs : X s = ξ s - p 0 s := rfl
    linear_combination hXt - hXs + h1 - (1 + (∑ i, ρ i) / 2) * h2
  obtain ⟨α, hα, T, hT⟩ := eventually_mul_le_of_gap_eq (X := X) (Y := Yr) (N := N)
    (E := fun u => El u + Er u) (T₀ := 0) (K := K)
    (V := (∑ i, |ρ i| / 2 * (p 0 0 - p i 0)) + VR) hXc hXpos hXY hint heq
    (fun ε hε => (hN ε hε)) (fun s t hs hst => by
      have h1 := hElbd s t hs (hs.trans hst)
      have h2 := hErbd s t hs (hs.trans hst)
      calc |(El t + Er t) - (El s + Er s)| = |(El t - El s) + (Er t - Er s)| := by ring_nf
        _ ≤ |El t - El s| + |Er t - Er s| := abs_add_le _ _
        _ ≤ _ := add_le_add h1 h2) hsL hΔ
  exact ⟨α, hα, T, hT⟩

/-! ### Finite energy of exponentially small coth errors -/

theorem integral_exp_neg_le {a T t : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    ∫ u in T..t, Real.exp (-a * u) ≤ 1 / a := by
  have hd : ∀ u ∈ uIcc T t, HasDerivAt (fun u => -Real.exp (-a * u) / a) (Real.exp (-a * u)) u := by
    intro u _
    have h1 : HasDerivAt (fun u => -a * u) (-a) u := by simpa using (hasDerivAt_id u).const_mul (-a)
    have h2 : HasDerivAt (fun u => -Real.exp (-a * u) / a) (-(Real.exp (-a * u) * -a) / a) u :=
      (h1.exp.neg).div_const a
    rwa [show -(Real.exp (-a * u) * -a) / a = Real.exp (-a * u) by field_simp] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  have h3 : Real.exp (-a * T) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h4 := Real.exp_pos (-a * t)
  calc -Real.exp (-a * t) / a - -Real.exp (-a * T) / a = (Real.exp (-a * T) - Real.exp (-a * t)) / a := by
        ring
    _ ≤ 1 / a := div_le_div_of_nonneg_right (by linarith) ha.le

/-- **Finite energy of escaping coth errors**: if every gap `Yᵢ` is positive, continuous and eventually `≥ α t`, the
squared coth error `(Σ (ρᵢ/2)(coth(Yᵢ/2) − 1))²` has uniformly bounded integrals over `[0, t]`. -/
theorem exists_integral_sq_le_of_escape {n : ℕ} {Y : Fin n → ℝ → ℝ} (ρ : Fin n → ℝ)
    (hYc : ∀ i, ContinuousOn (Y i) (Ici 0)) (hYpos : ∀ i u, 0 ≤ u → 0 < Y i u) {α T : ℝ} (hα : 0 < α)
    (hT : ∀ i t, T ≤ t → α * t ≤ Y i t) :
    ∃ m : ℝ, ∀ t, 0 ≤ t → ∫ u in (0 : ℝ)..t, (∑ i, ρ i / 2 * (Sec4.cothHalf (Y i u) - 1)) ^ 2 ≤ m := by
  set f : ℝ → ℝ := fun u => (∑ i, ρ i / 2 * (Sec4.cothHalf (Y i u) - 1)) ^ 2 with hfdef
  have hfc : ContinuousOn f (Ici 0) := by
    refine ContinuousOn.pow (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_) 2
    exact (continuousOn_cothHalf_of_ne.comp (hYc i) fun u hu => (hYpos i u hu).ne').sub continuousOn_const
  have hf0 : ∀ u, 0 ≤ f u := fun u => sq_nonneg _
  set T₁ := max (max T 0) (Real.log 2 / α) with hT₁
  have hT₁0 : 0 ≤ T₁ := (le_max_right _ _).trans (le_max_left _ _)
  set K := ∑ i, |ρ i| * 2 with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  have hdecay : ∀ u, T₁ ≤ u → f u ≤ K ^ 2 * Real.exp (-(2 * α) * u) := by
    intro u hu
    have hu0 : 0 ≤ u := hT₁0.trans hu
    have hlog : Real.log 2 ≤ α * u := by
      have := (le_max_right _ _).trans hu
      rwa [div_le_iff₀ hα, mul_comm] at this
    have hterm : ∀ i, |ρ i / 2 * (Sec4.cothHalf (Y i u) - 1)| ≤ |ρ i| * 2 * Real.exp (-(α * u)) := by
      intro i
      have hYi : α * u ≤ Y i u := hT i u ((le_max_left _ _).trans ((le_max_left _ _).trans hu))
      have h1 := Sec4.cothHalf_sub_one_le (hlog.trans hYi)
      have h2 : 0 ≤ Sec4.cothHalf (Y i u) - 1 := by linarith [Sec4.one_le_cothHalf (hYpos i u hu0)]
      have h3 : Real.exp (-Y i u) ≤ Real.exp (-(α * u)) := Real.exp_le_exp.2 (by linarith)
      rw [abs_mul, abs_div, abs_two, abs_of_nonneg h2]
      calc |ρ i| / 2 * (Sec4.cothHalf (Y i u) - 1) ≤ |ρ i| / 2 * (4 * Real.exp (-(α * u))) := by
            gcongr; linarith
        _ = |ρ i| * 2 * Real.exp (-(α * u)) := by ring
    have hsum : |∑ i, ρ i / 2 * (Sec4.cothHalf (Y i u) - 1)| ≤ K * Real.exp (-(α * u)) := by
      rw [hK, Finset.sum_mul]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    have hsq : f u ≤ (K * Real.exp (-(α * u))) ^ 2 := by
      simp only [hfdef]
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hsum 2
    calc f u ≤ (K * Real.exp (-(α * u))) ^ 2 := hsq
      _ = K ^ 2 * Real.exp (-(2 * α) * u) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hfc.mono (fun u hu => hu.1 : Icc 0 T₁ ⊆ Ici 0))
  refine ⟨M * T₁ + K ^ 2 * (1 / (2 * α)), fun t ht => ?_⟩
  set t' := max t T₁ with ht'
  have hfi : ∀ a b, 0 ≤ a → a ≤ b → IntervalIntegrable f volume a b := fun a b ha hab =>
    (hfc.mono fun u hu => ha.trans hu.1).intervalIntegrable_of_Icc hab
  have h1 : ∫ u in (0 : ℝ)..t, f u ≤ ∫ u in (0 : ℝ)..t', f u :=
    intervalIntegral.integral_mono_interval le_rfl ht (le_max_left _ _)
      (Eventually.of_forall fun u => hf0 u) (hfi 0 t' le_rfl (ht.trans (le_max_left _ _)))
  rw [← intervalIntegral.integral_add_adjacent_intervals (hfi 0 T₁ le_rfl hT₁0)
    (hfi T₁ t' hT₁0 (le_max_right _ _))] at h1
  have h2 : ∫ u in (0 : ℝ)..T₁, f u ≤ M * T₁ := by
    have := intervalIntegral.integral_mono_on hT₁0 (hfi 0 T₁ le_rfl hT₁0)
      (intervalIntegrable_const (c := M)) fun u hu => (le_abs_self _).trans (by
        have := hM u hu; rwa [Real.norm_eq_abs] at this)
    simpa [mul_comm] using this
  have h3 : ∫ u in T₁..t', f u ≤ K ^ 2 * (1 / (2 * α)) := by
    have hexp : IntervalIntegrable (fun u => K ^ 2 * Real.exp (-(2 * α) * u)) volume T₁ t' :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).const_smul (K ^ 2)).intervalIntegrable _ _
    have := intervalIntegral.integral_mono_on (le_max_right _ _) (hfi T₁ t' hT₁0 (le_max_right _ _)) hexp
      fun u hu => hdecay u hu.1
    rw [intervalIntegral.integral_const_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_left (integral_exp_neg_le (by positivity) hT₁0) (by positivity))
  linarith

/-! ### Strip equations of a chordal mark path -/

section MarkPath

variable {w v y : ℝ≥0 → ℝ} {S : ℝ≥0}

/-- The strip gap of a mark path off the driver is nonzero on `[0, t(S)]`. -/
theorem stripPoint_sub_stripDriver_ne (hsm : IsSepMark (extPath w) (extPath v) S)
    (hvy : ∀ r ≤ S, v r < y r) (hyw : ∀ r ≤ S, y r ≠ w r) {u : ℝ}
    (hu : u ∈ Icc 0 (stripClock (extPath w) (extPath v) S)) :
    stripPoint (extPath w) (extPath v) (extPath y) u - stripDriver (extPath w) (extPath v) u ≠ 0 := by
  have hs := hsm.chordalTime_mem hu
  set c := chordalTime (extPath w) (extPath v) u
  have hle : c.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hs.2
  have h1 : extPath v c < extPath y c := hvy _ hle
  rw [stripPoint, stripDriver, abs_of_pos (sub_pos.2 h1)]
  intro h0
  have h2 : Real.log (extPath y c - extPath v c) = Real.log (extPath w c - extPath v c) := by linarith
  have := Real.log_injOn_pos (Set.mem_Ioi.2 (sub_pos.2 h1)) (Set.mem_Ioi.2 (sub_pos.2 (hsm.lt c hs))) h2
  exact hyw _ hle (by simp only [extPath] at this; linarith)

/-- **The strip equation of a mark path**: for `0 ≤ s ≤ t ≤ t(S)`, `p_t − p_s = ∫ₛᵗ coth((p − ξ)/2)`, and the
integrand is continuous. -/
theorem stripPoint_sub_eq (hsm : IsSepMark (extPath w) (extPath v) S) (hyc : ContinuousOn (extPath y) (Icc 0 S))
    (hyint : IntervalIntegrable (fun u : ℝ => 2 / (y u.toNNReal - w u.toNNReal)) volume 0 S)
    (hyeq : ∀ r : ℝ≥0, r ≤ S → y r = y 0 + ∫ u in (0 : ℝ)..r, 2 / (y u.toNNReal - w u.toNNReal))
    (hvy : ∀ r ≤ S, v r < y r) (hyw : ∀ r ≤ S, y r ≠ w r) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ stripClock (extPath w) (extPath v) S) :
    stripPoint (extPath w) (extPath v) (extPath y) t - stripPoint (extPath w) (extPath v) (extPath y) s =
      ∫ u in s..t, Sec4.cothHalf (stripPoint (extPath w) (extPath v) (extPath y) u -
        stripDriver (extPath w) (extPath v) u) := by
  have hle : ∀ r : ℝ, r ∈ Icc 0 (S : ℝ) → r.toNNReal ≤ S := fun r hr => Real.toNNReal_le_iff_le_coe.2 hr.2
  have heq : ∀ r ∈ Icc 0 (S : ℝ), extPath y r = extPath y 0 + ∫ u in (0 : ℝ)..r, 2 / (extPath y u - extPath w u) :=
    fun r hr => by
      have := hyeq r.toNNReal (hle r hr)
      rw [Real.coe_toNNReal _ hr.1] at this
      simpa [extPath] using this
  have hcont : ContinuousOn (fun u => Sec4.cothHalf (stripPoint (extPath w) (extPath v) (extPath y) u -
      stripDriver (extPath w) (extPath v) u)) (Icc 0 (stripClock (extPath w) (extPath v) S)) :=
    continuousOn_cothHalf_of_ne.comp ((hsm.continuousOn_stripPoint hyc fun r hr => (hvy _ (hle r hr)).ne').sub
      hsm.continuousOn_stripDriver) fun u hu => stripPoint_sub_stripDriver_ne hsm hvy hyw hu
  have hI : ∀ a, 0 ≤ a → a ≤ stripClock (extPath w) (extPath v) S → IntervalIntegrable (fun u =>
      Sec4.cothHalf (stripPoint (extPath w) (extPath v) (extPath y) u - stripDriver (extPath w) (extPath v) u))
      volume 0 a := fun a ha haS =>
    (hcont.mono (Icc_subset_Icc le_rfl haS)).intervalIntegrable_of_Icc ha
  have e := fun a (ha : a ∈ Icc 0 (stripClock (extPath w) (extPath v) S)) =>
    Strip.IsSepMark.stripPoint_eq_add_integral_of_lower hsm hyc hyint heq (fun r hr => hvy _ (hle r hr))
      (fun r hr => hyw _ (hle r hr)) ha
  rw [e t ⟨hs.trans hst, ht⟩, e s ⟨hs, hst.trans ht⟩, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hI t (hs.trans hst) ht) (hI s hs (hst.trans ht))]

end MarkPath

/-- The strip gap of a mark right of the driver is positive. -/
theorem stripPoint_sub_stripDriver_pos {w v y : ℝ → ℝ} {S : ℝ} (hsm : IsSepMark w v S)
    (hwy : ∀ r ∈ Icc 0 S, w r < y r) {u : ℝ} (hu : u ∈ Icc 0 (stripClock w v S)) :
    0 < stripPoint w v y u - stripDriver w v u := by
  have hs := hsm.chordalTime_mem hu
  have h1 := hsm.lt _ hs
  have h2 := hwy _ hs
  rw [stripPoint, stripDriver, abs_of_pos (by linarith)]
  have := Real.log_lt_log (sub_pos.2 h1) (show w (chordalTime w v u) - v (chordalTime w v u) <
    y (chordalTime w v u) - v (chordalTime w v u) by linarith)
  linarith

/-- **The strip statement holds for every `κ > 0`**: linear escape of the nearest lower left gap and exponential
decay of the left coth errors give finite strip energy. -/
theorem stripLeftEnergyStatement {κ : ℝ} (hκ : 0 < κ) : StripLeftEnergyStatement.{u} κ := by
  intro n nR pL pR ρL ρR τm Ω mΩ P _ 𝓕 W VL VR B ζ hsep hpre hq hE
  rcases n with _ | n
  · exact ae_of_all _ fun ω => ⟨0, fun t _ => by simp [leftStripErr]⟩
  have hE' : IsIntegratedSLEEvolution κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR P 𝓕 W VL VR B ζ := hE
  obtain ⟨𝓗, B', hB', hdrv⟩ := exists_stripBrownian_of_prefixSums hκ hsep hpre hE
  filter_upwards [ae_stripLife_noncollision hκ hsep hpre hE, ae_hasUnboundedStripClock hκ hsep hpre hE, hdrv,
    ae_abs_le_add_mul hB', hE'.2.2.2.2] with ω hnc hcl hdω hsub hp
  have hF := hp.isForcePath
  set l : Fin (n + 1 + 1) := Fin.last (n + 1) with hl
  set w : ℝ≥0 → ℝ := fun t => W t ω with hw
  set v : ℝ≥0 → ℝ := fun t => VL l t ω with hv
  set ξ : ℝ → ℝ := stripDriver (extPath w) (extPath v) with hξdef
  set p : Fin (n + 1) → ℝ → ℝ := fun i => stripPoint (extPath w) (extPath v) (extPath fun t => VL i.castSucc t ω)
    with hpdef
  set q : Fin nR → ℝ → ℝ := fun j => stripPoint (extPath w) (extPath v) (extPath fun t => VR j t ω) with hqdef
  have hdata : ∀ S : ℝ≥0, IsStripLife w v (ζ ω) S → IsSepMark (extPath w) (extPath v) S ∧
      (∀ r ≤ S, ∀ i : Fin (n + 1), v r < VL i.castSucc r ω ∧ VL i.castSucc r ω < w r) ∧
      (∀ r ≤ S, ∀ j, v r < VR j r ω ∧ w r < VR j r ω) := fun S hS => by
    refine ⟨isSepMark_of_isIntegratedSLEPath hp hS, fun r hr i =>
      ⟨vL_last_lt_vL_castSucc hp (hS.mono hr) i, (hnc r (hS.mono hr)).1 i⟩, fun r hr j => ?_⟩
    have h1 := (hS.mono hr).2 r le_rfl
    have h2 := (hnc r (hS.mono hr)).2 j
    exact ⟨h1.trans h2, h2⟩
  have hlt : ∀ {S : ℝ≥0}, IsStripLife w v (ζ ω) S → ∀ r : ℝ≥0, r ≤ S → (r : ℝ≥0∞) < ζ ω :=
    fun hS r hr => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hS.1
  have hpeq : ∀ i s t, 0 ≤ s → s ≤ t → p i t - p i s = ∫ r in s..t, Sec4.cothHalf (p i r - ξ r) := by
    intro i s t hs hst
    obtain ⟨S, hS, htS⟩ := hcl t
    obtain ⟨hsm, hL, -⟩ := hdata S hS
    refine stripPoint_sub_eq hsm (continuousOn_extPath (hF.continuousOn_vL _) hS.1)
      (hF.intervalIntegrable_forceL hS.1 _) (fun r hr => ?_) (fun r hr => (hL r hr i).1)
      (fun r hr => (hL r hr i).2.ne) hs hst htS
    have e1 := hF.vL_eq (hlt hS r hr) i.castSucc
    have e0 := hF.vL_zero i.castSucc
    rw [e1, e0]
  have hqeq : ∀ j s t, 0 ≤ s → s ≤ t → q j t - q j s = ∫ r in s..t, Sec4.cothHalf (q j r - ξ r) := by
    intro j s t hs hst
    obtain ⟨S, hS, htS⟩ := hcl t
    obtain ⟨hsm, -, hR⟩ := hdata S hS
    refine stripPoint_sub_eq hsm (continuousOn_extPath (hF.continuousOn_vR _) hS.1)
      (hF.intervalIntegrable_forceR hS.1 _) (fun r hr => ?_) (fun r hr => (hR r hr j).1)
      (fun r hr => (hR r hr j).2.ne') hs hst htS
    have e1 := hF.vR_eq (hlt hS r hr) j
    have e0 := hF.vR_zero j
    rw [e1, e0]
  -- the driver identity
  set N : ℝ → ℝ := fun u => -(Real.sqrt κ * B' u.toNNReal ω) with hNdef
  set τd : ℝ := (τm - tauPlus κ ρL ρR τm) / 2 with hτd
  have hξeq : ∀ s t, 0 ≤ s → s ≤ t → ξ t - ξ s = -(N t - N s) - (∑ i, ρL i / 2 * (p i t - p i s)) -
      (∑ j, ρR j / 2 * (q j t - q j s)) + τd * (t - s) := by
    intro s t hs hst
    have e1 := (hdω t.toNNReal).2
    have e2 := (hdω s.toNNReal).2
    rw [Real.coe_toNNReal _ (hs.trans hst)] at e1
    rw [Real.coe_toNNReal _ hs] at e2
    have hL : (∑ i, ρL i / 2 * (p i t - p i s)) =
        (∑ i, ρL i / 2 * (p i t - pL i)) - ∑ i, ρL i / 2 * (p i s - pL i) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    have hR : (∑ j, ρR j / 2 * (q j t - q j s)) =
        (∑ j, ρR j / 2 * (q j t - pR j)) - ∑ j, ρR j / 2 * (q j s - pR j) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hL, hR]
    simp only [hNdef, hξdef, hpdef, hqdef, hτd] at e1 e2 ⊢
    linarith
  have hN : ∀ ε > 0, ∃ C, ∀ u, 0 ≤ u → |N u| ≤ C + ε * u := by
    intro ε hε
    have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    obtain ⟨C, hC⟩ := hsub (ε / Real.sqrt κ) (div_pos hε hsk)
    refine ⟨Real.sqrt κ * C, fun u hu => ?_⟩
    have h1 := hC u.toNNReal
    rw [Real.coe_toNNReal _ hu] at h1
    simp only [hNdef, abs_neg, abs_mul, abs_of_pos hsk]
    calc Real.sqrt κ * |B' u.toNNReal ω| ≤ Real.sqrt κ * (C + ε / Real.sqrt κ * u) :=
          mul_le_mul_of_nonneg_left h1 hsk.le
      _ = Real.sqrt κ * C + ε * u := by field_simp
  have hle : ∀ {S : ℝ≥0} {r : ℝ}, r ∈ Icc 0 (S : ℝ) → r.toNNReal ≤ S := fun hr =>
    Real.toNNReal_le_iff_le_coe.2 hr.2
  have hY : ∀ i u, 0 ≤ u → 0 < ξ u - p i u := fun i u hu => by
    obtain ⟨S, hS, huS⟩ := hcl u
    obtain ⟨hsm, hL, -⟩ := hdata S hS
    exact stripDriver_sub_stripPoint_pos hsm (y := extPath fun t => VL i.castSucc t ω)
      (fun r hr => ⟨(hL _ (hle hr) i).1, (hL _ (hle hr) i).2⟩) ⟨hu, huS⟩
  have hX : ∀ j u, 0 ≤ u → 0 < q j u - ξ u := fun j u hu => by
    obtain ⟨S, hS, huS⟩ := hcl u
    obtain ⟨hsm, -, hR⟩ := hdata S hS
    exact stripPoint_sub_stripDriver_pos hsm (y := extPath fun t => VR j t ω)
      (fun r hr => (hR _ (hle hr) j).2) ⟨hu, huS⟩
  have hY0 : ∀ i u, 0 ≤ u → ξ u - p 0 u ≤ ξ u - p i u := fun i u hu => by
    obtain ⟨S, hS, huS⟩ := hcl u
    obtain ⟨hsm, hL, -⟩ := hdata S hS
    have hc := hsm.chordalTime_mem ⟨hu, huS⟩
    set c := chordalTime (extPath w) (extPath v) u
    have hmono : VL i.castSucc c.toNNReal ω ≤ VL (0 : Fin (n + 1)).castSucc c.toNNReal ω :=
      hF.antitone_vL (hlt hS _ (hle hc)) (Fin.castSucc_le_castSucc_iff.2 (Fin.zero_le i))
    have h1 := (hL _ (hle hc) i).1
    have h0 := (hL _ (hle hc) 0).1
    simp only [hpdef, stripPoint, extPath] at h1 h0 hmono ⊢
    rw [abs_of_pos (sub_pos.2 h1), abs_of_pos (sub_pos.2 h0)]
    have := Real.log_le_log (sub_pos.2 h1) (sub_le_sub_right hmono _)
    linarith
  have hX0 : ∀ (hm : 0 < nR) j u, 0 ≤ u → q ⟨0, hm⟩ u - ξ u ≤ q j u - ξ u := fun hm j u hu => by
    obtain ⟨S, hS, huS⟩ := hcl u
    obtain ⟨hsm, -, hR⟩ := hdata S hS
    have hc := hsm.chordalTime_mem ⟨hu, huS⟩
    set c := chordalTime (extPath w) (extPath v) u
    have hmono : VR ⟨0, hm⟩ c.toNNReal ω ≤ VR j c.toNNReal ω :=
      hF.monotone_vR (hlt hS _ (hle hc)) (Fin.le_def.2 (Nat.zero_le _))
    have h1 := (hR _ (hle hc) j).1
    have h0 := (hR _ (hle hc) ⟨0, hm⟩).1
    simp only [hqdef, stripPoint, extPath] at h1 h0 hmono ⊢
    rw [abs_of_pos (sub_pos.2 h1), abs_of_pos (sub_pos.2 h0)]
    have := Real.log_le_log (sub_pos.2 h0) (sub_le_sub_right hmono _)
    linarith
  have hξc : ContinuousOn ξ (Ici 0) := continuousOn_Ici_of_forall_Icc fun T _ => by
    obtain ⟨S, hS, hTS⟩ := hcl T
    exact (hdata S hS).1.continuousOn_stripDriver.mono (Icc_subset_Icc le_rfl hTS)
  have hpc : ∀ i, ContinuousOn (p i) (Ici 0) := fun i => continuousOn_Ici_of_forall_Icc fun T _ => by
    obtain ⟨S, hS, hTS⟩ := hcl T
    obtain ⟨hsm, hL, -⟩ := hdata S hS
    exact (hsm.continuousOn_stripPoint (continuousOn_extPath (hF.continuousOn_vL _) hS.1)
      fun r hr => (hL _ (hle hr) i).1.ne').mono (Icc_subset_Icc le_rfl hTS)
  have hqc : ∀ j, ContinuousOn (q j) (Ici 0) := fun j => continuousOn_Ici_of_forall_Icc fun T _ => by
    obtain ⟨S, hS, hTS⟩ := hcl T
    obtain ⟨hsm, -, hR⟩ := hdata S hS
    exact (hsm.continuousOn_stripPoint (continuousOn_extPath (hF.continuousOn_vR _) hS.1)
      fun r hr => (hR _ (hle hr) j).1.ne').mono (Icc_subset_Icc le_rfl hTS)
  have hsL : 0 ≤ 1 + (∑ i, ρL i) / 2 := by
    have h := hpre.1 (Fin.last n)
    rw [show Finset.Iic (Fin.last n) = Finset.univ by ext; simp [Fin.le_last]] at h
    linarith
  have hΔ : 0 < 1 + (∑ i, ρL i) / 2 - (∑ j, ρR j) / 2 + τd := by
    simp only [hτd, tauPlus]
    simp only [chargeMinus] at hq
    linarith
  obtain ⟨α, hα, T, hT⟩ := exists_linear_escape_left (ξ := ξ) (p := p) (q := q) (N := N) (ρ := ρL)
    (σ := ρR) (τd := τd) hξc hpc hqc hpeq hqeq hξeq hY hX hY0 hX0 hN hsL hΔ
  obtain ⟨m, hm⟩ := exists_integral_sq_le_of_escape ρL (Y := fun i u => ξ u - p i u)
    (fun i => hξc.sub (hpc i)) hY hα (T := max T 0) fun i t ht =>
      (hT t ((le_max_left _ _).trans ht)).trans (hY0 i t ((le_max_right _ _).trans ht))
  exact ⟨m, hm⟩

/-! ### The discharged statements -/

/-- **Transience for every separated word, `0 < κ ≤ 4`** (Astra §3, "Chordal transience for an arbitrary finite
word"; the core of Aux. lemma 7 and of Wang–Wu's input 8.3). -/
theorem separatedTransienceStatement {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    SeparatedTransienceStatement.{u} κ :=
  separatedTransienceStatement_of_stripLeftEnergy hκ hκ4 (stripLeftEnergyStatement hκ)

/-- **Aux. lemma 7 for `0 < κ ≤ 4`** (Specification §2.2, p. 33): infinite lifetime, a continuous trace and
transience for every ordered word with admissible side partial sums. -/
theorem aux7Statement {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) : Sec4.Aux7Statement.{u} κ :=
  aux7Statement_of_stripLeftEnergy hκ hκ4 (stripLeftEnergyStatement hκ)

/-- **Wang–Wu's input 8.3** (Zhan's nonboundary transience at `κ = 4`). -/
theorem zhanNonboundaryTransience : WangWu.ZhanNonboundaryTransience.{u} :=
  zhanNonboundaryTransience_of_stripLeftEnergy (stripLeftEnergyStatement (by norm_num))

end InteractingSLE.Zhan
