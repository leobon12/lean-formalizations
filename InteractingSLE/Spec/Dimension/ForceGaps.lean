import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Sec2.OneForceLip
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# Nonzero force gaps at interior tips (input (O2) of Aux. lemma 15)

Packet PROVE-T11-DU2. Specification, proof of Aux. lemma 15 (`source/spec/p049-096.md`, L866, p. 89): "At an
interior physical tip every force gap is nonzero. Indeed, the inverse mapping-out function extends
continuously to the boundary of a finite continuous-trace hull … If such a coordinate equaled the driver,
continuity of the inverse map would make the current trace tip that real value, contrary to its being in
`ℍ`."

The source identifies each force coordinate with an original real mark or an extreme prime end (whose inverse
boundary values are real). Here the same conclusion is reached directly from the integrated force equation,
without identifying the coordinate: suppose the centred coordinate `û = V − W` (`û ≥ 0` on the right side)
vanishes at a time `t` whose tip `η(t) = F̄_t(0)` lies in `ℍ`.

* By continuity of the boundary extension `F̄_t` (`IsLoewnerTraceLT.hasBdryLimits`), `F̄_t(c) ∈ ℍ` for all real
  `c` with `|c| < ε₀`.
* Fix `0 < δ < c < ε₀` and solve the real Loewner equation **backward** from `c` at time `t`, with the drift
  `2/y` cut below at `δ` (`exists_backward_cut`, from PROVE-SEC2-ONE's global Lipschitz solutions
  `OneForce.lipSol` in reversed time).
* Comparison (`lt_of_backward_cut`): where `Y > û`, both are positive and the cut drift `2/max(Y, δ)` is at most
  `2/Y < 2/û`, so `Y − û` decreases there. If `Y ≤ δ` at some time `s₀`, then `Y − û ≤ δ` at `s₀`, hence
  `c = Y(t) − û(t) ≤ max(δ, 0) < c`. So `Y > δ` on `[0, t]`, and `Y` is a genuine solution of the centred forward
  flow from the real point `Y(0)` (`isForwardSol_ofReal`).
* Real starting points are boundary values (`IsLoewnerTraceLT.extendFrom_eq_of_isForwardSol`, from
  `RealPoints.lean`): `F̄_t(c) = Y(0) ∈ ℝ`, contradicting `F̄_t(c) ∈ ℍ`.

The left side follows by the reflection `(û, W) ↦ (−û, −W)` of the real equation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

/-! ### Real comparison lemmas -/

/-- A continuous function that decreases on every interval where it is positive ends below
`max (f α) 0`. -/
theorem le_max_of_antitone_of_pos {f : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hf : ContinuousOn f (Icc α β))
    (hmono : ∀ s₁ s₂, α ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ β → (∀ s ∈ Icc s₁ s₂, 0 < f s) → f s₂ ≤ f s₁) :
    f β ≤ max (f α) 0 := by
  by_contra hcon
  have hβ : max (f α) 0 < f β := not_le.1 hcon
  have hβ0 : 0 < f β := lt_of_le_of_lt (le_max_right _ _) hβ
  set S : Set ℝ := Icc α β ∩ f ⁻¹' Iic 0 with hS
  have hSc : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  by_cases hne : S.Nonempty
  · have hbdd : BddAbove S := ⟨β, fun s hs => hs.1.2⟩
    set r := sSup S with hr
    have hrS : r ∈ S := hSc.csSup_mem hne hbdd
    have hrβ : r < β := lt_of_le_of_ne hrS.1.2 fun h => by
      have : f r ≤ 0 := hrS.2
      rw [h] at this; linarith
    have hpos : ∀ s ∈ Ioc r β, 0 < f s := fun s hs => by
      by_contra h
      have hsS : s ∈ S := ⟨⟨hrS.1.1.trans hs.1.le, hs.2⟩, not_lt.1 h⟩
      exact absurd (le_csSup hbdd hsS) (not_le.2 hs.1)
    set C : Set ℝ := Icc α β ∩ f ⁻¹' Ici (f β) with hC
    have hCc : IsClosed C := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Ioc r β ⊆ C := fun s hs =>
      ⟨⟨hrS.1.1.trans hs.1.le, hs.2⟩, hmono s β (hrS.1.1.trans hs.1.le) hs.2 le_rfl
        fun s' hs' => hpos s' ⟨lt_of_lt_of_le hs.1 hs'.1, hs'.2⟩⟩
    have hrC : r ∈ C := by
      have h1 := closure_minimal hsub hCc
      rw [closure_Ioc hrβ.ne] at h1
      exact h1 ⟨le_rfl, hrβ.le⟩
    have h1 : f β ≤ f r := hrC.2
    have h2 : f r ≤ 0 := hrS.2
    linarith
  · have hpos : ∀ s ∈ Icc α β, 0 < f s := fun s hs => by
      by_contra h
      exact hne ⟨s, hs, not_lt.1 h⟩
    have := hmono α β le_rfl hαβ le_rfl hpos
    linarith [le_max_left (f α) 0]

/-- **Comparison with a cut backward solution.** Let `û ≥ 0` solve the centred real Loewner equation
`û(s₂) − û(s₁) = −(W(s₂) − W(s₁)) + ∫ 2/û` on `[0, t]` (integrable reciprocal, null zero set), with `û(t) = 0`.
Let `Y` solve the equation with the drift cut below at `δ`, `2/max(Y, δ)`, with `Y(t) = c > δ > 0`. Then
`Y > δ` on `[0, t]`. -/
theorem lt_of_backward_cut {W : ℝ → ℝ} {t : ℝ} {u Y : ℝ → ℝ} {c δ : ℝ}
    (hδ : 0 < δ) (hδc : δ < c) (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hut : u t = 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0)
    (hYc : ContinuousOn Y (Icc 0 t)) (hYt : Y t = c)
    (hYeq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      Y s₂ - Y s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, Bessel.regDrift 2 δ (Y s)) :
    ∀ s ∈ Icc (0 : ℝ) t, δ < Y s := by
  intro s₀ hs₀
  by_contra hcon
  have hY₀ : Y s₀ ≤ δ := not_lt.1 hcon
  have hsub0 : Icc s₀ t ⊆ Icc 0 t := Icc_subset_Icc_left hs₀.1
  have hreg : Continuous (Bessel.regDrift 2 δ) :=
    (Bessel.lipschitzWith_regDrift (by norm_num) hδ).continuous
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) t → u s ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [this] with s hs h1 h2
    exact hs ⟨h1, h2⟩
  have key := le_max_of_antitone_of_pos (f := fun s => Y s - u s) hs₀.2
    ((hYc.mono hsub0).sub (huc.mono hsub0)) ?_
  · simp only [hYt, hut, sub_zero] at key
    have : max (Y s₀ - u s₀) 0 ≤ δ := max_le (by linarith [hu0 s₀ hs₀]) hδ.le
    linarith
  intro s₁ s₂ h1 h12 h2 hpos
  have hs₁ : s₁ ∈ Icc (0 : ℝ) t := ⟨hs₀.1.trans h1, h12.trans h2⟩
  have hs₂ : s₂ ∈ Icc (0 : ℝ) t := ⟨hs₀.1.trans (h1.trans h12), h2⟩
  have hI : Icc s₁ s₂ ⊆ Icc 0 t := Icc_subset_Icc hs₁.1 h2
  have hint1 : IntervalIntegrable (fun s => Bessel.regDrift 2 δ (Y s)) volume s₁ s₂ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h12]
    exact hreg.comp_continuousOn (hYc.mono hI)
  have ht0 : (0 : ℝ) ≤ t := hs₀.1.trans hs₀.2
  have hint2 : IntervalIntegrable (fun s => 2 / u s) volume s₁ s₂ :=
    huint.mono_set (by rw [uIcc_of_le h12, uIcc_of_le ht0]; exact hI)
  have hdiff : (Y s₂ - u s₂) - (Y s₁ - u s₁) =
      ∫ s in s₁..s₂, (Bessel.regDrift 2 δ (Y s) - 2 / u s) := by
    rw [intervalIntegral.integral_sub hint1 hint2]
    have e1 := hYeq s₁ hs₁ s₂ hs₂ h12
    have e2 := hueq s₁ hs₁ s₂ hs₂ h12
    linarith
  have hnn : 0 ≤ ∫ s in s₁..s₂, (2 / u s - Bessel.regDrift 2 δ (Y s)) := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict h12 ?_
    have hmem : ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)), s ∈ Icc s₁ s₂ :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem, ae_restrict_of_ae hae] with s hs hsu
    have hu' : 0 < u s := lt_of_le_of_ne (hu0 s (hI hs)) (Ne.symm (hsu (hI hs)))
    have hYu : u s < Y s := by
      have := hpos s hs
      linarith
    have hYpos : 0 < Y s := hu'.trans hYu
    have h1 : Bessel.regDrift 2 δ (Y s) ≤ 2 / Y s := by
      show 2 / max (Y s) δ ≤ 2 / Y s
      exact div_le_div_of_nonneg_left (by norm_num) hYpos (le_max_left _ _)
    have h2 : 2 / Y s ≤ 2 / u s := div_le_div_of_nonneg_left (by norm_num) hu' hYu.le
    show (0 : ℝ) ≤ 2 / u s - Bessel.regDrift 2 δ (Y s)
    linarith
  rw [intervalIntegral.integral_sub hint2 hint1] at hnn
  rw [intervalIntegral.integral_sub hint1 hint2] at hdiff
  show Y s₂ - u s₂ ≤ Y s₁ - u s₁
  linarith

/-- **A cut backward solution** of the centred real Loewner equation: for any `c` and `δ > 0` there is a
continuous `Y` on `[0, t]` with `Y(t) = c` and `Y(s₂) − Y(s₁) = −(W(s₂) − W(s₁)) + ∫_{s₁}^{s₂} 2/max(Y, δ)`.
(PROVE-SEC2-ONE's global solution `OneForce.lipSol` of `Z = c + w + ∫ f(Z)` for the bounded Lipschitz drift
`f = −2/max(·, δ)` and `w(r) = W(t) − W(t − r)`, read in reversed time `Y(s) = Z(t − s)`.) -/
theorem exists_backward_cut {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) (c : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ Y : ℝ → ℝ, ContinuousOn Y (Icc 0 t) ∧ Y t = c ∧
      ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
        Y s₂ - Y s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, Bessel.regDrift 2 δ (Y s) := by
  have hlip := Bessel.lipschitzWith_regDrift (c := 2) (by norm_num) hδ
  have hreg : Continuous (Bessel.regDrift 2 δ) := hlip.continuous
  have hD : OneForce.LipData (fun y => -Bessel.regDrift 2 δ y) (fun r => W t - W (t - r)) :=
    ⟨⟨_, hlip.neg⟩, ⟨2 / δ, fun y => by
      rw [abs_neg]; exact Bessel.abs_regDrift_le (by norm_num) hδ y⟩,
      continuous_const.sub (hW.comp (continuous_const.sub continuous_id))⟩
  set Z := OneForce.lipSol (fun y => -Bessel.regDrift 2 δ y) c (fun r => W t - W (t - r)) with hZ
  have hZc : ContinuousOn Z (Icc 0 t) := OneForce.continuousOn_lipSol hD ht c
  have hYc : ContinuousOn (fun s => Z (t - s)) (Icc 0 t) :=
    hZc.comp (continuous_const.sub continuous_id).continuousOn
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
  have hform : ∀ s ∈ Icc (0 : ℝ) t, Z (t - s) =
      c + W t - W s - ∫ x in s..t, Bessel.regDrift 2 δ (Z (t - x)) := by
    intro s hs
    have h1 := OneForce.lipSol_eq hD c (show 0 ≤ t - s by linarith [hs.2])
    have h2 := intervalIntegral.integral_comp_sub_left
      (fun x => Bessel.regDrift 2 δ (Z (t - x))) (a := (0 : ℝ)) (b := t - s) t
    simp only [sub_sub_cancel, sub_zero] at h2
    rw [← hZ] at h1
    rw [h1, intervalIntegral.integral_neg, ← h2, sub_sub_cancel]
    ring
  refine ⟨fun s => Z (t - s), hYc, ?_, fun s₁ hs₁ s₂ hs₂ h12 => ?_⟩
  · show Z (t - t) = c
    rw [sub_self, hZ, OneForce.lipSol_zero hD, sub_zero, sub_self, add_zero]
  · have hint : ∀ a b, a ∈ Icc (0 : ℝ) t → b ∈ Icc (0 : ℝ) t →
        IntervalIntegrable (fun x => Bessel.regDrift 2 δ (Z (t - x))) volume a b := by
      intro a b ha hb
      apply ContinuousOn.intervalIntegrable
      refine hreg.comp_continuousOn (hYc.mono ?_)
      exact uIcc_subset_Icc ha hb
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hint s₁ s₂ hs₁ hs₂)
      (hint s₂ t hs₂ ⟨ht, le_rfl⟩)
    show Z (t - s₂) - Z (t - s₁) = _
    rw [hform s₂ hs₂, hform s₁ hs₁, ← hadd]
    ring

/-- A real path solving the centred Loewner equation without touching `0` is a solution of the
centred forward flow from the real point `Y(0)` (`W 0 = 0`). -/
theorem isForwardSol_ofReal {W : ℝ → ℝ} (hW0 : W 0 = 0) {t : ℝ} {Y : ℝ → ℝ}
    (hYc : ContinuousOn Y (Icc 0 t)) (hY0 : ∀ s ∈ Icc (0 : ℝ) t, Y s ≠ 0)
    (hYeq : ∀ s ∈ Icc (0 : ℝ) t, Y s - Y 0 = -(W s - W 0) + ∫ r in (0 : ℝ)..s, 2 / Y r) :
    IsForwardSol W (Y 0 : ℂ) t (fun s => (Y s : ℂ)) := by
  refine ⟨continuous_ofReal.comp_continuousOn hYc, fun s hs => ⟨ofReal_ne_zero.2 (hY0 s hs), ?_⟩⟩
  have h1 : ∫ r in (0 : ℝ)..s, (2 : ℂ) / (Y r : ℂ) = ((∫ r in (0 : ℝ)..s, 2 / Y r : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext r
    push_cast
    rfl
  rw [h1]
  have h2 := hYeq s hs
  rw [hW0] at h2
  have h3 : Y s = Y 0 - W s + ∫ r in (0 : ℝ)..s, 2 / Y r := by linarith
  show ((Y s : ℝ) : ℂ) = _
  rw [h3]
  push_cast
  ring

/-! ### Boundary values of `F̄_t` -/

section Boundary

variable {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}

/-- **Real starting points are boundary values of `F̄_t`.** If the centred forward flow from a real point
`x` has a real solution `y` on `[0, t]`, then `F̄_t(y(t)) = x`. -/
theorem IsLoewnerTraceLT.extendFrom_eq_of_isForwardSol (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) {x : ℝ}
    {y : ℝ → ℝ} (hu : IsForwardSol W (x : ℂ) t (fun s => (y s : ℂ))) :
    extendFrom H (fwdMapInv W t) (y t : ℂ) = x := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ht hu
  set E := Real.exp (2 / δ ^ 2 * t) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fwdHull W t := by
    have hball : Metric.ball (x : ℂ) (δ / E) ∈ 𝓝 (x : ℂ) := Metric.ball_mem_nhds _ (by positivity)
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzH
    refine ⟨hzH, not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzH ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc ‖z - (x : ℂ)‖ * E < δ / E * E := mul_lt_mul_of_pos_right hz hE
      _ = δ := div_mul_cancel₀ _ hE.ne'
  have hf := tendsto_fwdMap_of_isForwardSol hW ht hu
  have hf' : Tendsto (fwdMap W t) (𝓝[H] (x : ℂ)) (𝓝[H] (y t : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hf, hev.mono fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz⟩
  have hB := (hη.hasBdryLimits hW hW0 ht htT).tendsto
    (mem_Hbar_of_im_eq_zero (z := (y t : ℂ)) (by simp))
  have hid : Tendsto (fun z : ℂ => z) (𝓝[H] (x : ℂ))
      (𝓝 (extendFrom H (fwdMapInv W t) (y t : ℂ))) := by
    refine (hB.comp hf').congr' (hev.mono fun z hz => ?_)
    exact QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hz
  have hne : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_H]; exact mem_Hbar_of_im_eq_zero (by simp))
  exact tendsto_nhds_unique hid (tendsto_id.mono_left nhdsWithin_le_nhds)

/-- If the tip `η(t) = F̄_t(0)` is in `ℍ`, so is `F̄_t(c)` for all real `c` near `0`. -/
theorem IsLoewnerTraceLT.exists_extendFrom_mem_H (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) (hηH : η t ∈ H) :
    ∃ ε > 0, ∀ c : ℝ, |c| < ε → extendFrom H (fwdMapInv W t) (c : ℂ) ∈ H := by
  have hcont := (hη.hasBdryLimits hW hW0 ht htT).continuousOn
  have h0 : (0 : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hmem : extendFrom H (fwdMapInv W t) ⁻¹' H ∈ 𝓝[Hbar] (0 : ℂ) := by
    refine (hcont 0 h0).preimage_mem_nhdsWithin (QuantumZipper.isOpen_H.mem_nhds ?_)
    rw [hη.extendFrom_zero hW hW0 ht htT]
    exact hηH
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hmem
  refine ⟨ε, hε, fun c hc => hball ⟨?_, mem_Hbar_of_im_eq_zero (by simp)⟩⟩
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact hc

end Boundary

/-! ### Nonzero gaps at interior tips -/

/-- **(O2), deterministic core.** Let `η` be a continuous Loewner trace of `W` before `T`, `0 ≤ t < T`, and
let `u` be a one-signed solution on `[0, t]` of the centred real Loewner equation
`u(s₂) − u(s₁) = −(W(s₂) − W(s₁)) + ∫ 2/u` (integrable reciprocal, null zero set) — a centred force coordinate
`V − W`. If `u(t) = 0` (a force collision at `t`), the tip `η(t)` is not in `ℍ`. -/
theorem IsLoewnerTraceLT.not_mem_H_of_eq_zero {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (htT : t < T) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 t))
    (hside : (∀ s ∈ Icc (0 : ℝ) t, 0 ≤ u s) ∨ ∀ s ∈ Icc (0 : ℝ) t, u s ≤ 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) (hut : u t = 0) : η t ∉ H := by
  intro hηH
  obtain ⟨ε, hε, hεH⟩ := hη.exists_extendFrom_mem_H hW hW0 ht htT hηH
  have hδ : 0 < ε / 4 := by positivity
  have hδc : ε / 4 < ε / 2 := by linarith
  have hreal : ∀ r : ℝ, ((r : ℝ) : ℂ) ∉ H := fun r h => by
    have : (0 : ℝ) < ((r : ℝ) : ℂ).im := h
    simp at this
  rcases hside with hpos | hneg
  · obtain ⟨Y, hYc, hYt, hYeq⟩ := exists_backward_cut hW ht (ε / 2) hδ
    have hYgt := lt_of_backward_cut hδ hδc huc hpos hut hueq huint hnull hYc hYt hYeq
    have hsol : IsForwardSol W (Y 0 : ℂ) t (fun s => (Y s : ℂ)) := by
      refine isForwardSol_ofReal hW0 hYc (fun s hs => (hδ.trans (hYgt s hs)).ne') fun s hs => ?_
      rw [hYeq 0 ⟨le_rfl, ht⟩ s hs hs.1]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      exact Bessel.regDrift_of_le (hYgt r ⟨hr.1, hr.2.trans hs.2⟩).le
    have h1 := hη.extendFrom_eq_of_isForwardSol hW hW0 ht htT hsol
    rw [hYt] at h1
    have h2 := hεH (ε / 2) (by rw [abs_of_pos (by positivity)]; linarith)
    rw [h1] at h2
    exact hreal _ h2
  · -- reflect `(u, W) ↦ (−u, −W)`
    have hW' : Continuous fun s => -W s := hW.neg
    have hu'eq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
        -u s₂ - -u s₁ = -(-W s₂ - -W s₁) + ∫ s in s₁..s₂, 2 / -u s := by
      intro s₁ hs₁ s₂ hs₂ h12
      have h := hueq s₁ hs₁ s₂ hs₂ h12
      have e : ∫ s in s₁..s₂, 2 / -u s = -∫ s in s₁..s₂, 2 / u s := by
        rw [← intervalIntegral.integral_neg]
        congr 1
        funext s
        rw [div_neg]
      rw [e]
      linarith
    have hu'int : IntervalIntegrable (fun s => 2 / -u s) volume 0 t := by
      have e : (fun s => 2 / -u s) = -(fun s => 2 / u s) := by
        funext s
        simp [div_neg]
      rw [e]
      exact huint.neg
    have hnull' : volume {s | s ∈ Icc (0 : ℝ) t ∧ -u s = 0} = 0 := by
      simpa only [neg_eq_zero] using hnull
    obtain ⟨Y, hYc, hYt, hYeq⟩ := exists_backward_cut hW' ht (ε / 2) hδ
    have hYgt := lt_of_backward_cut (u := fun s => -u s) (W := fun s => -W s) hδ hδc huc.neg
      (fun s hs => neg_nonneg.2 (hneg s hs)) (show -u t = 0 by rw [hut, neg_zero]) hu'eq hu'int
      hnull' hYc hYt hYeq
    have hsol : IsForwardSol W (((fun s => -Y s) 0 : ℝ) : ℂ) t
        (fun s => (((fun s => -Y s) s : ℝ) : ℂ)) := by
      refine isForwardSol_ofReal hW0 hYc.neg
        (fun s hs => neg_ne_zero.2 (hδ.trans (hYgt s hs)).ne') fun s hs => ?_
      have h := hYeq 0 ⟨le_rfl, ht⟩ s hs hs.1
      have e : ∫ r in (0 : ℝ)..s, Bessel.regDrift 2 (ε / 4) (Y r) =
          -∫ r in (0 : ℝ)..s, 2 / -Y r := by
        rw [← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hs.1] at hr
        simp only [Bessel.regDrift_of_le (hYgt r ⟨hr.1, hr.2.trans hs.2⟩).le, div_neg, neg_neg]
      rw [e] at h
      show -Y s - -Y 0 = -(W s - W 0) + ∫ r in (0 : ℝ)..s, 2 / -Y r
      linarith
    have h1 := hη.extendFrom_eq_of_isForwardSol hW hW0 ht htT hsol
    simp only [hYt] at h1
    have h2 := hεH (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    rw [show (((-(ε / 2) : ℝ)) : ℂ) = ((-(ε / 2) : ℝ) : ℂ) from rfl, h1] at h2
    exact hreal _ h2

/-- **(O2) for one force coordinate of a frozen path.** Let `η` be a frozen generating trace of `w` before `ζ`
(`w` continuous before `ζ`, `w 0 = 0`) and `v` a force coordinate on one side of `w` satisfying its integrated
equation `v = x + ∫ 2/(v − w)` with integrable reciprocal gap and a Lebesgue-null collision set. At every
`t < ζ` with `η(t) ∈ ℍ`, `w(t) ≠ v(t)`. -/
theorem ne_of_mem_H_of_mark {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {v : ℝ≥0 → ℝ} {x : ℝ}
    (hv : ContinuousOn v {s | (s : ℝ≥0∞) < ζ})
    (hside : (∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → w s ≤ v s) ∨ ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → v s ≤ w s)
    (hint : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 s)
    (heq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ →
      v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal))
    (hnull : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = v s.toNNReal} = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hηt : η t ∈ H) : w t ≠ v t := by
  intro hcol
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := exists_real_btwn_of_lt ht
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  set W := frozenDrive w t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hw ht₂ζ
  have hW0 : W 0 = 0 := by rw [hWdef, frozenDrive_zero ht₂, hw0]
  have hL := hη.isLoewnerTraceLT ht₂ζ
  set T : ℝ := (t : ℝ) with hT
  have hT0 : 0 ≤ T := NNReal.coe_nonneg t
  have hlt : ∀ s ∈ Icc (0 : ℝ) T, ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2)) ht
  have hWeq : ∀ s ∈ Icc (0 : ℝ) T, W s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans htt₂.le⟩
  set u : ℝ → ℝ := fun s => v s.toNNReal - W s with hu
  have hu_eq : ∀ s ∈ Icc (0 : ℝ) T, u s = v s.toNNReal - w s.toNNReal := fun s hs => by
    simp only [hu, hWeq s hs]
  have huc : ContinuousOn u (Icc 0 T) :=
    (hv.comp continuous_real_toNNReal.continuousOn fun s hs => hlt s hs).sub hW.continuousOn
  have hint' : ∀ s ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 s := by
    intro s hs
    have h := hint s.toNNReal (hlt s hs)
    rw [Real.coe_toNNReal _ hs.1] at h
    have e : (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) =
        fun r => (-2) * (w r.toNNReal - v r.toNNReal)⁻¹ := by
      funext r
      rw [div_eq_mul_inv, ← neg_sub, inv_neg]
      ring
    rw [e]
    exact h.const_mul _
  have heq' : ∀ s ∈ Icc (0 : ℝ) T,
      v s.toNNReal = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal) := by
    intro s hs
    have h := heq s.toNNReal (hlt s hs)
    rwa [Real.coe_toNNReal _ hs.1] at h
  have hcongr : ∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T,
      (∫ r in s₁..s₂, 2 / (v r.toNNReal - w r.toNNReal)) = ∫ r in s₁..s₂, 2 / u r := by
    intro s₁ hs₁ s₂ hs₂
    refine intervalIntegral.integral_congr fun r hr => ?_
    simp only [hu_eq r (uIcc_subset_Icc hs₁ hs₂ hr)]
  have hueq : ∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s := by
    intro s₁ hs₁ s₂ hs₂ _
    rw [← hcongr s₁ hs₁ s₂ hs₂,
      ← intervalIntegral.integral_interval_sub_left (hint' s₂ hs₂) (hint' s₁ hs₁)]
    have e1 := heq' s₁ hs₁
    have e2 := heq' s₂ hs₂
    simp only [hu]
    linarith
  have huint : IntervalIntegrable (fun s => 2 / u s) volume 0 T := by
    have h := hint' T ⟨hT0, le_rfl⟩
    rw [intervalIntegrable_iff] at h ⊢
    refine h.congr_fun (fun r hr => ?_) measurableSet_uIoc
    rw [uIoc_of_le hT0] at hr
    simp only [hu_eq r ⟨hr.1.le, hr.2⟩]
  have hnull' : volume {s | s ∈ Icc (0 : ℝ) T ∧ u s = 0} = 0 := by
    refine measure_mono_null (fun s hs => ?_) hnull
    refine ⟨hs.1.1, hlt s hs.1, ?_⟩
    have h := hs.2
    rw [hu_eq s hs.1] at h
    linarith
  have hside' : (∀ s ∈ Icc (0 : ℝ) T, 0 ≤ u s) ∨ ∀ s ∈ Icc (0 : ℝ) T, u s ≤ 0 := by
    rcases hside with h | h
    · exact Or.inl fun s hs => by rw [hu_eq s hs]; linarith [h _ (hlt s hs)]
    · exact Or.inr fun s hs => by rw [hu_eq s hs]; linarith [h _ (hlt s hs)]
  have hut : u T = 0 := by
    rw [hu_eq T ⟨hT0, le_rfl⟩, hT, Real.toNNReal_coe, hcol, sub_self]
  exact hL.not_mem_H_of_eq_zero hW hW0 hT0 htt₂ huc hside' hueq huint hnull' hut
    (by simpa [hT] using hηt)

/-- **(O2): nonzero force gaps at interior tips** (Aux. lemma 15, first paragraph of the proof; graph node
`SPEC.aux-15#nonzero-gaps-at-tip`), pathwise. For an integrated `SLE_a(ρ)` path with a continuous generating
trace `η` before its lifetime `ζ`, at every `t < ζ` with `η(t) ∈ ℍ` every force coordinate differs from the
driver. -/
theorem IsIntegratedSLEPath.forall_ne_of_mem_H {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ζ η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hηt : η t ∈ H) :
    (∀ i, w t ≠ vL i t) ∧ ∀ i, w t ≠ vR i t := by
  obtain ⟨hw0, -, -, hwc, hvLc, hvRc, -, hvLw, hwvR, -, hgapL, hgapR, -, hvLeq, hvReq, hcolL,
    hcolR, -⟩ := hp
  exact ⟨fun i => ne_of_mem_H_of_mark hη hwc hw0 (hvLc i) (Or.inr fun s hs => hvLw s hs i)
      (fun s hs => hgapL s hs i) (fun s hs => hvLeq s hs i) (hcolL i) ht hηt,
    fun i => ne_of_mem_H_of_mark hη hwc hw0 (hvRc i) (Or.inl fun s hs => hwvR s hs i)
      (fun s hs => hgapR s hs i) (fun s hs => hvReq s hs i) (hcolR i) ht hηt⟩

/-- **(O2) for evolutions**: almost surely, for every continuous generating trace before the lifetime, every
force gap is nonzero at every interior tip. -/
theorem IsIntegratedSLEEvolution.ae_forall_ne_of_mem_H {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η t ∈ H →
        (∀ i, W t ω ≠ VL i t ω) ∧ ∀ i, W t ω ≠ VR i t ω :=
  hE.2.2.2.2.mono fun _ hp _ hη _ ht hηt => hp.forall_ne_of_mem_H hη ht hηt

end InteractingSLE
