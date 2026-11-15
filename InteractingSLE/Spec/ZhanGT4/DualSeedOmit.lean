/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedClear
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Zhan's A.1.6, the conformal part II: a seed coordinate is never the image of an alive real point

Packet PROVE-ZHAN-GT4-A19. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L431, R38): "For a mark `p_m = x_j^±`, interpret `g_j(p_m)` as its integrated force
coordinate `V_j^m` … The seed inequalities in the coupling statement imply `V_j^m ≠ W_j` at every positive time before
lifetime."

The uniform clearance of `DualSeedClear` holds at every real value that no alive real point is mapped to. A seed
coordinate `V` (`V_0 = W_0`, `V_s = V_0 + ∫_0^s 2/(V − W)`, `V ≠ W` at positive times) is such a value: if
`g_s(y) = V_s` for an alive real `y ≠ W_0` and a first time `s₀ > 0`, both `g_·(y)` and `V` solve the Loewner ODE
`ẋ = 2/(x − W)` near `s₀` away from the driver (Lipschitz there), and backward uniqueness (Mathlib's
`ODE_solution_unique_of_mem_Icc_left`) makes them equal before `s₀`, a contradiction.

## Main results

* `hasDerivWithinAt_integral_gap`: the left derivative of `s ↦ x₀ + ∫₀ˢ 2/(X − W)` (Loewner ODE from the integrated
  equation);
* `lipschitzOnWith_loewner`: `x ↦ 2/(x − w)` is `2/c²`-Lipschitz on `{‖x − w‖ ≥ c}`;
* **`seed_ne_fwdMap`**: `g_t(y) = u_t + W_t ≠ V_t` for every alive real `y ≠ W_0`, `t > 0`;
* **`exists_le_norm_fwdMap_sub_seed_uniform`**: the uniform clearance at seed coordinates.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- **The Loewner vector field is Lipschitz away from the driver**: `x ↦ 2/(x − w)` is `(2/c²)`-Lipschitz on
`{x : c ≤ ‖x − w‖}`. -/
theorem lipschitzOnWith_loewner {w : ℂ} {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith (2 / c ^ 2).toNNReal (fun x : ℂ => 2 / (x - w)) {x | c ≤ ‖x - w‖} := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hx0 : x - w ≠ 0 := fun h => by
    have : c ≤ ‖x - w‖ := hx; rw [h, norm_zero] at this; linarith
  have hy0 : y - w ≠ 0 := fun h => by
    have : c ≤ ‖y - w‖ := hy; rw [h, norm_zero] at this; linarith
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  have e : 2 / (x - w) - 2 / (y - w) = 2 * (y - x) / ((x - w) * (y - w)) := by
    field_simp; ring
  rw [e, norm_div, norm_mul, norm_mul, norm_sub_rev y x]
  have hxy : c * c ≤ ‖x - w‖ * ‖y - w‖ := mul_le_mul hx hy hc.le (norm_nonneg _)
  have hpos : 0 < ‖x - w‖ * ‖y - w‖ := by positivity
  rw [div_le_iff₀ hpos]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  calc 2 * ‖x - y‖ = 2 / c ^ 2 * ‖x - y‖ * (c * c) := by field_simp
    _ ≤ 2 / c ^ 2 * ‖x - y‖ * (‖x - w‖ * ‖y - w‖) := by gcongr

/-- **The left derivative of an integrated Loewner coordinate**: if `X s = x₀ + ∫₀ˢ f` with `f` interval integrable on
`[0, s]` and continuous within `[0, s]` at `s > 0`, then `X` has left derivative `f s` at `s`. -/
theorem hasDerivWithinAt_integral_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {x₀ : E} {s : ℝ} (hs : 0 < s)
    (hint : IntervalIntegrable f volume 0 s) (hc : ContinuousWithinAt f (Icc 0 s) s) :
    HasDerivWithinAt (fun r => x₀ + ∫ τ in (0 : ℝ)..r, f τ) (f s) (Iic s) s := by
  have hc' : ContinuousWithinAt f (Iic s) s := by
    have hmem : Icc 0 s ∈ 𝓝[Iic s] s := Icc_mem_nhdsLE hs
    exact hc.mono_of_mem_nhdsWithin hmem
  have hmeas : StronglyMeasurableAtFilter f (𝓝[Iic s] s) volume := by
    refine ⟨Ioc (s / 2) s, ?_, ?_⟩
    · exact Ioc_mem_nhdsLE (by linarith)
    · exact hint.1.aestronglyMeasurable.mono_set (Ioc_subset_Ioc (by linarith) le_rfl)
  have h := intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := s) (f := f) (s := Iic s)
    (t := Iic s) hint hmeas hc'
  exact h.const_add x₀

/-- **A seed coordinate is never the image of an alive real point.** Let `V` be continuous on `[0, t]`, `t > 0`, with
`V 0 = W 0`, `V ≠ W` on `(0, t]` and `V s = V 0 + ∫₀ˢ 2/(V − W)`; let `y ≠ W 0` be alive at `t` (`u` the centered
forward flow). Then `g_t(y) = u_t + W_t ≠ V_t`. -/
theorem seed_ne_fwdMap {W : ℝ → ℝ} (hW : Continuous W) {V : ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hVc : ContinuousOn V (Icc 0 t)) (hV0 : V 0 = W 0) (hVne : ∀ s ∈ Ioc 0 t, V s ≠ W s)
    (hVint : ∀ s ∈ Icc 0 t, IntervalIntegrable (fun r => 2 / (V r - W r)) volume 0 s)
    (hVeq : ∀ s ∈ Icc 0 t, V s = V 0 + ∫ r in (0 : ℝ)..s, 2 / (V r - W r))
    {y : ℝ} (hy : y ≠ W 0) {u : ℝ → ℂ} (hu : IsForwardSol W (y : ℂ) t u) :
    u t + (W t : ℂ) ≠ (V t : ℂ) := by
  set X₁ : ℝ → ℂ := fun s => u s + W s with hX₁
  set X₂ : ℝ → ℂ := fun s => (V s : ℂ) with hX₂
  have hWc : Continuous fun s => (W s : ℂ) := continuous_ofReal.comp hW
  have hX₁c : ContinuousOn X₁ (Icc 0 t) := hu.1.add hWc.continuousOn
  have hX₂c : ContinuousOn X₂ (Icc 0 t) := continuous_ofReal.comp_continuousOn hVc
  have hu0 : ∀ s ∈ Icc (0 : ℝ) t, u s ≠ 0 := fun s hs => (hu.2 s hs).1
  -- the zero set of `X₁ − X₂`
  set Z : Set ℝ := Icc 0 t ∩ (fun s => X₁ s - X₂ s) ⁻¹' {0} with hZ
  have hZc : IsClosed Z := (hX₁c.sub hX₂c).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  by_contra hcon
  have htZ : t ∈ Z := ⟨⟨ht.le, le_rfl⟩, by simp [hX₁, hX₂, hcon]⟩
  have hZne : Z.Nonempty := ⟨t, htZ⟩
  have hZbdd : BddBelow Z := ⟨0, fun s hs => hs.1.1⟩
  set t₀ := sInf Z with ht₀
  have ht₀Z : t₀ ∈ Z := hZc.csInf_mem hZne hZbdd
  -- `t₀ > 0`
  have hX0 : X₁ 0 - X₂ 0 ≠ 0 := by
    have h0 := (hu.2 0 ⟨le_rfl, ht.le⟩).2
    simp only [intervalIntegral.integral_same, add_zero] at h0
    simp only [hX₁, hX₂, h0, hV0, sub_add_cancel, ne_eq, sub_eq_zero]
    exact fun h => hy (by exact_mod_cast h)
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀Z.1.1 with h | h
    · exact absurd (by rw [h]; exact ht₀Z.2) hX0
    · exact h
  have ht₀t : t₀ ≤ t := ht₀Z.1.2
  set a : ℝ := t₀ / 2 with ha
  have hat : Icc a t₀ ⊆ Ioc 0 t := fun s hs => ⟨by linarith [hs.1], hs.2.trans ht₀t⟩
  have hat' : Icc a t₀ ⊆ Icc 0 t := fun s hs => Ioc_subset_Icc_self (hat hs)
  -- a uniform distance from the driver on `[a, t₀]`
  obtain ⟨c₁, hc₁, hc₁le⟩ : ∃ c₁ > 0, ∀ s ∈ Icc a t₀, c₁ ≤ ‖u s‖ := by
    obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := a) (b := t₀)).exists_isMinOn
      (nonempty_Icc.2 (by linarith)) ((hu.1.mono hat').norm)
    exact ⟨‖u s₀‖, norm_pos_iff.2 (hu0 s₀ (hat' hs₀)), fun s hs => hmin hs⟩
  obtain ⟨c₂, hc₂, hc₂le⟩ : ∃ c₂ > 0, ∀ s ∈ Icc a t₀, c₂ ≤ ‖X₂ s - W s‖ := by
    have hcont : ContinuousOn (fun s => ‖X₂ s - W s‖) (Icc a t₀) :=
      ((hX₂c.mono hat').sub hWc.continuousOn).norm
    obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := a) (b := t₀)).exists_isMinOn
      (nonempty_Icc.2 (by linarith)) hcont
    refine ⟨‖X₂ s₀ - W s₀‖, norm_pos_iff.2 (sub_ne_zero.2 fun h => hVne s₀ (hat hs₀) ?_), fun s hs => hmin hs⟩
    simp only [hX₂] at h
    exact_mod_cast h
  set c := min c₁ c₂ with hc
  have hcpos : 0 < c := lt_min hc₁ hc₂
  -- the two Loewner ODE solutions
  have hd₁ : ∀ s ∈ Ioc a t₀, HasDerivWithinAt X₁ (2 / (X₁ s - W s)) (Iic s) s := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hst : s ≤ t := hs.2.trans ht₀t
    have hcont : ContinuousOn (fun r => 2 / u r) (Icc 0 t) :=
      continuousOn_const.div hu.1 hu0
    have hint : IntervalIntegrable (fun r => 2 / u r) volume 0 s :=
      (hcont.mono (Icc_subset_Icc le_rfl hst)).intervalIntegrable_of_Icc hs0.le
    have hcw : ContinuousWithinAt (fun r => 2 / u r) (Icc 0 s) s :=
      (hcont.mono (Icc_subset_Icc le_rfl hst)) s ⟨hs0.le, le_rfl⟩
    have h := hasDerivWithinAt_integral_left (x₀ := (y : ℂ)) hs0 hint hcw
    have heq : EqOn X₁ (fun r => (y : ℂ) + ∫ τ in (0 : ℝ)..r, 2 / u τ) (Icc 0 t) := fun r hr => by
      simp only [hX₁, (hu.2 r hr).2]; ring
    have hev : X₁ =ᶠ[𝓝[Iic s] s] fun r => (y : ℂ) + ∫ τ in (0 : ℝ)..r, 2 / u τ := by
      filter_upwards [Icc_mem_nhdsLE hs0] with r hr
      exact heq ⟨hr.1, hr.2.trans hst⟩
    have h' := h.congr_of_eventuallyEq hev (heq ⟨hs0.le, hst⟩)
    have hX₁W : X₁ s - W s = u s := by simp only [hX₁, add_sub_cancel_right]
    rw [hX₁W]
    exact h'
  have hd₂ : ∀ s ∈ Ioc a t₀, HasDerivWithinAt X₂ (2 / (X₂ s - W s)) (Iic s) s := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hst : s ≤ t := hs.2.trans ht₀t
    have hcw : ContinuousWithinAt (fun r => 2 / (V r - W r)) (Icc 0 s) s :=
      (continuousWithinAt_const.div ((hVc.mono (Icc_subset_Icc le_rfl hst)).sub hW.continuousOn s
        ⟨hs0.le, le_rfl⟩) (sub_ne_zero.2 (hVne s ⟨hs0, hst⟩)))
    have h := hasDerivWithinAt_integral_left (x₀ := V 0) hs0 (hVint s ⟨hs0.le, hst⟩) hcw
    have hev : V =ᶠ[𝓝[Iic s] s] fun r => V 0 + ∫ τ in (0 : ℝ)..r, 2 / (V τ - W τ) := by
      filter_upwards [Icc_mem_nhdsLE hs0] with r hr
      exact hVeq r ⟨hr.1, hr.2.trans hst⟩
    have h' := (h.congr_of_eventuallyEq hev (hVeq s ⟨hs0.le, hst⟩)).ofReal_comp
    have e : ((2 / (V s - W s) : ℝ) : ℂ) = 2 / (X₂ s - W s) := by simp only [hX₂]; push_cast; ring
    rw [← e]
    exact h'
  -- backward uniqueness on `[a, t₀]`
  have hLip : ∀ s ∈ Ioc a t₀, LipschitzOnWith (2 / c ^ 2).toNNReal (fun x : ℂ => 2 / (x - W s))
      {x : ℂ | c ≤ ‖x - W s‖} := fun s _ => lipschitzOnWith_loewner hcpos
  have hs₁ : ∀ s ∈ Ioc a t₀, X₁ s ∈ {x : ℂ | c ≤ ‖x - W s‖} := fun s hs => by
    show c ≤ ‖X₁ s - W s‖
    simp only [hX₁, add_sub_cancel_right]
    exact (min_le_left _ _).trans (hc₁le s (Ioc_subset_Icc_self hs))
  have hs₂ : ∀ s ∈ Ioc a t₀, X₂ s ∈ {x : ℂ | c ≤ ‖x - W s‖} := fun s hs =>
    (min_le_right _ _).trans (hc₂le s (Ioc_subset_Icc_self hs))
  have heq₀ : X₁ t₀ = X₂ t₀ := sub_eq_zero.1 ht₀Z.2
  have hEq := ODE_solution_unique_of_mem_Icc_left (v := fun s x => 2 / (x - (W s : ℂ)))
    (s := fun s => {x : ℂ | c ≤ ‖x - W s‖}) hLip (hX₁c.mono hat') hd₁ hs₁ (hX₂c.mono hat') hd₂ hs₂ heq₀
  have haZ : a ∈ Z := ⟨hat' ⟨le_rfl, by linarith⟩, by
    simp only [mem_preimage, mem_singleton_iff, sub_eq_zero]
    exact hEq ⟨le_rfl, by linarith⟩⟩
  have := csInf_le hZbdd haZ
  linarith

/-- **(D9), uniform clearance of a far set from the seed coordinates** (§A.1.3, §A.1.6): for a compact `ℍ`-hull `H₁`
and a bounded `S₂ ⊆ ℍ` at distance `≥ 2δ` from it, there is `r > 0` such that for every continuous driver starting in
`closure H₁` with hull in `H₁` up to `T`, every `t ∈ (0, T]`, `a ∈ S₂`, and every seed coordinate `V` of the driver on
`[0, t]`: `r ≤ |g_t(a) − V_t|`. -/
theorem exists_le_norm_fwdMap_sub_seed_uniform {H₁ S₂ : Set ℂ} (hH₁ : IsHPHull H₁)
    (hS₂ : Bornology.IsBounded S₂) (hS₂H : S₂ ⊆ H) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ S₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) :
    ∃ r > 0, ∀ W : ℝ → ℝ, Continuous W → ((W 0 : ℝ) : ℂ) ∈ closure H₁ → ∀ T : ℝ, fwdHull W T ⊆ H₁ →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ a ∈ S₂, ∀ V : ℝ → ℝ, ContinuousOn V (Icc 0 t) → V 0 = W 0 →
        (∀ s ∈ Ioc 0 t, V s ≠ W s) →
        (∀ s ∈ Icc 0 t, IntervalIntegrable (fun r => 2 / (V r - W r)) volume 0 s) →
        (∀ s ∈ Icc 0 t, V s = V 0 + ∫ r in (0 : ℝ)..s, 2 / (V r - W r)) →
        r ≤ ‖fwdMap W t a + W t - V t‖ := by
  obtain ⟨r, hr, hmain⟩ := exists_le_norm_fwdMap_sub_uniform hH₁ hS₂ hS₂H hδ hsep
  refine ⟨r, hr, fun W hW hW0 T hKH t ht a ha V hVc hV0 hVne hVint hVeq => ?_⟩
  exact hmain W hW hW0 T hKH t (Ioc_subset_Icc_self ht) a ha (V t) fun y u hy hu =>
    seed_ne_fwdMap hW ht.1 hVc hV0 hVne hVint hVeq hy hu

end InteractingSLE.ZhanGT4
