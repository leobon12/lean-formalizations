/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Dynkin
import InteractingSLE.Stochastic.LocalTime.Taylor

/-!
# Itô's formula for an adapted random field `Φ(t, B_t)` (martingale form)

Packet PROVE-ZHAN-GT4-A5 (Astra, *Follow-up proofs*, Part A.1.1–A.1.3, `source/external/AstraIG1/
ig1_followup_proofs.txt` L216–L233 and L333–L341: "When `W_j` has quadratic variation `κ_j dt_j`, Itô
therefore yields …"). In the stopped dual coupling the mapped driver is `A_{j,0} = h_t(W_t)`, where the
conformal map `h_t` depends on the whole past of the driving path: it is a *random field*, adapted, `C¹` in
time (two-time Loewner equation (D1)) and analytic in space. The landed Itô formulas (`martingale_itoDynkin`,
a deterministic `F` of an absolutely continuous adapted `Λ` and `B`; MathFin's `ItoFormulaAdaptedTD`, a
deterministic `f(t, x)`) do not cover it. This file proves the case needed, in an arbitrary filtration and
without a stochastic integral (Revuz–Yor IV.3.3 in martingale-problem form; the Taylor-expansion argument of
`Spec/Ito/Dynkin.lean`, with the frozen coefficients of each step read at the left endpoint).

**The field theorem** (`integral_mul_fieldIncr_eq_zero`, in `Stochastic/ItoAdaptedStop.lean`). Let `B` be an
`𝓕`-Brownian motion with continuous paths and `s ≤ t`. Let `Φ, Φ₁, Φ₂, Ψ : ℝ → Ω → ℝ → ℝ` be random fields such
that for every time `r ∈ [s, t]`

* `x ↦ Φ r ω x` has derivative `Φ₁ r ω x` and `x ↦ Φ₁ r ω x` has derivative `Φ₂ r ω x`, with `Φ₂ r ω`
  `C`-Lipschitz;
* `Φ b ω x − Φ a ω x = ∫_a^b Ψ u ω x du` for `s ≤ a ≤ b ≤ t` (`Ψ` is the time derivative);
* `(r, x) ↦ Ψ r ω x` and `(r, x) ↦ Φ₂ r ω x` are continuous on `[s, t] × ℝ`;
* `|Φ|, |Φ₁|, |Φ₂|, |Ψ| ≤ C`;
* for every `x`, `ω ↦ Φ r ω x, Φ₁ r ω x, Φ₂ r ω x, Ψ r ω x` are `𝓕_r`-measurable.

Then `E[ξ (M_t − M_s)] = 0` for every `𝓕_s`-measurable `|ξ| ≤ 1`, where
`M_t − M_s = Φ(t, B_t) − Φ(s, B_s) − ∫_s^t (Ψ(u, B_u) + ½ Φ₂(u, B_u)) du`; `martingale_fieldDynkin` is the
martingale statement, and `integral_mul_fieldStopped_sub_eq_zero` the version for fields regular only up to a
stopping time.

This file contains the ingredients:

* `field_pathwise_step`: the pathwise second-order expansion of one time step of a random field along a path,
  with frozen coefficients read at the left endpoint, up to `C |Δβ|³ + fieldStepRem`;
* `exists_fieldStepRem_le`: the step remainder is `≤ ε (b − a)` on all short steps (uniform continuity);
* `measurable_field_comp`, `measurable_intervalIntegral_of_continuousOn`, `measurable_integral_fieldGen`:
  Carathéodory measurability of a field along a process and of its generator integral;
* **`integral_mul_sub_eq_zero_of_defectExcess`** (the abstract engine): for a measurable integrable process `X`
  and adapted coefficients `c₁, c₂` bounded by `C`, if the excesses of the Itô defects
  `X_b − X_a − c₁(a) ΔB − ½ c₂(a) (ΔB² − (b − a))` over `C |ΔB|³` along the uniform grids of `[s, t]` are
  uniformly bounded and tend to `0` along every path, then `E[ξ (X_t − X_s)] = 0` for `𝓕_s`-measurable `|ξ| ≤ 1`.

The space variable is unrestricted: a field that is only regular near the path is first cut off in space
(the consumer's localization).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Ito

/-! ### Measurability of a Carathéodory field along a process -/

section Measurability

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **A Carathéodory field evaluated along a measurable process is measurable**: if `ω ↦ Φ ω x` is
measurable for every `x` and `x ↦ Φ ω x` is continuous for every `ω`, then `ω ↦ Φ ω (X ω)` is measurable
for every measurable `X` (all with respect to the same, arbitrary, σ-algebra). -/
theorem measurable_field_comp {Φ : Ω → ℝ → ℝ} (hm : ∀ x, Measurable (fun ω => Φ ω x))
    (hc : ∀ ω, Continuous (Φ ω)) {X : Ω → ℝ} (hX : Measurable X) :
    Measurable fun ω => Φ ω (X ω) := by
  have hj : Measurable (Function.uncurry fun (x : ℝ) (ω : Ω) => Φ ω x) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hc ω) hm
  exact hj.comp (hX.prodMk measurable_id)

/-- **A time integral of a Carathéodory process on `[a, b]` is measurable**: if `g r` is measurable for
every `r ∈ [a, b]` and `r ↦ g r ω` is continuous on `[a, b]`, then `ω ↦ ∫_a^b g r ω dr` is measurable. -/
theorem measurable_intervalIntegral_of_continuousOn {g : ℝ → Ω → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hm : ∀ r ∈ Icc a b, Measurable (g r)) (hc : ∀ ω, ContinuousOn (fun r => g r ω) (Icc a b)) :
    Measurable fun ω => ∫ r in a..b, g r ω := by
  set cl : ℝ → ℝ := fun r => max a (min r b) with hcl
  have hclm : ∀ r, cl r ∈ Icc a b := fun r => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hcl_eq : ∀ r ∈ uIcc a b, cl r = r := fun r hr => by
    rw [uIcc_of_le hab] at hr
    simp only [hcl, min_eq_left hr.2, max_eq_right hr.1]
  have hm' : ∀ r, Measurable (g (cl r)) := fun r => hm _ (hclm r)
  have hc' : ∀ ω, Continuous fun r => g (cl r) ω := fun ω =>
    (hc ω).comp_continuous hclc hclm
  have h := QuantumZipper.Dynkin.measurable_intervalIntegral_of_continuous hm' hc' a b
  have heq : (fun ω => ∫ r in a..b, g r ω) = fun ω => ∫ r in a..b, g (cl r) ω := by
    funext ω
    exact intervalIntegral.integral_congr fun r hr => by simp only [hcl_eq r hr]
  rw [heq]
  exact h

end Measurability

/-! ### The pathwise remainder of one step -/

section Step

/-- The pathwise remainder of the time step `[a, b]` for the time-derivative field `ψ` and the second
space-derivative field `φ` along the path `β`. -/
def fieldStepRem (ψ φ : ℝ → ℝ → ℝ) (β : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ u in a..b, |ψ u (β b) - ψ u (β u)|) + 1 / 2 * ∫ u in a..b, |φ a (β a) - φ u (β u)|

theorem fieldStepRem_nonneg {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    0 ≤ fieldStepRem ψ φ β a b :=
  add_nonneg (intervalIntegral.integral_nonneg hab fun _ _ => abs_nonneg _)
    (mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hab fun _ _ => abs_nonneg _))

/-- Continuity on `[a, b]` of a jointly continuous field along a continuous path. -/
theorem continuousOn_field_path {ψ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {S : Set ℝ}
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (S ×ˢ univ)) (hβ : ContinuousOn β S) :
    ContinuousOn (fun u => ψ u (β u)) S :=
  hψ.comp (continuousOn_id.prodMk hβ) fun _ hu => ⟨hu, mem_univ _⟩

/-- Continuity on `S` of a jointly continuous field at a frozen space point. -/
theorem continuousOn_field_const {ψ : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (S ×ˢ univ)) (x : ℝ) :
    ContinuousOn (fun u => ψ u x) S :=
  hψ.comp (continuousOn_id.prodMk continuousOn_const) fun _ hu => ⟨hu, mem_univ _⟩

/-- A crude bound on the step remainder from bounds on the fields. -/
theorem fieldStepRem_le {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (Icc a b ×ˢ univ))
    (hφ : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Icc a b ×ˢ univ))
    (hβ : ContinuousOn β (Icc a b)) {α γ : ℝ}
    (hα : ∀ u ∈ Icc a b, |ψ u (β b) - ψ u (β u)| ≤ α)
    (hγ : ∀ u ∈ Icc a b, |φ a (β a) - φ u (β u)| ≤ γ) :
    fieldStepRem ψ φ β a b ≤ α * (b - a) + 1 / 2 * (γ * (b - a)) := by
  have hc1 : ContinuousOn (fun u => |ψ u (β b) - ψ u (β u)|) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact ((continuousOn_field_const hψ (β b)).sub (continuousOn_field_path hψ hβ)).abs
  have hc2 : ContinuousOn (fun u => |φ a (β a) - φ u (β u)|) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (continuousOn_const.sub (continuousOn_field_path hφ hβ)).abs
  unfold fieldStepRem
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  · have := intervalIntegral.integral_mono_on hab hc1.intervalIntegrable
      (intervalIntegrable_const : IntervalIntegrable (fun _ => α) volume a b) hα
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this
  · have := intervalIntegral.integral_mono_on hab hc2.intervalIntegrable
      (intervalIntegrable_const : IntervalIntegrable (fun _ => γ) volume a b) hγ
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this

/-- **The pathwise step.** For one time step `[a, b]` of a random field along a path `β` (frozen `ω`):
`Φ(b, β_b) − Φ(a, β_a) − ∫_a^b (Ψ(u, β_u) + ½ Φ₂(u, β_u)) du` equals the first two Taylor terms
`Φ₁(a, β_a) Δβ + ½ Φ₂(a, β_a) (Δβ² − (b − a))` up to `C |Δβ|³ + fieldStepRem`. -/
theorem field_pathwise_step {Φ Φ1 Φ2 Ψ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hd1 : ∀ x, HasDerivAt (Φ a) (Φ1 a x) x) (hd2 : ∀ x, HasDerivAt (Φ1 a) (Φ2 a x) x)
    (hlip : ∀ x y, |Φ2 a x - Φ2 a y| ≤ C * |x - y|)
    (htime : Φ b (β b) - Φ a (β b) = ∫ u in a..b, Ψ u (β b))
    (hΨ : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) (Icc a b ×ˢ univ))
    (hΦ2 : ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 p.2) (Icc a b ×ˢ univ))
    (hβ : ContinuousOn β (Icc a b)) :
    |Φ b (β b) - Φ a (β a) - (∫ u in a..b, (Ψ u (β u) + 1 / 2 * Φ2 u (β u)))
        - Φ1 a (β a) * (β b - β a) - 1 / 2 * Φ2 a (β a) * ((β b - β a) ^ 2 - (b - a))|
      ≤ C * |β b - β a| ^ 3 + fieldStepRem Ψ Φ2 β a b := by
  set Δ := β b - β a with hΔ
  -- (i) the Taylor step at the frozen time `a`
  have hTay := LocalTime.abs_taylor_two_le (f := Φ a) (f' := Φ1 a) (f'' := Φ2 a) hd1 hd2
    (x := β a) (y := β b) (M := C * |Δ|) fun z hz => by
      refine (hlip z (β a)).trans ?_
      have hC0 : 0 ≤ C := by
        have h := hlip 1 0
        norm_num at h
        exact (abs_nonneg _).trans h
      exact mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hz) hC0
  rw [← hΔ] at hTay
  have hT3 : C * |Δ| * Δ ^ 2 = C * |Δ| ^ 3 := by
    rw [← sq_abs Δ]; ring
  rw [hT3] at hTay
  -- (ii) the integrals
  have hc1 : ContinuousOn (fun u => Ψ u (β u)) (uIcc a b) := by
    rw [uIcc_of_le hab]; exact continuousOn_field_path hΨ hβ
  have hc2 : ContinuousOn (fun u => Φ2 u (β u)) (uIcc a b) := by
    rw [uIcc_of_le hab]; exact continuousOn_field_path hΦ2 hβ
  have hc3 : ContinuousOn (fun u => Ψ u (β b)) (uIcc a b) := by
    rw [uIcc_of_le hab]; exact continuousOn_field_const hΨ (β b)
  have hi1 := hc1.intervalIntegrable (μ := volume)
  have hi2 := hc2.intervalIntegrable (μ := volume)
  have hi3 := hc3.intervalIntegrable (μ := volume)
  have hsplit : ∫ u in a..b, (Ψ u (β u) + 1 / 2 * Φ2 u (β u)) =
      (∫ u in a..b, Ψ u (β u)) + 1 / 2 * ∫ u in a..b, Φ2 u (β u) := by
    rw [intervalIntegral.integral_add hi1 (hi2.const_mul _), intervalIntegral.integral_const_mul]
  have hR1 : |(∫ u in a..b, Ψ u (β b)) - ∫ u in a..b, Ψ u (β u)| ≤
      ∫ u in a..b, |Ψ u (β b) - Ψ u (β u)| := by
    rw [← intervalIntegral.integral_sub hi3 hi1]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  have hR2 : |(b - a) * Φ2 a (β a) - ∫ u in a..b, Φ2 u (β u)| ≤
      ∫ u in a..b, |Φ2 a (β a) - Φ2 u (β u)| := by
    have heq : (b - a) * Φ2 a (β a) - ∫ u in a..b, Φ2 u (β u) =
        ∫ u in a..b, (Φ2 a (β a) - Φ2 u (β u)) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hi2,
        intervalIntegral.integral_const, smul_eq_mul]
    rw [heq]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  have hkey : Φ b (β b) - Φ a (β a) - (∫ u in a..b, (Ψ u (β u) + 1 / 2 * Φ2 u (β u)))
        - Φ1 a (β a) * Δ - 1 / 2 * Φ2 a (β a) * (Δ ^ 2 - (b - a)) =
      (Φ a (β b) - Φ a (β a) - Φ1 a (β a) * Δ - Φ2 a (β a) * Δ ^ 2 / 2) +
        ((∫ u in a..b, Ψ u (β b)) - ∫ u in a..b, Ψ u (β u)) +
        1 / 2 * ((b - a) * Φ2 a (β a) - ∫ u in a..b, Φ2 u (β u)) := by
    rw [hsplit, ← htime]; ring
  rw [hkey, fieldStepRem]
  calc _ ≤ |Φ a (β b) - Φ a (β a) - Φ1 a (β a) * Δ - Φ2 a (β a) * Δ ^ 2 / 2| +
        |(∫ u in a..b, Ψ u (β b)) - ∫ u in a..b, Ψ u (β u)| +
        1 / 2 * |(b - a) * Φ2 a (β a) - ∫ u in a..b, Φ2 u (β u)| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) ?_)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ _ := by linarith [hTay, hR1, hR2]

/-- **Uniform smallness of the step remainder on short steps**: for fields jointly continuous on
`[s, t] × ℝ` and a continuous path, every step `[a, b] ⊆ [s, t]` shorter than some `δ` has
`fieldStepRem ≤ ε (b − a)`. -/
theorem exists_fieldStepRem_le {ψ φ : ℝ → ℝ → ℝ} {β : ℝ → ℝ} {s t : ℝ}
    (hψ : ContinuousOn (fun p : ℝ × ℝ => ψ p.1 p.2) (Icc s t ×ˢ univ))
    (hφ : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2) (Icc s t ×ˢ univ))
    (hβ : ContinuousOn β (Icc s t)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b, s ≤ a → a ≤ b → b ≤ t → b - a < δ →
      fieldStepRem ψ φ β a b ≤ ε * (b - a) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  set K : Set (ℝ × ℝ) := Icc s t ×ˢ Icc (-R) R with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKsub : K ⊆ Icc s t ×ˢ univ := prod_mono le_rfl (subset_univ _)
  have hmemK : ∀ u ∈ Icc s t, ∀ x ∈ Icc s t, ((u, β x) : ℝ × ℝ) ∈ K := fun u hu x hx =>
    ⟨hu, abs_le.1 (by simpa only [Real.norm_eq_abs] using hR x hx)⟩
  set η := ε / 2 with hη
  have hη0 : 0 < η := half_pos hε
  obtain ⟨δ1, hδ1, hψu⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous (hψ.mono hKsub)) η hη0
  obtain ⟨δ2, hδ2, hφu⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous (hφ.mono hKsub)) η hη0
  obtain ⟨δ3, hδ3, hβu⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hβ) (min δ1 δ2) (lt_min hδ1 hδ2)
  refine ⟨min (min δ1 δ2) δ3, lt_min (lt_min hδ1 hδ2) hδ3, fun a b hsa hab hbt hδ => ?_⟩
  have hS : Icc a b ⊆ Icc s t := Icc_subset_Icc hsa hbt
  have hclose : ∀ r ∈ Icc a b, ∀ r' ∈ Icc a b, dist r r' < min (min δ1 δ2) δ3 := by
    intro r hr r' hr'
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2, hr'.1, hr'.2]
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab
  have ha' : a ∈ Icc a b := left_mem_Icc.2 hab
  have h := fieldStepRem_le (ψ := ψ) (φ := φ) (β := β) hab (hψ.mono (prod_mono hS le_rfl))
    (hφ.mono (prod_mono hS le_rfl)) (hβ.mono hS) (α := η) (γ := η) (fun u hu => ?_) (fun u hu => ?_)
  · have hba : 0 ≤ b - a := sub_nonneg.2 hab
    calc fieldStepRem ψ φ β a b ≤ η * (b - a) + 1 / 2 * (η * (b - a)) := h
      _ ≤ ε * (b - a) := by rw [hη]; nlinarith
  · have hβd : dist (β b) (β u) < min δ1 δ2 :=
      hβu _ (hS hb) _ (hS hu) ((hclose _ hb _ hu).trans_le (min_le_right _ _))
    have hd : dist ((u, β b) : ℝ × ℝ) (u, β u) < δ1 := by
      rw [Prod.dist_eq, dist_self]
      exact max_lt hδ1 (hβd.trans_le (min_le_left _ _))
    have := hψu _ (hmemK u (hS hu) _ (hS hb)) _ (hmemK u (hS hu) u (hS hu)) hd
    rw [Real.dist_eq] at this
    exact this.le
  · have hβd : dist (β a) (β u) < min δ1 δ2 :=
      hβu _ (hS ha') _ (hS hu) ((hclose _ ha' _ hu).trans_le (min_le_right _ _))
    have hd : dist ((a, β a) : ℝ × ℝ) (u, β u) < δ2 := by
      rw [Prod.dist_eq]
      exact max_lt ((hclose _ ha' _ hu).trans_le ((min_le_left _ _).trans (min_le_right _ _)))
        (hβd.trans_le (min_le_right _ _))
    have := hφu _ (hmemK _ (hS ha') _ (hS ha')) _ (hmemK u (hS hu) u (hS hu)) hd
    rw [Real.dist_eq] at this
    exact this.le

end Step

/-! ### The abstract engine -/

section Grid

/-- The uniform grid `s + (t − s) k / n` of `[s, t]`. -/
def unifGrid (s t : ℝ≥0) (n k : ℕ) : ℝ≥0 := Real.toNNReal ((s : ℝ) + ((t : ℝ) - s) * k / n)

variable {s t : ℝ≥0}

theorem coe_unifGrid (hst : s ≤ t) (n k : ℕ) :
    (unifGrid s t n k : ℝ) = (s : ℝ) + ((t : ℝ) - s) * k / n := by
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  rw [unifGrid, Real.coe_toNNReal _ (add_nonneg s.coe_nonneg (by positivity))]

theorem unifGrid_zero (hst : s ≤ t) (n : ℕ) : unifGrid s t n 0 = s :=
  NNReal.eq (by rw [coe_unifGrid hst]; simp)

theorem unifGrid_self (hst : s ≤ t) {n : ℕ} (hn : 0 < n) : unifGrid s t n n = t :=
  NNReal.eq (by
    rw [coe_unifGrid hst, mul_div_assoc, div_self (by exact_mod_cast hn.ne'), mul_one]; ring)

theorem unifGrid_succ_sub (hst : s ≤ t) (n k : ℕ) :
    (unifGrid s t n (k + 1) : ℝ) - unifGrid s t n k = ((t : ℝ) - s) / n := by
  rw [coe_unifGrid hst, coe_unifGrid hst]; push_cast; ring

theorem unifGrid_le_succ (hst : s ≤ t) (n k : ℕ) : unifGrid s t n k ≤ unifGrid s t n (k + 1) := by
  have h := unifGrid_succ_sub hst n k
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  have : (0 : ℝ) ≤ ((t : ℝ) - s) / n := div_nonneg hts (Nat.cast_nonneg n)
  exact NNReal.coe_le_coe.1 (by linarith)

theorem le_unifGrid (hst : s ≤ t) (n k : ℕ) : s ≤ unifGrid s t n k := by
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  refine NNReal.coe_le_coe.1 ?_
  rw [coe_unifGrid hst]; exact le_add_of_nonneg_right (by positivity)

theorem unifGrid_le (hst : s ≤ t) {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) : unifGrid s t n k ≤ t := by
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine NNReal.coe_le_coe.1 ?_
  have : ((t : ℝ) - s) * k / n ≤ (t : ℝ) - s := by
    rw [div_le_iff₀ hn0]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hts
  rw [coe_unifGrid hst]; linarith

end Grid

section AbstractEngine

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- The Itô defect of a process `X` over a time step `[a, b]`, with frozen coefficients `c₁, c₂` read at
`a`: `X_b − X_a − c₁(a) ΔB − ½ c₂(a) (ΔB² − (b − a))`. -/
def itoDefect (X c1 c2 B : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (ω : Ω) : ℝ :=
  X b ω - X a ω - c1 a ω * (B b ω - B a ω) - 1 / 2 * c2 a ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))

/-- The excess of the Itô defect over `C |ΔB|³`, summed over the `n`-th uniform grid of `[s, t]`. -/
def defectExcess (X c1 c2 B : ℝ≥0 → Ω → ℝ) (C : ℝ) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, max (|itoDefect X c1 c2 B (unifGrid s t n k) (unifGrid s t n (k + 1)) ω| -
    C * |B (unifGrid s t n (k + 1)) ω - B (unifGrid s t n k) ω| ^ 3) 0

theorem max_sub_le_of_abs_le {d c R : ℝ} (h : |d| ≤ c + R) (hR : 0 ≤ R) : max (|d| - c) 0 ≤ R :=
  max_le (by linarith) hR

/-- **The abstract Itô–Dynkin engine.** Let `B` be an `𝓕`-Brownian motion, `s ≤ t`, `X` a measurable and
integrable process on `[s, t]`, and `c₁, c₂` adapted coefficients bounded by `C` on `[s, t]`. If the excess of
the Itô defects over `C |ΔB|³` along the uniform grids is uniformly bounded and tends to `0` along every path,
then `E[ξ (X_t − X_s)] = 0` for every `𝓕_s`-measurable `|ξ| ≤ 1`. -/
theorem integral_mul_sub_eq_zero_of_defectExcess (hB : IsFilteredBrownianReal 𝓕 B P)
    {X c1 c2 : ℝ≥0 → Ω → ℝ} {C K : ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    (hXm : ∀ r, s ≤ r → r ≤ t → Measurable (X r)) (hXi : ∀ r, s ≤ r → r ≤ t → Integrable (X r) P)
    (hc1 : ∀ r, s ≤ r → r ≤ t → Measurable[𝓕 r] (c1 r))
    (hc2 : ∀ r, s ≤ r → r ≤ t → Measurable[𝓕 r] (c2 r))
    (hc1b : ∀ r, s ≤ r → r ≤ t → ∀ ω, |c1 r ω| ≤ C)
    (hc2b : ∀ r, s ≤ r → r ≤ t → ∀ ω, |c2 r ω| ≤ C)
    (hdom : ∀ n, 0 < n → ∀ ω, defectExcess X c1 c2 B C s t n ω ≤ K)
    (hlim : ∀ ω, Tendsto (fun n => defectExcess X c1 c2 B C s t n ω) atTop (𝓝 0))
    {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (X t ω - X s ω) ∂P = 0 := by
  have hP := hB.isProbabilityMeasure'
  have hBm : ∀ r, Measurable (B r) := hB.measurable'
  have hst' : (s : ℝ) ≤ t := hst
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 hst'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hc1b s le_rfl hst ω₀)
  set g := unifGrid s t with hg
  have hgs : ∀ n k, s ≤ g n k := le_unifGrid hst
  have hgt : ∀ n k, 0 < n → k ≤ n → g n k ≤ t := fun n k hn hk => unifGrid_le hst hn hk
  have hgle : ∀ n k, g n k ≤ g n (k + 1) := unifGrid_le_succ hst
  have hξm : Measurable ξ := hξ.mono (𝓕.le s) le_rfl
  set ΔB : ℕ → ℕ → Ω → ℝ := fun n k ω => B (g n (k + 1)) ω - B (g n k) ω with hΔB
  set ρ : ℕ → ℕ → Ω → ℝ := fun n k => itoDefect X c1 c2 B (g n k) (g n (k + 1)) with hρ
  -- the expectation of a step is that of its defect
  have hstep_exp : ∀ n k, 0 < n → k < n →
      ∫ ω, ξ ω * (X (g n (k + 1)) ω - X (g n k) ω) ∂P = ∫ ω, ξ ω * ρ n k ω ∂P := by
    intro n k hn hk
    have hsa := hgs n k
    have hat := hgt n k hn hk.le
    have hbt := hgt n (k + 1) hn hk
    have hab := hgle n k
    have hξa : Measurable[𝓕 (g n k)] ξ := hξ.mono (𝓕.mono hsa) le_rfl
    set a := g n k
    set b := g n (k + 1)
    set g1 : Ω → ℝ := fun ω => ξ ω * c1 a ω
    set g2 : Ω → ℝ := fun ω => ξ ω * (1 / 2 * c2 a ω)
    have hg1 : Measurable[𝓕 a] g1 := hξa.mul (hc1 a hsa hat)
    have hg2 : Measurable[𝓕 a] g2 := hξa.mul (measurable_const.mul (hc2 a hsa hat))
    have hg1b : ∀ ω, ‖g1 ω‖ ≤ C := fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hξb ω)).trans (hc1b a hsa hat ω)
    have hg2b : ∀ ω, ‖g2 ω‖ ≤ C := fun ω => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      refine (mul_le_of_le_one_left (by positivity) (hξb ω)).trans ?_
      linarith [hc2b a hsa hat ω, abs_nonneg (c2 a ω)]
    have hi1 : Integrable (fun ω => g1 ω * (B b ω - B a ω)) P :=
      (hB.integrable_incr hab).bdd_mul (hg1.mono (𝓕.le a) le_rfl).aestronglyMeasurable
        (Eventually.of_forall hg1b)
    have hi2 : Integrable (fun ω => g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))) P :=
      ((hB.integrable_incr_sq hab).sub (integrable_const _)).bdd_mul
        (hg2.mono (𝓕.le a) le_rfl).aestronglyMeasurable (Eventually.of_forall hg2b)
    have hz1 : ∫ ω, g1 ω * (B b ω - B a ω) ∂P = 0 := by
      have := hB.integral_mul_incr hab hg1 (φ := id) measurable_id
      simp only [id] at this
      rw [this, hB.integral_incr hab, mul_zero]
    have hz2 : ∫ ω, g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a)) ∂P = 0 := by
      have := hB.integral_mul_incr hab hg2 (φ := fun x => x ^ 2 - ((b : ℝ) - a))
        ((measurable_id.pow_const 2).sub measurable_const)
      rw [this, integral_sub (hB.integrable_incr_sq hab) (integrable_const _),
        hB.integral_incr_sq hab, integral_const, probReal_univ, one_smul, sub_self, mul_zero]
    have hiM : Integrable (fun ω => ξ ω * (X b ω - X a ω)) P :=
      ((hXi b (hsa.trans hab) hbt).sub (hXi a hsa hat)).bdd_mul hξm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
    have hsplit : (fun ω => ξ ω * (X b ω - X a ω)) = fun ω => ξ ω * ρ n k ω +
        (g1 ω * (B b ω - B a ω) + g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))) := by
      funext ω; simp only [hρ, itoDefect, g1, g2, a, b]; ring
    have hi12 : Integrable (fun ω => g1 ω * (B b ω - B a ω) +
        g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))) P := hi1.add hi2
    have hiρ : Integrable (fun ω => ξ ω * ρ n k ω) P := by
      have : (fun ω => ξ ω * ρ n k ω) = fun ω => ξ ω * (X b ω - X a ω) -
          (g1 ω * (B b ω - B a ω) + g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))) := by
        funext ω; simp only [hρ, itoDefect, g1, g2, a, b]; ring
      rw [this]; exact hiM.sub hi12
    rw [hsplit, integral_add hiρ hi12, integral_add hi1 hi2, hz1, hz2]
    ring
  -- measurability and integrability of the defects
  have hρm : ∀ n k, 0 < n → k < n → Measurable (ρ n k) := fun n k hn hk => by
    have hsa := hgs n k
    have hat := hgt n k hn hk.le
    exact ((((hXm _ (hsa.trans (hgle n k)) (hgt n (k + 1) hn hk)).sub (hXm _ hsa hat)).sub
      (((hc1 _ hsa hat).mono (𝓕.le _) le_rfl).mul ((hBm _).sub (hBm _)))).sub
      ((measurable_const.mul ((hc2 _ hsa hat).mono (𝓕.le _) le_rfl)).mul
        ((((hBm _).sub (hBm _)).pow_const 2).sub measurable_const)))
  have hρi : ∀ n k, 0 < n → k < n → Integrable (ρ n k) P := by
    intro n k hn hk
    have hsa := hgs n k
    have hat := hgt n k hn hk.le
    have hab := hgle n k
    have hi1 : Integrable (fun ω => c1 (g n k) ω * ΔB n k ω) P :=
      (hB.integrable_incr hab).bdd_mul ((hc1 _ hsa hat).mono (𝓕.le _) le_rfl).aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hc1b _ hsa hat ω)
    have hi2 : Integrable (fun ω => 1 / 2 * c2 (g n k) ω *
        (ΔB n k ω ^ 2 - ((g n (k + 1) : ℝ) - g n k))) P :=
      ((hB.integrable_incr_sq hab).sub (integrable_const _)).bdd_mul (c := C)
        (measurable_const.mul ((hc2 _ hsa hat).mono (𝓕.le _) le_rfl)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          linarith [hc2b _ hsa hat ω, abs_nonneg (c2 (g n k) ω)])
    exact (((hXi _ (hsa.trans hab) (hgt n (k + 1) hn hk)).sub (hXi _ hsa hat)).sub hi1).sub hi2
  -- the excesses and their limit
  set D : ℕ → Ω → ℝ := fun n => defectExcess X c1 c2 B C s t n with hD
  set T : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, |ΔB n k ω| ^ 3 with hT
  have hDnn : ∀ n ω, 0 ≤ D n ω := fun n ω =>
    Finset.sum_nonneg fun k _ => le_max_right _ _
  have hK0 : 0 ≤ K := (hDnn 1 ω₀).trans (hdom 1 one_pos ω₀)
  have hDb : ∀ n ω, D n ω ≤ K := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : D 0 ω = 0 := by simp [hD, defectExcess]
      rw [h0]; exact hK0
    · exact hdom n hn ω
  have hDm : ∀ n, Measurable (D n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : D 0 = fun _ => 0 := by funext ω; simp [hD, defectExcess]
      rw [h0]; exact measurable_const
    · exact Finset.measurable_sum _ fun k hk => ((continuous_abs.measurable.comp
        (hρm n k hn (Finset.mem_range.1 hk))).sub (measurable_const.mul
          ((continuous_abs.measurable.comp ((hBm _).sub (hBm _))).pow_const 3))).max measurable_const
  have hSρ : ∀ n ω, ∑ k ∈ Finset.range n, |ρ n k ω| ≤ C * T n ω + D n ω := by
    intro n ω
    have h : ∀ k ∈ Finset.range n, |ρ n k ω| ≤ C * |ΔB n k ω| ^ 3 +
        max (|ρ n k ω| - C * |ΔB n k ω| ^ 3) 0 := fun k _ => by
      have := le_max_left (|ρ n k ω| - C * |ΔB n k ω| ^ 3) 0
      linarith
    refine (Finset.sum_le_sum h).trans_eq ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  have hID : Tendsto (fun n => ∫ ω, D n ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun n => (hDm n).aestronglyMeasurable) (integrable_const (μ := P) K)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDnn n ω)]; exact hDb n ω)
      (Eventually.of_forall hlim)
    simpa only [integral_zero] using h
  set m3 := QuantumZipper.gaussianAbsMoment 3 with hm3
  have hT_int : ∀ n, 0 < n → ∫ ω, T n ω ∂P ≤
      n * (m3 * (((t : ℝ) - s) / n * Real.sqrt (((t : ℝ) - s) / n))) := by
    intro n hn
    rw [integral_finsetSum _ fun k _ => hB.integrable_abs_incr_pow (hgle n k) 3]
    have hk : ∀ k ∈ Finset.range n, ∫ ω, |ΔB n k ω| ^ 3 ∂P ≤
        m3 * (((t : ℝ) - s) / n * Real.sqrt (((t : ℝ) - s) / n)) := fun k _ => by
      have h := hB.integral_abs_incr_pow_three_le (hgle n k)
      rwa [unifGrid_succ_sub hst n k] at h
    refine (Finset.sum_le_sum hk).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmain : ∀ n, 0 < n → |∫ ω, ξ ω * (X t ω - X s ω) ∂P| ≤
      ∫ ω, D n ω ∂P + C * (n * (m3 * (((t : ℝ) - s) / n * Real.sqrt (((t : ℝ) - s) / n)))) := by
    intro n hn
    have htel : ∀ ω, X t ω - X s ω = ∑ k ∈ Finset.range n, (X (g n (k + 1)) ω - X (g n k) ω) :=
      fun ω => by
        rw [Finset.sum_range_sub (f := fun k => X (g n k) ω), hg, unifGrid_self hst hn,
          unifGrid_zero hst]
    have hint : ∀ k ∈ Finset.range n,
        Integrable (fun ω => ξ ω * (X (g n (k + 1)) ω - X (g n k) ω)) P := fun k hk => by
      have hk' := Finset.mem_range.1 hk
      exact ((hXi _ ((hgs n k).trans (hgle n k)) (hgt n (k + 1) hn hk')).sub
        (hXi _ (hgs n k) (hgt n k hn hk'.le))).bdd_mul hξm.aestronglyMeasurable
          (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
    have e1 : ∫ ω, ξ ω * (X t ω - X s ω) ∂P = ∑ k ∈ Finset.range n, ∫ ω, ξ ω * ρ n k ω ∂P := by
      simp_rw [htel, Finset.mul_sum]
      rw [integral_finsetSum _ hint]
      exact Finset.sum_congr rfl fun k hk => hstep_exp n k hn (Finset.mem_range.1 hk)
    rw [e1]
    have e2 : ∀ k ∈ Finset.range n, |∫ ω, ξ ω * ρ n k ω ∂P| ≤ ∫ ω, |ρ n k ω| ∂P := fun k hk => by
      have hk' := Finset.mem_range.1 hk
      refine abs_integral_le_integral_abs.trans (integral_mono
        ((hρi n k hn hk').bdd_mul hξm.aestronglyMeasurable
          (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)).abs
        (hρi n k hn hk').abs fun ω => ?_)
      simp only [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hξb ω)
    have hTi : Integrable (T n) P :=
      integrable_finsetSum _ fun k _ => hB.integrable_abs_incr_pow (hgle n k) 3
    have hDi : Integrable (D n) P := (integrable_const K).mono' (hDm n).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hDnn n ω)]; exact hDb n ω)
    have e3 : ∑ k ∈ Finset.range n, ∫ ω, |ρ n k ω| ∂P ≤ ∫ ω, D n ω ∂P + C * ∫ ω, T n ω ∂P := by
      rw [← integral_finsetSum _ fun k hk => (hρi n k hn (Finset.mem_range.1 hk)).abs,
        ← integral_const_mul, ← integral_add hDi (hTi.const_mul C)]
      refine integral_mono (integrable_finsetSum _ fun k hk =>
        (hρi n k hn (Finset.mem_range.1 hk)).abs) (hDi.add (hTi.const_mul C)) fun ω => ?_
      have := hSρ n ω
      simp only at this ⊢
      linarith
    calc |∑ k ∈ Finset.range n, ∫ ω, ξ ω * ρ n k ω ∂P|
        ≤ ∑ k ∈ Finset.range n, |∫ ω, ξ ω * ρ n k ω ∂P| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, ∫ ω, |ρ n k ω| ∂P := Finset.sum_le_sum e2
      _ ≤ ∫ ω, D n ω ∂P + C * ∫ ω, T n ω ∂P := e3
      _ ≤ _ := by gcongr; exact hT_int n hn
  have hb : Tendsto (fun n : ℕ => ∫ ω, D n ω ∂P +
      C * (n * (m3 * (((t : ℝ) - s) / n * Real.sqrt (((t : ℝ) - s) / n))))) atTop (𝓝 0) := by
    have h0 := (tendsto_const_div_atTop_nhds_zero_nat ((t : ℝ) - s)).sqrt
    rw [Real.sqrt_zero] at h0
    have h1 : Tendsto (fun n : ℕ => C * (m3 * (((t : ℝ) - s) * Real.sqrt (((t : ℝ) - s) / n))))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ((h0.const_mul ((t : ℝ) - s)).const_mul m3).const_mul C
    have h2 : Tendsto (fun n : ℕ => C * (n * (m3 * (((t : ℝ) - s) / n *
        Real.sqrt (((t : ℝ) - s) / n))))) atTop (𝓝 0) := by
      refine h1.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    simpa only [add_zero] using hID.add h2
  have hle := ge_of_tendsto hb ((eventually_gt_atTop 0).mono fun n hn => hmain n hn)
  exact abs_nonpos_iff.1 hle

end AbstractEngine

/-! ### The martingale identity -/

section Engine

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

/-- The Itô generator of the random field along `B` at time `u`: `Ψ(u, B_u) + ½ Φ₂(u, B_u)`. -/
def fieldGen (Φ2 Ψ : ℝ → Ω → ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ :=
  Ψ u ω (B u.toNNReal ω) + 1 / 2 * Φ2 u ω (B u.toNNReal ω)

/-- The process `Φ(t, B_t) − ∫₀ᵗ (Ψ(u, B_u) + ½ Φ₂(u, B_u)) du` of `martingale_fieldDynkin`. -/
def fieldDynkin (Φ Φ2 Ψ : ℝ → Ω → ℝ → ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Φ t ω (B t ω) - ∫ u in (0 : ℝ)..t, fieldGen Φ2 Ψ B u ω

/-- A field jointly continuous on `S × ℝ` is continuous in space at every time of `S`. -/
theorem continuous_of_continuousOn_prod {F : ℝ → ℝ → ℝ} {S : Set ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ univ)) {r : ℝ} (hr : r ∈ S) :
    Continuous (F r) :=
  continuousOn_univ.1 (hF.comp (continuousOn_const.prodMk continuousOn_id)
    fun _ _ => ⟨hr, mem_univ _⟩)

/-- Measurability of the generator integral over `[a, b]`, for any σ-algebra in which the fields at
times of `[a, b]` and the values of `B` are measurable. -/
theorem measurable_integral_fieldGen {m : MeasurableSpace Ω} {Φ2 Ψ : ℝ → Ω → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hBm : ∀ r ∈ Icc a b, Measurable[m] (B r.toNNReal))
    (hBc : ∀ ω, Continuous (B · ω))
    (hm2 : ∀ r ∈ Icc a b, ∀ x, Measurable[m] fun ω => Φ2 r ω x)
    (hmΨ : ∀ r ∈ Icc a b, ∀ x, Measurable[m] fun ω => Ψ r ω x)
    (hΨc : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2) (Icc a b ×ˢ univ))
    (hΦ2c : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => Φ2 p.1 ω p.2) (Icc a b ×ˢ univ)) :
    Measurable[m] fun ω => ∫ u in a..b, fieldGen Φ2 Ψ B u ω := by
  refine measurable_intervalIntegral_of_continuousOn hab (fun r hr => ?_) (fun ω => ?_)
  · exact (measurable_field_comp (hmΨ r hr) (fun ω => continuous_of_continuousOn_prod (F := fun u x => Ψ u ω x) (hΨc ω) hr)
      (hBm r hr)).add (measurable_const.mul (measurable_field_comp (hm2 r hr)
        (fun ω => continuous_of_continuousOn_prod (F := fun u x => Φ2 u ω x) (hΦ2c ω) hr) (hBm r hr)))
  · have hβ : ContinuousOn (fun r : ℝ => B r.toNNReal ω) (Icc a b) :=
      ((hBc ω).comp continuous_real_toNNReal).continuousOn
    exact (continuousOn_field_path (ψ := fun u x => Ψ u ω x) (hΨc ω) hβ).add
      (continuousOn_const.mul (continuousOn_field_path (ψ := fun u x => Φ2 u ω x) (hΦ2c ω) hβ))

/-- The bound `|∫_a^b fieldGen| ≤ (3C/2)(b − a)` from `|Ψ|, |Φ₂| ≤ C`. -/
theorem abs_integral_fieldGen_le {Φ2 Ψ : ℝ → Ω → ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (hb2 : ∀ r ∈ Icc a b, ∀ ω x, |Φ2 r ω x| ≤ C) (hbΨ : ∀ r ∈ Icc a b, ∀ ω x, |Ψ r ω x| ≤ C)
    (ω : Ω) : |∫ u in a..b, fieldGen Φ2 Ψ B u ω| ≤ 3 * C / 2 * (b - a) := by
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 3 * C / 2)
    (a := a) (b := b) fun u hu => ?_).trans_eq ?_
  · rw [uIoc_of_le hab] at hu
    have hu' : u ∈ Icc a b := ⟨hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs, fieldGen]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [hbΨ u hu' ω (B u.toNNReal ω), hb2 u hu' ω (B u.toNNReal ω)]
  · rw [abs_of_nonneg (sub_nonneg.2 hab)]

end Engine

end InteractingSLE.Ito
