/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux62Hit
import InteractingSLE.Spec.Supplement.Aux62Repulsion
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# Aux. lemma 62, probabilistic layer: the separation time and the comparison drift

Packet PROVE-GB7A2. The comparison of Aux. lemma 62 changes the weights of the marks from a deterministic restart
time `q` on, as long as the *monitored* marks (nonzero original or comparison weight, and the repelled mark `k`)
stay at distance `> δ` from the driver. This file sets up, for a driver `W` and marks `U j` adapted before the
lifetime `ζ` and continuous on `[0, ζ)`:

* `monGap`: the monitored gaps `|W − U j|`, floored by `δ + (q − t)` so that nothing is detected before `q`;
* `sepTime`: the first time at which a monitored gap is `≤ δ` (or the lifetime, or the horizon `T₀`), a stopping
  time `≤ ζ ∧ T₀` (`measurableSet_sepTime_le`) after `q` while alive (`le_sepTime`);
* `cmpDrift`: the cut weight-change drift between `q` and the separation time, i.e. the difference of the
  landed cut drifts `shiftDrift` killed at `τ` and at `τ ∧ q`; it is progressive, bounded and Riemann-regular,
  its increments after `q` are the uncut drift (`drift_sub_drift_cmpDrift`) and its energy is the energy of the
  uncut drift between `q` and the separation time (`quadInt_cmpDrift_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB7a

open Girsanov Sec2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {m : ℕ}

/-! ### Monitored gaps and the separation time -/

/-- The monitored marks: nonzero original or comparison weight, or the repelled mark `k`. -/
def IsMon (ρ ρ' : Fin m → ℝ) (k j : Fin m) : Prop := ρ j ≠ 0 ∨ ρ' j ≠ 0 ∨ j = k

open Classical in
/-- The monitored gaps, floored by `δ + (q − t)` (nothing is detected before `q`). -/
def monGap (ρ ρ' : Fin m → ℝ) (k : Fin m) (q : ℝ≥0) (δ : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (j : Fin m) (t : ℝ≥0) (ω : Ω) : ℝ :=
  max (if IsMon ρ ρ' k j then |W t ω - U j t ω| else δ + 1) (δ + ((q : ℝ) - t))

/-- **The separation time**: the first time after `q` at which a monitored gap is `≤ δ`, the lifetime, or the
horizon `T₀`, whichever comes first. -/
def sepTime (ρ ρ' : Fin m → ℝ) (k : Fin m) (q : ℝ≥0) (δ : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T₀ : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  min (hitAfter 0 (killedF ζ (monGap ρ ρ' k q δ W U)) δ ω) T₀

variable {𝓖 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {U : Fin m → ℝ≥0 → Ω → ℝ}
  {ρ ρ' : Fin m → ℝ} {k : Fin m} {q T₀ : ℝ≥0} {δ : ℝ}

/-- A measurable time-dependent function of two processes adapted before `ζ` is adapted before `ζ`. -/
theorem adaptedBefore_comp₂ {V X : ℝ≥0 → Ω → ℝ} (F : ℝ≥0 → ℝ × ℝ → ℝ) (hF : ∀ t, Measurable (F t))
    (hW : AdaptedBefore 𝓖 ζ W) (hV : AdaptedBefore 𝓖 ζ V) (hX : ∀ t ω, X t ω = F t (W t ω, V t ω)) :
    AdaptedBefore 𝓖 ζ X := by
  intro t A hA
  have hm : Measurable[𝓖 t] fun ω => (killed ζ W t ω, killed ζ V t ω) :=
    (measurable_killed hW t).prodMk (measurable_killed hV t)
  have hlife : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hW t univ MeasurableSet.univ
  have heq : {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} =
      {ω | (t : ℝ≥0∞) < ζ ω} ∩ (fun ω => F t (killed ζ W t ω, killed ζ V t ω)) ⁻¹' A := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [killed_of_lt h1, killed_of_lt h1, ← hX]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [killed_of_lt h1, killed_of_lt h1, ← hX] at h2⟩
  rw [heq]
  exact hlife.inter (((hF t).comp hm) hA)

theorem adaptedBefore_monGap (hW : AdaptedBefore 𝓖 ζ W) (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j)) (j : Fin m) :
    AdaptedBefore 𝓖 ζ (monGap ρ ρ' k q δ W U j) := by
  classical
  refine adaptedBefore_comp₂ (fun t p => max (if IsMon ρ ρ' k j then |p.1 - p.2| else δ + 1)
    (δ + ((q : ℝ) - t))) (fun t => ?_) hW (hU j) (fun t ω => by simp only [monGap])
  split_ifs
  · exact (measurable_fst.sub measurable_snd).abs.max measurable_const
  · exact measurable_const

theorem continuousOn_monGap {ω : Ω} (hWc : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (U j · ω) {t | (t : ℝ≥0∞) < ζ ω}) (j : Fin m) :
    ContinuousOn (monGap ρ ρ' k q δ W U j · ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  classical
  have hr : ContinuousOn (fun t : ℝ≥0 => δ + ((q : ℝ) - t)) {t | (t : ℝ≥0∞) < ζ ω} :=
    (continuous_const.add (continuous_const.sub NNReal.continuous_coe)).continuousOn
  simp only [monGap]
  split_ifs
  · exact (continuous_abs.comp_continuousOn (hWc.sub (hUc j))).sup hr
  · exact continuousOn_const.sup hr

theorem sepTime_le_lifetime (hδ : 0 ≤ δ) (ω : Ω) : sepTime ρ ρ' k q δ W U ζ T₀ ω ≤ ζ ω := by
  have : Nonempty (Fin m) := ⟨k⟩
  exact (min_le_left _ _).trans (hitAfter_killed_le hδ ω (by simp))

theorem sepTime_le_horizon (ω : Ω) : sepTime ρ ρ' k q δ W U ζ T₀ ω ≤ T₀ := min_le_right _ _

theorem sepTime_ne_top (ω : Ω) : sepTime ρ ρ' k q δ W U ζ T₀ ω ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (sepTime_le_horizon ω)

/-- **The separation time is a stopping time.** -/
theorem measurableSet_sepTime_le (hδ : 0 ≤ δ) (hW : AdaptedBefore 𝓖 ζ W) (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j))
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j ω, ContinuousOn (U j · ω) {t | (t : ℝ≥0∞) < ζ ω}) (s : ℝ≥0) :
    MeasurableSet[𝓖 s] {ω | sepTime ρ ρ' k q δ W U ζ T₀ ω ≤ s} := by
  have : Nonempty (Fin m) := ⟨k⟩
  have h1 := measurableSet_hitAfter_le (q := 0) (𝓖 := 𝓖) hδ (adaptedBefore_monGap (ρ := ρ) (ρ' := ρ')
    (k := k) (q := q) (δ := δ) hW hU) (fun j ω => continuousOn_monGap (hWc ω) (fun i => hUc i ω) j) s
  have e : {ω | sepTime ρ ρ' k q δ W U ζ T₀ ω ≤ s} =
      {ω | hitAfter 0 (killedF ζ (monGap ρ ρ' k q δ W U)) δ ω ≤ s} ∪ {_ω | (T₀ : ℝ≥0∞) ≤ s} := by
    ext ω
    simp only [sepTime, Set.mem_ofPred_eq, mem_union, min_le_iff]
  rw [e]
  refine h1.union ?_
  by_cases h : (T₀ : ℝ≥0∞) ≤ s
  · simp only [h, ofPred_true, MeasurableSet.univ]
  · simp only [h, ofPred_false, MeasurableSet.empty]

/-- Before the separation time and after `q`, the evolution is alive and every monitored gap exceeds `δ`. -/
theorem lt_of_lt_sepTime (hδ : 0 ≤ δ) {ω : Ω} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < sepTime ρ ρ' k q δ W U ζ T₀ ω)
    (hqt : q ≤ t) : (t : ℝ≥0∞) < ζ ω ∧ ∀ j, IsMon ρ ρ' k j → δ < |W t ω - U j t ω| := by
  have : Nonempty (Fin m) := ⟨k⟩
  obtain ⟨hζ, hX⟩ := lt_of_lt_hitAfter_killed hδ (ht.trans_le (min_le_left _ _)) bot_le
  refine ⟨hζ, fun j hj => ?_⟩
  have h := hX j
  simp only [monGap, hj, ↓reduceIte] at h
  have hq : δ + ((q : ℝ) - t) ≤ δ := by
    have : (q : ℝ) ≤ t := hqt
    linarith
  rcases lt_max_iff.1 h with h' | h'
  · exact h'
  · linarith

/-- While alive at `q`, the separation time is at least `q` (for `q ≤ T₀`). -/
theorem le_sepTime (hqT : q ≤ T₀) {ω : Ω} (hqζ : (q : ℝ≥0∞) < ζ ω) :
    (q : ℝ≥0∞) ≤ sepTime ρ ρ' k q δ W U ζ T₀ ω := by
  refine le_min (le_iInf₂ fun t ht => ?_) (by exact_mod_cast hqT)
  by_contra htq
  rw [not_le] at htq
  have htq' : t < q := by exact_mod_cast htq
  obtain ⟨j, hj⟩ := ht.2
  have htζ : (t : ℝ≥0∞) < ζ ω := htq.trans hqζ
  rw [killedF, killed_of_lt htζ, monGap] at hj
  have : δ < δ + ((q : ℝ) - t) := by
    have : (t : ℝ) < q := htq'
    linarith
  exact absurd hj (not_le.2 (this.trans_le (le_max_right _ _)))

/-- If a monitored gap tends to `0` at a time `T > q` before the lifetime, the separation time comes before `T`. -/
theorem sepTime_lt_of_tendsto (hδ : 0 < δ) {ω : Ω} {T : ℝ≥0} (hqT : q < T) (hTζ : (T : ℝ≥0∞) ≤ ζ ω)
    {j : Fin m} (hj : IsMon ρ ρ' k j) (hlim : Tendsto (fun t => W t ω - U j t ω) (𝓝[<] T) (𝓝 0)) :
    sepTime ρ ρ' k q δ W U ζ T₀ ω < T := by
  have hev : ∀ᶠ t in 𝓝[<] T, |W t ω - U j t ω| < δ := by
    have := hlim.abs
    rw [abs_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  have hev2 : ∀ᶠ t in 𝓝[<] T, q < t := Filter.eventually_of_mem (Ioo_mem_nhdsLT hqT) fun t ht => ht.1
  have : (𝓝[<] T).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' ⟨q, hqT⟩]
    exact Set.mem_Iic.2 le_rfl
  obtain ⟨t, ht1, ht2, ht3⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
  refine (min_le_left _ _).trans_lt (lt_of_le_of_lt ?_ (show (t : ℝ≥0∞) < T by exact_mod_cast ht3))
  refine iInf₂_le (f := fun (s : ℝ≥0) (_ : 0 ≤ s ∧ ∃ i, killedF ζ (monGap ρ ρ' k q δ W U) i s ω ≤ δ) =>
    (s : ℝ≥0∞)) t ⟨bot_le, j, ?_⟩
  have htζ : (t : ℝ≥0∞) < ζ ω := (show (t : ℝ≥0∞) < T by exact_mod_cast ht3).trans_le hTζ
  rw [killedF, killed_of_lt htζ, monGap]
  simp only [hj, ↓reduceIte]
  refine max_le ht1.le ?_
  have : (q : ℝ) < t := ht2
  linarith

/-! ### The comparison drift -/

/-- **The comparison drift**: the cut weight-change drift between `q` and `τ`, i.e. the landed cut drift killed
at `τ` minus the one killed at `τ ∧ q`. -/
def cmpDrift (κ δ : ℝ) (σ : Fin m → ℝ) (τ ζ : Ω → ℝ≥0∞) (q : ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  shiftDrift κ 1 δ σ τ ζ W U t ω - shiftDrift κ 1 δ σ (fun ω => min (τ ω) q) ζ W U t ω

variable {κ : ℝ} {σ : Fin m → ℝ} {τ : Ω → ℝ≥0∞}

theorem measurableSet_min_le (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s}) (s : ℝ≥0) :
    MeasurableSet[𝓖 s] {ω | min (τ ω) q ≤ s} := by
  have e : {ω | min (τ ω) q ≤ s} = {ω | τ ω ≤ s} ∪ {_ω | (q : ℝ≥0∞) ≤ s} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_union, min_le_iff]
  rw [e]
  refine (hτ s).union ?_
  by_cases h : (q : ℝ≥0∞) ≤ s
  · simp only [h, ofPred_true, MeasurableSet.univ]
  · simp only [h, ofPred_false, MeasurableSet.empty]

theorem isStronglyProgressive_cmpDrift (hδ : 0 < δ) (hW : AdaptedBefore 𝓖 ζ W)
    (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j)) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s}) :
    IsStronglyProgressive 𝓖 (cmpDrift κ δ σ τ ζ q W U) := by
  have hF := continuous_shiftIntegrand κ 1 hδ σ
  have p1 := isStronglyProgressive_cutDrift hF hW hU hτ
  have p2 := isStronglyProgressive_cutDrift hF hW hU (measurableSet_min_le (q := q) hτ)
  exact fun t => (p1 t).sub (p2 t)

/-- The bound of the comparison drift. -/
def cmpBound (κ δ : ℝ) (σ : Fin m → ℝ) : ℝ := 2 * (|1 / Real.sqrt κ| * ((∑ j, |σ j|) * δ⁻¹))

theorem abs_cmpDrift_le (hδ : 0 < δ) (t : ℝ≥0) (ω : Ω) :
    |cmpDrift κ δ σ τ ζ q W U t ω| ≤ cmpBound κ δ σ := by
  have h1 := abs_cutDrift_le (τ := τ) (ζ := ζ) (W := W) (U := U) (abs_shiftIntegrand_le κ 1 hδ σ) t ω
  have h2 := abs_cutDrift_le (τ := fun ω => min (τ ω) q) (ζ := ζ) (W := W) (U := U)
    (abs_shiftIntegrand_le κ 1 hδ σ) t ω
  simp only [one_div] at h1 h2
  simp only [cmpDrift, shiftDrift, cmpBound, one_div]
  linarith [abs_sub (cutDrift τ ζ (shiftIntegrand κ 1 δ σ) W U t ω)
    (cutDrift (fun ω => min (τ ω) q) ζ (shiftIntegrand κ 1 δ σ) W U t ω)]

theorem isRiemannRegular_cmpDrift (hδ : 0 < δ) (hτζ : ∀ ω, τ ω ≤ ζ ω) {P : Measure Ω}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) :
    IsRiemannRegular P (cmpDrift κ δ σ τ ζ q W U) := by
  have hF := continuous_shiftIntegrand κ 1 hδ σ
  have r1 := isRiemannRegular_cutDrift (P := P) hF hτζ hcont
  have r2 := isRiemannRegular_cutDrift (P := P) (τ := fun ω => min (τ ω) q) hF
    (fun ω => (min_le_left _ _).trans (hτζ ω)) hcont
  filter_upwards [r1, r2] with ω h1 h2
  filter_upwards [h1, h2] with u hu1 hu2
  exact hu1.sub hu2

theorem cmpDrift_eq_zero_of_horizon_le (hτT : ∀ ω, τ ω ≤ T₀) (t : ℝ≥0) (ω : Ω) (ht : T₀ + 1 ≤ t) :
    cmpDrift κ δ σ τ ζ q W U t ω = 0 := by
  have h : τ ω < t := (hτT ω).trans_lt (by rw [ENNReal.coe_lt_coe]; exact (lt_add_one T₀).trans_le ht)
  simp only [cmpDrift, shiftDrift]
  rw [cutDrift_eq_zero h, cutDrift_eq_zero (τ := fun ω => min (τ ω) q) ((min_le_left _ _).trans_lt h), sub_zero]

/-- The three regimes of the comparison drift. -/
theorem cmpDrift_eq_zero_of_lt_min {t : ℝ≥0} {ω : Ω} (hδ : 0 < δ) (hτζ : τ ω ≤ ζ ω)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) (ht : (t : ℝ≥0∞) < min (τ ω) q) :
    cmpDrift κ δ σ τ ζ q W U t ω = 0 := by
  have hF := continuous_shiftIntegrand κ 1 hδ σ
  simp only [cmpDrift, shiftDrift]
  rw [cutDrift_eq_of_lt hF hτζ hWc hUc (ht.trans_le (min_le_left _ _)),
    cutDrift_eq_of_lt (τ := fun ω => min (τ ω) q) hF ((min_le_left _ _).trans hτζ) hWc hUc ht, sub_self]

theorem cmpDrift_eq_zero_of_gt {t : ℝ≥0} {ω : Ω} (ht : τ ω < t) : cmpDrift κ δ σ τ ζ q W U t ω = 0 := by
  simp only [cmpDrift, shiftDrift]
  rw [cutDrift_eq_zero ht, cutDrift_eq_zero (τ := fun ω => min (τ ω) q) ((min_le_left _ _).trans_lt ht),
    sub_zero]

theorem cmpDrift_eq_of_mem {t : ℝ≥0} {ω : Ω} (hδ : 0 < δ) (hτζ : τ ω ≤ ζ ω)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) (hqt : q < t)
    (ht : (t : ℝ≥0∞) < τ ω) :
    cmpDrift κ δ σ τ ζ q W U t ω = shiftIntegrand κ 1 δ σ (W t ω) (fun j => U j t ω) := by
  have hF := continuous_shiftIntegrand κ 1 hδ σ
  simp only [cmpDrift, shiftDrift]
  rw [cutDrift_eq_of_lt hF hτζ hWc hUc ht, cutDrift_eq_zero (τ := fun ω => min (τ ω) q)
    ((min_le_right _ _).trans_lt (by exact_mod_cast hqt)), sub_zero]

/-- A nonnegative real `s ≠ x.toReal` is on one side of a finite `x`. -/
theorem toNNReal_lt_or_gt {x : ℝ≥0∞} (hx : x ≠ ⊤) {s : ℝ} (hs : 0 ≤ s) (hne : s ≠ x.toReal) :
    (s.toNNReal : ℝ≥0∞) < x ∨ x < (s.toNNReal : ℝ≥0∞) := by
  rcases lt_or_gt_of_ne hne with h | h
  · left
    exact (ENNReal.ofReal_lt_iff_lt_toReal hs hx).2 h
  · right
    exact (ENNReal.lt_ofReal_iff_toReal_lt hx).2 h

theorem toNNReal_lt_iff {x : ℝ≥0∞} (hx : x ≠ ⊤) {s : ℝ} (hs : 0 ≤ s) :
    (s.toNNReal : ℝ≥0∞) < x ↔ s < x.toReal := ENNReal.ofReal_lt_iff_lt_toReal hs hx

/-- **The increments of the comparison drift after `q`** are the uncut weight-change drift. -/
theorem drift_sub_drift_cmpDrift (hδ : 0 < δ) (hW : AdaptedBefore 𝓖 ζ W)
    (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j)) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s}) {ω : Ω}
    (hτζ : τ ω ≤ ζ ω) (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {u : ℝ≥0} (hqu : q ≤ u)
    (hu : (u : ℝ≥0∞) ≤ τ ω) :
    drift (cmpDrift κ δ σ τ ζ q W U) u ω - drift (cmpDrift κ δ σ τ ζ q W U) q ω =
      ∫ s in (q : ℝ)..u, shiftIntegrand κ 1 δ σ (W s.toNNReal ω) (fun j => U j s.toNNReal ω) := by
  have hθ := isStronglyProgressive_cmpDrift (κ := κ) (σ := σ) (q := q) hδ hW hU hτ
  have hθb := abs_cmpDrift_le (κ := κ) (σ := σ) (τ := τ) (ζ := ζ) (q := q) (W := W) (U := U) hδ
  rw [drift, drift, intervalIntegral.integral_interval_sub_left (intervalIntegrable_time hθ hθb ω 0 u)
    (intervalIntegrable_time hθ hθb ω 0 q)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real (u : ℝ)] with s hsu hs
  rw [uIoc_of_le (by exact_mod_cast hqu)] at hs
  have hs0 : 0 ≤ s := q.2.trans hs.1.le
  have hlt : (s.toNNReal : ℝ≥0∞) < τ ω := by
    refine lt_of_lt_of_le ?_ hu
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]
    exact lt_of_le_of_ne hs.2 hsu
  have hqs : q < s.toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]
    exact hs.1
  exact cmpDrift_eq_of_mem hδ hτζ hWc hUc hqs hlt

/-- **The energy of the comparison drift** is the energy of the uncut drift between `q` and `τ`. -/
theorem quadInt_cmpDrift_eq (hδ : 0 < δ) (hW : AdaptedBefore 𝓖 ζ W)
    (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j)) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s})
    (hτT : ∀ ω, τ ω ≤ T₀) {ω : Ω} (hτζ : τ ω ≤ ζ ω)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) (hqτ : (q : ℝ≥0∞) ≤ τ ω) :
    quadInt (cmpDrift κ δ σ τ ζ q W U) (T₀ + 1) ω =
      ∫ s in (q : ℝ)..(τ ω).toReal, shiftIntegrand κ 1 δ σ (W s.toNNReal ω) (fun j => U j s.toNNReal ω) ^ 2 := by
  have hθ := isStronglyProgressive_cmpDrift (κ := κ) (σ := σ) (q := q) hδ hW hU hτ
  have hθ2 : IsStronglyProgressive 𝓖 (fun t ω => cmpDrift κ δ σ τ ζ q W U t ω ^ 2) := fun t => (hθ t).pow 2
  have hθ2b : ∀ t ω, |cmpDrift κ δ σ τ ζ q W U t ω ^ 2| ≤ cmpBound κ δ σ ^ 2 := fun t ω => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_cmpDrift_le hδ t ω) 2
  have hI := fun a b => intervalIntegrable_time hθ2 hθ2b ω a b
  have hτtop : τ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hτT ω)
  set τr := (τ ω).toReal with hτr
  have hqτr : (q : ℝ) ≤ τr := by
    rw [hτr, ← ENNReal.coe_toReal]
    exact ENNReal.toReal_mono hτtop hqτ
  have hτrT : τr ≤ ((T₀ + 1 : ℝ≥0) : ℝ) := by
    rw [hτr, ← ENNReal.coe_toReal]
    exact ENNReal.toReal_mono ENNReal.coe_ne_top ((hτT ω).trans (by exact_mod_cast le_self_add))
  have hmtop : min (τ ω) (q : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top hτtop (min_le_left _ _)
  rw [quadInt, ← intervalIntegral.integral_add_adjacent_intervals (hI 0 q) (hI q _),
    ← intervalIntegral.integral_add_adjacent_intervals (hI q τr) (hI τr _)]
  have h1 : ∫ s in (0 : ℝ)..(q : ℝ), cmpDrift κ δ σ τ ζ q W U s.toNNReal ω ^ 2 = 0 := by
    refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans (by simp)
    filter_upwards [ae_ne_real τr, ae_ne_real (q : ℝ)] with s hsτ hsq0 hs
    rw [uIoc_of_le (NNReal.coe_nonneg q)] at hs
    have hs0 : 0 ≤ s := hs.1.le
    rcases toNNReal_lt_or_gt hτtop hs0 hsτ with h | h
    · by_cases hsq : (s.toNNReal : ℝ≥0∞) < q
      · rw [cmpDrift_eq_zero_of_lt_min hδ hτζ hWc hUc (lt_min h hsq), zero_pow two_ne_zero]
      · -- `s = q`
        have hsq' : (q : ℝ) ≤ s := by
          rw [not_lt, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0] at hsq
          exact hsq
        exact absurd (le_antisymm hs.2 hsq') hsq0
    · rw [cmpDrift_eq_zero_of_gt h, zero_pow two_ne_zero]
  have h3 : ∫ s in τr..((T₀ + 1 : ℝ≥0) : ℝ), cmpDrift κ δ σ τ ζ q W U s.toNNReal ω ^ 2 = 0 := by
    refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans (by simp)
    filter_upwards with s hs
    rw [uIoc_of_le hτrT] at hs
    have hs0 : 0 ≤ s := ENNReal.toReal_nonneg.trans hs.1.le
    have h : τ ω < (s.toNNReal : ℝ≥0∞) := (ENNReal.lt_ofReal_iff_toReal_lt hτtop).2 hs.1
    rw [cmpDrift_eq_zero_of_gt h, zero_pow two_ne_zero]
  rw [h1, h3, zero_add, add_zero]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real τr] with s hsτ hs
  rw [uIoc_of_le hqτr] at hs
  have hs0 : 0 ≤ s := q.2.trans hs.1.le
  have hlt : (s.toNNReal : ℝ≥0∞) < τ ω := (toNNReal_lt_iff hτtop hs0).2 (lt_of_le_of_ne hs.2 hsτ)
  have hqs : q < s.toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]
    exact hs.1
  rw [cmpDrift_eq_of_mem hδ hτζ hWc hUc hqs hlt]

end GB7a

end InteractingSLE
