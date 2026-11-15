/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Sec2.RestartEvolution
import InteractingSLE.Spec.Supplement.LPAssembly

/-!
# §7.3: restarting at a stopping time with a known force word, and continuing the trace

Packet PROVE-SEC7-C3. The continuation steps of §7.3 restart the integrated equations at a stopping time
at which the force word is known (Aux. lemma 99, p. 343: "restart the integrated equations at the finite
swallow with the sole admissible seed group. The seed theorem gives a continuous transient trace in the
remaining half-plane chart"; Aux. lemma 106, p. 354, first paragraph). This file proves the probabilistic
half of that step from PROVE-RESTART's strong Markov restart (`Sec2.Restart.exists_restart`):

* `IsGeneratingTrace.congr_lt`: a generating trace only sees the driver before its horizon;
* `ae_restart_hasTransientTrace`: if `A ∈ 𝓕_T`, `T < ζ` on `A`, and almost surely on `A` the force word
  `V_T − W_T` is a fixed complete word, then almost surely on `A` the shifted driver `W_{T+·} − W_T` has a
  continuous generating trace up to the remaining lifetime `ζ − T`, transient when `ζ = ∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-- **A generating trace only sees the driver before its horizon**: if `η` generates the chain driven by
`w'` on `[0, T]` and `w = w'` before `T`, then `η` generates the chain driven by `w` on `[0, T]`. -/
theorem IsGeneratingTrace.congr_lt {w w' : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (h : IsGeneratingTrace w' T η) (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t = w' t) :
    IsGeneratingTrace w T η := by
  refine ⟨h.1, h.2.1, fun t ht => ?_⟩
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt ht
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, w r.toNNReal = w' r.toNNReal := fun r hr =>
    hww' _ ((ENNReal.ofReal_le_ofReal hr.2).trans_lt ht₂T)
  rw [fwdHull_eq_of_eqOn (W' := fun s : ℝ => w' s.toNNReal) (NNReal.coe_nonneg t) htt₂ heq]
  exact h.2.2 t ht

/-- From `P[·|A]`-almost surely to `P`-almost surely on `A`. -/
theorem ae_imp_of_ae_cond {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) {p : Ω → Prop} (h : ∀ᵐ ω ∂(P[|A]), p ω) :
    ∀ᵐ ω ∂P, ω ∈ A → p ω := by
  rw [ae_iff] at h ⊢
  rw [cond_apply hA] at h
  have hPA : (P A)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top P A)
  have h0 : P (A ∩ {ω | ¬p ω}) = 0 := (mul_eq_zero.1 h).resolve_left hPA
  refine measure_mono_null (fun ω hω => ?_) h0
  simp only [mem_ofPred_eq, Classical.not_imp] at hω
  exact ⟨hω.1, hω.2⟩

/-- **Restart with a known complete force word.** Let `(W, V, B)` be an integrated `SLE_κ(ρ)` evolution,
`T` a finite stopping time of its filtration, and `A ∈ 𝓕_T` with `T < ζ` on `A`. If almost surely on `A`
the force word at time `T`, `V_T − W_T`, is the fixed word `(yL; yR)` (with the same weights) and that word
is complete, then almost surely on `A` the shifted driver `W_{T+·} − W_T` has a continuous generating trace
up to and including the remaining lifetime `ζ − T`, which tends to infinity when `ζ − T = ∞`. (Strong
Markov restart, `Sec2.Restart.exists_restart`, under `P[·|A]`, then completeness of `(yL; yR)`.) -/
theorem ae_restart_hasTransientTrace {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (hAζ : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω)
    {yL : Fin nL → ℝ} {yR : Fin nR → ℝ}
    (hy : ∀ᵐ ω ∂P, ω ∈ A → (∀ i, VL i (T ω) ω - W (T ω) ω = yL i) ∧
      ∀ j, VR j (T ω) ω - W (T ω) ω = yR j)
    (hc : LP.IsCompleteForceWord.{u} κ yL yR ρL ρR) :
    ∀ᵐ ω ∂P, ω ∈ A → ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (shiftNN (fun t => W t ω) (T ω)) (ζ ω - T ω) η ∧
        (ζ ω - T ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  rcases eq_or_ne (P A) 0 with hPA | hPA
  · rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hPA
    simp only [mem_ofPred_eq, Classical.not_imp] at hω
    exact hω.1
  obtain ⟨𝓕', xL', xR', W', VL', VR', B', hE', -, hid⟩ :=
    Sec2.Restart.exists_restart hE hT hA hAζ hPA
  have : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hPA
  obtain ⟨hB', -, -, hW', hVL', hVR', hpath'⟩ := hE'
  have hE'' : IsIntegratedSLEEvolution κ yL yR ρL ρR (P[|A]) 𝓕' W' VL' VR' B'
      (fun ω => ζ ω - T ω) := by
    refine ⟨hB', hW', hVL', hVR', ?_⟩
    filter_upwards [hpath', cond_absolutelyContinuous.ae_le hid, cond_absolutelyContinuous.ae_le hy,
      ae_cond_mem hAm] with ω hp hidω hyω hω
    obtain ⟨hxL, hxR, -, -⟩ := hidω hω
    obtain ⟨hyL, hyR⟩ := hyω hω
    have e1 : xL' ω = yL := funext fun i => (hxL i).trans (hyL i)
    have e2 : xR' ω = yR := funext fun j => (hxR j).trans (hyR j)
    rw [e1, e2] at hp
    exact hp
  have htr := hc (P[|A]) 𝓕' W' VL' VR' B' (fun ω => ζ ω - T ω) hE''
  filter_upwards [ae_imp_of_ae_cond hAm htr, hid] with ω htrω hidω hω
  obtain ⟨η, hη, hηt⟩ := htrω hω
  obtain ⟨-, -, hW'ω, -⟩ := hidω hω
  exact ⟨η, IsGeneratingTrace.congr_lt hη fun t ht => ((hW'ω t ht).1).symm, hηt⟩

/-- **The open input for restarts with a random force word** (strong Markov property with a random initial
word, in trace form). Needed by Aux. lemmas 103, 106 and 113, by the one-sided step of the revised induction
(restart "with the smaller active count" at random positions, p. 379), and by LP1 and LP9. Let `T` be a finite
stopping time and `A ∈ 𝓕_T` with `T < ζ` on `A`, and suppose that for every `ω ∈ A` the force word at `T`,
`(V_T − W_T)(ω)`, is complete. Then almost surely on `A` the shifted driver has a continuous generating trace up to
the remaining lifetime, and the trace is transient. `ae_restart_hasTransientTrace` proves the case of an almost
surely constant word. The general case needs the conditional law of the restarted evolution given `𝓕'_0`, as a
kernel of evolutions started from the realized word. PROVE-RESTART's `exists_restart` gives an evolution with an
`𝓕'_0`-measurable random start under `P[·|A]`. The general case also needs a measurable form of the trace event of
the driving path, so that the conditional statements can be integrated. -/
def RandomRestartTraceStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∀ (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (A : Set Ω),
      MeasurableSet[hT.measurableSpace] A → (∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω) →
      (∀ ω ∈ A, LP.IsCompleteForceWord.{u} κ (fun i => VL i (T ω) ω - W (T ω) ω)
        (fun j => VR j (T ω) ω - W (T ω) ω) ρL ρR) →
      ∀ᵐ ω ∂P, ω ∈ A → ∃ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (shiftNN (fun t => W t ω) (T ω)) (ζ ω - T ω) η ∧
          (ζ ω - T ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)

/-! ### The first meeting time of the driver with a right mark -/

section FirstMeet

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {W V : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- The **first meeting time** of the driver `W` with a right force coordinate `V` before the lifetime
(the first time with `V ≤ W`, i.e. `V = W` since `W ≤ V` before `ζ`), or the lifetime `ζ` if they never
meet before it. For a single right mark this is "the first swallow of that mark" (Aux. lemma 99). -/
def firstMeet (W V : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ζ ω ⊓ ⨅ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ ω ∧ V t ω ≤ W t ω), (t : ℝ≥0∞)

theorem firstMeet_le_lifetime : firstMeet W V ζ ω ≤ ζ ω := inf_le_left

theorem firstMeet_le_of {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) (hm : V t ω ≤ W t ω) :
    firstMeet W V ζ ω ≤ t :=
  inf_le_right.trans (iInf₂_le t ⟨ht, hm⟩)

/-- Before the first meeting time the driver is strictly left of the mark. -/
theorem lt_of_lt_firstMeet {t : ℝ≥0} (ht : (t : ℝ≥0∞) < firstMeet W V ζ ω) :
    (t : ℝ≥0∞) < ζ ω ∧ W t ω < V t ω := by
  have htζ : (t : ℝ≥0∞) < ζ ω := ht.trans_le firstMeet_le_lifetime
  refine ⟨htζ, lt_of_not_ge fun hm => ?_⟩
  exact absurd (firstMeet_le_of htζ hm) (not_le.2 ht)

/-- **The first meeting is attained** when the gap `V − W` is continuous before `ζ`: if `firstMeet < ζ`,
it is a finite time `m < ζ` with `V_m ≤ W_m`. -/
theorem exists_eq_firstMeet (hc : ContinuousOn (fun t => V t ω - W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (h : firstMeet W V ζ ω < ζ ω) :
    ∃ m : ℝ≥0, firstMeet W V ζ ω = m ∧ (m : ℝ≥0∞) < ζ ω ∧ V m ω ≤ W m ω := by
  have h1 : ¬ ζ ω ≤ ⨅ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < ζ ω ∧ V t ω ≤ W t ω), (t : ℝ≥0∞) :=
    inf_lt_left.1 h
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ≥0, (t₁ : ℝ≥0∞) < ζ ω ∧ V t₁ ω ≤ W t₁ ω := by
    by_contra hn
    push Not at hn
    exact h1 (le_iInf₂ fun t ht => absurd ht.2 (not_le.2 (hn t ht.1)))
  set C : Set ℝ≥0 := Icc 0 t₁ ∩ (fun t => V t ω - W t ω) ⁻¹' Iic 0 with hCdef
  have hsub : Icc 0 t₁ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t ht =>
    (ENNReal.coe_le_coe.2 ht.2).trans_lt ht₁.1
  have hC : IsClosed C := (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : C.Nonempty := ⟨t₁, ⟨zero_le, le_rfl⟩, by simp [sub_nonpos.2 ht₁.2]⟩
  have hbdd : BddBelow C := ⟨0, fun _ _ => zero_le⟩
  have hm := hC.csInf_mem hne hbdd
  set m := sInf C with hmdef
  have hmζ : (m : ℝ≥0∞) < ζ ω := hsub hm.1
  have hmV : V m ω ≤ W m ω := sub_nonpos.1 hm.2
  refine ⟨m, le_antisymm (firstMeet_le_of hmζ hmV) (le_inf hmζ.le (le_iInf₂ fun s hs => ?_)), hmζ, hmV⟩
  rcases le_or_gt s t₁ with hst | hst
  · exact ENNReal.coe_le_coe.2 (csInf_le hbdd ⟨⟨zero_le, hst⟩, sub_nonpos.2 hs.2⟩)
  · exact ENNReal.coe_le_coe.2 (hm.1.2.trans hst.le)

/-- **The event `{firstMeet ≤ t}` by rational approximation** (gap continuous before `ζ`): either the
lifetime is at most `t`, or `t < ζ` and the gap `V − W` gets below every `1/(k+1)` at a rational time
`≤ t` or at `t`. -/
theorem firstMeet_le_iff (hc : ContinuousOn (fun t => V t ω - W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (t : ℝ≥0) :
    firstMeet W V ζ ω ≤ t ↔ ζ ω ≤ t ∨ ((t : ℝ≥0∞) < ζ ω ∧ ∀ k : ℕ,
      (∃ q : ℚ, ((q : ℝ).toNNReal ≤ t ∧
        V (q : ℝ).toNNReal ω - W (q : ℝ).toNNReal ω < 1 / ((k : ℝ) + 1))) ∨
        V t ω - W t ω < 1 / ((k : ℝ) + 1)) := by
  constructor
  · intro h
    rcases le_or_gt (ζ ω) t with hζ | hζ
    · exact Or.inl hζ
    refine Or.inr ⟨hζ, fun k => ?_⟩
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨m, hm, hmζ, hmV⟩ := exists_eq_firstMeet hc (h.trans_lt hζ)
    have hmt : m ≤ t := ENNReal.coe_le_coe.1 (hm ▸ h)
    have hfm : V m ω - W m ω < 1 / ((k : ℝ) + 1) := by linarith [sub_nonpos.2 hmV]
    rcases hmt.lt_or_eq with hlt | heq
    · left
      obtain ⟨ε, hε, hεf⟩ := Metric.continuousWithinAt_iff.1 (hc m hmζ)
        (1 / ((k : ℝ) + 1) - (V m ω - W m ω)) (by linarith)
      have hlt' : (m : ℝ) < min (t : ℝ) (m + ε) := lt_min (by exact_mod_cast hlt) (by linarith)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg m).trans hq1.le
      have hqt : (q : ℝ).toNNReal ≤ t := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact (hq2.trans_le (min_le_left _ _)).le
      refine ⟨q, hqt, ?_⟩
      have hqζ : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω :=
        (ENNReal.coe_le_coe.2 hqt).trans_lt hζ
      have hd : dist (q : ℝ).toNNReal m < ε := by
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_of_nonneg (by linarith)]
        linarith [min_le_right (t : ℝ) (m + ε)]
      have h3 := hεf hqζ hd
      rw [Real.dist_eq] at h3
      linarith [le_abs_self ((V (q : ℝ).toNNReal ω - W (q : ℝ).toNNReal ω) - (V m ω - W m ω))]
    · right; rw [← heq]; exact hfm
  · rintro (h | ⟨hζ, hk⟩)
    · exact firstMeet_le_lifetime.trans h
    by_contra hlt
    push Not at hlt
    have hsub : Icc 0 t ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := fun s hs =>
      (ENNReal.coe_le_coe.2 hs.2).trans_lt hζ
    have hpos : ∀ s ∈ Icc (0 : ℝ≥0) t, 0 < V s ω - W s ω := fun s hs =>
      sub_pos.2 (lt_of_lt_firstMeet ((ENNReal.coe_le_coe.2 hs.2).trans_lt hlt)).2
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, zero_le, zero_le⟩ (hc.mono hsub)
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (hpos s₀ hs₀)
    rcases hk k with ⟨q, hqt, hq⟩ | hq
    · have := hmin ⟨zero_le, hqt⟩
      simp only [mem_ofPred_eq] at this
      linarith
    · have := hmin ⟨zero_le, le_rfl⟩
      simp only [mem_ofPred_eq] at this
      linarith

open Classical in
/-- A random time `τ` set to `0` on the event `N`. -/
def zeroOn (N : Set Ω) (τ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := if ω ∈ N then 0 else τ ω

theorem zeroOn_of_mem {N : Set Ω} {τ : Ω → ℝ≥0∞} (h : ω ∈ N) : zeroOn N τ ω = 0 := by
  simp [zeroOn, h]

theorem zeroOn_of_notMem {N : Set Ω} {τ : Ω → ℝ≥0∞} (h : ω ∉ N) : zeroOn N τ ω = τ ω := by
  simp [zeroOn, h]

/-- **The first meeting time, set to `0` on a null set, is a stopping time.** Let `W, V` be adapted
before `ζ` to `𝓖`, and `N` an event in every `𝓖_t` off which the gap `V − W` is continuous before `ζ`.
Then `ω ↦ (0 on N, firstMeet W V ζ ω off N)` is a stopping time of `𝓖`. -/
theorem isStoppingTime_firstMeet_off {𝓖 : Filtration ℝ≥0 mΩ} (hW : AdaptedBefore 𝓖 ζ W)
    (hV : AdaptedBefore 𝓖 ζ V) {N : Set Ω} (hN : ∀ t, MeasurableSet[𝓖 t] N)
    (hc : ∀ ω ∉ N, ContinuousOn (fun t => V t ω - W t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    IsStoppingTime 𝓖 fun ω => (zeroOn N (firstMeet W V ζ) ω : WithTop ℝ≥0) := by
  intro t
  have hlife : ∀ q : ℝ≥0, MeasurableSet[𝓖 q] {ω | (q : ℝ≥0∞) < ζ ω} := fun q => by
    simpa using hW q univ MeasurableSet.univ
  have hE : ∀ (q : ℝ≥0) (c : ℝ),
      MeasurableSet[𝓖 q] {ω | (q : ℝ≥0∞) < ζ ω ∧ V q ω - W q ω < c} := by
    intro q c
    have hm : Measurable[𝓖 q] fun ω => Girsanov.killed ζ V q ω - Girsanov.killed ζ W q ω :=
      (Girsanov.measurable_killed hV q).sub (Girsanov.measurable_killed hW q)
    have heq : {ω | (q : ℝ≥0∞) < ζ ω ∧ V q ω - W q ω < c} =
        {ω | (q : ℝ≥0∞) < ζ ω} ∩
          (fun ω => Girsanov.killed ζ V q ω - Girsanov.killed ζ W q ω) ⁻¹' Iio c := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [Girsanov.killed_of_lt h1, Girsanov.killed_of_lt h1]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [Girsanov.killed_of_lt h1, Girsanov.killed_of_lt h1] at h2⟩
    rw [heq]
    exact (hlife q).inter (hm measurableSet_Iio)
  set G : Set Ω := {ω | ζ ω ≤ t} ∪ ({ω | (t : ℝ≥0∞) < ζ ω} ∩ ⋂ k : ℕ,
    ((⋃ q : ℚ, ⋃ (_ : (q : ℝ).toNNReal ≤ t), {ω | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      V (q : ℝ).toNNReal ω - W (q : ℝ).toNNReal ω < 1 / ((k : ℝ) + 1)}) ∪
      {ω | (t : ℝ≥0∞) < ζ ω ∧ V t ω - W t ω < 1 / ((k : ℝ) + 1)})) with hGdef
  have hG : MeasurableSet[𝓖 t] G := by
    refine MeasurableSet.union ?_ ((hlife t).inter (MeasurableSet.iInter fun k => ?_))
    · have := (hlife t).compl
      convert this using 1
      ext ω; simp
    · refine MeasurableSet.union (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_)
        (hE t _)
      exact 𝓖.mono hq _ (hE _ _)
  have hset : {ω | (zeroOn N (firstMeet W V ζ) ω : WithTop ℝ≥0) ≤ t} =
      N ∪ (Nᶜ ∩ G) := by
    ext ω
    by_cases hω : ω ∈ N
    · simp only [mem_ofPred_eq, mem_union, hω, true_or, iff_true]
      rw [zeroOn_of_mem hω]
      exact zero_le
    · simp only [mem_ofPred_eq, mem_union, hω, false_or, mem_inter_iff, mem_compl_iff,
        not_false_eq_true, true_and]
      rw [zeroOn_of_notMem hω]
      show firstMeet W V ζ ω ≤ t ↔ ω ∈ G
      rw [firstMeet_le_iff (hc ω hω) t]
      simp only [hGdef, mem_union, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion,
        exists_prop]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · refine Or.inr ⟨h1, fun k => ?_⟩
          rcases h2 k with ⟨q, hq, hq'⟩ | h
          · exact Or.inl ⟨q, hq, (ENNReal.coe_le_coe.2 hq).trans_lt h1, hq'⟩
          · exact Or.inr ⟨h1, h⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · refine Or.inr ⟨h1, fun k => ?_⟩
          rcases h2 k with ⟨q, hq, -, hq'⟩ | ⟨-, h⟩
          · exact Or.inl ⟨q, hq, hq'⟩
          · exact Or.inr h
  have hfin := (hN t).union ((hN t).compl.inter hG)
  rw [← hset] at hfin
  exact hfin

end FirstMeet

end Sec7

end InteractingSLE
