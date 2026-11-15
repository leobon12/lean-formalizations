/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoForceSeed
import InteractingSLE.Spec.Zhan.TwoForceBase

/-!
# The inverse-fibre step: the seed is not a terminal cluster point (Part B.3)

Packet PROVE-ZHAN-GT4-B. Source: Astra, *Follow-up proofs and dependency audit*, §B.3 L1260–L1264 (ruling R38):
"For the two-seed chordal law, restart at time one. The two gaps are strictly positive by noncollision, and its future
is a separated two-force law. The inverse-fibre argument excludes zero from the original cluster set. The same scaling
argument as for one force proves seed transience." The inverse-fibre argument is §B.2 L1184–L1188: "If the original trace
accumulated at zero, the future trace would accumulate on the compact real inverse fibre of zero under that finite
prefix. This is impossible. The fibre is compact because the inverse map is continuous and proper at infinity; its
points are real because its interior map is injective into the active domain." (Additional note, Proposition 3.5,
L1508–L1512, ruling R39.)

The input is §B.3's "the separated two-force chordal law has no finite real cluster point" (L1257–L1259; additional
note Lemma 3.4), a consequence of Part A's geometric outputs (the stopping-time collar and the separated two-force
confinement) which is **not proved here**: it is the named statement `SeparatedNoRealClusterStatement κ`.

## Main results

* `NoRealCluster η`, `UnifNoRealCluster η`, `NoRealCluster.unif` (compactness).
* `eventually_le_norm_of_shift_noRealCluster`: **the deterministic inverse-fibre step** — if the trace restarted at `σ`
  has no real terminal cluster point, then `0` is not a terminal cluster point of the original trace.
* `ratNoClusterSet`, `NoClusterEvent`, `noClusterCodeSet`: the Borel coding (rational times, trace evaluations).
* `IsIntegratedSLEEvolution.ae_restart_noClusterEvent`: the restart transfer at a positive time.
* `IsIntegratedSLEEvolution.ae_noCluster_zero_twoSeed` and
  **`IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed_of_separatedNoCluster`**: two-seed transience for every
  `κ > 0` from `SeparatedNoRealClusterStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Zhan
open QuantumZipper (H Hbar fwdMapInv)

/-! ### Real terminal cluster points -/

/-- `η` has **no real terminal cluster point**: every real `x` is avoided by `η(t)` for all large `t`. -/
def NoRealCluster (η : ℝ≥0 → ℂ) : Prop :=
  ∀ x : ℝ, ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖η t - x‖

/-- The uniform form on the compact intervals `[−M, M]`. -/
def UnifNoRealCluster (η : ℝ≥0 → ℂ) : Prop :=
  ∀ M : ℕ, ∃ d > (0 : ℝ), ∀ᶠ t in atTop, ∀ x ∈ Icc (-(M : ℝ)) M, d ≤ ‖η t - x‖

/-- **Compactness**: no real terminal cluster point gives the uniform form. -/
theorem NoRealCluster.unif {η : ℝ≥0 → ℂ} (h : NoRealCluster η) : UnifNoRealCluster η := by
  intro M
  choose d hd hev using h
  obtain ⟨s, -, hcover⟩ := (isCompact_Icc (a := -(M : ℝ)) (b := M)).elim_nhds_subcover
    (fun x => ball x (d x / 2)) fun x _ => ball_mem_nhds x (half_pos (hd x))
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ > (0 : ℝ), ∀ x ∈ s, δ ≤ d x / 2 := by
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact ⟨1, one_pos, fun x hx => by simp [hs] at hx⟩
    · exact ⟨s.inf' hs fun x => d x / 2, (Finset.lt_inf'_iff hs).2 fun x _ => half_pos (hd x),
        fun x hx => Finset.inf'_le _ hx⟩
  refine ⟨δ, hδ, ?_⟩
  have hall : ∀ᶠ t in atTop, ∀ x ∈ s, d x ≤ ‖η t - x‖ := (eventually_all_finset s).2 fun x _ => hev x
  filter_upwards [hall] with t ht y hy
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.1 (hcover hy)
  have h1 := ht x hxs
  have h2 : ‖((x : ℝ) : ℂ) - (y : ℂ)‖ < d x / 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hyx
  have h3 : ‖η t - x‖ ≤ ‖η t - y‖ + ‖((y : ℝ) : ℂ) - (x : ℂ)‖ := by
    calc ‖η t - x‖ = ‖(η t - y) + ((y : ℂ) - x)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev ((y : ℝ) : ℂ)] at h3
  linarith [hδle x hxs]

/-! ### The deterministic inverse-fibre step -/

/-- **The inverse-fibre step** (B.2 L1184–L1188). Let `w` be a continuous driver with `w 0 = 0` and a continuous
generating trace `η` on `[0, ∞)`, and let `η₂` be a continuous generating trace on `[0, ∞)` of the driver restarted at
`σ`, with no real terminal cluster point. Then `0` is not a terminal cluster point of `η`. (`η(σ + s) = F̄_σ(η₂(s))`,
`F̄_σ` continuous on `ℍ̄` at bounded distance from the identity, `F̄_σ(ℍ) ⊆ ℍ`; the real fibre `Z = F̄_σ⁻¹(0) ∩ ℝ` is
compact and the future eventually stays away from it.) -/
theorem eventually_le_norm_of_shift_noRealCluster {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) {σ : ℝ≥0} {η₂ : ℝ≥0 → ℂ}
    (hη₂ : IsGeneratingTrace (Sec7.shiftNN w σ) ⊤ η₂) (hno : UnifNoRealCluster η₂) :
    ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖η t‖ := by
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤} := hw.continuousOn
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη hwc hw0 (σ := σ) ENNReal.coe_lt_top
  have hσt₂ : (σ : ℝ) < (σ : ℝ) + 1 := lt_add_one _
  have hfc : Continuous (frozenDrive w ((σ : ℝ) + 1)) := continuous_frozenDrive hw.continuousOn
  obtain ⟨hF, -, hEq, hcont, -, ⟨C, hC⟩, -⟩ := h₁.extend_props hσt₂ hfc hw0
  set Fb := extendFrom H (fwdMapInv (frozenDrive w ((σ : ℝ) + 1)) σ) with hFb
  -- the join identifies the future with `F̄_σ ∘ η₂`
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < (σ : ℝ≥0∞) + ⊤} := by rw [add_top]; exact hwc
  obtain ⟨hjoin, -⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have hjoinF : ∀ t : ℝ≥0, σ < t → η t = Fb (η₂ (t - σ)) := by
    intro t ht
    rw [hη.eq_of_le hjoin hwc hw0 le_top, Sec7.joinTrace_of_lt ht, hF]
  -- values of `η₂` lie in `ℍ̄`
  have hw₂ : Continuous fun s : ℝ => Sec7.shiftNN w σ s.toNNReal := by
    unfold Sec7.shiftNN
    exact ((hw.comp (continuous_const.add continuous_id)).sub continuous_const).comp continuous_real_toNNReal
  have hη₂H : ∀ s, η₂ s ∈ Hbar := fun s =>
    Sec4.im_nonneg_of_isGeneratingTrace hw₂ (Sec7.shiftNN_zero w σ) hη₂ s
  -- `F̄_σ` maps `ℍ` into `ℍ`
  have hf0 : frozenDrive w ((σ : ℝ) + 1) 0 = 0 := by
    simp [frozenDrive, min_eq_left (show (0 : ℝ) ≤ (σ : ℝ) + 1 by positivity), hw0]
  have hFbH : ∀ z ∈ H, Fb z ∈ H := fun z hz => by
    rw [hEq hz]
    exact QuantumZipper.RS.fwdMapInv_mem_H hfc hf0 σ.coe_nonneg hz
  have hRH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => by
    show 0 ≤ (x : ℂ).im
    simp
  -- the real fibre over `0` lies in `[−M, M]`
  set Z : Set ℝ := {x | Fb x = 0} with hZ
  set M : ℕ := ⌈C⌉₊ with hM
  have hZM : ∀ x ∈ Z, x ∈ Icc (-(M : ℝ)) M := by
    intro x hx
    have h := hC x (hRH x)
    rw [show Fb x = 0 from hx, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs] at h
    have hCM : C ≤ M := Nat.le_ceil C
    exact abs_le.1 (h.trans hCM)
  obtain ⟨d', hd', hev⟩ := hno M
  -- the compact set of candidate restarted positions near `0`
  set K : Set ℂ := (closedBall (0 : ℂ) (C + 1) ∩ Hbar) ∩ ⋂ x ∈ Z, {y | d' ≤ ‖y - x‖} with hK
  have hKc : IsCompact K := by
    refine ((isCompact_closedBall 0 (C + 1)).inter_right ?_).inter_right ?_
    · exact isClosed_le continuous_const Complex.continuous_im
    · exact isClosed_biInter fun x _ => isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  have hKH : K ⊆ Hbar := fun y hy => hy.1.2
  have hne : ∀ y ∈ K, Fb y ≠ 0 := by
    intro y hy h
    rcases (show 0 ≤ y.im from hy.1.2).lt_or_eq with hpos | hzero
    · exact (show ¬ (0 < (0 : ℂ).im) by simp) (h ▸ hFbH y hpos)
    · have hy' : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hmem : y.re ∈ Z := by
        show Fb (y.re : ℂ) = 0
        rw [← hy']; exact h
      have h2 : d' ≤ ‖y - (y.re : ℂ)‖ := mem_iInter₂.1 hy.2 y.re hmem
      rw [← hy', sub_self, norm_zero] at h2
      linarith
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ y ∈ K, m ≤ ‖Fb y‖ := by
    rcases K.eq_empty_or_nonempty with hK0 | hK0
    · exact ⟨1, one_pos, fun y hy => by rw [hK0] at hy; exact hy.elim⟩
    · obtain ⟨y₀, hy₀, hmin⟩ := hKc.exists_isMinOn hK0 ((hcont.mono hKH).norm)
      exact ⟨‖Fb y₀‖, norm_pos_iff.2 (hne y₀ hy₀), fun y hy => hmin hy⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  refine ⟨min m 1, lt_min hm one_pos, ?_⟩
  filter_upwards [eventually_ge_atTop (σ + T + 1)] with t ht
  have htσ : σ < t := lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one (σ + T))) ht
  have hTt : T ≤ t - σ := by
    rw [le_tsub_iff_left htσ.le]
    exact le_trans (by
      calc σ + T ≤ σ + T + 1 := le_self_add) ht
  rw [hjoinF t htσ]
  set y := η₂ (t - σ)
  by_cases hy : ‖y‖ ≤ C + 1
  · have hyK : y ∈ K := ⟨⟨by rwa [mem_closedBall, dist_zero_right], hη₂H _⟩,
      mem_iInter₂.2 fun x hx => hT (t - σ) hTt x (hZM x hx)⟩
    exact (min_le_left _ _).trans (hmK y hyK)
  · push Not at hy
    have h1 := hC y (hη₂H _)
    have h2 : ‖y‖ - ‖Fb y‖ ≤ ‖Fb y - y‖ := by
      have := norm_sub_norm_le y (Fb y)
      rw [norm_sub_rev] at this
      exact this
    exact (min_le_right _ _).trans (by linarith)

/-! ### The Borel coding -/

/-- `[−M, M]` in `ℂ`. -/
def realIntC (M : ℕ) : Set ℂ := ((↑) : ℝ → ℂ) '' Icc (-(M : ℝ)) M

theorem realIntC_nonempty (M : ℕ) : (realIntC M).Nonempty :=
  ⟨((0 : ℝ) : ℂ), 0, ⟨by simp, by positivity⟩, rfl⟩

/-- The rational-time uniform no-real-cluster condition on the measurable trace evaluations. -/
def ratNoClusterSet : Set (ℚ≥0 → ℝ) :=
  ⋂ M : ℕ, ⋃ k : ℕ, ⋃ N : ℕ, ⋂ q : ℚ≥0,
    {v | (N : ℝ≥0) ≤ (q : ℝ≥0) → 1 / ((k : ℝ) + 1) ≤ infDist (LP.traceAt q (Sec7.extendRat v)) (realIntC M)}

theorem measurableSet_ratNoClusterSet : MeasurableSet ratNoClusterSet := by
  refine MeasurableSet.iInter fun M => MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun q => ?_
  by_cases hq : (N : ℝ≥0) ≤ (q : ℝ≥0)
  · simp only [hq, forall_const]
    exact measurableSet_le measurable_const ((continuous_infDist_pt _).measurable.comp
      ((LP.measurable_traceAt (q : ℝ≥0)).comp Sec7.measurable_extendRat))
  · simp [hq]

/-- For a continuous driver with a generating trace on `[0, ∞)`, the rational condition is the uniform absence of real
terminal cluster points. -/
theorem ratVals_mem_ratNoClusterSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) : (fun q : ℚ≥0 => w q) ∈ ratNoClusterSet ↔ UnifNoRealCluster η := by
  have htr : ∀ q : ℚ≥0, LP.traceAt q (Sec7.extendRat fun q : ℚ≥0 => w q) = η q := fun q => by
    rw [Sec7.extendRat_eq hw]
    exact LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  simp only [ratNoClusterSet, mem_iInter, mem_iUnion, mem_ofPred_eq, htr]
  constructor
  · intro h M
    obtain ⟨k, N, hk⟩ := h M
    refine ⟨1 / ((k : ℝ) + 1), by positivity, eventually_atTop.2 ⟨(N : ℝ≥0), fun t ht x hx => ?_⟩⟩
    have hlim : Tendsto (fun m => infDist (η (Sec7.ratAbove t m)) (realIntC M)) atTop
        (𝓝 (infDist (η t) (realIntC M))) :=
      ((continuous_infDist_pt _).tendsto _).comp ((hηc.tendsto t).comp (Sec7.tendsto_ratAbove t))
    have hge := ge_of_tendsto' hlim fun m => hk (Sec7.ratAbove t m) (ht.trans (Sec7.le_ratAbove t m))
    calc 1 / ((k : ℝ) + 1) ≤ infDist (η t) (realIntC M) := hge
      _ ≤ dist (η t) x := infDist_le_dist_of_mem (mem_image_of_mem _ hx)
      _ = ‖η t - x‖ := dist_eq_norm _ _
  · intro h M
    obtain ⟨d, hd, hev⟩ := h M
    obtain ⟨T, hT⟩ := eventually_atTop.1 hev
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd
    obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
    refine ⟨k, N, fun q hq => ?_⟩
    have hTq : T ≤ (q : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]; exact hN.trans (by exact_mod_cast hq)
    rw [le_infDist (s := realIntC M) (realIntC_nonempty M)]
    rintro _ ⟨x, hx, rfl⟩
    rw [dist_eq_norm]
    exact hk.le.trans (hT _ hTq x hx)

/-- **The no-real-cluster event** of a (driver, horizon) pair: infinite horizon, a continuous generating trace on
`[0, ∞)`, and the rational uniform condition. -/
def NoClusterEvent (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ (fun q : ℚ≥0 => w q) ∈ topSet ∧ (fun q : ℚ≥0 => w q) ∈ ratNoClusterSet

/-- The Borel set of (driver, horizon) pairs with the no-real-cluster event. -/
def noClusterSet : Set ((ℝ≥0 → ℝ) × ℝ≥0∞) :=
  (Prod.snd ⁻¹' {⊤}) ∩ ((fun x => fun q : ℚ≥0 => x.1 q) ⁻¹' (topSet ∩ ratNoClusterSet))

theorem measurableSet_noClusterSet : MeasurableSet noClusterSet := by
  refine (measurable_snd (measurableSet_singleton ⊤)).inter ?_
  have hm : Measurable fun x : (ℝ≥0 → ℝ) × ℝ≥0∞ => fun q : ℚ≥0 => x.1 q :=
    measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp measurable_fst
  exact hm (measurableSet_topSet.inter measurableSet_ratNoClusterSet)

theorem NoClusterEvent.of_noRealCluster {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (hno : NoRealCluster η) : NoClusterEvent w ⊤ :=
  ⟨rfl, (ratVals_mem_topSet_iff hw hw0).2 ⟨η, hη⟩, (ratVals_mem_ratNoClusterSet_iff hw hw0 hη).2 hno.unif⟩

theorem not_noClusterEvent_congr (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hn : ¬ NoClusterEvent w τ) : ¬ NoClusterEvent w' τ := by
  rintro ⟨hτ, h2⟩
  subst hτ
  have : w = w' := funext fun t => h t ENNReal.coe_lt_top
  subst this
  exact hn ⟨rfl, h2⟩

/-! ### The named input: Lemma 3.4 -/

/-- **Named input: the separated two-force law has no real terminal cluster point** (Part B.3, L1236–L1259: "Hence
`ℙ[Q ∩ ℝ ≠ ∅] ≤ ε`, and letting `ε ↓ 0` proves that the separated two-force chordal law has no finite real cluster
point"; additional note, Lemma 3.4, L1479–L1505). For `κ > 4` its proof uses Part A's stopping-time collar and separated
two-force confinement (`StoppingCollarStatement`, `SeparatedTwoForceStatement`), the annulus estimate (additional note
Lemma 3.1) and the recurrent upper-mark diffusion (E11)/(ZE.6); it is not proved here. For marks `xL 0 < 0 < xR 0` with
weights `ρ_L, ρ_R ≥ κ/2 − 2`, almost surely every continuous generating trace on `[0, ∞)` has no real terminal cluster
point. -/
def SeparatedNoRealClusterStatement (κ : ℝ) : Prop :=
  ∀ (xL xR ρL ρR : Fin 1 → ℝ), xL 0 < 0 → 0 < xR 0 → κ / 2 - 2 ≤ ρL 0 → κ / 2 - 2 ≤ ρR 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
          ∀ x : ℝ, ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖η t - x‖

/-- The weights of a separated admissible one-mark-per-side word are `≥ κ/2 − 2`. -/
theorem weights_of_hasAdmissiblePartialSums {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ}
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : xL 0 < 0) (hxR : 0 < xR 0) :
    κ / 2 - 2 ≤ ρL 0 ∧ κ / 2 - 2 ≤ ρR 0 := by
  constructor
  · have h := hadm.1 (xL 0 - 1) (by linarith) ⟨0, by linarith⟩
    have hf : (Finset.univ.filter fun i : Fin 1 => xL 0 - 1 < xL i) = Finset.univ := by
      ext i; simp [Fin.fin_one_eq_zero i]
    rwa [hf, Fin.sum_univ_one] at h
  · have h := hadm.2 (xR 0) hxR.le ⟨0, le_rfl⟩
    have hf : (Finset.univ.filter fun i : Fin 1 => xR i ≤ xR 0) = Finset.univ := by
      ext i; simp [Fin.fin_one_eq_zero i]
    rwa [hf, Fin.sum_univ_one] at h

/-! ### Transfer through the restart kernel -/

section Kernel

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-- The Borel set of solution codes whose driver has the no-real-cluster event up to the lifetime. -/
def noClusterCodeSet {nL nR : ℕ} : Set (XCode nL nR) := (fun x => (cw x, cζ x)) ⁻¹' noClusterSet

theorem measurableSet_noClusterCodeSet {nL nR : ℕ} : MeasurableSet (noClusterCodeSet (nL := nL) (nR := nR)) :=
  measurable_cw_cζ measurableSet_noClusterSet

/-- **No real terminal cluster at a realized separated word**, from the named input: the canonical probability of the
complement of the no-real-cluster event is zero. -/
theorem codeLaw_compl_noClusterCodeSet_eq_zero {κ : ℝ} (hκ : 0 < κ)
    (hN : SeparatedNoRealClusterStatement.{0} κ) {ρL ρR : Fin 1 → ℝ} {s : (Fin 1 → ℝ) × (Fin 1 → ℝ)}
    (hF : IsOrderedForceWord s.1 s.2) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR s.1 s.2)
    (hxL : ∀ i, s.1 i < 0) (hxR : ∀ j, 0 < s.2 j)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR) :
    codeLaw κ ρL ρR (noClusterCodeSet (nL := 1) (nR := 1))ᶜ s = 0 := by
  have hsep : ∀ i j, s.1 i < s.2 j := fun i j => (hxL i).trans (hxR j)
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have := hP
  obtain ⟨hwL, hwR⟩ := weights_of_hasAdmissiblePartialSums hadm (hxL 0) (hxR 0)
  have hev : ∀ᵐ ω ∂P, NoClusterEvent (fun t => W t ω) (ζ ω) := by
    filter_upwards [hN s.1 s.2 ρL ρR (hxL 0) (hxR 0) hwL hwR P 𝓕 W VL VR B ζ hE,
      hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ hF hadm hxL hxR,
      hE.2.2.2.2] with ω hnoω ⟨hζ, η, hη⟩ hp
    have hwc : Continuous fun t => W t ω := by
      have h := hp.2.2.2.1
      rw [hζ] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    rw [hζ]
    exact NoClusterEvent.of_noRealCluster hwc hp.1 hη (hnoω η hη)
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (Φ := fun w τ => ¬ NoClusterEvent w τ)
    measurableSet_noClusterCodeSet.compl (fun _ _ _ => Iff.rfl) not_noClusterEvent_congr
  rw [← e]
  exact ae_iff.1 hev

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL xR ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The restarted driver has no real terminal cluster point.** For an admissible one-mark-per-side word (marks at
the seed allowed) and every `σ > 0`, almost surely the driver restarted at `σ` has the no-real-cluster event, given the
named input. -/
theorem IsIntegratedSLEEvolution.ae_restart_noClusterEvent [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hN : SeparatedNoRealClusterStatement.{0} κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ : ℝ≥0} (hσ : 0 < σ) :
    ∀ᵐ ω ∂P, NoClusterEvent (fun t => W (σ + t) ω - W σ ω) (ζ ω - σ) := by
  have hT := isStoppingTime_const 𝓕 σ
  have hA : MeasurableSet[hT.measurableSpace] (restartEventTies σ xL xR W VL VR ζ) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurableSet_restartEventTies σ hE
  have hAT : ∀ ω ∈ restartEventTies σ xL xR W VL VR ζ,
      (((fun _ => σ) ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (0 < (fun _ => σ) ω ∨ ∀ i j, xL i < xR j) :=
    fun ω hω => ⟨hω.1, Or.inl hσ⟩
  have hlaw := measure_restart_codeEvent hκ hE hT hA hAT (Φ := fun w τ => ¬ NoClusterEvent w τ)
    measurableSet_noClusterCodeSet.compl (fun _ _ _ => Iff.rfl) not_noClusterEvent_congr
  have hAm : MeasurableSet (restartEventTies σ xL xR W VL VR ζ) := hT.measurableSpace_le _ hA
  have hzero : ∫⁻ ω in restartEventTies σ xL xR W VL VR ζ,
      codeLaw κ ρL ρR (noClusterCodeSet (nL := 1) (nR := 1))ᶜ (wordAt W VL VR (fun _ => σ) ω) ∂P = 0 := by
    refine (setLIntegral_congr_fun_ae hAm ?_).trans (setLIntegral_const _ 0 |>.trans (zero_mul _))
    filter_upwards [ae_solvable_restart hκ hE hT hA hAT] with ω h hω
    obtain ⟨hFy, hadm', hxL', hxR'⟩ := word_of_mem_restartEventTies hF hadm hω
    exact codeLaw_compl_noClusterCodeSet_eq_zero hκ hN hFy hadm' hxL' hxR' (h hω).2
  rw [hzero] at hlaw
  have h1 : ∀ᵐ ω ∂P, ω ∈ restartEventTies σ xL xR W VL VR ζ →
      NoClusterEvent (fun t => W (σ + t) ω - W σ ω) (ζ ω - σ) := by
    rw [ae_iff]
    refine le_antisymm (le_of_eq_of_le ?_ hlaw.le) bot_le
    congr 1
    ext ω
    simp only [mem_ofPred_eq, Classical.not_imp, mem_inter_iff]
  filter_upwards [h1, Zhan.IsIntegratedSLEEvolution.ae_mem_restartEventTies hκ hF hadm hE] with ω h ⟨_, hmem⟩
  exact h (hmem σ hσ)

/-- **The seed is not a terminal cluster point** (B.3 L1260–L1262), given the named input: for an admissible
one-mark-per-side word (in particular the two-seed word), almost surely `0` is not a terminal cluster point of any
continuous generating trace on `[0, ∞)`. -/
theorem IsIntegratedSLEEvolution.ae_noCluster_zero (hκ : 0 < κ) (hN : SeparatedNoRealClusterStatement.{0} κ)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖η t‖ := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  filter_upwards [IsIntegratedSLEEvolution.ae_restart_noClusterEvent hκ hN hF hadm hE (σ := 1) one_pos,
    hE.2.2.2.2, Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE] with ω hev hp ⟨hζ, _⟩ η hη
  obtain ⟨-, hTop, hRat⟩ := hev
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hw0 : (fun t => W t ω) 0 = 0 := hp.1
  have hwc₂ : Continuous (Sec7.shiftNN (fun t => W t ω) 1) :=
    (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
  obtain ⟨η₂, hη₂⟩ := (ratVals_mem_topSet_iff hwc₂ (Sec7.shiftNN_zero _ _)).1 hTop
  have hno₂ := (ratVals_mem_ratNoClusterSet_iff hwc₂ (Sec7.shiftNN_zero _ _) hη₂).1 hRat
  exact eventually_le_norm_of_shift_noRealCluster hwc hw0 hη hη₂ hno₂

end Kernel

/-! ### Two-seed transience -/

section Assembly

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Two-seed transience from the named input** (B.3 L1260–L1264), every `κ > 0`: for seed forces at `0⁻`, `0⁺` with
admissible weights (`ρ_L, ρ_R ≥ κ/2 − 2`), if separated two-force laws have no real terminal cluster point, then almost
surely every continuous generating trace on `[0, ∞)` tends to `∞`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed_of_separatedNoCluster (hκ : 0 < κ)
    (hN : SeparatedNoRealClusterStatement.{0} κ)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR (fun _ => 0) (fun _ => 0))
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoSeed_of_noCluster hκ hadm hE
    (IsIntegratedSLEEvolution.ae_noCluster_zero hκ hN isOrderedForceWord_zero hadm hE)

end Assembly

end InteractingSLE.ZhanGT4
