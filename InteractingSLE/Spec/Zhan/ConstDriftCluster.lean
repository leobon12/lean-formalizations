/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftHull
import InteractingSLE.Spec.Zhan.ConstDriftKoebe

/-!
# Constant strip drift `|σ| < 1`: from the upper points to the actual endpoint (deterministic)

Packet PROVE-ZHAN-A5. Astra, *Formalization proofs and dependency audit* (ruling R35), "Constant drift with
`|σ| < 1`" (`source/external/AstraIG1/ig1_formalization_proofs.txt` L1441–L1499). This file is the deterministic
part of the argument, for one strip path `(w, v, ζ)` and one generating trace `η` on its strip life, in chordal
coordinates (`x + iπ ↦ −1 − e^x`, the strip height of `η` is `arg (1 + η)`):

* `IsStripPath.trace_mem_of_mem_H`: a closed condition on the trace points in `ℍ` holds at every time of the
  strip life (real trace points are limits of later points in `ℍ`, by strict growth of the hulls);
* `IsStripPath.exists_pos_le_norm_trace_sub_left`, `…_right` (**every upper point with a bounded upper-gap
  integral stays at positive distance from the trace**): Koebe at the real point `y < −1` (`ConstDriftKoebe.lean`)
  on every hull of the strip life, with the bound `∫ 2/((v − y)(w − v)) ≤ K` (resp. `∫ 2(v − y)/(w − v)³ ≤ K`),
  which in strip time is `∫ 2e^{∓X}`, `X` the upper gap (3.15); `…_sech`: the same from the derivative integral
  `∫ (2/(u_y(v − w)) − 2/u_y²)`, in strip time `½∫ sech²(X/2)` ((3.23), used downstream);
* `IsStripPath.stripConv_of_height` (**the endpoint**): if the trace is horizontally bounded (`ConstDriftHull.lean`),
  its strip height tends to `π` along the strip life, and every point `−1 − e^q`, `q ∈ ℚ`, stays at positive distance
  from it, then it converges along the strip life to a point `x < −1`. (The source's cluster-set argument: the
  limit points lie on the upper line and form an interval; the rational upper points are excluded. Here: the real
  part of the trace eventually stays on one side of each rational upper point, by the intermediate value theorem,
  and `x` is the supremum of the levels it eventually exceeds.)
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace Zhan

open Strip

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-! ### Eventually along the strip life -/

/-- `P` holds eventually along the strip life. -/
def EvLife (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (P : ℝ≥0 → Prop) : Prop :=
  ∃ s₀ : ℝ≥0, IsStripLife w v ζ s₀ ∧ ∀ s : ℝ≥0, s₀ ≤ s → IsStripLife w v ζ s → P s

theorem EvLife.and {P Q : ℝ≥0 → Prop} (h₁ : EvLife w v ζ P) (h₂ : EvLife w v ζ Q) :
    EvLife w v ζ fun s => P s ∧ Q s := by
  obtain ⟨a, ha, hP⟩ := h₁
  obtain ⟨b, hb, hQ⟩ := h₂
  refine ⟨max a b, ?_, fun s hs hsl =>
    ⟨hP s ((le_max_left _ _).trans hs) hsl, hQ s ((le_max_right _ _).trans hs) hsl⟩⟩
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab]; exact hb
  · rw [max_eq_left hab]; exact ha

theorem EvLife.mono {P Q : ℝ≥0 → Prop} (h : EvLife w v ζ P)
    (hPQ : ∀ s, IsStripLife w v ζ s → P s → Q s) : EvLife w v ζ Q := by
  obtain ⟨a, ha, hP⟩ := h
  exact ⟨a, ha, fun s hs hsl => hPQ s hsl (hP s hs hsl)⟩

theorem EvLife.exists {P : ℝ≥0 → Prop} (h : EvLife w v ζ P) : ∃ s, IsStripLife w v ζ s ∧ P s := by
  obtain ⟨a, ha, hP⟩ := h
  exact ⟨a, ha, hP a le_rfl ha⟩

/-! ### Closed conditions on the trace -/

/-- **A closed condition on the trace points in `ℍ` holds on the whole strip life.** -/
theorem IsStripPath.trace_mem_of_mem_H (h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {C : Set ℂ} (hC : IsClosed C)
    (hH : ∀ t : ℝ≥0, IsStripLife w v ζ t → 0 < (η t).im → η t ∈ C) {s : ℝ≥0}
    (hs : IsStripLife w v ζ s) : η s ∈ C := by
  by_contra hns
  obtain ⟨s', hss', hs'⟩ := h.exists_gt hs
  have hηs' := hη s' hs'
  have hw := h.continuousOn_lt hs'
  have hw0 : w 0 = 0 := h.1
  have hcont : ContinuousWithinAt η {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s'} s :=
    hηs'.2.1 s (show ((s : ℝ≥0) : ℝ≥0∞) ≤ s' from ENNReal.coe_le_coe.2 hss'.le)
  have hev := hcont.preimage_mem_nhdsWithin (hC.isOpen_compl.mem_nhds hns)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set b' : ℝ≥0 := min s' (s + (ε / 2).toNNReal) with hb'
  have hsb' : s < b' := lt_min hss' (by
    have : (0 : ℝ≥0) < (ε / 2).toNNReal := Real.toNNReal_pos.2 (by linarith)
    exact lt_add_of_pos_right s this)
  obtain ⟨t, ⟨hst, htb⟩, htH⟩ :=
    Restart.IsGeneratingTrace.exists_mem_H hηs' hw hw0 hsb' (ENNReal.coe_le_coe.2 (min_le_left _ _))
  have hts' : t ≤ s' := htb.le.trans (min_le_left _ _)
  have ht : IsStripLife w v ζ t := hs'.mono hts'
  refine hball ⟨?_, show ((t : ℝ≥0) : ℝ≥0∞) ≤ s' from ENNReal.coe_le_coe.2 hts'⟩ (hH t ht htH)
  rw [Metric.mem_ball, NNReal.dist_eq]
  have h1 : (t : ℝ) ≤ s + ε / 2 := by
    have := htb.le.trans (min_le_right s' _)
    have h2 : ((s + (ε / 2).toNNReal : ℝ≥0) : ℝ) = s + ε / 2 := by
      rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)]
    exact (NNReal.coe_le_coe.2 this).trans h2.le
  have h2 : (s : ℝ) < t := NNReal.coe_lt_coe.2 hst
  rw [abs_lt]; constructor <;> linarith

/-! ### Upper points with bounded upper-gap integral avoid the trace -/

/-- The data of the Koebe lemma on a hull of the strip life: for `s < s' < s''` in the strip life, the frozen
driver at `s''` is continuous, `−1` is alive (end mark), and the inverse map at `s'` extends continuously to `ℍ̄`. -/
theorem IsStripPath.koebe_data (h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {s' s'' : ℝ≥0} (hs's'' : s' < s'')
    (hs'' : IsStripLife w v ζ s'') :
    Continuous (frozenDrive w s'') ∧ frozenDrive w s'' 0 = 0 ∧
      IsForwardSol (frozenDrive w s'') ((-1 : ℝ) : ℂ) s'
        (fun r => ((extPath v r - extPath w r : ℝ) : ℂ)) ∧
      EqOn (extendFrom H (fwdMapInv (frozenDrive w s'') s')) (fwdMapInv (frozenDrive w s'') s') H ∧
      ContinuousOn (extendFrom H (fwdMapInv (frozenDrive w s'') s')) Hbar ∧
      fwdHull (extPath w) s' = fwdHull (frozenDrive w s'') s' := by
  have hw0 : w 0 = 0 := h.1
  have hfc : Continuous (frozenDrive w s'') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.continuousOn_le hs'')
  have hW0 : frozenDrive w s'' 0 = 0 := by rw [frozenDrive_zero (NNReal.coe_nonneg s''), hw0]
  have h₁ : Sec7.IsGeneratingTraceIcc w s' η :=
    Sec7.IsGeneratingTrace.isGeneratingTraceIcc (hη s'' hs'') (h.continuousOn_lt hs'') hw0
      (ENNReal.coe_lt_coe.2 hs's'')
  obtain ⟨-, -, hFeq, hFc, -, -, -⟩ :=
    h₁.extend_props (t₂ := (s'' : ℝ)) (NNReal.coe_lt_coe.2 hs's'') hfc hw0
  refine ⟨hfc, hW0, h.isForwardSol_end hs'' hs's''.le, hFeq, hFc, ?_⟩
  exact fwdHull_eq_of_eqOn (NNReal.coe_nonneg s') (NNReal.coe_lt_coe.2 hs's'') fun r hr =>
    (frozenDrive_eq hr).symm

/-- **An upper point with a bounded left upper-gap integral avoids the trace.** Let `y < −1`. If, for every pair
`s' < s''` of the strip life, the flow of `y` under the frozen driver satisfies
`∫₀^{s'} 2/((v − y)(w − v)) ≤ K` (in strip time `∫ 2e^{−X}`), then the trace stays at distance
`≥ (−1 − y)e^{−K}/48` from `y` on the strip life. -/
theorem IsStripPath.exists_pos_le_norm_trace_sub_left (h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {y : ℝ} (hy : y < -1) {K : ℝ}
    (hK : ∀ s' s'' : ℝ≥0, s' < s'' → IsStripLife w v ζ s'' → ∀ uy : ℝ → ℂ,
      IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy →
        ∫ r in (0 : ℝ)..s', 2 / (((extPath v r - extPath w r) - (uy r).re) *
          -(extPath v r - extPath w r)) ≤ K) :
    ∃ ρ > 0, ∀ s : ℝ≥0, IsStripLife w v ζ s → ρ ≤ ‖η s - y‖ := by
  have hk := QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hy1 : 0 < -1 - y := by linarith
  refine ⟨QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K)), by positivity,
    fun s hs => ?_⟩
  refine h.trace_mem_of_mem_H hη (C := {z | QuantumZipper.CA.Koebe.koebeCovConst *
    ((-1 - y) * Real.exp (-K)) ≤ ‖z - y‖}) (isClosed_le continuous_const (by fun_prop)) (fun t ht htH => ?_) hs
  obtain ⟨s', hts', hs'⟩ := h.exists_gt ht
  obtain ⟨s'', hs's'', hs''⟩ := h.exists_gt hs'
  obtain ⟨hfc, hW0, huV, hFeq, hFc, hKeq⟩ := h.koebe_data hη hs's'' hs''
  obtain ⟨uy, huy⟩ := exists_isForwardSol_of_lt_neg_one hfc hW0 (NNReal.coe_nonneg s') huV hy
  have hdisj := disjoint_ball_fwdHull_left hfc hW0 (NNReal.coe_nonneg s') hFeq hFc huV hy huy
    (K := K) (by simpa using hK s' s'' hs's'' hs'' uy huy)
  have hmem : η t ∈ fwdHull (extPath w) s' := h.mem_fwdHull_of_trace hη hts'.le hs' htH
  rw [hKeq] at hmem
  show _ ≤ ‖η t - y‖
  by_contra hlt
  push Not at hlt
  exact Set.disjoint_left.1 hdisj (show η t ∈ ball (y : ℂ) _ by rw [mem_ball, dist_eq_norm]; exact hlt) hmem

/-- **An upper point with a bounded right upper-gap integral avoids the trace** (`∫ 2(v − y)/(w − v)³ ≤ K`, in strip
time `∫ 2e^{X}`): distance `≥ (−1 − y)e^{−K}/96`. -/
theorem IsStripPath.exists_pos_le_norm_trace_sub_right (h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {y : ℝ} (hy : y < -1) {K : ℝ}
    (hK : ∀ s' s'' : ℝ≥0, s' < s'' → IsStripLife w v ζ s'' → ∀ uy : ℝ → ℂ,
      IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy →
        ∫ r in (0 : ℝ)..s', 2 * ((extPath v r - extPath w r) - (uy r).re) /
          (-(extPath v r - extPath w r)) ^ 3 ≤ K) :
    ∃ ρ > 0, ∀ s : ℝ≥0, IsStripLife w v ζ s → ρ ≤ ‖η s - y‖ := by
  have hk := QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hy1 : 0 < -1 - y := by linarith
  refine ⟨QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K) / 2), by positivity,
    fun s hs => ?_⟩
  refine h.trace_mem_of_mem_H hη (C := {z | QuantumZipper.CA.Koebe.koebeCovConst *
    ((-1 - y) * Real.exp (-K) / 2) ≤ ‖z - y‖}) (isClosed_le continuous_const (by fun_prop))
    (fun t ht htH => ?_) hs
  obtain ⟨s', hts', hs'⟩ := h.exists_gt ht
  obtain ⟨s'', hs's'', hs''⟩ := h.exists_gt hs'
  obtain ⟨hfc, hW0, huV, hFeq, hFc, hKeq⟩ := h.koebe_data hη hs's'' hs''
  obtain ⟨uy, huy⟩ := exists_isForwardSol_of_lt_neg_one hfc hW0 (NNReal.coe_nonneg s') huV hy
  have hdisj := disjoint_ball_fwdHull_right hfc hW0 (NNReal.coe_nonneg s') hFeq hFc huV hy huy
    (K := K) (by simpa using hK s' s'' hs's'' hs'' uy huy)
  have hmem : η t ∈ fwdHull (extPath w) s' := h.mem_fwdHull_of_trace hη hts'.le hs' htH
  rw [hKeq] at hmem
  show _ ≤ ‖η t - y‖
  by_contra hlt
  push Not at hlt
  exact Set.disjoint_left.1 hdisj (show η t ∈ ball (y : ℂ) _ by rw [mem_ball, dist_eq_norm]; exact hlt) hmem

/-! ### The endpoint -/

/-- The points `−1 − e^q`, `q ∈ ℚ`, are dense in `(−∞, −1)`. -/
theorem exists_rat_neg_one_sub_exp_mem {α β : ℝ} (hαβ : α < β) (hβ : β < -1) :
    ∃ q : ℚ, α < -1 - Real.exp q ∧ -1 - Real.exp q < β := by
  have h1 : 0 < -1 - β := by linarith
  have h2 : -1 - β < -1 - α := by linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Real.log_lt_log h1 h2)
  have e1 := Real.exp_lt_exp.2 hq1
  have e2 := Real.exp_lt_exp.2 hq2
  rw [Real.exp_log h1] at e1
  rw [Real.exp_log (h1.trans h2)] at e2
  exact ⟨q, by linarith, by linarith⟩

/-- **One side of a level.** If the real part of the trace avoids a level `y` from the time `s₀` of the strip life
on, it stays on one side of `y` (intermediate value theorem). -/
theorem IsStripPath.side_of_ne (_h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {y : ℝ} {s₀ : ℝ≥0}
    (hs₀ : IsStripLife w v ζ s₀) (hne : ∀ s, s₀ ≤ s → IsStripLife w v ζ s → (η s).re ≠ y) :
    (∀ s, s₀ ≤ s → IsStripLife w v ζ s → (η s).re < y) ∨
      ∀ s, s₀ ≤ s → IsStripLife w v ζ s → y < (η s).re := by
  have hcont : ∀ s, IsStripLife w v ζ s → ContinuousOn (fun t => (η t).re) (Icc s₀ s) := fun s hs =>
    (continuous_re.comp_continuousOn (hη s hs).2.1).mono fun t ht =>
      show ((t : ℝ≥0) : ℝ≥0∞) ≤ s from ENNReal.coe_le_coe.2 ht.2
  rcases (hne s₀ le_rfl hs₀).lt_or_gt with hlt | hgt
  · left
    intro s hs hsl
    by_contra hge
    push Not at hge
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc hs (hcont s hsl) ⟨hlt.le, hge⟩
    exact hne t ht.1 (hsl.mono ht.2) hty
  · right
    intro s hs hsl
    by_contra hge
    push Not at hge
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc' hs (hcont s hsl) ⟨hge, hgt.le⟩
    exact hne t ht.1 (hsl.mono ht.2) hty

/-- **The actual endpoint** (deterministic). Let the trace `η` of a strip path be horizontally bounded
(`e^{−M} ≤ ‖1 + η‖ ≤ e^M`), let its strip height `arg (1 + η)` tend to `π` along the strip life, and let every
point `−1 − e^q`, `q ∈ ℚ`, stay at positive distance from it. Then `η` converges along the strip life to a point
`x < −1`. -/
theorem IsStripPath.stripConv_of_height (h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {M : ℝ}
    (hbd : ∀ s : ℝ≥0, IsStripLife w v ζ s → ‖1 + η s‖ ∈ Icc (Real.exp (-M)) (Real.exp M))
    (hheight : ∀ ε > 0, EvLife w v ζ fun s => Real.pi - ε < arg (1 + η s))
    (havoid : ∀ q : ℚ, ∃ ρ > 0, ∀ s : ℝ≥0, IsStripLife w v ζ s → ρ ≤ ‖η s - ((-1 - Real.exp q : ℝ) : ℂ)‖) :
    ∃ x : ℝ, x < -1 ∧ ∀ ε > 0, EvLife w v ζ fun s => ‖η s - x‖ < ε := by
  have hM0 := Real.exp_pos M
  have hMm := Real.exp_pos (-M)
  -- the height angle near `π`
  have htrig : ∀ s : ℝ≥0, ∀ δ, δ ≤ 1 → Real.pi - δ < arg (1 + η s) →
      Real.sin (arg (1 + η s)) ≤ δ ∧ Real.cos (arg (1 + η s)) ≤ -1 / 2 := by
    intro s δ hδ harg
    have hle : arg (1 + η s) ≤ Real.pi := arg_le_pi _
    set φ := Real.pi - arg (1 + η s) with hφ
    have hθ : arg (1 + η s) = Real.pi - φ := by rw [hφ]; ring
    have hφ0 : 0 ≤ φ := by linarith
    have hφ1 : φ < δ := by linarith
    rw [hθ, Real.sin_pi_sub, Real.cos_pi_sub]
    refine ⟨(Real.sin_le hφ0).trans hφ1.le, ?_⟩
    have := Real.one_sub_sq_div_two_le_cos (x := φ)
    nlinarith
  -- the imaginary part tends to `0`; the real part is eventually in `[−1 − e^M, −1 − e^{−M}/2]`
  have him : ∀ ε > 0, EvLife w v ζ fun s => |(η s).im| < ε := by
    intro ε hε
    refine (hheight (min 1 (ε / (2 * Real.exp M))) (lt_min one_pos (by positivity))).mono
      fun s hs harg => ?_
    have hb := hbd s hs
    obtain ⟨hsin, -⟩ := htrig s _ (min_le_left _ _) harg
    have hsin0 : 0 ≤ Real.sin (arg (1 + η s)) := by
      rw [sin_arg]
      by_cases h0 : ‖1 + η s‖ = 0
      · rw [h0, div_zero]
      · refine div_nonneg ?_ (norm_nonneg _)
        by_contra hneg
        push Not at hneg
        have := arg_neg_iff.2 hneg
        linarith [Real.pi_gt_three, min_le_left 1 (ε / (2 * Real.exp M))]
    have e : (η s).im = ‖1 + η s‖ * Real.sin (arg (1 + η s)) := by
      rw [norm_mul_sin_arg]; simp
    rw [e, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hsin0]
    calc ‖1 + η s‖ * Real.sin (arg (1 + η s)) ≤ Real.exp M * (ε / (2 * Real.exp M)) :=
          mul_le_mul hb.2 (hsin.trans (min_le_right _ _)) hsin0 hM0.le
      _ < ε := by field_simp; linarith
  have hre : EvLife w v ζ fun s => -1 - Real.exp M ≤ (η s).re ∧ (η s).re ≤ -1 - Real.exp (-M) / 2 := by
    refine (hheight 1 one_pos).mono fun s hs harg => ?_
    have hb := hbd s hs
    obtain ⟨-, hcos⟩ := htrig s 1 le_rfl harg
    have e : (η s).re = ‖1 + η s‖ * Real.cos (arg (1 + η s)) - 1 := by
      rw [norm_mul_cos_arg]; simp
    have hc1 := Real.neg_one_le_cos (arg (1 + η s))
    constructor
    · rw [e]; nlinarith [hb.2, norm_nonneg (1 + η s)]
    · rw [e]; nlinarith [hb.1, norm_nonneg (1 + η s)]
  -- each rational level: eventually on one side
  have hside : ∀ q : ℚ, EvLife w v ζ (fun s => (η s).re < -1 - Real.exp q) ∨
      EvLife w v ζ (fun s => -1 - Real.exp q < (η s).re) := by
    intro q
    obtain ⟨ρ, hρ, hρη⟩ := havoid q
    obtain ⟨s₀, hs₀, hs₀im⟩ := him ρ hρ
    have hne : ∀ s, s₀ ≤ s → IsStripLife w v ζ s → (η s).re ≠ -1 - Real.exp q := by
      intro s hs hsl heq
      have h1 := hρη s hsl
      have h2 := hs₀im s hs hsl
      have e : η s - ((-1 - Real.exp q : ℝ) : ℂ) = ((η s).im : ℂ) * I := by
        apply Complex.ext
        · simp only [sub_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]; rw [heq]; ring
        · simp only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re]; ring
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h1
      linarith
    rcases h.side_of_ne hη hs₀ hne with hl | hr
    · exact Or.inl ⟨s₀, hs₀, hl⟩
    · exact Or.inr ⟨s₀, hs₀, hr⟩
  -- the levels eventually exceeded
  set A : Set ℝ := {a | EvLife w v ζ fun s => a < (η s).re} with hA
  have hAne : (-2 - Real.exp M) ∈ A := hre.mono fun s _ hs => by linarith [hs.1]
  have hAbdd : ∀ a ∈ A, a ≤ -1 - Real.exp (-M) / 2 := by
    intro a ha
    by_contra hlt
    push Not at hlt
    obtain ⟨s, -, hs1, hs2⟩ := (EvLife.and ha hre).exists
    linarith [hs2.2]
  have hbdd : BddAbove A := ⟨_, hAbdd⟩
  set x := sSup A with hx
  have hxle : x ≤ -1 - Real.exp (-M) / 2 := csSup_le ⟨_, hAne⟩ hAbdd
  have hx1 : x < -1 := by linarith
  refine ⟨x, hx1, fun ε hε => ?_⟩
  obtain ⟨q₁, -, hq₁b⟩ := exists_rat_neg_one_sub_exp_mem (show x - ε / 2 < x by linarith) hx1
  obtain ⟨q₁', hq₁a', hq₁b'⟩ :=
    exists_rat_neg_one_sub_exp_mem (show x - ε / 2 < x by linarith) hx1
  have hlow : EvLife w v ζ fun s => -1 - Real.exp q₁' < (η s).re := by
    obtain ⟨a, haA, ha⟩ := exists_lt_of_lt_csSup ⟨_, hAne⟩ hq₁b'
    exact EvLife.mono haA fun s _ hs => by linarith
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_neg_one_sub_exp_mem
    (show x < min (x + ε / 2) ((x - 1) / 2) from lt_min (by linarith) (by linarith))
    (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have hup : EvLife w v ζ fun s => (η s).re < -1 - Real.exp q₂ := by
    rcases hside q₂ with hl | hr
    · exact hl
    · exfalso
      have := le_csSup hbdd (show -1 - Real.exp q₂ ∈ A from hr)
      linarith
  have hq₂' : -1 - Real.exp q₂ < x + ε / 2 := lt_of_lt_of_le hq₂b (min_le_left _ _)
  refine EvLife.mono (EvLife.and (EvLife.and hlow hup) (him (ε / 2) (by linarith))) fun s _ hs => ?_
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  calc ‖η s - x‖ ≤ |(η s - x).re| + |(η s - x).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |(η s).re - x| + |(η s).im| := by simp
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add_of_le_of_lt _ h3
        rw [abs_le]; constructor <;> linarith
    _ = ε := by ring

/-- **An upper point with a bounded derivative integral avoids the trace** ((3.23)): if, for every pair `s' < s''`
of the strip life, `∫₀^{s'} (2/(u_y (v − w)) − 2/u_y²) ≤ K` (in strip time `½∫ sech²(X/2)`), then the trace stays at
distance `≥ (−1 − y)e^{−K}/48` from `y` on the strip life. -/
theorem IsStripPath.exists_pos_le_norm_trace_sub_sech (h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {y : ℝ} (hy : y < -1) {K : ℝ}
    (hK : ∀ s' s'' : ℝ≥0, s' < s'' → IsStripLife w v ζ s'' → ∀ uy : ℝ → ℂ,
      IsForwardSol (frozenDrive w s'') (y : ℂ) s' uy →
        ∫ r in (0 : ℝ)..s', (2 / ((uy r).re * (extPath v r - extPath w r)) - 2 / (uy r).re ^ 2) ≤ K) :
    ∃ ρ > 0, ∀ s : ℝ≥0, IsStripLife w v ζ s → ρ ≤ ‖η s - y‖ := by
  have hk := QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hy1 : 0 < -1 - y := by linarith
  refine ⟨QuantumZipper.CA.Koebe.koebeCovConst * ((-1 - y) * Real.exp (-K)), by positivity,
    fun s hs => ?_⟩
  refine h.trace_mem_of_mem_H hη (C := {z | QuantumZipper.CA.Koebe.koebeCovConst *
    ((-1 - y) * Real.exp (-K)) ≤ ‖z - y‖}) (isClosed_le continuous_const (by fun_prop)) (fun t ht htH => ?_) hs
  obtain ⟨s', hts', hs'⟩ := h.exists_gt ht
  obtain ⟨s'', hs's'', hs''⟩ := h.exists_gt hs'
  obtain ⟨hfc, hW0, huV, hFeq, hFc, hKeq⟩ := h.koebe_data hη hs's'' hs''
  obtain ⟨uy, huy⟩ := exists_isForwardSol_of_lt_neg_one hfc hW0 (NNReal.coe_nonneg s') huV hy
  have hdisj := disjoint_ball_fwdHull_sech hfc hW0 (NNReal.coe_nonneg s') hFeq hFc huV hy huy
    (K := K) (by simpa using hK s' s'' hs's'' hs'' uy huy)
  have hmem : η t ∈ fwdHull (extPath w) s' := h.mem_fwdHull_of_trace hη hts'.le hs' htH
  rw [hKeq] at hmem
  show _ ≤ ‖η t - y‖
  by_contra hlt
  push Not at hlt
  exact Set.disjoint_left.1 hdisj (show η t ∈ ball (y : ℂ) _ by rw [mem_ball, dist_eq_norm]; exact hlt) hmem

end Zhan

end InteractingSLE
