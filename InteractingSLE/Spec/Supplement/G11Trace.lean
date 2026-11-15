/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G11Ode
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Spec.Sec5.CrossRestartTrace
import InteractingSLE.Spec.Sec7.TwoForcePocket
import InteractingSLE.Foundations.Strip.SLE
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Lemma G11, pathwise part: a finite budget keeps the trace off the mark

Packet PROVE-G11-G4. Supplement §7.9, Lemma G11 (p. 503). This file turns the deterministic estimate of
`G11Ode.lean` into the pathwise statement used for G11:

* `false_of_hull_stable`: a generating trace cannot be at a point `η(t) ∈ U` (`U` open, `t > 0`) if the hulls do not
  grow inside `U` just before `t` (`U ∩ K_{s₂} ⊆ K_{s₁}` for `s₁ < s₂` close to `t`): the trace near time `t` would add
  nothing to the filling, against the strict growth of the hulls;
* `isSeedMarkPath_of_isForcePath`: the pathwise data of the two-mark word on `[0, T]` before the mark is swallowed
  (`IsSeedMarkPath`, with the driver frozen after a time `T₂ < ζ`);
* `trace_ne_one_of_budget`: for one path of the two-mark word (seed weight `r > −2` at `0⁺`, the mark at `1`) whose
  budget `∫₀ˢ β` is bounded on the life before the swallow of the mark, every generating trace avoids `1` on `[0, ζ]`,
  the terminal value included. Before and at the first swallow
  `τ` the ball `B(1, e^{−C/2}/2)` meets no hull (`IsSeedMarkPath.not_mem_fwdHull`); after it, the half-ball is inside
  `K_τ` (`IsSeedMarkPath.mem_fwdHull_of_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Supp7

namespace G11

/-! ### Hulls that stop growing near a trace point -/

section Topo

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- If the trace between `s₁ ≤ s₂ < T` only meets `ℍ` inside `K_{s₁}`, then `K_{s₂} ⊆ K_{s₁}`. -/
theorem hull_subset_of_trace (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T})
    {s₁ s₂ : ℝ≥0} (h12 : s₁ ≤ s₂) (hs₂ : (s₂ : ℝ≥0∞) < T)
    (hsub : η '' Icc s₁ s₂ ∩ H ⊆ fwdHull (fun s : ℝ => w s.toNNReal) s₁) :
    fwdHull (fun s : ℝ => w s.toNNReal) s₂ ⊆ fwdHull (fun s : ℝ => w s.toNNReal) s₁ := by
  have hs₁ : (s₁ : ℝ≥0∞) < T := lt_of_le_of_lt (ENNReal.coe_le_coe.2 h12) hs₂
  have hF₁ := hη.2.2 s₁ hs₁
  have hF₂ := hη.2.2 s₂ hs₂
  set K₁ := fwdHull (fun s : ℝ => w s.toNNReal) s₁ with hK₁
  set K₂ := fwdHull (fun s : ℝ => w s.toNNReal) s₂ with hK₂
  -- `K₂` is bounded (it is the hull of a continuous frozen driver)
  obtain ⟨t₂, ht₂, ht₂T⟩ : ∃ t₂ : ℝ, (s₂ : ℝ) < t₂ ∧ ENNReal.ofReal t₂ < T := by
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs₂
    refine ⟨c, by exact_mod_cast hc1, ?_⟩
    rw [ENNReal.ofReal_coe_nnreal]; exact hc2
  have hK₂b : Bornology.IsBounded K₂ := by
    rw [hK₂, fwdHull_eq_of_eqOn (W' := frozenDrive w t₂) s₂.coe_nonneg ht₂ fun r hr => (frozenDrive_eq hr).symm]
    exact isBounded_fwdHull (continuous_frozenDrive_of_lt hw ht₂T) _
  -- `ℍ \ K₁` is a preconnected unbounded subset of `ℍ \ η[0, s₂]`
  obtain ⟨⟨z₁, -, hcomp⟩, hunb⟩ := hF₁
  have hP : IsPreconnected (H \ K₁) := by rw [← hcomp]; exact isPreconnected_connectedComponentIn
  have hPA : H \ K₁ ⊆ H \ η '' Icc 0 s₂ := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    rintro ⟨u, hu, rfl⟩
    by_cases hu1 : u ≤ s₁
    · exact hx.2 (Sec5.CrossRestart.inter_H_subset_of_isFilling (hη.2.2 s₁ hs₁)
        ⟨⟨u, ⟨hu.1, hu1⟩, rfl⟩, hx.1⟩)
    · exact hx.2 (hsub ⟨⟨u, ⟨(not_le.1 hu1).le, hu.2⟩, rfl⟩, hx.1⟩)
  intro z hz
  by_contra hz₁
  have hzP : z ∈ H \ K₁ := ⟨hz.1, hz₁⟩
  -- a far point of `ℍ \ K₁` lies outside the bounded `K₂`
  obtain ⟨z', hz'P, hz'K⟩ : ∃ z' ∈ H \ K₁, z' ∉ K₂ := by
    by_contra hall
    push Not at hall
    exact hunb (hK₂b.subset fun x hx => hall x hx)
  exact Sec7.notMem_of_isFilling_of_isPreconnected hF₂ hP hPA hz'P hzP hz'K hz

/-- **A trace point where the hulls stop growing.** If `η(t) ∈ U` (`U` open, `0 < t ≤ T`) and `U ∩ K_{s₂} ⊆ K_{s₁}`
whenever `t − ε < s₁ < s₂ < t`, we reach a contradiction: the trace just before `t` adds nothing to the filling. -/
theorem false_of_hull_stable (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {t : ℝ≥0} (ht0 : 0 < t) (htT : (t : ℝ≥0∞) ≤ T) {U : Set ℂ} (hU : IsOpen U)
    (hηU : η t ∈ U) {ε : ℝ} (hε : 0 < ε)
    (hstab : ∀ s₁ s₂ : ℝ≥0, (t : ℝ) - ε < s₁ → s₁ < s₂ → s₂ < t →
      U ∩ fwdHull (fun s : ℝ => w s.toNNReal) s₂ ⊆ fwdHull (fun s : ℝ => w s.toNNReal) s₁) : False := by
  -- continuity of `η` at `t` within `[0, T]`
  have hcont : ContinuousWithinAt η {s | (s : ℝ≥0∞) ≤ T} t := hη.2.1 t htT
  have hev : ∀ᶠ s in 𝓝[{s | (s : ℝ≥0∞) ≤ T}] t, η s ∈ U := hcont (hU.mem_nhds hηU)
  rw [Filter.Eventually, mem_nhdsWithin] at hev
  obtain ⟨V, hVo, htV, hVsub⟩ := hev
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hVo t htV
  set m : ℝ := min (min ε δ) t with hm
  have hm0 : 0 < m := lt_min (lt_min hε hδ) (by exact_mod_cast ht0)
  set s₁ : ℝ≥0 := ⟨(t : ℝ) - m / 2, by have : m ≤ t := min_le_right _ _; linarith⟩ with hs₁
  set s₂ : ℝ≥0 := ⟨(t : ℝ) - m / 4, by have : m ≤ t := min_le_right _ _; linarith⟩ with hs₂
  have hs12 : s₁ < s₂ := by
    show (t : ℝ) - m / 2 < (t : ℝ) - m / 4
    linarith
  have hs2t : s₂ < t := by
    show (t : ℝ) - m / 4 < t
    linarith
  have hmε : m ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
  have hs₂T : (s₂ : ℝ≥0∞) < T := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hs2t) htT
  -- the trace on `[s₁, s₂]` stays in `U`
  have hin : ∀ u ∈ Icc s₁ s₂, η u ∈ U := by
    intro u hu
    refine hVsub ⟨hball ?_, ?_⟩
    · rw [Metric.mem_ball, NNReal.dist_eq]
      have h1 : (t : ℝ) - m / 2 ≤ u := hu.1
      have h2 : (u : ℝ) ≤ (t : ℝ) - m / 4 := hu.2
      rw [abs_lt]
      constructor <;> linarith
    · exact (ENNReal.coe_le_coe.2 (hu.2.trans hs2t.le)).trans htT
  have hsub : η '' Icc s₁ s₂ ∩ H ⊆ fwdHull (fun s : ℝ => w s.toNNReal) s₁ := by
    rintro x ⟨⟨u, hu, rfl⟩, hxH⟩
    refine hstab s₁ s₂ (by show (t : ℝ) - ε < (t : ℝ) - m / 2; linarith) hs12 hs2t ⟨hin u hu, ?_⟩
    exact Sec5.CrossRestart.inter_H_subset_of_isFilling (hη.2.2 s₂ hs₂T)
      ⟨⟨u, ⟨zero_le, hu.2⟩, rfl⟩, hxH⟩
  have hle := hull_subset_of_trace hη hw hs12.le hs₂T hsub
  have hge := (QuantumZipper.fwdHull_mono (W := fun s : ℝ => w s.toNNReal)).1
    (show (s₁ : ℝ) ≤ s₂ from hs12.le)
  -- strict growth of the hulls of the frozen driver
  obtain ⟨t₂, ht₂, ht₂T⟩ : ∃ t₂ : ℝ, (s₂ : ℝ) < t₂ ∧ ENNReal.ofReal t₂ < T := by
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs₂T
    refine ⟨c, by exact_mod_cast hc1, ?_⟩
    rw [ENNReal.ofReal_coe_nnreal]; exact hc2
  have hW := continuous_frozenDrive_of_lt hw ht₂T
  have hW0 : frozenDrive w t₂ 0 = 0 := by
    rw [frozenDrive_zero (s₂.coe_nonneg.trans ht₂.le), hw0]
  have hne := fwdHull_ne_of_lt hW hW0 s₁.coe_nonneg (show (s₁ : ℝ) < s₂ from hs12)
  rw [← fwdHull_eq_of_eqOn s₁.coe_nonneg ((show (s₁ : ℝ) < s₂ from hs12).trans ht₂)
      fun r hr => (frozenDrive_eq hr).symm,
    ← fwdHull_eq_of_eqOn s₂.coe_nonneg ht₂ fun r hr => (frozenDrive_eq hr).symm] at hne
  exact hne (le_antisymm hge hle)

end Topo

/-! ### After the swallow: a half-ball around the mark is inside the hull -/

section Swallow

variable {w v0 v1 : ℝ → ℝ}

/-- **The swallowed half-ball.** If the two-mark data hold on every `[0, T]`, `T < τ`, with budget `≤ C`, and the gap
to the mark tends to `0` at `τ`, then every `z ∈ ℍ` with `‖z − 1‖ e^{C/2} < 1/2` is swallowed by time `τ`. -/
theorem mem_fwdHull_of_tendsto {τ C : ℝ} (hτ : 0 < τ) (hpath : ∀ T, 0 ≤ T → T < τ → IsSeedMarkPath w v0 v1 T)
    (hC : ∀ T, 0 ≤ T → T < τ → ∫ s in (0 : ℝ)..T, budget w v0 v1 s ≤ C)
    (hlim : Tendsto (fun s => v1 s - w s) (𝓝[<] τ) (𝓝 0)) {z : ℂ} (hzH : 0 < z.im)
    (hz : ‖z - 1‖ * Real.exp (C / 2) < 1 / 2) : z ∈ fwdHull w τ := by
  by_contra hzK
  obtain ⟨v, hv⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hτ.le hzH hzK
  have hbound : ∀ T ∈ Ico 0 τ, ‖v T‖ ≤ 3 / 2 * (v1 T - w T) := by
    intro T hT
    have hp := hpath T hT.1 hT.2
    have hvT := QuantumZipper.isForwardSol_restrict hv hT.1 hT.2.le
    have hlt := hp.norm_sub_gapC_lt (hC T hT.1 hT.2) hz ⟨hT.1, le_rfl⟩ hvT T ⟨hT.1, le_rfl⟩
    have he := hp.span_le_gap T ⟨hT.1, le_rfl⟩
    have hg := hp.gap_pos T ⟨hT.1, le_rfl⟩
    have h1 : ‖(((v1 T - w T : ℝ)) : ℂ)‖ = v1 T - w T := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
    have h2 := norm_le_insert' (v T) (((v1 T - w T : ℝ)) : ℂ)
    linarith [norm_sub_rev (v T) (((v1 T - w T : ℝ)) : ℂ)]
  -- `v T → 0` as `T ↑ τ`, and `v T → v τ`
  have hlim0 : Tendsto (fun T => ‖v T‖) (𝓝[<] τ) (𝓝 0) := by
    have hup : Tendsto (fun T => 3 / 2 * (v1 T - w T)) (𝓝[<] τ) (𝓝 0) := by
      simpa using hlim.const_mul (3 / 2)
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hup
    filter_upwards [Ioo_mem_nhdsLT hτ] with T hT
    exact hbound T ⟨hT.1.le, hT.2⟩
  have hcontv : Tendsto v (𝓝[<] τ) (𝓝 (v τ)) := by
    have := (hv.1 τ ⟨hτ.le, le_rfl⟩).mono_left (nhdsWithin_mono τ Ioo_subset_Icc_self)
    rwa [nhdsWithin_Ioo_eq_nhdsLT hτ] at this
  have hlimv : Tendsto (fun T => ‖v T‖) (𝓝[<] τ) (𝓝 ‖v τ‖) := hcontv.norm
  have h0 : ‖v τ‖ = 0 := tendsto_nhds_unique hlimv hlim0
  exact (hv.2 τ ⟨hτ.le, le_rfl⟩).1 (norm_eq_zero.1 h0)

end Swallow

/-! ### The two-mark word along one path -/

section Path

variable {r ρ : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ} {v : Fin 2 → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The life before the swallow of the mark: `s < ζ` and the mark has not met the driver on `[0, s]`. -/
def IsMarkLife (w : ℝ≥0 → ℝ) (v1 : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (s : ℝ≥0) : Prop :=
  (s : ℝ≥0∞) < ζ ∧ ∀ u ≤ s, w u < v1 u

/-- The budget of the two-mark path read on `ℝ`. -/
def pathBudget (w : ℝ≥0 → ℝ) (v : Fin 2 → ℝ≥0 → ℝ) (x : ℝ) : ℝ :=
  budget (fun x : ℝ => w x.toNNReal) (fun x : ℝ => v 0 x.toNNReal) (fun x : ℝ => v 1 x.toNNReal) x

theorem lt_of_toNNReal {T₂ : ℝ} (hT₂ : ENNReal.ofReal T₂ < ζ) {s : ℝ} (hs : s ≤ T₂) :
    (s.toNNReal : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hs)) hT₂

/-- **The pathwise data on `[0, T]`** from the force-point conditions of the two-mark word, with the driver frozen
after a time `T₂ ∈ [T, ζ)`. -/
theorem isSeedMarkPath_of_isForcePath (hF : Sec2.IsForcePath ![] ![0, 1] ![] ![r, ρ] w vL v ζ) {T T₂ : ℝ}
    (hT : 0 ≤ T) (hTT₂ : T ≤ T₂) (hT₂ : ENNReal.ofReal T₂ < ζ)
    (hlife : ∀ s ∈ Icc 0 T, w s.toNNReal < v 1 s.toNNReal) :
    IsSeedMarkPath (frozenDrive w T₂) (fun s => v 0 s.toNNReal) (fun s => v 1 s.toNNReal) T := by
  have hζ : ∀ s ∈ Icc 0 T, (s.toNNReal : ℝ≥0∞) < ζ := fun s hs => lt_of_toNNReal hT₂ (hs.2.trans hTT₂)
  have hfr : ∀ s ∈ Icc 0 T, frozenDrive w T₂ s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans hTT₂⟩
  have hcomp : ∀ i, ContinuousOn (fun s : ℝ => v i s.toNNReal) (Icc 0 T) := fun i =>
    (hF.continuousOn_vR i).comp continuous_real_toNNReal.continuousOn fun s hs => hζ s hs
  have hint : ∀ i, ∀ t ∈ Icc 0 T, v i t.toNNReal = (![0, 1] : Fin 2 → ℝ) i +
      ∫ s in (0 : ℝ)..t, 2 / (v i s.toNNReal - frozenDrive w T₂ s) := by
    intro i t ht
    have h := hF.vR_eq (hζ t ht) i
    rw [Real.coe_toNNReal t ht.1] at h
    rw [h]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [hfr s ⟨hs.1, hs.2.trans ht.2⟩]
  refine ⟨hT, continuous_frozenDrive_of_lt hF.continuousOn_w hT₂, ?_, hcomp 0, hcomp 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frozenDrive_zero (hT.trans hTT₂), hF.w_zero]
  · intro t ht
    rw [hfr t ht]
    exact hF.w_le_vR (hζ t ht) 0
  · intro t ht
    exact hF.monotone_vR (hζ t ht) (show (0 : Fin 2) ≤ 1 by decide)
  · intro t ht
    rw [hfr t ht]
    exact hlife t ht
  · intro t ht
    simpa using hint 0 t ht
  · intro t ht
    simpa using hint 1 t ht
  · have h := (hF.integrable_gapR (t := T.toNNReal) (hζ T ⟨hT, le_rfl⟩) 0).neg
    rw [Real.coe_toNNReal T hT] at h
    refine h.congr fun s hs => ?_
    rw [uIoc_of_le hT] at hs
    simp only [Pi.neg_apply, hfr s ⟨hs.1.le, hs.2⟩]
    rw [← inv_neg, neg_sub]
  · have h := hF.volume_collisionR 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with s hs hsI
    rw [hfr s hsI]
    intro heq
    exact hs ⟨hsI.1, hζ s hsI, heq.symm⟩

theorem exists_real_gt_lt {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) : ∃ T₂ : ℝ, (s : ℝ) < T₂ ∧ ENNReal.ofReal T₂ < ζ := by
  obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  exact ⟨c, by exact_mod_cast hc1, by rw [ENNReal.ofReal_coe_nnreal]; exact hc2⟩

theorem integral_budget_frozen {T T₂ : ℝ} (hT : 0 ≤ T) (hTT₂ : T ≤ T₂) :
    ∫ x in (0 : ℝ)..T, budget (frozenDrive w T₂) (fun x : ℝ => v 0 x.toNNReal) (fun x : ℝ => v 1 x.toNNReal) x =
      ∫ x in (0 : ℝ)..T, pathBudget w v x := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hT] at hx
  simp only [pathBudget, budget, frozenDrive_eq (show x ∈ Icc 0 T₂ from ⟨hx.1, hx.2.trans hTT₂⟩)]

/-- **No hull before the swallow meets the ball** `B(1, e^{−C/2}/2)`. -/
theorem ball_inter_fwdHull_eq_empty (hF : Sec2.IsForcePath ![] ![0, 1] ![] ![r, ρ] w vL v ζ) {C : ℝ}
    (hC : ∀ s : ℝ≥0, IsMarkLife w (v 1) ζ s → ∫ x in (0 : ℝ)..s, pathBudget w v x ≤ C) {s : ℝ≥0}
    (hs : IsMarkLife w (v 1) ζ s) :
    Metric.ball (1 : ℂ) (Real.exp (-C / 2) / 2) ∩ fwdHull (fun x : ℝ => w x.toNNReal) s = ∅ := by
  obtain ⟨T₂, hsT₂, hT₂⟩ := exists_real_gt_lt hs.1
  have hpath := isSeedMarkPath_of_isForcePath hF s.coe_nonneg hsT₂.le hT₂ fun x hx =>
    hs.2 x.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx.1]; exact hx.2)
  have hCb : ∫ x in (0 : ℝ)..s, budget (frozenDrive w T₂) (fun x : ℝ => v 0 x.toNNReal)
      (fun x : ℝ => v 1 x.toNNReal) x ≤ C := by
    rw [integral_budget_frozen s.coe_nonneg hsT₂.le]; exact hC s hs
  refine eq_empty_of_forall_notMem fun z ⟨hzB, hzK⟩ => ?_
  rw [fwdHull_eq_of_eqOn (W' := frozenDrive w T₂) s.coe_nonneg hsT₂ fun x hx => (frozenDrive_eq hx).symm] at hzK
  refine hpath.not_mem_fwdHull hCb hzK.1 ?_ hzK
  rw [Metric.mem_ball, dist_eq_norm] at hzB
  have := mul_lt_mul_of_pos_right hzB (Real.exp_pos (C / 2))
  rwa [div_mul_eq_mul_div, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero] at this

/-- **Lemma G11, pathwise.** For one path of the two-mark word (seed group at `0⁺`, the mark at `1`) whose budget is
bounded on the life before the swallow of the mark, every generating trace on `[0, ζ]` avoids the mark, the terminal
value included. -/
theorem trace_ne_one_of_budget (hF : Sec2.IsForcePath ![] ![0, 1] ![] ![r, ρ] w vL v ζ) {C : ℝ}
    (hC : ∀ s : ℝ≥0, IsMarkLife w (v 1) ζ s → ∫ x in (0 : ℝ)..s, pathBudget w v x ≤ C) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ζ η) : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η t ≠ 1 := by
  intro t ht hηt
  rcases eq_zero_or_pos t with rfl | ht0
  · rw [hη.1] at hηt; exact zero_ne_one hηt
  set U : Set ℂ := Metric.ball (1 : ℂ) (Real.exp (-C / 2) / 2) with hU
  have hηU : η t ∈ U := by rw [hηt]; exact Metric.mem_ball_self (by positivity)
  have hw := hF.continuousOn_w
  have hw0 := hF.w_zero
  have hopen : IsOpen {u : ℝ≥0 | (u : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  by_cases hall : ∀ s < t, IsMarkLife w (v 1) ζ s
  · -- before (or at) the first swallow: no hull meets `U`
    refine false_of_hull_stable hη hw hw0 ht0 ht Metric.isOpen_ball hηU (ε := t) (by exact_mod_cast ht0)
      fun s₁ s₂ _ _ hs₂ => ?_
    rw [ball_inter_fwdHull_eq_empty hF hC (hall s₂ hs₂)]
    exact empty_subset _
  -- after the first swallow `τ` of the mark: `U ∩ ℍ ⊆ K_τ`
  push Not at hall
  obtain ⟨s₀, hs₀t, hs₀⟩ := hall
  have hs₀ζ : (s₀ : ℝ≥0∞) < ζ := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hs₀t) ht
  have hex : ∃ u ≤ s₀, v 1 u ≤ w u := by
    by_contra hno
    push Not at hno
    exact hs₀ ⟨hs₀ζ, fun u hu => hno u hu⟩
  set S : Set ℝ≥0 := Iic s₀ ∩ (fun u => v 1 u - w u) ⁻¹' Iic 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨u, hu, hle⟩ := hex
    exact ⟨u, hu, by simp only [mem_preimage, mem_Iic]; linarith⟩
  have hIic : Iic s₀ ⊆ {u : ℝ≥0 | (u : ℝ≥0∞) < ζ} := fun u hu =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) hs₀ζ
  have hScl : IsClosed S :=
    (((hF.continuousOn_vR 1).sub hw).mono hIic).preimage_isClosed_of_isClosed isClosed_Iic isClosed_Iic
  set τ := sInf S with hτ
  have hτS : τ ∈ S := hScl.csInf_mem hSne (OrderBot.bddBelow S)
  have hτs₀ : τ ≤ s₀ := hτS.1
  have hτζ : (τ : ℝ≥0∞) < ζ := hIic hτs₀
  have hτeq : v 1 τ = w τ := by
    have h1 : v 1 τ - w τ ≤ 0 := hτS.2
    linarith [hF.w_le_vR hτζ 1]
  have hlifeτ : ∀ u < τ, IsMarkLife w (v 1) ζ u := by
    intro u hu
    refine ⟨lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hu) (ENNReal.coe_le_coe.2 hτs₀) |>.trans hs₀ζ, fun u' hu' => ?_⟩
    by_contra hle
    rw [not_lt] at hle
    have hu'S : u' ∈ S := ⟨hu'.trans (hu.le.trans hτs₀), by simp only [mem_preimage, mem_Iic]; linarith⟩
    exact absurd (csInf_le (OrderBot.bddBelow S) hu'S) (not_le.2 (lt_of_le_of_lt hu' hu))
  have hτ0 : 0 < τ := by
    rcases eq_zero_or_pos τ with h0 | h0
    · rw [h0, hF.vR_zero 1, hw0] at hτeq; simp at hτeq
    · exact h0
  obtain ⟨T₂, hτT₂, hT₂⟩ := exists_real_gt_lt hτζ
  have hswallow : U ∩ H ⊆ fwdHull (fun x : ℝ => w x.toNNReal) τ := by
    rintro z ⟨hzU, hzH⟩
    rw [fwdHull_eq_of_eqOn (W' := frozenDrive w T₂) τ.coe_nonneg hτT₂ fun x hx => (frozenDrive_eq hx).symm]
    have hlifeR : ∀ T : ℝ, 0 ≤ T → T < τ → ∀ x ∈ Icc 0 T, w x.toNNReal < v 1 x.toNNReal := by
      intro T hT hTτ x hx
      have hxτ : x.toNNReal < τ := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal x hx.1]; exact lt_of_le_of_lt hx.2 hTτ
      exact (hlifeτ x.toNNReal hxτ).2 _ le_rfl
    refine mem_fwdHull_of_tendsto (C := C) (by exact_mod_cast hτ0)
      (fun T hT hTτ => isSeedMarkPath_of_isForcePath hF hT (hTτ.le.trans hτT₂.le) hT₂ (hlifeR T hT hTτ))
      (fun T hT hTτ => ?_) ?_ hzH ?_
    · rw [integral_budget_frozen hT (hTτ.le.trans hτT₂.le)]
      have hTn : T.toNNReal < τ := by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal T hT]; exact hTτ
      have := hC T.toNNReal (hlifeτ _ hTn)
      rwa [Real.coe_toNNReal T hT] at this
    · have hcont : ContinuousAt (fun x : ℝ => v 1 x.toNNReal - frozenDrive w T₂ x) τ := by
        refine ContinuousAt.sub ?_ (continuous_frozenDrive_of_lt hw hT₂).continuousAt
        refine ContinuousAt.comp (f := fun x : ℝ => x.toNNReal) ?_ continuous_real_toNNReal.continuousAt
        rw [Real.toNNReal_coe]
        exact (hF.continuousOn_vR 1).continuousAt (hopen.mem_nhds hτζ)
      have h0 : v 1 (τ : ℝ).toNNReal - frozenDrive w T₂ τ = 0 := by
        rw [Real.toNNReal_coe, frozenDrive_eq ⟨τ.coe_nonneg, hτT₂.le⟩, Real.toNNReal_coe, hτeq, sub_self]
      have := hcont.tendsto
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · rw [Metric.mem_ball, dist_eq_norm] at hzU
      have := mul_lt_mul_of_pos_right hzU (Real.exp_pos (C / 2))
      rwa [div_mul_eq_mul_div, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero] at this
  have hτt : τ < t := lt_of_le_of_lt hτs₀ hs₀t
  refine false_of_hull_stable hη hw hw0 ht0 ht Metric.isOpen_ball hηU (ε := (t : ℝ) - τ)
    (by rw [sub_pos]; exact_mod_cast hτt) fun s₁ s₂ hs₁ _ _ => ?_
  have hτs₁ : (τ : ℝ) ≤ s₁ := by linarith
  intro z ⟨hzU, hzK⟩
  exact (QuantumZipper.fwdHull_mono (W := fun x : ℝ => w x.toNNReal)).1 hτs₁ (hswallow ⟨hzU, hzK.1⟩)

end Path


end G11

end Supp7

end InteractingSLE
