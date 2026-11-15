/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Ode
import InteractingSLE.Spec.Supplement.G11Trace

/-!
# Lemma G12, pathwise part: a finite budget keeps the trace off a mark of any word

Packet PROVE-G12. Supplement §7.9, Lemma G12 (p. 504). This is `G11Trace.lean` (PROVE-G11-G4) for an arbitrary force
word: the inner force point is any right mark `i₀` (the seed group, or the innermost mark), the target is a right mark
`j₀` with `xR i₀ < xR j₀`, and the budget is G11's `β = 4e/(u² o) + 4e/u³` for the pair `(V^{i₀}, V^{j₀})`.

* `isPairPath_of_isForcePath`: the pathwise data of the pair on `[0, T]` before the mark `j₀` is swallowed;
* `mem_fwdHull_of_tendsto`: the half-ball `B(x_{j₀}, (x_{j₀} − x_{i₀}) e^{−C/2}/2)` is swallowed when the mark is;
* `trace_ne_of_budget_lt` (**per time**): if the budget is at most `C` on the life of the mark before a time
  `t ≤ ζ`, the trace is not at the mark at time `t`;
* `trace_ne_of_budget`: the uniform form (every `t ≤ ζ`, the terminal value included);
* `trace_ne_of_isMarkLife`: the trace is never at the mark while it is alive (no budget needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Supp7

namespace G12

open G11 (spanRate budget IsMarkLife false_of_hull_stable exists_real_gt_lt lt_of_toNNReal)

/-! ### The swallowed half-ball -/

section Swallow

variable {w v0 v1 : ℝ → ℝ} {a b : ℝ}

/-- **The swallowed half-ball.** If the pair data hold on every `[0, T]`, `T < τ`, with budget `≤ C`, and the gap
to the mark tends to `0` at `τ`, then every `z ∈ ℍ` with `‖z − b‖ e^{C/2} < (b − a)/2` is swallowed by time `τ`. -/
theorem mem_fwdHull_of_tendsto {τ C : ℝ} (hτ : 0 < τ) (hpath : ∀ T, 0 ≤ T → T < τ → IsPairPath w v0 v1 a b T)
    (hC : ∀ T, 0 ≤ T → T < τ → ∫ s in (0 : ℝ)..T, budget w v0 v1 s ≤ C)
    (hlim : Tendsto (fun s => v1 s - w s) (𝓝[<] τ) (𝓝 0)) {z : ℂ} (hzH : 0 < z.im)
    (hz : ‖z - b‖ * Real.exp (C / 2) < (b - a) / 2) : z ∈ fwdHull w τ := by
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

/-! ### Two right marks of a word along one path -/

section Path

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {i₀ j₀ : Fin nR}

/-- The budget of the pair `(V^{i₀}, V^{j₀})` read on `ℝ`. -/
def pairBudget (w : ℝ≥0 → ℝ) (v0 v1 : ℝ≥0 → ℝ) (x : ℝ) : ℝ :=
  budget (fun x : ℝ => w x.toNNReal) (fun x : ℝ => v0 x.toNNReal) (fun x : ℝ => v1 x.toNNReal) x

/-- **The pathwise data of the pair on `[0, T]`** from the force-point conditions, with the driver frozen after a
time `T₂ ∈ [T, ζ)`. -/
theorem isPairPath_of_isForcePath (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hij : i₀ ≤ j₀)
    (hx : xR i₀ < xR j₀) {T T₂ : ℝ} (hT : 0 ≤ T) (hTT₂ : T ≤ T₂) (hT₂ : ENNReal.ofReal T₂ < ζ)
    (hlife : ∀ s ∈ Icc 0 T, w s.toNNReal < vR j₀ s.toNNReal) :
    IsPairPath (frozenDrive w T₂) (fun s => vR i₀ s.toNNReal) (fun s => vR j₀ s.toNNReal) (xR i₀) (xR j₀) T := by
  have hζ : ∀ s ∈ Icc 0 T, (s.toNNReal : ℝ≥0∞) < ζ := fun s hs => lt_of_toNNReal hT₂ (hs.2.trans hTT₂)
  have hfr : ∀ s ∈ Icc 0 T, frozenDrive w T₂ s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans hTT₂⟩
  have hcomp : ∀ i, ContinuousOn (fun s : ℝ => vR i s.toNNReal) (Icc 0 T) := fun i =>
    (hF.continuousOn_vR i).comp continuous_real_toNNReal.continuousOn fun s hs => hζ s hs
  have hint : ∀ i, ∀ t ∈ Icc 0 T, vR i t.toNNReal = xR i +
      ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - frozenDrive w T₂ s) := by
    intro i t ht
    have h := hF.vR_eq (hζ t ht) i
    rw [Real.coe_toNNReal t ht.1] at h
    rw [h]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    simp only [hfr s ⟨hs.1, hs.2.trans ht.2⟩]
  refine ⟨hT, hx, continuous_frozenDrive_of_lt hF.continuousOn_w hT₂, ?_, hcomp i₀, hcomp j₀, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [frozenDrive_zero (hT.trans hTT₂), hF.w_zero]
  · intro t ht
    rw [hfr t ht]
    exact hF.w_le_vR (hζ t ht) i₀
  · intro t ht
    exact hF.monotone_vR (hζ t ht) hij
  · intro t ht
    rw [hfr t ht]
    exact hlife t ht
  · exact hint i₀
  · exact hint j₀
  · have h := (hF.integrable_gapR (t := T.toNNReal) (hζ T ⟨hT, le_rfl⟩) i₀).neg
    rw [Real.coe_toNNReal T hT] at h
    refine h.congr fun s hs => ?_
    rw [uIoc_of_le hT] at hs
    simp only [Pi.neg_apply, hfr s ⟨hs.1.le, hs.2⟩]
    rw [← inv_neg, neg_sub]
  · have h := hF.volume_collisionR i₀
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with s hs hsI
    rw [hfr s hsI]
    intro heq
    exact hs ⟨hsI.1, hζ s hsI, heq.symm⟩

theorem integral_pairBudget_frozen {T T₂ : ℝ} (hT : 0 ≤ T) (hTT₂ : T ≤ T₂) :
    ∫ x in (0 : ℝ)..T, budget (frozenDrive w T₂) (fun x : ℝ => vR i₀ x.toNNReal)
      (fun x : ℝ => vR j₀ x.toNNReal) x = ∫ x in (0 : ℝ)..T, pairBudget w (vR i₀) (vR j₀) x := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hT] at hx
  simp only [pairBudget, budget, frozenDrive_eq (show x ∈ Icc 0 T₂ from ⟨hx.1, hx.2.trans hTT₂⟩)]

/-- **No hull before the swallow meets the ball** `B(x_{j₀}, (x_{j₀} − x_{i₀}) e^{−C/2}/2)`. -/
theorem ball_inter_fwdHull_eq_empty (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hij : i₀ ≤ j₀)
    (hx : xR i₀ < xR j₀) {C : ℝ} {s : ℝ≥0} (hs : IsMarkLife w (vR j₀) ζ s)
    (hC : ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ C) :
    Metric.ball (xR j₀ : ℂ) ((xR j₀ - xR i₀) * Real.exp (-C / 2) / 2) ∩
      fwdHull (fun x : ℝ => w x.toNNReal) s = ∅ := by
  obtain ⟨T₂, hsT₂, hT₂⟩ := exists_real_gt_lt hs.1
  have hpath := isPairPath_of_isForcePath hF hij hx s.coe_nonneg hsT₂.le hT₂ fun x hx =>
    hs.2 x.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx.1]; exact hx.2)
  have hCb : ∫ x in (0 : ℝ)..s, budget (frozenDrive w T₂) (fun x : ℝ => vR i₀ x.toNNReal)
      (fun x : ℝ => vR j₀ x.toNNReal) x ≤ C := by
    rw [integral_pairBudget_frozen s.coe_nonneg hsT₂.le]; exact hC
  refine eq_empty_of_forall_notMem fun z ⟨hzB, hzK⟩ => ?_
  rw [fwdHull_eq_of_eqOn (W' := frozenDrive w T₂) s.coe_nonneg hsT₂ fun x hx => (frozenDrive_eq hx).symm] at hzK
  refine hpath.not_mem_fwdHull hCb hzK.1 ?_ hzK
  rw [Metric.mem_ball, dist_eq_norm] at hzB
  have := mul_lt_mul_of_pos_right hzB (Real.exp_pos (C / 2))
  rwa [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one] at this

/-- **Lemma G12, pathwise, at one time.** If the budget of the pair is at most `C` on the life of the mark `j₀`
before a time `t ≤ ζ`, then the trace is not at the mark at time `t`. -/
theorem trace_ne_of_budget_lt (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hij : i₀ ≤ j₀)
    (hx0 : 0 ≤ xR i₀) (hx : xR i₀ < xR j₀) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ ζ) {C : ℝ} (hC : ∀ s : ℝ≥0, IsMarkLife w (vR j₀) ζ s → s < t →
      ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ C) : η t ≠ xR j₀ := by
  intro hηt
  have hxj : 0 < xR j₀ := lt_of_le_of_lt hx0 hx
  rcases eq_zero_or_pos t with rfl | ht0
  · rw [hη.1] at hηt
    exact hxj.ne (by exact_mod_cast hηt)
  have hd : 0 < xR j₀ - xR i₀ := sub_pos.2 hx
  set U : Set ℂ := Metric.ball (xR j₀ : ℂ) ((xR j₀ - xR i₀) * Real.exp (-C / 2) / 2) with hU
  have hηU : η t ∈ U := by rw [hηt]; exact Metric.mem_ball_self (by positivity)
  have hw := hF.continuousOn_w
  have hw0 := hF.w_zero
  have hopen : IsOpen {u : ℝ≥0 | (u : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  by_cases hall : ∀ s < t, IsMarkLife w (vR j₀) ζ s
  · refine false_of_hull_stable hη hw hw0 ht0 ht Metric.isOpen_ball hηU (ε := t) (by exact_mod_cast ht0)
      fun s₁ s₂ _ _ hs₂ => ?_
    rw [ball_inter_fwdHull_eq_empty hF hij hx (hall s₂ hs₂) (hC s₂ (hall s₂ hs₂) hs₂)]
    exact empty_subset _
  rw [not_forall] at hall
  obtain ⟨s₀, hall⟩ := hall
  rw [Classical.not_imp] at hall
  obtain ⟨hs₀t, hs₀⟩ := hall
  have hs₀ζ : (s₀ : ℝ≥0∞) < ζ := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hs₀t) ht
  have hex : ∃ u ≤ s₀, vR j₀ u ≤ w u := by
    by_contra hno
    push Not at hno
    exact hs₀ ⟨hs₀ζ, fun u hu => hno u hu⟩
  set S : Set ℝ≥0 := Iic s₀ ∩ (fun u => vR j₀ u - w u) ⁻¹' Iic 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨u, hu, hle⟩ := hex
    exact ⟨u, hu, by simp only [mem_preimage, mem_Iic]; linarith⟩
  have hIic : Iic s₀ ⊆ {u : ℝ≥0 | (u : ℝ≥0∞) < ζ} := fun u hu =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) hs₀ζ
  have hScl : IsClosed S :=
    (((hF.continuousOn_vR j₀).sub hw).mono hIic).preimage_isClosed_of_isClosed isClosed_Iic isClosed_Iic
  set τ := sInf S with hτ
  have hτS : τ ∈ S := hScl.csInf_mem hSne (OrderBot.bddBelow S)
  have hτs₀ : τ ≤ s₀ := hτS.1
  have hτζ : (τ : ℝ≥0∞) < ζ := hIic hτs₀
  have hτeq : vR j₀ τ = w τ := by
    have h1 : vR j₀ τ - w τ ≤ 0 := hτS.2
    linarith [hF.w_le_vR hτζ j₀]
  have hlifeτ : ∀ u < τ, IsMarkLife w (vR j₀) ζ u := by
    intro u hu
    refine ⟨lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hu) (ENNReal.coe_le_coe.2 hτs₀) |>.trans hs₀ζ, fun u' hu' => ?_⟩
    by_contra hle
    rw [not_lt] at hle
    have hu'S : u' ∈ S := ⟨hu'.trans (hu.le.trans hτs₀), by simp only [mem_preimage, mem_Iic]; linarith⟩
    exact absurd (csInf_le (OrderBot.bddBelow S) hu'S) (not_le.2 (lt_of_le_of_lt hu' hu))
  have hτ0 : 0 < τ := by
    rcases eq_zero_or_pos τ with h0 | h0
    · rw [h0, hF.vR_zero j₀, hw0] at hτeq; exact absurd hτeq hxj.ne'
    · exact h0
  have hτt : τ < t := lt_of_le_of_lt hτs₀ hs₀t
  obtain ⟨T₂, hτT₂, hT₂⟩ := exists_real_gt_lt hτζ
  have hswallow : U ∩ H ⊆ fwdHull (fun x : ℝ => w x.toNNReal) τ := by
    rintro z ⟨hzU, hzH⟩
    rw [fwdHull_eq_of_eqOn (W' := frozenDrive w T₂) τ.coe_nonneg hτT₂ fun x hx => (frozenDrive_eq hx).symm]
    have hlifeR : ∀ T : ℝ, 0 ≤ T → T < τ → ∀ x ∈ Icc 0 T, w x.toNNReal < vR j₀ x.toNNReal := by
      intro T hT hTτ x hx
      have hxτ : x.toNNReal < τ := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal x hx.1]; exact lt_of_le_of_lt hx.2 hTτ
      exact (hlifeτ x.toNNReal hxτ).2 _ le_rfl
    refine mem_fwdHull_of_tendsto (C := C) (by exact_mod_cast hτ0)
      (fun T hT hTτ => isPairPath_of_isForcePath hF hij hx hT (hTτ.le.trans hτT₂.le) hT₂ (hlifeR T hT hTτ))
      (fun T hT hTτ => ?_) ?_ hzH ?_
    · rw [integral_pairBudget_frozen hT (hTτ.le.trans hτT₂.le)]
      have hTn : T.toNNReal < τ := by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal T hT]; exact hTτ
      have := hC T.toNNReal (hlifeτ _ hTn) (hTn.trans hτt)
      rwa [Real.coe_toNNReal T hT] at this
    · have hcont : ContinuousAt (fun x : ℝ => vR j₀ x.toNNReal - frozenDrive w T₂ x) τ := by
        refine ContinuousAt.sub ?_ (continuous_frozenDrive_of_lt hw hT₂).continuousAt
        refine ContinuousAt.comp (f := fun x : ℝ => x.toNNReal) ?_ continuous_real_toNNReal.continuousAt
        rw [Real.toNNReal_coe]
        exact (hF.continuousOn_vR j₀).continuousAt (hopen.mem_nhds hτζ)
      have h0 : vR j₀ (τ : ℝ).toNNReal - frozenDrive w T₂ τ = 0 := by
        rw [Real.toNNReal_coe, frozenDrive_eq ⟨τ.coe_nonneg, hτT₂.le⟩, Real.toNNReal_coe, hτeq, sub_self]
      have := hcont.tendsto
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    · rw [Metric.mem_ball, dist_eq_norm] at hzU
      have := mul_lt_mul_of_pos_right hzU (Real.exp_pos (C / 2))
      rwa [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero,
        mul_one] at this
  refine false_of_hull_stable hη hw hw0 ht0 ht Metric.isOpen_ball hηU (ε := (t : ℝ) - τ)
    (by rw [sub_pos]; exact_mod_cast hτt) fun s₁ s₂ hs₁ _ _ => ?_
  have hτs₁ : (τ : ℝ) ≤ s₁ := by linarith
  intro z ⟨hzU, hzK⟩
  exact (QuantumZipper.fwdHull_mono (W := fun x : ℝ => w x.toNNReal)).1 hτs₁ (hswallow ⟨hzU, hzK.1⟩)

/-- **Lemma G12, pathwise.** If the budget of the pair is bounded on the whole life of the mark, the trace avoids
the mark on `[0, ζ]`, the terminal value included. -/
theorem trace_ne_of_budget (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hij : i₀ ≤ j₀)
    (hx0 : 0 ≤ xR i₀) (hx : xR i₀ < xR j₀) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {C : ℝ}
    (hC : ∀ s : ℝ≥0, IsMarkLife w (vR j₀) ζ s → ∫ x in (0 : ℝ)..s, pairBudget w (vR i₀) (vR j₀) x ≤ C) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η t ≠ xR j₀ := fun _ ht =>
  trace_ne_of_budget_lt hF hij hx0 hx hη ht fun s hs _ => hC s hs

theorem pairBudget_nonneg (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hij : i₀ ≤ j₀) {s : ℝ≥0}
    (hs : IsMarkLife w (vR j₀) ζ s) {x : ℝ} (hx : x ∈ Icc 0 (s : ℝ)) :
    0 ≤ pairBudget w (vR i₀) (vR j₀) x := by
  have hxs : x.toNNReal ≤ s := by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx.1]; exact hx.2
  have hxζ : (x.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hxs) hs.1
  have hu : 0 < vR j₀ x.toNNReal - w x.toNNReal := sub_pos.2 (hs.2 _ hxs)
  have ho : 0 ≤ vR i₀ x.toNNReal - w x.toNNReal := sub_nonneg.2 (hF.w_le_vR hxζ i₀)
  have he : 0 ≤ vR j₀ x.toNNReal - vR i₀ x.toNNReal := sub_nonneg.2 (hF.monotone_vR hxζ hij)
  simp only [pairBudget, budget]
  positivity

/-- **While the mark is alive, the trace is not at it** (no budget needed: on `[0, t]` the budget is finite). -/
theorem trace_ne_of_isMarkLife (hF : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hij : i₀ ≤ j₀)
    (hx0 : 0 ≤ xR i₀) (hx : xR i₀ < xR j₀) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {t : ℝ≥0}
    (ht : IsMarkLife w (vR j₀) ζ t) : η t ≠ xR j₀ := by
  obtain ⟨T₂, htT₂, hT₂⟩ := exists_real_gt_lt ht.1
  have hpath := isPairPath_of_isForcePath hF hij hx t.coe_nonneg htT₂.le hT₂ fun x hx =>
    ht.2 x.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal x hx.1]; exact hx.2)
  have hI : IntervalIntegrable (pairBudget w (vR i₀) (vR j₀)) volume 0 t := by
    refine hpath.intervalIntegrable_budget.congr fun x hx => ?_
    rw [uIoc_of_le t.coe_nonneg] at hx
    simp only [pairBudget, budget, frozenDrive_eq (show x ∈ Icc 0 T₂ from ⟨hx.1.le, hx.2.trans htT₂.le⟩)]
  refine trace_ne_of_budget_lt hF hij hx0 hx hη ht.1.le (C := ∫ x in (0 : ℝ)..t,
    pairBudget w (vR i₀) (vR j₀) x) fun s hs hst => ?_
  refine intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg (by exact_mod_cast hst.le) ?_ hI
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun x hx => pairBudget_nonneg hF hij ht ⟨hx.1.le, hx.2⟩

end Path

end G12

end Supp7

end InteractingSLE
