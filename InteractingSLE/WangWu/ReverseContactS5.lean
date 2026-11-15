/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactBdryGlue

/-!
# Step (S5) of the contact step: contact at the reverse tip from a transient continuation of the image chain

Packet PROVE-WW-B15. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition
4.18 (text dump L1629–1641):

> "The trace lemma and Corollary 4.13 imply that its first boundary limit is precisely `β(s)`. At a finite transformed
> time the nonboundary trace lemma excludes contact with a finite real point, while nonexplosion and the bounded-driver
> hull estimate exclude arrival at infinity. An interior endpoint could be continued by the original continuous trace.
> Thus the transformed exploration cannot end before its limit at the new target. The inverse prime-end map is
> continuous at the slit tip, so the original forward trace approaches `β(s)`. This occurs at a finite original forward
> time: otherwise its already established properness would give limit equal to the original target instead. Continuity
> gives first contact exactly at `β(s)`."

In the chart `Ψ = revChart W_β s` of `ℍ \ G`, `G = R(β((0, s]))`, the image `Ψ ∘ α` of the forward line before its first
contact with `G` is, after the capacity clock `σ`, the beginning of the image chain. Step (S4) identifies the image chain's
driver as `SLE₄(r_L, −r_L; r_R, −r_R)` killed at the end of the image; continued after that time (by an independent
Brownian motion), its trace `X` is a simple trace in `ℍ` tending to `∞` (Lemma 4.12 and transience, nonnegative cumulative
weights `r, 0`). This file proves everything after that:

* **`tendsto_revChartInv_tip`**: `Ψ⁻¹(ζ) → R(β(s))` as `ζ → ∞` in `ℍ` ("the inverse prime-end map is continuous at the slit
  tip");
* **`exists_tendsto_of_continuation`**: along increasing pre-contact times `t_n`, the forward points `α(t_n)` converge to a
  point of `ℍ \ G` (if `σ(t_n)` stays bounded: the continuation is at an interior point) or to the tip (if `σ(t_n) → ∞`);
* **`mem_arcRange_of_continuation`** (deterministic (S5)): if `X ∘ σ = Ψ ∘ α` at the positive pre-contact times
  (`preContact`; `σ` monotone and positive there), with `X` continuous, in `ℍ` at
  positive times and tending to `∞`, then `α` passes through `R(β(s))`: a forward line that never meets `G` would converge
  to a finite point, contradicting properness; at the first contact time `τ` the limit is `α(τ) ∈ G`, which is not in
  `ℍ \ G`, so it is the tip;
* `ImageContinuationStatement` (**named input**, the output of step (S4)): on the glued space of
  `ReverseTipContactStatement`, for each rational `s > 0`, almost surely there are such `X` and `σ`;
* **`reverseTipContactStatement_of_imageContinuation`**: `ReverseTipContactStatement` from it. A conditional helper; it
  replaces no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open LQGMetric (DistOn TestOn)
open LawUnique

/-! ### The inverse chart at infinity -/

section Tip

variable {W : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ}

/-- **The inverse chart tends to the reverse tip at infinity**: along any filter on which `ζ ∈ ℍ` eventually and
`‖ζ‖ → ∞`, `Ψ⁻¹(ζ) = R(F_s(R(ζ))) → R(β(s))`. -/
theorem tendsto_revChartInv_tip {ι : Type*} {l : Filter ι} {f : ι → ℂ} (hβ : IsLoewnerTrace W β)
    (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) (hβs : β s ≠ 0) (hfH : ∀ᶠ i in l, f i ∈ H)
    (hf : Tendsto (fun i => ‖f i‖) l atTop) :
    Tendsto (fun i => revChartInv W s (f i)) l (𝓝 (negInv (β s))) := by
  have h1 : Tendsto (fun i => negInv (f i)) l (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hfH.mono fun i hi => negInv_mem_H hi⟩
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_negInv]
    exact hf.inv_tendsto_atTop
  have h2 := (hβ.tendsto_fwdMapInv_tip hW hW0 hs).comp h1
  exact (continuousAt_negInv hβs).tendsto.comp h2

end Tip

/-! ### Contact at the tip from a transient continuation -/

section Contact

/-- **The pre-contact times** of a curve `α` with a set `G`: the `t ≥ 0` with `α([0, t]) ∩ G = ∅`. -/
def preContact (α : ℝ → ℂ) (G : Set ℂ) : Set ℝ := {t | 0 ≤ t ∧ ∀ u ∈ Icc 0 t, α u ∉ G}

theorem Icc_subset_preContact {α : ℝ → ℂ} {G : Set ℂ} {t : ℝ} (ht : t ∈ preContact α G) :
    Icc 0 t ⊆ preContact α G := fun _ hu => ⟨hu.1, fun v hv => ht.2 v ⟨hv.1, hv.2.trans hu.2⟩⟩

variable {W : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {α : ℝ → ℂ} {X : ℝ → ℂ} {σ : ℝ → ℝ}

/-- **Along increasing pre-contact times the forward points converge to an interior point or to the tip.** If
`X ∘ σ = Ψ ∘ α` before contact with `G = R(K_s)`, `X` continuous on `[0, ∞)` and in `ℍ` at positive times, `σ`
monotone and positive at positive times, and `‖X‖ → ∞`, then along increasing positive times `t_n` before contact,
`α(t_n)` converges either to some point of `ℍ \ G` or to `R(β(s))`. -/
theorem exists_tendsto_of_continuation (hβ : IsLoewnerTrace W β) (hW : Continuous W) (hW0 : W 0 = 0)
    (hs : 0 ≤ s) (hβs : β s ≠ 0) (hα : IsProperArc α) (hXc : ContinuousOn X (Ici 0))
    (hXH : ∀ u, 0 < u → X u ∈ H) (hXt : Tendsto (fun u => ‖X u‖) atTop atTop) (hσm : MonotoneOn σ (preContact α (negInv '' fwdHull W s)))
    (hσpos : ∀ t ∈ preContact α (negInv '' fwdHull W s), 0 < t → 0 < σ t)
    (hXσ : ∀ t ∈ preContact α (negInv '' fwdHull W s), 0 < t → X (σ t) = revChart W s (α t))
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 < t n) (htm : Monotone t)
    (hpre : ∀ n, ∀ u ∈ Icc 0 (t n), α u ∉ negInv '' fwdHull W s) :
    (∃ p ∈ H \ negInv '' fwdHull W s, Tendsto (fun n => α (t n)) atTop (𝓝 p)) ∨
      Tendsto (fun n => α (t n)) atTop (𝓝 (negInv (β s))) := by
  set G := negInv '' fwdHull W s with hGdef
  set a : ℕ → ℝ := fun n => σ (t n) with ha
  have htpre : ∀ n, t n ∈ preContact α G := fun n => ⟨(ht0 n).le, hpre n⟩
  have ham : Monotone a := fun m n hmn => hσm (htpre m) (htpre n) (htm hmn)
  have ha0 : ∀ n, 0 < a n := fun n => hσpos _ (htpre n) (ht0 n)
  have hαmem : ∀ n, α (t n) ∈ H \ G := fun n =>
    ⟨hα.mem_H _ (ht0 n), hpre n (t n) ⟨(ht0 n).le, le_rfl⟩⟩
  have heq : ∀ n, α (t n) = revChartInv W s (X (a n)) := fun n => by
    rw [ha, hXσ (t n) (htpre n) (ht0 n), revChartInv_revChart hW hW0 hs (hαmem n)]
  by_cases hbdd : BddAbove (range a)
  · -- the clock converges: the continuation is at an interior point
    left
    set L := ⨆ n, a n with hL
    have haL : Tendsto a atTop (𝓝 L) := tendsto_atTop_ciSup ham hbdd
    have hLpos : 0 < L := lt_of_lt_of_le (ha0 0) (le_ciSup hbdd 0)
    have hXL : X L ∈ H := hXH L hLpos
    have hXcont : ContinuousAt X L := hXc.continuousAt (Ici_mem_nhds hLpos)
    have hRcont : ContinuousAt (revChartInv W s) (X L) :=
      (continuousOn_revChartInv hW hW0 hs).continuousAt (QuantumZipper.isOpen_H.mem_nhds hXL)
    refine ⟨revChartInv W s (X L), revChartInv_mem hW hW0 hs hXL, ?_⟩
    have := hRcont.tendsto.comp (hXcont.tendsto.comp haL)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, heq n]
  · -- the clock is unbounded: the continuation tends to `∞`, the forward points to the tip
    right
    have haT : Tendsto a atTop atTop := by
      refine tendsto_atTop_atTop_of_monotone ham fun b => ?_
      by_contra hcon
      push Not at hcon
      exact hbdd ⟨b, by rintro _ ⟨n, rfl⟩; exact (hcon n).le⟩
    have hT := tendsto_revChartInv_tip (l := atTop) (f := fun n => X (a n)) hβ hW hW0 hs hβs
      (Eventually.of_forall fun n => hXH _ (ha0 n)) (hXt.comp haT)
    exact hT.congr fun n => (heq n).symm

/-- **Step (S5) of the contact step, deterministic.** Let `β` be a Loewner trace of `W` with `β(s) ∈ ℍ`, `G = R(K_s)`
closed, `α` a simple proper arc, `X` continuous on `[0, ∞)`, in `ℍ` at positive times, with `‖X‖ → ∞`, and `σ` monotone
with `σ > 0` at positive times. If `X(σ(t)) = Ψ(α(t))` at every time `t` before the first contact of `α` with `G`, then
`α` passes through the reverse tip `R(β(s))`. -/
theorem mem_arcRange_of_continuation (hβ : IsLoewnerTrace W β) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hβs : β s ∈ H) (hG : IsClosed (negInv '' fwdHull W s)) (hα : IsProperArc α) (hXc : ContinuousOn X (Ici 0))
    (hXH : ∀ u, 0 < u → X u ∈ H) (hXt : Tendsto (fun u => ‖X u‖) atTop atTop) (hσm : MonotoneOn σ (preContact α (negInv '' fwdHull W s)))
    (hσpos : ∀ t ∈ preContact α (negInv '' fwdHull W s), 0 < t → 0 < σ t)
    (hXσ : ∀ t ∈ preContact α (negInv '' fwdHull W s), 0 < t → X (σ t) = revChart W s (α t)) :
    negInv (β s) ∈ arcRange α := by
  set G := negInv '' fwdHull W s with hGdef
  have hβ0 : β s ≠ 0 := ne_zero_of_mem_H hβs
  have hGH : G ⊆ H := fun z ⟨w, hw, e⟩ => e ▸ negInv_mem_H hw.1
  have hα0 : α 0 ∉ G := fun h => by
    have := hGH h
    rw [hα.zero] at this
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  have key : ∀ {t : ℕ → ℝ}, (∀ n, 0 < t n) → Monotone t → (∀ n, ∀ u ∈ Icc 0 (t n), α u ∉ G) →
      (∃ p ∈ H \ G, Tendsto (fun n => α (t n)) atTop (𝓝 p)) ∨
        Tendsto (fun n => α (t n)) atTop (𝓝 (negInv (β s))) := fun ht0 htm hpre =>
    exists_tendsto_of_continuation hβ hW hW0 hs hβ0 hα hXc hXH hXt hσm hσpos hXσ ht0 htm hpre
  set C := {t : ℝ | 0 ≤ t ∧ α t ∈ G} with hCdef
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · -- no contact: the forward points at integer times would converge, contradicting properness
    exfalso
    have hnot : ∀ u, 0 ≤ u → α u ∉ G := fun u hu hu' => by
      have : u ∈ C := ⟨hu, hu'⟩
      rw [hCe] at this; exact this
    have ht0 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
    have htm : Monotone fun n : ℕ => (n : ℝ) + 1 := fun m n hmn => by
      simp only; exact_mod_cast Nat.add_le_add_right hmn 1
    have hinf : Tendsto (fun n : ℕ => ‖α ((n : ℝ) + 1)‖) atTop atTop :=
      hα.tendsto.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    rcases key ht0 htm (fun n u hu => hnot u hu.1) with ⟨p, -, hp⟩ | hp
    · exact not_tendsto_nhds_of_tendsto_atTop hinf _ hp.norm
    · exact not_tendsto_nhds_of_tendsto_atTop hinf _ hp.norm
  · -- the first contact time
    have hCc : IsClosed C := by
      have : C = Ici 0 ∩ α ⁻¹' G := by ext t; simp [hCdef, mem_Ici]
      rw [this]
      exact hα.cont.preimage_isClosed_of_isClosed isClosed_Ici hG
    have hCb : BddBelow C := ⟨0, fun t ht => ht.1⟩
    set τ := sInf C with hτ
    have hτC : τ ∈ C := hCc.csInf_mem hCne hCb
    have hτpos : 0 < τ := by
      rcases hτC.1.eq_or_lt with h0 | h0
      · exfalso; rw [← h0] at hτC; exact hα0 hτC.2
      · exact h0
    have hbefore : ∀ u, 0 ≤ u → u < τ → α u ∉ G := fun u hu huτ hu' =>
      absurd (csInf_le hCb ⟨hu, hu'⟩) (not_le.2 huτ)
    -- increasing times `t_n ↑ τ`
    set t : ℕ → ℝ := fun n => τ - τ / 2 * (1 / ((n : ℝ) + 1)) with htdef
    have hinv : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have ht0 : ∀ n, 0 < t n := fun n => by
      have := hinv n
      simp only [htdef]
      nlinarith
    have htτ : ∀ n, t n < τ := fun n => by
      have := hinv n
      simp only [htdef]
      have : 0 < τ / 2 * (1 / ((n : ℝ) + 1)) := mul_pos (by linarith) this.1
      linarith
    have htm : Monotone t := by
      intro m n hmn
      simp only [htdef]
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hmn 1
      nlinarith
    have httend : Tendsto t atTop (𝓝 τ) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (τ / 2)
      rw [mul_zero] at h
      have h2 := (tendsto_const_nhds (x := τ)).sub h
      rw [sub_zero] at h2
      exact h2
    have hpre : ∀ n, ∀ u ∈ Icc 0 (t n), α u ∉ G := fun n u hu =>
      hbefore u hu.1 (lt_of_le_of_lt hu.2 (htτ n))
    -- `α(t_n) → α(τ)` by continuity
    have hαt : Tendsto (fun n => α (t n)) atTop (𝓝 (α τ)) := by
      have hcw : ContinuousWithinAt α (Ici 0) τ := hα.cont τ (mem_Ici.2 hτC.1)
      exact hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨httend,
        Eventually.of_forall fun n => mem_Ici.2 (ht0 n).le⟩)
    rcases key ht0 htm hpre with ⟨p, hp, hpt⟩ | hpt
    · exfalso
      have e := tendsto_nhds_unique hαt hpt
      exact hp.2 (e ▸ hτC.2)
    · have e := tendsto_nhds_unique hαt hpt
      exact ⟨τ, mem_Ici.2 hτC.1, e⟩

/-- **The hull family determines the continued trace before contact.** If a continued driver `X̂` has a simple proper
trace `η`, and `σ` is a continuous strictly increasing clock with `σ(0) = 0` such that the hull of `X̂` at `σ(t)` is the
chart image `Ψ(α((0, t]))` at every positive time `t` before contact, then `η(σ(t)) = Ψ(α(t))` at those times: `Ψ(α(t))`
lies in `η((0, σ(t)])`, and a parameter `v < σ(t)` would be `σ(t')` for some `t' < t` (intermediate values), putting
`Ψ(α(t))` in `Ψ(α((0, t']))`, against the injectivity of `Ψ` and `α`. -/
theorem trace_clock_eq_revChart {Wh : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace Wh η) (hηp : IsProperArc η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s) (hα : IsProperArc α)
    (hσc : ContinuousOn σ (preContact α (negInv '' fwdHull W s)))
    (hσm : StrictMonoOn σ (preContact α (negInv '' fwdHull W s))) (hσ0 : σ 0 = 0)
    (hK : ∀ t ∈ preContact α (negInv '' fwdHull W s), 0 < t →
      fwdHull Wh (σ t) = revChart W s '' (α '' Ioc 0 t))
    {t : ℝ} (htp : t ∈ preContact α (negInv '' fwdHull W s)) (ht : 0 < t) :
    η (σ t) = revChart W s (α t) := by
  set G := negInv '' fwdHull W s with hGdef
  have hpre := htp.2
  have h0p : (0 : ℝ) ∈ preContact α G := Icc_subset_preContact htp ⟨le_rfl, ht.le⟩
  have hmem : ∀ u ∈ Ioc 0 t, α u ∈ H \ G := fun u hu => ⟨hα.mem_H u hu.1, hpre u ⟨hu.1.le, hu.2⟩⟩
  have hσt : 0 < σ t := by
    have := hσm h0p htp ht
    rwa [hσ0] at this
  have h1 : revChart W s (α t) ∈ η '' Ioc 0 (σ t) := by
    rw [← fwdHull_eq_image_Ioc hη hηp hσt.le, hK t htp ht]
    exact ⟨α t, ⟨t, ⟨ht, le_rfl⟩, rfl⟩, rfl⟩
  obtain ⟨v, hv, hve⟩ := h1
  rcases hv.2.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨t', ht', hσt'⟩ := intermediate_value_Icc ht.le (hσc.mono (Icc_subset_preContact htp))
      (show v ∈ Icc (σ 0) (σ t) by rw [hσ0]; exact ⟨hv.1.le, hlt.le⟩)
    have ht'pos : 0 < t' := by
      rcases ht'.1.eq_or_lt with h0 | h0
      · rw [← h0, hσ0] at hσt'; exact absurd hσt' (ne_of_lt hv.1)
      · exact h0
    have ht't : t' < t := by
      rcases ht'.2.lt_or_eq with h0 | h0
      · exact h0
      · rw [h0] at hσt'; exact absurd hσt' (ne_of_gt hlt)
    have hpre' : t' ∈ preContact α G := Icc_subset_preContact htp ht'
    have h2 : η v ∈ fwdHull Wh (σ t') := by
      rw [fwdHull_eq_image_Ioc hη hηp (by rw [hσt']; exact hv.1.le)]
      exact ⟨v, ⟨hv.1, hσt'.ge⟩, rfl⟩
    rw [hK t' hpre' ht'pos, hve] at h2
    obtain ⟨_, ⟨u, hu, rfl⟩, hue⟩ := h2
    have e1 := injOn_revChart hW hW0 hs (hmem u ⟨hu.1, hu.2.trans ht't.le⟩) (hmem t ⟨ht, le_rfl⟩) hue
    have e2 := hα.inj (mem_Ici.2 hu.1.le) (mem_Ici.2 ht.le) e1
    linarith [hu.2]
  · rw [← heq]; exact hve

end Contact

/-! ### The reduction of the contact step to the image continuation -/

section Reduction

/-- **Named input: the output of step (S4) of the contact step** (Wang–Wu, proof of Proposition 4.18, text dump
L1626–1629: "Map this domain to `H`, taking the start to `0` and `β(s)` to `∞`. Before contact, the simple forward trace
has continuous driving in this domain. Its conditional harmonic means and conformal-radius brackets, just identified,
satisfy Lemma 2.11. Hence its law is the nonnegative-cumulative force-point law. The trace lemma and Corollary 4.13
imply …"). In the setting of `ReverseTipContactStatement`, for each rational `s > 0`, almost surely on the glued space
the chart image `Ψ ∘ α` of the forward seed line before its first contact with `G = R(β((0, s]))`
(`Ψ = revChart` of the reverse frozen driver) is, after a clock `σ` that is monotone and positive at positive times on
the pre-contact times `preContact α G` (only there: in the true scenario `σ(t) → ∞` at the contact time), the beginning
of a curve `X` that is continuous on `[0, ∞)`, lies in `ℍ` at positive times and tends to `∞` — the trace of the image chain's
`SLE₄(r_L, −r_L; r_R, −r_R)` driver continued after the end of the image (Lemma 4.12 and transience for the nonnegative
cumulative weights `r, 0`). -/
def ImageContinuationStatement : Prop :=
  ∀ (rL rR : ℝ), 0 ≤ rL → 0 ≤ rR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      P.map h = P₂.map (fun ω => reflectField (h₂ ω)) →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k],
        P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
          P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k →
        ∀ s : ℚ, 0 < s → ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
          ∃ X : ℝ → ℂ, ContinuousOn X (Ici 0) ∧ (∀ u, 0 < u → X u ∈ H) ∧
            Tendsto (fun u => ‖X u‖) atTop atTop ∧ ∃ σ : ℝ → ℝ,
              MonotoneOn σ (preContact (seedLine ζ W p.1) (negInv '' histHull s p.2)) ∧
              (∀ t ∈ preContact (seedLine ζ W p.1) (negInv '' histHull s p.2), 0 < t → 0 < σ t) ∧
              ∀ t ∈ preContact (seedLine ζ W p.1) (negInv '' histHull s p.2), 0 < t →
                X (σ t) = revChart (Ito.rpath (frzDrive s p.2)) s (seedLine ζ W p.1 t)

/-- **The contact step from the image continuation** (step (S5) on the glued space): `ReverseTipContactStatement` follows
from `ImageContinuationStatement`. On the glued space the forward line is a simple proper arc, the reverse history is good
(`BetaSet`: its frozen driver generates a simple proper trace `β` whose hull at `s` is `histHull s`), `G` is closed, and
`revLine p.2 s = R(β(s))`; then `mem_arcRange_of_continuation` applies. -/
theorem reverseTipContactStatement_of_imageContinuation (hI : ImageContinuationStatement.{u}) :
    ReverseTipContactStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs
  have hh : Measurable h := hC.2.1
  have hRh₂ : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hC₂.2.1
  have hD₂ := measurable_killedHistory hC₂.2.2.2.1
  -- the forward line is a simple proper arc
  have hgood := ae_glue_fst (μ := P) k hh (ae_good_twoSeed hL hR hC.1)
  -- the reverse history is good
  have hbeta : ∀ᵐ p ∂(glueMeasure P k h hh), p.2 ∈ BetaSet s :=
    ae_glue_snd hh hRh₂ hD₂ hlaw k hk (measurableSet_betaSet s) (ae_killedHistory_mem_betaSet hR hL hC₂.1 hs)
  have hgh := ae_goodHist_snd_glue hL hR hC hC₂ hlaw k hk s
  filter_upwards [hI rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs, hgood, hbeta,
    hgh] with p hp hpα hpβ hpg
  obtain ⟨X, hXc, hXH, hXt, σ, hσm, hσpos, hXσ⟩ := hp
  obtain ⟨hcont, h0, hLT, hP, hhull, -, -⟩ := trace_of_mem_betaSet hs hpβ
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hG : IsClosed (negInv '' fwdHull (Ito.rpath (frzDrive s p.2)) s) := by
    rw [← hhull]; exact isClosed_image_negInv_histHull hs hpg
  have hrev : revLine p.2 s = negInv (frzLine s p.2 s) := by
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hrat⟩, -⟩, -⟩ := hpβ
    rw [revLine, hrat s hs.le le_rfl]
  rw [hrev]
  rw [hhull] at hσm hσpos hXσ
  exact mem_arcRange_of_continuation hLT hcont h0 hs'.le (hP.mem_H _ hs') hG hpα.1 hXc hXH hXt hσm hσpos hXσ

/-- **Named input, hull form: the output of step (S4) of the contact step.** As `ImageContinuationStatement`, in the form
the martingale characterization delivers: almost surely there are a continuous driver `X̂` with `X̂(0) = 0` whose Loewner
trace `η` is a simple proper arc (the image chain's `SLE₄(r_L, −r_L; r_R, −r_R)` driver continued after the end of the
image; Lemma 4.12 and transience), and a continuous strictly increasing clock `σ` with `σ(0) = 0` (the capacity clock of
the image), such that at every positive time `t` before the first contact of the forward line `α` with
`G = R(β((0, s]))`, the hull of `X̂` at `σ(t)` is the chart image `Ψ(α((0, t]))`. -/
def ImageHullStatement : Prop :=
  ∀ (rL rR : ℝ), 0 ≤ rL → 0 ≤ rR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 mΩ₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR) (fun _ => rL) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      P.map h = P₂.map (fun ω => reflectField (h₂ ω)) →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k],
        P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
          P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k →
        ∀ s : ℚ, 0 < s → ∀ᵐ p ∂(glueMeasure P k h hC.2.1),
          ∃ Xh : ℝ → ℝ, Continuous Xh ∧ Xh 0 = 0 ∧ ∃ η : ℝ → ℂ, IsLoewnerTrace Xh η ∧ IsProperArc η ∧
            ∃ σ : ℝ → ℝ, ContinuousOn σ (preContact (seedLine ζ W p.1) (negInv '' histHull s p.2)) ∧
              StrictMonoOn σ (preContact (seedLine ζ W p.1) (negInv '' histHull s p.2)) ∧ σ 0 = 0 ∧
              ∀ t ∈ preContact (seedLine ζ W p.1) (negInv '' histHull s p.2), 0 < t →
                fwdHull Xh (σ t) = revChart (Ito.rpath (frzDrive s p.2)) s '' (seedLine ζ W p.1 '' Ioc 0 t)

/-- `ImageContinuationStatement` from its hull form (`trace_clock_eq_revChart` on the good event). -/
theorem imageContinuationStatement_of_imageHull (hI : ImageHullStatement.{u}) : ImageContinuationStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs
  have hh : Measurable h := hC.2.1
  have hRh₂ : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hC₂.2.1
  have hD₂ := measurable_killedHistory hC₂.2.2.2.1
  have hgood := ae_glue_fst (μ := P) k hh (ae_good_twoSeed hL hR hC.1)
  have hbeta : ∀ᵐ p ∂(glueMeasure P k h hh), p.2 ∈ BetaSet s :=
    ae_glue_snd hh hRh₂ hD₂ hlaw k hk (measurableSet_betaSet s) (ae_killedHistory_mem_betaSet hR hL hC₂.1 hs)
  filter_upwards [hI rL rR hL hR P 𝓕 W VL VR B ζ h hC P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k hk s hs, hgood, hbeta]
    with p hp hpα hpβ
  obtain ⟨Xh, -, -, η, hη, hηp, σ, hσc, hσm, hσ0, hK⟩ := hp
  obtain ⟨hcont, h0, -, -, hhull, -, -⟩ := trace_of_mem_betaSet hs hpβ
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  refine ⟨η, hηp.cont, hηp.mem_H, hηp.tendsto, σ, hσm.monotoneOn, fun t htp ht => ?_, fun t htp ht => ?_⟩
  · have := hσm (Icc_subset_preContact htp ⟨le_rfl, ht.le⟩) htp ht
    rwa [hσ0] at this
  · rw [hhull] at hσc hσm hK htp
    exact trace_clock_eq_revChart hη hηp hcont h0 hs' hpα.1 hσc hσm hσ0 hK htp ht

/-- `ReverseTipContactStatement` from the hull form of step (S4). -/
theorem reverseTipContactStatement_of_imageHull (hI : ImageHullStatement.{u}) : ReverseTipContactStatement.{u} :=
  reverseTipContactStatement_of_imageContinuation (imageContinuationStatement_of_imageHull hI)

end Reduction

end InteractingSLE.WangWu
