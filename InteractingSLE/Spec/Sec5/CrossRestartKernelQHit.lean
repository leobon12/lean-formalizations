/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQSample
import InteractingSLE.Spec.Sec5.Lemma47QTip

/-!
# Lemma 4.7 in the chart `Q`: the first hit pulled back from the image chart of the counterflow

Packet PROVE-CFRESTART3 (item (E) of PROVE-CFRESTART2's route, deterministic part; specification p. 118: "conformally
mapping `𝒮 ∖ η([0, τ])` back to `𝒮` … we just need to argue that `η′` first hits `∂_L𝒮` at `0` … Lemma 4.5 implies that
`η′` first hits the specified lower boundary at its tip"). Let `β` be the flow line (a simple proper Loewner trace of
`Wβ`), `q > 0`, `G = R(K_q)` its reflected prefix (closed), and `α` the counterflow in the chart `R`: continuous, from
`0`, in `ℍ` at positive times, and transient. Read `α` before its first contact with `G` in the chart
`Ψ = revChart Wβ q = R ∘ f_q ∘ R` (which sends the tip `R(β(q))` to `∞`).

**`isFirstHitQ_of_imgFull`**: suppose that on the pre-contact times `P` the image `Ψ ∘ α` is `γ ∘ a` for a monotone
clock `a ≥ 0` and a continuous curve `γ` on `[0, ∞)` that never meets `ℝ ∖ {0}` and tends to `∞` (the trace of the
full image word, from Lemma 4.5 at `16/κ` once the killed image word is identified with a full evolution before its
killing time). Then `Prop411Q.IsFirstHitQ β α q`: the counterflow `η′ = R ∘ α` visits `β(q)` and avoids `β((0, q])`
before.

## Proof

Run `u` up the pre-contact interval `P = [0, u₀)` (`u₀ ≤ ∞`).

* If the clock stays bounded, `Ψ(α(u)) = γ(a(u)) → γ(S)`, `S = sup a(P)`. A limit in `ℍ` pulls back through the
  continuous `Ψ⁻¹` to a point of `ℍ ∖ G`; a real limit is `0` (`γ` avoids `ℝ ∖ {0}`) and pulls back to `0`
  (`tendsto_revChartInv_nhdsWithin_zero`). Either contradicts `α(u₀) ∈ G` (first contact) or, if `u₀ = ∞`, the
  transience of `α`.
* If the clock is unbounded, `|Ψ(α(u))| → ∞`, so `f_q(R(α(u))) = R(Ψ(α(u))) → 0`. With no contact (`u₀ = ∞`) this
  forces `R(α(u)) → β(q)` (`TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT`), against transience; so `u₀ < ∞` and
  `Lemma47Q.isFirstHitQ_of_tendsto_fwdMap` concludes.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal

open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop411Q

/-! ### The pre-contact interval -/

section Pre

variable {α : ℝ → ℂ} {G : Set ℂ}

theorem mem_preContact_of_le {u v : ℝ} (hu : u ∈ preContact α G) (hv : 0 ≤ v) (hvu : v ≤ u) :
    v ∈ preContact α G :=
  Icc_subset_preContact hu ⟨hv, hvu⟩

/-- A continuous path from a point off a closed set stays off it for a while. -/
theorem exists_pos_mem_preContact (hαc : Continuous α) (hGc : IsClosed G) (h0 : α 0 ∉ G) :
    ∃ δ > 0, δ ∈ preContact α G := by
  have hU : ∀ᶠ v in 𝓝 (0 : ℝ), α v ∈ Gᶜ := hαc.continuousAt.eventually (hGc.isOpen_compl.mem_nhds h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hU
  refine ⟨δ / 2, by positivity, by positivity, fun v hv => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hv.1]
  linarith [hv.2]

/-- The supremum of a bounded pre-contact interval is not in it. -/
theorem sSup_notMem_preContact (hαc : Continuous α) (hGc : IsClosed G)
    (hbdd : BddAbove (preContact α G)) : sSup (preContact α G) ∉ preContact α G := by
  intro hmem
  set u₀ := sSup (preContact α G) with hu₀
  have hU : ∀ᶠ v in 𝓝 u₀, α v ∈ Gᶜ :=
    hαc.continuousAt.eventually (hGc.isOpen_compl.mem_nhds (hmem.2 u₀ ⟨hmem.1, le_rfl⟩))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hU
  have hin : u₀ + δ / 2 ∈ preContact α G := by
    refine ⟨by linarith [hmem.1], fun v hv => ?_⟩
    rcases le_or_gt v u₀ with hvu | hvu
    · exact hmem.2 v ⟨hv.1, hvu⟩
    · refine hball ?_
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [hv.2]
  have := le_csSup hbdd hin
  linarith

/-- At the supremum of a bounded pre-contact interval the path is in `G`. -/
theorem mem_of_sSup_preContact (hαc : Continuous α) (hGc : IsClosed G) (hne : (preContact α G).Nonempty)
    (hbdd : BddAbove (preContact α G)) : α (sSup (preContact α G)) ∈ G := by
  set u₀ := sSup (preContact α G) with hu₀
  have hnot := sSup_notMem_preContact hαc hGc hbdd
  obtain ⟨p, hp⟩ := hne
  have hu₀0 : 0 ≤ u₀ := hp.1.trans (le_csSup hbdd hp)
  have : ¬ ∀ v ∈ Icc 0 u₀, α v ∉ G := fun h => hnot ⟨hu₀0, h⟩
  push Not at this
  obtain ⟨v, hv, hvG⟩ := this
  rcases hv.2.lt_or_eq with hlt | heq
  · obtain ⟨u', hu', hvu'⟩ := exists_lt_of_lt_csSup ⟨p, hp⟩ hlt
    exact absurd hvG (hu'.2 v ⟨hv.1, hvu'.le⟩)
  · rwa [heq] at hvG

end Pre

/-! ### The first hit -/

section Hit

variable {Wβ : ℝ → ℝ} {β α : ℝ → ℂ} {q : ℝ}

/-- **Lemma 4.7's first hit from the full image trace** (deterministic; see the module docstring). -/
theorem isFirstHitQ_of_imgFull (hβ : IsLoewnerTrace Wβ β) (hβp : IsProperArc β) (hW : Continuous Wβ)
    (hW0 : Wβ 0 = 0) (hq : 0 < q) (hGc : IsClosed (negInv '' fwdHull Wβ q))
    (hαc : Continuous α) (hα0 : α 0 = 0) (hαH : ∀ v, 0 < v → α v ∈ H)
    (hαtr : Tendsto (fun v => ‖α v‖) atTop atTop)
    {a : ℝ → ℝ≥0} (ha : MonotoneOn a (preContact α (negInv '' fwdHull Wβ q)))
    {γ : ℝ≥0 → ℂ} (hγc : Continuous γ) (hγR : ∀ (r : ℝ≥0) (x : ℝ), x ≠ 0 → γ r ≠ x)
    (hγtr : Tendsto (fun r => ‖γ r‖) atTop atTop)
    (hagree : ∀ u ∈ preContact α (negInv '' fwdHull Wβ q), 0 < u → γ (a u) = revChart Wβ q (α u)) :
    IsFirstHitQ β α q := by
  classical
  set G := negInv '' fwdHull Wβ q with hGdef
  set P := preContact α G with hPdef
  have hGH : G ⊆ H := image_negInv_subset_H fun z hz => hz.1
  have h0G : α 0 ∉ G := fun h => by rw [hα0] at h; exact ne_zero_of_mem_H (hGH h) rfl
  obtain ⟨δ, hδ, hδP⟩ := exists_pos_mem_preContact hαc hGc h0G
  have hPne : P.Nonempty := ⟨δ, hδP⟩
  have hPmem : ∀ u ∈ P, 0 < u → α u ∈ H \ G := fun u hu hu0 => ⟨hαH u hu0, hu.2 u ⟨hu.1, le_rfl⟩⟩
  -- a filter running up the pre-contact interval
  obtain ⟨L, hLne, hLP, hLS, hcase⟩ : ∃ L : Filter ℝ, L.NeBot ∧ (∀ᶠ u in L, u ∈ P ∧ 0 < u) ∧
      (∀ S ∈ P, ∀ᶠ u in L, S ≤ u) ∧
      ((∃ u₀ : ℝ, 0 < u₀ ∧ α u₀ ∈ G ∧ L = 𝓝[<] u₀ ∧ (∀ u, 0 < u → u < u₀ → u ∈ P)) ∨
        Tendsto (fun u => ‖α u‖) L atTop) := by
    by_cases hbdd : BddAbove P
    · set u₀ := sSup P with hu₀def
      have hnot := sSup_notMem_preContact hαc hGc hbdd
      have hu₀G := mem_of_sSup_preContact hαc hGc hPne hbdd
      have hu₀ : 0 < u₀ := lt_of_lt_of_le hδ (le_csSup hbdd hδP)
      have hlow : ∀ u, 0 ≤ u → u < u₀ → u ∈ P := fun u hu0 hu => by
        obtain ⟨u', hu', huu'⟩ := exists_lt_of_lt_csSup hPne hu
        exact mem_preContact_of_le hu' hu0 huu'.le
      refine ⟨𝓝[<] u₀, inferInstance, ?_, fun S hS => ?_,
        Or.inl ⟨u₀, hu₀, hu₀G, rfl, fun u h0 h1 => hlow u h0.le h1⟩⟩
      · filter_upwards [Ioo_mem_nhdsLT hu₀] with u hu
        exact ⟨hlow u hu.1.le hu.2, hu.1⟩
      · have hSu : S < u₀ := lt_of_le_of_ne (le_csSup hbdd hS) fun h => hnot (show u₀ ∈ P by rw [← h]; exact hS)
        filter_upwards [Ioo_mem_nhdsLT hSu] with u hu using hu.1.le
    · have hall : ∀ u, 0 ≤ u → u ∈ P := fun u hu => by
        rw [not_bddAbove_iff] at hbdd
        obtain ⟨u', hu', huu'⟩ := hbdd u
        exact mem_preContact_of_le hu' hu huu'.le
      refine ⟨atTop, inferInstance, ?_, fun S _ => eventually_ge_atTop S, Or.inr hαtr⟩
      filter_upwards [eventually_gt_atTop 0] with u hu using ⟨hall u hu.le, hu⟩
  -- the path has no limit off `G` along `L`
  have hnolim : ∀ z : ℂ, z ∉ G → ¬ Tendsto α L (𝓝 z) := by
    intro z hz hlim
    rcases hcase with ⟨u₀, -, hu₀G, rfl, -⟩ | htr
    · have h2 : Tendsto α (𝓝[<] u₀) (𝓝 (α u₀)) := hαc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact hz (tendsto_nhds_unique hlim h2 ▸ hu₀G)
    · exact not_tendsto_atTop_of_tendsto_nhds hlim.norm htr
  have hΨ : ∀ᶠ u in L, revChart Wβ q (α u) ∈ H ∧ γ (a u) = revChart Wβ q (α u) ∧ α u ∈ H \ G := by
    filter_upwards [hLP] with u hu
    exact ⟨revChart_mem_H hW hq.le (hPmem u hu.1 hu.2), hagree u hu.1 hu.2, hPmem u hu.1 hu.2⟩
  by_cases hab : BddAbove (a '' P)
  · exfalso
    set S := sSup (a '' P) with hSdef
    have haS : Tendsto (fun u => a u) L (𝓝 S) := by
      refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
      · obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hbu₁⟩ := exists_lt_of_lt_csSup (hPne.image a) hb
        filter_upwards [hLP, hLS u₁ hu₁] with u hu hu₁u
        exact lt_of_lt_of_le hbu₁ (ha hu₁ hu.1 hu₁u)
      · filter_upwards [hLP] with u hu
        exact lt_of_le_of_lt (le_csSup hab ⟨u, hu.1, rfl⟩) hb
    have hγS : Tendsto (fun u => revChart Wβ q (α u)) L (𝓝 (γ S)) :=
      ((hγc.tendsto S).comp haS).congr' (hΨ.mono fun u hu => hu.2.1)
    have hHlim : Tendsto (fun u => revChart Wβ q (α u)) L (𝓝[H] (γ S)) :=
      tendsto_nhdsWithin_iff.2 ⟨hγS, hΨ.mono fun u hu => hu.1⟩
    have him : 0 ≤ (γ S).im :=
      ge_of_tendsto ((Complex.continuous_im.tendsto _).comp hγS) (hΨ.mono fun u hu => le_of_lt hu.1)
    rcases him.lt_or_eq with hpos | hzero
    · have hc := (continuousOn_revChartInv hW hW0 hq.le) (γ S) hpos
      have h1 := hc.tendsto.comp hHlim
      have h2 : Tendsto α L (𝓝 (revChartInv Wβ q (γ S))) :=
        h1.congr' (hΨ.mono fun u hu => revChartInv_revChart hW hW0 hq.le hu.2.2)
      exact hnolim _ (revChartInv_mem hW hW0 hq.le hpos).2 h2
    · have hreal : γ S = ((γ S).re : ℂ) := Complex.ext rfl (by simp [← hzero])
      have hre0 : (γ S).re = 0 := by
        by_contra hne
        exact hγR S _ hne hreal
      have hS0 : γ S = 0 := by rw [hreal, hre0]; simp
      rw [hS0] at hHlim
      have h1 := (GlueImg.tendsto_revChartInv_nhdsWithin_zero hW hW0 hq.le).comp hHlim
      have h2 : Tendsto α L (𝓝 0) :=
        h1.congr' (hΨ.mono fun u hu => revChartInv_revChart hW hW0 hq.le hu.2.2)
      exact hnolim 0 (fun h => ne_zero_of_mem_H (hGH h) rfl) h2
  · have hainf : Tendsto (fun u => a u) L atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      have hex : ∃ u₁ ∈ P, b ≤ a u₁ := by
        by_contra hcon
        push Not at hcon
        exact hab ⟨b, by rintro _ ⟨u, hu, rfl⟩; exact (hcon u hu).le⟩
      obtain ⟨u₁, hu₁, hb⟩ := hex
      filter_upwards [hLP, hLS u₁ hu₁] with u hu hu₁u using hb.trans (ha hu₁ hu.1 hu₁u)
    have hnorm : Tendsto (fun u => ‖revChart Wβ q (α u)‖) L atTop :=
      (hγtr.comp hainf).congr' (hΨ.mono fun u hu => by simp only [Function.comp_apply, hu.2.1])
    have e : ∀ u, fwdMap Wβ q (negInv (α u)) = negInv (revChart Wβ q (α u)) := fun u => by
      rw [revChart, negInv_negInv]
    have hf0 : Tendsto (fun u => fwdMap Wβ q (negInv (α u))) L (𝓝[H] 0) := by
      simp_rw [e]
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hΨ.mono fun u hu => negInv_mem_H hu.1⟩
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_negInv]
      exact hnorm.inv_tendsto_atTop
    rcases hcase with ⟨u₀, hu₀, -, rfl, hlow⟩ | htr
    · refine Lemma47Q.isFirstHitQ_of_tendsto_fwdMap hβ hβp hW hW0 hq hu₀ hαc.continuousAt.continuousWithinAt
        (fun v hv => negInv_notMem_fwdHull (hPmem v (hlow v hv.1 hv.2) hv.1)) ?_
      exact (tendsto_nhdsWithin_iff.1 hf0).1.mono_left (nhdsWithin_mono _ Ioo_subset_Iio_self)
    · exfalso
      have htip := TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT (isLoewnerTraceLT_of_isLoewnerTrace hβ q) hW
        hW0 hq (hβ.2.1.mono Icc_subset_Ici_self)
      have h3 : Tendsto (fun u => negInv (α u)) L (𝓝 (β q)) :=
        (htip.comp hf0).congr' (hΨ.mono fun u hu =>
          QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hq.le (negInv_notMem_fwdHull hu.2.2))
      have h4 : Tendsto (fun u => negInv (α u)) L (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [norm_negInv]
        exact htr.inv_tendsto_atTop
      exact ne_zero_of_mem_H (hβp.mem_H q hq) (tendsto_nhds_unique h3 h4)

end Hit

end InteractingSLE.Sec5.CrossRestart.KernelQ
