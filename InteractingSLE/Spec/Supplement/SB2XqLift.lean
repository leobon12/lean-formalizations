/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XjStage
import InteractingSLE.Spec.Supplement.G7ClockCluster
import InteractingSLE.Spec.Supplement.SB2GLift

/-!
# The lift clause of the per-stage correspondence: boundary limits of the relative chart's inverse

Packet PROVE-T14-SB2LIFT (round 27). The lift clause of `Mn.StageChainAtR2` asks for the limits of the inverse
`G = (stageRelChart cℓ c c₁ m).2.1 = cℓ.1 ∘ ĝ_m ∘ c₁.2.1` along `ℍ` at the points `γ s` of the lift, including the start
point and the points where B's piece touches the boundary of its domain. There `cℓ.1` (a forward map) has no boundary
extension in general. Instead:

* **`tendsto_of_cluster`** (Yuan's fibre lemma, `Supp7.exists_tendsto_of_tendsto_comp_filter`): if the inverse `cℓ.2.1`
  of a conformal chart has boundary limits on `ℍ̄`, `G` is continuous, `ℍ`-valued and within bounded distance of the
  identity, and `cℓ.2.1 ∘ G` has a limit at `p`, then `G` converges at `p`; its limit is the limit of `G` along any
  sequence of `ℍ` tending to `p` on which `G` converges;
* **`stageInv_facts`**: for the relative chart read in B's stage coordinates the three charts' boundary extensions give
  exactly these inputs (`cℓ.2.1 ∘ G = c.2.1 ∘ (c₁.2.1 · − m)` on `ℍ`);
* **`mapsTo_stage_of_lift`**: the relative domain is carried into B's stage domain off the retained union (the data of
  `isDomainChart_stage_of_lift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Lk

/-- **A chart inverse with boundary limits on `ℍ̄` forces convergence by clustering** (Yuan's fibre lemma). -/
theorem tendsto_of_cluster {cℓ : Chart} (hℓ : cℓ.IsConformal) {Fℓ : ℂ → ℂ}
    (hFℓ : ∀ q ∈ Hbar, Tendsto cℓ.2.1 (𝓝[H] q) (𝓝 (Fℓ q))) {G : ℂ → ℂ} (hGc : ContinuousOn G H)
    (hGH : ∀ y ∈ H, G y ∈ H) {C : ℝ} (hGb : ∀ y ∈ H, ‖G y - y‖ ≤ C) {p v : ℂ} (hp : p ∈ Hbar)
    (hFG : Tendsto (fun y => cℓ.2.1 (G y)) (𝓝[H] p) (𝓝 v)) {u : ℕ → ℂ} (huH : ∀ᶠ n in atTop, u n ∈ H)
    (hu : Tendsto u atTop (𝓝 p)) {w : ℂ} (hw : Tendsto (fun n => G (u n)) atTop (𝓝 w)) :
    Tendsto G (𝓝[H] p) (𝓝 w) := by
  have hFeq : EqOn Fℓ cℓ.2.1 H := fun y hy => by
    have hyH : y ∈ Hbar := QuantumZipper.H_subset_Hbar hy
    have : (𝓝[H] y).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hFℓ y hyH) (hℓ.1.continuousOn y hy)
  have hd : DifferentiableOn ℂ Fℓ H := hℓ.1.congr hFeq
  have hc : ContinuousOn Fℓ Hbar := GW1P.continuousOn_of_tendsto hFℓ
  have hinj : InjOn Fℓ H := hℓ.injOn.congr hFeq.symm
  have hR : ∀ x : ℂ, x.im = 0 → Fℓ x ∉ Fℓ '' H := by
    intro x hx hmem
    obtain ⟨x', rfl⟩ : ∃ x' : ℝ, x = (x' : ℂ) := ⟨x.re, Complex.ext (by simp) (by simp [hx])⟩
    have hlim := hFℓ (x' : ℂ) (show (0 : ℝ) ≤ (x' : ℂ).im by simp)
    rw [image_congr hFeq] at hmem
    exact FinRel.notMem_image_of_tendsto_inv hℓ hlim hmem
  have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
  have hGH' : ∀ᶠ y in 𝓝[H] p, G y ∈ Hbar :=
    eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.H_subset_Hbar (hGH y hy)
  have hGR : ∀ᶠ y in 𝓝[H] p, ‖G y‖ ≤ C + (‖p‖ + 1) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p one_pos), self_mem_nhdsWithin] with y hy hyH
    have h1 : ‖y‖ ≤ ‖p‖ + 1 := by
      have := mem_ball.1 hy
      rw [dist_eq_norm] at this
      calc ‖y‖ = ‖(y - p) + p‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - p‖ + ‖p‖ := norm_add_le _ _
        _ ≤ ‖p‖ + 1 := by linarith
    calc ‖G y‖ = ‖(G y - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖G y - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ C + (‖p‖ + 1) := add_le_add (hGb y hyH) h1
  have hconn : ∀ U ∈ 𝓝[H] p, ∃ S ∈ 𝓝[H] p, S ⊆ U ∧ IsPreconnected S ∧ ContinuousOn G S := by
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
    refine ⟨ball p ε ∩ H, by rw [inter_comm]; exact inter_mem_nhdsWithin H (ball_mem_nhds p hε), hεU, ?_,
      hGc.mono inter_subset_right⟩
    exact ((convex_ball p ε).inter InteractingSLE.convex_H).isPreconnected
  have hFG' : Tendsto (fun y => Fℓ (G y)) (𝓝[H] p) (𝓝 v) :=
    hFG.congr' (eventually_nhdsWithin_of_forall fun y hy => (hFeq (hGH y hy)).symm)
  obtain ⟨ξ, -, -, hξ⟩ := Supp7.exists_tendsto_of_tendsto_comp_filter hd hc hinj hR hGH' hGR hconn hFG'
  have hu' : Tendsto u atTop (𝓝[H] p) := tendsto_nhdsWithin_iff.2 ⟨hu, huH⟩
  rw [tendsto_nhds_unique hw (hξ.comp hu')]
  exact hξ

/-- The inverse of the relative chart read in B's stage coordinates. -/
theorem stageRelChart_inv (cℓ c c₁ : Chart) (m : ℝ) (y : ℂ) :
    (stageRelChart cℓ c c₁ m).2.1 y = cℓ.1 (c.2.1 (c₁.2.1 y - (m : ℂ))) := rfl

/-- **The inverse of the relative chart in B's stage coordinates**: continuous on `ℍ`, `ℍ`-valued, within bounded
distance of the identity, and `cℓ.2.1` of it has a limit at every point of `ℍ̄`. -/
theorem stageInv_facts {cℓ c c₁ : Chart} {m : ℝ} {Bset : Set ℂ} (hℓ : IsDomainChart (H \ fillH Bset) cℓ)
    (hc : c.IsConformal) (hc₁ : c₁.IsConformal) {Fℓ : ℂ → ℂ} {Cℓ : ℝ}
    (hFℓ : ∀ q ∈ Hbar, Tendsto cℓ.2.1 (𝓝[H] q) (𝓝 (Fℓ q))) (hCℓ : ∀ q ∈ Hbar, ‖Fℓ q - q‖ ≤ Cℓ)
    {ĝ : ℂ → ℂ} {Cg : ℝ} (hĝ : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q)))
    (hCg : ∀ q ∈ Hbar, ‖ĝ q - q‖ ≤ Cg) {F₁ : ℂ → ℂ} {C₁ : ℝ}
    (hF₁ : ∀ q ∈ Hbar, Tendsto c₁.2.1 (𝓝[H] q) (𝓝 (F₁ q))) (hC₁ : ∀ q ∈ Hbar, ‖F₁ q - q‖ ≤ C₁)
    (hmaps : ∀ y ∈ H, c.2.1 (c₁.2.1 y - (m : ℂ)) ∈ H \ fillH Bset) :
    ContinuousOn (stageRelChart cℓ c c₁ m).2.1 H ∧ (∀ y ∈ H, (stageRelChart cℓ c c₁ m).2.1 y ∈ H) ∧
      (∀ y ∈ H, ‖(stageRelChart cℓ c c₁ m).2.1 y - y‖ ≤ Cℓ + Cg + C₁ + |m|) ∧
      (∀ y ∈ H, cℓ.2.1 ((stageRelChart cℓ c c₁ m).2.1 y) = c.2.1 (c₁.2.1 y - (m : ℂ))) ∧
      ∀ p ∈ Hbar, Tendsto (fun y => cℓ.2.1 ((stageRelChart cℓ c c₁ m).2.1 y)) (𝓝[H] p)
        (𝓝 (ĝ (F₁ p - (m : ℂ)))) := by
  -- each chart inverse agrees with its boundary map on `ℍ`
  have heq : ∀ {d : Chart} {F : ℂ → ℂ}, d.IsConformal → (∀ q ∈ Hbar, Tendsto d.2.1 (𝓝[H] q) (𝓝 (F q))) →
      EqOn F d.2.1 H := fun {d F} hd hF y hy => by
    have hyH : y ∈ Hbar := QuantumZipper.H_subset_Hbar hy
    have : (𝓝[H] y).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hF y hyH) (hd.1.continuousOn y hy)
  have hb : ∀ {d : Chart} {F : ℂ → ℂ} {C : ℝ}, d.IsConformal → (∀ q ∈ Hbar, Tendsto d.2.1 (𝓝[H] q) (𝓝 (F q))) →
      (∀ q ∈ Hbar, ‖F q - q‖ ≤ C) → ∀ y ∈ H, ‖d.2.1 y - y‖ ≤ C := fun {d F C} hd hF hC y hy => by
    rw [← heq hd hF hy]
    exact hC y (QuantumZipper.H_subset_Hbar hy)
  have h₁H : ∀ y ∈ H, c₁.2.1 y - (m : ℂ) ∈ H := fun y hy => sub_real_mem_H (hc₁.2.1 hy) m
  have hcomp : ContinuousOn (fun y => c.2.1 (c₁.2.1 y - (m : ℂ))) H :=
    hc.1.continuousOn.comp (hc₁.1.continuousOn.sub continuousOn_const) fun y hy => h₁H y hy
  refine ⟨?_, fun y hy => hℓ.fwd_mem (hmaps y hy), fun y hy => ?_, fun y hy => hℓ.inv_fwd (hmaps y hy),
    fun p hp => ?_⟩
  · exact hℓ.differentiableOn_fwd.continuousOn.comp hcomp fun y hy => hmaps y hy
  · -- bounded displacement of each map
    set w := c.2.1 (c₁.2.1 y - (m : ℂ)) with hw
    have hwD := hmaps y hy
    have hv : cℓ.1 w ∈ H := hℓ.fwd_mem hwD
    have h1 : ‖cℓ.1 w - w‖ ≤ Cℓ := by
      have := hb hℓ.1 hFℓ hCℓ (cℓ.1 w) hv
      rw [hℓ.inv_fwd hwD, norm_sub_rev] at this
      exact this
    have h2 : ‖w - (c₁.2.1 y - (m : ℂ))‖ ≤ Cg := hb hc hĝ hCg _ (h₁H y hy)
    have h3 : ‖c₁.2.1 y - y‖ ≤ C₁ := hb hc₁ hF₁ hC₁ y hy
    have h4 : ‖(m : ℂ)‖ = |m| := Complex.norm_real m
    rw [stageRelChart_inv]
    calc ‖cℓ.1 w - y‖ = ‖(cℓ.1 w - w) + (w - (c₁.2.1 y - (m : ℂ))) + (c₁.2.1 y - y) - (m : ℂ)‖ := by
          congr 1; ring
      _ ≤ ‖(cℓ.1 w - w) + (w - (c₁.2.1 y - (m : ℂ))) + (c₁.2.1 y - y)‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖cℓ.1 w - w‖ + ‖w - (c₁.2.1 y - (m : ℂ))‖ + ‖c₁.2.1 y - y‖ + ‖(m : ℂ)‖ := by
          gcongr
          exact norm_add₃_le
      _ ≤ Cℓ + Cg + C₁ + |m| := by rw [h4]; linarith
  · -- the composite limit
    have hlim₁ : Tendsto (fun y => c₁.2.1 y - (m : ℂ)) (𝓝[H] p) (𝓝[H] (F₁ p - (m : ℂ))) :=
      tendsto_nhdsWithin_iff.2 ⟨(hF₁ p hp).sub tendsto_const_nhds,
        eventually_nhdsWithin_of_forall fun y hy => h₁H y hy⟩
    have hqH : F₁ p - (m : ℂ) ∈ Hbar := by
      have hF₁p : F₁ p ∈ Hbar := by
        have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
        exact isClosed_Hbar.mem_of_tendsto (hF₁ p hp)
          (eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.H_subset_Hbar (hc₁.2.1 hy))
      show 0 ≤ (F₁ p - (m : ℂ)).im
      simpa using (show (0 : ℝ) ≤ (F₁ p).im from hF₁p)
    refine ((hĝ _ hqH).comp hlim₁).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    exact (hℓ.inv_fwd (hmaps y hy)).symm

/-- **The lift clause by clustering**: the inverse of the relative chart in B's stage coordinates converges at every
point `p` of `ℍ̄`; its limit is that along any sequence of `ℍ` tending to `p` on which it converges. -/
theorem tendsto_stageInv_of_seq {cℓ c c₁ : Chart} {m : ℝ} {Bset : Set ℂ} (hℓ : IsDomainChart (H \ fillH Bset) cℓ)
    (hc : c.IsConformal) (hc₁ : c₁.IsConformal) {Fℓ : ℂ → ℂ} {Cℓ : ℝ}
    (hFℓ : ∀ q ∈ Hbar, Tendsto cℓ.2.1 (𝓝[H] q) (𝓝 (Fℓ q))) (hCℓ : ∀ q ∈ Hbar, ‖Fℓ q - q‖ ≤ Cℓ)
    {ĝ : ℂ → ℂ} {Cg : ℝ} (hĝ : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q)))
    (hCg : ∀ q ∈ Hbar, ‖ĝ q - q‖ ≤ Cg) {F₁ : ℂ → ℂ} {C₁ : ℝ}
    (hF₁ : ∀ q ∈ Hbar, Tendsto c₁.2.1 (𝓝[H] q) (𝓝 (F₁ q))) (hC₁ : ∀ q ∈ Hbar, ‖F₁ q - q‖ ≤ C₁)
    (hmaps : ∀ y ∈ H, c.2.1 (c₁.2.1 y - (m : ℂ)) ∈ H \ fillH Bset) {p : ℂ} (hp : p ∈ Hbar) {u : ℕ → ℂ}
    (huH : ∀ᶠ n in atTop, u n ∈ H) (hu : Tendsto u atTop (𝓝 p)) {w : ℂ}
    (hw : Tendsto (fun n => (stageRelChart cℓ c c₁ m).2.1 (u n)) atTop (𝓝 w)) :
    Tendsto (stageRelChart cℓ c c₁ m).2.1 (𝓝[H] p) (𝓝 w) := by
  obtain ⟨hGc, hGH, hGb, -, hFG⟩ := stageInv_facts hℓ hc hc₁ hFℓ hCℓ hĝ hCg hF₁ hC₁ hmaps
  exact tendsto_of_cluster hℓ.1 hFℓ hGc hGH hGb hp (hFG p hp) huH hu hw

/-- **The relative domain is carried into B's stage domain off the retained union** (the data of
`isDomainChart_stage_of_lift`). -/
theorem mapsTo_stage_of_lift {c c₁ : Chart} {A B Rel : Set ℂ} {m R : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    {ĝ : ℂ → ℂ} (hc : IsDomainChart (H \ fillH A) c)
    (h₁ : IsDomainChart (H \ fillH Rel) c₁) (hA : IsCompact A)
    (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hRel : IsCompact Rel) (hRelH : Rel ⊆ Hbar) (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Continuous β₀)
    (hRelEq : Rel = liftImage β₀ tL γ B) (hB : IsCompact B) (hBr : B ⊆ range β₀)
    (hhead : β₀ '' Icc 0 tL ⊆ hullK A) (hcl : IsClosed (β₀ '' Ici tL)) :
    ∀ y ∈ H, c.2.1 (c₁.2.1 y - (m : ℂ)) ∈ H \ fillH (A ∪ B) := by
  have hĝc : ContinuousOn ĝ Hbar := GW1P.continuousOn_of_tendsto hĝ
  have hgg : EqOn ĝ c.2.1 H := fun w hw => by
    have hwH : w ∈ Hbar := QuantumZipper.H_subset_Hbar hw
    have : (𝓝[H] w).NeBot := GW1P.neBot_nhdsWithin_H hwH
    exact tendsto_nhds_unique (hĝ w hwH) ((hc.1.1.continuousOn w hw).tendsto)
  have hfill : fillH (A ∪ (fun y => ĝ (y - (m : ℂ))) '' Rel) = fillH (A ∪ B) := by
    rw [hRelEq, image_ext_liftImage hγ hĝ B]
    exact fillH_tail_eq hβ hA hB hBr hhead hcl
  have himg := image_relShift_diff_fillH (m := m) hc hA hĝc hgg hC hRel hRelH
  intro y hy
  have hmem : c.2.1 (c₁.2.1 y - (m : ℂ)) ∈ (fun y => c.2.1 (y - (m : ℂ))) '' (H \ fillH Rel) :=
    ⟨c₁.2.1 y, h₁.inv_mem hy, rfl⟩
  rw [himg, hfill] at hmem
  exact hmem

end InteractingSLE.Theorem14.SB.Mn
