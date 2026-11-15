/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NqChain
import InteractingSLE.Spec.Supplement.SB2XfChain
import InteractingSLE.Spec.Supplement.SB2BqPath

/-!
# SB2(2)'s (G2) for PROVE-T14-SB2LIFT's chain core: the two hull fields from boundary limits along the lift

Packet PROVE-GW2-GEOM2 (D11 (G2), ruling R120). PROVE-T14-SB2LIFT's round 25 builds every field of
`FinRel.IsSB2RelChain` except the two hull fields (`Mn.RelChainCore`, for `EL`'s own frozen driver and the stage lift
`γ`) and asks GEOM2 for the hull fields (`Mn.isSB2RelChain_of_core`). Both fields read the driver only through
`fwdHull Wr (capClock γ s) = fill γ([0, s])`, which the core supplies, so they are statements about the lift alone:

* **`hullFields_of_lim`**: for a domain chart `c` of `ℍ ∖ fill A` whose inverse grows at most linearly, an explored
  curve `β'` continuous on `[0, tL + S]` that does not enter `D_A` up to the head time `tL`, and a lift `γ` continuous
  on `[0, S]` in `ℍ̄` along which the chart inverse has the boundary limits `β'(tL + ·)`: for every `s ∈ [0, S]`,
  - (in) every point of `fill β'([0, tL + s])` outside `fill A` has its chart image in `fill γ([0, s])`;
  - (frontier) every point of `D_A` whose chart image is on the frontier of `fill γ([0, s])` is in
    `fill β'([0, tL + s])`;
* **`isSB2RelChain_of_core_lim`**: SB2LIFT's core plus these fields is the relative chain;
* **`isSB2RelChain_of_core_lim_zero`**: the same at head time `0` in the form of `Mn.StageChainAtR` (a retained set
  `X ⊆ ℍ`, bounded, relatively closed, with `X ∪ {im ≤ 0}` preconnected, and a domain chart of `ℍ ∖ X` taking `∞` to
  `∞`; the head condition is vacuous since `β' 0 = 0 ∉ ℍ`);
* **`isSB2RelChain_of_core_g`**: the same from a lift through a continuous extension `g` of the chart inverse
  (`g ∘ γ = β'(tL + ·)` on `[0, S]`, the head in `K_A`; the input form of `FinRel.exists_relConfig`), via
  `tendsto_inv_of_lift`;
* **`isSB2RelChain_of_core_bridge`**: R120's bridge form at head time `0` — the retained set `R` with
  `fill R = fill q([0, 1])` for the lifted upper prefix `q`; the bridge `bridgePath x₁ q` makes the growth inputs
  (boundedness, preconnectedness with the lower half-plane) automatic.

Only boundary limits before `S` enter: no global extension of the chart inverse and nothing of `β'` or `γ` after `S`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Bq

open Sec7.Lemma71C FinRel

variable {A : Set ℂ} {c : Chart} {β' γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The two hull fields of the relative chain from boundary limits along the lift** (driver-free). -/
theorem hullFields_of_lim (hD : IsDomainChart (H \ fillH A) c) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂) {S : ℝ}
    (hβc : ContinuousOn β' (Icc 0 (tL + S.toNNReal))) (hpre : ∀ r ≤ tL, β' r ∉ H \ fillH A)
    (hγc : ContinuousOn γ (Icc 0 S.toNNReal)) (hγH : ∀ s : ℝ≥0, (s : ℝ) ≤ S → 0 ≤ (γ s).im)
    (hlim : ∀ s : ℝ≥0, (s : ℝ) ≤ S → Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (β' (tL + s))))
    {s : ℝ} (hs : s ∈ Icc 0 S) :
    (∀ z ∈ fillH (β' '' Icc 0 (tL + s.toNNReal)), z ∉ fillH A → c.1 z ∈ fillH (γ '' Icc 0 s.toNNReal)) ∧
      (∀ z ∈ H \ fillH A, c.1 z ∈ frontier (fillH (γ '' Icc 0 s.toNNReal)) →
        z ∈ fillH (β' '' Icc 0 (tL + s.toNNReal))) := by
  have hliftH : ∀ s : ℝ≥0, (s : ℝ) ≤ S → γ s ∈ H → c.2.1 (γ s) = β' (tL + s) := by
    intro s hs hsH
    have hca : ContinuousAt c.2.1 (γ s) :=
      hD.1.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hsH)
    have h1 : Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (c.2.1 (γ s))) := hca.tendsto.mono_left nhdsWithin_le_nhds
    have : (𝓝[H] (γ s)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hsH)
    exact tendsto_nhds_unique h1 (hlim s hs)
  have hsS : s.toNNReal ≤ S.toNNReal := Real.toNNReal_le_toNNReal hs.2
  have hYc : IsClosed (γ '' Icc 0 s.toNNReal) :=
    (isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc le_rfl hsS))).isClosed
  have hXc : IsClosed (β' '' Icc 0 (tL + s.toNNReal)) :=
    (isCompact_Icc.image_of_continuousOn (hβc.mono (Icc_subset_Icc le_rfl
      ((add_le_add_iff_left tL).2 hsS)))).isClosed
  have hreal : ∀ r : ℝ≥0, r ≤ s.toNNReal → (r : ℝ) ≤ S := fun r hr =>
    (NNReal.coe_le_coe.2 hr).trans (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
  refine ⟨fun z hz hzA => ?_, fun z hz hfr => ?_⟩
  · refine Nq.fwd_mem_fillH_of_mem_fillH_lim hD hC₁ hgrow hXc hYc ?_ hz hzA
    rintro _ ⟨⟨r, hr, rfl⟩, hDr⟩
    by_cases hrt : r ≤ tL
    · exact absurd hDr (hpre r hrt)
    · have hle : tL ≤ r := le_of_lt (not_le.1 hrt)
      have hrs : r - tL ≤ s.toNNReal := tsub_le_iff_left.2 hr.2
      have heq : tL + (r - tL) = r := add_tsub_cancel_of_le hle
      have hl := hlim (r - tL) (hreal _ hrs)
      rw [heq] at hl
      by_cases hγr : γ (r - tL) ∈ H
      · refine ⟨γ (r - tL), ⟨⟨r - tL, ⟨zero_le, hrs⟩, rfl⟩, hγr⟩, ?_⟩
        rw [hliftH _ (hreal _ hrs) hγr, heq]
      · exfalso
        have hre : γ (r - tL) = ((γ (r - tL)).re : ℂ) :=
          Complex.ext (by simp) (by
            simp only [ofReal_im]
            exact le_antisymm (not_lt.1 hγr) (hγH _ (hreal _ hrs)))
        rw [hre] at hl
        have h := FinRel.notMem_image_of_tendsto_inv hD.isConformal hl
        rw [hD.image_eq] at h
        exact h hDr
  · refine mem_fillH_of_fwd_mem_frontier_fillH (g := c.2.1) hD (fun _ _ => rfl) hYc ?_ hz hfr
    rintro _ ⟨r, hr, rfl⟩ hrH
    rw [hliftH r (hreal r hr.2) hrH]
    exact ⟨tL + r, ⟨zero_le, (add_le_add_iff_left tL).2 hr.2⟩, rfl⟩

/-- **SB2LIFT's chain core plus the hull fields from boundary limits is the relative chain.** -/
theorem isSB2RelChain_of_core_lim {S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} (hcore : Mn.RelChainCore γ S₀ Wr ηr)
    (hD : IsDomainChart (H \ fillH A) c) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁)
    (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂) {S : ℝ} (hS₀S : S₀ ≤ S)
    (hβc : ContinuousOn β' (Icc 0 (tL + S.toNNReal))) (hpre : ∀ r ≤ tL, β' r ∉ H \ fillH A)
    (hγc : ContinuousOn γ (Icc 0 S.toNNReal)) (hγH : ∀ s : ℝ≥0, (s : ℝ) ≤ S → 0 ≤ (γ s).im)
    (hlim : ∀ s : ℝ≥0, (s : ℝ) ≤ S → Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (β' (tL + s)))) :
    IsSB2RelChain A c β' γ tL S₀ Wr ηr := by
  have hK := hcore.2.2.2.2.2.2
  refine Mn.isSB2RelChain_of_core hcore (fun s hs z hz hzA => ?_) (fun s hs z hz hfr => ?_)
  · rw [(hK s hs).2.2]
    exact (hullFields_of_lim hD hC₁ hgrow hβc hpre hγc hγH hlim ⟨hs.1, hs.2.trans hS₀S⟩).1 z hz hzA
  · rw [(hK s hs).2.2] at hfr
    exact (hullFields_of_lim hD hC₁ hgrow hβc hpre hγc hγH hlim ⟨hs.1, hs.2.trans hS₀S⟩).2 z hz hfr

/-- **SB2(2)'s (G2) for SB2LIFT's chain core in the form of `Mn.StageChainAtR`** (head time `0`; retained set
`X ⊆ ℍ` with a domain chart of `ℍ ∖ X` taking `∞` to `∞`). -/
theorem isSB2RelChain_of_core_lim_zero {X : Set ℂ} {S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ}
    (hcore : Mn.RelChainCore γ S₀ Wr ηr) (hXH : X ⊆ H) (hXb : IsBounded X) (hXc : closure X ∩ H ⊆ X)
    (hXp : IsPreconnected (X ∪ {z : ℂ | z.im ≤ 0})) (hD : IsDomainChart (H \ X) c)
    (hinf : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ X)) (cobounded ℂ)) {S : ℝ} (hS₀S : S₀ ≤ S)
    (hβc : ContinuousOn β' (Icc 0 S.toNNReal)) (hβ'0 : β' 0 = 0)
    (hγc : ContinuousOn γ (Icc 0 S.toNNReal)) (hγH : ∀ s : ℝ≥0, (s : ℝ) ≤ S → 0 ≤ (γ s).im)
    (hlim : ∀ s : ℝ≥0, (s : ℝ) ≤ S → Tendsto c.2.1 (𝓝[H] (γ s)) (𝓝 (β' s))) :
    IsSB2RelChain X c β' γ 0 S₀ Wr ηr := by
  have hfX : fillH X = X := Nq.fillH_eq_self_of_isDomainChart hXH hXb hXc hD
  have hD' : IsDomainChart (H \ fillH X) c := by rw [hfX]; exact hD
  have hinf' : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH X)) (cobounded ℂ) := by rw [hfX]; exact hinf
  obtain ⟨C₁, C₂, hC₁, hgrow⟩ := Nq.exists_growth_inv_of_cobounded hXb hXp hD' hinf'
  have hpre : ∀ r ≤ (0 : ℝ≥0), β' r ∉ H \ fillH X := by
    intro r hr hmem
    have hr0 : r = 0 := le_antisymm hr bot_le
    rw [hr0, hβ'0] at hmem
    have h0 : 0 < (0 : ℂ).im := hmem.1
    simp at h0
  exact isSB2RelChain_of_core_lim hcore hD' hC₁ hgrow hS₀S (by simpa only [zero_add] using hβc) hpre hγc hγH
    (fun s hs => by rw [zero_add]; exact hlim s hs)

/-- **Boundary limits along a lift from a continuous extension of the chart inverse to `ℍ̄`.** -/
theorem tendsto_inv_of_lift {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {w : ℂ}
    (hw : 0 ≤ w.im) : Tendsto c.2.1 (𝓝[H] w) (𝓝 (g w)) := by
  have h1 : Tendsto g (𝓝[{z : ℂ | 0 ≤ z.im}] w) (𝓝 (g w)) := hgc w hw
  have h2 : Tendsto g (𝓝[H] w) (𝓝 (g w)) :=
    h1.mono_left (nhdsWithin_mono _ fun z hz => le_of_lt (show 0 < z.im from hz))
  exact h2.congr' (eventually_nhdsWithin_of_forall fun z hz => hgi hz)

/-- **SB2LIFT's chain core plus the hull fields, from a lift through a continuous extension of the chart inverse**
(the input form of `FinRel.exists_relConfig`, read only on `[0, S]`). -/
theorem isSB2RelChain_of_core_g {L S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {g : ℂ → ℂ}
    (hcore : Mn.RelChainCore γ S₀ Wr ηr) (hAb : IsBounded A) (hAc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hc : IsLeftEntryChart A L c) (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {S : ℝ}
    (hS₀S : S₀ ≤ S) (hβc : ContinuousOn β' (Icc 0 (tL + S.toNNReal))) (hpre : β' '' Icc 0 tL ⊆ hullK A)
    (hγc : ContinuousOn γ (Icc 0 S.toNNReal)) (hγH : ∀ s : ℝ≥0, (s : ℝ) ≤ S → 0 ≤ (γ s).im)
    (hlift : ∀ s : ℝ≥0, (s : ℝ) ≤ S → g (γ s) = β' (tL + s)) :
    IsSB2RelChain A c β' γ tL S₀ Wr ηr := by
  obtain ⟨C₁, C₂, hC₁, hgrow⟩ := Nq.exists_growth_inv_of_cobounded hAb hAc hc.1 hc.2.2.1
  have hpre' : ∀ r ≤ tL, β' r ∉ H \ fillH A := by
    intro r hr hmem
    have h := hpre ⟨r, ⟨zero_le, hr⟩, rfl⟩
    unfold hullK at h
    rcases h with h | ⟨x, -, hx⟩
    · exact hmem.2 h
    · have h0 : 0 < (β' r).im := hmem.1
      rw [← hx] at h0
      simp at h0
  exact isSB2RelChain_of_core_lim hcore hc.1 hC₁ hgrow hS₀S hβc hpre' hγc hγH
    fun s hs => by rw [← hlift s hs]; exact tendsto_inv_of_lift hgc hgi (hγH s hs)

/-- **SB2(2)'s (G2) for SB2LIFT's chain core by the bridge** (R120; head time `0`): the retained set `R` with
`fill R = fill q([0, 1])` (`q` the lifted upper prefix, continuous on `[0, 1]` from the real point `x₁ ≥ 0`), a domain
chart of `ℍ ∖ fill R` taking `∞` to `∞`, and a continuous extension `g` of its inverse with `g ∘ γ = β'` on `[0, S]`.
-/
theorem isSB2RelChain_of_core_bridge {R : Set ℂ} {q : ℝ → ℂ} {x₁ S₀ : ℝ} {Wr : ℝ → ℝ} {ηr : ℝ → ℂ}
    {g : ℂ → ℂ} (hcore : Mn.RelChainCore γ S₀ Wr ηr) (hq : ContinuousOn q (Icc 0 1)) (hq0 : q 0 = x₁)
    (hx₁ : 0 ≤ x₁) (hR : fillH R = fillH (q '' Icc 0 1)) (hD : IsDomainChart (H \ fillH R) c)
    (hinf : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH R)) (cobounded ℂ))
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {S : ℝ} (hS₀S : S₀ ≤ S)
    (hβc : ContinuousOn β' (Icc 0 S.toNNReal)) (hβ'0 : β' 0 = 0)
    (hγc : ContinuousOn γ (Icc 0 S.toNNReal)) (hγH : ∀ s : ℝ≥0, (s : ℝ) ≤ S → 0 ≤ (γ s).im)
    (hlift : ∀ s : ℝ≥0, (s : ℝ) ≤ S → g (γ s) = β' s) :
    IsSB2RelChain R c β' γ 0 S₀ Wr ηr := by
  have hPc : IsCompact (bridgePath x₁ q '' Icc 0 1) :=
    isCompact_Icc.image_of_continuousOn (continuousOn_bridgePath hq)
  have hfill : fillH (bridgePath x₁ q '' Icc 0 1) = fillH R := (fillH_image_bridgePath hx₁ hq0).trans hR.symm
  have h0 : (0 : ℂ) ∈ bridgePath x₁ q '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, bridgePath_zero hq0⟩
  have hPp : IsPreconnected (bridgePath x₁ q '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) :=
    (isPreconnected_Icc.image _ (continuousOn_bridgePath hq)).union 0 h0 (show (0 : ℂ).im ≤ 0 by simp)
      isPreconnected_lowerHalf
  have hD' : IsDomainChart (H \ fillH (bridgePath x₁ q '' Icc 0 1)) c := by rw [hfill]; exact hD
  have hinf' : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH (bridgePath x₁ q '' Icc 0 1))) (cobounded ℂ) := by
    rw [hfill]; exact hinf
  obtain ⟨C₁, C₂, hC₁, hgrow⟩ := Nq.exists_growth_inv_of_cobounded hPc.isBounded hPp hD' hinf'
  have hpre : ∀ r ≤ (0 : ℝ≥0), β' r ∉ H \ fillH R := by
    intro r hr hmem
    have hr0 : r = 0 := le_antisymm hr bot_le
    rw [hr0, hβ'0] at hmem
    have h0' : 0 < (0 : ℂ).im := hmem.1
    simp at h0'
  exact isSB2RelChain_of_core_lim hcore hD hC₁ hgrow hS₀S (by simpa only [zero_add] using hβc) hpre hγc hγH
    fun s hs => by rw [zero_add, ← hlift s hs]; exact tendsto_inv_of_lift hgc hgi (hγH s hs)

end InteractingSLE.Theorem14.SB.Bq
