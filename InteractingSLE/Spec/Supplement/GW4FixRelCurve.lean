/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinal
import InteractingSLE.Spec.Supplement.GW4FixSafe

/-!
# GW4's relative trace with explicit pocket data, and its local driven curves

Packet PROVE-T14-GW4FIX (continuation: instantiate PROVE-GB6-RELSAFE's core for GW4). Lemma GB11's relative trace of a
pocket traversal is `ζ(u) = relPt E ψ k (γ(τ + u))` (`GB11Chart.exists_relCurve`), where the pocket data `(E, ψ, G, k)`
(`GB11Chart.exists_pocketData`) depend only on the two walks, the component and its chart — not on the counterflow.
Under the conditional law given the walks they are therefore fixed, and the relative trace is a fixed function of the
physical trace. `exists_relCurve` hides the data in an `obtain`; here:

* `IsPocketData` (the conclusion of `exists_pocketData`), `relTrace E ψ k γ τ u = relPt E ψ k (γ (τ + u))`;
* **`exists_relCurve_of_data`**: `GB11Chart.exists_relCurve` for the given pocket data (its proof, copied, with the
  data as hypotheses) — the relative trace is continuous from `0`, its fills are the relative hulls and grow strictly;
* **`exists_loewner_relTrace`**: on every `[0, T]`, `T < σ − τ`, the fills are Loewner hulls after a continuous strictly
  increasing time change (Yuan's theorem with GB11's proved continuous own futures,
  `GB11Chart.gb11RelOwnFutureStatement`);
* **`isDrivenCurve_relTrace`**: the reparametrized relative trace `relCurve (relTrace …) T` is a driven curve
  (`PocketTraversal.isDrivenCurve_relCurve`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Reg GB11Conn GB11Chart Sec7.PocketTraversal

/-- **The pocket data of a shaped pocket** (the conclusion of `GB11Chart.exists_pocketData`). -/
def IsPocketData (αR αL : ℝ≥0 → ℂ) (C : Set ℂ) (c : Chart) (s₁ t₁ : ℝ≥0) (s₂ : ℝ≥0∞) (E : Set ℂ)
    (ψ G : ℂ → ℂ) (k : ℝ) : Prop :=
  IsPocketCoord αR αL C c s₁ t₁ E ψ G k ∧ IsClosed E ∧ (0 : ℂ) ∉ E ∧
    (∀ Q ∈ E, Tendsto ψ (𝓝[closure C \ E] Q) (cobounded ℂ)) ∧
    (∀ Q ∈ E, Tendsto G (cobounded ℂ ⊓ 𝓟 H) (𝓝 Q)) ∧
    (E = ∅ → Tendsto ψ (cobounded ℂ ⊓ 𝓟 (closure C)) (cobounded ℂ)) ∧
    (E = ∅ → Tendsto G (cobounded ℂ ⊓ 𝓟 H) (cobounded ℂ)) ∧
    ((E = ∅ ∧ s₂ = ⊤) ∨ (E = {αR s₂.toNNReal} ∧ s₂ ≠ ⊤))

theorem exists_isPocketData {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR)
    (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c) (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) :
    ∃ (E : Set ℂ) (ψ G : ℂ → ℂ) (k : ℝ), IsPocketData αR αL C c s₁ t₁ s₂ E ψ G k :=
  exists_pocketData hR hL hord hC hs hc hxC

/-- **The relative trace** of the traversal entered at `τ`: `u ↦ relPt E ψ k (γ (τ + u))`. -/
def relTrace (E : Set ℂ) (ψ : ℂ → ℂ) (k : ℝ) (γ : ℝ≥0 → ℂ) (τ : ℝ≥0) (u : ℝ) : ℂ :=
  relPt E ψ k (γ (τ + u.toNNReal))

/-- **`GB11Chart.exists_relCurve` with the pocket data given** (the same proof). -/
theorem exists_relCurve_of_data {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hγ : IsGeneratingTrace W' ⊤ γ) {αR αL : ℝ≥0 → ℂ} (hB : GB11.IsGB11Barrier αR αL γ)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) {c : Chart} (hc : IsComponentChart (range αR) (range αL) C c)
    (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)))
    (hE : ∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C)
    (hTr : ∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C)
    (hD : ∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C)
    {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ} (hpd : IsPocketData αR αL C c s₁ t₁ s₂ E ψ G k)
    {T : ℝ} (hT : T ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂)) :
    IsRelCurve c γ (entryTime γ αR s₂) T (relTrace E ψ k γ (entryTime γ αR s₂)) ∧
      ContinuousOn (relTrace E ψ k γ (entryTime γ αR s₂)) (Icc 0 T) ∧
      relTrace E ψ k γ (entryTime γ αR s₂) 0 = 0 ∧
      (∀ u ∈ Icc (0 : ℝ) T, fillH (relTrace E ψ k γ (entryTime γ αR s₂) '' Icc 0 u) =
        relHull W' c C (entryTime γ αR s₂) u) ∧
      StrictMonoOn (fun u => fillH (relTrace E ψ k γ (entryTime γ αR s₂) '' Icc 0 u)) (Icc 0 T) := by
  set τ := entryTime γ αR s₂ with hτ
  set σ := GB11.firstVisit γ (αR s₁) with hσ
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  have hRc : IsClosed (range αR) := isClosed_range_of_isCompleteSimpleFlow hB.1
  have hLc : IsClosed (range αL) := isClosed_range_of_isCompleteSimpleFlow hB.2.1
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents hRc hLc hC
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hC
  obtain ⟨z₀, hz₀, -, -, hCz⟩ := id hC
  have hCsub : C ⊆ H \ (range αR ∪ range αL) := hCz ▸ connectedComponentIn_subset _ _
  have hWc : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  -- the pocket coordinate and the boundary correspondence
  obtain ⟨hpc, hEcl, hE0, hψE, hGE, hψinf, hGinf, hcase⟩ := hpd
  obtain ⟨e, rR, rL, hbc⟩ : ∃ (e : ℝ → ℂ) (rR rL : ℝ → ℝ≥0), ChartBdryCorr αR αL c s₂ e rR rL := by
    by_cases hs₂ : s₂ = ⊤
    · exact exists_chartBdryCorr_of_unbounded hB.1 hB.2.1 hB.2.2.1 hC hs hs₂ hc hxC
    · exact exists_chartBdryCorr_of_bounded hB.1 hB.2.1 hB.2.2.1 hC hs hs₂ hc hxC
  -- relative times
  set tt : ℝ → ℝ≥0 := fun u => τ + u.toNNReal with htt
  have hhor : ∀ u ∈ Icc (0 : ℝ) T, u ∈ horizon (σ - τ) := fun u hu =>
    ⟨hu.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) hT.2⟩
  have htσ : ∀ u ∈ Icc (0 : ℝ) T, (tt u : ℝ≥0∞) < σ := fun u hu => coe_add_lt_of_mem_horizon (hhor u hu)
  have hτt : ∀ u : ℝ, τ ≤ tt u := fun u => le_self_add
  have httc : ∀ u ∈ Icc (0 : ℝ) T, ((tt u : ℝ≥0) : ℝ) = (τ : ℝ) + u := fun u hu => by
    rw [htt, NNReal.coe_add, Real.coe_toNNReal _ hu.1]
  -- the trace stays in the closed pocket without its exit
  have hdom : ∀ u ∈ Icc (0 : ℝ) T, γ (tt u) ∈ relDomBar C E (αR s₁) := by
    intro u hu
    by_cases h0 : γ (tt u) = 0
    · refine Or.inl ⟨h0, ?_⟩
      rcases hcase with ⟨hE', -⟩ | ⟨-, hs₂⟩
      · exact hE'
      · exact absurd h0 (trace_ne_zero_of_isBounded hγc (hs.entry hs₂).2.2 hD (hτt u) (htσ u hu))
    · refine Or.inr ⟨h0, hTr _ (hτt u) (htσ u hu) h0, fun hP => ?_⟩
      have : σ ≤ (tt u : ℝ≥0∞) := iInf₂_le (tt u) ⟨h0, hP⟩
      exact absurd (htσ u hu) (not_lt.2 this)
  -- the relative trace
  set ζ : ℝ → ℂ := fun u => relPt E ψ k (γ (tt u)) with hζ
  have hrel : IsRelCurve c γ τ T ζ := fun u hu =>
    ⟨relPt_mem_Hbar hpc (hdom u hu), tendsto_relInvC_relPt hpc hE0 hGE hGinf (hdom u hu)⟩
  have hζc : ContinuousOn ζ (Icc 0 T) :=
    (continuousOn_relPt hpc hEcl hψE hψinf).comp
      ((hγc.comp (continuous_const.add continuous_real_toNNReal)).continuousOn) hdom
  have hζ0 : ζ 0 = 0 := by
    have ht0 : tt 0 = τ := by simp [htt]
    show relPt E ψ k (γ (tt 0)) = 0
    rw [ht0]
    rcases hcase with ⟨-, hs₂⟩ | ⟨hEQ, hs₂⟩
    · have hτ0 : τ = 0 := by simp [hτ, entryTime, hs₂]
      rw [hτ0, hγ.1]
      simp [relPt]
    · have hQ0 : αR s₂.toNNReal ≠ 0 := fun h => hE0 (by rw [hEQ, h]; exact mem_singleton _)
      have hfin : GB11.firstVisit γ (αR s₂.toNNReal) < ⊤ :=
        firstVisit_lt_top_of_ne_zero hB.1.2.2.1 hB.2.2.2.2.2.1 hQ0
      obtain ⟨s₀, hs₀, hne, hp⟩ := exists_eq_firstVisit hγc hfin
      have hτs : τ = s₀ := by
        simp only [hτ, entryTime, hs₂, ↓reduceIte, ← hs₀, ENNReal.toNNReal_coe]
      rw [hτs]
      have hcond : γ s₀ = 0 ∨ -(γ s₀)⁻¹ ∈ E := Or.inr (by rw [hp, hEQ]; exact mem_singleton _)
      simp only [relPt, hcond, ↓reduceIte]
  -- the fill identity
  have hfill : ∀ u ∈ Icc (0 : ℝ) T, fillH (ζ '' Icc 0 u) = relHull W' c C τ u := by
    intro u hu
    set K := fwdHull (fun r : ℝ => W' r.toNNReal) ((τ : ℝ) + u) with hK
    have hKeq : K = fwdHull (fun r : ℝ => W' r.toNNReal) ((tt u : ℝ≥0) : ℝ) := by rw [httc u hu]
    have hKH : IsHPHull K := isHPHull_fwdHull hWc (by rw [← httc u hu]; exact NNReal.coe_nonneg _)
    show fillH (ζ '' Icc 0 u) = relMapC c '' (K ∩ relDom C)
    have hsubH : relMapC c '' (relDom C \ K) ⊆ H := by
      rintro _ ⟨w, hw, rfl⟩; exact relMapC_mem_H hc hw.1
    refine fillH_eq_of_frontier ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩; exact relMapC_mem_H hc hw.2
    · rw [hKeq]; exact isBounded_relHull hW' hW'0 hγ hB hc hxC (htσ u hu)
    · rw [H_diff_relHull_eq hc K, image_relDom_diff_eq hc K]
      have hD' : relDom C \ K = relDom C ∩ (H \ K) := by
        ext w
        exact ⟨fun h => ⟨h.1, relDom_subset_H hCH h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [hD']
      exact (continuousOn_relInvC hc hCo hCH).isOpen_inter_preimage QuantumZipper.isOpen_H
        ((isOpen_relDom hCo hCH).inter hKH.isOpen)
    · rw [H_diff_relHull_eq hc K, hKeq]
      exact (isPreconnected_relDom_diff_fwdHull hW' hW'0 hγ hB hs hc hCo hCH hxC hbc (hτt u)
        (htσ u hu)).image _ ((continuousOn_relMapC hc hCo hCH).mono sdiff_subset)
    · exact (isCompact_Icc.image_of_continuousOn (hζc.mono (Icc_subset_Icc_right hu.2))).isClosed
    · rintro z ⟨⟨v, hv, rfl⟩, hzH⟩
      have hvT : v ∈ Icc (0 : ℝ) T := ⟨hv.1, hv.2.trans hu.2⟩
      obtain ⟨-, hlim⟩ := hrel v hvT
      have := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hzH)
      have hval : relInvC c (ζ v) = γ (tt v) :=
        tendsto_nhds_unique ((continuousOn_relInvC hc hCo hCH) _ hzH).tendsto hlim
      have hw : γ (tt v) ∈ relDom C := hval ▸ relInvC_mem hc hzH
      have hwH := relDom_subset_H hCH hw
      have hvu : tt v ≤ tt u := add_le_add_right (Real.toNNReal_le_toNNReal hv.2) τ
      have hwK : γ (tt v) ∈ K := by rw [hKeq]; exact mem_fwdHull_of_isGeneratingTrace hγ hvu hwH
      exact ⟨γ (tt v), ⟨hwK, hw⟩, by rw [← hval, relMapC_relInvC hc hzH]⟩
    · rintro _ ⟨w, ⟨hwK, hwD⟩, rfl⟩ hcl
      have hwH := relDom_subset_H hCH hwD
      have hqH := relMapC_mem_H hc hwD
      rw [H_diff_relHull_eq hc K] at hcl
      have h1 := (((continuousOn_relInvC hc hCo hCH) _ hqH).mono hsubH).mem_closure_image hcl
      rw [relInvC_relMapC hc hwD] at h1
      have hwcl : w ∈ closure (H \ K) := closure_mono (by
        rintro _ ⟨_, ⟨w', hw', rfl⟩, rfl⟩
        rw [relInvC_relMapC hc hw'.1]
        exact ⟨relDom_subset_H hCH hw'.1, hw'.2⟩) h1
      rw [hKeq] at hwK hwcl
      obtain ⟨t', ht', hγt'⟩ := mem_image_of_mem_closure_compl hγ hwK hwcl hwH
      have hγt'0 : γ t' ≠ 0 := hγt' ▸ ne_zero_of_mem_H' hwH
      have hτt' : τ ≤ t' := by
        by_contra hlt
        push Not at hlt
        exact hE t' hlt hγt'0 (subset_closure (by rw [hγt']; exact hwD))
      set v : ℝ := (t' : ℝ) - τ with hvdef
      have hv0 : 0 ≤ v := sub_nonneg.2 (NNReal.coe_le_coe.2 hτt')
      have hvu : v ≤ u := by
        have := NNReal.coe_le_coe.2 ht'.2
        rw [httc u hu] at this
        linarith
      have htv : tt v = t' := by
        apply NNReal.eq
        rw [htt, NNReal.coe_add, Real.coe_toNNReal _ hv0, hvdef]
        ring
      obtain ⟨hζH, hlim⟩ := hrel v ⟨hv0, hvu.trans hu.2⟩
      rw [show τ + v.toNNReal = t' from htv, hγt'] at hlim
      refine ⟨v, ⟨hv0, hvu⟩, ?_⟩
      by_cases hζvH : ζ v ∈ H
      · have := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hζvH)
        have hval : relInvC c (ζ v) = w :=
          tendsto_nhds_unique ((continuousOn_relInvC hc hCo hCH) _ hζvH).tendsto hlim
        rw [← hval, relMapC_relInvC hc hζvH]
      · exfalso
        have him : (ζ v).im = 0 := le_antisymm (not_lt.1 hζvH) hζH
        have hx : ζ v = (((ζ v).re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
        rw [hx] at hlim
        have := FiniteEndpoint.neBot_nhdsWithin_H (z := (((ζ v).re : ℝ) : ℂ)) (by simp)
        have hwe : w = e (ζ v).re := tendsto_nhds_unique hlim (hbc.1 _)
        have hwC : -w⁻¹ ∈ C := hwD
        obtain ⟨-, hposL, -, hnegR, -, he0top, he0⟩ := hbc
        rcases lt_trichotomy (ζ v).re 0 with hx0 | hx0 | hx0
        · obtain ⟨-, he⟩ := hnegR _ hx0
          rw [hwe, he, negInv_negInv'] at hwC
          exact (hCsub hwC).2 (Or.inl ⟨_, rfl⟩)
        · rw [hx0] at hwe
          by_cases hs₂ : s₂ = ⊤
          · rw [he0top hs₂] at hwe
            exact ne_zero_of_mem_H' hwH hwe
          · rw [he0 hs₂] at hwe
            rw [hwe, negInv_negInv'] at hwC
            exact (hCsub hwC).2 (Or.inl ⟨_, rfl⟩)
        · obtain ⟨-, he⟩ := hposL _ hx0
          rw [hwe, he, negInv_negInv'] at hwC
          exact (hCsub hwC).2 (Or.inr ⟨_, rfl⟩)
  -- strict growth
  have hmono : StrictMonoOn (fun u => fillH (ζ '' Icc 0 u)) (Icc 0 T) := by
    intro u hu u' hu' huu'
    show fillH (ζ '' Icc 0 u) < fillH (ζ '' Icc 0 u')
    rw [hfill u hu, hfill u' hu']
    have hsub : relHull W' c C τ u ⊆ relHull W' c C τ u' :=
      image_mono (inter_subset_inter_left _ (QuantumZipper.fwdHull_mono.1 (by linarith)))
    refine ⟨hsub, fun h => ?_⟩
    have hab : tt u < tt u' :=
      add_lt_add_right ((Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt hu.1 huu')).2 huu') τ
    obtain ⟨w, hwD, hwb, hwa⟩ := exists_mem_relDom_fwdHull_sdiff hW' hW'0 hγ hCo hCH hD (hτt u) hab (htσ u' hu')
    have hmem : relMapC c w ∈ relHull W' c C τ u' := ⟨w, ⟨by rw [← httc u' hu']; exact hwb, hwD⟩, rfl⟩
    obtain ⟨w', ⟨hw'K, hw'D⟩, he⟩ := h hmem
    have : w' = w := injOn_relMapC hc hw'D hwD he
    rw [this, ← httc u hu] at hw'K
    exact hwa hw'K
  exact ⟨hrel, hζc, hζ0, hfill, hmono⟩

section Drive

variable {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {αR αL : ℝ≥0 → ℂ} {C : Set ℂ} {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞} {c : Chart}
  {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ}

/-- **The fills of the relative trace are Loewner hulls on every `[0, T]`, `0 < T < σ − τ`** (Yuan's theorem with the
proved continuous own futures `GB11Chart.gb11RelOwnFutureStatement`). -/
theorem exists_loewner_relTrace (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hno : GB10.NoSimpleArcInterval γ ⊤) (hB : GB11.IsGB11Barrier αR αL γ) (hP : WalkPocketShape αR αL)
    (hC : C ∈ betweenComponents (range αR) (range αL)) (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂)
    (hc : IsComponentChart (range αR) (range αL) C c) (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)))
    (hE : ∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C)
    (hTr : ∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C)
    (hD : ∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C)
    (hpd : IsPocketData αR αL C c s₁ t₁ s₂ E ψ G k)
    {T : ℝ} (hT : T ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂)) (hT0 : 0 < T) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 T) ∧
      ContinuousOn σ (Icc 0 T) ∧
      ∀ u ∈ Icc (0 : ℝ) T, fwdHull W (σ u) = fillH (relTrace E ψ k γ (entryTime γ αR s₂) '' Icc 0 u) := by
  obtain ⟨hrel, hζc, hζ0, -, hmono⟩ := exists_relCurve_of_data hW' hW'0 hγ hB hC hs hc hxC hE hTr hD hpd hT
  have hii := gb11RelOwnFutureStatement W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
    T hT hT0 _ hrel hζc hζ0
  exact YuanCharacterisation.exists_loewner_of_hasContinuousOwnFuture hT0 hζc hζ0 (fun u hu => (hrel u hu).1)
    hmono hii

/-- **The reparametrized relative trace is a driven curve** for every finite relative horizon `0 < L < σ − τ`. -/
theorem isDrivenCurve_relTrace (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hno : GB10.NoSimpleArcInterval γ ⊤) (hB : GB11.IsGB11Barrier αR αL γ) (hP : WalkPocketShape αR αL)
    (hC : C ∈ betweenComponents (range αR) (range αL)) (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂)
    (hc : IsComponentChart (range αR) (range αL) C c) (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)))
    (hE : ∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C)
    (hTr : ∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C)
    (hD : ∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C)
    (hpd : IsPocketData αR αL C c s₁ t₁ s₂ E ψ G k)
    {L : ℝ} (hL : L ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂)) (hL0 : 0 < L) :
    IsDrivenCurve (relCurve (relTrace E ψ k γ (entryTime γ αR s₂)) L) := by
  obtain ⟨-, hζc, hζ0, -, -⟩ := exists_relCurve_of_data hW' hW'0 hγ hB hC hs hc hxC hE hTr hD hpd hL
  refine isDrivenCurve_relCurve hL0 (hζc.mono Ico_subset_Icc_self) hζ0 fun S' hS' hS'L => ?_
  exact exists_loewner_relTrace hW' hW'0 hγ hno hB hP hC hs hc hxC hE hTr hD hpd
    (mem_horizon_of_le hL hS'.le hS'L.le) hS'

end Drive

end InteractingSLE.Theorem14.GW4Fix
