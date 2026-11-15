/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdGapWire

/-!
# Theorem 1.5's leaf 3: enclosure along the first continuation

Packet PROVE-T15-ORDDET5. The mirror of `OrdGap.subset_fillH_of_inactive_snd` and `OrdGap.ae_ord_or_encl_snd` for the
first continuation (the path `η₁` continued from `u` to `u + t`, read in the stop-line chart through the shift `τ₀`,
as in PROVE-T15-ORDDET3's `OrdDet.later_tip_mem_closure_activeDomain_fst`):

* **`subset_fillH_of_inactive_fst`** (deterministic): if the second tip `η₂(r)` is not adherent to the later active
  domain, the second prefix lies in the filling of the later first prefix;
* **`ae_ord_or_encl_fst`** (the cover): almost surely, at a deterministic line before the first continuation's first
  new contact with the second prefix, the later pair `(u + t, r)` is ordinary, or the second prefix is enclosed — the
  pair is in the enclosed event `enclSet η₂ η₁ ζ₂ ζ₁ d''` of the **swapped** retained data `d''` (the paths exchanged,
  chart at the first tip). There the mean word is `exists_enclWord` for the exchanged flow lines.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

universe u

namespace InteractingSLE.RLC.OrdGap

open Supp7 Restart

open MartChar.RealFlow in
/-- **An inactive second tip along the first continuation means the second prefix is enclosed** (the mirror of
`subset_fillH_of_inactive_snd`, with the first continuation's chart path `γ` read through the shift `τ₀`). -/
theorem subset_fillH_of_inactive_fst {Ω : Type u} [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood)
    {t : ℝ≥0} {ω : Ω} (hω : ω ∈ d.E) {L R : ℝ}
    (hzone : IsZoneInterval (d.inv ω) (d.η₂ ω '' Icc 0 d.r) (d.η₁ ω '' Icc 0 d.u) L R 0 (d.η₂ ω d.r))
    {τ₀ : ℝ} {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0} (hg : IsGeneratingTrace W ζc γ)
    (hWc : Continuous W) (hW0 : W 0 = 0) (hQ : (Q : ℝ≥0∞) < ζc)
    (himg : (fun s => d.inv ω (γ s + τ₀)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t))
    (htip : d.inv ω (γ Q + τ₀) = d.η₁ ω (d.u + t))
    (hnc : ∀ s ∈ Icc d.u (d.u + t), d.η₁ ω s ∉ d.η₂ ω '' Icc 0 d.r)
    (hin : d.η₂ ω d.r ∉ closure (activeDomain (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r)) :
    d.η₂ ω '' Icc 0 d.r ∩ H ⊆ fillH (d.η₁ ω '' Icc 0 (d.u + t)) := by
  obtain ⟨hLτ, hτR, hτ, hS, hZ⟩ := hzone
  set ψ := d.inv ω with hψ
  have hG : ω ∈ d.G := RetData.E₀_subset_G (RetData.E_subset_E₀ hω)
  have hgood := hd.good ω hG
  have h0₂ : (d.η₂ ω 0).im = 0 := hgood.2.2.2.2.2.1
  have hC := (hd.isRetChart hω).2
  have hKc := hd.isCompact_K ω
  rw [RetData.K_of_mem hω] at hKc
  have hDC : IsDomChart (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r) (d.fwd ω) ψ := hC.isDomChart h0₂ hKc.isClosed
  have hA₁c : IsCompact (d.η₁ ω '' Icc 0 d.u) := isCompact_Icc.image_of_continuousOn hgood.1
  have hA₂c : IsCompact (d.η₂ ω '' Icc 0 d.r) := isCompact_Icc.image_of_continuousOn hgood.2.1
  -- the chart path lies in `ℍ̄`
  have hγH : ∀ s ∈ Icc 0 Q, γ s ∈ Hbar := by
    intro s hs
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · rw [← h0, hg.1]
      show (0 : ℝ) ≤ (0 : ℂ).im
      simp
    · have h1 := IsGeneratingTrace.mem_closure_of_lt hg hWc.continuousOn hW0 h0
        ((ENNReal.coe_le_coe.2 hs.2).trans hQ.le)
      have h2 : closure (H \ fillH (γ '' Icc 0 0)) ⊆ Hbar := by
        rw [← closure_H]
        exact closure_mono sdiff_subset
      exact h2 h1
  have hγc : ContinuousOn γ (Icc 0 Q) := hg.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hQ.le
  set Gs : Set ℂ := (fun z : ℂ => z + τ₀) '' (γ '' Icc 0 Q) with hGs
  have hGc : IsCompact Gs := (isCompact_Icc.image_of_continuousOn hγc).image (continuous_id.add continuous_const)
  -- the new piece
  have hnewc : IsCompact (d.η₁ ω '' Icc d.u (d.u + t)) := by
    rw [← himg]
    refine isCompact_Icc.image_of_continuousOn (hC.continuousOn_inv.comp (hγc.add continuousOn_const) ?_)
    intro s hs
    show (0 : ℝ) ≤ (γ s + τ₀).im
    simpa using (show (0 : ℝ) ≤ (γ s).im from hγH s hs)
  have hsplit : d.η₁ ω '' Icc 0 (d.u + t) = d.η₁ ω '' Icc 0 d.u ∪ d.η₁ ω '' Icc d.u (d.u + t) := by
    rw [← image_union, Icc_union_Icc_eq_Icc zero_le (le_add_right le_rfl)]
  have hA₁'c : IsCompact (d.η₁ ω '' Icc 0 (d.u + t)) := by rw [hsplit]; exact hA₁c.union hnewc
  have hX : prefixSet (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r = d.η₁ ω '' Icc 0 (d.u + t) ∪ d.η₂ ω '' Icc 0 d.r := rfl
  have hXc : IsClosed (prefixSet (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r) := by
    rw [hX]; exact (hA₁'c.union hA₂c).isClosed
  have hD'eq := activeDomain_eq hXc
  rw [hD'eq, hX, union_comm] at hin
  -- the later active domain contains the chart image of the complement of the hull of `G`
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  have hQr : (0 : ℝ) ≤ Q := Q.coe_nonneg
  obtain ⟨Wg, γg, T', hQT', hWgc, hWg0, hγg, hWeq, hγeq⟩ :=
    Sec7.ReverseArc.exists_global_model hg hWc.continuousOn hW0 hQ
  have hΦeq : fwdMapInv w' Q = fwdMapInv Wg Q := fwdMapInv_eq_of_eqOn hQr hQT' fun r hr => (hWeq r hr).symm
  have himgg : γg '' Icc 0 (Q : ℝ) = γ '' Icc 0 Q := by
    rw [image_congr (fun r hr => hγeq r ⟨hr.1, hr.2.trans hQT'.le⟩), image_toNNReal_Icc γ hQr,
      Real.toNNReal_coe]
  have hK : fwdHull Wg Q = fillH (γ '' Icc 0 Q) := by rw [hγg.2.2 Q hQr, himgg]
  have hlater := (OrdDet.later_tip_mem_closure_activeDomain_fst hd hω hg hWc hW0 hQ himg htip).1
  rw [hD'eq, hX] at hlater
  have hD' : ψ '' (H \ fillH Gs) ⊆ H \ fillH (d.η₂ ω '' Icc 0 d.r ∪ d.η₁ ω '' Icc 0 (d.u + t)) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z - τ₀ ∈ H \ fwdHull Wg Q := by
      rw [hK]
      refine ⟨show 0 < (z - τ₀).im by simpa using (show 0 < z.im from hz.1), fun h => hz.2 ?_⟩
      rw [hGs, Restart.fillH_image_add_real]
      exact ⟨z - τ₀, h, by ring⟩
    have hfz : fwdMap Wg Q (z - τ₀) ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hWgc hQr hz'
    have he : extendFrom H (fwdMapInv w' Q) (fwdMap Wg Q (z - τ₀)) + τ₀ = z := by
      rw [hΦeq, ZhanGT4.extendFrom_eq_fwdMapInv hWgc hWg0 hQr hfz,
        QuantumZipper.RS.fwdMapInv_fwdMap hWgc hWg0 hQr hz']
      ring
    have h1 : d.inv ω (extendFrom H (fwdMapInv w' Q) (fwdMap Wg Q (z - τ₀)) + τ₀) ∈
        H \ fillH (d.η₁ ω '' Icc 0 (d.u + t) ∪ d.η₂ ω '' Icc 0 d.r) := hlater ⟨fwdMap Wg Q (z - τ₀), hfz, rfl⟩
    rw [he, union_comm] at h1
    exact h1
  have hτ' : ψ ((0 : ℝ) : ℂ) = d.η₂ ω d.r := hτ
  refine subset_fillH_of_inactive hDC hA₂c hA₁'c hGc subset_union_right ?_ (fun z hz => ?_) hD' hLτ hτR hS
    (fun w hw1 hw2 => hZ w hw1 fun h => hw2 (by rw [hsplit]; exact Or.inl h)) (by rw [hτ']; exact hin)
  · rintro z (hz | hz)
    · exact Or.inr (by rw [hsplit]; exact Or.inl hz)
    · exact Or.inl hz
  · obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hz
    have hmem : ψ (γ s + τ₀) ∈ d.η₁ ω '' Icc d.u (d.u + t) := by rw [← himg]; exact ⟨s, hs, rfl⟩
    refine ⟨by rw [hsplit]; exact Or.inr hmem, ?_⟩
    obtain ⟨s', hs', he⟩ := hmem
    rw [← he]
    exact hnc s' hs'

section Cover

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The cover for the first continuation**: almost surely, at a deterministic line `t`, an ordinary pair `(u, r)`
continued along the first path to `u + t` (before its lifetime, without a new contact with the second prefix, along a
chart path read through the shift `τ₀`) is at the later line either ordinary or **enclosed with the roles exchanged**:
the sample is in `enclSet η₂ η₁ ζ₂ ζ₁ d''` for the swapped retained data `d''` (first path `η₂` cut at `r`, second path
`η₁` cut at `u + t`, chart at the first tip). -/
theorem ae_ord_or_encl_fst (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d d'' : RetData Ω} (hd : d.IsMeasGood) (hd'' : d''.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag'' : ∀ᵐ ω ∂P, (d''.u : ℝ≥0∞) < ζ₂ ω → (d''.r : ℝ≥0∞) < ζ₁ ω → ω ∈ d''.G ∧
      (∀ s ≤ d''.u, d''.η₁ ω s = η₂ ω s) ∧ ∀ t ≤ d''.r, d''.η₂ ω t = η₁ ω t)
    {t : ℝ≥0} (s₁ : d''.η₁ = d.η₂) (s₂ : d''.η₂ = d.η₁) (su : d''.u = d.r) (sr : d''.r = d.u + t) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → (∀ s, d.u < s → s ≤ d.u + t → η₁ ω s ∉ η₂ ω '' Icc 0 d.r) →
      ∀ (τ₀ : ℝ) (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ →
        Continuous W → W 0 = 0 → (Q : ℝ≥0∞) < ζc →
        (fun s => d.inv ω (γ s + τ₀)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t) →
        d.inv ω (γ Q + τ₀) = d.η₁ ω (d.u + t) →
        IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) (d.u + t) (η₂ ω) (ζ₂ ω) d.r ∨ ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ d'' := by
  have hHae : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → η₁ ω (d.u + t) ∈ H := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ d.u + t) with h0 | hpos
    · refine Eventually.of_forall fun ω hord _ => ?_
      have hu0 : d.u = 0 := le_antisymm (by rw [h0]; exact le_add_right le_rfl) zero_le
      have hut : d.u + t = d.u := by rw [← h0, hu0]
      rw [hut]
      exact hord.2.2.1
    · filter_upwards [OrdLate.ae_mem_H_at hκ hκ4.le hη₁ (d.u + t) hpos] with ω hH _ hlt
      exact hH hlt
  filter_upwards [OrdLate.ae_isOrdinaryRetainedPair_later_fst_at hκ hκ4 hb hx hθ hh hη₁ hη₂ d.u d.r t,
    ae_isZoneInterval hκ hκ4 hx hη₁ hη₂ hd hag, hag, hag'', hHae] with ω hlate hzone hagω hag''ω hHω
  intro hord hlt hnc τ₀ W γ ζc Q hg hWc hW0 hQ himg htip
  obtain ⟨-, -, a₂⟩ := hagω hord.1 hord.2.1
  obtain ⟨hE, -, ⟨L, R, hZ⟩⟩ := hzone hord
  have hu'' : (d''.u : ℝ≥0∞) < ζ₂ ω := by rw [su]; exact hord.2.1
  have hr'' : (d''.r : ℝ≥0∞) < ζ₁ ω := by rw [sr]; exact hlt
  obtain ⟨hG'', -, b₂⟩ := hag''ω hu'' hr''
  have e₁ : ∀ s ≤ d.u + t, d.η₁ ω s = η₁ ω s := fun s hs => by
    have := b₂ s (by rw [sr]; exact hs)
    rwa [s₂] at this
  have i₁ : d.η₁ ω '' Icc 0 (d.u + t) = η₁ ω '' Icc 0 (d.u + t) := image_congr fun s hs => e₁ s hs.2
  have i₂ : d.η₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r := image_congr fun s hs => a₂ s hs.2
  have hDcongr : activeDomain (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r = activeDomain (η₁ ω) (d.u + t) (η₂ ω) d.r :=
    activeDomain_congr_Icc (fun s hs => e₁ s hs.2) fun s hs => a₂ s hs.2
  have hnc' : ∀ s ∈ Icc d.u (d.u + t), d.η₁ ω s ∉ d.η₂ ω '' Icc 0 d.r := by
    intro s hs
    rw [i₂, e₁ s hs.2]
    rcases eq_or_lt_of_le hs.1 with hus | hus
    · rw [← hus]; exact hord.2.2.2.2.2.1
    · exact hnc s hus hs.2
  have hact₁ := (OrdDet.later_tip_mem_closure_activeDomain_fst hd hE hg hWc hW0 hQ himg htip).2
  rw [hDcongr, e₁ _ le_rfl] at hact₁
  by_cases hact : η₂ ω d.r ∈ closure (activeDomain (η₁ ω) (d.u + t) (η₂ ω) d.r)
  · exact Or.inl (hlate hord hlt hnc hact₁ hact)
  · have hin : d.η₂ ω d.r ∉ closure (activeDomain (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r) := by
      rw [hDcongr, a₂ d.r le_rfl]; exact hact
    have hencl := subset_fillH_of_inactive_fst hd hE hZ hg hWc hW0 hQ himg htip hnc' hin
    rw [i₁, i₂] at hencl
    -- the swapped chart event
    have hH : d''.η₂ ω d''.r ∈ H := by rw [s₂, sr, e₁ _ le_rfl]; exact hHω hord hlt
    have hoff : d''.η₂ ω d''.r ∉ d''.η₁ ω '' Icc 0 d''.u := by
      rw [s₂, s₁, sr, su]; exact hnc' _ ⟨le_add_right le_rfl, le_rfl⟩
    have hE₀ : ω ∈ d''.E₀ := ⟨⟨hG'', hH⟩, hoff⟩
    have hE'' : ω ∈ d''.E := by
      refine ⟨hE₀, ?_⟩
      have hKc : IsClosed (prefixSet (d''.η₁ ω) d''.u (d''.η₂ ω) d''.r) := by
        have h := (hd''.isCompact_KOf (fun _ h => h.1.1) ω (F := d''.E₀)).isClosed
        rwa [RetData.KOf_of_mem hE₀] at h
      show d''.η₂ ω d''.r ∈ closure (H \ fillH (d''.KOf d''.E₀ ω))
      rw [RetData.KOf_of_mem hE₀, ← activeDomain_eq hKc, s₁, s₂, su, sr, activeDomain_comm]
      exact (OrdDet.later_tip_mem_closure_activeDomain_fst hd hE hg hWc hW0 hQ himg htip).2
    refine Or.inr ⟨hu'', hr'', hE'', ?_⟩
    rw [su, sr]
    exact hencl

end Cover

end InteractingSLE.RLC.OrdGap
