/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdGapEncl
import InteractingSLE.Spec.Supplement.Aux85Junction
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj
import InteractingSLE.Spec.Supplement.OrdSlitSide

/-!
# Theorem 1.5's leaf 3: the zone interval of a prefix at an ordinary pair, and enclosure of the fixed prefix

Packet PROVE-T15-ORDDET5. At an ordinary retained pair, the chart preimage of the exposed part of each prefix is
contained in a closed interval of the real chart line that contains the prefix's tip chart point and is mapped into the
prefix (`IsZoneInterval`). This is read off Lemma 7.6's zones (`Sec7.Lemma76G.IsSetting`, disjoint prefixes) and
Aux. lemma 85's touching zones (`RetTouch.IsTouchZones`, `Aux85.retTouchZonesStatement`):

* `isZoneInterval_fst_of_setting`, `isZoneInterval_snd_of_setting` (disjoint prefixes);
* `isZoneInterval_fst_of_touch`, `isZoneInterval_snd_of_touch` (meeting prefixes);
* **`ae_isZoneInterval`**: almost surely at an ordinary pair, both zone intervals in the retained chart.

With the planar lemma `OrdGap.subset_fillH_of_inactive`:

* **`subset_fillH_of_inactive_snd`**: along a chart path of the second continuation (as in PROVE-T15-ORDDET2's
  `OrdDet.later_tip_mem_closure_activeDomain`), without a new contact with the first prefix, if the first tip is not
  adherent to the later active domain, then the first prefix lies in the filling of the later second prefix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

universe u

namespace InteractingSLE.RLC.OrdGap

open Supp7 Sec7 Sec7.Lemma76G RetTouch

/-- **A zone interval of a prefix in a chart**: `[L, R]` contains the chart point `τ` of the tip `p`, is mapped into
the prefix `A`, and contains every real chart point mapped to a point of `A` off the other prefix `B`. -/
def IsZoneInterval (ψ : ℂ → ℂ) (A B : Set ℂ) (L R τ : ℝ) (p : ℂ) : Prop :=
  L ≤ τ ∧ τ ≤ R ∧ ψ τ = p ∧ (∀ w ∈ Icc L R, ψ w ∈ A) ∧ ∀ w : ℝ, ψ w ∈ A → ψ w ∉ B → w ∈ Icc L R

/-- A closed set containing the images of an open interval and of one of its points contains the image of its
closure. -/
theorem forall_Icc_of_Ioo {ψ : ℂ → ℂ} (hψ : ContinuousOn ψ Hbar) {A : Set ℂ} (hA : IsClosed A) {L R τ : ℝ}
    (hLτ : L ≤ τ) (hτR : τ ≤ R) (hτ : ψ τ ∈ A) (hIoo : ∀ w ∈ Ioo L R, ψ w ∈ A) :
    ∀ w ∈ Icc L R, ψ w ∈ A := by
  intro w hw
  rcases eq_or_lt_of_le (hLτ.trans hτR) with hLR | hLR
  · have hwτ : w = τ := by
      have := hw.1; have := hw.2
      linarith
    rw [hwτ]
    exact hτ
  · have hc : Continuous fun x : ℝ => ψ x :=
      hψ.comp_continuous Complex.continuous_ofReal fun x => show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp
    have hpre : IsClosed ((fun x : ℝ => ψ x) ⁻¹' A) := hA.preimage hc
    have hsub : closure (Ioo L R) ⊆ (fun x : ℝ => ψ x) ⁻¹' A := hpre.closure_subset_iff.2 hIoo
    rw [closure_Ioo hLR.ne] at hsub
    exact hsub hw

/-! ### Disjoint prefixes: Lemma 7.6's zones -/

section Setting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- The first prefix's zone interval `[L₁, R₁]` at a disjoint pair. -/
theorem isZoneInterval_fst_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) :
    IsZoneInterval ψ (α '' Icc 0 a) (β '' Icc 0 b) (zoneData φ α a β b).L₁ (zoneData φ α a β b).R₁
      (zoneData φ α a β b).M₁ (α a) := by
  have hz := hs.zoneData_good
  have htip : ψ (zoneData φ α a β b).M₁ = α a := hs.chartPt_tip₁.2.1
  refine ⟨hz.L₁_le, hz.M₁_le, htip, forall_Icc_of_Ioo hs.ψc hs.isCompact₁.isClosed hz.L₁_le hz.M₁_le ?_
    (fun w h => hs.mem₁_of_mem_Ioo h.1 h.2), fun w hw _ => ⟨hs.L₁_le_of_mem₁ hw, hs.le_R₁_of_mem₁ hw⟩⟩
  rw [htip]
  exact ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩

/-- The second prefix's zone interval `[L₂, R₂]` at a disjoint pair (the second tip at the chart point `0`). -/
theorem isZoneInterval_snd_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) :
    IsZoneInterval ψ (β '' Icc 0 b) (α '' Icc 0 a) (zoneData φ α a β b).L₂ (zoneData φ α a β b).R₂ 0 (β b) := by
  have hz := hs.zoneData_good
  have h0 : ψ ((0 : ℝ) : ℂ) = β b := by rw [ofReal_zero]; exact hs.ψ0
  have hL0 : (zoneData φ α a β b).L₂ ≤ 0 := hz.L₂_le
  have h0R : (0 : ℝ) ≤ (zoneData φ α a β b).R₂ := hz.M₂_le
  refine ⟨hL0, h0R, h0, forall_Icc_of_Ioo hs.ψc hs.isCompact₂.isClosed hL0 h0R ?_
    (fun w h => hs.mem₂_of_mem_Ioo h.1 h.2), fun w hw _ => ⟨hs.L₂_le_of_mem₂ hw, hs.le_R₂_of_mem₂ hw⟩⟩
  rw [h0]
  exact ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩

end Setting

/-! ### Meeting prefixes: Aux. lemma 85's zones -/

section Touch

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {z : ZW}

/-- A chart point left of `L₂` or right of `R₁` is mapped off both prefixes. -/
theorem touch_notMem_of_out (ht : IsTouchZones α a β b ψ z) {w : ℝ} (hw : w < z.L₂ ∨ z.R₁ < w) :
    ψ w ∉ α '' Icc 0 a ∪ β '' Icc 0 b := by
  rcases hw with hw | hw
  · obtain ⟨him, hre, -⟩ := ht.zone₀ w hw
    have he : ψ w = (((ψ w).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [he]
    exact ht.notMem_zone _ (Or.inl hre)
  · obtain ⟨him, hre, -⟩ := ht.zone₂ w hw
    have he : ψ w = (((ψ w).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [he]
    exact ht.notMem_zone _ (Or.inr hre)

/-- The open first-prefix zone `(R₂, R₁)` is mapped into the first prefix. -/
theorem touch_mem₁_of_mem_Ioo (ht : IsTouchZones α a β b ψ z) {w : ℝ} (h1 : z.R₂ < w) (h2 : w < z.R₁) :
    ψ w ∈ α '' Icc 0 a := by
  rcases lt_trichotomy w z.M₁ with h | rfl | h
  · exact (ht.side₃ w (ht.junction ▸ h1) h).1
  · rw [ht.tip₁]; exact ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩
  · exact ht.side₄ w h h2

/-- The first prefix's zone interval `[R₂, R₁]` at a touching pair (`R₂` is the junction). -/
theorem isZoneInterval_fst_of_touch (ht : IsTouchZones α a β b ψ z) (hψ : ContinuousOn ψ Hbar)
    (hA : IsClosed (α '' Icc 0 a)) : IsZoneInterval ψ (α '' Icc 0 a) (β '' Icc 0 b) z.R₂ z.R₁ z.M₁ (α a) := by
  have hz := ht.good
  have hRM : z.R₂ ≤ z.M₁ := ht.R₂_lt_M₁.le
  refine ⟨hRM, hz.M₁_le, ht.tip₁, forall_Icc_of_Ioo hψ hA hRM hz.M₁_le (by rw [ht.tip₁]; exact
    ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩) fun w h => touch_mem₁_of_mem_Ioo ht h.1 h.2, fun w hwA hwB => ?_⟩
  by_contra hw
  rw [mem_Icc, not_and_or, not_le, not_le] at hw
  rcases hw with hw | hw
  · rcases lt_trichotomy w z.L₂ with h | rfl | h
    · exact touch_notMem_of_out ht (Or.inl h) (Or.inl hwA)
    · exact hwB ht.L₂_mem
    · exact hwB (ht.side₂ w h hw)
  · exact touch_notMem_of_out ht (Or.inr hw) (Or.inl hwA)

/-- The second prefix's zone interval `[L₂, R₂]` at a touching pair. -/
theorem isZoneInterval_snd_of_touch (ht : IsTouchZones α a β b ψ z) (hψ : ContinuousOn ψ Hbar)
    (hB : IsClosed (β '' Icc 0 b)) : IsZoneInterval ψ (β '' Icc 0 b) (α '' Icc 0 a) z.L₂ z.R₂ 0 (β b) := by
  have hz := ht.good
  have h0 : ψ ((0 : ℝ) : ℂ) = β b := by rw [ofReal_zero]; exact ht.tip₂
  refine ⟨ht.L₂_le_zero, ht.zero_lt_R₂.le, h0, forall_Icc_of_Ioo hψ hB ht.L₂_le_zero ht.zero_lt_R₂.le
    (by rw [h0]; exact ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩) fun w h => ht.side₂ w h.1 h.2, fun w hwB hwA => ?_⟩
  by_contra hw
  rw [mem_Icc, not_and_or, not_le, not_le] at hw
  rcases hw with hw | hw
  · exact touch_notMem_of_out ht (Or.inl hw) (Or.inr hwB)
  · rcases lt_or_ge w z.R₁ with h | h
    · exact hwA (touch_mem₁_of_mem_Ioo ht hw h)
    · rcases eq_or_lt_of_le h with rfl | h
      · exact hwA ht.R₁_mem
      · exact touch_notMem_of_out ht (Or.inr h) (Or.inr hwB)

end Touch

/-! ### Almost surely at an ordinary pair -/

section AE

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Both zone intervals in the retained chart, almost surely at an ordinary pair** (Lemma 7.6's zones for disjoint
prefixes, Aux. lemma 85's touching zones otherwise). -/
theorem ae_isZoneInterval (hκ : 0 < κ) (hκ4 : κ < 4) (hx : x₂ ≤ x₁)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ω ∈ d.E ∧
      (∃ L R τ : ℝ, IsZoneInterval (d.inv ω) (d.η₁ ω '' Icc 0 d.u) (d.η₂ ω '' Icc 0 d.r) L R τ (d.η₁ ω d.u)) ∧
      ∃ L R : ℝ, IsZoneInterval (d.inv ω) (d.η₂ ω '' Icc 0 d.r) (d.η₁ ω '' Icc 0 d.u) L R 0 (d.η₂ ω d.r) := by
  filter_upwards [hag, Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hagω hp₁ hp₂ hord
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  have hE := hd.mem_E_of_ordinary hG a₁ a₂ hord
  have hC : IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
    (Sec7.Lemma76F.isRetChart_congr a₁ a₂).1 (hd.isRetChart hE).2
  have i₁ : d.η₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := image_congr fun s hs => a₁ s hs.2
  have i₂ : d.η₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r := image_congr fun t ht => a₂ t ht.2
  rw [i₁, i₂, a₁ d.u le_rfl, a₂ d.r le_rfl]
  refine ⟨hE, ?_⟩
  by_cases hdis : Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)
  · have hx' : x₂ < x₁ := by
      refine lt_of_le_of_ne hx fun he => Set.disjoint_left.1 hdis ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
        ⟨0, ⟨le_rfl, zero_le⟩, ?_⟩
      rw [Sec7.IsPathGood.zero hp₁, Sec7.IsPathGood.zero hp₂, he]
    have hs : IsSetting (η₁ ω) (ζ₁ ω) x₁ d.u (η₂ ω) (ζ₂ ω) x₂ d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
      ⟨hp₁, hp₂, hx', isDisjointPair_of_ordinary hord hdis, hC⟩
    exact ⟨⟨_, _, _, isZoneInterval_fst_of_setting hs⟩, ⟨_, _, isZoneInterval_snd_of_setting hs⟩⟩
  · have ht := Aux85.retTouchZonesStatement (η₁ ω) (η₂ ω) (ζ₁ ω) (ζ₂ ω) x₁ x₂ d.u d.r (d.fwd ω) (d.inv ω)
      (d.lift ω) hp₁ hp₂ hx hord hdis hC
    have hA₁ := (Sec7.IsPathGood.isCompact_image hp₁ hord.1.le).isClosed
    have hA₂ := (Sec7.IsPathGood.isCompact_image hp₂ hord.2.1.le).isClosed
    exact ⟨⟨_, _, _, isZoneInterval_fst_of_touch ht hC.continuousOn_inv hA₁⟩,
      ⟨_, _, isZoneInterval_snd_of_touch ht hC.continuousOn_inv hA₂⟩⟩

end AE

/-! ### Enclosure along the second continuation -/

open Restart MartChar.RealFlow in
/-- **An inactive first tip along the second continuation means the first prefix is enclosed.** With the stop-line
chart `ψ = d.inv` and a chart path `γ` of the second continuation up to the line (`ψ ∘ γ` runs through the new piece
`η₂[r, r + t]` and ends at the later tip, as in `OrdDet.later_tip_mem_closure_activeDomain`), the zone interval of the
first prefix, and no contact of the new piece with the first prefix: if the first tip `η₁(u)` is not adherent to the
later active domain, then `η₁[0, u] ∩ ℍ ⊆ fill(η₂[0, r + t])`. -/
theorem subset_fillH_of_inactive_snd {Ω : Type u} [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood)
    {t : ℝ≥0} {ω : Ω} (hω : ω ∈ d.E) {L R τ : ℝ}
    (hzone : IsZoneInterval (d.inv ω) (d.η₁ ω '' Icc 0 d.u) (d.η₂ ω '' Icc 0 d.r) L R τ (d.η₁ ω d.u))
    {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0} (hg : IsGeneratingTrace W ζc γ) (hWc : Continuous W)
    (hW0 : W 0 = 0) (hQ : (Q : ℝ≥0∞) < ζc)
    (himg : (fun s => d.inv ω (γ s)) '' Icc 0 Q = d.η₂ ω '' Icc d.r (d.r + t))
    (htip : d.inv ω (γ Q) = d.η₂ ω (d.r + t))
    (hnc : ∀ s ∈ Icc d.r (d.r + t), d.η₂ ω s ∉ d.η₁ ω '' Icc 0 d.u)
    (hin : d.η₁ ω d.u ∉ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) (d.r + t))) :
    d.η₁ ω '' Icc 0 d.u ∩ H ⊆ fillH (d.η₂ ω '' Icc 0 (d.r + t)) := by
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
  set Gs : Set ℂ := γ '' Icc 0 Q with hGs
  have hGc : IsCompact Gs := isCompact_Icc.image_of_continuousOn
    (hg.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hQ.le)
  -- the new piece
  have hnewc : IsCompact (d.η₂ ω '' Icc d.r (d.r + t)) := by
    rw [← himg]
    exact isCompact_Icc.image_of_continuousOn (hC.continuousOn_inv.comp
      (hg.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hQ.le) fun s hs => hγH s hs)
  have hsplit : d.η₂ ω '' Icc 0 (d.r + t) = d.η₂ ω '' Icc 0 d.r ∪ d.η₂ ω '' Icc d.r (d.r + t) := by
    rw [← image_union, Icc_union_Icc_eq_Icc zero_le (le_add_right le_rfl)]
  have hA₂'c : IsCompact (d.η₂ ω '' Icc 0 (d.r + t)) := by rw [hsplit]; exact hA₂c.union hnewc
  have hX : prefixSet (d.η₁ ω) d.u (d.η₂ ω) (d.r + t) = d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 (d.r + t) := rfl
  have hXc : IsClosed (prefixSet (d.η₁ ω) d.u (d.η₂ ω) (d.r + t)) := by rw [hX]; exact (hA₁c.union hA₂'c).isClosed
  have hD'eq := activeDomain_eq hXc
  rw [hD'eq, hX] at hin
  -- the later active domain contains the chart image of the complement of the hull of `γ`
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  have hQr : (0 : ℝ) ≤ Q := Q.coe_nonneg
  obtain ⟨Wg, γg, T', hQT', hWgc, hWg0, hγg, hWeq, hγeq⟩ :=
    Sec7.ReverseArc.exists_global_model hg hWc.continuousOn hW0 hQ
  have hΦeq : fwdMapInv w' Q = fwdMapInv Wg Q := fwdMapInv_eq_of_eqOn hQr hQT' fun r hr => (hWeq r hr).symm
  have himgg : γg '' Icc 0 (Q : ℝ) = γ '' Icc 0 Q := by
    rw [image_congr (fun r hr => hγeq r ⟨hr.1, hr.2.trans hQT'.le⟩), image_toNNReal_Icc γ hQr,
      Real.toNNReal_coe]
  have hK : fwdHull Wg Q = fillH Gs := by rw [hγg.2.2 Q hQr, himgg]
  have hlater := (OrdDet.later_tip_mem_closure_activeDomain hd hω hg hWc hW0 hQ himg htip).1
  rw [hD'eq, hX] at hlater
  have hD' : ψ '' (H \ fillH Gs) ⊆ H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 (d.r + t)) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hK] at hz
    have hfz : fwdMap Wg Q z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hWgc hQr hz
    have he : extendFrom H (fwdMapInv w' Q) (fwdMap Wg Q z) = z := by
      rw [hΦeq, ZhanGT4.extendFrom_eq_fwdMapInv hWgc hWg0 hQr hfz,
        QuantumZipper.RS.fwdMapInv_fwdMap hWgc hWg0 hQr hz]
    have h1 : d.inv ω (extendFrom H (fwdMapInv w' Q) (fwdMap Wg Q z)) ∈
        H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 (d.r + t)) := hlater ⟨fwdMap Wg Q z, hfz, rfl⟩
    rwa [he] at h1
  refine subset_fillH_of_inactive hDC hA₁c hA₂'c hGc subset_union_left
    (union_subset_union_right _ (by rw [hsplit]; exact subset_union_left)) (fun z hz => ?_) hD' hLτ hτR hS
    (fun w hw1 hw2 => hZ w hw1 fun h => hw2 (by rw [hsplit]; exact Or.inl h)) (by rw [hτ]; exact hin)
  obtain ⟨s, hs, rfl⟩ := hz
  have hmem : ψ (γ s) ∈ d.η₂ ω '' Icc d.r (d.r + t) := by rw [← himg]; exact ⟨s, hs, rfl⟩
  refine ⟨by rw [hsplit]; exact Or.inr hmem, ?_⟩
  obtain ⟨s', hs', he⟩ := hmem
  rw [← he]
  exact hnc s' hs'

end InteractingSLE.RLC.OrdGap
