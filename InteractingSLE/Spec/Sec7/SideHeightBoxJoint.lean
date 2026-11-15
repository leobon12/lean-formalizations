/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightBoxSign
import InteractingSLE.Spec.Sec7.Lemma78MeanWordGeom

/-!
# The exposed sides in the first-contact chart: which path the chart points of `(L, 0)` and `(0, R)` lie on

Packet PROVE-SIDEHEIGHT2 (specification Lemma 7.8, p. 290: "the images of the exposed left and right sides of the
selected `i`th arc"). In the first-contact chart `ψ = d.inv ω` of two simple prefixes `α = η₁([0, s₀])` (seed `x₁`)
and `β = η₂([0, t₀])` (seed `x₂ < x₁`) meeting first at `α(s₀) = β(t₀)`:

* `ψ` takes each boundary point at a single chart point (every point is regular for simple prefixes,
  `inv_injective_real`);
* the extreme real points of `K` are `ψ(R) = b` (on the first prefix) and `ψ(L) = a` (on the second): otherwise the
  other prefix would trap a seed and hence the contact, which the tip property frees (`false_of_trap`);
* hence, by connectedness, `ψ((0, R)) ⊆ α([0, s₀))` and `ψ((L, 0)) ⊆ β([0, t₀))` (`exists_inv_eq_right`,
  `exists_inv_eq_left`), and near such a point the real points adherent to the active domain lie on the same prefix
  (`exists_ball_real_right`, `exists_ball_real_left`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace SideHeightBox

open HalfPlaneSep Restart

/-! ### The trap -/

section Trap

variable {γ₁ γ₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {y₁ y₂ : ℝ}

/-- **The other prefix cannot pass round a seed before the first contact.** If `γ₂([0, t])`, `t < σ₂`, joins two real
points `u < v` with the seed `y₁` of `γ₁` in between, it traps `y₁`, hence all of `γ₁([0, σ₁])` (which misses it),
hence the contact point `γ₁(σ₁) = γ₂(σ₂)`, which the tip property of `γ₂` frees. -/
theorem false_of_trap (hp₁ : IsPathGood γ₁ ζ₁ y₁) (hp₂ : IsPathGood γ₂ ζ₂ y₂) {σ₁ σ₂ t : ℝ≥0}
    (hσ₁ : (σ₁ : ℝ≥0∞) ≤ ζ₁) (hσ₂ : (σ₂ : ℝ≥0∞) ≤ ζ₂) (hc : γ₁ σ₁ = γ₂ σ₂)
    (hmin : ∀ s t' : ℝ≥0, s ≤ σ₁ → t' ≤ σ₂ → γ₁ s = γ₂ t' → s = σ₁ ∧ t' = σ₂) (htσ : t < σ₂) {u v : ℝ}
    (hu : (u : ℂ) ∈ γ₂ '' Icc 0 t) (hv : (v : ℂ) ∈ γ₂ '' Icc 0 t) (huy : u < y₁) (hyv : y₁ < v) : False := by
  have htζ : (t : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 htσ.le).trans hσ₂
  set K' := γ₂ '' Icc 0 t with hK'
  have hK'c : IsCompact K' := IsPathGood.isCompact_image hp₂ htζ
  have hK'pc : IsPreconnected K' := isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hp₂ htζ)
  have hK'im : ∀ z ∈ K', 0 ≤ z.im := by
    rintro _ ⟨t', ht', rfl⟩
    exact IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 ht'.2).trans htζ)
  have hdis : ∀ s ≤ σ₁, γ₁ s ∉ K' := by
    rintro s hs ⟨t', ht', hte⟩
    have := (hmin s t' hs (ht'.2.trans htσ.le) hte.symm).2
    exact absurd (this ▸ ht'.2) (not_le.2 htσ)
  have hy₁ : γ₁ 0 = (y₁ : ℂ) := IsPathGood.zero hp₁
  have htrap := isTrappedAt_of_isPreconnected hK'c hK'pc hK'im hu hv huy hyv (hy₁ ▸ hdis 0 zero_le)
  have hApc : IsPreconnected (γ₁ '' Icc 0 σ₁) := isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hp₁ hσ₁)
  have hAX : γ₁ '' Icc 0 σ₁ ⊆ {z : ℂ | 0 ≤ z.im} \ K' := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 hs.2).trans hσ₁), hdis s hs.2⟩
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hK'c.isClosed hApc hAX with hall | hall
  · exact (hall _ ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩).not_isTrappedAt (by rw [hy₁]; simp) (hy₁ ▸ htrap)
  · have h1 := hall _ ⟨σ₁, ⟨zero_le, le_rfl⟩, rfl⟩
    rw [hc] at h1
    exact (IsPathGood.isFreeAt_of_lt hp₂ htσ hσ₂).not_isTrappedAt (IsPathGood.im_nonneg hp₂ hσ₂) h1

end Trap

/-! ### Connectedness along a chart side -/

/-- **A connected side lands on one prefix**: if a continuous `ψ` sends a preconnected parameter set `I` into the
union of two closed sets meeting only at points not attained on `I`, and one point of `I` into the first, all of `I`
goes into the first. -/
theorem forall_mem_of_isPreconnected {ψ : ℝ → ℂ} (hψ : Continuous ψ) {I : Set ℝ} (hI : IsPreconnected I)
    {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B) (hsub : ∀ w ∈ I, ψ w ∈ A ∪ B)
    (hAB : ∀ w ∈ I, ψ w ∈ A → ψ w ∉ B) {e : ℝ} (he : e ∈ I) (heA : ψ e ∈ A) : ∀ w ∈ I, ψ w ∈ A := by
  intro w hw
  by_contra hwA
  have hwB : ψ w ∈ B := (hsub w hw).resolve_left hwA
  obtain ⟨w', hw', hw'A, hw'B⟩ := isPreconnected_closed_iff.1 hI (ψ ⁻¹' A) (ψ ⁻¹' B) (hA.preimage hψ)
    (hB.preimage hψ) (fun w hw => hsub w hw) ⟨e, he, heA⟩ ⟨w, hw, hwB⟩
  exact hAB w' hw' hw'A hw'B

/-! ### The first-contact chart -/

section Chart

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

theorem ofReal_mem_Hbar (x : ℝ) : ((x : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp

/-- The two prefixes meet only at the first contact. -/
theorem meet_eq_contact (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    ∀ s t : ℝ≥0, s ≤ d.s₀ ω → t ≤ d.t₀ ω → d.η₁ ω s = d.η₂ ω t → s = d.s₀ ω ∧ t = d.t₀ ω := by
  have hfc := hd.isFirstContact hE
  intro s t hs ht hst
  obtain ⟨h1, h2⟩ := hfc.2.2.2 s t ((ENNReal.coe_le_coe.2 hs).trans hfc.1) ((ENNReal.coe_le_coe.2 ht).trans hfc.2.1)
    hst
  exact ⟨le_antisymm hs h1, le_antisymm ht h2⟩

/-- **The chart attains every point of `K` once** (for simple prefixes every point is regular). -/
theorem inv_injective_real (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    (hi₁ : InjOn (d.η₁ ω) (Icc 0 (d.s₀ ω))) (hi₂ : InjOn (d.η₂ ω) (Icc 0 (d.t₀ ω))) {w w' : ℝ}
    (h : d.inv ω w' = d.inv ω w) : w' = w := by
  obtain ⟨hc₁, hc₂, -, -, h0₁, h0₂, hp⟩ := hd.pathFacts hE
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hreg⟩ := (hd.isFirstContactChart hE).2
  obtain ⟨-, hcl⟩ := hd.tendsto_inv_real hE w
  rw [hd.D_of_mem hE] at hcl
  have hlink := isUnboundedLinked_of_injOn hc₁ hc₂ h0₁ h0₂ hp (injOn_joinPath hi₁ hi₂ (meet_eq_contact hd hE))
    (d.inv ω w)
  obtain ⟨w₀, -, -, -, huniq⟩ := hreg _ hcl (Or.inr hlink)
  have e1 := huniq w (ofReal_mem_Hbar w) rfl
  have e2 := huniq w' (ofReal_mem_Hbar w') h
  exact_mod_cast e2.trans e1.symm

theorem continuous_inv_real (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    Continuous fun x : ℝ => d.inv ω x := by
  obtain ⟨-, -, -, -, -, -, -, hψc, -⟩ := (hd.isFirstContactChart hE).2
  exact hψc.comp_continuous continuous_ofReal ofReal_mem_Hbar

theorem inv_zero_eq_contact (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) : d.inv ω 0 = d.η₁ ω (d.s₀ ω) :=
  (hd.isFirstContactChart hE).2.2.2.2.2.2.2.2.2.1

/-- **The right end of the exposed sides is the rightmost real point of `K`**: `ψ(R) = b`. -/
theorem inv_wordR (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    d.inv ω (d.wordR ω) = d.baseR ω := by
  have hK := hd.inv_mem_K_of_mem_Icc hE ((hd.wordL_nonpos hE).trans (hd.wordR_nonneg hE)) le_rfl
  set u : ℕ → ℝ := fun n => d.wordR ω + 1 / ((n : ℝ) + 1) with hu
  have hun : ∀ n, d.wordR ω < u n := fun n => by simp only [hu]; linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
  have hlim : Tendsto u atTop (𝓝 (d.wordR ω)) := by
    rw [hu]
    simpa using (tendsto_const_nhds (x := d.wordR ω)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hψ := ((continuous_inv_real hd hE).tendsto _).comp hlim
  have him : (d.inv ω (d.wordR ω)).im = 0 := by
    refine tendsto_nhds_unique ((continuous_im.tendsto _).comp hψ) (tendsto_const_nhds.congr fun n => ?_)
    have := (hd.inv_of_wordR_lt hE (hun n)).2.1
    simp only [Function.comp_apply]
    rw [this]
    simp
  have hge : d.baseR ω ≤ (d.inv ω (d.wordR ω)).re :=
    ge_of_tendsto ((continuous_re.tendsto _).comp hψ) (Eventually.of_forall fun n =>
      (hd.inv_of_wordR_lt hE (hun n)).1.le)
  have hle : (d.inv ω (d.wordR ω)).re ≤ d.baseR ω := hd.le_baseR (by rwa [ofReal_re_of_im him])
  rw [← ofReal_re_of_im him, le_antisymm hle hge]

/-- **The left end of the exposed sides is the leftmost real point of `K`**: `ψ(L) = a`. -/
theorem inv_wordL (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    d.inv ω (d.wordL ω) = d.baseL ω := by
  have hK := hd.inv_mem_K_of_mem_Icc hE le_rfl ((hd.wordL_nonpos hE).trans (hd.wordR_nonneg hE))
  set u : ℕ → ℝ := fun n => d.wordL ω - 1 / ((n : ℝ) + 1) with hu
  have hun : ∀ n, u n < d.wordL ω := fun n => by simp only [hu]; linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := n)]
  have hlim : Tendsto u atTop (𝓝 (d.wordL ω)) := by
    rw [hu]
    simpa using (tendsto_const_nhds (x := d.wordL ω)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hψ := ((continuous_inv_real hd hE).tendsto _).comp hlim
  have him : (d.inv ω (d.wordL ω)).im = 0 := by
    refine tendsto_nhds_unique ((continuous_im.tendsto _).comp hψ) (tendsto_const_nhds.congr fun n => ?_)
    have := (hd.inv_of_lt_wordL hE (hun n)).2.1
    simp only [Function.comp_apply]
    rw [this]
    simp
  have hle : (d.inv ω (d.wordL ω)).re ≤ d.baseL ω :=
    le_of_tendsto ((continuous_re.tendsto _).comp hψ) (Eventually.of_forall fun n =>
      (hd.inv_of_lt_wordL hE (hun n)).1.le)
  have hge : d.baseL ω ≤ (d.inv ω (d.wordL ω)).re := hd.baseL_le (by rwa [ofReal_re_of_im him])
  rw [← ofReal_re_of_im him, le_antisymm hle hge]

/-- **The right side `(0, R)` of the chart lies on the first prefix before the contact.** -/
theorem exists_inv_eq_right (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂) (hx : x₂ < x₁) {w : ℝ}
    (hw0 : 0 < w) (hwR : w < d.wordR ω) : ∃ s < d.s₀ ω, d.inv ω w = d.η₁ ω s := by
  have hfc := hd.isFirstContact hE
  have hmeet := meet_eq_contact hd hE
  have hi₁ := IsPathGood.injOn_Icc hp₁ hfc.1
  have hi₂ := IsPathGood.injOn_Icc hp₂ hfc.2.1
  have huniq : ∀ {u v : ℝ}, d.inv ω u = d.inv ω v → u = v := fun h => inv_injective_real hd hE hi₁ hi₂ h
  have hψ0 : d.inv ω 0 = d.η₁ ω (d.s₀ ω) := by exact_mod_cast inv_zero_eq_contact hd hE
  have hKeq : d.K ω = d.η₁ ω '' Icc 0 (d.s₀ ω) ∪ d.η₂ ω '' Icc 0 (d.t₀ ω) := by rw [PairData.K_of_mem hE, prefixSet]
  have hR0 : 0 < d.wordR ω := hw0.trans hwR
  have hsub : ∀ w' ∈ Ioc 0 (d.wordR ω), d.inv ω w' ∈ d.η₁ ω '' Icc 0 (d.s₀ ω) ∪ d.η₂ ω '' Icc 0 (d.t₀ ω) :=
    fun w' hw' => hKeq ▸ hd.inv_mem_K_of_mem_Icc hE ((hd.wordL_nonpos hE).trans hw'.1.le) hw'.2
  have hAB : ∀ w' ∈ Ioc 0 (d.wordR ω), d.inv ω w' ∈ d.η₁ ω '' Icc 0 (d.s₀ ω) →
      d.inv ω w' ∉ d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    rintro w' hw' ⟨s, hs, hse⟩ ⟨t, ht, hte⟩
    have := (hmeet s t hs.2 ht.2 (hse.trans hte.symm)).1
    rw [this, ← hψ0] at hse
    exact (ne_of_gt hw'.1) (huniq (by exact_mod_cast hse.symm))
  -- the anchor `ψ(R) = b` is on the first prefix
  have hψR := inv_wordR hd hE
  have hanchor : d.inv ω (d.wordR ω) ∈ d.η₁ ω '' Icc 0 (d.s₀ ω) := by
    rcases hsub _ ⟨hR0, le_rfl⟩ with h | ⟨t, ht, hte⟩
    · exact h
    exfalso
    rcases eq_or_lt_of_le ht.2 with htt | htt
    · rw [htt, ← hfc.2.2.1, ← hψ0] at hte
      exact (ne_of_gt hR0) (huniq (by exact_mod_cast hte.symm))
    · have hx₁K : ((x₁ : ℝ) : ℂ) ∈ d.K ω := hKeq ▸ Or.inl ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₁⟩
      have hx₁b : x₁ ≤ d.baseR ω := hd.le_baseR hx₁K
      have hx₁b' : x₁ ≠ d.baseR ω := by
        intro h
        have h1 : d.η₁ ω 0 = d.η₂ ω t := by rw [IsPathGood.zero hp₁, h, ← hψR, ← hte]
        exact (ne_of_lt htt) (hmeet 0 t zero_le ht.2 h1).2
      refine false_of_trap hp₁ hp₂ hfc.1 hfc.2.1 hfc.2.2.1 hmeet htt (u := x₂) (v := d.baseR ω)
        ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₂⟩ ⟨t, ⟨zero_le, le_rfl⟩, by rw [hte, hψR]⟩ hx
        (lt_of_le_of_ne hx₁b hx₁b')
  have hall := forall_mem_of_isPreconnected (continuous_inv_real hd hE) isPreconnected_Ioc
    (IsPathGood.isCompact_image hp₁ hfc.1).isClosed (IsPathGood.isCompact_image hp₂ hfc.2.1).isClosed hsub hAB
    ⟨hR0, le_rfl⟩ hanchor
  obtain ⟨s, hs, hse⟩ := hall w ⟨hw0, hwR.le⟩
  refine ⟨s, lt_of_le_of_ne hs.2 fun h => ?_, hse.symm⟩
  rw [h, ← hψ0] at hse
  exact (ne_of_gt hw0) (huniq (by exact_mod_cast hse.symm))

/-- **The left side `(L, 0)` of the chart lies on the second prefix before the contact.** -/
theorem exists_inv_eq_left (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂) (hx : x₂ < x₁) {w : ℝ}
    (hwL : d.wordL ω < w) (hw0 : w < 0) : ∃ t < d.t₀ ω, d.inv ω w = d.η₂ ω t := by
  have hfc := hd.isFirstContact hE
  have hmeet := meet_eq_contact hd hE
  have hmeet' : ∀ t s : ℝ≥0, t ≤ d.t₀ ω → s ≤ d.s₀ ω → d.η₂ ω t = d.η₁ ω s → t = d.t₀ ω ∧ s = d.s₀ ω :=
    fun t s ht hs h => (hmeet s t hs ht h.symm).symm
  have hi₁ := IsPathGood.injOn_Icc hp₁ hfc.1
  have hi₂ := IsPathGood.injOn_Icc hp₂ hfc.2.1
  have huniq : ∀ {u v : ℝ}, d.inv ω u = d.inv ω v → u = v := fun h => inv_injective_real hd hE hi₁ hi₂ h
  have hψ0 : d.inv ω 0 = d.η₂ ω (d.t₀ ω) := by rw [← hfc.2.2.1]; exact_mod_cast inv_zero_eq_contact hd hE
  have hKeq : d.K ω = d.η₂ ω '' Icc 0 (d.t₀ ω) ∪ d.η₁ ω '' Icc 0 (d.s₀ ω) := by
    rw [PairData.K_of_mem hE, prefixSet, union_comm]
  have hL0 : d.wordL ω < 0 := hwL.trans hw0
  have hsub : ∀ w' ∈ Ico (d.wordL ω) 0, d.inv ω w' ∈ d.η₂ ω '' Icc 0 (d.t₀ ω) ∪ d.η₁ ω '' Icc 0 (d.s₀ ω) :=
    fun w' hw' => hKeq ▸ hd.inv_mem_K_of_mem_Icc hE hw'.1 (hw'.2.le.trans (hd.wordR_nonneg hE))
  have hAB : ∀ w' ∈ Ico (d.wordL ω) 0, d.inv ω w' ∈ d.η₂ ω '' Icc 0 (d.t₀ ω) →
      d.inv ω w' ∉ d.η₁ ω '' Icc 0 (d.s₀ ω) := by
    rintro w' hw' ⟨t, ht, hte⟩ ⟨s, hs, hse⟩
    have := (hmeet' t s ht.2 hs.2 (hte.trans hse.symm)).1
    rw [this, ← hψ0] at hte
    exact (ne_of_lt hw'.2) (huniq (by exact_mod_cast hte.symm))
  have hψL := inv_wordL hd hE
  have hanchor : d.inv ω (d.wordL ω) ∈ d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    rcases hsub _ ⟨le_rfl, hL0⟩ with h | ⟨s, hs, hse⟩
    · exact h
    exfalso
    rcases eq_or_lt_of_le hs.2 with hss | hss
    · rw [hss, hfc.2.2.1, ← hψ0] at hse
      exact (ne_of_lt hL0) (huniq (by exact_mod_cast hse.symm))
    · have hx₂K : ((x₂ : ℝ) : ℂ) ∈ d.K ω := hKeq ▸ Or.inl ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₂⟩
      have hax₂ : d.baseL ω ≤ x₂ := hd.baseL_le hx₂K
      have hax₂' : d.baseL ω ≠ x₂ := by
        intro h
        have h1 : d.η₂ ω 0 = d.η₁ ω s := by rw [IsPathGood.zero hp₂, ← h, ← hψL, ← hse]
        exact (ne_of_lt hss) (hmeet' 0 s zero_le hs.2 h1).2
      refine false_of_trap hp₂ hp₁ hfc.2.1 hfc.1 hfc.2.2.1.symm hmeet' hss (u := d.baseL ω) (v := x₁)
        ⟨s, ⟨zero_le, le_rfl⟩, by rw [hse, hψL]⟩ ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₁⟩
        (lt_of_le_of_ne hax₂ hax₂') hx
  have hall := forall_mem_of_isPreconnected (continuous_inv_real hd hE) isPreconnected_Ico
    (IsPathGood.isCompact_image hp₂ hfc.2.1).isClosed (IsPathGood.isCompact_image hp₁ hfc.1).isClosed hsub hAB
    ⟨le_rfl, hL0⟩ hanchor
  obtain ⟨t, ht, hte⟩ := hall w ⟨hwL.le, hw0⟩
  refine ⟨t, lt_of_le_of_ne ht.2 fun h => ?_, hte.symm⟩
  rw [h, ← hψ0] at hte
  exact (ne_of_lt hw0) (huniq (by exact_mod_cast hte.symm))

/-- **Near a chart point of an exposed side, the real points adherent to the domain lie on the same prefix** (a
real point of `(a, b)` off `K` is not adherent, `notMem_closure_D_of_mem_Ioo`; the other prefix is at positive
distance). Generic form: `p = ψ(w)` on the prefix `P`, off the other prefix `Q`, with `w` neither `L` nor `R`. -/
theorem exists_ball_real_of_mem (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {P Q : Set ℂ}
    (hKeq : d.K ω = P ∪ Q) (hQ : IsClosed Q) {w : ℝ} (hpQ : d.inv ω w ∉ Q)
    (hpa : d.inv ω w ≠ d.baseL ω) (hpb : d.inv ω w ≠ d.baseR ω) (hpK : d.inv ω w ∈ d.K ω) :
    ∃ r > 0, ∀ z ∈ ball (d.inv ω w) r, z.im = 0 → z ∈ closure (d.D ω) → z ∈ P := by
  set p := d.inv ω w with hpdef
  obtain ⟨r₂, hr₂, hr₂Q⟩ := Metric.isOpen_iff.1 hQ.isOpen_compl p hpQ
  have hmemK : ∀ z ∈ ball p r₂, z ∈ d.K ω → z ∈ P := fun z hz hzK => by
    rw [hKeq] at hzK
    exact hzK.resolve_right (hr₂Q hz)
  by_cases hpH : 0 < p.im
  · refine ⟨min r₂ p.im, lt_min hr₂ hpH, fun z hz hzim _ => absurd hz ?_⟩
    intro hz'
    have h1 : |p.im - z.im| ≤ dist p z := by
      rw [dist_eq_norm, ← sub_im]
      exact abs_im_le_norm _
    rw [hzim, sub_zero, abs_of_pos hpH, dist_comm] at h1
    exact absurd ((mem_ball.1 hz').trans_le (min_le_right _ _)) (not_lt.2 h1)
  · have hpHbar : 0 ≤ p.im := by
      rw [PairData.K_of_mem hE] at hpK
      obtain ⟨-, -, hH₁, hH₂, -⟩ := hd.pathFacts hE
      rcases hpK with ⟨s, hs, hse⟩ | ⟨t, ht, hte⟩
      · rw [← hse]; exact hH₁ hs
      · rw [← hte]; exact hH₂ ht
    have him : p.im = 0 := le_antisymm (not_lt.1 hpH) hpHbar
    have hpr : ((p.re : ℝ) : ℂ) = p := ofReal_re_of_im him
    have ha : d.baseL ω < p.re := lt_of_le_of_ne (hd.baseL_le (by rwa [hpr])) fun h => hpa (by rw [← hpr, h])
    have hb : p.re < d.baseR ω := lt_of_le_of_ne (hd.le_baseR (by rwa [hpr])) fun h => hpb (by rw [← hpr, h])
    refine ⟨min r₂ (min (p.re - d.baseL ω) (d.baseR ω - p.re)), lt_min hr₂ (lt_min (by linarith) (by linarith)),
      fun z hz hzim hzcl => ?_⟩
    have hzr : ((z.re : ℝ) : ℂ) = z := ofReal_re_of_im hzim
    have hd' : |z.re - p.re| < min (p.re - d.baseL ω) (d.baseR ω - p.re) := by
      have h1 := (mem_ball.1 hz).trans_le (min_le_right _ _)
      rwa [← hzr, ← hpr, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs] at h1
    have h1 := (abs_sub_lt_iff.1 (hd'.trans_le (min_le_left _ _))).2
    have h2 := (abs_sub_lt_iff.1 (hd'.trans_le (min_le_right _ _))).1
    refine hmemK z (ball_subset_ball (min_le_left _ _) hz) ?_
    by_contra hzK
    rw [← hzr] at hzK hzcl
    exact hd.notMem_closure_D_of_mem_Ioo hE (by linarith) (by linarith) hzK hzcl

theorem exists_ball_real_right (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂) (hx : x₂ < x₁) {w : ℝ}
    (hw0 : 0 < w) (hwR : w < d.wordR ω) :
    ∃ r > 0, ∀ z ∈ ball (d.inv ω w) r, z.im = 0 → z ∈ closure (d.D ω) → z ∈ d.η₁ ω '' Icc 0 (d.s₀ ω) := by
  have hfc := hd.isFirstContact hE
  have hi₁ := IsPathGood.injOn_Icc hp₁ hfc.1
  have hi₂ := IsPathGood.injOn_Icc hp₂ hfc.2.1
  obtain ⟨s, hs, hse⟩ := exists_inv_eq_right hd hE hp₁ hp₂ hx hw0 hwR
  refine exists_ball_real_of_mem hd hE (by rw [PairData.K_of_mem hE, prefixSet])
    (IsPathGood.isCompact_image hp₂ hfc.2.1).isClosed ?_ ?_ ?_
    (hd.inv_mem_K_of_mem_Icc hE ((hd.wordL_nonpos hE).trans hw0.le) hwR.le)
  · rintro ⟨t, ht, hte⟩
    rw [hse] at hte
    exact (ne_of_lt hs) (meet_eq_contact hd hE s t hs.le ht.2 hte.symm).1
  · intro h
    rw [← inv_wordL hd hE] at h
    exact (ne_of_gt (lt_of_le_of_lt (hd.wordL_nonpos hE) hw0)) (inv_injective_real hd hE hi₁ hi₂ h)
  · intro h
    rw [← inv_wordR hd hE] at h
    exact (ne_of_lt hwR) (inv_injective_real hd hE hi₁ hi₂ h)

theorem exists_ball_real_left (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂) (hx : x₂ < x₁) {w : ℝ}
    (hwL : d.wordL ω < w) (hw0 : w < 0) :
    ∃ r > 0, ∀ z ∈ ball (d.inv ω w) r, z.im = 0 → z ∈ closure (d.D ω) → z ∈ d.η₂ ω '' Icc 0 (d.t₀ ω) := by
  have hfc := hd.isFirstContact hE
  have hi₁ := IsPathGood.injOn_Icc hp₁ hfc.1
  have hi₂ := IsPathGood.injOn_Icc hp₂ hfc.2.1
  obtain ⟨t, ht, hte⟩ := exists_inv_eq_left hd hE hp₁ hp₂ hx hwL hw0
  refine exists_ball_real_of_mem hd hE (by rw [PairData.K_of_mem hE, prefixSet, union_comm])
    (IsPathGood.isCompact_image hp₁ hfc.1).isClosed ?_ ?_ ?_
    (hd.inv_mem_K_of_mem_Icc hE hwL.le (hw0.le.trans (hd.wordR_nonneg hE)))
  · rintro ⟨s, hs, hse⟩
    rw [hte] at hse
    exact (ne_of_lt ht) (meet_eq_contact hd hE s t hs.2 ht.le hse).2
  · intro h
    rw [← inv_wordL hd hE] at h
    exact (ne_of_gt hwL) (inv_injective_real hd hE hi₁ hi₂ h)
  · intro h
    rw [← inv_wordR hd hE] at h
    exact (ne_of_lt (lt_of_lt_of_le hw0 (hd.wordR_nonneg hE))) (inv_injective_real hd hE hi₁ hi₂ h)

/-- **Aux. lemma 57 for the transition from a single-prefix chart to the first-contact chart, along an approach**
(the filter form of PROVE-PRIMEEND's `tendsto_lift_sub_of_transition`, after PROVE-LEMMA76B's chart-lift step): for a
simple trace `γ` from `x` with `γ([0, q]) ⊆ K` and `K = γ([0, q])` near `p`, along every approach `U` to `p` from
the active domain on which `f_q(· − x)` has a real limit, the joint lift `arg φ′` minus `Im log f_q′(· − x)` tends to
`0`. -/
theorem tendsto_lift_sub (hd : d.IsMeasGood) (ω : Ω) {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ}
    {q : ℝ≥0} (hg : IsGeneratingTrace W ζ (fun t => γ t - x)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ})
    (hW0 : W 0 = 0) (hi : InjOn γ {t | (t : ℝ≥0∞) ≤ ζ}) (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q)
    (hsub : γ '' Icc 0 q ⊆ d.K ω) {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hloc : d.K ω ∩ ball p ρ ⊆ γ '' Icc 0 q)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[d.D ω] p) {y : ℝ}
    (hfy : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ))) :
    Tendsto (fun z => d.lift ω z - (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) U
      (𝓝 0) := by
  have hKc := hd.isCompact_K ω
  have hB := hd.isHPHull ω
  obtain ⟨κ, hK, hgm, hL⟩ := ReverseArc.exists_physChart hg hWc hW0 hq
  obtain ⟨Φ, hΦc, hΦH, -, hinv, hmaps⟩ := ReverseArc.exists_physInv hg hWc hW0 hi hq hq0
  obtain ⟨ε, hε, hno⟩ := ReverseArc.exists_ball_notMem_of_approach hKc.isClosed hsub hmaps hΦc hΦH hinv hρ hloc U hU
    hfy
  have hdisj : Disjoint (ball (((y + κ : ℝ)) : ℂ) ε)
      ((fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) '' (fillH (d.K ω) \
        fillH (γ '' Icc 0 q))) := by
    rw [Set.disjoint_left]
    rintro w hwb ⟨z, ⟨hzK, hzA⟩, rfl⟩
    refine hno z ⟨hzK.1, hzA⟩ hzK ?_
    rw [mem_ball, dist_eq_norm] at hwb ⊢
    convert hwb using 2
    push_cast; ring
  have hF : (U : Filter ℂ) ≤ 𝓟 (H \ fillH (d.K ω)) := hU.trans inf_le_right
  have hq' : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) U
      (𝓝[H] (((y + κ : ℝ)) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hfy.add_const (κ : ℂ)
      convert this using 2
      push_cast; ring
    · filter_upwards [hF (mem_principal_self _)] with z hz
      exact hgm.1.2.mapsTo ⟨hz.1, fun h => hz.2 (fillH_mono hsub h)⟩
  exact ReverseArc.tendsto_im_sub_of_le hK hB (fillH_mono hsub) hgm (ConformalImage.isMapOut_mapOut hB) hL
    (isCanonicalDerivLog_canonDerivLog hB) hF hε hdisj hq'

/-- **Real points of the right side lie left of the first seed**: a chart point `w ∈ (0, R)` is attained at a time
`s ∈ (s_b, s₀)` of the first prefix, `s_b` the time of `b = ψ(R)` (the side is the arc of `α` between the contact and
`b`), and a real `ψ(w)` hit after `s_b` cannot lie in `(x₁, b)`, which `α([0, s_b])` traps. -/
theorem exists_inv_eq_right' (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂) (hx : x₂ < x₁) {w : ℝ}
    (hw0 : 0 < w) (hwR : w < d.wordR ω) :
    ∃ s < d.s₀ ω, d.inv ω w = d.η₁ ω s ∧ ((d.inv ω w).im = 0 → (d.inv ω w).re < x₁) := by
  have hfc := hd.isFirstContact hE
  have hi₁ := IsPathGood.injOn_Icc hp₁ hfc.1
  have hi₂ := IsPathGood.injOn_Icc hp₂ hfc.2.1
  have huniq : ∀ {u v : ℝ}, d.inv ω u = d.inv ω v → u = v := fun h => inv_injective_real hd hE hi₁ hi₂ h
  have hψc := continuous_inv_real hd hE
  have hψ0 : d.inv ω 0 = d.η₁ ω (d.s₀ ω) := by exact_mod_cast inv_zero_eq_contact hd hE
  set α := d.η₁ ω with hαdef
  have hR0 : 0 < (d.wordR ω) := hw0.trans hwR
  have hαc : IsCompact (α '' Icc 0 (d.s₀ ω)) := IsPathGood.isCompact_image hp₁ hfc.1
  -- `ψ(d.wordR ω) = α(s_b)` with `s_b < s₀`
  have hmemR : d.inv ω (d.wordR ω) ∈ α '' Icc 0 (d.s₀ ω) := by
    have hlim : Tendsto (fun n : ℕ => (d.wordR ω) - (d.wordR ω) / ((n : ℝ) + 2)) atTop (𝓝 (d.wordR ω)) := by
      have h1 : Tendsto (fun n : ℕ => (d.wordR ω) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      simpa using (tendsto_const_nhds (x := (d.wordR ω))).sub h1
    refine hαc.isClosed.mem_of_tendsto ((hψc.tendsto (d.wordR ω)).comp hlim) (Eventually.of_forall fun n => ?_)
    have hpos : 0 < (d.wordR ω) / ((n : ℝ) + 2) := div_pos hR0 (by positivity)
    have hlt : (d.wordR ω) / ((n : ℝ) + 2) < (d.wordR ω) :=
      div_lt_self hR0 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    obtain ⟨s', hs', hs'e⟩ := exists_inv_eq_right hd hE hp₁ hp₂ hx
      (w := (d.wordR ω) - (d.wordR ω) / ((n : ℝ) + 2)) (by linarith) (by linarith)
    exact ⟨s', ⟨zero_le, hs'.le⟩, hs'e.symm⟩
  obtain ⟨sb, hsb, hsbe⟩ := hmemR
  have hsbs₀ : sb < d.s₀ ω := lt_of_le_of_ne hsb.2 fun h => by
    rw [h, ← hψ0] at hsbe
    exact (ne_of_gt hR0) (huniq hsbe.symm)
  -- the right side lies on `α([s_b, s₀])`
  set P₁ := α '' Icc sb (d.s₀ ω) with hP₁
  set P₂ := α '' Icc 0 sb with hP₂
  have hP₂c : IsClosed P₂ := (IsPathGood.isCompact_image hp₁ ((ENNReal.coe_le_coe.2 hsb.2).trans hfc.1)).isClosed
  have hP₁c : IsClosed P₁ := (IsPathGood.isCompact_image_Icc hp₁ hfc.1).isClosed
  have hsplit : α '' Icc 0 (d.s₀ ω) = P₁ ∪ P₂ := by
    rw [hP₁, hP₂, ← image_union, union_comm, Icc_union_Icc_eq_Icc zero_le hsb.2]
  have hsub : ∀ w' ∈ Ioo 0 (d.wordR ω), d.inv ω w' ∈ P₁ ∪ P₂ := fun w' hw' => by
    obtain ⟨s', hs', hs'e⟩ := exists_inv_eq_right hd hE hp₁ hp₂ hx hw'.1 hw'.2
    rw [← hsplit, hs'e]
    exact ⟨s', ⟨zero_le, hs'.le⟩, rfl⟩
  have hAB : ∀ w' ∈ Ioo 0 (d.wordR ω), d.inv ω w' ∈ P₁ → d.inv ω w' ∉ P₂ := by
    rintro w' hw' ⟨s₁, hs₁, hs₁e⟩ ⟨s₂, hs₂, hs₂e⟩
    have := hi₁ ⟨zero_le, hs₁.2⟩ ⟨zero_le, hs₂.2.trans hsb.2⟩ (hs₁e.trans hs₂e.symm)
    have hss : s₁ = sb := le_antisymm (this ▸ hs₂.2) hs₁.1
    rw [hss, hsbe] at hs₁e
    exact (ne_of_lt hw'.2) (huniq hs₁e.symm)
  -- an anchor near `0`
  have hψ0P₂ : d.inv ω 0 ∉ P₂ := by
    rintro ⟨s', hs', hs'e⟩
    rw [hψ0] at hs'e
    have := hi₁ ⟨zero_le, hs'.2.trans hsb.2⟩ ⟨zero_le, le_rfl⟩ hs'e
    exact absurd (this ▸ hs'.2) (not_le.2 hsbs₀)
  obtain ⟨δ, hδ, hδP⟩ := Metric.isOpen_iff.1 (hP₂c.isOpen_compl.preimage hψc) 0 (by simpa using hψ0P₂)
  set e := min (δ / 2) ((d.wordR ω) / 2) with hedef
  have he : e ∈ Ioo 0 (d.wordR ω) :=
    ⟨lt_min (half_pos hδ) (half_pos hR0), (min_le_right _ _).trans_lt (half_lt_self hR0)⟩
  have heP₂ : d.inv ω e ∉ P₂ := hδP (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos he.1]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ))
  have heP₁ : d.inv ω e ∈ P₁ := (hsub e he).resolve_right heP₂
  have hall := forall_mem_of_isPreconnected hψc isPreconnected_Ioo hP₁c hP₂c hsub hAB he heP₁
  obtain ⟨s, hs, hse⟩ := hall w ⟨hw0, hwR⟩
  have hss₀ : s < d.s₀ ω := lt_of_le_of_ne hs.2 fun h => by
    rw [h, ← hψ0] at hse
    exact (ne_of_gt hw0) (huniq hse.symm)
  have hsbs : sb < s := lt_of_le_of_ne hs.1 fun h => by
    rw [← h, hsbe] at hse
    exact (ne_of_lt hwR) (huniq hse.symm)
  refine ⟨s, hss₀, hse.symm, fun him => ?_⟩
  -- a real point hit after `s_b` lies left of `x₁`
  by_contra hge
  push Not at hge
  set p := d.inv ω w with hpdef
  have hpr : ((p.re : ℝ) : ℂ) = p := ofReal_re_of_im him
  have hx₁ : α 0 = (x₁ : ℂ) := IsPathGood.zero hp₁
  have hpne : p.re ≠ x₁ := fun h => by
    have h1 : α s = α 0 := by rw [hse, ← hpr, h, hx₁]
    have := hi₁ ⟨zero_le, hs.2⟩ ⟨zero_le, zero_le⟩ h1
    rw [this] at hsbs
    exact absurd hsbs (not_lt.2 zero_le)
  have hb : p.re < d.baseR ω := by
    refine lt_of_le_of_ne (hd.le_baseR ?_) fun h => ?_
    · rw [hpr]; exact hd.inv_mem_K_of_mem_Icc hE ((hd.wordL_nonpos hE).trans hw0.le) hwR.le
    · have h1 : d.inv ω w = d.inv ω (d.wordR ω) := by rw [inv_wordR hd hE, ← h, hpr]
      exact (ne_of_lt hwR) (huniq h1)
  set K' := α '' Icc 0 sb with hK'
  have hK'c : IsCompact K' := IsPathGood.isCompact_image hp₁ ((ENNReal.coe_le_coe.2 hsb.2).trans hfc.1)
  have hK'pc : IsPreconnected K' :=
    isPreconnected_Icc.image _ ((IsPathGood.continuousOn_Icc hp₁ hfc.1).mono (Icc_subset_Icc_right hsb.2))
  have hK'im : ∀ z ∈ K', 0 ≤ z.im := by
    rintro _ ⟨t, ht, rfl⟩
    exact IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 (ht.2.trans hsb.2)).trans hfc.1)
  have hpK' : ((p.re : ℝ) : ℂ) ∉ K' := by
    rintro ⟨t, ht, hte⟩
    have hte' : α t = α s := by rw [hte, hpr, hse]
    have := hi₁ ⟨zero_le, ht.2.trans hsb.2⟩ ⟨zero_le, hs.2⟩ hte'
    exact absurd (this ▸ ht.2) (not_le.2 hsbs)
  have hbK' : ((d.baseR ω : ℝ) : ℂ) ∈ K' := ⟨sb, ⟨zero_le, le_rfl⟩, by rw [hsbe, inv_wordR hd hE]⟩
  obtain ⟨ε, hε, hdis⟩ := isTrappedAt_of_isPreconnected hK'c hK'pc hK'im (u := x₁) (v := d.baseR ω)
    ⟨0, ⟨le_rfl, zero_le⟩, hx₁⟩ hbK' (lt_of_le_of_ne hge (Ne.symm hpne)) hb hpK'
  obtain ⟨-, hcl⟩ := hd.tendsto_inv_real hE w
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl (ball ((p.re : ℝ) : ℂ) ε) isOpen_ball
    (by rw [hpr]; exact mem_ball_self hε)
  have hK'K : K' ⊆ d.K ω := by
    rw [PairData.K_of_mem hE, prefixSet]
    exact (image_mono (Icc_subset_Icc_right hsb.2)).trans subset_union_left
  exact Set.disjoint_left.1 hdis hz1 ⟨hz2.1, fun hzK => hz2.2 (fillH_mono hK'K hzK)⟩

/-- **Real points of the left side lie right of the second seed** (the mirror image of `exists_inv_eq_right'`). -/
theorem exists_inv_eq_left' (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁) (hp₂ : IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂) (hx : x₂ < x₁) {w : ℝ}
    (hwL : d.wordL ω < w) (hw0 : w < 0) :
    ∃ t < d.t₀ ω, d.inv ω w = d.η₂ ω t ∧ ((d.inv ω w).im = 0 → x₂ < (d.inv ω w).re) := by
  have hfc := hd.isFirstContact hE
  have hi₁ := IsPathGood.injOn_Icc hp₁ hfc.1
  have hi₂ := IsPathGood.injOn_Icc hp₂ hfc.2.1
  have huniq : ∀ {u v : ℝ}, d.inv ω u = d.inv ω v → u = v := fun h => inv_injective_real hd hE hi₁ hi₂ h
  have hψc := continuous_inv_real hd hE
  have hψ0 : d.inv ω 0 = d.η₂ ω (d.t₀ ω) := by rw [← hfc.2.2.1]; exact_mod_cast inv_zero_eq_contact hd hE
  set β := d.η₂ ω with hβdef
  have hL0 : d.wordL ω < 0 := hwL.trans hw0
  have hβc : IsCompact (β '' Icc 0 (d.t₀ ω)) := IsPathGood.isCompact_image hp₂ hfc.2.1
  have hmemL : d.inv ω (d.wordL ω) ∈ β '' Icc 0 (d.t₀ ω) := by
    have hlim : Tendsto (fun n : ℕ => d.wordL ω - d.wordL ω / ((n : ℝ) + 2)) atTop (𝓝 (d.wordL ω)) := by
      have h1 : Tendsto (fun n : ℕ => d.wordL ω / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      simpa using (tendsto_const_nhds (x := d.wordL ω)).sub h1
    refine hβc.isClosed.mem_of_tendsto ((hψc.tendsto _).comp hlim) (Eventually.of_forall fun n => ?_)
    have hneg : d.wordL ω / ((n : ℝ) + 2) < 0 := div_neg_of_neg_of_pos hL0 (by positivity)
    have hgt : d.wordL ω < d.wordL ω / ((n : ℝ) + 2) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    obtain ⟨t', ht', ht'e⟩ := exists_inv_eq_left hd hE hp₁ hp₂ hx
      (w := d.wordL ω - d.wordL ω / ((n : ℝ) + 2)) (by linarith) (by linarith)
    exact ⟨t', ⟨zero_le, ht'.le⟩, ht'e.symm⟩
  obtain ⟨ta, hta, htae⟩ := hmemL
  have htat₀ : ta < d.t₀ ω := lt_of_le_of_ne hta.2 fun h => by
    rw [h, ← hψ0] at htae
    exact (ne_of_lt hL0) (huniq htae.symm)
  set P₁ := β '' Icc ta (d.t₀ ω) with hP₁
  set P₂ := β '' Icc 0 ta with hP₂
  have hP₂c : IsClosed P₂ :=
    (IsPathGood.isCompact_image hp₂ ((ENNReal.coe_le_coe.2 hta.2).trans hfc.2.1)).isClosed
  have hP₁c : IsClosed P₁ := (IsPathGood.isCompact_image_Icc hp₂ hfc.2.1).isClosed
  have hsplit : β '' Icc 0 (d.t₀ ω) = P₁ ∪ P₂ := by
    rw [hP₁, hP₂, ← image_union, union_comm, Icc_union_Icc_eq_Icc zero_le hta.2]
  have hsub : ∀ w' ∈ Ioo (d.wordL ω) 0, d.inv ω w' ∈ P₁ ∪ P₂ := fun w' hw' => by
    obtain ⟨t', ht', ht'e⟩ := exists_inv_eq_left hd hE hp₁ hp₂ hx hw'.1 hw'.2
    rw [← hsplit, ht'e]
    exact ⟨t', ⟨zero_le, ht'.le⟩, rfl⟩
  have hAB : ∀ w' ∈ Ioo (d.wordL ω) 0, d.inv ω w' ∈ P₁ → d.inv ω w' ∉ P₂ := by
    rintro w' hw' ⟨t₁, ht₁, ht₁e⟩ ⟨t₂, ht₂, ht₂e⟩
    have := hi₂ ⟨zero_le, ht₁.2⟩ ⟨zero_le, ht₂.2.trans hta.2⟩ (ht₁e.trans ht₂e.symm)
    have htt : t₁ = ta := le_antisymm (this ▸ ht₂.2) ht₁.1
    rw [htt, htae] at ht₁e
    exact (ne_of_gt hw'.1) (huniq ht₁e.symm)
  have hψ0P₂ : d.inv ω 0 ∉ P₂ := by
    rintro ⟨t', ht', ht'e⟩
    rw [hψ0] at ht'e
    have := hi₂ ⟨zero_le, ht'.2.trans hta.2⟩ ⟨zero_le, le_rfl⟩ ht'e
    exact absurd (this ▸ ht'.2) (not_le.2 htat₀)
  obtain ⟨δ, hδ, hδP⟩ := Metric.isOpen_iff.1 (hP₂c.isOpen_compl.preimage hψc) 0 (by simpa using hψ0P₂)
  set e := -min (δ / 2) (-d.wordL ω / 2) with hedef
  have hmin : 0 < min (δ / 2) (-d.wordL ω / 2) := lt_min (half_pos hδ) (by linarith)
  have he : e ∈ Ioo (d.wordL ω) 0 := by
    refine ⟨?_, by rw [hedef]; linarith⟩
    have := min_le_right (δ / 2) (-d.wordL ω / 2)
    rw [hedef]; linarith
  have heP₂ : d.inv ω e ∉ P₂ := hδP (by
    rw [mem_ball, Real.dist_eq, sub_zero, hedef, abs_neg, abs_of_pos hmin]
    exact (min_le_left _ _).trans_lt (half_lt_self hδ))
  have heP₁ : d.inv ω e ∈ P₁ := (hsub e he).resolve_right heP₂
  have hall := forall_mem_of_isPreconnected hψc isPreconnected_Ioo hP₁c hP₂c hsub hAB he heP₁
  obtain ⟨t, ht, hte⟩ := hall w ⟨hwL, hw0⟩
  have htt₀ : t < d.t₀ ω := lt_of_le_of_ne ht.2 fun h => by
    rw [h, ← hψ0] at hte
    exact (ne_of_lt hw0) (huniq hte.symm)
  have htat : ta < t := lt_of_le_of_ne ht.1 fun h => by
    rw [← h, htae] at hte
    exact (ne_of_gt hwL) (huniq hte.symm)
  refine ⟨t, htt₀, hte.symm, fun him => ?_⟩
  by_contra hle
  push Not at hle
  set p := d.inv ω w with hpdef
  have hpr : ((p.re : ℝ) : ℂ) = p := ofReal_re_of_im him
  have hx₂ : β 0 = (x₂ : ℂ) := IsPathGood.zero hp₂
  have hpne : p.re ≠ x₂ := fun h => by
    have h1 : β t = β 0 := by rw [hte, ← hpr, h, hx₂]
    have := hi₂ ⟨zero_le, ht.2⟩ ⟨zero_le, zero_le⟩ h1
    rw [this] at htat
    exact absurd htat (not_lt.2 zero_le)
  have ha : d.baseL ω < p.re := by
    refine lt_of_le_of_ne (hd.baseL_le ?_) fun h => ?_
    · rw [hpr]; exact hd.inv_mem_K_of_mem_Icc hE hwL.le (hw0.le.trans (hd.wordR_nonneg hE))
    · have h1 : d.inv ω w = d.inv ω (d.wordL ω) := by rw [inv_wordL hd hE, h, hpr]
      exact (ne_of_gt hwL) (huniq h1)
  set K' := β '' Icc 0 ta with hK'
  have hK'c : IsCompact K' := IsPathGood.isCompact_image hp₂ ((ENNReal.coe_le_coe.2 hta.2).trans hfc.2.1)
  have hK'pc : IsPreconnected K' :=
    isPreconnected_Icc.image _ ((IsPathGood.continuousOn_Icc hp₂ hfc.2.1).mono (Icc_subset_Icc_right hta.2))
  have hK'im : ∀ z ∈ K', 0 ≤ z.im := by
    rintro _ ⟨t', ht', rfl⟩
    exact IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 (ht'.2.trans hta.2)).trans hfc.2.1)
  have hpK' : ((p.re : ℝ) : ℂ) ∉ K' := by
    rintro ⟨t', ht', ht'e⟩
    have ht'e' : β t' = β t := by rw [ht'e, hpr, hte]
    have := hi₂ ⟨zero_le, ht'.2.trans hta.2⟩ ⟨zero_le, ht.2⟩ ht'e'
    exact absurd (this ▸ ht'.2) (not_le.2 htat)
  have haK' : ((d.baseL ω : ℝ) : ℂ) ∈ K' := ⟨ta, ⟨zero_le, le_rfl⟩, by rw [htae, inv_wordL hd hE]⟩
  obtain ⟨ε, hε, hdis⟩ := isTrappedAt_of_isPreconnected hK'c hK'pc hK'im (u := d.baseL ω) (v := x₂)
    haK' ⟨0, ⟨le_rfl, zero_le⟩, hx₂⟩ ha (lt_of_le_of_ne hle hpne) hpK'
  obtain ⟨-, hcl⟩ := hd.tendsto_inv_real hE w
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.1 hcl (ball ((p.re : ℝ) : ℂ) ε) isOpen_ball
    (by rw [hpr]; exact mem_ball_self hε)
  have hK'K : K' ⊆ d.K ω := by
    rw [PairData.K_of_mem hE, prefixSet]
    exact (image_mono (Icc_subset_Icc_right hta.2)).trans subset_union_right
  exact Set.disjoint_left.1 hdis hz1 ⟨hz2.1, fun hzK => hz2.2 (fillH_mono hK'K hzK)⟩

end Chart

end SideHeightBox

end Sec7

end InteractingSLE
