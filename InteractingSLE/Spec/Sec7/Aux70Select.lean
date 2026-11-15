/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.InteractionProbFirstContact

/-!
# Aux. lemma 70: the rational stops of a reverse minimal common arc (deterministic)

Packet PROVE-LEMMA76 (specification §7.2, proof of Aux. lemma 70, p. 274, `source/spec/p241-288.md#aux-70-proof`):
"Suppose, to the contrary, that a nondegenerate interval of minimal contacts occurs. The decreasing correspondence in
Aux. lemma 68 is a homeomorphism between the two parameter intervals. Choose a rational number `qᵢ < Tᵢ` for each
path, strictly inside these intervals, so that the histories stopped at `qᵢ ∧ Tᵢ` overlap in a nondegenerate reverse
subarc `J`. […] The intersection of the two stopped ranges is exactly `J`. Indeed, an additional contact lying before
this subarc in either traversal would lie below one of its minimal contacts in both coordinates, contradicting
minimality. The common subarc contains an open subarc in `ℍ`."

## Main results

* **`exists_rat_reverseArc`**: if the first-coordinate projection of the minimal contacts of `α|[0, A]`, `β|[0, B]`
  (continuous, injective) contains a nondegenerate interval, there are rationals `r₁, r₂` with stops
  `q₁ = r₁⁺ < A`, `q₂ = r₂⁺ < B`, times `σ₁ < s₀ < q₁`, `σ₂ < q₂` and a continuous strictly decreasing `f` on
  `[σ₁, q₁]` from `q₂` to `σ₂` with `β ∘ f = α` there, such that the stopped ranges meet exactly in
  `J = α([σ₁, q₁])`, and `α(s₀)` is an interior point (given that interior times are dense, as for Loewner traces);
* `local_agree_of_reverseArc`: near every point `α(s)`, `σ₁ < s < q₁`, of the open common arc the two stopped ranges
  coincide (positive distance from the two initial prefixes `α([0, σ₁])`, `β([0, σ₂])`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

open QuantumZipper (H)

/-- A rational stop strictly between two nonnegative reals. -/
private theorem exists_rat_toNNReal_btwn' {a b : ℝ≥0} (h : a < b) :
    ∃ q : ℚ, a < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal < b := by
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show (a : ℝ) < b from h)
  have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg a).trans hq₁.le
  refine ⟨q, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq₁
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq₂

variable {α β : ℝ≥0 → ℂ} {A B : ℝ≥0}

/-- **The rational stops of a reverse minimal common arc** (proof of Aux. lemma 70, p. 274). -/
theorem exists_rat_reverseArc (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 B))
    (hdense : ∀ a c : ℝ≥0, a < c → c ≤ A → ∃ s ∈ Ioo a c, α s ∈ H)
    (hrev : ¬ NoReverseMinimalArc α A β B) :
    ∃ (r₁ r₂ : ℚ) (σ₁ σ₂ s₀ : ℝ≥0) (f : ℝ≥0 → ℝ≥0),
      (r₁ : ℝ).toNNReal < A ∧ (r₂ : ℝ).toNNReal < B ∧ σ₁ < s₀ ∧ s₀ < (r₁ : ℝ).toNNReal ∧
      σ₂ < (r₂ : ℝ).toNNReal ∧ ContinuousOn f (Icc σ₁ (r₁ : ℝ).toNNReal) ∧
      StrictAntiOn f (Icc σ₁ (r₁ : ℝ).toNNReal) ∧ f σ₁ = (r₂ : ℝ).toNNReal ∧ f (r₁ : ℝ).toNNReal = σ₂ ∧
      (∀ s ∈ Icc σ₁ (r₁ : ℝ).toNNReal, β (f s) = α s) ∧
      α '' Icc 0 (r₁ : ℝ).toNNReal ∩ β '' Icc 0 (r₂ : ℝ).toNNReal ⊆ α '' Icc σ₁ (r₁ : ℝ).toNNReal ∧
      α s₀ ∈ H := by
  simp only [NoReverseMinimalArc, not_forall, not_not] at hrev
  obtain ⟨a, c, hac, hsub⟩ := hrev
  obtain ⟨f, hfc, hfa, hfim, hfP, hfeq, -⟩ :=
    exists_strictAntiOn_of_Icc_subset_fst_image hα hβ hαi hβi hac.le hsub
  have haI : a ∈ Icc a c := ⟨le_rfl, hac.le⟩
  have hcI : c ∈ Icc a c := ⟨hac.le, le_rfl⟩
  have hcA : c ≤ A := (hfP c hcI).1.1.2
  have hfaB : f a ≤ B := (hfP a haI).1.2.1.2
  -- the first stop
  obtain ⟨r₁, hr₁a, hr₁c⟩ := exists_rat_toNNReal_btwn' hac
  set q₁ := (r₁ : ℝ).toNNReal with hq₁
  have hq₁I : q₁ ∈ Icc a c := ⟨hr₁a.le, hr₁c.le⟩
  -- the second stop
  have hfq₁ : f q₁ < f a := hfa haI hq₁I hr₁a
  obtain ⟨r₂, hr₂l, hr₂r⟩ := exists_rat_toNNReal_btwn' hfq₁
  set q₂ := (r₂ : ℝ).toNNReal with hq₂
  -- the first-path time of the second stop
  have hq₂im : q₂ ∈ f '' Icc a c := by
    rw [hfim]
    exact ⟨(hfa.antitoneOn hq₁I hcI hr₁c.le).trans hr₂l.le, hr₂r.le⟩
  obtain ⟨σ₁, hσ₁I, hfσ₁⟩ := hq₂im
  have hσ₁q₁ : σ₁ < q₁ := by
    by_contra hle
    rw [not_lt] at hle
    have := hfa.antitoneOn hq₁I hσ₁I hle
    rw [hfσ₁] at this
    exact absurd hr₂l (not_lt.2 this)
  -- an interior time on the common arc
  obtain ⟨s₀, hs₀, hs₀H⟩ := hdense σ₁ q₁ hσ₁q₁ (hr₁c.le.trans hcA)
  have hsubI : Icc σ₁ q₁ ⊆ Icc a c := Icc_subset_Icc hσ₁I.1 hq₁I.2
  refine ⟨r₁, r₂, σ₁, f q₁, s₀, f, lt_of_lt_of_le hr₁c hcA, lt_of_lt_of_le hr₂r hfaB, hs₀.1, hs₀.2, hr₂l,
    hfc.mono hsubI, hfa.mono hsubI, hfσ₁, rfl, fun s hs => hfeq s (hsubI hs), ?_, hs₀H⟩
  -- the exact overlap
  rintro z ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
  have hsA : s ∈ Icc 0 A := ⟨zero_le, hs.2.trans (hr₁c.le.trans hcA)⟩
  have htB : t ∈ Icc 0 B := ⟨zero_le, ht.2.trans (hr₂r.le.trans hfaB)⟩
  have hC : (s, t) ∈ contactSet α A β B := ⟨hsA, htB, hts.symm⟩
  obtain ⟨p, hpP, hp₁, hp₂⟩ := exists_mem_minimalContacts_le hα hβ hC
  -- the dominated minimal contact has its first coordinate in `[a, c]`
  have hpa : a ≤ p.1 := by
    by_contra hlt
    rw [not_le] at hlt
    have h2 := (fst_lt_iff_snd_lt_of_mem_minimalContacts hpP (hfP a haI)).1 hlt
    exact absurd (h2.trans_le hp₂) (not_lt.2 (ht.2.trans (hr₂r.le)))
  have hpc : p.1 ≤ c := hp₁.trans (hs.2.trans hq₁I.2)
  have hpI : p.1 ∈ Icc a c := ⟨hpa, hpc⟩
  have hpf : p = (p.1, f p.1) :=
    eq_of_mem_contactSet_of_fst_eq hβi hpP.1 (hfP p.1 hpI).1 rfl
  have hσ₁p : σ₁ ≤ p.1 := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := hfa (show p.1 ∈ Icc a c from hpI) hσ₁I hlt
    rw [hfσ₁] at h1
    have h2 : p.2 = f p.1 := congrArg Prod.snd hpf
    have h3 : f p.1 ≤ q₂ := h2 ▸ hp₂.trans ht.2
    exact absurd h1 (not_lt.2 h3)
  exact ⟨s, ⟨hσ₁p.trans hp₁, hs.2⟩, rfl⟩

/-- **The stopped ranges agree near an interior point of the open common arc.** In the configuration of
`exists_rat_reverseArc`, every `α(s)`, `σ₁ < s < q₁`, has a ball in which the two stopped ranges coincide. -/
theorem local_agree_of_reverseArc (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 B)) {q₁ q₂ σ₁ σ₂ : ℝ≥0} (hq₁ : q₁ ≤ A) (hq₂ : q₂ ≤ B)
    {f : ℝ≥0 → ℝ≥0} (hfc : ContinuousOn f (Icc σ₁ q₁)) (hfa : StrictAntiOn f (Icc σ₁ q₁)) (hfσ₁ : f σ₁ = q₂)
    (hfq₁ : f q₁ = σ₂) (hfeq : ∀ s ∈ Icc σ₁ q₁, β (f s) = α s)
    (hover : α '' Icc 0 q₁ ∩ β '' Icc 0 q₂ ⊆ α '' Icc σ₁ q₁) {s : ℝ≥0} (hs : s ∈ Ioo σ₁ q₁) :
    ∃ r > 0, α '' Icc 0 q₁ ∩ ball (α s) r = β '' Icc 0 q₂ ∩ ball (α s) r := by
  have hsI : s ∈ Icc σ₁ q₁ := Ioo_subset_Icc_self hs
  have hσ₁I : σ₁ ∈ Icc σ₁ q₁ := ⟨le_rfl, (hs.1.trans hs.2).le⟩
  have hq₁I : q₁ ∈ Icc σ₁ q₁ := ⟨(hs.1.trans hs.2).le, le_rfl⟩
  have hfs₁ : f s < q₂ := hfσ₁ ▸ hfa hσ₁I hsI hs.1
  have hfs₂ : σ₂ < f s := hfq₁ ▸ hfa hsI hq₁I hs.2
  -- the two initial prefixes miss `α s`
  have hK₁ : IsCompact (α '' Icc 0 σ₁) :=
    isCompact_Icc.image_of_continuousOn (hα.mono (Icc_subset_Icc le_rfl (hσ₁I.2.trans hq₁)))
  have hK₂ : IsCompact (β '' Icc 0 σ₂) :=
    isCompact_Icc.image_of_continuousOn (hβ.mono (Icc_subset_Icc le_rfl (hfs₂.le.trans
      (hfs₁.le.trans hq₂))))
  have hn₁ : α s ∉ α '' Icc 0 σ₁ := by
    rintro ⟨u, hu, he⟩
    have := hαi ⟨zero_le, hu.2.trans (hσ₁I.2.trans hq₁)⟩ ⟨zero_le, hs.2.le.trans hq₁⟩ he
    exact absurd (this ▸ hu.2) (not_le.2 hs.1)
  have hn₂ : α s ∉ β '' Icc 0 σ₂ := by
    rintro ⟨u, hu, he⟩
    rw [← hfeq s hsI] at he
    have := hβi ⟨zero_le, hu.2.trans (hfs₂.le.trans (hfs₁.le.trans hq₂))⟩
      ⟨zero_le, hfs₁.le.trans hq₂⟩ he
    exact absurd (this ▸ hu.2) (not_le.2 hfs₂)
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 hK₁.isClosed.isOpen_compl _ hn₁
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.isOpen_iff.1 hK₂.isClosed.isOpen_compl _ hn₂
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, Subset.antisymm ?_ ?_⟩
  · rintro z ⟨⟨u, hu, rfl⟩, hzb⟩
    have hσu : σ₁ < u := by
      by_contra hle
      exact hb₁ (ball_subset_ball (min_le_left _ _) hzb) ⟨u, ⟨zero_le, not_lt.1 hle⟩, rfl⟩
    have huI : u ∈ Icc σ₁ q₁ := ⟨hσu.le, hu.2⟩
    exact ⟨⟨f u, ⟨zero_le, (hfa.antitoneOn hσ₁I huI hσu.le).trans hfσ₁.le⟩, hfeq u huI⟩, hzb⟩
  · rintro z ⟨⟨t, ht, rfl⟩, hzb⟩
    have hσt : σ₂ < t := by
      by_contra hle
      exact hb₂ (ball_subset_ball (min_le_right _ _) hzb) ⟨t, ⟨zero_le, not_lt.1 hle⟩, rfl⟩
    -- `β t` lies on the common arc: `t ∈ [σ₂, q₂] = f '' [σ₁, q₁]`
    have hmem : β t ∈ α '' Icc 0 q₁ ∩ β '' Icc 0 q₂ := by
      obtain ⟨u, hu, hut⟩ := intermediate_value_Icc' hσ₁I.2 hfc
        (show t ∈ Icc (f q₁) (f σ₁) from ⟨hfq₁ ▸ hσt.le, hfσ₁ ▸ ht.2⟩)
      exact ⟨⟨u, ⟨zero_le, hu.2⟩, by rw [← hfeq u hu, hut]⟩, ⟨t, ht, rfl⟩⟩
    obtain ⟨u, hu, hue⟩ := hover hmem
    exact ⟨⟨u, ⟨zero_le, hu.2⟩, hue⟩, hzb⟩

end Sec7

end InteractingSLE
