/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GOrder
import InteractingSLE.Spec.Sec7.Lemma76GMono
import InteractingSLE.Spec.Sec7.Lemma76GWord
import InteractingSLE.Spec.Sec7.Lemma77Sep
import InteractingSLE.Spec.Supplement.RLCBGerm

/-!
# The zones of the retained chart at a disjoint pair

Packet PROVE-LEMMA76G (proof of Lemma 7.6, pp. 268–269). Two good paths `α` (from `x₁`, stop `a`) and `β` (from
`x₂ < x₁`, stop `b`) at a disjoint pair, with the retained chart `(φ, ψ)` of `D = ℍ \ fill(α[0, a] ∪ β[0, b])` based at
the second tip (`IsSetting`). Let `[a₂, b₂]`, `[a₁, b₁]` be the real bases of the two prefixes.

* `b₂ < a₁` (`b₂_lt_a₁`): otherwise the second prefix is trapped by the first, against the second tip being accessible;
* the **untouched** real points (real, off `α ∪ β`, adherent to `D`) are exactly the real points of the three zones
  `(−∞, a₂)`, `(b₂, a₁)`, `(b₁, ∞)` (`isUntouched_iff`); each has exactly one chart point `T(x)` (`chartPt`);
* **order** (Aux. lemma 60 generalized, `lt_of_inv_mem`): chart points of untouched points increase with the point;
  zone `(−∞, a₂)` < chart points of `β` < zone `(b₂, a₁)` < chart points of `α` < zone `(b₁, ∞)`;
* hence the zone data `zoneData` (`L₂ = sup T(−∞, a₂)`, `R₂ = inf T(b₂, a₁)`, `L₁ = sup T(b₂, a₁)`,
  `R₁ = inf T(b₁, ∞)`, tips `0` and `w₁`) satisfies `ZW.Good`, and every real chart point in `(L₂, R₂)` (resp.
  `(L₁, R₁)`) is mapped into `β` (resp. `α`), while every chart point left of `L₂`, between `R₂` and `L₁`, or right of
  `R₁` is the chart point of an untouched point of the corresponding zone.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open HalfPlaneSep Restart Supp7

/-! ### Real bases of a good path -/

section Base

variable {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x₀ : ℝ} {c : ℝ≥0}

/-- The real points of a stopped path. -/
def realSet (γ : ℝ≥0 → ℂ) (c : ℝ≥0) : Set ℝ := {x | ((x : ℝ) : ℂ) ∈ γ '' Icc 0 c}

/-- The left end of the real base. -/
def baseL (γ : ℝ≥0 → ℂ) (c : ℝ≥0) : ℝ := sInf (realSet γ c)

/-- The right end of the real base. -/
def baseR (γ : ℝ≥0 → ℂ) (c : ℝ≥0) : ℝ := sSup (realSet γ c)

theorem isCompact_realSet (hp : IsPathGood γ ζ x₀) (hc : (c : ℝ≥0∞) ≤ ζ) : IsCompact (realSet γ c) :=
  Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage (Sec7.IsPathGood.isCompact_image hp hc)

theorem seed_mem_realSet (hp : IsPathGood γ ζ x₀) : x₀ ∈ realSet γ c :=
  ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hp⟩

theorem baseL_mem (hp : IsPathGood γ ζ x₀) (hc : (c : ℝ≥0∞) ≤ ζ) : baseL γ c ∈ realSet γ c :=
  (isCompact_realSet hp hc).sInf_mem ⟨x₀, seed_mem_realSet hp⟩

theorem baseR_mem (hp : IsPathGood γ ζ x₀) (hc : (c : ℝ≥0∞) ≤ ζ) : baseR γ c ∈ realSet γ c :=
  (isCompact_realSet hp hc).sSup_mem ⟨x₀, seed_mem_realSet hp⟩

theorem baseL_le (hp : IsPathGood γ ζ x₀) (hc : (c : ℝ≥0∞) ≤ ζ) {x : ℝ} (hx : x ∈ realSet γ c) :
    baseL γ c ≤ x :=
  csInf_le (isCompact_realSet hp hc).isBounded.bddBelow hx

theorem le_baseR (hp : IsPathGood γ ζ x₀) (hc : (c : ℝ≥0∞) ≤ ζ) {x : ℝ} (hx : x ∈ realSet γ c) :
    x ≤ baseR γ c :=
  le_csSup (isCompact_realSet hp hc).isBounded.bddAbove hx

/-- Every real point `z` of the stopped path has `baseL ≤ Re z ≤ baseR`. -/
theorem re_mem_Icc_base (hp : IsPathGood γ ζ x₀) (hc : (c : ℝ≥0∞) ≤ ζ) {z : ℂ} (hz : z ∈ γ '' Icc 0 c)
    (hz0 : z.im = 0) : z.re ∈ Icc (baseL γ c) (baseR γ c) := by
  have hm : z.re ∈ realSet γ c := by
    show ((z.re : ℝ) : ℂ) ∈ γ '' Icc 0 c
    rwa [Restart.ofReal_re_eq hz0]
  exact ⟨baseL_le hp hc hm, le_baseR hp hc hm⟩

theorem baseL_le_seed (hp : IsPathGood γ ζ x₀) (hc : (c : ℝ≥0∞) ≤ ζ) : baseL γ c ≤ x₀ :=
  baseL_le hp hc (seed_mem_realSet hp)

theorem seed_le_baseR (hp : IsPathGood γ ζ x₀) (hc : (c : ℝ≥0∞) ≤ ζ) : x₀ ≤ baseR γ c :=
  le_baseR hp hc (seed_mem_realSet hp)

end Base

/-! ### The setting -/

/-- **The pathwise setting**: two good paths at a disjoint pair and the retained chart based at the second tip. -/
structure IsSetting (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (x₁ : ℝ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (x₂ : ℝ) (b : ℝ≥0)
    (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) : Prop where
  hp₁ : IsPathGood α ζ₁ x₁
  hp₂ : IsPathGood β ζ₂ x₂
  hx : x₂ < x₁
  hpair : Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ b
  hC : IsRetChart α a β b φ ψ lift

/-- An untouched real point: off both prefixes and adherent to the joint domain. -/
def IsUntouched (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b : ℝ≥0) (x : ℝ) : Prop :=
  ((x : ℝ) : ℂ) ∉ prefixSet α a β b ∧ ((x : ℝ) : ℂ) ∈ closure (activeDomain α a β b)

/-- The chart point of a real point (the real part of the forward limit along the domain). -/
def chartPt (φ : ℂ → ℂ) (D : Set ℂ) (z : ℂ) : ℝ := (limUnder (𝓝[D] z) φ).re

namespace IsSetting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
  (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift)
include hs

theorem ha : (a : ℝ≥0∞) ≤ ζ₁ := hs.hpair.1.le

theorem hb : (b : ℝ≥0∞) ≤ ζ₂ := hs.hpair.2.1.le

theorem h0₁ : (α 0).im = 0 := by rw [Sec7.IsPathGood.zero hs.hp₁]; simp

theorem h0₂ : (β 0).im = 0 := by rw [Sec7.IsPathGood.zero hs.hp₂]; simp

theorem hc₁ : ContinuousOn α (Icc 0 a) := Sec7.IsPathGood.continuousOn_Icc hs.hp₁ hs.ha

theorem hc₂ : ContinuousOn β (Icc 0 b) := Sec7.IsPathGood.continuousOn_Icc hs.hp₂ hs.hb

theorem isCompact₁ : IsCompact (α '' Icc 0 a) := Sec7.IsPathGood.isCompact_image hs.hp₁ hs.ha

theorem isCompact₂ : IsCompact (β '' Icc 0 b) := Sec7.IsPathGood.isCompact_image hs.hp₂ hs.hb

theorem isCompact_K : IsCompact (prefixSet α a β b) := hs.isCompact₁.union hs.isCompact₂

theorem D_eq : activeDomain α a β b = H \ fillH (prefixSet α a β b) := activeDomain_eq hs.isCompact_K.isClosed

theorem disj : Disjoint (α '' Icc 0 a) (β '' Icc 0 b) := hs.hpair.2.2.2.1

theorem ψc : ContinuousOn ψ Hbar := hs.hC.continuousOn_inv

theorem ψd : DifferentiableOn ℂ ψ H := hs.hC.differentiableOn_inv

theorem bij : BijOn ψ H (H \ fillH (prefixSet α a β b)) := by
  rw [← hs.D_eq]; exact hs.hC.bijOn hs.h0₂

theorem real : ∀ w ∉ H, ψ w ∉ H \ fillH (prefixSet α a β b) := by
  rw [← hs.D_eq]; exact hs.hC.inv_notMem hs.h0₂

theorem disp : ∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M := hs.hC.2.2.2.2.2.2.2.2.2.1

theorem ψ0 : ψ 0 = β b := hs.hC.inv_zero hs.h0₂

theorem im_nonneg {w : ℂ} (hw : w ∈ Hbar) : 0 ≤ (ψ w).im :=
  Lemma76E.im_nonneg_of_mapsTo hs.ψc (fun _ hv => (hs.bij.mapsTo hv).1) hw

omit hs in
theorem notMem_D_of_mem_K {z : ℂ} (hz : z ∈ prefixSet α a β b) : z ∉ H \ fillH (prefixSet α a β b) :=
  fun h => h.2 ⟨h.1, Or.inl (subset_closure hz)⟩

omit hs in
theorem fill₁_subset : H \ fillH (prefixSet α a β b) ⊆ H \ fillH (α '' Icc 0 a) :=
  sdiff_subset_sdiff_right (fillH_mono subset_union_left)

omit hs in
theorem fill₂_subset : H \ fillH (prefixSet α a β b) ⊆ H \ fillH (β '' Icc 0 b) :=
  sdiff_subset_sdiff_right (fillH_mono subset_union_right)

/-- **Every real chart point is on a prefix or an untouched real point.** -/
theorem inv_cases (w : ℝ) : ψ w ∈ α '' Icc 0 a ∨ ψ w ∈ β '' Icc 0 b ∨
    ((ψ w).im = 0 ∧ ψ w ∉ prefixSet α a β b) := by
  by_cases hK : ψ w ∈ prefixSet α a β b
  · rcases hK with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨?_, hK⟩)
    by_contra hne
    have hH : ψ w ∈ H := lt_of_le_of_ne (hs.im_nonneg (ofReal_mem_Hbar w)) (Ne.symm hne)
    exact hK (inv_mem_prefixSet_of_real hs.hC hs.h0₂ hs.hc₁ hs.hc₂ hH)

theorem inv_mem_closure (w : ℝ) : ψ w ∈ closure (activeDomain α a β b) :=
  Supp7.inv_mem_closure hs.hC hs.h0₂ (ofReal_mem_Hbar w)

/-! ### The real bases -/

/-- No interleaving: the second base is left of the first seed. -/
theorem b₂_lt_x₁ : baseR β b < x₁ := by
  have hm := baseR_mem hs.hp₂ hs.hb
  exact Lemma76E.re_lt_of_mem_snd hs.hp₁ hs.hp₂ hs.hx hs.hpair hm (by simp) |>.trans_eq' (by simp)

/-- **The second base is left of the first one.** -/
theorem b₂_lt_a₁ : baseR β b < baseL α a := by
  by_contra hle
  push Not at hle
  have hb₂ := baseR_mem hs.hp₂ hs.hb
  have ha₁ := baseL_mem hs.hp₁ hs.ha
  have hb₁ := baseR_mem hs.hp₁ hs.ha
  have hne : baseL α a ≠ baseR β b := fun h => Set.disjoint_left.1 hs.disj ha₁ (by rw [h]; exact hb₂)
  have hlt : baseL α a < baseR β b := lt_of_le_of_ne hle hne
  have hb₂b₁ : baseR β b < baseR α a := lt_of_lt_of_le hs.b₂_lt_x₁ (seed_le_baseR hs.hp₁ hs.ha)
  have hb₂α : ((baseR β b : ℝ) : ℂ) ∉ α '' Icc 0 a := fun h => Set.disjoint_left.1 hs.disj h hb₂
  have hApc : IsPreconnected (α '' Icc 0 a) := isPreconnected_Icc.image _ hs.hc₁
  have hAim : ∀ z ∈ α '' Icc 0 a, 0 ≤ z.im := by
    rintro _ ⟨s, hs', rfl⟩
    exact Sec7.IsPathGood.im_nonneg hs.hp₁ ((ENNReal.coe_le_coe.2 hs'.2).trans hs.ha)
  have htrap := Sec7.isTrappedAt_of_isPreconnected hs.isCompact₁ hApc hAim ha₁ hb₁ hlt hb₂b₁ hb₂α
  -- the label is constant along the second prefix
  have hBpc : IsPreconnected (β '' Icc 0 b) := isPreconnected_Icc.image _ hs.hc₂
  have hBX : β '' Icc 0 b ⊆ {w | 0 ≤ w.im} \ α '' Icc 0 a := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨Sec7.IsPathGood.im_nonneg hs.hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans hs.hb),
      fun h => Set.disjoint_left.1 hs.disj h ⟨t, ht, rfl⟩⟩
  rcases isFreeAt_or_isTrappedAt_of_isPreconnected hs.isCompact₁.isClosed hBpc hBX with hall | hall
  · exact (hall _ hb₂).not_isTrappedAt (by simp) htrap
  · obtain ⟨ε, hε, hdis⟩ := hall _ ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩
    obtain ⟨z', hz'D, hz'⟩ := Metric.mem_closure_iff.1 hs.hpair.2.2.2.2.1 ε hε
    rw [hs.D_eq] at hz'D
    exact Set.disjoint_left.1 hdis (mem_ball.2 (by rwa [dist_comm])) (IsSetting.fill₁_subset hz'D)

/-! ### Untouched real points -/

/-- A real point strictly inside the first base and off the first prefix is not adherent to the domain. -/
theorem notMem_closure₁ {x : ℝ} (hx : x ∈ Ioo (baseL α a) (baseR α a)) (hxα : ((x : ℝ) : ℂ) ∉ α '' Icc 0 a) :
    ((x : ℝ) : ℂ) ∉ closure (activeDomain α a β b) := by
  have hApc : IsPreconnected (α '' Icc 0 a) := isPreconnected_Icc.image _ hs.hc₁
  have hAim : ∀ z ∈ α '' Icc 0 a, 0 ≤ z.im := by
    rintro _ ⟨s, hs', rfl⟩
    exact Sec7.IsPathGood.im_nonneg hs.hp₁ ((ENNReal.coe_le_coe.2 hs'.2).trans hs.ha)
  obtain ⟨ε, hε, hdis⟩ := Sec7.isTrappedAt_of_isPreconnected hs.isCompact₁ hApc hAim (baseL_mem hs.hp₁ hs.ha)
    (baseR_mem hs.hp₁ hs.ha) hx.1 hx.2 hxα
  intro hcl
  obtain ⟨z, hzD, hz⟩ := Metric.mem_closure_iff.1 hcl ε hε
  rw [hs.D_eq] at hzD
  exact Set.disjoint_left.1 hdis (mem_ball.2 (by rwa [dist_comm])) (IsSetting.fill₁_subset hzD)

/-- The mirror statement for the second base. -/
theorem notMem_closure₂ {x : ℝ} (hx : x ∈ Ioo (baseL β b) (baseR β b)) (hxβ : ((x : ℝ) : ℂ) ∉ β '' Icc 0 b) :
    ((x : ℝ) : ℂ) ∉ closure (activeDomain α a β b) := by
  have hBpc : IsPreconnected (β '' Icc 0 b) := isPreconnected_Icc.image _ hs.hc₂
  have hBim : ∀ z ∈ β '' Icc 0 b, 0 ≤ z.im := by
    rintro _ ⟨t, ht, rfl⟩
    exact Sec7.IsPathGood.im_nonneg hs.hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans hs.hb)
  obtain ⟨ε, hε, hdis⟩ := Sec7.isTrappedAt_of_isPreconnected hs.isCompact₂ hBpc hBim (baseL_mem hs.hp₂ hs.hb)
    (baseR_mem hs.hp₂ hs.hb) hx.1 hx.2 hxβ
  intro hcl
  obtain ⟨z, hzD, hz⟩ := Metric.mem_closure_iff.1 hcl ε hε
  rw [hs.D_eq] at hzD
  exact Set.disjoint_left.1 hdis (mem_ball.2 (by rwa [dist_comm])) (IsSetting.fill₂_subset hzD)

theorem isFreeAt₁ {x : ℝ} (hx : x < baseL α a ∨ baseR α a < x) : IsFreeAt (α '' Icc 0 a) (x : ℂ) := by
  rcases hx with hx | hx
  · obtain ⟨ρ, hρ, -, hdis⟩ := Restart.exists_ball_disjoint_of_lt hs.isCompact₁ hx fun z hz hz0 =>
      (re_mem_Icc_base hs.hp₁ hs.ha hz hz0).1
    exact ⟨ρ, hρ, fun z hz => ⟨hz.2, fun h => Set.disjoint_left.1 hdis hz.1 h⟩⟩
  · obtain ⟨ρ, hρ, -, hdis⟩ := Restart.exists_ball_disjoint_of_gt hs.isCompact₁ hx fun z hz hz0 =>
      (re_mem_Icc_base hs.hp₁ hs.ha hz hz0).2
    exact ⟨ρ, hρ, fun z hz => ⟨hz.2, fun h => Set.disjoint_left.1 hdis hz.1 h⟩⟩

theorem isFreeAt₂ {x : ℝ} (hx : x < baseL β b ∨ baseR β b < x) : IsFreeAt (β '' Icc 0 b) (x : ℂ) := by
  rcases hx with hx | hx
  · obtain ⟨ρ, hρ, -, hdis⟩ := Restart.exists_ball_disjoint_of_lt hs.isCompact₂ hx fun z hz hz0 =>
      (re_mem_Icc_base hs.hp₂ hs.hb hz hz0).1
    exact ⟨ρ, hρ, fun z hz => ⟨hz.2, fun h => Set.disjoint_left.1 hdis hz.1 h⟩⟩
  · obtain ⟨ρ, hρ, -, hdis⟩ := Restart.exists_ball_disjoint_of_gt hs.isCompact₂ hx fun z hz hz0 =>
      (re_mem_Icc_base hs.hp₂ hs.hb hz hz0).2
    exact ⟨ρ, hρ, fun z hz => ⟨hz.2, fun h => Set.disjoint_left.1 hdis hz.1 h⟩⟩

/-- **The untouched real points are those of the three zones.** -/
theorem isUntouched_iff (x : ℝ) : IsUntouched α a β b x ↔
    x < baseL β b ∨ x ∈ Ioo (baseR β b) (baseL α a) ∨ baseR α a < x := by
  have hab₂ : baseL β b ≤ baseR β b := baseL_le hs.hp₂ hs.hb (baseR_mem hs.hp₂ hs.hb)
  have hab₁ : baseL α a ≤ baseR α a := baseL_le hs.hp₁ hs.ha (baseR_mem hs.hp₁ hs.ha)
  have h21 := hs.b₂_lt_a₁
  constructor
  · rintro ⟨hK, hcl⟩
    by_contra hno
    push Not at hno
    obtain ⟨h1, h2, h3⟩ := hno
    by_cases hxb : x ≤ baseR β b
    · -- in the second base
      rcases (h1 : baseL β b ≤ x).lt_or_eq with h1' | h1'
      · rcases hxb.lt_or_eq with h2' | h2'
        · exact hs.notMem_closure₂ ⟨h1', h2'⟩ (fun h => hK (Or.inr h)) hcl
        · exact hK (Or.inr (by rw [h2']; exact baseR_mem hs.hp₂ hs.hb))
      · exact hK (Or.inr (by rw [← h1']; exact baseL_mem hs.hp₂ hs.hb))
    · have hxa : baseL α a ≤ x := by
        by_contra h
        exact h2 ⟨lt_of_not_ge hxb, lt_of_not_ge h⟩
      rcases hxa.lt_or_eq with h1' | h1'
      · rcases (h3 : x ≤ baseR α a).lt_or_eq with h2' | h2'
        · exact hs.notMem_closure₁ ⟨h1', h2'⟩ (fun h => hK (Or.inl h)) hcl
        · exact hK (Or.inl (by rw [h2']; exact baseR_mem hs.hp₁ hs.ha))
      · exact hK (Or.inl (by rw [← h1']; exact baseL_mem hs.hp₁ hs.ha))
  · intro hx
    have hf₁ : x < baseL α a ∨ baseR α a < x := by
      rcases hx with hx | hx | hx
      · exact Or.inl (by linarith)
      · exact Or.inl hx.2
      · exact Or.inr hx
    have hf₂ : x < baseL β b ∨ baseR β b < x := by
      rcases hx with hx | hx | hx
      · exact Or.inl hx
      · exact Or.inr hx.1
      · exact Or.inr (by linarith)
    refine ⟨?_, ?_⟩
    · rintro (h | h)
      · have := re_mem_Icc_base hs.hp₁ hs.ha h (by simp)
        simp only [ofReal_re] at this
        rcases hf₁ with h' | h' <;> linarith [this.1, this.2]
      · have := re_mem_Icc_base hs.hp₂ hs.hb h (by simp)
        simp only [ofReal_re] at this
        rcases hf₂ with h' | h' <;> linarith [this.1, this.2]
    · obtain ⟨ε, hε, hfree⟩ := Sec7.isFreeAt_union_of_disjoint hs.isCompact₁ hs.isCompact₂ hs.disj
        (hs.isFreeAt₁ hf₁) (hs.isFreeAt₂ hf₂)
      refine Metric.mem_closure_iff.2 fun δ hδ => ?_
      set t : ℝ := min ε δ / 2 with ht
      have ht0 : 0 < t := half_pos (lt_min hε hδ)
      have hzb : dist ((x : ℂ) + (t : ℂ) * I) (x : ℂ) = t := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ht0]
      refine ⟨(x : ℂ) + (t : ℂ) * I, ?_, by rw [dist_comm, hzb]; linarith [min_le_right ε δ]⟩
      rw [hs.D_eq]
      exact hfree ⟨mem_ball.2 (by rw [hzb]; linarith [min_le_left ε δ]),
        show 0 < ((x : ℂ) + (t : ℂ) * I).im by simp [ht0]⟩

/-! ### Chart points -/

/-- **The chart point of a regular point off the domain**: the forward limit is a real point mapped back to it, and
it is its only chart preimage in `ℍ̄`. -/
theorem chartPt_spec {z : ℂ} (hz : z ∈ closure (activeDomain α a β b)) (hzD : z ∉ activeDomain α a β b)
    (hreg : IsChartRegularPoint α a β b z) :
    Tendsto φ (𝓝[activeDomain α a β b] z) (𝓝 ((chartPt φ (activeDomain α a β b) z : ℝ) : ℂ)) ∧
      ψ (chartPt φ (activeDomain α a β b) z) = z ∧
      ∀ w ∈ Hbar, ψ w = z → w = ((chartPt φ (activeDomain α a β b) z : ℝ) : ℂ) := by
  obtain ⟨w₀, hw₀, hlim, hψ, huniq⟩ := hs.hC.exists_tendsto_of_regular hs.h0₂ hz hreg
  have hw₀r : w₀.im = 0 := by
    by_contra hne
    have hH : w₀ ∈ H := lt_of_le_of_ne hw₀ (Ne.symm hne)
    exact hzD (hψ ▸ (hs.hC.bijOn hs.h0₂).mapsTo hH)
  have := mem_closure_iff_nhdsWithin_neBot.1 hz
  have hlu : limUnder (𝓝[activeDomain α a β b] z) φ = w₀ := hlim.limUnder_eq
  have hcp : ((chartPt φ (activeDomain α a β b) z : ℝ) : ℂ) = w₀ := by
    rw [chartPt, hlu]; exact Restart.ofReal_re_eq hw₀r
  rw [hcp]
  exact ⟨hlim, hψ, huniq⟩

/-- The chart point of an untouched real point. -/
theorem chartPt_untouched {x : ℝ} (hx : IsUntouched α a β b x) :
    Tendsto φ (𝓝[activeDomain α a β b] (x : ℂ)) (𝓝 ((chartPt φ (activeDomain α a β b) x : ℝ) : ℂ)) ∧
      ψ (chartPt φ (activeDomain α a β b) x) = x ∧
      ∀ w ∈ Hbar, ψ w = x → w = ((chartPt φ (activeDomain α a β b) x : ℝ) : ℂ) :=
  hs.chartPt_spec hx.2 (fun h => ofReal_notMem_H x h.1.1)
    (isChartRegularPoint_of_notMem hs.hc₁ hs.hc₂ hs.h0₁ hs.h0₂ hx.1)

theorem hi₁ : InjOn α (Icc 0 a) := Sec7.IsPathGood.injOn_Icc hs.hp₁ hs.ha

theorem hi₂ : InjOn β (Icc 0 b) := Sec7.IsPathGood.injOn_Icc hs.hp₂ hs.hb

/-- The chart point of the first tip. -/
theorem chartPt_tip₁ :
    Tendsto φ (𝓝[activeDomain α a β b] (α a)) (𝓝 ((chartPt φ (activeDomain α a β b) (α a) : ℝ) : ℂ)) ∧
      ψ (chartPt φ (activeDomain α a β b) (α a)) = α a ∧
      ∀ w ∈ Hbar, ψ w = α a → w = ((chartPt φ (activeDomain α a β b) (α a) : ℝ) : ℂ) := by
  refine hs.chartPt_spec hs.hpair.2.2.2.2.2 (fun h => ?_) (RLC.isChartRegularPoint_tip₁ hs.hc₁ hs.hc₂ hs.h0₁ hs.h0₂
    (fun h => Set.disjoint_left.1 hs.disj ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩ h) hs.hi₁)
  rw [hs.D_eq] at h
  exact IsSetting.notMem_D_of_mem_K (Or.inl ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩) h

/-- `0` is the only chart preimage of the second tip. -/
theorem eq_zero_of_inv_eq_tip₂ {w : ℂ} (hw : w ∈ Hbar) (he : ψ w = β b) : w = 0 :=
  RLC.eq_of_inv_eq_of_regular hs.hC hs.h0₂ (RLC.isChartRegularPoint_tip₂ hs.hc₁ hs.hc₂ hs.h0₁ hs.h0₂
    (fun h => Set.disjoint_left.1 hs.disj h ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩)
    (fun t ht he' => (ne_of_lt ht) (hs.hi₂ ⟨zero_le, ht.le⟩ ⟨zero_le, le_rfl⟩ he')))
    (show (0 : ℂ) ∈ Hbar by simp [Hbar]) hs.ψ0 hw he

/-! ### The order of chart points -/

/-- Aux. lemma 60 generalized, in the setting. -/
theorem lt_of_mem {A C : Set ℂ} (hAc : IsCompact A) (hApc : IsPreconnected A) (hAim : ∀ z ∈ A, 0 ≤ z.im)
    (hAD : ∀ z ∈ A, z ∉ H \ fillH (prefixSet α a β b)) (hCc : IsCompact C) (hCpc : IsPreconnected C)
    (hCim : ∀ z ∈ C, 0 ≤ z.im) (hCD : ∀ z ∈ C, z ∉ H \ fillH (prefixSet α a β b)) (hAC : Disjoint A C) {x : ℝ}
    (hxA : ((x : ℝ) : ℂ) ∈ A) (hCx : ∀ z ∈ C, z.im = 0 → z.re < x) {x₀ : ℝ} (hx₀C : ((x₀ : ℝ) : ℂ) ∈ C)
    {wA wC : ℝ} (hwA : ψ wA ∈ A) (hwC : ψ wC ∈ C) : wC < wA := by
  obtain ⟨M, hM⟩ := hs.disp
  exact lt_of_inv_mem hs.isCompact_K hs.ψc hs.bij hs.real hM hAc hApc hAim hAD hCc hCpc hCim hCD hAC hxA hCx
    hx₀C hwA hwC

/-- The mirror image of `lt_of_mem`. -/
theorem lt_of_mem' {A C : Set ℂ} (hAc : IsCompact A) (hApc : IsPreconnected A) (hAim : ∀ z ∈ A, 0 ≤ z.im)
    (hAD : ∀ z ∈ A, z ∉ H \ fillH (prefixSet α a β b)) (hCc : IsCompact C) (hCpc : IsPreconnected C)
    (hCim : ∀ z ∈ C, 0 ≤ z.im) (hCD : ∀ z ∈ C, z ∉ H \ fillH (prefixSet α a β b)) (hAC : Disjoint A C) {x : ℝ}
    (hxA : ((x : ℝ) : ℂ) ∈ A) (hCx : ∀ z ∈ C, z.im = 0 → x < z.re) {x₀ : ℝ} (hx₀C : ((x₀ : ℝ) : ℂ) ∈ C)
    {wA wC : ℝ} (hwA : ψ wA ∈ A) (hwC : ψ wC ∈ C) : wA < wC := by
  obtain ⟨M, hM⟩ := hs.disp
  exact lt_of_inv_mem' hs.isCompact_K hs.ψc hs.bij hs.real hM hAc hApc hAim hAD hCc hCpc hCim hCD hAC hxA hCx
    hx₀C hwA hwC

theorem pc₁ : IsPreconnected (α '' Icc 0 a) := isPreconnected_Icc.image _ hs.hc₁

theorem pc₂ : IsPreconnected (β '' Icc 0 b) := isPreconnected_Icc.image _ hs.hc₂

theorem im₁ : ∀ z ∈ α '' Icc 0 a, 0 ≤ z.im := by
  rintro _ ⟨s, hs', rfl⟩
  exact Sec7.IsPathGood.im_nonneg hs.hp₁ ((ENNReal.coe_le_coe.2 hs'.2).trans hs.ha)

theorem im₂ : ∀ z ∈ β '' Icc 0 b, 0 ≤ z.im := by
  rintro _ ⟨t, ht, rfl⟩
  exact Sec7.IsPathGood.im_nonneg hs.hp₂ ((ENNReal.coe_le_coe.2 ht.2).trans hs.hb)

omit hs in
theorem off₁ : ∀ z ∈ α '' Icc 0 a, z ∉ H \ fillH (prefixSet α a β b) := fun _ hz =>
  IsSetting.notMem_D_of_mem_K (Or.inl hz)

omit hs in
theorem off₂ : ∀ z ∈ β '' Icc 0 b, z ∉ H \ fillH (prefixSet α a β b) := fun _ hz =>
  IsSetting.notMem_D_of_mem_K (Or.inr hz)

omit hs in
theorem offR (x : ℝ) : ∀ z ∈ ({((x : ℝ) : ℂ)} : Set ℂ), z ∉ H \ fillH (prefixSet α a β b) := by
  rintro _ rfl h
  exact ofReal_notMem_H x h.1

omit hs in
theorem imR (x : ℝ) : ∀ z ∈ ({((x : ℝ) : ℂ)} : Set ℂ), 0 ≤ z.im := by
  rintro z rfl; simp

theorem seed₁ : ((x₁ : ℝ) : ℂ) ∈ α '' Icc 0 a := ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hs.hp₁⟩

theorem seed₂ : ((x₂ : ℝ) : ℂ) ∈ β '' Icc 0 b := ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hs.hp₂⟩

/-- **Chart points of the second prefix precede those of the first.** -/
theorem lt_of_mem₂_of_mem₁ {w w' : ℝ} (hw : ψ w ∈ β '' Icc 0 b) (hw' : ψ w' ∈ α '' Icc 0 a) : w < w' :=
  hs.lt_of_mem hs.isCompact₁ hs.pc₁ hs.im₁ IsSetting.off₁ hs.isCompact₂ hs.pc₂ hs.im₂ IsSetting.off₂ hs.disj hs.seed₁
    (fun _ hz hz0 => Lemma76E.re_lt_of_mem_snd hs.hp₁ hs.hp₂ hs.hx hs.hpair hz hz0) hs.seed₂ hw' hw

/-- **Chart points of distinct real points are in the same order** (for the chart points of untouched points). -/
theorem lt_of_real {x x' : ℝ} (hxx : x < x')
    {w w' : ℝ} (hw : ψ w = x) (hw' : ψ w' = x') : w < w' :=
  hs.lt_of_mem isCompact_singleton isPreconnected_singleton (imR x') (offR x') isCompact_singleton
    isPreconnected_singleton (imR x) (offR x)
    (Set.disjoint_singleton.2 fun h => (ne_of_lt hxx) (ofReal_injective h).symm) (mem_singleton _)
    (fun _ hz _ => by rw [hz]; simpa using hxx) (mem_singleton _) hw' hw

theorem lt_of_untouched_of_mem₁ {x : ℝ} (hx : IsUntouched α a β b x) (hxa : x < baseL α a) {w w' : ℝ}
    (hw : ψ w = x) (hw' : ψ w' ∈ α '' Icc 0 a) : w < w' :=
  hs.lt_of_mem hs.isCompact₁ hs.pc₁ hs.im₁ IsSetting.off₁ isCompact_singleton isPreconnected_singleton (imR x) (offR x)
    (Set.disjoint_singleton_right.2 fun h => hx.1 (Or.inl h)) hs.seed₁
    (fun _ hz _ => by rw [hz]; simpa using hxa.trans_le (baseL_le_seed hs.hp₁ hs.ha)) (mem_singleton _) hw' hw

theorem lt_of_mem₁_of_untouched {x : ℝ} (hx : IsUntouched α a β b x) (hxb : baseR α a < x) {w w' : ℝ}
    (hw : ψ w = x) (hw' : ψ w' ∈ α '' Icc 0 a) : w' < w :=
  hs.lt_of_mem isCompact_singleton isPreconnected_singleton (imR x) (offR x) hs.isCompact₁ hs.pc₁ hs.im₁ IsSetting.off₁
    (Set.disjoint_singleton_left.2 fun h => hx.1 (Or.inl h)) (mem_singleton _)
    (fun _ hz hz0 => lt_of_le_of_lt (re_mem_Icc_base hs.hp₁ hs.ha hz hz0).2 hxb) hs.seed₁ hw hw'

theorem lt_of_untouched_of_mem₂ {x : ℝ} (hx : IsUntouched α a β b x) (hxa : x < baseL β b) {w w' : ℝ}
    (hw : ψ w = x) (hw' : ψ w' ∈ β '' Icc 0 b) : w < w' :=
  hs.lt_of_mem' isCompact_singleton isPreconnected_singleton (imR x) (offR x) hs.isCompact₂ hs.pc₂ hs.im₂ IsSetting.off₂
    (Set.disjoint_singleton_left.2 fun h => hx.1 (Or.inr h)) (mem_singleton _)
    (fun _ hz hz0 => lt_of_lt_of_le hxa (re_mem_Icc_base hs.hp₂ hs.hb hz hz0).1) hs.seed₂ hw hw'

theorem lt_of_mem₂_of_untouched {x : ℝ} (hx : IsUntouched α a β b x) (hxb : baseR β b < x) {w w' : ℝ}
    (hw : ψ w = x) (hw' : ψ w' ∈ β '' Icc 0 b) : w' < w :=
  hs.lt_of_mem' hs.isCompact₂ hs.pc₂ hs.im₂ IsSetting.off₂ isCompact_singleton isPreconnected_singleton (imR x) (offR x)
    (Set.disjoint_singleton_right.2 fun h => hx.1 (Or.inr h)) hs.seed₂
    (fun _ hz _ => by rw [hz]; simpa using (seed_le_baseR hs.hp₂ hs.hb).trans_lt hxb) (mem_singleton _) hw' hw

/-! ### The chart points of the zones -/

theorem untouched_of_zone {x : ℝ} (hx : x < baseL β b ∨ x ∈ Ioo (baseR β b) (baseL α a) ∨ baseR α a < x) :
    IsUntouched α a β b x := (hs.isUntouched_iff x).2 hx

theorem T_spec {x : ℝ} (hx : IsUntouched α a β b x) : ψ (chartPt φ (activeDomain α a β b) x) = x :=
  (hs.chartPt_untouched hx).2.1

theorem w₁_spec : ψ (chartPt φ (activeDomain α a β b) (α a)) ∈ α '' Icc 0 a := by
  rw [hs.chartPt_tip₁.2.1]; exact ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩

theorem zero_spec : ψ ((0 : ℝ) : ℂ) ∈ β '' Icc 0 b := by
  rw [ofReal_zero, hs.ψ0]; exact ⟨b, ⟨zero_le, le_rfl⟩, rfl⟩

theorem T_lt_zero {x : ℝ} (hx : x < baseL β b) : chartPt φ (activeDomain α a β b) x < 0 :=
  hs.lt_of_untouched_of_mem₂ (hs.untouched_of_zone (Or.inl hx)) hx (hs.T_spec (hs.untouched_of_zone (Or.inl hx)))
    hs.zero_spec

theorem zero_lt_T {x : ℝ} (hx : x ∈ Ioo (baseR β b) (baseL α a)) : 0 < chartPt φ (activeDomain α a β b) x :=
  hs.lt_of_mem₂_of_untouched (hs.untouched_of_zone (Or.inr (Or.inl hx))) hx.1
    (hs.T_spec (hs.untouched_of_zone (Or.inr (Or.inl hx)))) hs.zero_spec

theorem T_lt_w₁ {x : ℝ} (hx : x ∈ Ioo (baseR β b) (baseL α a)) :
    chartPt φ (activeDomain α a β b) x < chartPt φ (activeDomain α a β b) (α a) :=
  hs.lt_of_untouched_of_mem₁ (hs.untouched_of_zone (Or.inr (Or.inl hx))) hx.2
    (hs.T_spec (hs.untouched_of_zone (Or.inr (Or.inl hx)))) hs.w₁_spec

theorem w₁_lt_T {x : ℝ} (hx : baseR α a < x) :
    chartPt φ (activeDomain α a β b) (α a) < chartPt φ (activeDomain α a β b) x :=
  hs.lt_of_mem₁_of_untouched (hs.untouched_of_zone (Or.inr (Or.inr hx))) hx
    (hs.T_spec (hs.untouched_of_zone (Or.inr (Or.inr hx)))) hs.w₁_spec

theorem T_strictMonoOn {S : Set ℝ} (hS : ∀ x ∈ S, IsUntouched α a β b x) :
    StrictMonoOn (fun x : ℝ => chartPt φ (activeDomain α a β b) (x : ℂ)) S := fun x hx x' hx' hxx =>
  hs.lt_of_real hxx (hs.T_spec (hS x hx)) (hs.T_spec (hS x' hx'))

end IsSetting

/-! ### The zone data -/

/-- **The zone data of the retained chart**: the chart point of untouched points, the bases, the extreme chart
points of the zones and the two tips. -/
def zoneData (φ : ℂ → ℂ) (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b : ℝ≥0) : ZW where
  T := fun x : ℝ => chartPt φ (activeDomain α a β b) (x : ℂ)
  a₂ := baseL β b
  b₂ := baseR β b
  a₁ := baseL α a
  b₁ := baseR α a
  L₂ := sSup ((fun x : ℝ => chartPt φ (activeDomain α a β b) (x : ℂ)) '' Iio (baseL β b))
  M₂ := 0
  R₂ := sInf ((fun x : ℝ => chartPt φ (activeDomain α a β b) (x : ℂ)) '' Ioo (baseR β b) (baseL α a))
  L₁ := sSup ((fun x : ℝ => chartPt φ (activeDomain α a β b) (x : ℂ)) '' Ioo (baseR β b) (baseL α a))
  M₁ := chartPt φ (activeDomain α a β b) (α a)
  R₁ := sInf ((fun x : ℝ => chartPt φ (activeDomain α a β b) (x : ℂ)) '' Ioi (baseR α a))

namespace IsSetting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
  (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift)
include hs

theorem zone₁_nonempty : (Ioo (baseR β b) (baseL α a)).Nonempty := nonempty_Ioo.2 hs.b₂_lt_a₁

theorem bddAbove₀ : BddAbove ((zoneData φ α a β b).T '' Iio (baseL β b)) :=
  ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact (hs.T_lt_zero hx).le⟩

theorem bddBelow₁ : BddBelow ((zoneData φ α a β b).T '' Ioo (baseR β b) (baseL α a)) :=
  ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact (hs.zero_lt_T hx).le⟩

theorem bddAbove₁ : BddAbove ((zoneData φ α a β b).T '' Ioo (baseR β b) (baseL α a)) :=
  ⟨chartPt φ (activeDomain α a β b) (α a), by rintro _ ⟨x, hx, rfl⟩; exact (hs.T_lt_w₁ hx).le⟩

theorem bddBelow₂ : BddBelow ((zoneData φ α a β b).T '' Ioi (baseR α a)) :=
  ⟨chartPt φ (activeDomain α a β b) (α a), by rintro _ ⟨x, hx, rfl⟩; exact (hs.w₁_lt_T hx).le⟩

/-- **The zone data satisfy the order hypotheses of the word.** -/
theorem zoneData_good : (zoneData φ α a β b).Good where
  a₂_le_b₂ := baseL_le hs.hp₂ hs.hb (baseR_mem hs.hp₂ hs.hb)
  b₂_lt_a₁ := hs.b₂_lt_a₁
  a₁_le_b₁ := baseL_le hs.hp₁ hs.ha (baseR_mem hs.hp₁ hs.ha)
  mono₀ := hs.T_strictMonoOn fun x hx => hs.untouched_of_zone (Or.inl hx)
  mono₁ := hs.T_strictMonoOn fun x hx => hs.untouched_of_zone (Or.inr (Or.inl hx))
  mono₂ := hs.T_strictMonoOn fun x hx => hs.untouched_of_zone (Or.inr (Or.inr hx))
  T₀_lt := fun x hx => by
    obtain ⟨x', hxx, hx'⟩ := exists_between hx
    exact lt_of_lt_of_le ((hs.T_strictMonoOn fun y hy => hs.untouched_of_zone (Or.inl hy)) hx hx' hxx)
      (le_csSup hs.bddAbove₀ ⟨x', hx', rfl⟩)
  L₂_le := csSup_le (nonempty_Iio.image _) (by rintro _ ⟨x, hx, rfl⟩; exact (hs.T_lt_zero hx).le)
  M₂_le := le_csInf (hs.zone₁_nonempty.image _) (by rintro _ ⟨x, hx, rfl⟩; exact (hs.zero_lt_T hx).le)
  lt_T₁ := fun x hx => by
    obtain ⟨x', hx'1, hx'2⟩ := exists_between hx.1
    exact lt_of_le_of_lt (csInf_le hs.bddBelow₁ ⟨x', ⟨hx'1, hx'2.trans hx.2⟩, rfl⟩)
      ((hs.T_strictMonoOn fun y hy => hs.untouched_of_zone (Or.inr (Or.inl hy))) ⟨hx'1, hx'2.trans hx.2⟩ hx hx'2)
  T₁_lt := fun x hx => by
    obtain ⟨x', hx'1, hx'2⟩ := exists_between hx.2
    exact lt_of_lt_of_le
      ((hs.T_strictMonoOn fun y hy => hs.untouched_of_zone (Or.inr (Or.inl hy))) hx ⟨hx.1.trans hx'1, hx'2⟩ hx'1)
      (le_csSup hs.bddAbove₁ ⟨x', ⟨hx.1.trans hx'1, hx'2⟩, rfl⟩)
  L₁_le := csSup_le (hs.zone₁_nonempty.image _) (by rintro _ ⟨x, hx, rfl⟩; exact (hs.T_lt_w₁ hx).le)
  M₁_le := le_csInf (nonempty_Ioi.image _) (by rintro _ ⟨x, hx, rfl⟩; exact (hs.w₁_lt_T hx).le)
  lt_T₂ := fun x hx => by
    obtain ⟨x', hx'1, hx'2⟩ := exists_between hx
    exact lt_of_le_of_lt (csInf_le hs.bddBelow₂ ⟨x', hx'1, rfl⟩)
      ((hs.T_strictMonoOn fun y hy => hs.untouched_of_zone (Or.inr (Or.inr hy))) hx'1 (hx'1.trans hx'2) hx'2)

/-! ### Where a real chart point lands -/

theorem L₂_le_of_mem₂ {w : ℝ} (hw : ψ w ∈ β '' Icc 0 b) : (zoneData φ α a β b).L₂ ≤ w :=
  csSup_le (nonempty_Iio.image _) (by
    rintro _ ⟨x, hx, rfl⟩
    exact (hs.lt_of_untouched_of_mem₂ (hs.untouched_of_zone (Or.inl hx)) hx
      (hs.T_spec (hs.untouched_of_zone (Or.inl hx))) hw).le)

theorem le_R₂_of_mem₂ {w : ℝ} (hw : ψ w ∈ β '' Icc 0 b) : w ≤ (zoneData φ α a β b).R₂ :=
  le_csInf (hs.zone₁_nonempty.image _) (by
    rintro _ ⟨x, hx, rfl⟩
    exact (hs.lt_of_mem₂_of_untouched (hs.untouched_of_zone (Or.inr (Or.inl hx))) hx.1
      (hs.T_spec (hs.untouched_of_zone (Or.inr (Or.inl hx)))) hw).le)

theorem L₁_le_of_mem₁ {w : ℝ} (hw : ψ w ∈ α '' Icc 0 a) : (zoneData φ α a β b).L₁ ≤ w :=
  csSup_le (hs.zone₁_nonempty.image _) (by
    rintro _ ⟨x, hx, rfl⟩
    exact (hs.lt_of_untouched_of_mem₁ (hs.untouched_of_zone (Or.inr (Or.inl hx))) hx.2
      (hs.T_spec (hs.untouched_of_zone (Or.inr (Or.inl hx)))) hw).le)

theorem le_R₁_of_mem₁ {w : ℝ} (hw : ψ w ∈ α '' Icc 0 a) : w ≤ (zoneData φ α a β b).R₁ :=
  le_csInf (nonempty_Ioi.image _) (by
    rintro _ ⟨x, hx, rfl⟩
    exact (hs.lt_of_mem₁_of_untouched (hs.untouched_of_zone (Or.inr (Or.inr hx))) hx
      (hs.T_spec (hs.untouched_of_zone (Or.inr (Or.inr hx)))) hw).le)

theorem R₂_lt_L₁ : (zoneData φ α a β b).R₂ < (zoneData φ α a β b).L₁ := by
  obtain ⟨x, hx⟩ := hs.zone₁_nonempty
  exact (hs.zoneData_good.lt_T₁ x hx).trans (hs.zoneData_good.T₁_lt x hx)

/-- The untouched case of a real chart point: its preimage `x` is untouched and `T(x) = w`. -/
theorem untouched_cases {w : ℝ} (h : (ψ w).im = 0 ∧ ψ w ∉ prefixSet α a β b) :
    ψ w = (((ψ w).re : ℝ) : ℂ) ∧ IsUntouched α a β b (ψ w).re ∧ (zoneData φ α a β b).T (ψ w).re = w := by
  have he : ψ w = (((ψ w).re : ℝ) : ℂ) := (Restart.ofReal_re_eq h.1).symm
  have hu : IsUntouched α a β b (ψ w).re := ⟨by rw [← he]; exact h.2, by rw [← he]; exact hs.inv_mem_closure w⟩
  refine ⟨he, hu, ?_⟩
  have := (hs.chartPt_untouched hu).2.2 w (ofReal_mem_Hbar w) he
  exact (ofReal_injective this).symm

/-- **A chart point strictly inside `(L₂, R₂)` is on the second prefix.** -/
theorem mem₂_of_mem_Ioo {w : ℝ} (h1 : (zoneData φ α a β b).L₂ < w) (h2 : w < (zoneData φ α a β b).R₂) :
    ψ w ∈ β '' Icc 0 b := by
  have hz := hs.zoneData_good
  rcases hs.inv_cases w with hα | hβ | hu
  · exact absurd ((hs.L₁_le_of_mem₁ hα).trans_lt h2) (not_lt.2 hs.R₂_lt_L₁.le)
  · exact hβ
  · obtain ⟨-, hx, hT⟩ := hs.untouched_cases hu
    rcases (hs.isUntouched_iff _).1 hx with hx0 | hx1 | hx2
    · exact absurd (hT ▸ hz.T₀_lt _ hx0) (not_lt.2 h1.le)
    · exact absurd (hT ▸ hz.lt_T₁ _ hx1) (not_lt.2 h2.le)
    · have := hz.lt_T₂ _ hx2
      rw [hT] at this
      linarith [hs.R₂_lt_L₁, hz.L₁_le, hz.M₁_le]

/-- **A chart point strictly inside `(L₁, R₁)` is on the first prefix.** -/
theorem mem₁_of_mem_Ioo {w : ℝ} (h1 : (zoneData φ α a β b).L₁ < w) (h2 : w < (zoneData φ α a β b).R₁) :
    ψ w ∈ α '' Icc 0 a := by
  have hz := hs.zoneData_good
  rcases hs.inv_cases w with hα | hβ | hu
  · exact hα
  · exact absurd ((hs.le_R₂_of_mem₂ hβ).trans_lt hs.R₂_lt_L₁) (not_lt.2 h1.le)
  · obtain ⟨-, hx, hT⟩ := hs.untouched_cases hu
    rcases (hs.isUntouched_iff _).1 hx with hx0 | hx1 | hx2
    · have := hz.T₀_lt _ hx0
      rw [hT] at this
      linarith [hs.R₂_lt_L₁, hz.L₂_le, hz.M₂_le]
    · exact absurd (hT ▸ hz.T₁_lt _ hx1) (not_lt.2 h1.le)
    · exact absurd (hT ▸ hz.lt_T₂ _ hx2) (not_lt.2 h2.le)

/-- **Left of `L₂` the chart point is that of an untouched point left of the second base.** -/
theorem zone₀_of_lt {w : ℝ} (hw : w < (zoneData φ α a β b).L₂) :
    ψ w = (((ψ w).re : ℝ) : ℂ) ∧ (ψ w).re < baseL β b ∧ (zoneData φ α a β b).T (ψ w).re = w := by
  have hz := hs.zoneData_good
  rcases hs.inv_cases w with hα | hβ | hu
  · exact absurd ((hs.L₁_le_of_mem₁ hα)) (not_le.2 (by linarith [hs.R₂_lt_L₁, hz.L₂_le, hz.M₂_le]))
  · exact absurd (hs.L₂_le_of_mem₂ hβ) (not_le.2 hw)
  · obtain ⟨he, hx, hT⟩ := hs.untouched_cases hu
    rcases (hs.isUntouched_iff _).1 hx with hx0 | hx1 | hx2
    · exact ⟨he, hx0, hT⟩
    · have := hz.lt_T₁ _ hx1
      rw [hT] at this
      linarith [hz.L₂_le, hz.M₂_le]
    · have := hz.lt_T₂ _ hx2
      rw [hT] at this
      linarith [hs.R₂_lt_L₁, hz.L₂_le, hz.M₂_le, hz.L₁_le, hz.M₁_le]

/-- **Between `R₂` and `L₁` the chart point is that of an untouched point between the bases.** -/
theorem zone₁_of_mem {w : ℝ} (h1 : (zoneData φ α a β b).R₂ < w) (h2 : w < (zoneData φ α a β b).L₁) :
    ψ w = (((ψ w).re : ℝ) : ℂ) ∧ (ψ w).re ∈ Ioo (baseR β b) (baseL α a) ∧
      (zoneData φ α a β b).T (ψ w).re = w := by
  have hz := hs.zoneData_good
  rcases hs.inv_cases w with hα | hβ | hu
  · exact absurd (hs.L₁_le_of_mem₁ hα) (not_le.2 h2)
  · exact absurd (hs.le_R₂_of_mem₂ hβ) (not_le.2 h1)
  · obtain ⟨he, hx, hT⟩ := hs.untouched_cases hu
    rcases (hs.isUntouched_iff _).1 hx with hx0 | hx1 | hx2
    · have := hz.T₀_lt _ hx0
      rw [hT] at this
      linarith [hz.L₂_le, hz.M₂_le]
    · exact ⟨he, hx1, hT⟩
    · have := hz.lt_T₂ _ hx2
      rw [hT] at this
      linarith [hz.L₁_le, hz.M₁_le]

/-- **Right of `R₁` the chart point is that of an untouched point right of the first base.** -/
theorem zone₂_of_lt {w : ℝ} (hw : (zoneData φ α a β b).R₁ < w) :
    ψ w = (((ψ w).re : ℝ) : ℂ) ∧ baseR α a < (ψ w).re ∧ (zoneData φ α a β b).T (ψ w).re = w := by
  have hz := hs.zoneData_good
  rcases hs.inv_cases w with hα | hβ | hu
  · exact absurd (hs.le_R₁_of_mem₁ hα) (not_le.2 hw)
  · exact absurd (hs.le_R₂_of_mem₂ hβ) (not_le.2 (by linarith [hs.R₂_lt_L₁, hz.L₁_le, hz.M₁_le]))
  · obtain ⟨he, hx, hT⟩ := hs.untouched_cases hu
    rcases (hs.isUntouched_iff _).1 hx with hx0 | hx1 | hx2
    · have := hz.T₀_lt _ hx0
      rw [hT] at this
      linarith [hz.L₂_le, hz.M₂_le, hs.R₂_lt_L₁, hz.L₁_le, hz.M₁_le]
    · have := hz.T₁_lt _ hx1
      rw [hT] at this
      linarith [hz.L₁_le, hz.M₁_le]
    · exact ⟨he, hx2, hT⟩

end IsSetting

end Lemma76G

end Sec7

end InteractingSLE
