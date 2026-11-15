/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberOrder

/-!
# Wang–Wu Proposition 4.19, deterministic part: first contacts with the tails of a proper arc

Packet PROVE-WW-B25 (route R2 of `planning/handoffs/PROVE-WW-B21.md`). Source: Wang–Wu preprocessed document
(`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition 4.19 (L1655–L1708).

Let `α`, `β` be simple proper arcs of `ℍ` from `0` to `∞` (`IsProperArc`), and write `L`, `R` for the left and right
sides of `β`. The probabilistic input of Proposition 4.19 (the level line `α` of `h + u` in the slit domain
`ℍ \ β[a, ∞)`, whose data on the right are all at least `λ`) gives two facts for a dense set `D` of heights `a`:

* **(H1)** `NoRightFirstContact α β a`: the first contact of `α` with the tail `β[a, ∞)`, when it is not the tip
  `β(a)`, is not approached from `R` (on every left neighbourhood of the contact time `α` has a point outside `R`);
* **(H2)** `NoRightEscape α β a`: if `α` never meets `β[a, ∞)`, then `α` is not eventually in `R`.

**Theorem** (`disjoint_arcRange_rightSideOf_of_tails`): then `α` avoids `R` — "`α` lies to the left of `β`".

The proof (new; it replaces the lobe induction sketched in PROVE-WW-B21's handoff) uses only the crossing lemma in the
Jordan domain `L` (`jordan_crossing`, through the Cayley crosscut of `β`):

1. **Arrival from the left** (`exists_arrival`): if `s` is the first time at which `α` reaches a height above `h` on
   `β`, then the excursion of `α` arriving at `β` at time `s` lies in `L` and starts at height `≤ h`.
2. Let `α(t*) ∈ R`, let `τ₁ < t*` be the last contact before `t*` and `ρ` the largest height reached up to `τ₁`. By
   (H1)–(H2) the excursion of `α` into `R` through `t*` ends at a contact `τ₂ < ∞` of height `c₂ < ρ`.
3. If `α` later reaches a height above `ρ`, the arrival excursion `U⁺` (in `L`) starts at a height `s⁺ ∈ (0, ρ)`;
   the arrival excursion `U'` at the first height above `s⁺` (before `τ₁`, in `L`) has endpoints of heights
   `c' < s⁺ < c'' ≤ ρ`. The four endpoints interleave on `∂L`: `U'` and `U⁺` cross, contradicting simplicity of `α`.
4. Otherwise all heights stay `≤ ρ`; by (H2) `α` ends in `L`; at its last visit `T_L` of `R` it is at a height
   `c_L ∈ (0, ρ)`, and `α[T_L, ∞)` (a path in `L ∪ β` to `∞`) crosses the arrival excursion at the first height above
   `c_L`. Contradiction.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.WangWu.Descent

/-! ### The hypotheses -/

/-- **(H1)** at height `a`: at the first contact of `α` with the tail `β([a, ∞))`, if it is not the tip `β(a)`, `α`
is not in the right side of `β` on a whole left neighbourhood of the contact time. -/
def NoRightFirstContact (α β : ℝ → ℂ) (a : ℝ) : Prop :=
  ∀ T : ℝ, 0 < T → α T ∈ β '' Ioi a → (∀ t ∈ Ico 0 T, α t ∉ β '' Ici a) →
    ∀ ε > 0, ∃ t ∈ Ioo (T - ε) T, α t ∉ rightSideOf (arcRange β)

/-- **(H2)** at height `a`: if `α` never meets the tail `β([a, ∞))`, it is not eventually in the right side of `β`. -/
def NoRightEscape (α β : ℝ → ℂ) (a : ℝ) : Prop :=
  (∀ t, 0 ≤ t → α t ∉ β '' Ici a) → ∃ᶠ t in atTop, α t ∉ rightSideOf (arcRange β)

/-- A set of heights dense in `[0, ∞)`. -/
def IsDenseAbove (D : Set ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a ∈ D, x < a ∧ a < y

/-! ### Basic facts on proper arcs -/

variable {α β γ : ℝ → ℂ}

theorem isClosed_image_Ici (hγ : IsProperArc γ) {a : ℝ} (ha : 0 ≤ a) : IsClosed (γ '' Ici a) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hγ.tendsto (‖z‖ + 1))
  have hcpt : IsClosed (γ '' Icc a T) :=
    (isCompact_Icc.image_of_continuousOn (hγ.cont.mono fun _ ht => mem_Ici.2 (ha.trans ht.1))).isClosed
  have hzT : z ∈ closure (γ '' Icc a T) := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨b, hbA, hb⟩ := Metric.mem_closure_iff.1 hz (min ε 1) (lt_min hε one_pos)
    obtain ⟨t, ht, rfl⟩ := hbA
    refine ⟨γ t, ⟨t, ⟨ht, ?_⟩, rfl⟩, lt_of_lt_of_le hb (min_le_left _ _)⟩
    by_contra htT
    push Not at htT
    have h1 := hT t htT.le
    have h2 : dist z (γ t) < 1 := lt_of_lt_of_le hb (min_le_right _ _)
    rw [dist_eq_norm] at h2
    have := norm_sub_norm_le (γ t) z
    rw [norm_sub_rev] at h2
    linarith
  rw [hcpt.closure_eq] at hzT
  obtain ⟨t, ht, rfl⟩ := hzT
  exact ⟨t, mem_Ici.2 ht.1, rfl⟩

theorem isCompact_image_Icc (hγ : IsProperArc γ) {a b : ℝ} (ha : 0 ≤ a) : IsCompact (γ '' Icc a b) :=
  isCompact_Icc.image_of_continuousOn (hγ.cont.mono fun _ ht => mem_Ici.2 (ha.trans ht.1))

theorem image_Ici_subset_arcRange {a : ℝ} (ha : 0 ≤ a) : γ '' Ici a ⊆ arcRange γ :=
  image_mono fun _ ht => mem_Ici.2 (ha.trans ht)

theorem mem_arcRange_iff {z : ℂ} {c : ℝ} (hc : 0 ≤ c) :
    z ∈ arcRange γ ↔ z ∈ γ '' Icc 0 c ∨ z ∈ γ '' Ioi c := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases le_or_gt t c with h | h
    · exact Or.inl ⟨t, ⟨ht, h⟩, rfl⟩
    · exact Or.inr ⟨t, h, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, mem_Ici.2 ht.1, rfl⟩
    · exact ⟨t, mem_Ici.2 (hc.trans ht.le), rfl⟩

/-- Heights on a proper arc are unique. -/
theorem eq_height (hγ : IsProperArc γ) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (h : γ c = γ c') :
    c = c' :=
  hγ.inj (mem_Ici.2 hc) (mem_Ici.2 hc') h

theorem leftSideOf_subset_H : leftSideOf (arcRange γ) ⊆ H := fun _ hz => hz.1.1

theorem rightSideOf_subset_H : rightSideOf (arcRange γ) ⊆ H := fun _ hz => hz.1.1

theorem disjoint_leftSideOf_arcRange : Disjoint (leftSideOf (arcRange γ)) (arcRange γ) :=
  Set.disjoint_left.2 fun _ hz h => hz.1.2 h

theorem disjoint_rightSideOf_arcRange : Disjoint (rightSideOf (arcRange γ)) (arcRange γ) :=
  Set.disjoint_left.2 fun _ hz h => hz.1.2 h

theorem continuousOn_cayley_H : ContinuousOn cayley H := fun z hz =>
  (continuousAt_cayley_of_mem_Hbar (le_of_lt (show (0 : ℝ) < z.im from hz))).continuousWithinAt

theorem isOpen_leftSide (hγ : IsProperArc γ) : IsOpen (leftSideOf (arcRange γ)) := by
  have e : leftSideOf (arcRange γ) = H ∩ cayley ⁻¹' crossSide (toDisc γ) 1 := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1.1, (hγ.mem_leftSideOf_iff hz.1.1).1 hz⟩
    · rintro ⟨hz, h⟩
      exact (hγ.mem_leftSideOf_iff hz).2 h
  rw [e]
  exact continuousOn_cayley_H.isOpen_inter_preimage QuantumZipper.isOpen_H
    (hγ.isDiscCrosscut_toDisc.isOpen_crossSide (Or.inl rfl))

theorem isOpen_rightSide (hγ : IsProperArc γ) : IsOpen (rightSideOf (arcRange γ)) := by
  have e : rightSideOf (arcRange γ) = H ∩ cayley ⁻¹' crossSide (toDisc γ) (-1) := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1.1, (hγ.mem_rightSideOf_iff hz.1.1).1 hz⟩
    · rintro ⟨hz, h⟩
      exact (hγ.mem_rightSideOf_iff hz).2 h
  rw [e]
  exact continuousOn_cayley_H.isOpen_inter_preimage QuantumZipper.isOpen_H
    (hγ.isDiscCrosscut_toDisc.isOpen_crossSide (Or.inr rfl))

/-- A preconnected subset of `ℍ \ β` with a point outside `R` lies in `L`. -/
theorem subset_leftSide_of (hβ : IsProperArc β) {S : Set ℂ} (hS : IsPreconnected S) (hSH : S ⊆ H)
    (hSβ : Disjoint S (arcRange β)) {z : ℂ} (hz : z ∈ S) (hzR : z ∉ rightSideOf (arcRange β)) :
    S ⊆ leftSideOf (arcRange β) := by
  have hcov : S ⊆ leftSideOf (arcRange β) ∪ rightSideOf (arcRange β) := fun w hw =>
    hβ.mem_leftSideOf_or_mem_rightSideOf (hSH hw) (Set.disjoint_left.1 hSβ hw)
  rcases hS.subset_or_subset (isOpen_leftSide hβ) (isOpen_rightSide hβ) hβ.disjoint_leftSideOf_rightSideOf hcov
    with h | h
  · exact h
  · exact absurd (h hz) hzR

/-- A preconnected subset of `ℍ \ β` with a point in `R` lies in `R`. -/
theorem subset_rightSide_of (hβ : IsProperArc β) {S : Set ℂ} (hS : IsPreconnected S) (hSH : S ⊆ H)
    (hSβ : Disjoint S (arcRange β)) {z : ℂ} (hz : z ∈ S) (hzR : z ∈ rightSideOf (arcRange β)) :
    S ⊆ rightSideOf (arcRange β) := by
  have hcov : S ⊆ leftSideOf (arcRange β) ∪ rightSideOf (arcRange β) := fun w hw =>
    hβ.mem_leftSideOf_or_mem_rightSideOf (hSH hw) (Set.disjoint_left.1 hSβ hw)
  rcases hS.subset_or_subset (isOpen_leftSide hβ) (isOpen_rightSide hβ) hβ.disjoint_leftSideOf_rightSideOf hcov
    with h | h
  · exact absurd hzR (Set.disjoint_left.1 hβ.disjoint_leftSideOf_rightSideOf (h hz))
  · exact h

/-- The image of an interval of positive times avoiding `β` is a preconnected subset of `ℍ \ β`. -/
theorem isPreconnected_image (hα : IsProperArc α) {I : Set ℝ} (hI : IsPreconnected I) (hI0 : I ⊆ Ici 0) :
    IsPreconnected (α '' I) :=
  hI.image _ (hα.cont.mono hI0)

theorem image_subset_H (hα : IsProperArc α) {I : Set ℝ} (hI : I ⊆ Ioi 0) : α '' I ⊆ H := by
  rintro _ ⟨t, ht, rfl⟩
  exact hα.mem_H t (hI ht)

/-! ### Heights and arrivals -/

/-- **The largest height met up to time `τ`.** -/
theorem exists_max_height (hα : IsProperArc α) (hβ : IsProperArc β) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ ρ, 0 ≤ ρ ∧ ∃ tρ ∈ Icc 0 τ, α tρ = β ρ ∧ ∀ t ∈ Icc 0 τ, ∀ c, 0 ≤ c → α t = β c → c ≤ ρ := by
  set K := α '' Icc 0 τ with hKdef
  have hK : IsCompact K := isCompact_image_Icc hα le_rfl
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hβ.tendsto (B + 1))
  have hCc : IsClosed (Ici 0 ∩ β ⁻¹' K) := hβ.cont.preimage_isClosed_of_isClosed isClosed_Ici hK.isClosed
  have hsub : Ici 0 ∩ β ⁻¹' K ⊆ Icc 0 N := by
    rintro c ⟨hc0, hcK⟩
    refine ⟨hc0, ?_⟩
    by_contra hcN
    push Not at hcN
    have := hN c hcN.le
    have := hB _ hcK
    linarith
  have hC : IsCompact (Ici 0 ∩ β ⁻¹' K) := isCompact_Icc.of_isClosed_subset hCc hsub
  have h0 : (0 : ℝ) ∈ Ici 0 ∩ β ⁻¹' K :=
    ⟨mem_Ici.2 le_rfl, ⟨0, ⟨le_rfl, hτ⟩, by rw [hα.zero, hβ.zero]⟩⟩
  obtain ⟨ρ, ⟨hρ0, hρK⟩, hρmax⟩ := hC.exists_isGreatest ⟨0, h0⟩
  obtain ⟨tρ, htρ, e⟩ := hρK
  exact ⟨ρ, hρ0, tρ, htρ, e, fun t ht c hc htc => hρmax ⟨mem_Ici.2 hc, ⟨t, ht, htc⟩⟩⟩

/-- **Arrival from the left** (first step of the proof of Proposition 4.19). If `s` is the first time at which `α`
meets `β` above the height `h`, the excursion of `α` arriving at time `s` lies in the left side of `β` and starts
from a contact of height at most `h`, after which `α` does not meet `β([0, h])` up to time `s`. -/
theorem exists_arrival (hα : IsProperArc α) (hβ : IsProperArc β) {D : Set ℝ} (hD : IsDenseAbove D)
    (h1 : ∀ a ∈ D, NoRightFirstContact α β a) {h s c : ℝ} (hh : 0 ≤ h) (hs : 0 ≤ s) (hch : h < c)
    (hsc : α s = β c) (hfirst : ∀ t ∈ Ico 0 s, α t ∉ β '' Ioi h) :
    ∃ σ ∈ Ico 0 s, ∃ c' ∈ Icc 0 h, α σ = β c' ∧ (∀ t ∈ Ioc σ s, α t ∉ β '' Icc 0 h) ∧
      ∀ t ∈ Ioo σ s, α t ∈ leftSideOf (arcRange β) := by
  have hc0 : 0 ≤ c := hh.trans hch.le
  set C := Icc 0 s ∩ α ⁻¹' (β '' Icc 0 h) with hCdef
  have hCc : IsClosed C := (hα.cont.mono fun _ ht => mem_Ici.2 ht.1).preimage_isClosed_of_isClosed isClosed_Icc
    (isCompact_image_Icc hβ le_rfl).isClosed
  have hC : IsCompact C := isCompact_Icc.of_isClosed_subset hCc inter_subset_left
  have h0 : (0 : ℝ) ∈ C := ⟨⟨le_rfl, hs⟩, ⟨0, ⟨le_rfl, hh⟩, by rw [hα.zero, hβ.zero]⟩⟩
  obtain ⟨σ, ⟨hσs, hσK⟩, hσmax⟩ := hC.exists_isGreatest ⟨0, h0⟩
  obtain ⟨c', hc', e'⟩ := hσK
  have hnot : α s ∉ β '' Icc 0 h := by
    rintro ⟨c'', hc'', e''⟩
    have := eq_height hβ hc''.1 hc0 (e''.trans hsc)
    linarith [hc''.2]
  have hσlt : σ < s := lt_of_le_of_ne hσs.2 fun he => hnot (he ▸ ⟨c', hc', e'⟩)
  have hafter : ∀ t ∈ Ioc σ s, α t ∉ β '' Icc 0 h := by
    intro t ht hmem
    have := hσmax ⟨⟨hσs.1.trans ht.1.le, ht.2⟩, hmem⟩
    linarith [ht.1]
  have hoff : ∀ t ∈ Ioo σ s, α t ∉ arcRange β := by
    intro t ht hmem
    rcases (mem_arcRange_iff hh).1 hmem with hm | hm
    · exact hafter t ⟨ht.1, ht.2.le⟩ hm
    · exact hfirst t ⟨hσs.1.trans ht.1.le, ht.2⟩ hm
  refine ⟨σ, ⟨hσs.1, hσlt⟩, c', hc', e'.symm, hafter, ?_⟩
  -- the excursion is in `L`: by (H1) it has a point outside `R`
  obtain ⟨a, haD, hha, hac⟩ := hD h c hh hch
  have hs0 : 0 < s := lt_of_le_of_lt hσs.1 hσlt
  obtain ⟨t₁, ht₁, ht₁R⟩ := h1 a haD s hs0 ⟨c, mem_Ioi.2 hac, hsc.symm⟩
    (fun t ht hmem => hfirst t ht (image_mono (fun x hx => mem_Ioi.2 (hha.trans_le (mem_Ici.1 hx))) hmem))
    (s - σ) (by linarith)
  rw [sub_sub_cancel] at ht₁
  have hsub := subset_leftSide_of hβ (isPreconnected_image hα isPreconnected_Ioo
    (fun t ht => mem_Ici.2 (hσs.1.trans ht.1.le)))
    (image_subset_H hα fun t ht => mem_Ioi.2 (lt_of_le_of_lt hσs.1 ht.1))
    (Set.disjoint_left.2 (by rintro _ ⟨t, ht, rfl⟩; exact hoff t ht)) ⟨t₁, ht₁, rfl⟩ ht₁R
  exact fun t ht => hsub ⟨t, ht, rfl⟩

/-- **The first contact above a height.** If `α` meets `β` above `h` before time `τ` and the point `β h` is not met
up to time `τ`, there is a first time `s ≤ τ` at which `α` meets `β` above `h`. -/
theorem exists_first_above (hα : IsProperArc α) (hβ : IsProperArc β) {h τ t₀ c₀ : ℝ} (hh : 0 ≤ h)
    (ht₀ : t₀ ∈ Icc 0 τ) (hc₀ : h < c₀) (e₀ : α t₀ = β c₀) (hnot : ∀ t ∈ Icc 0 τ, α t ≠ β h) :
    ∃ s ∈ Icc 0 τ, ∃ c, h < c ∧ α s = β c ∧ ∀ t ∈ Ico 0 s, α t ∉ β '' Ioi h := by
  set E := Ici 0 ∩ α ⁻¹' (β '' Ici h) with hEdef
  have hEc : IsClosed E := hα.cont.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_image_Ici hβ hh)
  have hne : E.Nonempty := ⟨t₀, mem_Ici.2 ht₀.1, ⟨c₀, mem_Ici.2 hc₀.le, e₀.symm⟩⟩
  have hbdd : BddBelow E := ⟨0, fun t ht => mem_Ici.1 ht.1⟩
  have hs := hEc.csInf_mem hne hbdd
  set s := sInf E
  have hsτ : s ≤ τ := (csInf_le hbdd ⟨mem_Ici.2 ht₀.1, ⟨c₀, mem_Ici.2 hc₀.le, e₀.symm⟩⟩).trans ht₀.2
  obtain ⟨c, hc, e⟩ := hs.2
  have hsI : s ∈ Icc 0 τ := ⟨mem_Ici.1 hs.1, hsτ⟩
  have hch : h < c := lt_of_le_of_ne (mem_Ici.1 hc) fun he => hnot s hsI (by rw [← e, he])
  refine ⟨s, hsI, c, hch, e.symm, fun t ht hmem => ?_⟩
  have := csInf_le hbdd ⟨mem_Ici.2 ht.1, image_mono (fun x hx => mem_Ici.2 (mem_Ioi.1 hx).le) hmem⟩
  linarith [ht.2]

/-! ### Crossing in the left side -/

theorem discTime_lt_discTime {t t' : ℝ} (ht : 0 ≤ t) (htt' : t < t') : discTime t < discTime t' := by
  rw [discTime, discTime, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem discTime_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ discTime t := (discTime_mem_Ico ht).1

theorem discTime_lt_one {t : ℝ} (ht : 0 ≤ t) : discTime t < 1 := (discTime_mem_Ico ht).2

theorem arcTime_ge {a p : ℝ} (ha : 0 ≤ a) (hp : discTime a ≤ p) (hp1 : p < 1) : a ≤ arcTime p := by
  have h := strictMonoOn_arcTime.monotoneOn (discTime_mem_Ico ha) ⟨(discTime_nonneg ha).trans hp, hp1⟩ hp
  rwa [arcTime_discTime ha] at h

theorem arcTime_le {b p : ℝ} (hb : 0 ≤ b) (hp0 : 0 ≤ p) (hp : p ≤ discTime b) : arcTime p ≤ b := by
  have h := strictMonoOn_arcTime.monotoneOn ⟨hp0, hp.trans_lt (discTime_lt_one hb)⟩ (discTime_mem_Ico hb) hp
  rwa [arcTime_discTime hb] at h

/-- A point of `α` in `L ∪ β` is carried into the closed left side of the crosscut of `β`. -/
theorem toDisc_mem_closure_left (hα : IsProperArc α) (hβ : IsProperArc β) {p : ℝ} (hp : p ∈ Icc 0 1)
    (hgood : p < 1 → α (arcTime p) ∈ leftSideOf (arcRange β) ∨ α (arcTime p) ∈ arcRange β) :
    toDisc α p ∈ jordanIn (crossRange (toDisc β) ∪ semiArc 1) ∪ (crossRange (toDisc β) ∪ semiArc 1) := by
  rcases eq_or_lt_of_le hp.2 with h1 | h1
  · rw [h1, toDisc_one]
    exact Or.inr (Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, toDisc_one β⟩)
  · rw [toDisc_of_lt h1]
    have ht0 : 0 ≤ arcTime p := arcTime_nonneg ⟨hp.1, h1⟩
    rcases hgood h1 with hL | hA
    · exact Or.inl ((hβ.mem_leftSideOf_iff (leftSideOf_subset_H hL)).1 hL)
    · exact Or.inr (Or.inl ((hβ.cayley_mem_crossRange_iff (hα.mem_Hbar ht0)).2 hA))

/-- **Separation on the boundary of the left side.** Four points of the crosscut in increasing order: every
preconnected subset of the boundary curve containing the first and the third point contains the second or the
fourth. -/
theorem sep_of_lt {A : ℝ → ℂ} (hA : IsDiscCrosscut A) {x₁ x₂ x₃ x₄ : ℝ} (h0 : 0 ≤ x₁) (h12 : x₁ < x₂)
    (h23 : x₂ < x₃) (h34 : x₃ < x₄) (h4 : x₄ ≤ 1) :
    ∀ K ⊆ crossRange A ∪ semiArc 1, IsPreconnected K → A x₁ ∈ K → A x₃ ∈ K → A x₂ ∈ K ∨ A x₄ ∈ K := by
  intro K hKΓ hK h1 h3
  by_contra hcon
  push Not at hcon
  obtain ⟨hn2, hn4⟩ := hcon
  have hI : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → Icc a b ⊆ Icc 0 1 := fun ha hb x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hcl : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → IsClosed (A '' Icc a b) := fun ha hb =>
    (isCompact_Icc.image_of_continuousOn (hA.cont.mono (hI ha hb))).isClosed
  have hsemi : IsClosed (semiArc 1) :=
    (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_le continuous_const (continuous_const.mul continuous_im))
  set u : Set ℂ := (A '' Icc 0 x₂ ∪ A '' Icc x₄ 1 ∪ semiArc 1)ᶜ with hu
  set v : Set ℂ := (A '' Icc x₂ x₄)ᶜ with hv
  have huo : IsOpen u :=
    (((hcl le_rfl (by linarith)).union (hcl (by linarith) le_rfl)).union hsemi).isOpen_compl
  have hvo : IsOpen v := (hcl (by linarith) (by linarith)).isOpen_compl
  have hx01 : ∀ x ∈ Icc x₂ x₄, x ∈ Icc (0 : ℝ) 1 := fun x hx => ⟨by linarith [hx.1], hx.2.trans h4⟩
  have hcov : K ⊆ u ∪ v := by
    intro z hz
    by_cases hzI : z ∈ A '' Icc x₂ x₄
    · obtain ⟨x, hx, rfl⟩ := hzI
      have hx2 : x ≠ x₂ := fun he => hn2 (he ▸ hz)
      have hx4 : x ≠ x₄ := fun he => hn4 (he ▸ hz)
      have hxo : x ∈ Ioo x₂ x₄ := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx2), lt_of_le_of_ne hx.2 hx4⟩
      refine Or.inl ?_
      simp only [hu, mem_compl_iff, mem_union, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rintro ⟨y, hy, hyx⟩
        have := hA.inj (hI le_rfl (by linarith) hy) (hx01 x hx) hyx
        linarith [hy.2, hxo.1]
      · rintro ⟨y, hy, hyx⟩
        have := hA.inj (hI (by linarith) le_rfl hy) (hx01 x hx) hyx
        linarith [hy.1, hxo.2]
      · rintro ⟨hn, -⟩
        have hb := hA.mem_disc x ⟨by linarith [hxo.1], by linarith [hxo.2]⟩
        rw [mem_ball, dist_zero_right] at hb
        linarith
    · exact Or.inr hzI
  have hdis : K ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z ⟨hz, hzu, hzv⟩ => ?_
    simp only [hu, mem_compl_iff, mem_union, not_or] at hzu
    rcases hKΓ hz with ⟨x, hx, rfl⟩ | hzs
    · rcases le_or_gt x x₂ with hle | hlt
      · exact hzu.1.1 ⟨x, ⟨hx.1, hle⟩, rfl⟩
      rcases le_or_gt x₄ x with hle' | hlt'
      · exact hzu.1.2 ⟨x, ⟨hle', hx.2⟩, rfl⟩
      · exact hzv ⟨x, ⟨hlt.le, hlt'.le⟩, rfl⟩
    · exact hzu.2 hzs
  rcases (isPreconnected_iff_subset_of_disjoint.1 hK) u v huo hvo hcov hdis with h | h
  · have := h h1
    simp only [hu, mem_compl_iff, mem_union, not_or] at this
    exact this.1.1 ⟨x₁, ⟨h0, h12.le⟩, rfl⟩
  · exact h h3 ⟨x₃, ⟨h23.le, h34.le⟩, rfl⟩

/-- **Two pieces of `α` in the closed left side of `β` with interleaved endpoints on `β` would cross.** -/
theorem false_of_interleave (hα : IsProperArc α) (hβ : IsProperArc β) {p₁ q₁ p₂ q₂ x₁ x₂ x₃ x₄ : ℝ}
    (hp₁ : 0 ≤ p₁) (hpq₁ : p₁ < q₁) (hqp : q₁ < p₂) (hpq₂ : p₂ < q₂) (hq₂ : q₂ ≤ 1)
    (hx₁ : 0 ≤ x₁) (h12 : x₁ < x₂) (h23 : x₂ < x₃) (h34 : x₃ < x₄) (hx₄ : x₄ ≤ 1)
    (hQ : ∀ p ∈ Icc p₁ q₁,
      toDisc α p ∈ jordanIn (crossRange (toDisc β) ∪ semiArc 1) ∪ (crossRange (toDisc β) ∪ semiArc 1))
    (hP : ∀ p ∈ Icc p₂ q₂,
      toDisc α p ∈ jordanIn (crossRange (toDisc β) ∪ semiArc 1) ∪ (crossRange (toDisc β) ∪ semiArc 1))
    (e₁ : toDisc α p₁ = toDisc β x₁) (e₃ : toDisc α q₁ = toDisc β x₃) (e₂ : toDisc α p₂ = toDisc β x₂)
    (e₄ : toDisc α q₂ = toDisc β x₄) : False := by
  have hA := hβ.isDiscCrosscut_toDisc
  have hX := hα.isDiscCrosscut_toDisc
  have hΓ := hA.isJordanCurve (σ := 1) (Or.inl rfl)
  have hmemΓ : ∀ x ∈ Icc (0 : ℝ) 1, toDisc β x ∈ crossRange (toDisc β) ∪ semiArc 1 :=
    fun x hx => Or.inl ⟨x, hx, rfl⟩
  have haff : ∀ {p q : ℝ}, p ≤ q → ∀ w ∈ Icc (0 : ℝ) 1, p + w * (q - p) ∈ Icc p q := by
    intro p q hpq w hw
    constructor
    · nlinarith [hw.1]
    · nlinarith [hw.2]
  have hsub : ∀ {p q : ℝ}, 0 ≤ p → q ≤ 1 → Icc p q ⊆ Icc (0 : ℝ) 1 := fun hp hq x hx =>
    ⟨hp.trans hx.1, hx.2.trans hq⟩
  set P : ℝ → ℂ := fun w => toDisc α (p₂ + w * (q₂ - p₂)) with hPdef
  set Q : ℝ → ℂ := fun w => toDisc α (p₁ + w * (q₁ - p₁)) with hQdef
  have hPc : ContinuousOn P (Icc 0 1) :=
    hX.cont.comp (by fun_prop) fun w hw => hsub (by linarith) hq₂ (haff hpq₂.le w hw)
  have hQc : ContinuousOn Q (Icc 0 1) :=
    hX.cont.comp (by fun_prop) fun w hw => hsub hp₁ (by linarith) (haff hpq₁.le w hw)
  have hab : toDisc β x₂ ≠ toDisc β x₄ := fun he =>
    (ne_of_lt (h23.trans h34)) (hA.inj ⟨by linarith, by linarith⟩ ⟨by linarith, hx₄⟩ he)
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := jordan_crossing hΓ (hmemΓ x₂ ⟨by linarith, by linarith⟩)
    (hmemΓ x₄ ⟨by linarith, hx₄⟩) hab (hmemΓ x₁ ⟨hx₁, by linarith⟩) (hmemΓ x₃ ⟨by linarith, by linarith⟩)
    (sep_of_lt hA hx₁ h12 h23 h34 hx₄) hPc hQc (fun w hw => hP _ (haff hpq₂.le w hw))
    (fun w hw => hQ _ (haff hpq₁.le w hw)) (by simp [hPdef, e₂]) (by simp [hPdef, e₄])
    (by simp [hQdef, e₁]) (by simp [hQdef, e₃])
  have h₁ := haff hpq₂.le w₁ hw₁
  have h₂ := haff hpq₁.le w₂ hw₂
  have := hX.inj (hsub (by linarith) hq₂ h₁) (hsub hp₁ (by linarith) h₂) hw
  linarith [h₁.1, h₂.2]


/-- Points of a closed time interval whose ends are on `β` and whose interior is in `L`. -/
theorem good_of_excursion {σ s : ℝ} (hσβ : α σ ∈ arcRange β) (hsβ : α s ∈ arcRange β)
    (hL : ∀ t ∈ Ioo σ s, α t ∈ leftSideOf (arcRange β)) :
    ∀ t ∈ Icc σ s, α t ∈ leftSideOf (arcRange β) ∨ α t ∈ arcRange β := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · exact Or.inr (h ▸ hσβ)
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · exact Or.inr (h' ▸ hsβ)
  exact Or.inl (hL t ⟨h, h'⟩)

theorem mem_arcRange_of_eq {t c : ℝ} (hc : 0 ≤ c) (e : α t = β c) : α t ∈ arcRange β :=
  ⟨c, mem_Ici.2 hc, e.symm⟩

/-- **Two arrival excursions in `L` with interleaved heights would cross.** -/
theorem false_of_arrivals (hα : IsProperArc α) (hβ : IsProperArc β) {σ₁ s₁ σ₂ s₂ c₁ d₁ c₂ d₂ : ℝ}
    (hσ₁ : 0 ≤ σ₁) (h₁ : σ₁ < s₁) (h₁₂ : s₁ < σ₂) (h₂ : σ₂ < s₂) (hc₁ : 0 ≤ c₁) (hc : c₁ < c₂)
    (hcd : c₂ < d₁) (hd : d₁ < d₂) (e₁ : α σ₁ = β c₁) (f₁ : α s₁ = β d₁) (e₂ : α σ₂ = β c₂)
    (f₂ : α s₂ = β d₂) (hL₁ : ∀ t ∈ Ioo σ₁ s₁, α t ∈ leftSideOf (arcRange β))
    (hL₂ : ∀ t ∈ Ioo σ₂ s₂, α t ∈ leftSideOf (arcRange β)) : False := by
  have hs₁ : 0 ≤ s₁ := by linarith
  have hσ₂ : 0 ≤ σ₂ := by linarith
  have hs₂ : 0 ≤ s₂ := by linarith
  have hgood : ∀ {σ s c d : ℝ}, 0 ≤ σ → 0 ≤ s → 0 ≤ c → 0 ≤ d → α σ = β c → α s = β d →
      (∀ t ∈ Ioo σ s, α t ∈ leftSideOf (arcRange β)) → ∀ p ∈ Icc (discTime σ) (discTime s),
        toDisc α p ∈ jordanIn (crossRange (toDisc β) ∪ semiArc 1) ∪ (crossRange (toDisc β) ∪ semiArc 1) := by
    intro σ s c d hσ hs hc hd e f hL p hp
    have hp0 : 0 ≤ p := (discTime_nonneg hσ).trans hp.1
    have hp1 : p < 1 := hp.2.trans_lt (discTime_lt_one hs)
    refine toDisc_mem_closure_left hα hβ ⟨hp0, hp1.le⟩ fun _ => ?_
    exact good_of_excursion (mem_arcRange_of_eq hc e) (mem_arcRange_of_eq hd f) hL _
      ⟨arcTime_ge hσ hp.1 hp1, arcTime_le hs hp0 hp.2⟩
  refine false_of_interleave hα hβ (discTime_nonneg hσ₁) (discTime_lt_discTime hσ₁ h₁)
    (discTime_lt_discTime hs₁ h₁₂) (discTime_lt_discTime hσ₂ h₂) (discTime_lt_one hs₂).le
    (discTime_nonneg hc₁) (discTime_lt_discTime hc₁ hc) (discTime_lt_discTime (by linarith) hcd)
    (discTime_lt_discTime (by linarith) hd) (discTime_lt_one (by linarith)).le
    (hgood hσ₁ hs₁ hc₁ (by linarith) e₁ f₁ hL₁) (hgood hσ₂ hs₂ (by linarith) (by linarith) e₂ f₂ hL₂) ?_ ?_ ?_ ?_
  · rw [toDisc_discTime α hσ₁, toDisc_discTime β hc₁, e₁]
  · rw [toDisc_discTime α hs₁, toDisc_discTime β (by linarith), f₁]
  · rw [toDisc_discTime α hσ₂, toDisc_discTime β (by linarith), e₂]
  · rw [toDisc_discTime α hs₂, toDisc_discTime β (by linarith), f₂]

/-- **An arrival excursion in `L` and a final path in `L ∪ β` with interleaved heights would cross.** -/
theorem false_of_arrival_tail (hα : IsProperArc α) (hβ : IsProperArc β) {σ₁ s₁ σ₂ c₁ d₁ c₂ : ℝ}
    (hσ₁ : 0 ≤ σ₁) (h₁ : σ₁ < s₁) (h₁₂ : s₁ < σ₂) (hc₁ : 0 ≤ c₁) (hc : c₁ < c₂) (hcd : c₂ < d₁)
    (e₁ : α σ₁ = β c₁) (f₁ : α s₁ = β d₁) (e₂ : α σ₂ = β c₂)
    (hL₁ : ∀ t ∈ Ioo σ₁ s₁, α t ∈ leftSideOf (arcRange β))
    (hT : ∀ t, σ₂ ≤ t → α t ∈ leftSideOf (arcRange β) ∨ α t ∈ arcRange β) : False := by
  have hs₁ : 0 ≤ s₁ := by linarith
  have hσ₂ : 0 ≤ σ₂ := by linarith
  refine false_of_interleave hα hβ (discTime_nonneg hσ₁) (discTime_lt_discTime hσ₁ h₁)
    (discTime_lt_discTime hs₁ h₁₂) (discTime_lt_one hσ₂) le_rfl
    (discTime_nonneg hc₁) (discTime_lt_discTime hc₁ hc) (discTime_lt_discTime (by linarith) hcd)
    (discTime_lt_one (by linarith)) le_rfl ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have hp0 : 0 ≤ p := (discTime_nonneg hσ₁).trans hp.1
    have hp1 : p < 1 := hp.2.trans_lt (discTime_lt_one hs₁)
    refine toDisc_mem_closure_left hα hβ ⟨hp0, hp1.le⟩ fun _ => ?_
    exact good_of_excursion (mem_arcRange_of_eq hc₁ e₁) (mem_arcRange_of_eq (by linarith) f₁) hL₁ _
      ⟨arcTime_ge hσ₁ hp.1 hp1, arcTime_le hs₁ hp0 hp.2⟩
  · intro p hp
    exact toDisc_mem_closure_left hα hβ ⟨(discTime_nonneg hσ₂).trans hp.1, hp.2⟩ fun hp1 =>
      hT _ (arcTime_ge hσ₂ hp.1 hp1)
  · rw [toDisc_discTime α hσ₁, toDisc_discTime β hc₁, e₁]
  · rw [toDisc_discTime α hs₁, toDisc_discTime β (by linarith), f₁]
  · rw [toDisc_discTime α hσ₂, toDisc_discTime β (by linarith), e₂]
  · rw [toDisc_one, toDisc_one]

theorem zero_notMem_H : (0 : ℂ) ∉ H := fun h => by
  have : (0 : ℝ) < (0 : ℂ).im := h
  simp at this


/-! ### The theorem -/

/-- **Wang–Wu Proposition 4.19, deterministic part.** Let `α`, `β` be simple proper arcs of `ℍ`. If, for a dense set
`D` of heights `a`, the first contact of `α` with the tail `β([a, ∞))` is not approached from the right side of `β`
(`NoRightFirstContact`) and `α` does not end in the right side of `β` without meeting that tail (`NoRightEscape`),
then `α` avoids the right side of `β`. -/
theorem disjoint_arcRange_rightSideOf_of_tails (hα : IsProperArc α) (hβ : IsProperArc β) {D : Set ℝ}
    (hD : IsDenseAbove D) (h1 : ∀ a ∈ D, NoRightFirstContact α β a) (h2 : ∀ a ∈ D, NoRightEscape α β a) :
    Disjoint (arcRange α) (rightSideOf (arcRange β)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨ts, hts0, rfl⟩ hR
  have hts : 0 < ts := by
    rcases eq_or_lt_of_le (mem_Ici.1 hts0) with h | h
    · rw [← h, hα.zero] at hR
      exact absurd (rightSideOf_subset_H hR) zero_notMem_H
    · exact h
  have hRβ : α ts ∉ arcRange β := Set.disjoint_left.1 disjoint_rightSideOf_arcRange hR
  have hα0 : α 0 ∈ arcRange β := ⟨0, mem_Ici.2 le_rfl, by rw [hα.zero, hβ.zero]⟩
  have hinj : ∀ {t t' : ℝ}, 0 ≤ t → 0 ≤ t' → α t = α t' → t = t' := fun ht ht' h =>
    hα.inj (mem_Ici.2 ht) (mem_Ici.2 ht') h
  -- the last contact `τ₁` before `ts`
  set C₁ := Icc 0 ts ∩ α ⁻¹' arcRange β with hC₁def
  have hC₁c : IsClosed C₁ := (hα.cont.mono fun _ ht => mem_Ici.2 ht.1).preimage_isClosed_of_isClosed isClosed_Icc
    hβ.isClosed_arcRange
  have hC₁ : IsCompact C₁ := isCompact_Icc.of_isClosed_subset hC₁c inter_subset_left
  obtain ⟨τ₁, ⟨hτ₁I, hτ₁β⟩, hτ₁max⟩ := hC₁.exists_isGreatest ⟨0, ⟨le_rfl, hts.le⟩, hα0⟩
  have hτ₁lt : τ₁ < ts := lt_of_le_of_ne hτ₁I.2 fun he => hRβ (he ▸ hτ₁β)
  have hτ₁0 : 0 ≤ τ₁ := hτ₁I.1
  have hnoc₁ : ∀ t ∈ Ioc τ₁ ts, α t ∉ arcRange β := fun t ht hm => by
    have := hτ₁max ⟨⟨hτ₁0.trans ht.1.le, ht.2⟩, hm⟩
    linarith [ht.1]
  -- the largest height `ρ` up to `τ₁`
  obtain ⟨ρ, hρ0, tρ, htρ, eρ, hρmax⟩ := exists_max_height hα hβ hτ₁0
  -- the excursion of `α` through `ts` lies in `R`
  have hexc : ∀ t, τ₁ < t → (∀ t' ∈ Ioc τ₁ t, α t' ∉ arcRange β) → α t ∈ rightSideOf (arcRange β) := by
    intro t ht hno
    have hI : Ioc τ₁ (max t ts) ⊆ Ici 0 := fun x hx => mem_Ici.2 (hτ₁0.trans hx.1.le)
    have hsub := subset_rightSide_of hβ (isPreconnected_image hα isPreconnected_Ioc hI)
      (image_subset_H hα fun x hx => mem_Ioi.2 (lt_of_le_of_lt hτ₁0 hx.1))
      (Set.disjoint_left.2 (by
        rintro _ ⟨x, hx, rfl⟩
        rcases le_max_iff.1 hx.2 with hxt | hxs
        · exact hno x ⟨hx.1, hxt⟩
        · exact hnoc₁ x ⟨hx.1, hxs⟩))
      ⟨ts, ⟨hτ₁lt, le_max_right _ _⟩, rfl⟩ hR
    exact hsub ⟨t, ⟨ht, le_max_left _ _⟩, rfl⟩
  -- heights up to `τ₁` are at most `ρ`
  have hρa : ∀ a, ρ < a → ∀ t ∈ Icc 0 τ₁, α t ∉ β '' Ici a := by
    rintro a ha t ht ⟨c, hc, e⟩
    have := hρmax t ht c (hρ0.trans (ha.le.trans hc)) e.symm
    linarith [mem_Ici.1 hc]
  -- the excursion ends: contacts after `ts`
  by_cases hE₂ : ∃ t, ts ≤ t ∧ α t ∈ arcRange β
  swap
  · -- no further contact: `α` stays in `R`, contradicting (H2)
    push Not at hE₂
    have hallR : ∀ t, τ₁ < t → α t ∈ rightSideOf (arcRange β) := fun t ht =>
      hexc t ht fun t' ht' => by
        rcases le_total t' ts with h | h
        · exact hnoc₁ t' ⟨ht'.1, h⟩
        · exact hE₂ t' h
    obtain ⟨a, haD, hρa', -⟩ := hD ρ (ρ + 1) hρ0 (by linarith)
    have hfreq := h2 a haD fun t ht hm => by
      rcases le_total t τ₁ with h | h
      · exact hρa a hρa' t ⟨ht, h⟩ hm
      · rcases eq_or_lt_of_le h with h' | h'
        · exact hρa a hρa' t ⟨ht, h'.symm.le⟩ hm
        · exact Set.disjoint_left.1 disjoint_rightSideOf_arcRange (hallR t h')
            (image_Ici_subset_arcRange (hρ0.trans hρa'.le) hm)
    obtain ⟨t, htR, htτ⟩ := (hfreq.and_eventually (eventually_gt_atTop τ₁)).exists
    exact htR (hallR t htτ)
  -- `τ₂`: the end of the excursion
  set E₂ := Ici ts ∩ α ⁻¹' arcRange β with hE₂def
  have hE₂c : IsClosed E₂ := (hα.cont.mono fun _ ht => mem_Ici.2 (hts.le.trans ht)).preimage_isClosed_of_isClosed
    isClosed_Ici hβ.isClosed_arcRange
  have hbdd₂ : BddBelow E₂ := ⟨ts, fun t ht => ht.1⟩
  obtain ⟨t₂, ht₂, ht₂β⟩ := hE₂
  have hτ₂ := hE₂c.csInf_mem ⟨t₂, ht₂, ht₂β⟩ hbdd₂
  set τ₂ := sInf E₂ with hτ₂def
  have hτ₂ts : ts < τ₂ := lt_of_le_of_ne hτ₂.1 fun he => hRβ (he ▸ hτ₂.2)
  have hnoc₂ : ∀ t ∈ Ioo τ₁ τ₂, α t ∉ arcRange β := by
    intro t ht hm
    rcases le_total t ts with h | h
    · exact hnoc₁ t ⟨ht.1, h⟩ hm
    · have := csInf_le hbdd₂ ⟨h, hm⟩
      linarith [ht.2]
  obtain ⟨c₂, hc₂0, e₂⟩ := hτ₂.2
  have hc₂0' : 0 ≤ c₂ := mem_Ici.1 hc₂0
  have hτ₂0 : 0 < τ₂ := hts.trans hτ₂ts
  -- `c₂ < ρ`, by (H1)
  have hc₂ρ : c₂ < ρ := by
    by_contra hle
    push Not at hle
    have hne : c₂ ≠ ρ := fun he => by
      have := hinj hτ₂0.le htρ.1 (by rw [← e₂, he, eρ])
      linarith [htρ.2]
    obtain ⟨a, haD, hρa', hac₂⟩ := hD ρ c₂ hρ0 (lt_of_le_of_ne hle (Ne.symm hne))
    obtain ⟨t, ht, htR⟩ := h1 a haD τ₂ hτ₂0 ⟨c₂, mem_Ioi.2 hac₂, e₂⟩
      (fun t ht hm => by
        rcases le_total t τ₁ with h | h
        · exact hρa a hρa' t ⟨ht.1, h⟩ hm
        · rcases eq_or_lt_of_le h with h' | h'
          · exact hρa a hρa' t ⟨ht.1, h'.symm.le⟩ hm
          · exact hnoc₂ t ⟨h', ht.2⟩ (image_Ici_subset_arcRange (hρ0.trans hρa'.le) hm))
      (τ₂ - τ₁) (by linarith)
    rw [sub_sub_cancel] at ht
    exact htR (hexc t ht.1 fun t' ht' => hnoc₂ t' ⟨ht'.1, ht'.2.trans_lt ht.2⟩)
  -- heights up to `τ₂` are at most `ρ`
  have hle₂ : ∀ t ∈ Icc 0 τ₂, ∀ c, 0 ≤ c → α t = β c → c ≤ ρ := by
    intro t ht c hc e
    rcases le_total t τ₁ with h | h
    · exact hρmax t ⟨ht.1, h⟩ c hc e
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', ← e₂] at e
      rw [eq_height hβ hc hc₂0' e.symm]
      exact hc₂ρ.le
    · rcases eq_or_lt_of_le h with h'' | h''
      · exact hρmax t ⟨ht.1, h''.symm.le⟩ c hc e
      · exact absurd (mem_arcRange_of_eq hc e) (hnoc₂ t ⟨h'', h'⟩)
  have hτ₁τ₂ : τ₁ < τ₂ := hτ₁lt.trans hτ₂ts
  by_cases hup : ∃ t, τ₂ ≤ t ∧ α t ∈ β '' Ioi ρ
  · -- (2a): a later height above `ρ`
    set E₃ := Ici τ₂ ∩ α ⁻¹' (β '' Ici ρ) with hE₃def
    have hE₃c : IsClosed E₃ :=
      (hα.cont.mono fun _ ht => mem_Ici.2 (hτ₂0.le.trans ht)).preimage_isClosed_of_isClosed isClosed_Ici
        (isClosed_image_Ici hβ hρ0)
    have hbdd₃ : BddBelow E₃ := ⟨τ₂, fun t ht => ht.1⟩
    obtain ⟨t₃, ht₃, ht₃β⟩ := hup
    have hmem₃ : t₃ ∈ E₃ := ⟨ht₃, image_mono (fun x hx => mem_Ici.2 (mem_Ioi.1 hx).le) ht₃β⟩
    have hT := hE₃c.csInf_mem ⟨t₃, hmem₃⟩ hbdd₃
    set Tp := sInf E₃ with hTpdef
    have hTpτ₂ : τ₂ ≤ Tp := hT.1
    obtain ⟨cp, hcp, ep⟩ := hT.2
    have hρcp : ρ < cp := lt_of_le_of_ne (mem_Ici.1 hcp) fun he => by
      have := hinj (hτ₂0.le.trans hTpτ₂) htρ.1 (by rw [← ep, ← he, eρ])
      linarith [htρ.2]
    have hfirstp : ∀ t ∈ Ico 0 Tp, α t ∉ β '' Ioi ρ := by
      rintro t ht ⟨c, hc, e⟩
      rcases le_total t τ₂ with h | h
      · have := hle₂ t ⟨ht.1, h⟩ c (hρ0.trans (mem_Ioi.1 hc).le) e.symm
        linarith [mem_Ioi.1 hc]
      · have := csInf_le hbdd₃ ⟨h, ⟨c, mem_Ici.2 (mem_Ioi.1 hc).le, e⟩⟩
        linarith [ht.2]
    obtain ⟨σp, hσp, sp, hsp, esp, hafterp, hLp⟩ :=
      exists_arrival hα hβ hD h1 hρ0 (hτ₂0.le.trans hTpτ₂) hρcp ep.symm hfirstp
    have hσpτ₂ : τ₂ ≤ σp := by
      by_contra hlt
      push Not at hlt
      exact hafterp τ₂ ⟨hlt, hTpτ₂⟩ ⟨c₂, ⟨hc₂0', hc₂ρ.le⟩, e₂⟩
    have hsp0 : 0 < sp := lt_of_le_of_ne hsp.1 fun he => by
      have := hinj hσp.1 le_rfl (by rw [esp, ← he, hβ.zero, hα.zero])
      linarith
    have hspρ : sp < ρ := lt_of_le_of_ne hsp.2 fun he => by
      have := hinj hσp.1 htρ.1 (by rw [esp, he, eρ])
      linarith [htρ.2]
    obtain ⟨s, hs, c'', hc'', e'', hfirst''⟩ := exists_first_above hα hβ hsp0.le htρ hspρ eρ
      fun t ht he => by
        have := hinj ht.1 hσp.1 (by rw [he, esp])
        linarith [ht.2]
    obtain ⟨σ', hσ', c', hc', e', -, hL'⟩ := exists_arrival hα hβ hD h1 hsp0.le hs.1 hc'' e'' hfirst''
    have hc'sp : c' < sp := lt_of_le_of_ne hc'.2 fun he => by
      have := hinj hσ'.1 hσp.1 (by rw [e', he, esp])
      linarith [hσ'.2, hs.2]
    have hc''ρ : c'' ≤ ρ := hρmax s hs c'' (hsp0.le.trans hc''.le) e''
    exact false_of_arrivals hα hβ hσ'.1 hσ'.2 (by linarith [hs.2]) hσp.2 hc'.1 hc'sp hc'' (hc''ρ.trans_lt hρcp)
      e' e'' esp ep.symm hL' hLp
  · -- (2b): all heights at most `ρ`; `α` ends in `L`
    push Not at hup
    have hall : ∀ t, 0 ≤ t → ∀ c, 0 ≤ c → α t = β c → c ≤ ρ := by
      intro t ht c hc e
      rcases le_total t τ₂ with h | h
      · exact hle₂ t ⟨ht, h⟩ c hc e
      · by_contra hlt
        push Not at hlt
        exact hup t h ⟨c, hlt, e.symm⟩
    obtain ⟨a, haD, hρa', -⟩ := hD ρ (ρ + 1) hρ0 (by linarith)
    have hfreq := h2 a haD fun t ht ⟨c, hc, e⟩ => by
      have := hall t ht c (hρ0.trans (hρa'.le.trans hc)) e.symm
      linarith [mem_Ici.1 hc]
    obtain ⟨B, hB⟩ := (isCompact_image_Icc hβ (a := 0) (b := ρ) le_rfl).isBounded.exists_norm_le
    obtain ⟨T₀', hT₀'⟩ := Filter.eventually_atTop.1 (tendsto_atTop.1 hα.tendsto (B + 1))
    set T₀ := max T₀' (τ₂ + 1) with hT₀def
    have hT₀pos : 0 < T₀ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hfar : ∀ t, T₀ ≤ t → α t ∉ arcRange β := by
      rintro t ht ⟨c, hc, e⟩
      have hcρ := hall t (hT₀pos.le.trans ht) c (mem_Ici.1 hc) e.symm
      have h₁ := hB _ ⟨c, ⟨mem_Ici.1 hc, hcρ⟩, rfl⟩
      have h₂ := hT₀' t ((le_max_left _ _).trans ht)
      rw [← e] at h₂
      linarith
    obtain ⟨t₁, ht₁R, ht₁T⟩ := (hfreq.and_eventually (eventually_ge_atTop T₀)).exists
    have hLsub := subset_leftSide_of hβ (isPreconnected_image hα isPreconnected_Ici
        fun x hx => mem_Ici.2 (hT₀pos.le.trans hx))
      (image_subset_H hα fun x hx => mem_Ioi.2 (lt_of_lt_of_le hT₀pos hx))
      (Set.disjoint_left.2 (by rintro _ ⟨x, hx, rfl⟩; exact hfar x hx)) ⟨t₁, ht₁T, rfl⟩ ht₁R
    have hLtail : ∀ t, T₀ ≤ t → α t ∈ leftSideOf (arcRange β) := fun t ht => hLsub ⟨t, ht, rfl⟩
    have htsT₀ : ts < T₀ := by
      by_contra hle
      push Not at hle
      exact Set.disjoint_left.1 hβ.disjoint_leftSideOf_rightSideOf (hLtail ts hle) hR
    -- the last visit `T_L` of `R`
    set SR := Icc ts T₀ ∩ {t | α t ∈ rightSideOf (arcRange β)} with hSRdef
    have hSRne : SR.Nonempty := ⟨ts, ⟨le_rfl, htsT₀.le⟩, hR⟩
    have hSRbdd : BddAbove SR := ⟨T₀, fun t ht => ht.1.2⟩
    set TL := sSup SR with hTLdef
    have hTL1 : ts ≤ TL := le_csSup hSRbdd ⟨⟨le_rfl, htsT₀.le⟩, hR⟩
    have hTL2 : TL ≤ T₀ := csSup_le hSRne fun t ht => ht.1.2
    have hTLpos : 0 < TL := hts.trans_le hTL1
    have hafterR : ∀ t, TL < t → α t ∉ rightSideOf (arcRange β) := by
      intro t ht htR
      rcases le_total t T₀ with h | h
      · have := le_csSup hSRbdd ⟨⟨hTL1.trans ht.le, h⟩, htR⟩
        linarith
      · exact Set.disjoint_left.1 hβ.disjoint_leftSideOf_rightSideOf (hLtail t h) htR
    have hcont : ContinuousAt α TL := hα.cont.continuousAt (Ici_mem_nhds hTLpos)
    have hTLβ : α TL ∈ arcRange β := by
      by_contra hnot
      rcases hβ.mem_leftSideOf_or_mem_rightSideOf (hα.mem_H TL hTLpos) hnot with hL | hR'
      · obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
          (hcont.eventually ((isOpen_leftSide hβ).mem_nhds hL))
        obtain ⟨t, ht, htlt⟩ := exists_lt_of_lt_csSup hSRne (show TL - δ < TL by linarith)
        have htle : t ≤ TL := le_csSup hSRbdd ht
        have hd : dist t TL < δ := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith
        exact Set.disjoint_left.1 hβ.disjoint_leftSideOf_rightSideOf (hball hd) ht.2
      · obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
          (hcont.eventually ((isOpen_rightSide hβ).mem_nhds hR'))
        have hd : dist (TL + δ / 2) TL < δ := by
          rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
          linarith
        exact hafterR (TL + δ / 2) (by linarith) (hball hd)
    obtain ⟨cL, hcL, eL⟩ := hTLβ
    have hcL0 : 0 ≤ cL := mem_Ici.1 hcL
    have hcLρ : cL < ρ := lt_of_le_of_ne (hall TL hTLpos.le cL hcL0 eL.symm) fun he => by
      have := hinj hTLpos.le htρ.1 (by rw [← eL, he, eρ])
      linarith [htρ.2]
    have hcLpos : 0 < cL := lt_of_le_of_ne hcL0 fun he => by
      have := hinj hTLpos.le le_rfl (by rw [← eL, ← he, hβ.zero, hα.zero])
      linarith
    have hgood : ∀ t, TL ≤ t → α t ∈ leftSideOf (arcRange β) ∨ α t ∈ arcRange β := by
      intro t ht
      rcases eq_or_lt_of_le ht with h | h
      · exact Or.inr (h ▸ ⟨cL, hcL, eL⟩)
      · by_cases hm : α t ∈ arcRange β
        · exact Or.inr hm
        · rcases hβ.mem_leftSideOf_or_mem_rightSideOf (hα.mem_H t (hTLpos.trans h)) hm with hL | hR'
          · exact Or.inl hL
          · exact absurd hR' (hafterR t h)
    obtain ⟨s, hs, c'', hc'', e'', hfirst''⟩ := exists_first_above hα hβ hcL0 htρ hcLρ eρ
      fun t ht he => by
        have := hinj ht.1 hTLpos.le (by rw [he, eL])
        linarith [ht.2]
    obtain ⟨σ', hσ', c', hc', e', -, hL'⟩ := exists_arrival hα hβ hD h1 hcL0 hs.1 hc'' e'' hfirst''
    have hc'cL : c' < cL := lt_of_le_of_ne hc'.2 fun he => by
      have := hinj hσ'.1 hTLpos.le (by rw [e', he, eL])
      linarith [hσ'.2, hs.2]
    exact false_of_arrival_tail hα hβ hσ'.1 hσ'.2 (by linarith [hs.2]) hc'.1 hc'cL hc'' e' e'' eL.symm hL' hgood

end InteractingSLE.WangWu.Descent
