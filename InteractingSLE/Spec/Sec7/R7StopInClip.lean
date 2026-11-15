/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInErase

/-!
# Consequence R.4 for a mixed or outer pocket: the visit interval and the absence of a terminal gap

Packet PROVE-R7-STOPIN. Supplement §5.3, Lemma R.3 and Consequence R.4 (`source/spec/p433-480.md` L951–L971,
pp. 472–473):

> "**Consequence R.4.** Set `τ = T(y_C)` and `σ = T(x_C)`, using first visits of the contained frontiers, and allowing
> the terminal original-target time for `σ`. Then `η⁻¹(C) ⊂ (τ, σ)`. […] Before `τ`, no boundary point of the
> selected pocket can be reached: on a contained side this is reverse first-visit order; on an outer side, a contact is
> a contact with the intervening certified frontier and the same order applies. Since the original counterflow seed is
> outside `C`, continuity excludes an earlier visit. At `σ`, the contained barrier arcs from `x_C` to `y_C` are already
> in the old range. The components between those arcs are separated from the original target and are swallowed in the
> original domain. The part between an outer arm and its certified frontier is globally forbidden. A later open-`C`
> visit would therefore have to stay on one of the old simple frontier arcs for a nontrivial time interval, contrary to
> Aux. 42."

This file proves R.4 deterministically for an abstract pocket in the counterflow chart, with the source's ingredients
as hypotheses:

* `C` is open, bounded, in `ℍ`, the counterflow `η` is a continuous Loewner trace from `0`;
* **two barrier arcs** `B₁`, `B₂ : [0, 1] → C̄` from `x₀` (`B 0`) to `y₀` (`B 1`), in reverse first-visit order (the
  contained arm and the clipped certified frontier in a mixed pocket; the two clipped certified frontiers in an outer
  pocket — Lemma R.3);
* **the forbidden set** `F` (the exterior sides `E_R`, `E_L` read in the chart): open, avoided by `η`, every frontier
  point of `C` is in `F` or on a barrier (R.3: "An outer-arm point in the counterflow range is on the certified
  frontier"), and every point of `C̄ ∩ ∂F` in `ℍ` is on a barrier (the certified frontier bounds the forbidden side);
* **Aux. 42**: no nontrivial time interval of `η` stays in the union of the two barriers.

Results:

* **`mem_Ioo_of_barriers`**: (JP1) `η⁻¹(C) ⊂ (τ, σ)` (Consequence R.4, both halves);
* **`noFinal_of_attach`**: the absence of a terminal gap (R.4: "There is no positive terminal no-`C` interval before
  `σ`") from Aux. 37's attachment constancy along one barrier (§5.4: "On a contained strict-angle arm, the proof of
  Aux. 37 applies verbatim to that one arm"), exactly the landed argument of `Sec6.IsReversePocket.clock_lt_clock_σ`;
* **`isErasurePocket_of_barriers`**: `IsErasurePocket` from these and the equal gap endpoints (§5.4).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Sec7.R7StopIn

open Sec6

section Barriers

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C F : Set ℂ} {x₀ y₀ : ℂ} {B₁ B₂ : ℝ → ℂ} {τ σ : ℝ}

/-- A visited barrier point forces `y₀` to be visited (reverse first-visit order). -/
theorem y_mem_of_barrier {B : ℝ → ℂ} (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t) (hB1 : B 1 = y₀)
    {v t : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (h : B v ∈ η '' Icc 0 t) : y₀ ∈ η '' Icc 0 t :=
  hB1 ▸ hrev t v hv 1 ⟨zero_le_one, le_rfl⟩ hv.2 h

/-- A visited `x₀` forces the whole barrier to be visited (reverse first-visit order). -/
theorem mem_of_x_mem_barrier {B : ℝ → ℂ} (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hB0 : B 0 = x₀) {t : ℝ} (h : x₀ ∈ η '' Icc 0 t) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : B v ∈ η '' Icc 0 t :=
  hrev t 0 ⟨le_rfl, zero_le_one⟩ v hv hv.1 (hB0 ▸ h)

/-- **Consequence R.4: `η⁻¹(C) ⊂ (τ, σ)`** for a pocket with two reverse-visited barrier arcs and a forbidden set.
Before `τ`: the first boundary visit is on a barrier (the rest of `∂C` is forbidden), and reverse order puts `y₀`
before it. After `σ`: both barriers are visited, so `C ∖ F̄` is cut off from the unbounded current domain (its boundary
in `ℍ` lies on the barriers and on `C̄ ∩ ∂F`, all visited) and is swallowed; a point of `C ∩ ∂F` is on a barrier, so a
later visit to `C` would keep the trace on the barriers for a nontrivial time interval (Aux. 42). -/
theorem mem_Ioo_of_barriers (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hCo : IsOpen C)
    (hCb : IsBounded C) (hCH : C ⊆ H) (hFo : IsOpen F)
    (hrev₁ : R16.IsReverseVisitOrder B₁ fun t => η '' Icc 0 t)
    (hrev₂ : R16.IsReverseVisitOrder B₂ fun t => η '' Icc 0 t)
    (h₁0 : B₁ 0 = x₀) (h₁1 : B₁ 1 = y₀) (h₂0 : B₂ 0 = x₀) (h₂1 : B₂ 1 = y₀)
    (hfr : frontier C ⊆ F ∪ (B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1))
    (hFfr : closure C ∩ frontier F ∩ H ⊆ B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (h42 : ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1)
    (hτf : y₀ ∉ η '' Ico 0 τ) (hσ0 : 0 ≤ σ) (hσ : η σ = x₀) {t : ℝ} (ht : 0 ≤ t) (htC : η t ∈ C) :
    t ∈ Ioo τ σ := by
  -- a visited barrier point
  have hbar : ∀ {z : ℂ} {s : ℝ}, z ∈ B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1 → z ∈ η '' Icc 0 s → y₀ ∈ η '' Icc 0 s := by
    rintro z s (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) h
    exacts [y_mem_of_barrier hrev₁ h₁1 hv h, y_mem_of_barrier hrev₂ h₂1 hv h]
  refine ⟨?_, ?_⟩
  · -- the path `η([0, t])` from `0 ∉ C` to `η(t) ∈ C` meets `∂C` before `t`
    have hpre : IsPreconnected (η '' Icc 0 t) := isPreconnected_Icc.image _ (hη.2.1.mono fun s hs => hs.1)
    obtain ⟨z, hzR, hzf⟩ : (η '' Icc 0 t ∩ frontier C).Nonempty := by
      by_contra hne
      have hsub := subset_of_isPreconnected_of_disjoint_frontier hpre hCo ⟨η t, ⟨t, ⟨ht, le_rfl⟩, rfl⟩, htC⟩
        (Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne))
      have h0 := hCH (hsub ⟨0, ⟨le_rfl, ht⟩, rfl⟩)
      rw [hη.1] at h0
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0)
    obtain ⟨t', ht', rfl⟩ := hzR
    have hzB : η t' ∈ B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1 := by
      rcases hfr hzf with h | h
      · exact absurd h (havoid t' ht'.1)
      · exact h
    have hτ := le_of_fresh hτf (hbar hzB ⟨t', ⟨ht'.1, le_rfl⟩, rfl⟩)
    refine lt_of_le_of_lt hτ (lt_of_le_of_ne ht'.2 fun h => ?_)
    rw [h] at hzf
    have := hzf.2
    rw [hCo.interior_eq] at this
    exact this htC
  · by_contra hσt
    push Not at hσt
    -- every later visit to `C` is a barrier point
    have key : ∀ s, σ ≤ s → η s ∈ C → η s ∈ B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1 := by
      intro s hs hsC
      have hs0 : 0 ≤ s := hσ0.trans hs
      have hx : x₀ ∈ η '' Icc 0 s := ⟨σ, ⟨hσ0, hs⟩, hσ⟩
      have hBvis : B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1 ⊆ η '' Icc 0 s := by
        rintro _ (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
        exacts [mem_of_x_mem_barrier hrev₁ h₁0 hx hv, mem_of_x_mem_barrier hrev₂ h₂0 hx hv]
      set V := C ∩ (closure F)ᶜ with hV
      have hVo : IsOpen V := hCo.inter isClosed_closure.isOpen_compl
      -- the frontier of `C ∖ F̄` in `ℍ` is visited
      have hVfr : ∀ z ∈ frontier V, z ∈ H → z ∈ η '' Icc 0 s := by
        intro z hz hzH
        rcases frontier_inter_subset C (closure F)ᶜ hz with ⟨hzC, hzcl⟩ | ⟨hzcl, hzF⟩
        · rcases hfr hzC with hzF | hzB
          · exfalso
            rw [closure_compl] at hzcl
            exact hzcl (interior_mono subset_closure (hFo.interior_eq.symm ▸ hzF))
          · exact hBvis hzB
        · rw [frontier_compl] at hzF
          exact hBvis (hFfr ⟨⟨hzcl, frontier_closure_subset hzF⟩, hzH⟩)
      have hD := QuantumZipper.RS.isPreconnected_compl_fwdHull hW hW0 hs0
      have hDfr : Disjoint (H \ fwdHull W s) (frontier V) := Set.disjoint_left.2 fun z hzD hzf =>
        notMem_domain_of_mem_trace hη hs0 (hVfr z hzf hzD.1) hzD
      have hVD : V ∩ (H \ fwdHull W s) = ∅ := by
        by_contra hne
        have hsub := subset_of_isPreconnected_of_disjoint_frontier hD hVo
          (by rw [inter_comm]; exact Set.nonempty_iff_ne_empty.2 hne) hDfr
        exact not_isBounded_domain hη hs0 (hCb.subset (hsub.trans inter_subset_left))
      have hsV : η s ∉ V := fun hsV => by
        have hcl := hVo.inter_closure ⟨hsV, trace_mem_closure_domain hη hW hW0 hs0⟩
        rw [hVD, closure_empty] at hcl
        exact hcl
      have hscl : η s ∈ closure F := by
        by_contra h
        exact hsV ⟨hsC, h⟩
      refine hFfr ⟨⟨subset_closure hsC, ?_⟩, hCH hsC⟩
      exact ⟨hscl, by rw [hFo.interior_eq]; exact havoid s hs0⟩
    -- a later visit stays in `C`, hence on the barriers, for a nontrivial time
    have hcont : ContinuousWithinAt η (Ici 0) t := hη.2.1 t ht
    obtain ⟨δ, hδ, hδC⟩ := Metric.mem_nhdsWithin_iff.1 (hcont.preimage_mem_nhdsWithin (hCo.mem_nhds htC))
    refine h42 t (t + δ / 2) ht (by linarith) ?_
    rintro _ ⟨s, hs, rfl⟩
    have hsC : η s ∈ C := hδC ⟨by
      rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
      linarith [hs.2], ht.trans hs.1⟩
    exact key s (hσt.trans hs.1) hsC

/-- **No terminal gap** (Consequence R.4: "There is no positive terminal no-`C` interval before `σ`"), from Aux. 37's
attachment constancy along one barrier `B` (injective and continuous on `[0, 1]`, reverse visited, from `x₀` to `y₀`):
on a terminal gap `[a, σ)` the attachment `u(a) > 0` would stay put, so `B(u(a)/2)` would be first visited exactly at
`σ`, where the tip is `x₀ = B 0` (the landed argument of `Sec6.IsReversePocket.clock_lt_clock_σ`). -/
theorem noFinal_of_attach (hηc : ContinuousOn η (Ici 0)) (hCo : IsOpen C) {B : ℝ → ℂ}
    (hBc : ContinuousOn B (Icc 0 1)) (hBi : InjOn B (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t) (hB0 : B 0 = x₀) (hB1 : B 1 = y₀)
    (hAC : ∀ a b : ℝ, τ ≤ a → a ≤ b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
      firstVisit (fun t => η '' Icc 0 t) B b = firstVisit (fun t => η '' Icc 0 t) B a)
    (hτ0 : 0 ≤ τ) (hτ : η τ = y₀) (hσ0 : 0 ≤ σ) (hσ : η σ = x₀) (hσf : x₀ ∉ η '' Ico 0 σ) :
    ∀ a ∈ Ico τ σ, ∃ t ∈ Ioo a σ, η t ∈ C := by
  intro a ha
  by_contra hno
  push Not at hno
  have ha0 : 0 ≤ a := hτ0.trans ha.1
  -- the trace avoids `C` on `[a, σ)`
  have hgap : ∀ t ∈ Ico a σ, η t ∉ C := by
    intro t ht htC
    rcases eq_or_lt_of_le ht.1 with hta | hta
    · obtain ⟨δ, hδ, hδC⟩ := Metric.mem_nhdsWithin_iff.1
        ((hηc t (ha0.trans ht.1)).preimage_mem_nhdsWithin (hCo.mem_nhds htC))
      set t' := min (t + δ / 2) ((t + σ) / 2) with ht'
      have h1 : t < t' := lt_min (by linarith) (by linarith [ht.2])
      have h2 : t' < σ := (min_le_right _ _).trans_lt (by linarith [ht.2])
      refine hno t' ⟨hta ▸ h1, h2⟩ (hδC ⟨?_, (ha0.trans ht.1).trans h1.le⟩)
      rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      exact (sub_le_sub_right (min_le_left _ _) t).trans_lt (by linarith)
    · exact hno t ⟨hta, ht.2⟩ htC
  have hcl : ∀ s, IsClosed (η '' Icc 0 s) := fun s =>
    (isCompact_Icc.image_of_continuousOn (hηc.mono fun _ hr => hr.1)).isClosed
  set u := firstVisit (fun t => η '' Icc 0 t) B a with hudef
  have hne : ∃ v ∈ Icc (0 : ℝ) 1, B v ∈ η '' Icc 0 a :=
    ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [hB1]; exact ⟨τ, ⟨hτ0, ha.1⟩, hτ⟩⟩
  have hmem := firstVisit_mem (R := fun t => η '' Icc 0 t) hBc (hcl a) hne
  have hu : 0 < u := lt_of_le_of_ne hmem.1.1 fun h => by
    have e : B u = x₀ := by rw [← h, hB0]
    have hx : x₀ ∈ η '' Icc 0 a := e ▸ hmem.2
    exact absurd (le_of_fresh hσf hx) (not_le.2 ha.2)
  have hv : u / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hmem.1.2]⟩
  -- `B(u/2)` is not visited before `σ`
  have hnot : ∀ b ∈ Ico 0 σ, B (u / 2) ∉ η '' Icc 0 b := by
    intro b hb hvis
    rcases le_or_gt b a with hba | hab
    · have := firstVisit_le (R := fun t => η '' Icc 0 t) (α := B) (t := a) hv (monotone_image_Icc hba hvis)
      rw [← hudef] at this
      linarith
    · have hc := hAC a b ha.1 hab.le hb.2 fun t ht => hgap t ⟨ht.1, ht.2.trans_lt hb.2⟩
      have := firstVisit_le (R := fun t => η '' Icc 0 t) (α := B) (t := b) hv hvis
      rw [hc, ← hudef] at this
      linarith
  have hx : x₀ ∈ η '' Icc 0 σ := ⟨σ, ⟨hσ0, le_rfl⟩, hσ⟩
  obtain ⟨t, ht, hte⟩ := mem_of_x_mem_barrier hrev hB0 hx hv
  rcases lt_or_eq_of_le ht.2 with htσ | htσ
  · exact hnot t ⟨ht.1, htσ⟩ ⟨t, ⟨ht.1, le_rfl⟩, hte⟩
  · rw [htσ, hσ, ← hB0] at hte
    have := hBi ⟨le_rfl, zero_le_one⟩ hv hte
    linarith

/-- **The erasure facts of a mixed or outer pocket** (`IsErasurePocket`) from Consequence R.4's ingredients
(`mem_Ioo_of_barriers`), Aux. 37's attachment constancy along the first barrier (`noFinal_of_attach`), the first visits
`τ = T(y₀)`, `σ = T(x₀)`, and the equal gap endpoints of §5.4 ("Closed gaps have identical endpoints"). -/
theorem isErasurePocket_of_barriers (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hCo : IsOpen C)
    (hCb : IsBounded C) (hCH : C ⊆ H) (hFo : IsOpen F)
    (hB₁c : ContinuousOn B₁ (Icc 0 1)) (hB₁i : InjOn B₁ (Icc 0 1))
    (hrev₁ : R16.IsReverseVisitOrder B₁ fun t => η '' Icc 0 t)
    (hrev₂ : R16.IsReverseVisitOrder B₂ fun t => η '' Icc 0 t)
    (h₁0 : B₁ 0 = x₀) (h₁1 : B₁ 1 = y₀) (h₂0 : B₂ 0 = x₀) (h₂1 : B₂ 1 = y₀)
    (hfr : frontier C ⊆ F ∪ (B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1))
    (hFfr : closure C ∩ frontier F ∩ H ⊆ B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (h42 : ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ B₁ '' Icc 0 1 ∪ B₂ '' Icc 0 1)
    (hτ0 : 0 ≤ τ) (hτ : η τ = y₀) (hτf : y₀ ∉ η '' Ico 0 τ) (hσ0 : 0 ≤ σ) (hσ : η σ = x₀)
    (hσf : x₀ ∉ η '' Ico 0 σ) (hxy : x₀ ≠ y₀)
    (hAC : ∀ a b : ℝ, τ ≤ a → a ≤ b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
      firstVisit (fun t => η '' Icc 0 t) B₁ b = firstVisit (fun t => η '' Icc 0 t) B₁ a)
    (hgap : ∀ a b : ℝ, τ ≤ a → a < b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
      b ∈ closure {t | a < t ∧ η t ∈ C} → (a = τ ∨ a ∈ closure {t | τ < t ∧ η t ∈ C}) → η a = η b) :
    IsErasurePocket η C x₀ y₀ τ σ := by
  have hτσ : τ < σ := by
    have hx : x₀ ∈ η '' Icc 0 σ := ⟨σ, ⟨hσ0, le_rfl⟩, hσ⟩
    refine lt_of_le_of_ne (le_of_fresh hτf (y_mem_of_barrier hrev₁ h₁1 ⟨zero_le_one, le_rfl⟩
      (mem_of_x_mem_barrier hrev₁ h₁0 hx ⟨zero_le_one, le_rfl⟩))) fun h => hxy ?_
    rw [← hσ, ← h, hτ]
  exact ⟨hη.2.1, hCo, hτ0, hτσ, fun t ht htC => mem_Ioo_of_barriers hη hW hW0 hCo hCb hCH hFo hrev₁ hrev₂ h₁0 h₁1
    h₂0 h₂1 hfr hFfr havoid h42 hτf hσ0 hσ ht htC, hτ, hσ, hσf,
    noFinal_of_attach hη.2.1 hCo hB₁c hB₁i hrev₁ h₁0 h₁1 hAC hτ0 hτ hσ0 hσ hσf, hgap⟩

end Barriers

end InteractingSLE.Sec7.R7StopIn
