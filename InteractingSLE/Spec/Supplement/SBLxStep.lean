/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxEntry
import InteractingSLE.Spec.Supplement.SBLemmaS34Proof
import InteractingSLE.Spec.Supplement.BW1DetPhys

/-!
# SB3's stage step at one sample: S1 for the retained prefix plus the next lower piece

Packet PROVE-T14-SBLEAVES3. The deterministic half of Lemma SB3's induction step (specification p. 633,
`source/spec/p625-671.md` L159–L163): "If that upper prefix is wholly in `K_A` [...] the final clause of S5 gives the
assertion after the next lower piece. Otherwise SB2(1) gives its actual remaining upper flow from `e_L = g_A(L⁻)` in
`D_A` [...] S5 pulls this comparison back."

* `isOneSided_union_of_link`: from S1 for the retained prefix `A = p([0, 1])` (through every available upper stop) and
  the data of one stage — the walk's launch chart `c` read as a left entry chart in S5's coordinates, its boundary map
  `g`, SB2(1)'s relative curve `ηr` linked to the actual upper flow, the relative lower piece `αR` from the tip `0` and
  the ordering of the two — S1 holds for `A ∪ g(αR([0, d]))`. Both of S5's cases: the upper prefix does not reach
  `L = min(A ∩ ℝ)` (S5's inside clause, `ErasureStep.inside`, with the hull clause from S1 and S2), or it does (S5's
  relative step, `Lw.erasureStep_of_link_shift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lx

open Lv Lw

/-- `min(A ∩ ℝ)` of a compact path image from the real point `u`, translated by `−u`. -/
theorem realMin_path_sub {p : ℝ → ℂ} {u : ℝ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = u) :
    realMin ((fun z => z - (u : ℂ)) '' (p '' Icc 0 1)) = realMin (p '' Icc 0 1) - u := by
  have hAb : Bornology.IsBounded (p '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hp).isBounded
  refine realMin_image_sub u ⟨u, 0, ⟨le_rfl, zero_le_one⟩, hp0⟩ ?_
  obtain ⟨R, hR⟩ := hAb.exists_norm_le
  refine ⟨-R, fun x hx => ?_⟩
  have h1 := hR _ hx
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  linarith [neg_abs_le x]

/-- S1 in S5's coordinates (translate the set and the curve by `−u`). -/
theorem isOneSided_sub_real_iff {A : Set ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0} (u : ℝ) :
    IsOneSided ((fun z => z - (u : ℂ)) '' A) (fun t => β t - u) a ↔ IsOneSided A β a := by
  have h1 : (fun z : ℂ => z - (u : ℂ)) = (· + ((-u : ℝ) : ℂ)) := by funext z; push_cast; ring
  have h2 : (fun t => β t - (u : ℂ)) = (fun t => β t + ((-u : ℝ) : ℂ)) := by funext t; push_cast; ring
  rw [h1, h2]
  exact Erase.isOneSided_add_real_iff (-u)

/-- The boundary map of a chart sends `ℍ̄` into the closure of the chart's domain (here in S5's coordinates). -/
theorem sub_mem_closure_of_bdryMap {D : Set ℂ} {c : Chart} {u m : ℝ} (hc : IsDomainChart D (shiftChart c u m))
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {v : ℂ} (hv : 0 ≤ v.im) :
    g v - u ∈ closure D := by
  have := GW1P.neBot_nhdsWithin_H (show v ∈ Hbar from hv)
  have hlim : Tendsto (fun w => g w - u) (𝓝[H] v) (𝓝 (g v - u)) :=
    ((hgc v hv).tendsto.mono_left (nhdsWithin_mono _ fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz))).sub_const _
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [← hc.2.1]
  refine ⟨w - m, ?_, ?_⟩
  · have := (add_real_mem_H_iff (-m)).2 hw
    rwa [show w + ((-m : ℝ) : ℂ) = w - m by push_cast; ring] at this
  · show c.2.1 (w - m + m) - u = g w - u
    rw [sub_add_cancel, hgi hw]

/-- **SB3's stage step at one sample** (S5's two cases). Let `A = p([0, 1])` be the retained prefix, a continuous path
with finite fibres in `ℍ̄` from the upper seed `u`, and `η` the actual upper flow from `u` with S1 for `A` through every
available stop. Let `c` be the walk's launch chart, read in S5's coordinates (`shiftChart c u m`) as a left entry chart
of `A − u` at `L − u` (`L = min(A ∩ ℝ)`), with boundary map `g`; `ηr` SB2(1)'s relative curve from `m ≤ 0`, linked to
`η` after its first visit to `L`; `αR` the relative lower piece from the tip `0`, with positive lifetime `ζα`, ordered
with `ηr` through all available endpoints. Then S1 holds for `A ∪ g(αR([0, d]))` and every available stop `a` of `η`.
If `η` does not reach `L` before `a`, its prefix lies in `K_A` (S2) and S5's inside clause applies; otherwise S5's
relative step does. -/
theorem isOneSided_union_of_link {p : ℝ → ℂ} {u m : ℝ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {c : Chart}
    {g : ℂ → ℂ} {ηr αR : ℝ≥0 → ℂ} {ζr ζα : ℝ≥0∞} {d : ℝ≥0}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = u) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hη0 : η 0 = u) (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (ha : (a : ℝ≥0∞) ≤ ζ) (hS1 : ∀ a' : ℝ≥0, (a' : ℝ≥0∞) ≤ ζ → IsOneSided (p '' Icc 0 1) η a')
    (hc : IsLeftEntryChart ((fun z => z - (u : ℂ)) '' (p '' Icc 0 1)) (realMin (p '' Icc 0 1) - u)
      (shiftChart c u m))
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hηr : ContinuousOn ηr {t | (t : ℝ≥0∞) ≤ ζr}) (hηr0 : ηr 0 = m)
    (hηrH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζr → 0 ≤ (ηr s).im)
    (hdense : ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) ≤ ζr → ∃ s ∈ Ioo a b, ηr s ∈ H)
    (htr : ζr = ⊤ → Tendsto (fun s => ‖ηr s‖) atTop atTop)
    (hlink : IsRemainderLink c η ζ (realMin (p '' Icc 0 1)) ηr ζr)
    (hm : m ≤ 0) (hα0 : αR 0 = 0) (hαH : ∀ t : ℝ≥0, t ≤ d → 0 ≤ (αR t).im) (hdα : (d : ℝ≥0∞) ≤ ζα)
    (hζα : 0 < ζα)
    (hord : 0 < ζα → 0 < ζr → ∀ d' a' : ℝ≥0, (d' : ℝ≥0∞) ≤ ζα → (a' : ℝ≥0∞) ≤ ζr →
      HasOrderedProperCompletions αR d' ηr a') :
    IsOneSided (p '' Icc 0 1 ∪ g '' (αR '' Icc 0 d)) η a := by
  rw [← isOneSided_sub_real_iff u]
  have hS1a : IsOneSided ((fun z => z - (u : ℂ)) '' (p '' Icc 0 1)) (fun t => η t - u) a :=
    (isOneSided_sub_real_iff u).2 (hS1 a ha)
  by_cases hv : firstVisit η ζ (realMin (p '' Icc 0 1)) < (a : ℝ≥0∞)
  · -- S5's relative step
    have hvζ : firstVisit η ζ (realMin (p '' Icc 0 1)) < ζ := hv.trans_le ha
    have hta : (firstVisit η ζ (realMin (p '' Icc 0 1))).toNNReal ≤ a := by
      have := ENNReal.toNNReal_mono ENNReal.coe_ne_top hv.le
      simpa using this
    have hζr := zeta_pos_of_link hlink hvζ
    exact (erasureStep_of_link_shift hp hp0 hpf hpH hη0 hη ha hc hgc hgi hηr hηr0 hηrH hdense htr hlink hvζ hta hm
      hα0 hdα (hord hζα hζr)).isOneSided hS1a
  · -- S5's inside clause
    push Not at hv
    set p' : ℝ → ℂ := fun s => p s - u with hp'
    have himg : p' '' Icc 0 1 = (fun z => z - (u : ℂ)) '' (p '' Icc 0 1) := by rw [image_image]
    have hreal : realMin (p' '' Icc 0 1) = realMin (p '' Icc 0 1) - u := by
      rw [himg]; exact realMin_path_sub hp hp0
    have hp'c : ContinuousOn p' (Icc 0 1) := hp.sub continuousOn_const
    have hp'0 : p' 0 = 0 := by simp [hp', hp0]
    have hp'H : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p' s).im := fun s hs => by simpa [hp'] using hpH s hs
    have hβ0 : (fun t => η t - (u : ℂ)) 0 = 0 := by simp [hη0]
    have hfv : firstVisit (fun t => η t - (u : ℂ)) ζ (realMin (p' '' Icc 0 1)) =
        firstVisit η ζ (realMin (p '' Icc 0 1)) := by
      rw [hreal]; exact firstVisit_sub_real η ζ _ u
    have hS1' : ∀ a' : ℝ≥0, (a' : ℝ≥0∞) ≤ ζ → IsOneSided (p' '' Icc 0 1) (fun t => η t - (u : ℂ)) a' :=
      fun a' ha' => by rw [himg]; exact (isOneSided_sub_real_iff u).2 (hS1 a' ha')
    have hin0 := image_subset_hullK_of_isOneSided (T := (a : ℝ≥0∞)) hp'c hp'0 hp'H hβ0 hS1'
    have hin : (fun t => η t - (u : ℂ)) '' Icc 0 a ⊆ hullK (p' '' Icc 0 1) := by
      refine (image_mono fun s hs => ?_).trans hin0
      have hsa : (s : ℝ≥0∞) ≤ a := ENNReal.coe_le_coe.2 hs.2
      show (s : ℝ≥0∞) ≤ min (min (a : ℝ≥0∞) ζ) _
      rw [hfv]
      exact le_min (le_min hsa (hsa.trans ha)) (hsa.trans hv)
    have hvisit : ∀ s : ℝ≥0, s < a → (fun t => η t - (u : ℂ)) s ≠ realMin (p' '' Icc 0 1) := by
      intro s hs heq
      rw [hreal] at heq
      have hηs : η s = realMin (p '' Icc 0 1) := by
        push_cast at heq; linear_combination heq
      have hle : firstVisit η ζ (realMin (p '' Icc 0 1)) ≤ s :=
        iInf₂_le s ⟨(ENNReal.coe_le_coe.2 hs.le).trans ha, hηs⟩
      exact absurd (hv.trans hle) (not_le.2 (ENNReal.coe_lt_coe.2 hs))
    have hB : (fun z => z - (u : ℂ)) '' (g '' (αR '' Icc 0 d)) ⊆ closure (H \ fillH (p' '' Icc 0 1)) := by
      rintro _ ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
      rw [himg]
      exact sub_mem_closure_of_bdryMap hc.1 hgc hgi (hαH t ht.2)
    have hstep := Erase.ErasureStep.inside (β := fun t => η t - (u : ℂ)) (a := a) hp'c hp'0 hp'H hβ0 hin hvisit hB
    have hres := hstep.isOneSided (by rw [himg]; exact hS1a)
    rw [himg] at hres
    rwa [image_union]

/-- `min(A ∩ ℝ)` is below every real point of a compact path image. -/
theorem realMin_le_of_mem_path {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) {y : ℝ}
    (hy : (y : ℂ) ∈ p '' Icc 0 1) : realMin (p '' Icc 0 1) ≤ y := by
  have hAb : Bornology.IsBounded (p '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hp).isBounded
  obtain ⟨R, hR⟩ := hAb.exists_norm_le
  refine csInf_le ⟨-R, fun x hx => ?_⟩ hy
  have h1 := hR _ hx
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  linarith [neg_abs_le x]

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

open WalkIntCanon Exist.Staged Exist.StagedLaw in
/-- **SB3's stage step for a walk run** (`isOneSided_union_of_link` with the left entry chart supplied by
`isLeftEntryChart_shift_of_runChart_entry`). The retained set `A = p([0, 1])` has the fill of the run's prefix through
`n` instructions (e.g. the lower prefix with its bridge, `Lw.fillH_union_real`); the run is regular and not finished;
`m` is the entry value of the run's chart at `L = min(A ∩ ℝ)` (SB2(1)'s entry); `g` is the boundary map of the chart. -/
theorem isOneSided_union_of_runChart (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone)
    {p : ℝ → ℂ} {u m : ℝ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0}
    {g : ℂ → ℂ} {ηr αR : ℝ≥0 → ℂ} {ζr ζα : ℝ≥0∞} {d : ℝ≥0}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = u) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hpA : fillH (p '' Icc 0 1) = fillH (SB.prefixPhysSet κ b jumps spec D n))
    (hent : IsLeftEntryValue (stChart (ExplState.run κ b jumps spec D n)) (realMin (p '' Icc 0 1)) m)
    (hη0 : η 0 = u) (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (ha : (a : ℝ≥0∞) ≤ ζ) (hS1 : ∀ a' : ℝ≥0, (a' : ℝ≥0∞) ≤ ζ → IsOneSided (p '' Icc 0 1) η a')
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart (ExplState.run κ b jumps spec D n)).2.1 H)
    (hηr : ContinuousOn ηr {t | (t : ℝ≥0∞) ≤ ζr}) (hηr0 : ηr 0 = m)
    (hηrH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζr → 0 ≤ (ηr s).im)
    (hdense : ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) ≤ ζr → ∃ s ∈ Ioo a b, ηr s ∈ H)
    (htr : ζr = ⊤ → Tendsto (fun s => ‖ηr s‖) atTop atTop)
    (hlink : IsRemainderLink (stChart (ExplState.run κ b jumps spec D n)) η ζ (realMin (p '' Icc 0 1)) ηr ζr)
    (hm : m ≤ 0) (hα0 : αR 0 = 0) (hαH : ∀ t : ℝ≥0, t ≤ d → 0 ≤ (αR t).im) (hdα : (d : ℝ≥0∞) ≤ ζα)
    (hζα : 0 < ζα)
    (hord : 0 < ζα → 0 < ζr → ∀ d' a' : ℝ≥0, (d' : ℝ≥0∞) ≤ ζα → (a' : ℝ≥0∞) ≤ ζr →
      HasOrderedProperCompletions αR d' ηr a') :
    IsOneSided (p '' Icc 0 1 ∪ g '' (αR '' Icc 0 d)) η a :=
  isOneSided_union_of_link hp hp0 hpf hpH hη0 hη ha hS1
    (isLeftEntryChart_shift_of_runChart_entry spec D hreg n hnot (isCompact_Icc.image_of_continuousOn hp) hpA
      (fun _ hy => realMin_le_of_mem_path hp hy) hent u)
    hgc hgi hηr hηr0 hηrH hdense htr hlink hm hα0 hαH hdα hζα hord

end Run

/-- Boundary limits of a chart's inverse from a boundary map `g` (continuous on `ℍ̄`, equal to `c⁻¹` on `ℍ`). -/
theorem tendsto_inv_of_bdryMap {c : Chart} {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {v : ℂ} (hv : 0 ≤ v.im) : Tendsto c.2.1 (𝓝[H] v) (𝓝 (g v)) := by
  have h1 : Tendsto g (𝓝[H] v) (𝓝 (g v)) :=
    (hgc v hv).tendsto.mono_left (nhdsWithin_mono _ fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz))
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact hgi hw

section Phys

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

open Exist.Staged Exist.StagedLaw in
/-- **The physical identity at a walk launch** (`Lw` handoff §4.2): the prefix after the launch is the old prefix and
the image under the launch chart's boundary map `g` of the piece's trace `α` through its available lifetime. -/
theorem prefixPhysSet_succ_eq_image (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)).2.1 H)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (D k).1 (D k).2 α)
    (hW : ContinuousOn (D k).1 {t | (t : ℝ≥0∞) ≤ (D k).2}) (hW0 : (D k).1 0 = 0)
    (hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D k).2 → 0 ≤ (α t).im) :
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1) =
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D k ∪
        g '' (α '' {t | (t : ℝ≥0∞) ≤ (D k).2}) := by
  rw [BW1Det.prefixPhysSet_succ_of_launch hl]
  congr 1
  simp only [retOf, min_top_left]
  exact CounterflowRange.tipSet_stopped_eq_of_tendsto hα hW hW0
    (fun t ht => tendsto_inv_of_bdryMap hgc hgi (hαH t ht))

end Phys

end InteractingSLE.Theorem14.SB.Lx
