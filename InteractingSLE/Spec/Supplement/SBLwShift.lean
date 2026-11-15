/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLwLink
import InteractingSLE.Spec.Supplement.GW1PieceChart
import InteractingSLE.Spec.Supplement.W5CommonSeedShift

/-!
# S5's relative step in the walk's coordinates

Packet PROVE-T14-SBLEAVES2, items (2)(b)–(d) of `planning/handoffs/PROVE-T14-SBLEAVES.md` §7.4, the coordinate part.
SB2(1) in launch form is stated in the walk's launch chart `c` (the walk's tip at `0`, the prime end over
`L = min(A ∩ ℝ)` at `m ≤ 0`), with the actual upper flow `η` from `u ≤ 0`; Lemma S5 is stated with the retained set and
the upper curve from `0` and the left entry prime end at `0`. `shiftChart c u m` is the walk chart read in S5's
coordinates (`z ↦ c(z + u) − m`), and

* `isRemainderLink_shift`, `hasOrderedProperCompletions_sub_real`: SB2(1)'s link and SB1's ordering move to S5's
  coordinates;
* `exists_bdryMap_of_hasProperBdryExt`: the boundary map `g` of a run chart (`GW1P.isClosed_pieces_run`), continuous on
  `ℍ̄`, equal to `c⁻¹` on `ℍ`, proper; `bdryMap_shift`: the same for the shifted chart;
* `erasureStep_of_link_shift`: Lemma S5's relative step for the physical prefix `A` from `u`, the physical upper flow
  and the relative curves of the walk chart, translated by `−u` (`Erase.isOneSided_add_real_iff` translates S1 back).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lw

open Lv

/-- The chart `c` read in S5's coordinates: the physical plane translated by `−u`, the chart's coordinate by `−m`. -/
def shiftChart (c : Chart) (u m : ℝ) : Chart :=
  (fun z => c.1 (z + u) - m, fun w => c.2.1 (w + m) - u, fun z => c.2.2 (z + u))

@[simp] theorem shiftChart_inv (c : Chart) (u m : ℝ) (w : ℂ) : (shiftChart c u m).2.1 w = c.2.1 (w + m) - u := rfl

@[simp] theorem shiftChart_fwd (c : Chart) (u m : ℝ) (z : ℂ) : (shiftChart c u m).1 z = c.1 (z + u) - m := rfl

theorem add_real_mem_H_iff {w : ℂ} (x : ℝ) : w + x ∈ H ↔ w ∈ H := by
  show 0 < (w + x).im ↔ 0 < w.im
  simp

/-- The first visit of a translated curve to a translated point. -/
theorem firstVisit_sub_real (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (L u : ℝ) :
    firstVisit (fun t => η t - u) ζ ((L - u : ℝ) : ℂ) = firstVisit η ζ L := by
  have key : ∀ t, (η t - u = ((L - u : ℝ) : ℂ)) ↔ η t = L := fun t => by
    push_cast; constructor <;> intro h <;> linear_combination h
  unfold firstVisit
  simp_rw [key]

/-- **SB2(1)'s link in S5's coordinates.** -/
theorem isRemainderLink_shift {c : Chart} {η ηr : ℝ≥0 → ℂ} {ζ ζr : ℝ≥0∞} {L : ℝ} (u m : ℝ)
    (h : IsRemainderLink c η ζ L ηr ζr) :
    IsRemainderLink (shiftChart c u m) (fun t => η t - u) ζ (L - u) (fun s => ηr s - m) ζr := by
  intro hv
  rw [firstVisit_sub_real] at hv ⊢
  obtain ⟨σ, hσ0, hσm, hσc, hσ⟩ := h hv
  refine ⟨σ, hσ0, hσm, hσc, fun s => ⟨(hσ s).1, fun hs hsH => ?_⟩⟩
  have hsH' : ηr s ∈ H := by
    have := (add_real_mem_H_iff (w := ηr s - m) m).2 hsH
    simpa using this
  rw [shiftChart_inv, sub_add_cancel, (hσ s).2 hs hsH']

/-- **SB1's ordering in S5's coordinates** (both relative curves translated by the same real `−m`). -/
theorem hasOrderedProperCompletions_sub_real {α β : ℝ≥0 → ℂ} {a c : ℝ≥0} (m : ℝ)
    (h : HasOrderedProperCompletions α a β c) :
    HasOrderedProperCompletions (fun t => α t - m) a (fun t => β t - m) c := by
  refine Supp9.HasOrderedProperCompletions.of_sub_real (-m) ?_
  have e : ∀ γ : ℝ≥0 → ℂ, (fun t => (fun t => γ t - (m : ℂ)) t - ((-m : ℝ) : ℂ)) = γ := fun γ => by
    funext t; push_cast; ring
  rw [e α, e β]
  exact h

/-- **The boundary map of a run chart.** A conformal chart with a proper boundary extension (`GW1P.HasProperBdryExt`,
every run chart by `GW1P.isClosed_pieces_run`) has a boundary map `g`: continuous on `ℍ̄`, equal to `c⁻¹` on `ℍ`, the
limit of `c⁻¹` at every point of `ℍ̄`, and proper (`‖w‖ ≤ ‖g w‖ + C`). -/
theorem exists_bdryMap_of_hasProperBdryExt {c : Chart} (hcc : c.IsConformal) (hc : GW1P.HasProperBdryExt c) :
    ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g c.2.1 H ∧
      (∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) ∧
      ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (g p)) := by
  obtain ⟨f, C, hf, hC⟩ := hc
  refine ⟨f, GW1P.continuousOn_of_tendsto hf, fun w hw => ?_, ⟨1, C, zero_le_one, fun w hw => ?_⟩, hf⟩
  · have hwH : w ∈ Hbar := le_of_lt (show (0 : ℝ) < w.im from hw)
    have hcont : ContinuousAt c.2.1 w :=
      (hcc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hw)).continuousAt
    have h1 : Tendsto c.2.1 (𝓝[H] w) (𝓝 (c.2.1 w)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have := GW1P.neBot_nhdsWithin_H hwH
    exact tendsto_nhds_unique (hf w hwH) h1
  · have h1 := hC w hw
    have h2 : ‖w‖ ≤ ‖f w‖ + ‖f w - w‖ := by
      calc ‖w‖ = ‖f w - (f w - w)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖f w‖ + ‖f w - w‖ := norm_sub_le _ _
    linarith

/-- The boundary map of the shifted chart. -/
theorem bdryMap_shift {c : Chart} {g : ℂ → ℂ} (u m : ℝ) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) :
    ContinuousOn (fun w => g (w + m) - u) {z | 0 ≤ z.im} ∧
      EqOn (fun w => g (w + m) - u) (shiftChart c u m).2.1 H := by
  refine ⟨?_, fun w hw => ?_⟩
  · refine (hgc.comp (continuous_id.add continuous_const).continuousOn fun w hw => ?_).sub continuousOn_const
    show 0 ≤ (w + m).im
    simpa using hw
  · simp only [shiftChart_inv]
    rw [hgi ((add_real_mem_H_iff m).2 hw)]

/-- `min(A ∩ ℝ)` of a translated set. -/
theorem realMin_image_sub {A : Set ℂ} (u : ℝ) (hne : ∃ x : ℝ, (x : ℂ) ∈ A)
    (hbdd : BddBelow {x : ℝ | (x : ℂ) ∈ A}) : realMin ((fun z => z - (u : ℂ)) '' A) = realMin A - u := by
  unfold realMin
  have hset : {x : ℝ | (x : ℂ) ∈ (fun z => z - (u : ℂ)) '' A} = (fun x => x - u) '' {x : ℝ | (x : ℂ) ∈ A} := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      refine ⟨x + u, ?_, by ring⟩
      have hz' : z = ((x + u : ℝ) : ℂ) := by push_cast; linear_combination hzx
      exact show ((x + u : ℝ) : ℂ) ∈ A from hz' ▸ hz
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by push_cast; ring⟩
  rw [hset]
  obtain ⟨x, hx⟩ := hne
  exact (Monotone.map_csInf_of_continuousAt (f := fun x : ℝ => x - u) (continuous_sub_right u).continuousAt
    (fun a b h => sub_le_sub_right h u) ⟨x, hx⟩ hbdd).symm

/-- **Lemma S5's relative step in the walk's coordinates.** The physical retained set `A = p([0, 1])` from the upper
seed `u` (`p 0 = u`, finite fibres), the actual upper flow `η` from `u`, the walk's launch chart `c` with boundary map
`g`, the relative upper curve `ηr` from `m ≤ 0` and the relative lower piece `αR` from the walk's tip `0`, ordered at
all stops and linked to `η` after its first visit to `L = min(A ∩ ℝ)`. If the walk chart read in S5's coordinates
(`shiftChart c u m`) is a left entry chart of `A − u` at `L − u`, the translated history is an erasure step adding the
physical piece `g(αR([0, d]))`. -/
theorem erasureStep_of_link_shift {p : ℝ → ℂ} {u m : ℝ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {c : Chart}
    {g : ℂ → ℂ} {ηr αR : ℝ≥0 → ℂ} {ζr ζα : ℝ≥0∞} {d : ℝ≥0}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = u) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hη0 : η 0 = u) (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (ha : (a : ℝ≥0∞) ≤ ζ)
    (hc : IsLeftEntryChart ((fun z => z - (u : ℂ)) '' (p '' Icc 0 1)) (realMin (p '' Icc 0 1) - u)
      (shiftChart c u m))
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hηr : ContinuousOn ηr {t | (t : ℝ≥0∞) ≤ ζr}) (hηr0 : ηr 0 = m)
    (hηrH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζr → 0 ≤ (ηr s).im)
    (hdense : ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) ≤ ζr → ∃ s ∈ Ioo a b, ηr s ∈ H)
    (htr : ζr = ⊤ → Tendsto (fun s => ‖ηr s‖) atTop atTop)
    (hlink : IsRemainderLink c η ζ (realMin (p '' Icc 0 1)) ηr ζr)
    (hv : firstVisit η ζ (realMin (p '' Icc 0 1)) < ζ)
    (hta : (firstVisit η ζ (realMin (p '' Icc 0 1))).toNNReal ≤ a)
    (hm : m ≤ 0) (hα0 : αR 0 = 0) (hdα : (d : ℝ≥0∞) ≤ ζα)
    (hord : ∀ d' a' : ℝ≥0, (d' : ℝ≥0∞) ≤ ζα → (a' : ℝ≥0∞) ≤ ζr → HasOrderedProperCompletions αR d' ηr a') :
    Erase.ErasureStep (fun t => η t - u) a ((fun z => z - (u : ℂ)) '' (p '' Icc 0 1))
      ((fun z => z - (u : ℂ)) '' (p '' Icc 0 1 ∪ g '' (αR '' Icc 0 d))) := by
  set p' : ℝ → ℂ := fun s => p s - u with hp'
  have himg : p' '' Icc 0 1 = (fun z => z - (u : ℂ)) '' (p '' Icc 0 1) := by rw [image_image]
  have hAb : Bornology.IsBounded (p '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hp).isBounded
  have hreal : realMin (p' '' Icc 0 1) = realMin (p '' Icc 0 1) - u := by
    rw [himg]
    refine realMin_image_sub u ⟨u, 0, ⟨le_rfl, zero_le_one⟩, hp0⟩ ?_
    obtain ⟨R, hR⟩ := hAb.exists_norm_le
    refine ⟨-R, fun x hx => ?_⟩
    have h1 := hR _ hx
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [neg_abs_le x]
  have hc' : IsLeftEntryChart (p' '' Icc 0 1) (realMin (p' '' Icc 0 1)) (shiftChart c u m) := by
    rw [hreal, himg]; exact hc
  obtain ⟨hg'c, hg'i⟩ := bdryMap_shift u m hgc hgi
  have hlink' : IsRemainderLink (shiftChart c u m) (fun t => η t - u) ζ (realMin (p' '' Icc 0 1))
      (fun s => ηr s - m) ζr := by
    rw [hreal]; exact isRemainderLink_shift u m hlink
  have hfv : firstVisit (fun t => η t - u) ζ (realMin (p' '' Icc 0 1) : ℂ) =
      firstVisit η ζ (realMin (p '' Icc 0 1)) := by
    rw [hreal, firstVisit_sub_real]
  have hstep := erasureStep_of_link (p := p') (η := fun t => η t - u) (ηr := fun s => ηr s - m)
    (αR := fun t => αR t - m) (w := -m) (d := d) (ζα := ζα)
    (hp.sub continuousOn_const) (by simp [hp', hp0])
    (fun z => by
      have : p' ⁻¹' {z} = p ⁻¹' {z + u} := by
        ext s; simp only [mem_preimage, mem_singleton_iff, hp']; constructor <;> intro h <;>
          linear_combination h
      rw [this]; exact hpf _)
    (fun s hs => by simpa [hp'] using hpH s hs) (by simp [hη0]) (hη.sub continuousOn_const) ha hc' hg'c hg'i
    (hηr.sub continuousOn_const) (by simp [hηr0]) (fun s hs => by simpa using hηrH s hs)
    (fun a b hab hb => by
      obtain ⟨s, hs, hsH⟩ := hdense a b hab hb
      exact ⟨s, hs, by simpa [sub_eq_add_neg] using (add_real_mem_H_iff (-m)).2 hsH⟩)
    (fun hζ => by
      refine tendsto_atTop_mono (fun s => ?_) (tendsto_atTop_add_const_right _ (-‖(m : ℂ)‖) (htr hζ))
      have := norm_sub_norm_le (ηr s) (m : ℂ)
      show ‖ηr s‖ + -‖(m : ℂ)‖ ≤ ‖ηr s - m‖
      linarith)
    hlink' (by rw [hfv]; exact hv) (by rw [hfv]; exact hta) (by linarith) (by simp [hα0]) hdα
    (fun d' a' hd' ha' => hasOrderedProperCompletions_sub_real m (hord d' a' hd' ha'))
  have hfin : (fun w => g (w + m) - u) '' ((fun t => αR t - m) '' Icc 0 d) =
      (fun z => z - (u : ℂ)) '' (g '' (αR '' Icc 0 d)) := by
    simp only [image_image, sub_add_cancel]
  rw [image_union, ← himg, ← hfin]
  exact hstep

end InteractingSLE.Theorem14.SB.Lw
