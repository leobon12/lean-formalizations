/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4AvoidHalfBall
import QuantumZipper.Proofs.RS.HullBasics

/-!
# First visits of a Loewner trace (proof of Proposition 5.13): Lemma 5.7's first visit and the filled-hull facts

Packet PROVE-PROP513. Specification §5.2, proof of Proposition 5.13 (`source/spec/p145-192.md` L94–L140,
pp. 149–151): "For `z ∈ Γ`, let `T_z` be the first counterflow time at which `z` is visited", "Lemma 5.7 puts every
point of `Γ` on the counterflow trace", "`L_z = η'([0, T_z])`", and "A continuous Loewner trace cannot visit the
interior of an earlier filled hull: at every later time its tip lies in the closure of the then unexplored domain,
which is contained in the closure of the earlier unexplored domain".

Throughout, `w : ℝ≥0 → ℝ` is a continuous driver with `w 0 = 0` and `η` a generating trace of it on `[0, ∞)`
(the frozen `IsGeneratingTrace w ⊤ η`; this is the counterflow in its capacity chart, which has infinite lifetime in
the non-boundary regime of §5). The hulls are `K_t = fwdHull W t`, `W = w ∘ toNNReal`.

## Main results

* `traceFirstVisit γ z` (`T_z`): the first time a path visits `z`; `apply_traceFirstVisit` (it is a visit when `z` is
  visited at all), `traceFirstVisit_le`, `apply_ne_of_lt_traceFirstVisit`.
* **`closure_subset_image_traceFirstVisit`** ("Lemma 5.7's first visit in the needed form"): if every point of a
  set `S` is visited strictly before the first visit of `z` (the reverse chronological order of Lemma 5.7 for the
  descendants of the prefix ending at `z`), then `closure S ⊆ γ([0, T_z])`; this is the inclusion
  `L_z ⊆ η'([0, T_z])` of the light-cone identity.
* `image_Icc_inter_H_subset_fwdHull`: `η([0, t]) ∩ ℍ ⊆ K_t`.
* **`notMem_interior_fwdHull_of_lt`**: a generating trace never visits the interior of an earlier hull,
  `η(t) ∉ int K_s` for `s < t` (proof: otherwise the filled hull would not grow near `t`, against the strict growth of
  Loewner hulls, QuantumZipper's `RS.fwdHull_ssubset`).
* **`exists_mem_fwdHull_sdiff`**: on every time interval `(r, t]` the trace visits `K_t \ K_r`.
* **`lt_traceFirstVisit_and_le`** (the window of (5.7)): a visited point `z ∈ ℍ \ K_r` in the interior of
  `K_{r+δ}` has `r < T_z ≤ r + δ` ("In particular, `z` was not visited by the counterflow by time `r`. … it must
  have been visited by time `r + δ`").
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

open QuantumZipper

/-! ### First visits -/

/-- The first time `T_z` at which the path `γ` visits `z` (`0` if it never does). -/
def traceFirstVisit (γ : ℝ≥0 → ℂ) (z : ℂ) : ℝ≥0 := sInf {t | γ t = z}

theorem traceFirstVisit_le {γ : ℝ≥0 → ℂ} {z : ℂ} {t : ℝ≥0} (h : γ t = z) : traceFirstVisit γ z ≤ t :=
  csInf_le (OrderBot.bddBelow _) h

/-- A visited point is visited at its first visit time. -/
theorem apply_traceFirstVisit {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {z : ℂ} (hz : ∃ t, γ t = z) :
    γ (traceFirstVisit γ z) = z :=
  (isClosed_eq hγ continuous_const).csInf_mem hz (OrderBot.bddBelow _)

theorem apply_ne_of_lt_traceFirstVisit {γ : ℝ≥0 → ℂ} {z : ℂ} {t : ℝ≥0} (h : t < traceFirstVisit γ z) :
    γ t ≠ z := fun h' => (traceFirstVisit_le h').not_gt h

/-- **Lemma 5.7's first visit in the needed form.** If every point `p ∈ S` is visited at some time `v` strictly
before the first visit of `z` (`γ w ≠ z` for `w ≤ v`), then the closure of `S` lies in the trace prefix
`γ([0, T_z])`. With `S` the post-`σ` portions of the descendants of the prefix ending at `z` (Lemma 5.7: the
counterflow hits the points of each descendant in reverse chronological order) this is `L_z ⊆ η'([0, T_z])`. -/
theorem closure_subset_image_traceFirstVisit {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {z : ℂ} (hz : ∃ t, γ t = z)
    {S : Set ℂ} (hS : ∀ p ∈ S, ∃ v, γ v = p ∧ ∀ w ≤ v, γ w ≠ z) :
    closure S ⊆ γ '' Icc 0 (traceFirstVisit γ z) := by
  refine closure_minimal ?_ (isCompact_Icc.image hγ).isClosed
  intro p hp
  obtain ⟨v, rfl, hv⟩ := hS p hp
  refine ⟨v, ⟨zero_le, ?_⟩, rfl⟩
  by_contra hlt
  push Not at hlt
  exact hv _ hlt.le (apply_traceFirstVisit hγ hz)

/-! ### Filled hulls of a generating trace -/

variable {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}

/-- The trace points in `ℍ` up to time `t` lie in the hull `K_t`. -/
theorem image_Icc_inter_H_subset_fwdHull {T : ℝ≥0∞} (hη : IsGeneratingTrace w T η) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) :
    η '' Icc 0 t ∩ H ⊆ fwdHull (fun s : ℝ => w s.toNNReal) t := by
  rintro p ⟨hpA, hpH⟩
  by_contra hpK
  obtain ⟨⟨z, -, hc⟩, -⟩ := hη.2.2 t ht
  have hp : p ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) t := ⟨hpH, hpK⟩
  rw [← hc] at hp
  exact (connectedComponentIn_subset _ _ hp).2 hpA

theorem continuous_of_isGeneratingTrace_top (hη : IsGeneratingTrace w ⊤ η) : Continuous η :=
  continuousOn_univ.1 (by simpa using hη.2.1)

/-- **A generating trace never visits the interior of an earlier hull**: for `s < t`, `η(t) ∉ int K_s`. -/
theorem notMem_interior_fwdHull_of_lt (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsGeneratingTrace w ⊤ η)
    {s t : ℝ≥0} (hst : s < t) :
    η t ∉ interior (fwdHull (fun s : ℝ => w s.toNNReal) s) := by
  intro hin
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hηc := continuous_of_isGeneratingTrace_top hη
  have hev : ∀ᶠ u in 𝓝[<] t, η u ∈ interior (fwdHull W s) :=
    nhdsWithin_le_nhds ((hηc.continuousAt).preimage_mem_nhds (isOpen_interior.mem_nhds hin))
  obtain ⟨l, hlt', hIoo⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hst).1 hev
  obtain ⟨s₁, hs₁, hs₁t⟩ := exists_between (max_lt hlt' hst)
  have hl : l < s₁ := (le_max_left _ _).trans_lt hs₁
  have hss : s < s₁ := (le_max_right _ _).trans_lt hs₁
  have hF1 := hη.2.2 s₁ ENNReal.coe_lt_top
  have hF2 := hη.2.2 t ENNReal.coe_lt_top
  have hmono : fwdHull W s₁ ⊆ fwdHull W t := fwdHull_mono.1 (by exact_mod_cast hs₁t.le)
  have hsub : fwdHull W s ⊆ fwdHull W s₁ := fwdHull_mono.1 (by exact_mod_cast hss.le)
  have heq := LP.eq_of_isFilling_of_subset hF1 hF2
    (fun z hz _ hz1 => by
      obtain ⟨r, hr, rfl⟩ := hz
      have hrs : s₁ < r := by
        by_contra h; push Not at h; exact hz1 ⟨r, ⟨hr.1, h⟩, rfl⟩
      have hmem : η r ∈ interior (fwdHull W s) := by
        rcases hr.2.lt_or_eq with h | h
        · exact hIoo ⟨hl.trans hrs, h⟩
        · rw [h]; exact hin
      exact hsub (interior_subset hmem))
    hmono (fwdHull_mono.2 _)
  exact (RS.fwdHull_ssubset hW hW0 s₁.coe_nonneg (by exact_mod_cast hs₁t)).ne heq

/-- **On every time interval `(r, t]` the trace visits `K_t \ K_r`** (otherwise the filled hull would not grow). -/
theorem exists_mem_fwdHull_sdiff (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsGeneratingTrace w ⊤ η)
    {r t : ℝ≥0} (hrt : r < t) :
    ∃ u, r < u ∧ u ≤ t ∧ η u ∈ fwdHull (fun s : ℝ => w s.toNNReal) t \
      fwdHull (fun s : ℝ => w s.toNNReal) r := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  by_contra hno
  push Not at hno
  have hFr := hη.2.2 r ENNReal.coe_lt_top
  have hFt := hη.2.2 t ENNReal.coe_lt_top
  have hmono : fwdHull W r ⊆ fwdHull W t := fwdHull_mono.1 (by exact_mod_cast hrt.le)
  have heq := LP.eq_of_isFilling_of_subset hFr hFt
    (fun z hz hzH hz1 => by
      obtain ⟨u, hu, rfl⟩ := hz
      have hru : r < u := by
        by_contra h; push Not at h; exact hz1 ⟨u, ⟨hu.1, h⟩, rfl⟩
      have hK : η u ∈ fwdHull W t := image_Icc_inter_H_subset_fwdHull hη ENNReal.coe_lt_top ⟨⟨u, hu, rfl⟩, hzH⟩
      by_contra hKr
      exact hno u hru hu.2 ⟨hK, hKr⟩)
    hmono (fwdHull_mono.2 _)
  exact (RS.fwdHull_ssubset hW hW0 r.coe_nonneg (by exact_mod_cast hrt)).ne heq

/-- **The window of (5.7).** A point `z ∈ ℍ \ K_r` that the trace visits and that lies in the interior of
`K_{r+δ}` has its first visit in `(r, r + δ]`. -/
theorem lt_traceFirstVisit_and_le (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsGeneratingTrace w ⊤ η) {z : ℂ}
    (hz : ∃ t, η t = z) {r δ : ℝ≥0} (hzH : z ∈ H) (hzr : z ∉ fwdHull (fun s : ℝ => w s.toNNReal) r)
    (hzi : z ∈ interior (fwdHull (fun s : ℝ => w s.toNNReal) (r + δ))) :
    r < traceFirstVisit η z ∧ traceFirstVisit η z ≤ r + δ := by
  have hηc := continuous_of_isGeneratingTrace_top hη
  have hvis := apply_traceFirstVisit hηc hz
  refine ⟨?_, ?_⟩
  · by_contra hle
    push Not at hle
    refine hzr (image_Icc_inter_H_subset_fwdHull hη ENNReal.coe_lt_top ⟨⟨_, ⟨zero_le, hle⟩, hvis⟩, hzH⟩)
  · by_contra hlt
    push Not at hlt
    have := notMem_interior_fwdHull_of_lt hw hw0 hη hlt
    rw [hvis] at this
    exact this (by exact_mod_cast hzi)

end Sec5

end InteractingSLE
