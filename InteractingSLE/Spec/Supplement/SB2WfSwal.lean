/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VrVis

/-!
# A point swallowed untouched is not the endpoint either

Packet PROVE-T14-SB2WORD (round 3, E7). NOJUMP's `Vr.trace_ne_of_mem_closure_hull` excludes the trace from a real point
swallowed untouched at every time strictly before the horizon `T`; `trace_end_ne_of_mem_closure_hull` excludes the
endpoint `η T` as well, for a trace continuous on `[0, T]`: near `T` the trace would stay in a half-ball inside the hull
at `s`, so the hull would not grow on a time interval just before `T`, against `hcap K_t = 2t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.SB.Wf

/-- **A point swallowed untouched at `s < T` is not the endpoint at `T`** (a continuous Loewner trace before every
earlier horizon, the driver allowed to depend on the horizon). -/
theorem trace_end_ne_of_mem_closure_fill {T : ℝ} {η : ℝ → ℂ} (hc : ContinuousOn η (Icc 0 T)) {s : ℝ} (hs : 0 ≤ s)
    (hsT : s < T)
    (hLT : ∀ T' : ℝ, s < T' → T' < T → ∃ U : ℝ → ℝ, Continuous U ∧ U 0 = 0 ∧ IsLoewnerTraceLT U T' η) {p : ℂ}
    (hpA : p ∉ η '' Icc 0 s) (hpK : p ∈ closure (fillH (η '' Icc 0 s))) : η T ≠ p := by
  intro htp
  have hAc : ∀ r, r ≤ T → IsCompact (η '' Icc 0 r) := fun r hr =>
    isCompact_Icc.image_of_continuousOn (hc.mono fun q hq => ⟨hq.1, hq.2.trans hr⟩)
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ z ∈ ball p δ, z ∉ η '' Icc 0 s := by
    have ho : IsOpen (η '' Icc 0 s)ᶜ := (hAc s hsT.le).isClosed.isOpen_compl
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1 ho p hpA
    exact ⟨δ, hδ, fun z hz => hsub hz⟩
  -- near `T` the trace stays in the ball
  have hT0 : 0 ≤ T := hs.trans hsT.le
  have hca : ContinuousWithinAt η (Icc 0 T) T := hc T ⟨hT0, le_rfl⟩
  obtain ⟨ε, hε, hεb⟩ := Metric.continuousWithinAt_iff.1 hca δ hδ
  set e : ℝ := min (ε / 4) ((T - s) / 4) with he
  have he0 : 0 < e := lt_min (by linarith) (by linarith)
  have he1 : e ≤ ε / 4 := min_le_left _ _
  have he2 : e ≤ (T - s) / 4 := min_le_right _ _
  set t₁ := T - 2 * e with ht₁
  set t₂ := T - e with ht₂
  set T' := T - e / 2 with hT'
  have ht₁0 : 0 ≤ t₁ := by linarith
  have hst₁ : s ≤ t₁ := by linarith
  have ht₂0 : 0 ≤ t₂ := by linarith
  have ht₁T : t₁ < T' := by linarith
  have ht₂T : t₂ < T' := by linarith
  have hsT' : s < T' := by linarith
  obtain ⟨U, hU, hU0, hη⟩ := hLT T' hsT' (by linarith)
  have hfill : ∀ r, 0 ≤ r → r < T' → IsFilling (fwdHull U r) (η '' Icc 0 r) := fun r hr0 hr => by
    rw [hη.2.2 r hr0 hr]; exact isFilling_fillH (hAc r (by linarith))
  have hsub : ball p δ ∩ H ⊆ fwdHull U s := by
    intro z hz
    by_contra hzK
    rw [← hη.2.2 s hs hsT'] at hpK
    obtain ⟨w, hwK, hwd⟩ := Metric.mem_closure_iff.1 hpK δ hδ
    have hwH : w ∈ H := Exist.fwdHull_subset_H hs hwK
    have hPA : ball p δ ∩ H ⊆ H \ η '' Icc 0 s := fun v hv => ⟨hv.2, hball v hv.1⟩
    exact Sec7.notMem_of_isFilling_of_isPreconnected (hfill s hs hsT') (HalfPlaneSep.isPreconnected_ball_inter_H p δ)
      hPA hz ⟨mem_ball'.2 hwd, hwH⟩ hzK hwK
  have hnear : ∀ r ∈ Icc t₁ t₂, η r ∈ ball p δ := fun r hr => by
    have h1 : dist r T < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2]
    have h2 := hεb ⟨by linarith [hr.1], by linarith [hr.2]⟩ h1
    rw [htp] at h2
    exact h2
  set P := H \ fwdHull U t₁ with hPdef
  have hPA : P ⊆ H \ η '' Icc 0 t₂ := by
    rintro v ⟨hvH, hvK⟩
    refine ⟨hvH, ?_⟩
    rintro ⟨r, hr, rfl⟩
    rcases le_or_gt r t₁ with hr1 | hr1
    · exact hvK (Sec5.CrossRestart.inter_H_subset_of_isFilling (hfill t₁ ht₁0 ht₁T) ⟨⟨r, ⟨hr.1, hr1⟩, rfl⟩, hvH⟩)
    · exact hvK (WangWu.fwdHull_mono hst₁ (hsub ⟨hnear r ⟨hr1.le, hr.2⟩, hvH⟩))
  have hPpre : IsPreconnected P := ZhanGT4.IsHPHull.isPreconnected_H_diff (isHPHull_fwdHull hU ht₁0)
  have hK2b : Bornology.IsBounded (fwdHull U t₂) := (isHPHull_fwdHull hU ht₂0).2.1
  obtain ⟨z₀, hz₀P, hz₀K⟩ : ∃ z ∈ P, z ∉ fwdHull U t₂ := by
    by_contra hcon
    push Not at hcon
    exact (hfill t₁ ht₁0 ht₁T).2 (hK2b.subset hcon)
  have hK21 : fwdHull U t₂ ⊆ fwdHull U t₁ := by
    intro z hz
    by_contra hz1
    have hzP : z ∈ P := ⟨Exist.fwdHull_subset_H ht₂0 hz, hz1⟩
    exact Sec7.notMem_of_isFilling_of_isPreconnected (hfill t₂ ht₂0 ht₂T) hPpre hPA hz₀P hzP hz₀K hz
  have heq : fwdHull U t₁ = fwdHull U t₂ := le_antisymm (WangWu.fwdHull_mono (by linarith)) hK21
  have h1 := hcap_fwdHull hU hU0 ht₁0
  have h2 := hcap_fwdHull hU hU0 ht₂0
  have hsub' : (⟨fwdHull U t₁, isHPHull_fwdHull hU ht₁0⟩ : HPHull) = ⟨fwdHull U t₂, isHPHull_fwdHull hU ht₂0⟩ :=
    Subtype.ext heq
  rw [hsub', h2] at h1
  linarith

/-- **The generating-trace form**: a point swallowed untouched at `s < T` is not the endpoint of a generating trace on
`[0, T]` of a driver continuous before `T`. -/
theorem gen_end_ne_of_mem_closure_fill {w : ℝ≥0 → ℝ} {T : ℝ≥0} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {r | (r : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {s : ℝ≥0} (hsT : s < T) {p : ℂ}
    (hpA : p ∉ η '' Icc 0 s) (hpK : p ∈ closure (fillH (η '' Icc 0 s))) : η T ≠ p := by
  have hc : ContinuousOn (fun r : ℝ => η r.toNNReal) (Icc 0 T) := by
    refine hη.2.1.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T
    exact ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hr.2)
  have himg : ∀ r : ℝ≥0, η '' Icc 0 r = (fun q : ℝ => η q.toNNReal) '' Icc 0 (r : ℝ) := fun r => by
    rw [image_toNNReal_Icc η r.coe_nonneg, Real.toNNReal_coe]
  have hLT : ∀ T' : ℝ, (s : ℝ) < T' → T' < T →
      ∃ U : ℝ → ℝ, Continuous U ∧ U 0 = 0 ∧ IsLoewnerTraceLT U T' (fun q : ℝ => η q.toNNReal) := by
    intro T' hsT' hT'T
    have hT'0 : 0 ≤ T' := s.coe_nonneg.trans hsT'.le
    have hlt : ENNReal.ofReal T' < (T : ℝ≥0∞) := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal hT'0 ENNReal.coe_ne_top]
      exact hT'T
    refine ⟨frozenDrive w T', continuous_frozenDrive_of_lt hw hlt, by rw [frozenDrive_zero hT'0, hw0],
      hη.isLoewnerTraceLT hlt⟩
  have h := trace_end_ne_of_mem_closure_fill hc s.coe_nonneg (NNReal.coe_lt_coe.2 hsT) hLT
    (by rw [← himg]; exact hpA) (by rw [← himg]; exact hpK)
  simpa using h

end InteractingSLE.Theorem14.SB.Wf
