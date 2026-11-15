/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VqEnd
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov
import InteractingSLE.Spec.Sec7.R6FdLand
import InteractingSLE.Spec.Supplement.Aux10FullLocal
import InteractingSLE.Spec.Sec7.Lemma76EJunction

/-!
# A real tip is first reached at a collision of the zero mark

Packet PROVE-T14-SB2WORD (round 2, toward E7). For a Loewner trace `η` of a continuous driver `U` from `0`,
continuous on `[0, T]`, whose tip at `T` is a real point `x > 0`: at the first time `τ₀ ≤ T` with `η τ₀ = η T`
the zero right mark collides with the driver, so the colliding right marks are exactly those at or left of `x`
(`FlowStopIdentLL.rightImg_eq_iff_of_zero_collision`). Two facts give it:

* before `τ₀` the trace has no real point right of `x`: such a point `x₁` would make `x` (strictly between the real
  points `0` and `x₁` and off the earlier trace) a point of the closed fill away from the closure of its complement
  (Yuan's `mem_closure_fillH_of_lt_of_lt` and `mem_of_mem_closure_of_mem_frontier`), while the tip at `τ₀` is a limit
  of points off the later hull;
* hence `x` is alive at the last zero collision `S < τ₀` (a dead `x` would give a real trace point `≥ x` before `τ₀`,
  `R6Fd.exists_real_ge_of_mem_closure_fillH`), and the landing at `τ₀` swallows it
  (`Vo.rightImg_zero_eq_at_later_real_tip`).

* **`exists_first_zero_collision`**; **`exists_first_threshold_right`** (a bad real positive tip forces the right
  threshold condition at its first visit). The left side follows by reflection (`Vo.isLoewnerTraceLT_reflect`).

Deterministic Loewner geometry; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Vo

open MartChar.RealFlow

variable {U : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}

/-- The hull grows with time. -/
theorem fwdHull_mono {W : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) : fwdHull W s ⊆ fwdHull W t := fun _ hz =>
  ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal hst)⟩

/-- **The tip of a Loewner trace at a positive time is the limit of its inverse map at `0`.** -/
theorem tendsto_tip (hU : Continuous U) (hU0 : U 0 = 0) (hη : IsLoewnerTraceLT U T η)
    (hc : ContinuousOn η (Icc 0 T)) {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    Tendsto (fwdMapInv U t) (𝓝[H] 0) (𝓝 (η t)) := by
  have hη' := isLoewnerTraceLT_mono hη htT
  have hc' : ContinuousOn η (Icc 0 t) := hc.mono fun s hs => ⟨hs.1, hs.2.trans htT⟩
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη' hU hU0 ht hc'
  have htip := TraceClose.extendFrom_zero_eq hη' hU hU0 ht hc'
  rw [← htip]
  exact hB.tendsto (show (0 : ℂ) ∈ Hbar by simp [Hbar])

/-- The trace lies in `ℍ̄`. -/
theorem mem_Hbar_of_trace (hU : Continuous U) (hU0 : U 0 = 0) (hη : IsLoewnerTraceLT U T η)
    (hc : ContinuousOn η (Icc 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) : η t ∈ Hbar := by
  rcases ht.1.lt_or_eq with h | h
  · have hlim := tendsto_tip hU hU0 hη hc h ht.2
    have hNB : (𝓝[H] (0 : ℂ)).NeBot := Theorem14.GW1P.neBot_nhdsWithin_H (by simp [Hbar])
    refine isClosed_le continuous_const Complex.continuous_im |>.mem_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 h.le hw).1.le
  · rw [← h, hη.1]
    simp [Hbar]

/-- **A real positive tip is first reached at a collision of the zero right mark.** -/
theorem exists_first_zero_collision (hU : Continuous U) (hU0 : U 0 = 0) (hT : 0 < T) (hη : IsLoewnerTraceLT U T η)
    (hc : ContinuousOn η (Icc 0 T)) (hre : (η T).im = 0) (hpos : 0 < (η T).re) :
    ∃ τ₀, 0 < τ₀ ∧ τ₀ ≤ T ∧ η τ₀ = η T ∧ rightImg U 0 τ₀ = U τ₀ := by
  set x := (η T).re with hxdef
  have hηT : η T = (x : ℂ) := Complex.ext (by simp [hxdef]) (by simp [hre])
  -- the first visit
  set P := {t | t ∈ Icc 0 T ∧ η t = η T} with hPdef
  have hPc : IsClosed P := by
    have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := η T))
    convert this using 1
    ext t
    simp only [hPdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hPne : P.Nonempty := ⟨T, ⟨⟨hT.le, le_rfl⟩, rfl⟩⟩
  have hPbdd : BddBelow P := ⟨0, fun t ht => ht.1.1⟩
  set τ₀ := sInf P with hτ₀
  have hτ₀P : τ₀ ∈ P := hPc.csInf_mem hPne hPbdd
  have hτ₀T : τ₀ ≤ T := hτ₀P.1.2
  have hfirst : ∀ s, 0 ≤ s → s < τ₀ → η s ≠ η T := fun s hs hsτ he =>
    absurd (csInf_le hPbdd ⟨⟨hs, hsτ.le.trans hτ₀T⟩, he⟩) (not_le.2 hsτ)
  have hτ₀0 : 0 < τ₀ := by
    rcases hτ₀P.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := hτ₀P.2
      rw [← h, hη.1, hηT] at h0
      have : x = 0 := by exact_mod_cast h0.symm
      linarith
  have hτx : η τ₀ = (x : ℂ) := hτ₀P.2.trans hηT
  -- the hull before `τ₀` is the fill of the trace
  have hhull : ∀ s, 0 ≤ s → s < τ₀ → fwdHull U s = fillH (η '' Icc 0 s) := fun s hs hsτ =>
    hη.2.2 s hs (lt_of_lt_of_le hsτ hτ₀T)
  have hHbar : ∀ s, s ≤ T → MapsTo η (Icc 0 s) Hbar := fun s hsT t ht =>
    mem_Hbar_of_trace hU hU0 hη hc ⟨ht.1, ht.2.trans hsT⟩
  -- the tip at `τ₀` is adherent to the complement of every earlier hull
  have hlim := tendsto_tip hU hU0 hη hc hτ₀0 hτ₀T
  rw [hτx] at hlim
  have hadh : ∀ s, 0 ≤ s → s < τ₀ → (x : ℂ) ∈ closure (H \ fillH (η '' Icc 0 s)) := fun s hs hsτ => by
    have hNB : (𝓝[H] (0 : ℂ)).NeBot := Theorem14.GW1P.neBot_nhdsWithin_H (by simp [Hbar])
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hm := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hτ₀0.le hw
    rw [← hhull s hs hsτ]
    exact ⟨hm.1, fun hK => hm.2 (fwdHull_mono hsτ.le hK)⟩
  -- (A) before `τ₀` no real point of the trace lies right of `x`
  have hA : ∀ s, s ∈ Icc 0 τ₀ → (η s).im = 0 → (η s).re ≤ x := by
    intro s hs hsim
    by_contra hgt
    push Not at hgt
    have hsτ : s < τ₀ := lt_of_le_of_ne hs.2 fun h => by
      rw [h, hτx] at hgt; simp at hgt
    have hxP : (x : ℂ) ∉ η '' Icc 0 s := by
      rintro ⟨t, ht, he⟩
      exact hfirst t ht.1 (lt_of_le_of_lt ht.2 hsτ) (he.trans hηT.symm)
    have hcl := YuanCharacterisation.mem_closure_fillH_of_lt_of_lt (hc.mono fun t ht => ⟨ht.1, ht.2.trans
      (hsτ.le.trans hτ₀T)⟩) (hHbar s (hsτ.le.trans hτ₀T)) (u₁ := 0) (u₂ := s) ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩
      (by rw [hη.1]; simp) hsim (by rw [hη.1]; simpa using hpos) hgt hxP
    have hPc' : IsClosed (η '' Icc 0 s) :=
      (isCompact_Icc.image_of_continuousOn (hc.mono fun t ht => ⟨ht.1, ht.2.trans
        (hsτ.le.trans hτ₀T)⟩)).isClosed
    refine hxP (YuanCharacterisation.mem_of_mem_closure_of_mem_frontier hPc' (by simp) hcl ?_)
    refine ⟨hadh s hs.1 hsτ, fun hint => ?_⟩
    have := interior_subset hint
    exact absurd this.1 (by simp [H])
  -- (B) the last zero collision before `τ₀`
  set C := {t | t ∈ Icc 0 τ₀ ∧ rightImg U 0 t = U t} with hCdef
  have hCc : IsClosed C := by
    have hcont : ContinuousOn (fun t => rightImg U 0 t - U t) (Icc 0 τ₀) :=
      ((continuousOn_rightImg hU 0).mono fun t ht => ht.1).sub hU.continuousOn
    have := hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := (0 : ℝ)))
    convert this using 1
    ext t
    simp only [hCdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      sub_eq_zero]
  have hC0 : (0 : ℝ) ∈ C := ⟨⟨le_rfl, hτ₀0.le⟩, by rw [rightImg_zero hU hU0 le_rfl, hU0]⟩
  have hCbdd : BddAbove C := ⟨τ₀, fun t ht => ht.1.2⟩
  set S := sSup C with hSdef
  have hSC : S ∈ C := hCc.csSup_mem ⟨0, hC0⟩ hCbdd
  refine ⟨τ₀, hτ₀0, hτ₀T, hτ₀P.2, ?_⟩
  rcases hSC.1.2.lt_or_eq with hSτ | hSτ
  swap
  · rw [← hSτ]; exact hSC.2
  have hS0 : 0 ≤ S := hSC.1.1
  have hsep : ∀ t ∈ Ioo S τ₀, U t < rightImg U 0 t := fun t ht =>
    lt_of_le_of_ne (le_rightImg hU 0 (hS0.trans ht.1.le)) fun he =>
      absurd (le_csSup hCbdd ⟨⟨hS0.trans ht.1.le, ht.2.le⟩, he.symm⟩) (not_le.2 ht.1)
  -- `x` is alive at `S`
  have hxS : Alive U x S := by
    by_contra hdead
    have hcl : (x : ℂ) ∈ closure (fwdHull U S) := by
      by_contra hn
      obtain ⟨v, hv⟩ := Aux10.exists_isForwardSol_of_notMem_closure hU hU0 hS0 hpos.ne' hn
      exact hdead (Sec7.Lemma76E.alive_of_isForwardSol hU hS0 (by rw [hU0]; exact hpos) hv)
    rw [hhull S hS0 hSτ] at hcl
    have hcpt : IsCompact (η '' Icc 0 S) :=
      isCompact_Icc.image_of_continuousOn (hc.mono fun t ht => ⟨ht.1, ht.2.trans (hSτ.le.trans hτ₀T)⟩)
    obtain ⟨_, ⟨s₂, hs₂, rfl⟩, him, hge⟩ := Sec7.R6Fd.exists_real_ge_of_mem_closure_fillH hcpt
      (hHbar S (hSτ.le.trans hτ₀T)).image_subset hcl
    have hle := hA s₂ ⟨hs₂.1, hs₂.2.trans hSτ.le⟩ him
    have heq : η s₂ = η T := by
      rw [hηT]
      exact Complex.ext (by simp; linarith) (by simp [him])
    exact hfirst s₂ hs₂.1 (lt_of_le_of_lt hs₂.2 hSτ) heq
  exact rightImg_zero_eq_at_later_real_tip (σ := τ₀) hU hU0 hS0 hSτ hSC.2 hsep hlim hpos le_rfl hxS

/-- **A bad real positive tip forces a threshold at its first visit**: if the right cumulative weight up to the tip
`x = Re η(T) > 0` is `≤ −2`, then at the first time `τ₀ ≤ T` with `η τ₀ = η T` the colliding right marks are those
`≤ x` and their weights sum to `≤ −2` (the right half of the continuation threshold condition). -/
theorem exists_first_threshold_right (hU : Continuous U) (hU0 : U 0 = 0) (hT : 0 < T)
    (hη : IsLoewnerTraceLT U T η) (hc : ContinuousOn η (Icc 0 T)) (hre : (η T).im = 0) (hpos : 0 < (η T).re)
    {nR : ℕ} (xR : Fin nR → ℝ) (ρR : Fin nR → ℝ) (hbad : Vq.wR xR ρR (η T).re ≤ -2) :
    ∃ τ₀, 0 < τ₀ ∧ τ₀ ≤ T ∧ η τ₀ = η T ∧
      ∑ j ∈ univ.filter (fun j => rightImg U (xR j) τ₀ = U τ₀), ρR j ≤ -2 := by
  obtain ⟨τ₀, hτ₀0, hτ₀T, hτ₀e, hzero⟩ := exists_first_zero_collision hU hU0 hT hη hc hre hpos
  refine ⟨τ₀, hτ₀0, hτ₀T, hτ₀e, ?_⟩
  have hη' := isLoewnerTraceLT_mono hη hτ₀T
  have hc' : ContinuousOn η (Icc 0 τ₀) := hc.mono fun s hs => ⟨hs.1, hs.2.trans hτ₀T⟩
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη' hU hU0 hτ₀0 hc'
  have htip := TraceClose.extendFrom_zero_eq hη' hU hU0 hτ₀0 hc'
  rw [Vq.filter_eq_of_zero_collision hU hU0 hτ₀0.le hB htip hzero xR, hτ₀e]
  exact hbad

end InteractingSLE.Theorem14.SB.Vo
