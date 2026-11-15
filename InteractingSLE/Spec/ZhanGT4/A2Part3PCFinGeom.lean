/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFinEnd
import InteractingSLE.Spec.ZhanGT4.A2Part2Count
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# First contact with a small simple prefix

Packet PROVE-ZHAN-A2P3-PC. The finite-time kernel identity places the live-domain
frontier on the closure of earlier hulls. Real-flow clearance at the small root
then reduces first contact to the compact-interior first-hit API of A.2 part 2.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Bornology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-- The unbounded part of a closed set's complement is the complement of its
half-plane filling. -/
theorem unbddPart_eq_compl_fillH_of_isClosed {S : Set ℂ} (hS : IsClosed S) :
    unbddPart S = H \ fillH S := by
  apply Subset.antisymm
  · rintro z ⟨U, ⟨hUc, hUS, hUb⟩, hz⟩
    exact HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hS hUc hUb hUS hz
  · intro z hz
    have hh := (HalfPlaneSep.mem_H_diff_fillH_of_isClosed hS).1 hz
    exact Set.mem_sUnion.2 ⟨connectedComponentIn (H \ S) z,
      ⟨isPreconnected_connectedComponentIn, connectedComponentIn_subset _ _, hh.2⟩,
      mem_connectedComponentIn hh.1⟩

/-- Inside `H`, the live-domain frontier at a positive time lies in the closure
of the earlier hull union, including when the time swallows a whole component. -/
theorem mem_closure_hullBefore_of_mem_frontier
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    {p : ℂ} (hp : p ∈ frontier (H \ fwdHull W T)) (hpH : p ∈ H) :
    p ∈ closure (A34.hullBefore W T) := by
  have hb : IsBounded (A34.hullBefore W T) := by
    refine (isBounded_fwdHull hW T).subset ?_
    intro z hz
    simp only [A34.hullBefore, mem_iUnion] at hz
    obtain ⟨s, hs, hz⟩ := hz
    exact (fwdHull_mono (W := W)).1 hs.2.le hz
  rw [A34.compl_fwdHull_eq_unbddPart hW hW0 hT,
    unbddPart_eq_compl_fillH_of_isClosed isClosed_closure] at hp
  rcases frontier_H_diff_fillH_subset hb.closure hp with him | hcl
  · exact False.elim ((ne_of_gt hpH) him)
  · simpa only [closure_closure] using hcl

/-- A real forward solution gives a ball around its start disjoint from every
earlier closed hull. -/
theorem exists_ball_disjoint_closure_fwdHull_of_isForwardSol
    {W : ℝ → ℝ} (hW : Continuous W) {x R : ℝ} (hR : 0 ≤ R)
    {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) R u) :
    ∃ ε > 0, ∀ s : ℝ≥0, (s : ℝ) ≤ R →
      Disjoint (ball (x : ℂ) ε) (closure (fwdHull W s)) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hR hu
  let E := Real.exp (2 / δ ^ 2 * R)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨δ / E, div_pos hδ hE, fun s hs => ?_⟩
  apply Disjoint.closure_right _ isOpen_ball
  refine Set.disjoint_left.2 fun z hz hzK => ?_
  have hzR : z ∈ fwdHull W R := (fwdHull_mono (W := W)).1 hs hzK
  exact not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzK.1
    ((mul_lt_mul_of_pos_right (show ‖z - x‖ < δ / E by
      simpa only [mem_ball, dist_eq_norm] using hz) hE).trans_eq
      (div_mul_cancel₀ δ hE.ne')) hzR

/-- First contact with a compact arc rooted at an alive real point occurs on
the large live-domain frontier, hence on the closure of its earlier hulls. -/
theorem exists_contact_mem_closure_hullBefore_of_arc
    {W Wraw : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {x : ℝ} {w₁ : ℝ → ℝ} {q Q : ℝ} {cap : ℝ≥0∞} {T R : ℝ≥0}
    (hT : (T : ℝ≥0∞) = contactTime 0 Wraw cap x w₁ q)
    (hTcap : (T : ℝ≥0∞) < cap) (hTR : T < R)
    (hagree : EqOn Wraw W (Icc 0 R))
    {α : ℝ → ℂ} (hQ : 0 < Q) (hα : ContinuousOn α (Icc 0 Q))
    (hα0 : α 0 = (x : ℂ)) (hαH : MapsTo α (Ioc 0 Q) H)
    (hK : closure (physHull x w₁ q) = α '' Icc 0 Q)
    {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) R u) :
    ∃ p : ℂ, p ∈ closure (A34.hullBefore Wraw T) ∧
      p ∈ H ∧ p ∈ closure (physHull x w₁ q) := by
  obtain ⟨ε, hε, hdroot⟩ := exists_ball_disjoint_closure_fwdHull_of_isForwardSol
    hW R.coe_nonneg hu
  have hWK : ∀ s : ℝ≥0, s < R → fwdHull Wraw s = fwdHull W s :=
    fun s hs => fwdHull_eq_of_eqOn s.coe_nonneg (NNReal.coe_lt_coe.2 hs) hagree
  let L := (α '' Icc 0 Q) \ ball (x : ℂ) ε
  have hLc : IsCompact L := (isCompact_Icc.image_of_continuousOn hα).diff isOpen_ball
  have hLH : L ⊆ H := by
    rintro z ⟨⟨s, hs, rfl⟩, hn⟩
    have hs0 : 0 < s := lt_of_le_of_ne hs.1 fun he => by
      rw [← he, hα0] at hn
      exact hn (mem_ball_self hε)
    exact hαH ⟨hs0, hs.2⟩
  have hhit : ∀ s : ℝ≥0, s < R →
      (closure (physHull 0 Wraw s) ∩ closure (physHull x w₁ q)).Nonempty →
      (fwdHull W s ∩ L).Nonempty := by
    intro s hs ⟨p, hp, hpk⟩
    rw [physHull_zero, hWK s hs] at hp
    have hpL : p ∈ L := ⟨hK ▸ hpk, fun hball =>
      (hdroot s (NNReal.coe_le_coe.2 hs.le)).ne_of_mem hball hp rfl⟩
    exact ⟨p, (isHPHull_fwdHull hW s.coe_nonneg).mem_of_mem_closure (hLH hpL) hp, hpL⟩
  let E : ℝ≥0∞ := ⨅ (s : ℝ≥0)
    (_ : (closure (physHull 0 Wraw s) ∩ closure (physHull x w₁ q)).Nonempty), (s : ℝ≥0∞)
  have hE : E = (T : ℝ≥0∞) := by
    have hc : (T : ℝ≥0∞) = min cap E := hT
    apply le_antisymm
    · by_contra h
      exact (ne_of_lt (lt_min hTcap (not_le.1 h))) hc
    · exact hc ▸ min_le_right cap E
  have hER : E < (R : ℝ≥0∞) := hE ▸ ENNReal.coe_lt_coe.2 hTR
  simp only [E, iInf_lt_iff] at hER
  obtain ⟨s, hsmeet, hsR⟩ := hER
  have hsR' : s < R := ENNReal.coe_lt_coe.1 hsR
  obtain ⟨s₀, hfirst, hs₀s⟩ := A2Part2.exists_isFirstHit hW hLc hLH
    s.coe_nonneg (hhit s hsR' hsmeet)
  have hs₀R : s₀ < R := hs₀s.trans_lt (NNReal.coe_lt_coe.2 hsR')
  have hmeet₀ : (closure (physHull 0 Wraw s₀.toNNReal) ∩
      closure (physHull x w₁ q)).Nonempty := by
    obtain ⟨p, hpK, hpL⟩ := hfirst.2.1
    refine ⟨p, ?_, hK ▸ hpL.1⟩
    rw [physHull_zero, hWK s₀.toNNReal
      ((Real.toNNReal_lt_iff_lt_coe hfirst.1).2 hs₀R), Real.coe_toNNReal _ hfirst.1]
    exact subset_closure hpK
  have hEs₀ : E ≤ ENNReal.ofReal s₀ := by
    have hh : E ≤ (s₀.toNNReal : ℝ≥0∞) := iInf₂_le s₀.toNNReal hmeet₀
    simpa only [ENNReal.ofReal] using hh
  have hs₀E : ENNReal.ofReal s₀ ≤ E := by
    refine le_iInf₂ fun t ht => ?_
    by_contra hn
    have hts₀ : (t : ℝ) < s₀ := by
      have hh : ENNReal.ofReal (t : ℝ) < ENNReal.ofReal s₀ := by
        simpa only [ENNReal.ofReal_coe_nnreal] using not_le.1 hn
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 hh).1
    obtain ⟨p, hpK, hpL⟩ := hhit t
      (NNReal.coe_lt_coe.1 (hts₀.trans hs₀R)) ht
    have hh := hfirst.2.2 t t.coe_nonneg hts₀
    exact Set.not_nonempty_iff_eq_empty.2 hh ⟨p, hpK, hpL⟩
  have hs₀T : s₀ = (T : ℝ) := by
    apply (ENNReal.ofReal_eq_ofReal_iff hfirst.1 T.coe_nonneg).1
    simpa only [ENNReal.ofReal_coe_nnreal] using (le_antisymm hs₀E hEs₀).trans hE
  have hTpos : (0 : ℝ) < T := by
    have hs₀pos : 0 < s₀ := lt_of_le_of_ne hfirst.1 fun he => by
      obtain ⟨p, hp, -⟩ := hfirst.2.1
      rw [← he, RS.fwdHull_zero_eq_empty hW] at hp
      exact hp
    rwa [hs₀T] at hs₀pos
  have hArc : IsPreconnected (α '' Ioc 0 Q) :=
    isPreconnected_Ioc.image α (hα.mono Ioc_subset_Icc_self)
  have hroot : (x : ℂ) ∈ closure (α '' Ioc 0 Q) := by
    have h0 : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) Q) := by
      rw [closure_Ioc hQ.ne]
      exact ⟨le_rfl, hQ.le⟩
    rw [← hα0]
    exact (hα.continuousWithinAt ⟨le_rfl, hQ.le⟩).mono Ioc_subset_Icc_self
      |>.mem_closure_image h0
  obtain ⟨z, hzball, hzArc⟩ := mem_closure_iff.1 hroot _ isOpen_ball (mem_ball_self hε)
  have hzD : z ∈ H \ fwdHull W T := by
    refine ⟨hαH.image_subset hzArc, fun hzK => ?_⟩
    exact (hdroot T (NNReal.coe_le_coe.2 hTR.le)).ne_of_mem hzball (subset_closure hzK) rfl
  obtain ⟨b, hbK, hbL⟩ := hfirst.2.1
  rw [hs₀T] at hbK
  have hbArc : b ∈ α '' Ioc 0 Q := by
    obtain ⟨t, ht, htb⟩ := hbL.1
    refine ⟨t, ⟨?_, ht.2⟩, htb⟩
    refine lt_of_le_of_ne ht.1 fun he => ?_
    rw [← he, hα0] at htb
    exact hbL.2 (htb ▸ mem_ball_self hε)
  obtain ⟨p, hpArc, hpfr⟩ := CA.Kernel.inter_frontier_nonempty_of_isPreconnected hArc
    (FwdHolo.isOpen_compl_fwdHull hW T.coe_nonneg) hzArc hzD hbArc
    (fun hbD => hbD.2 hbK)
  have hpH := hαH.image_subset hpArc
  refine ⟨p, ?_, hpH, hK ▸ image_mono Ioc_subset_Icc_self hpArc⟩
  rw [hullBefore_eq_of_eqOn_lt (W := Wraw) (U := W)
    (fun t ht => hagree ⟨ht.1, ht.2.le.trans (NNReal.coe_le_coe.2 hTR.le)⟩)]
  exact mem_closure_hullBefore_of_mem_frontier hW hW0 hTpos hpfr hpH

end InteractingSLE.ZhanGT4.A2X.P3
