/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HGateCut

/-!
# The local orientation of an excursion crosscut

Packet PROVE-PROP51H-TOPO2 (ruling R71; Astra's follow-up 4, §1.7 "The orientation forces an eastern endpoint").
Near an interior point `q = Ψ(η(u₀))` of a completed chart crosscut `κ`, the **physical side index**
`windRef z = windNum (flowReferenceLoop η) (cayley (Ψ⁻¹ z))` (`1` on the left of `η`, `0` on its right) and the
winding number of the crosscut's closed loop `κ.loop` jump together:

  `windRef z - windNum κ.loop z` is constant for `z` near `q` off the chart flow set
  (`ExcursionChartCut.exists_local_const`).

This is the boundary orientation of a Jordan domain preserved by the conformal chart. Proof: one auxiliary loop
`m` in `ℍ` runs backwards along a compact piece of the crosscut through `q` and returns around `q`; the crossing
lemma `Orientation.windNum_add_windNum_eq` applied twice — in the chart to `(κ.loop, m)` and in the compactified
physical plane to `(flowReferenceLoop η, Ψ⁻¹ ∘ m)` — and the conformal invariance of winding numbers
(`Prop51HTopo.windNum_discRevChart`) give the identity.

Deterministic; nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Prop51HGate

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G Prop51HTopo
open _root_.InteractingSLE.Orientation

variable {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} {C : Set ℝ}

theorem ofReal_notMem_H (y : ℝ) : (y : ℂ) ∉ H := fun h =>
  lt_irrefl _ (show (0 : ℝ) < (y : ℂ).im from h)

theorem discTime_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : discTime x < discTime y := by
  rw [discTime, discTime, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem discTime_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : discTime x ≤ discTime y := by
  rcases hxy.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (discTime_lt hx h).le

theorem continuousOn_discRevChart (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    ContinuousOn (discRevChart w s) H :=
  QuantumZipper.CA.differentiableOn_cayley_Hbar.continuousOn.comp (continuousOn_revChartInv hw hw0 hs)
    fun _ hz => H_subset_Hbar (revChartInv_mem hw hw0 hs hz).1

theorem injOn_discRevChart (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) :
    InjOn (discRevChart w s) H := by
  have hF := isConformalBijection_revChartInv hw hw0 hs
  intro x hx y hy he
  exact hF.2.injOn hx hy (cayley_injOn_Hbar
    (H_subset_Hbar (hF.2.mapsTo hx).1) (H_subset_Hbar (hF.2.mapsTo hy).1) he)

/-- The global reference index is zero on the right of the physical flow line. -/
theorem windNum_flowReferenceLoop_of_mem_right (hη : IsProperArc η) {z : ℂ}
    (hz : z ∈ rightSideOf (arcRange η)) : windNum (flowReferenceLoop η) (cayley z) = 0 := by
  have hα := hη.isDiscCrosscut_toDisc
  have hcl : flowReferenceLoop η '' Icc 0 1 ⊆ closure (crossSide (toDisc η) 1) := by
    intro v hv
    rcases image_crossLoop_subset hα.one hv with h | h
    · exact hα.crossRange_subset_closure_crossSide (Or.inl rfl) h
    · exact hα.semiArc_subset_closure_crossSide (Or.inl rfl) h
  exact windNum_eq_zero_of_mem_crossSide_neg hα (continuousOn_crossLoop hα.cont hα.one)
    (crossLoop_loop hα.zero hα.one) hcl ((hη.mem_rightSideOf_iff hz.1.1).1 hz)

/-- A chart point off the chart flow set has its compactified physical image off the disc picture of `η`. -/
theorem discRevChart_notMem_crossRange (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    (hη : IsProperArc η) {z : ℂ} (hzH : z ∈ H) (hzA : z ∉ chartFlowSet η w s) :
    discRevChart w s z ∉ crossRange (toDisc η) := by
  intro h
  have hD := revChartInv_mem hw hw0 hs hzH
  have hP := (hη.cayley_mem_crossRange_iff (H_subset_Hbar hD.1)).1 h
  exact hzA ⟨revChartInv w s z, ⟨hP, hD⟩, revChart_revChartInv hw hw0 hs hzH⟩

namespace ExcursionChartCut

variable (κ : ExcursionChartCut η w s C)

theorem discRevChart_cut (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : discRevChart w s (κ.cut t) = toDisc η (discTime (κ.time t)) := by
  rw [discRevChart, κ.revChartInv_cut hw hw0 hs ht, toDisc_discTime η (κ.time_pos ht).le]

/-- A point of the closed loop equal to an interior crosscut point `κ.cut t₀` is met only at parameter
`t₀ / 2`. -/
theorem eq_of_loop_eq_cut (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {t t₀ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (he : κ.loop t = κ.cut t₀) :
    2 * t = t₀ := by
  obtain ⟨u, hu, hue⟩ := κ.exists_of_loop_mem_H ht (he ▸ κ.cut_mem_H hw hs ht₀)
  have hut : u = t₀ := κ.injOn_cut hη hw hw0 hs hu ht₀ (hue.symm.trans he)
  rcases le_or_gt t (1 / 2) with h | h
  · rw [κ.loop_of_le h] at hue
    have h2 : 2 * t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc h2 with h0 | h1 | h2'
    · rw [h0, κ.cut_zero] at hue
      have := κ.cut_mem_H hw hs hu
      rw [← hue] at this
      exact (ofReal_notMem_H _ this).elim
    · rw [h1, κ.cut_one] at hue
      have := κ.cut_mem_H hw hs hu
      rw [← hue] at this
      exact (ofReal_notMem_H _ this).elim
    · rw [← hut]
      exact κ.injOn_cut hη hw hw0 hs h2' hu hue
  · rw [κ.loop_of_ge h.le] at hue
    have := κ.cut_mem_H hw hs hu
    rw [← hue] at this
    exact (ofReal_notMem_H _ this).elim

/-- **The local orientation of a chart crosscut.** Near an interior point of `κ`, the physical side index minus
the winding number of `κ.loop` is constant off the chart flow set. -/
theorem exists_local_const (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ ε > 0, ∀ z ∈ ball (κ.cut t₀) ε, ∀ z' ∈ ball (κ.cut t₀) ε, z ∈ H → z' ∈ H →
      z ∉ chartFlowSet η w s → z' ∉ chartFlowSet η w s →
        windNum (flowReferenceLoop η) (discRevChart w s z) - windNum κ.loop z =
          windNum (flowReferenceLoop η) (discRevChart w s z') - windNum κ.loop z' := by
  set t₁ : ℝ := t₀ / 2 with ht₁def
  set t₂ : ℝ := (t₀ + 1) / 2 with ht₂def
  have h01 : 0 < t₁ := by rw [ht₁def]; linarith [ht₀.1]
  have h10 : t₁ < t₀ := by rw [ht₁def]; linarith [ht₀.1]
  have h02 : t₀ < t₂ := by rw [ht₂def]; linarith [ht₀.2]
  have h21 : t₂ < 1 := by rw [ht₂def]; linarith [ht₀.2]
  have hI₁ : t₁ ∈ Ioo (0 : ℝ) 1 := ⟨h01, by linarith⟩
  have hI₂ : t₂ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, h21⟩
  have hsub : Icc t₁ t₂ ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨h01.trans_le ht.1, ht.2.trans_lt h21⟩
  set q := κ.cut t₀ with hqdef
  have hqH := κ.cut_mem_H hw hs ht₀
  have hinj := κ.injOn_cut hη hw hw0 hs
  have haq : κ.cut t₁ ≠ q := fun h => h10.ne (hinj hI₁ ht₀ h)
  have hbq : κ.cut t₂ ≠ q := fun h => h02.ne' (hinj hI₂ ht₀ h)
  obtain ⟨P, hPc, hP0, hP1, hPm⟩ := exists_path_H_avoid (κ.cut_mem_H hw hs hI₁)
    (κ.cut_mem_H hw hs hI₂) haq hbq
  -- the auxiliary loop: backwards along the crosscut from `t₂` to `t₁`, then back along `P`
  let τ : ℝ → ℝ := fun t => t₂ - 2 * t * (t₂ - t₁)
  have hτ : ∀ t ∈ Icc (0 : ℝ) (1 / 2), τ t ∈ Icc t₁ t₂ := fun t ht =>
    ⟨by dsimp only [τ]; nlinarith [ht.2], by dsimp only [τ]; nlinarith [ht.1]⟩
  let m : ℝ → ℂ := fun t => if t ≤ 1 / 2 then κ.cut (τ t) else P (2 * t - 1)
  have hm_le : ∀ t, t ≤ 1 / 2 → m t = κ.cut (τ t) := fun t ht => by simp only [m, ht, ↓reduceIte]
  have hm_ge : ∀ t, 1 / 2 ≤ t → m t = P (2 * t - 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hm_le _ le_rfl, show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, hP0]
      congr 1
      dsimp only [τ]
      ring
    · simp only [m, not_le.2 h, ↓reduceIte]
  have hmc : ContinuousOn m (Icc 0 1) := by
    have h1 : ContinuousOn m (Icc 0 (1 / 2)) := by
      refine ContinuousOn.congr (f := fun t => κ.cut (τ t)) ?_ fun t ht => hm_le t ht.2
      exact κ.cont.comp (by fun_prop) fun t ht => Icc_subset_Icc h01.le h21.le (hτ t ht)
    have h2 : ContinuousOn m (Icc (1 / 2) 1) :=
      ContinuousOn.congr (f := fun t => P (2 * t - 1)) (hPc.comp (by fun_prop)).continuousOn
        fun t ht => hm_ge t ht.1
    have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this
  have hm0 : m 0 = κ.cut t₂ := by rw [hm_le 0 (by norm_num)]; congr 1; dsimp only [τ]; ring
  have hm1 : m 1 = κ.cut t₂ := by rw [hm_ge 1 (by norm_num), show 2 * (1 : ℝ) - 1 = 1 by norm_num, hP1]
  have hmh : m (1 / 2) = κ.cut t₁ := by rw [hm_le _ le_rfl]; congr 1; dsimp only [τ]; ring
  have hml : m 0 = m 1 := hm0.trans hm1.symm
  have hmH : MapsTo m (Icc 0 1) H := by
    intro t ht
    rcases le_total t (1 / 2) with h | h
    · rw [hm_le t h]; exact κ.cut_mem_H hw hs (hsub (hτ t ⟨ht.1, h⟩))
    · rw [hm_ge t h]; exact (hPm ⟨by linarith, by linarith [ht.2]⟩).1
  have hmP : ∀ t ∈ Icc (1 / 2 : ℝ) 1, m t ∈ P '' Icc 0 1 := fun t ht =>
    ⟨2 * t - 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, (hm_ge t ht.1).symm⟩
  -- the chart crossing: `κ.loop` and `m` share `κ.cut '' [t₁, t₂]`
  have hAc : ∀ v ∉ κ.cut '' Icc t₁ t₂, QuantumZipper.CA.Topo.HasLogOn (fun z => z - v)
      (κ.cut '' Icc t₁ t₂) := fun v hv =>
    hasLogOn_sub_image_Icc (h10.trans h02) (κ.cont.mono (hsub.trans Ioo_subset_Icc_self))
      (hinj.mono hsub) hv
  have hγA : MapsTo κ.loop (Icc (t₁ / 2) (t₂ / 2)) (κ.cut '' Icc t₁ t₂) := fun t ht => by
    rw [κ.loop_of_le (by linarith [ht.2])]
    exact ⟨2 * t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  have hδA : MapsTo m (Icc 0 (1 / 2)) (κ.cut '' Icc t₁ t₂) := fun t ht => by
    rw [hm_le t ht.2]
    exact ⟨τ t, hτ t ht, rfl⟩
  have hp₁ : q ∉ κ.loop '' Icc 0 (t₁ / 2) ∪ κ.loop '' Icc (t₂ / 2) 1 ∪ m '' Icc 0 0 ∪
      m '' Icc (1 / 2) 1 := by
    rintro (((⟨t, ht, he⟩ | ⟨t, ht, he⟩) | ⟨t, ht, he⟩) | ⟨t, ht, he⟩)
    · have := κ.eq_of_loop_eq_cut hη hw hw0 hs ⟨ht.1, by linarith [ht.2]⟩ ht₀ he
      linarith [ht.2]
    · have := κ.eq_of_loop_eq_cut hη hw hw0 hs ⟨by linarith [ht.1], ht.2⟩ ht₀ he
      linarith [ht.1]
    · rw [Icc_self, mem_singleton_iff] at ht
      rw [ht, hm0] at he
      exact hbq he
    · obtain ⟨v, hv, hve⟩ := hmP t ht
      rw [← hve] at he
      exact (hPm hv).2 he
  obtain ⟨ε₁, hε₁, hcross₁⟩ := windNum_add_windNum_eq κ.continuousOn_loop hmc κ.loop_closed hml hAc
    (by linarith) (by linarith) (by linarith) le_rfl (by norm_num) (by norm_num) hγA hδA
    (by rw [κ.loop_of_le (by linarith), hmh]; congr 1; ring)
    (by rw [κ.loop_of_le (by linarith), hm0]; congr 1; ring) hp₁
  -- the physical crossing: the reference loop and `Ψ⁻¹ ∘ m` share a piece of the disc picture of `η`
  have hα := hη.isDiscCrosscut_toDisc
  set d₀ := discTime (κ.time t₀)
  set d₁ := discTime (κ.time t₁)
  set d₂ := discTime (κ.time t₂)
  have hd01 : d₁ < d₀ := discTime_lt (κ.time_pos hI₁).le (κ.time_strictMono hI₁ ht₀ h10)
  have hd02 : d₀ < d₂ := discTime_lt (κ.time_pos ht₀).le (κ.time_strictMono ht₀ hI₂ h02)
  have hd1 : 0 ≤ d₁ := (discTime_mem_Ico (κ.time_pos hI₁).le).1
  have hd2 : d₂ < 1 := (discTime_mem_Ico (κ.time_pos hI₂).le).2
  have hpq : discRevChart w s q = toDisc η d₀ := κ.discRevChart_cut hw hw0 hs ht₀
  have hAp : ∀ v ∉ toDisc η '' Icc d₁ d₂, QuantumZipper.CA.Topo.HasLogOn (fun z => z - v)
      (toDisc η '' Icc d₁ d₂) := fun v hv =>
    hasLogOn_sub_image_Icc (hd01.trans hd02) (hα.cont.mono (Icc_subset_Icc hd1 hd2.le))
      (hα.inj.mono (Icc_subset_Icc hd1 hd2.le)) hv
  have hRc := continuousOn_crossLoop hα.cont hα.one
  have hRl := crossLoop_loop hα.zero hα.one
  have hδc : ContinuousOn (discRevChart w s ∘ m) (Icc 0 1) :=
    (continuousOn_discRevChart hw hw0 hs).comp hmc hmH
  have hδl : (discRevChart w s ∘ m) 0 = (discRevChart w s ∘ m) 1 := congrArg (discRevChart w s) hml
  have hRA : MapsTo (flowReferenceLoop η) (Icc (d₁ / 2) (d₂ / 2)) (toDisc η '' Icc d₁ d₂) :=
    fun t ht => by
      change crossLoop (toDisc η) t ∈ _
      rw [crossLoop_of_le (by linarith [ht.2])]
      exact ⟨2 * t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  have hδA' : MapsTo (discRevChart w s ∘ m) (Icc 0 (1 / 2)) (toDisc η '' Icc d₁ d₂) := fun t ht => by
    have hτt := hτ t ht
    change discRevChart w s (m t) ∈ _
    rw [hm_le t ht.2, κ.discRevChart_cut hw hw0 hs (hsub hτt)]
    refine ⟨discTime (κ.time (τ t)), ⟨?_, ?_⟩, rfl⟩
    · rcases hτt.1.eq_or_lt with h | h
      · rw [← h]
      · exact discTime_le (κ.time_pos hI₁).le (κ.time_strictMono hI₁ (hsub hτt) h).le
    · rcases hτt.2.eq_or_lt with h | h
      · rw [h]
      · exact discTime_le (κ.time_pos (hsub hτt)).le (κ.time_strictMono (hsub hτt) hI₂ h).le
  have hp₂ : discRevChart w s q ∉ flowReferenceLoop η '' Icc 0 (d₁ / 2) ∪
      flowReferenceLoop η '' Icc (d₂ / 2) 1 ∪ (discRevChart w s ∘ m) '' Icc 0 0 ∪
      (discRevChart w s ∘ m) '' Icc (1 / 2) 1 := by
    have hd0I : d₀ ∈ Icc (0 : ℝ) 1 := ⟨hd1.trans hd01.le, (hd02.trans hd2).le⟩
    have hnorm : ‖toDisc η d₀‖ < 1 :=
      mem_ball_zero_iff.1 (hα.mem_disc d₀ ⟨hd1.trans_lt hd01, hd02.trans hd2⟩)
    rw [hpq]
    rintro (((⟨t, ht, he⟩ | ⟨t, ht, he⟩) | ⟨t, ht, he⟩) | ⟨t, ht, he⟩)
    · change crossLoop (toDisc η) t = _ at he
      rw [crossLoop_of_le (by linarith [ht.2])] at he
      have := hα.inj ⟨by linarith [ht.1], by linarith [ht.2]⟩ hd0I he
      linarith [ht.2]
    · change crossLoop (toDisc η) t = _ at he
      rcases le_total t (1 / 2) with h | h
      · rw [crossLoop_of_le h] at he
        have := hα.inj ⟨by linarith [ht.1], by linarith⟩ hd0I he
        linarith [ht.1]
      · have hs1 := (crossLoop_mem_semiArc hα.one ⟨h, ht.2⟩).1
        rw [he] at hs1
        linarith
    · rw [Icc_self, mem_singleton_iff] at ht
      rw [ht] at he
      change discRevChart w s (m 0) = _ at he
      rw [hm0, κ.discRevChart_cut hw hw0 hs hI₂] at he
      have := hα.inj ⟨hd1.trans (hd01.trans hd02).le, hd2.le⟩ hd0I he
      exact hd02.ne' this
    · obtain ⟨v, hv, hve⟩ := hmP t ht
      change discRevChart w s (m t) = _ at he
      rw [← hpq, ← hve] at he
      exact (hPm hv).2 (injOn_discRevChart hw hw0 hs (hPm hv).1 hqH he)
  obtain ⟨ε₂, hε₂, hcross₂⟩ := windNum_add_windNum_eq hRc hδc hRl hδl hAp
    (by linarith) (by linarith) (by linarith) le_rfl (by norm_num) (by norm_num) hRA hδA'
    (by
      change crossLoop (toDisc η) (d₁ / 2) = discRevChart w s (m (1 / 2))
      rw [crossLoop_of_le (by linarith), hmh, κ.discRevChart_cut hw hw0 hs hI₁]
      congr 1; ring)
    (by
      change crossLoop (toDisc η) (d₂ / 2) = discRevChart w s (m 0)
      rw [crossLoop_of_le (by linarith), hm0, κ.discRevChart_cut hw hw0 hs hI₂]
      congr 1; ring) hp₂
  -- the radius
  obtain ⟨ρ₁, hρ₁, hρ₁c⟩ := Metric.continuousOn_iff.1 (continuousOn_discRevChart hw hw0 hs) q hqH ε₂ hε₂
  have hPK : IsClosed (P '' Icc 0 1) := (isCompact_Icc.image hPc).isClosed
  have hqP : q ∉ P '' Icc 0 1 := fun ⟨v, hv, hve⟩ => (hPm hv).2 hve
  obtain ⟨ρ₂, hρ₂, hρ₂P⟩ := exists_ball_disjoint hPK hqP
  refine ⟨min ε₁ (min ρ₁ ρ₂), lt_min hε₁ (lt_min hρ₁ hρ₂), ?_⟩
  -- the facts used at each point
  have hpoint : ∀ z ∈ ball q (min ε₁ (min ρ₁ ρ₂)), z ∈ H → z ∉ chartFlowSet η w s →
      z ∈ ball q ε₁ ∧ z ∉ κ.cut '' Icc t₁ t₂ ∧ discRevChart w s z ∈ ball (discRevChart w s q) ε₂ ∧
        discRevChart w s z ∉ toDisc η '' Icc d₁ d₂ ∧
          windNum (discRevChart w s ∘ m) (discRevChart w s z) = windNum m z := by
    intro z hz hzH hzA
    have hz₁ : dist z q < ε₁ := (mem_ball.1 hz).trans_le (min_le_left _ _)
    have hz₂ : dist z q < ρ₁ := (mem_ball.1 hz).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hz₃ : dist z q < ρ₂ := (mem_ball.1 hz).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hzcut : z ∉ κ.cut '' Icc t₁ t₂ := by
      rintro ⟨t, ht, rfl⟩
      exact hzA (κ.cut_mem_chartFlowSet (hsub ht))
    have hzm : ∀ t ∈ Icc (0 : ℝ) 1, m t ≠ z := by
      intro t ht he
      rcases le_total t (1 / 2) with h | h
      · exact hzcut (he ▸ hδA ⟨ht.1, h⟩)
      · have := hρ₂P _ (hmP t ⟨h, ht.2⟩)
        rw [he, ← dist_eq_norm] at this
        linarith
    refine ⟨hz₁, hzcut, hρ₁c z hzH hz₂, fun h => ?_,
      windNum_discRevChart hw hw0 hs hmc hml hmH hzH hzm⟩
    obtain ⟨d, hd, hde⟩ := h
    exact discRevChart_notMem_crossRange hw hw0 hs hη hzH hzA
      ⟨d, Icc_subset_Icc hd1 hd2.le hd, hde⟩
  intro z hz z' hz' hzH hz'H hzA hz'A
  obtain ⟨hz₁, hzc, hzp, hzp', hzw⟩ := hpoint z hz hzH hzA
  obtain ⟨hz'₁, hz'c, hz'p, hz'p', hz'w⟩ := hpoint z' hz' hz'H hz'A
  have e₁ := hcross₁ z hz₁ z' hz'₁ hzc hz'c
  have e₂ : windNum (flowReferenceLoop η) (discRevChart w s z) +
      windNum (discRevChart w s ∘ m) (discRevChart w s z) =
      windNum (flowReferenceLoop η) (discRevChart w s z') +
      windNum (discRevChart w s ∘ m) (discRevChart w s z') := hcross₂ _ hzp _ hz'p hzp' hz'p'
  rw [hzw, hz'w] at e₂
  omega

end ExcursionChartCut

end InteractingSLE.Sec5.Prop51HGate
