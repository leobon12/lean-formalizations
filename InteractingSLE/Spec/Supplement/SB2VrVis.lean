/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VrRad
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Spec.Sec5.CrossRestartTrace
import InteractingSLE.Spec.Sec7.TwoForcePocket
import InteractingSLE.WangWu.CouplingRetained
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalHull

/-!
# Bad real points are never visited before the lifetime (D10 step 3's deterministic core)

Packet PROVE-AUX61-NOJUMP (decision D10, step 3).

* **`trace_ne_of_mem_closure_hull`** (topology of Loewner traces): a real point swallowed at time `s` without being
  touched by the trace up to `s` is never the tip at a later time before the horizon. Otherwise the trace would stay
  near the point, inside the hull, for a while, and the hull would not grow, against `hcap K_t = 2t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Theorem14.SB.Vr

/-- **A point swallowed untouched is never the tip later.** If `p` lies in the closure of the hull at `s` but not on
the trace up to `s`, then the trace is not at `p` at any time in `[s, T)`. -/
theorem trace_ne_of_mem_closure_hull {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTraceLT U T η) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t < T) {p : ℂ}
    (hpA : p ∉ η '' Icc 0 s) (hpK : p ∈ closure (fwdHull U s)) : η t ≠ p := by
  intro htp
  have hsT : s < T := lt_of_le_of_lt hst htT
  have hcont : ∀ r, r < T → ContinuousOn η (Icc 0 r) := fun r hr =>
    hη.2.1.mono fun q hq => ⟨hq.1, lt_of_le_of_lt hq.2 hr⟩
  have hAc : ∀ r, r < T → IsCompact (η '' Icc 0 r) := fun r hr =>
    isCompact_Icc.image_of_continuousOn (hcont r hr)
  have hfill : ∀ r, 0 ≤ r → r < T → IsFilling (fwdHull U r) (η '' Icc 0 r) := fun r hr0 hr => by
    rw [hη.2.2 r hr0 hr]; exact isFilling_fillH (hAc r hr)
  -- a ball around `p` missing the trace up to `s`
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ z ∈ ball p δ, z ∉ η '' Icc 0 s := by
    have ho : IsOpen (η '' Icc 0 s)ᶜ := (hAc s hsT).isClosed.isOpen_compl
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1 ho p hpA
    exact ⟨δ, hδ, fun z hz => hsub hz⟩
  -- the upper half of the ball lies in the hull at `s`
  have hsub : ball p δ ∩ H ⊆ fwdHull U s := by
    intro z hz
    by_contra hzK
    obtain ⟨w, hwK, hwd⟩ := Metric.mem_closure_iff.1 hpK δ hδ
    have hwH : w ∈ H := Exist.fwdHull_subset_H hs hwK
    have hPA : ball p δ ∩ H ⊆ H \ η '' Icc 0 s := fun v hv => ⟨hv.2, hball v hv.1⟩
    exact Sec7.notMem_of_isFilling_of_isPreconnected (hfill s hs hsT) (HalfPlaneSep.isPreconnected_ball_inter_H p δ)
      hPA hz ⟨mem_ball'.2 hwd, hwH⟩ hzK hwK
  have hst' : s < t := lt_of_le_of_ne hst fun h => hpA ⟨t, ⟨hs.trans hst, h.ge⟩, htp⟩
  -- near `t` the trace stays in the ball
  have hca : ContinuousAt η t := hη.2.1.continuousAt (Ico_mem_nhds (by linarith) htT)
  obtain ⟨ε, hε, hεb⟩ := Metric.continuousAt_iff.1 hca δ hδ
  set e : ℝ := min (ε / 2) (min ((t - s) / 2) ((T - t) / 2)) with he
  have he0 : 0 < e := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have he1 : e ≤ ε / 2 := min_le_left _ _
  have he2 : e ≤ (t - s) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : e ≤ (T - t) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set t₁ := t - e with ht₁
  set t₂ := t + e with ht₂
  have ht₁0 : 0 ≤ t₁ := by linarith
  have hst₁ : s ≤ t₁ := by linarith
  have ht₂0 : 0 ≤ t₂ := by linarith
  have ht₁T : t₁ < T := by linarith
  have ht₂T : t₂ < T := by linarith
  have hnear : ∀ r ∈ Icc t₁ t₂, η r ∈ ball p δ := fun r hr => by
    have h1 : dist r t < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2]
    have h2 := hεb h1
    rw [htp] at h2
    exact h2
  -- the outside of the hull at `t₁` misses the trace up to `t₂`
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

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

open MartChar.RealFlow in
/-- **At the first visit of a real point `p > 0`, the colliding right marks are those `≤ p`** (deterministic). Let `S`
be the last collision of the zero mark at or before the visit `t₀`. Either `S = t₀`, or `p` was alive at `S`
(otherwise it was swallowed untouched, `trace_ne_of_mem_closure_hull`) and the zero mark collides again at `t₀`
(`Vo.rightImg_zero_eq_at_later_real_tip`). -/
theorem rightImg_eq_iff_at_first_visit_pt {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTraceLT U T η) {t₀ : ℝ} (ht₀r : 0 < t₀) (ht₀t' : t₀ < T) {p : ℝ} (hp0 : 0 < p)
    (hη't₀ : η t₀ = p) (hmin : ∀ r ∈ Ico 0 t₀, η r ≠ p) (z : ℝ) : rightImg U z t₀ = U t₀ ↔ z ≤ p := by
  have hηt₀ : IsLoewnerTraceLT U t₀ η := Vo.isLoewnerTraceLT_mono hη ht₀t'.le
  have hc : ContinuousOn η (Icc 0 t₀) := hη.2.1.mono fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht₀t'⟩
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hηt₀ hU hU0 ht₀r hc
  have htip : extendFrom H (QuantumZipper.fwdMapInv U t₀) 0 = (p : ℂ) := by
    rw [TraceClose.extendFrom_zero_eq hηt₀ hU hU0 ht₀r hc, hη't₀]
  have hlim : Tendsto (QuantumZipper.fwdMapInv U t₀) (𝓝[H] 0) (𝓝 (p : ℂ)) := by
    rw [← htip]
    exact hB.tendsto (show (0 : ℂ) ∈ QuantumZipper.Hbar by simp [QuantumZipper.Hbar])
  -- the last collision of the zero mark at or before `t₀`
  set C : Set ℝ := {r | r ∈ Icc 0 t₀ ∧ rightImg U 0 r = U r} with hCdef
  have hCc : IsClosed C := by
    have hf : ContinuousOn (fun r => rightImg U 0 r - U r) (Icc 0 t₀) :=
      ((continuousOn_rightImg hU 0).mono fun r hr => hr.1).sub hU.continuousOn
    have h := hf.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := (0 : ℝ)))
    convert h using 1
    ext r
    simp only [hCdef, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, sub_eq_zero]
  have h0C : (0 : ℝ) ∈ C := ⟨⟨le_rfl, ht₀r.le⟩, by rw [rightImg_zero hU hU0 le_rfl, hU0]⟩
  have hCb : BddAbove C := ⟨t₀, fun r hr => hr.1.2⟩
  set S := sSup C with hSdef
  have hSC : S ∈ C := hCc.csSup_mem ⟨0, h0C⟩ hCb
  have hzero : rightImg U 0 t₀ = U t₀ := by
    rcases eq_or_lt_of_le hSC.1.2 with hSt | hSt
    · rw [← hSt]; exact hSC.2
    · have hS0 : 0 ≤ S := hSC.1.1
      have hsep : ∀ r ∈ Ioo S t₀, U r < rightImg U 0 r := fun r hr =>
        lt_of_le_of_ne (le_rightImg hU 0 (hS0.trans hr.1.le)) fun h =>
          not_le.2 hr.1 (le_csSup hCb ⟨⟨hS0.trans hr.1.le, hr.2.le⟩, h.symm⟩)
      have halive : Alive U p S := by
        by_contra hdead
        have hpK : (p : ℂ) ∈ closure (fwdHull U S) := by
          by_contra hnot
          obtain ⟨v, hv⟩ := RLC.G8Det.alive_of_notMem_closure hU (by rw [hU0]; exact hp0.ne') hS0 hnot
          exact hdead (Sec7.Lemma76E.alive_of_isForwardSol hU hS0 (by rw [hU0]; exact hp0) hv)
        have hpA : (p : ℂ) ∉ η '' Icc 0 S := by
          rintro ⟨r, hr, hrp⟩
          exact hmin r ⟨hr.1, lt_of_le_of_lt hr.2 hSt⟩ hrp
        exact trace_ne_of_mem_closure_hull hU hU0 hη hS0 hSt.le ht₀t' hpA hpK hη't₀
      exact Vo.rightImg_zero_eq_at_later_real_tip hU hU0 hS0 hSt hSC.2 hsep hlim hp0 le_rfl halive
  have := Restart.FlowStopIdentLL.rightImg_eq_iff_of_zero_collision hU hU0 ht₀r.le hB htip hzero z
  simpa using this

open MartChar.RealFlow in
/-- **Bad points are never visited before the lifetime** (deterministic). For an integrated SLE path with a
generating trace, a nonzero bad point (real, outward cumulative weight `≤ −2`) is not the tip at any time before `ζ`:
at the first visit the colliding marks on that side are those between the start and the point
(`rightImg_eq_iff_at_first_visit_pt`, reflected on the left), of weight `≤ −2`, a threshold before `ζ`. -/
theorem trace_ne_of_bad {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {β : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR β ζ)
    (hgen : IsGeneratingTrace w ζ γ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {z : ℂ}
    (hz : Vq.IsBadPoint xL xR ρL ρR z) (hz0 : z ≠ 0) : γ t ≠ z := by
  intro hγt
  set p : ℝ := z.re with hpdef
  have hzp : z = (p : ℂ) := Complex.ext (by simp [hpdef]) (by simp [hz.1])
  have hp0 : p ≠ 0 := fun h => hz0 (by rw [hzp, h, Complex.ofReal_zero])
  rw [hzp] at hγt
  have hp' := hp
  obtain ⟨hw0, -, -, hwc, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt, -⟩ := hp'
  -- the first visit
  set Z : Set ℝ≥0 := {s | s ≤ t ∧ γ s = p} with hZ
  have hZc : IsClosed Z := by
    have hco : ContinuousOn γ (Iic t) := hgen.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs).trans ht.le
    have h := hco.preimage_isClosed_of_isClosed isClosed_Iic (isClosed_singleton (x := (p : ℂ)))
    convert h using 1
    ext s
    simp only [hZ, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Iic, Set.mem_preimage, Set.mem_singleton_iff]
  have hZne : Z.Nonempty := ⟨t, le_rfl, hγt⟩
  set t₀ := sInf Z with ht₀def
  have ht₀Z : t₀ ∈ Z := hZc.csInf_mem hZne (OrderBot.bddBelow Z)
  have hmin : ∀ s < t₀, γ s ≠ p := fun s hs heq =>
    not_le.2 hs (csInf_le (OrderBot.bddBelow Z) ⟨hs.le.trans ht₀Z.1, heq⟩)
  have ht₀pos : 0 < t₀ := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have := ht₀Z.2
    rw [h0, hgen.1] at this
    exact hp0 (by exact_mod_cast (congrArg Complex.re this).symm)
  -- a horizon beyond `t`, the frozen driver and its trace
  obtain ⟨t', htt', ht'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt'' : t < t' := by exact_mod_cast htt'
  have ht'ofReal : ENNReal.ofReal (t' : ℝ) < ζ := by rw [ENNReal.ofReal_coe_nnreal]; exact ht'ζ
  set U : ℝ → ℝ := frozenDrive w t' with hUdef
  have hU : Continuous U := continuous_frozenDrive_of_lt hwc ht'ofReal
  have hU0 : U 0 = 0 := by simp [hUdef, frozenDrive, hw0]
  set η' : ℝ → ℂ := fun s => γ s.toNNReal with hη'def
  have heqU : EqOn U (fun s : ℝ => w s.toNNReal) (Icc 0 (t' : ℝ)) := fun s hs => by
    simp only [hUdef, frozenDrive, min_eq_left hs.2]
  have hη0 := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (hgen.mono_horizon ht'ζ.le)
  have hη : IsLoewnerTraceLT U t' η' :=
    ⟨hη0.1, hη0.2.1, fun r hr hrt => (LocalExt.fwdHull_congr_of_eqOn_of_lt hr hrt heqU).trans (hη0.2.2 r hr hrt)⟩
  have ht₀t' : (t₀ : ℝ) < t' := by exact_mod_cast lt_of_le_of_lt ht₀Z.1 htt''
  have ht₀r : (0 : ℝ) < t₀ := by exact_mod_cast ht₀pos
  have hη't₀ : η' t₀ = p := by simp only [hη'def, Real.toNNReal_coe]; exact ht₀Z.2
  have hmin' : ∀ r ∈ Ico (0 : ℝ) t₀, η' r ≠ p := fun r hr => hmin _ (by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)
  have hwU : w t₀ = U t₀ := by simp only [hUdef, frozenDrive, min_eq_left ht₀t'.le, Real.toNNReal_coe]
  refine hnt t₀ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₀Z.1) ht) ?_
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · -- a left bad point, by reflection
    have hbad : Vq.wL xL ρL p ≤ -2 := by
      rcases hz.2 with h | h
      · exact absurd h.1 (not_le.2 hneg)
      · exact h.2
    have hηr := Vo.isLoewnerTraceLT_reflect hη
    have hnU : Continuous (-U) := hU.neg
    have hnU0 : (-U) 0 = 0 := by simp [hU0]
    have hrt₀ : LP.reflectC (η' t₀) = ((-p : ℝ) : ℂ) := by
      rw [hη't₀]; apply Complex.ext <;> simp [LP.reflectC]
    have hrmin : ∀ r ∈ Ico (0 : ℝ) t₀, LP.reflectC (η' r) ≠ ((-p : ℝ) : ℂ) := fun r hr h => by
      apply hmin' r hr
      rw [← LP.reflectC_reflectC (η' r), h]; apply Complex.ext <;> simp [LP.reflectC]
    have hcol := rightImg_eq_iff_at_first_visit_pt hnU hnU0 hηr ht₀r ht₀t' (by linarith) hrt₀ hrmin
    have hvL : ∀ i, vL i t₀ = -rightImg (-U) (-xL i) t₀ := fun i =>
      Sec7.SideHeight.vL_eq_neg_rightImg_frozenDrive hp ht'ofReal ht₀t'.le i
    left
    have hf : univ.filter (fun i => vL i t₀ = w t₀) = univ.filter (fun i => p ≤ xL i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hvL, hwU]
      have := hcol (-xL i)
      simp only [Pi.neg_apply] at this
      constructor
      · intro h; have := this.1 (by linarith); linarith
      · intro h; have := this.2 (by linarith); linarith
    rw [hf]
    exact hbad
  · have hbad : Vq.wR xR ρR p ≤ -2 := by
      rcases hz.2 with h | h
      · exact h.2
      · exact absurd h.1 (not_le.2 hpos)
    have hcol := rightImg_eq_iff_at_first_visit_pt hU hU0 hη ht₀r ht₀t' hpos hη't₀ hmin'
    have hvR : ∀ j, vR j t₀ = rightImg U (xR j) t₀ := fun j =>
      Sec7.SideHeight.vR_eq_rightImg_frozenDrive hp ht'ofReal ht₀t'.le j
    right
    have hf : univ.filter (fun j => vR j t₀ = w t₀) = univ.filter (fun j => xR j ≤ p) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hvR, hwU, hcol]
    rw [hf]
    exact hbad

end InteractingSLE.Theorem14.SB.Vr
