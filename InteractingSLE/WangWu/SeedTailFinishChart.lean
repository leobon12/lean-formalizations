/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailAssembly

/-!
# The deterministic terminal chart problem

PROVE-WW-B27 continuation. Bounded killed arcs have finite positive terminal
capacity. The two remaining geometric inputs below separate positive boundary
landing in the reverse slit chart from collision at that landing.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedTail

open ImgWord LawUnique Sec7.Lemma71C

/-- A bounded killed arc has finite positive terminal capacity. -/
theorem exists_finite_kLife_of_isBounded {γ : ℝ → ℂ} {P : Set ℝ}
    (hγ : IsKilledArc γ P) (hb : IsBounded (γ '' P)) :
    ∃ τ : ℝ≥0, 0 < τ ∧ (τ : WithTop ℝ≥0) = kLife γ P := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hcap : ∀ S ∈ P, capClock γ S ≤ R ^ 2 / 2 := by
    intro S hS
    obtain ⟨S', hS', hSS'⟩ := hγ.exists_gt S hS
    obtain ⟨w, hw, hw0, -, -, -, hK⟩ :=
      hγ.exists_localDriver hS' ((hγ.nonneg S hS).trans_lt hSS')
    have hKS := hK S ⟨hγ.nonneg S hS, hSS'.le⟩
    have hbound : fwdHull w (capClock γ S) ⊆ closedBall (0 : ℂ) R := by
      rw [hKS.2]
      rintro _ ⟨u, hu, rfl⟩
      exact hR ⟨u, hγ.icc S hS ⟨hu.1.le, hu.2⟩, rfl⟩
    have h := HPHull.hcap_le_rad_sq ⟨_, isHPHull_fwdHull hw hKS.1⟩ hbound
    rw [hcap_fwdHull hw hw0 hKS.1] at h
    linarith only [h]
  have hL : kLife γ P ≤ (((R ^ 2 / 2).toNNReal : ℝ≥0) : WithTop ℝ≥0) := by
    exact iSup_le fun S => iSup_le fun hS => WithTop.coe_le_coe.2 (Real.toNNReal_mono (hcap S hS))
  have hne : kLife γ P ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hL
  lift kLife γ P to ℝ≥0 using hne with τ hτ
  refine ⟨τ, ?_, rfl⟩
  have hp := hγ.zero_lt_kLife
  rw [← hτ] at hp
  exact_mod_cast hp

/-- A real limit of points on the right side of a proper arc is nonnegative. -/
theorem nonneg_of_tendsto_rightSideOf {ι : Type*} {l : Filter ι} [l.NeBot]
    {γ : ℝ → ℂ} (hγ : IsProperArc γ) {f : ι → ℂ} {x : ℝ}
    (hf : Tendsto f l (𝓝 (x : ℂ))) (hr : ∀ᶠ i in l, f i ∈ rightSideOf (arcRange γ)) :
    0 ≤ x :=
  not_lt.1 fun hx => hγ.notMem_closure_rightSideOf_of_neg hx (mem_closure_of_tendsto hf hr)

/-- An unbounded chart limit at an actual first-contact point forces that point
to be the reverse tip. No continuation of the image driver is assumed. -/
theorem eq_revTip_of_chart_tendsto_atTop {w : ℝ → ℝ} {η α : ℝ → ℂ} {s T : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η)
    (hs : 0 ≤ s) (hηs : η s ≠ 0) (hα : IsProperArc α) (hT : 0 < T)
    (hmem : ∀ᶠ t in 𝓝[<] T, α t ∈ H \ negInv '' fwdHull w s)
    (hinf : Tendsto (fun t => ‖revChart w s (α t)‖) (𝓝[<] T) atTop) :
    α T = negInv (η s) := by
  have hlim := tendsto_revChartInv_tip hη hw hw0 hs hηs
    (hmem.mono fun t ht => revChart_mem_H hw hs ht) hinf
  have hback : Tendsto α (𝓝[<] T) (𝓝 (negInv (η s))) := by
    refine hlim.congr' ?_
    filter_upwards [hmem] with t ht
    exact revChartInv_revChart hw hw0 hs ht
  exact tendsto_nhds_unique
    (((hα.cont.continuousAt (Ici_mem_nhds hT)).tendsto).mono_left nhdsWithin_le_nhds) hback

/-- The remaining slit-side boundary correspondence. A forbidden right first
contact, or a right escape, gives a bounded image arc landing on the positive
real axis at the end of its capacity parametrization. This is a named input,
not a theorem or an additional premise on a source declaration. -/
def SlitRightLandingStatement : Prop :=
  ∀ {w : ℝ → ℝ} {η α β : ℝ → ℂ} {s a : ℝ},
    Continuous w → w 0 = 0 → IsLoewnerTrace w η → IsProperArc η →
    IsProperArc α → IsProperArc β → 0 < s → 0 < a →
    negInv '' fwdHull w s = β '' Ici a → negInv (η s) = β a →
    ¬ (Descent.NoRightFirstContact α β a ∧ Descent.NoRightEscape α β a) →
    let γ := imgCurve w s α
    let P := preContact α (negInv '' fwdHull w s)
    IsBounded (γ '' P) ∧ ∃ x : ℝ, 0 < x ∧
      Tendsto (kTrace γ P) (𝓝[<] ENNReal.toNNReal (kLife γ P)) (𝓝 (x : ℂ))

/-- The remaining endpoint collision theorem for a killed simple arc. The
driver is continuous only before the terminal time; no extension through that
time is available in `IsKilledArc`. -/
def PositiveLandingGapStatement : Prop :=
  ∀ {γ : ℝ → ℂ} {P : Set ℝ}, IsKilledArc γ P →
    ∀ {τ : ℝ≥0}, 0 < τ → (τ : WithTop ℝ≥0) = kLife γ P →
    ∀ {x : ℝ}, 0 < x → Tendsto (kTrace γ P) (𝓝[<] τ) (𝓝 (x : ℂ)) →
      Tendsto (fun t => kImg (kPath γ P) 0 t - kW γ P t) (𝓝[<] τ) (𝓝 0)

/-- The chart translation from the two explicit endpoint inputs. All capacity
finiteness and the transfer to the first right force mark are proved here. -/
theorem tailChartStatement_of_landing (hSide : SlitRightLandingStatement)
    (hGap : PositiveLandingGapStatement) : TailChartStatement.{u} := by
  intro Ω s ζ W E p β a hs hβ hg hp ha htail htip hsafe
  by_contra hbad
  obtain ⟨hw, hw0, hη, hηp, hhull, -, -⟩ := trace_of_mem_betaSet hs hg.2.1
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have htail' : negInv '' fwdHull (Ito.rpath (frzDrive s p.2)) s = β '' Ici a := by
    rw [← hhull]
    exact htail
  have htip' : negInv (frzLine s p.2 s) = β a := by
    have he := hg.2.1.1.1.2 s hs.le le_rfl
    simpa only [revLine, he] using htip
  obtain ⟨hb, x, hx, hlim⟩ := hSide hw hw0 hη hηp hg.1 hβ hs' ha htail' htip' hbad
  have hG : IsClosed (negInv '' fwdHull (Ito.rpath (frzDrive s p.2)) s) := by
    rw [← hhull]
    exact isClosed_image_negInv_histHull hs hg.2.2
  have hK := isKilledArc_imgCurve hw hw0 hs'.le hG hg.1
  obtain ⟨τ, hτ, hτL⟩ := exists_finite_kLife_of_isBounded hK hb
  have hlim' : Tendsto (kTrace (imgCurve (Ito.rpath (frzDrive s p.2)) s
      (seedLine ζ W p.1)) (preContact (seedLine ζ W p.1)
        (negInv '' fwdHull (Ito.rpath (frzDrive s p.2)) s)))
      (𝓝[<] τ) (𝓝 (x : ℂ)) := by
    have he : (τ : ℝ≥0∞) = (kLife (imgCurve (Ito.rpath (frzDrive s p.2)) s
        (seedLine ζ W p.1)) (preContact (seedLine ζ W p.1)
          (negInv '' fwdHull (Ito.rpath (frzDrive s p.2)) s)) : ℝ≥0∞) := by exact_mod_cast hτL
    simpa only [← he, ENNReal.toNNReal_coe] using hlim
  have hzero := hGap hK hτ hτL hx hlim'
  have hτimg : (τ : WithTop ℝ≥0) = imgT s ζ W E p := by
    simpa only [imgT, gCurve_of_mem hp, gPre_of_mem hp, hhull] using hτL
  apply hsafe τ hτ (by exact_mod_cast hτimg) 0
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htL : (t : WithTop ℝ≥0) < kLife (gCurve s ζ W E p) (gPre s ζ W E p) := by
    change (t : WithTop ℝ≥0) < imgT s ζ W E p
    rw [← hτimg]
    exact_mod_cast ht
  rw [imgVR, imgW, kVR_of_lt _ _ htL]
  simp only [kVRr, gXR, Matrix.cons_val_zero, gCurve_of_mem hp, gPre_of_mem hp, hhull]

end InteractingSLE.WangWu.SeedTail
