/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailLandingBoundary

/-!
# The slit landing from the precise planar side transport

PROVE-WW-B27. Finite contact and infinite escape give finite nonzero real chart
limits by the proved fibre lemma. Transport to the right of a proper mapped
initial arc determines their positive sign. This file isolates that planar
transport, discharged in `SeedTailLandingTransport`; boundedness and all
capacity-limit assertions are proved here.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex Bornology
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedTail

open ImgWord

/-- The planar transport interface: transport the right component of a proper arc
whose reversed tail is the frozen slit to the right of a proper arc in its chart.
No trace, capacity, stochastic, or landing assertion is included in the conclusion. -/
def ReversedTailSideTransportStatement : Prop :=
  ∀ {w : ℝ → ℝ} {η β : ℝ → ℂ} {s a : ℝ},
    Continuous w → w 0 = 0 → IsLoewnerTrace w η → IsProperArc η → IsProperArc β →
    0 < s → 0 < a → negInv '' fwdHull w s = β '' Ici a → negInv (η s) = β a →
    ∃ χ : ℝ → ℂ, IsProperArc χ ∧
      MapsTo (revChart w s) (rightSideOf (arcRange β)) (rightSideOf (arcRange χ))

/-- The pre-contact order filter at a first contact is the left-neighbourhood filter. -/
theorem preContact_eq_Ico_of_first {α : ℝ → ℂ} {G : Set ℂ} {T : ℝ}
    (hT : 0 < T) (hhit : α T ∈ G) (havoid : ∀ t ∈ Ico 0 T, α t ∉ G) :
    preContact α G = Ico 0 T := by
  ext t
  constructor
  · intro ht
    refine ⟨ht.1, lt_of_not_ge fun hTt => ht.2 T ⟨hT.le, hTt⟩ hhit⟩
  · intro ht
    exact ⟨ht.1, fun u hu => havoid u ⟨hu.1, hu.2.trans_lt ht.2⟩⟩

/-- The analytic and capacity parts of the slit landing, with only the planar
side transport left as an input. -/
theorem slitRightLandingStatement_of_sideTransport (hSide : ReversedTailSideTransportStatement) :
    SlitRightLandingStatement := by
  intro w η α β s a hw hw0 hη hηp hα hβ hs ha htail htip hbad
  let P := preContact α (negInv '' fwdHull w s)
  let γ := imgCurve w s α
  have hG : IsClosed (negInv '' fwdHull w s) := by
    rw [htail]
    exact Descent.isClosed_image_Ici hβ ha.le
  have hK : IsKilledArc γ P := isKilledArc_imgCurve hw hw0 hs.le hG hα
  have : (arcEnd P).NeBot := arcEnd_neBot hK
  have hraw : ∃ x : ℝ, x ≠ 0 ∧ Tendsto γ (arcEnd P) (𝓝 (x : ℂ)) ∧
      ∀ᶠ u in arcEnd P, α u ∈ rightSideOf (arcRange β) := by
    rcases not_and_or.1 hbad with hcontact | hescape
    · unfold Descent.NoRightFirstContact at hcontact
      push Not at hcontact
      obtain ⟨T, hT, hhit, havoid, ε, hε, hR⟩ := hcontact
      have hhit' : α T ∈ β '' Ici a := (image_mono Ioi_subset_Ici_self) hhit
      have hP : P = Ico 0 T := preContact_eq_Ico_of_first hT (htail ▸ hhit')
        (fun t ht => htail ▸ havoid t ht)
      have hEnd : arcEnd P = 𝓝[<] T := by rw [hP, arcEnd_Ico hT]
      have htipne : α T ≠ β a := by
        intro he
        obtain ⟨b, hb, hbT⟩ := hhit
        have h := hβ.inj (ha.le.trans hb.le) ha.le (hbT.trans he)
        exact hb.ne' h
      have hyK : negInv (α T) ∈ fwdHull w s := by
        obtain ⟨z, hz, hze⟩ := (show α T ∈ negInv '' fwdHull w s from htail ▸ hhit')
        rw [← hze, negInv_negInv]
        exact hz
      have hytip : negInv (α T) ≠ η s := by
        intro he
        apply htipne
        rw [← negInv_negInv (α T), he, htip]
      have hInv : Tendsto (fun u => negInv (α u)) (arcEnd P) (𝓝 (negInv (α T))) := by
        rw [hEnd]
        exact ((continuousAt_negInv (ne_zero_of_mem_H (hα.mem_H T hT))).tendsto.comp
          ((hα.cont.continuousAt (Ici_mem_nhds hT)).tendsto)).mono_left nhdsWithin_le_nhds
      obtain ⟨x, hx, hlim⟩ := exists_real_chart_limit hw hw0 hη hs.le hα hK
        (fun hy => hy.2 hyK) hytip hInv
      refine ⟨x, hx, hlim, ?_⟩
      rw [hEnd]
      filter_upwards [Ioo_mem_nhdsLT (sub_lt_self T hε)] with u hu
      exact hR u hu
    · change ¬ ((∀ t, 0 ≤ t → α t ∉ β '' Ici a) →
        ∃ᶠ t in atTop, α t ∉ rightSideOf (arcRange β)) at hescape
      obtain ⟨havoid, hNR⟩ := not_imp.1 hescape
      have hP : P = Ici 0 := by
        ext t
        exact ⟨fun ht => ht.1, fun ht => ⟨ht, fun u hu => htail ▸ havoid u hu.1⟩⟩
      have hEnd : arcEnd P = atTop := by rw [hP, arcEnd_Ici]
      have hInv : Tendsto (fun u => negInv (α u)) (arcEnd P) (𝓝 0) := by
        rw [hEnd]
        have hαinf : Tendsto α atTop (cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.1 hα.tendsto
        simpa only [negInv, Function.comp_def, neg_zero] using (tendsto_inv₀_cobounded.comp hαinf).neg
      have hy : (0 : ℂ) ∉ H \ fwdHull w s := fun h => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h.1)
      obtain ⟨x, hx, hlim⟩ := exists_real_chart_limit hw hw0 hη hs.le hα hK hy
        (Ne.symm (ne_zero_of_mem_H (hηp.mem_H s hs))) hInv
      refine ⟨x, hx, hlim, ?_⟩
      rw [hEnd]
      simpa only [not_not] using not_frequently.1 hNR
  obtain ⟨x, hx, hlim, hRight⟩ := hraw
  obtain ⟨χ, hχ, hmap⟩ := hSide hw hw0 hη hηp hβ hs ha htail htip
  have hR : ∀ᶠ u in arcEnd P, γ u ∈ rightSideOf (arcRange χ) := by
    obtain ⟨S, hS, -, -, hSP⟩ := arcEnd_connected_basis hK (Filter.univ_mem : univ ∈ arcEnd P)
    filter_upwards [hRight, hS] with u hu huS
    rw [show γ u = revChart w s (α u) from imgCurve_of_pos (hSP huS).2]
    exact hmap hu
  have hxpos : 0 < x := lt_of_le_of_ne (nonneg_of_tendsto_rightSideOf hχ hlim hR) (Ne.symm hx)
  have hb := isBounded_image_of_arcEnd_limit hK hlim
  obtain ⟨τ, -, hτ, hcap⟩ := exists_kTrace_limit_of_arcEnd_limit hK hlim
  refine ⟨hb, x, hxpos, ?_⟩
  change Tendsto (kTrace γ P) (𝓝[<] ENNReal.toNNReal (kLife γ P)) (𝓝 (x : ℂ))
  have he : (τ : ℝ≥0∞) = (kLife γ P : ℝ≥0∞) := by exact_mod_cast hτ
  simpa only [← he, ENNReal.toNNReal_coe] using hcap

end InteractingSLE.WangWu.SeedTail
