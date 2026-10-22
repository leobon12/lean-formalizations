import HigherDimLQGMetric.Thm13.Stable
import HigherDimLQGMetric.Sec6.Defs
import HigherDimLQGMetric.Determ.CopyTight
import HigherDimLQGMetric.Limits.RemarkBounded

/-! Axiom V for bounded continuous perturbations, using L6f and the
varying-law comparison of L6c Remark 3.8(b). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l8_stable_normalized_of_good
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hN : L8NormalizedGood hd hκ ξ εs hεs)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsNormalizedLGF h P) :
    StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n)
      (fun ω => (l8_patch hd hκ ξ εs hεs (h ω)).1) := by
  have hXm (n : ℕ) : AEMeasurable
      (fun ω => lfppSeq κ ξ εs (h ω) n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  exact l8_stablyTendstoLU_of_ae P h hh.1.measurable _ _ hXm
    (measurable_subtype_coe.comp
      ((l8_measurable_patch hd hκ ξ εs hεs).comp hh.1.measurable))
    (hN P h hh).2.1

theorem l8_canonical_scales_of_stable
    (hL6f : ∀ d ξ κ, L6f_tightScales d ξ κ)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (_hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (D : DistRd d → ContMetric d) (hDm : Measurable D)
    (hstable : StablyTendstoLU (normLGFLaw d) id
      (fun n g => lfppSeq κ ξ εs g n) (fun g => (D g).1)) :
    ∃ c : ℝ → ℝ, (∀ r, 0 < r → 0 < c r) ∧
      TightFamily (normLGFLaw d)
        (fun r g => normalizedAtScale ξ D c g r) (Ioi 0) := by
  letI : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d hd).1
  have hh : IsNormalizedLGF id (normLGFLaw d) :=
    (normLGFLaw_spec_holds d hd).2.1
  let c : ℝ → ℝ := fun r => lowerMedian (normLGFLaw d) (fun g =>
    Real.exp (-ξ * sphereAvg g r 0) *
      (D g).1 (0, r • e₁ d))
  have hs := (hL6f d ξ κ) hB2 εs hεs hεt (normLGFLaw d) id
    D hh hDm hstable
  exact ⟨c, hs⟩

theorem l8_canonical_scales_of_good
    (hL6f : ∀ d ξ κ, L6f_tightScales d ξ κ)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (hN : L8NormalizedGood hd hκ ξ εs hεs) :
    ∃ c : ℝ → ℝ, (∀ r, 0 < r → 0 < c r) ∧
      TightFamily (normLGFLaw d)
        (fun r g => normalizedAtScale ξ
          (l8_patch hd hκ ξ εs hεs) c g r) (Ioi 0) := by
  letI : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d hd).1
  have hh : IsNormalizedLGF id (normLGFLaw d) :=
    (normLGFLaw_spec_holds d hd).2.1
  exact l8_canonical_scales_of_stable hL6f hd κ hκ ξ hB2 εs hεs
    hεt (l8_patch hd hκ ξ εs hεs)
    (l8_measurable_patch hd hκ ξ εs hεs)
    (l8_stable_normalized_of_good hd κ hκ ξ εs hεs hN
      (normLGFLaw d) id hh)

theorem l8_pure_tight_of_assign
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ)
    (D : DistRd d → ContMetric d) (hDm : Measurable D)
    (c : ℝ → ℝ)
    (hcan : TightFamily (normLGFLaw d)
      (fun r g => normalizedAtScale ξ D c g r) (Ioi 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsNormalizedLGF h P) :
    TightFamily P
        (fun r ω => normalizedAtScale ξ D c (h ω) r) (Ioi 0) := by
  let P₀ : Measure (DistRd d) := normLGFLaw d
  letI : IsProbabilityMeasure P₀ := (normLGFLaw_spec_holds d hd).1
  have hmap : P.map h = normLGFLaw d :=
    (normLGFLaw_spec_holds d hd).2.2 _ inferInstance hh.map_id
  apply determ_tightFamily_law_transfer P₀ P
      (fun r g => normalizedAtScale ξ D c g r)
      (fun r ω => normalizedAtScale ξ D c (h ω) r) (Ioi 0) hcan
  · intro r _
    have hF : Measurable (fun g : DistRd d => normalizedAtScale ξ D c g r) := by
      simpa only [← scaledField_zero] using
          (measurable_scaledField hDm c r 0)
    exact (hF.comp hh.1.measurable).aemeasurable
  · intro r _
    let F : DistRd d → C(Rd d × Rd d, ℝ) :=
      fun g => normalizedAtScale ξ D c g r
    have hF : Measurable F := by
      simpa only [F, ← scaledField_zero] using
          (measurable_scaledField hDm c r 0)
    change P₀.map F = P.map (F ∘ h)
    calc
      P₀.map F = (P.map h).map F := by rw [hmap]
      _ = P.map (F ∘ h) := Measure.map_map hF hh.1.measurable

theorem l8_tight_bdd_of_normalized
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (D : DistRd d → ContMetric d) (hDm : Measurable D)
    (hN : L8NormalizedWeyl ξ D)
    (c : ℝ → ℝ) (hc : ∀ r, 0 < r → 0 < c r)
    (hcan : TightFamily (normLGFLaw d)
      (fun r g => normalizedAtScale ξ D c g r) (Ioi 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsLGFPlusBddCont h P) :
    TightOver P (fun r ω => normalizedAtScale ξ
      D c (h ω) r) (Ioi 0) := by
  obtain ⟨h₀, g, hh₀, hgm, hgb, hdec⟩ :=
    l8_lgfPlusBddCont_decomp hd P h hh
  have hPure := l8_pure_tight_of_assign hd ξ D
    hDm c hcan P h₀ hh₀
  have hDg : Measurable (fun ω => D (addFun (h₀ ω) (g ω))) :=
    hDm.comp
      (measurable_addFun.comp (hh₀.1.measurable.prodMk hgm))
  have hW : ∀ᵐ ω ∂P, IsWeylOf ξ (g ω) (D (h₀ ω))
      (D (addFun (h₀ ω) (g ω))) := by
    filter_upwards [hN P h₀ hh₀] with ω ⟨hD, hw⟩
    intro z w
    rw [hw (g ω)]
    exact weylMetric_spec hD z w
  have hLen : ∀ᵐ ω ∂P, (D (h₀ ω)).IsLength :=
    (hN P h₀ hh₀).mono fun ω hw => hw.1
  have hT := l6c_remark38_bounded_of_weyl hd
    hξ
    P h₀ hh₀ g hgm (ae_of_all _ hgb)
    (fun ω => D (h₀ ω)) (fun ω => D (addFun (h₀ ω) (g ω)))
    hDg hLen hW c hc hPure
  have hTO : TightOver P
      (fun r ω => normalizedAtScale ξ D c
        (addFun (h₀ ω) (g ω)) r) (Ioi 0) :=
    ⟨hT.1, hT.2.1, fun μ hμ =>
      (hT.2.2 μ hμ).mono fun E hE => hE.1⟩
  simpa only [hdec] using hTO

end HigherDimLQGMetric
