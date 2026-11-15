/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutCover
import InteractingSLE.Spec.Sec7.R5RefAmbientCover

/-!
# Ambient accesses selected by the outer incident reference cover

For a landing inside the pocket, the constructed reference contains the
landing in its ambient hull. The ambient access and force-jump exclusion
then use the existing Loewner lemmas on that selected component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase R5Ref MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
  {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- The ambient access at the constructed source reference in an outer pocket. -/
theorem exists_ambient_cover {ω : Ω} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζ : ζ' ω = ⊤) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, VL i t ω = -rightImg (fun s : ℝ => -W' s.toNNReal ω) (-xL i) t)
    (hVR : ∀ j t, VR j t ω = rightImg (fun s : ℝ => W' s.toNNReal ω) (xR j) t)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω)
    (hC : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r) :
    ∃ (i : ℕ) (x ε x' : ℝ),
      ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
      IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω ∧
      Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
        H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) ∧
      x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
        (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((refChart c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  have hγ := (hcfg.props hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨hLanding, -, -⟩ :=
    current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ hc hdom heq hq ξ
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h | h
    · exfalso
      subst h
      apply inverse_real_landing_notMem_dom hNow hLanding
      show _ ∈ ((relChart c (travAll R L r η ψ) 0 ω).dom : Set ℂ)
      rw [relChart_zero_dom (c := c) (γ := travAll R L r η ψ) hγ, hdom]
      exact hC
    · exact h
  simp only [refExc, mem_insert_iff, mem_singleton_iff, not_or] at hX
  obtain ⟨s, hs0, hv, hQ, hne, hpHull, x, ε, hcol⟩ :=
    exists_visit_collar (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq0 hq ξ hX.1 hX.2
  set i := Denumerable.eqv ℚ s with hi
  set t := rationalOriginalTime i with htdef
  have hti : (t : ℝ) = s := coe_rationalOriginalTime_eqv hs0
  have hv' : η ω t ∈ cfPocket (R ω) (L ω) r := by rw [hti]; exact hv
  have hQ' : (visitCap R L r η ψ ω t).toNNReal ≤ q := by rw [hti]; exact hQ
  have hne' : η ω t ≠ extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ := by rw [hti]; exact hne
  have hcol' : IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
      (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
    simp only [refChart, htdef ▸ hti]
    exact hcol
  have hHull : refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    refHull_eq_of_continuous hcfg.continuous_W hζ i
  obtain ⟨-, hOld0, hOldSub⟩ := visit_chart_subset
    (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq t.coe_nonneg hv'
  have hIncl := relChart_dom_antitone (c := c) (γ := travAll R L r η ψ) hc hγ hq hQ'
  have hOld : (refChart c R L r η ψ i ω).IsConformal := hOld0
  have hOldDom' : ((refChart c R L r η ψ i ω).dom : Set ℂ) ⊆
      H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) t := fun z hz => (hOldSub hz).2
  have hOldLive : ((refChart c R L r η ψ i ω).dom : Set ℂ) ⊆
      H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω := by
    rw [H_diff_liveExt_zero hω hγ, hHull]
    exact hOldSub
  have hpK : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈
      fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
    rw [hti]
    exact hpHull hC
  obtain ⟨x', hx'p, hlimOld⟩ := exists_ambient_access hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg hOld
    hOldDom' (tendsto_nhdsWithin_iff.1 hcol'.2.2.2.1).1 hpK
  have hlimCur : Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) t
      ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr : Tendsto (fun y => (refChart c R L r η ψ i ω).1 ((relChart c (travAll R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcol'.2.2.1, eventually_nhdsWithin_of_forall fun y hy =>
        hOld.fwd_mem (hIncl (hNow.inv_mem_dom hy))⟩
    refine (hlimOld.comp htr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    show fwdMap _ t ((refChart c R L r η ψ i ω).2.1 ((refChart c R L r η ψ i ω).1
      ((relChart c (travAll R L r η ψ) q ω).2.1 y))) = fwdMap _ t ((relChart c (travAll R L r η ψ) q ω).2.1 y)
    rw [hOld.inv_fwd (hIncl (hNow.inv_mem_dom hy))]
  have hjump := notMem_forceJumpSet_of_extendFrom hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg xL xR
    hx'p (hCH hC) (Ne.symm hne')
  have hWt : W' t ω = (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by simp only [Real.toNNReal_coe]
  have hJL : (fun j => VL j t ω - W' t ω) =
      fun j => -rightImg (fun s : ℝ => -(fun s : ℝ => W' s.toNNReal ω) s) (-xL j) (t : ℝ) -
        (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVL j t, hWt]
  have hJR : (fun j => VR j t ω - W' t ω) =
      fun j => rightImg (fun s : ℝ => W' s.toNNReal ω) (xR j) (t : ℝ) - (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVR j t, hWt]
  refine ⟨i, x, ε, x', ⟨hω, hq, Or.inl hv', hQ', hHull⟩, hv', hcol', ⟨hC, hHull ▸ hpK⟩, hLanding,
    eventually_nhdsWithin_of_forall fun y hy => hOldLive (hIncl (hNow.inv_mem_dom hy)), ?_, hlimCur, hlimOld⟩
  rw [hJL, hJR]
  exact hjump

/-- **The geometric part of R.5's ambient cover** (bounded change pocket), almost surely: the force processes are the
geometric images of the marks on the coupling's paths (`CfStep.force_eq_geom_of_path_top`). -/
theorem ae_exists_ambient_cover [MeasurableSpace Ω] {P : Measure Ω} {α : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL xR ρL ρR (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∀ ξ : ℝ,
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω →
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
      ∃ (i : ℕ) (x ε x' : ℝ),
        ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
        IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε ∧
        extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω ∧
        Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
          (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) ∧
        (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
          H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) ∧
        x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
          (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
          ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
          ((refChart c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  filter_upwards [hpath] with ω hp hω hq ξ hX hC
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h := (hcfg ω hω).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp (hζ ω hω) hV fun _ => rfl
  exact exists_ambient_cover hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hζ ω hω)
    (fun i t => hL i t) (fun j t => hR j t) hq ξ hX hC

/-- The ambient access at the source reference in a seed-opening outer pocket. -/
theorem exists_ambient_coverInf {ω : Ω} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζ : ζ' ω = ⊤) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, VL i t ω = -rightImg (fun s : ℝ => -W' s.toNNReal ω) (-xL i) t)
    (hVR : ∀ j t, VR j t ω = rightImg (fun s : ℝ => W' s.toNNReal ω) (xR j) t)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω)
    (hC : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r) :
    ∃ (i : ℕ) (x ε x' : ℝ),
      ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω ∧
      Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
        H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) ∧
      x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
        (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((refChartInf c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  have hγ := (hcfg.props hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨hLanding, -, -⟩ :=
    current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ hc hdom heq hq ξ
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h | h
    · exfalso
      subst h
      apply inverse_real_landing_notMem_dom hNow hLanding
      show _ ∈ ((relChart c (travAllInf R L r η ψ) 0 ω).dom : Set ℂ)
      rw [relChart_zero_dom (c := c) (γ := travAllInf R L r η ψ) hγ, hdom]
      exact hC
    · exact h
  simp only [refExcInf, mem_singleton_iff] at hX
  obtain ⟨s, hs0, hv, hQ, hne, hpHull, x, ε, hcol⟩ :=
    exists_visit_collarInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq0 hq ξ hX
  set i := Denumerable.eqv ℚ s with hi
  set t := rationalOriginalTime i with htdef
  have hti : (t : ℝ) = s := coe_rationalOriginalTime_eqv hs0
  have hv' : η ω t ∈ cfPocket (R ω) (L ω) r := by rw [hti]; exact hv
  have hQ' : (visitCapInf R L r η ψ ω t).toNNReal ≤ q := by rw [hti]; exact hQ
  have hne' : η ω t ≠ extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ := by rw [hti]; exact hne
  have hcol' : IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
      (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
    simp only [refChartInf, htdef ▸ hti]
    exact hcol
  have hHull : refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    refHull_eq_of_continuous hcfg.continuous_W hζ i
  obtain ⟨-, hOld0, hOldSub⟩ := visit_chart_subsetInf
    (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq t.coe_nonneg hv'
  have hIncl := relChart_dom_antitone (c := c) (γ := travAllInf R L r η ψ) hc hγ hq hQ'
  have hOld : (refChartInf c R L r η ψ i ω).IsConformal := hOld0
  have hOldDom' : ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ⊆
      H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) t := fun z hz => (hOldSub hz).2
  have hOldLive : ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ⊆
      H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω := by
    rw [H_diff_liveExt_zero hω hγ, hHull]
    exact hOldSub
  have hpK : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈
      fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
    rw [hti]
    exact hpHull hC
  obtain ⟨x', hx'p, hlimOld⟩ := exists_ambient_access hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg hOld
    hOldDom' (tendsto_nhdsWithin_iff.1 hcol'.2.2.2.1).1 hpK
  have hlimCur : Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) t
      ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr : Tendsto (fun y => (refChartInf c R L r η ψ i ω).1 ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcol'.2.2.1, eventually_nhdsWithin_of_forall fun y hy =>
        hOld.fwd_mem (hIncl (hNow.inv_mem_dom hy))⟩
    refine (hlimOld.comp htr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    show fwdMap _ t ((refChartInf c R L r η ψ i ω).2.1 ((refChartInf c R L r η ψ i ω).1
      ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))) = fwdMap _ t ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)
    rw [hOld.inv_fwd (hIncl (hNow.inv_mem_dom hy))]
  have hjump := notMem_forceJumpSet_of_extendFrom hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg xL xR
    hx'p (hCH hC) (Ne.symm hne')
  have hWt : W' t ω = (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by simp only [Real.toNNReal_coe]
  have hJL : (fun j => VL j t ω - W' t ω) =
      fun j => -rightImg (fun s : ℝ => -(fun s : ℝ => W' s.toNNReal ω) s) (-xL j) (t : ℝ) -
        (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVL j t, hWt]
  have hJR : (fun j => VR j t ω - W' t ω) =
      fun j => rightImg (fun s : ℝ => W' s.toNNReal ω) (xR j) (t : ℝ) - (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVR j t, hWt]
  refine ⟨i, x, ε, x', ⟨hω, hq, Or.inl hv', hQ', hHull⟩, hv', hcol', ⟨hC, hHull ▸ hpK⟩, hLanding,
    eventually_nhdsWithin_of_forall fun y hy => hOldLive (hIncl (hNow.inv_mem_dom hy)), ?_, hlimCur, hlimOld⟩
  rw [hJL, hJR]
  exact hjump

/-- **The geometric part of R.5's ambient cover** (change pocket opening at the flow seed), almost surely: the force
    processes are the
geometric images of the marks on the coupling's paths (`CfStep.force_eq_geom_of_path_top`). -/
theorem ae_exists_ambient_coverInf [MeasurableSpace Ω] {P : Measure Ω} {α : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL xR ρL ρR (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ,
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω →
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
      ∃ (i : ℕ) (x ε x' : ℝ),
        ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
        IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε ∧
        extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω ∧
        Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
          (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) ∧
        (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
          H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) ∧
        x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
          (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
          ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
          ((refChartInf c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  filter_upwards [hpath] with ω hp hω hq ξ hX hC
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h := (hcfg ω hω).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hp (hζ ω hω) hV fun _ => rfl
  exact exists_ambient_coverInf hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hζ ω hω)
    (fun i t => hL i t) (fun j t => hR j t) hq ξ hX hC

end InteractingSLE.Sec7.R5Out
