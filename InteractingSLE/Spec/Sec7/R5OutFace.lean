/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutHalf
import InteractingSLE.Spec.Sec7.R5OutSeed
import InteractingSLE.Spec.Sec7.R5LfCur

/-! # The exposed incident face supplies an old ambient half-disc (R98) -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open PocketTraversal Lemma71C PocketStop PocketStopField PocketStopSide PocketUnionPt
  PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen PocketCoupling R5Ref

/-- A continuous inverse extension agrees with the canonical boundary value. -/
theorem inverse_extension_eq_extendFrom {cur : Chart} {Fc : ℂ → ℂ}
    (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar) (u : ℝ) :
    Fc u = extendFrom H cur.2.1 u := by
  have hu : (u : ℂ) ∈ Hbar := by change (0 : ℝ) ≤ (u : ℂ).im; simp
  have hcl : (u : ℂ) ∈ closure H := by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hu
  symm
  apply extendFrom_eq hcl
  exact ((hFcc _ hu).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
    (eventually_nhdsWithin_of_forall fun z hz => hFc hz)

/-- An interior exposed coordinate has a whole real interval of trace
landings in `H`, after omitting the target. -/
theorem exists_local_trace_landing_of_interval {Fc : ℂ → ℂ}
    (hFc : ContinuousOn Fc Hbar) {η : ℝ → ℂ} {T a b ξ : ℝ} {exit : ℂ}
    (hTrace : ∀ u ∈ Ioo a b, Fc u ≠ exit → Fc u ∈ η '' Icc 0 T)
    (hξ : ξ ∈ Ioo a b) (hpH : Fc ξ ∈ H) (hpExit : Fc ξ ≠ exit) :
    ∃ r > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (ξ : ℂ) r → Fc u ∈ η '' Icc 0 T ∧ Fc u ∈ H := by
  have hc : Continuous fun u : ℝ => Fc u := hFc.comp_continuous Complex.continuous_ofReal
    fun u => by change (0 : ℝ) ≤ (u : ℂ).im; simp
  have hO : IsOpen {u : ℝ | u ∈ Ioo a b ∧ Fc u ∈ H ∧ Fc u ≠ exit} :=
    isOpen_Ioo.inter ((QuantumZipper.isOpen_H.preimage hc).inter
      (isOpen_ne_fun hc continuous_const))
  obtain ⟨r, hr, hBall⟩ := Metric.isOpen_iff.1 hO ξ ⟨hξ, hpH, hpExit⟩
  refine ⟨r, hr, fun u hu => ?_⟩
  have hgood := hBall (R5Lift.mem_ball_of_ofReal_mem_ball hu)
  exact ⟨hTrace u hgood.1 hgood.2.2, hgood.2.1⟩

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {ω : Ω}

/-- R98's protected old ambient half-disc for a bounded outer pocket.
It lies in the actual incident component, with no assertion that the raw
cut complement is connected. -/
theorem exists_ambient_halfDisc_outer
    (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAll R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω -
        segDriver (travAll R L r η ψ ω) q))
    (hpH : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ H)
    (hpExit : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ cfPt (openPt (R ω) (L ω) r))
    {s ρ : ℝ} (hs : 0 ≤ s) (hsT : s ≤ leftStop R L r η ψ q ω) (hρ : 0 < ρ)
    (hTail : Disjoint (η ω '' Icc s (leftStop R L r η ψ q ω))
      (closedBall (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) ρ)) :
    ∃ (v d : ℝ), 0 < d ∧
      Tendsto (fun z => fwdMap (W ω) s ((relChart c (travAll R L r η ψ) q ω).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (v : ℂ)) ∧
      fwdMapInv (W ω) s '' (H ∩ ball (v : ℂ) d) ⊆ (relChart c (travAll R L r η ψ) q ω).dom := by
  have hγ := (hcfg.props hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases (jordan_of_cfg hcfg hψ) hc hdom heq
  obtain ⟨Fc, hFc, hFcc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ) hγ hq hE hEc
  have hFext := inverse_extension_eq_extendFrom hFc hFcc
  have hLand := exists_local_trace_landing_of_interval hFcc
    (fun u hu hexit => by
      rw [hFext] at hexit ⊢
      exact mem_trace_of_seed_interval hcfg hψ hc hdom heq hxL hxR hq hu hexit)
    hξ (by rwa [hFext]) (by rwa [hFext])
  have hCurrent := current_dom_subset_ambient (A := univ) (mem_univ ω) hcfg hψ hc hdom heq hq
  have hK : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ H \ fwdHull (W ω) s := by
    intro z hz
    have hzT := (hCurrent hz).2
    exact ⟨hzT.1, fun hzK => hzT.2 (QuantumZipper.fwdHull_mono.1 hsT hzK)⟩
  exact exists_ambient_halfDisc_of_local_trace_landing hNow hFc hFcc hcfg.trace hcfg.continuous_W
    hcfg.W_zero hs hK (hFext ξ) hρ hTail hLand

/-- The same ambient half-disc for an outer pocket opening at the seed. -/
theorem exists_ambient_halfDisc_outerInf
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAllInf R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω -
        segDriver (travAllInf R L r η ψ ω) q))
    (hpH : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ H)
    {s ρ : ℝ} (hs : 0 ≤ s) (hsT : s ≤ leftStopInf R L r η ψ q ω) (hρ : 0 < ρ)
    (hTail : Disjoint (η ω '' Icc s (leftStopInf R L r η ψ q ω))
      (closedBall (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) ρ)) :
    ∃ (v d : ℝ), 0 < d ∧
      Tendsto (fun z => fwdMap (W ω) s ((relChart c (travAllInf R L r η ψ) q ω).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (v : ℂ)) ∧
      fwdMapInv (W ω) s '' (H ∩ ball (v : ℂ) d) ⊆ (relChart c (travAllInf R L r η ψ) q ω).dom := by
  have hγ := (hcfg.props hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases (Or.inr hψ) hc hdom heq
  obtain ⟨Fc, hFc, hFcc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hq hE hEc
  have hFext := inverse_extension_eq_extendFrom hFc hFcc
  have hLand := exists_local_trace_landing_of_interval (exit := Fc ξ + 1) hFcc
    (fun u hu _ => by rw [hFext]; exact mem_trace_of_seed_intervalInf hcfg hψ hc hdom heq hxL hxR hq hu)
    hξ (by rwa [hFext]) (by simp)
  have hCurrent := current_dom_subset_ambientInf (A := univ) (mem_univ ω) hcfg hψ hc hdom heq hq
  have hK : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ H \ fwdHull (W ω) s := by
    intro z hz
    have hzT := (hCurrent hz).2
    exact ⟨hzT.1, fun hzK => hzT.2 (QuantumZipper.fwdHull_mono.1 hsT hzK)⟩
  exact exists_ambient_halfDisc_of_local_trace_landing hNow hFc hFcc hcfg.trace hcfg.continuous_W
    hcfg.W_zero hs hK (hFext ξ) hρ hTail hLand

end InteractingSLE.Sec7.R5Out
