/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PTrace
import InteractingSLE.Spec.Sec7.R6SafeCollar
import InteractingSLE.Spec.Supplement.RelTransHull
import InteractingSLE.Spec.Restart.FlowStopIdentLLTerminal

/-!
# Alive and dead prime ends of one current chart

Packet PROVE-R6-FACE2. Deterministic tools for the R.6 face (`R6FcCore`), for one current chart
`ψ⁻¹ ∘ f_q⁻¹` of a bounded Jordan pocket `C` with Jordan coordinate `ψ` and the Loewner chain of a driven curve.

* `exists_loewnerTrace_of_driven`: a driven curve's chain up to any live capacity time is the beginning of a global
  continuous Loewner trace of a continuous driver (the slit extension of `Lemma71P.exists_loewnerTrace`, for
  `IsDrivenCurve` instead of `IsSegCurve`).
* `jordan_comp_ext`: `ψ ∘ E₀ = id` on `ℍ̄` for the inverse boundary extension `E₀`.
* `exists_ball_subset_of_alive` / `notMem_closure_of_ball_subset`: a point `p` of `C̄ ∖ {x₀}` has a neighbourhood
  `C ∩ B(p, ρ)` inside the current domain `C ∩ ψ⁻¹(ℍ ∖ K)` iff `ψ(p) ∉ closure K` ("alive").
* `extendFrom_props`: the boundary extension of `f_q⁻¹` is continuous on `ℍ̄` with values in `ℍ̄`.
* `alive_of_not_mem_Icc`, `dead_of_mem_Icc`: off `[a_L, a_R]` the boundary extension lands off the closed hull, on
  `[a_L, a_R]` on it (PROVE-RELTRANS).
* `chartAR_pos_of_tip`, `chartAL_neg_of_tip`: if the tip is in `ℍ` the two force coordinates are nonzero.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Fc

open PocketTraversal Lemma71C
open WangWu (chartAL chartAR)

/-! ### A global trace for a driven curve -/

/-- **A driven curve's chain is the beginning of a global continuous Loewner trace**: for `t` below the terminal
capacity time there is a continuous driver `W` (`W 0 = 0`) agreeing with the canonical driver on `[0, t]` and a
continuous Loewner trace `η` of `W` with `η s = γ(capInv s)` on `[0, t]`. -/
theorem exists_loewnerTrace_of_driven {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < capLife γ) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ EqOn W (Ito.rpath fun s => segDriver γ s) (Icc 0 t) ∧
      ∃ η : ℝ → ℂ, IsLoewnerTrace W η ∧ ∀ s : ℝ, 0 ≤ s → s ≤ t → η s = γ (capInv γ s) := by
  set w : ℝ≥0 → ℝ := fun s => segDriver γ s with hwdef
  have hw : ContinuousOn w {s | (s : ℝ≥0∞) < capLife γ} := hγ.segDriver_spec.2.1
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  set W₁ := Ito.clampDrv (Ito.rpath w) t₂ with hW₁
  have hW₁c : Continuous W₁ := Ito.continuous_clampDrv t₂.coe_nonneg (Ito.continuousOn_rpath hw ht₂ζ)
  have hW₁e : EqOn W₁ (Ito.rpath w) (Icc 0 t₂) := Ito.clampDrv_eqOn
  have hW₁0 : W₁ 0 = 0 := by
    rw [hW₁e ⟨le_rfl, t₂.coe_nonneg⟩]
    show w (0 : ℝ).toNNReal = 0
    rw [Real.toNNReal_zero]
    exact hγ.segDriver_spec.1
  have hgen := hγ.isGeneratingTrace (T := (t₂ : ℝ≥0∞)) ht₂ζ
  have hLT := Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen
  have hLT₁ : IsLoewnerTraceLT W₁ t₂ (fun s : ℝ => capTrace γ s.toNNReal) :=
    ⟨hLT.1, hLT.2.1, fun s hs hst => by
      rw [← hLT.2.2 s hs hst]
      exact fwdHull_eq_of_eqOn hs hst fun r hr => hW₁e hr⟩
  have hext := hLT₁.isLoewnerTrace_ext hW₁c hW₁0 t.coe_nonneg htt₂'
  refine ⟨YuanCorollary13.extDrive W₁ t, YuanCorollary13.continuous_extDrive hW₁c,
    YuanCorollary13.extDrive_zero hW₁0 t.coe_nonneg, fun r hr => ?_, _, hext, fun s hs hst => ?_⟩
  · rw [YuanCorollary13.extDrive_eq hr.2]
    exact hW₁e ⟨hr.1, hr.2.trans htt₂'.le⟩
  · rw [YuanCorollary13.extTrace_eq hst]
    simp only [capTrace, Real.coe_toNNReal _ hs]

/-! ### Jordan coordinates: alive points -/

section Jordan

variable {C : Set ℂ} {x₀ y₀ : ℂ} {ψ : ℂ → ℂ}

/-- `ψ ∘ E₀ = id` on `ℍ̄` for a continuous extension `E₀` of `ψ⁻¹` with values in `C̄ ∖ {x₀}`. -/
theorem jordan_comp_ext (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) {E₀ : ℂ → ℂ}
    (hE : EqOn E₀ (Function.invFunOn ψ C) H) (hEc : ContinuousOn E₀ Hbar)
    (hEm : MapsTo E₀ Hbar (closure C \ {x₀})) {w : ℂ} (hw : w ∈ Hbar) : ψ (E₀ w) = w := by
  have hbij := hψ.2.2.2.1.2
  have hH : ∀ u ∈ H, ψ (E₀ u) = u := fun u hu => by
    rw [hE hu]; exact Function.invFunOn_eq (hbij.surjOn hu)
  have hcl : w ∈ closure H := by rwa [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  have hE' : Tendsto E₀ (𝓝[H] w) (𝓝 (E₀ w)) := ((hEc w hw).mono QuantumZipper.H_subset_Hbar).tendsto
  have hE'' : Tendsto E₀ (𝓝[H] w) (𝓝[closure C \ {x₀}] (E₀ w)) :=
    tendsto_nhdsWithin_iff.2 ⟨hE', eventually_nhdsWithin_of_forall fun u hu =>
      hEm (QuantumZipper.H_subset_Hbar hu)⟩
  have hlim := ((hψ.1 _ (hEm hw)).tendsto).comp hE''
  have hid : Tendsto (fun u => ψ (E₀ u)) (𝓝[H] w) (𝓝 w) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun u hu => (hH u hu).symm)
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact tendsto_nhds_unique hlim hid

/-- **An alive point has a neighbourhood in the current domain**: if `ψ(p) ∉ closure K`, then `C ∩ B(p, ρ)` lies in
`C ∩ ψ⁻¹(ℍ ∖ K)` for some `ρ > 0`. -/
theorem exists_ball_subset_of_alive (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) (hx₀ : x₀ ∉ C) {K : Set ℂ} {p : ℂ}
    (hp : p ∈ closure C \ {x₀}) (hpK : ψ p ∉ closure K) :
    ∃ ρ > 0, C ∩ ball p ρ ⊆ C ∩ ψ ⁻¹' (H \ K) := by
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hpK
  obtain ⟨ρ, hρ, hρψ⟩ := Metric.continuousWithinAt_iff.1 (hψ.1 p hp) r hr
  refine ⟨ρ, hρ, fun z hz => ⟨hz.1, hψ.2.2.2.1.2.mapsTo hz.1, fun hzK => ?_⟩⟩
  have hzC : z ∈ closure C \ {x₀} := ⟨subset_closure hz.1, fun h => hx₀ (h ▸ hz.1)⟩
  exact hrK (hρψ hzC (mem_ball.1 hz.2)) (subset_closure hzK)

/-- **A neighbourhood in the current domain makes a point alive** (bounded `C`): if `C ∩ B(p, ρ)` lies in
`C ∩ ψ⁻¹(ℍ ∖ K)` with `K ⊆ ℍ`, then `ψ(p) ∉ closure K`. -/
theorem notMem_closure_of_ball_subset (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) (hCb : Bornology.IsBounded C)
    (hx₀ : x₀ ∉ C) {K : Set ℂ} (hKH : K ⊆ H) {p : ℂ} (hp : p ∈ closure C \ {x₀}) {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : C ∩ ball p ρ ⊆ C ∩ ψ ⁻¹' (H \ K)) : ψ p ∉ closure K := by
  have hbij := hψ.2.2.2.1.2
  obtain ⟨r, hr, hball⟩ := R6Safe.jordan_mem_ball_of_mem_ball hψ hCb hp hρ
  intro hcl
  obtain ⟨u, huK, hud⟩ := Metric.mem_closure_iff.1 hcl r hr
  have huH : u ∈ H := hKH huK
  set z := Function.invFunOn ψ C u with hz
  have hzC : z ∈ C := Function.invFunOn_mem (hbij.surjOn huH)
  have hzu : ψ z = u := Function.invFunOn_eq (hbij.surjOn huH)
  have hzx : z ∈ closure C \ {x₀} := ⟨subset_closure hzC, fun h => hx₀ (h ▸ hzC)⟩
  have hzb : z ∈ ball p ρ := hball z hzx (by rw [hzu, mem_ball, dist_comm]; exact hud)
  exact (hsub ⟨hzC, hzb⟩).2.2 (by rw [hzu]; exact huK)

end Jordan

/-! ### The boundary extension of one Loewner chain -/

section Loewner

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {q : ℝ}

/-- The boundary extension of `f_q⁻¹` is continuous on `ℍ̄`, equals `f_q⁻¹` on `ℍ`, and takes values in `ℍ̄`. -/
theorem extendFrom_props (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hq : 0 ≤ q) :
    ContinuousOn (extendFrom H (fwdMapInv W q)) Hbar ∧ EqOn (extendFrom H (fwdMapInv W q)) (fwdMapInv W q) H ∧
      MapsTo (extendFrom H (fwdMapInv W q)) Hbar Hbar := by
  have hB := hη.hasBdryLimits hW hW0 hq
  have hc := continuousOn_fwdMapInv hW hW0 hq
  refine ⟨hB.continuousOn, fun z hz => extendFrom_H_eq hc hz, fun z hz => ?_⟩
  have hlim := hB.tendsto hz
  have hmem : ∀ᶠ u in 𝓝[H] z, fwdMapInv W q u ∈ Hbar := eventually_nhdsWithin_of_forall fun u hu =>
    QuantumZipper.H_subset_Hbar (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hq hu)
  have hcl : z ∈ closure H := by rwa [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hHbar : IsClosed Hbar := by
    rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact isClosed_closure
  exact hHbar.mem_of_tendsto hlim hmem

/-- **Off `[a_L, a_R]` the boundary extension lands off the closed hull.** -/
theorem alive_of_not_mem_Icc (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hq : 0 ≤ q) {x : ℝ}
    (hx : x < chartAL W q ∨ chartAR W q < x) :
    extendFrom H (fwdMapInv W q) (x : ℂ) ∉ closure (fwdHull W q) := by
  rcases hx with hx | hx
  · exact Supp8.RelTrans.extendFrom_notMem_closure_of_lt_chartAL hη hW hW0 hq hx
  · exact Supp8.RelTrans.extendFrom_notMem_closure_of_chartAR_lt hη hW hW0 hq hx

/-- **On `[a_L, a_R]` the boundary extension lands on the closed hull** (`q > 0`, `a_L < a_R`). -/
theorem dead_of_mem_Icc (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hq : 0 < q)
    (hlt : chartAL W q < chartAR W q) {x : ℝ} (hx : x ∈ Icc (chartAL W q) (chartAR W q)) :
    extendFrom H (fwdMapInv W q) (x : ℂ) ∈ closure (fwdHull W q) :=
  Supp8.RelTrans.Icc_subset_hullImage hη hW hW0 hq hlt hx

/-- **A tip in `ℍ` makes the right force coordinate positive.** -/
theorem chartAR_pos_of_tip (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hq : 0 ≤ q)
    (htip : extendFrom H (fwdMapInv W q) ((0 : ℝ) : ℂ) ∈ H) : 0 < chartAR W q := by
  have h := WangWu.lt_rightImg_sub_of_extendFrom_mem_H hη hW hW0 hq htip
  rw [chartAR]; exact h

/-- **A tip in `ℍ` makes the left force coordinate negative.** -/
theorem chartAL_neg_of_tip (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hq : 0 ≤ q)
    (htip : extendFrom H (fwdMapInv W q) ((0 : ℝ) : ℂ) ∈ H) : chartAL W q < 0 := by
  have h := WangWu.neg_rightImg_sub_lt_of_extendFrom_mem_H hη hW hW0 hq htip
  rw [chartAL]; exact h

end Loewner

end InteractingSLE.Sec7.R6Fc
