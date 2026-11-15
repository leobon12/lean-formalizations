/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HQJunctionKilled
import InteractingSLE.Spec.Sec5.Prop51GQExit
import InteractingSLE.Spec.Sec5.CrossRestartKernelObst

/-!
# Proposition 5.1's forward route in the chart `Q`: no contact at and above the critical gap

Packet PROVE-PROP51H, `FwdNoContactQStatement` (PROVE-PROP51G's large-gap input). Specification §5, proof of
Proposition 5.1 (p. 135, and (UC13), p. 115: "In the remaining empty-span case, `a₀ ≤ −λ` and `a₁ ≥ λ`; Lemma 4.5
puts the endpoint at their common junction"; "In the left-strip-end case, the completed simple flow segment joins `0`
to that end without meeting the revealed counterflow").

In the glued setting of `Cond44Ref.Prop51QStatement` at counterflow time `s`, the flow line `η = η_{θ₂}` read in the
counterflow chart `Ψ = revChart w s` is, up to its first contact with `R(K_s)`, the killed image word of
PROVE-CROSSCOND-THETA at relative angle `θ = θ₂ − θ₁ + π/2`. Its left-span weight is
`W = (3/2 + θ/π)(κ/2 − 2)`, and **at and above the critical gap** `θ₂ − θ₁ ≥ πκ/(4 − κ)` one has `W ≤ κ/2 − 4`: the
junction `Ψ(∞⁻) = junL` (the last left mark) is a low barrier for the western side, and the image word ends at it
(`Prop51HQJunctionKilled.ae_junctionExit_of_killed`). Pulled back, the flow line never meets the counterflow hull and
`Ψ ∘ η → junL < 0`.

* `extendFrom_eq_of_alive_neg`, `extendFrom_kVLr_eq`, `kVLr_lt_kVLr_zero`: `F̄_t` at the image of an alive negative
  point, and the order of the images of `0⁻` and of a negative point, for a killed arc;
* `noContact_of_imgJunction` (deterministic): an image limit in `ℍ ∪ {junL}` at the killing time forces "no contact
  and `Ψ ∘ η → junL`";
* `ae_imgJunctionT`, **`ae_noContactT`**: the glued image junction exit and its pull-back;
* **`fwdNoContactQStatement`**: `Prop51G.FwdNoContactQStatement`, unconditionally (the pull-back needs only the
  regularity of the counterflow recorded on the good set of the glued space, not `Prop51Q.CfLineRegularQStatement`);
* `prop51QOn_largeGap_of_reg`, `prop51QOn_largeGap_of_partA`: Proposition 5.1 in the chart `Q` at and above the
  critical gap; `prop51QStatement_of_partA_of_post`, `cfFirstContactQStatement_of_partA_of_post`: PROVE-PROP51G's
  wiring with the large-gap input discharged.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop51H

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond CrossCond.Word49 CrossCond.Theta MartChar.RealFlow LawUnique Cond44Ref Prop411Q
  CfRegQ Prop49Exit Prop51G
open Sec7.Lemma71C (capClock)

/-! ### Boundary values at the junction of a killed arc -/

section Killed

/-- **`F̄_t` at the image of an alive negative point is the point.** -/
theorem extendFrom_eq_of_alive_neg {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hB : HasBdryLimits (fwdMapInv w t)) {a : ℝ} (ha : Alive (fun s => -w s) (-a) t) :
    extendFrom H (fwdMapInv w t) ((-rightImg (fun s => -w s) (-a) t - w t : ℝ) : ℂ) = a := by
  have hsol := WangWu.isForwardSol_neg_of_alive hw ha
  have hHb : -((-a : ℝ) : ℂ) ∈ Hbar := by
    show 0 ≤ (-((-a : ℝ) : ℂ)).im
    simp
  have hE := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hw hw0 ht hHb hsol
  have hw' : Continuous fun s => -w s := hw.neg
  have hc : -rightImg (fun s => -w s) (-a) t - w t = -cflow (fun s => -w s) (-a) t := by
    rw [rightImg_eq_gImg hw' ht ha]
    have h1 : gImg (fun s => -w s) (-a) t = (fun s => -w s) t + cflow (fun s => -w s) (-a) t := rfl
    rw [h1]
    ring
  rw [hc]
  have e : (((-cflow (fun s => -w s) (-a) t : ℝ)) : ℂ) = -((cflow (fun s => -w s) (-a) t : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, hE]
  push_cast
  ring

variable {γ : ℝ → ℂ} {P : Set ℝ}

/-- **The killed version**: before the terminal capacity, `F̄_t` sends the left image of a negative point `a` (under
the killed driver) back to `a`. -/
theorem extendFrom_kVLr_eq (hγ : IsKilledArc γ P) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kLife γ P) {a : ℝ}
    (ha : a < 0) :
    extendFrom H (fwdMapInv (kPath γ P) t) ((-kImg (fun r => -kPath γ P r) (-a) t - kW γ P t : ℝ) : ℂ) = a := by
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ := hγ.exists_kPath_trace ht
  have hEq' : EqOn (fun r => -kPath γ P r) (fun r => -w r) (Icc 0 (capClock γ S)) := fun r hr => by
    simp only [hEq hr]
  have hal := CrossRestart.alive_neg_of_mem_H hηL (fun s hs => hηP.mem_H s hs.1) hw hw0 t.coe_nonneg
  rw [kImg_eq hw.neg hEq' htS.le, ← kPath_coe, hEq ⟨t.coe_nonneg, htS.le⟩,
    fwdMapInv_eq_of_eqOn (W := kPath γ P) (W' := w) t.coe_nonneg htS fun r hr => hEq hr]
  exact extendFrom_eq_of_alive_neg hw hw0 t.coe_nonneg (hηL.hasBdryLimits hw hw0 t.coe_nonneg)
    (hal _ (by linarith))

/-- **The left image of a negative point lies strictly left of the image of `0⁻`** before the terminal capacity. -/
theorem kVLr_lt_kVLr_zero (hγ : IsKilledArc γ P) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < kLife γ P) {a : ℝ}
    (ha : a < 0) :
    -kImg (fun r => -kPath γ P r) (-a) t < -kImg (fun r => -kPath γ P r) (-0) t := by
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ := hγ.exists_kPath_trace ht
  have hEq' : EqOn (fun r => -kPath γ P r) (fun r => -w r) (Icc 0 (capClock γ S)) := fun r hr => by
    simp only [hEq hr]
  have hal := CrossRestart.alive_neg_of_mem_H hηL (fun s hs => hηP.mem_H s hs.1) hw hw0 t.coe_nonneg
  have hw' : Continuous fun s => -w s := hw.neg
  rw [kImg_eq hw' hEq' htS.le, kImg_eq hw' hEq' htS.le, neg_zero,
    rightImg_eq_gImg hw' t.coe_nonneg (hal _ (by linarith))]
  have := GlueImg.rightImg_lt_gImg_of_lt hw' t.coe_nonneg hal le_rfl (show (0 : ℝ) < -a by linarith)
  linarith

end Killed

/-! ### The junction exit pulled back to the flow line (deterministic) -/

section Det

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {η : ℝ → ℂ} {s : ℝ}

/-- `R(junL) = R_s(0⁺) − W_s`, the image of `0⁺` in the counterflow's own chart. -/
theorem negInv_junL (hjL : 0 < rightImg w 0 s - w s) :
    negInv (junL w s : ℂ) = ((rightImg w 0 s - w s : ℝ) : ℂ) := by
  have hne : ((rightImg w 0 s - w s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hjL.ne'
  have e : ((junL w s : ℝ) : ℂ) = -((rightImg w 0 s - w s : ℝ) : ℂ)⁻¹ := by
    simp only [junL]; push_cast; ring
  rw [e, negInv, neg_inv, neg_neg, inv_inv]

/-- **The junction exit, pulled back to the flow line** (deterministic). If the image curve `Ψ ∘ η` of the proper arc
`η` in the counterflow chart `Ψ = revChart w s` converges at its killing capacity to a point of `ℍ` or to the left
junction `junL = Ψ(∞⁻)`, then `η` never meets the counterflow hull `R(K_s)` and `Ψ ∘ η → junL` as `t → ∞`. A first
contact at a finite time `τ` is impossible: a limit in `ℍ` would put `η(τ)` off the hull, and the limit `junL` would
make `R(η(τ)) ∈ ℍ` the boundary value `F̄_s(R_s(0⁺) − W_s)`, which is not in `ℍ`. -/
theorem noContact_of_imgJunction (hw : Continuous w) (hw0 : w 0 = 0) (hβ : IsLoewnerTrace w β) (hs : 0 < s)
    (hjL : 0 < rightImg w 0 s - w s) (hG : IsClosed (negInv '' fwdHull w s)) (hη : IsProperArc η) {T' : ℝ≥0}
    (hT' : (T' : WithTop ℝ≥0) = kLife (imgCurve w s η) (preContact η (negInv '' fwdHull w s))) {z : ℂ}
    (hz : Tendsto (kTrace (imgCurve w s η) (preContact η (negInv '' fwdHull w s))) (𝓝[<] T') (𝓝 z))
    (hzalt : z ∈ H ∨ z = (junL w s : ℂ)) :
    (∀ t : ℝ, 0 < t → η t ∉ negInv '' fwdHull w s) ∧
      Tendsto (fun t => revChart w s (η t)) atTop (𝓝 (junL w s : ℂ)) := by
  set G := negInv '' fwdHull w s with hGdef
  set γ := imgCurve w s η with hγdef
  set P := preContact η G with hPdef
  have hK : IsKilledArc γ P := isKilledArc_imgCurve hw hw0 hs.le hG hη
  have hjL' : junL w s < 0 := by
    simp only [junL]; rw [neg_div]; exact neg_neg_of_pos (div_pos one_pos hjL)
  have hPmem : ∀ u ∈ P, 0 < u → η u ∈ H \ G := fun u hu hu0 => ⟨hη.mem_H u hu0, hu.2 u ⟨hu.1, le_rfl⟩⟩
  have hlimγ : ∀ L : Filter ℝ, (∀ᶠ u in L, u ∈ P) → (∀ S ∈ P, ∀ᶠ u in L, S ≤ u) → Tendsto γ L (𝓝 z) := by
    intro L hLP hLS
    refine (hz.comp (tendsto_capClock_kLife hK hT' hLP hLS)).congr' ?_
    filter_upwards [hLP] with u hu
    exact kTrace_capClock hK hu
  by_cases hbdd : BddAbove P
  · -- a first contact at `τ = sup P` is impossible
    exfalso
    set τ := sSup P with hτdef
    have hPne : P.Nonempty := ⟨0, hK.zero_mem⟩
    obtain ⟨S₁, hS₁, hS₁0⟩ := hK.exists_gt 0 hK.zero_mem
    have hτ0 : 0 < τ := lt_of_lt_of_le hS₁0 (le_csSup hbdd hS₁)
    have hτP : τ ∉ P := fun h => by
      obtain ⟨S', hS', hτS'⟩ := hK.exists_gt τ h
      exact absurd (le_csSup hbdd hS') (not_le.2 hτS')
    have hIco : ∀ t, 0 ≤ t → t < τ → t ∈ P := fun t ht htτ => by
      obtain ⟨S, hS, htS⟩ := exists_lt_of_lt_csSup hPne htτ
      exact hK.icc S hS ⟨ht, htS.le⟩
    have hητG : η τ ∈ G := by
      by_contra hn
      refine hτP ⟨hτ0.le, fun u hu => ?_⟩
      rcases hu.2.lt_or_eq with hlt | rfl
      · exact (hIco u hu.1 hlt).2 u ⟨hu.1, le_rfl⟩
      · exact hn
    have hLP : ∀ᶠ u in 𝓝[<] τ, u ∈ P ∧ 0 < u := by
      filter_upwards [Ioo_mem_nhdsLT hτ0] with u hu
      exact ⟨hIco u hu.1.le hu.2, hu.1⟩
    have hLS : ∀ S ∈ P, ∀ᶠ u in 𝓝[<] τ, S ≤ u := fun S hS => by
      have hSτ : S < τ := lt_of_le_of_ne (le_csSup hbdd hS) fun h => hτP (h ▸ hS)
      filter_upwards [Ioo_mem_nhdsLT hSτ] with u hu
      exact hu.1.le
    have hγz := hlimγ _ (hLP.mono fun u hu => hu.1) hLS
    have hηc : Tendsto η (𝓝[<] τ) (𝓝 (η τ)) :=
      ((hη.cont.continuousAt (Ici_mem_nhds hτ0)).tendsto).mono_left nhdsWithin_le_nhds
    have hγΨ : ∀ᶠ u in 𝓝[<] τ, γ u = revChart w s (η u) := by
      filter_upwards [hLP] with u hu
      exact imgCurve_of_pos hu.2
    rcases hzalt with hzH | hzj
    · -- a limit in `ℍ` would put `η(τ)` off `G`
      have hinv : Tendsto (fun u => revChartInv w s (γ u)) (𝓝[<] τ) (𝓝 (revChartInv w s z)) :=
        ((continuousOn_revChartInv hw hw0 hs.le).continuousAt (QuantumZipper.isOpen_H.mem_nhds hzH)).tendsto.comp
          hγz
      have hinv' : Tendsto η (𝓝[<] τ) (𝓝 (revChartInv w s z)) := by
        refine hinv.congr' ?_
        filter_upwards [hLP, hγΨ] with u hu he
        rw [he, revChartInv_revChart hw hw0 hs.le (hPmem u hu.1 hu.2)]
      have heq := tendsto_nhds_unique hηc hinv'
      exact (revChartInv_mem hw hw0 hs.le hzH).2 (heq ▸ hητG)
    · -- the junction: `R(η(τ)) ∈ ℍ` would be the boundary value at `R_s(0⁺) − W_s`
      obtain ⟨k, hkK, hke⟩ := hητG
      have hkH : k ∈ H := hkK.1
      have hne : η τ ≠ 0 := fun h => by
        have := hη.mem_H τ hτ0
        rw [h] at this
        exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
      have hξ : Tendsto (fun u => negInv (η u)) (𝓝[<] τ) (𝓝 k) := by
        have := (continuousAt_negInv hne).tendsto.comp hηc
        rwa [← hke, negInv_negInv] at this
      have hξH : ∀ᶠ u in 𝓝[<] τ, negInv (η u) ∈ H \ fwdHull w s := by
        filter_upwards [hLP] with u hu
        exact negInv_notMem_fwdHull (hPmem u hu.1 hu.2)
      have hj0 : (junL w s : ℂ) ≠ 0 := by exact_mod_cast hjL'.ne
      have hf : Tendsto (fun u => fwdMap w s (negInv (η u))) (𝓝[<] τ)
          (𝓝[H] ((rightImg w 0 s - w s : ℝ) : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have hγz' : Tendsto γ (𝓝[<] τ) (𝓝 (junL w s : ℂ)) := hzj ▸ hγz
          have h1 := (continuousAt_negInv hj0).tendsto.comp hγz'
          rw [negInv_junL hjL] at h1
          refine h1.congr' ?_
          filter_upwards [hγΨ] with u he'
          simp only [Function.comp_apply, he', revChart, negInv_negInv]
        · filter_upwards [hξH] with u hu
          exact QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs.le hu
      have hB := (hβ.hasBdryLimits hw hw0 hs.le).tendsto (ofReal_mem_Hbar (rightImg w 0 s - w s))
      have h3 : Tendsto (fun u => negInv (η u)) (𝓝[<] τ)
          (𝓝 (extendFrom H (fwdMapInv w s) ((rightImg w 0 s - w s : ℝ) : ℂ))) := by
        refine (hB.comp hf).congr' ?_
        filter_upwards [hξH] with u hu
        exact QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hs.le hu
      have hk := tendsto_nhds_unique h3 hξ
      have hlt := lt_rightImg_sub_of_extendFrom_mem_H hβ hw hw0 hs.le (hk ▸ hkH)
      exact lt_irrefl _ hlt
  · -- no contact
    have hPall : ∀ t, 0 ≤ t → t ∈ P := fun t ht => by
      rw [not_bddAbove_iff] at hbdd
      obtain ⟨S, hS, htS⟩ := hbdd t
      exact hK.icc S hS ⟨ht, htS.le⟩
    have hLP : ∀ᶠ u in (atTop : Filter ℝ), u ∈ P ∧ 0 < u := by
      filter_upwards [eventually_gt_atTop 0] with u hu
      exact ⟨hPall u hu.le, hu⟩
    have hγz := hlimγ atTop (hLP.mono fun u hu => hu.1) fun S _ => eventually_ge_atTop S
    have hγΨ : ∀ᶠ u in (atTop : Filter ℝ), γ u = revChart w s (η u) := by
      filter_upwards [hLP] with u hu
      exact imgCurve_of_pos hu.2
    rcases hzalt with hzH | hzj
    · exfalso
      have hinv : Tendsto (fun u => revChartInv w s (γ u)) atTop (𝓝 (revChartInv w s z)) :=
        ((continuousOn_revChartInv hw hw0 hs.le).continuousAt (QuantumZipper.isOpen_H.mem_nhds hzH)).tendsto.comp
          hγz
      have hinv' : Tendsto η atTop (𝓝 (revChartInv w s z)) := by
        refine hinv.congr' ?_
        filter_upwards [hLP, hγΨ] with u hu he
        rw [he, revChartInv_revChart hw hw0 hs.le (hPmem u hu.1 hu.2)]
      exact not_tendsto_nhds_of_tendsto_atTop hη.tendsto _ ((continuous_norm.tendsto _).comp hinv')
    · refine ⟨fun t ht => (hPall t ht.le).2 t ⟨ht.le, le_rfl⟩, ?_⟩
      rw [← hzj]
      exact hγz.congr' hγΨ

end Det

/-! ### The image junction exit at relative angle `θ` (at and above the critical gap) -/

section Glued

/-- **The left total of the image word at relative angle `θ`**: `Σ ρ^L + cLT θ κ (Σ ρ^L) = (3/2 + θ/π)(κ/2 − 2)`. -/
theorem sum_jwL_cLT {κ θ : ℝ} {nL : ℕ} (ρL : Fin nL → ℝ) :
    ∑ i, jwL (cLT θ) κ ρL i = (3 / 2 + θ / π) * (κ / 2 - 2) := by
  rw [Fin.sum_univ_castSucc]
  simp only [jwL, cLT, Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- At and above the critical gap the left total of the image word is at most `κ/2 − 4`. -/
theorem sum_jwL_cLT_le {κ θ : ℝ} (hθ₂ : 2 ≤ (1 / 2 + θ / π) * (2 - κ / 2)) {nL : ℕ} (ρL : Fin nL → ℝ) :
    ∑ i, jwL (cLT θ) κ ρL i ≤ κ / 2 - 4 := by
  rw [sum_jwL_cLT]
  have e : (3 / 2 + θ / π) * (κ / 2 - 2) = (κ / 2 - 2) - (1 / 2 + θ / π) * (2 - κ / 2) := by ring
  linarith

/-- **The image junction exit at relative angle `θ`** (the large-gap counterpart of `Prop51G.ae_imgExitT`). In the
glued setting of `CrossCond.Theta.CfGlueAET θ`, for `π/2 ≤ θ` at and above the critical gap
(`(1/2 + θ/π)(2 − κ/2) ≥ 2`), a flow word with a mark at `0⁻`, and every counterflow time `s > 0`, almost surely the
killing time `imgT` of the image word is finite and the image trace converges at `imgT`, either to a point of `ℍ` or
to the left junction `Ψ(∞⁻)` (Aux. lemma 22's empty-span case for the image word). -/
theorem ae_imgJunctionT {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : π / 2 ≤ θ)
    (hθ₂ : 2 ≤ (1 / 2 + θ / π) * (2 - κ / 2)) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hseed : ∃ i₀, xL i₀ = 0) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p : ℝ≥0∞) ≠ ⊤ ∧
      ∃ z : ℂ, Tendsto (imgTr s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p)
        (𝓝[<] ENNReal.toNNReal (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p)) (𝓝 z) ∧
        (z ∈ H ∨ z = (gXL xL s (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p (Fin.last nL) : ℂ)) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49T θ s hs κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂
      hcf hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  obtain ⟨-, hK, hWa, hVLa, hVRa, -, -, -, -, hζq⟩ := filtClauses (μ := μ) (xL := xL) (xR := xR) hWad hF hae
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓦, Bi, hB, hBc, hEnt⟩ :=
    exists_isWordEntrance_of_filtTheta (imageWordFiltThetaStatement θ) hκ hκ4 hF h44 hθb hC hcf hlaw k hk hs
  set 𝓖 := imgFilt μ xL xR s ζ W E with h𝓖
  have hTq' : ∀ q : ℝ≥0, MeasurableSet[WholeField.prodFiltration 𝓖 𝓦 q]
      {p : (Ω × HistorySpace 0 0) × Ω₀ | (q : ℝ≥0∞) < (imgT s ζ W E p.1 : ℝ≥0∞)} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hζq q, rfl⟩
  have hthr : ∀ᵐ p ∂(μ.prod P₀), ¬ ForceWord.ThresholdCondition (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
      (imgW s ζ W E 0 p.1) (fun i => imgVL xL s ζ W E i 0 p.1) (fun j => imgVR xR s ζ W E j 0 p.1) := by
    have h1 : ∀ᵐ p ∂μ, ¬ ForceWord.ThresholdCondition (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
        (imgW s ζ W E 0 p) (fun i => imgVL xL s ζ W E i 0 p) (fun j => imgVR xR s ζ W E j 0 p) := by
      filter_upwards [ae_mem_glueGood hae] with p hp
      exact not_threshold_img_gen (cLT θ) (cRT θ) hκ hF h44 hEg hp
    exact Measure.quasiMeasurePreserving_fst.ae h1
  -- on the good set, the junction is negative and the seed mark's image is right of the junction's
  obtain ⟨i₀, hi₀⟩ := hseed
  have hgood : ∀ p ∈ E, gXL xL s E p (Fin.last nL) < 0 ∧ gXL xL s E p (Fin.castSucc i₀) = 0 := by
    intro p hp
    obtain ⟨-, -, hjL, -, -⟩ := hEg p hp
    rw [gXL_of_mem hp, Fin.snoc_last, Fin.snoc_castSucc, hi₀]
    refine ⟨?_, by simp [psiL]⟩
    simp only [junL]; rw [neg_div]; exact neg_neg_of_pos (div_pos one_pos hjL)
  have hfl : ∀ᵐ p ∂(μ.prod P₀), ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < (imgT s ζ W E p.1 : ℝ≥0∞) →
      ∃ i, imgVL xL s ζ W E (Fin.last nL) t p.1 < imgVL xL s ζ W E i t p.1 := by
    have h1 : ∀ᵐ p ∂μ, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) →
        ∃ i, imgVL xL s ζ W E (Fin.last nL) t p < imgVL xL s ζ W E i t p := by
      filter_upwards [ae_mem_glueGood hae] with p hp t _ htT
      obtain ⟨hneg, hzero⟩ := hgood p hp
      refine ⟨Fin.castSucc i₀, ?_⟩
      simp only [Word49.imgVL]
      rw [kVL_of_lt _ _ htT, kVL_of_lt _ _ htT]
      simp only [kVLr]
      rw [hzero]
      exact kVLr_lt_kVLr_zero (isKilledArc_gCurve hEg p) htT hneg
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have hgeo : ∀ᵐ p ∂(μ.prod P₀), ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < (imgT s ζ W E p.1 : ℝ≥0∞) →
      extendFrom H (fwdMapInv (fun r : ℝ => imgW s ζ W E r.toNNReal p.1) t)
        ((imgVL xL s ζ W E (Fin.last nL) t p.1 - imgW s ζ W E t p.1 : ℝ) : ℂ) ∉ H := by
    have h1 : ∀ᵐ p ∂μ, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) →
        extendFrom H (fwdMapInv (fun r : ℝ => imgW s ζ W E r.toNNReal p) t)
          ((imgVL xL s ζ W E (Fin.last nL) t p - imgW s ζ W E t p : ℝ) : ℂ) =
            (gXL xL s E p (Fin.last nL) : ℂ) := by
      filter_upwards [ae_mem_glueGood hae] with p hp t _ htT
      simp only [Word49.imgVL, Word49.imgW]
      rw [kVL_of_lt _ _ htT]
      exact extendFrom_kVLr_eq (isKilledArc_gCurve hEg p) htT (hgood p hp).1
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1] with p hp t ht0 htT
    rw [hp t ht0 htT]
    intro hH
    exact lt_irrefl _ (show (0 : ℝ) < ((gXL xL s E p.1 (Fin.last nL) : ℝ) : ℂ).im from hH |>.trans_eq (by simp))
  have hX := ae_junctionExit_of_killed (P := μ.prod P₀) (𝓘 := WholeField.prodFiltration 𝓖 𝓦) hκ hκ4.le
    (Nat.succ_pos nR) (hasStripPrefixSums_jwT hκ4 hθ h44) (sum_jwL_cLT_le hθ₂ ρL) hB hBc
    (W := fun t p => imgW s ζ W E t p.1) (VL := fun i t p => imgVL xL s ζ W E i t p.1)
    (VR := fun j t p => imgVR xR s ζ W E j t p.1)
    (Sec7.PhaseSelFull.stronglyAdapted_fst hWa) (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
    (fun j => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa j)) (T := fun p => (imgT s ζ W E p.1 : ℝ≥0∞)) hTq'
    (fun p => (isKilledArc_gCurve hEg p.1).zero_lt_kLife) hEnt
    (fun p t ht htT i => hK.sepL p.1 t ht htT i) (fun p t ht htT j => hK.sepR p.1 t ht htT j) hfl hthr hgeo
  have hgeoμ : ∀ᵐ p ∂μ, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) →
      extendFrom H (fwdMapInv (fun r : ℝ => imgW s ζ W E r.toNNReal p) t)
        ((imgVL xL s ζ W E (Fin.last nL) t p - imgW s ζ W E t p : ℝ) : ℂ) =
          (gXL xL s E p (Fin.last nL) : ℂ) := by
    filter_upwards [ae_mem_glueGood hae] with p hp t _ htT
    simp only [Word49.imgVL, Word49.imgW]
    rw [kVL_of_lt _ _ htT]
    exact extendFrom_kVLr_eq (isKilledArc_gCurve hEg p) htT (hgood p hp).1
  have h2 := Measure.ae_ae_of_ae_prod hX
  filter_upwards [h2, hgeoμ] with p hp hpg
  obtain ⟨_, hpω⟩ := hp.exists
  obtain ⟨hTne, z, hz, hzalt⟩ := hpω (imgTr s ζ W E p) (fun r hr => isGeneratingTraceIcc_imgTr hEg p hr)
    (fun t ht0 ht => imgTr_mem_H hEg p ht0 ht)
  refine ⟨hTne, z, hz, ?_⟩
  rcases hzalt with hzH | ⟨q, hq0, hqT, rfl⟩
  · exact Or.inl hzH
  · exact Or.inr (hpg q hq0 hqT)

end Glued

/-! ### No contact at and above the critical gap -/

section NoContact

/-- **No contact at and above the critical gap, on the glued space** (the large-gap counterpart of
`Prop51G.ae_exitT`). In the glued setting of `CrossCond.Theta.CfGlueAET θ`, for `π/2 ≤ θ` at and above the critical gap
and a flow word with a mark at `0⁻`, for every positive rational `s`, almost surely the flow line `η = seedLine ζ W`
never meets `R(K_s)` at positive times and `Ψ ∘ η` tends to the left junction `junL = Ψ(∞⁻) < 0` (it leaves
`ℍ ∖ R(K_s)` through the western end of `∞`). -/
theorem ae_noContactT {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : π / 2 ≤ θ)
    (hθ₂ : 2 ≤ (1 / 2 + θ / π) * (2 - κ / 2)) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hseed : ∃ i₀, xL i₀ = 0) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    {s : ℚ} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      (∀ t : ℝ, 0 < t → seedLine ζ W p.1 t ∉ negInv '' fwdHull (cfDrv p.2) s) ∧ junL (cfDrv p.2) s < 0 ∧
        Tendsto (fun t => revChart (cfDrv p.2) s (seedLine ζ W p.1 t)) atTop (𝓝 (junL (cfDrv p.2) s : ℂ)) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set s' : ℝ≥0 := (s : ℝ).toNNReal with hs'def
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs' : 0 < s' := Real.toNNReal_pos.2 hs0
  have hss' : (s' : ℝ) = (s : ℝ) := Real.coe_toNNReal _ hs0.le
  set E := glueGood μ s' ζ W with hEdef
  have hgood := cfGlueAE_isGood49T θ s' hs' κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂
    hcf hlaw k hk
  have hae : ∀ᵐ p ∂μ, IsGood49 s' ζ W p := by
    filter_upwards [hgood] with p hp
    exact isGood49_of_mem hp.1 hp.2
  have hexit := ae_imgJunctionT hκ hκ4 hθ hθ₂ hF h44 hseed hθb hC hcf hlaw k hk hs'
  filter_upwards [hexit, hgood, ae_mem_glueGood hae] with p ⟨hTne, z, hz, hzalt⟩ hpg hpE
  obtain ⟨hα, hG0, hjL0, -, hQ⟩ := isGood49_of_mem_glueGood p hpE
  have hy : p.2 ∈ goodCfSet := hpg.2.1.1
  obtain ⟨-, hw, hw0, hβ⟩ := reg_of_mem_goodCfSet hy
  have hEq := eqOn_cfDrv0_cfDrv hy s'
  have hK0 := fwdHull_cfDrv0 hy s'
  have hR0 := revChart_cfDrv0 hy s'
  have hrI : rightImg (cfDrv0 s' p.2) 0 s' = rightImg (cfDrv p.2) 0 s' :=
    Sec7.Lemma71B.rightImg_congr hw s'.coe_nonneg hEq 0
  have hw0s : cfDrv0 s' p.2 s' = cfDrv p.2 s' := hEq s' ⟨s'.coe_nonneg, le_rfl⟩
  have hjL : 0 < rightImg (cfDrv p.2) 0 s - cfDrv p.2 s := by
    rw [← hss', ← hrI, ← hw0s]; exact hjL0
  have hG : IsClosed (negInv '' fwdHull (cfDrv p.2) s) := by rw [← hss', ← hK0]; exact hG0
  have hcurve : gCurve s' ζ W E p = imgCurve (cfDrv p.2) s (seedLine ζ W p.1) := by
    rw [gCurve_of_mem hpE]
    funext u
    simp only [imgCurve]
    rw [hR0, hss']
  have hpre : gPre s' ζ W E p = preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s) := by
    rw [gPre_of_mem hpE, hQ, hK0, hss']
  have hjun : gXL xL s' E p (Fin.last nL) = junL (cfDrv p.2) s := by
    rw [gXL_of_mem hpE, Fin.snoc_last]
    simp only [junL]
    rw [hrI, hw0s, hss']
  have hT' : ((ENNReal.toNNReal (imgT s' ζ W E p) : ℝ≥0) : WithTop ℝ≥0) =
      kLife (imgCurve (cfDrv p.2) s (seedLine ζ W p.1))
        (preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s)) := by
    rw [← hcurve, ← hpre]
    exact ENNReal.coe_toNNReal hTne
  have hz' : Tendsto (kTrace (imgCurve (cfDrv p.2) s (seedLine ζ W p.1))
      (preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s)))
      (𝓝[<] ENNReal.toNNReal (imgT s' ζ W E p)) (𝓝 z) := by
    rw [← hcurve, ← hpre]; exact hz
  have hzalt' : z ∈ H ∨ z = (junL (cfDrv p.2) s : ℂ) := by
    rcases hzalt with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by rw [h1, hjun])
  have hjL' : junL (cfDrv p.2) s < 0 := by
    simp only [junL]; rw [neg_div]; exact neg_neg_of_pos (div_pos one_pos hjL)
  obtain ⟨hno, hlim⟩ := noContact_of_imgJunction hw hw0 hβ hs0 hjL hG hα hT' hz' hzalt'
  exact ⟨hno, hjL', hlim⟩

/-- At and above the critical gap, the charge bound of `ae_imgJunctionT` at `θ = θ₂ − θ₁ + π/2`. -/
theorem charge_bound_of_isLargeGap {κ θ₁ θ₂ : ℝ} (hκ4 : κ < 4) (hG : IsLargeGap κ θ₁ θ₂) :
    2 ≤ (1 / 2 + (θ₂ - θ₁ + π / 2) / π) * (2 - κ / 2) := by
  have hπ := Real.pi_pos
  have h4 : 0 < 4 - κ := by linarith
  have hg : π * κ ≤ (θ₂ - θ₁) * (4 - κ) := by
    have := hG
    unfold IsLargeGap at this
    rwa [div_le_iff₀ h4] at this
  have e : (1 / 2 + (θ₂ - θ₁ + π / 2) / π) * (2 - κ / 2) =
      (4 - κ) / 2 + (θ₂ - θ₁) * (4 - κ) / (2 * π) := by
    field_simp
    ring
  rw [e]
  have : κ / 2 ≤ (θ₂ - θ₁) * (4 - κ) / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **`Prop51G.FwdNoContactQStatement` holds** (PROVE-PROP51G's large-gap input): at and above the critical gap
`θ₂ − θ₁ ≥ πκ/(4 − κ)`, for every positive rational `s`, almost surely the flow line never meets the counterflow hull
`R(K_s)` and tends to the western end of `∞` in the counterflow chart (Aux. lemma 22's empty-span case for the image
word at relative angle `θ₂ − θ₁ + π/2`, read on the glued space of `Cond44Ref.Prop51QStatement`). -/
theorem fwdNoContactQStatement : FwdNoContactQStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  obtain ⟨h', 𝓕, W, VL, VR, B, htrans, hC, htr⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htrans ω)
  set θ := θ₂ - θ₁ + π / 2 with hθdef
  have hXeq : (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = fun ω => cfFieldT κ θ (h' ω) := by
    funext ω
    rw [hh', cfField_flowField_eq_cfFieldT κ θ₁ θ₂]
  have hμ : glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)) =
      glueMeasure P k (fun ω => cfFieldT κ θ (h' ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) := by
    congr 1
  have hlaw' : P.map (fun ω => cfFieldT κ θ (h' ω)) = P₂.map h₂ := by rw [← hXeq]; exact hlaw
  have hθb : CfThetaBounds κ θ _ _ _ _ :=
    cfThetaBounds_prop74 (a := a) (b := b) (θ₁ := θ₁) (θ₂ := θ₂) hκ hb (by linarith)
  rw [hμ]
  have hseed₀ : ∃ i₀, flowLineXL (Sec7.prop74Data a b) {0} 0 i₀ = 0 := ⟨_, Sec4.flowLineXL_zero _ _⟩
  have hnc := ae_noContactT hκ hκ4 (by linarith) (charge_bound_of_isLargeGap hκ4 hG) hF h44 hseed₀ hθb hC hcf
    hlaw' k hk hs
  -- the flow line is the coupling's seed line
  have hseed : ∀ᵐ ω ∂P, seedLine ζ W ω = fun u : ℝ => η ω u.toNNReal := by
    filter_upwards [ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1, htr, hC.1.2.2.2.2] with ω hω ht hp
    obtain ⟨hζ, -, -⟩ := hω
    have e : (fun t => η ω t - ((0 : ℝ) : ℂ)) = η ω := by
      funext t
      simp
    rw [e] at ht
    exact seedLine_eq_of_isGeneratingTrace hζ hp.2.2.2.1 hp.1 ht
  have hseedG := ae_glue_fst (μ := P) k ((measurable_cfFieldT κ θ).comp hC.2.1) hseed
  filter_upwards [hnc, hseedG] with p hp hps
  rw [hps] at hp
  exact ⟨hp.1, junL (cfDrv p.2) s, hp.2.1, hp.2.2⟩

/-- **Proposition 5.1 in the chart `Q` at and above the critical gap**, from the counterflow's regularity alone. -/
theorem prop51QOn_largeGap_of_reg (hreg : Prop51Q.CfLineRegularQStatement.{u}) : Prop51QOn.{u} IsLargeGap :=
  prop51QOn_largeGap hreg fwdNoContactQStatement

/-- **Proposition 5.1 in the chart `Q` at and above the critical gap**, from Zhan's Part A inputs at `16/κ`. -/
theorem prop51QOn_largeGap_of_partA (hA : PartAInputsSixteenDiv) : Prop51QOn.{u} IsLargeGap :=
  prop51QOn_largeGap_of_reg (CfLineRegQ.cfLineRegularQStatement_of_partA hA)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs, the no-wrap topology and the post-contact barrier**
(PROVE-PROP51G's `prop51QStatement_of_partA_of_fwd_post` with its large-gap input `FwdNoContactQStatement` discharged).
-/
theorem prop51QStatement_of_partA_of_post (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_fwd_post hA htopo hpost fwdNoContactQStatement

/-- **Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from Zhan's Part A inputs, the no-wrap topology and
the post-contact barrier** (the large-gap input discharged). -/
theorem cfFirstContactQStatement_of_partA_of_post (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hpost : FwdPostContactQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_partA_of_fwd_post hA htopo hpost fwdNoContactQStatement

end NoContact

end InteractingSLE.Sec5.Prop51H
