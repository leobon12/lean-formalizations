/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2FbReduce
import InteractingSLE.Spec.Supplement.GW2FbConfig
import InteractingSLE.Spec.Supplement.GW2RdShift
import InteractingSLE.Spec.Supplement.GB6RelDetGood
import InteractingSLE.Spec.Supplement.GW2JDetCode

/-!
# GW2's relative determination, part 1: the hull identity from stopped matches before an end time

Packet PROVE-GW2-RELDET. GB6's last deterministic step (`GB6.RelDrv.drvDec_eq_of_isStopDrvMatch_family` with
`GB6.exists_relDriver_of_traces`, `GB6.fwdHull_relClock_eq_of_agree`) assumes an explored curve of infinite lifetime.
GW2's explored curve is a flow line that may reach a continuation threshold at a finite time `ζα`. Here the step is
proved before the END TIME `min(ζα, T_c)` (`T_c` the first contact of the flow line with the inverted counterflow
prefix), by freezing the flow before its lifetime (`GW2Fb.exists_frozen_generatingTrace`):

* **`fwdHull_drvDec_eq_of_family`** (deterministic, one sample): a good code `p`, stopped drivers `R m` matched by
  `p` up to `V m`, generating the chart images of the flow hulls in the relative clock while the clock is below
  `V m`, and exhausting the relative clock of every time before `min(ζα, T_c)`, give the hull identity
  `K^p_{a(t)} = Ψ(K^α_t)` for every `t < min(ζα, T_c)`;
* **`ae_isGoodDrvCode_ret_theta`**: GB6's good-code clause with the explored code at any angle `θ′`
  (`ae_isGoodDrvCode_gb6` for `θ′ = 0`), from Theorems 1.2–1.3 at universe `0`
  (`GW2JDet.ae_isGoodDrvCode_of_isGFF_theta`).
  No `κ < 4`: it holds for every retained parameter `k > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Sec2.Assembly Exist.Staged Exist.StagedLaw Sec7.StripSysField Supp8.GB6 Supp8.GB6.RelDrv

/-! ### The hull identity before an end time (one sample) -/

/-- **The decoded code generates the chart images of the flow hulls before `min(ζα, T_c)`.** Retained curve: a
continuous driver `w` from `0` with a generating trace `γ` on `[0, ∞)` and an interior tip `γ(s)`. Explored curve:
a driver `wα` continuous before `Tα` with a generating trace `α` on `[0, Tα]`. If the stopped drivers `R m` are matched
by the good code `p` up to `V m`, generate `Ψ(K^α_t)` at the relative clock `a(t)` whenever `a(t) ≤ V m`, and every
`a(t)` with `t < min(Tα, T_c)` is below some `V m`, then `p` generates `Ψ(K^α_t)` at `a(t)` for every such `t`. -/
theorem fwdHull_drvDec_eq_of_family {p : PCode × ℝ≥0∞} (hp : IsGoodDrvCode p)
    {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    {s : ℝ≥0} (hsH : γ s ∈ H)
    {wα : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace wα Tα α)
    (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    {R : ℕ → ℝ≥0 → ℝ} (hRc : ∀ m, Continuous (R m)) (hR0 : ∀ m, R m 0 = 0) {V : ℕ → ℝ≥0∞}
    (hm : ∀ m, IsStopDrvMatch p (R m) (V m))
    (hRK : ∀ m (t : ℝ≥0), (t : ℝ≥0∞) < Tα →
      (t : ℝ≥0∞) < firstContactTime (fun t => (α t : OnePoint ℂ))
        ((fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s) →
      ENNReal.ofReal (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wα r.toNNReal) t) ≤ V m →
      QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal)
          (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wα r.toNNReal) t) =
        relMap (fun r : ℝ => w r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) t)
    (hexh : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tα →
      (t : ℝ≥0∞) < firstContactTime (fun t => (α t : OnePoint ℂ))
        ((fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s) →
      ∃ m, ENNReal.ofReal (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wα r.toNNReal) t) < V m) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tα →
      (t : ℝ≥0∞) < firstContactTime (fun t => (α t : OnePoint ℂ))
        ((fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => drvDec p r.toNNReal)
          (relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wα r.toNNReal) t) =
        relMap (fun r : ℝ => w r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) t := by
  intro t htα htc
  set Tc := firstContactTime (fun t => (α t : OnePoint ℂ)) ((fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s)
    with hTc
  obtain ⟨t₁, htt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min htα htc)
  have ht₁α : (t₁ : ℝ≥0∞) < Tα := lt_of_lt_of_le ht₁ (min_le_left _ _)
  have ht₁c : (t₁ : ℝ≥0∞) < Tc := lt_of_lt_of_le ht₁ (min_le_right _ _)
  have htt₁' : t < t₁ := by exact_mod_cast htt₁
  obtain ⟨w', α', t₂, ht₁₂, -, hw'c, hw'0, hα', hww, hαα⟩ :=
    GW2Fb.exists_frozen_generatingTrace hα hwα hwα0 ht₁α
  -- the frozen flow is still before its first contact at `t₁`
  have ht₁c' : (t₁ : ℝ≥0∞) < firstContactTime (fun t => (α' t : OnePoint ℂ))
      ((fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s) :=
    GW2Fb.lt_firstContactTime_of_prefix ht₁₂ (fun u hu => by rw [hαα u hu]) ht₁c
  have hcG : firstContactTime (fun t => sphereInv (α' t : OnePoint ℂ)) ((fun u => (γ u : OnePoint ℂ)) '' Icc 0 s) =
      firstContactTime (fun t => (α' t : OnePoint ℂ)) ((fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s) :=
    GW2JDetR4.firstContactTime_sphereInv α' γ s
  have hs : (s : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ⊤} := hw.continuousOn
  obtain ⟨W'', -, ha0, hsm, hW''c, hK⟩ := exists_relDriver_of_traces hγ hwc hw0 hs hsH hα' hw'c hw'0
  obtain ⟨-, -, hac⟩ := relClock_props_of_traces hγ hwc hw0 hs hsH hα' hw'c hw'0
  rw [hcG] at hsm hW''c hK hac
  -- the clocks and the hulls of the frozen flow before `t₂`
  have hhull : ∀ t' : ℝ≥0, t' ≤ t₁ → QuantumZipper.fwdHull (fun r : ℝ => w' r.toNNReal) t' =
      QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) t' := fun t' ht' =>
    fwdHull_eq_of_eqOn t'.coe_nonneg (lt_of_le_of_lt (NNReal.coe_le_coe.2 ht') (NNReal.coe_lt_coe.2 ht₁₂))
      fun r hr => hww r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hclock : ∀ t' : ℝ≥0, t' ≤ t₁ →
      relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t' =
        relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => wα r.toNNReal) t' := fun t' ht' => by
    unfold relClock
    rw [hhull t' ht']
  set a : ℝ≥0 → ℝ := fun t' => relClock (fun r : ℝ => w r.toNNReal) s (fun r : ℝ => w' r.toNNReal) t' with ha
  set K : ℝ≥0 → Set ℂ := fun t' =>
    relMap (fun r : ℝ => w r.toNNReal) s '' QuantumZipper.fwdHull (fun r : ℝ => w' r.toNNReal) t' with hKdef
  have hsub : {t' : ℝ≥0 | (t' : ℝ≥0∞) < (t₁ : ℝ≥0∞)} ⊆
      {t' : ℝ≥0 | (t' : ℝ≥0∞) < firstContactTime (fun t => (α' t : OnePoint ℂ))
        ((fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s)} := fun t' ht' => lt_trans ht' ht₁c'
  have hlt₁ : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < (t₁ : ℝ≥0∞) → t' ≤ t₁ := fun t' ht' => (by exact_mod_cast ht'.le)
  have hlt₁α : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < (t₁ : ℝ≥0∞) → (t' : ℝ≥0∞) < Tα := fun t' ht' => lt_trans ht' ht₁α
  have hlt₁c : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < (t₁ : ℝ≥0∞) → (t' : ℝ≥0∞) < Tc := fun t' ht' => lt_trans ht' ht₁c
  have hRK' : ∀ m (t' : ℝ≥0), (t' : ℝ≥0∞) < (t₁ : ℝ≥0∞) → ENNReal.ofReal (a t') ≤ V m →
      QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal) (a t') = K t' := fun m t' ht' hle => by
    simp only [ha, hKdef, hclock t' (hlt₁ t' ht'), hhull t' (hlt₁ t' ht')] at hle ⊢
    exact hRK m t' (hlt₁α t' ht') (hlt₁c t' ht') hle
  have hexh' : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < (t₁ : ℝ≥0∞) → ∃ m, ENNReal.ofReal (a t') < V m := fun t' ht' => by
    simp only [ha, hclock t' (hlt₁ t' ht')]
    exact hexh t' (hlt₁α t' ht') (hlt₁c t' ht')
  have hW''c' : ContinuousOn W'' {u | ∃ t' : ℝ≥0, (t' : ℝ≥0∞) < (t₁ : ℝ≥0∞) ∧ (u : ℝ) < a t'} :=
    hW''c.mono fun u ⟨t', ht', hu⟩ => ⟨t', hsub ht', hu⟩
  have hK' : ∀ t' : ℝ≥0, (t' : ℝ≥0∞) < (t₁ : ℝ≥0∞) →
      QuantumZipper.fwdHull (fun r : ℝ => W'' r.toNNReal) (a t') = K t' := fun t' ht' => hK t' (hsub ht')
  have hD := drvDec_eq_of_isStopDrvMatch_family hp (fun m => (hRc m)) hR0 hm ha0 (hsm.mono hsub)
    (hac.mono hsub) hRK' hexh' hW''c' hK'
  have hfin := fwdHull_relClock_eq_of_agree ha0 (hsm.mono hsub) hK' hD t htt₁
  simp only [ha, hKdef, hclock t htt₁'.le, hhull t htt₁'.le] at hfin
  exact hfin

/-! ### The good-code clause at any explored angle -/

/-- **GB6's good-code clause with the explored code at an angle `θ′`** (no `κ < 4`). Almost surely on
`{s < ζα, α(s) ∈ ℍ}` the canonical driver code `F` at parameter `16/k`, angle `θ′`, of the conditional field `Hc`
and the conditional word `gb6Word k θ c s Wα` is good. -/
theorem ae_isGoodDrvCode_ret_theta (h12p₀ : Theorem12ParamStatement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    {k θ θ' : ℝ} (hk : 0 < k) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (hfl : IsFlowLineDriver k b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC k)) (chiC (16 / k)) (h ω) (Hc ω))
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode (16 / k) θ' F)
    {c : BoundaryWord} (hcb : ∀ y ∉ J, c.fn y = b y) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsGoodDrvCode (F (gb6Word k θ c s (fun t => Wα t ω), Hc ω)) := by
  have hflc : IsFlowLineDriver k c.fn c.jumps θ P h Wα ζα :=
    (isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData J hcb).2 hfl
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  have hM𝒢 : MeasurableSet[MeasurableSpace.comap (gb6Rec s Wα ζα) inferInstance] (gb6Rec s Wα ζα ⁻¹' gb6TS s) :=
    ⟨gb6TS s, measurableSet_gb6TS s, rfl⟩
  have hMm : MeasurableSet (gb6Rec s Wα ζα ⁻¹' gb6TS s) := hrecm (measurableSet_gb6TS s)
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P (gb6Rec s Wα ζα ⁻¹' gb6TS s) hrecm hHcm
  have hGK := ae_isGFFWithBoundaryData_of_condExp_word hrecm.comap_le hM𝒢 (comap_measurable _)
    (measurable_gb6WordOfRec k θ c) (ae_of_all _ fun ω _ => isSorted_gb6WordOfRec k θ c _) hHcm measurable_id
    hlaw (fun φ => gb6_condDet_r1 hk hG hflc hα s hHcm hHc φ)
  have hE : MeasurableSet
      {p : RecData × DistOn upperHalfPlaneOpens | IsGoodDrvCode (F (gb6WordOfRec k θ c p.1, p.2))} :=
    (hF.1.comp (((measurable_gb6WordOfRec k θ c).comp measurable_fst).prodMk measurable_snd))
      measurableSet_isGoodDrvCode
  have hk' : 0 < 16 / k := div_pos (by norm_num) hk
  have hgood := Sec5.MarkovOther.ae_mem_of_compProd_eq_prod hMm hrecm hHcm hlaw hE (by
    filter_upwards [hGK] with r hr
    exact GW2JDet.ae_isGoodDrvCode_of_isGFF_theta h12p₀ h13₀ hk' hF hr.1 hr.2)
  filter_upwards [hgood, ae_gb6RecGood hfl hα s] with ω hω hg hs hsH
  have hωM : gb6Rec s Wα ζα ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs, hsH⟩
  have hβ : gb6WordOfRec k θ c (gb6Rec s Wα ζα ω) = gb6Word k θ c s (fun t => Wα t ω) := by
    rw [gb6Word, (hg hs).2.1]
  have h1 : IsGoodDrvCode (F (gb6WordOfRec k θ c (gb6Rec s Wα ζα ω), Hc ω)) := hω hωM
  rwa [hβ] at h1

end InteractingSLE.Theorem14.GW2Rd
