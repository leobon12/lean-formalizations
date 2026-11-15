/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71NProb

/-!
# Lemma 7.1: `IsPocketChartData` from the inherited branch and the side limits along the middle curve

Packet PROVE-LEMMA71N (specification Remark 6.7, `source/spec/p145-192.md` L566–L590; Lemma 7.1,
`source/spec/p193-240.md` L576–L606). PROVE-LEMMA71M reduced Lemma 7.1's `IsPocketChartData` to the side limits of the
active pocket component (`Lemma71M.isPocketChartData_of_sideLimit`, hypothesis `hside`). This file proves `hside` on
the outer arcs and isolates the two remaining inputs:

* `capTime_le_visit`, `mem_image_of_mem_prefix`: the capacity stopping time is at most the visit-clock time of the
  capacity inverse, so a point of the stopped middle prefix in the closed pocket is mapped by the boundary map into the
  mapped prefix up to the capacity time;
* `PocketCurveSide`: the side limits along the middle curve (the first alternative of `Lemma71M.PocketSideLimit` at the
  chart points of `(L_t − W_t, 0) ∪ (0, R_t − W_t)`);
* `pocketSideLimit_of_curveSide`: `Lemma71M.PocketSideLimit` with the exceptional set `{L_t − W_t, 0, R_t − W_t}` from
  the outer side limits (`arc_sideLimit`) and `PocketCurveSide` (pathwise);
* `cpf2_heights`: the CPF2 heights `λ(−1 − ρ^L) = λ − θ₂χ`, `λ(1 + ρ^R) = −λ − θ₁χ`;
* **`isPocketChartData_of_curveSide`**: `Lemma72B.IsPocketChartData` (chart `shiftLift (c ω) (n ω)`, `a = 0`, `k = χ`)
  from a `σ(β, α)`-measurable branch shift that is almost surely the inherited branch (`IsPocketBranch`) and the side
  limits along the middle curve; the outer arcs are proved (`ae_outerSideLimit`).

Conditional helper (on the branch, the middle-curve side limits and the §4.2 reference of the three-curve space); it
replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71N

open QuantumZipper (H Hbar chiC)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71C Lemma71K Lemma71L Sec6 LocalSets

/-! ### The stopped middle prefix in the pocket chart -/

section Geom

variable {Ω : Type*} {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

/-- **The capacity stopping time is at most the visit-clock time of the capacity inverse** (`0` at `t = 0`, the clock
time otherwise; the argument of `Lemma71L.connectedComponentIn_eq_image`). -/
theorem capTime_le_visit {ω : Ω} (hg : PocketGood β α γ C c γ' ω) (hCo : IsOpen (C ω)) (hCH : C ω ⊆ H)
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = C ω) (hγH : ∀ t, γ ω t ∈ Hbar)
    (hγc : Continuous (γ ω)) (hΓ : IsSegCurve (γ' ω))
    (hMiff : ∀ z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) (hGeq : ∀ z ∈ C ω, G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : Y (outerHist β α ω) = closePt α C ω) {t : ℝ≥0} (htl : (t : ℝ≥0∞) < capLife (γ' ω)) :
    capTime G M Y β α γ t ω ≤ ENNReal.ofReal (visitClock (γ ω) (closure (cayley '' C ω)) (capInv (γ' ω) t)) := by
  obtain ⟨hvc, -, -, hD1, -⟩ := hg.visit hCo hCH hc hdom hγH
  rw [← hYeq] at hD1
  have hFc : ContinuousOn (c ω).1 (C ω) := by rw [← hdom]; exact hc.differentiableOn_fwd.continuousOn
  have htl' : ENNReal.ofReal (t : ℝ) < capLife (γ' ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  show capRule G M Y (ENNReal.ofReal (2 * (t : ℝ))) (outerHist β α ω) (pathCoord (γ ω)) ≤ _
  rcases eq_or_lt_of_le (zero_le (a := t)) with ht0 | ht0
  · rw [← ht0, NNReal.coe_zero, mul_zero, ENNReal.ofReal_zero, capRule_zero_eq ((hD1 0 le_rfl).mono bot_le)]
    exact zero_le (a := _)
  · exact (capRule_eq_visitClock hMiff hGeq hCo hFc hγc hΓ hvc hD1 (NNReal.coe_pos.2 ht0) htl').le

/-- **A point of the stopped middle prefix in the closed pocket is mapped by the boundary map into the mapped prefix up
to the capacity time** (the visit clock is strictly increasing). -/
theorem mem_image_of_mem_prefix {ω : Ω} (hg : PocketGood β α γ C c γ' ω) (hCo : IsOpen (C ω)) (hCH : C ω ⊆ H)
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = C ω) (hγH : ∀ t, γ ω t ∈ Hbar)
    (hγc : Continuous (γ ω)) (hγi : Function.Injective (γ ω)) (hΓ : IsSegCurve (γ' ω))
    (hMiff : ∀ z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) (hGeq : ∀ z ∈ C ω, G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : Y (outerHist β α ω) = closePt α C ω) {t : ℝ≥0} (htl : (t : ℝ≥0∞) < capLife (γ' ω))
    {Ψ : ℂ → ℂ} {b' : ℝ} (hΨi : InjOn Ψ (closure (cayley '' C ω) \ {wallPt (α ω) b'}))
    (hseg : ∀ u, 0 ≤ u → segPt (γ ω) (closure (cayley '' C ω)) u ∈ closure (cayley '' C ω) \ {wallPt (α ω) b'} ∧
      γ' ω u = Ψ (segPt (γ ω) (closure (cayley '' C ω)) u))
    (hrange : γ' ω '' Ici 0 = Ψ '' (cayley '' range (γ ω) ∩ (closure (cayley '' C ω) \ {wallPt (α ω) b'})))
    {z : ℂ} (hzK : z ∈ closure (cayley '' C ω) \ {wallPt (α ω) b'}) (hz1 : z ≠ 1)
    (hzΓ : cayleyInv z ∈ γ ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ capTime G M Y β α γ t ω}) :
    Ψ z ∈ γ' ω '' Icc 0 (capInv (γ' ω) t) := by
  obtain ⟨hvc, hcay, -, -, -⟩ := hg.visit hCo hCH hc hdom hγH
  obtain ⟨-, hκm, hκ0, -, -, -⟩ := hvc
  set κ := visitClock (γ ω) (closure (cayley '' C ω)) with hκdef
  set U := capInv (γ' ω) t with hUdef
  have htl' : ENNReal.ofReal (t : ℝ) < capLife (γ' ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  have hU0 : 0 ≤ U := (hΓ.capInv_spec t.coe_nonneg htl').1
  obtain ⟨s, hs, hsz⟩ := hzΓ
  have hzc : cayley (γ ω s) = z := by rw [hsz]; exact QuantumZipper.CA.cayley_cayleyInv hz1
  have hΨmem : Ψ z ∈ γ' ω '' Ici 0 := by
    rw [hrange]; exact ⟨z, ⟨⟨γ ω s, ⟨s, rfl⟩, hzc⟩, hzK⟩, rfl⟩
  obtain ⟨v, hv0, hvz⟩ := hΨmem
  obtain ⟨hsegK, hsegΨ⟩ := hseg v hv0
  have hsegz : segPt (γ ω) (closure (cayley '' C ω)) v = z := hΨi hsegK hzK (by rw [← hsegΨ, hvz])
  have hγeq : γ ω (κ v).toNNReal = γ ω s := by
    have h1 := hcay v hv0
    rw [hsegz, ← hzc] at h1
    have h2 := congrArg cayleyInv h1
    rwa [WangWu.cayleyInv_cayley_of_mem_Hbar (hγH _), WangWu.cayleyInv_cayley_of_mem_Hbar (hγH _)] at h2
  have hκvs : (κ v).toNNReal = s := hγi hγeq
  have hτle := capTime_le_visit hg hCo hCH hc hdom hγH hγc hΓ hMiff hGeq hYeq htl
  have hκU : 0 ≤ κ U := hκ0.trans (hκm.monotoneOn self_mem_Ici hU0 hU0)
  have hsle : (s : ℝ) ≤ κ U := by
    have h3 := (show (s : ℝ≥0∞) ≤ _ from hs).trans hτle
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hκU] at h3
  have hκv0 : 0 ≤ κ v := hκ0.trans (hκm.monotoneOn self_mem_Ici hv0 hv0)
  have hκvU : κ v ≤ κ U := by
    rw [← Real.coe_toNNReal _ hκv0, hκvs]; exact hsle
  exact ⟨v, ⟨hv0, (hκm.le_iff_le hv0 hU0).1 hκvU⟩, hvz⟩

end Geom

/-! ### The side limits from the arcs and the middle curve -/

section Side

open Lemma71M

/-- **The side limits of the active component along the middle curve** (the first alternative of
`Lemma71M.PocketSideLimit`, Remark 6.7: "On each boundary side incident to the active component, compare `A(τ) ⊆ A`
using Proposition 3.8 … The full-curve mean on that side is the mean of the appropriate adjacent pair"): at every
chart point `x` strictly between the image `xL` of `0⁻` and `0`, or between `0` and the image `xR` of `0⁺`, the
inverse chart lands at a point `p` of `A ∪ ℝ` near which the full union `AL` lies in `A`, and `vL + u₀ − Gl → 0`. -/
def PocketCurveSide (A AL : Set ℂ) (vL u₀ : ℂ → ℝ) (Finv : ℂ → ℂ) (Gl : ℂ → ℝ) (xL xR : ℝ) : Prop :=
  ∀ x : ℝ, (xL < x ∧ x < 0) ∨ (0 < x ∧ x < xR) → ∃ p : ℂ, Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝 p) ∧
    p ∈ A ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, AL ∩ ball p r ⊆ A) ∧
    Tendsto (fun y => vL (Finv y) + u₀ (Finv y) - Gl y) (𝓝[H] (x : ℂ)) (𝓝 0)

/-- **The side limits of the active component** (`Lemma71M.PocketSideLimit`, with the three exceptional chart points
`xL`, `0`, `xR`) from the outer side limits of the pocket chart (`arc_sideLimit`) and the side limits along the middle
curve (`PocketCurveSide`). Pathwise. -/
theorem pocketSideLimit_of_curveSide {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {b : ℂ} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = C) (hCH : C ⊆ H) (hbC : b ∉ cayley '' C)
    (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {b})) (hΨi : InjOn Ψ (closure (cayley '' C) \ {b}))
    (hΨtop : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {b}] b) atTop)
    (hΨe : ∀ x ∈ C, c.1 x = Ψ (cayley x)) (h1 : (1 : ℂ) ∉ closure (cayley '' C) \ {b})
    {γ' : ℝ → ℂ} (hΓ : IsSegCurve γ') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < capLife γ')
    {A AL AT Γ : Set ℂ} (hΓc : IsCompact Γ) (hA : A ⊆ AT ∪ Γ) (hfr : frontier C ∩ H ⊆ AT)
    (hΓK : ∀ z ∈ closure (cayley '' C) \ {b}, cayleyInv z ∈ Γ → Ψ z ∈ γ' '' Icc 0 (capInv γ' t))
    (κ : ℝ) (ρL ρR : Fin 1 → ℝ) {vL vR : Fin 1 → ℝ≥0 → ℝ}
    (hvL : vL 0 t = -MartChar.RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver γ' s) s) 0 t)
    (hvR : vR 0 t = MartChar.RealFlow.rightImg (Ito.rpath fun s => segDriver γ' s) 0 t) (a' : ℝ)
    {vLh vT u₀ : ℂ → ℝ}
    (hOS : OuterSideLimit c vT u₀ (chiC κ) (sleLambda κ * (-1 - ρL 0) - a') (sleLambda κ * (1 + ρR 0) - a'))
    (hcurve : PocketCurveSide A AL vLh u₀ (pocketInv c (fun s => segDriver γ' s) t)
      (pocketGl κ ρL ρR c (fun s => segDriver γ' s) vL vR t a') (vL 0 t - segDriver γ' t)
      (vR 0 t - segDriver γ' t)) :
    ∃ Ex : Set ℝ, Ex.Finite ∧ PocketSideLimit A AL AT vLh vT u₀ (pocketInv c (fun s => segDriver γ' s) t)
      (pocketGl κ ρL ρR c (fun s => segDriver γ' s) vL vR t a') Ex := by
  refine ⟨{vL 0 t - segDriver γ' t, 0, vR 0 t - segDriver γ' t}, (((finite_singleton _).insert _).insert _),
    fun x hx => ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
  obtain ⟨hxL, hx0, hxR⟩ := hx
  by_cases harc : x < vL 0 t - segDriver γ' t ∨ vR 0 t - segDriver γ' t < x
  · obtain ⟨p, hp, h2, h3, h4⟩ := arc_sideLimit hc hdom hCH hbC hΨc hΨi hΨtop hΨe h1 hΓ ht hΓc hA hfr hΓK κ ρL ρR
      hvL hvR a' hOS harc
    exact ⟨p, hp, Or.inr ⟨h2, h3, h4⟩⟩
  · push Not at harc
    have hmid : (vL 0 t - segDriver γ' t < x ∧ x < 0) ∨ (0 < x ∧ x < vR 0 t - segDriver γ' t) := by
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · exact Or.inl ⟨lt_of_le_of_ne harc.1 (Ne.symm hxL), hneg⟩
      · exact Or.inr ⟨hpos, lt_of_le_of_ne harc.2 hxR⟩
    obtain ⟨p, hp, h2, h3, h4⟩ := hcurve x hmid
    exact ⟨p, hp, Or.inl ⟨h2, h3, h4⟩⟩

end Side

/-! ### `IsPocketChartData` from the branch and the middle-curve side limits -/

section Main

open MartChar Lemma71M Lemma71E Lemma71D Coupling Lemma71G

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}
  {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

/-- The CPF2 heights in the chart: `λ(−1 − ρ^L) = λ − θ₂χ` and `λ(1 + ρ^R) = −λ − θ₁χ`. -/
theorem cpf2_heights (hκ : 0 < κ) (θ₁ θ₂ : ℝ) :
    sleLambda κ * (-1 - cpf2RhoL κ θ₂) - 0 = sleLambda κ - θ₂ * chiC κ ∧
      sleLambda κ * (1 + cpf2RhoR κ θ₁) - 0 = -sleLambda κ - θ₁ * chiC κ := by
  have hlam : sleLambda κ ≠ 0 := (div_pos Real.pi_pos (Real.sqrt_pos.2 hκ)).ne'
  constructor <;> simp only [cpf2RhoL, cpf2RhoR] <;> field_simp <;> ring

/-- **`IsPocketChartData` from the inherited branch and the side limits along the middle curve** (Lemma 7.1's last
input, `Lemma71M.isPocketChartData_of_sideLimit`'s `hside`, with the outer arcs proved). On every three-curve space with
the pocket construction of PROVE-LEMMA71K and the capacity data of PROVE-LEMMA71L: if the branch shift `n` is
`σ(β, α)`-measurable and almost surely the inherited branch (`IsPocketBranch`), and at every capacity time `t`, for
every version `gL` of the mean of the complete three curves, almost surely on `{t < capLife}` the active component has
the side limits along the middle curve (`PocketCurveSide`) for all harmonic representatives of `gL`, then
`Lemma72B.IsPocketChartData` holds with the chart `shiftLift (c ω) (n ω)`, `a = 0`, `k = χ`. The side limits along the
outer arcs (the second alternative of `PocketSideLimit` at every chart point outside `[L_t − W_t, R_t − W_t]`) are
proved here (`ae_outerSideLimit`, `arc_sideLimit`). The named input `Lemma71H.Cond44ReferenceStatement` is that of the
three-curve space itself. Conditional helper (on the branch and the middle-curve side limits). -/
theorem isPocketChartData_of_curveSide [IsProbabilityMeasure P] (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n)
    (hN : ∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω))
    (hcurve : ∀ (t : ℝ≥0) (gL : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        PocketCurveSide (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) vL u₀
          (pocketInv (Lemma71E.shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
          (pocketGl κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
            (Lemma71E.shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t 0)
          (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t)
          (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t)) :
    Lemma72B.IsPocketChartData κ θ₁ θ₂ P β α γ h
      (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
      γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => Lemma71E.shiftLift (c ω) (n ω)) 0
      (chiC κ) := by
  refine isPocketChartData_of_sideLimit hS hpc hG hM hY hMiff hGeq hYeq hn (a' := 0) fun t gL gT hgL hgT => ?_
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, hγ62, hae⟩ := hS'
  obtain ⟨hc3, -, him3, -, -, -, -⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, hbetw, hfr, hsegc, -, hmark⟩ := hpc'
  obtain ⟨hhL, hhR⟩ := cpf2_heights hκ θ₁ θ₂
  filter_upwards [ae_outerSideLimit href hκ hκ4 hθ₁ hθ₂ ha hb hS hpc hN hgT, hcurve t gL hgL, hae, hbetw, hfr,
    hmark] with ω hOSω hcv hω hbω hfrω hmω htl vL vT hvL hgvL hvT hgvT
  obtain ⟨-, -, -, -, -, -, hβα, hsβ, hsα, hsγ, hord, hγα, hγβ⟩ := hω
  obtain ⟨a', b', Ψ, hMk, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hseg, hrange⟩ := hmω
  have hg : PocketGood β α γ C c γ' ω :=
    ⟨hord, hγα, hγβ, hbω, hfrω, a', b', Ψ, hMk, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hseg⟩
  have hF : IsPocketFrame (β ω) (α ω) (C ω) (c ω) Ψ a' b' :=
    ⟨hsβ, hsα, hβα, hbω, hMk, hconf ω, hdom ω, hΨc, hΨi, hΨH, hΨ0, hΨtop, hΨe, hfrω⟩
  have hCo : IsOpen (C ω) := (hC ω).1
  have hCH : C ω ⊆ H := (hC ω).2.2.2
  have hγc : Continuous (γ ω) := hc3 2 ω
  have hγH : ∀ t, γ ω t ∈ Hbar := fun t => him3 2 ω t
  -- the sets
  set τ := capTime G M Y β α γ t ω with hτdef
  have hAT : explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω =
      (range (β ω) ∪ range (α ω)) ∩ H := Three.explored_threeOuter β α γ ω (by rw [hsγ.2.2.1]; simp)
  have hA := Three.explored_threeStops β α γ (capTime G M Y β α γ t) ω
  set Γ : Set ℂ := γ ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ τ} with hΓdef
  have hτle := capTime_le_visit hg hCo hCH (hconf ω) (hdom ω) hγH hγc (hsegc ω) (hMiff ω) (hGeq ω) (hYeq ω) htl
  have hΓc : IsCompact Γ := by
    refine (Metric.isCompact_of_isClosed_isBounded (isClosed_le ENNReal.continuous_coe continuous_const)
      ((Metric.isBounded_Icc (0 : ℝ≥0)
        (visitClock (γ ω) (closure (cayley '' C ω)) (capInv (γ' ω) t)).toNNReal).subset fun s hs => ?_)).image hγc
    refine ⟨zero_le (a := s), ?_⟩
    have h3 := (show (s : ℝ≥0∞) ≤ τ from hs).trans hτle
    rw [ENNReal.ofReal] at h3
    exact_mod_cast h3
  have hAsub : explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω ⊆
      explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω ∪ Γ := by
    rw [hA, hAT]
    rintro z ⟨(hz | hz) | hz, hzH⟩
    · exact Or.inl ⟨Or.inl hz, hzH⟩
    · exact Or.inl ⟨Or.inr hz, hzH⟩
    · exact Or.inr hz
  have hfr' : frontier (C ω) ∩ H ⊆ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω := by
    rw [hAT]; exact fun z hz => ⟨hfrω hz, hz.2⟩
  have hΓK : ∀ z ∈ closure (cayley '' C ω) \ {wallPt (α ω) b'}, cayleyInv z ∈ Γ →
      Ψ z ∈ γ' ω '' Icc 0 (capInv (γ' ω) t) := fun z hzK hzΓ =>
    mem_image_of_mem_prefix hg hCo hCH (hconf ω) (hdom ω) hγH hγc hsγ.2.1 (hsegc ω) (hMiff ω) (hGeq ω) (hYeq ω) htl
      hΨi hseg hrange hzK (fun h1 => hF.one_notMem (h1 ▸ hzK)) hzΓ
  have hOS : OuterSideLimit (Lemma71E.shiftLift (c ω) (n ω)) vT u₀ (chiC κ)
      (sleLambda κ * (-1 - (fun _ : Fin 1 => cpf2RhoL κ θ₂) 0) - 0)
      (sleLambda κ * (1 + (fun _ : Fin 1 => cpf2RhoR κ θ₁) 0) - 0) := by
    simp only
    rw [hhL, hhR]
    exact hOSω vT hvT hgvT
  have hvL' : (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω) 0 t =
      -RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver (γ' ω) s) s) 0 t := by
    simp only [geomL, LP.twoSeedXL, neg_zero]
    rfl
  have hvR' : (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) 0 t =
      RealFlow.rightImg (Ito.rpath fun s => segDriver (γ' ω) s) 0 t := by
    simp only [geomR, LP.twoSeedXR]
    rfl
  exact pocketSideLimit_of_curveSide (isConformal_shiftLift (hconf ω) (n ω)) (hdom ω) hCH hF.closePt_notMem hΨc hΨi
    hΨtop hΨe hF.one_notMem (hsegc ω) htl hΓc hAsub hfr' hΓK κ _ _ hvL' hvR' 0 hOS (hcv htl vL hvL hgvL)

end Main

/-! ### The two remaining inputs as named statements -/

section Named

open MartChar Lemma71M Lemma71E Lemma71D Coupling Lemma71G

/-- **Named input (N): the inherited branch of Lemma 7.1's pocket chart** (supplement §2.3, "Deterministic
normalization lemma", (2); Lemma 7.1's proof, p. 225: "with the inherited logarithmic-derivative branch"). On every
pocket construction over a three-curve space there is a `σ(β, α)`-measurable branch shift that is almost surely the
inherited branch (`IsPocketBranch`). -/
def PocketBranchStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ a b : ℝ, θ₁ < 0 → 0 < θ₂ →
    sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a → sleLambda κ - θ₁ * chiC κ ≤ b →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ →
    ∀ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ), IsPocketConstruction P β α γ C c γ' →
    ∃ n : Ω → ℤ, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n ∧
      ∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω)

/-- **Named input (CS): the side limits of the active component along the middle curve** (Remark 6.7: "On each
boundary side incident to the active component, compare `A(τ) ⊆ A` using Proposition 3.8 … The full-curve mean on that
side is the mean of the appropriate adjacent pair. Contacts with the other outer curve cause no extra exception, since
that curve avoids the relevant component and Proposition 3.9 removes it"), for the inherited branch: on every pocket
construction over a three-curve space with capacity data, for every branch shift that is almost surely the inherited
branch, at every capacity time `t` and for every version `gL` of the mean of the complete three curves, almost surely on
`{t < capLife}` and for all harmonic representatives of `gL`, `PocketCurveSide` holds. -/
def PocketCurveSideStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ a b : ℝ, θ₁ < 0 → 0 < θ₂ →
    sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a → sleLambda κ - θ₁ * chiC κ ≤ b →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ →
    ∀ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ), IsPocketConstruction P β α γ C c γ' →
    ∀ (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ),
      Measurable G → MeasurableSet M → Measurable Y → (∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) →
      (∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z) → (∀ ω, Y (outerHist β α ω) = closePt α C ω) →
    ∀ n : Ω → ℤ, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n →
      (∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω)) →
    ∀ (t : ℝ≥0) (gL : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL →
      ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∀ vL : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
        (∀ ψ : TestOn upperHalfPlaneOpens,
          tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
        PocketCurveSide (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) vL u₀
          (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
          (pocketGl κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
            (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s)
            (fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω)
            (fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω) t 0)
          (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t)
          (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t)

/-- **Lemma 7.1's `IsPocketChartData` on every pocket construction over a three-curve space, from the named inputs**
(N) and (CS) and the §4.2 reference: there is a `σ(β, α)`-measurable branch shift `n` with
`Lemma72B.IsPocketChartData` for the chart `shiftLift (c ω) (n ω)`, `a = 0`, `k = χ`. Conditional helper. -/
theorem exists_isPocketChartData_of_named (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hB : PocketBranchStatement.{u}) (hCS : PocketCurveSideStatement.{u}) {κ θ₁ θ₂ a b : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ}
    {ζβ ζα ζγ : Ω → ℝ≥0∞} (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ} (hpc : IsPocketConstruction P β α γ C c γ') :
    ∃ n : Ω → ℤ, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n ∧
      Lemma72B.IsPocketChartData κ θ₁ θ₂ P β α γ h
        (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
          (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
        γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) 0
        (chiC κ) := by
  obtain ⟨n, hn, hN⟩ := hB κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc
  obtain ⟨G, M, Y, hG, hM, hY, hMiff, hGeq, hYeq⟩ := exists_capData hS hpc
  exact ⟨n, hn, isPocketChartData_of_curveSide href hκ hκ4 hθ₁ hθ₂ ha hb hS hpc hG hM hY hMiff hGeq hYeq hn hN
    (hCS κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq n hn hN)⟩

end Named

end InteractingSLE.Sec7.Lemma71N
