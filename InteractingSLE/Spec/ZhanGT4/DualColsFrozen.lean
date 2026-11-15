/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualCols
import InteractingSLE.Spec.ZhanGT4.DualA1Left

/-!
# Zhan's A.1.4, (D12) for one frozen path of the second curve: A8's martingales in the columns

Packet PROVE-ZHAN-GT4-A14. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L407,
R38): "For a time `I ≤ t̄` known at a stopping time `R`, the process `M(R + s, I)`, as long as the hulls remain disjoint
and protected, is a local martingale in `s`. Indeed `K₂(I)` is known at `R`; … the identical calculation (D8), with the
conformal map of `K₂(I)` frozen, applies. … Thus `M*(s, t̄)` is a bounded martingale."

The second curve is a fixed continuous driver `W₂` (one path of it; the whole curve is integrated out later by Fubini).
For a height `y`, its hull `K₂(y) = fwdHull W₂ y` is frozen and the first curve (ordinary `SLE_κ`, driver `√κ B`)
grows: A8 (`martingale_MTilde_stopped`) makes `s ↦ M̃(s ∧ S, y)` a martingale under the hypotheses `FrzMartHyp`. The
density `N(ω, x, y) = M̃(x, y)` (`frzN`) uses image data `(W', a)` chosen per height (`W'y y`, `ay y`), so that one
function serves every rectangle of the same height.

## Main results

* `OwnData.restrict`: the image data up to `T` are image data up to every `T' ∈ (0, T]`;
* `FrzMartHyp.continuous_stopped`, `FrzMartHyp.abs_ell_stopped_le`: the stopped `M̃` has continuous paths and
  `|log M̃| ≤ K` on `[0, S]`;
* **`martingale_colProd_of_frzMartHyp`**: if for every rectangle `i` the A8 hypotheses hold at the height
  `S₂ i ∧ t̄` up to the first curve's exit time `S₁ i`, the closed column product of (D11) for `N = frzN` is a
  bounded continuous martingale;
* **`martingale_colProd_frozen`**, **`martingale_colProd_frozen_left`**: the same from the enclosure data of §A.1.3
  (`exists_frzD10Hyp`, `exists_frzD10Hyp_left`), with a bound uniform in the frozen path: the image data are chosen up
  to the staircase width at each height (`frzWidth`), where the two hulls lie in one enclosure pair, and restricted to
  each rectangle by `OwnData.restrict` (common core `martingale_colProd_frzDens_of`).
-/

set_option autoImplicit false

noncomputable section

open Set Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-! ### Image data restrict to shorter horizons -/

/-- The hulls increase: `K_s ⊆ K_t` for `s ≤ t`. -/
theorem fwdHull_subset_of_le {W : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) : fwdHull W s ⊆ fwdHull W t :=
  fun _ hz => ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal hst)⟩

/-- **The image data up to `T` are image data up to every `T' ∈ (0, T]`.** -/
theorem OwnData.restrict {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T T' : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
    (hT' : 0 < T') (hTT : T' ≤ T) : OwnData W A φ T' a W' where
  cont := h.cont
  zero := h.zero
  pos := hT'
  hull := h.hull
  mapOut := h.mapOut
  disj := h.disj.mono_right (closure_mono (fwdHull_subset_of_le hTT))
  contW' := h.contW'
  a0 := h.a0
  mono := h.mono.mono (Icc_subset_Icc_right hTT)
  contA := h.contA.mono (Icc_subset_Icc_right hTT)
  img := fun t ht => h.img t ⟨ht.1, ht.2.trans hTT⟩
  rate := fun t ht R hR => by
    obtain ⟨h1, h2, h3, h4⟩ := h.rate t ⟨ht.1, ht.2.trans hTT⟩ R hR
    refine ⟨h1, h2, h3, fun δ hδ Rext hd heq => ?_⟩
    obtain ⟨p1, p2, p3⟩ := h4 δ hδ Rext hd heq
    exact ⟨p1, p2, p3.mono (Icc_subset_Icc_right hTT)⟩


/-! ### The stopped `M̃` of A8: continuous paths and bounds -/

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ} {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0}
  {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}

namespace FrzMartHyp

variable (hH : FrzMartHyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

/-- **`|log M̃| ≤ K` along the driver on `[0, S]`**, `K = 2 · coefTot κ rr · scaleBound L`. -/
theorem abs_ell_le (hκ : 0 < κ) (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ω : Ω) {x : ℝ} (hx : x ∈ Icc 0 (S ω : ℝ)) :
    |(frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell x ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).W x)| ≤
      2 * coefTot κ rr * scaleBound L :=
  (isDriverLogField_frozen hκ hBm hBc hS hH).abs_le (hH.cutRad_pos ω) ω hx

/-- **The stopped `M̃` has continuous paths.** -/
theorem continuous_stopped (hκ : 0 < κ) (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ω : Ω) :
    Continuous fun t : ℝ≥0 => Real.exp ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell ((min t (S ω) : ℝ≥0) : ℝ)
      ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).W ((min t (S ω) : ℝ≥0) : ℝ))) := by
  have hc := (isDriverLogField_frozen hκ hBm hBc hS hH).continuousOn_driver hBc (hH.cutRad_pos ω) ω
  have hm : Continuous fun t : ℝ≥0 => ((min t (S ω) : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hmaps : ∀ t : ℝ≥0, ((min t (S ω) : ℝ≥0) : ℝ) ∈ Icc 0 (S ω : ℝ) := fun t =>
    ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩
  exact Real.continuous_exp.comp (hc.comp_continuous hm hmaps)

end FrzMartHyp

end Stopped

/-! ### The column product of the frozen-height densities -/

section Core

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {n : ℕ}

/-- **The density `N(ω, x, y) = M̃(x, y)`** with the second curve frozen at height `y`: A7's `exp ℓ` of the frozen data
of height `y` (image data `W'y y`, `ay y`, chart `φy y`, tip `ζ₀y y`, marks `ζy y`) along the driver `√κ B`. -/
def frzN (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W'y ay : ℝ → Ω → ℝ → ℝ) (φy : ℝ → ℂ → ℂ) (rr : Fin n → ℝ) (ζ₀y : ℝ → ℝ)
    (ζy : ℝ → Fin n → ℝ) (ω : Ω) (x y : ℝ) : ℝ :=
  Real.exp ((frzDataOf κ B (W'y y) (ay y) (φy y) rr (ζ₀y y) (ζy y) ω).ell x
    ((frzDataOf κ B (W'y y) (ay y) (φy y) rr (ζ₀y y) (ζy y) ω).W x))

theorem frzN_pos (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W'y ay : ℝ → Ω → ℝ → ℝ) (φy : ℝ → ℂ → ℂ) (rr : Fin n → ℝ)
    (ζ₀y : ℝ → ℝ) (ζy : ℝ → Fin n → ℝ) (ω : Ω) (x y : ℝ) : 0 < frzN κ B W'y ay φy rr ζ₀y ζy ω x y :=
  Real.exp_pos _

/-- **The deterministic bound of the column product**: `(e^{K}/e^{−K})^{|ι|}`, `K = ∑_i |2 · coefTot κ rr ·
scaleBound (L i)|` (the (D9) bounds of the rectangles). -/
def colBound {ι : Type*} [Fintype ι] (κ : ℝ) (rr : Fin n → ℝ) (L : ι → ℝ) : ℝ :=
  (Real.exp (∑ i, |2 * coefTot κ rr * scaleBound (L i)|) / Real.exp (-∑ i, |2 * coefTot κ rr * scaleBound (L i)|)) ^
    Fintype.card ι

variable {ι : Type*} [Fintype ι] {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W'y ay : ℝ → Ω → ℝ → ℝ} {φy : ℝ → ℂ → ℂ}
  {rr : Fin n → ℝ} {ζ₀y : ℝ → ℝ} {ζy : ℝ → Fin n → ℝ} {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ}

/-- **(D12) for one frozen path of the second curve, from A8's hypotheses.** If the first curve's exit times `S₁ i`
are stopping times and, for every rectangle `i`, the A8 hypotheses `FrzMartHyp` hold at the height `S₂ i ∧ t̄` (hull of
that height frozen) up to `S₁ i`, then the closed column product of (D11) for `N = frzN` is a martingale with continuous
paths, bounded by a deterministic constant. -/
theorem martingale_colProd_of_frzMartHyp (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0))
    (hS₂ : ∀ i, 0 ≤ S₂ i) (tb : ℝ) (L : ι → ℝ)
    (hH : ∀ i, ∃ (A : Set ℂ) (T : Ω → ℝ) (r a₀ γ Γ lam Tmax : ℝ),
      FrzMartHyp κ B (W'y (min (S₂ i) tb)) (ay (min (S₂ i) tb)) A (φy (min (S₂ i) tb)) rr (ζ₀y (min (S₂ i) tb))
        (ζy (min (S₂ i) tb)) (S₁ i) T r a₀ γ Γ lam (L i) Tmax) :
    Martingale (colProd (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb) 𝓕 P ∧
      (∀ ω t, ContinuousWithinAt (colProd (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb · ω) (Ici t) t) ∧
      ∀ s ω, |colProd (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb s ω| ≤ colBound κ rr L := by
  have hP : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · -- no rectangles: the column product is `1`
    have e : colProd (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb = fun _ _ => 1 := by
      funext s ω
      have hC : colEnds S₁ ω = ∅ := by
        simp only [colEnds, stairCols, Finset.univ_eq_empty, Finset.image_empty]
      simp only [colProd, hC, Finset.prod_empty]
    rw [e]
    exact ⟨martingale_const 𝓕 P 1, fun ω t => continuousWithinAt_const, fun s ω => by
      simp [colBound, Fintype.card_eq_zero]⟩
  choose A T r a₀ γ Γ lam Tmax hHi using hH
  set K : ι → ℝ := fun i => 2 * coefTot κ rr * scaleBound (L i) with hK
  set Kt : ℝ := ∑ i, |K i| with hKt
  have hKi : ∀ i, K i ≤ Kt := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (K j)) (Finset.mem_univ i))
  -- the frozen-height processes are A8's stopped `M̃`
  have hYeq : ∀ i, frzHeightProc (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb i = fun t ω =>
      Real.exp ((frzDataOf κ B (W'y (min (S₂ i) tb)) (ay (min (S₂ i) tb)) (φy (min (S₂ i) tb)) rr
        (ζ₀y (min (S₂ i) tb)) (ζy (min (S₂ i) tb)) ω).ell ((min t (S₁ i ω) : ℝ≥0) : ℝ)
        ((frzDataOf κ B (W'y (min (S₂ i) tb)) (ay (min (S₂ i) tb)) (φy (min (S₂ i) tb)) rr
          (ζ₀y (min (S₂ i) tb)) (ζy (min (S₂ i) tb)) ω).W ((min t (S₁ i ω) : ℝ≥0) : ℝ))) := fun i => by
    funext t ω
    simp only [frzHeightProc, frzN, NNReal.coe_min]
  have hY : ∀ i, Martingale (frzHeightProc (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb i) 𝓕 P := fun i => by
    rw [hYeq i]
    exact martingale_MTilde_stopped hκ hB hBc (hS i) (hHi i)
  have hYrc : ∀ i ω t, ContinuousWithinAt (frzHeightProc (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb i · ω)
      (Ici t) t := fun i ω t => by
    rw [hYeq i]
    exact ((hHi i).continuous_stopped hκ hBm hBc (hS i) ω).continuousAt.continuousWithinAt
  have hYb : ∀ i s ω, Real.exp (-Kt) ≤ frzHeightProc (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb i s ω ∧
      frzHeightProc (frzN κ B W'y ay φy rr ζ₀y ζy) S₁ S₂ tb i s ω ≤ Real.exp Kt := fun i s ω => by
    rw [hYeq i]
    have hb := (hHi i).abs_ell_le hκ hBm hBc (hS i) ω (x := ((min s (S₁ i ω) : ℝ≥0) : ℝ))
      ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩
    have hb' := hb.trans (hKi i)
    rw [abs_le] at hb'
    exact ⟨Real.exp_le_exp.2 hb'.1, Real.exp_le_exp.2 hb'.2⟩
  exact martingale_colProd hS hS₂ i₀ (frzN_pos κ B W'y ay φy rr ζ₀y ζy) tb hY hYrc (Real.exp_pos _) hYb

end Core

/-! ### From the enclosure data of §A.1.3 -/

section Enclosure

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} {n : ℕ} {ι : Type*}
  [Fintype ι]

/-- Sets at positive distance have disjoint closures. -/
theorem disjoint_closure_of_le_norm {X Y : Set ℂ} {ε : ℝ} (hε : 0 < ε) (h : ∀ a ∈ X, ∀ z ∈ Y, ε ≤ ‖a - z‖) :
    Disjoint (closure X) (closure Y) := by
  rw [Set.disjoint_left]
  intro x hxX hxY
  obtain ⟨a, haX, ha⟩ := Metric.mem_closure_iff.1 hxX (ε / 2) (half_pos hε)
  obtain ⟨z, hzY, hz⟩ := Metric.mem_closure_iff.1 hxY (ε / 2) (half_pos hε)
  have h1 := h a haX z hzY
  have h2 : ‖a - z‖ < ε := by
    calc ‖a - z‖ = dist a z := (dist_eq_norm a z).symm
      _ ≤ dist x a + dist x z := dist_triangle_left a z x
      _ < ε / 2 + ε / 2 := add_lt_add ha hz
      _ = ε := add_halves ε
  linarith

/-- The chart of the frozen second curve at height `y`: `g_y = f_y + W₂(y)`. -/
def frzChart (W₂ : ℝ → ℝ) (y : ℝ) (z : ℂ) : ℂ := fwdMap W₂ y z + W₂ y

/-- **The staircase width at height `y`**: `max{S₁ i : y ≤ S₂ i ∧ t̄}` (`0` if there is none). -/
def frzWidth (S₁ : ι → Ω → ℝ≥0) (S₂ : ι → ℝ) (tb y : ℝ) (ω : Ω) : ℝ≥0 :=
  (Finset.univ.filter fun i => y ≤ min (S₂ i) tb).sup fun i => S₁ i ω

open scoped Classical in
/-- **The image data at height `y`**, chosen up to the staircase width (Aux. lemma 8, `exists_ownData`): the capacity
clock `a` and the image driver `W'` of the first curve in the chart of the second curve's hull of height `y`
(`(0, 0)` if there are none). -/
def frzImgSel (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W₂ : ℝ → ℝ) (S₁ : ι → Ω → ℝ≥0) (S₂ : ι → ℝ) (tb y : ℝ) (ω : Ω) :
    (ℝ → ℝ) × (ℝ → ℝ) :=
  if h : ∃ a W', OwnData (drive κ B ω) (fwdHull W₂ y) (frzChart W₂ y) (frzWidth S₁ S₂ tb y ω) a W' then
    (h.choose, h.choose_spec.choose)
  else (0, 0)

theorem frzImgSel_spec {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W₂ : ℝ → ℝ} {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ} {tb y : ℝ}
    {ω : Ω} (h : ∃ a W', OwnData (drive κ B ω) (fwdHull W₂ y) (frzChart W₂ y) (frzWidth S₁ S₂ tb y ω) a W') :
    OwnData (drive κ B ω) (fwdHull W₂ y) (frzChart W₂ y) (frzWidth S₁ S₂ tb y ω)
      (frzImgSel κ B W₂ S₁ S₂ tb y ω).1 (frzImgSel κ B W₂ S₁ S₂ tb y ω).2 := by
  classical
  unfold frzImgSel
  split_ifs
  exact h.choose_spec.choose_spec

/-- The marks of the frozen data at height `y`: `g_y(p_m)` (real parts). -/
def frzMarks (W₂ : ℝ → ℝ) (p : Fin n → ℝ) (y : ℝ) (m : Fin n) : ℝ := (fwdMap W₂ y (p m)).re + W₂ y

/-- **The density of the two-curve coupling with the second curve frozen** (`frzN` with the image data
`frzImgSel`, the chart `frzChart`, the tip `W₂ y` and the marks `frzMarks`). -/
def frzDens (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W₂ : ℝ → ℝ) (S₁ : ι → Ω → ℝ≥0) (S₂ : ι → ℝ) (tb : ℝ) (rr : Fin n → ℝ)
    (p : Fin n → ℝ) : Ω → ℝ → ℝ → ℝ :=
  frzN κ B (fun y ω => (frzImgSel κ B W₂ S₁ S₂ tb y ω).2) (fun y ω => (frzImgSel κ B W₂ S₁ S₂ tb y ω).1)
    (frzChart W₂) rr W₂ (frzMarks W₂ p)

/-- **(D12) for one frozen path of the second curve, from per-rectangle A8 hypotheses for the chosen image data.**
The common core of `martingale_colProd_frozen` and `martingale_colProd_frozen_left`: `hmain i` is the output of
`exists_frzD10Hyp` (or its left form) for the enclosure pair `i`, with the conditions on the frozen driver discharged. -/
theorem martingale_colProd_frzDens_of {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) {H₁ H₂ : ι → Set ℂ} {δ : ι → ℝ} (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i, ∀ a ∈ H₂ i, ∀ z ∈ H₁ i, 2 * δ i ≤ ‖a - z‖) {p : Fin n → ℝ} {Tm : ℝ} (rr : Fin n → ℝ)
    {S₁ : ι → Ω → ℝ≥0} (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0)) (hS₁0 : ∀ i ω, 0 < S₁ i ω)
    (hS₁m : ∀ i ω, (S₁ i ω : ℝ) ≤ Tm) (hK₁ : ∀ i ω, fwdHull (drive κ B ω) (S₁ i ω) ⊆ H₁ i)
    {W₂ : ℝ → ℝ} (hW₂ : Continuous W₂) {S₂ : ι → ℝ} (hS₂0 : ∀ i, 0 < S₂ i) (hS₂m : ∀ i, S₂ i ≤ Tm)
    (hK₂ : ∀ i, fwdHull W₂ (S₂ i) ⊆ H₂ i) {tb : ℝ} (htb : 0 < tb) (L : ι → ℝ)
    (hmain : ∀ i (W' a : Ω → ℝ → ℝ) (t₂ : ℝ) (S : Ω → ℝ≥0) (T : Ω → ℝ),
      (∀ ω, OwnData (drive κ B ω) (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (a ω) (W' ω)) →
      (∀ ω, (S ω : ℝ) ≤ T ω) → (∀ ω, T ω ≤ Tm) → (∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ H₁ i) → 0 < t₂ → t₂ ≤ Tm →
      fwdHull W₂ t₂ ⊆ H₂ i → ∃ (r a₀ γ Γ lam Tmax : ℝ), FrzMartHyp κ B W' a (fwdHull W₂ t₂)
        (fun z => fwdMap W₂ t₂ z + W₂ t₂) rr (W₂ t₂) (fun m => (fwdMap W₂ t₂ (p m)).re + W₂ t₂) S T r a₀ γ Γ lam
        (L i) Tmax) :
    Martingale (colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb) 𝓕 P ∧
      (∀ ω t, ContinuousWithinAt (colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb · ω) (Ici t) t) ∧
      ∀ s ω, |colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb s ω| ≤ colBound κ rr L := by
  classical
  have hdc : ∀ ω, Continuous (drive κ B ω) := fun ω => QuantumZipper.drive_continuous (hBc ω)
  have hd0 : ∀ ω, drive κ B ω 0 = 0 := fun ω => QuantumZipper.drive_zero (hB0 ω)
  set h : ι → ℝ := fun i => min (S₂ i) tb with hh
  have hh0 : ∀ i, 0 < h i := fun i => lt_min (hS₂0 i) htb
  have hK₂' : ∀ i, fwdHull W₂ (h i) ⊆ H₂ i := fun i => (fwdHull_subset_of_le (min_le_left _ _)).trans (hK₂ i)
  -- the image data at the height of each rectangle exist up to the staircase width
  have hex : ∀ i ω, ∃ a W', OwnData (drive κ B ω) (fwdHull W₂ (h i)) (frzChart W₂ (h i))
      (frzWidth S₁ S₂ tb (h i) ω) a W' := fun i ω => by
    have hne : (Finset.univ.filter fun j => h i ≤ min (S₂ j) tb).Nonempty :=
      ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩⟩
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup _ hne fun j => S₁ j ω
    have hij : h i ≤ h j := (Finset.mem_filter.1 hj).2
    have hw : frzWidth S₁ S₂ tb (h i) ω = S₁ j ω := hjeq
    rw [hw]
    refine exists_ownData (hdc ω) (hd0 ω) (NNReal.coe_pos.2 (hS₁0 j ω)) (isHPHull_fwdHull hW₂ (hh0 i).le)
      (isMapOut_fwdMap_gen hW₂ (hh0 i).le) ?_
    exact disjoint_closure_of_le_norm (mul_pos two_pos (hδ j)) fun a ha z hz =>
      hsep j a (hK₂' j (fwdHull_subset_of_le hij ha)) z (hK₁ j ω hz)
  -- the A8 hypotheses for every rectangle
  have hH : ∀ i, ∃ (A : Set ℂ) (T : Ω → ℝ) (r' a₀' γ' Γ' lam' Tmax : ℝ),
      FrzMartHyp κ B (fun ω => (frzImgSel κ B W₂ S₁ S₂ tb (h i) ω).2)
        (fun ω => (frzImgSel κ B W₂ S₁ S₂ tb (h i) ω).1) A (frzChart W₂ (h i)) rr (W₂ (h i))
        (frzMarks W₂ p (h i)) (S₁ i) T r' a₀' γ' Γ' lam' (L i) Tmax := fun i => by
    have hown : ∀ ω, OwnData (drive κ B ω) (fwdHull W₂ (h i)) (fun z => fwdMap W₂ (h i) z + W₂ (h i))
        (S₁ i ω) (frzImgSel κ B W₂ S₁ S₂ tb (h i) ω).1 (frzImgSel κ B W₂ S₁ S₂ tb (h i) ω).2 := fun ω => by
      have hspec := frzImgSel_spec (hex i ω)
      refine hspec.restrict (NNReal.coe_pos.2 (hS₁0 i ω)) (NNReal.coe_le_coe.2 ?_)
      exact Finset.le_sup (f := fun j => S₁ j ω) (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩)
    obtain ⟨r', a₀', γ', Γ', lam', Tmax, hD⟩ := hmain i (fun ω => (frzImgSel κ B W₂ S₁ S₂ tb (h i) ω).2)
      (fun ω => (frzImgSel κ B W₂ S₁ S₂ tb (h i) ω).1) (h i) (S₁ i) (fun ω => (S₁ i ω : ℝ)) hown
      (fun ω => le_rfl) (hS₁m i) (hK₁ i) (hh0 i) ((min_le_left _ _).trans (hS₂m i)) (hK₂' i)
    exact ⟨_, _, _, _, _, _, _, _, hD⟩
  exact martingale_colProd_of_frzMartHyp hκ hB hBc hS (fun i => (hS₂0 i).le) tb L hH

theorem nonempty_of_isFilteredBrownianReal {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P) : Nonempty Ω := by
  have hP : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  by_contra h
  rw [not_nonempty_iff] at h
  have := hP.measure_univ
  rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
  exact zero_ne_one this

/-- **(D12) for one frozen path of the second curve, from the enclosure data of §A.1.3** (second source to the right
of the protected point `q i > 0`). Given enclosure pairs `(H₁ i, H₂ i)` with the separation, protected point and mark
data of `exists_frzD10Hyp` and a time bound `T_m`, there is a constant `K` such that: for a first curve (ordinary
`SLE_κ`, driver `√κ B`) whose exit times `S₁ i ∈ (0, T_m]` are stopping times with `K₁(S₁ i) ⊆ H₁ i`, and **every**
frozen continuous second driver `W₂` from `closure (H₂ i)` with `K₂(S₂ i) ⊆ H₂ i`, `0 < S₂ i ≤ T_m`, and every
`t̄ > 0`, the closed column product of (D11) of `frzDens` is a martingale with continuous paths bounded by `K`
(uniformly in the frozen path). -/
theorem martingale_colProd_frozen {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {H₁ H₂ : ι → Set ℂ} (hH₁ : ∀ i, IsHPHull (H₁ i)) (hH₂ : ∀ i, IsHPHull (H₂ i)) {δ : ι → ℝ}
    (hδ : ∀ i, 0 < δ i) (hsep : ∀ i, ∀ a ∈ H₂ i, ∀ z ∈ H₁ i, 2 * δ i ≤ ‖a - z‖) {q d : ι → ℝ}
    (hd : ∀ i, 0 < d i) (hq : ∀ i, 0 < q i) (hqH : ∀ i, Disjoint (Metric.ball (q i : ℂ) (2 * d i)) (H₁ i ∪ H₂ i))
    {p : Fin n → ℝ} (hpH : ∀ i m, Disjoint (Metric.ball (p m : ℂ) (2 * d i)) (H₁ i ∪ H₂ i))
    (hpinj : Function.Injective p) (Tm : ℝ) (rr : Fin n → ℝ) :
    ∃ K : ℝ, ∀ {S₁ : ι → Ω → ℝ≥0}, (∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0)) →
      (∀ i ω, 0 < S₁ i ω) → (∀ i ω, (S₁ i ω : ℝ) ≤ Tm) → (∀ i ω, fwdHull (drive κ B ω) (S₁ i ω) ⊆ H₁ i) →
      ∀ {W₂ : ℝ → ℝ}, Continuous W₂ → (∀ i, ((W₂ 0 : ℝ) : ℂ) ∈ closure (H₂ i)) → (∀ i, q i < W₂ 0) →
      ∀ {S₂ : ι → ℝ}, (∀ i, 0 < S₂ i) → (∀ i, S₂ i ≤ Tm) → (∀ i, fwdHull W₂ (S₂ i) ⊆ H₂ i) →
      ∀ {tb : ℝ}, 0 < tb →
        Martingale (colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb) 𝓕 P ∧
          (∀ ω t, ContinuousWithinAt (colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb · ω) (Ici t) t) ∧
          ∀ s ω, |colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb s ω| ≤ K := by
  have := nonempty_of_isFilteredBrownianReal hB
  have hconst := fun i => exists_frzD10Hyp (Ω := Ω) (hH₁ i) (hH₂ i) (hδ i) (hsep i) (hd i) (hq i) (hqH i) (hpH i)
    hpinj Tm
  choose r a₀ γ Γ lam L hmain using hconst
  refine ⟨colBound κ rr L, fun {S₁} hS hS₁0 hS₁m hK₁ {W₂} hW₂ hW₂H hqW {S₂} hS₂0 hS₂m hK₂ {tb} htb => ?_⟩
  exact martingale_colProd_frzDens_of hκ hB hBc hB0 hδ hsep rr hS hS₁0 hS₁m hK₁ hW₂ hS₂0 hS₂m hK₂ htb L
    fun i W' a t₂ S T hown hST hTm hK₁' ht₂ ht₂m hK₂' => ⟨_, _, _, _, _, _,
      (hmain i κ B W' a rr W₂ t₂ S T hown hST hTm hK₁' hW₂ (hW₂H i) (hqW i) ht₂ ht₂m hK₂').toFrzMartHyp⟩

/-- **The same with the second source to the left** of the protected point `q i < 0` (`exists_frzD10Hyp_left`). -/
theorem martingale_colProd_frozen_left {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {H₁ H₂ : ι → Set ℂ} (hH₁ : ∀ i, IsHPHull (H₁ i)) (hH₂ : ∀ i, IsHPHull (H₂ i)) {δ : ι → ℝ}
    (hδ : ∀ i, 0 < δ i) (hsep : ∀ i, ∀ a ∈ H₂ i, ∀ z ∈ H₁ i, 2 * δ i ≤ ‖a - z‖) {q d : ι → ℝ}
    (hd : ∀ i, 0 < d i) (hq : ∀ i, q i < 0) (hqH : ∀ i, Disjoint (Metric.ball (q i : ℂ) (2 * d i)) (H₁ i ∪ H₂ i))
    {p : Fin n → ℝ} (hpH : ∀ i m, Disjoint (Metric.ball (p m : ℂ) (2 * d i)) (H₁ i ∪ H₂ i))
    (hpinj : Function.Injective p) (Tm : ℝ) (rr : Fin n → ℝ) :
    ∃ K : ℝ, ∀ {S₁ : ι → Ω → ℝ≥0}, (∀ i, IsStoppingTime 𝓕 fun ω => (S₁ i ω : WithTop ℝ≥0)) →
      (∀ i ω, 0 < S₁ i ω) → (∀ i ω, (S₁ i ω : ℝ) ≤ Tm) → (∀ i ω, fwdHull (drive κ B ω) (S₁ i ω) ⊆ H₁ i) →
      ∀ {W₂ : ℝ → ℝ}, Continuous W₂ → (∀ i, ((W₂ 0 : ℝ) : ℂ) ∈ closure (H₂ i)) → (∀ i, W₂ 0 < q i) →
      ∀ {S₂ : ι → ℝ}, (∀ i, 0 < S₂ i) → (∀ i, S₂ i ≤ Tm) → (∀ i, fwdHull W₂ (S₂ i) ⊆ H₂ i) →
      ∀ {tb : ℝ}, 0 < tb →
        Martingale (colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb) 𝓕 P ∧
          (∀ ω t, ContinuousWithinAt (colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb · ω) (Ici t) t) ∧
          ∀ s ω, |colProd (frzDens κ B W₂ S₁ S₂ tb rr p) S₁ S₂ tb s ω| ≤ K := by
  have := nonempty_of_isFilteredBrownianReal hB
  have hconst := fun i => exists_frzD10Hyp_left (Ω := Ω) (hH₁ i) (hH₂ i) (hδ i) (hsep i) (hd i) (hq i) (hqH i)
    (hpH i) hpinj Tm
  choose r a₀ γ Γ lam L hmain using hconst
  refine ⟨colBound κ rr L, fun {S₁} hS hS₁0 hS₁m hK₁ {W₂} hW₂ hW₂H hqW {S₂} hS₂0 hS₂m hK₂ {tb} htb => ?_⟩
  exact martingale_colProd_frzDens_of hκ hB hBc hB0 hδ hsep rr hS hS₁0 hS₁m hK₁ hW₂ hS₂0 hS₂m hK₂ htb L
    fun i W' a t₂ S T hown hST hTm hK₁' ht₂ ht₂m hK₂' => ⟨_, _, _, _, _, _,
      (hmain i κ B W' a rr W₂ t₂ S T hown hST hTm hK₁' hW₂ (hW₂H i) (hqW i) ht₂ ht₂m hK₂').toFrzMartHyp⟩

end Enclosure

end InteractingSLE.ZhanGT4
