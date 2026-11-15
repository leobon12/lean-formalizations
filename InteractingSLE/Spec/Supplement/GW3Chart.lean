/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem14Inputs
import InteractingSLE.Spec.Jordan.ChartExists
import InteractingSLE.Spec.Jordan.Coupling
import InteractingSLE.Foundations.PrimeEnd.Jordan

/-!
# Lemma GW3, the charts: common-lift charts of the components between the walks

Packet PROVE-T14-GW4. Supplement Lemma GW3 (`source/spec/p625-671.md` L203–L219, p. 636): "Let `C` be a nondegenerate
Jordan component between consecutive common contacts `x_C, y_C`, in the incoming orientation. Then, in a common-lift
chart `(C; x_C, y_C) → (ℍ; 0, ∞)` …"; Theorem GW4, proof (p. 637): "The ordered-contact Jordan argument and GB13a
consequently apply to these two proper simple curves … Their closed between-region is exactly
`𝓑 = R ∪ L ∪ ⋃_j C_j`". The named input `Theorem14.GW3ChartStatement` asks for a common-lift chart (the frozen
`IsComponentChart`) of every component between the walks.

## Main results

* `isComponentChart_of_isDomainChart`: a chart of `C` (`IsDomainChart`, Spec/Jordan) whose inverse has the boundary
  limits of the frozen predicate is a component chart;
* `HasOrientedUniformizer R L C`: `C` has a conformal map onto `ℍ` whose inverse tends, at every real point, to a
  point of `R` (positive points) resp. `L` (negative points); `exists_isComponentChart_of_hasOrientedUniformizer`;
* `IsTwoArcJordanComponent R L C`: `C ⊆ ℍ` is a bounded Jordan domain whose boundary is the union of a closed arc
  `A ⊆ R` and a closed arc `B ⊆ L` meeting exactly at two points (the consecutive common contacts);
* **`exists_isComponentChart_of_isTwoArcJordanComponent`** (deterministic, unconditional): such a component has a
  component chart. No orientation input is needed: Carathéodory's correspondence (`Sec6.exists_jordanCoord`) maps
  `(0, ∞)` and `(−∞, 0)` onto the two open arcs (connectedness), and if `(0, ∞)` lands on the `L`-arc the chart is
  composed with the inversion `w ↦ −1/w`, which exchanges the two half-lines (the contact at `∞` of the chart is then
  finite, because the component is bounded);
* `GW3GeometryStatement` (named input: the a.s. geometry of the between-region) and
  **`gw3ChartStatement_of_geometry`**: `GW3GeometryStatement → GW3ChartStatement`.

For an unbounded component (consecutive contacts `x_C` and `∞`) the chart must take `∞` to `∞` (the frozen predicate
asks for a finite limit at every real point), so the two half-lines cannot be exchanged and the orientation (the
`R`-arc goes to `(0, ∞)`) is genuine geometric content (GB13a's winding-number argument, p. 559). The named input
keeps it, as the alternative `HasOrientedUniformizer`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function Bornology
open QuantumZipper (H Hbar isOpen_H)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric.JordanMap (IsJordanCurve)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW3

/-! ### Component charts from domain charts -/

/-- **A chart of `C` with the boundary limits is a component chart.** -/
theorem isComponentChart_of_isDomainChart {R L C : Set ℂ} {c : Chart} (hc : IsDomainChart C c)
    (hlim : ∀ x : ℝ, ∃ p : ℂ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) ∧ (0 < x → p ∈ R) ∧ (x < 0 → p ∈ L)) :
    IsComponentChart R L C c :=
  ⟨hc.differentiableOn_fwd, fun _ hz => hc.fwd_mem hz, fun _ hw => hc.inv_mem hw,
    ⟨fun _ hz => hc.inv_fwd hz, fun _ hw => hc.fwd_inv hw⟩, hlim, hc.continuousOn_lift,
    fun _ hz => hc.deriv_eq hz⟩

/-- `C` has an **oriented uniformizer**: a conformal bijection `ψ : C → ℍ` whose inverse tends, at every real point,
to a point of `R` (for a positive point, the right incoming side) resp. of `L` (for a negative point). -/
def HasOrientedUniformizer (R L C : Set ℂ) : Prop :=
  IsOpen C ∧ C ⊆ H ∧ ∃ ψ : ℂ → ℂ, IsConformalBijection ψ C H ∧
    ∀ x : ℝ, ∃ p : ℂ, Tendsto (invFunOn ψ C) (𝓝[H] (x : ℂ)) (𝓝 p) ∧ (0 < x → p ∈ R) ∧ (x < 0 → p ∈ L)

/-- An oriented uniformizer is the forward map of a component chart (the lift is `Im` of an analytic logarithm of
`ψ′`, `exists_isDomainChart_of_isConformalBijection`). -/
theorem exists_isComponentChart_of_hasOrientedUniformizer {R L C : Set ℂ} (h : HasOrientedUniformizer R L C) :
    ∃ c : Chart, IsComponentChart R L C c := by
  obtain ⟨hCo, hCH, ψ, hψ, hlim⟩ := h
  obtain ⟨c, -, hc2, hc⟩ := exists_isDomainChart_of_isConformalBijection hCo hCH hψ
  exact ⟨c, isComponentChart_of_isDomainChart hc (hc2 ▸ hlim)⟩

/-- A component chart gives an oriented uniformizer (the converse; so `HasOrientedUniformizer` is exactly the
existence of a component chart up to the lift). -/
theorem hasOrientedUniformizer_of_isComponentChart {R L C : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) : HasOrientedUniformizer R L C := by
  obtain ⟨hd, hmF, hmI, hinv, hlim, -, -⟩ := hc
  have hbij : BijOn c.1 C H := hinv.bijOn hmF hmI
  have heq : EqOn (invFunOn c.1 C) c.2.1 H := fun w hw => by
    have h1 : c.2.1 w ∈ C := hmI hw
    have h2 : c.1 (c.2.1 w) = w := hinv.2 hw
    calc invFunOn c.1 C w = invFunOn c.1 C (c.1 (c.2.1 w)) := by rw [h2]
      _ = c.2.1 w := hbij.injOn.leftInvOn_invFunOn h1
  refine ⟨hCo, hCH, c.1, ⟨hd, hbij⟩, fun x => ?_⟩
  obtain ⟨p, hp, hpR, hpL⟩ := hlim x
  exact ⟨p, hp.congr' (eventually_nhdsWithin_of_forall fun w hw => (heq hw).symm), hpR, hpL⟩

/-! ### Bounded two-arc Jordan components -/

/-- `C` is a **bounded two-arc Jordan component** of the walks `(R, L)` (Lemma GW3, p. 636: "a nondegenerate Jordan
component between consecutive common contacts `x_C, y_C`"; GB11.0 and GB13a, p. 559: "the matched two-arc Jordan
interiors"): `C ⊆ ℍ` is a bounded domain whose frontier is a Jordan curve, the union of a closed arc `A ⊆ R` and a
closed arc `B ⊆ L` that meet exactly at the two contacts `a ≠ e`, each arc having a point other than the contacts. -/
def IsTwoArcJordanComponent (R L C : Set ℂ) : Prop :=
  IsOpen C ∧ IsConnected C ∧ C ⊆ H ∧ IsBounded C ∧ IsJordanCurve (frontier C) ∧
    ∃ (A B : Set ℂ) (a e : ℂ), IsClosed A ∧ IsClosed B ∧ frontier C = A ∪ B ∧ A ∩ B = {a, e} ∧ a ≠ e ∧
      A ⊆ R ∧ B ⊆ L ∧ (A \ {a, e}).Nonempty ∧ (B \ {a, e}).Nonempty

/-- The inverse of a Carathéodory coordinate of a bounded domain (continuous on `ℍ̄`, into `C̄ \ {e}`, with `ψ`
continuous on `C̄ \ {e}` and `ψ ∘ ψinv = id`) tends to the marked point `e` at `∞`. -/
theorem tendsto_cobounded_of_coord {C : Set ℂ} (hCb : IsBounded C) {ψ ψinv : ℂ → ℂ} {e : ℂ}
    (hψc : ContinuousOn ψ (closure C \ {e})) (hψi : ∀ w ∈ Hbar, ψ (ψinv w) = w)
    (him : MapsTo ψinv Hbar (closure C \ {e})) :
    Tendsto ψinv (cobounded ℂ ⊓ 𝓟 H) (𝓝 e) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : IsCompact (closure C) := hCb.isCompact_closure
  set K := closure C ∩ (Metric.ball e ε)ᶜ with hKdef
  have hKc : IsCompact K := hK.inter_right Metric.isOpen_ball.isClosed_compl
  have hKsub : K ⊆ closure C \ {e} := fun z hz =>
    ⟨hz.1, fun he => hz.2 (by rw [mem_singleton_iff.1 he]; exact Metric.mem_ball_self hε)⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hψc.mono hKsub)
  have hev : ∀ᶠ w in cobounded ℂ, M < ‖w‖ := tendsto_norm_cobounded_atTop.eventually_gt_atTop M
  filter_upwards [mem_inf_of_left hev, mem_inf_of_right (mem_principal_self H)] with w hw hwH
  have hwb : w ∈ Hbar := show (0 : ℝ) ≤ w.im from le_of_lt hwH
  by_contra hd
  have hwK : ψinv w ∈ K := ⟨(him hwb).1, fun hb' => hd (Metric.mem_ball.1 hb')⟩
  have hb' := hM _ hwK
  rw [hψi w hwb] at hb'
  exact absurd hw (not_lt.2 hb')

/-- The inversion `w ↦ −1/w` tends to `∞` within `ℍ` at `0`. -/
theorem tendsto_neg_inv_nhdsWithin_zero :
    Tendsto (fun w : ℂ => -w⁻¹) (𝓝[H] 0) (cobounded ℂ ⊓ 𝓟 H) := by
  have hH0 : H ⊆ ({0} : Set ℂ)ᶜ := fun w hw h0 => by
    have : (0 : ℝ) < w.im := hw
    rw [mem_singleton_iff.1 h0, Complex.zero_im] at this
    exact lt_irrefl 0 this
  refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
  · exact tendsto_neg_cobounded.comp (tendsto_inv₀_nhdsNE_zero.mono_left (nhdsWithin_mono _ hH0))
  · exact eventually_nhdsWithin_of_forall fun w hw => Chart.isConformal_infinitySourceChart.2.1 hw

/-- At a nonzero real point the inversion `w ↦ −1/w` tends within `ℍ` to the real point `−1/x`. -/
theorem tendsto_neg_inv_nhdsWithin {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun w : ℂ => -w⁻¹) (𝓝[H] (x : ℂ)) (𝓝[H] (((-x⁻¹ : ℝ)) : ℂ)) := by
  have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx
  have hval : (((-x⁻¹ : ℝ)) : ℂ) = -(x : ℂ)⁻¹ := by push_cast; ring
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · rw [hval]
    exact ((continuousAt_inv₀ hx').neg.tendsto).mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun w hw => Chart.isConformal_infinitySourceChart.2.1 hw

/-- **A bounded two-arc Jordan component has a component chart** (Lemma GW3, p. 636, the chart; deterministic).
Carathéodory's coordinate `ψ` of the Jordan domain (`Sec6.exists_jordanCoord`, contacts `a ↦ 0`, `e ↦ ∞`) has an
inverse continuous on `ℍ̄` that maps every half-line `(0, ∞)`, `(−∞, 0)` onto a connected subset of the frontier
avoiding the two contacts, hence into one of the closed arcs `A`, `B` (they meet only at the contacts); since every
frontier point other than the contacts is reached, the two half-lines go to different arcs. If `(0, ∞)` goes to `A`
the chart of `ψ` is a component chart; otherwise its composition with the inversion `w ↦ −1/w` is (the contact `e`
is then the finite limit at `0`). -/
theorem exists_isComponentChart_of_isTwoArcJordanComponent {R L C : Set ℂ}
    (h : IsTwoArcJordanComponent R L C) : ∃ c : Chart, IsComponentChart R L C c := by
  obtain ⟨hCo, hCc, hCH, hCb, hJ, A, B, a, e, hA, hB, hAB, hABi, hae, hAR, hBL, ⟨zA, hzA⟩, ⟨zB, hzB⟩⟩ := h
  obtain ⟨p, hp⟩ := hCc.nonempty
  have hDeq : connectedComponentIn (frontier C)ᶜ p = C := connectedComponentIn_compl_frontier_eq hCo hCc hp
  have hpΓ : p ∈ (frontier C)ᶜ := fun hpf => by
    rw [hCo.frontier_eq] at hpf
    exact hpf.2 hp
  have haAB : a ∈ A ∩ B := by rw [hABi]; exact mem_insert a {e}
  have heAB : e ∈ A ∩ B := by rw [hABi]; exact mem_insert_of_mem a (mem_singleton e)
  have haΓ : a ∈ frontier C := by rw [hAB]; exact Or.inl haAB.1
  have heΓ : e ∈ frontier C := by rw [hAB]; exact Or.inl heAB.1
  obtain ⟨ψ, ψinv, hψc, -, hic, him, hiψ, hψi, hψ, hΓre, hy0, -⟩ :=
    Sec6.exists_jordanCoord hJ hpΓ (by rw [hDeq]; exact hCb) heΓ haΓ
  rw [hDeq] at hψc him hiψ hψ
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hHb : ∀ w ∈ H, w ∈ Hbar := fun w hw => show (0 : ℝ) ≤ w.im from le_of_lt hw
  -- the boundary map `f = ψinv` on `ℝ`
  set f : ℝ → ℂ := fun x => ψinv x with hfdef
  have hfc : Continuous f := hic.comp_continuous continuous_ofReal hreal
  have hfΓ : ∀ x : ℝ, f x ∈ frontier C \ {e} := by
    intro x
    obtain ⟨hcl, hne⟩ := him (hreal x)
    refine ⟨?_, hne⟩
    rw [hCo.frontier_eq]
    refine ⟨hcl, fun hC => ?_⟩
    have h1 : ψ (f x) ∈ H := hψ.2.mapsTo hC
    rw [hψi _ (hreal x)] at h1
    have h2 : (0 : ℝ) < (x : ℂ).im := h1
    simp at h2
  have haCl : a ∈ closure C \ {e} := ⟨frontier_subset_closure haΓ, hae⟩
  have hfa : ∀ x : ℝ, x ≠ 0 → f x ≠ a := fun x hx hfx => by
    have h1 := hψi _ (hreal x)
    rw [show ψinv (x : ℂ) = a from hfx, hy0] at h1
    exact hx (by exact_mod_cast h1.symm)
  have hsurj : ∀ z ∈ frontier C, z ≠ a → z ≠ e → ∃ x : ℝ, x ≠ 0 ∧ f x = z := by
    intro z hz hza hze
    have hzcl : z ∈ closure C \ {e} := ⟨frontier_subset_closure hz, hze⟩
    have him0 := hΓre z ⟨hz, hze⟩
    refine ⟨(ψ z).re, fun h0 => hza ?_, ?_⟩
    · have hψz : ψ z = 0 := Complex.ext (by simpa using h0) (by simpa using him0)
      rw [← hiψ z hzcl, ← hiψ a haCl, hψz, hy0]
    · have hψz : (((ψ z).re : ℝ) : ℂ) = ψ z := Complex.ext (by simp) (by simp [him0])
      change ψinv (((ψ z).re : ℝ) : ℂ) = z
      rw [hψz, hiψ z hzcl]
  -- connectedness: each half-line goes into one arc
  have hsplit : ∀ s : Set ℝ, IsPreconnected s → (∀ x ∈ s, x ≠ 0) → f '' s ⊆ A ∨ f '' s ⊆ B := by
    intro s hs hs0
    refine isPreconnected_iff_subset_of_disjoint_closed.1 (hs.image f hfc.continuousOn) A B hA hB ?_ ?_
    · rintro _ ⟨x, -, rfl⟩
      rw [← hAB]
      exact (hfΓ x).1
    · rw [hABi, eq_empty_iff_forall_notMem]
      rintro _ ⟨⟨x, hx, rfl⟩, hxae⟩
      rcases hxae with h | h
      · exact hfa x (hs0 x hx) h
      · exact (hfΓ x).2 h
  have hpos := hsplit (Ioi 0) isPreconnected_Ioi fun x hx => (mem_Ioi.1 hx).ne'
  have hneg := hsplit (Iio 0) isPreconnected_Iio fun x hx => (mem_Iio.1 hx).ne
  have hcover : ∀ x : ℝ, x ≠ 0 → f x ∈ f '' Ioi 0 ∨ f x ∈ f '' Iio 0 := fun x hx => by
    rcases lt_or_gt_of_ne hx with h | h
    · exact Or.inr (mem_image_of_mem f h)
    · exact Or.inl (mem_image_of_mem f h)
  -- the points of the open arcs
  have hzAΓ : zA ∈ frontier C := by rw [hAB]; exact Or.inl hzA.1
  have hzBΓ : zB ∈ frontier C := by rw [hAB]; exact Or.inr hzB.1
  have hzAB : zA ∉ B := fun h' => hzA.2 (by rw [← hABi]; exact ⟨hzA.1, h'⟩)
  have hzBA : zB ∉ A := fun h' => hzB.2 (by rw [← hABi]; exact ⟨h', hzB.1⟩)
  obtain ⟨xA, hxA0, hfxA⟩ := hsurj zA hzAΓ (fun h' => hzA.2 (Or.inl h')) (fun h' => hzA.2 (Or.inr h'))
  obtain ⟨xB, hxB0, hfxB⟩ := hsurj zB hzBΓ (fun h' => hzB.2 (Or.inl h')) (fun h' => hzB.2 (Or.inr h'))
  -- the chart of `ψ`
  obtain ⟨c, -, hc2, hc⟩ := exists_isDomainChart_of_isConformalBijection hCo hCH hψ
  have heqH : EqOn c.2.1 ψinv H := by
    intro w hw
    have hmem : ψinv w ∈ C := by
      have hm := him (hHb w hw)
      by_contra hnot
      have hfr : ψinv w ∈ frontier C := by rw [hCo.frontier_eq]; exact ⟨hm.1, hnot⟩
      have hre := hΓre (ψinv w) ⟨hfr, hm.2⟩
      rw [hψi w (hHb w hw)] at hre
      exact (ne_of_gt hw) hre
    rw [hc2]
    have h2 := hψ.2.injOn.leftInvOn_invFunOn hmem
    rwa [hψi w (hHb w hw)] at h2
  have hlimR : ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (f x)) := fun x =>
    ((hic _ (hreal x)).tendsto.mono_left (nhdsWithin_mono _ hHb)).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (heqH hw).symm)
  rcases hpos with hP | hP <;> rcases hneg with hN | hN
  · -- both half-lines in `A`: impossible (`zB`)
    exfalso
    rcases hcover xB hxB0 with h' | h'
    · exact hzBA (hfxB ▸ hP h')
    · exact hzBA (hfxB ▸ hN h')
  · -- the right orientation
    exact ⟨c, isComponentChart_of_isDomainChart hc fun x =>
      ⟨f x, hlimR x, fun hx => hAR (hP (mem_image_of_mem f hx)), fun hx => hBL (hN (mem_image_of_mem f hx))⟩⟩
  · -- the reversed orientation: compose with `w ↦ −1/w`
    have hc' : IsDomainChart C (c.trans infinitySourceChart) := by
      have h' := hc.trans isDomainChart_infinitySourceChart
      rwa [hc.image_eq] at h'
    refine ⟨c.trans infinitySourceChart, isComponentChart_of_isDomainChart hc' fun x => ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · -- at `0`: the contact `e`
      subst hx
      refine ⟨e, ?_, fun h' => absurd h' (lt_irrefl 0), fun h' => absurd h' (lt_irrefl 0)⟩
      have hinf : Tendsto c.2.1 (cobounded ℂ ⊓ 𝓟 H) (𝓝 e) :=
        (tendsto_cobounded_of_coord hCb hψc hψi him).congr'
          (eventually_of_mem (mem_inf_of_right (mem_principal_self H)) fun w hw => (heqH hw).symm)
      have h0 : ((0 : ℝ) : ℂ) = 0 := Complex.ofReal_zero
      rw [h0]
      exact hinf.comp tendsto_neg_inv_nhdsWithin_zero
    · refine ⟨f (-x⁻¹), (hlimR (-x⁻¹)).comp (tendsto_neg_inv_nhdsWithin hx), fun hx' => ?_, fun hx' => ?_⟩
      · exact hAR (hN (mem_image_of_mem f (show -x⁻¹ ∈ Iio (0 : ℝ) from neg_neg_of_pos (inv_pos.2 hx'))))
      · exact hBL (hP (mem_image_of_mem f (show -x⁻¹ ∈ Ioi (0 : ℝ) from
          neg_pos.2 (inv_lt_zero.2 hx'))))
  · -- both half-lines in `B`: impossible (`zA`)
    exfalso
    rcases hcover xA hxA0 with h' | h'
    · exact hzAB (hfxA ▸ hP h')
    · exact hzAB (hfxA ▸ hN h')

/-- Each alternative of the geometry gives a component chart. -/
theorem exists_isComponentChart_of_geometry {R L C : Set ℂ}
    (h : IsTwoArcJordanComponent R L C ∨ HasOrientedUniformizer R L C) : ∃ c : Chart, IsComponentChart R L C c :=
  h.elim exists_isComponentChart_of_isTwoArcJordanComponent exists_isComponentChart_of_hasOrientedUniformizer

/-! ### The named geometric input and Lemma GW3's charts -/

/-- **Named input: the between-region geometry** (Theorem GW4, proof, p. 637: "The ordered-contact Jordan argument and
GB13a consequently apply to these two proper simple curves, with their actual real connectors included. Their closed
between-region is exactly `𝓑 = R ∪ L ∪ ⋃_j C_j`"; Lemma GW3, p. 636: "a nondegenerate Jordan component between
consecutive common contacts `x_C, y_C`, in the incoming orientation"; GB13a, p. 559). In the setting of
`GW3ChartStatement` (verbatim binders), almost surely every component between the walks is a bounded two-arc Jordan
component (both contacts finite), or has an oriented uniformizer (the component whose far contact is `∞`: its
uniformizer fixing `∞` takes the `R`-arc to `(0, ∞)`, GB13a's orientation by winding numbers). -/
def GW3GeometryStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω₀ ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)),
          IsTwoArcJordanComponent
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C ∨
            HasOrientedUniformizer
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
              (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
                (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)) C

/-- **Lemma GW3, the charts, from the between-region geometry** (conditional helper with a distinct name). -/
theorem gw3ChartStatement_of_geometry (hG : GW3GeometryStatement.{u}) : GW3ChartStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hω C hC
  exact exists_isComponentChart_of_geometry (hω C hC)

end GW3

end Theorem14

end InteractingSLE
