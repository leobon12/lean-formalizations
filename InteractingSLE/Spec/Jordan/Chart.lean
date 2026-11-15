/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.Pushforward
import InteractingSLE.Foundations.PrimeEnd.Basic

/-!
# Charts of a domain with two marked prime ends

Packet PROVE-JORDANCPL (carriers for supplement GB6, specification §6.2 Remarks 6.9–6.10 and Aux. 32–37, and
Aux. 119–125). Specification p. 2, "Conformal coordinate and derivative lift": a conformal coordinate `ψ` comes
with "the chosen analytic logarithm `L_ψ` of `ψ′`"; "for compositions use the analytic chain-rule lift inherited
from these choices"; "boundary markings used in conformal maps are prime ends".

Every domain of the specification's half-plane arguments is a subdomain `D ⊆ ℍ` of the original chart (GB6:
"Work first in the original flow chart `(D, x, y) = (ℍ, 0, ∞)`"; Aux. 32: "compactified by a fixed conformal map";
the pockets of Aux. 34–41 and 119–125 and the components of GW3–GW4 lie in `ℍ`). A chart of `D` is the frozen
`Chart = (fwd, inv, lift)` whose inverse maps `ℍ` onto `D`.

## Main definitions

* `Chart.trans c₁ c₂`: `c₁` followed by `c₂` (`fwd₂ ∘ fwd₁`, `inv₁ ∘ inv₂`, chain-rule lift `lift₂ ∘ fwd₁ + lift₁`);
  the frozen `Chart.loewner c W t` is `c.trans (Chart.id.loewner W t)` (`loewner_eq_trans`);
* `Chart.dilation r`: `w ↦ r w` with lift `0`;
* `IsDomainChart D c`: `c` is conformal, `inv '' ℍ = D`, and `lift = Im L` on `D` for an analytic logarithm `L` of
  `fwd′` (`IsDerivLog`);
* `IsDomainChart.hChart`: the half-plane chart `fwd : D → ℍ` (`HChart D`);
* `IsDomainChartAt D a b c`: moreover the prime ends of `D` marked by `0` and `∞` in this chart are `a` and `b`
  ("the chart of `U` taking `(y, p)` to `(0, ∞)`", GB6).

## Main results

* `IsDomainChart.trans`: charts compose (domain `inv₁ '' D₂`, chain-rule lift);
* `IsDomainChartAt.trans_dilation`: a dilation keeps the marked prime ends;
* **`IsDomainChartAt.exists_dilation`** (chart independence): two charts of `D` taking the same prime ends to
  `0, ∞` differ by a dilation `w ↦ r w`, `r > 0`, and their lifts by one constant `2πn` (`n ∈ ℤ`);
* `isDomainChartAt_id`: the identity chart of `ℍ` takes the prime ends `0, ∞` of `ℍ` to `0, ∞`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function
open QuantumZipper (H isOpen_H)
open QuantumZipper.CA (realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE

/-! ### Composition and dilation of charts -/

/-- **Composition of charts** (Specification p. 2: "for compositions use the analytic chain-rule lift"): the chart
`c₁` followed by a chart `c₂` written in the coordinate of `c₁`: `fwd = fwd₂ ∘ fwd₁`, `inv = inv₁ ∘ inv₂`,
`lift = lift₂ ∘ fwd₁ + lift₁`. -/
def Chart.trans (c₁ c₂ : Chart) : Chart :=
  (fun z => c₂.1 (c₁.1 z), fun w => c₁.2.1 (c₂.2.1 w), fun z => c₂.2.2 (c₁.1 z) + c₁.2.2 z)

/-- The **dilation chart** `w ↦ r w` of `ℍ` (lift `0`; for `r > 0` its derivative `r` has argument `0`). -/
def Chart.dilation (r : ℝ) : Chart :=
  (fun z => (r : ℂ) * z, fun w => w / r, fun _ => 0)

namespace Chart

@[simp] theorem trans_fst (c₁ c₂ : Chart) (z : ℂ) : (c₁.trans c₂).1 z = c₂.1 (c₁.1 z) := rfl

@[simp] theorem trans_inv (c₁ c₂ : Chart) (w : ℂ) : (c₁.trans c₂).2.1 w = c₁.2.1 (c₂.2.1 w) := rfl

@[simp] theorem trans_lift (c₁ c₂ : Chart) (z : ℂ) :
    (c₁.trans c₂).2.2 z = c₂.2.2 (c₁.1 z) + c₁.2.2 z := rfl

@[simp] theorem dilation_fst (r : ℝ) (z : ℂ) : (dilation r).1 z = r * z := rfl

@[simp] theorem dilation_inv (r : ℝ) (w : ℂ) : (dilation r).2.1 w = w / r := rfl

@[simp] theorem dilation_lift (r : ℝ) (z : ℂ) : (dilation r).2.2 z = 0 := rfl

theorem trans_assoc (c₁ c₂ c₃ : Chart) : (c₁.trans c₂).trans c₃ = c₁.trans (c₂.trans c₃) := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext z
  change c₃.2.2 (c₂.1 (c₁.1 z)) + (c₂.2.2 (c₁.1 z) + c₁.2.2 z) =
    c₃.2.2 (c₂.1 (c₁.1 z)) + c₂.2.2 (c₁.1 z) + c₁.2.2 z
  ring

theorem id_trans (c : Chart) : Chart.id.trans c = c := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext z
  change c.2.2 z + 0 = c.2.2 z
  rw [add_zero]

/-- The frozen Loewner step is the composition with the centred Loewner chart of `ℍ`. -/
theorem loewner_eq_trans (c : Chart) (W : ℝ → ℝ) (t : ℝ) :
    c.loewner W t = c.trans (Chart.id.loewner W t) := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext z
  change (QuantumZipper.logDerivFwd W t (c.1 z)).im + c.2.2 z =
    ((QuantumZipper.logDerivFwd W t (c.1 z)).im + 0) + c.2.2 z
  rw [add_zero]

variable {c c₁ c₂ : Chart}

/-- Conformal charts compose. -/
theorem IsConformal.trans (h₁ : c₁.IsConformal) (h₂ : c₂.IsConformal) : (c₁.trans c₂).IsConformal :=
  ⟨h₁.1.comp h₂.1 h₂.2.1, h₁.2.1.comp h₂.2.1, fun w hw => by
    change c₂.1 (c₁.1 (c₁.2.1 (c₂.2.1 w))) = w
    rw [h₁.2.2 _ (h₂.2.1 hw), h₂.2.2 w hw]⟩

theorem trans_image (c₁ c₂ : Chart) : (c₁.trans c₂).2.1 '' H = c₁.2.1 '' (c₂.2.1 '' H) := by
  rw [image_image]
  rfl

theorem dilation_mem_H {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ H) : (r : ℂ) * z ∈ H := by
  change 0 < ((r : ℂ) * z).im
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact mul_pos hr hz

theorem div_mem_H {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ H) : w / (r : ℂ) ∈ H := by
  change 0 < (w / (r : ℂ)).im
  rw [Complex.div_ofReal_im]
  exact div_pos hw hr

theorem isConformal_dilation {r : ℝ} (hr : 0 < r) : (dilation r).IsConformal := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  refine ⟨(differentiableOn_id.div_const _), fun w hw => div_mem_H hr hw, fun w _ => ?_⟩
  change (r : ℂ) * (w / r) = w
  field_simp

theorem dilation_image_H {r : ℝ} (hr : 0 < r) : (dilation r).2.1 '' H = H := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  refine Subset.antisymm (fun _ ⟨w, hw, he⟩ => he ▸ div_mem_H hr hw) fun w hw =>
    ⟨(r : ℂ) * w, dilation_mem_H hr hw, ?_⟩
  change (r : ℂ) * w / r = w
  field_simp

end Chart

/-! ### Charts of a domain -/

/-- **A chart of the domain `D`** (Specification p. 2, "Conformal coordinate and derivative lift"): the frozen chart
`c = (fwd, inv, lift)` is conformal with domain `inv '' ℍ = D` (so `D ⊆ ℍ` is open and `fwd : D → ℍ` is a
conformal bijection with inverse `inv`), and its lift is `Im L` on `D` for an analytic logarithm `L` of `fwd′` on
`D` ("the chosen analytic logarithm of `ψ′`"; the lift is data, as in the source). -/
def IsDomainChart (D : Set ℂ) (c : Chart) : Prop :=
  c.IsConformal ∧ c.2.1 '' H = D ∧ ∃ L : ℂ → ℂ, IsDerivLog c.1 L D ∧ EqOn c.2.2 (fun z => (L z).im) D

namespace IsDomainChart

variable {D D₂ : Set ℂ} {c c₁ c₂ : Chart}

theorem isConformal (hc : IsDomainChart D c) : c.IsConformal := hc.1

theorem image_eq (hc : IsDomainChart D c) : c.2.1 '' H = D := hc.2.1

theorem isOpen (hc : IsDomainChart D c) : IsOpen D := hc.image_eq ▸ hc.1.isOpen_image

theorem subset_H (hc : IsDomainChart D c) : D ⊆ H := hc.image_eq ▸ hc.1.2.1.image_subset

theorem isPreconnected (hc : IsDomainChart D c) : IsPreconnected D :=
  hc.image_eq ▸ ((convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected.image _
    hc.1.1.continuousOn)

theorem coe_dom (hc : IsDomainChart D c) : (c.dom : Set ℂ) = D := hc.1.coe_dom.trans hc.image_eq

theorem inv_mem (hc : IsDomainChart D c) {w : ℂ} (hw : w ∈ H) : c.2.1 w ∈ D :=
  hc.image_eq ▸ mem_image_of_mem _ hw

theorem fwd_mem (hc : IsDomainChart D c) {z : ℂ} (hz : z ∈ D) : c.1 z ∈ H :=
  hc.1.fwd_mem (by rw [← SetLike.mem_coe, hc.coe_dom]; exact hz)

theorem inv_fwd (hc : IsDomainChart D c) {z : ℂ} (hz : z ∈ D) : c.2.1 (c.1 z) = z :=
  hc.1.inv_fwd (by rw [← SetLike.mem_coe, hc.coe_dom]; exact hz)

theorem fwd_inv (hc : IsDomainChart D c) {w : ℂ} (hw : w ∈ H) : c.1 (c.2.1 w) = w := hc.1.2.2 w hw

theorem differentiableOn_fwd (hc : IsDomainChart D c) : DifferentiableOn ℂ c.1 D := by
  have h := hc.1.differentiableOn_fwd
  rwa [hc.coe_dom] at h

/-- `fwd` is a conformal bijection of `D` onto `ℍ`. -/
theorem isConformalBijection (hc : IsDomainChart D c) : IsConformalBijection c.1 D H :=
  ⟨hc.differentiableOn_fwd, fun _ hz => hc.fwd_mem hz, fun z₁ hz₁ z₂ hz₂ he => by
    rw [← hc.inv_fwd hz₁, he, hc.inv_fwd hz₂], fun w hw => ⟨c.2.1 w, hc.inv_mem hw, hc.fwd_inv hw⟩⟩

/-- The half-plane chart `fwd : D → ℍ`. -/
def hChart (hc : IsDomainChart D c) : HChart D := ⟨c.1, hc.isConformalBijection⟩

@[simp] theorem hChart_val (hc : IsDomainChart D c) : hc.hChart.1 = c.1 := rfl

theorem deriv_ne_zero (hc : IsDomainChart D c) {z : ℂ} (hz : z ∈ D) : deriv c.1 z ≠ 0 := by
  obtain ⟨L, hL, -⟩ := hc.2.2
  rw [← hL.2 z hz]
  exact Complex.exp_ne_zero _

/-- The lift is continuous on `D`. -/
theorem continuousOn_lift (hc : IsDomainChart D c) : ContinuousOn c.2.2 D := by
  obtain ⟨L, hL, hlift⟩ := hc.2.2
  exact (Complex.continuous_im.comp_continuousOn hL.1.continuousOn).congr hlift

/-- The lift written in the coordinate of `ℍ`, `lift ∘ inv`, is continuous on `ℍ`. -/
theorem continuousOn_lift_inv (hc : IsDomainChart D c) : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H :=
  hc.continuousOn_lift.comp hc.1.1.continuousOn fun _ hw => hc.inv_mem hw

/-- The lift is a branch of `arg fwd′` (the frozen `IsComponentChart` form). -/
theorem deriv_eq (hc : IsDomainChart D c) {z : ℂ} (hz : z ∈ D) :
    deriv c.1 z = (‖deriv c.1 z‖ : ℂ) * Complex.exp ((c.2.2 z : ℂ) * Complex.I) := by
  obtain ⟨L, hL, hlift⟩ := hc.2.2
  rw [← hL.2 z hz, Complex.norm_exp, hlift hz]
  conv_lhs => rw [← Complex.re_add_im (L z)]
  rw [Complex.exp_add, ← Complex.ofReal_exp]

/-- **Composition**: a chart `c₂` of `D₂ ⊆ ℍ` read in the coordinate of a chart `c₁` of `D` gives the chart
`c₁.trans c₂` of the subdomain `inv₁ '' D₂ ⊆ D`, with the chain-rule lift. -/
theorem trans (h₁ : IsDomainChart D c₁) (h₂ : IsDomainChart D₂ c₂) :
    IsDomainChart (c₁.2.1 '' D₂) (c₁.trans c₂) := by
  have hD₂H : D₂ ⊆ H := h₂.subset_H
  have himg : (c₁.trans c₂).2.1 '' H = c₁.2.1 '' D₂ := by rw [Chart.trans_image, h₂.image_eq]
  have hopen : IsOpen (c₁.2.1 '' D₂) := himg ▸ (h₁.1.trans h₂.1).isOpen_image
  have hsub : c₁.2.1 '' D₂ ⊆ D := by
    rw [← h₁.image_eq]
    exact image_mono hD₂H
  have hmaps : MapsTo c₁.1 (c₁.2.1 '' D₂) D₂ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [h₁.fwd_inv (hD₂H hw)]
    exact hw
  obtain ⟨L₁, hL₁, hlift₁⟩ := h₁.2.2
  obtain ⟨L₂, hL₂, hlift₂⟩ := h₂.2.2
  refine ⟨h₁.1.trans h₂.1, himg, fun z => L₂ (c₁.1 z) + L₁ z, ?_, fun z hz => ?_⟩
  · exact IsDerivLog.comp (ψ := c₂.1) (φ := c₁.1) hopen h₂.isOpen h₂.differentiableOn_fwd
      (h₁.differentiableOn_fwd.mono hsub) hmaps hL₂ (hL₁.mono hsub)
  · change c₂.2.2 (c₁.1 z) + c₁.2.2 z = (L₂ (c₁.1 z) + L₁ z).im
    rw [Complex.add_im, hlift₂ (hmaps hz), hlift₁ (hsub hz)]

end IsDomainChart

/-- The identity chart of `ℍ`. -/
theorem isDomainChart_id : IsDomainChart H Chart.id := by
  refine ⟨Chart.isConformal_id, image_id H, fun _ => 0, ⟨differentiableOn_const _, fun z _ => ?_⟩,
    fun z _ => ?_⟩
  · change Complex.exp 0 = deriv (fun z : ℂ => z) z
    rw [Complex.exp_zero, deriv_id'']
  · change (0 : ℝ) = (0 : ℂ).im
    rw [Complex.zero_im]

/-- The dilation chart of `ℍ` (`r > 0`). -/
theorem isDomainChart_dilation {r : ℝ} (hr : 0 < r) : IsDomainChart H (Chart.dilation r) := by
  refine ⟨Chart.isConformal_dilation hr, Chart.dilation_image_H hr, fun _ => Complex.log r,
    ⟨differentiableOn_const _, fun z _ => ?_⟩, fun z _ => ?_⟩
  · change Complex.exp (Complex.log r) = deriv (fun z : ℂ => (r : ℂ) * z) z
    rw [Complex.exp_log (Complex.ofReal_ne_zero.2 hr.ne'), ((hasDerivAt_id' z).const_mul (r : ℂ)).deriv,
      mul_one]
  · change (0 : ℝ) = (Complex.log r).im
    rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hr.le]

/-! ### Marked prime ends -/

/-- **A chart of `D` taking the prime ends `a, b` to `0, ∞`** (Specification p. 2: "boundary markings used in
conformal maps are prime ends"; supplement GB6: "the chart of `U` taking `(y, p)` to `(0, ∞)`"). -/
def IsDomainChartAt (D : Set ℂ) (a b : PrimeEnd D) (c : Chart) : Prop :=
  ∃ hc : IsDomainChart D c, PrimeEnd.mk hc.hChart ((0 : ℝ) : OnePoint ℝ) = a ∧
    PrimeEnd.mk hc.hChart OnePoint.infty = b

/-- The prime ends of `ℍ` at `0` and at `∞` in the identity chart. -/
def primeEndH (x : OnePoint ℝ) : PrimeEnd H := PrimeEnd.mk isDomainChart_id.hChart x

theorem isDomainChartAt_id :
    IsDomainChartAt H (primeEndH ((0 : ℝ) : OnePoint ℝ)) (primeEndH OnePoint.infty) Chart.id :=
  ⟨isDomainChart_id, rfl, rfl⟩

namespace IsDomainChartAt

variable {D : Set ℂ} {a b : PrimeEnd D} {c c' : Chart}

theorem isDomainChart (h : IsDomainChartAt D a b c) : IsDomainChart D c := h.1

/-- The two marked prime ends are distinct. -/
theorem ne (h : IsDomainChartAt D a b c) : a ≠ b := by
  obtain ⟨hc, rfl, rfl⟩ := h
  exact fun he => OnePoint.coe_ne_infty _ (PrimeEnd.mk_injective _ he)

/-- A positive dilation keeps the marked prime ends. -/
theorem trans_dilation (h : IsDomainChartAt D a b c) {r : ℝ} (hr : 0 < r) :
    IsDomainChartAt D a b (c.trans (Chart.dilation r)) := by
  obtain ⟨hc, ha, hb⟩ := h
  have hc' : IsDomainChart D (c.trans (Chart.dilation r)) := by
    have := hc.trans (isDomainChart_dilation hr)
    rwa [hc.image_eq] at this
  have hdet : 0 < r * 1 - 0 * 0 := by simpa using hr
  have hEq : EqOn hc'.hChart.1 (realMobius r 0 0 1 ∘ hc.hChart.1) D := fun z _ => by
    change (r : ℂ) * c.1 z = ((r : ℂ) * c.1 z + (0 : ℝ)) / ((0 : ℝ) * c.1 z + (1 : ℝ))
    simp
  refine ⟨hc', ?_, ?_⟩
  · have := PrimeEnd.mk_mobiusBdry hdet hEq ((0 : ℝ) : OnePoint ℝ)
    rw [mobiusBdry_coe] at this
    simp only [zero_add, one_ne_zero, ↓reduceIte, mul_zero, add_zero, div_one] at this
    rw [this, ha]
  · have := PrimeEnd.mk_mobiusBdry hdet hEq OnePoint.infty
    rw [mobiusBdry_infty] at this
    simp only [↓reduceIte] at this
    rw [this, hb]

/-- **Chart independence.** Two charts of `D` taking the same prime ends to `0` and `∞` differ by a positive
dilation, `fwd' = r · fwd` on `D`, and their lifts by one constant `2πn` (Specification p. 2: "a change by `2πin`
changes the actual lifted heights"). -/
theorem exists_dilation (h : IsDomainChartAt D a b c) (h' : IsDomainChartAt D a b c') :
    ∃ r : ℝ, 0 < r ∧ EqOn c'.1 (fun z => (r : ℂ) * c.1 z) D ∧
      ∃ n : ℤ, EqOn c'.2.2 (fun z => c.2.2 z + 2 * Real.pi * n) D := by
  obtain ⟨hc, ha, hb⟩ := h
  obtain ⟨hc', ha', hb'⟩ := h'
  obtain ⟨p, q, s, t, hdet, hEq⟩ := hc.hChart.exists_realMobius hc.isOpen hc'.hChart
  -- the Möbius map fixes the boundary points `0` and `∞`
  have h0 := PrimeEnd.mk_mobiusBdry hdet hEq ((0 : ℝ) : OnePoint ℝ)
  have hinf := PrimeEnd.mk_mobiusBdry hdet hEq OnePoint.infty
  rw [ha, ← ha'] at h0
  rw [hb, ← hb'] at hinf
  have h0' := PrimeEnd.mk_injective _ h0
  have hinf' := PrimeEnd.mk_injective _ hinf
  rw [mobiusBdry_infty] at hinf'
  have hs : s = 0 := by
    by_contra hs
    rw [ite_eq_right_iff.mpr (fun h => absurd h hs)] at hinf'
    exact OnePoint.coe_ne_infty _ hinf'
  subst hs
  rw [mobiusBdry_coe] at h0'
  simp only [zero_add, mul_zero] at h0'
  have ht : t ≠ 0 := by
    rintro rfl
    simp at hdet
  rw [show (if t = 0 then OnePoint.infty else ((q / t : ℝ) : OnePoint ℝ)) =
      ((q / t : ℝ) : OnePoint ℝ) from ite_eq_right_iff.mpr (fun h => absurd h ht)] at h0'
  have hq : q = 0 := by
    have := OnePoint.coe_injective h0'
    rwa [div_eq_zero_iff, or_iff_left ht] at this
  subst hq
  have hpt : 0 < p * t := by simpa using hdet
  set r : ℝ := p / t with hr
  have hr0 : 0 < r := by
    rcases lt_or_gt_of_ne ht with htn | htp
    · exact div_pos_of_neg_of_neg (by nlinarith) htn
    · exact div_pos (by nlinarith) htp
  have hfwd : EqOn c'.1 (fun z => (r : ℂ) * c.1 z) D := fun z hz => by
    have := hEq hz
    change c'.1 z = ((p : ℂ) * c.1 z + (0 : ℝ)) / ((0 : ℝ) * c.1 z + t) at this
    rw [this, hr]
    push_cast
    rw [zero_mul, zero_add, add_zero, div_eq_mul_inv, div_eq_mul_inv]
    ring
  refine ⟨r, hr0, hfwd, ?_⟩
  -- the lifts: `L' ` and `L + log r` are two logarithms of `fwd′` on `D`
  obtain ⟨L, hL, hlift⟩ := hc.2.2
  obtain ⟨L', hL', hlift'⟩ := hc'.2.2
  have hDo := hc.isOpen
  have hL'' : IsDerivLog c'.1 (fun z => L z + Complex.log r) D := by
    refine ⟨hL.1.add_const _, fun z hz => ?_⟩
    have hev : c'.1 =ᶠ[𝓝 z] fun z => (r : ℂ) * c.1 z :=
      Filter.eventuallyEq_of_mem (hDo.mem_nhds hz) hfwd
    rw [hev.deriv_eq, Complex.exp_add, hL.2 z hz,
      Complex.exp_log (Complex.ofReal_ne_zero.2 hr0.ne'), deriv_const_mul_field', mul_comm]
  obtain ⟨n, hn⟩ := hL'.exists_int_eqOn hDo hc.isPreconnected hL''
  refine ⟨n, fun z hz => ?_⟩
  change c'.2.2 z = c.2.2 z + 2 * Real.pi * n
  rw [hlift' hz, hlift hz]
  change (L' z).im = (L z).im + 2 * Real.pi * n
  rw [hn hz]
  simp only [Complex.add_im, Complex.log_im, Complex.arg_ofReal_of_nonneg hr0.le, add_zero,
    Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

end IsDomainChartAt

end InteractingSLE
