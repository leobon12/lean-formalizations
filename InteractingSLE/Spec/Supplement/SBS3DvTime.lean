/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DvCore

/-!
# D5's F2a: time changes of lifted tails

Worker PROVE-R6-CORNER (round 8). A piece of SB2(2)'s lower walk runs on its own time, a proper parametrization
`β` of the walk on another; this file passes between the two:

* `isDrivenCurve_comp`: drivenness is invariant under continuous strictly increasing reparametrizations of `[0, ∞)`
  from `0` (onto every `[0, φ t]`);
* `canon_eq_of_lift_good`, `canonVal_eq_of_lift`: `canon_eq_lift_of_good` / `canonVal_eq_lift` for any curve with a
  continuous pointwise lift through the hull chart;
* `interior_real_eq_empty_of_dense`;
* **`isDrivenCurve_canonCurve_of_timeChange`**: the canonical stage curve of a curve whose lift is `γ ∘ φ₀` (`γ` a
  proper curve whose times in `ℍ` are dense in `[0, S)`, `φ₀` a continuous time change from `0`, strictly increasing
  on `[0, L)` into `[0, S)`), with dense good times on `[0, L)`, is driven.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Dv

open Sec7.PocketTraversal Sec7.Lemma71C

/-- **Drivenness is invariant under increasing reparametrizations**: if `φ` is continuous and strictly increasing on
`[0, ∞)`, `φ 0 = 0`, and maps every `[0, t]` onto `[0, φ t]`, then `γ ∘ φ` is driven whenever `γ` is. -/
theorem isDrivenCurve_comp {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {φ : ℝ → ℝ} (hφc : ContinuousOn φ (Ici 0))
    (hφm : StrictMonoOn φ (Ici 0)) (hφ0 : φ 0 = 0) (hφs : ∀ t, 0 ≤ t → φ '' Icc 0 t = Icc 0 (φ t)) :
    IsDrivenCurve (γ ∘ φ) := by
  have hφnn : ∀ t, 0 ≤ t → 0 ≤ φ t := fun t ht => by
    rcases ht.eq_or_lt with h | h
    · rw [← h, hφ0]
    · rw [← hφ0]; exact (hφm (le_refl (0 : ℝ)) ht h).le
  have hmaps : MapsTo φ (Ici 0) (Ici 0) := fun t ht => hφnn t ht
  have hcap : ∀ t, 0 ≤ t → capClock (γ ∘ φ) t = capClock γ (φ t) := fun t ht => by
    unfold capClock
    rw [image_comp, hφs t ht]
  refine ⟨hγ.continuousOn.comp hφc hmaps, by simp [hφ0, hγ.zero], fun S hS => ?_⟩
  have hφS : 0 < φ S := by rw [← hφ0]; exact hφm (le_refl (0 : ℝ)) hS.le hS
  obtain ⟨W, hW, hW0, hc0, hm, hcc, hK⟩ := hγ.localDriver (φ S) hφS
  have hsub : MapsTo φ (Icc 0 S) (Icc 0 (φ S)) := fun t ht =>
    ⟨hφnn t ht.1, hφm.monotoneOn ht.1 hS.le ht.2⟩
  refine ⟨W, hW, hW0, by rw [hcap 0 le_rfl, hφ0, hc0], fun a ha b hb hab => ?_, ?_, fun t ht => ?_⟩
  · rw [hcap a ha.1, hcap b hb.1]
    exact hm (hsub ha) (hsub hb) (hφm ha.1 hb.1 hab)
  · exact (hcc.comp (hφc.mono Icc_subset_Ici_self) hsub).congr fun t ht => hcap t ht.1
  · rw [hcap t ht.1]
    obtain ⟨h1, h2⟩ := hK (φ t) (hsub ht)
    refine ⟨h1, ?_⟩
    rw [h2, image_comp, hφs t ht.1]

/-! ### Lifts of arbitrary curves -/

/-- **A pointwise lift through the hull chart is the chart image at the good times** (`canon_eq_lift_of_good` for any
curve `q` with a lift `ζ`: `c⁻¹ → q t` at `ζ t + e`). -/
theorem canon_eq_of_lift_good {X : Set ℂ} (hA : IsHPHull (fillH X)) {e : ℝ} {q ζ : ℝ≥0 → ℂ}
    (hζH : ∀ t, 0 ≤ (ζ t).im)
    (hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (ζ t - ((-e : ℝ) : ℂ))) (𝓝 (q t)))
    {g : ℂ → ℂ} (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q)))
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (hgfr : MapsTo g (Hbar \ H) (frontier (H \ fillH X)))
    {t : ℝ≥0} (ht : q t ∈ H \ fillH X) :
    (Mo.hullChart (fillH X) e).1 (q t) = ζ t ∧ ζ t ∈ H := by
  set c := Mo.hullChart (fillH X) 0 with hcdef
  have hD : IsDomainChart (H \ fillH X) c := Mo.isDomainChart_hullChart hA 0
  set w : ℂ := ζ t - ((-e : ℝ) : ℂ) with hwdef
  have hwH : w ∈ Hbar := by
    show 0 ≤ w.im
    simpa [hwdef] using hζH t
  have := GW1P.neBot_nhdsWithin_H hwH
  have hgq : g w = q t := tendsto_nhds_unique (hgt w hwH) (hζl t)
  have hwH' : w ∈ H := by
    by_contra hw
    have hfr := hgfr ⟨hwH, hw⟩
    rw [hgq, (show IsOpen (H \ fillH X) from hA.2.2.1).frontier_eq] at hfr
    exact hfr.2 ht
  have hinv : c.2.1 w = q t := by rw [← hgi hwH', hgq]
  have hfw : c.1 (q t) = w := by rw [← hinv]; exact hD.fwd_inv hwH'
  refine ⟨?_, ?_⟩
  · have : (Mo.hullChart (fillH X) e).1 (q t) = c.1 (q t) - (e : ℂ) := by simp [hcdef]
    rw [this, hfw, hwdef]
    push_cast
    ring
  · have : ζ t = w + ((-e : ℝ) : ℂ) := by rw [hwdef]; ring
    rw [this]
    exact Mo.add_ofReal_mem_H hwH' _

/-- The canonical values of a curve with a continuous lift are the lift on the closure of its good times. -/
theorem canonVal_eq_of_lift {X : Set ℂ} (hA : IsHPHull (fillH X)) {e : ℝ} {q ζ : ℝ≥0 → ℂ} (hζc : Continuous ζ)
    (hζH : ∀ t, 0 ≤ (ζ t).im)
    (hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (ζ t - ((-e : ℝ) : ℂ))) (𝓝 (q t)))
    {g : ℂ → ℂ} (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q)))
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (hgfr : MapsTo g (Hbar \ H) (frontier (H \ fillH X)))
    {L : ℝ≥0∞} {t : ℝ≥0} (ht : t ∈ closure (canonGood X q L)) : canonVal X e q L t = ζ t := by
  classical
  have hval : ∀ t' ∈ canonGood X q L, (Mo.hullChart (fillH X) e).1 (q t') = ζ t' := fun t' ht' =>
    (canon_eq_of_lift_good hA hζH hζl hgt hgi hgfr ht'.2).1
  unfold canonVal
  split_ifs with hg
  · exact hval t hg
  · have hne : (𝓝[canonGood X q L] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 ht
    have hlim : Tendsto (fun t' => (Mo.hullChart (fillH X) e).1 (q t')) (𝓝[canonGood X q L] t) (𝓝 (ζ t)) :=
      ((hζc.tendsto t).mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun t' ht' => (hval t' ht').symm)
    exact hlim.limUnder_eq

/-! ### A time-changed lifted tail -/

/-- Real times of a curve have empty interior where its times in `ℍ` are dense. -/
theorem interior_real_eq_empty_of_dense {γ : ℝ≥0 → ℂ} {S : ℝ}
    (hd : ∀ s : ℝ≥0, (s : ℝ) < S → s ∈ closure {s' : ℝ≥0 | γ s' ∈ H}) :
    interior {r ∈ Ioo (0 : ℝ) S | ((fun r : ℝ => γ r.toNNReal) r).im = 0} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun r hr => ?_
  have hrS : r ∈ Ioo (0 : ℝ) S := (interior_subset hr).1
  set U : Set ℝ≥0 := (fun t : ℝ≥0 => (t : ℝ)) ⁻¹'
    interior {r ∈ Ioo (0 : ℝ) S | ((fun r : ℝ => γ r.toNNReal) r).im = 0} with hUdef
  have hUo : IsOpen U := isOpen_interior.preimage NNReal.continuous_coe
  have hrU : r.toNNReal ∈ U := by
    show ((r.toNNReal : ℝ≥0) : ℝ) ∈ interior {r ∈ Ioo (0 : ℝ) S | ((fun r : ℝ => γ r.toNNReal) r).im = 0}
    rwa [Real.coe_toNNReal _ hrS.1.le]
  have hcl := hd r.toNNReal (by rw [Real.coe_toNNReal _ hrS.1.le]; exact hrS.2)
  obtain ⟨t, htU, htg⟩ := mem_closure_iff.1 hcl U hUo hrU
  have him := (interior_subset htU).2
  simp only [Real.toNNReal_coe] at him
  exact (ne_of_gt (show 0 < (γ t).im from htg)) him

/-- **The canonical stage curve of a time-changed lifted tail is driven** (finite lifetime `L`). `γ` is a proper curve
from `0` in `ℍ̄` whose times in `ℍ` are dense in `[0, S)`; the curve `q` has the lift `γ ∘ φ₀` through the hull chart
of `X` (offset `e`), where the time change `φ₀` is continuous, from `0`, strictly increasing on `[0, L)` with values
in `[0, S)`; the good times of `q` are dense in `[0, L)`. -/
theorem isDrivenCurve_canonCurve_of_timeChange {X : Set ℂ} (hA : IsHPHull (fillH X)) {e : ℝ} {g : ℂ → ℂ}
    (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q)))
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (hgfr : MapsTo g (Hbar \ H) (frontier (H \ fillH X)))
    {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) (hγ0 : γ 0 = 0) {S L : ℝ≥0} (hS : 0 < S) (hL : 0 < L)
    {φ₀ : ℝ≥0 → ℝ≥0} (hφc : Continuous φ₀) (hφm : StrictMonoOn φ₀ (Iio L)) (hφ0 : φ₀ 0 = 0)
    (hφS : ∀ t : ℝ≥0, t < L → φ₀ t < S)
    (hdγ : ∀ s : ℝ≥0, (s : ℝ) < S → s ∈ closure {s' : ℝ≥0 | γ s' ∈ H})
    {q : ℝ≥0 → ℂ}
    (hql : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (γ (φ₀ t) - ((-e : ℝ) : ℂ))) (𝓝 (q t)))
    (hdq : ∀ t : ℝ≥0, t < L → t ∈ closure (canonGood X q L)) :
    IsDrivenCurve (canonCurve X e q L) := by
  set γ' : ℝ → ℂ := fun r => γ r.toNNReal with hγ'def
  have hc' : ContinuousOn γ' (Ici 0) := (hγ.1.comp continuous_real_toNNReal).continuousOn
  have hinj' : InjOn γ' (Ici 0) := fun a ha b hb hab => by
    have := hγ.2.1 hab
    rw [← Real.coe_toNNReal a ha, ← Real.coe_toNNReal b hb, this]
  have hH' : MapsTo γ' (Ici 0) Hbar := fun r _ => hγ.2.2.1 r.toNNReal
  have h0' : γ' 0 = 0 := by simp [hγ'def, hγ0]
  have hinf' : Tendsto (fun r => ‖γ' r‖) atTop atTop := hγ.2.2.2.comp tendsto_real_toNNReal_atTop
  have hS' : (0 : ℝ) < S := hS
  have hL' : (0 : ℝ) < L := hL
  have hdr := FinRel.isDrivenCurve_relCurve_of_lt hc' hinj' hH' h0' hinf' hS'
    (interior_real_eq_empty_of_dense hdγ)
  -- the time change on `[0, ∞)`
  set Φ : ℝ → ℝ := fun r => (φ₀ r.toNNReal : ℝ) with hΦdef
  set ψ : ℝ → ℝ := fun u => Φ (clockOf L u) / (S - Φ (clockOf L u)) with hψdef
  have hcL : ∀ u, 0 ≤ u → clockOf L u ∈ Ico 0 (L : ℝ) := fun u hu => clockOf_mem_Ico hL' hu
  have hlt : ∀ r ∈ Ico 0 (L : ℝ), r.toNNReal < L := fun r hr => by
    rw [Real.toNNReal_lt_iff_lt_coe hr.1]; exact hr.2
  have hΦS : ∀ r ∈ Ico 0 (L : ℝ), Φ r ∈ Ico 0 (S : ℝ) := fun r hr =>
    ⟨NNReal.coe_nonneg _, by exact_mod_cast hφS _ (hlt r hr)⟩
  have hden : ∀ u, 0 ≤ u → 0 < (S : ℝ) - Φ (clockOf L u) := fun u hu => by
    have := (hΦS _ (hcL u hu)).2; linarith
  have hΦc : Continuous Φ := NNReal.continuous_coe.comp (hφc.comp continuous_real_toNNReal)
  have hcLc : ContinuousOn (clockOf (L : ℝ)) (Ici 0) := by
    unfold clockOf
    exact continuousOn_const.mul (continuousOn_id.div (continuousOn_const.add continuousOn_id)
      fun u (hu : 0 ≤ u) => by positivity)
  have hΦL : ContinuousOn (fun u => Φ (clockOf L u)) (Ici 0) := hΦc.comp_continuousOn hcLc
  have hψc : ContinuousOn ψ (Ici 0) :=
    hΦL.div (continuousOn_const.sub hΦL) fun u hu => (hden u hu).ne'
  have hψm : StrictMonoOn ψ (Ici 0) := by
    intro a ha b hb hab
    have h1 := strictMonoOn_clockOf hL' ha hb hab
    have h1' : (clockOf L a).toNNReal < (clockOf L b).toNNReal :=
      (Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt (hcL a ha).1 h1)).2 h1
    have h2 : Φ (clockOf L a) < Φ (clockOf L b) := by
      show (φ₀ (clockOf L a).toNNReal : ℝ) < φ₀ (clockOf L b).toNNReal
      exact_mod_cast hφm (hlt _ (hcL a ha)) (hlt _ (hcL b hb)) h1'
    have hpa := hden a ha
    have hpb := hden b hb
    show Φ (clockOf L a) / (S - Φ (clockOf L a)) < Φ (clockOf L b) / (S - Φ (clockOf L b))
    rw [div_lt_div_iff₀ hpa hpb]
    nlinarith
  have hψ0 : ψ 0 = 0 := by simp [hψdef, hΦdef, clockOf_zero, hφ0]
  have hψs : ∀ t, 0 ≤ t → ψ '' Icc 0 t = Icc 0 (ψ t) := by
    intro t ht
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, hψm.monotoneOn hx.1 ht hx.2⟩
      rw [← hψ0]; exact hψm.monotoneOn (le_refl (0 : ℝ)) hx.1 hx.1
    · have := intermediate_value_Icc ht (hψc.mono Icc_subset_Ici_self)
      rwa [hψ0] at this
  have hcomp := isDrivenCurve_comp hdr hψc hψm hψ0 hψs
  refine Vk.IsDrivenCurve.congr hcomp fun u hu => ?_
  have hu' : (0 : ℝ) ≤ u := hu
  show relCurve γ' S (ψ u) = canonVal X e q L
    (if (L : ℝ≥0∞) = ⊤ then u else clockOf (L : ℝ≥0∞).toReal u).toNNReal
  simp only [ENNReal.coe_ne_top, ↓reduceIte, ENNReal.coe_toReal]
  rw [canonVal_eq_of_lift (ζ := γ ∘ φ₀) hA (hγ.1.comp hφc) (fun t => hγ.2.2.1 _) hql hgt hgi hgfr
    (hdq _ (hlt _ (hcL u hu')))]
  show γ' (clockOf S (ψ u)) = γ (φ₀ (clockOf L u).toNNReal)
  rw [show ψ u = Φ (clockOf L u) / (S - Φ (clockOf L u)) from rfl, FinRel.clockOf_inv (hΦS _ (hcL u hu'))]
  simp [hγ'def, hΦdef]

end InteractingSLE.Theorem14.SB.Dv
