/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3DvStage
import InteractingSLE.Spec.Supplement.SB2LkCurve
import InteractingSLE.Spec.Supplement.SBLvPinchUse
import InteractingSLE.Spec.Supplement.SB2FinChain
import InteractingSLE.Spec.Supplement.SB2JRight
import InteractingSLE.Spec.Supplement.SB4RChart
import InteractingSLE.Spec.Supplement.SB2MoNorm
import InteractingSLE.Spec.Supplement.SB2VkFam
import InteractingSLE.Foundations.Topology.PathComplement
import InteractingSLE.Spec.Supplement.SB2MtLift

/-!
# D5's F2a: the deterministic core — canonical images of lifted tails are driven

Worker PROVE-R6-CORNER (round 8). For a path image `X = p([0, 1])` attached to `ℝ` at `0` (finite fibres) on the
closed left of a proper curve `β` from `0`:

* `exists_canon_package`: the canonical hull chart `Mo.hullChart (fill X) 0` has a right entry value `e` at
  `R = max (X ∩ ℝ)` (so its recentring is a right entry chart, `Lf.isRightEntryChart_recenter`) and a continuous
  finite-fibre boundary map `g` of its inverse on `ℍ̄` sending real points to the frontier
  (`exists_continuousOn_extension_of_ulc_fillH`, `ulc_image_Icc`, `Lv.finite_fibre_of_isDomainChart`);
* Lemma S2 (`Lk.exists_tailLiftCurve`) lifts the tail of `β` after its visit `tL` of `R`; at the good times
  (`β (tL + t) ∈ ℍ ∖ fill X`) the lift is the chart image of `β (tL + t)` (`canon_eq_lift_of_good`), hence on the
  closure of the good times the canonical values are the lift (`canonVal_eq_lift`), and the lift's real times have
  empty interior where the good times are dense (`interior_real_lift_eq_empty`);
* **`exists_canon_tail_driven`**: the canonical stage curve `canonCurve X x₀ (β (tL + ·)) L` is driven for every
  finite lifetime `L` in which the good times are dense (`FinRel.isDrivenCurve_relCurve_of_lt`) and for `L = ∞` if
  they are dense in `[0, ∞)` (`FinRel.exists_localDriver_of_lt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.SB.Dv

open Sec7.PocketTraversal Sec7.Lemma71C

section PathHull

variable {p : ℝ → ℂ}

theorem isPreconnected_path_union_lower (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) :
    IsPreconnected (p '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) :=
  (isPreconnected_Icc.image _ hp).union (p 0) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    (show (p 0).im ≤ 0 by rw [hp0, Complex.zero_im]) isPreconnected_lowerHalf

theorem isPreconnected_real_union_path (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) :
    IsPreconnected ({z : ℂ | z.im = 0} ∪ p '' Icc 0 1) := by
  have hR : IsPreconnected {z : ℂ | z.im = 0} := by
    have : {z : ℂ | z.im = 0} = Set.range ((↑) : ℝ → ℂ) := by
      ext z; constructor
      · intro hz; exact ⟨z.re, Complex.ext (by simp) (by simpa using hz.symm)⟩
      · rintro ⟨x, rfl⟩; simp
    rw [this]; exact isPreconnected_range Complex.continuous_ofReal
  exact hR.union (0 : ℂ) (show (0 : ℂ).im = 0 by simp) ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
    (isPreconnected_Icc.image _ hp)

theorem isHPHull_fillH_path (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) :
    IsHPHull (fillH (p '' Icc 0 1)) :=
  isHPHull_fillH_of_isPreconnected (isCompact_Icc.image_of_continuousOn hp).isBounded
    (isPreconnected_path_union_lower hp hp0)

end PathHull


section Package

variable {p : ℝ → ℂ}

/-- **The canonical chart package of a path image** `X = p([0, 1])` attached to `ℝ` at `0`: with `c = Mo.hullChart
(fill X) 0`, a right entry value `e` at `R = max (X ∩ ℝ)` (so `c.recenter e` is a right entry chart of `X` at `R`), and
the continuous boundary map `g` of `c`'s inverse on `ℍ̄` (finite fibres, real points to the frontier). -/
theorem exists_canon_package (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) :
    ∃ (e : ℝ) (g : ℂ → ℂ),
      IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
        ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter e) ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g (Mo.hullChart (fillH (p '' Icc 0 1)) 0).2.1 H ∧
      (∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH (p '' Icc 0 1)) 0).2.1 (𝓝[H] q) (𝓝 (g q))) ∧
      (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) ∧
      MapsTo g (Hbar \ H) (frontier (H \ fillH (p '' Icc 0 1))) := by
  set X := p '' Icc 0 1 with hXdef
  have hXc : IsCompact X := isCompact_Icc.image_of_continuousOn hp
  have hXH : X ⊆ Hbar := by
    rintro _ ⟨s, hs, rfl⟩
    exact hpH s hs
  have hA := isHPHull_fillH_path hp hp0
  set c := Mo.hullChart (fillH X) 0 with hcdef
  have hD : IsDomainChart (H \ fillH X) c := Mo.isDomainChart_hullChart hA 0
  have hcc : c.IsConformal := Mo.isConformal_hullChart hA 0
  have hbij : IsConformalBijection c.2.1 H (H \ fillH X) := by
    have h := hcc.isConformalBijection
    rw [Mo.coe_dom_hullChart hA 0] at h
    exact h
  obtain ⟨B, hB⟩ := Mo.hullChart_inv_bounded hA 0
  have hInf : Tendsto c.2.1 (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-B)
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
    filter_upwards [mem_inf_of_right (mem_principal_self H)] with z hz
    have h1 := hB z hz
    have h2 := norm_le_norm_add_norm_sub' z (c.2.1 z)
    rw [norm_sub_rev] at h2
    linarith
  obtain ⟨g, hgi, hgc, hgfr, hginf⟩ := exists_continuousOn_extension_of_ulc_fillH hXc hXH (ulc_image_Icc hp)
    (isPreconnected_real_union_path hp hp0) hbij hInf
  have hgt : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (g q)) := fun q hq =>
    (((hgc q hq).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hz => hgi hz)
  have hgf := Lv.finite_fibre_of_isDomainChart hp hpf hD hgc hgi
    (hginf.mono_left (inf_le_inf_left _ (principal_mono.2 QuantumZipper.H_subset_Hbar)))
  -- the hull model and the right entry value
  have hmo : IsMapOut (fillH X) (fun z => c.1 z + ((0 : ℝ) : ℂ)) :=
    Mt.isMapOut_congr (ConformalImage.isMapOut_mapOut hA) fun z _ => by simp [hcdef]
  let M : WalkIntCanon.HullModel c := ⟨fillH X, 0, hA, Mo.coe_dom_hullChart hA 0, hmo⟩
  have hfree : ∀ x : ℝ, realMax X < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull := fun x hx =>
    Lx.exists_ball_disjoint_fillH_right hXc fun y hy => lt_of_le_of_lt (Lx.le_realMax_of_mem hXc hy) hx
  obtain ⟨e, he⟩ := Lx.exists_isRightEntryValue_of_hullModel hcc M hgc hgi hfree
  have hcob : Tendsto c.1 (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH X)) (Bornology.cobounded ℂ) := by
    obtain ⟨B', hB'⟩ := (ConformalImage.isMapOut_mapOut hA).exists_norm_sub_le hA
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-B')
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
    filter_upwards [mem_inf_of_right (mem_principal_self (H \ fillH X))] with z hz
    have h1 : ‖ConformalImage.mapOut (fillH X) z - z‖ ≤ B' := hB' z hz
    have h3 : c.1 z = ConformalImage.mapOut (fillH X) z := by simp [hcdef]
    have h2 := norm_le_norm_add_norm_sub' z (ConformalImage.mapOut (fillH X) z)
    rw [norm_sub_rev] at h2
    rw [h3]
    linarith
  have hlift : ∀ x > realMax X, Tendsto c.2.2 (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x hx
    obtain ⟨ρ, hρ, hd⟩ := hfree x hx
    exact (Restart.isCanonicalDerivLog_canonDerivLog hA).tendsto_im_nhdsWithin_zero hA
      (ConformalImage.isMapOut_mapOut hA) hρ hd
  exact ⟨e, g, Lf.isRightEntryChart_recenter hD he hcob hlift, hgc, hgi, hgt, hgf, hgfr⟩

end Package

section Tail

variable {p : ℝ → ℂ}

/-- **The canonical image of a lifted tail at its good times**: if `γ` is a lift of `t ↦ β (tL + t)` through the hull
chart of `X` recentred at `e` (`IsTailLiftCurve`), the boundary map `g` of the chart's inverse sends real points to
the frontier, and the point `β (tL + t)` is off `fill X` in `ℍ`, then `γ t` is the hull chart's image of it (offset
`e`) and lies in `ℍ`. -/
theorem canon_eq_lift_of_good {X : Set ℂ} (hA : IsHPHull (fillH X)) {R e : ℝ} {β γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : Lk.IsTailLiftCurve (Mo.hullChart (fillH X) 0) R (-e) β tL γ) {g : ℂ → ℂ}
    (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q)))
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (hgfr : MapsTo g (Hbar \ H) (frontier (H \ fillH X)))
    {t : ℝ≥0} (ht : β (tL + t) ∈ H \ fillH X) :
    (Mo.hullChart (fillH X) e).1 (β (tL + t)) = γ t ∧ γ t ∈ H := by
  set c := Mo.hullChart (fillH X) 0 with hcdef
  have hD : IsDomainChart (H \ fillH X) c := Mo.isDomainChart_hullChart hA 0
  set q : ℂ := γ t - ((-e : ℝ) : ℂ) with hqdef
  have hqH : q ∈ Hbar := by
    show 0 ≤ q.im
    simpa [hqdef] using hγ.2.1.2.2.1 t
  have := GW1P.neBot_nhdsWithin_H hqH
  have hgq : g q = β (tL + t) := tendsto_nhds_unique (hgt q hqH) (hγ.2.2.2 t)
  have hqH' : q ∈ H := by
    by_contra hq
    have hfr := hgfr ⟨hqH, hq⟩
    rw [hgq, (show IsOpen (H \ fillH X) from hA.2.2.1).frontier_eq] at hfr
    exact hfr.2 ht
  have hinv : c.2.1 q = β (tL + t) := by rw [← hgi hqH', hgq]
  have hfw : c.1 (β (tL + t)) = q := by rw [← hinv]; exact hD.fwd_inv hqH'
  refine ⟨?_, ?_⟩
  · have : (Mo.hullChart (fillH X) e).1 (β (tL + t)) = c.1 (β (tL + t)) - (e : ℂ) := by
      simp [hcdef]
    rw [this, hfw, hqdef]
    push_cast
    ring
  · have : γ t = q + ((-e : ℝ) : ℂ) := by rw [hqdef]; ring
    rw [this]
    exact Mo.add_ofReal_mem_H hqH' _

end Tail

section Core

variable {p : ℝ → ℂ}

/-- The canonical values of a lifted tail are the lift, on the closure of the good times. -/
theorem canonVal_eq_lift {X : Set ℂ} (hA : IsHPHull (fillH X)) {R e : ℝ} {β γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : Lk.IsTailLiftCurve (Mo.hullChart (fillH X) 0) R (-e) β tL γ) {g : ℂ → ℂ}
    (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q)))
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (hgfr : MapsTo g (Hbar \ H) (frontier (H \ fillH X)))
    {L : ℝ≥0∞} {t : ℝ≥0} (ht : t ∈ closure (canonGood X (fun t => β (tL + t)) L)) :
    canonVal X e (fun t => β (tL + t)) L t = γ t := by
  classical
  have hval : ∀ t' ∈ canonGood X (fun t => β (tL + t)) L,
      (Mo.hullChart (fillH X) e).1 (β (tL + t')) = γ t' := fun t' ht' =>
    (canon_eq_lift_of_good hA hγ hgt hgi hgfr ht'.2).1
  unfold canonVal
  split_ifs with hg
  · exact hval t hg
  · have hne : (𝓝[canonGood X (fun t => β (tL + t)) L] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 ht
    have hlim : Tendsto (fun t' => (Mo.hullChart (fillH X) e).1 (β (tL + t')))
        (𝓝[canonGood X (fun t => β (tL + t)) L] t) (𝓝 (γ t)) :=
      ((hγ.2.1.1.tendsto t).mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun t' ht' => (hval t' ht').symm)
    exact hlim.limUnder_eq

/-- The real times of a lifted tail have empty interior wherever the good times are dense. -/
theorem interior_real_lift_eq_empty {X : Set ℂ} (hA : IsHPHull (fillH X)) {R e : ℝ} {β γ : ℝ≥0 → ℂ}
    {tL : ℝ≥0} (hγ : Lk.IsTailLiftCurve (Mo.hullChart (fillH X) 0) R (-e) β tL γ) {g : ℂ → ℂ}
    (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q)))
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (hgfr : MapsTo g (Hbar \ H) (frontier (H \ fillH X)))
    {L : ℝ≥0∞} {S : ℝ} (hS : ∀ t : ℝ≥0, (t : ℝ) < S → t ∈ closure (canonGood X (fun t => β (tL + t)) L)) :
    interior {r ∈ Ioo (0 : ℝ) S | ((fun r : ℝ => γ r.toNNReal) r).im = 0} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun r hr => ?_
  have hrS : r ∈ Ioo (0 : ℝ) S := (interior_subset hr).1
  set U : Set ℝ≥0 := (fun t : ℝ≥0 => (t : ℝ)) ⁻¹'
    interior {r ∈ Ioo (0 : ℝ) S | ((fun r : ℝ => γ r.toNNReal) r).im = 0} with hUdef
  have hUo : IsOpen U := isOpen_interior.preimage NNReal.continuous_coe
  have hrU : r.toNNReal ∈ U := by
    show ((r.toNNReal : ℝ≥0) : ℝ) ∈ interior {r ∈ Ioo (0 : ℝ) S | ((fun r : ℝ => γ r.toNNReal) r).im = 0}
    rwa [Real.coe_toNNReal _ hrS.1.le]
  have hcl := hS r.toNNReal (by rw [Real.coe_toNNReal _ hrS.1.le]; exact hrS.2)
  obtain ⟨t, htU, htg⟩ := mem_closure_iff.1 hcl U hUo hrU
  have him := (interior_subset htU).2
  have hH := (canon_eq_lift_of_good hA hγ hgt hgi hgfr htg.2).2
  simp only [Real.toNNReal_coe] at him
  exact (ne_of_gt (show 0 < (γ t).im from hH)) him

/-- **F2a's deterministic core.** Let `X = p([0, 1])` be a path image attached to `ℝ` at `0` with finite fibres, on
the closed left of a proper curve `β` from `0`. There are the visit time `tL` of `R = max (X ∩ ℝ)` and an offset `x₀`
such that the canonical stage curve of the tail `t ↦ β (tL + t)` (chart `Mo.hullChart (fill X) x₀`) is driven, with
any finite lifetime `S > 0` in which the good times are dense, and with infinite lifetime if they are dense in
`[0, ∞)`. -/
theorem exists_canon_tail_driven (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hS1 : p '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β) :
    ∃ (tL : ℝ≥0) (x₀ : ℝ), β tL = realMax (p '' Icc 0 1) ∧
      (∀ S : ℝ≥0, 0 < S → (∀ t : ℝ≥0, t < S → t ∈ closure (canonGood (p '' Icc 0 1) (fun t => β (tL + t)) S)) →
        IsDrivenCurve (canonCurve (p '' Icc 0 1) x₀ (fun t => β (tL + t)) S)) ∧
      ((∀ t : ℝ≥0, t ∈ closure (canonGood (p '' Icc 0 1) (fun t => β (tL + t)) ⊤)) →
        IsDrivenCurve (canonCurve (p '' Icc 0 1) x₀ (fun t => β (tL + t)) ⊤)) := by
  obtain ⟨e, g, hrc, hgc, hgi, hgt, hgf, hgfr⟩ := exists_canon_package hp hp0 hpH hpf
  have hA := isHPHull_fillH_path hp hp0
  have hrc' : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
      ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter (-(-e))) := by rwa [neg_neg]
  obtain ⟨tL, γ, hγ⟩ := Lk.exists_tailLiftCurve hp hp0 hpH hβ hβ0 hS1 hrc' hgc hgi hgt hgf
  set γ' : ℝ → ℂ := fun r => γ r.toNNReal with hγ'def
  have hpc := hγ.2.1
  have hc' : ContinuousOn γ' (Ici 0) := (hpc.1.comp continuous_real_toNNReal).continuousOn
  have hinj' : InjOn γ' (Ici 0) := fun a ha b hb hab => by
    have := hpc.2.1 hab
    rw [← Real.coe_toNNReal a ha, ← Real.coe_toNNReal b hb, this]
  have hH' : MapsTo γ' (Ici 0) Hbar := fun r _ => hpc.2.2.1 r.toNNReal
  have h0' : γ' 0 = 0 := by simp [hγ'def, hγ.2.2.1]
  have hinf' : Tendsto (fun r => ‖γ' r‖) atTop atTop := hpc.2.2.2.comp tendsto_real_toNNReal_atTop
  refine ⟨tL, e, hγ.1, fun S hS hden => ?_, fun hden => ?_⟩
  · have hS' : (0 : ℝ) < S := hS
    have hR := interior_real_lift_eq_empty hA hγ hgt hgi hgfr (L := (S : ℝ≥0∞)) (S := (S : ℝ))
      fun t ht => hden t (by exact_mod_cast ht)
    have hdr := FinRel.isDrivenCurve_relCurve_of_lt hc' hinj' hH' h0' hinf' hS' hR
    refine Vk.IsDrivenCurve.congr hdr fun u hu => ?_
    have hmem := clockOf_mem_Ico hS' (show (0 : ℝ) ≤ u from hu)
    have hlt : (clockOf (S : ℝ) u).toNNReal < S := by
      rw [Real.toNNReal_lt_iff_lt_coe hmem.1]; exact hmem.2
    show γ' (clockOf (S : ℝ) u) = canonVal _ e _ (S : ℝ≥0∞)
      (if (S : ℝ≥0∞) = ⊤ then u else clockOf (S : ℝ≥0∞).toReal u).toNNReal
    simp only [ENNReal.coe_ne_top, ↓reduceIte, ENNReal.coe_toReal]
    rw [canonVal_eq_lift hA hγ hgt hgi hgfr (hden _ hlt)]
  · have hR : ∀ S : ℝ, interior {r ∈ Ioo (0 : ℝ) S | (γ' r).im = 0} = ∅ := fun S =>
      interior_real_lift_eq_empty hA hγ hgt hgi hgfr (L := ⊤) (S := S) fun t _ => hden t
    have hdr : IsDrivenCurve γ' :=
      ⟨hc', h0', fun S hS => FinRel.exists_localDriver_of_lt hc' hinj' hH' h0' hinf' (hR S) hS le_rfl⟩
    refine Vk.IsDrivenCurve.congr hdr fun u hu => ?_
    show γ' u = canonVal _ e _ ⊤ (if (⊤ : ℝ≥0∞) = ⊤ then u else clockOf (⊤ : ℝ≥0∞).toReal u).toNNReal
    simp only [↓reduceIte]
    rw [canonVal_eq_lift hA hγ hgt hgi hgfr (hden _)]

end Core

end InteractingSLE.Theorem14.SB.Dv
