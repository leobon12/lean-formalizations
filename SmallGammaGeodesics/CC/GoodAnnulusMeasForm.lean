import SmallGammaGeodesics.CC.GoodAnnulus
import SmallGammaGeodesics.CC.GoodAnnulusDense
import LQGMetric.Papers.GM.S3.GoodAnnulusMeas4

/-!
# Good-annulus events for `(D_h, J')`: D-forms and universal measurability (track CC, CC9a)

Auxiliary for [3] Lemma 3.8 (CC0, Details D14; T2 is `CC/GoodAnnulusMeas.lean`).

GM's measurability proof of the J-form event (`GM.gm_L3_7meas`) converts it, on the a.s. set of
boundedly compact length metrics, into D-forms which are universally measurable (`GM.gaCompareB`,
`GM.gaLongB`, `GM.gaAround`). GM's D-forms are stated for a pair of metrics `(D_h, D̃_h)` on all of
`ℂ`. Here the second function is the extended-valued `J' = D^ϕ(·,·;𝔸)`, which is not a metric on
`ℂ`, so the J-form machinery does not transfer verbatim. The variant proved here:

* `gaCompareD`, `gaLongD`: conditions 1 and 2 in D-form for `D_h` and an **arbitrary** second
  function `J'`, which stays in J-form (`J'(u,v)` and `bdFun J' 𝔸 u`);
* `goodAnnulusI_iff_dForm`: for a proper length metric `D_h`, the J-form event is
  `gaCompareD ∧ gaLongD ∧ gaAround` (GM l. 1348–1359: the proofs of `GM.mem_gaLong_iff_internal`
  and `GM.mem_gaCompareB_iff_internal` with `J'` arbitrary; condition 2 localizes the
  `D_h`-geodesics of condition 1 through `ofReal_le_setDist_of_gaLongI`);
* `uMeasurableSet_gaCompareD`, `uMeasurableSet_gaLongD`: for a standard Borel parameter space `β`, a
  measurable `β → ContMetric` and a second function `F : β → ℂ → ℂ → [0,∞]` that is jointly Borel
  in `(b, u, v)` and whose `bdFun` is jointly Borel in `(b, u)`, the D-forms are coanalytic, hence
  universally measurable (GM's `uMeasurableSet_gaCompareB` and `measurableSet_gaLongS` with the
  second metric replaced by `F`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-! ## The D-forms -/

/-- **condition 1 in D-form** for `D_h` (here `d`) and an arbitrary second function `J'`: GM's
Borel form `gaCompareB` with `D̃_h(u,v)` replaced by `J'(u,v)` -/
def gaCompareD (d : ContMetric) (J' : ℂ → ℂ → ℝ≥0∞) (α C' r : ℝ) (z : ℂ) : Prop :=
  ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r, ∀ η : C(unitInterval, ℂ),
    GM.MidUnique d u v → d.IsGeod01 u v η →
    (∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ)) → (J' u v).toReal ≤ C' * d.1 (u, v)

/-- **condition 2 in D-form** for `D_h` (here `d`) and an arbitrary second function `J'`, whose
clause stays in J-form; the internal metric of `d` is in its Borel version `chainInf` (as in GM's
`gaLongB`) -/
def gaLongD (d : ContMetric) (J' : ℂ → ℂ → ℝ≥0∞) (α r : ℝ) (z : ℂ) : Prop :=
  ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r,
    (setDist d {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) < ENNReal.ofReal (d.1 (u, v)) ∨
      GM.bdFun J' (annulus z (r / 2) (2 * r)) u < J' u v) →
    ∀ (a b : ℝ) (P : ℝ → ℂ), a ≤ b → ContinuousOn P (Icc a b) → P a = u → P b = v →
      P '' Icc a b ⊆ closure (annulus z (α * r) r : Set ℂ) →
      d.chainInf (annulus z (r / 2) (2 * r)) u v < d.len P a b

/-! ## J-form = D-form on proper length metrics -/

section Equiv
variable {α A C' r : ℝ} {z : ℂ}

/-- **condition 2, J-form = D-form** (GM l. 1350–1353, `GM.mem_gaLong_iff_internal` with an
arbitrary second function) -/
theorem gaLongI_iff_gaLongD (d : ContMetric) (hL : d.IsLength) [ProperSpace d.Space]
    (J' : ℂ → ℂ → ℝ≥0∞) (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) :
    GM.gaLongI (d.internal (annulus z (r / 2) (2 * r))) J' α r z ↔ gaLongD d J' α r z := by
  unfold GM.gaLongI gaLongD
  have hUo : IsOpen (annulus z (r / 2) (2 * r) : Set ℂ) := (annulus z (r / 2) (2 * r)).isOpen
  have hUb : Bornology.IsBounded (annulus z (r / 2) (2 * r) : Set ℂ) := GM.isBounded_annulus _ _
  refine forall₂_congr fun u hu => forall₂_congr fun v hv => ?_
  have huU := sphere_inner_subset hα hα1 hr hu
  have hvU := sphere_outer_subset hα hα1 hr hv
  have hb : GM.bdFun (d.internal (annulus z (r / 2) (2 * r))) (annulus z (r / 2) (2 * r)) u <
        d.internal (annulus z (r / 2) (2 * r)) u v ↔
      setDist d {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) <
        ENNReal.ofReal (d.1 (u, v)) := by
    rw [GM.setDist_frontier_lt_iff d hL hUo huU hvU,
      GM.setDist_frontier_eq_iSup d hL hUo hUb huU]
    rfl
  rw [hb]
  refine imp_congr_right fun _ => forall₃_congr fun a b P => imp_congr_right fun _ =>
    forall_congr' fun hP => imp_congr_right fun _ => imp_congr_right fun _ =>
      forall_congr' fun hK => ?_
  rw [GM.lenFun_internal d hP fun t ht => GM.closure_annulus_subset hα hr (hK ⟨t, ht, rfl⟩),
    d.internal_eq_chainInf hL hUo]

/-- **condition 1, J-form = D-form on condition 2** (GM l. 1354–1358,
`GM.mem_gaCompareB_iff_internal` with an arbitrary second function `J'`, which needs no
localization) -/
theorem gaCompareBI_iff_gaCompareD (d : ContMetric) (hL : d.IsLength) [ProperSpace d.Space]
    {J' : ℂ → ℂ → ℝ≥0∞} (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hlong : GM.gaLongI (d.internal (annulus z (r / 2) (2 * r))) J' α r z) :
    GM.gaCompareBI (d.internal (annulus z (r / 2) (2 * r))) J' α C' r z ↔
      gaCompareD d J' α C' r z := by
  have hUo : IsOpen (annulus z (r / 2) (2 * r) : Set ℂ) := (annulus z (r / 2) (2 * r)).isOpen
  unfold GM.gaCompareBI gaCompareD
  refine forall₂_congr fun u hu => forall₂_congr fun v hv => forall_congr' fun η => ?_
  have huU := sphere_inner_subset hα hα1 hr hu
  have hvU := sphere_outer_subset hα hα1 hr hv
  constructor
  · intro H hm hg hK
    have hloc := ofReal_le_setDist_of_gaLongI hL hα hα1 hr hlong hu hv (Or.inl hg) hK
    have := H ((GM.midUnique_iff_midUniqueI d hL hUo huU hvU hloc).1 hm)
      ((GM.isGeod01_iff_isGeodI d hL hUo huU hvU hloc η).1 hg) hK
    rwa [GM.internal_eq_of_le d hL hUo huU hvU hloc, ENNReal.toReal_ofReal (d.nonneg u v)] at this
  · intro H hm hgI hK
    have hloc := ofReal_le_setDist_of_gaLongI hL hα hα1 hr hlong hu hv (Or.inr hgI) hK
    have := H ((GM.midUnique_iff_midUniqueI d hL hUo huU hvU hloc).2 hm)
      ((GM.isGeod01_iff_isGeodI d hL hUo huU hvU hloc η).2 hgI) hK
    rwa [GM.internal_eq_of_le d hL hUo huU hvU hloc, ENNReal.toReal_ofReal (d.nonneg u v)]

/-- **the J-form event is the D-form event** for a proper length metric `D_h` and an arbitrary
second function `J'` (GM l. 1348–1359, `GM.mem_goodAnnulus_iff_internal` with `J'` arbitrary) -/
theorem goodAnnulusI_iff_dForm {D : DistC → ContMetric} {g : DistC} (hL : (D g).IsLength)
    [ProperSpace (D g).Space] (J' : ℂ → ℂ → ℝ≥0∞) (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) :
    GM.goodAnnulusI ((D g).internal (annulus z (r / 2) (2 * r))) J' α A C' r z ↔
      gaCompareD (D g) J' α C' r z ∧ gaLongD (D g) J' α r z ∧ g ∈ GM.gaAround D α A r z := by
  have eL := gaLongI_iff_gaLongD (z := z) (D g) hL J' hα hα1 hr
  have eA := GM.mem_gaAround_iff_internal (D := D) (A := A) (z := z) (g := g) hα hα1 hr hL
  unfold GM.goodAnnulusI
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(gaCompareBI_iff_gaCompareD (D g) hL hα hα1 hr h2).1 h1, eL.1 h2, eA.2 h3⟩
  · rintro ⟨h1, h2, h3⟩
    have h2' := eL.2 h2
    exact ⟨(gaCompareBI_iff_gaCompareD (D g) hL hα hα1 hr h2').2 h1, h2', eA.1 h3⟩

end Equiv

/-! ## Universal measurability of the D-forms -/

section UM
variable {β : Type*} [MeasurableSpace β] [StandardBorelSpace β] {Dm : β → ContMetric}
  {F : β → ℂ → ℂ → ℝ≥0∞}

/-- **condition 1 (D-form) is universally measurable** (coanalytic; GM's
`uMeasurableSet_gaCompareB` with the second metric replaced by a jointly Borel `F`) -/
theorem uMeasurableSet_gaCompareD (hD : Measurable Dm)
    (hF : Measurable fun p : β × ℂ × ℂ => F p.1 p.2.1 p.2.2) (α C' r : ℝ) (z : ℂ) :
    UMeasurableSet {b | gaCompareD (Dm b) (F b) α C' r z} := by
  set K := closure (annulus z (α * r) r : Set ℂ)
  let T := β × (ℂ × ℂ) × C(unitInterval, ℂ)
  have m1 : Measurable fun p : T => (p.2.1.1, p.2.1.2) := measurable_snd.fst
  have mDuv : Measurable fun p : T => (Dm p.1, p.2.1.1, p.2.1.2) :=
    (hD.comp measurable_fst).prodMk m1
  have mGeo : Measurable fun p : T => (Dm p.1, p.2) :=
    (hD.comp measurable_fst).prodMk measurable_snd
  have hS1 : MeasurableSet {p : T | p.2.1.1 ∈ sphere z (α * r)} :=
    isClosed_sphere.measurableSet.preimage measurable_snd.fst.fst
  have hS2 : MeasurableSet {p : T | p.2.1.2 ∈ sphere z r} :=
    isClosed_sphere.measurableSet.preimage measurable_snd.fst.snd
  have hM : MeasurableSet {p : T | GM.MidUnique (Dm p.1) p.2.1.1 p.2.1.2} :=
    GM.measurableSet_midUnique.preimage mDuv
  have hG : MeasurableSet {p : T | (Dm p.1).IsGeod01 p.2.1.1 p.2.1.2 p.2.2} :=
    GM.isClosed_geodRel3.measurableSet.preimage mGeo
  have hKc : IsClosed {η : C(unitInterval, ℂ) | ∀ t, η t ∈ K} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => isClosed_closure.preimage (continuous_eval_const t)
  have hK : MeasurableSet {p : T | ∀ t, p.2.2 t ∈ K} :=
    hKc.measurableSet.preimage measurable_snd.snd
  have fD : Measurable fun p : T => (Dm p.1).1 (p.2.1.1, p.2.1.2) :=
    continuous_contMetric_apply.measurable.comp ((hD.comp measurable_fst).prodMk m1)
  have fF : Measurable fun p : T => F p.1 p.2.1.1 p.2.1.2 :=
    Measurable.comp (g := fun p : β × ℂ × ℂ => F p.1 p.2.1 p.2.2)
      (f := fun p : T => (p.1, p.2.1.1, p.2.1.2)) hF (measurable_fst.prodMk m1)
  have hR : MeasurableSet {p : T | (F p.1 p.2.1.1 p.2.1.2).toReal ≤
      C' * (Dm p.1).1 (p.2.1.1, p.2.1.2)} :=
    measurableSet_le (ENNReal.measurable_toReal.comp fF) (fD.const_mul C')
  have hS : MeasurableSet ({p : T | p.2.1.1 ∈ sphere z (α * r)}ᶜ ∪
      {p : T | p.2.1.2 ∈ sphere z r}ᶜ ∪ {p : T | GM.MidUnique (Dm p.1) p.2.1.1 p.2.1.2}ᶜ ∪
      {p : T | (Dm p.1).IsGeod01 p.2.1.1 p.2.1.2 p.2.2}ᶜ ∪ {p : T | ∀ t, p.2.2 t ∈ K}ᶜ ∪
      {p : T | (F p.1 p.2.1.1 p.2.1.2).toReal ≤ C' * (Dm p.1).1 (p.2.1.1, p.2.1.2)}) :=
    ((((hS1.compl.union hS2.compl).union hM.compl).union hG.compl).union hK.compl).union hR
  convert UMeasurableSet.setOf_forall hS using 1
  ext b
  simp only [gaCompareD, mem_ofPred_eq, mem_union, mem_compl_iff, Prod.forall]
  constructor
  · intro h u v η
    by_contra hc
    simp only [not_or, not_not] at hc
    exact hc.2 (h u hc.1.1.1.1.1 v hc.1.1.1.1.2 η hc.1.1.1.2 hc.1.1.2 hc.1.2)
  · intro h u hu v hv η hm hη hk
    rcases h u v η with ((((h1 | h1) | h1) | h1) | h1) | h1
    · exact absurd hu h1
    · exact absurd hv h1
    · exact absurd hm h1
    · exact absurd hη h1
    · exact absurd hk h1
    · exact h1

/-- **condition 2 (D-form) is universally measurable** (coanalytic; GM's `measurableSet_gaLongS`
and `uMeasurableSet_gaLongB` with the second metric replaced by `F`, whose `bdFun` must be jointly
Borel) -/
theorem uMeasurableSet_gaLongD (hD : Measurable Dm)
    (hF : Measurable fun p : β × ℂ × ℂ => F p.1 p.2.1 p.2.2) (α r : ℝ) (z : ℂ)
    (hFb : Measurable fun p : β × ℂ => GM.bdFun (F p.1) (annulus z (r / 2) (2 * r)) p.2) :
    UMeasurableSet {b | gaLongD (Dm b) (F b) α r z} := by
  set K := closure (annulus z (α * r) r : Set ℂ) with hKdef
  set V : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ) with hVdef
  let T := β × ℂ × ℂ × C(unitInterval, ℂ)
  let S : Set T := {p | p.2.1 ∈ sphere z (α * r) → p.2.2.1 ∈ sphere z r →
      (setDist (Dm p.1) {p.2.1} (frontier V) < ENNReal.ofReal ((Dm p.1).1 (p.2.1, p.2.2.1)) ∨
        GM.bdFun (F p.1) V p.2.1 < F p.1 p.2.1 p.2.2.1) →
      p.2.2.2 0 = p.2.1 → p.2.2.2 1 = p.2.2.1 → (∀ t, p.2.2.2 t ∈ K) →
      (Dm p.1).chainInf V p.2.1 p.2.2.1 < (Dm p.1).len (fun t => p.2.2.2 (GM.pj t)) 0 1}
  have hS : MeasurableSet S := by
    have mu : Measurable fun p : T => p.2.1 := measurable_snd.fst
    have mv : Measurable fun p : T => p.2.2.1 := measurable_snd.snd.fst
    have mη : Measurable fun p : T => p.2.2.2 := measurable_snd.snd.snd
    have mDm : Measurable fun p : T => Dm p.1 := hD.comp measurable_fst
    have hKc : IsClosed {η : C(unitInterval, ℂ) | ∀ t, η t ∈ K} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun t => isClosed_closure.preimage (continuous_eval_const t)
    have m1 := GM.measurable_of_set
      ((isClosed_sphere (x := z) (ε := α * r)).measurableSet.preimage mu)
    have m2 := GM.measurable_of_set ((isClosed_sphere (x := z) (ε := r)).measurableSet.preimage mv)
    have m3a := GM.measurable_setDist_lt mDm mu mv (frontier V)
    have fb : Measurable fun p : T => GM.bdFun (F p.1) V p.2.1 :=
      Measurable.comp (g := fun p : β × ℂ => GM.bdFun (F p.1) V p.2)
        (f := fun p : T => (p.1, p.2.1)) hFb (measurable_fst.prodMk mu)
    have fF : Measurable fun p : T => F p.1 p.2.1 p.2.2.1 :=
      Measurable.comp (g := fun p : β × ℂ × ℂ => F p.1 p.2.1 p.2.2)
        (f := fun p : T => (p.1, p.2.1, p.2.2.1)) hF (measurable_fst.prodMk (mu.prodMk mv))
    have m3b := GM.measurable_of_set (measurableSet_lt fb fF)
    have m4 := GM.measurable_of_set
      (measurableSet_eq_fun ((continuous_eval_const (0 : unitInterval)).measurable.comp mη) mu)
    have m5 := GM.measurable_of_set
      (measurableSet_eq_fun ((continuous_eval_const (1 : unitInterval)).measurable.comp mη) mv)
    have m6 := GM.measurable_of_set (hKc.measurableSet.preimage mη)
    have m7 := GM.measurable_of_set (measurableSet_lt
      (GM.measurable_chainInf_comp mDm mu mv V) (GM.measurable_lenPath_comp mDm mη))
    exact measurableSet_setOfPred.2 (m1.imp (m2.imp ((m3a.or m3b).imp
      (m4.imp (m5.imp (m6.imp m7))))))
  convert UMeasurableSet.setOf_forall hS using 1
  ext b
  constructor
  · rintro H ⟨u, v, η⟩ hu hv hc h0 h1 hK
    exact (GM.forall_path_iff (Dm b) (fun x y I l => x = u → y = v → I ⊆ K →
      (Dm b).chainInf V u v < l)).1 (fun a b' P hab hP => H u hu v hv hc a b' P hab hP) η h0 h1
      (range_subset_iff.2 hK)
  · intro H u hu v hv hc
    exact (GM.forall_path_iff (Dm b) (fun x y I l => x = u → y = v → I ⊆ K →
      (Dm b).chainInf V u v < l)).2 (fun η h0 h1 hK => H (u, v, η) hu hv hc h0 h1
      (range_subset_iff.1 hK))

end UM

end SmallGammaGeodesics.CC
