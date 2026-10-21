import SmallGammaGeodesics.CC.ConfMetric
import SmallGammaGeodesics.Geodesic.Basic
import LQGMetric.Papers.GM.S3.GoodAnnulusMeas3
import LQGMetric.Papers.GM.S3.GoodAnnulusAround
import LQGMetric.Papers.GM.S2.Geodesics
import LQGMetric.Papers.GM.S2.Bilip
import LQGMetric.Papers.GM.S1.Eq115

/-!
# Good-annulus events for the pair `(D_h, D^ϕ)` (track CC, packet CC9a: T1, T3, T4)

Source: Gwynne–Miller arXiv:1905.00384 ([3]), Lemmas 3.8–3.10 and the event (3.9)–(3.11), in the
corrected form of `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D14**.

For a conformal neighbourhood `(ϕ, W, V)` and a coupling `(h, h̄, f)`, the event `E_r(z)` is GM's
good-annulus event in J-form, `GM.goodAnnulusI J J' α A C' r z`, for the internal metrics of
`𝔸 = 𝔸_{r/2,2r}(z)`:
* `J = D_h(·,·;𝔸)`;
* `J' = D^ϕ(·,·;𝔸) = confMetric D ϕ 𝔸 h̄ f = D_{h̄+f}(ϕ·, ϕ·; ϕ(𝔸))`.

Contents:
* **T1** `confGoodAnnulus` (the event for fixed fields) and `confGoodEvent` (the event family for
  the covering lemma `CoverLemma`: `E_r(w)` where an activation predicate `act w r` holds, the sure
  event elsewhere);
* J-form algebra: `goodAnnulusI_smul` (invariance under multiplying `J`, `J'` by one constant
  `k ∈ (0, ∞)`, the Weyl step of [3] Lemma 3.8), `goodAnnulusI_congr` and
  `goodAnnulusI_congr_right` (only the values of `J`, `J'` on `𝔸 × 𝔸` matter);
* **T4** (D-forms consumed by the improvement step, CC8a's `p36_pair_ext_improve`):
  `ofReal_le_setDist_of_gaLongI` (condition 2 localizes geodesics), `internal_eq_of_gaLongI`,
  `le_of_gaCompareBI`, `confMetric_le_of_confGoodAnnulus` (condition 1 gives
  `D^ϕ(u,u') ≤ C' D_h(u,u')`), `exists_disconnect_of_gaAroundI` (condition 3), and the a.s. forms
  `ae_dForms`, `ae_dForms_event`, `ae_hgood_confGoodEvent` (exactly `hgood1`, `hgood3`);
* **T3** `exists_gaAroundI_prob` (condition 3: `GM.gm_gaAround_prob`, uniformly in `z` and
  `r > 0`), the union bound `measure_compl_confGoodEvent_le`, `ofReal_le_measure_of_compl_le` and
  `ofReal_le_measure_confGoodEvent` (the union with CC9b's conditions 1 and 2).

Splits: the measurability modulo constants ([3] Lemma 3.8, **T2**) is in `CC/GoodAnnulusMeas.lean`
(with `CC/GoodAnnulusDense.lean`, `CC/GoodAnnulusMeasForm.lean`); the localization of `D^ϕ` by
condition 2 (T4 for the second metric, used by CC9b) is in `CC/GoodAnnulusLocal.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-! ## 1. The event (T1) -/

/-- **The event `E_r(z)` for `(D_h, D^ϕ)`** ([3] (3.9)–(3.11); CC0 D14): GM's good-annulus event
in J-form for the internal metrics `J = D_h(·,·;𝔸)` and `J' = D^ϕ(·,·;𝔸)` of
`𝔸 = 𝔸_{r/2,2r}(z)`. -/
def confGoodAnnulus (D : DistC → ContMetric) (ϕ : ℂ → ℂ) (α A C' r : ℝ) (z : ℂ)
    (h hbar : DistC) (f : C(ℂ, ℝ)) : Prop :=
  GM.goodAnnulusI ((D h).internal (annulus z (r / 2) (2 * r)))
    (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α A C' r z

/-- **The event family for the covering lemma**: `E_r(w)` where `act w r` holds (e.g.
`closedBall w (2r) ⊆ K` for a compact `K ⊆ V`), and the sure event elsewhere. T2 and T4 need
`act w r → 𝔸_{r/2,2r}(w) ⊆ V` for `r > 0`: off `V` the coupling says nothing about `h̄ + f` on
`ϕ(𝔸)` (and `ϕ` is arbitrary off `W`), so the non-activated family is not annulus-local. -/
def confGoodEvent (D : DistC → ContMetric) (ϕ : ℂ → ℂ) (α A C' : ℝ) (act : ℂ → ℝ → Prop)
    {Ω : Type} (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)) (w : ℂ) (r : ℝ) : Set Ω :=
  {ω | act w r → confGoodAnnulus D ϕ α A C' r w (h ω) (hbar ω) (f ω)}

lemma confGoodEvent_of_act {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {α A C' : ℝ}
    {act : ℂ → ℝ → Prop} {Ω : Type} {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} {w : ℂ} {r : ℝ}
    (ha : act w r) :
    confGoodEvent D ϕ α A C' act h hbar f w r =
      {ω | confGoodAnnulus D ϕ α A C' r w (h ω) (hbar ω) (f ω)} := by
  ext ω
  simp only [confGoodEvent, mem_ofPred_eq, ha, true_imp_iff]

lemma confGoodEvent_of_not_act {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {α A C' : ℝ}
    {act : ℂ → ℝ → Prop} {Ω : Type} {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} {w : ℂ} {r : ℝ}
    (ha : ¬ act w r) : confGoodEvent D ϕ α A C' act h hbar f w r = univ := by
  ext ω
  simp only [confGoodEvent, mem_ofPred_eq, ha, false_imp_iff, mem_univ]

/-! ## 2. Annuli -/

/-- an annulus around any centre is preconnected -/
lemma isPreconnected_annulus (z : ℂ) {a b : ℝ} (ha : 0 ≤ a) :
    IsPreconnected (annulus z a b : Set ℂ) := by
  have e : (annulus z a b : Set ℂ) = (fun w => w + z) '' (annulus 0 a b : Set ℂ) := by
    ext w
    constructor
    · intro hw
      refine ⟨w - z, ?_, sub_add_cancel w z⟩
      show a < ‖w - z - 0‖ ∧ ‖w - z - 0‖ < b
      rw [sub_zero]
      exact hw
    · rintro ⟨y, hy, rfl⟩
      show a < ‖y + z - z‖ ∧ ‖y + z - z‖ < b
      rw [add_sub_cancel_right]
      have hy' : a < ‖y - 0‖ ∧ ‖y - 0‖ < b := hy
      rwa [sub_zero] at hy'
  rw [e]
  exact (GM.Bilip.isPreconnected_annulus_zero ha).image _
    (continuous_id.add continuous_const).continuousOn

section Spheres
variable {α r : ℝ} {z : ℂ}

lemma sphere_inner_subset (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) :
    sphere z (α * r) ⊆ (annulus z (r / 2) (2 * r) : Set ℂ) := fun u hu =>
  GM.closedAnnulus_subset hα hr (mem_sphere_iff_norm.1 hu).ge
    ((mem_sphere_iff_norm.1 hu).le.trans (by nlinarith))

lemma sphere_outer_subset (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) :
    sphere z r ⊆ (annulus z (r / 2) (2 * r) : Set ℂ) := fun v hv =>
  GM.closedAnnulus_subset hα hr ((mem_sphere_iff_norm.1 hv).ge.trans' (by nlinarith))
    (mem_sphere_iff_norm.1 hv).le

end Spheres

/-! ## 3. J-form algebra -/

section JForm
variable {J J' : ℂ → ℂ → ℝ≥0∞} {k : ℝ≥0∞} {α A C' r : ℝ} {z : ℂ}

lemma midPtI_smul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (U : Set ℂ) (u v : ℂ) (t : ℝ) (x : ℂ) :
    GM.midPtI (fun a b => k * J a b) U u v t x ↔ GM.midPtI J U u v t x := by
  simp only [GM.midPtI]
  rw [mul_left_comm (ENNReal.ofReal t), mul_left_comm (ENNReal.ofReal (1 - t)),
    ENNReal.mul_right_inj hk0 hkt, ENNReal.mul_right_inj hk0 hkt]

lemma midUniqueI_smul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (U : Set ℂ) (u v : ℂ) :
    GM.MidUniqueI (fun a b => k * J a b) U u v ↔ GM.MidUniqueI J U u v := by
  simp only [GM.MidUniqueI, midPtI_smul hk0 hkt]

lemma isGeodI_smul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (U : Set ℂ) (u v : ℂ)
    (η : C(unitInterval, ℂ)) :
    GM.IsGeodI (fun a b => k * J a b) U u v η ↔ GM.IsGeodI J U u v η := by
  simp only [GM.IsGeodI]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    forall₂_congr fun s t => ?_
  rw [mul_left_comm (ENNReal.ofReal _), ENNReal.mul_right_inj hk0 hkt]

lemma bdFun_smul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (U : Set ℂ) (u : ℂ) :
    GM.bdFun (fun a b => k * J a b) U u = k * GM.bdFun J U u := by
  simp only [GM.bdFun, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hk0 hkt]

lemma lenFun_smul (P : ℝ → ℂ) (a b : ℝ) :
    GM.lenFun (fun x y => k * J x y) P a b = k * GM.lenFun J P a b := by
  simp only [GM.lenFun, ENNReal.mul_iSup, Finset.mul_sum]

lemma gaCompareBI_smul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) :
    GM.gaCompareBI (fun a b => k * J a b) (fun a b => k * J' a b) α C' r z ↔
      GM.gaCompareBI J J' α C' r z := by
  have hk : 0 < k.toReal := ENNReal.toReal_pos hk0 hkt
  unfold GM.gaCompareBI
  refine forall₂_congr fun u _ => forall₂_congr fun v _ => forall_congr' fun η => ?_
  rw [midUniqueI_smul hk0 hkt, isGeodI_smul hk0 hkt]
  refine imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, mul_left_comm C',
    mul_le_mul_iff_of_pos_left hk]

lemma gaLongI_smul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) :
    GM.gaLongI (fun a b => k * J a b) (fun a b => k * J' a b) α r z ↔ GM.gaLongI J J' α r z := by
  simp only [GM.gaLongI, bdFun_smul hk0 hkt, lenFun_smul, ENNReal.mul_lt_mul_iff_right hk0 hkt]

lemma gaAroundI_smul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) :
    GM.gaAroundI (fun a b => k * J a b) α A r z ↔ GM.gaAroundI J α A r z := by
  unfold GM.gaAroundI
  refine exists₃_congr fun a b G => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  simp only [lenFun_smul, ← ENNReal.mul_iInf_of_ne hk0 hkt]
  rw [mul_left_comm (ENNReal.ofReal A), ENNReal.mul_le_mul_iff_right hk0 hkt]

/-- **The Weyl step of [3] Lemma 3.8** (GM l. 1346): the J-form event is invariant under
multiplying `J` and `J'` by the same constant `k ∈ (0, ∞)`. -/
theorem goodAnnulusI_smul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) :
    GM.goodAnnulusI (fun a b => k * J a b) (fun a b => k * J' a b) α A C' r z ↔
      GM.goodAnnulusI J J' α A C' r z := by
  unfold GM.goodAnnulusI
  rw [gaCompareBI_smul hk0 hkt, gaLongI_smul hk0 hkt, gaAroundI_smul hk0 hkt]

lemma bdFun_congr {J₁ J₂ : ℂ → ℂ → ℝ≥0∞} {U : Set ℂ} {u : ℂ}
    (h : ∀ v ∈ U, J₁ u v = J₂ u v) : GM.bdFun J₁ U u = GM.bdFun J₂ U u := by
  unfold GM.bdFun
  exact iSup_congr fun n => iInf_congr fun y => iInf_congr fun hy => h y hy.1

/-- only the values of `J'` on `𝔸_{r/2,2r}(z) × 𝔸_{r/2,2r}(z)` enter the J-form event -/
theorem goodAnnulusI_congr_right {J'₂ : ℂ → ℂ → ℝ≥0∞} (hα : 1 / 2 < α) (hα1 : α < 1)
    (hr : 0 < r)
    (h : ∀ u ∈ (annulus z (r / 2) (2 * r) : Set ℂ), ∀ v ∈ (annulus z (r / 2) (2 * r) : Set ℂ),
      J' u v = J'₂ u v) :
    GM.goodAnnulusI J J' α A C' r z ↔ GM.goodAnnulusI J J'₂ α A C' r z := by
  unfold GM.goodAnnulusI GM.gaCompareBI GM.gaLongI
  refine and_congr ?_ (and_congr ?_ Iff.rfl)
  · refine forall₂_congr fun u hu => forall₂_congr fun v hv => forall_congr' fun η => ?_
    rw [h u (sphere_inner_subset hα hα1 hr hu) v (sphere_outer_subset hα hα1 hr hv)]
  · refine forall₂_congr fun u hu => forall₂_congr fun v hv => ?_
    have huU := sphere_inner_subset hα hα1 hr hu
    rw [h u huU v (sphere_outer_subset hα hα1 hr hv), bdFun_congr (h u huU)]

section Congr
variable {J₁ J₂ : ℂ → ℂ → ℝ≥0∞} {U : Set ℂ} {u v : ℂ}

lemma midPtI_congr (hu : u ∈ U) (hv : v ∈ U) (h : ∀ a ∈ U, ∀ b ∈ U, J₁ a b = J₂ a b) (t : ℝ)
    (x : ℂ) : GM.midPtI J₁ U u v t x ↔ GM.midPtI J₂ U u v t x := by
  unfold GM.midPtI
  refine and_congr_right fun hx => ?_
  rw [h u hu x hx, h x hx v hv, h u hu v hv]

lemma midUniqueI_congr (hu : u ∈ U) (hv : v ∈ U) (h : ∀ a ∈ U, ∀ b ∈ U, J₁ a b = J₂ a b) :
    GM.MidUniqueI J₁ U u v ↔ GM.MidUniqueI J₂ U u v := by
  unfold GM.MidUniqueI
  simp only [midPtI_congr hu hv h]

lemma isGeodI_congr (hu : u ∈ U) (hv : v ∈ U) (h : ∀ a ∈ U, ∀ b ∈ U, J₁ a b = J₂ a b)
    (η : C(unitInterval, ℂ)) : GM.IsGeodI J₁ U u v η ↔ GM.IsGeodI J₂ U u v η := by
  unfold GM.IsGeodI
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun hη =>
    forall₂_congr fun s t => ?_
  rw [h _ (hη s) _ (hη t), h u hu v hv]

/-- the `J`-length of a path with values in `U` only involves `J` on `U × U` -/
lemma lenFun_congr {P : ℝ → ℂ} {a b : ℝ} (hP : MapsTo P (Icc a b) U)
    (h : ∀ x ∈ U, ∀ y ∈ U, J₁ x y = J₂ x y) : GM.lenFun J₁ P a b = GM.lenFun J₂ P a b := by
  unfold GM.lenFun
  exact iSup_congr fun p => Finset.sum_congr rfl fun i _ =>
    h _ (hP (p.2.2.2 (i + 1))) _ (hP (p.2.2.2 i))

end Congr

/-- **only the values of `J` and `J'` on `𝔸_{r/2,2r}(z) × 𝔸_{r/2,2r}(z)` enter the J-form
event** -/
theorem goodAnnulusI_congr {J₁ J₂ J'₁ J'₂ : ℂ → ℂ → ℝ≥0∞} (hα : 1 / 2 < α) (hα1 : α < 1)
    (hr : 0 < r)
    (hJ : ∀ u ∈ (annulus z (r / 2) (2 * r) : Set ℂ), ∀ v ∈ (annulus z (r / 2) (2 * r) : Set ℂ),
      J₁ u v = J₂ u v)
    (hJ' : ∀ u ∈ (annulus z (r / 2) (2 * r) : Set ℂ), ∀ v ∈ (annulus z (r / 2) (2 * r) : Set ℂ),
      J'₁ u v = J'₂ u v) :
    GM.goodAnnulusI J₁ J'₁ α A C' r z ↔ GM.goodAnnulusI J₂ J'₂ α A C' r z := by
  unfold GM.goodAnnulusI GM.gaCompareBI GM.gaLongI GM.gaAroundI
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine forall₂_congr fun u hu => forall₂_congr fun v hv => forall_congr' fun η => ?_
    have huU := sphere_inner_subset hα hα1 hr hu
    have hvU := sphere_outer_subset hα hα1 hr hv
    rw [midUniqueI_congr huU hvU hJ, isGeodI_congr huU hvU hJ η, hJ u huU v hvU,
      hJ' u huU v hvU]
  · refine forall₂_congr fun u hu => forall₂_congr fun v hv => ?_
    have huU := sphere_inner_subset hα hα1 hr hu
    have hvU := sphere_outer_subset hα hα1 hr hv
    rw [hJ u huU v hvU, hJ' u huU v hvU, bdFun_congr (hJ u huU), bdFun_congr (hJ' u huU)]
    refine imp_congr_right fun _ => forall₃_congr fun a b P => imp_congr_right fun _ =>
      forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
        forall_congr' fun hK => ?_
    rw [lenFun_congr (fun t ht => GM.closure_annulus_subset hα hr (hK ⟨t, ht, rfl⟩)) hJ]
  · refine exists₃_congr fun a b G => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun hGA => and_congr_right fun _ => ?_
    have hmaps : MapsTo G (Icc a b) (annulus z (r / 2) (2 * r) : Set ℂ) := fun t ht =>
      GM.closure_annulus_subset hα hr (subset_closure (hGA ⟨t, ht, rfl⟩))
    rw [lenFun_congr hmaps hJ]
    have e : (⨅ x ∈ sphere z (α * r), ⨅ y ∈ sphere z r, J₁ x y) =
        ⨅ x ∈ sphere z (α * r), ⨅ y ∈ sphere z r, J₂ x y :=
      iInf_congr fun x => iInf_congr fun hx => iInf_congr fun y => iInf_congr fun hy =>
        hJ x (sphere_inner_subset hα hα1 hr hx) y (sphere_outer_subset hα hα1 hr hy)
    rw [e]

end JForm

/-! ## 4. D-forms (T4) -/

section DForm
variable {d : ContMetric} {α r : ℝ} {z : ℂ}

/-- **Condition 2 localizes geodesics** (GM l. 1354–1358; the first step of
`GM.mem_gaCompareB_iff_internal`, with an arbitrary second function `J'`): a `D`-geodesic, or a
geodesic of the internal metric, from `u ∈ ∂B_{αr}(z)` to `v ∈ ∂B_r(z)` inside
`cl 𝔸_{αr,r}(z)` has `D(u,v) ≤ D(u, ∂𝔸_{r/2,2r}(z))`. -/
theorem ofReal_le_setDist_of_gaLongI (hL : d.IsLength) [ProperSpace d.Space]
    {J' : ℂ → ℂ → ℝ≥0∞} (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hlong : GM.gaLongI (d.internal (annulus z (r / 2) (2 * r))) J' α r z)
    {u v : ℂ} (hu : u ∈ sphere z (α * r)) (hv : v ∈ sphere z r) {η : C(unitInterval, ℂ)}
    (hgeo : d.IsGeod01 u v η ∨
      GM.IsGeodI (d.internal (annulus z (r / 2) (2 * r))) (annulus z (r / 2) (2 * r)) u v η)
    (hK : ∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ)) :
    ENNReal.ofReal (d.1 (u, v)) ≤ setDist d {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) := by
  set U : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ) with hUdef
  have hUo : IsOpen U := (annulus z (r / 2) (2 * r)).isOpen
  have hUb : Bornology.IsBounded U := GM.isBounded_annulus _ _
  have huU : u ∈ U := sphere_inner_subset hα hα1 hr hu
  have hvU : v ∈ U := sphere_outer_subset hα hα1 hr hv
  by_contra hc
  rw [not_le] at hc
  have hbd : GM.bdFun (d.internal U) U u < d.internal U u v := by
    have h1 := (GM.setDist_frontier_lt_iff d hL hUo huU hvU).1 hc
    rwa [GM.setDist_frontier_eq_iSup d hL hUo hUb huU] at h1
  have hP : ContinuousOn (fun t => η (GM.pj t)) (Icc 0 1) := GM.pjPath_continuousOn η
  have h0 : η (GM.pj 0) = u := by
    rw [GM.pjPath_zero]
    rcases hgeo with hg | hg
    exacts [hg.1, hg.1]
  have h1 : η (GM.pj 1) = v := by
    rw [GM.pjPath_one]
    rcases hgeo with hg | hg
    exacts [hg.2.1, hg.2.1]
  have hlt := hlong u hu v hv (Or.inl hbd) 0 1 (fun t => η (GM.pj t)) zero_le_one hP h0 h1
    (by rintro _ ⟨t, -, rfl⟩; exact hK _)
  have hmaps : MapsTo (fun t => η (GM.pj t)) (Icc 0 1) U := fun t _ =>
    GM.closure_annulus_subset hα hr (hK _)
  rcases hgeo with hg | hg
  · have hlen : d.len (fun t => η (GM.pj t)) 0 1 ≤ ENNReal.ofReal (d.1 (u, v)) := by
      rw [GM.len_eq_lenFun]
      refine GM.lenFun_pj_le fun s t => ?_
      rw [hg.2.2 s t, ENNReal.ofReal_mul (abs_nonneg _)]
    have hle : ENNReal.ofReal (d.1 (u, v)) ≤ d.internal U u v := by
      rw [← ContMetric.edist_pt]
      exact MetricGeometry.edist_le_internalEDist _ _ _
    rw [GM.lenFun_internal d hP hmaps] at hlt
    exact absurd (hlt.trans_le (hlen.trans hle)) (lt_irrefl _)
  · exact absurd (hlt.trans_le (GM.lenFun_pj_le hg.2.2.2)) (lt_irrefl _)

/-- **internal = global** on the pairs of condition 1: under condition 2, for a `D`-geodesic in
`cl 𝔸_{αr,r}(z)` from `u ∈ ∂B_{αr}(z)` to `v ∈ ∂B_r(z)`, `D(u,v;𝔸_{r/2,2r}(z)) = D(u,v)` -/
theorem internal_eq_of_gaLongI (hL : d.IsLength) [ProperSpace d.Space]
    {J' : ℂ → ℂ → ℝ≥0∞} (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hlong : GM.gaLongI (d.internal (annulus z (r / 2) (2 * r))) J' α r z)
    {u v : ℂ} (hu : u ∈ sphere z (α * r)) (hv : v ∈ sphere z r) {η : C(unitInterval, ℂ)}
    (hgeo : d.IsGeod01 u v η) (hK : ∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ)) :
    d.internal (annulus z (r / 2) (2 * r)) u v = ENNReal.ofReal (d.1 (u, v)) :=
  GM.internal_eq_of_le d hL (annulus z (r / 2) (2 * r)).isOpen
    (sphere_inner_subset hα hα1 hr hu) (sphere_outer_subset hα hα1 hr hv)
    (ofReal_le_setDist_of_gaLongI hL hα hα1 hr hlong hu hv (Or.inl hgeo) hK)

/-- **D-form of condition 1** (abstract `J'`): under conditions 1 and 2, if the `D`-geodesic from
`u ∈ ∂B_{αr}(z)` to `v ∈ ∂B_r(z)` is unique and lies in `cl 𝔸_{αr,r}(z)`, and `J'(u,v) < ∞`,
then `J'(u,v) ≤ C' D(u,v)`. -/
theorem le_of_gaCompareBI (hL : d.IsLength) [ProperSpace d.Space]
    (hex : ∀ a b : ℂ, ∃ η, d.IsGeod01 a b η) {J' : ℂ → ℂ → ℝ≥0∞} {C' : ℝ}
    (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (h1 : GM.gaCompareBI (d.internal (annulus z (r / 2) (2 * r))) J' α C' r z)
    (h2 : GM.gaLongI (d.internal (annulus z (r / 2) (2 * r))) J' α r z)
    {u v : ℂ} (hu : u ∈ sphere z (α * r)) (hv : v ∈ sphere z r) (hJ' : J' u v ≠ ⊤)
    (huniq : GM.UniqueGeodIn d u v (closure (annulus z (α * r) r : Set ℂ))) :
    J' u v ≤ ENNReal.ofReal (C' * d.1 (u, v)) := by
  set U : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ) with hUdef
  have hUo : IsOpen U := (annulus z (r / 2) (2 * r)).isOpen
  have huU : u ∈ U := sphere_inner_subset hα hα1 hr hu
  have hvU : v ∈ U := sphere_outer_subset hα hα1 hr hv
  obtain ⟨⟨η, hη, huniq'⟩, hin⟩ := huniq
  have hηd : d.IsGeod01 u v η := hη
  have hU : d.GeodUnique u v := fun a b ha hb => (huniq' a ha).trans (huniq' b hb).symm
  have hm : GM.MidUnique d u v := GM.midUnique_of_geodUnique hex hU
  have hK : ∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ) := fun t => hin η hη ⟨t, rfl⟩
  have hloc := ofReal_le_setDist_of_gaLongI hL hα hα1 hr h2 hu hv (Or.inl hηd) hK
  have hc := h1 u hu v hv η ((GM.midUnique_iff_midUniqueI d hL hUo huU hvU hloc).1 hm)
    ((GM.isGeod01_iff_isGeodI d hL hUo huU hvU hloc η).1 hηd) hK
  rw [GM.internal_eq_of_le d hL hUo huU hvU hloc, ENNReal.toReal_ofReal (d.nonneg u v)] at hc
  rw [← ENNReal.ofReal_toReal hJ']
  exact ENNReal.ofReal_le_ofReal hc

/-- **D-form of condition 3**: a disconnecting path in `𝔸_{αr,r}(z)` with
`len(G; D) ≤ A D(∂B_{αr}(z), ∂B_r(z))` (the form of CC8a's `hgood3`) -/
theorem exists_disconnect_of_gaAroundI (hL : d.IsLength) {A : ℝ} (hα : 1 / 2 < α)
    (hα1 : α < 1) (hr : 0 < r)
    (h3 : GM.gaAroundI (d.internal (annulus z (r / 2) (2 * r))) α A r z) :
    ∃ (a' b' : ℝ) (G : ℝ → ℂ), Disconnects (G '' Icc a' b') (sphere z (α * r)) (sphere z r) ∧
      d.len G a' b' ≤ ENNReal.ofReal A * setDist d (sphere z (α * r)) (sphere z r) := by
  obtain ⟨a, b, G, -, hG, hGA, hdisc, hlen⟩ := h3
  refine ⟨a, b, G, hdisc, ?_⟩
  rw [GM.setDist_spheres_eq_internal d hL (by nlinarith : α * r < r)
      (fun w h1 h2 => GM.closedAnnulus_subset hα hr h1 h2),
    ← GM.lenFun_internal d hG (fun t ht => GM.closure_annulus_subset hα hr
      (subset_closure (hGA ⟨t, ht, rfl⟩)))]
  exact hlen

variable {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V : Set ℂ} {hbar : DistC} {f : C(ℂ, ℝ)}

/-- `D^ϕ(·,·;𝔸)` is finite on `𝔸 = 𝔸_{r/2,2r}(z) ⊆ V` when `D_{h̄+f}` is a length metric -/
theorem confMetric_annulus_ne_top (hϕ : IsConfNbhd ϕ W V)
    (hL' : (D (addFun hbar f)).IsLength) (hr : 0 < r)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V) {u v : ℂ}
    (hu : u ∈ (annulus z (r / 2) (2 * r) : Set ℂ)) (hv : v ∈ (annulus z (r / 2) (2 * r) : Set ℂ)) :
    confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f u v ≠ ⊤ :=
  (confMetric_lt_top (hϕ.mono (annulus z (r / 2) (2 * r)).isOpen hUV) hL' hu
    ((isPreconnected_annulus z (by positivity)).subset_connectedComponentIn hu subset_rfl hv)).ne

/-- **D-form of condition 1 for `D^ϕ`** (CC0 D14, "for condition 1 only an upper bound on `D^ϕ` is
needed, and `D^ϕ(u,v) ≤ D^ϕ(u,v;𝔸) = J'(u,v)`"): on `E_r(z)` with `𝔸_{r/2,2r}(z) ⊆ V`, every pair
`u ∈ ∂B_{αr}(z)`, `u' ∈ ∂B_r(z)` whose `D_h`-geodesic is unique and lies in `cl 𝔸_{αr,r}(z)` has
`D^ϕ(u,u') ≤ C' D_h(u,u')` (the form of CC8a's `hgood1`). -/
theorem confMetric_le_of_confGoodAnnulus {h : DistC} (hL : (D h).IsLength)
    (hb : LocalEvent.IsBcpt (D h)) (hϕ : IsConfNbhd ϕ W V) (hL' : (D (addFun hbar f)).IsLength)
    {A C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (hE : confGoodAnnulus D ϕ α A C' r z h hbar f) :
    ∀ u ∈ sphere z (α * r), ∀ u' ∈ sphere z r,
      GM.UniqueGeodIn (D h) u u' (closure (annulus z (α * r) r : Set ℂ)) →
        confMetric D ϕ V hbar f u u' ≤ ENNReal.ofReal (C' * (D h).1 (u, u')) := by
  intro u hu u' hu' huniq
  have := GM.properSpace_of_bcpt (D h) hb
  have hex : ∀ a b : ℂ, ∃ η, (D h).IsGeod01 a b η := fun a b =>
    GM.exists_isGeod01_of_bcpt (D h) hL hb a b
  have hJ' := confMetric_annulus_ne_top hϕ hL' hr hUV (sphere_inner_subset hα hα1 hr hu)
    (sphere_outer_subset hα hα1 hr hu')
  exact (confMetric_anti hUV u u').trans
    (le_of_gaCompareBI hL hex hα hα1 hr hE.1 hE.2.1 hu hu' hJ' huniq)

/-- **D-forms of conditions 1 and 3 on `E_r(z)`** (deterministic): the hypotheses `hgood1` (with
`C' = 1 + δ`) and `hgood3` of CC8a's `p36_pair_ext_improve`, for `d' = D^ϕ = confMetric D ϕ V h̄ f`
and the metric `D_h`. -/
theorem dForms_of_confGoodAnnulus {h : DistC} (hL : (D h).IsLength)
    (hb : LocalEvent.IsBcpt (D h)) (hϕ : IsConfNbhd ϕ W V) (hL' : (D (addFun hbar f)).IsLength)
    {A C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (hE : confGoodAnnulus D ϕ α A C' r z h hbar f) :
    (∀ u ∈ sphere z (α * r), ∀ u' ∈ sphere z r,
      GM.UniqueGeodIn (D h) u u' (closure (annulus z (α * r) r : Set ℂ)) →
        confMetric D ϕ V hbar f u u' ≤ ENNReal.ofReal (C' * (D h).1 (u, u'))) ∧
    ∃ (a' b' : ℝ) (G : ℝ → ℂ), Disconnects (G '' Icc a' b') (sphere z (α * r)) (sphere z r) ∧
      (D h).len G a' b' ≤ ENNReal.ofReal A * setDist (D h) (sphere z (α * r)) (sphere z r) :=
  ⟨confMetric_le_of_confGoodAnnulus hL hb hϕ hL' hα hα1 hr hUV hE,
    exists_disconnect_of_gaAroundI hL hα hα1 hr hE.2.2⟩

end DForm

section AS
variable {γ : ℝ} {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V : Set ℂ}
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)}

/-- **T4, almost surely** (uniformly in the centre and the radius): a.s., on every `E_r(z)` with
`𝔸_{r/2,2r}(z) ⊆ V`, the D-forms of conditions 1 and 3 hold. No coupling is needed. -/
theorem ae_dForms (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (hh : IsWholePlaneGFF h P) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) {α A C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (r : ℝ), 0 < r → (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V →
      confGoodAnnulus D ϕ α A C' r z (h ω) (hbar ω) (f ω) →
      (∀ u ∈ sphere z (α * r), ∀ u' ∈ sphere z r,
        GM.UniqueGeodIn (D (h ω)) u u' (closure (annulus z (α * r) r : Set ℂ)) →
          confMetric D ϕ V (hbar ω) (f ω) u u' ≤ ENNReal.ofReal (C' * (D (h ω)).1 (u, u'))) ∧
      ∃ (a' b' : ℝ) (G : ℝ → ℂ), Disconnects (G '' Icc a' b') (sphere z (α * r)) (sphere z r) ∧
        (D (h ω)).len G a' b' ≤
          ENNReal.ofReal A * setDist (D (h ω)) (sphere z (α * r)) (sphere z r) := by
  filter_upwards [hD.length P h (isGFFPlusCont_of_wp hh),
    GM.gm_S1_1_bcpt dfgpsLem3_8_holds hγ hγ2 (GM.gm_eq1_15 hγ hD) P h hh,
    ae_isLength_addFun hD hhb hf] with ω hL hb hL' z r hr hUV hE
  exact dForms_of_confGoodAnnulus hL hb hϕ hL' hα hα1 hr hUV hE

/-- **T4, event form**: a.s., for every `(v, r)` with `act v r` and `ω ∈ E_r(v)`, the D-forms of
conditions 1 and 3 hold (`act` must force `𝔸_{r/2,2r}(v) ⊆ V`). This is the input `hgood1`,
`hgood3` of CC8a's `p36_pair_ext_improve` with `Good v r := act v r ∧ ω ∈ E_r(v)`. -/
theorem ae_dForms_event (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (hh : IsWholePlaneGFF h P) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) {α A C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) {act : ℂ → ℝ → Prop}
    (hact : ∀ w r, 0 < r → act w r → (annulus w (r / 2) (2 * r) : Set ℂ) ⊆ V) :
    ∀ᵐ ω ∂P, ∀ (v : ℂ) (r : ℝ), 0 < r → act v r →
      ω ∈ confGoodEvent D ϕ α A C' act h hbar f v r →
      (∀ u ∈ sphere v (α * r), ∀ u' ∈ sphere v r,
        GM.UniqueGeodIn (D (h ω)) u u' (closure (annulus v (α * r) r : Set ℂ)) →
          confMetric D ϕ V (hbar ω) (f ω) u u' ≤ ENNReal.ofReal (C' * (D (h ω)).1 (u, u'))) ∧
      ∃ (a' b' : ℝ) (G : ℝ → ℂ), Disconnects (G '' Icc a' b') (sphere v (α * r)) (sphere v r) ∧
        (D (h ω)).len G a' b' ≤
          ENNReal.ofReal A * setDist (D (h ω)) (sphere v (α * r)) (sphere v r) := by
  filter_upwards [ae_dForms (C' := C') (A := A) hγ hγ2 hD hϕ hh hhb hf hα hα1] with ω hω v r hr
    ha hE
  exact hω v r hr (hact v r hr ha) (hE ha)

/-- **T4 in the exact shape of CC8a's `p36_pair_ext_improve`**: a.s., the hypotheses `hgood1`
(with `C'`; take `C' = 1 + δ`) and `hgood3` hold for `D = D_h`, `d' = D^ϕ = confMetric D ϕ V h̄ f`
and `Good v r := 0 < r ∧ act v r ∧ ω ∈ E_r(v)`. -/
theorem ae_hgood_confGoodEvent (hγ : 0 < γ) (hγ2 : γ < 2) (hD : IsStrongLQGMetric γ D)
    (hϕ : IsConfNbhd ϕ W V) (hh : IsWholePlaneGFF h P) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) {α A C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) {act : ℂ → ℝ → Prop}
    (hact : ∀ w r, 0 < r → act w r → (annulus w (r / 2) (2 * r) : Set ℂ) ⊆ V) :
    ∀ᵐ ω ∂P,
      (∀ v r, (0 < r ∧ act v r ∧ ω ∈ confGoodEvent D ϕ α A C' act h hbar f v r) →
        ∀ u ∈ sphere v (α * r), ∀ u' ∈ sphere v r,
          GM.UniqueGeodIn (D (h ω)) u u' (closure (annulus v (α * r) r : Set ℂ)) →
            confMetric D ϕ V (hbar ω) (f ω) u u' ≤ ENNReal.ofReal (C' * (D (h ω)).1 (u, u'))) ∧
      (∀ v r, (0 < r ∧ act v r ∧ ω ∈ confGoodEvent D ϕ α A C' act h hbar f v r) →
        ∃ (a' b' : ℝ) (G : ℝ → ℂ), Disconnects (G '' Icc a' b') (sphere v (α * r)) (sphere v r) ∧
          (D (h ω)).len G a' b' ≤
            ENNReal.ofReal A * setDist (D (h ω)) (sphere v (α * r)) (sphere v r)) := by
  filter_upwards [ae_dForms_event (C' := C') (A := A) hγ hγ2 hD hϕ hh hhb hf hα hα1 hact] with
    ω hω
  exact ⟨fun v r hg => (hω v r hg.1 hg.2.1 hg.2.2).1, fun v r hg => (hω v r hg.1 hg.2.1 hg.2.2).2⟩

end AS

/-! ## 5. Condition 3: probability (T3) and the union bound -/

section Prob
variable {γ : ℝ} {D : DistC → ContMetric}

/-- **T3: condition 3** ([3] Lemma 3.9, condition 3; GM l. 1391, `GM.gm_gaAround_prob` verbatim):
for `α ∈ (1/2, 1)` and `ε > 0` there is `A > 1` such that, for every whole-plane GFF `h`, every
`r > 0` and every `z`, condition 3 of `E_r(z)` (J-form) fails with probability `< ε`. The bound is
uniform in `z ∈ ℂ` and `r > 0`, and it involves neither the coupling nor `C'`. -/
theorem exists_gaAroundI_prob (hγ : 0 < γ) (hD : IsStrongLQGMetric γ D) {α : ℝ}
    (hα : 1 / 2 < α) (hα1 : α < 1) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : ℝ, 1 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        P {ω | ¬ GM.gaAroundI ((D (h ω)).internal (annulus z (r / 2) (2 * r))) α A r z} < ε := by
  obtain ⟨A, hA, H⟩ := GM.gm_gaAround_prob (GM.gm_eq1_15 hγ hD) (by linarith : (0 : ℝ) < α)
    hα1 hε
  refine ⟨A, hA, fun P _ h hh r hr z => lt_of_le_of_lt (measure_mono_ae ?_) (H P h hh r hr z)⟩
  filter_upwards [hD.length P h (isGFFPlusCont_of_wp hh)] with ω hL hω
  exact fun hg => hω ((GM.mem_gaAround_iff_internal hα hα1 hr hL).1 hg)

variable {ϕ : ℂ → ℂ} {α A C' : ℝ} {act : ℂ → ℝ → Prop}

/-- **union bound** for `E_r(w)` over its three conditions (GM l. 1395; `P` is used as an outer
measure, no measurability is needed) -/
theorem measure_compl_confGoodEvent_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)) (w : ℂ) (r : ℝ) :
    P (confGoodEvent D ϕ α A C' act h hbar f w r)ᶜ ≤
      P {ω | act w r ∧ ¬ GM.gaCompareBI ((D (h ω)).internal (annulus w (r / 2) (2 * r)))
          (confMetric D ϕ (annulus w (r / 2) (2 * r)) (hbar ω) (f ω)) α C' r w} +
        P {ω | act w r ∧ ¬ GM.gaLongI ((D (h ω)).internal (annulus w (r / 2) (2 * r)))
          (confMetric D ϕ (annulus w (r / 2) (2 * r)) (hbar ω) (f ω)) α r w} +
        P {ω | ¬ GM.gaAroundI ((D (h ω)).internal (annulus w (r / 2) (2 * r))) α A r w} := by
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans
    (add_le_add_left (measure_union_le _ _) _))
  intro ω hω
  simp only [confGoodEvent, confGoodAnnulus, GM.goodAnnulusI, mem_compl_iff, mem_ofPred_eq,
    not_imp, not_and_or] at hω
  obtain ⟨ha, h1 | h2 | h3⟩ := hω
  · exact Or.inl (Or.inl ⟨ha, h1⟩)
  · exact Or.inl (Or.inr ⟨ha, h2⟩)
  · exact Or.inr h3

/-- `P(E) ≥ p` from `P(Eᶜ) ≤ 1 − p` for a probability measure, without measurability of `E` -/
theorem ofReal_le_measure_of_compl_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Set Ω} {p : ℝ} (hp : p ≤ 1)
    (hE : P Eᶜ ≤ ENNReal.ofReal (1 - p)) : ENNReal.ofReal p ≤ P E := by
  rcases le_or_gt p 0 with hp0 | hp0
  · rw [ENNReal.ofReal_of_nonpos hp0]
    exact zero_le
  have h1 : (1 : ℝ≥0∞) ≤ P E + ENNReal.ofReal (1 - p) := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ = P (E ∪ Eᶜ) := by rw [union_compl_self]
      _ ≤ P E + P Eᶜ := measure_union_le _ _
      _ ≤ P E + ENNReal.ofReal (1 - p) := add_le_add_right hE _
  have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
    rw [← ENNReal.ofReal_add hp0.le (by linarith), add_sub_cancel, ENNReal.ofReal_one]
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (h2 ▸ h1)

/-- **`P(E_r(w)) ≥ p` from the three condition bounds** (the union of CC9b's bounds for the
activated conditions 1 and 2 with condition 3, e.g. from `exists_gaAroundI_prob`): if the three
failure probabilities are at most `e₁, e₂, e₃ ≥ 0` with `e₁ + e₂ + e₃ ≤ 1 − p`, then
`P(E_r(w)) ≥ p`. No measurability is needed. -/
theorem ofReal_le_measure_confGoodEvent {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)) (w : ℂ) (r : ℝ)
    {p e₁ e₂ e₃ : ℝ} (hp : p ≤ 1) (he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂) (he₃ : 0 ≤ e₃)
    (hsum : e₁ + e₂ + e₃ ≤ 1 - p)
    (h1 : P {ω | act w r ∧ ¬ GM.gaCompareBI ((D (h ω)).internal (annulus w (r / 2) (2 * r)))
      (confMetric D ϕ (annulus w (r / 2) (2 * r)) (hbar ω) (f ω)) α C' r w} ≤ ENNReal.ofReal e₁)
    (h2 : P {ω | act w r ∧ ¬ GM.gaLongI ((D (h ω)).internal (annulus w (r / 2) (2 * r)))
      (confMetric D ϕ (annulus w (r / 2) (2 * r)) (hbar ω) (f ω)) α r w} ≤ ENNReal.ofReal e₂)
    (h3 : P {ω | ¬ GM.gaAroundI ((D (h ω)).internal (annulus w (r / 2) (2 * r))) α A r w} ≤
      ENNReal.ofReal e₃) :
    ENNReal.ofReal p ≤ P (confGoodEvent D ϕ α A C' act h hbar f w r) := by
  refine ofReal_le_measure_of_compl_le hp ((measure_compl_confGoodEvent_le P h hbar f w r).trans ?_)
  calc _ ≤ ENNReal.ofReal e₁ + ENNReal.ofReal e₂ + ENNReal.ofReal e₃ :=
        add_le_add (add_le_add h1 h2) h3
    _ = ENNReal.ofReal (e₁ + e₂ + e₃) := by
        rw [ENNReal.ofReal_add (add_nonneg he₁ he₂) he₃, ENNReal.ofReal_add he₁ he₂]
    _ ≤ ENNReal.ofReal (1 - p) := ENNReal.ofReal_le_ofReal hsum

end Prob

end SmallGammaGeodesics.CC
