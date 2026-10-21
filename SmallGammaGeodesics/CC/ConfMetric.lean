import SmallGammaGeodesics.CC.Pullback
import LQGMetric.Metric.InternalC
import LQGMetric.Metric.WeylLQG
import LQGMetric.Papers.GM.S3.GoodAnnulusMeas
import LQGMetric.Meas.Internal

/-!
# The structure of the transported metric `D^ϕ` (track CC, packet CC2, target T1)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D2**, for Gwynne–Miller
arXiv:1905.00384 ([3]), (1.12). For `IsConfNbhd ϕ W V` (`ϕ` holomorphic and injective on an open
`W ⊇ closure V`), `U = ϕ '' V`, a field `h̄` and a continuous `f`, the transported metric is
`D^ϕ(z, w) = confMetric D ϕ V h̄ f z w = D_{h̄+f}(ϕ z, ϕ w; U)` (`Core/Interfaces.lean`).

Results (deterministic unless stated):
* **pseudometric**: `confMetric_comm`, `confMetric_self` (on `V`), `confMetric_triangle`;
  monotonicity in the domain `confMetric_anti`;
* **continuity** on `V × V` when `D_{h̄+f}` is a length metric: `continuousOn_confMetric`
  (LM Lemma 1.1 = `ContMetric.continuousOn_internal`, composed with `ϕ × ϕ`);
* **finiteness** on each connected component of `V`: `confMetric_lt_top`, from the generic
  `lt_top_of_mem_connectedComponentIn` (a continuous `[0,∞]`-valued pseudometric is finite on
  connected components);
* **lengths**: `lenFun_confMetric`: the `D^ϕ`-length (`GM.lenFun`) of a path in `V` is the
  `D_{h̄+f}`-length of its image under `ϕ` (BBI 2.3.12(1) = `GM.lenFun_internal`);
  `confMetric_le_lenFun`;
* **length metric and internal of internal**: with `funInternal d A` the infimum of the `d`-lengths
  of paths in `A`, `funInternal_confMetric`: for `A ⊆ V`,
  `funInternal (confMetric D ϕ V h̄ f) A = confMetric D ϕ A h̄ f` on `W × W`; with `A = V`,
  `confMetric_eq_funInternal` says that `D^ϕ` is a length metric on `V`;
* `confMetric_eq_of_lt_iInf_frontier` (for [3] Lemma 3.5 / CC0 D11): if
  `D^ϕ(u, v) < D^ϕ(u, ∂A)` with `u ∈ A ⊆ V`, then `v ∈ A` and `D^ϕ(u, v; A) = D^ϕ(u, v)`;
* **almost surely** (`h̄` a whole-plane GFF, `f` a measurable random continuous function):
  `ae_isLength_addFun`, `ae_continuousOn_confMetric`, `ae_confMetric_lt_top`, uniformly in the
  map `(ϕ, W, V)`;
* **Weyl** (a.s., uniformly in the map and in the continuous function):
  `ae_internal_addFun_eq_weylScaleOn` (`D_{h̄+g}(·,·;U) = weylScaleOn ξ g (D h̄) U` for every open
  `U`), `ae_confMetric_eq_weylScaleOn`, `ae_confMetric_congr` (`g₁ = g₂` on `U` gives equal
  transported metrics), `ae_confMetric_add_const` and `ae_confMetric_addConst` (constants give
  factors `e^{ξ c}`), `ae_confMetric_mem_Icc` (two-sided bounds);
* **measurability in `ω`**: `measurable_chainInf_addFun` and `ae_confMetric_eq_chainInf` (a
  measurable version through LQGMetric's chain formula `ContMetric.chainInf`),
  `aemeasurable_confMetric`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.MetricGeometry

/-! ## 0. Neighbourhoods -/

section Nbhd

variable {ϕ : ℂ → ℂ} {W V A : Set ℂ}

/-- An open subset of `V` is again a conformal neighbourhood domain. -/
theorem IsConfNbhd.mono (hϕ : IsConfNbhd ϕ W V) (hA : IsOpen A) (hAV : A ⊆ V) :
    IsConfNbhd ϕ W A where
  isOpen_W := hϕ.isOpen_W
  isOpen_V := hA
  isBounded_V := hϕ.isBounded_V.subset hAV
  closure_subset := (closure_mono hAV).trans hϕ.closure_subset
  differentiableOn := hϕ.differentiableOn
  injOn := hϕ.injOn

theorem IsConfNbhd.continuousOn (hϕ : IsConfNbhd ϕ W V) : ContinuousOn ϕ W :=
  hϕ.differentiableOn.continuousOn

/-- `Function.invFunOn ϕ W` is a left inverse of `ϕ` on `W`. -/
theorem IsConfNbhd.invFunOn_apply (hϕ : IsConfNbhd ϕ W V) {z : ℂ} (hz : z ∈ W) :
    Function.invFunOn ϕ W (ϕ z) = z :=
  hϕ.injOn.leftInvOn_invFunOn hz

end Nbhd

variable {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V A : Set ℂ} {hbar : DistC} {f : C(ℂ, ℝ)}

theorem confMetric_def (D : DistC → ContMetric) (ϕ : ℂ → ℂ) (V : Set ℂ) (hbar : DistC)
    (f : C(ℂ, ℝ)) (z w : ℂ) :
    confMetric D ϕ V hbar f z w = (D (addFun hbar f)).internal (ϕ '' V) (ϕ z) (ϕ w) := rfl

/-! ## 1. `D^ϕ` is a `[0,∞]`-valued pseudometric on `V` -/

theorem confMetric_comm (z w : ℂ) :
    confMetric D ϕ V hbar f z w = confMetric D ϕ V hbar f w z :=
  internalEDist_comm _ _ _

theorem confMetric_self {z : ℂ} (hz : z ∈ V) : confMetric D ϕ V hbar f z z = 0 :=
  internalEDist_self ⟨ϕ z, mem_image_of_mem ϕ hz, rfl⟩

theorem confMetric_triangle (x y z : ℂ) :
    confMetric D ϕ V hbar f x z ≤ confMetric D ϕ V hbar f x y + confMetric D ϕ V hbar f y z :=
  internalEDist_triangle _ _ _ _

/-- A smaller domain gives a larger transported metric: `D^ϕ(·,·) ≤ D^ϕ(·,·;A)` for `A ⊆ V`. -/
theorem confMetric_anti (hAV : A ⊆ V) (z w : ℂ) :
    confMetric D ϕ V hbar f z w ≤ confMetric D ϕ A hbar f z w :=
  internalEDist_anti (image_mono (image_mono hAV)) _ _

/-! ## 2. Continuity on `V × V` -/

/-- **Continuity** (CC0 D2.2): if `D_{h̄+f}` is a length metric, `D^ϕ` is continuous on `V × V`. -/
theorem continuousOn_confMetric (hϕ : IsConfNbhd ϕ W V) (hlen : (D (addFun hbar f)).IsLength) :
    ContinuousOn (fun p : ℂ × ℂ => confMetric D ϕ V hbar f p.1 p.2) (V ×ˢ V) := by
  have hc := (D (addFun hbar f)).continuousOn_internal hlen hϕ.isOpen_image
  have hϕc : ContinuousOn ϕ V := hϕ.continuousOn.mono hϕ.subset
  have hmaps : MapsTo (Prod.map ϕ ϕ) (V ×ˢ V) ((ϕ '' V) ×ˢ (ϕ '' V)) := fun p hp =>
    ⟨mem_image_of_mem ϕ hp.1, mem_image_of_mem ϕ hp.2⟩
  exact hc.comp (hϕc.prodMap hϕc) hmaps

/-! ## 3. Finiteness on connected components -/

/-- A `[0,∞]`-valued pseudometric on an open set `V`, continuous on `V × V`, is finite on each
connected component of `V`: the points at finite distance from `z` and those at infinite distance
form two disjoint open sets covering `V`. -/
theorem lt_top_of_mem_connectedComponentIn {d : ℂ → ℂ → ℝ≥0∞} {V : Set ℂ} (hV : IsOpen V)
    (hd : ContinuousOn (fun p : ℂ × ℂ => d p.1 p.2) (V ×ˢ V)) (hself : ∀ z ∈ V, d z z = 0)
    (hsymm : ∀ z w, d z w = d w z) (htri : ∀ x y z, d x z ≤ d x y + d y z) {z w : ℂ}
    (hz : z ∈ V) (hw : w ∈ connectedComponentIn V z) : d z w < ⊤ := by
  -- near each `x ∈ V`, the points `y ∈ V` have `d x y < 1`
  have hloc : ∀ x ∈ V, ∀ᶠ y in 𝓝 x, y ∈ V ∧ d x y < 1 := by
    intro x hx
    have hc : ContinuousAt (fun p : ℂ × ℂ => d p.1 p.2) (x, x) :=
      (hd (x, x) ⟨hx, hx⟩).continuousAt (prod_mem_nhds (hV.mem_nhds hx) (hV.mem_nhds hx))
    have h1 : ∀ᶠ p in 𝓝 (x, x), d p.1 p.2 < 1 :=
      hc.eventually (gt_mem_nhds (show d x x < 1 by rw [hself x hx]; exact zero_lt_one))
    have h2 : Tendsto (fun y : ℂ => (x, y)) (𝓝 x) (𝓝 (x, x)) :=
      (continuous_const.prodMk continuous_id).tendsto x
    exact Filter.Eventually.and (hV.mem_nhds hx) (h2.eventually h1)
  set S : Set ℂ := {x | x ∈ V ∧ d z x < ⊤} with hSdef
  set T : Set ℂ := {x | x ∈ V ∧ d z x = ⊤} with hTdef
  have hS : IsOpen S := isOpen_iff_mem_nhds.2 fun x hx => (hloc x hx.1).mono fun y hy =>
    ⟨hy.1, lt_of_le_of_lt (htri z x y) (ENNReal.add_lt_top.2 ⟨hx.2, hy.2.trans ENNReal.one_lt_top⟩)⟩
  have hT : IsOpen T := isOpen_iff_mem_nhds.2 fun x hx => (hloc x hx.1).mono fun y hy => by
    refine ⟨hy.1, ?_⟩
    by_contra hne
    have h3 : d z x ≤ d z y + d y x := htri z y x
    rw [hx.2, hsymm y x] at h3
    exact absurd h3 (not_le.2 (ENNReal.add_lt_top.2
      ⟨lt_top_iff_ne_top.2 hne, hy.2.trans ENNReal.one_lt_top⟩))
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    intro x hxS hxT
    exact (ne_of_lt hxS.2) hxT.2
  have hcover : connectedComponentIn V z ⊆ S ∪ T := by
    intro x hx
    have hxV : x ∈ V := connectedComponentIn_subset V z hx
    by_cases hfin : d z x = ⊤
    · exact Or.inr ⟨hxV, hfin⟩
    · exact Or.inl ⟨hxV, lt_top_iff_ne_top.2 hfin⟩
  have hne : (connectedComponentIn V z ∩ S).Nonempty :=
    ⟨z, mem_connectedComponentIn hz, hz, by rw [hself z hz]; exact ENNReal.zero_lt_top⟩
  exact (isPreconnected_connectedComponentIn.subset_left_of_subset_union hS hT hdisj hcover hne
    hw).2

/-- **Finiteness** (CC0 D2.3): if `D_{h̄+f}` is a length metric, `D^ϕ` is finite on each connected
component of `V`. -/
theorem confMetric_lt_top (hϕ : IsConfNbhd ϕ W V) (hlen : (D (addFun hbar f)).IsLength) {z w : ℂ}
    (hz : z ∈ V) (hw : w ∈ connectedComponentIn V z) : confMetric D ϕ V hbar f z w < ⊤ :=
  lt_top_of_mem_connectedComponentIn hϕ.isOpen_V (continuousOn_confMetric hϕ hlen)
    (fun _ hx => confMetric_self hx) confMetric_comm confMetric_triangle hz hw

/-! ## 4. Lengths -/

/-- `GM.lenFun` is monotone in the right endpoint. -/
theorem lenFun_mono_right {J : ℂ → ℂ → ℝ≥0∞} (P : ℝ → ℂ) {a s b : ℝ} (hsb : s ≤ b) :
    GM.lenFun J P a s ≤ GM.lenFun J P a b :=
  iSup_le fun p => le_iSup_of_le
    ⟨p.1, p.2.1, p.2.2.1, fun i => Icc_subset_Icc le_rfl hsb (p.2.2.2 i)⟩ le_rfl

/-- **Lengths** (CC0 D2.4): the `D^ϕ`-length of a path in `V` is the `D_{h̄+f}`-length of its image
under `ϕ`. -/
theorem lenFun_confMetric (hϕ : IsConfNbhd ϕ W V) {P : ℝ → ℂ} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hPV : MapsTo P (Icc a b) V) :
    GM.lenFun (confMetric D ϕ V hbar f) P a b = (D (addFun hbar f)).len (ϕ ∘ P) a b := by
  have hϕP : ContinuousOn (ϕ ∘ P) (Icc a b) := (hϕ.continuousOn.mono hϕ.subset).comp hP hPV
  exact GM.lenFun_internal (D (addFun hbar f)) hϕP fun t ht => mem_image_of_mem ϕ (hPV ht)

/-- `D^ϕ(·,·;A)` between the endpoints of a path in `A ⊆ V` is at most its `D^ϕ`-length. -/
theorem confMetric_le_lenFun (hϕ : IsConfNbhd ϕ W V) (hAV : A ⊆ V) {P : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) (hPA : MapsTo P (Icc a b) A) :
    confMetric D ϕ A hbar f (P a) (P b) ≤ GM.lenFun (confMetric D ϕ V hbar f) P a b := by
  rw [lenFun_confMetric hϕ hP (hPA.mono_right hAV)]
  have hc : ContinuousOn ((D (addFun hbar f)).pt ∘ (ϕ ∘ P)) (Icc a b) :=
    (D (addFun hbar f)).continuous_pt.comp_continuousOn
      ((hϕ.continuousOn.mono hϕ.subset).comp hP (hPA.mono_right hAV))
  exact internalEDist_le_curveLength hab hc fun t ht =>
    ⟨ϕ (P t), mem_image_of_mem ϕ (hPA ht), rfl⟩

/-! ## 5. The length structure: internal metrics of `D^ϕ` -/

/-- The **internal metric of a `[0,∞]`-valued function** `d` on `A` (GM (1.5) with lengths computed by
`GM.lenFun d`): the infimum of the `d`-lengths of paths in `A`. -/
def funInternal (d : ℂ → ℂ → ℝ≥0∞) (A : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ γ : {γ : Path z w // ∀ t, γ t ∈ A}, GM.lenFun d γ.1.extend 0 1

theorem funInternal_le {d : ℂ → ℂ → ℝ≥0∞} {z w : ℂ} (γ : Path z w) (hγ : ∀ t, γ t ∈ A) :
    funInternal d A z w ≤ GM.lenFun d γ.extend 0 1 :=
  iInf_le_of_le ⟨γ, hγ⟩ le_rfl

/-- **Internal of internal** (CC0 D2.4): for `A ⊆ V`, the internal metric of `D^ϕ` on `A` is
`D_{h̄+f}(ϕ ·, ϕ ·; ϕ(A)) = confMetric D ϕ A h̄ f`, at all points of `W`. Paths in `A` and paths in
`ϕ(A)` correspond under the homeomorphism `ϕ : A → ϕ(A)` and have the same lengths. -/
theorem funInternal_confMetric (hϕ : IsConfNbhd ϕ W V) (hAV : A ⊆ V) {z w : ℂ} (hz : z ∈ W)
    (hw : w ∈ W) : funInternal (confMetric D ϕ V hbar f) A z w = confMetric D ϕ A hbar f z w := by
  set D' := D (addFun hbar f) with hD'
  set ψ : ℂ → ℂ := Function.invFunOn ϕ W with hψdef
  have hψ : ∀ x ∈ W, ψ (ϕ x) = x := fun x hx => hϕ.invFunOn_apply hx
  have hψc : ContinuousOn ψ (ϕ '' W) :=
    continuousOn_leftInv hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ
  have hAW : A ⊆ W := hAV.trans hϕ.subset
  refine le_antisymm ?_ ?_
  · -- pull back the paths of `D'` in `ϕ '' A` along `ψ`
    show funInternal (confMetric D ϕ V hbar f) A z w ≤
      internalEDist (D'.pt '' (ϕ '' A)) (D'.pt (ϕ z)) (D'.pt (ϕ w))
    refine le_iInf fun γ' => ?_
    obtain ⟨γ', hγ'⟩ := γ'
    have hmem : ∀ t, D'.unpt (γ' t) ∈ ϕ '' A := fun t =>
      (D'.mem_image_pt (z := D'.unpt (γ' t))).1 (hγ' t)
    have hmemW : ∀ t, D'.unpt (γ' t) ∈ ϕ '' W := fun t => image_mono hAW (hmem t)
    let γ : Path z w :=
      { toFun := fun t => ψ (D'.unpt (γ' t))
        continuous_toFun := hψc.comp_continuous (D'.continuous_unpt.comp γ'.continuous) hmemW
        source' := by
          show ψ (D'.unpt (γ' 0)) = z
          rw [γ'.source]
          exact hψ z hz
        target' := by
          show ψ (D'.unpt (γ' 1)) = w
          rw [γ'.target]
          exact hψ w hw }
    have hγA : ∀ t, γ t ∈ A := fun t => by
      obtain ⟨a, ha, hae⟩ := hmem t
      show ψ (D'.unpt (γ' t)) ∈ A
      rw [← hae, hψ a (hAW ha)]
      exact ha
    have hext : D'.pt ∘ (ϕ ∘ γ.extend) = γ'.extend := by
      funext t
      show D'.pt (ϕ (ψ (D'.unpt (γ'.extend t)))) = γ'.extend t
      have hmt : D'.unpt (γ'.extend t) ∈ ϕ '' W := hmemW (Set.projIcc 0 1 zero_le_one t)
      rw [apply_leftInv hψ hmt]
      rfl
    have hlen : GM.lenFun (confMetric D ϕ V hbar f) γ.extend 0 1 = pathLength γ' := by
      rw [lenFun_confMetric hϕ γ.continuous_extend.continuousOn fun t _ => hAV (hγA _)]
      show curveLength (D'.pt ∘ (ϕ ∘ γ.extend)) 0 1 = curveLength γ'.extend 0 1
      rw [hext]
    exact (funInternal_le γ hγA).trans_eq hlen
  · refine le_iInf fun γ => ?_
    have h := confMetric_le_lenFun (D := D) (hbar := hbar) (f := f) hϕ hAV zero_le_one
      γ.1.continuous_extend.continuousOn fun t _ => γ.2 _
    rwa [Path.extend_zero, Path.extend_one] at h

/-- **`D^ϕ` is a length metric on `V`** (CC0 D2.4, used in [3] Step 3): `D^ϕ(z, w)` is the infimum
of the `D^ϕ`-lengths of paths in `V` from `z` to `w`. -/
theorem confMetric_eq_funInternal (hϕ : IsConfNbhd ϕ W V) {z w : ℂ} (hz : z ∈ W) (hw : w ∈ W) :
    confMetric D ϕ V hbar f z w = funInternal (confMetric D ϕ V hbar f) V z w :=
  (funInternal_confMetric hϕ subset_rfl hz hw).symm

/-- **Distances below the distance to `∂A` are realized inside `A`** ([3] Lemma 3.5 chaining, CC0
D11; the length-metric property of `D^ϕ` on `V`): for `u ∈ A ⊆ V` (`A` open) and `v ∈ V` with
`D^ϕ(u, v) < D^ϕ(u, ∂A ∩ V)`, the point `v` lies in `A` and `D^ϕ(u, v; A) = D^ϕ(u, v)`. -/
theorem confMetric_eq_of_lt_iInf_frontier (hϕ : IsConfNbhd ϕ W V) (hA : IsOpen A) (hAV : A ⊆ V)
    {u v : ℂ} (hu : u ∈ A) (hv : v ∈ V)
    (hlt : confMetric D ϕ V hbar f u v < ⨅ y ∈ frontier A ∩ V, confMetric D ϕ V hbar f u y) :
    v ∈ A ∧ confMetric D ϕ A hbar f u v = confMetric D ϕ V hbar f u v := by
  set d := confMetric D ϕ V hbar f with hd
  set bd := ⨅ y ∈ frontier A ∩ V, d u y with hbd
  have huV : u ∈ V := hAV hu
  -- a path in `V` from `u` of `d`-length `< bd` stays in `A`
  have hstay : ∀ {x : ℂ} (γ : Path u x), (∀ t, γ t ∈ V) → GM.lenFun d γ.extend 0 1 < bd →
      ∀ t, γ t ∈ A := by
    intro x γ hγV hlen t
    by_contra hnot
    have hc : ContinuousOn γ.extend (Icc 0 1) := γ.continuous_extend.continuousOn
    obtain ⟨s, hs, hsA, hbefore⟩ := exists_first_hit hc hA.isClosed_compl
      ⟨t, t.2, by rw [Path.extend_extends']; exact hnot⟩
    have hs0 : 0 < s := by
      rcases hs.1.eq_or_lt with h | h
      · exfalso
        rw [← h, Path.extend_zero] at hsA
        exact hsA hu
      · exact h
    have hsV : γ.extend s ∈ V := by
      rw [Path.extend_apply γ hs]
      exact hγV _
    have hNe : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
    have hfr : γ.extend s ∈ frontier A := by
      refine ⟨mem_closure_of_tendsto
        ((γ.continuous_extend.tendsto s).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun r hr => not_not.1 (hbefore r hr)), ?_⟩
      rw [hA.interior_eq]
      exact hsA
    have h1 : d u (γ.extend s) ≤ GM.lenFun d γ.extend 0 s := by
      have h := confMetric_le_lenFun (D := D) (hbar := hbar) (f := f) hϕ subset_rfl hs.1
        (hc.mono (Icc_subset_Icc le_rfl hs.2)) fun r hr => by
          rw [Path.extend_apply γ ⟨hr.1, hr.2.trans hs.2⟩]
          exact hγV _
      rwa [Path.extend_zero] at h
    have h2 : GM.lenFun d γ.extend 0 s ≤ GM.lenFun d γ.extend 0 1 := lenFun_mono_right _ hs.2
    have h3 : bd ≤ d u (γ.extend s) := iInf₂_le _ ⟨hfr, hsV⟩
    exact absurd (h3.trans (h1.trans h2)) (not_le.2 hlen)
  have hdV : d u v = funInternal d V u v :=
    confMetric_eq_funInternal hϕ (hϕ.subset huV) (hϕ.subset hv)
  -- `D^ϕ(u, v; A) ≤ c` for every `c > D^ϕ(u, v)`, and `v ∈ A`
  have key : ∀ c, d u v < c → v ∈ A ∧ confMetric D ϕ A hbar f u v ≤ c := by
    intro c hc
    have hlt' : funInternal d V u v < min c bd := by
      rw [← hdV]
      exact lt_min hc hlt
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.1 hlt'
    have hγA := hstay γ.1 γ.2 (hγ.trans_le (min_le_right _ _))
    have hvA : v ∈ A := by
      have := hγA 1
      rwa [γ.1.target] at this
    refine ⟨hvA, ?_⟩
    rw [← funInternal_confMetric hϕ hAV (hϕ.subset huV) (hϕ.subset hv)]
    exact (funInternal_le γ.1 hγA).trans (hγ.trans_le (min_le_left _ _)).le
  obtain ⟨hvA, -⟩ := key bd hlt
  refine ⟨hvA, le_antisymm (le_of_forall_gt_imp_ge_of_dense fun c hc => (key c hc).2)
    (confMetric_anti hAV u v)⟩

/-! ## 6. Constants in Weyl scaling and in the field (deterministic) -/

/-- Adding a constant `c` to the Weyl function: lower bound `e^{ξ c} weylScaleOn ξ g ≤ weylScaleOn ξ (g + c)`
(the cost of each admissible path is multiplied by `e^{ξ c}`). -/
theorem le_weylScaleOn_add_const (ξ : ℝ) (g : C(ℂ, ℝ)) (c : ℝ) (D₀ : ContMetric) (U : Set ℂ)
    (z w : ℂ) :
    ENNReal.ofReal (Real.exp (ξ * c)) * weylScaleOn ξ g D₀ U z w ≤
      weylScaleOn ξ (g + ContinuousMap.const ℂ c) D₀ U z w := by
  refine le_weylScaleOn fun L Q hL hc hu h0 h1 hU => ?_
  have e : ∀ t, ENNReal.ofReal (Real.exp (ξ * (g + ContinuousMap.const ℂ c) (Q t))) =
      ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (Real.exp (ξ * g (Q t))) := fun t => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  simp only [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  gcongr
  exact weylScaleOn_le hL hc hu h0 h1 hU

/-- `weylScaleOn ξ (g + c) D U = e^{ξ c} weylScaleOn ξ g D U`. -/
theorem weylScaleOn_add_const (ξ : ℝ) (g : C(ℂ, ℝ)) (c : ℝ) (D₀ : ContMetric) (U : Set ℂ)
    (z w : ℂ) :
    weylScaleOn ξ (g + ContinuousMap.const ℂ c) D₀ U z w =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScaleOn ξ g D₀ U z w := by
  refine le_antisymm ?_ (le_weylScaleOn_add_const ξ g c D₀ U z w)
  have h1 := le_weylScaleOn_add_const ξ (g + ContinuousMap.const ℂ c) (-c) D₀ U z w
  have h2 : weylScaleOn ξ (g + ContinuousMap.const ℂ c + ContinuousMap.const ℂ (-c)) D₀ U z w =
      weylScaleOn ξ g D₀ U z w := weylScaleOn_congr fun x _ => by
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  rw [h2] at h1
  have hmul : ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (Real.exp (ξ * -c)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_neg, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  calc weylScaleOn ξ (g + ContinuousMap.const ℂ c) D₀ U z w
      = ENNReal.ofReal (Real.exp (ξ * c)) * (ENNReal.ofReal (Real.exp (ξ * -c)) *
          weylScaleOn ξ (g + ContinuousMap.const ℂ c) D₀ U z w) := by
        rw [← mul_assoc, hmul, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (ξ * c)) * weylScaleOn ξ g D₀ U z w := by gcongr

private theorem ofCont_add_cc2 (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  unfold ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

/-- `(h + c) + g = h + (g + c)`. -/
theorem addFun_addConst_eq_addFun (h : DistC) (c : ℝ) (g : C(ℂ, ℝ)) :
    addFun (addConst h c) g = addFun h (g + ContinuousMap.const ℂ c) := by
  simp only [addConst, addFun, ofCont_add_cc2]
  abel

/-! ## 7. Almost-sure structure -/

section AS

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- A whole-plane GFF plus a measurable random continuous function is a GFF plus a continuous
function. -/
theorem isGFFPlusCont_addFun_of_wp {hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)}
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f) :
    IsGFFPlusCont (fun ω => addFun (hbar ω) (f ω)) P := by
  refine ⟨measurable_addFun.comp (hhb.measurable.prodMk hf), f, hf, ?_⟩
  have e : (fun ω => addFun (hbar ω) (f ω) - ofCont (f ω)) = hbar := by
    funext ω
    simp only [addFun, add_sub_cancel_right]
  rw [e]
  exact hhb

omit [IsProbabilityMeasure P] in
/-- A whole-plane GFF is a GFF plus a continuous function. -/
theorem isGFFPlusCont_of_wp {h : Ω → DistC} (hh : IsWholePlaneGFF h P) : IsGFFPlusCont h P := by
  have e : (fun ω => addFun (h ω) ((fun _ => (0 : C(ℂ, ℝ))) ω)) = h := by
    funext ω
    have h0 : ofCont 0 = 0 := by
      have := ofCont_add_cc2 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    simp only [addFun, h0, add_zero]
  have := isGFFPlusCont_addFun_of_wp hh (measurable_const : Measurable fun _ : Ω => (0 : C(ℂ, ℝ)))
  rwa [e] at this

variable {hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)}

/-- Axiom I for `h̄ + f`: a.s. `D_{h̄+f}` is a length metric. -/
theorem ae_isLength_addFun (hD : IsStrongLQGMetric γ D) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) : ∀ᵐ ω ∂P, (D (addFun (hbar ω) (f ω))).IsLength :=
  hD.length P _ (isGFFPlusCont_addFun_of_wp hhb hf)

/-- **T1, continuity, a.s.**: a.s., for every conformal neighbourhood `(ϕ, W, V)`, `D^ϕ` is
continuous on `V × V`. -/
theorem ae_continuousOn_confMetric (hD : IsStrongLQGMetric γ D) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V →
      ContinuousOn (fun p : ℂ × ℂ => confMetric D ϕ V (hbar ω) (f ω) p.1 p.2) (V ×ˢ V) :=
  (ae_isLength_addFun hD hhb hf).mono fun _ hω _ _ _ hϕ => continuousOn_confMetric hϕ hω

/-- **T1, finiteness, a.s.**: a.s., for every conformal neighbourhood `(ϕ, W, V)`, `D^ϕ` is finite on
each connected component of `V`. -/
theorem ae_confMetric_lt_top (hD : IsStrongLQGMetric γ D) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ z ∈ V,
      ∀ w ∈ connectedComponentIn V z, confMetric D ϕ V (hbar ω) (f ω) z w < ⊤ :=
  (ae_isLength_addFun hD hhb hf).mono fun _ hω _ _ _ hϕ _ hz _ hw => confMetric_lt_top hϕ hω hz hw

/-! ## 8. Weyl scaling, almost surely -/

/-- **Weyl, internal form** (CC0 D2.5): a.s., for every open `U` and every continuous `g`,
`D_{h̄+g}(·,·;U) = weylScaleOn ξ g (D h̄) U` (Axiom III for `h̄` and `weylScaleOn_eq_internal`). -/
theorem ae_internal_addFun_eq_weylScaleOn (hD : IsStrongLQGMetric γ D)
    (hhb : IsGFFPlusCont hbar P) :
    ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → ∀ (g : C(ℂ, ℝ)) (y y' : ℂ),
      (D (addFun (hbar ω) g)).internal U y y' = weylScaleOn (xiGamma γ) g (D (hbar ω)) U y y' := by
  filter_upwards [hD.weyl P hbar hhb] with ω hw U hU g y y'
  exact (weylScaleOn_eq_internal (D (addFun (hbar ω) g)) (fun x x' => (hw g x x').symm) hU y y').symm

/-- **T1, Weyl** (CC0 D2.5): a.s., for every conformal neighbourhood and every continuous `g`,
`D^ϕ = weylScaleOn ξ g (D h̄) (ϕ '' V)` at `(ϕ ·, ϕ ·)`. -/
theorem ae_confMetric_eq_weylScaleOn (hD : IsStrongLQGMetric γ D) (hhb : IsGFFPlusCont hbar P) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ (g : C(ℂ, ℝ)) (z w : ℂ),
      confMetric D ϕ V (hbar ω) g z w =
        weylScaleOn (xiGamma γ) g (D (hbar ω)) (ϕ '' V) (ϕ z) (ϕ w) :=
  (ae_internal_addFun_eq_weylScaleOn hD hhb).mono fun _ hω ϕ _ _ hϕ g z w =>
    hω _ hϕ.isOpen_image g (ϕ z) (ϕ w)

/-- **T1, Weyl locality** (CC0 D2.5): a.s., if `g₁ = g₂` on `ϕ '' V`, the transported metrics agree. -/
theorem ae_confMetric_congr (hD : IsStrongLQGMetric γ D) (hhb : IsGFFPlusCont hbar P) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ g₁ g₂ : C(ℂ, ℝ),
      (∀ x ∈ ϕ '' V, g₁ x = g₂ x) → ∀ z w : ℂ,
        confMetric D ϕ V (hbar ω) g₁ z w = confMetric D ϕ V (hbar ω) g₂ z w :=
  (ae_confMetric_eq_weylScaleOn hD hhb).mono fun _ hω ϕ W V hϕ g₁ g₂ hg z w => by
    rw [hω ϕ W V hϕ g₁ z w, hω ϕ W V hϕ g₂ z w]
    exact weylScaleOn_congr fun x hx => by rw [hg x hx]

/-- **T1, constants in `f`** (CC0 D2.5): a.s., `D^ϕ` for `g + c` is `e^{ξ c}` times `D^ϕ` for `g`. -/
theorem ae_confMetric_add_const (hD : IsStrongLQGMetric γ D) (hhb : IsGFFPlusCont hbar P) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ (g : C(ℂ, ℝ)) (c : ℝ) (z w : ℂ),
      confMetric D ϕ V (hbar ω) (g + ContinuousMap.const ℂ c) z w =
        ENNReal.ofReal (Real.exp (xiGamma γ * c)) * confMetric D ϕ V (hbar ω) g z w :=
  (ae_confMetric_eq_weylScaleOn hD hhb).mono fun _ hω ϕ W V hϕ g c z w => by
    rw [hω ϕ W V hϕ _ z w, hω ϕ W V hϕ g z w]
    exact weylScaleOn_add_const _ g c _ _ _ _

/-- **T1, constants in `h̄`** (CC0 D2.5, D4): a.s., replacing `h̄` by `h̄ + c` multiplies `D^ϕ` by
`e^{ξ c}`, for every constant `c` (hence also for a random one). -/
theorem ae_confMetric_addConst (hD : IsStrongLQGMetric γ D) (hhb : IsGFFPlusCont hbar P) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ (g : C(ℂ, ℝ)) (c : ℝ) (z w : ℂ),
      confMetric D ϕ V (addConst (hbar ω) c) g z w =
        ENNReal.ofReal (Real.exp (xiGamma γ * c)) * confMetric D ϕ V (hbar ω) g z w :=
  (ae_confMetric_add_const hD hhb).mono fun ω hω ϕ W V hϕ g c z w => by
    rw [← hω ϕ W V hϕ g c z w]
    simp only [confMetric, addFun_addConst_eq_addFun]

/-- **T1, two-sided Weyl bounds**: a.s., if `a ≤ ξ g ≤ b` on `ϕ '' V`, then
`e^a D_{h̄}(ϕ·,ϕ·;ϕ(V)) ≤ D^ϕ ≤ e^b D_{h̄}(ϕ·,ϕ·;ϕ(V))`. -/
theorem ae_confMetric_mem_Icc (hD : IsStrongLQGMetric γ D) (hhb : IsGFFPlusCont hbar P) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ (g : C(ℂ, ℝ)) (a b : ℝ),
      (∀ x ∈ ϕ '' V, a ≤ xiGamma γ * g x) → (∀ x ∈ ϕ '' V, xiGamma γ * g x ≤ b) → ∀ z w : ℂ,
        ENNReal.ofReal (Real.exp a) * (D (hbar ω)).internal (ϕ '' V) (ϕ z) (ϕ w) ≤
            confMetric D ϕ V (hbar ω) g z w ∧
          confMetric D ϕ V (hbar ω) g z w ≤
            ENNReal.ofReal (Real.exp b) * (D (hbar ω)).internal (ϕ '' V) (ϕ z) (ϕ w) :=
  (ae_confMetric_eq_weylScaleOn hD hhb).mono fun _ hω ϕ W V hϕ g a b ha hb z w => by
    rw [hω ϕ W V hϕ g z w]
    exact ⟨le_weylScaleOn_of_le ha, weylScaleOn_le_of_le hb⟩

/-! ## 9. Measurability in `ω` -/

omit [IsProbabilityMeasure P] in
/-- The chain formula `ContMetric.chainInf` (LM S-int (a)) gives a measurable version of `D^ϕ`. -/
theorem measurable_chainInf_addFun (hD : IsStrongLQGMetric γ D) (hhb : Measurable hbar)
    (hf : Measurable f) (ϕ : ℂ → ℂ) (V : Set ℂ) (z w : ℂ) :
    Measurable fun ω => (D (addFun (hbar ω) (f ω))).chainInf (ϕ '' V) (ϕ z) (ϕ w) :=
  (ContMetric.measurable_chainInf (ϕ '' V)).comp
    ((hD.measurable.comp (measurable_addFun.comp (hhb.prodMk hf))).prodMk
      (measurable_const : Measurable fun _ : Ω => ((ϕ z, ϕ w) : ℂ × ℂ)))

/-- a.s., for every conformal neighbourhood, `D^ϕ` equals its measurable version. -/
theorem ae_confMetric_eq_chainInf (hD : IsStrongLQGMetric γ D) (hhb : IsWholePlaneGFF hbar P)
    (hf : Measurable f) :
    ∀ᵐ ω ∂P, ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V → ∀ z w : ℂ,
      confMetric D ϕ V (hbar ω) (f ω) z w =
        (D (addFun (hbar ω) (f ω))).chainInf (ϕ '' V) (ϕ z) (ϕ w) :=
  (ae_isLength_addFun hD hhb hf).mono fun _ hω ϕ _ _ hϕ z w =>
    ContMetric.internal_eq_chainInf _ hω hϕ.isOpen_image (ϕ z) (ϕ w)

/-- `ω ↦ D^ϕ(z, w)` is a.e.-measurable. -/
theorem aemeasurable_confMetric (hD : IsStrongLQGMetric γ D) (hϕ : IsConfNbhd ϕ W V)
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f) (z w : ℂ) :
    AEMeasurable (fun ω => confMetric D ϕ V (hbar ω) (f ω) z w) P :=
  (measurable_chainInf_addFun hD hhb.measurable hf ϕ V z w).aemeasurable.congr
    ((ae_confMetric_eq_chainInf hD hhb hf).mono fun _ hω => (hω ϕ W V hϕ z w).symm)

end AS

end SmallGammaGeodesics.CC
