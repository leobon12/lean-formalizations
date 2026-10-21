import SmallGammaGeodesics.CC.GoodAnnulus

/-!
# Condition 2 localizes `D^ϕ` (track CC, packet CC9a: T4, second metric)

Source: [3] (Gwynne–Miller arXiv:1905.00384) proof of Lemma 3.8, in the corrected form of CC0
Details (a) **D14**: condition 2 of `E_r(z)` makes condition 1 local for *both* metrics. For
`D_h` this is `internal_eq_of_gaLongI` (`CC/GoodAnnulus.lean`). For the extended-valued
`D^ϕ = confMetric D ϕ V h̄ f` with `J' = D^ϕ(·,·;𝔸)` (`𝔸 ⊆ V` open), the J-form of condition 2
compares `J'(u,v)` with `bdFun J' 𝔸 u`, and:

* `min_le_confMetric`: `min (J'(u,v), bdFun J' 𝔸 u) ≤ D^ϕ(u,v)` for `u, v ∈ 𝔸` (a path in `V`
  either stays in `𝔸`, or it comes arbitrarily close to `∂𝔸` inside `𝔸` before its first exit);
* `confMetric_eq_of_le_bdFun`: if `J'(u,v) ≤ bdFun J' 𝔸 u`, then `J'(u,v) = D^ϕ(u,v)`;
* `bdFun_le_confMetric_of_lt`: if `bdFun J' 𝔸 u < J'(u,v)`, then `bdFun J' 𝔸 u ≤ D^ϕ(u,v)`
  (the lower bound behind CC0 D14's condition-2 estimate);
* `confMetric_annulus_eq_of_lenFun_le`, `confMetric_annulus_eq_of_isGeodI`: on condition 2 (J-form),
  for `u ∈ ∂B_{αr}(z)`, `v ∈ ∂B_r(z)` joined by a `J`-shortest path in `cl 𝔸_{αr,r}(z)`,
  `D^ϕ(u,v;𝔸) = D^ϕ(u,v)`;
* `gaCompareBI_of_confMetric_le`: on condition 2, condition 1 (J-form) follows from the global bound
  `D^ϕ(u,v) ≤ C' D_h(u,v)` on `∂B_{αr}(z) × ∂B_r(z)` (the form in which CC9b uses [3] Lemma 2.2).

Own elementary arguments (first exit time, as in `GM.setDist_frontier_eq_iSup`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

section Local
variable {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V A : Set ℂ} {hbar : DistC} {f : C(ℂ, ℝ)}

/-- **a path in `V` either stays in `A` or comes close to `∂A` inside `A`**: for `u, v ∈ A ⊆ V`
(`A` open) and `J' = D^ϕ(·,·;A)`, `min (J'(u,v), bdFun J' A u) ≤ D^ϕ(u,v)`. -/
theorem min_le_confMetric (hϕ : IsConfNbhd ϕ W V) (hA : IsOpen A) (hAV : A ⊆ V) {u v : ℂ}
    (hu : u ∈ A) (hv : v ∈ A) :
    min (confMetric D ϕ A hbar f u v) (GM.bdFun (confMetric D ϕ A hbar f) A u) ≤
      confMetric D ϕ V hbar f u v := by
  rw [confMetric_eq_funInternal hϕ (hϕ.subset (hAV hu)) (hϕ.subset (hAV hv))]
  refine le_iInf fun γ => ?_
  obtain ⟨γ, -⟩ := γ
  set P : ℝ → ℂ := ⇑γ.extend with hPdef
  have hPc : Continuous P := γ.extend.continuous
  have hP0 : P 0 = u := Path.extend_zero γ
  by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ A
  · -- the path stays in `A`
    refine (min_le_left _ _).trans ?_
    have h1 := confMetric_le_lenFun (D := D) (hbar := hbar) (f := f) hϕ hAV zero_le_one
      hPc.continuousOn hstay
    rwa [hP0, show P 1 = v from Path.extend_one γ] at h1
  -- the first exit time `s` from `A`
  push Not at hstay
  obtain ⟨t₀, ht₀, ht₀A⟩ := hstay
  obtain ⟨s, hs, hPs, hbef⟩ :=
    MetricGeometry.exists_first_hit hPc.continuousOn hA.isClosed_compl ⟨t₀, ht₀, ht₀A⟩
  have hin : ∀ t ∈ Ico (0 : ℝ) s, P t ∈ A := fun t ht => not_not.1 (hbef t ht)
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, hP0] at hPs
      exact absurd hu hPs
    · exact h
  -- before `s`, `J'(u, P t)` is at most the length
  have hbound : ∀ t ∈ Ico (0 : ℝ) s,
      confMetric D ϕ A hbar f u (P t) ≤ GM.lenFun (confMetric D ϕ V hbar f) P 0 1 := by
    intro t ht
    have hmaps : MapsTo P (Icc 0 t) A := fun τ hτ => hin τ ⟨hτ.1, hτ.2.trans_lt ht.2⟩
    have h1 := confMetric_le_lenFun (D := D) (hbar := hbar) (f := f) hϕ hAV ht.1
      hPc.continuousOn hmaps
    rw [hP0] at h1
    exact h1.trans (lenFun_mono_right P (ht.2.le.trans hs.2))
  -- the exit point lies on `∂A`
  have hne : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
  have hPs_fr : P s ∈ frontier A := by
    rw [hA.frontier_eq]
    exact ⟨mem_closure_of_tendsto ((hPc.tendsto s).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall hin), hPs⟩
  refine (min_le_right _ _).trans (iSup_le fun n => ?_)
  have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hev : ∀ᶠ t in 𝓝[Ico 0 s] s, P t ∈ ball (P s) (1 / ((n : ℝ) + 1)) ∧ t ∈ Ico 0 s :=
    (((hPc.tendsto s).mono_left nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds (P s) hn)).and self_mem_nhdsWithin
  obtain ⟨t, htn, ht⟩ := hev.exists
  have hnear : P t ∈ GM.nearFrontier A (1 / ((n : ℝ) + 1)) := by
    refine ⟨hin t ht, (Metric.infDist_le_dist_of_mem hPs_fr).trans_lt ?_⟩
    exact htn
  exact (iInf₂_le (P t) hnear).trans (hbound t ht)

/-- **`D^ϕ(·,·;A)` is realized in `V`** when `J'(u,v) ≤ bdFun J' A u` (`J' = D^ϕ(·,·;A)`) -/
theorem confMetric_eq_of_le_bdFun (hϕ : IsConfNbhd ϕ W V) (hA : IsOpen A) (hAV : A ⊆ V)
    {u v : ℂ} (hu : u ∈ A) (hv : v ∈ A)
    (hle : confMetric D ϕ A hbar f u v ≤ GM.bdFun (confMetric D ϕ A hbar f) A u) :
    confMetric D ϕ A hbar f u v = confMetric D ϕ V hbar f u v := by
  refine le_antisymm ?_ (confMetric_anti hAV u v)
  have := min_le_confMetric (D := D) (hbar := hbar) (f := f) hϕ hA hAV hu hv
  rwa [min_eq_left hle] at this

/-- **the lower bound of condition 2** (CC0 D14): if `bdFun J' A u < J'(u,v)`
(`J' = D^ϕ(·,·;A)`), then `D^ϕ(u,v) ≥ bdFun J' A u` -/
theorem bdFun_le_confMetric_of_lt (hϕ : IsConfNbhd ϕ W V) (hA : IsOpen A) (hAV : A ⊆ V)
    {u v : ℂ} (hu : u ∈ A) (hv : v ∈ A)
    (hlt : GM.bdFun (confMetric D ϕ A hbar f) A u < confMetric D ϕ A hbar f u v) :
    GM.bdFun (confMetric D ϕ A hbar f) A u ≤ confMetric D ϕ V hbar f u v := by
  have := min_le_confMetric (D := D) (hbar := hbar) (f := f) hϕ hA hAV hu hv
  rwa [min_eq_right hlt.le] at this

end Local

section Annulus
variable {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V : Set ℂ} {hbar : DistC} {f : C(ℂ, ℝ)}
  {α r : ℝ} {z : ℂ}

/-- **condition 2 localizes `D^ϕ`** (CC0 D14): on condition 2 (J-form, any first function `J`),
for `u ∈ ∂B_{αr}(z)`, `v ∈ ∂B_r(z)` joined by a path in `cl 𝔸_{αr,r}(z)` of `J`-length
`≤ J(u,v)`, `D^ϕ(u,v;𝔸_{r/2,2r}(z)) = D^ϕ(u,v)`. -/
theorem confMetric_annulus_eq_of_lenFun_le (hϕ : IsConfNbhd ϕ W V) {J : ℂ → ℂ → ℝ≥0∞}
    (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (hlong : GM.gaLongI J (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α r z)
    {u v : ℂ} (hu : u ∈ sphere z (α * r)) (hv : v ∈ sphere z r) {a b : ℝ} {P : ℝ → ℂ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) (hPa : P a = u) (hPb : P b = v)
    (hPK : P '' Icc a b ⊆ closure (annulus z (α * r) r : Set ℂ))
    (hlen : GM.lenFun J P a b ≤ J u v) :
    confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f u v = confMetric D ϕ V hbar f u v := by
  refine confMetric_eq_of_le_bdFun hϕ (annulus z (r / 2) (2 * r)).isOpen hUV
    (sphere_inner_subset hα hα1 hr hu) (sphere_outer_subset hα hα1 hr hv) (not_lt.1 fun hlt => ?_)
  exact absurd (hlong u hu v hv (Or.inr hlt) a b P hab hP hPa hPb hPK) (not_lt.2 hlen)

/-- **condition 2 localizes `D^ϕ` on the pairs of condition 1** (J-geodesic form) -/
theorem confMetric_annulus_eq_of_isGeodI (hϕ : IsConfNbhd ϕ W V) {J : ℂ → ℂ → ℝ≥0∞}
    (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (hlong : GM.gaLongI J (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α r z)
    {u v : ℂ} (hu : u ∈ sphere z (α * r)) (hv : v ∈ sphere z r) {η : C(unitInterval, ℂ)}
    (hg : GM.IsGeodI J (annulus z (r / 2) (2 * r)) u v η)
    (hK : ∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ)) :
    confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f u v = confMetric D ϕ V hbar f u v := by
  refine confMetric_annulus_eq_of_lenFun_le hϕ hα hα1 hr hUV hlong hu hv zero_le_one
    (GM.pjPath_continuousOn η) ?_ ?_ (by rintro _ ⟨t, -, rfl⟩; exact hK _)
    (GM.lenFun_pj_le hg.2.2.2)
  · rw [GM.pjPath_zero]; exact hg.1
  · rw [GM.pjPath_one]; exact hg.2.1

/-- **condition 2 localizes `D^ϕ` on the pairs of condition 1** (`D_h`-geodesic form, with
`J = D_h(·,·;𝔸)`) -/
theorem confMetric_annulus_eq_of_isGeod01 (hϕ : IsConfNbhd ϕ W V) {d : ContMetric}
    (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (hlong : GM.gaLongI (d.internal (annulus z (r / 2) (2 * r)))
      (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α r z)
    {u v : ℂ} (hu : u ∈ sphere z (α * r)) (hv : v ∈ sphere z r) {η : C(unitInterval, ℂ)}
    (hg : d.IsGeod01 u v η) (hK : ∀ t, η t ∈ closure (annulus z (α * r) r : Set ℂ)) :
    confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f u v = confMetric D ϕ V hbar f u v := by
  refine confMetric_annulus_eq_of_lenFun_le hϕ hα hα1 hr hUV hlong hu hv zero_le_one
    (GM.pjPath_continuousOn η) ?_ ?_ (by rintro _ ⟨t, -, rfl⟩; exact hK _) ?_
  · rw [GM.pjPath_zero]; exact hg.1
  · rw [GM.pjPath_one]; exact hg.2.1
  · rw [GM.lenFun_internal d (GM.pjPath_continuousOn η)
      (fun t _ => GM.closure_annulus_subset hα hr (hK _))]
    calc d.len (fun t => η (GM.pj t)) 0 1 ≤ ENNReal.ofReal (d.1 (u, v)) := by
          rw [GM.len_eq_lenFun]
          exact GM.lenFun_pj_le fun s t => by rw [hg.2.2 s t, ENNReal.ofReal_mul (abs_nonneg _)]
      _ ≤ d.internal (annulus z (r / 2) (2 * r)) u v := by
          rw [← ContMetric.edist_pt]
          exact MetricGeometry.edist_le_internalEDist _ _ _

/-- **condition 1 from a global bound on `D^ϕ`** (for CC9b; CC0 D14 condition 1): for a proper
length metric `D_h` (`d`), on condition 2 (J-form, with `J = D_h(·,·;𝔸)`, `J' = D^ϕ(·,·;𝔸)`),
condition 1 (J-form) holds as soon as `D^ϕ(u,v) ≤ C' D_h(u,v)` for all `u ∈ ∂B_{αr}(z)`,
`v ∈ ∂B_r(z)`. -/
theorem gaCompareBI_of_confMetric_le {d : ContMetric} (hL : d.IsLength) [ProperSpace d.Space]
    (hϕ : IsConfNbhd ϕ W V) {C' : ℝ} (hC' : 0 ≤ C') (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (hlong : GM.gaLongI (d.internal (annulus z (r / 2) (2 * r)))
      (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α r z)
    (hcmp : ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r,
      confMetric D ϕ V hbar f u v ≤ ENNReal.ofReal (C' * d.1 (u, v))) :
    GM.gaCompareBI (d.internal (annulus z (r / 2) (2 * r)))
      (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α C' r z := by
  intro u hu v hv η _ hg hK
  have hUo : IsOpen (annulus z (r / 2) (2 * r) : Set ℂ) := (annulus z (r / 2) (2 * r)).isOpen
  have hloc := ofReal_le_setDist_of_gaLongI hL hα hα1 hr hlong hu hv (Or.inr hg) hK
  rw [confMetric_annulus_eq_of_isGeodI hϕ hα hα1 hr hUV hlong hu hv hg hK,
    GM.internal_eq_of_le d hL hUo (sphere_inner_subset hα hα1 hr hu)
      (sphere_outer_subset hα hα1 hr hv) hloc,
    ENNReal.toReal_ofReal (d.nonneg u v)]
  calc (confMetric D ϕ V hbar f u v).toReal ≤ (ENNReal.ofReal (C' * d.1 (u, v))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcmp u hu v hv)
    _ = C' * d.1 (u, v) := ENNReal.toReal_ofReal (mul_nonneg hC' (d.nonneg u v))

end Annulus

end SmallGammaGeodesics.CC
