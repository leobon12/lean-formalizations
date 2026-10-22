import HigherDimLQGMetric.DGZ.Crossing

/-!
# Path surgery for the bypass lemma (packet L4b2)

Source: MA7 (`planning/audits/MA7-ref2-sections-4-6.md`) Details (a) D-5.11, "Level `j`": a path
`π` that enters the inner box `B̄_{2Rs_j}(z)` of the shell `A_z = B̄_{4Rs_j}(z) \ B_{2Rs_j}(z)` is
rerouted along a detour `I_z ⊆ A_z ∩ B₂(0)` supplied by the around-good property, between a point
of the crossing before the first visit of the inner box and a point of the crossing after the last
visit.

Contents:
* `lfppLength_congr_Ioo`: paths that agree on `(0, 1)` have the same LFPP length;
* hitting times: `exists_first_visit`, `exists_last_visit` (closed sets), the boundary lemmas
  `notMem_obox_left_of_Ioo`, `notMem_obox_right_of_Ioo` and the two-set cut `exists_cut_between`
  (used for the final cut of D-5.11 between `B̄_{s_m}(γ(0))` and `B̄_{s_m}(γ(1))`);
* the splice `splicePath π I σ τ` (`π` with the parameter interval `(σ, τ)` replaced **in place**
  by `I`, reparametrized to `[σ, τ]`): it is piecewise `C¹` (`isPcwC1Path_splicePath`), agrees with
  `π` off `(σ, τ)` (so every time outside `(σ, τ)` keeps its meaning), its LFPP integrand agrees
  with that of `π` off `[σ, τ]`, and its integral over `[σ, τ]` is `lfppLength I`
  (`integral_splicePath`);
* **the single-detour step** `exists_detour_splice` (D-5.11, one centre `z`): the rerouted path
  avoids `B_{r₂}(z)`, each of its points is a point of `π` or lies in `B̄_{r₁}(z)` (and then `π`
  meets `B̄_{r₂}(z)`), and on every measurable set of times
  `J` the new length is at most the old length on `J₀ = J \ (σ, τ)` (where the two paths agree)
  plus `c`, and at most the old length on `J₀` if the new path misses `B̄_{r₁}(z)` at the times
  of `J`.

The in-place splice keeps the parametrization of the untouched times, so the bookkeeping of D-5.11
("pieces on pairwise disjoint parameter intervals") becomes the inequality over arbitrary
measurable sets of times proved in `exists_detour_splice`; see `HigherDimLQGMetric.DGZ.Bypass`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ## Congruence of LFPP lengths -/

section Congr

variable {ξ : ℝ} {φ : Rd d → ℝ}

/-- Two paths that agree on `(0, 1)` have the same LFPP length. -/
theorem lfppLength_congr_Ioo {f g : ℝ → Rd d} (h : EqOn f g (Ioo 0 1)) :
    lfppLength ξ φ f = lfppLength ξ φ g := by
  rw [lfppLength_eq_integral, lfppLength_eq_integral]
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({1} : Set ℝ) :=
    (countable_singleton _).ae_notMem volume
  filter_upwards [hnull] with u hu hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hmem.1, lt_of_le_of_ne hmem.2 hu⟩
  have hev : f =ᶠ[𝓝 u] g := Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hu') h
  unfold lfppIntegrand
  rw [hev.deriv_eq, hev.eq_of_nhds]

end Congr

/-! ## Hitting times -/

section Hitting

variable {π : ℝ → Rd d}

/-- **First visit** of a closed set on `[a, b]`. -/
theorem exists_first_visit {a b : ℝ} (hπ : ContinuousOn π (Icc a b)) {K : Set (Rd d)}
    (hK : IsClosed K) (h : ∃ u ∈ Icc a b, π u ∈ K) :
    ∃ u₀ ∈ Icc a b, π u₀ ∈ K ∧ ∀ u ∈ Icc a b, u < u₀ → π u ∉ K := by
  obtain ⟨u, hu, huK⟩ := h
  set S : Set ℝ := Icc a b ∩ π ⁻¹' K with hS
  have hSc : IsClosed S := hπ.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hSb : BddBelow S := ⟨a, fun v hv => hv.1.1⟩
  have hmem : sInf S ∈ S := hSc.csInf_mem ⟨u, hu, huK⟩ hSb
  exact ⟨sInf S, hmem.1, hmem.2, fun v hv hlt hvK =>
    absurd (csInf_le hSb ⟨hv, hvK⟩) (not_le.2 hlt)⟩

/-- **Last visit** of a closed set on `[a, b]`. -/
theorem exists_last_visit {a b : ℝ} (hπ : ContinuousOn π (Icc a b)) {K : Set (Rd d)}
    (hK : IsClosed K) (h : ∃ u ∈ Icc a b, π u ∈ K) :
    ∃ u₁ ∈ Icc a b, π u₁ ∈ K ∧ ∀ u ∈ Icc a b, u₁ < u → π u ∉ K := by
  obtain ⟨u, hu, huK⟩ := h
  set S : Set ℝ := Icc a b ∩ π ⁻¹' K with hS
  have hSc : IsClosed S := hπ.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hSb : BddAbove S := ⟨b, fun v hv => hv.1.2⟩
  have hmem : sSup S ∈ S := hSc.csSup_mem ⟨u, hu, huK⟩ hSb
  exact ⟨sSup S, hmem.1, hmem.2, fun v hv hlt hvK =>
    absurd (le_csSup hSb ⟨hv, hvK⟩) (not_le.2 hlt)⟩

/-- If `π` avoids the open box `obox c r` on `(t₀, t₁)`, so does its left endpoint. -/
theorem notMem_obox_left_of_Ioo {t₀ t₁ : ℝ} (h : t₀ < t₁) (hπ : ContinuousOn π (Icc t₀ t₁))
    {c : Rd d} {r : ℝ} (hout : ∀ u ∈ Ioo t₀ t₁, π u ∉ obox c r) : π t₀ ∉ obox c r := by
  have hcw : ContinuousWithinAt π (Ioo t₀ t₁) t₀ :=
    (hπ t₀ (left_mem_Icc.2 h.le)).mono Ioo_subset_Icc_self
  have hmem := hcw.mem_closure_image (by rw [closure_Ioo h.ne]; exact left_mem_Icc.2 h.le)
  have hsub : π '' Ioo t₀ t₁ ⊆ (obox c r)ᶜ := by
    rintro _ ⟨u, hu, rfl⟩
    exact hout u hu
  exact (HigherDimLFPP.DGZ.isOpen_obox c r).isClosed_compl.closure_subset_iff.2 hsub hmem

/-- If `π` avoids the open box `obox c r` on `(t₀, t₁)`, so does its right endpoint. -/
theorem notMem_obox_right_of_Ioo {t₀ t₁ : ℝ} (h : t₀ < t₁) (hπ : ContinuousOn π (Icc t₀ t₁))
    {c : Rd d} {r : ℝ} (hout : ∀ u ∈ Ioo t₀ t₁, π u ∉ obox c r) : π t₁ ∉ obox c r := by
  have hcw : ContinuousWithinAt π (Ioo t₀ t₁) t₁ :=
    (hπ t₁ (right_mem_Icc.2 h.le)).mono Ioo_subset_Icc_self
  have hmem := hcw.mem_closure_image (by rw [closure_Ioo h.ne]; exact right_mem_Icc.2 h.le)
  have hsub : π '' Ioo t₀ t₁ ⊆ (obox c r)ᶜ := by
    rintro _ ⟨u, hu, rfl⟩
    exact hout u hu
  exact (HigherDimLFPP.DGZ.isOpen_obox c r).isClosed_compl.closure_subset_iff.2 hsub hmem

/-- **Cut between two disjoint closed sets**: if `π 0 ∈ K₀` and `π 1 ∈ K₁`, there are
`0 ≤ t₀ < t₁ ≤ 1` with `π t₀ ∈ K₀`, `π t₁ ∈ K₁` and `π (t₀, t₁)` avoiding both sets (`t₁` is the
first visit of `K₁`, `t₀` the last visit of `K₀` before `t₁`). -/
theorem exists_cut_between (hπ : ContinuousOn π (Icc 0 1)) {K₀ K₁ : Set (Rd d)} (hK₀ : IsClosed K₀)
    (hK₁ : IsClosed K₁) (hdisj : Disjoint K₀ K₁) (h0 : π 0 ∈ K₀) (h1 : π 1 ∈ K₁) :
    ∃ t₀ t₁, 0 ≤ t₀ ∧ t₀ < t₁ ∧ t₁ ≤ 1 ∧ π t₀ ∈ K₀ ∧ π t₁ ∈ K₁ ∧
      ∀ u ∈ Ioo t₀ t₁, π u ∉ K₀ ∧ π u ∉ K₁ := by
  obtain ⟨t₁, ht₁, ht₁K, hbefore⟩ :=
    exists_first_visit hπ hK₁ ⟨1, right_mem_Icc.2 zero_le_one, h1⟩
  obtain ⟨t₀, ht₀, ht₀K, hafter⟩ := exists_last_visit (hπ.mono (Icc_subset_Icc le_rfl ht₁.2)) hK₀
    ⟨0, left_mem_Icc.2 ht₁.1, h0⟩
  have hlt : t₀ < t₁ := by
    rcases ht₀.2.lt_or_eq with h | h
    · exact h
    · exact absurd ht₁K (Set.disjoint_left.1 hdisj (h ▸ ht₀K))
  refine ⟨t₀, t₁, ht₀.1, hlt, ht₁.2, ht₀K, ht₁K, fun u hu => ⟨?_, ?_⟩⟩
  · exact hafter u ⟨ht₀.1.trans hu.1.le, hu.2.le⟩ hu.1
  · exact hbefore u ⟨ht₀.1.trans hu.1.le, hu.2.le.trans ht₁.2⟩ hu.2

end Hitting

/-! ## The splice of a path -/

section Splice

variable {π I : ℝ → Rd d} {σ τ u : ℝ}

/-- `π` with the parameter interval `(σ, τ)` replaced, in place, by the path `I` reparametrized to
`[σ, τ]` (`u ↦ I ((u - σ) / (τ - σ))`). For `σ = τ` it is `π`. -/
def splicePath (π I : ℝ → Rd d) (σ τ : ℝ) (u : ℝ) : Rd d :=
  if u ≤ σ then π u else if u < τ then I ((τ - σ)⁻¹ * (u - σ)) else π u

theorem splicePath_of_notMem (hu : u ∉ Ioo σ τ) : splicePath π I σ τ u = π u := by
  unfold splicePath
  split_ifs with h1 h2
  · rfl
  · exact absurd ⟨lt_of_not_ge h1, h2⟩ hu
  · rfl

theorem splicePath_of_mem (hu : u ∈ Ioo σ τ) :
    splicePath π I σ τ u = I ((τ - σ)⁻¹ * (u - σ)) := by
  unfold splicePath
  split_ifs with h1 h2
  · exact absurd hu.1 (not_lt.2 h1)
  · rfl
  · exact absurd hu.2 h2

theorem splicePath_self : splicePath π I σ σ = π := by
  funext u
  exact splicePath_of_notMem fun hu => absurd (hu.1.trans hu.2) (lt_irrefl σ)

/-- The rescaled time of a point of `(σ, τ)` lies in `(0, 1)`. -/
theorem inv_mul_sub_mem_Ioo (hu : u ∈ Ioo σ τ) : (τ - σ)⁻¹ * (u - σ) ∈ Ioo (0 : ℝ) 1 := by
  have hc : 0 < τ - σ := sub_pos.2 (hu.1.trans hu.2)
  refine ⟨mul_pos (inv_pos.2 hc) (sub_pos.2 hu.1), ?_⟩
  rw [inv_mul_lt_iff₀ hc, mul_one]
  linarith [hu.2]

/-- On `[σ, τ]` the splice is the reparametrized detour (including the two junction times). -/
theorem splicePath_eq_of_mem_Icc (hστ : σ < τ) (h0 : I 0 = π σ) (h1 : I 1 = π τ)
    (hu : u ∈ Icc σ τ) : splicePath π I σ τ u = I ((τ - σ)⁻¹ * (u - σ)) := by
  have hc : 0 < τ - σ := sub_pos.2 hστ
  rcases hu.1.lt_or_eq with h | h
  · rcases hu.2.lt_or_eq with h' | h'
    · exact splicePath_of_mem ⟨h, h'⟩
    · rw [h', splicePath_of_notMem fun hu' => absurd hu'.2 (lt_irrefl τ),
        inv_mul_cancel₀ hc.ne', h1]
  · rw [← h, splicePath_of_notMem fun hu' => absurd hu'.1 (lt_irrefl σ), sub_self, mul_zero, h0]

/-- **The splice is piecewise `C¹`.** -/
theorem isPcwC1Path_splicePath {x y : Rd d} (hπ : IsPcwC1Path π x y)
    (hI : IsPcwC1Path I (π σ) (π τ)) (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτ : τ ≤ 1) :
    IsPcwC1Path (splicePath π I σ τ) x y := by
  classical
  rcases hστ.lt_or_eq with hστ | rfl
  swap
  · rw [splicePath_self]; exact hπ
  obtain ⟨F, hF⟩ := hπ.exists_pcwC1
  obtain ⟨F', hF'⟩ := hI.exists_pcwC1
  have hc : 0 < τ - σ := sub_pos.2 hστ
  set c := (τ - σ)⁻¹ with hcdef
  have hcpos : 0 < c := inv_pos.2 hc
  have hL : ∀ u, u ≤ σ → splicePath π I σ τ u = π u := fun u hu =>
    splicePath_of_notMem fun h => absurd h.1 (not_lt.2 hu)
  have hR : ∀ u, τ ≤ u → splicePath π I σ τ u = π u := fun u hu =>
    splicePath_of_notMem fun h => absurd h.2 (not_lt.2 hu)
  have hM : ∀ u ∈ Icc σ τ,
      splicePath π I σ τ u = I (c * u + -(c * σ)) := fun u hu => by
    rw [splicePath_eq_of_mem_Icc hστ hI.source hI.target hu]
    congr 1
    ring
  have hmapsM : ∀ a b : ℝ, MapsTo (fun u : ℝ => c * u + -(c * σ)) (Icc a b)
      (Icc (c * a + -(c * σ)) (c * b + -(c * σ))) := fun a b u hu =>
    ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  have hcσ : c * σ + -(c * σ) = 0 := by ring
  have hcτ : c * τ + -(c * σ) = 1 := by
    rw [← mul_neg, ← mul_add, ← sub_eq_add_neg, hcdef, inv_mul_cancel₀ hc.ne']
  refine IsPcwC1Path.of_pcwC1 (F := insert σ (insert τ (F ∪ F'.image fun v => (τ - σ) * v + σ)))
    (by rw [hL 0 hσ, hπ.source]) (by rw [hR 1 hτ, hπ.target]) ?_ ?_
  · -- continuity on `[0, σ] ∪ [σ, τ] ∪ [τ, 1]`
    have c1 : ContinuousOn (splicePath π I σ τ) (Icc 0 σ) :=
      (hπ.continuousOn.mono (Icc_subset_Icc le_rfl (hστ.le.trans hτ))).congr fun u hu =>
        hL u hu.2
    have c2 : ContinuousOn (splicePath π I σ τ) (Icc σ τ) := by
      refine (hI.continuousOn.comp (by fun_prop) fun u hu => ?_).congr fun u hu => hM u hu
      have := hmapsM σ τ hu
      rwa [hcσ, hcτ] at this
    have c3 : ContinuousOn (splicePath π I σ τ) (Icc τ 1) :=
      (hπ.continuousOn.mono (Icc_subset_Icc (hσ.trans hστ.le) le_rfl)).congr fun u hu =>
        hR u hu.1
    have := (c1.union_of_isClosed c2 isClosed_Icc isClosed_Icc).union_of_isClosed c3
      (isClosed_Icc.union isClosed_Icc) isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hσ hστ.le, Icc_union_Icc_eq_Icc (hσ.trans hστ.le) hτ] at this
  · intro a b ha hab hb hFa
    have hσab : σ ≤ a ∨ b ≤ σ := by
      by_contra h
      push Not at h
      exact hFa σ (Finset.mem_insert_self _ _) ⟨h.1, h.2⟩
    have hτab : τ ≤ a ∨ b ≤ τ := by
      by_contra h
      push Not at h
      exact hFa τ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) ⟨h.1, h.2⟩
    have hFab : ∀ x ∈ F, x ∉ Ioo a b := fun x hx => hFa x
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)))
    rcases hτab with hτa | hbτ
    · -- right piece
      exact (hF a b ha hab hb hFab).congr fun u hu => hR u (hτa.trans hu.1)
    rcases hσab with hσa | hbσ
    · -- middle piece
      have hF'ab : ∀ v ∈ F', v ∉ Ioo (c * a + -(c * σ)) (c * b + -(c * σ)) := by
        intro v hv hvI
        refine hFa ((τ - σ) * v + σ) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)))) ⟨?_, ?_⟩
        · have h1 := hvI.1
          have : c * a + -(c * σ) = c * (a - σ) := by ring
          rw [this, hcdef, inv_mul_lt_iff₀ hc] at h1
          linarith
        · have h2 := hvI.2
          have : c * b + -(c * σ) = c * (b - σ) := by ring
          rw [this, hcdef, lt_inv_mul_iff₀ hc] at h2
          linarith
      have h0a : 0 ≤ c * a + -(c * σ) := by nlinarith
      have hab' : c * a + -(c * σ) < c * b + -(c * σ) := by nlinarith
      have hb1 : c * b + -(c * σ) ≤ 1 := by rw [← hcτ]; nlinarith
      exact (contDiffOn_comp_affine (hF' _ _ h0a hab' hb1 hF'ab) (hmapsM a b)).congr
        fun u hu => hM u ⟨hσa.trans hu.1, hu.2.trans hbτ⟩
    · -- left piece
      exact (hF a b ha hab hb hFab).congr fun u hu => hL u (hu.2.trans hbσ)

theorem mapsTo_splicePath {V : Set (Rd d)} (hπV : MapsTo π (Icc 0 1) V)
    (hIV : MapsTo I (Icc 0 1) V) (hu : u ∈ Icc (0 : ℝ) 1) : splicePath π I σ τ u ∈ V := by
  by_cases h : u ∈ Ioo σ τ
  · rw [splicePath_of_mem h]
    exact hIV (Ioo_subset_Icc_self (inv_mul_sub_mem_Ioo h))
  · rw [splicePath_of_notMem h]
    exact hπV hu

variable {ξ : ℝ} {φ : Rd d → ℝ}

theorem lfppIntegrand_splicePath_of_lt (hu : u < σ) :
    lfppIntegrand ξ φ (splicePath π I σ τ) u = lfppIntegrand ξ φ π u := by
  have hev : splicePath π I σ τ =ᶠ[𝓝 u] π := Filter.eventuallyEq_of_mem (Iio_mem_nhds hu)
    fun v hv => splicePath_of_notMem fun h => absurd h.1 (not_lt.2 (le_of_lt hv))
  unfold lfppIntegrand
  rw [hev.deriv_eq, hev.eq_of_nhds]

theorem lfppIntegrand_splicePath_of_gt (hu : τ < u) :
    lfppIntegrand ξ φ (splicePath π I σ τ) u = lfppIntegrand ξ φ π u := by
  have hev : splicePath π I σ τ =ᶠ[𝓝 u] π := Filter.eventuallyEq_of_mem (Ioi_mem_nhds hu)
    fun v hv => splicePath_of_notMem fun h => absurd h.2 (not_lt.2 (le_of_lt hv))
  unfold lfppIntegrand
  rw [hev.deriv_eq, hev.eq_of_nhds]

/-- The integral of the splice over `[σ, τ]` is the length of the detour. -/
theorem integral_splicePath (hστ : σ < τ) :
    ∫ u in σ..τ, lfppIntegrand ξ φ (splicePath π I σ τ) u = lfppLength ξ φ I := by
  rw [← lfppLength_subPath ξ φ _ hστ.le]
  refine lfppLength_congr_Ioo fun v hv => ?_
  have hc : 0 < τ - σ := sub_pos.2 hστ
  have hmem : (τ - σ) * v + σ ∈ Ioo σ τ := ⟨by nlinarith [hv.1], by nlinarith [hv.2]⟩
  simp only [subPath]
  rw [splicePath_of_mem hmem, add_sub_cancel_right, inv_mul_cancel_left₀ hc.ne']

/-- Off `(σ, τ)` the splice and `π` have the same integrals. -/
theorem setIntegral_sdiff_splicePath {J : Set ℝ} (hJ : MeasurableSet J) :
    ∫ u in J \ Ioo σ τ, lfppIntegrand ξ φ (splicePath π I σ τ) u =
      ∫ u in J \ Ioo σ τ, lfppIntegrand ξ φ π u := by
  have hnull : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({σ, τ} : Set ℝ) :=
    ((countable_singleton τ).insert σ).ae_notMem volume
  refine setIntegral_congr_ae (hJ.diff measurableSet_Ioo) ?_
  filter_upwards [hnull] with u hu hmem
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu
  have hout : u < σ ∨ τ < u := by
    by_contra h
    push Not at h
    exact hmem.2 ⟨lt_of_le_of_ne h.1 (Ne.symm hu.1), lt_of_le_of_ne h.2 hu.2⟩
  rcases hout with h | h
  · exact lfppIntegrand_splicePath_of_lt h
  · exact lfppIntegrand_splicePath_of_gt h

/-- On `(σ, τ) ∩ J` the splice costs at most the length of the detour. -/
theorem setIntegral_inter_Ioo_splicePath_le (hφ : Continuous φ) {x y : Rd d}
    (hπ' : IsPcwC1Path (splicePath π I σ τ) x y) (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτ : τ ≤ 1)
    (J : Set ℝ) :
    ∫ u in J ∩ Ioo σ τ, lfppIntegrand ξ φ (splicePath π I σ τ) u ≤ lfppLength ξ φ I := by
  rcases hστ.lt_or_eq with hστ | rfl
  · have hint : IntegrableOn (lfppIntegrand ξ φ (splicePath π I σ τ)) (Ioo σ τ) :=
      (integrableOn_lfppIntegrand hπ' hφ ξ).mono_set
        (Ioo_subset_Icc_self.trans (Icc_subset_Icc hσ hτ))
    calc ∫ u in J ∩ Ioo σ τ, lfppIntegrand ξ φ (splicePath π I σ τ) u
        ≤ ∫ u in Ioo σ τ, lfppIntegrand ξ φ (splicePath π I σ τ) u :=
          setIntegral_mono_set hint (ae_of_all _ fun u => lfppIntegrand_nonneg ξ φ _ u)
            inter_subset_right.eventuallyLE
      _ = ∫ u in σ..τ, lfppIntegrand ξ φ (splicePath π I σ τ) u := by
          rw [intervalIntegral.integral_of_le hστ.le, integral_Ioc_eq_integral_Ioo]
      _ = lfppLength ξ φ I := integral_splicePath hστ
  · rw [Ioo_self, inter_empty, Measure.restrict_empty, integral_zero_measure]
    exact lfppLength_nonneg ξ φ I

end Splice

/-! ## The single-detour step (MA7 D-5.11, level `j`, one centre `z`) -/

section Detour

variable {ξ : ℝ} {φ : Rd d → ℝ}

/-- **Single detour** (MA7 D-5.11, one centre). Let `π` be a piecewise `C¹` path in `B` whose
endpoints lie outside the open box `B_{r₁}(z)`, and let the shell
`A = B̄_{r₁}(z) \ B_{r₂}(z)` be around-good in `B` with threshold `t < c` (`c ≥ 0`). Then there is a
piecewise `C¹` path `π'` in `B` with the same endpoints such that
* `π'` avoids `B_{r₂}(z)`;
* every point of `π'` is a point of `π`, or lies in `B̄_{r₁}(z)` while `π` meets `B̄_{r₂}(z)`;
* for every measurable set `J ⊆ [0, 1]` of times there is a measurable `J₀ ⊆ J` on which `π'` and
  `π` agree, with `∫_J (LFPP integrand of π') ≤ ∫_{J₀} (LFPP integrand of π) + c`, and without the
  `+ c` if `π'` does not meet `B̄_{r₁}(z)` at a time of `J`.

If `π` meets `B̄_{r₂}(z)`, the path is cut at a point `π σ` of the last crossing of `A` before the
first visit of `B̄_{r₂}(z)` and at a point `π τ` of the first crossing after the last visit, and
`π (σ, τ)` is replaced in place by a detour of length `< c` in `A ∩ B` (around-good property and
near-optimal paths); otherwise `π' = π`. -/
theorem exists_detour_splice (hφ : Continuous φ) {π : ℝ → Rd d} {x y : Rd d}
    (hπ : IsPcwC1Path π x y) {B : Set (Rd d)} (hπB : MapsTo π (Icc 0 1) B) {z : Rd d}
    {r₁ r₂ t c : ℝ} (hr : r₂ < r₁) (hgood : AroundGood ξ φ z r₁ r₂ B t) (htc : t < c)
    (hc : 0 ≤ c) (hx : x ∉ obox z r₁) (hy : y ∉ obox z r₁) :
    ∃ π' : ℝ → Rd d, IsPcwC1Path π' x y ∧ MapsTo π' (Icc 0 1) B ∧
      (∀ u ∈ Icc (0 : ℝ) 1, π' u ∉ obox z r₂) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, (∃ v ∈ Icc (0 : ℝ) 1, π' u = π v) ∨
        (π' u ∈ cbox z r₁ ∧ ∃ v ∈ Icc (0 : ℝ) 1, π v ∈ cbox z r₂)) ∧
      ∀ J : Set ℝ, J ⊆ Icc 0 1 → MeasurableSet J →
        ∃ J₀ ⊆ J, MeasurableSet J₀ ∧ (∀ u ∈ J₀, π' u = π u) ∧
          ∫ u in J, lfppIntegrand ξ φ π' u ≤ (∫ u in J₀, lfppIntegrand ξ φ π u) + c ∧
          ((∀ u ∈ J, π' u ∉ cbox z r₁) →
            ∫ u in J, lfppIntegrand ξ φ π' u ≤ ∫ u in J₀, lfppIntegrand ξ φ π u) := by
  classical
  by_cases hmeet : ∃ u ∈ Icc (0 : ℝ) 1, π u ∈ cbox z r₂
  swap
  · -- `π` never visits the inner box: no detour
    push Not at hmeet
    refine ⟨π, hπ, hπB, fun u hu h => hmeet u hu (HigherDimLFPP.DGZ.obox_subset_cbox z r₂ h),
      fun u hu => Or.inl ⟨u, hu, rfl⟩, fun J _ hJm => ⟨J, subset_rfl, hJm, fun _ _ => rfl, ?_⟩⟩
    exact ⟨le_add_of_nonneg_right hc, fun _ => le_rfl⟩
  -- first and last visits of the inner box
  obtain ⟨σ₂, hσ₂, hσ₂K, hbefore⟩ :=
    exists_first_visit hπ.continuousOn (HigherDimLFPP.DGZ.isClosed_cbox z r₂) hmeet
  obtain ⟨τ₁, hτ₁, hτ₁K, hafter⟩ :=
    exists_last_visit hπ.continuousOn (HigherDimLFPP.DGZ.isClosed_cbox z r₂) hmeet
  have hστ₁ : σ₂ ≤ τ₁ := by
    by_contra h
    exact hafter σ₂ hσ₂ (lt_of_not_ge h) hσ₂K
  -- the crossing before the first visit and the crossing after the last visit
  have hx' : π 0 ∉ obox z r₁ := by rw [hπ.source]; exact hx
  have hy' : π 1 ∉ obox z r₁ := by rw [hπ.target]; exact hy
  obtain ⟨t₀, t₁, ht₀, ht₀₁, ht₁, hcr₁⟩ := exists_isShellCrossing_revPath hr hπ le_rfl hσ₂.1
    hσ₂.2 hx' hσ₂K fun u hu => hπB ⟨hu.1, hu.2.trans hσ₂.2⟩
  obtain ⟨t₀', t₁', ht₀', ht₀₁', ht₁', hcr₂⟩ := exists_isShellCrossing_subPath hr hπ hτ₁.1
    hτ₁.2 le_rfl hτ₁K hy' fun u hu => hπB ⟨hτ₁.1.trans hu.1, hu.2⟩
  obtain ⟨s₁, hs₁, s₂, hs₂, hjoin, hdist⟩ := hgood _ _ hcr₁ hcr₂
  -- the junction times
  set σ := (t₁ - t₀) * (1 - s₁) + t₀ with hσdef
  set τ := (t₁' - t₀') * s₂ + t₀' with hτdef
  have hσI : σ ∈ Icc t₀ t₁ := affine_mem_Icc ht₀₁.le ⟨by linarith [hs₁.2], by linarith [hs₁.1]⟩
  have hτI : τ ∈ Icc t₀' t₁' := affine_mem_Icc ht₀₁'.le hs₂
  have hσsh : π σ ∈ cbox z r₁ \ obox z r₂ := hcr₁.inShell hs₁
  have hτsh : π τ ∈ cbox z r₁ \ obox z r₂ := hcr₂.inShell hs₂
  have hjoin' : PcwJoined ((cbox z r₁ \ obox z r₂) ∩ B) (π σ) (π τ) := hjoin
  have hdist' : lfppDistOn ξ φ ((cbox z r₁ \ obox z r₂) ∩ B) (π σ) (π τ) ≤ t := hdist
  -- the detour
  obtain ⟨I, hI, hIV, hIlen⟩ := exists_lfppLength_lt hjoin' (hdist'.trans_lt htc)
  have hσ0 : 0 ≤ σ := ht₀.trans hσI.1
  have hσσ₂ : σ ≤ σ₂ := hσI.2.trans ht₁
  have hτ₁τ : τ₁ ≤ τ := ht₀'.trans hτI.1
  have hτ1 : τ ≤ 1 := hτI.2.trans ht₁'
  have hστ : σ ≤ τ := hσσ₂.trans (hστ₁.trans hτ₁τ)
  have hπ' : IsPcwC1Path (splicePath π I σ τ) x y := isPcwC1Path_splicePath hπ hI hσ0 hστ hτ1
  have hIA : ∀ u ∈ Ioo σ τ, I ((τ - σ)⁻¹ * (u - σ)) ∈ (cbox z r₁ \ obox z r₂) ∩ B :=
    fun u hu => hIV (Ioo_subset_Icc_self (inv_mul_sub_mem_Ioo hu))
  refine ⟨splicePath π I σ τ, hπ', fun u hu => mapsTo_splicePath hπB
    (hIV.mono_right inter_subset_right) hu, ?_, ?_, ?_⟩
  · -- the new path avoids the open inner box
    intro u hu
    by_cases hmid : u ∈ Ioo σ τ
    · rw [splicePath_of_mem hmid]
      exact (hIA u hmid).1.2
    rw [splicePath_of_notMem hmid]
    have hout : u ≤ σ ∨ τ ≤ u := by
      by_contra h
      push Not at h
      exact hmid ⟨h.1, h.2⟩
    rcases hout with h | h
    · rcases h.lt_or_eq with h | rfl
      · exact fun h' => hbefore u hu (h.trans_le hσσ₂)
          (HigherDimLFPP.DGZ.obox_subset_cbox z r₂ h')
      · exact hσsh.2
    · rcases h.lt_or_eq with h | rfl
      · exact fun h' => hafter u hu (hτ₁τ.trans_lt h)
          (HigherDimLFPP.DGZ.obox_subset_cbox z r₂ h')
      · exact hτsh.2
  · -- new points are old points or lie in the outer box
    intro u hu
    by_cases hmid : u ∈ Ioo σ τ
    · rw [splicePath_of_mem hmid]
      exact Or.inr ⟨(hIA u hmid).1.1, σ₂, hσ₂, hσ₂K⟩
    · rw [splicePath_of_notMem hmid]
      exact Or.inl ⟨u, hu, rfl⟩
  · -- the length bookkeeping
    intro J hJ hJm
    refine ⟨J \ Ioo σ τ, sdiff_subset, hJm.diff measurableSet_Ioo,
      fun u hu => splicePath_of_notMem hu.2, ?_⟩
    have hint : IntegrableOn (lfppIntegrand ξ φ (splicePath π I σ τ)) J :=
      (integrableOn_lfppIntegrand hπ' hφ ξ).mono_set hJ
    rw [← integral_inter_add_sdiff measurableSet_Ioo hint, setIntegral_sdiff_splicePath hJm]
    have hmid : ∫ u in J ∩ Ioo σ τ, lfppIntegrand ξ φ (splicePath π I σ τ) u ≤ c :=
      (setIntegral_inter_Ioo_splicePath_le hφ hπ' hσ0 hστ hτ1 J).trans hIlen.le
    refine ⟨by linarith, fun hJc => ?_⟩
    have he : J ∩ Ioo σ τ = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun u hu => hJc u hu.1 ?_
      rw [splicePath_of_mem hu.2]
      exact (hIA u hu.2).1.1
    rw [he, Measure.restrict_empty, integral_zero_measure, zero_add]

end Detour

end HigherDimLQGMetric.DGZ
