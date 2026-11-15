/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA2

/-!
# A.2, part 2: the unbounded side of a crosscut, and countable rational-ball chains

Packet PROVE-ZHAN-A2P2. Source: Astra, *Follow-up proofs and dependency audit*, §A.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L537–L561; R38, R53). The deterministic planar topology behind
"the entire large hull lies on the bounded side of `J`" and "the following countable argument" (L555–L561).

## Main results

* `exists_isCrosscutDomain`: **every simple real crosscut `γ` with `(γ 0).re < (γ 1).re` has an unbounded side**
  `D` (`IsCrosscutDomain D γ`): the connected component of `ℍ \ γ([0, 1])` containing the far points. The inclusion
  `γ((0, 1)) ⊆ ∂D` is the Jordan curve theorem for `γ([0, 1]) ∪ [γ 0, γ 1]`: the part in `ℍ` of its unbounded
  complementary component lies in `D` (the same open–closed argument as `IsCrosscutDomain.exists_inside`), and that
  component has the whole curve as frontier.
* `isPreconnected_farH`: the far part `{z ∈ ℍ : R < ‖z‖}` of `ℍ` is preconnected.
* `exists_chain`: **countable rational-ball chains.** If `D ⊆ ℍ` is open, preconnected and contains the far part
  `farH R`, every point of `D` lies in a set `chainOpen F ∪ farH R` that is preconnected, where `F` is a finite set of
  rational balls whose closures lie in `D` (`IsGoodChain D F`). This replaces the source's "rational polygonal
  crosscut `α`" (L557): the countable family is indexed by `Finset (ℚ × ℚ × ℚ)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology

namespace InteractingSLE.ZhanGT4.A2Part2

open QuantumZipper (H)

/-! ### The far part of `ℍ` -/

/-- The far part of the upper half-plane: points of `ℍ` of modulus `> R`. -/
def farH (R : ℝ) : Set ℂ := {z : ℂ | 0 < z.im ∧ R < ‖z‖}

theorem farH_subset_H (R : ℝ) : farH R ⊆ H := fun _ hz => hz.1

theorem isOpen_farH (R : ℝ) : IsOpen (farH R) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt continuous_const continuous_norm)

theorem norm_le_of_im_le {z : ℂ} {t : ℝ} (hz : 0 ≤ z.im) (ht : 0 ≤ t) : ‖z‖ ≤ ‖z + (t : ℂ) * I‖ := by
  have h1 : ‖z‖ ^ 2 ≤ ‖z + (t : ℂ) * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im,
      mul_im]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

theorem abs_im_le_norm' (z : ℂ) : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z

/-- **The far part of `ℍ` is preconnected**: every point goes straight up to height `> R + 1` and then along a
segment, at height `≥ R + 1`, to `(R + 1) i`. -/
theorem isPreconnected_farH (R : ℝ) (hR : 0 ≤ R) : IsPreconnected (farH R) := by
  set x₀ : ℂ := ((R + 1 : ℝ) : ℂ) * I with hx₀
  refine isPreconnected_of_forall x₀ fun y hy => ?_
  set y' : ℂ := y + ((R + 1 : ℝ) : ℂ) * I with hy'
  have hy'im : y'.im = y.im + (R + 1) := by simp [hy']
  have hx₀im : x₀.im = R + 1 := by simp [hx₀]
  -- the vertical segment from `y` to `y'`
  have hseg1 : segment ℝ y y' ⊆ farH R := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨θ, hθ, rfl⟩ := hw
    have hd : y' - y = ((R + 1 : ℝ) : ℂ) * I := by rw [hy']; ring
    have hθT : 0 ≤ θ * (R + 1) := mul_nonneg hθ.1 (by linarith)
    have he : y + θ • (y' - y) = y + ((θ * (R + 1) : ℝ) : ℂ) * I := by
      rw [hd, real_smul, ofReal_mul]; ring
    show y + θ • (y' - y) ∈ farH R
    rw [he]
    refine ⟨?_, lt_of_lt_of_le hy.2 (norm_le_of_im_le hy.1.le hθT)⟩
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith [hy.1]
  -- the segment from `y'` to `x₀`, at height `≥ R + 1`
  have hseg2 : segment ℝ y' x₀ ⊆ farH R := by
    intro w hw
    have him : R + 1 ≤ w.im := by
      have hconv : Convex ℝ {z : ℂ | R + 1 ≤ z.im} :=
        convex_halfSpace_ge (f := fun z : ℂ => z.im) Complex.imLm.isLinear (R + 1)
      refine hconv.segment_subset ?_ ?_ hw
      · show R + 1 ≤ y'.im
        rw [hy'im]; linarith [hy.1]
      · show R + 1 ≤ x₀.im
        rw [hx₀im]
    refine ⟨by linarith, ?_⟩
    have := abs_im_le_norm' w
    have : w.im ≤ |w.im| := le_abs_self _
    linarith
  refine ⟨segment ℝ y y' ∪ segment ℝ y' x₀, union_subset hseg1 hseg2, Or.inr (right_mem_segment _ _ _),
    Or.inl (left_mem_segment _ _ _), ?_⟩
  exact (convex_segment y y').isPreconnected.union y' (right_mem_segment _ _ _) (left_mem_segment _ _ _)
    (convex_segment y' x₀).isPreconnected

theorem mem_farH_of_im {R t : ℝ} (ht : R < t) (ht0 : 0 < t) : ((t : ℝ) : ℂ) * I ∈ farH R := by
  refine ⟨by simpa using ht0, ?_⟩
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
  exact ht

theorem not_isBounded_farH (R : ℝ) : ¬ IsBounded (farH R) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.subset_ball (0 : ℂ)
  have ht0 : 0 < |R| + |M| + 1 := by positivity
  have hRt : R < |R| + |M| + 1 := by linarith [le_abs_self R, abs_nonneg M]
  have h := hM (mem_farH_of_im hRt ht0)
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht0] at h
  linarith [le_abs_self M, abs_nonneg R]

/-! ### The unbounded side of a crosscut -/

section Domain

variable {γ : ℝ → ℂ}

theorem isCompact_image_Icc (hγ : IsRealCrosscut γ) : IsCompact (γ '' Icc 0 1) :=
  isCompact_Icc.image_of_continuousOn hγ.1

/-- The points of `γ([0, 1])` in `ℍ` are the points of `γ((0, 1))`. -/
theorem mem_image_Ioo_of_mem_H (hγ : IsRealCrosscut γ) {z : ℂ} (hz : z ∈ γ '' Icc 0 1) (hzH : z ∈ H) :
    z ∈ γ '' Ioo 0 1 := by
  obtain ⟨s, hs, rfl⟩ := hz
  have hzH' : 0 < (γ s).im := hzH
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h, hγ.2.2.2.1] at hzH'; exact absurd hzH' (lt_irrefl _)
  rcases eq_or_lt_of_le hs.2 with h' | h'
  · rw [h', hγ.2.2.2.2] at hzH'; exact absurd hzH' (lt_irrefl _)
  exact mem_image_of_mem γ ⟨h, h'⟩

/-- **The unbounded side of a simple real crosscut** (Jordan separation): the connected component `D` of
`ℍ \ γ([0, 1])` containing the far points is open, preconnected, contains every far point of `ℍ`, and its frontier in
`ℍ` is `γ((0, 1))`. -/
theorem exists_isCrosscutDomain (hγ : IsRealCrosscut γ) (hlt : (γ 0).re < (γ 1).re) :
    ∃ D : Set ℂ, IsCrosscutDomain D γ := by
  set Γ := crosscutCurve γ with hΓ
  have hΓc : IsCompact Γ := isCompact_crosscutCurve hγ
  have hJc : IsCompact (γ '' Icc 0 1) := isCompact_image_Icc hγ
  have hJΓ : γ '' Icc 0 1 ⊆ Γ := subset_union_left
  obtain ⟨R₀, hR₀⟩ := hΓc.isBounded.subset_ball (0 : ℂ)
  set R₁ : ℝ := max R₀ 1 with hR₁
  have hR₁0 : 0 < R₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΓR : ∀ z ∈ Γ, ‖z‖ < R₁ := fun z hz => by
    have := hR₀ hz
    rw [mem_ball_zero_iff] at this
    exact lt_of_lt_of_le this (le_max_left _ _)
  set O := H \ γ '' Icc 0 1 with hO
  have hOo : IsOpen O := QuantumZipper.isOpen_H.sdiff hJc.isClosed
  have hfarO : farH R₁ ⊆ O := fun z hz =>
    ⟨hz.1, fun hzJ => absurd (hΓR z (hJΓ hzJ)) (not_lt.2 hz.2.le)⟩
  set z₀ : ℂ := ((R₁ + 1 : ℝ) : ℂ) * I with hz₀
  have hz₀f : z₀ ∈ farH R₁ := mem_farH_of_im (by linarith) (by linarith)
  set D := connectedComponentIn O z₀ with hD
  have hDO : D ⊆ O := connectedComponentIn_subset _ _
  have hDo : IsOpen D := hOo.connectedComponentIn
  have hsubD : ∀ {C : Set ℂ}, IsPreconnected C → C ⊆ O → (C ∩ D).Nonempty → C ⊆ D := by
    intro C hC hCO hCD
    obtain ⟨w, hwC, hwD⟩ := hCD
    have h := hC.subset_connectedComponentIn hwC hCO
    rwa [← connectedComponentIn_eq hwD] at h
  have hfarD : farH R₁ ⊆ D := hsubD (isPreconnected_farH R₁ hR₁0.le) hfarO
    ⟨z₀, hz₀f, mem_connectedComponentIn (hfarO hz₀f)⟩
  -- real rays beyond the ends have relative half-disc neighbourhoods in `D`
  have hthick : ∀ {S : Set ℂ}, IsClosed S → Convex ℝ S → (∀ z ∈ S, z.im = 0) → Disjoint S Γ →
      (∀ M : ℝ, ∃ z ∈ S, M < ‖z‖) → ∃ δ > (0 : ℝ), thickening δ S ∩ H ⊆ D := by
    intro S hSc hSv hSr hSΓ hSu
    obtain ⟨z₁, hz₁S, -⟩ := hSu 0
    have hSne : S.Nonempty := ⟨z₁, hz₁S⟩
    have hΓne : Γ.Nonempty := ⟨γ 0, Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
    obtain ⟨w₀, hw₀, hmin⟩ := hΓc.exists_isMinOn hΓne (continuous_infDist_pt S).continuousOn
    have hδ : 0 < infDist w₀ S :=
      (hSc.notMem_iff_infDist_pos hSne).1 fun h => Set.disjoint_left.1 hSΓ h hw₀
    refine ⟨infDist w₀ S, hδ, ?_⟩
    have hconv : Convex ℝ (thickening (infDist w₀ S) S ∩ H) := (hSv.thickening _).inter
      (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)
    refine hsubD hconv.isPreconnected (fun z hz => ⟨hz.2, fun hzJ => ?_⟩) ?_
    · obtain ⟨w, hwS, hwd⟩ := mem_thickening_iff.1 hz.1
      have h1 : infDist w₀ S ≤ infDist z S := hmin (hJΓ hzJ)
      have h2 : infDist z S ≤ dist z w := infDist_le_dist_of_mem hwS
      linarith
    · obtain ⟨w, hwS, hwR⟩ := hSu (R₁ + infDist w₀ S)
      set z : ℂ := w + ((infDist w₀ S / 2 : ℝ) : ℂ) * I with hz
      have hzim : z.im = infDist w₀ S / 2 := by simp [hz, hSr w hwS]
      have hzH : z ∈ H := by show 0 < z.im; rw [hzim]; linarith
      have hzw : dist z w = infDist w₀ S / 2 := by
        rw [dist_eq_norm, hz, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)]
      refine ⟨z, ⟨mem_thickening_iff.2 ⟨w, hwS, by rw [hzw]; linarith⟩, hzH⟩, hfarD ⟨hzH, ?_⟩⟩
      have := norm_sub_norm_le w z
      rw [← dist_eq_norm, dist_comm, hzw] at this
      linarith
  have hIic : ∀ {x : ℝ}, x < (γ 0).re → Disjoint (((↑) : ℝ → ℂ) '' Iic x) Γ := by
    intro x hx
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyΓ
    have := re_mem_Icc_of_mem_crosscutCurve hγ hlt hyΓ (by simp)
    rw [Complex.ofReal_re] at this
    exact absurd (lt_of_le_of_lt hy hx) (not_lt.2 this.1)
  have hIci : ∀ {x : ℝ}, (γ 1).re < x → Disjoint (((↑) : ℝ → ℂ) '' Ici x) Γ := by
    intro x hx
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyΓ
    have := re_mem_Icc_of_mem_crosscutCurve hγ hlt hyΓ (by simp)
    rw [Complex.ofReal_re] at this
    exact absurd (lt_of_lt_of_le hx hy) (not_lt.2 this.2)
  have hhalf : ∀ {x : ℝ}, (x < (γ 0).re ∨ (γ 1).re < x) → ∃ δ > (0 : ℝ), ball (x : ℂ) δ ∩ H ⊆ D := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨δ, hδ, h⟩ := hthick (IsCrosscutDomain.isClosed_ofReal_image isClosed_Iic)
        (IsCrosscutDomain.convex_ofReal_image (convex_Iic x))
        (by rintro _ ⟨y, -, rfl⟩; simp) (hIic hx) fun M => ⟨((min x (-|M| - 1) : ℝ) : ℂ),
          mem_image_of_mem _ (show min x (-|M| - 1) ∈ Iic x from mem_Iic.2 (min_le_left _ _)), by
            rw [Complex.norm_real, Real.norm_eq_abs]
            have h1 := min_le_right x (-|M| - 1)
            have h0 := abs_nonneg M
            have h2 : -min x (-|M| - 1) ≤ |min x (-|M| - 1)| := neg_le_abs _
            linarith [le_abs_self M]⟩
      exact ⟨δ, hδ, fun z hz => h ⟨mem_thickening_iff.2 ⟨x, ⟨x, mem_Iic.2 le_rfl, rfl⟩, hz.1⟩, hz.2⟩⟩
    · obtain ⟨δ, hδ, h⟩ := hthick (IsCrosscutDomain.isClosed_ofReal_image isClosed_Ici)
        (IsCrosscutDomain.convex_ofReal_image (convex_Ici x))
        (by rintro _ ⟨y, -, rfl⟩; simp) (hIci hx) fun M => ⟨((max x (|M| + 1) : ℝ) : ℂ),
          mem_image_of_mem _ (show max x (|M| + 1) ∈ Ici x from mem_Ici.2 (le_max_left _ _)), by
            rw [Complex.norm_real, Real.norm_eq_abs]
            have h1 := le_max_right x (|M| + 1)
            have h2 := le_abs_self (max x (|M| + 1))
            linarith [le_abs_self M]⟩
      exact ⟨δ, hδ, fun z hz => h ⟨mem_thickening_iff.2 ⟨x, ⟨x, mem_Ici.2 le_rfl, rfl⟩, hz.1⟩, hz.2⟩⟩
  -- `frontier D ∩ ℍ ⊆ γ((0, 1))`
  have hfr1 : frontier D ∩ H ⊆ γ '' Ioo 0 1 := by
    rintro z ⟨hzf, hzH⟩
    have hzD : z ∉ D := fun h => hzf.2 (by rwa [hDo.interior_eq])
    by_cases hzO : z ∈ O
    · exfalso
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hOo z hzO
      obtain ⟨w, hwD, hwd⟩ := Metric.mem_closure_iff.1 hzf.1 r hr
      exact hzD (hsubD (convex_ball z r).isPreconnected hball
        ⟨w, by rw [mem_ball, dist_comm]; exact hwd, hwD⟩ (mem_ball_self hr))
    · have hzJ : z ∈ γ '' Icc 0 1 := by
        by_contra h
        exact hzO ⟨hzH, h⟩
      exact mem_image_Ioo_of_mem_H hγ hzJ hzH
  -- the Jordan components of `Γ`
  obtain ⟨x₁, -, x₀, -, hb, -, hdisj, hunion, -, hfr₀⟩ :=
    jordan_curve_components (isJordanCurve_crosscutCurve hγ hlt)
  set V := connectedComponentIn Γᶜ x₁ with hV
  set U := connectedComponentIn Γᶜ x₀ with hU
  obtain ⟨R₂, hR₂⟩ := (hb.union hΓc.isBounded).subset_ball (0 : ℂ)
  have hfarU : ∀ z : ℂ, R₂ ≤ ‖z‖ → z ∈ U := by
    intro z hz
    have hzV : z ∉ V := fun h => by
      have := hR₂ (Or.inl h); rw [mem_ball_zero_iff] at this; linarith
    have hzΓ : z ∉ Γ := fun h => by
      have := hR₂ (Or.inr h); rw [mem_ball_zero_iff] at this; linarith
    have : z ∈ Γᶜ := hzΓ
    rw [hunion] at this
    exact this.resolve_left hzV
  have hR₂0 : 0 ≤ R₂ := by
    have := hR₂ (Or.inr (Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩) : γ 0 ∈ V ∪ Γ)
    rw [mem_ball_zero_iff] at this; linarith [norm_nonneg (γ 0)]
  have hLΓ : lowerHalf ⊆ Γᶜ := fun z hz hzΓ => by
    have := crosscutCurve_im_nonneg hγ hzΓ
    exact absurd hz (not_lt.2 this)
  have hzL : (-(R₂ + 1 : ℝ) : ℂ) * I ∈ lowerHalf := by
    show (_ : ℂ).im < 0; simp; linarith
  have hzLn : R₂ ≤ ‖(-(R₂ + 1 : ℝ) : ℂ) * I‖ := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  have hLU : lowerHalf ⊆ U := by
    have h := isPreconnected_lowerHalf.subset_connectedComponentIn hzL hLΓ
    rwa [← connectedComponentIn_eq (hfarU _ hzLn)] at h
  -- the other components of `O`
  set O' := O \ D with hO'
  have hO'o : IsOpen O' := by
    rw [isOpen_iff_forall_mem_open]
    intro w hw
    refine ⟨connectedComponentIn O w, fun v hv => ⟨connectedComponentIn_subset _ _ hv, fun hvD => ?_⟩,
      hOo.connectedComponentIn, mem_connectedComponentIn hw.1⟩
    have h1 : connectedComponentIn O w = connectedComponentIn O v := connectedComponentIn_eq hv
    have h2 : D = connectedComponentIn O v := connectedComponentIn_eq hvD
    exact hw.2 (by rw [h2, ← h1]; exact mem_connectedComponentIn hw.1)
  have hclH : closure O' ⊆ {z : ℂ | 0 ≤ z.im} := by
    have : closure O' ⊆ closure H := closure_mono fun z hz => hz.1.1
    rwa [show closure H = {z : ℂ | 0 ≤ z.im} from Complex.closure_setOfPred_lt_im 0] at this
  have hUO' : U ∩ O' = ∅ := by
    have hsub : U ⊆ (closure O')ᶜ := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union
        isClosed_closure.isOpen_compl hO'o
        (Set.disjoint_left.2 fun z hz hz' => hz (subset_closure hz')) (fun y hy => ?_) ?_
      · by_cases hyc : y ∈ closure O'
        swap
        · exact Or.inl hyc
        right
        have hyΓ : y ∉ Γ := connectedComponentIn_subset _ _ hy
        rcases eq_or_lt_of_le (show 0 ≤ y.im from hclH hyc) with h | h
        · exfalso
          have hyre : y.re < (γ 0).re ∨ (γ 1).re < y.re := by
            by_contra hc
            push Not at hc
            exact hyΓ (by
              rw [eq_ofReal_re_of_im_eq_zero h.symm]
              exact mem_crosscutCurve_of_real hγ hlt hc)
          obtain ⟨δ, hδ, hball⟩ := hhalf hyre
          have hy' : (y.re : ℂ) = y := (eq_ofReal_re_of_im_eq_zero h.symm).symm
          rw [hy'] at hball
          obtain ⟨w, hwO, hwb⟩ := Metric.mem_closure_iff.1 hyc δ hδ
          rw [dist_comm] at hwb
          exact hwO.2 (hball ⟨hwb, hwO.1.1⟩)
        · have hyH : y ∈ H := h
          refine ⟨⟨hyH, fun hyJ => hyΓ (hJΓ hyJ)⟩, fun hyD => ?_⟩
          obtain ⟨w, hwD, hwO'⟩ := mem_closure_iff.1 hyc D hDo hyD
          exact hwO'.2 hwD
      · refine ⟨_, hLU hzL, fun hzO => ?_⟩
        have h1 : 0 ≤ ((-(R₂ + 1 : ℝ) : ℂ) * I).im := hclH hzO
        have h2 : ((-(R₂ + 1 : ℝ) : ℂ) * I).im < 0 := hzL
        linarith
    exact Set.eq_empty_iff_forall_notMem.2 fun z hz => hsub hz.1 (subset_closure hz.2)
  have hUHD : ∀ u ∈ U, u ∈ H → u ∈ D := by
    intro u hu huH
    have huΓ : u ∉ Γ := connectedComponentIn_subset _ _ hu
    by_contra huD
    exact (Set.eq_empty_iff_forall_notMem.1 hUO') u ⟨hu, ⟨huH, fun huJ => huΓ (hJΓ huJ)⟩, huD⟩
  -- `γ((0, 1)) ⊆ frontier D`
  have hfr2 : γ '' Ioo 0 1 ⊆ frontier D ∩ H := by
    rintro _ ⟨s, hs, rfl⟩
    have hpH : γ s ∈ H := hγ.2.2.1 (mem_image_of_mem γ hs)
    have hpJ : γ s ∈ γ '' Icc 0 1 := mem_image_of_mem γ (Ioo_subset_Icc_self hs)
    have hpD : γ s ∉ D := fun h => (hDO h).2 hpJ
    have hpU : γ s ∈ closure U := by
      have : γ s ∈ frontier U := by rw [hfr₀]; exact hJΓ hpJ
      exact this.1
    refine ⟨⟨Metric.mem_closure_iff.2 fun ε hε => ?_, by rwa [hDo.interior_eq]⟩, hpH⟩
    have hpH' : 0 < (γ s).im := hpH
    obtain ⟨u, huU, hud⟩ := Metric.mem_closure_iff.1 hpU (min ε (γ s).im) (lt_min hε hpH')
    refine ⟨u, hUHD u huU ?_, lt_of_lt_of_le hud (min_le_left _ _)⟩
    have h1 : |(γ s - u).im| ≤ dist (γ s) u := by
      rw [dist_eq_norm]; exact Complex.abs_im_le_norm _
    rw [sub_im] at h1
    have h2 : dist (γ s) u < (γ s).im := lt_of_lt_of_le hud (min_le_right _ _)
    show 0 < u.im
    have := le_abs_self ((γ s).im - u.im)
    linarith
  exact ⟨D, ⟨hDo, fun z hz => (hDO hz).1, isPreconnected_connectedComponentIn,
    ⟨R₁, fun z hz hzR => hfarD ⟨hz, hzR⟩⟩, hγ, hlt, Subset.antisymm hfr1 hfr2⟩⟩

end Domain

/-! ### Rational-ball chains -/

section Chain

/-- The centre `a + b i` of the rational ball with code `(a, b, r)`. -/
def ratCenter (b : ℚ × ℚ × ℚ) : ℂ := ⟨(b.1 : ℝ), (b.2.1 : ℝ)⟩

/-- The radius `r` of the rational ball with code `(a, b, r)`. -/
def ratRad (b : ℚ × ℚ × ℚ) : ℝ := (b.2.2 : ℝ)

/-- The union of the open rational balls of a finite set of codes. -/
def chainOpen (F : Finset (ℚ × ℚ × ℚ)) : Set ℂ := ⋃ b ∈ F, ball (ratCenter b) (ratRad b)

/-- The union of the closed rational balls of a finite set of codes. -/
def chainClosed (F : Finset (ℚ × ℚ × ℚ)) : Set ℂ := ⋃ b ∈ F, closedBall (ratCenter b) (ratRad b)

/-- A finite set of rational balls of positive radius whose closures lie in `D`. -/
def IsGoodChain (D : Set ℂ) (F : Finset (ℚ × ℚ × ℚ)) : Prop :=
  ∀ b ∈ F, 0 < ratRad b ∧ closedBall (ratCenter b) (ratRad b) ⊆ D

theorem isOpen_chainOpen (F : Finset (ℚ × ℚ × ℚ)) : IsOpen (chainOpen F) :=
  isOpen_biUnion fun _ _ => isOpen_ball

theorem isCompact_chainClosed (F : Finset (ℚ × ℚ × ℚ)) : IsCompact (chainClosed F) :=
  F.isCompact_biUnion fun _ _ => isCompact_closedBall _ _

theorem chainOpen_subset_chainClosed (F : Finset (ℚ × ℚ × ℚ)) : chainOpen F ⊆ chainClosed F :=
  iUnion₂_mono fun _ _ => ball_subset_closedBall

theorem IsGoodChain.chainClosed_subset {D : Set ℂ} {F : Finset (ℚ × ℚ × ℚ)} (h : IsGoodChain D F) :
    chainClosed F ⊆ D :=
  iUnion₂_subset fun b hb => (h b hb).2

theorem IsGoodChain.mono {D D' : Set ℂ} {F : Finset (ℚ × ℚ × ℚ)} (h : IsGoodChain D F) (hDD' : D ⊆ D') :
    IsGoodChain D' F :=
  fun b hb => ⟨(h b hb).1, (h b hb).2.trans hDD'⟩

/-- The closed balls of a good chain lie in the closure of its open balls. -/
theorem IsGoodChain.chainClosed_subset_closure {D : Set ℂ} {F : Finset (ℚ × ℚ × ℚ)} (h : IsGoodChain D F) :
    chainClosed F ⊆ closure (chainOpen F) := by
  refine iUnion₂_subset fun b hb => ?_
  rw [← closure_ball _ (h b hb).1.ne']
  exact closure_mono (subset_biUnion_of_mem (u := fun b => ball (ratCenter b) (ratRad b)) hb)

theorem chainOpen_insert (b : ℚ × ℚ × ℚ) (F : Finset (ℚ × ℚ × ℚ)) :
    chainOpen (insert b F) = ball (ratCenter b) (ratRad b) ∪ chainOpen F := by
  simp only [chainOpen, Finset.set_biUnion_insert]

theorem chainOpen_empty : chainOpen ∅ = ∅ := by simp [chainOpen]

/-- **A rational ball around a point of an open set**, with its closure inside the set. -/
theorem exists_ratBall {D : Set ℂ} (hD : IsOpen D) {w : ℂ} (hw : w ∈ D) :
    ∃ b : ℚ × ℚ × ℚ, 0 < ratRad b ∧ closedBall (ratCenter b) (ratRad b) ⊆ D ∧
      w ∈ ball (ratCenter b) (ratRad b) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hD w hw
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 3 by positivity)
  have hq0' : (0 : ℝ) < q := hq0
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show w.re - q / 2 < w.re + q / 2 by linarith)
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show w.im - q / 2 < w.im + q / 2 by linarith)
  have hdist : dist w (ratCenter (a, c, q)) < q := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    have hre : (w - ratCenter (a, c, q)).re = w.re - a := by simp [ratCenter]
    have him : (w - ratCenter (a, c, q)).im = w.im - c := by simp [ratCenter]
    rw [hre, him]
    have h1 : |w.re - a| < q / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    have h2 : |w.im - c| < q / 2 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    linarith
  refine ⟨(a, c, q), hq0', fun v hv => hball ?_, ?_⟩
  · rw [mem_closedBall] at hv
    rw [mem_ball]
    have := dist_triangle v (ratCenter (a, c, q)) w
    rw [dist_comm (ratCenter (a, c, q)) w] at this
    have hv' : dist v (ratCenter (a, c, q)) ≤ q := hv
    linarith
  · rw [mem_ball]; exact hdist

/-- **Countable rational-ball chains** (replacing the source's rational polygonal crosscut, L557). If `D` is open
and preconnected and contains the far part `farH R`, every point `z ∈ D` lies in `chainOpen F ∪ farH R` for a good
chain `F` of `D` with `chainOpen F ∪ farH R` preconnected. -/
theorem exists_chain {D : Set ℂ} (hDo : IsOpen D) (hDc : IsPreconnected D) {R : ℝ} (hR : 0 ≤ R)
    (hfar : farH R ⊆ D) {z : ℂ} (hz : z ∈ D) :
    ∃ F : Finset (ℚ × ℚ × ℚ), IsGoodChain D F ∧ IsPreconnected (chainOpen F ∪ farH R) ∧
      z ∈ chainOpen F ∪ farH R := by
  set C := {w : ℂ | ∃ F : Finset (ℚ × ℚ × ℚ), IsGoodChain D F ∧ IsPreconnected (chainOpen F ∪ farH R) ∧
      w ∈ chainOpen F ∪ farH R} with hC
  have hadd : ∀ {F : Finset (ℚ × ℚ × ℚ)} {b : ℚ × ℚ × ℚ}, IsGoodChain D F →
      IsPreconnected (chainOpen F ∪ farH R) → 0 < ratRad b → closedBall (ratCenter b) (ratRad b) ⊆ D →
      (ball (ratCenter b) (ratRad b) ∩ (chainOpen F ∪ farH R)).Nonempty →
      ball (ratCenter b) (ratRad b) ⊆ C := by
    intro F b hF hFc hb0 hbD hne v hv
    refine ⟨insert b F, fun b' hb' => ?_, ?_, ?_⟩
    · rcases Finset.mem_insert.1 hb' with rfl | h
      · exact ⟨hb0, hbD⟩
      · exact hF b' h
    · rw [chainOpen_insert, union_assoc]
      exact (convex_ball _ _).isPreconnected.union' hne hFc
    · rw [chainOpen_insert, union_assoc]
      exact Or.inl hv
  have hmemD : ∀ {F : Finset (ℚ × ℚ × ℚ)} {w : ℂ}, IsGoodChain D F → w ∈ chainOpen F ∪ farH R → w ∈ D := by
    intro F w hF hw
    rcases hw with h | h
    · exact hF.chainClosed_subset (chainOpen_subset_chainClosed F h)
    · exact hfar h
  have hCo : IsOpen C := by
    rw [isOpen_iff_forall_mem_open]
    intro w hw
    obtain ⟨F, hF, hFc, hwF⟩ := hw
    obtain ⟨b, hb0, hbD, hwb⟩ := exists_ratBall hDo (hmemD hF hwF)
    exact ⟨_, hadd hF hFc hb0 hbD ⟨w, hwb, hwF⟩, isOpen_ball, hwb⟩
  have hDCo : IsOpen (D \ C) := by
    rw [isOpen_iff_forall_mem_open]
    intro w hw
    obtain ⟨b, hb0, hbD, hwb⟩ := exists_ratBall hDo hw.1
    refine ⟨ball (ratCenter b) (ratRad b), fun v hv => ⟨hbD (ball_subset_closedBall hv), fun hvC => ?_⟩,
      isOpen_ball, hwb⟩
    obtain ⟨F, hF, hFc, hvF⟩ := hvC
    exact hw.2 (hadd hF hFc hb0 hbD ⟨v, hv, hvF⟩ hwb)
  have hfar0 : ((R + 1 : ℝ) : ℂ) * I ∈ farH R := mem_farH_of_im (by linarith) (by linarith)
  have hCne : (D ∩ C).Nonempty := by
    refine ⟨_, hfar hfar0, ∅, fun b hb => absurd hb (Finset.notMem_empty b), ?_, ?_⟩
    · rw [chainOpen_empty, empty_union]; exact isPreconnected_farH R hR
    · rw [chainOpen_empty, empty_union]; exact hfar0
  have hsub : D ⊆ C := hDc.subset_left_of_subset_union hCo hDCo
    (Set.disjoint_left.2 fun w hw hw' => hw'.2 hw)
    (fun w hw => by
      by_cases h : w ∈ C
      · exact Or.inl h
      · exact Or.inr ⟨hw, h⟩) hCne
  exact hsub hz

end Chain

end InteractingSLE.ZhanGT4.A2Part2
