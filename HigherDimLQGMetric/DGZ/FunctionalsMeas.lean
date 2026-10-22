import HigherDimLQGMetric.DGZ.Continuity
import HigherDimLQGMetric.DGZ.Crossing
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Measurability of the LFPP functionals (packet L3b1)

Source: MA7 (`planning/audits/MA7-ref2-sections-4-6.md`) §5 row L3b1 (`measurable_selfDiam`,
`measurable_acrossDist`), Details (a) D-4.6 (concentration needs `log Φ(X)` measurable), D-4.9
("`E` measurable: `selfDiam` is measurable, L3b1"), D-5.3 / Remark 5.4′ (statuses of boxes are
measurable functions of the field restricted to a box), D-6.9 and `DGZThm12Shape` (measurability of
the normalized metric as a random element of `C(ℝ^d × ℝ^d, ℝ)`).

Method. The functionals are infima or suprema over uncountably many pairs of a function that is
continuous on the pairs (`continuousOn_lfppDistOn`). Over a countable dense subset `T` of the index
set the infimum (supremum) is the same (`sInf_image_eq_iInf_of_dense`,
`sSup_image_eq_iSup_of_dense`; the junk value of a non-bounded supremum is matched), and the dense set
does not depend on the field; `Measurable.iInf`/`Measurable.iSup` and HigherDimLFPP's
`measurable_lfppDistOn` conclude.

Main results (for a random field `H` with continuous paths and measurable values):
* `measurable_lfppSetDist` (open preconnected `V ⊇ A ∪ B`), **`measurable_acrossDist`**,
  `measurable_lfppDiam` (open preconnected `V ⊇ U`), **`measurable_selfDiam`**,
  `measurable_lfppMetric`;
* Borel measurability on `C(ℝ^d, ℝ)` (for the law-transfer lemmas):
  `measurable_lfppSetDist_continuousMap`, `measurable_acrossDist_continuousMap`,
  `measurable_lfppDiam_continuousMap`, `measurable_selfDiam_continuousMap`;
* locality (measurability for the σ-algebra of the field restricted to a closed box):
  `measurable_selfDiam_comap` (field on `cbox c r`), `measurable_acrossDist_comap` (field on
  `cbox c r₁`), with `comap_restrict_le` (monotonicity in the restriction set);
* `measurable_continuousMap_of_eq_lfppMetric`: `ω ↦ (a · D^ξ(H(·, ω)))` as an element of
  `C(ℝ^d × ℝ^d, ℝ)` is measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ## Infima and suprema over a dense subset -/

section Dense

variable {X : Type*} [TopologicalSpace X] {f : X → ℝ} {A T : Set X}

omit [TopologicalSpace X] in
theorem range_restrict_eq_image (f : X → ℝ) (T : Set X) :
    range (fun p : T => f p) = f '' T := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

/-- Values on `A` lie in the closure of the values on a dense subset `T ⊆ A` (continuity on `A`). -/
theorem image_subset_closure_image_of_dense (hf : ContinuousOn f A) (hTA : T ⊆ A)
    (hAT : A ⊆ closure T) : f '' A ⊆ closure (f '' T) := by
  rintro _ ⟨a, ha, rfl⟩
  exact ((hf a ha).mono hTA).mem_closure_image (hAT ha)

/-- **Infimum over a dense subset**: for `f` continuous on `A`, bounded below on `A`, and `T ⊆ A`
dense in `A`, `inf_A f = inf_T f`. -/
theorem sInf_image_eq_iInf_of_dense (hf : ContinuousOn f A) (hTA : T ⊆ A) (hAT : A ⊆ closure T)
    (hbdd : BddBelow (f '' A)) : sInf (f '' A) = ⨅ p : T, f p := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hT : T = ∅ := subset_empty_iff.1 hTA
    subst hT
    rw [image_empty, Real.sInf_empty]
    exact (Real.iInf_of_isEmpty _).symm
  have hT : T.Nonempty := by
    by_contra hT
    rw [not_nonempty_iff_eq_empty] at hT
    rw [hT, closure_empty] at hAT
    exact hA.ne_empty (subset_empty_iff.1 hAT)
  have : Nonempty T := hT.to_subtype
  have hbddT : BddBelow (range fun p : T => f p) := by
    rw [range_restrict_eq_image]
    exact hbdd.mono (image_mono hTA)
  refine le_antisymm ?_ ?_
  · exact le_ciInf fun p => csInf_le hbdd ⟨p, hTA p.2, rfl⟩
  · refine le_csInf (hA.image f) fun y hy => ?_
    have hsub : f '' T ⊆ Ici (⨅ p : T, f p) := by
      rintro _ ⟨p, hp, rfl⟩
      exact ciInf_le hbddT ⟨p, hp⟩
    exact (isClosed_Ici.closure_subset_iff.2 hsub)
      (image_subset_closure_image_of_dense hf hTA hAT hy)

/-- **Supremum over a dense subset** (including the junk value `0` of an unbounded supremum): for
`f` continuous on `A` and `T ⊆ A` dense in `A`, `sSup (f '' A) = ⨆_{p ∈ T} f p`. -/
theorem sSup_image_eq_iSup_of_dense (hf : ContinuousOn f A) (hTA : T ⊆ A)
    (hAT : A ⊆ closure T) : sSup (f '' A) = ⨆ p : T, f p := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hT : T = ∅ := subset_empty_iff.1 hTA
    subst hT
    rw [image_empty, Real.sSup_empty]
    exact (Real.iSup_of_isEmpty _).symm
  have hT : T.Nonempty := by
    by_contra hT
    rw [not_nonempty_iff_eq_empty] at hT
    rw [hT, closure_empty] at hAT
    exact hA.ne_empty (subset_empty_iff.1 hAT)
  have : Nonempty T := hT.to_subtype
  have hcl := image_subset_closure_image_of_dense hf hTA hAT
  by_cases hbddT : BddAbove (f '' T)
  · have hbddT' : BddAbove (range fun p : T => f p) := by
      rw [range_restrict_eq_image]
      exact hbddT
    have hsub : f '' T ⊆ Iic (⨆ p : T, f p) := by
      rintro _ ⟨p, hp, rfl⟩
      exact le_ciSup hbddT' ⟨p, hp⟩
    have hle : f '' A ⊆ Iic (⨆ p : T, f p) :=
      hcl.trans (isClosed_Iic.closure_subset_iff.2 hsub)
    have hbddA : BddAbove (f '' A) := ⟨_, hle⟩
    refine le_antisymm (csSup_le (hA.image f) fun y hy => hle hy) ?_
    exact ciSup_le fun p => le_csSup hbddA ⟨p, hTA p.2, rfl⟩
  · have hbddA : ¬ BddAbove (f '' A) := fun h => hbddT (h.mono (image_mono hTA))
    rw [Real.sSup_of_not_bddAbove hbddA, Real.iSup_of_not_bddAbove]
    rwa [range_restrict_eq_image]

end Dense

/-- A subset of `ℝ^d × ℝ^d` has a countable dense subset. -/
theorem exists_countable_dense_subset_pairs (A : Set (Rd d × Rd d)) :
    ∃ T ⊆ A, T.Countable ∧ A ⊆ closure T := by
  obtain ⟨T, hTc, hTA, hAT⟩ := TopologicalSpace.exists_countable_dense_subset A
  exact ⟨T, hTA, hTc, hAT⟩

/-! ## Random fields -/

section Random

variable {Ω : Type*} [MeasurableSpace Ω] {H : Rd d → Ω → ℝ} {V U A B : Set (Rd d)}

/-- **Measurability of set distances**: for `V` open and preconnected and `A, B ⊆ V`,
`ω ↦ D(A, B; V)(H(·, ω))` is measurable. -/
theorem measurable_lfppSetDist (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) (hV : IsOpen V) (hVc : IsPreconnected V) (hA : A ⊆ V)
    (hB : B ⊆ V) (ξ : ℝ) : Measurable fun ω => lfppSetDist ξ (fun z => H z ω) V A B := by
  obtain ⟨T, hTA, hTc, hAT⟩ := exists_countable_dense_subset_pairs (A ×ˢ B)
  have heq : ∀ ω, lfppSetDist ξ (fun z => H z ω) V A B =
      ⨅ p : T, lfppDistOn ξ (fun z => H z ω) V p.1.1 p.1.2 := fun ω =>
    sInf_image_eq_iInf_of_dense ((continuousOn_lfppDistOn hV hVc (hc ω) ξ).mono
      (prod_mono hA hB)) hTA hAT (bddBelow_lfppSetDist _ _ _ _ _)
  simp_rw [heq]
  have := hTc.to_subtype
  exact Measurable.iInf fun p => measurable_lfppDistOn hc hm hV ξ p.1.1 p.1.2

/-- **Measurability of the across distance** (MA7 §5 row L3b1). -/
theorem measurable_acrossDist (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) (ξ : ℝ) (c : Rd d) (r₁ r₂ : ℝ) :
    Measurable fun ω => acrossDist ξ (fun z => H z ω) c r₁ r₂ :=
  measurable_lfppSetDist hc hm isOpen_univ convex_univ.isPreconnected (subset_univ _)
    (subset_univ _) ξ

/-- **Measurability of internal diameters**: for `V` open and preconnected and `U ⊆ V`,
`ω ↦ Diam(U; V)(H(·, ω))` is measurable (also when the supremum is infinite: junk value `0`). -/
theorem measurable_lfppDiam (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) (hV : IsOpen V) (hVc : IsPreconnected V) (hU : U ⊆ V)
    (ξ : ℝ) : Measurable fun ω => lfppDiam ξ (fun z => H z ω) U V := by
  obtain ⟨T, hTA, hTc, hAT⟩ := exists_countable_dense_subset_pairs (U ×ˢ U)
  have heq : ∀ ω, lfppDiam ξ (fun z => H z ω) U V =
      ⨆ p : T, lfppDistOn ξ (fun z => H z ω) V p.1.1 p.1.2 := fun ω =>
    sSup_image_eq_iSup_of_dense ((continuousOn_lfppDistOn hV hVc (hc ω) ξ).mono
      (prod_mono hU hU)) hTA hAT
  simp_rw [heq]
  have := hTc.to_subtype
  exact Measurable.iSup fun p => measurable_lfppDistOn hc hm hV ξ p.1.1 p.1.2

/-- **Measurability of the self-internal diameter** (MA7 §5 row L3b1, D-4.9). -/
theorem measurable_selfDiam (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) (ξ : ℝ) (c : Rd d) (r : ℝ) :
    Measurable fun ω => selfDiam ξ (fun z => H z ω) c r :=
  measurable_lfppDiam hc hm (HigherDimLFPP.DGZ.isOpen_obox c r)
    (HigherDimLFPP.DGZ.convex_obox c r).isPreconnected subset_rfl ξ

/-- Measurability of the whole-space metric at a fixed pair of points. -/
theorem measurable_lfppMetric (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) (ξ : ℝ) (x y : Rd d) :
    Measurable fun ω => lfppMetric ξ (fun z => H z ω) x y :=
  measurable_lfppDistOn hc hm isOpen_univ ξ x y

/-- **The normalized metric as a random continuous function** (for `DGZThm12Shape`): if
`F ω (x, y) = a · D^ξ(H(·, ω))(x, y)` for all `ω, x, y`, then `F : Ω → C(ℝ^d × ℝ^d, ℝ)` is
measurable (Borel σ-algebra of the compact-open topology). -/
theorem measurable_continuousMap_of_eq_lfppMetric (hc : ∀ ω, Continuous fun z => H z ω)
    (hm : ∀ z, Measurable (H z)) (ξ a : ℝ) {F : Ω → C(Rd d × Rd d, ℝ)}
    (hF : ∀ ω p, F ω p = a * lfppMetric ξ (fun z => H z ω) p.1 p.2) : Measurable F := by
  refine ContinuousMap.measurable_iff_eval.2 fun p => ?_
  have heq : (fun ω => F ω p) = fun ω => a * lfppMetric ξ (fun z => H z ω) p.1 p.2 :=
    funext fun ω => hF ω p
  rw [heq]
  exact (measurable_lfppMetric hc hm ξ p.1 p.2).const_mul a

end Random

/-! ## Borel measurability on `C(ℝ^d, ℝ)` -/

section ContinuousMap

variable [MeasurableSpace C(Rd d, ℝ)] [OpensMeasurableSpace C(Rd d, ℝ)] {V U A B : Set (Rd d)}

theorem measurable_lfppSetDist_continuousMap (hV : IsOpen V) (hVc : IsPreconnected V)
    (hA : A ⊆ V) (hB : B ⊆ V) (ξ : ℝ) :
    Measurable fun φ : C(Rd d, ℝ) => lfppSetDist ξ φ V A B :=
  measurable_lfppSetDist (H := fun z (φ : C(Rd d, ℝ)) => φ z) (fun φ => φ.continuous)
    (fun z => (continuous_eval_const z).measurable) hV hVc hA hB ξ

theorem measurable_acrossDist_continuousMap (ξ : ℝ) (c : Rd d) (r₁ r₂ : ℝ) :
    Measurable fun φ : C(Rd d, ℝ) => acrossDist ξ φ c r₁ r₂ :=
  measurable_acrossDist (H := fun z (φ : C(Rd d, ℝ)) => φ z) (fun φ => φ.continuous)
    (fun z => (continuous_eval_const z).measurable) ξ c r₁ r₂

theorem measurable_lfppDiam_continuousMap (hV : IsOpen V) (hVc : IsPreconnected V) (hU : U ⊆ V)
    (ξ : ℝ) : Measurable fun φ : C(Rd d, ℝ) => lfppDiam ξ φ U V :=
  measurable_lfppDiam (H := fun z (φ : C(Rd d, ℝ)) => φ z) (fun φ => φ.continuous)
    (fun z => (continuous_eval_const z).measurable) hV hVc hU ξ

theorem measurable_selfDiam_continuousMap (ξ : ℝ) (c : Rd d) (r : ℝ) :
    Measurable fun φ : C(Rd d, ℝ) => selfDiam ξ φ c r :=
  measurable_selfDiam (H := fun z (φ : C(Rd d, ℝ)) => φ z) (fun φ => φ.continuous)
    (fun z => (continuous_eval_const z).measurable) ξ c r

theorem measurable_lfppMetric_continuousMap (ξ : ℝ) (x y : Rd d) :
    Measurable fun φ : C(Rd d, ℝ) => lfppMetric ξ φ x y :=
  measurable_lfppMetric (H := fun z (φ : C(Rd d, ℝ)) => φ z) (fun φ => φ.continuous)
    (fun z => (continuous_eval_const z).measurable) ξ x y

end ContinuousMap

/-! ## Locality: measurability for the field restricted to a closed box -/

section Locality

variable {Ω : Type*} {H : Rd d → Ω → ℝ}

/-- The σ-algebra generated by the field on `K₁` is contained in the one generated by the field on
`K₂ ⊇ K₁`. -/
theorem comap_restrict_le (H : Rd d → Ω → ℝ) {K₁ K₂ : Set (Rd d)} (h : K₁ ⊆ K₂) :
    MeasurableSpace.comap (fun ω (z : K₁) => H z ω) MeasurableSpace.pi ≤
      MeasurableSpace.comap (fun ω (z : K₂) => H z ω) MeasurableSpace.pi := by
  have hm : Measurable fun (f : K₂ → ℝ) (z : K₁) => f ⟨z, h z.2⟩ :=
    measurable_pi_iff.2 fun z => measurable_pi_apply _
  have he : (fun ω (z : K₁) => H z ω) =
      (fun (f : K₂ → ℝ) (z : K₁) => f ⟨z, h z.2⟩) ∘ fun ω (z : K₂) => H z ω := rfl
  rw [he, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hm.comap_le

/-- **Locality of `selfDiam`** (MA7 D-5.3, Remark 5.4′): `ω ↦ selfDiam(H(·, ω))(B_r(c))` is
measurable for the σ-algebra generated by the field on the closed box `cbox c r` (`r ≥ 0`; only
continuity of the paths is needed). -/
theorem measurable_selfDiam_comap (hc : ∀ ω, Continuous fun z => H z ω) (ξ : ℝ) (c : Rd d)
    {r : ℝ} (hr : 0 ≤ r) :
    Measurable[MeasurableSpace.comap (fun ω (z : cbox c r) => H z ω) MeasurableSpace.pi]
      fun ω => selfDiam ξ (fun z => H z ω) c r := by
  set Y : Ω → cbox c r → ℝ := fun ω z => H z ω with hY
  let mΩ : MeasurableSpace Ω := MeasurableSpace.comap Y MeasurableSpace.pi
  set Ht : Rd d → Ω → ℝ := fun z ω => H (HigherDimLFPP.DGZ.clampBox c r z) ω with hHt
  have hct : ∀ ω, Continuous fun z => Ht z ω := fun ω =>
    (hc ω).comp (HigherDimLFPP.DGZ.continuous_clampBox _ _)
  have hmt : ∀ z, Measurable (Ht z) := fun z =>
    (measurable_pi_apply (⟨HigherDimLFPP.DGZ.clampBox c r z,
      HigherDimLFPP.DGZ.clampBox_mem c hr z⟩ : cbox c r)).comp (comap_measurable Y)
  have heq : (fun ω => selfDiam ξ (fun z => H z ω) c r) =
      fun ω => selfDiam ξ (fun z => Ht z ω) c r := by
    funext ω
    refine selfDiam_congr fun z hz => ?_
    simp only [hHt, HigherDimLFPP.DGZ.clampBox_of_mem
      (HigherDimLFPP.DGZ.obox_subset_cbox c r hz)]
  rw [heq]
  exact measurable_selfDiam hct hmt ξ c r

/-- **Locality of the across distance** (MA7 D-5.3, Remark 5.4′): for `r₂ < r₁`,
`ω ↦ D(across B_{r₁}(c) \ B_{r₂}(c))(H(·, ω))` is measurable for the σ-algebra generated by the
field on the closed outer box `cbox c r₁` (`r₁ ≥ 0`). -/
theorem measurable_acrossDist_comap (hc : ∀ ω, Continuous fun z => H z ω) (ξ : ℝ) (c : Rd d)
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₂ < r₁) :
    Measurable[MeasurableSpace.comap (fun ω (z : cbox c r₁) => H z ω) MeasurableSpace.pi]
      fun ω => acrossDist ξ (fun z => H z ω) c r₁ r₂ := by
  set Y : Ω → cbox c r₁ → ℝ := fun ω z => H z ω with hY
  let mΩ : MeasurableSpace Ω := MeasurableSpace.comap Y MeasurableSpace.pi
  set Ht : Rd d → Ω → ℝ := fun z ω => H (HigherDimLFPP.DGZ.clampBox c r₁ z) ω with hHt
  have hct : ∀ ω, Continuous fun z => Ht z ω := fun ω =>
    (hc ω).comp (HigherDimLFPP.DGZ.continuous_clampBox _ _)
  have hmt : ∀ z, Measurable (Ht z) := fun z =>
    (measurable_pi_apply (⟨HigherDimLFPP.DGZ.clampBox c r₁ z,
      HigherDimLFPP.DGZ.clampBox_mem c hr₁ z⟩ : cbox c r₁)).comp (comap_measurable Y)
  have heq : (fun ω => acrossDist ξ (fun z => H z ω) c r₁ r₂) =
      fun ω => acrossDist ξ (fun z => Ht z ω) c r₁ r₂ := by
    funext ω
    refine acrossDist_congr (hc ω) (hct ω) hr fun z hz => ?_
    simp only [hHt, HigherDimLFPP.DGZ.clampBox_of_mem hz.1]
  rw [heq]
  exact measurable_acrossDist hct hmt ξ c r₁ r₂

end Locality

end HigherDimLQGMetric.DGZ
