/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TwoForceMainRecover

/-!
# Lemma 7.2, ingredient (i): recovering the field from records on the two sides of a pocket

Packet PROVE-LEMMA72B. Specification §7.1, proof of Lemma 7.2 (`source/spec/p193-240.md` L626–L634, pp. 226–227):
"The pair `(Q, h_ψ)` determines `h` off `∂C`. The latter is a subset of the thin union of the two outer simple curves.
To obtain recovery as a measurable statement, let `N = E[h | Q, h_ψ]` as a locally `H^{-ε}` distribution. On every
rational ball disjoint from `∂C`, countable test coordinates of `h` are already recorded, so `N = h` there. Their
difference is supported on `∂C`, and Aux. lemma 12 makes it zero."

PROVE-SEC7-A2 proved the abstract recovery (`Sec7.exists_version_of_recorded_off`) when the record determines `h φ`
for **every** test `φ` whose support avoids the thin set. In Lemma 7.2 the record `(Q, h_ψ)` sees `h` through two
different objects: tests supported in the pocket `C` through the pocket field `h_ψ` (and the chart), tests supported off
`C̄` through the exterior field in `Q`. A test supported off `∂C` splits into these two pieces (`inTest`), but the
split depends on the random pocket, so the record of the sum is not directly a record of a fixed test. This file
proves the recovery from the two one-sided records, by a pathwise argument:

* `contDiff_indicator_of_disjoint_frontier`, **`inTest`**: for an open `C` whose frontier avoids the support of `φ`,
  `1_C φ` is a test function;
* **`apply_eq_zero_of_in_out`**: a distribution that vanishes on the tests supported in `C` and on the tests supported
  off `C̄` vanishes on every test supported off `∂C`;
* **`exists_version_of_recorded_sides`**: the field has a version measurable for the record, if the record determines
  `h φ` on `{supp φ ⊆ C}` and on `{supp φ ∩ C̄ = ∅}` (each for a fixed test `φ`), and `∂C ∩ U` lies in a thin random
  relatively closed set; the agreement of the conditional mean with `h` is first obtained on the countable test family
  of `Sobolev.ThinRange` (`testFam`), simultaneously for almost every sample, then extended pathwise
  (`Sobolev.eq_zero_off_of_testFam` on each side, `apply_eq_zero_of_in_out`), and Aux. lemma 12 removes `∂C`;
* `isAEDeterminedBy_of_recorded_sides`: with the record `σ(R)`, the field is almost surely a Borel function of `R`
  (`LQGMetric.standardBorelSpace_distOn`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal ContDiff

namespace InteractingSLE.Sec7.Lemma72B

open LQGMetric TopologicalSpace Sobolev

/-! ### Splitting a test function along an open set -/

section Split

variable {U : Opens ℂ}

/-- `1_C f` is smooth when `f` is smooth and the frontier of the open set `C` avoids the support of `f`. -/
theorem contDiff_indicator_of_disjoint_frontier {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) {C : Set ℂ} (hC : IsOpen C)
    (hd : Disjoint (tsupport f) (frontier C)) : ContDiff ℝ ∞ (C.indicator f) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ C
  · exact hf.contDiffAt.congr_of_eventuallyEq
      (eventually_of_mem (hC.mem_nhds hx) fun y hy => indicator_of_mem hy f)
  · by_cases hxc : x ∈ closure C
    · have hxf : x ∈ frontier C := ⟨hxc, by rwa [hC.interior_eq]⟩
      have hxt : x ∉ tsupport f := fun h => hd.ne_of_mem h hxf rfl
      have h0 : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxt
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (h0.mono fun y hy => ?_)
      by_cases hy' : y ∈ C
      · rw [indicator_of_mem hy', hy]
        rfl
      · exact indicator_of_notMem hy' f
    · have hev : ∀ᶠ y in 𝓝 x, y ∉ C :=
        eventually_of_mem (isClosed_closure.isOpen_compl.mem_nhds hxc) fun y hy hyC => hy (subset_closure hyC)
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hev.mono fun y hy => indicator_of_notMem hy f)

/-- **The part of a test function in an open set `C`** whose frontier avoids its support: `1_C φ`, a test function. -/
def inTest (φ : TestOn U) {C : Set ℂ} (hC : IsOpen C) (hφ : Disjoint (tsupport φ) (frontier C)) : TestOn U :=
  ⟨C.indicator φ, contDiff_indicator_of_disjoint_frontier φ.contDiff hC hφ,
    φ.hasCompactSupport.mono (by rw [support_indicator]; exact inter_subset_right),
    (closure_mono (by rw [support_indicator]; exact inter_subset_right)).trans φ.tsupport_subset⟩

theorem coe_inTest (φ : TestOn U) {C : Set ℂ} (hC : IsOpen C) (hφ : Disjoint (tsupport φ) (frontier C)) :
    ⇑(inTest φ hC hφ) = C.indicator φ := rfl

theorem tsupport_inTest_subset (φ : TestOn U) {C : Set ℂ} (hC : IsOpen C)
    (hφ : Disjoint (tsupport φ) (frontier C)) : tsupport (inTest φ hC hφ) ⊆ C := by
  intro x hx
  have hx' : x ∈ closure C ∩ tsupport φ := by
    refine (closure_mono ?_).trans (closure_inter_subset_inter_closure _ _) hx
    rw [coe_inTest, support_indicator]
  by_contra hxC
  exact hφ.ne_of_mem hx'.2 ⟨hx'.1, by rwa [hC.interior_eq]⟩ rfl

theorem disjoint_tsupport_sub_inTest (φ : TestOn U) {C : Set ℂ} (hC : IsOpen C)
    (hφ : Disjoint (tsupport φ) (frontier C)) : Disjoint (tsupport (φ - inTest φ hC hφ)) (closure C) := by
  have e : ⇑(φ - inTest φ hC hφ) = Cᶜ.indicator φ := by
    rw [indicator_compl]
    rfl
  have hsub : tsupport (φ - inTest φ hC hφ) ⊆ Cᶜ ∩ tsupport φ := by
    refine (closure_mono ?_).trans ((closure_inter_subset_inter_closure _ _).trans
      (inter_subset_inter_left _ hC.isClosed_compl.closure_subset))
    rw [e, support_indicator]
  refine Set.disjoint_left.2 fun x hx hxc => ?_
  obtain ⟨hxC, hxt⟩ := hsub hx
  exact hφ.ne_of_mem hxt ⟨hxc, by rwa [hC.interior_eq]⟩ rfl

/-- **A distribution vanishing on both sides of `∂C` vanishes off `∂C`.** If `T` vanishes on every test supported in
the open set `C` and on every test supported off `C̄`, it vanishes on every test whose support avoids `∂C`
(split `φ = 1_C φ + 1_{Cᶜ} φ`). -/
theorem apply_eq_zero_of_in_out (T : DistOn U) {C : Set ℂ} (hC : IsOpen C)
    (hin : ∀ ψ : TestOn U, tsupport ψ ⊆ C → T ψ = 0)
    (hout : ∀ ψ : TestOn U, Disjoint (tsupport ψ) (closure C) → T ψ = 0)
    (φ : TestOn U) (hφ : Disjoint (tsupport φ) (frontier C)) : T φ = 0 := by
  have h1 := hin _ (tsupport_inTest_subset φ hC hφ)
  have h2 := hout _ (disjoint_tsupport_sub_inTest φ hC hφ)
  rw [map_sub, h1, sub_zero] at h2
  exact h2

end Split

/-! ### Recovery from the two one-sided records -/

section Recover

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {U : Opens ℂ}

/-- One-sided record of `h φ` on a recorded event containing `{supp φ ⊆ C}` (resp. any event `E φ`). -/
theorem ae_condMean_eq_of_record {𝓡 : MeasurableSpace Ω} (h𝓡 : 𝓡 ≤ mΩ) {h N : Ω → DistOn U}
    (hint : ∀ φ : TestOn U, Integrable (fun o => h o φ) P)
    (hNv : ∀ φ : TestOn U, (fun o => N o φ) =ᵐ[P] P[fun o => h o φ | 𝓡]) {E : TestOn U → Ω → Prop}
    (hrec : ∀ φ : TestOn U, ∃ (S : Set Ω) (g : Ω → ℝ), MeasurableSet[𝓡] S ∧ StronglyMeasurable[𝓡] g ∧
      (∀ᵐ o ∂P, E φ o → o ∈ S) ∧ ∀ᵐ o ∂P, o ∈ S → h o φ = g o) (φ : TestOn U) :
    ∀ᵐ o ∂P, E φ o → N o φ = h o φ := by
  obtain ⟨S, g, hS, hg, hES, hSg⟩ := hrec φ
  have h1 := Sec7.condExp_eq_on_of_eq h𝓡 (hint φ) hS hg hSg
  filter_upwards [hES, hSg, h1, hNv φ] with o e1 e2 e3 e4 hd
  rw [e4, e3 (e1 hd), e2 (e1 hd)]

/-- **Recovery of a field from records on the two sides of a random open set** (proof of Lemma 7.2, pp. 226–227).
Let `h` be a measurable random distribution on `U` with integrable pairings and (SR1), `A` a random relatively closed
subset of `U` with `dim_H (A ∩ K) < 2 − 2ε` on compacts, and `C` a random open set with `∂C ∩ U ⊆ A` almost surely.
Suppose the sub-`σ`-algebra `𝓡` records `h φ` on an `𝓡`-event containing `{supp φ ⊆ C}` and on an `𝓡`-event
containing `{supp φ ∩ C̄ = ∅}`, for every test `φ`. Then `h` has an `𝓡`-measurable version. -/
theorem exists_version_of_recorded_sides {h : Ω → DistOn U} (hh : Measurable h)
    (hint : ∀ φ : TestOn U, Integrable (fun o => h o φ) P) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hSR1 : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h o) ζ ∂P < ⊤)
    {A : Ω → Set ℂ} (hAcl : ∀ᵐ o ∂P, closure (A o) ∩ U ⊆ A o)
    (hdim : ∀ᵐ o ∂P, ∀ K, IsCompact K → K ⊆ U → dimH (A o ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {C : Ω → Set ℂ} (hCo : ∀ o, IsOpen (C o)) (hfr : ∀ᵐ o ∂P, frontier (C o) ∩ U ⊆ A o)
    {𝓡 : MeasurableSpace Ω} (h𝓡 : 𝓡 ≤ mΩ)
    (hin : ∀ φ : TestOn U, ∃ (S : Set Ω) (g : Ω → ℝ), MeasurableSet[𝓡] S ∧
      StronglyMeasurable[𝓡] g ∧ (∀ᵐ o ∂P, tsupport φ ⊆ C o → o ∈ S) ∧ ∀ᵐ o ∂P, o ∈ S → h o φ = g o)
    (hout : ∀ φ : TestOn U, ∃ (S : Set Ω) (g : Ω → ℝ), MeasurableSet[𝓡] S ∧
      StronglyMeasurable[𝓡] g ∧ (∀ᵐ o ∂P, Disjoint (tsupport φ) (closure (C o)) → o ∈ S) ∧
      ∀ᵐ o ∂P, o ∈ S → h o φ = g o) :
    ∃ N : Ω → DistOn U, Measurable[𝓡] N ∧ ∀ᵐ o ∂P, h o = N o := by
  classical
  have hcut : ∀ k, ∃ ζ : TestOn U, EqOn ζ 1 (exhaustK U k) := fun k => by
    obtain ⟨ζ, -, h1⟩ := exists_cutoff_testOn (exhaustK U k).isCompact (exhaustK_subset U k)
    exact ⟨ζ, h1⟩
  choose ζ hζ using hcut
  obtain ⟨N, hNm, hNv, hNr⟩ := exists_condMean_version hh h𝓡 hint hε0 hε1 hSR1
  have hhr : ∀ᵐ o ∂P, ∀ k, negSobolevSq ε (h o) (ζ k) < ⊤ := by
    refine ae_all_iff.2 fun k => ?_
    have hm : @Measurable Ω ℝ≥0∞ mΩ _ (fun o => negSobolevSq ε (h o) (ζ k)) :=
      (measurable_negSobolevSq ε (ζ k)).comp hh
    exact ae_lt_top' (@Measurable.aemeasurable Ω ℝ≥0∞ mΩ _ _ P hm) (hSR1 (ζ k)).ne
  have hI : ∀ᵐ o ∂P, ∀ i : TestIdx U, tsupport (testFam i) ⊆ C o → N o (testFam i) = h o (testFam i) :=
    ae_all_iff.2 fun i => ae_condMean_eq_of_record (E := fun φ o => tsupport φ ⊆ C o) h𝓡 hint hNv hin _
  have hO : ∀ᵐ o ∂P, ∀ i : TestIdx U, Disjoint (tsupport (testFam i)) (closure (C o)) →
      N o (testFam i) = h o (testFam i) :=
    ae_all_iff.2 fun i => ae_condMean_eq_of_record (E := fun φ o => Disjoint (tsupport φ) (closure (C o))) h𝓡
      hint hNv hout _
  have hoff : ∀ φ : TestOn U, ∀ᵐ o ∂P, Disjoint (tsupport φ) (A o) → N o φ = h o φ := fun φ => by
    filter_upwards [hI, hO, hfr] with o hIo hOo hfro hd
    have hin' : ∀ ψ : TestOn U, tsupport ψ ⊆ C o → (N o - h o) ψ = 0 := by
      intro ψ hψ
      refine eq_zero_off_of_testFam (A := (U : Set ℂ) \ C o) ?_ (fun i hi => ?_) ψ ?_
      · rintro x ⟨hx, hxU⟩
        refine ⟨hxU, fun hxC => ?_⟩
        have : x ∈ closure (C o)ᶜ := closure_mono (fun y hy => hy.2) hx
        rw [(hCo o).isClosed_compl.closure_eq] at this
        exact this hxC
      · have hsub : (ratUnion i.1.1 : Set ℂ) ⊆ C o := fun x hx => by
          by_contra hxC
          exact hi.ne_of_mem hx ⟨i.1.2 hx, hxC⟩ rfl
        rw [sub_apply, hIo i ((tsupport_testFam_subset i).trans hsub), sub_self]
      · exact Set.disjoint_left.2 fun x hx hx' => hx'.2 (hψ hx)
    have hout' : ∀ ψ : TestOn U, Disjoint (tsupport ψ) (closure (C o)) → (N o - h o) ψ = 0 := by
      intro ψ hψ
      refine eq_zero_off_of_testFam (A := closure (C o) ∩ U) ?_ (fun i hi => ?_) ψ ?_
      · rintro x ⟨hx, hxU⟩
        exact ⟨(closure_mono inter_subset_left).trans isClosed_closure.closure_subset hx, hxU⟩
      · have hd' : Disjoint (tsupport (testFam i)) (closure (C o)) := by
          refine Set.disjoint_left.2 fun x hx hxc => ?_
          have hx' := tsupport_testFam_subset i hx
          exact hi.ne_of_mem hx' ⟨hxc, i.1.2 hx'⟩ rfl
        rw [sub_apply, hOo i hd', sub_self]
      · exact Set.disjoint_left.2 fun x hx hx' => hψ.ne_of_mem hx hx'.1 rfl
    have hfφ : Disjoint (tsupport φ) (frontier (C o)) := Set.disjoint_left.2 fun x hx hxf =>
      hd.ne_of_mem hx (hfro ⟨hxf, φ.tsupport_subset hx⟩) rfl
    have := apply_eq_zero_of_in_out (N o - h o) (hCo o) hin' hout' φ hfφ
    rwa [sub_apply, sub_eq_zero] at this
  let _ : MeasurableSpace Ω := mΩ
  refine ⟨N, hNm, ?_⟩
  filter_upwards [ae_eq_of_ae_eq_off hε0 hε1 hζ (ae_all_iff.2 fun k => hNr (ζ k)) hhr hAcl hdim hoff]
    with o ho
  exact ho.symm

/-- **Recovery, determined form.** Under the hypotheses of `exists_version_of_recorded_sides` with the record
`σ(R)`, the field is almost surely a Borel function of `R`. -/
theorem isAEDeterminedBy_of_recorded_sides {γ : Type*} [mγ : MeasurableSpace γ] {R : Ω → γ} (hR : Measurable R)
    {h : Ω → DistOn U} (hh : Measurable h)
    (hint : ∀ φ : TestOn U, Integrable (fun o => h o φ) P) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hSR1 : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h o) ζ ∂P < ⊤)
    {A : Ω → Set ℂ} (hAcl : ∀ᵐ o ∂P, closure (A o) ∩ U ⊆ A o)
    (hdim : ∀ᵐ o ∂P, ∀ K, IsCompact K → K ⊆ U → dimH (A o ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {C : Ω → Set ℂ} (hCo : ∀ o, IsOpen (C o)) (hfr : ∀ᵐ o ∂P, frontier (C o) ∩ U ⊆ A o)
    (hin : ∀ φ : TestOn U, ∃ (S : Set Ω) (g : Ω → ℝ), MeasurableSet[mγ.comap R] S ∧
      StronglyMeasurable[mγ.comap R] g ∧ (∀ᵐ o ∂P, tsupport φ ⊆ C o → o ∈ S) ∧ ∀ᵐ o ∂P, o ∈ S → h o φ = g o)
    (hout : ∀ φ : TestOn U, ∃ (S : Set Ω) (g : Ω → ℝ), MeasurableSet[mγ.comap R] S ∧
      StronglyMeasurable[mγ.comap R] g ∧ (∀ᵐ o ∂P, Disjoint (tsupport φ) (closure (C o)) → o ∈ S) ∧
      ∀ᵐ o ∂P, o ∈ S → h o φ = g o) :
    Sec7.IsAEDeterminedBy P R h := by
  obtain ⟨N, hNm, hhN⟩ :=
    exists_version_of_recorded_sides hh hint hε0 hε1 hSR1 hAcl hdim hCo hfr hR.comap_le hin hout
  obtain ⟨g, hg, hgN⟩ := hNm.exists_eq_measurable_comp
  refine ⟨g, hg, ?_⟩
  filter_upwards [hhN] with o ho
  rw [ho]
  exact congrFun hgN o

end Recover

end InteractingSLE.Sec7.Lemma72B
