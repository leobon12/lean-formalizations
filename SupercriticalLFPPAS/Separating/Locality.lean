import SupercriticalLQGUniqueness.B2.Polylog.P4Local

/-!
# Locality modulo additive constants: arbitrary centering and Boolean combinations

Packet P35. The events of Lemma 3.5 and of the good root event (§3.3) are finite Boolean
combinations of one-annulus events at many centres and radii. The annulus iteration (1.6)
(`Uniqueness.Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open`) consumes events that
are almost surely events of the restriction to an annulus of the field recentred by a circle
average around the centre of that annulus, while the library's
`B2.Polylog.plEventLoc_centered_local` recentres by a circle average around the event's own centre.

* `p35_aeEventIn_of_canonical`: the Gaussian-smoothing argument of `plEventLoc_centered_local`
  works for every event with a canonical local representative and almost sure invariance under
  adding a constant, and for an **arbitrary** recentring `X : Ω → ℝ` (no measurability needed);
* `p35_plEventLoc_aeEventIn`: hence the one-annulus event `plEventLoc` is almost surely an event of
  `σ((h - X)|_U)` for every open `U ⊇ A_{ρ/2,4ρ}(w)` and every `X`;
* closure of `AEEventIn` under finite intersections, unions, monotonicity of the σ-algebra, and the
  counting events `{b ≤ #{k ∈ [1, N] : ω ∈ E_k}}`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLFPPAS.Separating

open SupercriticalLQGUniqueness
open LQGMetric (DistC DistOn addConst restrictTo)
open LQGMetric.Blueprint (AEEventIn fieldSigma countOcc)

/-- **Locality modulo constants with an arbitrary recentring.** An event `E` of the field which has
a measurable local representative on `U` under the Gaussian-shifted law `muH P h` and which is
almost surely invariant under adding an independent standard Gaussian constant is, almost surely,
an event of the restriction to `U` of `h - X`, for every `X : Ω → ℝ`. Adapted from
`B2.Polylog.plEventLoc_centered_local`, whose proof uses the recentring only through the identity
`localShift U (restrictTo U (h - X)) (X + t) = restrictTo U (h + t)`. -/
theorem p35_aeEventIn_of_canonical {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (E : Set DistC) (U : TopologicalSpace.Opens ℂ)
    (hcanon : ∃ S : Set (DistOn U), MeasurableSet S ∧
      E =ᵐ[Uniqueness.TwoScale.S36.muH P h] restrictTo U ⁻¹' S)
    (hinv : ∀ᵐ y ∂P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian,
      (addConst (h y.1) y.2 ∈ E ↔ h y.1 ∈ E))
    (X : Ω → ℝ) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-X ω)) U) {ω | h ω ∈ E} := by
  let q' : Ω → DistOn U := fun ω => restrictTo U (addConst (h ω) (-X ω))
  obtain ⟨S, hS, hLocal⟩ := hcanon
  have hmeasH := (Uniqueness.BiLipschitz.OneScale.gff_gaussianShift P h hh.1).measurable
  have hLocalProd : {y : Ω × ℝ | Uniqueness.BiLipschitz.OneScale.gaussianShift h y ∈ E}
      =ᵐ[P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian]
      {y : Ω × ℝ | restrictTo U (Uniqueness.BiLipschitz.OneScale.gaussianShift h y) ∈ S} :=
    ae_of_ae_map hmeasH.aemeasurable hLocal
  have hAE : ∀ᵐ y ∂P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian,
      (h y.1 ∈ E ↔ Uniqueness.BiLipschitz.OneScale.localShift U (q' y.1) (X y.1 + y.2) ∈ S) := by
    filter_upwards [hinv, hLocalProd] with y hi hl
    have hShift : Uniqueness.BiLipschitz.OneScale.localShift U (q' y.1) (X y.1 + y.2) =
        restrictTo U (Uniqueness.BiLipschitz.OneScale.gaussianShift h y) := by
      calc Uniqueness.BiLipschitz.OneScale.localShift U (q' y.1) (X y.1 + y.2) =
            restrictTo U (addConst (addConst (h y.1) (-X y.1)) (X y.1 + y.2)) :=
          Uniqueness.BiLipschitz.OneScale.localShift_restrictTo U _ _
        _ = restrictTo U (addConst (h y.1) y.2) := by
          rw [LQGMetric.GFFLaw.addConst_addConst]
          congr 2
          ring
        _ = restrictTo U (Uniqueness.BiLipschitz.OneScale.gaussianShift h y) := rfl
    rw [hShift]
    exact hi.symm.trans (Iff.of_eq hl)
  have hSmooth := Uniqueness.BiLipschitz.OneScale.gaussian_smoothing_event P U q'
    X {ω | h ω ∈ E} S hS hAE
  refine ⟨{ω | Uniqueness.BiLipschitz.OneScale.gaussianSmooth U S (q' ω) > 1 / 2}, ?_, ?_⟩
  · have hB : MeasurableSet {v : DistOn U |
        Uniqueness.BiLipschitz.OneScale.gaussianSmooth U S v > 1 / 2} :=
      measurableSet_lt measurable_const
        (Uniqueness.BiLipschitz.OneScale.measurable_gaussianSmooth U hS)
    exact hB.preimage (Measurable.of_comap_le le_rfl)
  · filter_upwards [hSmooth] with ω hω
    exact propext hω

/-- **Locality of the one-annulus event with an arbitrary recentring.** For `2 ρ_ε < ρ` (with
`ρ_ε = ε (log ε⁻¹)^q`) and any open `U ⊇ A_{ρ/2,4ρ}(w)`, the event `{h ∈ E^ε_ρ(w; C)}` is almost
surely an event of the restriction to `U` of `h - X`, for every `X`. -/
theorem p35_plEventLoc_aeEventIn {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {D : DistC → LSCMetric} {c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    (hD : B2.Iface.IsPfeWeakMetric ξ D c) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : ℝ)
    (w : ℂ) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (ρ : Set.Ioi (0 : ℝ)) (C : ℝ)
    (U : TopologicalSpace.Opens ℂ) (hU : B2.Polylog.eventCarrier w ρ ⊆ U)
    (hρ : 2 * B2.Polylog.plRad q ε < ρ) (X : Ω → ℝ) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-X ω)) U)
      {ω | h ω ∈ B2.Polylog.plEventLoc (ξ : ℝ) D c m q w ε hε ρ C} := by
  refine p35_aeEventIn_of_canonical P h hh _ U
    (B2.Polylog.canonical_plEventLoc_local P h hh hD m q w ε hε ρ C U hU hρ) ?_ X
  have hprodW : LQGMetric.IsWholePlaneGFF (fun y : Ω × ℝ => h y.1)
      (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian) :=
    Uniqueness.BiLipschitz.OneScale.gff_prod_fst P
      Uniqueness.BiLipschitz.OneScale.standardGaussian h hh.1
  have hprod : LQGMetric.IsGFFPlusCont (fun y : Ω × ℝ => h y.1)
      (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian) :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hprodW
  exact B2.Polylog.ae_plEventLoc_addConst_iff
    (P.prod Uniqueness.BiLipschitz.OneScale.standardGaussian)
    (fun y => h y.1) hprod hprodW hD m q w ε hε ρ C (fun y => y.2)

/-! ### Closure properties of `AEEventIn` for field σ-algebras -/

section Closure

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} (σ : Ω → DistC)

theorem p35_aeEventIn_univ (U : TopologicalSpace.Opens ℂ) : AEEventIn P (fieldSigma σ U) univ :=
  ⟨univ, MeasurableSet.univ, Filter.EventuallyEq.rfl⟩

theorem p35_aeEventIn_mono {V W : TopologicalSpace.Opens ℂ} (hVW : V ≤ W) {A : Set Ω}
    (hA : AEEventIn P (fieldSigma σ V) A) : AEEventIn P (fieldSigma σ W) A := by
  obtain ⟨F, hF, hAF⟩ := hA
  exact ⟨F, LQGMetric.GM.fieldSigma_mono σ hVW F hF, hAF⟩

theorem p35_aeEventIn_inter {U : TopologicalSpace.Opens ℂ} {A B : Set Ω}
    (hA : AEEventIn P (fieldSigma σ U) A) (hB : AEEventIn P (fieldSigma σ U) B) :
    AEEventIn P (fieldSigma σ U) (A ∩ B) := by
  obtain ⟨F, hF, hAF⟩ := hA
  obtain ⟨G, hG, hBG⟩ := hB
  exact ⟨F ∩ G, hF.inter hG, hAF.inter hBG⟩

theorem p35_aeEventIn_union {U : TopologicalSpace.Opens ℂ} {A B : Set Ω}
    (hA : AEEventIn P (fieldSigma σ U) A) (hB : AEEventIn P (fieldSigma σ U) B) :
    AEEventIn P (fieldSigma σ U) (A ∪ B) := by
  obtain ⟨F, hF, hAF⟩ := hA
  obtain ⟨G, hG, hBG⟩ := hB
  exact ⟨F ∪ G, hF.union hG, hAF.union hBG⟩

theorem p35_aeEventIn_biInter_finset {ι : Type*} {U : TopologicalSpace.Opens ℂ} (s : Finset ι)
    {A : ι → Set Ω} (hA : ∀ i ∈ s, AEEventIn P (fieldSigma σ U) (A i)) :
    AEEventIn P (fieldSigma σ U) (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using p35_aeEventIn_univ (P := P) σ U
  | insert a s has ih =>
      have hEq : (⋂ i ∈ insert a s, A i) = A a ∩ ⋂ i ∈ s, A i := by
        ext ω
        simp
      rw [hEq]
      exact p35_aeEventIn_inter σ (hA a (Finset.mem_insert_self a s))
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

omit [MeasurableSpace Ω] in
/-- The counting function `countOcc` as a finite sum of indicators. -/
theorem p35_countOcc_eq_sum (E : ℕ → Set Ω) (N : ℕ) (ω : Ω) :
    (countOcc E N ω : ℝ) = ∑ k ∈ Finset.Icc 1 N, (E k).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  unfold countOcc
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : ω ∈ E k <;> simp [hk]

/-- **Counting events.** If each `E_k` (`1 ≤ k ≤ N`) is almost surely an event of the field
σ-algebra, so is `{b ≤ #{k ∈ [1, N] : ω ∈ E_k}}`. -/
theorem p35_aeEventIn_countOcc_ge {U : TopologicalSpace.Opens ℂ} (E : ℕ → Set Ω) (N : ℕ) (b : ℝ)
    (hE : ∀ k, 1 ≤ k → k ≤ N → AEEventIn P (fieldSigma σ U) (E k)) :
    AEEventIn P (fieldSigma σ U) {ω | b ≤ (countOcc E N ω : ℝ)} := by
  classical
  have hE' : ∀ k ∈ Finset.Icc 1 N, AEEventIn P (fieldSigma σ U) (E k) := fun k hk => by
    rw [Finset.mem_Icc] at hk
    exact hE k hk.1 hk.2
  choose F hF hEF using hE'
  let F' : ℕ → Set Ω := fun k => if hk : k ∈ Finset.Icc 1 N then F k hk else univ
  have hF'meas : ∀ k, MeasurableSet[fieldSigma σ U] (F' k) := by
    intro k
    by_cases hk : k ∈ Finset.Icc 1 N
    · simp only [F', hk, dite_true]
      exact hF k hk
    · simp only [F', hk, dite_false]
      exact MeasurableSet.univ
  have hae : ∀ᵐ ω ∂P, ∀ k ∈ Finset.Icc 1 N, (ω ∈ E k ↔ ω ∈ F' k) := by
    rw [Filter.eventually_all_finset]
    intro k hk
    filter_upwards [hEF k hk] with ω hω
    simp only [F', hk, dite_true]
    exact Iff.of_eq hω
  refine ⟨{ω | b ≤ (countOcc F' N ω : ℝ)}, ?_, ?_⟩
  · have hmeas : Measurable[fieldSigma σ U] fun ω => (countOcc F' N ω : ℝ) := by
      have : (fun ω => (countOcc F' N ω : ℝ)) =
          fun ω => ∑ k ∈ Finset.Icc 1 N, (F' k).indicator (fun _ => (1 : ℝ)) ω := by
        funext ω
        exact p35_countOcc_eq_sum F' N ω
      rw [this]
      exact Finset.measurable_sum _ fun k _ => (measurable_const.indicator (hF'meas k))
    exact measurableSet_le measurable_const hmeas
  · filter_upwards [hae] with ω hω
    have hcount : countOcc E N ω = countOcc F' N ω := by
      unfold countOcc
      congr 1
      exact Finset.filter_congr fun k hk => hω k hk
    simp only [hcount]

end Closure

end SupercriticalLFPPAS.Separating
