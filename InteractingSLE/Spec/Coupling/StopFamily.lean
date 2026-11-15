import InteractingSLE.Spec.Coupling.StopLemma311
import LQGMetric.Field.ZeroBoundary

/-!
# From a countable family of safe stops to every stopping time

Packet PROVE-T11-L312, Theorem 1.1 by the route of ruling R35 (`source/external/AstraIG1/ig1_formalization_proofs.pdf`
§1, "Arbitrary stopping times and locality"). Suppose a random field `h` on `ℍ` is coupled with the evolution so that,
for each member `(U_i, s_i)` of a countable family of stops (`s_i < ζ`, `U_i` unswallowed at `s_i`), conditionally on
`𝓕_{s_i}` its restriction to `U_i` has the protected kernel law: `∫_A exp(i (h, ψ)) = ∫_A exp(i (𝔥_{s_i}, ψ) − E_{s_i}(ψ)/2)`
for `A ∈ 𝓕_{s_i}`, `supp ψ ⊆ U_i` (`IsSampledAt`). If the family exhausts avoidance (every compact `K ⊆ ℍ ∖ K_t`,
`t < ζ`, lies in some `U_i` with `t ≤ s_i`), then the same identity holds at every stopping time `τ < ζ`, on every
`A ∈ 𝓕_τ` contained in the avoidance event `{supp ψ ∩ K_τ = ∅}`.

Proof: cut `A` into the pieces `A ∩ {τ ≤ s_i}` (disjointed); on such a piece, `τ = τ ∧ s_i`, the piece belongs to
`𝓕_{τ ∧ s_i} ⊆ 𝓕_{s_i}`, and optional stopping between `τ ∧ s_i ≤ s_i` (`setIntegral_cfAt_eq_of_le`) moves the
identity from `s_i` to `τ`. No right-continuity argument at rational times is needed.

## Main results

* `aestronglyMeasurable_cfAt_of_stoppingTime`: measurability of `cfAt τ` at a stopping time `τ < ζ ∧ τ_{supp ψ}`;
* `IsSampledAt`: the protected-kernel constraint of a field at one member of the family;
* **`setIntegral_cexp_eq_cfAt_of_family`**: the identity at every stopping time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

section Main

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
include hE hκ hu

/-- **`cfAt τ` is almost everywhere strongly measurable** at a stopping time `τ` of the usual augmentation with
`τ < ζ` and `supp ψ ∩ K_τ = ∅` almost surely (an almost everywhere limit of its values at the safe stops below
`τ ∧ n`). -/
theorem aestronglyMeasurable_cfAt_of_stoppingTime (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0))
    (hτs : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω))) (θ : ℝ) :
    AEStronglyMeasurable (cfAt κ W u ψ θ τ) P := by
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hE' : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ :=
    isIntegratedSLEEvolution_usualAugmentation hE
  have hnull : nullAugmented 𝓖 P = 𝓖 := nullAugmented_usualAugmentation 𝓕 P
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact (tsupport (ψ : ℂ → ℝ)) := ψ.hasCompactSupport.isCompact
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact hK hKH
  set σ₀ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ ω) n with hσ₀_def
  have hσ₀ : ∀ n : ℕ, IsStoppingTime 𝓖 fun ω => (σ₀ n ω : WithTop ℝ≥0) := fun n => by
    have h := hτ.min_const (n : ℝ≥0)
    convert h using 2 with ω
    simp only [hσ₀_def, WithTop.coe_min]
  have hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω := fun n => by
    filter_upwards [hτs] with ω h
    exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) h.1
  obtain ⟨ρ, hρst, hρle, -, hρsafe, hρex⟩ := exists_safeSeq_of_seq hE hK hKH hm hKm hσ₀
    (fun ω n n' h => min_le_min le_rfl (by exact_mod_cast h)) hσ₀ζ
  have hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ρ n ω = τ ω := by
    filter_upwards [hρex, hτs] with ω hex hτω
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (τ ω : ℝ) ≤ j := exists_nat_ge _
    have hτj : τ ω ≤ σ₀ j ω := le_min le_rfl (by exact_mod_cast hj)
    have halive : ∀ z ∈ tsupport (ψ : ℂ → ℝ), ∃ v, IsForwardSol (rpath (W · ω)) z (τ ω) v :=
      fun z hz => exists_isForwardSol_of_mem (τ ω).coe_nonneg
        ⟨hKH hz, fun h => hτω.2.ne_of_mem hz h rfl⟩
    filter_upwards [hex j (τ ω) hτj halive] with n hn
    exact le_antisymm ((hρle n ω).trans (min_le_left _ _)) hn
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (cfAt κ W u ψ θ (ρ n)) P := fun n => by
    have hb : IsStoppingTime (nullAugmented 𝓖 P) fun ω => (ρ n ω : WithTop ℝ≥0) := by
      rw [hnull]; exact hρst n
    have hbs : ∀ᵐ ω ∂P, IsTestSafe W ζ ψ (ρ n) (m / ((n : ℝ) + 1)) n ω := by
      filter_upwards [hρsafe n] with ω h; exact ⟨h.1, h.2.2.1, h.2.2.2⟩
    exact aestronglyMeasurable_cfAt_of_safe hE' hκ u hu hb hbs hKH ψ.continuous ψ.hasCompactSupport
      (by positivity) θ
  refine aestronglyMeasurable_of_tendsto_ae atTop hmeas ?_
  filter_upwards [hev] with ω hω
  exact tendsto_const_nhds.congr' (hω.mono fun n hn => cfAt_congr u θ hn.symm)

end Main

/-- **The protected-kernel constraint at a stop** (Astra §1, (1.10)): conditionally on `𝓖_s`, the field `h` tested
against every `ψ` supported in `U` has characteristic function `exp(i (𝔥_s, ψ) − E_s(ψ)/2)`, in integrated form:
`∫_A exp(i (h, ψ)) = ∫_A exp(i (𝔥_s, ψ) − E_s(ψ)/2)` for `A ∈ 𝓖_s`. -/
def IsSampledAt (κ : ℝ) (W : ℝ≥0 → Ω → ℝ) (u : Ω → ℝ≥0 → ℂ → ℝ) (P : Measure Ω)
    {𝓖 : Filtration ℝ≥0 mΩ} (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (U : Set ℂ)
    {s : Ω → ℝ≥0} (hs : IsStoppingTime 𝓖 fun ω => (s ω : WithTop ℝ≥0)) : Prop :=
  ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U → ∀ A : Set Ω,
    MeasurableSet[hs.measurableSpace] A →
      ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P = ∫ ω in A, cfAt κ W u ψ 1 s ω ∂P

theorem cexp_mul_one (x : ℝ) : Complex.exp (Complex.I * (x : ℂ)) = Complex.exp (Complex.I * (1 : ℝ) * x) := by
  push_cast; ring_nf

/-- **The constraint at every stopping time** (Astra §1, "Arbitrary stopping times"). Let `(U_i, s_i)`, `i ∈ ι`
countable, be stops of the usual augmentation with `s_i < ζ` and `U_i ∩ K_{s_i} = ∅` almost surely, at each of which
the field satisfies `IsSampledAt`, and which exhaust avoidance: almost surely, for every `t < ζ` and compact
`K ⊆ ℍ ∖ K_t` there is `i` with `K ⊆ U_i` and `t ≤ s_i`. Then for every stopping time `τ < ζ` of the usual
augmentation, every test function `ψ` and every `A ∈ 𝓖_τ` inside `{supp ψ ∩ K_τ = ∅}`,
`∫_A exp(i (h, ψ)) = ∫_A exp(i (𝔥_τ, ψ) − E_τ(ψ)/2)`. -/
theorem setIntegral_cexp_eq_cfAt_of_family
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    {ι : Type*} [Countable ι] (U : ι → Set ℂ) (s : ι → Ω → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s i ω : WithTop ℝ≥0))
    (hsafe : ∀ i, ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)))
    (hsamp : ∀ i, IsSampledAt κ W u P h (U i) (hs i))
    (hexh : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K ⊆ U i ∧ t ≤ s i ω)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0))
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (τ ω))}) :
    ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P = ∫ ω in A, cfAt κ W u ψ 1 τ ω ∂P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hpath := hE.2.2.2.2
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact (tsupport (ψ : ℂ → ℝ)) := ψ.hasCompactSupport.isCompact
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  -- the stops at which `ψ` is admissible
  set C : ι → Set Ω := fun i => if tsupport (ψ : ℂ → ℝ) ⊆ U i then A ∩ {ω | τ ω ≤ s i ω} else ∅
    with hC_def
  have hCτ : ∀ i, MeasurableSet[hτ.measurableSpace] (C i) := fun i => by
    by_cases hi : tsupport (ψ : ℂ → ℝ) ⊆ U i
    · simp only [hC_def, hi, ↓reduceIte]
      have h1 := hτ.measurableSet_le_stopping_time (hs i)
      simp only [WithTop.coe_le_coe] at h1
      exact @MeasurableSet.inter Ω hτ.measurableSpace _ _ hA h1
    · simp only [hC_def, hi, ↓reduceIte]; exact @MeasurableSet.empty Ω hτ.measurableSpace
  -- on each piece the identity holds
  have hpiece : ∀ i, ∀ D : Set Ω, MeasurableSet[hτ.measurableSpace] D → D ⊆ C i →
      ∫ ω in D, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P = ∫ ω in D, cfAt κ W u ψ 1 τ ω ∂P := by
    intro i D hD hDC
    by_cases hi : tsupport (ψ : ℂ → ℝ) ⊆ U i
    swap
    · have hD0 : D = ∅ := by
        refine Set.subset_empty_iff.1 (hDC.trans ?_)
        simp only [hC_def, hi, ↓reduceIte, subset_refl]
      simp [hD0]
    have hDC' : D ⊆ A ∩ {ω | τ ω ≤ s i ω} := by
      simpa only [hC_def, hi, ↓reduceIte] using hDC
    have hmin : IsStoppingTime 𝓖 fun ω => ((min (τ ω) (s i ω) : ℝ≥0) : WithTop ℝ≥0) := by
      rw [coe_min_fun]; exact hτ.min (hs i)
    have hDmin : MeasurableSet[hmin.measurableSpace] D := by
      have h1 := hτ.measurableSet_inter_le (hs i) D hD
      simp only [WithTop.coe_le_coe] at h1
      have h2 : D ∩ {ω | τ ω ≤ s i ω} = D := inter_eq_left.2 fun ω hω => (hDC' hω).2
      rw [h2] at h1
      exact measurableSet_stopping_congr rfl (coe_min_fun τ (s i)).symm _ hmin h1
    have hDs : MeasurableSet[(hs i).measurableSpace] D :=
      hmin.measurableSpace_mono (hs i) (fun ω => WithTop.coe_le_coe.2 (min_le_right (τ ω) (s i ω)))
        _ hDmin
    have hsψ : ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)) := by
      filter_upwards [hsafe i] with ω hω using ⟨hω.1, hω.2.mono_left hi⟩
    have e1 := hsamp i ψ hi D hDs
    have e2 := setIntegral_cfAt_eq_of_le hE hκ u hu ψ hmin (hs i) (fun ω => min_le_right _ _) hsψ
      hDmin 1
    rw [e1, e2]
    exact setIntegral_congr_fun (hτ.measurableSpace_le _ hD) fun ω hω =>
      cfAt_congr u 1 (min_eq_left (hDC' hω).2)
  -- enumerate the pieces and cut them disjoint
  let _ : Encodable ι := Encodable.ofCountable ι
  set C' : ℕ → Set Ω := fun n => ⋃ b ∈ Encodable.decode₂ ι n, C b with hC'_def
  have hC'τ : ∀ n, MeasurableSet[hτ.measurableSpace] (C' n) := fun n => by
    simp only [hC'_def]
    cases Encodable.decode₂ ι n with
    | none => simp
    | some b => simpa using hCτ b
  have hpiece' : ∀ n, ∀ D : Set Ω, MeasurableSet[hτ.measurableSpace] D → D ⊆ C' n →
      ∫ ω in D, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P = ∫ ω in D, cfAt κ W u ψ 1 τ ω ∂P := by
    intro n D hD hDC
    simp only [hC'_def] at hDC
    cases hb : Encodable.decode₂ ι n with
    | none =>
      have hD0 : D = ∅ := by
        refine Set.subset_empty_iff.1 (hDC.trans ?_)
        simp [hb]
      simp [hD0]
    | some b => exact hpiece b D hD (by simpa [hb] using hDC)
  set D : ℕ → Set Ω := disjointed C' with hD_def
  have hDτ : ∀ n, MeasurableSet[hτ.measurableSpace] (D n) := fun n =>
    @MeasurableSet.disjointed Ω hτ.measurableSpace C' hC'τ n
  have hDm : ∀ n, MeasurableSet (D n) := fun n => hτ.measurableSpace_le _ (hDτ n)
  have hUnion : ⋃ n, D n = ⋃ i, C i := by
    rw [hD_def, iUnion_disjointed, hC'_def, Encodable.iUnion_decode₂]
  have hCA : ⋃ i, C i ⊆ A := iUnion_subset fun i => by
    by_cases hi : tsupport (ψ : ℂ → ℝ) ⊆ U i
    · simp only [hC_def, hi, ↓reduceIte]; exact inter_subset_left
    · simp only [hC_def, hi, ↓reduceIte]; exact empty_subset _
  have hAU : A =ᵐ[P] (⋃ n, D n : Set Ω) := by
    rw [hUnion]
    refine (ae_eq_set.2 ⟨?_, ?_⟩)
    · refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hexh.and hτζ))
      obtain ⟨hωA, hωC⟩ := hω
      intro hgood
      obtain ⟨i, hi, hle⟩ := hgood.1 (τ ω) hgood.2 _ hK hKH (hAE hωA)
      exact hωC (mem_iUnion.2 ⟨i, by simp only [hC_def, hi, ↓reduceIte]; exact ⟨hωA, hle⟩⟩)
    · rw [sdiff_eq_empty.2 hCA, measure_empty]
  -- integrability
  have hint1 : Integrable (fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ))) P := by
    refine Integrable.of_bound (((by fun_prop : Measurable fun x : ℝ => Complex.exp (Complex.I * x)).comp
      (hh ψ)).aestronglyMeasurable) 1 (Eventually.of_forall fun ω => ?_)
    simp [Complex.norm_exp]
  have hbound : ∀ᵐ ω ∂P.restrict A, ‖cfAt κ W u ψ 1 τ ω‖ ≤ 1 := by
    refine (ae_restrict_iff' hAm).2 ?_
    filter_upwards [hτζ, hpath] with ω hω hP hωA
    exact norm_cfAt_le_one u 1 ψ (continuousOn_rpath hP.2.2.2.1 hω) hP.1 fun z hz =>
      exists_isForwardSol_of_mem (τ ω).coe_nonneg ⟨hKH hz, fun h' => (hAE hωA).ne_of_mem hz h' rfl⟩
  have hmeasD : ∀ n, AEStronglyMeasurable (cfAt κ W u ψ 1 τ) (P.restrict (D n)) := by
    intro n
    have hDC : D n ⊆ C' n := disjointed_subset C' n
    simp only [hC'_def] at hDC
    cases hb : Encodable.decode₂ ι n with
    | none =>
      have hD0 : D n = ∅ := by
        refine Set.subset_empty_iff.1 (hDC.trans ?_)
        simp [hb]
      rw [hD0, Measure.restrict_empty]; exact aestronglyMeasurable_zero_measure _
    | some b =>
      have hDC' : D n ⊆ C b := by simpa [hb] using hDC
      by_cases hi : tsupport (ψ : ℂ → ℝ) ⊆ U b
      swap
      · have hD0 : D n = ∅ := by
          refine Set.subset_empty_iff.1 (hDC'.trans ?_)
          simp only [hC_def, hi, ↓reduceIte, subset_refl]
        rw [hD0, Measure.restrict_empty]; exact aestronglyMeasurable_zero_measure _
      have hDC'' : D n ⊆ A ∩ {ω | τ ω ≤ s b ω} := by
        simpa only [hC_def, hi, ↓reduceIte] using hDC'
      have hmin : IsStoppingTime 𝓖 fun ω => ((min (τ ω) (s b ω) : ℝ≥0) : WithTop ℝ≥0) := by
        rw [coe_min_fun]; exact hτ.min (hs b)
      have hms : ∀ᵐ ω ∂P, ((min (τ ω) (s b ω) : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
          Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (min (τ ω) (s b ω))) := by
        filter_upwards [hsafe b] with ω hω
        refine ⟨lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hω.1, ?_⟩
        refine (hω.2.mono_left hi).mono_right ?_
        exact (fwdHull_mono (W := fun r : ℝ => W r.toNNReal ω)).1
          (by exact_mod_cast min_le_right (τ ω) (s b ω))
      refine (aestronglyMeasurable_cfAt_of_stoppingTime hE hκ u hu ψ hmin hms 1).restrict.congr ?_
      refine (ae_restrict_iff' (hDm n)).2 (Eventually.of_forall fun ω hω => ?_)
      exact cfAt_congr u 1 (min_eq_left (hDC'' hω).2)
  have hint2 : IntegrableOn (cfAt κ W u ψ 1 τ) (⋃ n, D n) P := by
    have hm : AEStronglyMeasurable (cfAt κ W u ψ 1 τ) (P.restrict (⋃ n, D n)) :=
      aestronglyMeasurable_iUnion_iff.2 hmeasD
    refine Integrable.of_bound hm 1 ?_
    rw [← Measure.restrict_congr_set hAU]
    exact hbound
  rw [setIntegral_congr_set hAU, setIntegral_congr_set hAU,
    integral_iUnion hDm (disjoint_disjointed C') hint1.integrableOn,
    integral_iUnion hDm (disjoint_disjointed C') hint2]
  exact tsum_congr fun n => hpiece' n (D n) (hDτ n) (disjointed_subset C' n)

end Coupling

end InteractingSLE
