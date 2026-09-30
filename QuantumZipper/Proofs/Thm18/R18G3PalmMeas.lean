import QuantumZipper.Proofs.Thm18.R18G3Defs
import QuantumZipper.Proofs.Thm18.G1ZB2RMain
import QuantumZipper.Proofs.Thm18.G2FixMixRoot
import QuantumZipper.Proofs.Thm18.G2FixMixRootR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 3 (1): pair tools for the joint Palm average

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71, Figure 1.7) and proof of Proposition 1.7 (pp. 25–26).

Pair versions of the tools of `G1ZB2RMeas.lean`:

* `g3_pair_map_eq`: two a.e.-measurable pairs of coordinate families with the same integrals of
  all products `Θ₁(truncated first) * Θ₂(truncated second)` have the same joint law (π-λ over
  the truncation radii, `E6.ext_of_monotone_generating`, and rectangles generate the product
  σ-algebra at each radius);
* `measurable_g3LenL`, `measurable_g3PartnerPt`: the left quantum length `b ↦ ν[b, 0]` and the
  length partner on the right side are Borel;
* `g3LenL_g1SidePt`: the quantile identity `ν[lenLeft ℓ, 0] = ℓ` (B0 regularity).

Own elementary bookkeeping (as the single-side originals).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm D3Plus CoordsFull

/-- The truncation of a pair of coordinate sequences. -/
def g3Trunc2 (R : ℕ) : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
  Prod.map (g1zTrunc R) (g1zTrunc R)

theorem measurable_g3Trunc2 (R : ℕ) : Measurable (g3Trunc2 R) :=
  (measurable_g1zTrunc R).prodMap (measurable_g1zTrunc R)

theorem g1zTrunc_comp_of_le {R R' : ℕ} (h : R ≤ R') :
    g1zTrunc R = g1zTrunc R ∘ g1zTrunc R' := by
  classical
  funext c i
  by_cases hi : inBallFull R i
  · simp [g1zTrunc, hi, inBallFull_mono h hi]
  · simp [g1zTrunc, hi]

/-- **Joint law of pairs of coordinates from local product integrals** (π-λ). -/
theorem g3_pair_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ ξ' : Ω → (ℕ → ℝ) × (ℕ → ℝ)} (hξ : AEMeasurable ξ P) (hξ' : AEMeasurable ξ' P)
    (hloc : ∀ R : ℕ, ∀ Γ₁ Γ₂ : (ℕ → ℝ) → ℝ≥0∞, Measurable Γ₁ → Measurable Γ₂ →
      (∀ c, Γ₁ c ≤ 1) → (∀ c, Γ₂ c ≤ 1) →
      ∫⁻ ω, Γ₁ (g1zTrunc R (ξ ω).1) * Γ₂ (g1zTrunc R (ξ ω).2) ∂P =
        ∫⁻ ω, Γ₁ (g1zTrunc R (ξ' ω).1) * Γ₂ (g1zTrunc R (ξ' ω).2) ∂P) :
    P.map ξ = P.map ξ' := by
  classical
  have : IsProbabilityMeasure (P.map ξ) := (Measure.isProbabilityMeasure_map_iff hξ).2 inferInstance
  have : IsProbabilityMeasure (P.map ξ') :=
    (Measure.isProbabilityMeasure_map_iff hξ').2 inferInstance
  refine E6.ext_of_monotone_generating g3Trunc2 measurable_g3Trunc2 ?_ ?_
    _ _ (by simp) fun R => ?_
  · intro R R' hRR'
    have e : g3Trunc2 R = g3Trunc2 R ∘ g3Trunc2 R' := by
      unfold g3Trunc2
      rw [Prod.map_comp_map, ← g1zTrunc_comp_of_le hRR']
    show MeasurableSpace.comap (g3Trunc2 R) _ ≤ MeasurableSpace.comap (g3Trunc2 R') _
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_g3Trunc2 R).comap_le
  · have hgen1 : ∀ f : (ℕ → ℝ) × (ℕ → ℝ) → ℕ → ℝ, Measurable f →
        (∀ R i, inBallFull R i → (fun p => f p i) = (fun q => f q i) ∘ g3Trunc2 R) →
        MeasurableSpace.comap f MeasurableSpace.pi ≤
          ⨆ R, MeasurableSpace.comap (g3Trunc2 R) inferInstance := by
      intro f hfm hf
      show MeasurableSpace.comap f (⨆ i, MeasurableSpace.comap (fun c : ℕ → ℝ => c i)
        inferInstance) ≤ _
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun i => ?_
      obtain ⟨R, hi⟩ := exists_inBallFull i
      rw [MeasurableSpace.comap_comp]
      change MeasurableSpace.comap (fun p => f p i) inferInstance ≤ _
      rw [hf R i hi, ← MeasurableSpace.comap_comp]
      exact (MeasurableSpace.comap_mono ((measurable_pi_apply i).comp hfm).comap_le).trans
        (le_iSup (fun R => MeasurableSpace.comap (g3Trunc2 R) inferInstance) R)
    show MeasurableSpace.comap Prod.fst MeasurableSpace.pi ⊔
      MeasurableSpace.comap Prod.snd MeasurableSpace.pi ≤ _
    refine sup_le (hgen1 Prod.fst measurable_fst fun R i hi => ?_)
      (hgen1 Prod.snd measurable_snd fun R i hi => ?_)
    · funext p; simp [g3Trunc2, g1zTrunc, hi]
    · funext p; simp [g3Trunc2, g1zTrunc, hi]
  · have key : ∀ (ζ : Ω → (ℕ → ℝ) × (ℕ → ℝ)), AEMeasurable ζ P → ∀ A B : Set (ℕ → ℝ),
        MeasurableSet A → MeasurableSet B →
        ((P.map ζ).map (g3Trunc2 R)) (A ×ˢ B) = ∫⁻ ω, A.indicator 1 (g1zTrunc R (ζ ω).1) *
          B.indicator 1 (g1zTrunc R (ζ ω).2) ∂P := by
      intro ζ hζ A B hA hB
      rw [AEMeasurable.map_map_of_aemeasurable (measurable_g3Trunc2 R).aemeasurable hζ,
        ← lintegral_indicator_one (hA.prod hB),
        lintegral_map' (measurable_one.indicator (hA.prod hB)).aemeasurable
          ((measurable_g3Trunc2 R).comp_aemeasurable hζ)]
      refine lintegral_congr fun ω => ?_
      simp only [Function.comp_apply, g3Trunc2]
      exact Set.indicator_prod_one
    have hrect : ∀ s ∈ image2 (· ×ˢ ·) {s : Set (ℕ → ℝ) | MeasurableSet s}
        {t : Set (ℕ → ℝ) | MeasurableSet t},
        ((P.map ξ).map (g3Trunc2 R)) s = ((P.map ξ').map (g3Trunc2 R)) s := by
      rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [key ξ hξ A B hA hB, key ξ' hξ' A B hA hB]
      refine hloc R (A.indicator 1) (B.indicator 1) (measurable_one.indicator hA)
        (measurable_one.indicator hB) (fun c => ?_) (fun c => ?_)
      · by_cases hc : c ∈ A <;> simp [hc]
      · by_cases hc : c ∈ B <;> simp [hc]
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod hrect ?_
    rw [← univ_prod_univ]
    exact hrect _ ⟨univ, (MeasurableSet.univ : MeasurableSet (univ : Set (ℕ → ℝ))), univ,
      (MeasurableSet.univ : MeasurableSet (univ : Set (ℕ → ℝ))), rfl⟩

/-- The left quantum length `b ↦ ν[b, 0]` is Borel. -/
theorem measurable_g3LenL (γ : ℝ) (x : FieldSample) : Measurable (g3LenL γ x) := by
  have h : Antitone fun b : ℝ => g1SideNu γ true x (Icc b 0) := fun a b hab =>
    measure_mono (Icc_subset_Icc_left hab)
  exact h.measurable.ennreal_toReal

/-- The length partner on the right side of a left point is Borel in the left point. -/
theorem measurable_g3PartnerPt (γ : ℝ) (x y : FieldSample) :
    Measurable fun b : ℝ => g1SidePt γ false y (g3LenL γ x b) :=
  (measurable_lenRight_left (g1SideNu γ false y)).comp (measurable_g3LenL γ x)

/-- **Quantile identity** on the left side: `ν[lenLeft ℓ, 0] = ℓ` for `ℓ ≥ 0` (B0). -/
theorem g3LenL_g1SidePt {γ : ℝ} {x : FieldSample}
    (hreg : (∀ t : ℝ, g1SideNu γ true x {t} = 0) ∧
      (∀ u v : ℝ, u < v → Ioo u v ⊆ g1SideHalf true → 0 < g1SideNu γ true x (Ioo u v)) ∧
      (∀ b ∈ g1SideHalf true, g1SideNu γ true x (g1SideSeg true b) < ⊤) ∧
      g1SideNu γ true x (g1SideHalf true) = ⊤)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : g3LenL γ x (g1SidePt γ true x ℓ) = ℓ := by
  obtain ⟨hat, -, hfin, hinf⟩ := hreg
  set m := g1SideNu γ true x with hm
  have hfin' : ∀ b : ℝ, m (Icc b 0) ≠ ⊤ := by
    intro b
    by_cases hb : b < 0
    · exact (hfin b hb).ne
    · have hsub : Icc b 0 ⊆ {0} := fun y hy =>
        le_antisymm hy.2 ((not_lt.1 hb).trans hy.1)
      exact ne_top_of_le_ne_top ENNReal.zero_ne_top ((measure_mono hsub).trans (hat 0).le)
  obtain ⟨n, hn⟩ := g1_exists_mass_gt (m := m) (S := Iio 0)
    (s := fun n : ℕ => Icc (-((n : ℝ) + 1)) 0)
    (fun a b hab => Icc_subset_Icc_left (by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith))
    (fun y hy => by
      obtain ⟨n, hn⟩ := exists_nat_gt (-y)
      exact mem_iUnion.2 ⟨n, ⟨by linarith, (show y < 0 from hy).le⟩⟩)
    hinf ℓ
  have hq := measure_Icc_lenLeft_eq (m := m) (δ := (n : ℝ) + 1) (ℓ := ℓ) (by positivity) hfin'
    (fun t _ => hat t) hn.le
  show (m (Icc (lenLeft m ℓ) 0)).toReal = ℓ
  rw [hq, ENNReal.toReal_ofReal hℓ]

end R18
end QuantumZipper
