import QuantumZipper.Proofs.Zipper.Cor15LawB1
import QuantumZipper.Proofs.Zipper.Cor15PosZip

/-!
# Corollary 1.5(a), positive times: the law transfer through finite marginals

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
the paper gives no proof). Task COR15-R12 (`handoff/COR15.md`).

`Cor15LawB1.theorem1_5a_pos_of_goodSet` asks for ONE measurable set `A` of `b1Data` values on
which ALL raw pairings `pairRaw (Z_t x).1 ρ`, `ρ : TestFun0 H`, are a measurable function of the
data. Because `b1Data` forgets the additive constant of the field (`nrm`), such an `A` forces a
statement for uncountably many `ρ` at once (see the report of COR15-R12). The σ-algebra of the
target of `configLawMod0` is the product (cylinder) σ-algebra, so laws only need to be compared
on finite marginals. This file proves the corresponding transfer, in which the good set may
depend on a finite family of test functions and times:

* `measure_eq_of_margJS`: finite measures on `(TestFun0 H → ℝ) × (ℝ≥0 → ℝ)` agreeing on all
  finite marginals `margJS J S` are equal (π–λ on cylinders);
* `map_eq_of_forall_ae`: two a.e.-measurable maps into that space whose coordinates agree a.s.
  (coordinate by coordinate) have the same law;
* `configLawMod0_zipCap_pos_of_goodSets`: the abstract transfer, per finite marginal;
* `theorem1_5a_pos_of_goodSets` (with `hR1`) and `theorem1_5a_pos_of_perTest` (with `hR1`
  replaced by per-test-function a.s. identities, via `ae_zipCapUp_zipCapDown_snd`).

Own elementary measure-theoretic argument (Dynkin π–λ via `ext_of_generate_finite`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full

/-- The finite marginal of `configLawMod0`-type data: pairings with the test functions in `J`,
driver values at the times in `S`. -/
def margJS (J : Finset (TestFun0 H)) (S : Finset ℝ≥0) (d : (TestFun0 H → ℝ) × (ℝ≥0 → ℝ)) :
    (J → ℝ) × (S → ℝ) :=
  (J.restrict d.1, S.restrict d.2)

theorem measurable_margJS (J : Finset (TestFun0 H)) (S : Finset ℝ≥0) :
    Measurable (margJS J S) :=
  ((Finset.measurable_restrict J).comp measurable_fst).prodMk
    ((Finset.measurable_restrict S).comp measurable_snd)

/-- **Finite marginals determine a finite measure** on `(TestFun0 H → ℝ) × (ℝ≥0 → ℝ)`. -/
theorem measure_eq_of_margJS {μ ν : Measure ((TestFun0 H → ℝ) × (ℝ≥0 → ℝ))}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ J S, μ.map (margJS J S) = ν.map (margJS J S)) : μ = ν := by
  let C : Set (Set ((TestFun0 H → ℝ) × (ℝ≥0 → ℝ))) :=
    Set.image2 (fun A c => A ×ˢ c) (measurableCylinders fun _ : TestFun0 H => ℝ)
      (measurableCylinders fun _ : ℝ≥0 => ℝ)
  have hgen : MeasurableSpace.generateFrom C =
      (inferInstance : MeasurableSpace ((TestFun0 H → ℝ) × (ℝ≥0 → ℝ))) :=
    generateFrom_eq_prod generateFrom_measurableCylinders generateFrom_measurableCylinders
      ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, iUnion_const _⟩
      ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, iUnion_const _⟩
  have hpi : IsPiSystem C := by
    rintro _ ⟨A, hA, c, hc, rfl⟩ _ ⟨A', hA', c', hc', rfl⟩ -
    exact ⟨A ∩ A', inter_mem_measurableCylinders hA hA', c ∩ c',
      inter_mem_measurableCylinders hc hc', Set.prod_inter_prod.symm⟩
  have key : ∀ s ∈ C, μ s = ν s := by
    rintro _ ⟨A, hA, c, hc, rfl⟩
    obtain ⟨J, T, hT, rfl⟩ := (mem_measurableCylinders _).1 hA
    obtain ⟨S, U, hU, rfl⟩ := (mem_measurableCylinders _).1 hc
    have hpre : cylinder J T ×ˢ cylinder S U = margJS J S ⁻¹' (T ×ˢ U) := rfl
    show μ (cylinder J T ×ˢ cylinder S U) = ν (cylinder J T ×ˢ cylinder S U)
    rw [hpre, ← Measure.map_apply (measurable_margJS J S) (hT.prod hU),
      ← Measure.map_apply (measurable_margJS J S) (hT.prod hU), h]
  exact ext_of_generate_finite C hgen.symm hpi key
    (key univ ⟨univ, univ_mem_measurableCylinders _, univ, univ_mem_measurableCylinders _,
      univ_prod_univ⟩)

section Maps

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem map_margJS_map {f : Ω → (TestFun0 H → ℝ) × (ℝ≥0 → ℝ)} (hf : AEMeasurable f P)
    (J : Finset (TestFun0 H)) (S : Finset ℝ≥0) :
    (P.map f).map (margJS J S) = P.map fun ω => margJS J S (f ω) :=
  AEMeasurable.map_map_of_aemeasurable (measurable_margJS J S).aemeasurable hf

/-- Two a.e.-measurable maps whose coordinates agree a.s., one coordinate at a time, have the
same law. -/
theorem map_eq_of_forall_ae [IsFiniteMeasure P] {f g : Ω → (TestFun0 H → ℝ) × (ℝ≥0 → ℝ)}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (h1 : ∀ ρ, ∀ᵐ ω ∂P, (f ω).1 ρ = (g ω).1 ρ) (h2 : ∀ s, ∀ᵐ ω ∂P, (f ω).2 s = (g ω).2 s) :
    P.map f = P.map g := by
  refine measure_eq_of_margJS fun J S => ?_
  rw [map_margJS_map hf, map_margJS_map hg]
  refine Measure.map_congr ?_
  have hJ : ∀ᵐ ω ∂P, ∀ ρ : J, (f ω).1 ρ = (g ω).1 ρ := ae_all_iff.2 fun ρ => h1 ρ
  have hS : ∀ᵐ ω ∂P, ∀ s : S, (f ω).2 s = (g ω).2 s := ae_all_iff.2 fun s => h2 s
  filter_upwards [hJ, hS] with ω h₁ h₂
  simp only [margJS]
  refine Prod.ext (funext fun ρ => ?_) (funext fun s => ?_)
  · simp only [Finset.restrict]; exact h₁ ρ
  · simp only [Finset.restrict]; exact h₂ s

/-- **Abstract transfer, per finite marginal.** As `configLawMod0_zipCap_pos_of_goodSet`, but the
measurable function `Φ` and the good set `A` may depend on a finite family `J` of test functions
and a finite set `S` of times; in exchange the zipped data must be a.e.-measurable. -/
theorem configLawMod0_zipCap_pos_of_goodSets [IsFiniteMeasure P] {γ t : ℝ} (ht : 0 ≤ t)
    (c : Ω → FieldSample × (ℝ → ℝ)) {E : Type*} [MeasurableSpace E]
    (e : FieldSample × (ℝ → ℝ) → E)
    (hZc : AEMeasurable (fun ω => mod0Data (zipCapUp γ t (c ω))) P)
    (hZy : AEMeasurable (fun ω => mod0Data (zipCapUp γ t (zipCapDown γ t (c ω)))) P)
    (hec : AEMeasurable (fun ω => e (c ω)) P)
    (hey : AEMeasurable (fun ω => e (zipCapDown γ t (c ω))) P)
    (hlaw : P.map (fun ω => e (c ω)) = P.map (fun ω => e (zipCapDown γ t (c ω))))
    (hgood : ∀ (J : Finset (TestFun0 H)) (S : Finset ℝ≥0),
      ∃ Φ : E → (J → ℝ) × (S → ℝ), Measurable Φ ∧ ∃ A : Set E, MeasurableSet A ∧
        (∀ x, e x ∈ A → margJS J S (mod0Data (zipCapUp γ t x)) = Φ (e x)) ∧
        ∀ᵐ ω ∂P, e (zipCapDown γ t (c ω)) ∈ A)
    (hR1 : configLawMod0 (fun ω => zipCapUp γ t (zipCapDown γ t (c ω))) P = configLawMod0 c P) :
    configLawMod0 (fun ω => zipCap γ t (c ω)) P = configLawMod0 c P := by
  rw [zipCap_of_nonneg ht, ← hR1, configLawMod0_eq_map, configLawMod0_eq_map]
  refine measure_eq_of_margJS fun J S => ?_
  obtain ⟨Φ, hΦ, A, hA, hfac, hyA⟩ := hgood J S
  rw [map_margJS_map hZc, map_margJS_map hZy]
  exact map_comp_eq_of_goodSet (Z := zipCapUp γ t) (m := fun x => margJS J S (mod0Data x))
    hΦ hA hfac hec hey hlaw hyA

end Maps

section Thm

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [IsProbabilityMeasure P] in
theorem aemeasurable_mod0Data_c (κ : ℝ) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) :
    AEMeasurable (fun ω => mod0Data (ofFun (h0rev κ) + X ω, drive κ B ω)) P := by
  obtain ⟨B', hB'm, -, hB'eq⟩ := CharFun.exists_good_version hB
  refine ⟨fun ω => mod0Data (ofFun (h0rev κ) + X ω, drive κ B' ω), ?_, ?_⟩
  · have hc : ∀ μ : Measure ℂ, Measurable fun ω => (ofFun (h0rev κ) + X ω) μ := fun μ =>
      measurable_const.add (hX.measurable_coord μ)
    refine Measurable.prodMk (measurable_pi_iff.2 fun ρ => ?_) (measurable_pi_iff.2 fun s => ?_)
    · unfold pairRaw; exact (hc _).sub (hc _)
    · exact measurable_const.mul (hB'm _)
  · filter_upwards [hB'eq] with ω h
    have : drive κ B ω = drive κ B' ω := by funext s; simp only [drive, h]
    rw [this]

/-- **Corollary 1.5(a) at `t > 0` from per-marginal good sets** (clause (a) of `theorem1_5`).
Inputs: `hZc`, `hZy` (a.e.-measurability of the zipped data), `hgood` (per finite marginal:
determination on a good set of `b1Data` values), `hR1` (law form of P1). -/
theorem theorem1_5a_pos_of_goodSets (κ : ℝ) (hκ : 0 < κ) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t)
    (hZc : AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (ofFun (h0rev κ) + X ω, drive κ B ω))) P)
    (hZy : AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))) P)
    (hgood : ∀ (J : Finset (TestFun0 H)) (S : Finset ℝ≥0),
      ∃ Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → (J → ℝ) × (S → ℝ), Measurable Φ ∧
        ∃ A : Set (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)), MeasurableSet A ∧
        (∀ x, b1Data x ∈ A →
          margJS J S (mod0Data (zipCapUp (Real.sqrt κ) t x)) = Φ (b1Data x)) ∧
        ∀ᵐ ω ∂P,
          b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A)
    (hR1 : configLawMod0 (fun ω => zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) P =
      configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P) :
    configLawMod0 (fun ω => zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) P =
      configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P :=
  configLawMod0_zipCap_pos_of_goodSets ht.le _ b1Data hZc hZy
    (aemeasurable_b1Data_c κ hB hX) (aemeasurable_b1Data_unzip κ hκ hB hX hind ht)
    (b1_full κ hκ P B X hB hX hind ht).symm hgood hR1

/-- **R1 from per-test-function identities.** The law form of P1 follows from: a.e.-measurability
of the re-zipped data (`hZy`) and, for each mass-zero test function `ρ`, a.s. equality of the raw
pairings of `Z_t (D_t c)` and of `c` (`hraw`). The driver half is
`ae_zipCapUp_zipCapDown_snd` (Theorem 1.3 + Rohde–Schramm). -/
theorem hR1_of_perTest (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t)
    (hZy : AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))) P)
    (hraw : ∀ ρ : TestFun0 H, ∀ᵐ ω ∂P,
      pairRaw (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).1 ρ.1.1 =
      pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1) :
    configLawMod0 (fun ω => zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) P =
      configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P := by
  rw [configLawMod0_eq_map, configLawMod0_eq_map]
  refine map_eq_of_forall_ae hZy (aemeasurable_mod0Data_c κ hB hX) (fun ρ => hraw ρ)
    (fun s => ?_)
  filter_upwards [ae_zipCapUp_zipCapDown_snd P B X h13 hRSS hκ hκ4 hB hX hind ht] with ω h
  exact h s s.2

/-- **Corollary 1.5(a) at `t > 0`, per-test-function form** (clause (a) of `theorem1_5`, for
`κ ∈ (0,4)`), from Theorem 1.3, `RohdeSchrammSimple` and the inputs `hZc`, `hZy`, `hraw`,
`hgood`. -/
theorem theorem1_5a_pos_of_perTest (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t)
    (hZc : AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (ofFun (h0rev κ) + X ω, drive κ B ω))) P)
    (hZy : AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)))) P)
    (hraw : ∀ ρ : TestFun0 H, ∀ᵐ ω ∂P,
      pairRaw (zipCapUp (Real.sqrt κ) t
        (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))).1 ρ.1.1 =
      pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1)
    (hgood : ∀ (J : Finset (TestFun0 H)) (S : Finset ℝ≥0),
      ∃ Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → (J → ℝ) × (S → ℝ), Measurable Φ ∧
        ∃ A : Set (((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)), MeasurableSet A ∧
        (∀ x, b1Data x ∈ A →
          margJS J S (mod0Data (zipCapUp (Real.sqrt κ) t x)) = Φ (b1Data x)) ∧
        ∀ᵐ ω ∂P,
          b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A) :
    configLawMod0 (fun ω => zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) P =
      configLawMod0 (fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)) P :=
  theorem1_5a_pos_of_goodSets κ hκ hB hX hind ht hZc hZy hgood
    (hR1_of_perTest h13 hRSS hκ hκ4 hB hX hind ht hZy hraw)

end Thm

end Cor15Group
end QuantumZipper
