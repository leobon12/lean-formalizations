import LQGMetric.Prob.CondIndepAEDet
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Section 4.2: field determination from conditional independence; law transfer (Aux. lemma 23)

Packet PROVE-SEC4-B. The probabilistic steps of §4.2 of the specification
(`source/spec/p097-144.md`) that do not depend on the strip geometry.

* **Proof of Theorem 1.2 for `κ ∈ (0, 4)` assuming (4.4)** (p. 122): "Proposition 4.11 implies
  that the flow line `η` … is equal to the left boundary of the counterflow line `η'` …, where
  `η, η', h` are coupled together so that `η` is conditionally independent of `η'` given `h`.
  Since `η` and `η'` are conditionally independent given `h`, it follows that `η` is almost surely
  determined by `h`." Here: `aeDeterminedBy_of_condIndepEv_of_ae_eq_comp` — if `η ⟂ η' | h` and
  `η = L(η')` a.s. for a measurable `L` (the left-boundary map), then `η = Φ(h)` a.s. for a
  measurable `Φ`. Conditional independence is the event form `LQGMetric.CondIndepEv` used by the
  project's local-set lemmas (no standard Borel sample space needed); the core is
  LQGMetric's two-copies criterion `LQGMetric.aeDeterminedBy_of_condIndepEv_of_ae_eq`.
* **Aux. lemma 23** (pp. 122–123), its measure-theoretic steps:
  - `measure_eq_of_map_eq_of_injOn`: "Restriction to the fixed open set `ℍ \ K` is a Borel
    injection between standard Borel spaces. Its inverse on its image is Borel by the
    measurable-inverse theorem for such injections. Consequently two probability measures
    supported on `H^{-ε}_loc` with the same restricted distribution law have the same full
    distribution law" (Lusin–Souslin);
  - `map_prod_eq_of_condDistrib_ae_eq`: "Integrating over the common history law proves equality
    of the full stopped joint laws" (same history law, a.e. equal regular conditional laws);
  - `measure_eq_of_map_finRecord_eq`, `map_prod_eq_of_forall_map_fin`: "Equality of all these
    finite joint laws gives equality of the field and full-history laws on the countable sequence
    space";
  - `ae_eq_comp_of_map_eq`: "If the reference law is concentrated on `X = Φ(h)`, equality of
    joint laws gives this identity in each other coupling as well."
* `exists_measurable_ae_eq_comp_of_condIndepEv`: the two steps combined — a reference coupling
  in which `η ⟂ η' | h` and `η = L(η')` gives one Borel `Φ` with `η = Φ(h)` in the reference and
  in every coupling with the same joint law of field and path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter

namespace InteractingSLE

namespace Sec4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Determination from conditional independence** (proof of Theorem 1.2 assuming (4.4),
p. 122). If `η` and `η'` are conditionally independent given `h` and `η = L(η')` almost surely
for a measurable `L` (with values in a standard Borel space), then `η` is almost surely a
measurable function of `h`. -/
theorem aeDeterminedBy_of_condIndepEv_of_ae_eq_comp [IsProbabilityMeasure P]
    {G E F : Type*} [mG : MeasurableSpace G] [mE : MeasurableSpace E] [mF : MeasurableSpace F]
    [StandardBorelSpace E] [Nonempty E] {h : Ω → G} {η : Ω → E} {η' : Ω → F}
    (hh : Measurable h) (hη : Measurable η)
    (hci : LQGMetric.CondIndepEv (mG.comap h) (mE.comap η) (mF.comap η') P)
    {L : F → E} (hL : Measurable L) (heq : η =ᵐ[P] L ∘ η') : LQGMetric.AEDeterminedBy η h P := by
  have hle : mE.comap (L ∘ η') ≤ mF.comap η' := by
    rw [← comap_comp]
    exact comap_mono hL.comap_le
  exact LQGMetric.aeDeterminedBy_of_condIndepEv_of_ae_eq hh hη (hci.mono le_rfl hle) heq

/-- **Transfer of field determination by equality of joint laws** (Aux. lemma 23, last
paragraph). If `(h', X')` has the same joint law as `(h, X)` and `X = Φ(h)` almost surely, then
`X' = Φ(h')` almost surely (`E` has a measurable diagonal, e.g. standard Borel). -/
theorem ae_eq_comp_of_map_eq {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    {G E : Type*} [MeasurableSpace G] [MeasurableSpace E] [MeasurableEq E]
    {h : Ω → G} {X : Ω → E} {h' : Ω' → G} {X' : Ω' → E}
    (hhX : AEMeasurable (fun ω => (h ω, X ω)) P) (hhX' : AEMeasurable (fun ω => (h' ω, X' ω)) P')
    (hlaw : P'.map (fun ω => (h' ω, X' ω)) = P.map (fun ω => (h ω, X ω)))
    {Φ : G → E} (hΦ : Measurable Φ) (hX : X =ᵐ[P] Φ ∘ h) : X' =ᵐ[P'] Φ ∘ h' := by
  set B : Set (G × E) := {p | p.2 ≠ Φ p.1} with hB
  have hBm : MeasurableSet B := (measurableSet_eq_fun measurable_snd (hΦ.comp measurable_fst)).compl
  have h1 : P.map (fun ω => (h ω, X ω)) B = 0 := by
    rw [Measure.map_apply_of_aemeasurable hhX hBm]
    exact measure_mono_null (fun ω hω => hω) (ae_iff.1 hX)
  have h2 : P' ((fun ω => (h' ω, X' ω)) ⁻¹' B) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable hhX' hBm, hlaw, h1]
  exact ae_iff.2 (measure_mono_null (fun ω hω => hω) h2)

/-- **Lusin–Souslin uniqueness** (Aux. lemma 23 proof, p. 123). Let `R : E → F` be measurable,
`E` standard Borel, `F` countably separated, and `R` injective on a measurable set `S`. Two
measures carried by `S` with the same image under `R` are equal. -/
theorem measure_eq_of_map_eq_of_injOn {E F : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace F] [CountablySeparated F] {R : E → F} (hR : Measurable R) {S : Set E}
    (hS : MeasurableSet S) (hinj : InjOn R S) {μ ν : Measure E} (hμ : μ Sᶜ = 0) (hν : ν Sᶜ = 0)
    (hmap : μ.map R = ν.map R) : μ = ν := by
  ext A hA
  have hB : MeasurableSet (R '' (A ∩ S)) :=
    (hA.inter hS).image_of_measurable_injOn hR (hinj.mono inter_subset_right)
  have hpre : R ⁻¹' (R '' (A ∩ S)) ∩ S = A ∩ S := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, hxy⟩, hx⟩
      rw [← hinj hy.2 hx hxy]
      exact hy
    · rintro hx
      exact ⟨⟨x, hx, rfl⟩, hx.2⟩
  have key : ∀ ρ : Measure E, ρ Sᶜ = 0 → ρ A = (ρ.map R) (R '' (A ∩ S)) := by
    intro ρ hρ
    rw [Measure.map_apply hR hB, ← measure_inter_conull hρ (s := A),
      ← measure_inter_conull hρ (s := R ⁻¹' (R '' (A ∩ S))), hpre]
  rw [key μ hμ, key ν hν, hmap]

/-- **Mixture over the common history law** (Aux. lemma 23 proof, p. 123: "Integrating over the
common history law proves equality of the full stopped joint laws"). If `H` and `H'` have the
same law and the regular conditional laws of `X` given `H` and of `X'` given `H'` agree almost
everywhere for that law, then `(H, X)` and `(H', X')` have the same joint law. -/
theorem map_prod_eq_of_condDistrib_ae_eq {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P'] {G E : Type*} [MeasurableSpace G]
    [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E] {H : Ω → G} {X : Ω → E}
    {H' : Ω' → G} {X' : Ω' → E} (hH : AEMeasurable H P) (hX : AEMeasurable X P)
    (hH' : AEMeasurable H' P') (hX' : AEMeasurable X' P') (hlaw : P'.map H' = P.map H)
    (hker : condDistrib X' H' P' =ᵐ[P.map H] condDistrib X H P) :
    P'.map (fun ω => (H' ω, X' ω)) = P.map (fun ω => (H ω, X ω)) := by
  rw [← compProd_map_condDistrib hH' hX', ← compProd_map_condDistrib hH hX, hlaw]
  exact Measure.compProd_congr hker

/-- The finite record `(g, x₀, …, x_{n−1})` of a field and a sequence. -/
def finRecord {G E : Type*} (n : ℕ) (p : G × (ℕ → E)) : G × (Fin n → E) :=
  (p.1, fun i => p.2 i)

theorem measurable_finRecord {G E : Type*} [MeasurableSpace G] [MeasurableSpace E] (n : ℕ) :
    Measurable (finRecord (G := G) (E := E) n) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_snd)

/-- **Countable exhaustion** (Aux. lemma 23 proof, p. 123: "Equality of all these finite joint
laws gives equality of the field and full-history laws on the countable sequence space"). Two
finite measures on `G × (ℕ → E)` whose images under every finite record
`(g, x) ↦ (g, x₀, …, x_{n−1})` agree are equal. -/
theorem measure_eq_of_map_finRecord_eq {G E : Type*} [MeasurableSpace G] [MeasurableSpace E]
    {μ ν : Measure (G × (ℕ → E))} [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (finRecord n) = ν.map (finRecord n)) : μ = ν := by
  set C : Set (Set (G × (ℕ → E))) :=
    {S | ∃ n : ℕ, ∃ B : Set (G × (Fin n → E)), MeasurableSet B ∧ S = finRecord n ⁻¹' B} with hC
  -- the cylinder rectangles form a π-system
  have hpi : IsPiSystem C := by
    rintro _ ⟨n, B₁, hB₁, rfl⟩ _ ⟨m, B₂, hB₂, rfl⟩ -
    set ρ₁ : G × (Fin (max n m) → E) → G × (Fin n → E) :=
      fun q => (q.1, fun i => q.2 ⟨i, lt_of_lt_of_le i.2 (le_max_left n m)⟩) with hρ₁
    set ρ₂ : G × (Fin (max n m) → E) → G × (Fin m → E) :=
      fun q => (q.1, fun i => q.2 ⟨i, lt_of_lt_of_le i.2 (le_max_right n m)⟩) with hρ₂
    have hρ₁m : Measurable ρ₁ :=
      measurable_fst.prodMk (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_snd)
    have hρ₂m : Measurable ρ₂ :=
      measurable_fst.prodMk (measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp measurable_snd)
    exact ⟨max n m, ρ₁ ⁻¹' B₁ ∩ ρ₂ ⁻¹' B₂, (hρ₁m hB₁).inter (hρ₂m hB₂), rfl⟩
  -- they generate the product σ-algebra
  have hgen : (inferInstance : MeasurableSpace (G × (ℕ → E))) = MeasurableSpace.generateFrom C := by
    refine le_antisymm ?_ (generateFrom_le ?_)
    · show (inferInstance : MeasurableSpace G).comap Prod.fst ⊔
          (MeasurableSpace.pi : MeasurableSpace (ℕ → E)).comap Prod.snd ≤ generateFrom C
      refine sup_le ?_ ?_
      · rintro _ ⟨A, hA, rfl⟩
        exact measurableSet_generateFrom ⟨0, A ×ˢ univ, hA.prod MeasurableSet.univ, by
          ext p; simp [finRecord]⟩
      · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
        refine iSup_le fun i => ?_
        rw [MeasurableSpace.comap_comp]
        rintro _ ⟨S, hS, rfl⟩
        have hm : MeasurableSet {f : Fin (i + 1) → E | f ⟨i, Nat.lt_succ_self i⟩ ∈ S} :=
          (measurable_pi_apply (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))) hS
        exact measurableSet_generateFrom ⟨i + 1, univ ×ˢ _, MeasurableSet.univ.prod hm, by
          ext p; simp [finRecord]⟩
    · rintro _ ⟨n, B, hB, rfl⟩
      exact measurable_finRecord n hB
  have hν : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    have := congrArg (fun ρ => ρ univ) (h 0)
    simp only [Measure.map_apply (measurable_finRecord 0) MeasurableSet.univ, preimage_univ] at this
    rw [← this]
    exact measure_lt_top μ univ
  refine ext_of_generate_finite C hgen hpi ?_ ?_
  · rintro _ ⟨n, B, hB, rfl⟩
    rw [← Measure.map_apply (measurable_finRecord n) hB, ← Measure.map_apply (measurable_finRecord n)
      hB, h n]
  · have := congrArg (fun ρ => ρ univ) (h 0)
    simpa only [Measure.map_apply (measurable_finRecord 0) MeasurableSet.univ, preimage_univ]
      using this

/-- **Countable exhaustion, coupling form** (Aux. lemma 23 proof, p. 123). If, for every `n`,
the field and the first `n` stopped records have the same joint law in two couplings, then the
field and the whole record sequence have the same joint law. -/
theorem map_prod_eq_of_forall_map_fin {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsFiniteMeasure P] {G E : Type*} [MeasurableSpace G] [MeasurableSpace E] {H : Ω → G}
    {X : ℕ → Ω → E} {H' : Ω' → G} {X' : ℕ → Ω' → E} (hH : Measurable H)
    (hX : ∀ n, Measurable (X n)) (hH' : Measurable H') (hX' : ∀ n, Measurable (X' n))
    (hfin : ∀ n : ℕ, P.map (fun ω => (H ω, fun i : Fin n => X i ω)) =
      P'.map (fun ω => (H' ω, fun i : Fin n => X' i ω))) :
    P.map (fun ω => (H ω, fun i => X i ω)) = P'.map (fun ω => (H' ω, fun i => X' i ω)) := by
  have hF : Measurable fun ω => (H ω, fun i => X i ω) := hH.prodMk (measurable_pi_iff.2 hX)
  have hF' : Measurable fun ω => (H' ω, fun i => X' i ω) := hH'.prodMk (measurable_pi_iff.2 hX')
  refine measure_eq_of_map_finRecord_eq fun n => ?_
  rw [Measure.map_map (measurable_finRecord n) hF, Measure.map_map (measurable_finRecord n) hF']
  exact hfin n

/-- **Theorem 1.2 assuming (4.4), probabilistic skeleton** (p. 122 with Aux. lemma 23, last
paragraph). In a reference coupling where `η ⟂ η' | h` and `η = L(η')` almost surely, there is a
measurable `Φ` with `η = Φ(h)` almost surely, and the same `Φ` determines the path in every
coupling `(h', X')` (on any probability space of the universe `v`) with the same joint law as
`(h, η)`. -/
theorem exists_measurable_ae_eq_comp_of_condIndepEv [IsProbabilityMeasure P]
    {G E F : Type*} [mG : MeasurableSpace G] [mE : MeasurableSpace E] [mF : MeasurableSpace F]
    [StandardBorelSpace E] [Nonempty E] {h : Ω → G} {η : Ω → E} {η' : Ω → F}
    (hh : Measurable h) (hη : Measurable η)
    (hci : LQGMetric.CondIndepEv (mG.comap h) (mE.comap η) (mF.comap η') P)
    {L : F → E} (hL : Measurable L) (heq : η =ᵐ[P] L ∘ η') :
    ∃ Φ : G → E, Measurable Φ ∧ η =ᵐ[P] Φ ∘ h ∧
      ∀ {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {h' : Ω' → G} {X' : Ω' → E},
        AEMeasurable (fun ω => (h' ω, X' ω)) P' →
        P'.map (fun ω => (h' ω, X' ω)) = P.map (fun ω => (h ω, η ω)) → X' =ᵐ[P'] Φ ∘ h' := by
  obtain ⟨Φ, hΦ, hηΦ⟩ := aeDeterminedBy_of_condIndepEv_of_ae_eq_comp hh hη hci hL heq
  exact ⟨Φ, hΦ, hηΦ, fun hm hlaw =>
    ae_eq_comp_of_map_eq (hh.prodMk hη).aemeasurable hm hlaw hΦ hηΦ⟩

end Sec4

end InteractingSLE
