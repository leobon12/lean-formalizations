/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Prop73Det

/-!
# Aux. lemma 50's field kernel for the two-seed words, in both of its uses

Packet PROVE-PROP73R. Specification Aux. lemma 50 (`source/spec/p193-240.md` L816ff., pp. 236–242, "with any
parameter `κ > 0`") and its consumers: Aux. lemma 51 (p. 242), Proposition 7.3's proof (pp. 242–243, `κ < 4`) and
Aux. lemma 126's proof (supplement p. 401, Theorem R.7, `κ > 4`).

Aux. lemma 50 identifies, through a bounded stop `S` of a coupling whose driver has a continuous trace, the
conditional law of the **entire** field given the recorded driving history through `t ∧ S`; its last paragraph
(p. 241–242) fixes "common Borel versions of its mean under the common driving marginal", so that "the same functions
apply in every coupling with that marginal". Proposition 7.3's proof then argues (p. 243):

> Aux. lemma 51 identifies its full field–history joint law through each deterministic capacity time `n` with that
> of the constructed reference. […] The histories through the integer times are nested. Their countable sequence
> determines the full continuous driving evolution and its trace. Equality of their finite stopped joint laws, each
> retaining the whole field, gives equality of the full field–curve joint laws.

The two consumers of Aux. lemma 50 in Lean need it at the **terminal** recorded history: Proposition 7.3
(`Prop73Det.Prop73FieldKernelStatement`, `0 < κ < 4`, boundary-hitting pairs) and Theorem R.7
(`R7.R7FieldKernelStatement`, `κ > 4`). Both are `R7.TwoSeedTraceFieldKernel` for one Borel `Ψ`.

This file proves both from **one** named input, Aux. lemma 50 for the two-seed words at the integer times in its
common-Borel-kernel form (`HasTraceStopKernel`, `Aux50TwoSeedStatement`), by the argument quoted above:

1. **Aux. lemma 51 at the integer times** (`map_prod_stopHistory_eq`): a common Borel kernel and Theorem 2.2's
   uniqueness of the two-seed driving law give one joint law of the field and the history stopped at `n`
   (`Sec7.map_prod_eq_of_condExp_exp_eq`, the last step of Aux. lemma 51's proof: "Integrating the equal kernels
   against the common stopped driving law proves equality of the full joint laws").
2. **The nested histories** (`map_prod_killedHistory_eq`): the lifetime is infinite (both seed weights exceed `−2`,
   `R7.ae_lifetime_eq_top`), the stopped histories are nested and read off the whole killed history
   (`Sec4.histOfStops`), so the full joint laws agree (`Sec4.map_prod_eq_of_forall_map_fin`).
3. **The terminal kernel** (`exists_twoSeedTraceFieldKernel`): the conditional characteristic functions of one
   reference coupling given its killed history are a Borel function `Ψ` of the history (Doob–Dynkin), and they
   transfer to every coupling along the common joint law (`isHistoryFieldKernel_of_map_eq`). With no reference
   coupling the statement is vacuous.
4. **Both uses** (`prop73FieldKernelStatement_of_aux50`, `r7FieldKernelStatement_of_aux50`).

## The named input

`HasTraceStopKernel κ rL rR` (with `IsTraceStopKernel`): there is one family `K n` of functions of the recorded
history, Borel for each test function, such that in **every** coupling of `SLE_κ(rL; rR)` with the original optional
hull specification whose driver almost surely has a continuous generating trace through its lifetime (Aux. lemma 50's
"known-continuous prefix"), on probability spaces of the two universes, `K n` is the conditional characteristic
function of the whole field given the killed driving history stopped at the integer time `n`. This is the conclusion
of Aux. lemma 50 at `S = n` (a bounded own-filtration stop below the infinite lifetime) with its common Borel versions,
**weakened**: the explicit Gaussian form (mean (HGV1), covariance `G_{Ω_t}`) is not asserted, only that the kernel is
one Borel function of the stopped history. `Aux50TwoSeedStatement` is its source-wide form (every `κ > 0`, every pair
`rL, rR > −2`); each consumer below takes only the parameter range it uses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v w

namespace InteractingSLE

namespace Aux50

open LawUnique LQGMetric

/-! ### Transfer of a field kernel along an equal joint law -/

section Transfer

variable {Γ : Type*} [mΓ : MeasurableSpace Γ]

/-- **A field kernel transfers along an equal joint law.** If `Ψ` (Borel in the history for each test function) is
the conditional characteristic function of `h₀` given `σ(H₀)`, and `(h, H)` has the joint law of `(h₀, H₀)`, then
`Ψ` is the conditional characteristic function of `h` given `σ(H)`. -/
theorem isHistoryFieldKernel_of_map_eq {Ω₀ Ω : Type*} {m₀ : MeasurableSpace Ω₀} {mΩ : MeasurableSpace Ω}
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {P : Measure Ω} [IsProbabilityMeasure P]
    {h₀ : Ω₀ → DistOn upperHalfPlaneOpens} {H₀ : Ω₀ → Γ} {h : Ω → DistOn upperHalfPlaneOpens} {H : Ω → Γ}
    (hh₀ : Measurable h₀) (hH₀ : Measurable H₀) (hh : Measurable h) (hH : Measurable H)
    {Ψ : Γ → TestOn upperHalfPlaneOpens → ℂ} (hΨ : ∀ φ, Measurable fun x => Ψ x φ)
    (hK₀ : IsHistoryFieldKernel P₀ h₀ H₀ Ψ)
    (hlaw : P₀.map (fun ω => (h₀ ω, H₀ ω)) = P.map (fun ω => (h ω, H ω))) :
    IsHistoryFieldKernel P h H Ψ := by
  intro φ
  have hlawH : P₀.map H₀ = P.map H := by
    have e₀ : P₀.map H₀ = (P₀.map fun ω => (h₀ ω, H₀ ω)).map Prod.snd := by
      rw [Measure.map_map measurable_snd (hh₀.prodMk hH₀)]
      rfl
    have e : P.map H = (P.map fun ω => (h ω, H ω)).map Prod.snd := by
      rw [Measure.map_map measurable_snd (hh.prodMk hH)]
      rfl
    rw [e₀, e, hlaw]
  have hint : Integrable (fun ω => Complex.exp (↑(h ω φ) * Complex.I)) P :=
    Sobolev.integrable_exp_mul_I ((Sobolev.measurable_distOn_apply φ).comp hh)
  have hgint₀ : Integrable (fun ω => Ψ (H₀ ω) φ) P₀ := integrable_condExp.congr (hK₀ φ)
  have hgint : Integrable (fun x => Ψ x φ) (P.map H) := by
    rw [← hlawH]
    exact (integrable_map_measure (hΨ φ).aestronglyMeasurable hH₀.aemeasurable).2 hgint₀
  have hgint' : Integrable (fun ω => Ψ (H ω) φ) P :=
    (integrable_map_measure (hΨ φ).aestronglyMeasurable hH.aemeasurable).1 hgint
  have hm1 : Measurable fun p : DistOn upperHalfPlaneOpens × Γ => Complex.exp (↑(p.1 φ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      ((Sobolev.measurable_distOn_apply φ).comp measurable_fst)).mul_const _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hH.comap_le hint
    (fun s _ _ => hgint'.integrableOn) (fun s hs _ => ?_)
    ((hΨ φ).stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable).symm
  obtain ⟨S, hS, rfl⟩ := hs
  have hk₀ := Sec7.setIntegral_exp_map_eq_of_condExp hΨ hh₀ hH₀ le_rfl hH₀.comap_le φ (hK₀ φ) hS
  have hpre : (fun ω => (h ω, H ω)) ⁻¹' (univ ×ˢ S) = H ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_prod, mem_univ, true_and]
  calc ∫ ω in H ⁻¹' S, Ψ (H ω) φ ∂P
      = ∫ x in S, Ψ x φ ∂(P.map H) :=
        (setIntegral_map hS (hΨ φ).aestronglyMeasurable hH.aemeasurable).symm
    _ = ∫ x in S, Ψ x φ ∂(P₀.map H₀) := by rw [hlawH]
    _ = ∫ p in univ ×ˢ S, Complex.exp (↑(p.1 φ) * Complex.I) ∂(P₀.map fun ω => (h₀ ω, H₀ ω)) := hk₀.symm
    _ = ∫ p in univ ×ˢ S, Complex.exp (↑(p.1 φ) * Complex.I) ∂(P.map fun ω => (h ω, H ω)) := by
        rw [hlaw]
    _ = ∫ ω in (fun ω => (h ω, H ω)) ⁻¹' (univ ×ˢ S), Complex.exp (↑(h ω φ) * Complex.I) ∂P :=
        setIntegral_map (MeasurableSet.univ.prod hS) hm1.aestronglyMeasurable (hh.prodMk hH).aemeasurable
    _ = ∫ ω in H ⁻¹' S, Complex.exp (↑(h ω φ) * Complex.I) ∂P := by rw [hpre]

/-- **Doob–Dynkin for the conditional characteristic functions**: in one coupling, the conditional characteristic
functions of `h` given `σ(H)` are one function `Ψ` of `H`, Borel for each test function. -/
theorem exists_isHistoryFieldKernel {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (H : Ω → Γ) :
    ∃ Ψ : Γ → TestOn upperHalfPlaneOpens → ℂ, (∀ φ, Measurable fun x => Ψ x φ) ∧
      IsHistoryFieldKernel P h H Ψ := by
  have hDD : ∀ φ : TestOn upperHalfPlaneOpens, ∃ g : Γ → ℂ, StronglyMeasurable g ∧
      P[fun ω => Complex.exp (↑(h ω φ) * Complex.I) | mΓ.comap H] = g ∘ H :=
    fun φ => stronglyMeasurable_condExp.exists_eq_measurable_comp
  choose g hgm hgeq using hDD
  exact ⟨fun x φ => g φ x, fun φ => (hgm φ).measurable, fun φ => Eventually.of_forall fun ω =>
    congrFun (hgeq φ) ω⟩

end Transfer

/-! ### The named input: Aux. lemma 50 at the integer times -/

/-- **Aux. lemma 50's common kernel at the integer times, in one universe.** `K n` is the conditional characteristic
function of the whole field given the killed driving history stopped at the integer time `n`, in every coupling of
`SLE_κ(rL; rR)` (marks at `0⁻`, `0⁺`) with the original optional hull specification on a probability space of the
universe `u` whose driver almost surely has a continuous generating trace through its lifetime. -/
def IsTraceStopKernel (κ rL rR : ℝ) (K : ℕ → HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h →
    (∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) →
    ∀ n : ℕ, IsHistoryFieldKernel P h
      (fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W VL VR ζ ω)) (K n)

/-- **Aux. lemma 50 for one two-seed word, at the integer times** (specification pp. 236–242: "the conditional law of
the entire field given its recorded driving history through `t ∧ S` is Gaussian with mean `M_t` and covariance
`G_{Ω_t}`", with "common measurable versions of (HGV1) under their one common driving marginal […] the same functions
apply in every coupling with that marginal"), in the weakened form "one Borel kernel of the stopped history", for
couplings on probability spaces of the universes `u` and `v`. -/
def HasTraceStopKernel (κ rL rR : ℝ) : Prop :=
  ∃ K : ℕ → HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ, (∀ n φ, Measurable fun x => K n x φ) ∧
    IsTraceStopKernel.{u} κ rL rR K ∧ IsTraceStopKernel.{v} κ rL rR K

/-- **Named input: Aux. lemma 50 for the two-seed words** (specification p. 236, "Fix a finite-force integrated driving
law, with any parameter `κ > 0`"), at the integer capacity times, for every pair of seed weights `rL, rR > −2` (whose
evolutions have infinite lifetime, so every integer time is a bounded stop below it). -/
def Aux50TwoSeedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → HasTraceStopKernel.{u, v} κ rL rR

/-! ### Step 1: Aux. lemma 51 at the integer times -/

section Laws

variable {κ rL rR : ℝ} {K : ℕ → HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ}

/-- **Aux. lemma 51 at the integer times** (p. 242: "Integrating the equal kernels against the common stopped driving
law proves equality of the full joint laws"): two couplings with continuous traces, on probability spaces of the
universes `u` and `v`, with the common kernel `K n`, have the same joint law of the field and the history stopped at
`n`. The history laws agree by Theorem 2.2's two-seed uniqueness (`LawUnique.killedStateLawUnique_twoSeed`). -/
theorem map_prod_stopHistory_eq (hκ : 0 < κ) (hKm : ∀ n φ, Measurable fun x => K n x φ)
    (hK₁ : IsTraceStopKernel.{u} κ rL rR K) (hK₂ : IsTraceStopKernel.{v} κ rL rR K)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ}
    {ζ₁ : Ω₁ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (htr₁ : ∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η)
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (htr₂ : ∀ᵐ ω ∂P₂, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω) (ζ₂ ω) η) (n : ℕ) :
    P₁.map (fun ω => (h₁ ω, Sec4.stopHistory (Sec4.natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
      P₂.map (fun ω => (h₂ ω, Sec4.stopHistory (Sec4.natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) := by
  obtain ⟨hX₁, -⟩ := hC₁.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hst : Measurable (Sec4.stopHistory (nL := 1) (nR := 1) (Sec4.natStop n)) :=
    Sec4.measurable_stopHistory (Sec4.measurable_natStop n)
  have hH₁ := measurable_killedHistory hX₁
  have hH₂ := measurable_killedHistory hX₂
  have hlawK : P₁.map (killedHistory W₁ VL₁ VR₁ ζ₁) = P₂.map (killedHistory W₂ VL₂ VR₂ ζ₂) :=
    map_killedHistory_eq (killedStateLawUnique_twoSeed hκ _ _ (fun _ => rfl) fun _ => rfl) hC₁.1 hX₁ hC₂.1 hX₂
  have hlaw : P₁.map (fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      P₂.map (fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
    have e₁ : (fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
        Sec4.stopHistory (Sec4.natStop n) ∘ killedHistory W₁ VL₁ VR₁ ζ₁ := rfl
    have e₂ : (fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
        Sec4.stopHistory (Sec4.natStop n) ∘ killedHistory W₂ VL₂ VR₂ ζ₂ := rfl
    rw [e₁, e₂, ← Measure.map_map hst hH₁, ← Measure.map_map hst hH₂, hlawK]
  have hS₁ : Measurable fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω) :=
    hst.comp hH₁
  have hS₂ : Measurable fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
    hst.comp hH₂
  exact Sec7.map_prod_eq_of_condExp_exp_eq (hKm n) hC₁.2.1 hS₁ le_rfl hS₁.comap_le
    (hK₁ P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ hC₁ htr₁ n) hC₂.2.1 hS₂ le_rfl hS₂.comap_le
    (hK₂ P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ htr₂ n) hlaw

/-- **The nested histories: one full joint law** (Proposition 7.3's proof, p. 243: "The histories through the integer
times are nested. Their countable sequence determines the full continuous driving evolution and its trace. Equality of
their finite stopped joint laws, each retaining the whole field, gives equality of the full field–curve joint laws").
Two couplings with continuous traces and the common kernel `K n` at every integer time have the same joint law of the
field and the killed driving history. Both seed weights exceed `−2`, so the lifetime is infinite and the killed
history is read off its integer stops (`Sec4.histOfStops_stopHistory`). -/
theorem map_prod_killedHistory_eq (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hKm : ∀ n φ, Measurable fun x => K n x φ)
    (hK₁ : IsTraceStopKernel.{u} κ rL rR K) (hK₂ : IsTraceStopKernel.{v} κ rL rR K)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ}
    {ζ₁ : Ω₁ → ℝ≥0∞} {h₁ : Ω₁ → DistOn upperHalfPlaneOpens}
    (hC₁ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁)
    (htr₁ : ∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η)
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hC₂ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂)
    (htr₂ : ∀ᵐ ω ∂P₂, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω) (ζ₂ ω) η) :
    P₁.map (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      P₂.map (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
  have hT₁ := R7.ae_lifetime_eq_top hκ hL hR hC₁.1
  have hT₂ := R7.ae_lifetime_eq_top hκ hL hR hC₂.1
  obtain ⟨hX₁, -⟩ := hC₁.2.2.2
  obtain ⟨hX₂, -⟩ := hC₂.2.2.2
  have hH₁ := measurable_killedHistory hX₁
  have hH₂ := measurable_killedHistory hX₂
  have hstop := map_prod_stopHistory_eq hκ hKm hK₁ hK₂ hC₁ htr₁ hC₂ htr₂
  have hXm₁ : ∀ n : ℕ, Measurable fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω) :=
    fun n => (Sec4.measurable_stopHistory (Sec4.measurable_natStop n)).comp hH₁
  have hXm₂ : ∀ n : ℕ, Measurable fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω) :=
    fun n => (Sec4.measurable_stopHistory (Sec4.measurable_natStop n)).comp hH₂
  -- the finite joint laws
  have hfin : ∀ N : ℕ,
      P₁.map (fun ω => (h₁ ω, fun i : Fin N =>
        Sec4.stopHistory (Sec4.natStop i) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
      P₂.map (fun ω => (h₂ ω, fun i : Fin N =>
        Sec4.stopHistory (Sec4.natStop i) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) := by
    intro N
    let R : DistOn upperHalfPlaneOpens × HistorySpace 1 1 →
        DistOn upperHalfPlaneOpens × (Fin N → HistorySpace 1 1) :=
      fun q => (q.1, fun i => Sec4.stopHistory (Sec4.natStop i) q.2)
    have hR : Measurable R := measurable_fst.prodMk
      (measurable_pi_iff.2 fun i => (Sec4.measurable_stopHistory (Sec4.measurable_natStop i)).comp measurable_snd)
    have e₁ : (fun ω => (h₁ ω, fun i : Fin N =>
        Sec4.stopHistory (Sec4.natStop i) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
        R ∘ fun ω => (h₁ ω, Sec4.stopHistory (Sec4.natStop N) (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) := by
      funext ω
      simp only [R, Function.comp_apply, Prod.mk.injEq, true_and]
      funext i
      exact (Sec4.stopHistory_natStop_stopHistory_natStop i.2.le _).symm
    have e₂ : (fun ω => (h₂ ω, fun i : Fin N =>
        Sec4.stopHistory (Sec4.natStop i) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) =
        R ∘ fun ω => (h₂ ω, Sec4.stopHistory (Sec4.natStop N) (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
      funext ω
      simp only [R, Function.comp_apply, Prod.mk.injEq, true_and]
      funext i
      exact (Sec4.stopHistory_natStop_stopHistory_natStop i.2.le _).symm
    rw [e₁, e₂, ← Measure.map_map hR (hC₁.2.1.prodMk (hXm₁ N)),
      ← Measure.map_map hR (hC₂.2.1.prodMk (hXm₂ N)), hstop N]
  -- the field and the whole sequence of stops
  have hseq := Sec4.map_prod_eq_of_forall_map_fin (P := P₁) (P' := P₂) hC₁.2.1 hXm₁ hC₂.2.1 hXm₂ hfin
  -- the killed history from the sequence of stops
  let G : DistOn upperHalfPlaneOpens × (ℕ → HistorySpace 1 1) → DistOn upperHalfPlaneOpens × HistorySpace 1 1 :=
    fun q => (q.1, Sec4.histOfStops q.2)
  have hG : Measurable G := measurable_fst.prodMk (Sec4.measurable_histOfStops.comp measurable_snd)
  have e₁ : P₁.map (fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      (P₁.map fun ω => (h₁ ω, fun n =>
        Sec4.stopHistory (Sec4.natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))).map G := by
    rw [Measure.map_map hG (hC₁.2.1.prodMk (measurable_pi_iff.2 hXm₁))]
    refine Measure.map_congr ?_
    filter_upwards [hT₁] with ω hω
    simp only [G, Function.comp_apply, Sec4.histOfStops_stopHistory hω]
  have e₂ : P₂.map (fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      (P₂.map fun ω => (h₂ ω, fun n =>
        Sec4.stopHistory (Sec4.natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))).map G := by
    rw [Measure.map_map hG (hC₂.2.1.prodMk (measurable_pi_iff.2 hXm₂))]
    refine Measure.map_congr ?_
    filter_upwards [hT₂] with ω hω
    simp only [G, Function.comp_apply, Sec4.histOfStops_stopHistory hω]
  rw [e₁, e₂, hseq]

end Laws

/-! ### Step 3: the terminal kernel -/

section Terminal

variable {κ rL rR : ℝ} {K : ℕ → HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ}

/-- There is a coupling of `SLE_κ(rL; rR)` with the original optional hull specification, on a probability space of
the universe `u`, whose driver almost surely has a continuous generating trace through its lifetime. -/
def HasTracedCoupling (κ rL rR : ℝ) : Prop :=
  ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
      ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η

/-- **The terminal kernel of one reference transfers to every coupling** (Proposition 7.3's proof: "Equality with the
reference also supplies its full retained-range Gaussian kernels"): if `Ψ` is the conditional characteristic function
of the field given the killed history in one reference coupling with a continuous trace (universe `w`), it is the
field kernel of every coupling with a continuous trace (universe `u`), given the common kernel at the integer times in
both universes. -/
theorem twoSeedTraceFieldKernel_of_reference (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hKm : ∀ n φ, Measurable fun x => K n x φ) (hK₀ : IsTraceStopKernel.{w} κ rL rR K)
    (hK : IsTraceStopKernel.{u} κ rL rR K)
    {Ω₀ : Type w} {m₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 m₀} {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ VR₀ : Fin 1 → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hC₀ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (htr₀ : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η)
    {Ψ : HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ} (hΨ : ∀ φ, Measurable fun x => Ψ x φ)
    (hΨ₀ : IsHistoryFieldKernel P₀ h₀ (killedHistory W₀ VL₀ VR₀ ζ₀) Ψ) :
    R7.TwoSeedTraceFieldKernel.{u} κ rL rR Ψ := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hC htr
  have hlaw := map_prod_killedHistory_eq hκ hL hR hKm hK₀ hK hC₀ htr₀ hC htr
  exact isHistoryFieldKernel_of_map_eq hC₀.2.1 (measurable_killedHistory hC₀.2.2.2.1) hC.2.1
    (measurable_killedHistory hC.2.2.2.1) hΨ hΨ₀ hlaw

/-- **Aux. lemma 50 at the terminal history, for one two-seed word** (the form `R7.TwoSeedTraceFieldKernel` consumed by
Proposition 7.3 and Theorem R.7): from the common kernel at the integer times (in the universes `u` and `v`), one
Borel kernel `Ψ` is the conditional characteristic function of the whole field given the killed driving history in
every coupling with a continuous trace, in both universes. A reference is taken in whichever universe has a coupling
with a continuous trace; if neither has one, both statements are vacuous. -/
theorem exists_twoSeedTraceFieldKernel (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hK : HasTraceStopKernel.{u, v} κ rL rR) :
    ∃ Ψ : HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ, (∀ φ, Measurable fun x => Ψ x φ) ∧
      R7.TwoSeedTraceFieldKernel.{u} κ rL rR Ψ ∧ R7.TwoSeedTraceFieldKernel.{v} κ rL rR Ψ := by
  obtain ⟨K, hKm, hKu, hKv⟩ := hK
  by_cases hu : HasTracedCoupling.{u} κ rL rR
  · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, htr₀⟩ := hu
    obtain ⟨Ψ, hΨ, hΨ₀⟩ := exists_isHistoryFieldKernel P₀ h₀ (killedHistory W₀ VL₀ VR₀ ζ₀)
    exact ⟨Ψ, hΨ, twoSeedTraceFieldKernel_of_reference hκ hL hR hKm hKu hKu hC₀ htr₀ hΨ hΨ₀,
      twoSeedTraceFieldKernel_of_reference hκ hL hR hKm hKu hKv hC₀ htr₀ hΨ hΨ₀⟩
  · have hu' : R7.TwoSeedTraceFieldKernel.{u} κ rL rR (fun _ _ => 0) := by
      intro Ω mΩ P hP 𝓕 W VL VR B ζ h hC htr
      exact absurd ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, htr⟩ hu
    by_cases hv : HasTracedCoupling.{v} κ rL rR
    · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, htr₀⟩ := hv
      obtain ⟨Ψ, hΨ, hΨ₀⟩ := exists_isHistoryFieldKernel P₀ h₀ (killedHistory W₀ VL₀ VR₀ ζ₀)
      refine ⟨Ψ, hΨ, ?_, twoSeedTraceFieldKernel_of_reference hκ hL hR hKm hKv hKv hC₀ htr₀ hΨ hΨ₀⟩
      intro Ω mΩ P hP 𝓕 W VL VR B ζ h hC htr
      exact absurd ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, htr⟩ hu
    · refine ⟨fun _ _ => 0, fun _ => measurable_const, hu', ?_⟩
      intro Ω mΩ P hP 𝓕 W VL VR B ζ h hC htr
      exact absurd ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, htr⟩ hv

end Terminal

/-! ### The law form: Aux. lemma 51 at the integer times gives the common kernels -/

section LawForm

variable {κ rL rR : ℝ}

/-- **Aux. lemma 51 at the integer times** (p. 242: "every coupling with the original outside-filled-hull
specification has the same full field–history joint law through `S`"), for `S = n`: any two couplings of the two-seed
word with continuous traces, on probability spaces of the universes `u` and `v`, have the same joint law of the field
and the killed history stopped at each integer time. -/
def TraceStopLawUnique (κ rL rR : ℝ) : Prop :=
  ∀ {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (𝓕₁ : Filtration ℝ≥0 m₁) (W₁ : ℝ≥0 → Ω₁ → ℝ) (VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω₁ → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ)
    (ζ₁ : Ω₁ → ℝ≥0∞) (h₁ : Ω₁ → DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ →
    (∀ᵐ ω ∂P₁, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) η) →
    ∀ {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (𝓕₂ : Filtration ℝ≥0 m₂) (W₂ : ℝ≥0 → Ω₂ → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ →
      (∀ᵐ ω ∂P₂, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω) (ζ₂ ω) η) →
      ∀ n : ℕ, P₁.map (fun ω => (h₁ ω, Sec4.stopHistory (Sec4.natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
        P₂.map (fun ω => (h₂ ω, Sec4.stopHistory (Sec4.natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω)))

/-- The kernels of one reference coupling (universe `w`) at the integer times are the kernels of every coupling
(universe `u`) whose stopped joint laws agree with the reference's. -/
theorem isTraceStopKernel_of_reference (hlaw : TraceStopLawUnique.{w, u} κ rL rR)
    {Ω₀ : Type w} {m₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 m₀} {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ VR₀ : Fin 1 → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}
    (hC₀ : IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (htr₀ : ∀ᵐ ω ∂P₀, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₀ t ω) (ζ₀ ω) η)
    {K : ℕ → HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ} (hKm : ∀ n φ, Measurable fun x => K n x φ)
    (hK₀ : ∀ n, IsHistoryFieldKernel P₀ h₀
      (fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (K n)) :
    IsTraceStopKernel.{u} κ rL rR K := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hC htr n
  have hst : Measurable (Sec4.stopHistory (nL := 1) (nR := 1) (Sec4.natStop n)) :=
    Sec4.measurable_stopHistory (Sec4.measurable_natStop n)
  exact isHistoryFieldKernel_of_map_eq hC₀.2.1 (hst.comp (measurable_killedHistory hC₀.2.2.2.1)) hC.2.1
    (hst.comp (measurable_killedHistory hC.2.2.2.1)) (hKm n) (hK₀ n)
    (hlaw P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀ hC₀ htr₀ P 𝓕 W VL VR B ζ h hC htr n)

/-- The conditional characteristic functions of one coupling at the integer times are Borel kernels (Doob–Dynkin). -/
theorem exists_stopKernels {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀)
    (h₀ : Ω₀ → DistOn upperHalfPlaneOpens) (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ VR₀ : Fin 1 → ℝ≥0 → Ω₀ → ℝ)
    (ζ₀ : Ω₀ → ℝ≥0∞) :
    ∃ K : ℕ → HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ, (∀ n φ, Measurable fun x => K n x φ) ∧
      ∀ n, IsHistoryFieldKernel P₀ h₀
        (fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₀ VL₀ VR₀ ζ₀ ω)) (K n) := by
  choose K hKm hK using fun n : ℕ => exists_isHistoryFieldKernel P₀ h₀
    (fun ω => Sec4.stopHistory (Sec4.natStop n) (killedHistory W₀ VL₀ VR₀ ζ₀ ω))
  exact ⟨K, hKm, hK⟩

/-- **Aux. lemma 51 at the integer times gives Aux. lemma 50's common kernels** (`HasTraceStopKernel`): the kernels of
one reference coupling with a continuous trace serve every coupling (the statement is vacuous without a reference). -/
theorem hasTraceStopKernel_of_traceStopLawUnique (huu : TraceStopLawUnique.{u, u} κ rL rR)
    (huv : TraceStopLawUnique.{u, v} κ rL rR) (hvv : TraceStopLawUnique.{v, v} κ rL rR) :
    HasTraceStopKernel.{u, v} κ rL rR := by
  by_cases hu : HasTracedCoupling.{u} κ rL rR
  · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, htr₀⟩ := hu
    obtain ⟨K, hKm, hK₀⟩ := exists_stopKernels P₀ h₀ W₀ VL₀ VR₀ ζ₀
    exact ⟨K, hKm, isTraceStopKernel_of_reference huu hC₀ htr₀ hKm hK₀,
      isTraceStopKernel_of_reference huv hC₀ htr₀ hKm hK₀⟩
  · have hu' : ∀ K : ℕ → HistorySpace 1 1 → TestOn upperHalfPlaneOpens → ℂ, IsTraceStopKernel.{u} κ rL rR K := by
      intro K Ω mΩ P hP 𝓕 W VL VR B ζ h hC htr
      exact absurd ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, htr⟩ hu
    by_cases hv : HasTracedCoupling.{v} κ rL rR
    · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, htr₀⟩ := hv
      obtain ⟨K, hKm, hK₀⟩ := exists_stopKernels P₀ h₀ W₀ VL₀ VR₀ ζ₀
      exact ⟨K, hKm, hu' K, isTraceStopKernel_of_reference hvv hC₀ htr₀ hKm hK₀⟩
    · refine ⟨fun _ _ _ => 0, fun _ _ => measurable_const, hu' _, ?_⟩
      intro Ω mΩ P hP 𝓕 W VL VR B ζ h hC htr
      exact absurd ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, htr⟩ hv

/-- Uniqueness of the full joint law of the field and the killed history gives Aux. lemma 51 at the integer times. -/
theorem traceStopLawUnique_of_isOptionalHullLawUnique
    (hU : IsOptionalHullLawUnique.{u, v} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR)) :
    TraceStopLawUnique.{u, v} κ rL rR := by
  intro Ω₁ m₁ P₁ _ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ hC₁ _ Ω₂ m₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ _ n
  have hR : Measurable fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 =>
      (q.1, Sec4.stopHistory (Sec4.natStop n) q.2) :=
    measurable_fst.prodMk ((Sec4.measurable_stopHistory (Sec4.measurable_natStop n)).comp measurable_snd)
  have e₁ : (fun ω => (h₁ ω, Sec4.stopHistory (Sec4.natStop n) (killedHistory W₁ VL₁ VR₁ ζ₁ ω))) =
      (fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1, Sec4.stopHistory (Sec4.natStop n) q.2)) ∘
        fun ω => (h₁ ω, killedHistory W₁ VL₁ VR₁ ζ₁ ω) := rfl
  have e₂ : (fun ω => (h₂ ω, Sec4.stopHistory (Sec4.natStop n) (killedHistory W₂ VL₂ VR₂ ζ₂ ω))) =
      (fun q : DistOn upperHalfPlaneOpens × HistorySpace 1 1 => (q.1, Sec4.stopHistory (Sec4.natStop n) q.2)) ∘
        fun ω => (h₂ ω, killedHistory W₂ VL₂ VR₂ ζ₂ ω) := rfl
  rw [e₁, e₂, ← Measure.map_map hR (hC₁.2.1.prodMk (measurable_killedHistory hC₁.2.2.2.1)),
    ← Measure.map_map hR (hC₂.2.1.prodMk (measurable_killedHistory hC₂.2.2.2.1)),
    hU P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ h₁ hC₁ P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂]

/-- **The named input holds in the non-boundary-intersecting regime** (`κ ≤ 4`, `ρ^L, ρ^R ≥ κ/2 − 2`), from the landed
Aux. lemma 23 (`Sec4.isOptionalHullLawUnique_of_admissible`). The named input is therefore needed only for the
boundary-hitting pairs (`κ < 4`) and for `κ > 4`. -/
theorem hasTraceStopKernel_of_admissible (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hL : κ / 2 - 2 ≤ rL)
    (hR : κ / 2 - 2 ≤ rR) : HasTraceStopKernel.{u, v} κ rL rR := by
  have hadm := WangWu.Theorem18.hasAdmissiblePartialSums_twoSeed hL hR
  exact hasTraceStopKernel_of_traceStopLawUnique
    (traceStopLawUnique_of_isOptionalHullLawUnique
      (Sec4.isOptionalHullLawUnique_of_admissible hκ hκ4 LP.isOrderedForceWord_twoSeed hadm))
    (traceStopLawUnique_of_isOptionalHullLawUnique
      (Sec4.isOptionalHullLawUnique_of_admissible hκ hκ4 LP.isOrderedForceWord_twoSeed hadm))
    (traceStopLawUnique_of_isOptionalHullLawUnique
      (Sec4.isOptionalHullLawUnique_of_admissible hκ hκ4 LP.isOrderedForceWord_twoSeed hadm))

end LawForm

/-! ### Step 4: both uses -/

/-- **Aux. lemma 50's field kernel for Proposition 7.3** (`Prop73Det.Prop73FieldKernelStatement`, `0 < κ < 4`,
boundary-hitting pairs) from Aux. lemma 50 at the integer times for those pairs. -/
theorem prop73FieldKernelStatement_of_aux50
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      HasTraceStopKernel.{u, u} κ rL rR) :
    Prop73Det.Prop73FieldKernelStatement.{u} := by
  intro κ hκ hκ4 rL rR hL hR hlow
  obtain ⟨Ψ, hΨ, hK, -⟩ := exists_twoSeedTraceFieldKernel hκ hL hR (h50 κ hκ hκ4 rL rR hL hR hlow)
  exact ⟨Ψ, hΨ, hK⟩

/-- **Aux. lemma 50's field kernel for Theorem R.7** (`R7.R7FieldKernelStatement`, `κ > 4`) from Aux. lemma 50 at the
integer times for the Theorem R.7 pairs. -/
theorem r7FieldKernelStatement_of_aux50
    (h50 : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      HasTraceStopKernel.{u, v} κ rL rR) :
    R7.R7FieldKernelStatement.{u, v} := by
  intro κ hκ rL rR hL hR hmax
  exact exists_twoSeedTraceFieldKernel (by linarith) hL hR (h50 κ hκ rL rR hL hR hmax)

/-- `Prop73Det.Prop73FieldKernelStatement` from the source-wide named input `Aux50TwoSeedStatement`. -/
theorem prop73FieldKernelStatement_of_aux50Statement (h50 : Aux50TwoSeedStatement.{u, u}) :
    Prop73Det.Prop73FieldKernelStatement.{u} :=
  prop73FieldKernelStatement_of_aux50 fun κ hκ _ rL rR hL hR _ => h50 κ hκ rL rR hL hR

/-- `R7.R7FieldKernelStatement` from the source-wide named input `Aux50TwoSeedStatement`. -/
theorem r7FieldKernelStatement_of_aux50Statement (h50 : Aux50TwoSeedStatement.{u, v}) :
    R7.R7FieldKernelStatement.{u, v} :=
  r7FieldKernelStatement_of_aux50 fun κ hκ rL rR hL hR _ => h50 κ (by linarith) rL rR hL hR

/-! ### Wiring into the determination statements -/

/-- **Proposition 7.3's determination** (`Determination.Prop73DeterminationStatement`) from the embedded reference, the
trace part of Proposition 7.3, and Aux. lemma 50 at the integer times for the boundary-hitting pairs
(`Prop73Det.prop73DeterminationStatement_of_reference` with its kernel input discharged). -/
theorem prop73DeterminationStatement_of_aux50 (h73t : Sec7.Prop73TraceStatement.{u})
    (href : Prop73Det.Prop73ReferenceStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      HasTraceStopKernel.{u, u} κ rL rR) :
    Determination.Prop73DeterminationStatement.{u} :=
  Prop73Det.prop73DeterminationStatement_of_reference h73t href (prop73FieldKernelStatement_of_aux50 h50)

/-- **Theorem R.7's determination consequence** (`LP.R7DeterminationStatement`) from the R.7 reference and Aux. lemma
50 at the integer times for the R.7 pairs (`R7.r7DeterminationStatement_of_inputs` with its kernel input discharged). -/
theorem r7DeterminationStatement_of_aux50 (href : R7.R7ReferenceStatement.{v})
    (h50 : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      HasTraceStopKernel.{v, u} κ rL rR) :
    LP.R7DeterminationStatement.{u} :=
  R7.r7DeterminationStatement_of_inputs href (r7FieldKernelStatement_of_aux50 h50)

end Aux50

end InteractingSLE
