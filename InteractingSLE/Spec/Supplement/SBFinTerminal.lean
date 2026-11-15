/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB1End
import InteractingSLE.Spec.Supplement.SBTail2EndFlow
import InteractingSLE.Spec.Supplement.S9CTip

/-!
# The terminal-endpoint step of Lemmas S6 and SB1: the clearance case

Packet PROVE-T14-SBFIN. Lemmas S6 (supplement p. 583) and SB1 (p. 630) extend W5's strict-prefix ordered
completions through finite terminal endpoints:

> "Now adjoin a finite terminal endpoint of either prefix while the other stop is strict. If it misses the other
> prefix, compact clearance and W4 extend an earlier ordered pair through that endpoint. If it meets the other
> prefix, it is an exterior original-real point, and G15 supplies actual proper completions through it [...]
> Adjoin the other finite endpoint in the same way." (`source/spec/p625-671.md` L111.)

The landed `Supp9.ExtendsWithoutNewContact` (Lemma W4) only reaches strict available times. This file proves:

* `ExtendsWithoutNewContactLE`, `extendsWithoutNewContactLE_of_slits`: Lemma W4 through finite terminal endpoints,
  pathwise, from slit completions at every available time **including** a finite lifetime (the same deterministic
  core `Supp9B.hasOrderedProperCompletions_extend_{left,right}_of_access` with the proved tip-access input);
* `ae_extendsWithoutNewContactLE_of_isFlowLine`: for two frozen flow lines (`0 < κ < 4`, ordered seeds) this holds
  almost surely, using the terminal slit completions `SB.End.ae_forall_exists_slitCompletion_of_isFlowLine`;
* `exists_lt_forall_Icc_notMem`: compact clearance before a terminal endpoint;
* `TerminalContactCompletionStatement`: the remaining case of the endpoint step (a terminal endpoint that lies on
  the other prefix, Lemma G15's case), stated with exactly the hypotheses of `TerminalEndpointStatement` plus
  positive lifetimes;
* **`terminalEndpointPosStatement_of_contact`**: the endpoint step (`TerminalEndpointPosStatement`, i.e.
  `TerminalEndpointStatement` for positive lifetimes) from the contact case alone — the clearance case is proved;
* `sb1Statement_of_inputs_pos`, `s6Statement_of_inputs_pos`: SB1 and S6 from W5, their middle exclusions and the
  positive-lifetime endpoint step (both lemmas assume nonempty initial lifetimes).

`TerminalEndpointStatement` itself (no positivity) is not claimed: at a zero lifetime there is no strict prefix to
extend, and its consumers only use positive lifetimes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fin

open Supp9B

/-! ### Lemma W4 through finite terminal endpoints -/

/-- **Lemma W4 with terminal endpoints** (supplement p. 532, "Extend one or both original simple Loewner prefixes,
within their available lifetimes, without adding any new mutual contact"): `Supp9.ExtendsWithoutNewContact` with
`a' ≤ ζ₁`, `c' ≤ ζ₂` (a finite lifetime is an available endpoint). -/
def ExtendsWithoutNewContactLE (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∀ a a' c c' : ℝ≥0, a ≤ a' → (a' : ℝ≥0∞) ≤ ζ₁ → c ≤ c' → (c' : ℝ≥0∞) ≤ ζ₂ →
    HasOrderedProperCompletions α a β c →
    (∀ x ∈ Icc 0 a', ∀ y ∈ Icc 0 c', α x = β y → x ≤ a ∧ y ≤ c) →
    (a < a' → α a ∉ β '' Icc 0 c) → (c < c' → β c ∉ α '' Icc 0 a) →
    HasOrderedProperCompletions α a' β c'

/-- **Lemma W4 through terminal endpoints, pathwise**: two curves from real seeds `β(0) ≤ α(0)` whose available
prefixes, including the terminal ones, have slit completions. The proof of `extendsWithoutNewContact_of_slits`
with `≤` in place of `<`; the tip-access input is the proved `Supp9B.w4TipAccessStatement`. -/
theorem extendsWithoutNewContactLE_of_slits {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re)
    (hslα : ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ₁ → ∃ S, IsSlitCompletion α a S)
    (hslβ : ∀ c : ℝ≥0, (c : ℝ≥0∞) ≤ ζ₂ → ∃ S, IsSlitCompletion β c S) :
    ExtendsWithoutNewContactLE α ζ₁ β ζ₂ := by
  intro a a' c c' haa' ha'ζ hcc' hc'ζ hE hcont hα hβ
  have hcζ : (c : ℝ≥0∞) ≤ ζ₂ := le_trans (by exact_mod_cast hcc') hc'ζ
  have h1 : HasOrderedProperCompletions α a' β c := by
    rcases haa'.lt_or_eq with hlt | heq
    · obtain ⟨S, hS⟩ := hslα a' ha'ζ
      obtain ⟨Sβ, hSβ⟩ := hslβ c hcζ
      refine hasOrderedProperCompletions_extend_left_of_access w4TipAccessStatement hE h0 hβ0 hseed hlt
        hS hSβ ?_
      intro x hx y hy hxy
      have hxa := (hcont x ⟨zero_le, hx.2⟩ y ⟨zero_le, hy.2.trans hcc'⟩ hxy).1
      have hxa' : x = a := le_antisymm hxa hx.1
      exact hα hlt ⟨y, hy, by rw [← hxa']; exact hxy.symm⟩
    · rw [← heq]; exact hE
  rcases hcc'.lt_or_eq with hlt | heq
  · obtain ⟨Sα, hSα⟩ := hslα a' ha'ζ
    obtain ⟨Sβ, hSβ⟩ := hslβ c' hc'ζ
    refine hasOrderedProperCompletions_extend_right_of_access w4TipAccessStatement h1 h0 hβ0 hseed hlt
      hSα hSβ ?_
    intro y hy x hx hyx
    have hc := hcont x ⟨zero_le, hx.2⟩ y ⟨zero_le, hy.2⟩ hyx.symm
    have hyc : y = c := le_antisymm hc.2 hy.1
    exact hβ hlt ⟨x, ⟨zero_le, hc.1⟩, by rw [← hyc]; exact hyx.symm⟩
  · rw [← heq]; exact h1

/-- **Lemma W4 through terminal endpoints for two flow lines** (`0 < κ < 4`, seeds `x₂ ≤ x₁`): almost surely. -/
theorem ae_extendsWithoutNewContactLE_of_isFlowLine {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ExtendsWithoutNewContactLE (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) := by
  filter_upwards [End.ae_forall_exists_slitCompletion_of_isFlowLine hκ hκ4 hη₁,
    End.ae_forall_exists_slitCompletion_of_isFlowLine hκ hκ4 hη₂,
    Supp9.ae_apply_zero_of_isFlowLine hη₁, Supp9.ae_apply_zero_of_isFlowLine hη₂] with ω h1 h2 h10 h20
  exact extendsWithoutNewContactLE_of_slits (by rw [h10]; simp) (by rw [h20]; simp)
    (by rw [h10, h20]; simpa using hx) h1 h2

/-! ### Compact clearance before a terminal endpoint -/

/-- **Compact clearance** ("compact clearance and W4 extend an earlier ordered pair through that endpoint"): if a
curve is continuous on `[0, a]` with `0 < a` and its endpoint `α a` misses a closed set `K`, then a whole final
segment `α([a₀, a])`, `a₀ < a`, misses `K`. -/
theorem exists_lt_forall_Icc_notMem {α : ℝ≥0 → ℂ} {a : ℝ≥0} (ha : 0 < a)
    (hα : ContinuousOn α (Icc 0 a)) {K : Set ℂ} (hK : IsClosed K) (haK : α a ∉ K) :
    ∃ a₀ < a, ∀ x ∈ Icc a₀ a, α x ∉ K := by
  have h1 : α ⁻¹' Kᶜ ∈ 𝓝[Icc 0 a] a :=
    (hα a ⟨zero_le, le_rfl⟩).preimage_mem_nhdsWithin (hK.isOpen_compl.mem_nhds haK)
  have hI : Icc (0 : ℝ≥0) a = Iic a := by
    ext x
    simp only [mem_Icc, mem_Iic, zero_le, true_and]
  rw [hI] at h1
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' ha).1 h1
  obtain ⟨a₀, hla₀, ha₀⟩ := exists_between (show l < a from hl)
  exact ⟨a₀, ha₀, fun x hx => hsub ⟨hla₀.trans_le hx.1, hx.2⟩⟩

/-- A slit completion at `a` makes the curve continuous on `[0, a]`. -/
theorem continuousOn_Icc_of_isSlitCompletion {γ S : ℝ≥0 → ℂ} {a : ℝ≥0} (h : IsSlitCompletion γ a S) :
    ContinuousOn γ (Icc 0 a) :=
  h.1.1.continuousOn.congr fun t ht => (h.1.2.2.2.2 t ht.2).symm

/-- A slit completion at `a` makes the prefix `γ([0, a])` compact. -/
theorem isCompact_image_of_isSlitCompletion {γ S : ℝ≥0 → ℂ} {a : ℝ≥0} (h : IsSlitCompletion γ a S) :
    IsCompact (γ '' Icc 0 a) :=
  isCompact_Icc.image_of_continuousOn (continuousOn_Icc_of_isSlitCompletion h)

/-! ### The endpoint step from its contact case -/

/-- **The endpoint step of S6 and SB1 for nonempty lifetimes**: `TerminalEndpointStatement` with the hypotheses
`0 < ζ₁`, `0 < ζ₂` almost surely, which both S6 and SB1 assume ("with nonempty initial lifetimes"). -/
def TerminalEndpointPosStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      (∀ᵐ ω ∂P, 0 < ζ₁ ω) → (∀ᵐ ω ∂P, 0 < ζ₂ ω) →
      ∀ᵐ ω ∂P, (∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
          HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) →
        TerminalContactsExterior (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) x₂ x₁ →
        ∀ a c : ℝ≥0, (a : ℝ≥0∞) ≤ ζ₁ ω → (c : ℝ≥0∞) ≤ ζ₂ ω → HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c

/-- The landed endpoint step implies its positive-lifetime form. -/
theorem terminalEndpointPosStatement_of_terminalEndpoint (hE : TerminalEndpointStatement.{u}) :
    TerminalEndpointPosStatement.{u} :=
  fun κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ _ _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ _ _ =>
    hE κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂

/-- **The contact case of the endpoint step** (Lemma G15's case, supplement pp. 508–509: "If it meets the other
prefix, it is an exterior original-real point, and G15 supplies actual proper completions through it"): in the
setting of `TerminalEndpointPosStatement`, the ordered proper completions at every pair of available prefixes one of
whose finite terminal endpoints lies on the other prefix. **Not proved here.** -/
def TerminalContactCompletionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      (∀ᵐ ω ∂P, 0 < ζ₁ ω) → (∀ᵐ ω ∂P, 0 < ζ₂ ω) →
      ∀ᵐ ω ∂P, (∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
          HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) →
        TerminalContactsExterior (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) x₂ x₁ →
        ∀ a c : ℝ≥0, (a : ℝ≥0∞) ≤ ζ₁ ω → (c : ℝ≥0∞) ≤ ζ₂ ω →
          (((a : ℝ≥0∞) = ζ₁ ω ∧ η₁ ω a ∈ η₂ ω '' Icc 0 c) ∨
            ((c : ℝ≥0∞) = ζ₂ ω ∧ η₂ ω c ∈ η₁ ω '' Icc 0 a)) →
          HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c

/-- Clearance of one path at an available stop: a strict stop is its own clear start; at a finite terminal endpoint
missing the compact other prefix `K`, a final segment misses `K`. -/
theorem exists_clear_start {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hz : 0 < ζ)
    (hsl : ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ → ∃ S, IsSlitCompletion α a S) {K : Set ℂ} (hK : IsClosed K)
    {a : ℝ≥0} (ha : (a : ℝ≥0∞) ≤ ζ) (hend : (a : ℝ≥0∞) = ζ → α a ∉ K) :
    ∃ a₀ ≤ a, (a₀ : ℝ≥0∞) < ζ ∧ (a₀ < a → ∀ x ∈ Icc a₀ a, α x ∉ K) := by
  rcases ha.lt_or_eq with hlt | heq
  · exact ⟨a, le_rfl, hlt, fun h => absurd h (lt_irrefl a)⟩
  · have hapos : 0 < a := by
      have h0 : (0 : ℝ≥0∞) < a := heq ▸ hz
      exact_mod_cast h0
    obtain ⟨S, hS⟩ := hsl a ha
    obtain ⟨a₀, ha₀, hclr⟩ :=
      exists_lt_forall_Icc_notMem hapos (continuousOn_Icc_of_isSlitCompletion hS) hK (hend heq)
    exact ⟨a₀, ha₀.le, lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ha₀) ha, fun _ => hclr⟩

/-- **The endpoint step of S6 and SB1 from its contact case.** The clearance case ("If it misses the other prefix,
compact clearance and W4 extend an earlier ordered pair through that endpoint [...] Adjoin the other finite endpoint
in the same way") is proved: both terminal endpoints that miss the other prefix are cleared at once, and Lemma W4
through terminal endpoints extends the strict ordered pair. -/
theorem terminalEndpointPosStatement_of_contact (hG : TerminalContactCompletionStatement.{u}) :
    TerminalEndpointPosStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hp₁ hp₂
  filter_upwards [hG κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hp₁ hp₂,
    ae_extendsWithoutNewContactLE_of_isFlowLine hκ hκ4 hx hη₁ hη₂,
    End.ae_forall_exists_slitCompletion_of_isFlowLine hκ hκ4 hη₁,
    End.ae_forall_exists_slitCompletion_of_isFlowLine hκ hκ4 hη₂, hp₁, hp₂]
    with ω hg hW4 hs₁ hs₂ hz₁ hz₂ hstrict hext a c ha hc
  by_cases hcon : ((a : ℝ≥0∞) = ζ₁ ω ∧ η₁ ω a ∈ η₂ ω '' Icc 0 c) ∨
      ((c : ℝ≥0∞) = ζ₂ ω ∧ η₂ ω c ∈ η₁ ω '' Icc 0 a)
  · exact hg hstrict hext a c ha hc hcon
  have hca : (a : ℝ≥0∞) = ζ₁ ω → η₁ ω a ∉ η₂ ω '' Icc 0 c := fun h1 h2 => hcon (Or.inl ⟨h1, h2⟩)
  have hcc : (c : ℝ≥0∞) = ζ₂ ω → η₂ ω c ∉ η₁ ω '' Icc 0 a := fun h1 h2 => hcon (Or.inr ⟨h1, h2⟩)
  obtain ⟨Sα, hSα⟩ := hs₁ a ha
  obtain ⟨Sβ, hSβ⟩ := hs₂ c hc
  obtain ⟨a₀, ha₀a, ha₀ζ, hclr₁⟩ :=
    exists_clear_start hz₁ hs₁ (isCompact_image_of_isSlitCompletion hSβ).isClosed ha hca
  obtain ⟨c₀, hc₀c, hc₀ζ, hclr₂⟩ :=
    exists_clear_start hz₂ hs₂ (isCompact_image_of_isSlitCompletion hSα).isClosed hc hcc
  refine hW4 a₀ a c₀ c ha₀a ha hc₀c hc (hstrict a₀ c₀ ha₀ζ hc₀ζ) ?_ ?_ ?_
  · intro x hx y hy hxy
    constructor
    · by_contra hxa
      rw [not_le] at hxa
      exact hclr₁ (hxa.trans_le hx.2) x ⟨hxa.le, hx.2⟩ ⟨y, hy, hxy.symm⟩
    · by_contra hyc
      rw [not_le] at hyc
      exact hclr₂ (hyc.trans_le hy.2) y ⟨hyc.le, hy.2⟩ ⟨x, hx, hxy⟩
  · intro hlt hmem
    exact hclr₁ hlt a₀ ⟨le_rfl, ha₀a⟩ (image_mono (Icc_subset_Icc le_rfl hc₀c) hmem)
  · intro hlt hmem
    exact hclr₂ hlt c₀ ⟨le_rfl, hc₀c⟩ (image_mono (Icc_subset_Icc le_rfl ha₀a) hmem)

/-- **Lemma SB1** from W5, its middle exclusion and the positive-lifetime endpoint step. -/
theorem sb1Statement_of_inputs_pos (hW5 : Theorem15.W5Statement.{u}) (hM : SB1MiddleStatement.{u})
    (hE : TerminalEndpointPosStatement.{u}) : SB1Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ P _ h hh u v ψ huv hψ hL hH ηL ηU ζL ζU hηL hηU hζL hζU
  filter_upwards [hW5 κ hκ hκ4 b jumps hb v u (-(Real.pi / 2)) ψ huv.le hψ P h hh ηL ηU ζL ζU hηL hηU,
    hM κ hκ hκ4 b jumps hb P h hh u v ψ huv hψ hL hH ηL ηU ζL ζU hηL hηU hζL hζU,
    hE κ hκ hκ4 b jumps hb v u (-(Real.pi / 2)) ψ huv.le hψ P h hh ηL ηU ζL ζU hηL hηU hζL hζU]
    with ω h5 hm he
  exact he h5 hm

/-- **Lemma S6** from W5, its middle exclusion and the positive-lifetime endpoint step. -/
theorem s6Statement_of_inputs_pos (hW5 : Theorem15.W5Statement.{u}) (hM : S6MiddleStatement.{u})
    (hE : TerminalEndpointPosStatement.{u}) : S6Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hL hR Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hζ₁ hζ₂
  filter_upwards [hW5 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hM κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hL hR P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hζ₁ hζ₂,
    hE κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hζ₁ hζ₂] with ω h5 hm he
  exact he h5 hm

end InteractingSLE.Theorem14.SB.Fin
