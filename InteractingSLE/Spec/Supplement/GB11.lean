/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB10
import InteractingSLE.Spec.Supplement.GW4TraverseTrace

/-!
# Lemma GB11: an actual extreme pocket has no erased excursions

Packet PROVE-T14-GW4R. Supplement §13, the barrier input (GB11.0)/(GB11.B) and **Lemma GB11**
(`source/spec/p529-576.md` L637–L679, pp. 555–557):

> "Let `α_R, α_L` be the complete simple extreme flows with angles `−π/2, +π/2` from `x` to `y`. Suppose their common
> contacts have the same order along the two curves and they share no open subarc. Let `C_j` be the Jordan interiors
> bounded by their two arcs between successive common contacts […] `η([0, ∞]) ⊂ 𝓑` (GB11.B), where `η` contains both
> extreme curves in reverse first-visit order."
>
> **Lemma GB11.** "Assume the displayed barrier input. Fix a nondegenerate `C = C_j`, write its flow-oriented
> endpoints as `x_C, y_C`, and set `τ = T(y_C)`, `σ = T(x_C)` […] Then `η([τ, σ]) ⊂ C̄`, `η([0, τ]) ∩ C̄ = {y_C}`
> (GB11.1). Every nontrivial subinterval of `(τ, σ)` contains an open-`C` visit. In a fixed Jordan chart
> `ψ_C : (C; y_C, x_C) → (ℍ; 0, ∞)`, this actual segment has a continuous relative Loewner parametrization with
> strictly increasing capacity. Its relative active component is exactly the original active component intersected
> with `C`."

Theorem GW4's proof (pp. 637–638) applies exactly this argument to the actual sewn walks: "This is precisely the
interval argument of GB11", "The two arcs and that interval form the same current Jordan face as in GB11".

## Coordinates

The original domain is `(ℍ; x, y) = (ℍ; 0, ∞)`: the flows `α_R`, `α_L` run from `0` to `∞`, the counterflow from `∞`
to `0`. The counterflow is the Loewner trace `γ` of its driver `W'` in the counterflow chart `R(z) = −1/z`; its
physical point at time `t` is `−1/γ(t)` (when `γ(t) ≠ 0`; `γ(t) = 0` is the original `∞`). The Jordan chart of `C` is
a component chart `c` (`IsComponentChart`: `c.1 : C → ℍ` with `x_C ↦ 0`, `y_C ↦ ∞`), read in the counterflow chart as
`Φ = relMapC c = R ∘ c.1 ∘ R` on `relDom C = R⁻¹(C)`, so that the relative chain runs from `Φ(y_C) = 0` to
`Φ(x_C) = ∞`; then `ψ_C = R ∘ c.1`. "Its relative active component is exactly the original active component
intersected with `C`" (GB11.2) together with the relative Loewner parametrization is the hull identity
`K^{W_rel}_s = Φ(K'_{T s} ∩ R⁻¹(C))` (the relative hull is the complement of the relative active component).

## Main definitions

* `firstVisit γ p`: the first time the physical counterflow `−1/γ` visits `p` (`⊤` if never);
* `IsGB11Barrier αR αL γ`: the barrier input of GB11 (complete simple flows from `0` to `∞`; same contact order; no
  common open subarc; (GB11.B); both flows visited in strict reverse first-visit order);
* `IsGB11RelParam W' γ c C xC S Wrel T`: a **maximal** continuous relative Loewner parametrization of the traversal
  of `C` on the relative times `[0, S)`, `0 < S ≤ ∞`: continuous driver from `0`, continuous strictly increasing clock
  before the exit time `σ = T(x_C)` and tending to it, relative hulls `Φ(K'_{T s} ∩ R⁻¹(C))`;
* **`GB11Statement`** (named input, deterministic): under the barrier input and GB10's pathwise conclusion
  (`GB10.NoSimpleArcInterval`, which GB11's proof uses through Baire's theorem, `GB10.lean`), every between-component
  `C` with a component chart has a maximal relative parametrization, with (GB11.1) and the density of open-`C` visits.
  (GB11 holds almost surely: GB10 almost surely, then this deterministic statement.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Theorem14

namespace GB11

open GW4Traverse

/-- The **first visit** of `p` by the physical counterflow `t ↦ −1/γ(t)` (the source's `T(p)`), `⊤` if `p` is
never visited (in particular for `p = 0`, the original target, and for the original source `∞`). -/
def firstVisit (γ : ℝ≥0 → ℂ) (p : ℂ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : γ t ≠ 0 ∧ -(γ t)⁻¹ = p), (t : ℝ≥0∞)

/-- `α` is a **complete simple flow** from `x = 0` to `y = ∞`: continuous, injective, from `0`, in `ℍ̄`, proper. -/
def IsCompleteSimpleFlow (α : ℝ≥0 → ℂ) : Prop :=
  Continuous α ∧ Function.Injective α ∧ α 0 = 0 ∧ (∀ t, α t ∈ Hbar) ∧ Tendsto (fun t => ‖α t‖) atTop atTop

/-- **The barrier input of GB11** (supplement pp. 555–556, "The explicit barrier input for the next two lemmas"),
for the extreme flows `α_R`, `α_L` and the counterflow trace `γ` (counterflow chart):
* both are complete simple flows from `0` to `∞`;
* "their common contacts have the same order along the two curves";
* "they share no open subarc" (no nontrivial subarc of `α_R` lies on `α_L`);
* (GB11.B) every finite physical counterflow point lies in `𝓑 = α_R ∪ α_L ∪ ⋃_j C_j`, the `C_j` being the
  components between the two curves (`betweenComponents`, the frozen carrier; GB13a identifies the two descriptions);
* "`η` contains both extreme curves in reverse first-visit order": along each flow, a point farther from `x = 0` is
  visited strictly earlier (the counterflow comes from `y = ∞`), and every point other than `x` is visited. -/
def IsGB11Barrier (αR αL γ : ℝ≥0 → ℂ) : Prop :=
  IsCompleteSimpleFlow αR ∧ IsCompleteSimpleFlow αL ∧
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) ∧
    (∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL) ∧
    (∀ t : ℝ≥0, γ t ≠ 0 → -(γ t)⁻¹ ∈ range αR ∪ range αL ∪ ⋃₀ betweenComponents (range αR) (range αL)) ∧
    (∀ s s' : ℝ≥0, 0 < s → s < s' → firstVisit γ (αR s') < firstVisit γ (αR s)) ∧
    ∀ s s' : ℝ≥0, 0 < s → s < s' → firstVisit γ (αL s') < firstVisit γ (αL s)

/-- **A maximal continuous relative Loewner parametrization of the traversal of `C`** on the relative times
`[0, S)`, `0 < S ≤ ∞` (GB11: "this actual segment has a continuous relative Loewner parametrization with strictly
increasing capacity. Its relative active component is exactly the original active component intersected with `C`"):
the relative driver `W_rel` is continuous before `S` with `W_rel 0 = 0`; the clock `T` (relative time ↦ ambient time)
is continuous and strictly increasing before `S`, stays before the exit time `σ = T(x_C)` and tends to it as `s → S`
(the parametrization exhausts the traversal); the relative hulls are `K^{W_rel}_s = Φ(K'_{T s} ∩ R⁻¹(C))`. -/
def IsGB11RelParam (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (c : Chart) (C : Set ℂ) (xC : ℂ) (S : ℝ≥0∞)
    (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0) : Prop :=
  0 < S ∧ ContinuousOn Wrel {s | (s : ℝ≥0∞) < S} ∧ Wrel 0 = 0 ∧ StrictMonoOn T {s | (s : ℝ≥0∞) < S} ∧
    ContinuousOn T {s | (s : ℝ≥0∞) < S} ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < S → (T s : ℝ≥0∞) < firstVisit γ xC) ∧
    Tendsto (fun s : ℝ≥0 => (T s : ℝ≥0∞)) (comap (fun s : ℝ≥0 => (s : ℝ≥0∞)) (𝓝[<] S))
      (𝓝 (firstVisit γ xC)) ∧
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < S → QuantumZipper.fwdHull (fun r : ℝ => Wrel r.toNNReal) s =
      relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (T s) ∩ relDom C)

/-- **Named input: Lemma GB11** (supplement pp. 556–557, `source/spec/p529-576.md` L651–L679), deterministic form.
Let `W'` be a continuous driver from `0` with a generating trace `γ` on `[0, ∞]` (the counterflow in its chart
`R(z) = −1/z`), satisfying GB10's pathwise conclusion, and let `α_R`, `α_L` satisfy the barrier input. For every
between-component `C` of the two flows with a component chart `c` (exit `x_C`, the boundary value of `c.2.1` at `0`):
there is a maximal continuous relative Loewner parametrization `(S, W_rel, T)` of the traversal (`IsGB11RelParam`), with
`T 0 = τ` the entry time, such that
* (GB11.1), second half: before `τ` the physical counterflow avoids `C̄` ("`η([0, τ]) ∩ C̄ = {y_C}`", `τ` being the
  first visit of `y_C`);
* (GB11.1), first half: between `τ` and `σ` it stays in `C̄`;
* every nontrivial subinterval of `(τ, σ)` contains an open-`C` visit.

Source proof (not formalized here): the only available open pocket (reverse first visits; the other pockets are
inaccessible or already filled); Baire and GB10 on the two compact simple ranges (proved form:
`GB10.NoSimpleArcInterval.not_image_subset_union_range`); the active component `D_s ∩ C = E_s` (GB11.2) by
active access of the unvisited incoming prefix; the current Jordan face `F_s = g_s(E_s)`; relative continuity by the
continuous-trace Loewner criterion (Aux. 41, Proposition 6.12) and strict growth by Baire, strict ambient growth and
GB10. -/
def GB11Statement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, IsGB11Barrier αR αL γ →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ c : Chart, IsComponentChart (range αR) (range αL) C c →
    ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) →
      ∃ (S : ℝ≥0∞) (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0), IsGB11RelParam W' γ c C xC S Wrel T ∧
        (∀ t : ℝ≥0, t < T 0 → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) ∧
        (∀ t : ℝ≥0, T 0 ≤ t → (t : ℝ≥0∞) < firstVisit γ xC → γ t ≠ 0 → -(γ t)⁻¹ ∈ closure C) ∧
        ∀ a b : ℝ≥0, T 0 ≤ a → a < b → (b : ℝ≥0∞) < firstVisit γ xC →
          ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C

/-! ### Elementary facts -/

/-- A time at which `p` is visited bounds its first visit. -/
theorem firstVisit_le {γ : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : γ t ≠ 0) : firstVisit γ (-(γ t)⁻¹) ≤ t :=
  iInf₂_le t ⟨ht, rfl⟩

/-- Every point of a complete simple flow other than `x = 0` is visited, under the barrier input. -/
theorem IsGB11Barrier.firstVisit_lt_top_R {αR αL γ : ℝ≥0 → ℂ} (h : IsGB11Barrier αR αL γ) {s : ℝ≥0} (hs : 0 < s) :
    firstVisit γ (αR s) < ⊤ :=
  (h.2.2.2.2.2.1 (s / 2) s (half_pos hs) (NNReal.half_lt_self hs.ne')).trans_le le_top

/-- With `S = ⊤`, the relative parametrization is global: continuous driver and clock on `[0, ∞)`, strictly
increasing clock and the hull identity at every relative time. -/
theorem IsGB11RelParam.global {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {c : Chart} {C : Set ℂ} {xC : ℂ}
    {Wrel : ℝ≥0 → ℝ} {T : ℝ≥0 → ℝ≥0} (h : IsGB11RelParam W' γ c C xC ⊤ Wrel T) :
    Continuous Wrel ∧ Wrel 0 = 0 ∧ StrictMono T ∧ Continuous T ∧
      ∀ s : ℝ≥0, QuantumZipper.fwdHull (fun r : ℝ => Wrel r.toNNReal) s =
        relMapC c '' (QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (T s) ∩ relDom C) := by
  obtain ⟨-, hWc, hW0, hTm, hTc, -, -, hK⟩ := h
  have hU : {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun s => ENNReal.coe_lt_top
  rw [hU] at hWc hTm hTc
  exact ⟨continuousOn_univ.1 hWc, hW0, strictMonoOn_univ.1 hTm, continuousOn_univ.1 hTc,
    fun s => hK s ENNReal.coe_lt_top⟩

end GB11

end Theorem14

end InteractingSLE
