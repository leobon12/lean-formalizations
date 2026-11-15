/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Spec.AuditFix.MarkovMain

/-!
# Theorem 2.2, the Markov sentence (external audit, item "Markov interface", priority 3)

Miller–Sheffield, Theorem 2.2 (p. 40; Specification p. 21) ends: "Under this law, the values `W_t`, `B_t`, and
`V_t^{i,q}` taken together are a continuous multidimensional Markovian process indexed by `t`." The frozen
Theorem 2.2 exports existence (`exists_isIntegratedSLEEvolution`) and uniqueness in law of the killed state
(`IsIntegratedSLEEvolution.measure_killedState_eq`). This file states and proves the Markov sentence.

Conventions (all explicit in the statements):

* **State.** `X_t = (W_t, V^L_t, V^R_t, B_t) ∈ ℝ × ℝ^{nL} × ℝ^{nR} × ℝ`, in the order of the frozen uniqueness theorem.
* **Killing.** The state lives before the lifetime `ζ` (the continuation threshold `T_*`). A future event is
  "alive at `T + t_j` and `X_{T+t_j} ∈ K_j` for `j = 1, …, n`", i.e. `t_j < ζ − T` and `X_{T+t_j} ∈ K_j`; these
  events form the generating π-system of the killed future, as in the frozen uniqueness theorem. Conditioning
  events lie in `{T < ζ}` (the process is alive at `T`); on `{ζ ≤ T}` the killed future is the cemetery and every
  such event with `n ≥ 1` is empty, so for `n ≥ 1` every `A ∈ 𝓕_T` is allowed, with the integral over
  `A ∩ {T < ζ}` (last clause of the strong form).
* **Kernel.** One kernel `Q` for all initial words with the given weights (time-homogeneous: it depends on neither
  the time nor the evolution). `Q n ts K x` is the probability, for the process started at the state `x`, of the
  event above with `T = 0`. The process started at `x = (w, w + xL, w + xR, b)` is an integrated evolution from the
  relative word `(xL, xR)`, translated by `w` in the driver and force coordinates and by `b` in the Brownian
  coordinate (law clause). `Q` is measurable on the states with separated force points (`V^{i,L} < V^{j,R}`),
  which are the only states the process visits at positive times. The only other state it visits is its
  deterministic initial state.
* **Filtration.** The evolution's own filtration `𝓕` (Definition 2.1: `B` is an `𝓕`-Brownian motion and `W, V` are
  `𝓕`-adapted before `ζ`); the deterministic-time statement also gives the natural filtration of the killed state.
* **Time zero.** No restriction to `T > 0` or to separated words. At `T = 0` and on events of `𝓕₀` the statement
  holds for every word, including the entrance words `0⁻, 0⁺`, by uniqueness in law under `P[·|A]`, `A ∈ 𝓕₀`.

Statements:

* `IntegratedSLEStrongMarkovStatement`: law, measurability, continuity, strong Markov at finite stopping times
  (events of `𝓕_T` inside `{T < ζ}`, and every event of `𝓕_T` for `n ≥ 1`);
* `IntegratedSLEMarkovStatement`: law, measurability, the time-zero law, simple Markov at deterministic times for `𝓕`
  and for the natural filtration;
* `IntegratedSLEIncrementStrongMarkovStatement`: the same strong Markov property for the increments
  `(W_{T+·} − W_T, V_{T+·} − W_T, B_{T+·} − B_T)` with a kernel of the relative word `V_T − W_T`; this is the landed
  restart law, with the restriction to `T > 0` or separated words removed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace AuditFix

/-- **Theorem 2.2, the Markov sentence: the strong Markov property of the state `(W, V^L, V^R, B)`**
(Specification p. 21; Miller–Sheffield p. 40). Fix `a > 0` (the source's `κ`) and the weights `ρ`. There is one
kernel `Q`, assigning to times `t_1, …, t_n`, Borel sets `K_1, …, K_n` of states and a state `x` a number
`Q n ts K x`, such that:

* **(law)** `Q` is the killed-state law of the process started at the state: for every ordered word `(xL; xR)`,
  every `w, b` and every integrated evolution from `(xL; xR)`,
  `Q(w, w + xL, w + xR, b) = P[t_j < ζ and (w + W, w + V^L, w + V^R, b + B)_{t_j} ∈ K_j for all j]`;
* **(measurable)** `Q` is measurable on the states with separated force points;
* **(continuous)** every integrated evolution has almost surely continuous state paths before its lifetime;
* **(strong Markov)** for every integrated evolution (of every word with these weights, on every filtered
  probability space), every finite stopping time `T` of its filtration `𝓕` and every `A ∈ 𝓕_T` with `T < ζ` on
  `A`: `P(A ∩ {t_j < ζ − T and X_{T+t_j} ∈ K_j for all j}) = ∫_A Q(X_T) dP`;
* **(strong Markov, every event of `𝓕_T`)** the killed-state convention: for `n ≥ 1` and every `A ∈ 𝓕_T`, the same
  probability is `∫_{A ∩ {T < ζ}} Q(X_T) dP` (on `{ζ ≤ T}` the killed future is the cemetery). -/
def IntegratedSLEStrongMarkovStatement : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    ∃ Q : ∀ n : ℕ, (Fin n → ℝ≥0) → (Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) →
        ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ → ℝ≥0∞,
      -- (law)
      (∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ), IsOrderedForceWord xL xR → ∀ (w b : ℝ)
        {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
        {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
          (∀ j, MeasurableSet (K j)) →
          Q n ts K (w, (fun i => w + xL i), (fun j => w + xR j), b) =
            P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
              (w + W (ts j) ω, (fun i => w + VL i (ts j) ω), (fun i => w + VR i (ts j) ω),
                b + B (ts j) ω) ∈ K j}) ∧
      -- (measurable)
      (∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
        (∀ j, MeasurableSet (K j)) →
        Measurable fun x : {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ // ∀ i j, x.2.1 i < x.2.2.1 j} =>
          Q n ts K x.1) ∧
      -- (continuous)
      (∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ContinuousOn (fun t => (W t ω, (fun i => VL i t ω), (fun i => VR i t ω), B t ω))
          {t | (t : ℝ≥0∞) < ζ ω}) ∧
      -- (strong Markov)
      (∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (A : Set Ω),
          MeasurableSet[hT.measurableSpace] A → (∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω) →
          ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (K j)) →
            P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
                (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
                  B (T ω + ts j) ω) ∈ K j}) =
              ∫⁻ ω in A, Q n ts K (W (T ω) ω, (fun i => VL i (T ω) ω), (fun i => VR i (T ω) ω),
                B (T ω) ω) ∂P) ∧
      -- (strong Markov, every event of `𝓕_T`: the killed state is the cemetery from `ζ` on)
      ∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (A : Set Ω),
          MeasurableSet[hT.measurableSpace] A →
          ∀ (n : ℕ), 0 < n →
          ∀ (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (K j)) →
            P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
                (W (T ω + ts j) ω, (fun i => VL i (T ω + ts j) ω), (fun i => VR i (T ω + ts j) ω),
                  B (T ω + ts j) ω) ∈ K j}) =
              ∫⁻ ω in A ∩ {ω | (T ω : ℝ≥0∞) < ζ ω}, Q n ts K (W (T ω) ω, (fun i => VL i (T ω) ω),
                (fun i => VR i (T ω) ω), B (T ω) ω) ∂P

/-- **Theorem 2.2, the Markov sentence, proved.** The kernel is `Markov.markovKer`: the measurable translated
canonical Wiener functional on separated states (Lusin–Souslin, `Markov.measurableSet_lawSetP`), the reference law
of frozen Theorem 2.2 elsewhere. Strong Markov: on `{T > 0}` the restart identity for the full state
(`Markov.measure_restart_state`, from the landed restart law's proof), on `{T = 0}` independence from `𝓕₀` by
uniqueness in law under the conditional measures (`Markov.measure_inter_killedState`). -/
theorem integratedSLEStrongMarkov_holds : IntegratedSLEStrongMarkovStatement.{u} := by
  intro a ha nL nR ρL ρR
  refine ⟨Markov.markovKer a ρL ρR, ?_, ?_, ?_, ?_, ?_⟩
  · intro xL xR hF w b Ω mΩ P 𝓕 W VL VR B ζ hE n ts K hK
    exact Markov.markovKer_eq ha (Markov.relWord_shift w b xL xR) hF hE ts hK
  · intro n ts K hK
    exact Markov.measurable_markovKer_sep ts hK
  · intro xL xR Ω mΩ P 𝓕 W VL VR B ζ hE
    exact Markov.ae_continuousOn_state hE
  · intro xL xR Ω mΩ P 𝓕 W VL VR B ζ hE T hT A hA hAT n ts K hK
    exact Markov.measure_markov ha hE hT hA hAT ts hK
  · intro xL xR Ω mΩ P 𝓕 W VL VR B ζ hE T hT A hA n hn ts K hK
    exact Markov.measure_markov_of_pos ha hE hT hA hn ts hK

/-- **Theorem 2.2, the Markov sentence: the simple Markov property at deterministic times**, for the evolution's
filtration and for the natural filtration of the killed state, with the time-zero law. With the kernel `Q` of the
strong form (the same law and measurability clauses):

* **(time zero)** the killed-state law of every evolution from an ordered word `(xL; xR)` is `Q` at its initial
  state `(0, xL, xR, 0)` (also for entrance words such as `0⁻, 0⁺`);
* **(Markov, `𝓕`)** for every deterministic `s ≥ 0` (including `s = 0`) and every `A ∈ 𝓕_s` with `s < ζ` on `A`:
  `P(A ∩ {t_j < ζ − s and X_{s+t_j} ∈ K_j for all j}) = ∫_A Q(X_s) dP`;
* **(Markov, natural filtration)** the same for every `A` in the σ-algebra generated by the killed state up to time
  `s`, that is by the events `{r < ζ, (W, V^L, V^R, B)_r ∈ D}`, `r ≤ s`, `D` Borel. -/
def IntegratedSLEMarkovStatement : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    ∃ Q : ∀ n : ℕ, (Fin n → ℝ≥0) → (Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) →
        ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ → ℝ≥0∞,
      -- (law)
      (∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ), IsOrderedForceWord xL xR → ∀ (w b : ℝ)
        {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
        {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
          (∀ j, MeasurableSet (K j)) →
          Q n ts K (w, (fun i => w + xL i), (fun j => w + xR j), b) =
            P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
              (w + W (ts j) ω, (fun i => w + VL i (ts j) ω), (fun i => w + VR i (ts j) ω),
                b + B (ts j) ω) ∈ K j}) ∧
      -- (measurable)
      (∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
        (∀ j, MeasurableSet (K j)) →
        Measurable fun x : {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ // ∀ i j, x.2.1 i < x.2.2.1 j} =>
          Q n ts K x.1) ∧
      -- (time zero)
      (∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsOrderedForceWord xL xR → IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
          (∀ j, MeasurableSet (K j)) →
          P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
              (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ K j} =
            Q n ts K (0, xL, xR, 0)) ∧
      -- (Markov, the evolution's filtration)
      (∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[𝓕 s] A → (∀ ω ∈ A, (s : ℝ≥0∞) < ζ ω) →
          ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (K j)) →
            P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - s ∧
                (W (s + ts j) ω, (fun i => VL i (s + ts j) ω), (fun i => VR i (s + ts j) ω),
                  B (s + ts j) ω) ∈ K j}) =
              ∫⁻ ω in A, Q n ts K (W s ω, (fun i => VL i s ω), (fun i => VR i s ω), B s ω) ∂P) ∧
      -- (Markov, the natural filtration of the killed state)
      ∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (s : ℝ≥0) (A : Set Ω),
          MeasurableSet[MeasurableSpace.generateFrom {E : Set Ω | ∃ r : ℝ≥0, r ≤ s ∧
            ∃ D : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ), MeasurableSet D ∧
              E = {ω | (r : ℝ≥0∞) < ζ ω ∧
                (W r ω, (fun i => VL i r ω), (fun i => VR i r ω), B r ω) ∈ D}}] A →
          (∀ ω ∈ A, (s : ℝ≥0∞) < ζ ω) →
          ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (K j)) →
            P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - s ∧
                (W (s + ts j) ω, (fun i => VL i (s + ts j) ω), (fun i => VR i (s + ts j) ω),
                  B (s + ts j) ω) ∈ K j}) =
              ∫⁻ ω in A, Q n ts K (W s ω, (fun i => VL i s ω), (fun i => VR i s ω), B s ω) ∂P

/-- **The simple Markov property, proved**: the strong form at the constant stopping time `s`
(`𝓕_s` is the σ-algebra of the constant stopping time), and the natural σ-algebra of the killed state up to `s`
is contained in `𝓕_s` (`Markov.naturalSigma_le`). -/
theorem integratedSLEMarkov_holds : IntegratedSLEMarkovStatement.{u} := by
  intro a ha nL nR ρL ρR
  refine ⟨Markov.markovKer a ρL ρR, ?_, ?_, ?_, ?_, ?_⟩
  · intro xL xR hF w b Ω mΩ P 𝓕 W VL VR B ζ hE n ts K hK
    exact Markov.markovKer_eq ha (Markov.relWord_shift w b xL xR) hF hE ts hK
  · intro n ts K hK
    exact Markov.measurable_markovKer_sep ts hK
  · intro xL xR Ω mΩ P 𝓕 W VL VR B ζ hF hE n ts K hK
    have h := Markov.markovKer_eq ha (x := ((0 : ℝ), xL, xR, (0 : ℝ))) (Markov.relWord_zero xL xR) hF
      hE ts hK
    simp only [Markov.shiftState, zero_add] at h
    exact h.symm
  · intro xL xR Ω mΩ P 𝓕 W VL VR B ζ hE s A hA hAs n ts K hK
    have hT := isStoppingTime_const 𝓕 s
    have hA' : MeasurableSet[hT.measurableSpace] A := by
      rw [IsStoppingTime.measurableSpace_const]
      exact hA
    exact Markov.measure_markov ha hE (T := fun _ => s) hT hA' hAs ts hK
  · intro xL xR Ω mΩ P 𝓕 W VL VR B ζ hE s A hA hAs n ts K hK
    have hT := isStoppingTime_const 𝓕 s
    have hA' : MeasurableSet[hT.measurableSpace] A := by
      rw [IsStoppingTime.measurableSpace_const]
      exact Markov.naturalSigma_le hE s _ hA
    exact Markov.measure_markov ha hE (T := fun _ => s) hT hA' hAs ts hK

/-- **Theorem 2.2, the Markov sentence for the increments** (the form the landed restart law gives, extended to
every finite stopping time and every word). There is one kernel `R` of the relative word such that:

* **(law)** `R(xL, xR)` is the killed-state law of every integrated evolution from an ordered word `(xL; xR)`;
* **(measurable)** `R` is measurable on the separated words;
* **(strong Markov)** for every integrated evolution, every finite stopping time `T` and every `A ∈ 𝓕_T` with
  `T < ζ` on `A`:
  `P(A ∩ {t_j < ζ − T and (W_{T+t_j} − W_T, V_{T+t_j} − W_T, B_{T+t_j} − B_T) ∈ K_j for all j}) =
    ∫_A R(V_T − W_T) dP`. -/
def IntegratedSLEIncrementStrongMarkovStatement : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    ∃ R : ∀ n : ℕ, (Fin n → ℝ≥0) → (Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) →
        (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ≥0∞,
      -- (law)
      (∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ), IsOrderedForceWord xL xR →
        ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
        {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
        {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
          (∀ j, MeasurableSet (K j)) →
          R n ts K (xL, xR) = P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
            (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ K j}) ∧
      -- (measurable)
      (∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
        (∀ j, MeasurableSet (K j)) →
        Measurable fun s : {s : (Fin nL → ℝ) × (Fin nR → ℝ) // ∀ i j, s.1 i < s.2 j} => R n ts K s.1) ∧
      -- (strong Markov)
      ∀ {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
        {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
        {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
        IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ (T : Ω → ℝ≥0) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (A : Set Ω),
          MeasurableSet[hT.measurableSpace] A → (∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω) →
          ∀ (n : ℕ) (ts : Fin n → ℝ≥0) (K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (K j)) →
            P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
                (W (T ω + ts j) ω - W (T ω) ω, (fun i => VL i (T ω + ts j) ω - W (T ω) ω),
                  (fun i => VR i (T ω + ts j) ω - W (T ω) ω), B (T ω + ts j) ω - B (T ω) ω) ∈ K j}) =
              ∫⁻ ω in A, R n ts K ((fun i => VL i (T ω) ω - W (T ω) ω),
                fun j => VR j (T ω) ω - W (T ω) ω) ∂P

/-- **The Markov sentence for the increments, proved**: `R = Markov.incrKer` (the landed `restartLaw` on separated
words, the reference law elsewhere); on `{T > 0}` the landed `Sec2.Restart.measure_restart_killedState`, on
`{T = 0}` independence from `𝓕₀` (`Markov.measure_markov_increment`). -/
theorem integratedSLEIncrementStrongMarkov_holds : IntegratedSLEIncrementStrongMarkovStatement.{u} := by
  intro a ha nL nR ρL ρR
  refine ⟨Markov.incrKer a ρL ρR, ?_, ?_, ?_⟩
  · intro xL xR hF Ω mΩ P 𝓕 W VL VR B ζ hE n ts K hK
    exact Markov.incrKer_eq ha hF hE ts hK
  · intro n ts K hK
    exact Markov.measurable_incrKer_sep ts hK
  · intro xL xR Ω mΩ P 𝓕 W VL VR B ζ hE T hT A hA hAT n ts K hK
    exact Markov.measure_markov_increment ha hE hT hA hAT ts hK

end AuditFix

end InteractingSLE
