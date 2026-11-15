/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibCode

/-!
# The fibres of the restart are `DyActFibre`s: assembly on the code space

Packet PROVE-AUX61-FIB, pieces (F1)–(F4) of `planning/handoffs/PROVE-AUX61-ACT.md`, in the form that makes the
remaining analytic pieces **statements about explicit objects**. Every fibre lives on the one standard Borel space
`ULift FibCode` (`Aux61FibCode`); on it, the fibre's driver (`fibW`), path (`fibΓ`), lifetime (`fibU`), field
(`fibField`) and the stops `min(T_N, k/2ⁿ)` (`fibStop`, with the explicit announcing stops `annStop` of
`Aux61FibClock`) are fixed functions of the code, independent of the fibre law. Hence:

* `FibData`: the deterministic data of a fibre (functions of the retained history only): the reference word, the
  window `V`, the clearance reader `ℓ`, the harmonic correction `q` with its zero-boundary set `O₀`, the buffer;
* `PathGood d s`: the path facts of a code relative to the data (generating trace, clearance, window exit, interior,
  injectivity);
* **`FibKernel d P`** (piece (F2)+(F3)): the kernel of the fibre law `P` at the explicit stops `fibStop` — exactly the
  `dyKernel` field of `Aux61Act.DyActFibre`, stated without any reference clock;
* **`FibMembers d P`** (piece (F4)): the member identities at rational times — the `members` field;
* **`fibDyActFibre`** / **`exists_dyActFibre`** (piece (F1)): a law on the codes with `PathGood` almost surely,
  `FibKernel` and `FibMembers` **is** a `DyActFibre` (clock source `fibSource`, reference clock `fibClock` killed at
  the clock, hull bound `Aux61Cov.ae_hull_buffer_of_exit`);
* **`ae_ae_condDistrib_of_ae_prod`**: almost-sure facts of `(history, code)` pass to almost every fibre (a jointly
  measurable good set, for data that depend on the history);
* **`hasDyActFibreCover_of_fib`**: `Aux61Act.HasDyActFibreCover` from a countable family of histories, codes, history
  events and data on the glued space: (cover), (event), the path facts almost surely, and `FibKernel`/`FibMembers` for
  almost every fibre.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result; R77: no post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Fib

open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open LocalExt (cfVal)
open Restart.FlowStopIdentCMI (CMCut)
open Aux61Win (meanF IsCutoffOn)
open Aux61R2 (RefExt)
open Aux61R45 (ClockSource ReferenceClock)
open Sec7.PocketTraversal

universe u

/-! ### The fibre's objects on the code space -/

/-- The fibre's driver (read from the path). -/
abbrev fibW : ℝ≥0 → ULift.{u} FibCode → ℝ := fun t s => FibCode.driver t s.down

/-- The fibre's path. -/
abbrev fibΓ : ULift.{u} FibCode → ℝ≥0 → ℂ := fun s => s.down.trace

/-- The fibre's lifetime (the clock). -/
abbrev fibU : ULift.{u} FibCode → ℝ≥0∞ := fun s => s.down.life

/-- The fibre's field (in the restart chart). -/
abbrev fibField : ULift.{u} FibCode → DistOn upperHalfPlaneOpens := fun s => s.down.field

/-- **The stops `min(T_N, k/2ⁿ)`** with the explicit announcing stops `annStop ℓ` of the fibre's clock. -/
def fibStop (ℓ : ℂ → ℝ) (n k N : ℕ) : ULift.{u} FibCode → WithTop ℝ≥0 :=
  fun s => min ((annStop ℓ fibΓ fibU N s : ℝ≥0) : WithTop ℝ≥0) ((Restart.DomainMarkov.dyT n k : ℝ≥0) : WithTop ℝ≥0)

/-! ### The deterministic data and the path facts -/

/-- **The deterministic data of a restart fibre** (functions of the retained history only): a piecewise constant
reference word whose seed is not a threshold state, the window `V`, a continuous clearance reader `ℓ` positive at the
seed, a correction `q` harmonic on `ℍ` with zero boundary values on the open set `O₀`, and an open buffer containing
the seed and the window, with compact closure whose real points lie in `O₀`. -/
structure FibData where
  κ : ℝ
  κ_pos : 0 < κ
  bR : ℝ → ℝ
  JR : Finset ℝ
  bR_pc : IsPiecewiseConstantBoundaryData bR JR
  seed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ bR JR 0 0) (flowLineRhoR κ bR JR 0 0) 0
    (flowLineXL bR JR 0) (flowLineXR bR JR 0)
  V : Set ℂ
  ℓ : ℂ → ℝ
  ℓ_cont : Continuous ℓ
  ℓ_zero : 0 < ℓ 0
  q : ℂ → ℝ
  q_harm : InnerProductSpace.HarmonicOnNhd q H
  O₀ : Set ℝ
  O₀_open : IsOpen O₀
  q_zero : ∀ x ∈ O₀, Tendsto q (𝓝[H] (x : ℂ)) (𝓝 0)
  buffer : Set ℂ
  buffer_open : IsOpen buffer
  zero_mem : (0 : ℂ) ∈ buffer
  buffer_compact : IsCompact (closure buffer)
  buffer_real : ∀ z ∈ closure buffer, z.im = 0 → z.re ∈ O₀
  V_sub : V ⊆ buffer

/-- **The path facts of a code relative to the data**: the decoded path is a generating trace of the decoded driver
through the lifetime; the clearance is positive before the lifetime and nonpositive at a finite lifetime; the lifetime
is the window exit; positive-time points before the lifetime are interior; the path is injective through the
lifetime. -/
def PathGood (d : FibData) (s : FibCode) : Prop :=
  s ∈ GoodTrace ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < s.life → 0 < d.ℓ (s.trace t)) ∧
    (∀ T : ℝ≥0, (T : ℝ≥0∞) = s.life → d.ℓ (s.trace T) ≤ 0) ∧ s.life = RLC.exitTime d.V s.trace s.life ∧
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < s.life → s.trace t ∈ H) ∧ InjOn s.trace {t | (t : ℝ≥0∞) ≤ s.life}

/-! ### The analytic statements of a fibre (pieces (F2)–(F4)) -/

/-- **The kernel of a fibre at the explicit stops** (pieces (F2) and (F3)): for every cutoff `(F, N)` of `q` on `O₀`
with `buffer ⊆ N`, at each stop `fibStop ℓ n k N'` of the completed filtration of the fibre's killed driver, for every
reference extension `u` at the stop, the conditional characteristic functional of the field at a test function off the
hull is the `meanF` Gaussian kernel. This is the `dyKernel` field of `Aux61Act.DyActFibre` for the fibre built on the
code space, stated with no reference clock. -/
def FibKernel (d : FibData) (P : Measure (ULift.{u} FibCode)) : Prop :=
  ∀ (F : CMCut) (N : Set ℂ), IsCutoffOn F d.q N d.O₀ → d.buffer ⊆ N → ∀ n k N' : ℕ,
    ∀ (hτ : IsStoppingTime (drivingFiltration P isMeasurableKilledDriving_fib) (fibStop.{u} d.ℓ n k N')),
    ∀ u : ULift.{u} FibCode → ℂ → ℝ,
      (∀ ω, RefExt d.κ d.bR d.JR fibW ((fibStop d.ℓ n k N' ω).untopD 0) ω (u ω)) →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
        Disjoint (tsupport ψ) (fwdHull (Ito.rpath (fibW · ω)) ((fibStop d.ℓ n k N' ω).untopD 0 : ℝ≥0)) →
        P[fun ω' => Complex.exp (Complex.I * (fibField ω' ψ : ℂ)) | hτ.measurableSpace] ω =
          cfVal (∫ z, meanF d.κ (u ω) d.q F (Ito.rpath (fibW · ω)) ((fibStop d.ℓ n k N' ω).untopD 0 : ℝ≥0) z * ψ z)
            (loewnerGreenEnergy (Ito.rpath (fibW · ω)) ((fibStop d.ℓ n k N' ω).untopD 0 : ℝ≥0) ψ)

/-- **The member identities of a fibre at rational times** (piece (F4)): the field centred by the reference mean plus
`q` satisfies `DomainMarkov.HasRatMembers` for the raw filtration of the killed driver and reference marks. This is the
`members` field of `Aux61Act.DyActFibre` (the killed-driving proof argument is irrelevant). -/
def FibMembers (d : FibData) (P : Measure (ULift.{u} FibCode)) : Prop :=
  ∀ hX : IsMeasurableKilledDriving fibW (geomLW fibW fun _ => flowLineXL d.bR d.JR 0)
      (geomRW fibW fun _ => flowLineXR d.bR d.JR 0) fibU,
    Restart.DomainMarkov.HasRatMembers P (killedDrivingFiltration hX) fibW fibU
      (WholeField.centredField fibField fun z =>
        MartChar.meanExt d.κ (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0) 0
          (flowLineXL d.bR d.JR 0) (flowLineXR d.bR d.JR 0) z + d.q z)

/-! ### A fibre is a `DyActFibre` -/

section Fibre

variable (d : FibData) (P : Measure (ULift.{u} FibCode)) [IsProbabilityMeasure P]
  (hgood : ∀ᵐ s ∂P, PathGood d s.down)

omit [IsProbabilityMeasure P] in
include hgood in
theorem ae_goodTrace_of_pathGood : ∀ᵐ s ∂P, s.down ∈ GoodTrace := hgood.mono fun _ h => h.1

/-- The fibre's reference clock (`fibClock`) for the data `d`. -/
def dataClock : ReferenceClock (fibSource P (ae_goodTrace_of_pathGood d P hgood)) d.κ d.bR d.JR 0 d.V :=
  fibClock P (ae_goodTrace_of_pathGood d P hgood) d.κ d.bR d.JR d.V d.seed d.ℓ d.ℓ_cont d.ℓ_zero
    (hgood.mono fun _ h => h.2.1) (hgood.mono fun _ h => h.2.2.1) (hgood.mono fun _ h => h.2.2.2.1)
    (hgood.mono fun _ h => h.2.2.2.2.1)

/-- **The fibre built on the code space** from the deterministic data, the path facts, the kernel at the explicit
stops and the member identities. -/
def fibDyActFibre (hker : FibKernel d P) (hmem : FibMembers d P) : Aux61Act.DyActFibre (ULift.{u} FibCode) where
  κ := d.κ
  κ_pos := d.κ_pos
  bR := d.bR
  JR := d.JR
  bR_pc := d.bR_pc
  CS := fibSource P (ae_goodTrace_of_pathGood d P hgood)
  y_zero := rfl
  V := d.V
  RC := dataClock d P hgood
  driving_eq := driving_eq_self (dataClock d P hgood) fun _ => rfl
  field := fibField
  measurable_field := FibCode.measurable_field.comp measurable_down
  q := d.q
  q_harm := d.q_harm
  O₀ := d.O₀
  O₀_open := d.O₀_open
  q_zero := d.q_zero
  buffer := d.buffer
  buffer_open := d.buffer_open
  zero_mem := d.zero_mem
  buffer_compact := d.buffer_compact
  buffer_real := d.buffer_real
  hull_buffer := Aux61Cov.ae_hull_buffer_of_exit rfl (dataClock d P hgood) d.V_sub
    (hgood.mono fun _ h => h.2.2.2.2.2) (hgood.mono fun _ h => h.2.2.2.2.1)
  dyKernel := by
    intro F N hF hbN τ hτ hτform u hu ψ
    obtain ⟨n, k, N', rfl⟩ := hτform
    exact hker F N hF hbN n k N' hτ u hu ψ
  members := hmem _
  injective := hgood.mono fun _ h => h.2.2.2.2.2

include hgood in
/-- **A law on the codes with the path facts, the kernel at the explicit stops and the member identities is a
`DyActFibre`** with that law, the data's reference word, the decoded path and the lifetime as its clock. -/
theorem exists_dyActFibre (hker : FibKernel d P) (hmem : FibMembers d P) :
    ∃ D : Aux61Act.DyActFibre (ULift.{u} FibCode), D.CS.P = P ∧ D.κ = d.κ ∧ D.bR = d.bR ∧ D.JR = d.JR ∧
      D.CS.Γ = fibΓ ∧ D.RC.e = fibU :=
  ⟨fibDyActFibre d P hgood hker hmem, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Fibre

/-! ### Almost-sure facts pass to almost every fibre (history-dependent good sets) -/

/-- **Almost-sure facts of `(history, code)` pass to almost every fibre**: if `(Z, Y) ∈ G` almost surely for a
measurable `G ⊆ β × S`, then for almost every `x` the fibre at `Z x` charges only codes `s` with `(Z x, s) ∈ G`. -/
theorem ae_ae_condDistrib_of_ae_prod {X β S : Type*} [MeasurableSpace X] [MeasurableSpace β] [MeasurableSpace S]
    [StandardBorelSpace S] [Nonempty S] {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β} {Y : X → S}
    (hZ : Measurable Z) (hY : Measurable Y) {G : Set (β × S)} (hG : MeasurableSet G)
    (h : ∀ᵐ x ∂μ, (Z x, Y x) ∈ G) : ∀ᵐ x ∂μ, ∀ᵐ s ∂(condDistrib Y Z μ (Z x)), (Z x, s) ∈ G := by
  have h0 : (μ.map fun a => (Z a, Y a)) Gᶜ = 0 := by
    rw [Measure.map_apply (hZ.prodMk hY) hG.compl]
    exact ae_iff.1 h
  rw [← compProd_map_condDistrib hZ.aemeasurable hY.aemeasurable, Measure.compProd_apply hG.compl,
    lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hG.compl)] at h0
  filter_upwards [ae_of_ae_map hZ.aemeasurable h0] with x hx
  rw [ae_iff]
  exact hx

/-! ### The cover -/

/-- **`HasDyActFibreCover` from fibre data on the code space.** Data: a countable family of retained histories `Z i`,
codes `Y i` (measurable, in `FibCode`), measurable history events `B i`, deterministic fibre data `d i` (functions of
the history), reference sets `I i` with `Ref` on `B i`, and measurable code events `L i` whose paths visit `I i`
before their lifetime. Hypotheses: (cover) the event is covered by the history events; (event) on `B i` the event
forces the code into `L i`; (path) almost surely on `B i`, `(Z i, Y i)` lies in a measurable set `G i` of pairs whose
code has the path facts relative to the data; (F2)–(F4) for almost every history value in `B i`, the fibre law of the
code has the kernel at the explicit stops and the member identities. -/
theorem hasDyActFibreCover_of_fib {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {E : X → Prop} {Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop} {ι : Type} [Countable ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (Y : ι → X → FibCode) (hY : ∀ i, Measurable (Y i))
    (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i)) (d : ∀ i, β i → FibData) (I : ι → Set ℝ)
    (L : ι → Set FibCode) (hL : ∀ i, MeasurableSet (L i))
    (hLv : ∀ i, ∀ s ∈ L i, ∃ v : ℝ≥0, (v : ℝ≥0∞) ≤ s.life ∧ ∃ y ∈ I i, s.trace v = (y : ℂ))
    (hRef : ∀ i, ∀ z ∈ B i, Ref (d i z).κ (d i z).bR (d i z).JR (I i))
    (G : ∀ i, Set (β i × FibCode)) (hG : ∀ i, MeasurableSet (G i))
    (hGgood : ∀ i z s, z ∈ B i → (z, s) ∈ G i → PathGood (d i z) s)
    (hYG : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → (Z i x, Y i x) ∈ G i)
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i) (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x → Y i x ∈ L i)
    (hker : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i →
      FibKernel (d i (Z i x)) (condDistrib (fun x => ULift.up.{u} (Y i x)) (Z i) μ (Z i x)))
    (hmem : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i →
      FibMembers (d i (Z i x)) (condDistrib (fun x => ULift.up.{u} (Y i x)) (Z i) μ (Z i x))) :
    Aux61Act.HasDyActFibreCover μ E Ref := by
  let Y' : ι → X → ULift.{u} FibCode := fun i x => ULift.up (Y i x)
  have hY' : ∀ i, Measurable (Y' i) := fun i => measurable_up.comp (hY i)
  let L' : ι → Set (ULift.{u} FibCode) := fun i => ULift.down ⁻¹' L i
  have hL' : ∀ i, MeasurableSet (L' i) := fun i => measurable_down (hL i)
  refine Aux61Act.hasDyActFibreCover_of_condDistrib Z hZ Y' hY' B hB L' hL' hcover
    (fun i => (hE i).mono fun x hx hxB hxE => hx hxB hxE) fun i => ?_
  let G' : Set (β i × ULift.{u} FibCode) := {p | p.1 ∈ B i → (p.1, p.2.down) ∈ G i}
  have hG' : MeasurableSet G' := by
    have e : G' = (Prod.fst ⁻¹' (B i)ᶜ) ∪ (fun p : β i × ULift.{u} FibCode => (p.1, p.2.down)) ⁻¹' G i := by
      ext p
      simp only [G', mem_ofPred_eq, mem_union, mem_preimage, mem_compl_iff]
      tauto
    rw [e]
    exact (measurable_fst (hB i).compl).union
      ((measurable_fst.prodMk (measurable_down.comp measurable_snd)) (hG i))
  have htr := ae_ae_condDistrib_of_ae_prod (hZ i) (hY' i) hG' ((hYG i).mono fun x hx hxB => hx hxB)
  filter_upwards [htr, hker i, hmem i] with x hx hkx hmx hxB
  have hgood : ∀ᵐ s ∂(condDistrib (Y' i) (Z i) μ (Z i x)), PathGood (d i (Z i x)) s.down :=
    hx.mono fun s hs => hGgood i (Z i x) s.down hxB (hs hxB)
  obtain ⟨D, hP, hκ, hbR, hJR, hΓ, he⟩ := exists_dyActFibre (d i (Z i x)) _ hgood (hkx hxB) (hmx hxB)
  refine ⟨D, I i, hP, ?_, fun ω hω => ?_⟩
  · rw [hκ, hbR, hJR]
    exact hRef i (Z i x) hxB
  · obtain ⟨v, hv, y, hy, hvy⟩ := hLv i ω.down hω
    refine ⟨v, ?_, y, hy, ?_⟩
    · rw [he]
      exact hv
    · rw [hΓ]
      exact hvy

end InteractingSLE.Sec5.Aux61Fib
