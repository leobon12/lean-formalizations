/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftWord
import InteractingSLE.Spec.Sec7.R5RefAmbientCover

/-!
# Lemma R.5's common phase at hull landings: `R5Ref.R7AmbientLiftWord` (ruling R86)

Packet PROVE-R5-LIFT. Ruling R86 splits R.5's ambient cover; at hull landings it reduces (R5-REFCHART,
`R5Ref.r7AmbientCoverHull_of_liftWord(Inf)`) to the per-collar input `R5Ref.R7AmbientLiftWord(Inf)`: for EVERY
interior-visit reference with an unfilled collar, a hull landing and an ambient image, the limit `d` of "current lift
− ambient lift" and the word identity `β_s(x′) + χ d = phaseData(δ)(ξ) − a`, with ONE phase `δ ω` for all of them.

* `IsAmbReflecting` (def): the ambient transition `f_s ∘ old⁻¹` extends, at every point of a preconnected real set
  `J`, continuously to the real diameter of a half-disc with real, injective boundary values;
* `IsDirectedRefs` (def): a later reference that sees some coordinate sees every coordinate an earlier one sees, and
  the earlier reference's ambient image there is off the closed hull of the increment;
* **`exists_int_common_pathwise`** (generic core, one sample): one integer `n` gives the limit `2πn` of
  `current lift − arg f_s′` at every good coordinate of every reference AND of `old lift − arg f_s′` at every point of
  the reflecting set of every reference with a good coordinate;
* `R7LiftGeom`, `R7LiftGeomInf` (defs, **named pathwise inputs**): reflection on `J i ω` for every interior-visit
  reference of R5-REFCHART's family, directedness, and the exposed-side position data on every selected collar;
* **`exists_r7AmbientLiftWord`**, **`exists_r7AmbientLiftWordInf`**: an integer field `N` with
  `R5Ref.R7AmbientLiftWord(Inf)` at the phase `δ ω = χ·2π N ω + a`. The reference domains avoid the ambient hulls by
  `R5Ref.refEvent(Inf)_spec` and `R5Phase.H_diff_liveExt_zero`; the ambient driver is continuous by the pocket
  configuration (`continuous_W`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref
open Wire.Current.SideTest (rationalOriginalTime)

/-! ### The generic core -/

/-- **The reference reflects against the ambient chart on `J`**: `J` is preconnected and at every `x ∈ J` the ambient
transition `f_s ∘ old⁻¹` agrees on a half-disc with a map continuous up to the real diameter, real and injective
there. -/
def IsAmbReflecting (old : Chart) (W : ℝ → ℝ) (s : ℝ) (J : Set ℝ) : Prop :=
  IsPreconnected J ∧ ∀ x ∈ J, ∃ ρ : ℝ, 0 < ρ ∧ ∃ g : ℂ → ℂ,
    EqOn (fun y => fwdMap W s (old.2.1 y)) g (H ∩ ball (x : ℂ) ρ) ∧ ContinuousOn g (Hbar ∩ ball (x : ℂ) ρ) ∧
    (∀ z ∈ ball (x : ℂ) ρ, z.im = 0 → (g z).im = 0) ∧ InjOn g (Hbar ∩ ball (x : ℂ) ρ)

/-- **Directed references**: if reference `i` sees `ξ`, reference `j` sees some coordinate and `σ i ≤ σ j`, then `j`
sees `ξ`, and the earlier ambient image of the `ξ`-approach tends to a real point off the closed increment hull. -/
def IsDirectedRefs {ι : Type*} (Q : ι → Prop) (old : ι → Chart) (cur : Chart) (J : ι → Set ℝ) (W : ℝ → ℝ)
    (σ : ι → ℝ) : Prop :=
  ∀ i j (ξ : ℝ), Q i → Q j → IsGoodRef (old i) cur (J i) ξ → (∃ ξ' : ℝ, IsGoodRef (old j) cur (J j) ξ') →
    σ i ≤ σ j → IsGoodRef (old j) cur (J j) ξ ∧ ∃ x : ℝ,
      Tendsto (fun y => fwdMap W (σ i) (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      (x : ℂ) ∉ closure (fwdHull (fun r => W (σ i + r) - W (σ i)) (σ j - σ i))

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **The common integer at one sample, in the current and in the reference charts.** -/
theorem exists_int_common_pathwise {p : ℕ → ℝ≥0} {q : ℝ≥0} {Q : ℕ → Prop} (hc : (c ω).IsConformal)
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) {ℓ : ℂ → ℂ}
    (hℓ : IsDerivLog (c ω).1 ℓ (c ω).dom) (hlift : ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ z).im)
    {W : ℝ → ℝ} (hW : Continuous W) {σ : ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i) {J : ℕ → Set ℝ}
    (hQ : ∀ i, Q i → p i ≤ q ∧ ((relChart c γ (p i) ω).dom : Set ℂ) ⊆ H \ fwdHull W (σ i) ∧
      IsAmbReflecting (relChart c γ (p i) ω) W (σ i) (J i))
    (hdir : IsDirectedRefs Q (fun i => relChart c γ (p i) ω) (relChart c γ q ω) J W σ) :
    ∃ n : ℤ, (∀ i (ξ : ℝ), Q i → IsGoodRef (relChart c γ (p i) ω) (relChart c γ q ω) (J i) ξ →
        Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
          (logDerivFwd W (σ i) ((relChart c γ q ω).2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n))) ∧
      ∀ i, Q i → (∃ ξ : ℝ, IsGoodRef (relChart c γ (p i) ω) (relChart c γ q ω) (J i) ξ) → ∀ x ∈ J i,
        Tendsto (fun y => (relChart c γ (p i) ω).2.2 ((relChart c γ (p i) ω).2.1 y) -
          (logDerivFwd W (σ i) ((relChart c γ (p i) ω).2.1 y)).im) (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  -- the qualified references
  have hold : ∀ i, Q i → (relChart c γ (p i) ω).IsConformal := fun i hi =>
    isConformal_relChart_of_driven hγ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hQ i hi).1) hq) hc
  obtain ⟨n, hn⟩ := exists_int_common_relChart_ambLift (ι := {i : ℕ // Q i}) (p := fun i => p i.1)
    (s := fun i => σ i.1) (J := fun i => J i.1) hc hγ hq (fun i => (hQ i.1 i.2).1) hℓ hlift hW
    (fun i => hσ i.1) (fun i => (hQ i.1 i.2).2.1) (fun i => (hQ i.1 i.2).2.2.1)
    (fun i x hx => by
      obtain ⟨ρ, hρ, g, hSg, hcg, hrg, hig⟩ := (hQ i.1 i.2).2.2.2 x hx
      exact exists_pos_tendsto_deriv_ambTransition (hold i.1 i.2) hW (hσ i.1) (hQ i.1 i.2).2.1 hρ hSg hcg hrg hig)
    (fun i j ξ ξ' hξ hξ' => by
      rcases le_total (σ i.1) (σ j.1) with hle | hle
      · obtain ⟨hj, x, hFx, hx⟩ := hdir i.1 j.1 ξ i.2 j.2 hξ ⟨ξ', hξ'⟩ hle
        exact ⟨ξ, hξ, hj, Or.inl ⟨hle, x, hFx, hx⟩⟩
      · obtain ⟨hi, x, hFx, hx⟩ := hdir j.1 i.1 ξ' j.2 i.2 hξ' ⟨ξ, hξ⟩ hle
        exact ⟨ξ', hi, hξ', Or.inr ⟨hle, x, hFx, hx⟩⟩)
  have hcur : ∀ i (ξ : ℝ), Q i → IsGoodRef (relChart c γ (p i) ω) (relChart c γ q ω) (J i) ξ →
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
        (logDerivFwd W (σ i) ((relChart c γ q ω).2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) :=
    fun i ξ hi hξ => hn ⟨i, hi⟩ ξ hξ
  refine ⟨n, hcur, fun i hi ⟨ξ₀, x₀, r₀, hx₀, hr₀, hcol₀, htr₀⟩ x hx => ?_⟩
  -- the reference's own integer on its reflecting set
  have hp : (p i : ℝ≥0∞) < capLife (γ ω) := lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hQ i hi).1) hq
  obtain ⟨Lc, hLc, hliftc⟩ := Aux29Cor.exists_isDerivLog_relChart hγ hp hc hℓ hlift
  obtain ⟨m, hm⟩ := exists_int_forall_tendsto_lift_sub (cur := relChart c γ (p i) ω) (g := fwdMap W (σ i))
    (Lg := logDerivFwd W (σ i)) (hold i hi) hLc hliftc (isDerivLog_fwdMap hW (hσ i)) (hQ i hi).2.2.1
    fun x hx => by
      obtain ⟨ρ, hρ, g, hSg, hcg, hrg, hig⟩ := (hQ i hi).2.2.2 x hx
      obtain ⟨b, hb, hder⟩ :=
        exists_pos_tendsto_deriv_ambTransition (hold i hi) hW (hσ i) (hQ i hi).2.1 hρ hSg hcg hrg hig
      exact ⟨1, one_pos, fun y hy => (hQ i hi).2.1 ((hold i hi).inv_mem_dom hy.1), b, hb, hder⟩
  -- the reference's integer is the common one (compare at `ξ₀`)
  have h₁ := tendsto_relChart_lift_sub_of_old (A := fun z => (logDerivFwd W (σ i) z).im) hc hγ hq (hQ i hi).1 hr₀
    hcol₀ htr₀ (hm x₀ hx₀)
  have h₂ := hcur i ξ₀ hi ⟨x₀, r₀, hx₀, hr₀, hcol₀, htr₀⟩
  have := nhdsWithin_H_neBot ξ₀
  have heq := tendsto_nhds_unique h₁ h₂
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have hmn : (m : ℝ) = n := mul_left_cancel₀ hπ heq
  rw [← hmn]
  exact hm x hx

/-! ### The R.7 bounded change pocket -/

section Bounded

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The pathwise geometry of R.5's common phase at hull landings** (bounded change pocket; named input): almost
surely on the live test, (b) every interior-visit reference of R5-REFCHART's family reflects against its ambient
chart on `J i ω`; (c) the interior-visit references are directed; (d) on every selected collar of
`R5Ref.R7AmbientLiftWord` the collar point lies in `J i ω`, the current seeds are the innermost current force points
with `ξ` between them, and the ambient image lies on the same side of the ambient driver inside the ambient seeds. -/
def R7LiftGeom {nL nR mL mR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ)
    (X : Ω → Set ℂ) (J : ℕ → Ω → Set ℝ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
    (∀ i, ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r →
      IsAmbReflecting (refChart c R L r η ψ i ω) (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i) (J i ω)) ∧
    IsDirectedRefs (fun i => ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r)
      (fun i => refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) (fun i => J i ω)
      (fun t : ℝ => W' t.toNNReal ω) (fun i => (rationalOriginalTime i : ℝ)) ∧
    ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω - segDriver (travAll R L r η ψ ω) q)
        (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
          segDriver (travAll R L r η ψ ω) q) →
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ X ω →
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
      ∀ (i : ℕ) (x ε x' : ℝ), let s := rationalOriginalTime i;
        ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
        η ω s ∈ cfPocket (R ω) (L ω) r →
        IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε →
        extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω →
        x' ∉ forceJumpSet (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) →
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((relChart c (travAll R L r η ψ) q ω).2.1 y))
          (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) →
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((refChart c R L r η ψ i ω).2.1 y))
          (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) →
        x ∈ J i ω ∧
        (∀ i', geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i' q ω ≤
          geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω) ∧
        (∀ j', geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω ≤
          geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j' q ω) ∧
        ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
          (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q) ∧
        (x' < 0 → ∀ j, VL j s ω - W' s ω ≤ x') ∧ (0 ≤ x' → ∀ j, x' < VR j s ω - W' s ω) ∧
        (ξ < 0 ↔ x' < 0)

/-- **`R5Ref.R7AmbientLiftWord` from the common-phase geometry** (bounded change pocket): an integer field `N` such
that the lift-difference limit is `2π N ω` and the word identity holds at the phase `δ ω = χ·2π N ω + a`, on every
selected collar of every interior-visit reference. -/
theorem exists_r7AmbientLiftWord {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {J : ℕ → Ω → Set ℝ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (h : R7LiftGeom P A R L r η ψ xL xR c W' ζ' VL VR X J q) (a : ℝ) :
    ∃ N : Ω → ℤ, R7AmbientLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * N ω) + a) X q := by
  classical
  set Φ : Ω → ℤ → Prop := fun ω n => ∀ i (ξ : ℝ),
    (ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r) →
    IsGoodRef (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) (J i ω) ξ →
    Tendsto (fun y => (relChart c (travAll R L r η ψ) q ω).2.2 ((relChart c (travAll R L r η ψ) q ω).2.1 y) -
      (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAll R L r η ψ) q ω).2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) with hΦ
  have hex : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∃ n, Φ ω n := by
    filter_upwards [h] with ω hω hA hlive
    obtain ⟨hrefl, hdir, -⟩ := hω hA hlive
    have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
    have hspec := refEvent_spec hcfg hψ hc hdom heq (refHull W' ζ') q
    obtain ⟨n, hn, -⟩ := exists_int_common_pathwise (c := c) (γ := travAll R L r η ψ) (ω := ω)
      (p := fun i => (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal)
      (Q := fun i => ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r)
      (W := fun t : ℝ => W' t.toNNReal ω) (σ := fun i => (rationalOriginalTime i : ℝ)) (J := fun i => J i ω)
      (hc ω hA) hγ hlive (hℓ ω hA).1 (hℓ ω hA).2 (hcfg ω hA).continuous_W
      (fun i => (rationalOriginalTime i).coe_nonneg)
      (fun i ⟨hM, hv⟩ => by
        refine ⟨hM.2.2.2.1, ?_, hrefl i hM hv⟩
        have hd := (hspec i ω hM).2.2.2.2
        intro z hz
        have hz' : z ∈ H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω := by
          rw [← hd]; exact hz
        rw [H_diff_liveExt_zero hA hγ, hM.2.2.2.2] at hz'
        exact hz'.2) hdir
    exact ⟨n, hn⟩
  set N : Ω → ℤ := fun ω =>
    if hh : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧ ∃ n, Φ ω n then Classical.choose hh.2.2 else 0
    with hN
  refine ⟨N, ?_⟩
  filter_upwards [h, hex] with ω hω hexω hA hlive ξ hξ hX hC i x ε x' s hM hv hcol hland hx' hfx hfo
  have hh : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧ ∃ n, Φ ω n := ⟨hA, hlive, hexω hA hlive⟩
  have hNspec : Φ ω (N ω) := by
    rw [hN]; simp only [hh, and_self, ↓reduceDIte]
    exact Classical.choose_spec hh.2.2
  obtain ⟨hxJ, hvL, hvR, hξI, hVL, hVR, hside⟩ :=
    (hω hA hlive).2.2 ξ hξ hX hC i x ε x' hM hv hcol hland hx' hfx hfo
  have hvL' : ∀ i', (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω -
      segDriver (travAll R L r η ψ ω) q) i' ≤ (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω -
      segDriver (travAll R L r η ψ ω) q) 0 := fun i' => by simp only; linarith [hvL i']
  have hvR' : ∀ j', (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
      segDriver (travAll R L r η ψ ω) q) 0 ≤ (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
      segDriver (travAll R L r η ψ ω) q) j' := fun j' => by simp only; linarith [hvR j']
  exact ⟨2 * Real.pi * N ω, hNspec i ξ ⟨hM, hv⟩ ⟨x, ε, hxJ, hcol.1, hcol.2.1, hcol.2.2.1⟩,
    word_identity_exposed ρL ρR ρL' ρR' hvL' hvR' hξI hVL hVR hside (N ω) a⟩

end Bounded

/-! ### The R.7 change pocket opening at the flow seed -/

section SeedOpen

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The pathwise geometry of R.5's common phase at hull landings** (change pocket opening at the flow seed; named
input): almost surely on the live test, (b) every interior-visit reference of R5-REFCHART's family reflects against
its ambient chart on `J i ω`; (c) the interior-visit references are directed; (d) on every selected collar of
`R5Ref.R7AmbientLiftWordInf` the collar point lies in `J i ω`, the current seeds are the innermost current force points
with `ξ` between them, and the ambient image lies on the same side of the ambient driver inside the ambient seeds. -/
def R7LiftGeomInf {nL nR mL mR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ)
    (X : Ω → Set ℂ) (J : ℕ → Ω → Set ℝ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
    (∀ i, ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r →
      IsAmbReflecting (refChartInf c R L r η ψ i ω) (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i) (J i ω)) ∧
    IsDirectedRefs (fun i => ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r)
      (fun i => refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) (fun i => J i ω)
      (fun t : ℝ => W' t.toNNReal ω) (fun i => (rationalOriginalTime i : ℝ)) ∧
    ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
          segDriver (travAllInf R L r η ψ ω) q)
        (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
          segDriver (travAllInf R L r η ψ ω) q) →
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ X ω →
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
      ∀ (i : ℕ) (x ε x' : ℝ), let s := rationalOriginalTime i;
        ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
        η ω s ∈ cfPocket (R ω) (L ω) r →
        IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε →
        extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω →
        x' ∉ forceJumpSet (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) →
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))
          (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) →
        Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((refChartInf c R L r η ψ i ω).2.1 y))
          (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) →
        x ∈ J i ω ∧
        (∀ i', geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i' q ω ≤
          geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω) ∧
        (∀ j', geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω ≤
          geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j' q ω) ∧
        ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
            segDriver (travAllInf R L r η ψ ω) q)
          (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q) ∧
        (x' < 0 → ∀ j, VL j s ω - W' s ω ≤ x') ∧ (0 ≤ x' → ∀ j, x' < VR j s ω - W' s ω) ∧
        (ξ < 0 ↔ x' < 0)

/-- **`R5Ref.R7AmbientLiftWordInf` from the common-phase geometry** (pocket opening at the flow seed): an integer field
`N` such
that the lift-difference limit is `2π N ω` and the word identity holds at the phase `δ ω = χ·2π N ω + a`, on every
selected collar of every interior-visit reference. -/
theorem exists_r7AmbientLiftWordInf {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {J : ℕ → Ω → Set ℝ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (h : R7LiftGeomInf P A R L r η ψ xL xR c W' ζ' VL VR X J q) (a : ℝ) :
    ∃ N : Ω → ℤ, R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * N ω) + a) X q := by
  classical
  set Φ : Ω → ℤ → Prop := fun ω n => ∀ i (ξ : ℝ),
    (ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r) →
    IsGoodRef (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) (J i ω) ξ →
    Tendsto (fun y => (relChart c (travAllInf R L r η ψ) q ω).2.2 ((relChart c (travAllInf R L r η ψ) q ω).2.1 y) -
      (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) with hΦ
  have hex : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∃ n, Φ ω n := by
    filter_upwards [h] with ω hω hA hlive
    obtain ⟨hrefl, hdir, -⟩ := hω hA hlive
    have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
    have hspec := refEventInf_spec hcfg hψ hc hdom heq (refHull W' ζ') q
    obtain ⟨n, hn, -⟩ := exists_int_common_pathwise (c := c) (γ := travAllInf R L r η ψ) (ω := ω)
      (p := fun i => (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal)
      (Q := fun i => ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r)
      (W := fun t : ℝ => W' t.toNNReal ω) (σ := fun i => (rationalOriginalTime i : ℝ)) (J := fun i => J i ω)
      (hc ω hA) hγ hlive (hℓ ω hA).1 (hℓ ω hA).2 (hcfg ω hA).continuous_W
      (fun i => (rationalOriginalTime i).coe_nonneg)
      (fun i ⟨hM, hv⟩ => by
        refine ⟨hM.2.2.2.1, ?_, hrefl i hM hv⟩
        have hd := (hspec i ω hM).2.2.2.2
        intro z hz
        have hz' : z ∈ H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
            (refHull W' ζ' i) 0 ω := by
          rw [← hd]; exact hz
        rw [H_diff_liveExt_zero hA hγ, hM.2.2.2.2] at hz'
        exact hz'.2) hdir
    exact ⟨n, hn⟩
  set N : Ω → ℤ := fun ω =>
    if hh : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧ ∃ n, Φ ω n then Classical.choose hh.2.2 else 0
    with hN
  refine ⟨N, ?_⟩
  filter_upwards [h, hex] with ω hω hexω hA hlive ξ hξ hX hC i x ε x' s hM hv hcol hland hx' hfx hfo
  have hh : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧ ∃ n, Φ ω n := ⟨hA, hlive, hexω hA hlive⟩
  have hNspec : Φ ω (N ω) := by
    rw [hN]; simp only [hh, and_self, ↓reduceDIte]
    exact Classical.choose_spec hh.2.2
  obtain ⟨hxJ, hvL, hvR, hξI, hVL, hVR, hside⟩ :=
    (hω hA hlive).2.2 ξ hξ hX hC i x ε x' hM hv hcol hland hx' hfx hfo
  have hvL' : ∀ i', (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
      segDriver (travAllInf R L r η ψ ω) q) i' ≤
      (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
      segDriver (travAllInf R L r η ψ ω) q) 0 := fun i' => by simp only; linarith [hvL i']
  have hvR' : ∀ j', (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
      segDriver (travAllInf R L r η ψ ω) q) 0 ≤
      (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
      segDriver (travAllInf R L r η ψ ω) q) j' := fun j' => by simp only; linarith [hvR j']
  exact ⟨2 * Real.pi * N ω, hNspec i ξ ⟨hM, hv⟩ ⟨x, ε, hxJ, hcol.1, hcol.2.1, hcol.2.2.1⟩,
    word_identity_exposed ρL ρR ρL' ρR' hvL' hvR' hξI hVL hVR hside (N ω) a⟩

end SeedOpen

end InteractingSLE.Sec7.R5Lift
