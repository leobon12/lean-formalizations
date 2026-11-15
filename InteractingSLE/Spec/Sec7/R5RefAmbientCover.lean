/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5RefAmbient
import InteractingSLE.Spec.Sec7.R5SameClause

/-!
# R.5's ambient cover at hull landings: the corrected form and its reduction to the lift input

Packet PROVE-R5-REFCHART. PROVE-R5-SAMETIME's `R5Same.R7AmbientCover` requires, at EVERY real current coordinate `ξ`
off the jumps whose landing avoids the finite set `X`, a point `z₀ ∈ C ω ∩ refHull W' ζ' i ω` to which the current
inverse tends. The limit of the current inverse is the landing (`extendFrom ℍ inv ξ`), so at a coordinate landing on an
unvisited side of the pocket (a point of `∂C`, never in the open `C`) the conclusion fails
(**`not_ambient_landing_of_notMem`**). Such coordinates exist at every live capacity (near the outgoing corner the
pocket's sides are not reached by the hull), so `R7AmbientCover` holds only on null tests; its wall part needs the
walls' own heights (the incoming flow germs, source p. 475 "Each open incoming prefix has its own canonical flow
germ"), which `R5Same.ae_tendsto_harmRep_ref` (heights at hull points) does not give.

* `R7AmbientCoverHull` (def): `R7AmbientCover` restricted to coordinates whose landing lies in the pocket;
* `R7AmbientLiftWord` (def): the input left to PROVE-R5-LIFT, per selected collar — the limit `d` of
  "current lift − ambient lift" and the word identity `β_s(x′) + χ d = current word − a`;
* **`r7AmbientCoverHull_of_liftWord`**, **`r7AmbientCoverHull_of_liftWordInf`**: the reference family of this packet
  (`refEvent`, `refChart`, exceptional set `refExc ∪ X`) and the geometric part `ae_exists_ambient_cover(Inf)` reduce
  `R7AmbientCoverHull` to `R7AmbientLiftWord`.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull fwdMap chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Ref

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*}

/-- **The obstruction to `R5Same.R7AmbientCover` at landings outside the pocket**: if the current inverse lands at
`p ∉ C` from `ξ`, no point `z₀ ∈ C` is its limit. -/
theorem not_ambient_landing_of_notMem {f : ℂ → ℂ} {ξ : ℝ} {p : ℂ} {C K : Set ℂ}
    (hLanding : Tendsto f (𝓝[H] (ξ : ℂ)) (𝓝 p)) (hp : p ∉ C) :
    ¬ ∃ z₀ : ℂ, z₀ ∈ C ∩ K ∧ Tendsto f (𝓝[H] (ξ : ℂ)) (𝓝 z₀) := by
  rintro ⟨z₀, hz₀, hlim⟩
  have : (𝓝[H] (ξ : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  exact hp (tendsto_nhds_unique hLanding hlim ▸ hz₀.1)

/-- **R.5's ambient cover at hull landings** (the corrected form of `R5Same.R7AmbientCover`): the same conclusion,
required only at coordinates whose landing lies in the pocket. -/
def R7AmbientCoverHull [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (a : ℝ) (C : Ω → Set ℂ)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ)
    (δ : Ω → ℝ) (X : Ω → Set ℂ) (M : ℕ → Set Ω) (old : ℕ → Ω → Chart) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
    extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω → extendFrom H (relChart c γ q ω).2.1 ξ ∈ C ω →
    ∃ (i : ℕ) (x r x' d : ℝ) (z₀ : ℂ), let s := Wire.Current.SideTest.rationalOriginalTime i;
      ω ∈ M i ∧ 0 < r ∧
      (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
      Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      z₀ ∈ C ω ∩ refHull W' ζ' i ω ∧
      Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 z₀) ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c γ q ω).2.1 y ∈ H \ liveExt A γ C (refHull W' ζ' i) 0 ω) ∧
      x' ∉ forceJumpSet (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ))
        (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
          ambLift W' i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
      forceBoundaryData κ ρL' ρR' (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) x' + chiC κ * d =
        phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
          (δ ω) ξ - a

/-- **The lift-difference limit and the word identity on every selected ambient collar** (the input left to
PROVE-R5-LIFT): almost surely on the live test, at every non-jump coordinate whose landing `p` lies in the pocket off
`X`, every reference `i` of the family that is an interior visit, carries an unfilled collar at `ξ`, has `p` in its
hull and an ambient image `x′` off the ambient jumps reached by `f_s` along the current and the old approach, has a
limit `d` of "current lift − ambient lift" with `β_s(x′) + χ d` equal to the current word minus `a`. -/
def R7AmbientLiftWord [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ)
    (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (c : Ω → Chart) (a : ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ)
    (VR : Fin mR → ℝ≥0 → Ω → ℝ) (δ : Ω → ℝ) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω - segDriver (travAll R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
        segDriver (travAll R L r η ψ ω) q) →
    extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ X ω →
    extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
    ∀ (i : ℕ) (x ε x' : ℝ), let s := Wire.Current.SideTest.rationalOriginalTime i;
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
      ∃ d : ℝ,
        Tendsto (fun y => (relChart c (travAll R L r η ψ) q ω).2.2 ((relChart c (travAll R L r η ψ) q ω).2.1 y) -
          ambLift W' i ω ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
        forceBoundaryData κ ρL' ρR' (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) x' + chiC κ * d =
          phaseData κ ρL ρR
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω -
              segDriver (travAll R L r η ψ ω) q)
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
              segDriver (travAll R L r η ψ ω) q)
            (δ ω) ξ - a

/-- **The lift-difference limit and the word identity on every selected ambient collar** (pocket opening at the flow
seed; the input left to PROVE-R5-LIFT): almost surely on the live test, at every non-jump coordinate whose landing
`p` lies in the pocket off `X`, every reference `i` of the family that is an interior visit, carries an unfilled
collar at `ξ`, has `p` in its hull and an ambient image `x′` off the ambient jumps reached by `f_s` along the current
and the old approach, has a limit `d` of "current lift − ambient lift" with `β_s(x′) + χ d` equal to the current word
minus `a`. -/
def R7AmbientLiftWordInf [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ)
    (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (c : Ω → Chart) (a : ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ)
    (VR : Fin mR → ℝ≥0 → Ω → ℝ) (δ : Ω → ℝ) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
        segDriver (travAllInf R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
        segDriver (travAllInf R L r η ψ ω) q) →
    extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ X ω →
    extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
    ∀ (i : ℕ) (x ε x' : ℝ), let s := Wire.Current.SideTest.rationalOriginalTime i;
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
      ∃ d : ℝ,
        Tendsto (fun y => (relChart c (travAllInf R L r η ψ) q ω).2.2 ((relChart c (travAllInf R L r η ψ) q ω).2.1 y) -
          ambLift W' i ω ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
        forceBoundaryData κ ρL' ρR' (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) x' + chiC κ * d =
          phaseData κ ρL ρR
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
              segDriver (travAllInf R L r η ψ ω) q)
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
              segDriver (travAllInf R L r η ψ ω) q)
            (δ ω) ξ - a

section Bounded

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω} {c : Ω → Chart}
  {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **`R7AmbientCoverHull` for the reference family from the lift input** (bounded change pocket): exceptional set
`refExc ∪ X`, pair events `refEvent`, reference charts `refChart`; the force processes follow the coupling's paths
(`hpath`) and the lifetime is infinite on the test. -/
theorem r7AmbientCoverHull_of_liftWord [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {mL mR : ℕ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {α : ℝ}
    {xL₀ : Fin mL → ℝ} {xR₀ : Fin mR → ℝ} {ρL₀ : Fin mL → ℝ} {ρR₀ : Fin mR → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζ : ∀ ω ∈ A, ζ' ω = ⊤)
    (hLW : R7AmbientLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R7AmbientCoverHull κ ρL ρR ρL' ρR' P A (travAll R L r η ψ) xL xR c a (fun ω => cfPocket (R ω) (L ω) r) W' ζ'
      VL VR δ (fun ω => refExc R L r η ψ q ω ∪ X ω)
      (refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChart c R L r η ψ) q := by
  filter_upwards [ae_exists_ambient_cover hpath hcfg hψ hc hdom heq hζ q, hLW] with ω hgeo hlw hω hq ξ hξ hXω hCω
  obtain ⟨i, x, ε, x', hM, hv, hcol, hz, hland, hev, hjump, hcur, hold⟩ :=
    hgeo hω hq ξ (fun h => hXω (Or.inl h)) hCω
  obtain ⟨d, hd, hword⟩ :=
    hlw hω hq ξ hξ (fun h => hXω (Or.inr h)) hCω i x ε x' hM hv hcol hz.2 hjump hcur hold
  exact ⟨i, x, ε, x', d, _, hM, hcol.1, hcol.2.1, hcol.2.2.1, hz, hland, hev, hjump, hcur, hd, hword⟩

end Bounded

section Inf

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω} {c : Ω → Chart}
  {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}

/-- **`R7AmbientCoverHull` for the reference family from the lift input** (change pocket opening at the flow seed):
exceptional set `refExcInf ∪ X`, pair events `refEventInf`, reference charts `refChartInf`; the force processes follow
the coupling's paths (`hpath`) and the lifetime is infinite on the test. -/
theorem r7AmbientCoverHull_of_liftWordInf [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {mL mR : ℕ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {α : ℝ}
    {xL₀ : Fin mL → ℝ} {xR₀ : Fin mR → ℝ} {ρL₀ : Fin mL → ℝ} {ρR₀ : Fin mR → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (hζ : ∀ ω ∈ A, ζ' ω = ⊤)
    (hLW : R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR δ X q) :
    R7AmbientCoverHull κ ρL ρR ρL' ρR' P A (travAllInf R L r η ψ) xL xR c a (fun ω => cfPocket (R ω) (L ω) r) W' ζ'
      VL VR δ (fun ω => refExcInf R L r η ψ q ω ∪ X ω)
      (refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q) (refChartInf c R L r η ψ) q := by
  filter_upwards [ae_exists_ambient_coverInf hpath hcfg hψ hc hdom heq hζ q, hLW] with ω hgeo hlw hω hq ξ hξ hXω hCω
  obtain ⟨i, x, ε, x', hM, hv, hcol, hz, hland, hev, hjump, hcur, hold⟩ :=
    hgeo hω hq ξ (fun h => hXω (Or.inl h)) hCω
  obtain ⟨d, hd, hword⟩ :=
    hlw hω hq ξ hξ (fun h => hXω (Or.inr h)) hCω i x ε x' hM hv hcol hz.2 hjump hcur hold
  exact ⟨i, x, ε, x', d, _, hM, hcol.1, hcol.2.1, hcol.2.2.1, hz, hland, hev, hjump, hcur, hd, hword⟩

end Inf

end InteractingSLE.Sec7.R5Ref
