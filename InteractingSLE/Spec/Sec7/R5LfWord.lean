/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfCur

/-!
# Lemma R.5's common phase at hull landings from the current chart alone

Packet PROVE-R5-LIFT2. `R5Ref.R7AmbientLiftWord` (and its `Inf` twin) from a pathwise input about the CURRENT chart
only. The integer of the common phase is the one of the current lift minus `arg f_T′` (`T = T⁰(q)`, the left stop)
along the current open seed interval; every reference is compared with time `T` at its own collar
(`R5Lift.ref_lift_side_of_cur`). No directedness of the references and no reflecting sets are needed (they were
parts (b)–(c) of `R5Lift.R7LiftGeom'`).

* `R7LiftCurGeom`, `R7LiftCurGeomInf` (defs, **named pathwise input**): almost surely on the live test, every
  coordinate of the current open seed interval lands in `ℍ` (not at the pocket's possible real corner), and at every
  such coordinate landing in the pocket its side is the side of its ambient image at time `T`;
* **`exists_r7AmbientLiftWord_of_cur`**, **`exists_r7AmbientLiftWordInf_of_cur`**: an integer field `N` with
  `R5Ref.R7AmbientLiftWord(Inf)` at the phase `χ·2π N ω + a`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*}

/-- The value of a continuous inverse extension at a real point is the boundary limit of the chart inverse. -/
theorem tendsto_of_ext {ch : Chart} {F : ℂ → ℂ} (hF : EqOn F ch.2.1 H) (hFc : ContinuousOn F Hbar) (u : ℝ) :
    Tendsto ch.2.1 (𝓝[H] (u : ℂ)) (𝓝 (F u)) ∧ F u = extendFrom H ch.2.1 (u : ℂ) := by
  have hubar : (u : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (u : ℂ).im by rw [ofReal_im]
  have hlim : Tendsto ch.2.1 (𝓝[H] (u : ℂ)) (𝓝 (F u)) :=
    ((hFc _ hubar).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
      (eventually_nhdsWithin_of_forall fun y hy => hF hy)
  refine ⟨hlim, (extendFrom_eq ?_ hlim).symm⟩
  rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
  exact hubar

section Bounded

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The remaining pathwise geometry of R.5's common phase, in the current chart** (bounded change pocket; named
input): almost surely on the live test, every coordinate `u` of the current open seed interval lands in `ℍ`, and if
it lands in the pocket, every real limit `y` of `f_T ∘ cur⁻¹` at `u` (`T = T⁰(q)`) lies on the side of `u`. -/
def R7LiftCurGeom {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q),
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 u ∈ H ∧
      (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 u ∈ cfPocket (R ω) (L ω) r →
        ∀ y : ℝ, Tendsto (fun z => fwdMap (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)
          ((relChart c (travAll R L r η ψ) q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → (u < 0 ↔ y < 0))

/-- **The current phase integer property** (bounded change pocket): the current lift minus `arg f_T′`
(`T = T⁰(q)`, the left stop) tends to `2πn` at every point of the current open seed interval. -/
def IsCurPhaseInt {nL nR : ℕ} (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (W' : ℝ≥0 → Ω → ℝ) (q : ℝ≥0)
    (ω : Ω) (n : ℤ) : Prop :=
  ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q),
    Tendsto (fun y => (relChart c (travAll R L r η ψ) q ω).2.2 ((relChart c (travAll R L r η ψ) q ω).2.1 y) -
      (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)
        ((relChart c (travAll R L r η ψ) q ω).2.1 y)).im) (𝓝[H] (u : ℂ)) (𝓝 (2 * Real.pi * n))

/-- **The current phase integer** (bounded change pocket): a choice of `n` with `IsCurPhaseInt` (any integer where
none exists). The common phase of R.5 is `χ·2π curPhaseInt + a`. -/
def curPhaseInt {nL nR : ℕ} (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (W' : ℝ≥0 → Ω → ℝ) (q : ℝ≥0)
    (ω : Ω) : ℤ :=
  Classical.epsilon (IsCurPhaseInt R L r η ψ xL xR c W' q ω)

omit [MeasurableSpace Ω] in
theorem curPhaseInt_spec {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart}
    {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0} {ω : Ω} (h : ∃ n, IsCurPhaseInt R L r η ψ xL xR c W' q ω n) :
    IsCurPhaseInt R L r η ψ xL xR c W' q ω (curPhaseInt R L r η ψ xL xR c W' q ω) :=
  Classical.epsilon_spec h

/-- **The current phase integer exists** (bounded change pocket): almost surely on the live test at a positive
capacity, every coordinate of the current open seed interval lands in the ambient hull `K_T` (from `R7LiftCurGeom`'s
first clause and `R5Lift.landing_mem_hull_of_mem_seed_interval`), so the current transition reflects along it. -/
theorem ae_exists_isCurPhaseInt {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0} {ℓ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (h : R7LiftCurGeom P A R L r η ψ xL xR c W' q) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → 0 < q →
      ∃ n, IsCurPhaseInt R L r η ψ xL xR c W' q ω n := by
  -- the current domain off the ambient hull at `T = T⁰(q)`
  have hcurdom : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r ∩
        (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)) := by
    intro ω hA hlive
    rw [current_dom_eq (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
        (heq ω hA) hlive,
      ← (hcfg ω hA).trace.2.2 _
        (leftStop_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q)]
  filter_upwards [h] with ω hω hA hlive hq0
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hT := leftStop_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (jordan_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ) hγ hlive hE hEc
  obtain ⟨Lc, hLc, hlc⟩ :=
    Aux29Cor.exists_isDerivLog_relChart (c := c) hγ hlive (hc ω hA) (hℓ ω hA).1 (hℓ ω hA).2
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hd := hcurdom ω hA hlive
  refine exists_int_forall_tendsto_cur hcur hLc hlc hFc hFcc (hcfg ω hA).trace (hcfg ω hA).continuous_W
    (hcfg ω hA).W_zero hT (by rw [hd]; exact inter_subset_right) fun u hu => ?_
  obtain ⟨hlim, hFu⟩ := tendsto_of_ext hFc hFcc u
  refine landing_mem_hull_of_mem_seed_interval (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA)
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) hd hu hlim ?_
  rw [hFu]; exact ((hω hA hlive) u hu).1

/-- **`R5Ref.R7AmbientLiftWord` at the current phase integer** (bounded change pocket; two-seed current words
with seeds at `0`; ambient force processes of an integrated path with ordered marks and infinite lifetime): an
integer field `N` such that the lift-difference limit is `2π N ω` and the word identity holds at the phase
`χ·2π N ω + a`. -/
theorem r7AmbientLiftWord_of_cur {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7LiftCurGeom P A R L r η ψ xL xR c W' q) (a : ℝ) :
    R7AmbientLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * curPhaseInt R L r η ψ xL xR c W' q ω) + a) X q := by
  have hcurdom : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r ∩
        (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)) := by
    intro ω hA hlive
    rw [current_dom_eq (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
        (heq ω hA) hlive,
      ← (hcfg ω hA).trace.2.2 _
        (leftStop_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q)]
  have hex := ae_exists_isCurPhaseInt hcfg hψ hc hdom heq hℓ hxL hxR h
  have hspec := refEvent_spec hcfg hψ hc hdom heq (refHull W' ζ') q
  filter_upwards [h, hex, hpath] with ω hω hexω hpω hA hlive ξ hξ hX hC i x ε x' s hM hv hcol hland hx' hfx hfo
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hcurland := (current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω)
    hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
    (heq ω hA) hlive ξ).1
  -- `q > 0`: at `q = 0` no real coordinate lands in the pocket
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0 | h0
    · exfalso
      subst h0
      have hn := landing_notMem_dom hcur hcurland
      rw [relChart_zero_dom (c := c) hγ, hdom ω hA] at hn
      exact hn hC
    · exact h0
  have hNspec := curPhaseInt_spec (hexω hA hlive hq0)
  -- the charts and their inverse extensions
  have hT := leftStop_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q
  have hCo : IsOpen (cfPocket (R ω) (L ω) r) := by rw [← hdom ω hA]; exact (c ω).dom.isOpen
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by rw [← hdom ω hA]; exact (hc ω hA).dom_subset
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (jordan_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ) hγ hlive hE hEc
  have hp : ((visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ≥0∞) <
      capLife (travAll R L r η ψ ω) := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hM.2.2.2.1) hlive
  obtain ⟨Fo, hFo, hFoc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ)
    (q := (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal) hγ hp hE hEc
  have holddom : ((refChart c R L r η ψ i ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ)) := by
    rw [(hspec i ω hM).2.2.2.2, H_diff_liveExt_zero hA hγ, hM.2.2.2.2]
  have hξC : Fc ξ ∈ cfPocket (R ω) (L ω) r := by rw [(tendsto_of_ext hFc hFcc ξ).2]; exact hC
  have hxC : Fo x ∈ cfPocket (R ω) (L ω) r := by
    have h1 := (tendsto_of_ext hFo hFoc x).1
    have h2 : Tendsto (refChart c R L r η ψ i ω).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) :=
      hcol.2.2.2.1.mono_right nhdsWithin_le_nhds
    have := nhdsWithin_H_neBot x
    rw [tendsto_nhds_unique h1 h2]; exact hC
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  -- the current positions
  have hξI := mem_seed_interval_of_landing (iL := 0) (iR := 0) (hxL ω) (hxR ω) (hc ω hA) hγ hlive hcurland
    (show _ ∈ ((c ω).dom : Set ℂ) by rw [hdom ω hA]; exact hC)
  -- the comparison with the current ambient time
  obtain ⟨hlim, hside⟩ := ref_lift_side_of_cur hcur (hspec i ω hM).2.2.1 hFc hFcc hFo hFoc hCo hCH
    (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero s.coe_nonneg hT
    (hcurdom ω hA hlive) holddom (hspec i ω hM).2.2.2.1 hcol.1 hcol.2.1 hξC hxC hx'0 hfx hfo
    (A := (relChart c (travAll R L r η ψ) q ω).2.2) (hNspec ξ hξI) ((hω hA hlive ξ hξI).2 hC)
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 := (hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy)
    rw [holddom] at h1
    exact h1.2
  have hamb := mem_ambient_seed_interval (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero
    (s.coe_nonneg) (hCH hC) hcurland hcurK hfx
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h1 := (hcfg ω hA).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h1
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hpω (hζ ω hA) hV fun _ => rfl
  have hWs : W' (s : ℝ).toNNReal ω = W' s ω := by rw [Real.toNNReal_coe]
  obtain ⟨hVLpos, hVRpos⟩ := ambient_force_positions (VL := fun j => VL j s ω) (VR := fun j => VR j s ω)
    (xL := xL₀) (xR := xR₀) (hcfg ω hA).continuous_W s.coe_nonneg hxL₀ hxR₀ (fun j => hL j s)
    (fun j => hR j s) hamb
  rw [hWs] at hVLpos hVRpos
  refine ⟨2 * Real.pi * curPhaseInt R L r η ψ xL xR c W' q ω, hlim, ?_⟩
  have hvL' : ∀ i' : Fin (0 + 1), (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω -
      segDriver (travAll R L r η ψ ω) q) i' ≤ (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i
      q ω - segDriver (travAll R L r η ψ ω) q) 0 := fun i' => by rw [Fin.fin_one_eq_zero i']
  have hvR' : ∀ j' : Fin (0 + 1), (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
      segDriver (travAll R L r η ψ ω) q) 0 ≤ (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j
      q ω - segDriver (travAll R L r η ψ ω) q) j' := fun j' => by rw [Fin.fin_one_eq_zero j']
  exact word_identity_exposed ρL ρR ρL' ρR' hvL' hvR' hξI (fun _ => hVLpos) (fun _ => hVRpos) hside
    (curPhaseInt R L r η ψ xL xR c W' q ω) a


/-- **`R5Ref.R7AmbientLiftWord` from the current chart's geometry** (bounded change pocket): an integer field `N`
(the current phase integer) such that the lift-difference limit is `2π N ω` and the word identity holds at the phase
`χ·2π N ω + a`. -/
theorem exists_r7AmbientLiftWord_of_cur {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7LiftCurGeom P A R L r η ψ xL xR c W' q) (a : ℝ) :
    ∃ N : Ω → ℤ, R7AmbientLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * N ω) + a) X q :=
  ⟨_, r7AmbientLiftWord_of_cur (κ := κ) (ρL := ρL) (ρR := ρR) hcfg hψ hc hdom heq hℓ hxL hxR hpath hζ hxL₀ hxR₀ h a⟩

end Bounded

section SeedOpen

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The remaining pathwise geometry of R.5's common phase, in the current chart** (pocket opening at the flow seed;
named input): almost surely on the live test, every coordinate `u` of the current open seed interval lands in `ℍ`, and
if it lands in the pocket, every real limit `y` of `f_T ∘ cur⁻¹` at `u` (`T = T⁰(q)`) lies on the side of `u`. -/
def R7LiftCurGeomInf {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
    ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω - segDriver (travAllInf R L r η ψ ω) q)
        (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q),
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 u ∈ H ∧
      (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 u ∈ cfPocket (R ω) (L ω) r →
        ∀ y : ℝ, Tendsto (fun z => fwdMap (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)
          ((relChart c (travAllInf R L r η ψ) q ω).2.1 z)) (𝓝[H] (u : ℂ)) (𝓝 (y : ℂ)) → (u < 0 ↔ y < 0))

/-- **The current phase integer property** (pocket opening at the flow seed): the current lift minus `arg f_T′`
(`T = T⁰(q)`, the left stop) tends to `2πn` at every point of the current open seed interval. -/
def IsCurPhaseIntInf {nL nR : ℕ} (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (W' : ℝ≥0 → Ω → ℝ) (q : ℝ≥0)
    (ω : Ω) (n : ℤ) : Prop :=
  ∀ u ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω - segDriver (travAllInf R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q),
    Tendsto (fun y => (relChart c (travAllInf R L r η ψ) q ω).2.2 ((relChart c (travAllInf R L r η ψ) q ω).2.1 y) -
      (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)).im) (𝓝[H] (u : ℂ)) (𝓝 (2 * Real.pi * n))

/-- **The current phase integer** (pocket opening at the flow seed): a choice of `n` with `IsCurPhaseIntInf` (any
integer where none exists). The common phase of R.5 is `χ·2π curPhaseIntInf + a`. -/
def curPhaseIntInf {nL nR : ℕ} (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (W' : ℝ≥0 → Ω → ℝ) (q : ℝ≥0)
    (ω : Ω) : ℤ :=
  Classical.epsilon (IsCurPhaseIntInf R L r η ψ xL xR c W' q ω)

omit [MeasurableSpace Ω] in
theorem curPhaseIntInf_spec {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart}
    {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0} {ω : Ω} (h : ∃ n, IsCurPhaseIntInf R L r η ψ xL xR c W' q ω n) :
    IsCurPhaseIntInf R L r η ψ xL xR c W' q ω (curPhaseIntInf R L r η ψ xL xR c W' q ω) :=
  Classical.epsilon_spec h

/-- **The current phase integer exists** (pocket opening at the flow seed): almost surely on the live test at a positive
capacity, every coordinate of the current open seed interval lands in the ambient hull `K_T` (from `R7LiftCurGeomInf`'s
first clause and `R5Lift.landing_mem_hull_of_mem_seed_interval`), so the current transition reflects along it. -/
theorem ae_exists_isCurPhaseIntInf {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ} {xR : Ω → Fin (0 + 1) → ℝ}
    {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {q : ℝ≥0} {ℓ : Ω → ℂ → ℂ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (h : R7LiftCurGeomInf P A R L r η ψ xL xR c W' q) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → 0 < q →
      ∃ n, IsCurPhaseIntInf R L r η ψ xL xR c W' q ω n := by
  -- the current domain off the ambient hull at `T = T⁰(q)`
  have hcurdom : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r ∩
        (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)) := by
    intro ω hA hlive
    rw [current_dom_eqInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
        (heq ω hA) hlive,
      ← (hcfg ω hA).trace.2.2 _
        (leftStopInf_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q)]
  filter_upwards [h] with ω hω hA hlive hq0
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hT := leftStopInf_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (Or.inr (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hlive hE hEc
  obtain ⟨Lc, hLc, hlc⟩ :=
    Aux29Cor.exists_isDerivLog_relChart (c := c) hγ hlive (hc ω hA) (hℓ ω hA).1 (hℓ ω hA).2
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hd := hcurdom ω hA hlive
  refine exists_int_forall_tendsto_cur hcur hLc hlc hFc hFcc (hcfg ω hA).trace (hcfg ω hA).continuous_W
    (hcfg ω hA).W_zero hT (by rw [hd]; exact inter_subset_right) fun u hu => ?_
  obtain ⟨hlim, hFu⟩ := tendsto_of_ext hFc hFcc u
  refine landing_mem_hull_of_mem_seed_interval (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA)
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) hd hu hlim ?_
  rw [hFu]; exact ((hω hA hlive) u hu).1

/-- **`R5Ref.R7AmbientLiftWordInf` at the current phase integer** (pocket opening at the flow seed; two-seed current
words with seeds at `0`; ambient force processes of an integrated path with ordered marks and infinite lifetime): an
integer field `N` such that the lift-difference limit is `2π N ω` and the word identity holds at the phase `χ·2π N ω +
a`. -/
theorem r7AmbientLiftWordInf_of_cur {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7LiftCurGeomInf P A R L r η ψ xL xR c W' q) (a : ℝ) :
    R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * curPhaseIntInf R L r η ψ xL xR c W' q ω) + a) X q := by
  have hcurdom : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r ∩
        (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)) := by
    intro ω hA hlive
    rw [current_dom_eqInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
        (heq ω hA) hlive,
      ← (hcfg ω hA).trace.2.2 _
        (leftStopInf_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q)]
  have hex := ae_exists_isCurPhaseIntInf hcfg hψ hc hdom heq hℓ hxL hxR h
  have hspec := refEventInf_spec hcfg hψ hc hdom heq (refHull W' ζ') q
  filter_upwards [h, hex, hpath] with ω hω hexω hpω hA hlive ξ hξ hX hC i x ε x' s hM hv hcol hland hx' hfx hfo
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hcurland := (current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω)
    hA (hcfg ω hA) (hψ ω hA) (hc ω hA) (hdom ω hA)
    (heq ω hA) hlive ξ).1
  -- `q > 0`: at `q = 0` no real coordinate lands in the pocket
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0 | h0
    · exfalso
      subst h0
      have hn := landing_notMem_dom hcur hcurland
      rw [relChart_zero_dom (c := c) hγ, hdom ω hA] at hn
      exact hn hC
    · exact h0
  have hNspec := curPhaseIntInf_spec (hexω hA hlive hq0)
  -- the charts and their inverse extensions
  have hT := leftStopInf_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q
  have hCo : IsOpen (cfPocket (R ω) (L ω) r) := by rw [← hdom ω hA]; exact (c ω).dom.isOpen
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by rw [← hdom ω hA]; exact (hc ω hA).dom_subset
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (Or.inr (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hlive hE hEc
  have hp : ((visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ≥0∞) <
      capLife (travAllInf R L r η ψ ω) := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hM.2.2.2.1) hlive
  obtain ⟨Fo, hFo, hFoc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ)
    (q := (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal) hγ hp hE hEc
  have holddom : ((refChartInf c R L r η ψ i ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ)) := by
    rw [(hspec i ω hM).2.2.2.2, H_diff_liveExt_zero hA hγ, hM.2.2.2.2]
  have hξC : Fc ξ ∈ cfPocket (R ω) (L ω) r := by rw [(tendsto_of_ext hFc hFcc ξ).2]; exact hC
  have hxC : Fo x ∈ cfPocket (R ω) (L ω) r := by
    have h1 := (tendsto_of_ext hFo hFoc x).1
    have h2 : Tendsto (refChartInf c R L r η ψ i ω).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) :=
      hcol.2.2.2.1.mono_right nhdsWithin_le_nhds
    have := nhdsWithin_H_neBot x
    rw [tendsto_nhds_unique h1 h2]; exact hC
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  -- the current positions
  have hξI := mem_seed_interval_of_landing (iL := 0) (iR := 0) (hxL ω) (hxR ω) (hc ω hA) hγ hlive hcurland
    (show _ ∈ ((c ω).dom : Set ℂ) by rw [hdom ω hA]; exact hC)
  -- the comparison with the current ambient time
  obtain ⟨hlim, hside⟩ := ref_lift_side_of_cur hcur (hspec i ω hM).2.2.1 hFc hFcc hFo hFoc hCo hCH
    (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero s.coe_nonneg hT
    (hcurdom ω hA hlive) holddom (hspec i ω hM).2.2.2.1 hcol.1 hcol.2.1 hξC hxC hx'0 hfx hfo
    (A := (relChart c (travAllInf R L r η ψ) q ω).2.2) (hNspec ξ hξI) ((hω hA hlive ξ hξI).2 hC)
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 := (hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy)
    rw [holddom] at h1
    exact h1.2
  have hamb := mem_ambient_seed_interval (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero
    (s.coe_nonneg) (hCH hC) hcurland hcurK hfx
  have hV : Continuous fun t : ℝ≥0 => W' t ω := by
    have h1 := (hcfg ω hA).continuous_W.comp NNReal.continuous_coe
    simpa only [Function.comp_def, Real.toNNReal_coe] using h1
  obtain ⟨hL, hR⟩ := Sec5.CfStep.force_eq_geom_of_path_top hpω (hζ ω hA) hV fun _ => rfl
  have hWs : W' (s : ℝ).toNNReal ω = W' s ω := by rw [Real.toNNReal_coe]
  obtain ⟨hVLpos, hVRpos⟩ := ambient_force_positions (VL := fun j => VL j s ω) (VR := fun j => VR j s ω)
    (xL := xL₀) (xR := xR₀) (hcfg ω hA).continuous_W s.coe_nonneg hxL₀ hxR₀ (fun j => hL j s)
    (fun j => hR j s) hamb
  rw [hWs] at hVLpos hVRpos
  refine ⟨2 * Real.pi * curPhaseIntInf R L r η ψ xL xR c W' q ω, hlim, ?_⟩
  have hvL' : ∀ i' : Fin (0 + 1), (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
      segDriver (travAllInf R L r η ψ ω) q) i' ≤ (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i
      q ω - segDriver (travAllInf R L r η ψ ω) q) 0 := fun i' => by rw [Fin.fin_one_eq_zero i']
  have hvR' : ∀ j' : Fin (0 + 1), (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
      segDriver (travAllInf R L r η ψ ω) q) 0 ≤ (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j
      q ω - segDriver (travAllInf R L r η ψ ω) q) j' := fun j' => by rw [Fin.fin_one_eq_zero j']
  exact word_identity_exposed ρL ρR ρL' ρR' hvL' hvR' hξI (fun _ => hVLpos) (fun _ => hVRpos) hside
    (curPhaseIntInf R L r η ψ xL xR c W' q ω) a


/-- **`R5Ref.R7AmbientLiftWordInf` from the current chart's geometry** (pocket opening at the flow seed): an integer
field `N` (the current phase integer) such that the lift-difference limit is `2π N ω` and the word identity holds at the
phase `χ·2π N ω + a`. -/
theorem exists_r7AmbientLiftWordInf_of_cur {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7LiftCurGeomInf P A R L r η ψ xL xR c W' q) (a : ℝ) :
    ∃ N : Ω → ℤ, R7AmbientLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * N ω) + a) X q :=
  ⟨_, r7AmbientLiftWordInf_of_cur (κ := κ) (ρL := ρL) (ρR := ρR) hcfg hψ hc hdom heq hℓ hxL hxR hpath hζ hxL₀ hxR₀ h a⟩

end SeedOpen

end InteractingSLE.Sec7.R5Lift
