/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftAccess
import InteractingSLE.Spec.Sec5.CfStepGeom

/-!
# Lemma R.5's common phase at hull landings with the positions and the reflection proved

Packet PROVE-R5-LIFT (round 3). `R5Ref.R7AmbientLiftWord` from a smaller pathwise input than `R7LiftGeom`: the
positions of the current and ambient coordinates (`R5LiftPos`) and the reflection of each reference at every
coordinate landing in the pocket (`R5LiftAccess`) are now proved.

* **`exists_int_common_pathwise'`**: the generic common-integer core with the reflection in derivative form;
* `R7LiftGeom'` (def, **named pathwise input**): for every interior-visit reference a preconnected set `J i ω` of real
  coordinates landing in the pocket; the references are directed (`IsDirectedRefs`); on every selected collar the
  collar point lies in `J i ω` and the current and ambient coordinates lie on the same side of their drivers;
* `R7LiftGeomInf'`, **`exists_r7AmbientLiftWordInf'`**: the same for the pocket opening at the flow seed;
* **`exists_r7AmbientLiftWord'`** (bounded change pocket, two-seed words with seeds at `0`, ordered ambient marks):
  an integer field `N` with `R5Ref.R7AmbientLiftWord` at the phase `χ·2π N ω + a`.

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

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **The common integer at one sample, reflection in derivative form.** -/
theorem exists_int_common_pathwise' {p : ℕ → ℝ≥0} {q : ℝ≥0} {Q : ℕ → Prop} (hc : (c ω).IsConformal)
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) {ℓ : ℂ → ℂ}
    (hℓ : IsDerivLog (c ω).1 ℓ (c ω).dom) (hlift : ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ z).im)
    {W : ℝ → ℝ} (hW : Continuous W) {σ : ℕ → ℝ} (hσ : ∀ i, 0 ≤ σ i) {J : ℕ → Set ℝ}
    (hQ : ∀ i, Q i → p i ≤ q ∧ ((relChart c γ (p i) ω).dom : Set ℂ) ⊆ H \ fwdHull W (σ i) ∧
      IsPreconnected (J i) ∧ ∀ x ∈ J i, ∃ b : ℝ, 0 < b ∧
        Tendsto (deriv fun y => fwdMap W (σ i) ((relChart c γ (p i) ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)))
    (hdir : IsDirectedRefs Q (fun i => relChart c γ (p i) ω) (relChart c γ q ω) J W σ) :
    ∃ n : ℤ, ∀ i (ξ : ℝ), Q i → IsGoodRef (relChart c γ (p i) ω) (relChart c γ q ω) (J i) ξ →
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
        (logDerivFwd W (σ i) ((relChart c γ q ω).2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  obtain ⟨n, hn⟩ := exists_int_common_relChart_ambLift (ι := {i : ℕ // Q i}) (p := fun i => p i.1)
    (s := fun i => σ i.1) (J := fun i => J i.1) hc hγ hq (fun i => (hQ i.1 i.2).1) hℓ hlift hW
    (fun i => hσ i.1) (fun i => (hQ i.1 i.2).2.1) (fun i => (hQ i.1 i.2).2.2.1)
    (fun i x hx => (hQ i.1 i.2).2.2.2 x hx)
    (fun i j ξ ξ' hξ hξ' => by
      rcases le_total (σ i.1) (σ j.1) with hle | hle
      · obtain ⟨hj, x, hFx, hx⟩ := hdir i.1 j.1 ξ i.2 j.2 hξ ⟨ξ', hξ'⟩ hle
        exact ⟨ξ, hξ, hj, Or.inl ⟨hle, x, hFx, hx⟩⟩
      · obtain ⟨hi, x, hFx, hx⟩ := hdir j.1 i.1 ξ' j.2 i.2 hξ' ⟨ξ, hξ⟩ hle
        exact ⟨ξ', hi, hξ', Or.inr ⟨hle, x, hFx, hx⟩⟩)
  exact ⟨n, fun i ξ hi hξ => hn ⟨i, hi⟩ ξ hξ⟩

section Bounded

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The remaining pathwise geometry of R.5's common phase** (bounded change pocket; named input): almost surely on
the live test, (b) every interior-visit reference has a preconnected set `J i ω` of real coordinates whose landings
lie in the pocket; (c) the interior-visit references are directed; (d) on every selected collar of
`R5Ref.R7AmbientLiftWord` the collar point lies in `J i ω` and `ξ` and `x′` lie on the same side of their drivers. -/
def R7LiftGeom' {nL nR mL mR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ)
    (X : Ω → Set ℂ) (J : ℕ → Ω → Set ℝ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
    (∀ i, ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r →
      IsPreconnected (J i ω) ∧
      ∀ u ∈ J i ω, extendFrom H (refChart c R L r η ψ i ω).2.1 (u : ℂ) ∈ cfPocket (R ω) (L ω) r) ∧
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
        x ∈ J i ω ∧ (ξ < 0 ↔ x' < 0)

/-- **`R5Ref.R7AmbientLiftWord` from the remaining geometry** (bounded change pocket; two-seed current words with
seeds at `0`; ambient force processes of an integrated path with ordered marks and infinite lifetime): an integer field
`N` such that the lift-difference limit is `2π N ω` and the word identity holds at the phase `χ·2π N ω + a`. -/
theorem exists_r7AmbientLiftWord' {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {J : ℕ → Ω → Set ℝ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7LiftGeom' P A R L r η ψ xL xR c W' ζ' VL VR X J q) (a : ℝ) :
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
  have hspec := refEvent_spec hcfg hψ hc hdom heq (refHull W' ζ') q
  -- the reference domains
  have hdomRef : ∀ ω ∈ A, ∀ i, ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      ((refChart c R L r η ψ i ω).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)) := by
    intro ω hA i hM
    have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
    rw [(hspec i ω hM).2.2.2.2, H_diff_liveExt_zero hA hγ, hM.2.2.2.2]
  have hex : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∃ n, Φ ω n := by
    filter_upwards [h] with ω hω hA hlive
    obtain ⟨hJ, hdir, -⟩ := hω hA hlive
    have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
    obtain ⟨E, hE, hEc⟩ := hcExt ω hA
    have hCo : IsOpen (cfPocket (R ω) (L ω) r) := by rw [← hdom ω hA]; exact (c ω).dom.isOpen
    have hCH : cfPocket (R ω) (L ω) r ⊆ H := by rw [← hdom ω hA]; exact (hc ω hA).dom_subset
    obtain ⟨n, hn⟩ := exists_int_common_pathwise' (c := c) (γ := travAll R L r η ψ) (ω := ω)
      (p := fun i => (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal)
      (Q := fun i => ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r)
      (W := fun t : ℝ => W' t.toNNReal ω) (σ := fun i => (rationalOriginalTime i : ℝ)) (J := fun i => J i ω)
      (hc ω hA) hγ hlive (hℓ ω hA).1 (hℓ ω hA).2 (hcfg ω hA).continuous_W
      (fun i => (rationalOriginalTime i).coe_nonneg)
      (fun i ⟨hM, hv⟩ => by
        have hd := hdomRef ω hA i hM
        refine ⟨hM.2.2.2.1, fun z hz => ?_, (hJ i hM hv).1, fun x hx => ?_⟩
        · have hz' : z ∈ ((refChart c R L r η ψ i ω).dom : Set ℂ) := hz
          rw [hd] at hz'
          exact hz'.2
        have hp : ((visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ≥0∞) <
            capLife (travAll R L r η ψ ω) := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hM.2.2.2.1) hlive
        have hold := (hspec i ω hM).2.2.1
        obtain ⟨Fo, hFo, hFoc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ)
          (q := (visitCap R L r η ψ ω (rationalOriginalTime i)).toNNReal) hγ hp hE hEc
        have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im]
        have hFx : Fo x = extendFrom H (refChart c R L r η ψ i ω).2.1 (x : ℂ) := by
          refine (extendFrom_eq (by rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]; exact hxbar)
            (((hFoc _ hxbar).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
              (eventually_nhdsWithin_of_forall fun y hy => hFo hy))).symm
        exact exists_pos_tendsto_deriv_of_landing_mem (old := refChart c R L r η ψ i ω) hold hFo hFoc hCo hCH
          (hcfg ω hA).trace
          (hcfg ω hA).continuous_W (hcfg ω hA).W_zero (rationalOriginalTime i).coe_nonneg hd
          (by rw [hFx]; exact (hJ i hM hv).2 x hx)) hdir
    exact ⟨n, hn⟩
  set N : Ω → ℤ := fun ω =>
    if hh : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧ ∃ n, Φ ω n then Classical.choose hh.2.2 else 0
    with hN
  refine ⟨N, ?_⟩
  filter_upwards [h, hex, hpath] with ω hω hexω hpω hA hlive ξ hξ hX hC i x ε x' s hM hv hcol hland hx' hfx hfo
  have hh : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧ ∃ n, Φ ω n := ⟨hA, hlive, hexω hA hlive⟩
  have hNspec : Φ ω (N ω) := by
    rw [hN]; simp only [hh, and_self, ↓reduceDIte]
    exact Classical.choose_spec hh.2.2
  obtain ⟨hxJ, hside⟩ := (hω hA hlive).2.2 ξ hξ hX hC i x ε x' hM hv hcol hland hx' hfx hfo
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  -- the current positions
  have hcurland := (current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) hlive ξ).1
  have hξI := mem_seed_interval_of_landing (iL := 0) (iR := 0) (hxL ω) (hxR ω) (hc ω hA) hγ hlive hcurland
    (show _ ∈ ((c ω).dom : Set ℂ) by rw [hdom ω hA]; exact hC)
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
    have h1 := (hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy)
    rw [hdomRef ω hA i hM] at h1
    exact h1.2
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by rw [← hdom ω hA]; exact (hc ω hA).dom_subset
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
  refine ⟨2 * Real.pi * N ω, hNspec i ξ ⟨hM, hv⟩ ⟨x, ε, hxJ, hcol.1, hcol.2.1, hcol.2.2.1⟩, ?_⟩
  have hvL' : ∀ i' : Fin (0 + 1), (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω -
      segDriver (travAll R L r η ψ ω) q) i' ≤ (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i
      q ω - segDriver (travAll R L r η ψ ω) q) 0 := fun i' => by rw [Fin.fin_one_eq_zero i']
  have hvR' : ∀ j' : Fin (0 + 1), (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
      segDriver (travAll R L r η ψ ω) q) 0 ≤ (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j
      q ω - segDriver (travAll R L r η ψ ω) q) j' := fun j' => by rw [Fin.fin_one_eq_zero j']
  exact word_identity_exposed ρL ρR ρL' ρR' hvL' hvR' hξI (fun _ => hVLpos) (fun _ => hVRpos) hside (N ω) a

end Bounded

section SeedOpen

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The remaining pathwise geometry of R.5's common phase** (pocket opening at the flow seed; named input): almost
surely on the live test, (b) every interior-visit reference has a preconnected set `J i ω` of real coordinates whose
landings lie in the pocket; (c) the interior-visit references are directed; (d) on every selected collar of
`R5Ref.R7AmbientLiftWordInf` the collar point lies in `J i ω` and `ξ` and `x′` lie on the same side of their drivers. -/
def R7LiftGeomInf' {nL nR mL mR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ)
    (X : Ω → Set ℂ) (J : ℕ → Ω → Set ℝ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
    (∀ i, ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r →
      IsPreconnected (J i ω) ∧
      ∀ u ∈ J i ω, extendFrom H (refChartInf c R L r η ψ i ω).2.1 (u : ℂ) ∈ cfPocket (R ω) (L ω) r) ∧
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
        x ∈ J i ω ∧ (ξ < 0 ↔ x' < 0)

/-- **`R5Ref.R7AmbientLiftWordInf` from the remaining geometry** (pocket opening at the flow seed; two-seed current
words with seeds at `0`; ambient force processes of an integrated path with ordered marks and infinite lifetime): an
integer field `N` such that the lift-difference limit is `2π N ω` and the word identity holds at the phase
`χ·2π N ω + a`. -/
theorem exists_r7AmbientLiftWordInf' {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {J : ℕ → Ω → Set ℝ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7LiftGeomInf' P A R L r η ψ xL xR c W' ζ' VL VR X J q) (a : ℝ) :
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
  have hspec := refEventInf_spec hcfg hψ hc hdom heq (refHull W' ζ') q
  -- the reference domains
  have hdomRef : ∀ ω ∈ A, ∀ i, ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      ((refChartInf c R L r η ψ i ω).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)) := by
    intro ω hA i hM
    have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
    rw [(hspec i ω hM).2.2.2.2, H_diff_liveExt_zero hA hγ, hM.2.2.2.2]
  have hex : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∃ n, Φ ω n := by
    filter_upwards [h] with ω hω hA hlive
    obtain ⟨hJ, hdir, -⟩ := hω hA hlive
    have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
    obtain ⟨E, hE, hEc⟩ := hcExt ω hA
    have hCo : IsOpen (cfPocket (R ω) (L ω) r) := by rw [← hdom ω hA]; exact (c ω).dom.isOpen
    have hCH : cfPocket (R ω) (L ω) r ⊆ H := by rw [← hdom ω hA]; exact (hc ω hA).dom_subset
    obtain ⟨n, hn⟩ := exists_int_common_pathwise' (c := c) (γ := travAllInf R L r η ψ) (ω := ω)
      (p := fun i => (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal)
      (Q := fun i => ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
        η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r)
      (W := fun t : ℝ => W' t.toNNReal ω) (σ := fun i => (rationalOriginalTime i : ℝ)) (J := fun i => J i ω)
      (hc ω hA) hγ hlive (hℓ ω hA).1 (hℓ ω hA).2 (hcfg ω hA).continuous_W
      (fun i => (rationalOriginalTime i).coe_nonneg)
      (fun i ⟨hM, hv⟩ => by
        have hd := hdomRef ω hA i hM
        refine ⟨hM.2.2.2.1, fun z hz => ?_, (hJ i hM hv).1, fun x hx => ?_⟩
        · have hz' : z ∈ ((refChartInf c R L r η ψ i ω).dom : Set ℂ) := hz
          rw [hd] at hz'
          exact hz'.2
        have hp : ((visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal : ℝ≥0∞) <
            capLife (travAllInf R L r η ψ ω) := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hM.2.2.2.1) hlive
        have hold := (hspec i ω hM).2.2.1
        obtain ⟨Fo, hFo, hFoc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ)
          (q := (visitCapInf R L r η ψ ω (rationalOriginalTime i)).toNNReal) hγ hp hE hEc
        have hxbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im]
        have hFx : Fo x = extendFrom H (refChartInf c R L r η ψ i ω).2.1 (x : ℂ) := by
          refine (extendFrom_eq (by rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]; exact hxbar)
            (((hFoc _ hxbar).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
              (eventually_nhdsWithin_of_forall fun y hy => hFo hy))).symm
        exact exists_pos_tendsto_deriv_of_landing_mem (old := refChartInf c R L r η ψ i ω) hold hFo hFoc hCo hCH
          (hcfg ω hA).trace
          (hcfg ω hA).continuous_W (hcfg ω hA).W_zero (rationalOriginalTime i).coe_nonneg hd
          (by rw [hFx]; exact (hJ i hM hv).2 x hx)) hdir
    exact ⟨n, hn⟩
  set N : Ω → ℤ := fun ω =>
    if hh : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧ ∃ n, Φ ω n then Classical.choose hh.2.2 else 0
    with hN
  refine ⟨N, ?_⟩
  filter_upwards [h, hex, hpath] with ω hω hexω hpω hA hlive ξ hξ hX hC i x ε x' s hM hv hcol hland hx' hfx hfo
  have hh : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧ ∃ n, Φ ω n := ⟨hA, hlive, hexω hA hlive⟩
  have hNspec : Φ ω (N ω) := by
    rw [hN]; simp only [hh, and_self, ↓reduceDIte]
    exact Classical.choose_spec hh.2.2
  obtain ⟨hxJ, hside⟩ := (hω hA hlive).2.2 ξ hξ hX hC i x ε x' hM hv hcol hland hx' hfx hfo
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  -- the current positions
  have hcurland := (current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) hlive ξ).1
  have hξI := mem_seed_interval_of_landing (iL := 0) (iR := 0) (hxL ω) (hxR ω) (hc ω hA) hγ hlive hcurland
    (show _ ∈ ((c ω).dom : Set ℂ) by rw [hdom ω hA]; exact hC)
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
    have h1 := (hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy)
    rw [hdomRef ω hA i hM] at h1
    exact h1.2
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by rw [← hdom ω hA]; exact (hc ω hA).dom_subset
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
  refine ⟨2 * Real.pi * N ω, hNspec i ξ ⟨hM, hv⟩ ⟨x, ε, hxJ, hcol.1, hcol.2.1, hcol.2.2.1⟩, ?_⟩
  have hvL' : ∀ i' : Fin (0 + 1), (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
      segDriver (travAllInf R L r η ψ ω) q) i' ≤ (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i
      q ω - segDriver (travAllInf R L r η ψ ω) q) 0 := fun i' => by rw [Fin.fin_one_eq_zero i']
  have hvR' : ∀ j' : Fin (0 + 1), (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
      segDriver (travAllInf R L r η ψ ω) q) 0 ≤ (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j
      q ω - segDriver (travAllInf R L r η ψ ω) q) j' := fun j' => by rw [Fin.fin_one_eq_zero j']
  exact word_identity_exposed ρL ρR ρL' ρR' hvL' hvR' hξI (fun _ => hVLpos) (fun _ => hVRpos) hside (N ω) a

end SeedOpen

end InteractingSLE.Sec7.R5Lift
