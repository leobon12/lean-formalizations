/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LfWord
import InteractingSLE.Spec.Sec7.R5WallOuterCoverInf

/-!
# Lemma R.5's common phase at the exposed landings on the walls (ruling R86a)

Packet PROVE-R5-LIFT2. PROVE-R5-WALL's outer lift input `R5Wall.R7OuterLiftWord(Inf)` (the lift-difference limit and
the word identity at exposed current coordinates whose landing lies on the pocket walls) at the SAME phase
`χ·2π curPhaseInt + a` as the hull identity `R5Lift.r7AmbientLiftWord_of_cur`, from the current-time comparison
(`R5Lift.ref_lift_side_of_cur_land`):

* `seed_interval_eq_empty_zero`: at relative capacity `0` the open seed interval is empty;
* `R7OuterLiftGeom`, `R7OuterLiftGeomInf` (defs, **named pathwise input**): at every exposed coordinate landing
  outside the pocket, its side is the side of its ambient image at `T = T⁰(q)`, and on every selected collar the old
  landings near the collar point lie in the ambient hull `K_s` (the reference reflects there: the "`K_s`-landing"
  reflecting set);
* **`r7OuterLiftWord_of_cur`**, **`r7OuterLiftWordInf_of_cur`**.

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

/-- **At relative capacity `0` the open seed interval is empty** (seeds at `0`). -/
theorem seed_interval_eq_empty_zero {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω} {nL nR : ℕ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0)
    (hγ : IsDrivenCurve (γ ω)) (hq : ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)) :
    Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 0 ω - segDriver (γ ω) 0)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 0 ω - segDriver (γ ω) 0) = ∅ := by
  obtain ⟨Wl, hWl, hWl0, q', hqq', hWeq, -⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  have hEq : EqOn (fun v : ℝ => (fun t ω => segDriver (γ ω) t) v.toNNReal ω) Wl (Icc 0 ((0 : ℝ≥0) : ℝ)) :=
    fun v hv => hWeq v ⟨hv.1, hv.2.trans hqq'.le⟩
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hWl hEq
  have h1 := congrFun hLeq 0
  have h2 := congrFun hReq 0
  rw [h1, h2, hxL, hxR, neg_zero, NNReal.coe_zero, rightImg_seed_zero_time (w := fun v => -Wl v) (by simp [hWl0]),
    rightImg_seed_zero_time hWl0, hWl0]
  simp

section Bounded

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The outer collars' side and reflection** (bounded change pocket; named pathwise input): almost surely on the live
test, at every non-jump exposed current coordinate `ξ` landing outside the pocket (off `X`), every real limit of
`f_T ∘ cur⁻¹` at `ξ` (`T = T⁰(q)`) lies on the side of `ξ`, and on every selected collar of `R5Wall.R7OuterLiftWord`
the old landings near the collar point lie in the ambient hull at the reference time. -/
def R7OuterLiftGeom {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω - segDriver (travAll R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
        segDriver (travAll R L r η ψ ω) q) →
    extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ X ω →
    R5Wall.exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ →
    (∀ y : ℝ, Tendsto (fun z => fwdMap (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)
        ((relChart c (travAll R L r η ψ) q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) → (ξ < 0 ↔ y < 0)) ∧
    ∀ (i : ℕ) (x ε : ℝ),
      ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r →
      IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε →
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω →
      ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
        extendFrom H (refChart c R L r η ψ i ω).2.1 u ∈
          fwdHull (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)

/-- **`R5Wall.R7OuterLiftWord` at the current phase integer** (bounded change pocket; two-seed current words with
seeds at `0`; ambient force processes of an integrated path with ordered marks and infinite lifetime): the outer lift
input holds at the phase `χ·2π curPhaseInt + a`, the phase of `R5Lift.r7AmbientLiftWord_of_cur`. -/
theorem r7OuterLiftWord_of_cur {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
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
    (h : R7LiftCurGeom P A R L r η ψ xL xR c W' q) (ho : R7OuterLiftGeom P A R L r η ψ xL xR c W' ζ' X q)
    (a : ℝ) :
    R5Wall.R7OuterLiftWord κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
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
  filter_upwards [h, ho, hex, hpath] with ω hω hoω hexω hpω hA hlive ξ hξ hX hsel i x ε x' s hM hv hcol hland
    hx' hfx hfo
  have hξI : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAll R L r η ψ ω) q) (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω -
      segDriver (travAll R L r η ψ ω) q) := not_not.1 hsel.1
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hcurland := (current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) hlive ξ).1
  -- `q > 0`: at `q = 0` the open seed interval is empty
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0 | h0
    · exfalso
      subst h0
      rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) hγ hlive] at hξI
      exact hξI
    · exact h0
  have hNspec := curPhaseInt_spec (hexω hA hlive hq0)
  -- the charts and their inverse extensions
  have hT := leftStop_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q
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
  have hd := hcurdom ω hA hlive
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  -- current landings near `ξ` lie in `K_T`; old landings near `x` lie in `K_s`
  have hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ →
      Fc v ∈ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω) := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo ξ hξI
    refine ⟨ρ, hρ, fun v hv => ?_⟩
    have hvI := hball (mem_ball_of_ofReal_mem_ball hv)
    obtain ⟨hlim, hFv⟩ := tendsto_of_ext hFc hFcc v
    refine landing_mem_hull_of_mem_seed_interval (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA)
      (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) hd hvI hlim ?_
    rw [hFv]; exact ((hω hA hlive) v hvI).1
  obtain ⟨hsideO, hrefl⟩ := hoω hA hlive ξ hξ hX hsel
  obtain ⟨ρo, hρo, hlandS'⟩ := hrefl i x ε hM hv hcol hland
  have hlandS : ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
      Fo u ∈ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) :=
    ⟨ρo, hρo, fun u hu => by rw [(tendsto_of_ext hFo hFoc u).2]; exact hlandS' u hu⟩
  obtain ⟨hlim, hside⟩ := ref_lift_side_of_cur_land hcur (hspec i ω hM).2.2.1 hFc hFcc hFo hFoc
    (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero s.coe_nonneg hT
    (by rw [hd]; exact inter_subset_right) (by rw [holddom]; exact inter_subset_right) (hspec i ω hM).2.2.2.1
    hcol.1 hcol.2.1 hlandT hlandS hx'0 hfx hfo (A := (relChart c (travAll R L r η ψ) q ω).2.2) (hNspec ξ hξI)
    hsideO
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 := (hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy)
    rw [holddom] at h1
    exact h1.2
  have hamb := mem_ambient_seed_interval (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero
    (s.coe_nonneg) ((hω hA hlive ξ hξI).1) hcurland hcurK hfx
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

end Bounded

section SeedOpen

variable [MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}

/-- **The outer collars' side and reflection** (pocket opening at the flow seed; named pathwise input): almost surely on
the live test, at every non-jump exposed current coordinate `ξ` landing outside the pocket (off `X`), every real limit
of `f_T ∘ cur⁻¹` at `ξ` (`T = T⁰(q)`) lies on the side of `ξ`, and on every selected collar of
`R5Wall.R7OuterLiftWordInf` the old landings near the collar point lie in the ambient hull at the reference time. -/
def R7OuterLiftGeomInf {nL nR : ℕ} (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω -
        segDriver (travAllInf R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
        segDriver (travAllInf R L r η ψ ω) q) →
    extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ X ω →
    R5Wall.exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ →
    (∀ y : ℝ, Tendsto (fun z => fwdMap (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) → (ξ < 0 ↔ y < 0)) ∧
    ∀ (i : ℕ) (x ε : ℝ),
      ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i →
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r →
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε →
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω →
      ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
        extendFrom H (refChartInf c R L r η ψ i ω).2.1 u ∈
          fwdHull (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)

/-- **`R5Wall.R7OuterLiftWordInf` at the current phase integer** (pocket opening at the flow seed; two-seed current
words with seeds at `0`; ambient force processes of an integrated path with ordered marks and infinite lifetime): the
outer lift input holds at the phase `χ·2π curPhaseIntInf + a`, the phase of `R5Lift.r7AmbientLiftWordInf_of_cur`. -/
theorem r7OuterLiftWordInf_of_cur {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
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
    (h : R7LiftCurGeomInf P A R L r η ψ xL xR c W' q) (ho : R7OuterLiftGeomInf P A R L r η ψ xL xR c W' ζ' X q)
    (a : ℝ) :
    R5Wall.R7OuterLiftWordInf κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
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
  filter_upwards [h, ho, hex, hpath] with ω hω hoω hexω hpω hA hlive ξ hξ hX hsel i x ε x' s hM hv hcol hland
    hx' hfx hfo
  have hξI : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAllInf R L r η ψ ω) q) (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω -
      segDriver (travAllInf R L r η ψ ω) q) := not_not.1 hsel.1
  have hγ := ((hcfg ω hA).isDrivenCurve (hψ ω hA)).1
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hcurland := (current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
    (hdom ω hA) (heq ω hA) hlive ξ).1
  -- `q > 0`: at `q = 0` the open seed interval is empty
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h0 | h0
    · exfalso
      subst h0
      rw [seed_interval_eq_empty_zero (c := c) (hxL ω) (hxR ω) hγ hlive] at hξI
      exact hξI
    · exact h0
  have hNspec := curPhaseIntInf_spec (hexω hA hlive hq0)
  -- the charts and their inverse extensions
  have hT := leftStopInf_nonneg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) q
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
  have hd := hcurdom ω hA hlive
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  -- current landings near `ξ` lie in `K_T`; old landings near `x` lie in `K_s`
  have hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ →
      Fc v ∈ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω) := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo ξ hξI
    refine ⟨ρ, hρ, fun v hv => ?_⟩
    have hvI := hball (mem_ball_of_ofReal_mem_ball hv)
    obtain ⟨hlim, hFv⟩ := tendsto_of_ext hFc hFcc v
    refine landing_mem_hull_of_mem_seed_interval (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc (hdom ω hA)
      (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) hd hvI hlim ?_
    rw [hFv]; exact ((hω hA hlive) v hvI).1
  obtain ⟨hsideO, hrefl⟩ := hoω hA hlive ξ hξ hX hsel
  obtain ⟨ρo, hρo, hlandS'⟩ := hrefl i x ε hM hv hcol hland
  have hlandS : ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
      Fo u ∈ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) :=
    ⟨ρo, hρo, fun u hu => by rw [(tendsto_of_ext hFo hFoc u).2]; exact hlandS' u hu⟩
  obtain ⟨hlim, hside⟩ := ref_lift_side_of_cur_land hcur (hspec i ω hM).2.2.1 hFc hFcc hFo hFoc
    (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero s.coe_nonneg hT
    (by rw [hd]; exact inter_subset_right) (by rw [holddom]; exact inter_subset_right) (hspec i ω hM).2.2.2.1
    hcol.1 hcol.2.1 hlandT hlandS hx'0 hfx hfo (A := (relChart c (travAllInf R L r η ψ) q ω).2.2) (hNspec ξ hξI)
    hsideO
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 := (hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy)
    rw [holddom] at h1
    exact h1.2
  have hamb := mem_ambient_seed_interval (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero
    (s.coe_nonneg) ((hω hA hlive ξ hξI).1) hcurland hcurK hfx
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

end SeedOpen

end InteractingSLE.Sec7.R5Lift
