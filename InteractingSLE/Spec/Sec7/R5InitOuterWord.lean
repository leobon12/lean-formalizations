/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5InitLiftOutInf
import InteractingSLE.Spec.Sec7.R5LfOuter
import InteractingSLE.Spec.Sec7.R5LfCur

/-!
# R.5's outer lift word on outer pockets at collars with an ambient half-disc (ruling R88)

Packet PROVE-R5-INIT (outer round). `R5Wall.R7OuterLiftWord` asks the current lift against the ambient lift at *every*
reference collar; the extremal proof (`R5Lift.r7OuterLiftWord_of_cur`) needs `R5Lift.R7OuterLiftGeom`, i.e. the
reflection through the reference chart (`R5Lift.R7OuterRefl`, from the clipped wall orders of WALL-ORDER), which is not
available on outer arms (R97). The outer cover of PROVE-R5-OUTER only uses the lift word at collars carrying an ambient
half-disc `f_s⁻¹(ℍ ∩ B(x′, ρ)) ⊆` current domain (`R5Out.R7OuterAmbientGeometry`), and there the reflection is
through the ambient map itself (`ref_lift_side_of_cur_amb`). This file states that form
(`R7OuterLiftWordAmb`, `R7OuterLiftWordInfAmb`: the extra premise inserted before the conclusion) and proves it on outer
pockets from the seed-interval landings `R5Fresh.R7SeedLand(Inf)` alone:
* **`ref_lift_side_of_cur_amb`**: the lift/side comparison of `R5Lift.ref_lift_side_of_cur_land` with the old chart
  replaced by the ambient half-disc;
* **`r7OuterLiftWordAmb_of_seedLand_outer`**, **`r7OuterLiftWordInfAmb_of_seedLand_outer`**, with the phase
  `χ·2π curPhaseInt + a` of `r7AmbientLiftWord_of_cur_outer`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC IsForwardSol)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Init

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide PhaseSel
  PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same R5Ref Sec6 PocketStopWallsFin R5Lift
  R5Fresh R5Out PocketStopMarked MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)
open R5Wall (exposedOuterSel)

section Generic

/-- **The current lift against the ambient chart at time `s`, from an ambient half-disc** (`ref_lift_side_of_cur_land`
with the old chart's hull landings replaced by an ambient half-disc `f_s⁻¹(ℍ ∩ B(x′, ρ)) ⊆ cur.dom`, the R98 form of
the outer collars): if a lift `A` minus `arg f_T′` tends to `d` along `cur⁻¹` at `ξ`, so does `A − arg f_s′`, and the
side of `ξ` is the side of `x′`. -/
theorem ref_lift_side_of_cur_amb {cur : Chart} (hcur : cur.IsConformal)
    {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H) (hFcc : ContinuousOn Fc Hbar)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s T : ℝ}
    (hs : 0 ≤ s) (hT : 0 ≤ T)
    (hKT : (cur.dom : Set ℂ) ⊆ H \ fwdHull W T) (hKs : (cur.dom : Set ℂ) ⊆ H \ fwdHull W s) {ξ x' ρ : ℝ}
    (hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ → Fc v ∈ fwdHull W T)
    (hρ : 0 < ρ) (hfree : fwdMapInv W s '' (H ∩ ball (x' : ℂ) ρ) ⊆ cur.dom) (hx'0 : x' ≠ 0)
    (hfx : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)))
    {A : ℂ → ℝ} {d : ℝ}
    (hn : Tendsto (fun y => A (cur.2.1 y) - (logDerivFwd W T (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 d))
    (hside : ∀ y : ℝ, Tendsto (fun z => fwdMap W T (cur.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) →
      (ξ < 0 ↔ y < 0)) :
    Tendsto (fun y => A (cur.2.1 y) - (logDerivFwd W s (cur.2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
      (ξ < 0 ↔ x' < 0) := by
  have := nhdsWithin_H_neBot ξ
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), cur.2.1 y ∈ H \ fwdHull W T :=
    eventually_nhdsWithin_of_forall fun y hy => hKT (hcur.inv_mem_dom hy)
  have hcurKs : ∀ᶠ y in 𝓝[H] (ξ : ℂ), cur.2.1 y ∈ H \ fwdHull W s :=
    eventually_nhdsWithin_of_forall fun y hy => hKs (hcur.inv_mem_dom hy)
  rcases le_total s T with hsT | hTs
  · -- the ambient half-disc about `x′` lies in `f_s(ℍ ∖ K_T)`
    have hsub' : H ∩ ball (x' : ℂ) ρ ⊆ fwdMap W s '' (H \ fwdHull W T) := fun w hw =>
      ⟨fwdMapInv W s w, hKT (hfree ⟨w, hw, rfl⟩), QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hs hw.1⟩
    have hxK := notMem_closure_incrHull_of_subset_image hW hs hsT hρ hsub'
    have hcomp := tendsto_im_logDerivFwd_sub_of_notMem_closure hW hs hsT hcurK hfx hxK
    refine ⟨?_, ?_⟩
    · have h := hn.add hcomp
      rw [add_zero] at h
      exact h.congr fun y => by ring
    · obtain ⟨y, hy, hyside⟩ := tendsto_fwdMap_of_alive hW hs hsT hcurK hx'0 hfx hxK
      exact (hside y hy).trans hyside
  · -- the current transition at time `T` covers a half-disc inside `f_T(ℍ ∖ K_s)`
    obtain ⟨ρ, hρ, hlandK⟩ := hlandT
    obtain ⟨hgΦ, hgc, hgreal, hmaps, hinj, hgd, hglim⟩ := reflect_data_of_hull_landing (x := ξ) (ρ := ρ) hcur
      hFc hFcc hη hW hW0 hT hKT hlandK
    have hξbar : (ξ : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (ξ : ℂ).im by rw [ofReal_im]
    set g := extendFrom H fun y => fwdMap W T (cur.2.1 y) with hg
    set y₀ : ℝ := (g ξ).re with hy₀
    have hgreal' : g ξ = (y₀ : ℂ) :=
      Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im]; exact hgreal _ (mem_ball_self hρ) (ofReal_im ξ))
    have hy₀T : Tendsto (fun y => fwdMap W T (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (y₀ : ℂ)) := by
      rw [← hgreal']; exact hglim ξ ⟨hξbar, mem_ball_self hρ⟩
    obtain ⟨ρ', hρ', hsub⟩ := exists_halfBall_subset_image_of_reflect hρ hgd hgc hgreal hmaps hinj
    rw [hgreal'] at hsub
    have hsub' : H ∩ ball (y₀ : ℂ) ρ' ⊆ fwdMap W T '' (H \ fwdHull W s) := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hsub hw
      exact ⟨cur.2.1 z, hKs (hcur.inv_mem_dom hz.1), (hgΦ hz)⟩
    have hyK := notMem_closure_incrHull_of_subset_image hW hT hTs hρ' hsub'
    have hcomp := tendsto_im_logDerivFwd_sub_of_notMem_closure hW hT hTs hcurKs hy₀T hyK
    refine ⟨?_, ?_⟩
    · have h := hn.sub hcomp
      rw [sub_zero] at h
      exact h.congr fun y => by ring
    · have hy₀0 : y₀ ≠ 0 := by
        rcases hTs.lt_or_eq with hlt | heq
        · intro h0
          apply hyK
          rw [h0, ofReal_zero]
          exact ConformalImageFull.zero_mem_closure_fwdHull
            ((hW.comp (continuous_const.add continuous_id)).sub continuous_const) (by simp) (sub_pos.2 hlt)
        · subst heq
          have h1 : (y₀ : ℂ) = (x' : ℂ) := tendsto_nhds_unique hy₀T hfx
          have h2 : y₀ = x' := by exact_mod_cast h1
          exact fun h0 => hx'0 (h2 ▸ h0)
      obtain ⟨z, hz, hzside⟩ := tendsto_fwdMap_of_alive hW hT hTs hcurKs hy₀0 hy₀T hyK
      have hzx : z = x' := by exact_mod_cast tendsto_nhds_unique hz hfx
      rw [hzx] at hzside
      exact (hside y₀ hy₀T).trans hzside.symm


end Generic

variable {Ω : Type*}

section Defs

/-- **`R5Wall.R7OuterLiftWord` at the collars carrying an ambient half-disc** (R98: the outer cover selects a
collar with `f_s⁻¹(ℍ ∩ B(x′, ρ))` in the current domain, `R5Out.R7OuterAmbientGeometry`; the lift word is asked only
there). -/
def R7OuterLiftWordAmb [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ)
    (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (c : Ω → Chart) (a : ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ)
    (VR : Fin mR → ℝ≥0 → Ω → ℝ) (δ : Ω → ℝ) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL i q ω - segDriver (travAll R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR j q ω -
        segDriver (travAll R L r η ψ ω) q) →
    extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ X ω →
    exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ →
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
      ∀ ρ : ℝ, 0 < ρ → QuantumZipper.fwdMapInv (fun t : ℝ => W' t.toNNReal ω) s '' (H ∩ ball (x' : ℂ) ρ) ⊆
        ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) →
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


/-- **`R5Wall.R7OuterLiftWordInf` at the collars carrying an ambient half-disc** (R98: the outer cover selects a
collar with `f_s⁻¹(ℍ ∩ B(x′, ρ))` in the current domain, `R5Out.R7OuterAmbientGeometry`; the lift word is asked only
there). -/
def R7OuterLiftWordInfAmb [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {mL mR : ℕ} (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) (P : Measure Ω) (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ)
    (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (c : Ω → Chart) (a : ℝ) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ)
    (VR : Fin mR → ℝ≥0 → Ω → ℝ) (δ : Ω → ℝ) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL i q ω - segDriver
        (travAllInf R L r η ψ ω) q)
      (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR j q ω -
        segDriver (travAllInf R L r η ψ ω) q) →
    extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ X ω →
    exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ →
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
      ∀ ρ : ℝ, 0 < ρ → QuantumZipper.fwdMapInv (fun t : ℝ => W' t.toNNReal ω) s '' (H ∩ ball (x' : ℂ) ρ) ⊆
        ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) →
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
end Defs

section Proofs

variable [MeasurableSpace Ω] {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

/-- **`R7OuterLiftWordAmb` on outer pockets from the seed-interval landings** (the phase `χ·2π curPhaseInt + a` of
`r7AmbientLiftWord_of_cur_outer`; the ambient half-disc replaces the extremal `R5Lift.R7OuterRefl`). -/
theorem r7OuterLiftWordAmb_of_seedLand_outer {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7SeedLand P A R L r η ψ xL xR c q)
    (a : ℝ) :
    R7OuterLiftWordAmb κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * curPhaseInt R L r η ψ xL xR c W' q ω) + a) X q := by
  have hcursub : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r ∩
        (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω)) := fun ω hA hlive =>
    current_dom_subset_ambient (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive
  have hcurfr : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      frontier ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ∩ cfPocket (R ω) (L ω) r ⊆
        fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω) := fun ω hA hlive =>
    frontier_cur_dom_subset_outer (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive
  have hLC := r7LiftCurGeom_of_seedLand_outer (W' := W') hcfg hψ hc hdom heq hxL hxR h
  have hsideAE := ae_curSide_of_seedLand_outer (W' := W') hcfg hψ hc hdom heq hxL hxR h
  have hex := ae_exists_isCurPhaseInt_outer hcfg hψ hc hdom heq hℓ hxL hxR hLC
  have hspec := R5Out.refEvent_spec hcfg hψ hc hdom heq (refHull W' ζ') q
  filter_upwards [hLC, hsideAE, hex, hpath] with ω hω hsω hexω hpω hA hlive ξ hξ hX hsel i x ε x' s hM hv hcol
    hland hx' hfx hfo ρf hρf hfree
  have hξI : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAll R L r η ψ ω) q) (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω -
      segDriver (travAll R L r η ψ ω) q) := not_not.1 hsel.1
  have hγ := ((hcfg ω hA).props (hψ ω hA)).1
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hcurland := (R5Out.current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) (hc ω hA)
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
  have hT := leftStop_nonneg_outer (ψ := ψ) (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) q
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (R5Out.jordan_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ) hγ hlive hE hEc
  have holdsub : ((refChart c R L r η ψ i ω).dom : Set ℂ) ⊆
      cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ)) := by
    have h1 := (hspec i ω hM).2.2.2.2
    rwa [R5Phase.H_diff_liveExt_zero hA hγ, hM.2.2.2.2] at h1
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  -- current landings near `ξ` lie in `K_T`
  have hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ →
      Fc v ∈ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStop R L r η ψ q ω) := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo ξ hξI
    refine ⟨ρ, hρ, fun v hv => ?_⟩
    have hvI := hball (mem_ball_of_ofReal_mem_ball hv)
    obtain ⟨hlim, hFv⟩ := tendsto_of_ext hFc hFcc v
    refine landing_mem_hull_of_mem_seed_interval_of_frontier (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc
      (hdom ω hA) (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) (hcurfr ω hA hlive) hvI hlim
      ?_
    rw [hFv]; exact ((hω hA hlive) v hvI).1
  have hsideO := hsω hA hlive ξ hξI
  obtain ⟨hlim, hside⟩ := ref_lift_side_of_cur_amb hcur hFc hFcc
    (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero s.coe_nonneg hT
    ((hcursub ω hA hlive).trans inter_subset_right)
    (fun z hz => (holdsub ((hspec i ω hM).2.2.2.1 hz)).2) hlandT hρf hfree hx'0 hfx
    (A := (relChart c (travAll R L r η ψ) q ω).2.2) (hNspec ξ hξI) hsideO
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    exact (holdsub ((hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy))).2
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


/-- **`R7OuterLiftWordInfAmb` on outer pockets from the seed-interval landings** (the phase `χ·2π curPhaseIntInf + a` of
`r7AmbientLiftWordInf_of_cur_outer`; the ambient half-disc replaces the extremal `R5Lift.R7OuterRefl`). -/
theorem r7OuterLiftWordInfAmb_of_seedLand_outer {κ : ℝ} {ρL : Fin (0 + 1) → ℝ} {ρR : Fin (0 + 1) → ℝ} {mL mR : ℕ}
    {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {xL : Ω → Fin (0 + 1) → ℝ}
    {xR : Ω → Fin (0 + 1) → ℝ} {c : Ω → Chart} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {X : Ω → Set ℂ} {q : ℝ≥0}
    {ℓ : Ω → ℂ → ℂ} {α : ℝ} {xL₀ ρL₀ : Fin mL → ℝ} {xR₀ ρR₀ : Fin mR → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧ ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hxL : ∀ ω, xL ω 0 = 0) (hxR : ∀ ω, xR ω 0 = 0)
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath α xL₀ xR₀ ρL₀ ρR₀ (fun t => W' t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (ζ' ω))
    (hζ : ∀ ω ∈ A, ζ' ω = ⊤) (hxL₀ : ∀ i, xL₀ i ≤ 0) (hxR₀ : ∀ j, 0 ≤ xR₀ j)
    (h : R7SeedLandInf P A R L r η ψ xL xR c q)
    (a : ℝ) :
    R7OuterLiftWordInfAmb κ ρL ρR ρL' ρR' P A R L r η ψ xL xR c a W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * curPhaseIntInf R L r η ψ xL xR c W' q ω) + a) X q := by
  have hcursub : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r ∩
        (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω)) := fun ω hA hlive =>
    current_dom_subset_ambientInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive
  have hcurfr : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      frontier ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ∩ cfPocket (R ω) (L ω) r ⊆
        fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω) := fun ω hA hlive =>
    frontier_cur_dom_subset_outerInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hA (hcfg ω hA) (hψ ω hA) (hc ω hA)
      (hdom ω hA) (heq ω hA) hlive
  have hLC := r7LiftCurGeomInf_of_seedLand_outer (W' := W') hcfg hψ hc hdom heq hxL hxR h
  have hsideAE := ae_curSideInf_of_seedLand_outer (W' := W') hcfg hψ hc hdom heq hxL hxR h
  have hex := ae_exists_isCurPhaseIntInf_outer hcfg hψ hc hdom heq hℓ hxL hxR hLC
  have hspec := R5Out.refEventInf_spec hcfg hψ hc hdom heq (refHull W' ζ') q
  filter_upwards [hLC, hsideAE, hex, hpath] with ω hω hsω hexω hpω hA hlive ξ hξ hX hsel i x ε x' s hM hv hcol
    hland hx' hfx hfo ρf hρf hfree
  have hξI : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAllInf R L r η ψ ω) q) (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω -
      segDriver (travAllInf R L r η ψ ω) q) := not_not.1 hsel.1
  have hγ := ((hcfg ω hA).props (hψ ω hA)).1
  have hcur := isConformal_relChart_of_driven (c := c) hγ hlive (hc ω hA)
  have hcurland := (R5Out.current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) (hψ ω hA) (hc ω hA)
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
  have hT := leftStopInf_nonneg_outer (ψ := ψ) (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hA) q
  obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases
    (Or.inr (hψ ω hA))
    (hc ω hA) (hdom ω hA) (heq ω hA)
  obtain ⟨Fc, hFc, hFcc, -⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hlive hE hEc
  have holdsub : ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ⊆
      cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ)) := by
    have h1 := (hspec i ω hM).2.2.2.2
    rwa [R5Phase.H_diff_liveExt_zero hA hγ, hM.2.2.2.2] at h1
  have hx'0 : x' ≠ 0 := fun h0 => hx' (h0 ▸ Set.mem_insert 0 _)
  -- current landings near `ξ` lie in `K_T`
  have hlandT : ∃ ρ > 0, ∀ v : ℝ, (v : ℂ) ∈ ball (ξ : ℂ) ρ →
      Fc v ∈ fwdHull (fun t : ℝ => W' t.toNNReal ω) (leftStopInf R L r η ψ q ω) := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo ξ hξI
    refine ⟨ρ, hρ, fun v hv => ?_⟩
    have hvI := hball (mem_ball_of_ofReal_mem_ball hv)
    obtain ⟨hlim, hFv⟩ := tendsto_of_ext hFc hFcc v
    refine landing_mem_hull_of_mem_seed_interval_of_frontier (hxL ω) (hxR ω) (hc ω hA) hγ hlive hq0 hE hEc
      (hdom ω hA) (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hcfg ω hA).continuous_W hT) (hcurfr ω hA hlive) hvI hlim
      ?_
    rw [hFv]; exact ((hω hA hlive) v hvI).1
  have hsideO := hsω hA hlive ξ hξI
  obtain ⟨hlim, hside⟩ := ref_lift_side_of_cur_amb hcur hFc hFcc
    (hcfg ω hA).trace (hcfg ω hA).continuous_W (hcfg ω hA).W_zero s.coe_nonneg hT
    ((hcursub ω hA hlive).trans inter_subset_right)
    (fun z hz => (holdsub ((hspec i ω hM).2.2.2.1 hz)).2) hlandT hρf hfree hx'0 hfx
    (A := (relChart c (travAllInf R L r η ψ) q ω).2.2) (hNspec ξ hξI) hsideO
  -- the ambient positions
  have hcurK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
      H \ fwdHull (fun t : ℝ => W' t.toNNReal ω) (s : ℝ) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    exact (holdsub ((hspec i ω hM).2.2.2.1 (hcur.inv_mem_dom hy))).2
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


end Proofs

end InteractingSLE.Sec7.R5Init
