/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HQNoContact
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitBase
import InteractingSLE.Spec.Supplement.CounterflowNoReturnBack

/-!
# Proposition 5.1's forward route in the chart `Q`: the post-contact barrier reduced to its two genuine cases

Packet PROVE-PROP51H, `FwdPostContactQOn` (PROVE-PROP51G's post-contact input: Lemma 5.4 after a contact, with the
eastern junction of R50 / Astra C). In the counterflow chart `Ψ = revChart w s` the eastern part of
`∂(ℍ ∖ R(K_s))` is the positive half-line: `(0, junR)` is the image of `ℝ₊`, `junR = Ψ(∞⁺)` is the eastern end of `∞`,
and `(junR, ∞)` is the eastern side of the hull. For a proper arc `η` (the flow line) and a regular counterflow
(continuous driver from `0`, Loewner trace, no return to `0`), two of the four ways for an excursion of `η` in
`ℍ ∖ R(K_s)` to end in the eastern part are impossible **deterministically**:

* at a finite end time `u₀`, a cluster point in `(0, junR]` would make `R(η(u₀)) ∈ ℍ` a boundary value
  `F̄_s(y)` at a point `y` at or left of the image of `0⁻`, which is not in `ℍ`;
* as `u → ∞`, a cluster point in `(0, ∞) ∖ {junR}` would make `F̄_s(y) = 0` for a real `y < 0`, `y` not the image of
  `0⁻` (an alive point left of the hull, or a point of the hull's eastern side, which the no-return excludes).

What remains (`PostContactEastResidual`) is exactly the probabilistic content of the source: **(E1)** a finite-time
end on the eastern side proper (Lemma 5.4's barrier, Lemma 5.2 / Aux. lemma 26 with the retained post-contact
comparison of Aux. lemmas 61–65) and **(E2)** an end at the eastern end of `∞` (R50, Astra C.2–C.3).

* `extendFrom_ne_zero_of_noReturn_left`: the left-side counterpart of `Prop49Exit.extendFrom_ne_zero_of_noReturn`;
* `mapClusterPt_negInv_of_revChart`: a cluster point of `Ψ ∘ η` transfers to `R ∘ η` through `F̄_s`;
* `not_hitsEast_finite_of_le_junR`, `not_hitsEast_atTop_of_ne_junR` (deterministic exclusions);
* `HitsEastSideAlong`, `HitsEastEndAlong`, **`PostContactEastResidual`**, **`FwdPostContactEastQOn`** (the residual);
* **`postContactNotEast_of_residual`**, **`fwdPostContactQOn_of_residual`**: `Prop51G.FwdPostContactQOn` from the
  residual and the counterflow's regularity;
* `prop51QStatement_of_partA_of_east`, `cfFirstContactQStatement_of_partA_of_east`: the wiring.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop51H

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond CrossCond.Word49 MartChar.RealFlow LawUnique Cond44Ref Prop411Q Prop49Exit Prop51G

/-! ### Boundary values of the counterflow chart -/

section Bdry

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ}

/-- **No return, left side** (the reflection of `Prop49Exit.extendFrom_ne_zero_of_noReturn`): if the counterflow
never returns to `0`, then `F̄_s` does not send a real point strictly between the image of `0⁻` and `0` to `0`. -/
theorem extendFrom_ne_zero_of_noReturn_left (hβ : IsLoewnerTrace w β) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 < s) (hNR : ∀ v ∈ Ioc 0 s, β v ≠ 0) {y : ℝ} (hy0 : y < 0)
    (hyL : -rightImg (fun r => -w r) 0 s - w s < y) : extendFrom H (fwdMapInv w s) (y : ℂ) ≠ 0 := by
  have hβ' := CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hβ
  have hNR' : ∀ v ∈ Ioc 0 s, LP.reflectC (β v) ≠ 0 := fun v hv h => hNR v hv (by
    have := congrArg LP.reflectC h
    rwa [LP.reflectC_reflectC, LP.reflectC_zero] at this)
  have hne := extendFrom_ne_zero_of_noReturn hβ' hw.neg (by simp [hw0]) hs hNR' (x := -y) (by linarith)
    (by
      have e : rightImg (-w) 0 s = rightImg (fun r => -w r) 0 s := rfl
      rw [e]; simp only [Pi.neg_apply]; linarith)
  have e := CfNoReturn.extendFrom_fwdMapInv_neg hβ hw hw0 hs.le (x := (y : ℂ)) (ofReal_mem_Hbar y)
  have hr : LP.reflectC ((y : ℝ) : ℂ) = ((-y : ℝ) : ℂ) := by simp [LP.reflectC]
  intro h0
  apply hne
  rw [← hr, e, h0, LP.reflectC_zero]

/-- **A cluster point of `Ψ ∘ η` at a positive real point transfers to `R ∘ η` through `F̄_s`**: if, along a filter
on the times when `η` is in `ℍ ∖ R(K_s)`, `Ψ ∘ η` clusters at `x > 0`, then `R ∘ η` clusters at `F̄_s(−1/x)`. -/
theorem mapClusterPt_negInv_of_revChart (hw : Continuous w) (hw0 : w 0 = 0) (hβ : IsLoewnerTrace w β)
    (hs : 0 ≤ s) {η : ℝ → ℂ} {F : Filter ℝ} {x : ℝ} (hx : 0 < x)
    (h : MapClusterPt (x : ℂ) (F ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s}) fun u => revChart w s (η u)) :
    MapClusterPt (extendFrom H (fwdMapInv w s) ((-x⁻¹ : ℝ) : ℂ)) (F ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s})
      fun u => negInv (η u) := by
  set F' := F ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s} with hF'
  have hD : ∀ᶠ u in F', η u ∈ H \ cfHullQ w s := mem_inf_of_right (mem_principal_self _)
  have hξ : ∀ᶠ u in F', negInv (η u) ∈ H \ fwdHull w s := hD.mono fun u hu => negInv_notMem_fwdHull hu
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- `R ∘ Ψ ∘ η = f_s ∘ R ∘ η` clusters at `−1/x`
  have h1 : MapClusterPt (negInv (x : ℂ)) F' (negInv ∘ fun u => revChart w s (η u)) :=
    MapClusterPt.continuousAt_comp (f := negInv) (continuousAt_negInv hx0) h
  have e1 : negInv (x : ℂ) = ((-x⁻¹ : ℝ) : ℂ) := by simp [negInv]
  rw [e1] at h1
  have heq : (negInv ∘ fun u => revChart w s (η u)) =ᶠ[F'] fun u => fwdMap w s (negInv (η u)) :=
    Eventually.of_forall fun u => by simp only [Function.comp_apply, revChart, negInv_negInv]
  have h2 : MapClusterPt ((-x⁻¹ : ℝ) : ℂ) F' fun u => fwdMap w s (negInv (η u)) := by
    unfold MapClusterPt at h1 ⊢
    rwa [Filter.map_congr heq] at h1
  -- the values lie in `ℍ`, where `F̄_s` is continuous up to the boundary
  have hgH : ∀ᶠ u in F', fwdMap w s (negInv (η u)) ∈ H :=
    hξ.mono fun u hu => QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs hu
  have hle : map (fun u => fwdMap w s (negInv (η u))) F' ≤ 𝓟 H := by
    rw [le_principal_iff]; exact hgH
  have hB := (hβ.hasBdryLimits hw hw0 hs).tendsto (ofReal_mem_Hbar (-x⁻¹))
  have hNe : (𝓝[H] ((-x⁻¹ : ℝ) : ℂ) ⊓ map (fun u => fwdMap w s (negInv (η u))) F').NeBot := by
    have e : 𝓝[H] ((-x⁻¹ : ℝ) : ℂ) ⊓ map (fun u => fwdMap w s (negInv (η u))) F' =
        𝓝 ((-x⁻¹ : ℝ) : ℂ) ⊓ map (fun u => fwdMap w s (negInv (η u))) F' := by
      rw [nhdsWithin, inf_assoc, inf_eq_right.2 hle]
    rw [e]; exact h2
  have hNe' := hNe.map (fwdMapInv w s)
  have hcl : MapClusterPt (extendFrom H (fwdMapInv w s) ((-x⁻¹ : ℝ) : ℂ)) F'
      fun u => fwdMapInv w s (fwdMap w s (negInv (η u))) := by
    show (𝓝 _ ⊓ map _ F').NeBot
    refine hNe'.mono (le_inf ((map_mono inf_le_left).trans hB) ?_)
    exact (map_mono inf_le_right).trans_eq Filter.map_map
  have heq' : (fun u => fwdMapInv w s (fwdMap w s (negInv (η u)))) =ᶠ[F'] fun u => negInv (η u) :=
    hξ.mono fun u hu => QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hs hu
  unfold MapClusterPt at hcl ⊢
  rwa [Filter.map_congr heq'] at hcl

end Bdry

/-! ### The deterministic exclusions -/

section Excl

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {η : ℝ → ℂ}

theorem negInv_mem_H_of_mem {z : ℂ} (hz : z ∈ H) : negInv z ∈ H := by
  show 0 < (-z⁻¹).im
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  refine div_pos hz (Complex.normSq_pos.2 fun h => ?_)
  rw [h] at hz
  exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)

/-- **No end at a point of `ℝ₊` or at the eastern end of `∞` at a finite time** (deterministic). If an excursion of
the proper arc `η` in `ℍ ∖ R(K_s)` ends at a finite time `u₀`, its chart image `Ψ ∘ η` does not cluster at a point
of `(0, junR]`: otherwise `R(η(u₀)) ∈ ℍ` would be the boundary value of `F̄_s` at a real point at or left of the image
of `0⁻`. -/
theorem not_hitsEast_finite_of_le_junR (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s) {t u₀ : ℝ} (ht : 0 ≤ t) (htu : t < u₀) {x : ℝ} (hx : 0 < x)
    (hxj : x ≤ junR w s)
    (h : MapClusterPt (x : ℂ) (𝓝[Ioo t u₀] u₀ ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s}) fun u => revChart w s (η u)) :
    False := by
  have hu₀ : 0 < u₀ := ht.trans_lt htu
  set L := -rightImg (fun r => -w r) 0 s - w s with hL
  have hjunR : junR w s = -1 / L := rfl
  rw [hjunR] at hxj
  have hL0 : L < 0 := by
    by_contra hc
    push Not at hc
    have : -1 / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hc
    linarith
  rw [le_div_iff_of_neg hL0] at hxj
  have hxinv : x⁻¹ * x = 1 := inv_mul_cancel₀ hx.ne'
  have hy : -x⁻¹ ≤ L := by nlinarith [mul_nonneg (inv_pos.2 hx).le (show 0 ≤ x * L + 1 by linarith)]
  have hk := mapClusterPt_negInv_of_revChart hw hw0 hβ hs hx h
  have hne : η u₀ ≠ 0 := fun h0 => by
    have := hη.mem_H u₀ hu₀
    rw [h0] at this
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
  have hηc : Tendsto η (𝓝 u₀) (𝓝 (η u₀)) := (hη.cont.continuousAt (Ici_mem_nhds hu₀)).tendsto
  have hξ : Tendsto (fun u => negInv (η u)) (𝓝[Ioo t u₀] u₀ ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s})
      (𝓝 (negInv (η u₀))) :=
    ((continuousAt_negInv hne).tendsto.comp hηc).mono_left (inf_le_left.trans nhdsWithin_le_nhds)
  have heq := eq_of_mapClusterPt_of_tendsto hk hξ
  have hmem : extendFrom H (fwdMapInv w s) ((-x⁻¹ : ℝ) : ℂ) ∈ H := by
    rw [heq]; exact negInv_mem_H_of_mem (hη.mem_H u₀ hu₀)
  have := neg_rightImg_sub_lt_of_extendFrom_mem_H hβ hw hw0 hs hmem
  linarith

/-- **No end at `∞` at a point of `ℝ₊` or of the eastern side** (deterministic). If an excursion of the proper arc
`η` in `ℍ ∖ R(K_s)` never ends, `Ψ ∘ η` does not cluster at `x > 0`, `x ≠ junR` as `t → ∞`: otherwise `F̄_s(−1/x) = 0`,
while `F̄_s` sends a real point left of the image of `0⁻` to a negative real point and (no return) a point between that
image and `0` off `0`. -/
theorem not_hitsEast_atTop_of_ne_junR (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 < s) (hNR : ∀ v ∈ Ioc 0 s, β v ≠ 0) {x : ℝ} (hx : 0 < x)
    (hxj : x ≠ junR w s)
    (h : MapClusterPt (x : ℂ) (atTop ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s}) fun u => revChart w s (η u)) : False := by
  have hk := mapClusterPt_negInv_of_revChart hw hw0 hβ hs.le hx h
  have hηinf : Tendsto η atTop (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]; exact hη.tendsto
  have hξ : Tendsto (fun u => negInv (η u)) atTop (𝓝 0) := by
    have := (tendsto_inv₀_cobounded.comp hηinf).neg
    simpa [negInv, Function.comp_def] using this
  have h0 := eq_of_mapClusterPt_of_tendsto hk (hξ.mono_left inf_le_left)
  set L := -rightImg (fun r => -w r) 0 s - w s with hL
  have hxinv : x⁻¹ * x = 1 := inv_mul_cancel₀ hx.ne'
  rcases lt_trichotomy (-x⁻¹) L with hlt | heq | hgt
  · obtain ⟨x₀, hx₀, he⟩ := exists_extendFrom_eq_lt hw hw0 hs.le (hβ.hasBdryLimits hw hw0 hs.le) (a := 0) le_rfl
      (by simpa only [neg_zero] using hlt)
    rw [he] at h0
    exact hx₀.ne (by exact_mod_cast h0)
  · apply hxj
    have hjunR : junR w s = -1 / L := rfl
    rw [hjunR, ← heq]
    field_simp
  · exact extendFrom_ne_zero_of_noReturn_left hβ hw hw0 hs hNR (by simpa using inv_pos.2 hx) hgt h0

end Excl

/-! ### The residual and the reduction -/

section Residual

/-- Along `F`, while in `ℍ ∖ R(K_s)`, `Ψ ∘ η` clusters at a point of the **eastern side proper** `(junR, ∞)`. -/
def HitsEastSideAlong (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (F : Filter ℝ) : Prop :=
  ∃ x : ℝ, junR w s < x ∧ MapClusterPt (x : ℂ) (F ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s}) fun u => revChart w s (η u)

/-- Along `F`, while in `ℍ ∖ R(K_s)`, `Ψ ∘ η` clusters at the **eastern end** `junR = Ψ(∞⁺)`. -/
def HitsEastEndAlong (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (F : Filter ℝ) : Prop :=
  MapClusterPt (junR w s : ℂ) (F ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s}) fun u => revChart w s (η u)

/-- **The post-contact residual** (the probabilistic content of Lemma 5.4 after a contact, with R50 / Astra C): if
`η` has met `R(K_s)` in `(0, t]` and is in `ℍ ∖ R(K_s)` at `t`, its excursion running at `t` (E1) does not end at a
finite time on the eastern side proper, and (E2) if it never ends, it does not end at the eastern end of `∞`. -/
def PostContactEastResidual (w : ℝ → ℝ) (s t : ℝ) (η : ℝ → ℂ) : Prop :=
  (∃ v ∈ Ioc 0 t, η v ∉ H \ cfHullQ w s) → (0 < t → η t ∈ H \ cfHullQ w s) →
    (∀ u₀, t < u₀ → (∀ v ∈ Ioo t u₀, η v ∈ H \ cfHullQ w s) → ¬ HitsEastSideAlong w s η (𝓝[Ioo t u₀] u₀)) ∧
      ((∀ v ∈ Ioi t, η v ∈ H \ cfHullQ w s) → ¬ HitsEastEndAlong w s η atTop)

/-- **The post-contact residual on a regime of angles**, almost surely on the glued space at every positive rational
counterflow time `s` and restart time `t` (the named input that replaces `Prop51G.FwdPostContactQOn`). -/
def FwdPostContactEastQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∀ t : ℚ, 0 < t → PostContactEastResidual w s t η

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {η : ℝ → ℂ}

/-- **`PostContactNotEast` from the residual** (deterministic): the remaining eastern ends are excluded by
`not_hitsEast_finite_of_le_junR` and `not_hitsEast_atTop_of_ne_junR`. -/
theorem postContactNotEast_of_residual (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 < s) (hNR : ∀ v ∈ Ioc 0 s, β v ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (hres : PostContactEastResidual w s t η) : PostContactNotEast w s t η := by
  intro hc hD
  obtain ⟨h1, h2⟩ := hres hc hD
  refine ⟨fun u₀ htu hDu ⟨x, hx0, hx⟩ => ?_, fun hDi ⟨x, hx0, hx⟩ => ?_⟩
  · rcases le_or_gt x (junR w s) with hle | hgt
    · exact not_hitsEast_finite_of_le_junR hη hw hw0 hβ hs.le ht htu hx0 hle hx
    · exact h1 u₀ htu hDu ⟨x, hgt, hx⟩
  · by_cases hxj : x = junR w s
    · subst hxj
      exact h2 hDi hx
    · exact not_hitsEast_atTop_of_ne_junR hη hw hw0 hβ hs hNR hx0 hxj hx

/-- **`Prop51G.FwdPostContactQOn` from the residual and the counterflow's regularity.** -/
theorem fwdPostContactQOn_of_residual {G : ℝ → ℝ → ℝ → Prop} (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hres : FwdPostContactEastQOn.{u} G) : FwdPostContactQOn.{u} G := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have harc := ae_glue_fst (μ := P) k hXm (ae_isProperArc_of_isFlowLine hκ hκ4.le hadm hfl)
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [hres κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs, harc, hregG]
    with p hp hpa hpr t ht
  obtain ⟨-, hwc, hw0, hβ, hne, -⟩ := hpr
  exact postContactNotEast_of_residual hpa hwc hw0 hβ (by exact_mod_cast hs) (fun v hv => hne v hv.1)
    (by exact_mod_cast ht.le) (hp t ht)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs at `16/κ`, the no-wrap topology and the post-contact
residual** (below the critical gap; at and above it, `fwdNoContactQStatement`). -/
theorem prop51QStatement_of_partA_of_east (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hres : FwdPostContactEastQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_post hA htopo
    (fwdPostContactQOn_of_residual (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hres)

/-- **Theorem 1.2's input `CfAvoidLeftQ.CfFirstContactQStatement` from Zhan's Part A inputs, the no-wrap topology and
the post-contact residual.** -/
theorem cfFirstContactQStatement_of_partA_of_east (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hres : FwdPostContactEastQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    CfAvoidLeftQ.CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_partA_of_post hA htopo
    (fwdPostContactQOn_of_residual (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hres)

end Residual

end InteractingSLE.Sec5.Prop51H
