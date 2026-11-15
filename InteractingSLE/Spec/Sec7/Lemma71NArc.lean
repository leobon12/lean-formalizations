/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71MBdry
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Sec6.DrivingArgLift
import InteractingSLE.WangWu.SideValues
import InteractingSLE.Spec.Sec7.Lemma71LComp
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# Lemma 7.1's side limits: the outer arcs of the active component at a fixed capacity time

Packet PROVE-LEMMA71N (specification Remark 6.7, `source/spec/p145-192.md` L566–L590: "Along the exposed outer-curve
suffixes, away from their attachment points, the stopped middle prefix has positive distance, so comparison with the
two outer curves gives the prescribed boundary values"; Lemma 7.1, `source/spec/p193-240.md` L576–L606).

In the pocket chart the active component at capacity time `t` is `D = ψ⁻¹(ℍ ∖ K_t)` and its chart is `f_t ∘ ψ`
(`Lemma71M.pocketFwd`). A real point `x` left of the image `L_t − W_t` of `0⁻` or right of the image `R_t − W_t` of
`0⁺` is the image under the centred flow of an **alive** real point `ξ ≠ 0` (`exists_alive_cflow_eq`,
`exists_alive_neg_cflow_eq`), so `f_t⁻¹ → ξ` at `x`, `Im log f_t′ → 0` there (Aux. lemma 45, (CA2)), `ξ` is off the
mapped prefix (`ofReal_notMem_image_of_isForwardSol`: a real alive point is not on the trace), and the inverse chart
`ψ⁻¹` lands at a point `p` of the pocket frontier away from the stopped middle prefix. The side limit of the active
component at `x` is therefore the side limit of the **pocket chart itself** at `ξ` (`OuterSideLimit`: Proposition 6.1
for the two outer curves, in the chart), plus the explicit boundary value of the seed function
(`tendsto_meanHarmonic`).

## Main results

* `exists_alive_cflow_eq`, `exists_alive_neg_cflow_eq`: real points outside `[L_t − W_t, R_t − W_t]` are images of
  alive points;
* `ofReal_notMem_image_of_isForwardSol`: an alive real point `ξ ≠ 0` is not on the trace prefix;
* `tendsto_arg_sub`, `tendsto_meanHarmonic`: boundary values of the explicit seed function;
* `hasBdryLimits_fwdMapInv_clamp`: boundary limits of `f_t⁻¹` for the mapped segment;
* `OuterSideLimit`: the outer side limits of a pocket chart;
* **`arc_sideLimit`**: the second alternative of `Lemma71M.PocketSideLimit` at every `x` outside
  `[L_t − W_t, R_t − W_t]`, from `OuterSideLimit` (pathwise).

Conditional helper (on `OuterSideLimit`); it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71N

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open MartChar.RealFlow

section Flow

variable {W : ℝ → ℝ} {t : ℝ}

/-- **Every point right of the image of `0⁺` is the image of an alive point** (intermediate values of the
`1`-Lipschitz map `y ↦ g_t(y)`). -/
theorem exists_alive_cflow_eq (hW : Continuous W) (ht : 0 ≤ t) {x : ℝ} (hx : rightImg W 0 t - W t < x) :
    ∃ y, 0 < y ∧ Alive W y t ∧ cflow W y t = x := by
  obtain ⟨y₀, hy₀0, hy₀, hg₀⟩ := exists_lt_of_rightImg_lt hW ht (show rightImg W 0 t < x + W t by linarith)
  set Y := max y₀ (x + W t) with hY
  have hy₀Y : y₀ ≤ Y := le_max_left _ _
  have hcont : ContinuousOn (fun y => gImg W y t) (Icc y₀ Y) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun a ha b hb => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_gImg_sub_le hW ht (hy₀.of_le hW hb.1 ht) (hy₀.of_le hW ha.1 ht)
  have hYg : x + W t ≤ gImg W Y t := (le_max_right _ _).trans ((hy₀.of_le hW hy₀Y ht).le_gImg hW ht)
  obtain ⟨y, hy, hyg⟩ := intermediate_value_Icc hy₀Y hcont ⟨hg₀.le, hYg⟩
  refine ⟨y, hy₀0.trans_le hy.1, hy₀.of_le hW hy.1 ht, ?_⟩
  simp only [gImg] at hyg
  linarith

/-- **Every point left of the image of `0⁻` is the image of an alive left point** (the reflected statement). -/
theorem exists_alive_neg_cflow_eq (hW : Continuous W) (ht : 0 ≤ t) {x : ℝ}
    (hx : x < -rightImg (fun s => -W s) 0 t - W t) :
    ∃ y, 0 < y ∧ Alive (fun s => -W s) y t ∧ -cflow (fun s => -W s) y t = x := by
  obtain ⟨y, hy0, hya, hy⟩ := exists_alive_cflow_eq (W := fun s => -W s) hW.neg ht (x := -x) (by linarith)
  exact ⟨y, hy0, hya, by linarith⟩

end Flow

section Arc

variable {W : ℝ → ℝ} {t : ℝ}

/-- **A real point of a hull's boundary flow is off the trace prefix**: if the hull at time `t` is the filling of
`Γ([0, U])` for a curve `Γ` in `ℍ̄` from `0` whose real times have empty interior, a real point `y ≠ 0` with a solution
of the centred flow on `[0, t]` is not on `Γ([0, U])`. -/
theorem ofReal_notMem_image_of_isForwardSol (hW : Continuous W) (ht : 0 ≤ t) {Γ : ℝ → ℂ}
    (hΓc : ContinuousOn Γ (Ici 0)) (hΓH : MapsTo Γ (Ici 0) Hbar) (hΓ0 : Γ 0 = 0)
    (hint : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (Γ u).im = 0} = ∅)
    {U : ℝ} (hK : fwdHull W t = fillH (Γ '' Icc 0 U)) {y : ℝ} (hy0 : y ≠ 0) {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W (y : ℂ) t u) : (y : ℂ) ∉ Γ '' Icc 0 U := by
  rintro ⟨v, hv, hvy⟩
  have hv0 : 0 < v := by
    rcases hv.1.eq_or_lt with h | h
    · rw [← h, hΓ0] at hvy
      exact absurd (by exact_mod_cast hvy.symm) hy0
    · exact h
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ht hu
  set E := Real.exp (2 / δ ^ 2 * t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  obtain ⟨ε, hε, hball⟩ := Metric.continuousWithinAt_iff.1 (hΓc v hv.1) (δ / E) (by positivity)
  set a := max 0 (v - ε) with ha
  have hav : a < v := max_lt hv0 (by linarith)
  have hsub : ¬ Ioo a v ⊆ {u ∈ Ici (0 : ℝ) | 0 < u ∧ (Γ u).im = 0} := by
    intro h
    have h' := interior_mono h
    rw [interior_Ioo, hint] at h'
    exact (nonempty_Ioo.2 hav).ne_empty (subset_empty_iff.1 h')
  obtain ⟨v', hv', hv'S⟩ := not_subset.1 hsub
  have hv'0 : 0 < v' := lt_of_le_of_lt (le_max_left _ _) hv'.1
  have hv'H : Γ v' ∈ H := by
    have h1 : 0 ≤ (Γ v').im := hΓH (mem_Ici.2 hv'0.le)
    rcases h1.eq_or_lt with h | h
    · exact absurd ⟨mem_Ici.2 hv'0.le, hv'0, h.symm⟩ hv'S
    · exact h
  have hv'K : Γ v' ∈ fwdHull W t := by
    rw [hK]
    exact ⟨hv'H, Or.inl (subset_closure ⟨v', ⟨hv'0.le, hv'.2.le.trans hv.2⟩, rfl⟩)⟩
  have hdist : dist (Γ v') (Γ v) < δ / E := by
    refine hball (mem_Ici.2 hv'0.le) ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right 0 (v - ε), hv'.1, hv'.2]
  refine not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hv'H ?_ hv'K
  rw [← hvy, ← dist_eq_norm]
  calc dist (Γ v') (Γ v) * E < δ / E * E := mul_lt_mul_of_pos_right hdist hE0
    _ = δ := div_mul_cancel₀ δ hE0.ne'

end Arc

section Mean

variable {nL nR : ℕ}

/-- `arg (w − v)` is continuous from `ℍ` at every real point `x ≠ v`. -/
theorem tendsto_arg_sub (v x : ℝ) (hxv : x ≠ v) :
    Tendsto (fun w : ℂ => Complex.arg (w - v)) (𝓝[H] (x : ℂ)) (𝓝 (Complex.arg ((x : ℂ) - v))) := by
  have hsub : Tendsto (fun w : ℂ => w - v) (𝓝[H] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im}] ((x : ℂ) - v)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right (v : ℂ)).tendsto _).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun w hw => ?_⟩
    show 0 ≤ (w - v).im
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact le_of_lt hw
  rcases lt_or_gt_of_ne hxv with h | h
  · have hre : ((x : ℂ) - v).re < 0 := by simp [h]
    have him : ((x : ℂ) - v).im = 0 := by simp
    have harg : Complex.arg ((x : ℂ) - v) = Real.pi := by
      rw [← Complex.ofReal_sub]; exact Complex.arg_ofReal_of_neg (by linarith)
    rw [harg]
    exact (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp hsub
  · have hsl : ((x : ℂ) - v) ∈ Complex.slitPlane := by
      rw [← Complex.ofReal_sub]
      exact Complex.ofReal_mem_slitPlane.2 (by linarith)
    exact (Complex.continuousAt_arg hsl).tendsto.comp (hsub.mono_right nhdsWithin_le_nhds)

/-- **The explicit harmonic function is continuous from `ℍ` at real points off its jump set**, with value the
formula at the real point. -/
theorem tendsto_meanHarmonic (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)
    {x : ℝ} (hx0 : x ≠ 0) (hxL : ∀ i, x ≠ vL i) (hxR : ∀ i, x ≠ vR i) :
    Tendsto (Ito.meanHarmonic κ ρL ρR vL vR) (𝓝[H] (x : ℂ)) (𝓝 (Ito.meanHarmonic κ ρL ρR vL vR x)) := by
  have h0 : Tendsto (fun w : ℂ => Complex.arg w) (𝓝[H] (x : ℂ)) (𝓝 (Complex.arg (x : ℂ))) := by
    have := tendsto_arg_sub 0 x hx0
    simpa using this
  have hL : ∀ i, Tendsto (fun w : ℂ => Complex.arg (w - vL i)) (𝓝[H] (x : ℂ)) (𝓝 (Complex.arg ((x : ℂ) - vL i))) :=
    fun i => tendsto_arg_sub (vL i) x (hxL i)
  have hR : ∀ i, Tendsto (fun w : ℂ => Complex.arg (w - vR i)) (𝓝[H] (x : ℂ)) (𝓝 (Complex.arg ((x : ℂ) - vR i))) :=
    fun i => tendsto_arg_sub (vR i) x (hxR i)
  unfold Ito.meanHarmonic
  refine Tendsto.const_mul _ (((tendsto_const_nhds.sub (h0.const_mul 2)).sub ?_).sub ?_)
  · exact tendsto_finsetSum _ fun i _ => (hL i).const_mul (ρL i)
  · exact tendsto_finsetSum _ fun i _ => (hR i).const_mul (ρR i)

end Mean

section Active

open QuantumZipper.CA (cayley cayleyInv)
open Lemma71M

/-- **The inverse Loewner map of the mapped segment has boundary limits** (for the clamped continuous driver; the
argument of `Lemma71M.exists_tendsto_pocketInv`). -/
theorem hasBdryLimits_fwdMapInv_clamp {γ' : ℝ → ℂ} (hΓ : Lemma71C.IsSegCurve γ') {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < Lemma71C.capLife γ') {W : ℝ → ℝ} {t₂ : ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (htt₂ : (t : ℝ) < t₂) (hEq : EqOn W (Ito.rpath fun s => Lemma71C.segDriver γ' s) (Icc 0 t₂)) :
    HasBdryLimits (fwdMapInv W t) := by
  intro x hx
  rcases (zero_le (a := t)).eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨x, ?_⟩
    have heq : ∀ y ∈ H, fwdMapInv W ((0 : ℝ≥0) : ℝ) y = y := fun y hy => by
      rw [NNReal.coe_zero]; exact fwdMapInv_zero_time hW hW0 hy
    exact (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
      (eventually_nhdsWithin_of_forall fun y hy => (heq y hy).symm)
  · have hgen := (PocketTraversal.isDrivenCurve_of_isSegCurve hΓ).isGeneratingTrace (T := (t : ℝ≥0∞)) ht
    have hη := Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hgen
    have hη' : IsLoewnerTraceLT W t (fun s : ℝ => PocketTraversal.capTrace γ' s.toNNReal) := by
      refine ⟨hη.1, hη.2.1, fun s hs0 hst => ?_⟩
      rw [← hη.2.2 s hs0 hst]
      exact InteractingSLE.fwdHull_eq_of_eqOn hs0 (hst.trans htt₂) fun r hr => hEq hr
    have hησ : ContinuousOn (fun s : ℝ => PocketTraversal.capTrace γ' s.toNNReal) (Icc 0 (t : ℝ)) :=
      hgen.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
        ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    exact TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη' hW hW0 (NNReal.coe_pos.2 hpos) hησ x hx

/-- **The outer side limits of a pocket chart** (Proposition 6.1 for the two outer curves, in the chart): at every
real point `ξ ≠ 0`, `vT ∘ ψ⁻¹ + u₀ ∘ ψ⁻¹ + k · ℓ ∘ ψ⁻¹` tends to the left height `hL` (`ξ < 0`) or the right height
`hR` (`ξ > 0`), `ℓ` the lift of the chart. -/
def OuterSideLimit (c : Chart) (vT u₀ : ℂ → ℝ) (k hL hR : ℝ) : Prop :=
  ∀ ξ : ℝ, ξ ≠ 0 → Tendsto (fun y => vT (c.2.1 y) + u₀ (c.2.1 y) + k * c.2.2 (c.2.1 y)) (𝓝[H] (ξ : ℂ))
    (𝓝 (if ξ < 0 then hL else hR))

/-- **The side limits of the active component along the outer arcs, at a fixed capacity time** (Remark 6.7: "along
the exposed outer-curve suffixes … the stopped middle prefix has positive distance, so comparison with the two outer
curves gives the prescribed boundary values"). Pathwise. Let `c` be a conformal pocket chart with boundary map `Ψ`,
`γ'` the mapped segment, `t` below its terminal capacity time, `A ⊆ AT ∪ Γ` with `Γ` compact (the stopped middle
prefix) whose points in the closed pocket are mapped by `Ψ` into the mapped prefix, and `∂C ∩ ℍ ⊆ AT`. If the pocket
chart has the outer side limits (`OuterSideLimit`, heights `λ(−1 − ρ^L) − a'` and `λ(1 + ρ^R) − a'`), then at every
real `x` left of the image of `0⁻` or right of the image of `0⁺` the inverse chart of the active component lands at a
point `p` of `AT ∪ ℝ` near which `A ⊆ AT`, and `vT + u₀ − Gl → 0` at `x` (the second alternative of
`Lemma71M.PocketSideLimit`). -/
theorem arc_sideLimit {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {b : ℂ} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = C) (hCH : C ⊆ H) (hbC : b ∉ cayley '' C)
    (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {b})) (hΨi : InjOn Ψ (closure (cayley '' C) \ {b}))
    (hΨtop : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {b}] b) atTop)
    (hΨe : ∀ x ∈ C, c.1 x = Ψ (cayley x)) (h1 : (1 : ℂ) ∉ closure (cayley '' C) \ {b})
    {γ' : ℝ → ℂ} (hΓ : Lemma71C.IsSegCurve γ') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Lemma71C.capLife γ')
    {A AT Γ : Set ℂ} (hΓc : IsCompact Γ) (hA : A ⊆ AT ∪ Γ) (hfr : frontier C ∩ H ⊆ AT)
    (hΓK : ∀ z ∈ closure (cayley '' C) \ {b}, cayleyInv z ∈ Γ → Ψ z ∈ γ' '' Icc 0 (Lemma71C.capInv γ' t))
    (κ : ℝ) (ρL ρR : Fin 1 → ℝ) {vL vR : Fin 1 → ℝ≥0 → ℝ}
    (hvL : vL 0 t = -rightImg (fun s => -Ito.rpath (fun s => Lemma71C.segDriver γ' s) s) 0 t)
    (hvR : vR 0 t = rightImg (Ito.rpath fun s => Lemma71C.segDriver γ' s) 0 t) (a' : ℝ) {vT u₀ : ℂ → ℝ}
    (hOS : OuterSideLimit c vT u₀ (QuantumZipper.chiC κ) (sleLambda κ * (-1 - ρL 0) - a')
      (sleLambda κ * (1 + ρR 0) - a'))
    {x : ℝ} (hx : x < vL 0 t - Lemma71C.segDriver γ' t ∨ vR 0 t - Lemma71C.segDriver γ' t < x) :
    ∃ p : ℂ, Tendsto (pocketInv c (fun s => Lemma71C.segDriver γ' s) t) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      p ∈ AT ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A ∩ ball p r ⊆ AT) ∧
      Tendsto (fun y => vT (pocketInv c (fun s => Lemma71C.segDriver γ' s) t y) +
          u₀ (pocketInv c (fun s => Lemma71C.segDriver γ' s) t y) -
          pocketGl κ ρL ρR c (fun s => Lemma71C.segDriver γ' s) vL vR t a' y) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set w : ℝ≥0 → ℝ := fun s => Lemma71C.segDriver γ' s with hwdef
  set χ := QuantumZipper.chiC κ with hχ
  have hw : ContinuousOn w {s | (s : ℝ≥0∞) < Lemma71C.capLife γ'} := hΓ.segDriver_spec.2.1
  have hw0 : w 0 = 0 := hΓ.segDriver_spec.1
  obtain ⟨W, t₂, hW, hW0, htt₂, hEq⟩ := exists_clamp_eqOn hw hw0 ht
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hEqt : EqOn W (Ito.rpath w) (Icc 0 (t : ℝ)) := fun r hr => hEq ⟨hr.1, hr.2.trans htt₂.le⟩
  have hc' := hc.loewner hW hW0 ht0
  have hf : ∀ z, fwdMap W t z = fwdMap (Ito.rpath w) t z := fun z => Ito.fwdMap_congr_of_eqOn_of_le hEq htt₂.le
  have hLd : ∀ z, logDerivFwd W t z = logDerivFwd (Ito.rpath w) t z := fun z =>
    Ito.logDerivFwd_congr_of_eqOn hEq ht0 htt₂.le
  have hK : fwdHull W t = fwdHull (Ito.rpath w) t :=
    InteractingSLE.fwdHull_eq_of_eqOn ht0 htt₂ fun r hr => hEq hr
  have h1c : (c.loewner W t).1 = pocketFwd c w t := funext fun z => hf (c.1 z)
  have hdomc : ((c.loewner W t).dom : Set ℂ) = pocketDom c w t := by
    rw [hc'.coe_dom]
    show (fun z => c.2.1 (fwdMapInv W t z)) '' H = c.2.1 '' (H \ fwdHull (Ito.rpath w) t)
    rw [← image_image c.2.1 (fwdMapInv W t), QuantumZipper.RS.image_fwdMapInv_H hW hW0 ht0, hK]
  have hinv : ∀ y ∈ H, pocketInv c w t y = c.2.1 (fwdMapInv W t y) := fun y hy =>
    pocketInv_eq hc hw hw0 ht hc' h1c hdomc hy
  have hB := hasBdryLimits_fwdMapInv_clamp hΓ ht hW hW0 htt₂ hEq
  -- the seeds
  have hWt : w t = W t := by
    have := hEqt ⟨ht0, le_rfl⟩
    simp only [Ito.rpath, Real.toNNReal_coe] at this
    exact this.symm
  have hR' : rightImg (Ito.rpath w) 0 t = rightImg W 0 t :=
    Lemma71B.rightImg_congr hW ht0 (fun r hr => (hEqt hr).symm) 0
  have hL' : rightImg (fun s => -Ito.rpath w s) 0 t = rightImg (fun s => -W s) 0 t :=
    Lemma71B.rightImg_congr hW.neg ht0 (fun r hr => by show -Ito.rpath w r = -W r; rw [hEqt hr]) 0
  have hsL : vL 0 t - w t ≤ 0 := by
    rw [hvL, hL', hWt]
    have := le_rightImg (w := fun s => -W s) hW.neg 0 ht0
    linarith
  have hsR : 0 ≤ vR 0 t - w t := by
    rw [hvR, hR', hWt]
    linarith [le_rightImg (w := W) hW 0 ht0]
  -- the real point `ξ` whose flow ends at `x`
  obtain ⟨ξ, u, hξ0, hu, hut, hsign⟩ : ∃ (ξ : ℝ) (u : ℝ → ℂ), ξ ≠ 0 ∧
      QuantumZipper.IsForwardSol W (ξ : ℂ) t u ∧ u t = x ∧ (ξ < 0 ↔ x < vL 0 t - w t) := by
    rcases hx with hxL | hxR
    · have hxL : x < vL 0 t - w t := hxL
      have hx' : x < -rightImg (fun s => -W s) 0 t - W t := by
        rw [hvL, hL'] at hxL
        rw [← hWt]
        exact hxL
      obtain ⟨y, hy0, hya, hyx⟩ := exists_alive_neg_cflow_eq hW ht0 hx'
      refine ⟨-y, fun s => -(cflow (fun s => -W s) y s : ℂ), neg_ne_zero.2 hy0.ne', ?_, ?_,
        iff_of_true (by linarith) hxL⟩
      · have := WangWu.isForwardSol_neg_of_alive hW hya
        rwa [show ((-y : ℝ) : ℂ) = -(y : ℂ) by push_cast; ring]
      · show -(cflow (fun s => -W s) y t : ℂ) = (x : ℂ)
        rw [← hyx]
        push_cast
        ring
    · have hxR : vR 0 t - w t < x := hxR
      obtain ⟨y, hy0, hya, hyx⟩ := exists_alive_cflow_eq hW ht0 (x := x) (by rw [hvR, hR', hWt] at hxR; exact hxR)
      refine ⟨y, fun s => (cflow W y s : ℂ), hy0.ne', WangWu.isForwardSol_of_alive hW hya, ?_,
        iff_of_false (by linarith) (by linarith)⟩
      show (cflow W y t : ℂ) = (x : ℂ)
      rw [hyx]
  -- the boundary limit of `f_t⁻¹` at `x`
  have hxH : ((x : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp
  have hξHb : ((ξ : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((ξ : ℝ) : ℂ).im by simp
  have hFx : extendFrom H (fwdMapInv W t) x = ξ := by
    have := SideHeight.extendFrom_eq_of_isForwardSol' hB hW hW0 ht0 hξHb hu
    rwa [hut] at this
  have hFt : Tendsto (fwdMapInv W t) (𝓝[H] (x : ℂ)) (𝓝[H] (ξ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht0 hy⟩
    have := hB.tendsto hxH
    rwa [hFx] at this
  -- the landing point
  have hξH : ((ξ : ℝ) : ℂ) ∈ closure H := by rw [closure_H]; exact hξHb
  obtain ⟨z, hzK, hΨz, hcz⟩ := tendsto_inv_of_ext hc hdom hCH hbC hΨc hΨi hΨtop hΨe h1 hξH
  have hz1 : z ≠ 1 := fun h => h1 (h ▸ hzK)
  have hpinv : Tendsto (pocketInv c w t) (𝓝[H] (x : ℂ)) (𝓝 (cayleyInv z)) :=
    (hcz.comp hFt).congr' (eventually_nhdsWithin_of_forall fun y hy => (hinv y hy).symm)
  refine ⟨cayleyInv z, hpinv, ?_, ?_, ?_⟩
  · have hCo : IsOpen C := hdom ▸ c.dom.isOpen
    have hNe : (𝓝[H] ((ξ : ℝ) : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hξH
    have hpcl : cayleyInv z ∈ closure C :=
      mem_closure_of_tendsto hcz (eventually_nhdsWithin_of_forall fun y hy => by
        rw [← hdom]; exact hc.inv_mem_dom hy)
    have hpC : cayleyInv z ∉ C := by
      intro hpC
      have h2 : c.1 (cayleyInv z) = ξ := by
        rw [hΨe _ hpC, QuantumZipper.CA.cayley_cayleyInv hz1, hΨz]
      have h3 : c.1 (cayleyInv z) ∈ H := hc.fwd_mem (by rw [← SetLike.mem_coe, hdom]; exact hpC)
      rw [h2] at h3
      have : (0 : ℝ) < ((ξ : ℝ) : ℂ).im := h3
      simp at this
    by_cases hpH : cayleyInv z ∈ H
    · refine Or.inl (hfr ⟨?_, hpH⟩)
      rw [hCo.frontier_eq]
      exact ⟨hpcl, hpC⟩
    · refine Or.inr (le_antisymm (not_lt.1 hpH) ?_)
      have : cayleyInv z ∈ closure H := closure_mono hCH hpcl
      rw [closure_H] at this
      exact this
  · have hpΓ : cayleyInv z ∉ Γ := by
      intro hpΓ
      have h2 := hΓK z hzK hpΓ
      rw [hΨz] at h2
      obtain ⟨hKeq, -⟩ := Lemma71L.IsSegCurve.fwdHull_segDriver_eq hΓ ht0 (by rwa [ENNReal.ofReal_coe_nnreal])
      have hKW : fwdHull W t = fillH (γ' '' Icc 0 (Lemma71C.capInv γ' t)) := by rw [hK]; exact hKeq
      exact ofReal_notMem_image_of_isForwardSol hW ht0 hΓ.1 hΓ.2.2.1 hΓ.2.2.2.1 hΓ.2.2.2.2.2 hKW hξ0 hu h2
    obtain ⟨d, hd, hdΓ⟩ := Lemma613.exists_ball_notMem hΓc hpΓ
    exact ⟨d, hd, fun z' hz' => (hA hz'.1).resolve_right fun h => hdΓ z' h hz'.2⟩
  · have heq : ∀ y ∈ H, vT (pocketInv c w t y) + u₀ (pocketInv c w t y) - pocketGl κ ρL ρR c w vL vR t a' y =
        (vT (c.2.1 (fwdMapInv W t y)) + u₀ (c.2.1 (fwdMapInv W t y)) + χ * c.2.2 (c.2.1 (fwdMapInv W t y))) -
          pocketG κ ρL ρR w vL vR t a' y + χ * (logDerivFwd W t (fwdMapInv W t y)).im := by
      intro y hy
      have hyt := QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht0 hy
      simp only [pocketGl, pocketLift, hinv y hy, hc.2.2 _ hyt, hLd]
      ring
    have hxL0 : x ≠ 0 := by
      intro h0
      have hx'' : x < vL 0 t - w t ∨ vR 0 t - w t < x := hx
      rw [h0] at hx''
      rcases hx'' with h | h <;> linarith
    have hx' : x < vL 0 t - w t ∨ vR 0 t - w t < x := hx
    have hxs1 : ∀ i, x ≠ (fun i => vL i t - w t) i := fun i => by
      rw [Subsingleton.elim i 0]; intro h; simp only at h; rcases hx' with h' | h' <;> linarith
    have hxs2 : ∀ i, x ≠ (fun i => vR i t - w t) i := fun i => by
      rw [Subsingleton.elim i 0]; intro h; simp only at h; rcases hx' with h' | h' <;> linarith
    have h1' := (hOS ξ hξ0).comp hFt
    have h2' : Tendsto (pocketG κ ρL ρR w vL vR t a') (𝓝[H] (x : ℂ))
        (𝓝 (Ito.meanHarmonic κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t) x - a')) :=
      (tendsto_meanHarmonic κ ρL ρR _ _ hxL0 hxs1 hxs2).sub_const a'
    have h3' := (Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real hW ht0 hu).comp hFt
    have hlim := (h1'.sub h2').add (h3'.const_mul χ)
    have hval : ((if ξ < 0 then sleLambda κ * (-1 - ρL 0) - a' else sleLambda κ * (1 + ρR 0) - a') -
        (Ito.meanHarmonic κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t) x - a')) + χ * 0 = 0 := by
      by_cases hξn : ξ < 0
      · have hxL : x < vL 0 t - w t := hsign.1 hξn
        simp only [hξn, ↓reduceIte]
        have hmh : Ito.meanHarmonic κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t) x =
            sleLambda κ * (-1 - ρL 0) := by
          simp only [Ito.meanHarmonic, Fin.sum_univ_one, sleLambda, ← Complex.ofReal_sub]
          rw [Complex.arg_ofReal_of_neg (by linarith : x < 0), Complex.arg_ofReal_of_neg (by linarith),
            Complex.arg_ofReal_of_neg (by linarith)]
          rw [div_eq_mul_one_div Real.pi]
          ring
        rw [hmh]
        ring
      · have hxR : vR 0 t - w t < x := by
          have hx'' : x < vL 0 t - w t ∨ vR 0 t - w t < x := hx
          exact hx''.resolve_left fun h => hξn (hsign.2 h)
        simp only [hξn, ↓reduceIte]
        have hmh : Ito.meanHarmonic κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t) x =
            sleLambda κ * (1 + ρR 0) := by
          simp only [Ito.meanHarmonic, Fin.sum_univ_one, sleLambda, ← Complex.ofReal_sub]
          rw [Complex.arg_ofReal_of_nonneg (by linarith : (0 : ℝ) ≤ x), Complex.arg_ofReal_of_nonneg (by linarith),
            Complex.arg_ofReal_of_nonneg (by linarith)]
          rw [div_eq_mul_one_div Real.pi]
          ring
        rw [hmh]
        ring
    rw [hval] at hlim
    exact hlim.congr' (eventually_nhdsWithin_of_forall fun y hy => (heq y hy).symm)

end Active

end InteractingSLE.Sec7.Lemma71N
