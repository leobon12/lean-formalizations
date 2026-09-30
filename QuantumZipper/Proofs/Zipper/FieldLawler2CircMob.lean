import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Möbius map sending the circle `|z| = ε` to `ℝ`, and harmonic-measure transport
(task FL2-C42CIRC)

Source: L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
proof of Corollary 4.2, p. 11: "Consider a Möbius transformation of the Riemann sphere that
sends C to R. Since Brownian motion is conformally invariant, ...". We use
`m(z) = i (ε − z)/(ε + z)` (pole `−ε`, `m(ε e^{iθ}) = tan(θ/2)`), with inverse
`m⁻¹(w) = ε (i − w)/(i + w)` (pole `−i`), and transport `IsHarmMeas` along `m` for a bounded
open `U` not containing the pole `−ε` (conformal invariance, in its Dirichlet form). The point
`∞` of the image is handled by the `zero` clause at the pole `−ε` (the transported `infty`
clause). Own elementary proofs of these routine facts.
-/

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.Thm18Asm.LWFar

/-- FL's Möbius map (p. 11): `m(z) = i (ε − z)/(ε + z)`, sending `{|z| = ε} \ {−ε}` onto `ℝ`. -/
noncomputable def fl2Mob (ε : ℝ) (z : ℂ) : ℂ := I * ((ε : ℂ) - z) / ((ε : ℂ) + z)

/-- The inverse Möbius map `m⁻¹(w) = ε (i − w)/(i + w)`. -/
noncomputable def fl2MobInv (ε : ℝ) (w : ℂ) : ℂ := (ε : ℂ) * (I - w) / (I + w)

section Mob

variable {ε : ℝ} (hε : 0 < ε)

lemma fl2Mob_add_I {z : ℂ} (hz : z ≠ -(ε : ℂ)) :
    fl2Mob ε z + I = 2 * (ε : ℂ) * I / ((ε : ℂ) + z) := by
  have h : (ε : ℂ) + z ≠ 0 := fun h => hz (by linear_combination h)
  unfold fl2Mob; field_simp; ring

include hε in
lemma fl2Mob_ne {z : ℂ} (hz : z ≠ -(ε : ℂ)) : fl2Mob ε z ≠ -I := by
  intro h
  have h1 := fl2Mob_add_I hz
  rw [h, neg_add_cancel] at h1
  have h2 : (ε : ℂ) + z ≠ 0 := fun h => hz (by linear_combination h)
  have h3 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  exact (div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h3) I_ne_zero) h2) h1.symm

lemma fl2MobInv_add {w : ℂ} (hw : w ≠ -I) :
    (ε : ℂ) + fl2MobInv ε w = 2 * (ε : ℂ) * I / (I + w) := by
  have h : I + w ≠ 0 := fun h => hw (by linear_combination h)
  unfold fl2MobInv; field_simp; ring

include hε in
lemma fl2MobInv_ne {w : ℂ} (hw : w ≠ -I) : fl2MobInv ε w ≠ -(ε : ℂ) := by
  intro h
  have h1 := fl2MobInv_add (ε := ε) hw
  rw [h, add_neg_cancel] at h1
  have h2 : I + w ≠ 0 := fun h => hw (by linear_combination h)
  have h3 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  exact (div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h3) I_ne_zero) h2) h1.symm

include hε in
lemma fl2MobInv_flMob {z : ℂ} (hz : z ≠ -(ε : ℂ)) : fl2MobInv ε (fl2Mob ε z) = z := by
  have h : (ε : ℂ) + z ≠ 0 := fun h => hz (by linear_combination h)
  have h3 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h4 : I + fl2Mob ε z ≠ 0 := fun h' => fl2Mob_ne hε hz (by linear_combination h')
  unfold fl2MobInv
  rw [div_eq_iff h4]
  unfold fl2Mob
  field_simp
  ring_nf

include hε in
lemma fl2Mob_flMobInv {w : ℂ} (hw : w ≠ -I) : fl2Mob ε (fl2MobInv ε w) = w := by
  have h : I + w ≠ 0 := fun h => hw (by linear_combination h)
  have h3 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h4 : (ε : ℂ) + fl2MobInv ε w ≠ 0 := fun h' => fl2MobInv_ne hε hw (by linear_combination h')
  unfold fl2Mob
  rw [div_eq_iff h4]
  unfold fl2MobInv
  field_simp
  ring_nf

lemma fl2Mob_analyticAt {z : ℂ} (hz : z ≠ -(ε : ℂ)) : AnalyticAt ℂ (fl2Mob ε) z := by
  have h : (ε : ℂ) + z ≠ 0 := fun h => hz (by linear_combination h)
  exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).div
    (analyticAt_const.add analyticAt_id) h

lemma fl2MobInv_analyticAt {w : ℂ} (hw : w ≠ -I) : AnalyticAt ℂ (fl2MobInv ε) w := by
  have h : I + w ≠ 0 := fun h => hw (by linear_combination h)
  exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).div
    (analyticAt_const.add analyticAt_id) h

include hε in
/-- Image characterization: for `S` avoiding the pole, `w ∈ m '' S ↔ w ≠ −i ∧ m⁻¹ w ∈ S`. -/
lemma fl2Mob_mem_image {S : Set ℂ} (hS : -(ε : ℂ) ∉ S) {w : ℂ} :
    w ∈ fl2Mob ε '' S ↔ w ≠ -I ∧ fl2MobInv ε w ∈ S := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ≠ -(ε : ℂ) := fun h => hS (h ▸ hz)
    exact ⟨fl2Mob_ne hε hz', by rwa [fl2MobInv_flMob hε hz']⟩
  · rintro ⟨hw, hS'⟩
    exact ⟨_, hS', fl2Mob_flMobInv hε hw⟩

include hε in
/-- Closure characterization away from `−i`. -/
lemma fl2Mob_mem_closure_image {S : Set ℂ} (hS : -(ε : ℂ) ∉ S) {w : ℂ} (hw : w ≠ -I) :
    w ∈ closure (fl2Mob ε '' S) ↔ fl2MobInv ε w ∈ closure S := by
  constructor
  · intro h
    have h1 := mem_closure_image (fl2MobInv_analyticAt (ε := ε) hw).continuousAt h
    have e : fl2MobInv ε '' (fl2Mob ε '' S) = S := by
      ext z; constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        rwa [fl2MobInv_flMob hε (fun h => hS (h ▸ hy))]
      · intro hz
        exact ⟨fl2Mob ε z, mem_image_of_mem _ hz, fl2MobInv_flMob hε (fun h => hS (h ▸ hz))⟩
    rwa [e] at h1
  · intro h
    have h1 := mem_closure_image
      (fl2Mob_analyticAt (ε := ε) (fl2MobInv_ne hε hw)).continuousAt h
    rwa [fl2Mob_flMobInv hε hw] at h1

include hε in
lemma fl2Mob_isOpen_image {U : Set ℂ} (hU : IsOpen U) (hp : -(ε : ℂ) ∉ U) :
    IsOpen (fl2Mob ε '' U) := by
  have e : fl2Mob ε '' U = {-I}ᶜ ∩ fl2MobInv ε ⁻¹' U := by
    ext w; rw [fl2Mob_mem_image hε hp]; rfl
  rw [e]
  refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_compl_singleton hU
  intro w hw
  exact (fl2MobInv_analyticAt (ε := ε) hw).continuousAt.continuousWithinAt

include hε in
lemma fl2Mob_image_diff {S T : Set ℂ} (hS : -(ε : ℂ) ∉ S) (hT : -(ε : ℂ) ∉ T) :
    fl2Mob ε '' (S \ T) = fl2Mob ε '' S \ fl2Mob ε '' T := by
  ext w
  rw [Set.mem_sdiff, fl2Mob_mem_image hε (fun h => hS h.1), fl2Mob_mem_image hε hS,
    fl2Mob_mem_image hε hT, Set.mem_sdiff]
  tauto

include hε in
/-- The image of a bounded set stays away from `−i`. -/
lemma fl2Mob_negI_not_mem_closure {U : Set ℂ} (hU : Bornology.IsBounded U)
    (hp : -(ε : ℂ) ∉ U) : -I ∉ closure (fl2Mob ε '' U) := by
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  set δ : ℝ := 2 * ε / (ε + max R 0 + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hsub : fl2Mob ε '' U ⊆ {w | δ ≤ ‖w + I‖} := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ≠ -(ε : ℂ) := fun h => hp (h ▸ hz)
    have hzR : ‖z‖ ≤ R := by simpa using hR hz
    have hden : (ε : ℂ) + z ≠ 0 := fun h => hz' (by linear_combination h)
    have hn : ‖(ε : ℂ) + z‖ ≤ ε + max R 0 + 1 := by
      calc ‖(ε : ℂ) + z‖ ≤ ‖(ε : ℂ)‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ε + max R 0 + 1 := by
          rw [Complex.norm_real, Real.norm_of_nonneg hε.le]
          linarith [le_max_left R 0]
    show δ ≤ ‖fl2Mob ε z + I‖
    rw [fl2Mob_add_I hz', norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hε.le, Complex.norm_two, mul_one, hδ]
    exact div_le_div_of_nonneg_left (by positivity) (norm_pos_iff.2 hden) hn
  have hc : IsClosed {w : ℂ | δ ≤ ‖w + I‖} :=
    isClosed_le continuous_const (continuous_norm.comp (continuous_id.add continuous_const))
  intro h
  have := closure_minimal hsub hc h
  simp only [mem_ofPred_eq, neg_add_cancel, norm_zero] at this
  linarith

include hε in
lemma fl2Mob_tendsto_within {S : Set ℂ} (hS : -(ε : ℂ) ∉ S) {x : ℂ} (hx : x ≠ -I) :
    Tendsto (fl2MobInv ε) (𝓝[fl2Mob ε '' S] x) (𝓝[S] (fl2MobInv ε x)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (fl2MobInv_analyticAt (ε := ε) hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact ((fl2Mob_mem_image hε hS).1 hw).2

include hε in
/-- `m⁻¹ w → −ε` as `w → ∞` within `m '' S`. -/
lemma fl2Mob_tendsto_cobounded {S : Set ℂ} (hS : -(ε : ℂ) ∉ S) :
    Tendsto (fl2MobInv ε) (Bornology.cobounded ℂ ⊓ 𝓟 (fl2Mob ε '' S)) (𝓝[S] (-(ε : ℂ))) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h1 : Tendsto (fun w : ℂ => -(ε : ℂ) + 2 * (ε : ℂ) * I * (I + w)⁻¹)
        (Bornology.cobounded ℂ) (𝓝 (-(ε : ℂ) + 2 * (ε : ℂ) * I * 0)) :=
      tendsto_const_nhds.add
        ((tendsto_inv₀_cobounded.comp (tendsto_const_add_cobounded I)).const_mul _)
    rw [mul_zero, add_zero] at h1
    refine (h1.mono_left inf_le_left).congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
    have hw' : w ≠ -I := ((fl2Mob_mem_image hε hS).1 hw).1
    have h : I + w ≠ 0 := fun h => hw' (by linear_combination h)
    have := fl2MobInv_add (ε := ε) hw'
    rw [div_eq_mul_inv] at this
    linear_combination -this
  · filter_upwards [mem_inf_of_right (mem_principal_self _)] with w hw
    exact ((fl2Mob_mem_image hε hS).1 hw).2

include hε in
/-- **Conformal invariance of harmonic measure under `m`** (FL p. 11). For a bounded open `U`
not containing the pole `−ε`, and `A` whose closure avoids `−ε`, `h ∘ m⁻¹` is the harmonic
measure of `m '' A` in `m '' U`. -/
theorem fl2Mob_isHarmMeas {U A : Set ℂ} {h : ℂ → ℝ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hpU : -(ε : ℂ) ∉ U) (hpA : -(ε : ℂ) ∉ closure A)
    (hh : IsHarmMeas U A h) :
    IsHarmMeas (fl2Mob ε '' U) (fl2Mob ε '' A) (fun w => h (fl2MobInv ε w)) := by
  have hpA' : -(ε : ℂ) ∉ A := fun h => hpA (subset_closure h)
  have hU' : IsOpen (fl2Mob ε '' U) := fl2Mob_isOpen_image hε hU hpU
  have hnI : ∀ x ∈ closure (fl2Mob ε '' U), x ≠ -I := fun x hx h =>
    fl2Mob_negI_not_mem_closure hε hUb hpU (h ▸ hx)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hz' : z ≠ -(ε : ℂ) := fun h => hpU (h ▸ hz)
    have h1 : InnerProductSpace.HarmonicAt h (fl2MobInv ε (fl2Mob ε z)) := by
      rw [fl2MobInv_flMob hε hz']; exact hh.harm z hz
    exact fl_harmonicAt_comp (fl2MobInv_analyticAt (fl2Mob_ne hε hz')) h1
  · rintro _ ⟨z, hz, rfl⟩
    rw [fl2MobInv_flMob hε (fun h => hpU (h ▸ hz))]; exact hh.mem01 z hz
  · rintro _ ⟨x₀, hx₀, rfl⟩ hcl
    have hx₀' : x₀ ≠ -(ε : ℂ) := fun h => hpA' (h ▸ hx₀)
    have hlim := hh.one x₀ hx₀ fun hc => hcl ?_
    · have h2 := fl2Mob_tendsto_within hε hpU (fl2Mob_ne hε hx₀')
      rw [fl2MobInv_flMob hε hx₀'] at h2
      exact hlim.comp h2
    set T : Set ℂ := (frontier U \ A) \ ({-(ε : ℂ)} : Set ℂ) with hTdef
    have hT : -(ε : ℂ) ∉ T := fun h => h.2 rfl
    have hcT : x₀ ∈ closure T := by
      have h1 : frontier U \ A ⊆ T ∪ {-(ε : ℂ)} := fun z hz => by
        by_cases hz' : z = -(ε : ℂ)
        · exact Or.inr hz'
        · exact Or.inl ⟨hz, hz'⟩
      have h2 := closure_mono h1 hc
      rw [closure_union, closure_singleton] at h2
      exact h2.resolve_right hx₀'
    have h3 := (fl2Mob_mem_closure_image hε hT (fl2Mob_ne hε hx₀')).2
      (by rwa [fl2MobInv_flMob hε hx₀'])
    refine closure_mono ?_ h3
    rintro _ ⟨z, ⟨⟨hzf, hzA⟩, hzp⟩, rfl⟩
    have hzp' : z ≠ -(ε : ℂ) := hzp
    rw [hU.frontier_eq] at hzf
    refine ⟨?_, fun hA => hzA ?_⟩
    · rw [hU'.frontier_eq]
      refine ⟨(fl2Mob_mem_closure_image hε hpU (fl2Mob_ne hε hzp')).2
        (by rw [fl2MobInv_flMob hε hzp']; exact hzf.1), fun hm => hzf.2 ?_⟩
      have := ((fl2Mob_mem_image hε hpU).1 hm).2
      rwa [fl2MobInv_flMob hε hzp'] at this
    · have := ((fl2Mob_mem_image hε hpA').1 hA).2
      rwa [fl2MobInv_flMob hε hzp'] at this
  · intro x hx hcl
    rw [hU'.frontier_eq] at hx
    have hxI := hnI x hx.1
    have hzc : fl2MobInv ε x ∈ closure U := (fl2Mob_mem_closure_image hε hpU hxI).1 hx.1
    have hzU : fl2MobInv ε x ∉ U := fun h => hx.2 ((fl2Mob_mem_image hε hpU).2 ⟨hxI, h⟩)
    have hzA : fl2MobInv ε x ∉ closure A := fun h =>
      hcl ((fl2Mob_mem_closure_image hε hpA' hxI).2 h)
    have hzf : fl2MobInv ε x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hzc, hzU⟩
    exact (hh.zero _ hzf hzA).comp (fl2Mob_tendsto_within hε hpU hxI)
  · intro _
    have hp0 : Tendsto h (𝓝[U] (-(ε : ℂ))) (𝓝 0) := by
      by_cases hcl : -(ε : ℂ) ∈ closure U
      · exact hh.zero _ (by rw [hU.frontier_eq]; exact ⟨hcl, hpU⟩) hpA
      · have : 𝓝[U] (-(ε : ℂ)) = ⊥ := by
          rw [mem_closure_iff_nhdsWithin_neBot] at hcl
          exact not_neBot.1 hcl
        rw [this]; exact tendsto_bot
    exact hp0.comp (fl2Mob_tendsto_cobounded hε hpU)

end Mob

end FieldLawler
end QuantumZipper
