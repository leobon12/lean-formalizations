import QuantumZipper.Proofs.Thm18.G1ZB2CPath
import QuantumZipper.Proofs.Complex.UniformizerNormalize
import QuantumZipper.Proofs.Complex.UniformizerRight
import QuantumZipper.Proofs.Thm18.G1ZA1aDrv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2C (4): geometry of Brownian rescaling of the side maps

Theorem 1.8, G1 zoom, node B2-C: `G1SideShiftGeomStmt` (G1ZB2CPath.lean). Rescaling a good driver
`W` to `W_s(r) = W(s² r⁺)/s` rescales its trace by `1/s` (`RS.trace_scale`), hence the side
domains by `1/s`; the normalized uniformizer of the rescaled domain is `φ(s ·)/s`, and two
normalized uniformizers of the same domain differ by a positive factor
(`CA.Uniformizer.normalizedUniformizer_unique_*`). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm

/-- The chosen uniformizer of a side domain of a simple chord is normalized (Riemann mapping
theorem with Carathéodory normalization, `CA.Uniformizer.exists_normalizedUniformizer_*`). -/
theorem g1zB2c_isNormalizedUniformizer_sideDom {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    IsNormalizedUniformizer (sideDom η left) (uniformizer (sideDom η left)) := by
  unfold uniformizer
  cases left
  · exact Classical.epsilon_spec (CA.Uniformizer.exists_normalizedUniformizer_rightComponent hη)
  · exact Classical.epsilon_spec (CA.Uniformizer.exists_normalizedUniformizer_leftComponent hη)

/-- The rescaled driver of `canonConfig` (`g1zNewDrv` at time `0`). -/
theorem g1zB2c_trace_scaled {W : ℝ → ℝ} (hG : G1zDrvGood W) {s : ℝ} (hs : 0 < s) {r : ℝ}
    (hr : 0 ≤ r) :
    trace (fun r => W (s ^ 2 * max r 0) / s) r = trace W (s ^ 2 * r) / s := by
  obtain ⟨hW, hW0, -, -, -⟩ := id hG
  have hV : Continuous fun r => W (s ^ 2 * r) / s := by fun_prop
  have hU : Continuous fun r => W (s ^ 2 * max r 0) / s := by fun_prop
  have hV0 : (fun r => W (s ^ 2 * r) / s) 0 = 0 := by simp [hW0]
  have hU0 : (fun r => W (s ^ 2 * max r 0) / s) 0 = 0 := by simp [hW0]
  rw [RS.trace_congr_drive hU hU0 hV hV0 hr (fun u hu => by
    simp only [max_eq_left hu.1])]
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    rw [mul_zero, G1Pkg.trace_zero_time hV, G1Pkg.trace_zero_time hW]
    simp [hW0]
  · exact (RS.trace_scale hW hW0 hs hr
      (G1ZA1a.tendsto_fwdMapInv_trace hG (by positivity))).2

/-- The rescaled trace is a simple chord. -/
theorem g1zB2c_simpleChord {W : ℝ → ℝ} (hG : G1zDrvGood W) {s : ℝ} (hs : 0 < s) :
    IsSimpleChord (trace fun r => W (s ^ 2 * max r 0) / s) := by
  have hη := hG.2.2.2.1
  have hs2 : 0 < s ^ 2 := by positivity
  have hEq : EqOn (trace fun r => W (s ^ 2 * max r 0) / s)
      (fun r => trace W (s ^ 2 * r) / s) (Ici 0) := fun r hr => g1zB2c_trace_scaled hG hs hr
  have hmap : MapsTo (fun r : ℝ => s ^ 2 * r) (Ici 0) (Ici 0) := fun r hr =>
    mul_nonneg hs2.le hr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hEq (Set.mem_Ici.2 (le_refl (0:ℝ)))]
    simp [hη.1]
  · refine ContinuousOn.congr ?_ hEq
    exact (hη.2.1.comp (by fun_prop) hmap).div_const _
  · intro a ha b hb hab
    rw [hEq ha, hEq hb] at hab
    have := hη.2.2.1 (hmap ha) (hmap hb) (by
      have h2 := congrArg (fun z => z * (s : ℂ)) hab
      simpa [div_mul_cancel₀, hs.ne'] using h2)
    exact mul_left_cancel₀ hs2.ne' this
  · intro t ht
    rw [hEq (le_of_lt ht)]
    have h := hη.2.2.2.1 (s ^ 2 * t) (by positivity)
    show 0 < (trace W (s ^ 2 * t) / (s : ℂ)).im
    rw [Complex.div_ofReal_im]
    exact div_pos h hs
  · have h1 := hη.2.2.2.2.comp (tendsto_id.const_mul_atTop hs2)
    have h2 := h1.atTop_div_const hs
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hEq ht]
    simp only [Function.comp, id, norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]

/-- Transport of a complementary component under a positive dilation: if `c z ∈ E' ↔ z ∈ E`,
then `z` in the `S`-component of `E` gives `c z` in the `S`-component of `E'`. -/
theorem g1zB2c_component_scale (S : ℝ → Prop) (hS : ∀ (x c : ℝ), 0 < c → S x → S (c * x))
    {c : ℝ} (hc : 0 < c) {E E' : Set ℂ} (hE : ∀ z : ℂ, (c : ℂ) * z ∈ E' ↔ z ∈ E) {z z' : ℂ}
    (hz' : z' = (c : ℂ) * z) (hz : z ∈ H \ E ∧ ∃ x : ℝ, S x ∧ ∃ p : Path z (x : ℂ), ∀ t : unitInterval, t ≠ 1 →
      p t ∈ H \ E) :
    z' ∈ H \ E' ∧ ∃ x : ℝ, S x ∧ ∃ p : Path z' (x : ℂ),
      ∀ t : unitInterval, t ≠ 1 → p t ∈ H \ E' := by
  subst hz'
  obtain ⟨hzE, x, hx, p, hp⟩ := hz
  have hmem : ∀ w : ℂ, w ∈ H \ E → (c : ℂ) * w ∈ H \ E' := fun w hw =>
    ⟨G1.mul_mem_H hc hw.1, fun h => hw.2 ((hE w).1 h)⟩
  refine ⟨hmem z hzE, c * x, hS x c hc hx, (p.map (continuous_const.mul continuous_id)).cast rfl
    (by push_cast; rfl), fun t ht => ?_⟩
  exact hmem _ (hp t ht)

/-- The side domain of the rescaled trace is the dilation by `1/s` of the side domain. -/
theorem g1zB2c_mem_sideDom {W : ℝ → ℝ} (hG : G1zDrvGood W) {s : ℝ} (hs : 0 < s) (left : Bool)
    (z : ℂ) :
    z ∈ sideDom (trace fun r => W (s ^ 2 * max r 0) / s) left ↔
      (s : ℂ) * z ∈ sideDom (trace W) left := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hEq := fun r (hr : r ∈ Ici (0:ℝ)) => g1zB2c_trace_scaled hG hs (Set.mem_Ici.1 hr)
  have himg : ∀ z : ℂ, (s : ℂ) * z ∈ trace W '' Ici 0 ↔
      z ∈ (trace fun r => W (s ^ 2 * max r 0) / s) '' Ici 0 := by
    intro z
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    constructor
    · rintro ⟨r, hr, hrz⟩
      refine ⟨r / s ^ 2, (div_nonneg (Set.mem_Ici.1 hr) hs2.le), ?_⟩
      rw [g1zB2c_trace_scaled hG hs (div_nonneg (Set.mem_Ici.1 hr) hs2.le),
        mul_div_cancel₀ _ hs2.ne', hrz, mul_div_cancel_left₀ _ hs']
    · rintro ⟨r, hr, rfl⟩
      refine ⟨s ^ 2 * r, mul_nonneg hs2.le hr, ?_⟩
      rw [g1zB2c_trace_scaled hG hs hr, mul_div_cancel₀ _ hs']
  have himg' : ∀ z : ℂ, ((s⁻¹ : ℝ) : ℂ) * z ∈ (trace fun r => W (s ^ 2 * max r 0) / s) '' Ici 0 ↔
      z ∈ trace W '' Ici 0 := by
    intro z
    rw [← himg]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    rw [mul_inv_cancel_left₀ hs']
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  cases left
  · show z ∈ rightComponent _ ↔ (s : ℂ) * z ∈ rightComponent _
    constructor
    · exact fun h => g1zB2c_component_scale (fun x => 0 < x)
        (fun x c hc hx => mul_pos hc hx) hs (fun z => himg z) rfl h
    · intro h
      have := g1zB2c_component_scale (fun x => 0 < x) (fun x c hc hx => mul_pos hc hx)
        (inv_pos.2 hs) (fun w => himg' w) (z' := z) (by push_cast; rw [inv_mul_cancel_left₀ hs'])
        h
      exact this
  · show z ∈ leftComponent _ ↔ (s : ℂ) * z ∈ leftComponent _
    constructor
    · exact fun h => g1zB2c_component_scale (fun x => x < 0)
        (fun x c hc hx => mul_neg_of_pos_of_neg hc hx) hs (fun z => himg z) rfl h
    · intro h
      have := g1zB2c_component_scale (fun x => x < 0)
        (fun x c hc hx => mul_neg_of_pos_of_neg hc hx)
        (inv_pos.2 hs) (fun w => himg' w) (z' := z) (by push_cast; rw [inv_mul_cancel_left₀ hs'])
        h
      exact this

/-- The rescaled uniformizer `z ↦ φ(s z)/s` of the dilated domain. -/
theorem g1zB2c_isNormalized {D D' : Set ℂ} {s : ℝ} (hs : 0 < s)
    (hDD : ∀ z : ℂ, z ∈ D' ↔ (s : ℂ) * z ∈ D) {φ : ℂ → ℂ} (hφ : IsNormalizedUniformizer D φ) :
    IsNormalizedUniformizer D' (fun z => (s : ℂ)⁻¹ * φ ((s : ℂ) * z)) := by
  obtain ⟨hb, hd, h0, hi⟩ := hφ
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hmulH : ∀ w ∈ H, (s : ℂ)⁻¹ * w ∈ H := fun w hw => by
    simpa [Complex.ofReal_inv] using G1.mul_mem_H (inv_pos.2 hs) hw
  have hmaps : MapsTo (fun z : ℂ => (s : ℂ) * z) D' D := fun z hz => (hDD z).1 hz
  refine ⟨⟨fun z hz => hmulH _ (hb.mapsTo ((hDD z).1 hz)), fun z1 hz1 z2 hz2 h => ?_,
    fun w hw => ?_⟩, ?_, ?_, ?_⟩
  · have h' := mul_left_cancel₀ (inv_ne_zero hs') h
    exact mul_left_cancel₀ hs' (hb.injOn ((hDD z1).1 hz1) ((hDD z2).1 hz2) h')
  · obtain ⟨u, hu, hφu⟩ := hb.surjOn (G1.mul_mem_H hs hw)
    refine ⟨(s : ℂ)⁻¹ * u, (hDD _).2 (by rw [mul_inv_cancel_left₀ hs']; exact hu), ?_⟩
    simp only
    rw [mul_inv_cancel_left₀ hs', hφu, inv_mul_cancel_left₀ hs']
  · exact (differentiableOn_const _).mul
      (hd.comp ((differentiable_id.const_mul (s : ℂ)).differentiableOn) hmaps)
  · have hT : Tendsto (fun z : ℂ => (s : ℂ) * z) (𝓝[D'] 0) (𝓝[D] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun z hz => hmaps hz⟩
      have : Tendsto (fun z : ℂ => (s : ℂ) * z) (𝓝 0) (𝓝 ((s : ℂ) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    simpa using (h0.comp hT).const_mul ((s : ℂ)⁻¹)
  · have hc : Tendsto (fun z : ℂ => (s : ℂ) * z) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      have := tendsto_norm_cobounded_atTop (E := ℂ)
      refine (this.const_mul_atTop hs).congr fun z => ?_
      simp [Real.norm_of_nonneg hs.le]
    have hT : Tendsto (fun z : ℂ => (s : ℂ) * z) (Bornology.cobounded ℂ ⊓ 𝓟 D')
        (Bornology.cobounded ℂ ⊓ 𝓟 D) :=
      tendsto_inf.2 ⟨hc.mono_left inf_le_left, tendsto_principal.2
        (eventually_of_mem (mem_inf_of_right (mem_principal_self D')) fun z hz => hmaps hz)⟩
    refine ((hi.comp hT).const_mul_atTop (inv_pos.2 hs)).congr fun z => ?_
    simp only [Function.comp]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]

/-- The inverse of the rescaled uniformizer. -/
theorem g1zB2c_invFunOn_scaled {D D' : Set ℂ} {s : ℝ} (hs : 0 < s)
    (hDD : ∀ z : ℂ, z ∈ D' ↔ (s : ℂ) * z ∈ D) {φ : ℂ → ℂ} (hφ : IsNormalizedUniformizer D φ)
    {w : ℂ} (hw : w ∈ H) :
    invFunOn (fun z => (s : ℂ)⁻¹ * φ ((s : ℂ) * z)) D' w =
      (s : ℂ)⁻¹ * invFunOn φ D ((s : ℂ) * w) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hφs := g1zB2c_isNormalized hs hDD hφ
  have hex : ∃ a ∈ D, φ a = (s : ℂ) * w := hφ.1.surjOn (G1.mul_mem_H hs hw)
  have hu : invFunOn φ D ((s : ℂ) * w) ∈ D := invFunOn_mem hex
  have hφu : φ (invFunOn φ D ((s : ℂ) * w)) = (s : ℂ) * w := invFunOn_eq hex
  have hex' : ∃ a ∈ D', (fun z => (s : ℂ)⁻¹ * φ ((s : ℂ) * z)) a = w := hφs.1.surjOn hw
  have hmem : (s : ℂ)⁻¹ * invFunOn φ D ((s : ℂ) * w) ∈ D' :=
    (hDD _).2 (by rw [mul_inv_cancel_left₀ hs']; exact hu)
  refine hφs.1.injOn (invFunOn_mem hex') hmem ?_
  rw [invFunOn_eq hex']
  show w = (s : ℂ)⁻¹ * φ ((s : ℂ) * ((s : ℂ)⁻¹ * invFunOn φ D ((s : ℂ) * w)))
  rw [mul_inv_cancel_left₀ hs', hφu, inv_mul_cancel_left₀ hs']

/-- **Geometry of Brownian rescaling (`G1SideShiftGeomStmt`).** -/
theorem g1SideShiftGeomStmt_holds : G1SideShiftGeomStmt := by
  intro W hG s hs left
  have hη : IsSimpleChord (trace W) := hG.2.2.2.1
  have hηs := g1zB2c_simpleChord hG hs
  have hDD := g1zB2c_mem_sideDom hG hs left
  have hu := g1zB2c_isNormalizedUniformizer_sideDom hη left
  have hus := g1zB2c_isNormalizedUniformizer_sideDom hηs left
  have hφs := g1zB2c_isNormalized hs hDD hu
  obtain ⟨b, hb, hEqb⟩ := G1.exists_invFunOn_uniformizer_eq hηs left hφs hus
  refine ⟨s * b, mul_pos hs hb, fun w hw => ?_⟩
  unfold g1zSideMap
  have hbw : (b : ℂ) * w ∈ H := G1.mul_mem_H hb hw
  rw [hEqb hw]
  show invFunOn _ _ ((b : ℂ) * w) = _
  rw [g1zB2c_invFunOn_scaled hs hDD hu hbw]
  have e : (s : ℂ) * ((b : ℂ) * w) = ((s * b : ℝ) : ℂ) * w := by push_cast; ring
  rw [e]

end Thm18Asm
end QuantumZipper
