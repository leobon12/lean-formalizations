import QuantumZipper.Proofs.Thm18.G1ZA1aAff
import QuantumZipper.Proofs.Thm18.G1ZA1aBdry
import QuantumZipper.Proofs.Thm18.G1RegRepMeas
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Thm18.G3Z2b2Loc
import QuantumZipper.Proofs.Thm18.G1Z2ReflChord
import QuantumZipper.Proofs.Thm18.G1ZZ1Meas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM (4): scale covariance of the side maps under Brownian scaling of the path

Removing the random dilation `b = scaleParam` from the Palm-window integral (the obstacle
"Palm after dilation"): the path law is invariant under Brownian scaling
`S_b a = a(b² ·)/b` (`map_pathOf_smul_eq`), and the side maps of the scaled path are the
dilated side maps of the path, up to a precomposed dilation that the canonical zoom data do not
see. So, averaging over the (independent) path first, the dilation `b` of the canonical wedge can
be absorbed into the path (Sheffield, arXiv:1012.4797, p. 70: the curve is independent of the
wedge, and SLE is scale invariant).

This file proves the deterministic part:
* `mem_sideDom_dil`: dilating the trace image by `c > 0` dilates both side components;
* `isNormalizedUniformizer_dil`: `φ(c⁻¹ ·)` is a normalized uniformizer of the dilated domain;
* `invFunOn_dil`: the inverse normalized uniformizers of the dilated domain are the dilated
  inverses up to a precomposed positive factor (uniqueness, `normalizedUniformizer_unique`);
* `pathDrive_scalePath`, `mem_pathTrace_scalePath`: the driver and trace image of `S_b a`
  (Loewner scaling, `RS.trace_scale`).

Own elementary arguments (AGENT_GUIDE cost rule) on top of `normalizedUniformizer_unique`
(uniqueness of normalized uniformizers) and `RS.trace_scale` (Lawler, *Conformally invariant
processes in the plane*, §4.1, scaling of the Loewner equation).
-/

noncomputable section

open Filter Set Complex Function Bornology
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Zm

/-- Dilating a path avoiding a set: `c · p` avoids the dilated set. -/
theorem exists_dil_path {I I' : Set ℂ} {c : ℝ} (hc : 0 < c)
    (hI : ∀ w, w ∈ I' ↔ ((c : ℂ))⁻¹ * w ∈ I) {P : ℝ → Prop} (hP : ∀ x, P x → P (c * x))
    {z : ℂ} {x : ℝ} (hx : P x) (p : Path z (x : ℂ)) (hp : ∀ t : unitInterval, t ≠ 1 → p t ∈ H \ I) :
    ∃ x' : ℝ, P x' ∧ ∃ p' : Path ((c : ℂ) * z) (x' : ℂ),
      ∀ t : unitInterval, t ≠ 1 → p' t ∈ H \ I' := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  refine ⟨c * x, hP x hx, (p.map (continuous_const.mul continuous_id :
    Continuous fun w : ℂ => (c : ℂ) * w)).cast rfl (by push_cast; rfl), fun t ht => ?_⟩
  obtain ⟨hH, hnI⟩ := hp t ht
  refine ⟨?_, fun hmem => hnI ?_⟩
  · show 0 < ((c : ℂ) * p t).im
    rw [im_ofReal_mul]; exact mul_pos hc hH
  · have := (hI _).1 hmem
    simpa [← mul_assoc, inv_mul_cancel₀ hc'] using this

/-- Dilating the trace image by `c > 0` dilates both side components. -/
theorem mem_sideDom_dil {η η' : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (himg : ∀ w, w ∈ η' '' Ici 0 ↔ ((c : ℂ))⁻¹ * w ∈ η '' Ici 0) (left : Bool) (w : ℂ) :
    w ∈ sideDom η' left ↔ ((c : ℂ))⁻¹ * w ∈ sideDom η left := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have himg' : ∀ w, w ∈ η '' Ici 0 ↔ ((c⁻¹ : ℝ) : ℂ)⁻¹ * w ∈ η' '' Ici 0 := fun w => by
    rw [himg]; push_cast; rw [inv_inv, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  have hHc : ∀ w : ℂ, w ∈ H → ((c : ℂ))⁻¹ * w ∈ H := fun w hw => by
    show 0 < ((c : ℂ)⁻¹ * w).im
    rw [← ofReal_inv, im_ofReal_mul]; exact mul_pos hci hw
  have e : ((c⁻¹ : ℝ) : ℂ) * w = ((c : ℂ))⁻¹ * w := by push_cast; ring
  have hnot : ∀ {I I' : Set ℂ}, (∀ w, w ∈ I' ↔ ((c : ℂ))⁻¹ * w ∈ I) →
      (w ∈ H \ I' ↔ ((c : ℂ))⁻¹ * w ∈ H \ I) := fun {I I'} h => by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hHc w h1, fun h3 => h2 ((h w).2 h3)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun h3 => h2 ((h w).1 h3)⟩
      have := hHc _ h1
      have h4 : (0 : ℝ) < c * (((c : ℂ))⁻¹ * w).im := mul_pos hc h1
      rw [← im_ofReal_mul, ← mul_assoc, mul_inv_cancel₀ hc', one_mul] at h4
      exact h4
  cases left <;> simp only [sideDom, Bool.false_eq_true, if_false, if_true]
  · -- right components
    constructor
    · rintro ⟨hz, x, hx, p, hp⟩
      obtain ⟨x', hx', p', hp'⟩ := exists_dil_path hci himg' (P := fun x => 0 < x)
        (fun x hx => mul_pos hci hx) hx p hp
      exact ⟨(hnot himg).1 hz, x', hx', p'.cast e.symm rfl, fun t ht => by simpa using hp' t ht⟩
    · rintro ⟨hz, x, hx, p, hp⟩
      obtain ⟨x', hx', p', hp'⟩ := exists_dil_path hc himg (P := fun x => 0 < x)
        (fun x hx => mul_pos hc hx) hx p hp
      have e2 : (c : ℂ) * (((c : ℂ))⁻¹ * w) = w := by
        rw [← mul_assoc, mul_inv_cancel₀ hc', one_mul]
      exact ⟨(hnot himg).2 hz, x', hx', p'.cast e2.symm rfl, fun t ht => by simpa using hp' t ht⟩
  · -- left components
    constructor
    · rintro ⟨hz, x, hx, p, hp⟩
      obtain ⟨x', hx', p', hp'⟩ := exists_dil_path hci himg' (P := fun x => x < 0)
        (fun x hx => mul_neg_of_pos_of_neg hci hx) hx p hp
      exact ⟨(hnot himg).1 hz, x', hx', p'.cast e.symm rfl, fun t ht => by simpa using hp' t ht⟩
    · rintro ⟨hz, x, hx, p, hp⟩
      obtain ⟨x', hx', p', hp'⟩ := exists_dil_path hc himg (P := fun x => x < 0)
        (fun x hx => mul_neg_of_pos_of_neg hc hx) hx p hp
      have e2 : (c : ℂ) * (((c : ℂ))⁻¹ * w) = w := by
        rw [← mul_assoc, mul_inv_cancel₀ hc', one_mul]
      exact ⟨(hnot himg).2 hz, x', hx', p'.cast e2.symm rfl, fun t ht => by simpa using hp' t ht⟩

/-- `φ(c⁻¹ ·)` is a normalized uniformizer of the dilated domain. -/
theorem isNormalizedUniformizer_dil {D D' : Set ℂ} {φ : ℂ → ℂ} (hφ : IsNormalizedUniformizer D φ)
    {c : ℝ} (hc : 0 < c) (hD : ∀ w, w ∈ D' ↔ ((c : ℂ))⁻¹ * w ∈ D) :
    IsNormalizedUniformizer D' fun w => φ (((c : ℂ))⁻¹ * w) := by
  obtain ⟨hb, hd, h0, hi⟩ := hφ
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  have hcont : Continuous fun w : ℂ => ((c : ℂ))⁻¹ * w := continuous_const.mul continuous_id
  refine ⟨⟨fun w hw => hb.mapsTo ((hD w).1 hw), fun w₁ h₁ w₂ h₂ h => ?_, fun y hy => ?_⟩,
    ?_, ?_, ?_⟩
  · have := hb.injOn ((hD w₁).1 h₁) ((hD w₂).1 h₂) h
    exact mul_left_cancel₀ (inv_ne_zero hc') this
  · obtain ⟨z, hz, rfl⟩ := hb.surjOn hy
    refine ⟨(c : ℂ) * z, (hD _).2 ?_, ?_⟩ <;>
      simp only [← mul_assoc, inv_mul_cancel₀ hc', one_mul, hz]
  · exact hd.comp ((differentiable_const _).mul differentiable_id).differentiableOn
      fun w hw => (hD w).1 hw
  · have ht : Tendsto (fun w : ℂ => ((c : ℂ))⁻¹ * w) (𝓝[D'] 0) (𝓝[D] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun w hw => (hD w).1 hw⟩
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := D'))
      simpa using this
    exact h0.comp ht
  · have ht : Tendsto (fun w : ℂ => ((c : ℂ))⁻¹ * w) (cobounded ℂ ⊓ 𝓟 D') (cobounded ℂ ⊓ 𝓟 D) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2
        (eventually_inf_principal.2 (Eventually.of_forall fun w hw => (hD w).1 hw))⟩
      refine Tendsto.mono_left ?_ inf_le_left
      rw [← tendsto_norm_atTop_iff_cobounded]
      have : Tendsto (fun w : ℂ => c⁻¹ * ‖w‖) (cobounded ℂ) atTop :=
        (tendsto_norm_cobounded_atTop).const_mul_atTop (inv_pos.2 hc)
      refine this.congr fun w => ?_
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact hi.comp ht

/-- **Inverse normalized uniformizers of a dilated domain.** If `D'` is the dilation of `D` by
`c > 0`, then the inverse of any normalized uniformizer of `D'` is `c ·` the inverse of any
normalized uniformizer of `D`, precomposed with a positive dilation. -/
theorem invFunOn_dil {D D' : Set ℂ} {φ φ' : ℂ → ℂ} (hφ : IsNormalizedUniformizer D φ)
    (hφ' : IsNormalizedUniformizer D' φ') (hD'o : IsOpen D') (hD'0 : (𝓝[D'] (0 : ℂ)).NeBot)
    (hD'i : (cobounded ℂ ⊓ 𝓟 D').NeBot) {c : ℝ} (hc : 0 < c)
    (hD : ∀ w, w ∈ D' ↔ ((c : ℂ))⁻¹ * w ∈ D) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ w ∈ H,
      invFunOn φ' D' w = (c : ℂ) * invFunOn φ D (((μ : ℂ))⁻¹ * w) := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  have hψ := isNormalizedUniformizer_dil hφ hc hD
  obtain ⟨μ, hμ, heq⟩ :=
    CA.Uniformizer.normalizedUniformizer_unique hD'o hD'0 hD'i hψ hφ'
  refine ⟨μ, hμ, fun w hw => ?_⟩
  have hμ' : (μ : ℂ) ≠ 0 := ofReal_ne_zero.2 hμ.ne'
  have hwμ : ((μ : ℂ))⁻¹ * w ∈ H := by
    show 0 < (((μ : ℂ))⁻¹ * w).im
    rw [← ofReal_inv, im_ofReal_mul]; exact mul_pos (inv_pos.2 hμ) hw
  obtain ⟨hb, -, -, -⟩ := hφ
  have hex : ∃ z ∈ D, φ z = ((μ : ℂ))⁻¹ * w := hb.surjOn hwμ
  set z := invFunOn φ D (((μ : ℂ))⁻¹ * w) with hz
  have hzD : z ∈ D := invFunOn_mem hex
  have hφz : φ z = ((μ : ℂ))⁻¹ * w := invFunOn_eq hex
  have hczD' : (c : ℂ) * z ∈ D' := (hD _).2 (by rwa [← mul_assoc, inv_mul_cancel₀ hc', one_mul])
  have hval : φ' ((c : ℂ) * z) = w := by
    rw [heq hczD']
    simp only [← mul_assoc, inv_mul_cancel₀ hc', one_mul, hφz]
    rw [mul_inv_cancel₀ hμ', one_mul]
  have hex' : ∃ z' ∈ D', φ' z' = w := ⟨_, hczD', hval⟩
  obtain ⟨hb', -, -, -⟩ := hφ'
  exact hb'.injOn (invFunOn_mem hex') hczD' ((invFunOn_eq hex').trans hval.symm)

/-- Brownian scaling of a path: `S_b a = a(b² ·)/b`. -/
def scalePath (b : ℝ) (a : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun s => a ((b ^ 2).toNNReal * s) / b

theorem pathDrive_scalePath (κ b : ℝ) (a : ℝ≥0 → ℝ) :
    pathDrive κ (scalePath b a) = fun r => pathDrive κ a (b ^ 2 * r) / b := by
  funext r
  simp only [pathDrive, scalePath]
  rw [Real.toNNReal_mul (sq_nonneg b), mul_div_assoc]

/-- The trace image of the scaled path is the trace image dilated by `b⁻¹` (Loewner scaling),
when the trace limits of the path exist at all times. -/
theorem mem_pathTrace_scalePath {κ b : ℝ} (hb : 0 < b) (a : ℝ≥0 → ℝ)
    (hW : Continuous (pathDrive κ a)) (hW0 : pathDrive κ a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive κ a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (w : ℂ) :
    w ∈ pathTrace κ (scalePath b a) '' Ici 0 ↔
      (((b⁻¹ : ℝ) : ℂ))⁻¹ * w ∈ pathTrace κ a '' Ici 0 := by
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  have htr : ∀ t : ℝ, 0 ≤ t →
      pathTrace κ (scalePath b a) t = pathTrace κ a (b ^ 2 * t) / b := by
    intro t ht
    obtain ⟨p, hp⟩ := hex (b ^ 2 * t) (by positivity)
    have h := (RS.trace_scale hW hW0 hb ht hp).2
    have e : pathTrace κ (scalePath b a) = trace (fun r => pathDrive κ a (b ^ 2 * r) / b) := by
      rw [← pathDrive_scalePath]; rfl
    rw [e, h]; rfl
  have hinv : (((b⁻¹ : ℝ) : ℂ))⁻¹ * w = (b : ℂ) * w := by push_cast; rw [inv_inv]
  rw [hinv]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨b ^ 2 * t, mul_nonneg (sq_nonneg b) ht, ?_⟩
    rw [htr t ht, mul_div_cancel₀ _ hb']
  · rintro ⟨s, hs, hsw⟩
    have hs0 : (0 : ℝ) ≤ s / b ^ 2 := div_nonneg hs (sq_nonneg b)
    refine ⟨s / b ^ 2, hs0, ?_⟩
    rw [htr _ hs0, mul_div_cancel₀ _ (pow_pos hb 2).ne', hsw]
    field_simp

/-- The trace of the scaled path, pointwise (Loewner scaling). -/
theorem pathTrace_scalePath_apply {κ b : ℝ} (hb : 0 < b) (a : ℝ≥0 → ℝ)
    (hW : Continuous (pathDrive κ a)) (hW0 : pathDrive κ a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive κ a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    {t : ℝ} (ht : 0 ≤ t) :
    pathTrace κ (scalePath b a) t = pathTrace κ a (b ^ 2 * t) / b := by
  obtain ⟨p, hp⟩ := hex (b ^ 2 * t) (by positivity)
  have h := (RS.trace_scale hW hW0 hb ht hp).2
  have e : pathTrace κ (scalePath b a) = trace (fun r => pathDrive κ a (b ^ 2 * r) / b) := by
    rw [← pathDrive_scalePath]; rfl
  rw [e, h]; rfl

/-- **Brownian scaling preserves simple chords.** -/
theorem isSimpleChord_scalePath {κ b : ℝ} (hb : 0 < b) (a : ℝ≥0 → ℝ)
    (hW : Continuous (pathDrive κ a)) (hW0 : pathDrive κ a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive κ a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (hs : IsSimpleChord (pathTrace κ a)) : IsSimpleChord (pathTrace κ (scalePath b a)) := by
  obtain ⟨h0, hc, hinj, hH, hinf⟩ := hs
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  have htr := fun {t : ℝ} (ht : 0 ≤ t) => pathTrace_scalePath_apply hb a hW hW0 hex (t := t) ht
  have hmaps : MapsTo (fun t : ℝ => b ^ 2 * t) (Ici 0) (Ici 0) := fun t ht =>
    mul_nonneg (sq_nonneg b) ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htr le_rfl, mul_zero, h0, zero_div]
  · have hc' : ContinuousOn (fun t : ℝ => pathTrace κ a (b ^ 2 * t) / b) (Ici 0) :=
      (hc.comp (continuous_const.mul continuous_id).continuousOn hmaps).div_const _
    exact hc'.congr fun t ht => htr ht
  · intro s hs t ht hst
    rw [htr hs, htr ht] at hst
    have h2 := hinj (hmaps hs) (hmaps ht) ((div_left_inj' hb').1 hst)
    exact mul_left_cancel₀ (pow_pos hb 2).ne' h2
  · intro t ht
    rw [htr ht.le]
    have h1 := hH (b ^ 2 * t) (by positivity)
    show 0 < (pathTrace κ a (b ^ 2 * t) / b).im
    rw [Complex.div_ofReal_im]
    exact div_pos h1 hb
  · have h1 : Tendsto (fun t : ℝ => ‖pathTrace κ a (b ^ 2 * t)‖ / b) atTop atTop :=
      (hinf.comp (tendsto_id.const_mul_atTop (pow_pos hb 2))).atTop_div_const hb
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [htr ht, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]

/-- **Scale covariance of the inverse side uniformizers.** For a good path `a` whose Brownian
scaling `S_b a` is also good, the selected inverse side uniformizer of `S_b a` is `b⁻¹ ·` the one
of `a`, precomposed with a positive dilation. -/
theorem psi_scalePath {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ) {b : ℝ}
    (hb : 0 < b) {a : ℝ≥0 → ℝ} (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a))
    (hac' : Continuous (scalePath b a))
    (hs' : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b a)))
    (hW : Continuous (pathDrive (γ ^ 2) a)) (hW0 : pathDrive (γ ^ 2) a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive (γ ^ 2) a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (left : Bool) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ w ∈ H,
      Ψ left (scalePath b a) w = ((b⁻¹ : ℝ) : ℂ) * Ψ left a (((μ : ℂ))⁻¹ * w) := by
  obtain ⟨φ, hN, hΨ⟩ := hsel.2.2 a hac hs left
  obtain ⟨φ', hN', hΨ'⟩ := hsel.2.2 _ hac' hs' left
  have hD : ∀ w, w ∈ sideDom (pathTrace (γ ^ 2) (scalePath b a)) left ↔
      (((b⁻¹ : ℝ) : ℂ))⁻¹ * w ∈ sideDom (pathTrace (γ ^ 2) a) left :=
    mem_sideDom_dil (inv_pos.2 hb) (mem_pathTrace_scalePath hb a hW hW0 hex) left
  obtain ⟨μ, hμ, h⟩ := invFunOn_dil hN hN' (G1ZA1a.isOpen_sideDom hs' left)
    (G1ZA1a.nhdsWithin_zero_sideDom_neBot hs' left)
    (G1ZA1a.neBot_cobounded_inf_sideDom hs' left) (inv_pos.2 hb) hD
  refine ⟨μ, hμ, fun w hw => ?_⟩
  rw [hΨ', hΨ]
  exact h w hw

/-- **Scale covariance of the measurable local maps.** Under the hypotheses of `psi_scalePath`,
the local map of the scaled path at `x / b`, multiplied by `b`, is the local map of the path at
`x` precomposed with the dilation by `μ⁻¹` (the same `μ > 0` for every `x`). -/
theorem g3locM_scalePath {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ) {b : ℝ}
    (hb : 0 < b) {a : ℝ≥0 → ℝ} (hac : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a))
    (hac' : Continuous (scalePath b a))
    (hs' : IsSimpleChord (pathTrace (γ ^ 2) (scalePath b a)))
    (hW : Continuous (pathDrive (γ ^ 2) a)) (hW0 : pathDrive (γ ^ 2) a 0 = 0)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive (γ ^ 2) a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))
    (left : Bool) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ g1SideHalf left, ∀ w ∈ H,
      (b : ℂ) * G3Z2b2.g3locM Ψ left (scalePath b a, x / b, w) =
        G3Z2b2.g3locM Ψ left (a, x, ((μ : ℂ))⁻¹ * w) := by
  obtain ⟨μ, hμ, hΨ⟩ := psi_scalePath hsel hb hac hs hac' hs' hW hW0 hex left
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.2 hb.ne'
  have hμ' : (μ : ℂ) ≠ 0 := ofReal_ne_zero.2 hμ.ne'
  obtain ⟨φ, hN, hΨa⟩ := hsel.2.2 a hac hs left
  obtain ⟨Φ, hΦ⟩ := G1Z2.sideReflChordStmt_holds _ hs left φ hN
  rw [← hΨa] at hΦ
  obtain ⟨φ', hN', hΨa'⟩ := hsel.2.2 _ hac' hs' left
  obtain ⟨Φ', hΦ'⟩ := G1Z2.sideReflChordStmt_holds _ hs' left φ' hN'
  rw [← hΨa'] at hΦ'
  have hhalf_mul : ∀ {c : ℝ}, 0 < c → ∀ {t : ℝ}, t ∈ g1SideHalf left → c * t ∈ g1SideHalf left :=
    fun {c} hc {t} ht => by
      cases left
      · exact mul_pos hc (by simpa [g1SideHalf] using ht)
      · show c * t ∈ g1SideHalf true
        simp only [g1SideHalf, if_true, mem_Iio] at ht ⊢
        exact mul_neg_of_pos_of_neg hc ht
  refine ⟨μ, hμ, fun x hx w hw => ?_⟩
  have hxb : x / b ∈ g1SideHalf left := by
    rw [div_eq_inv_mul]; exact hhalf_mul (inv_pos.2 hb) hx
  have hβ : G3Z2b2.g3bpre Ψ left a x = Φ.symm x := G3Z2b2.g3bpre_eq hΦ hx
  have hβh : Φ.symm x ∈ g1SideHalf left := (G1ZZ1.mem_half_symm_iff hΦ.1 left x).2 hx
  -- the boundary preimage of the scaled path
  have hβ' : G3Z2b2.g3bpre Ψ left (scalePath b a) (x / b) = μ * Φ.symm x := by
    rw [G3Z2b2.g3bpre_eq hΦ' hxb]
    set t := μ * Φ.symm x with ht
    have htH : t ∈ g1SideHalf left := hhalf_mul hμ hβh
    have h1 := G1ZZ1.tendsto_of_reflGood hΦ' htH
    have h2 : Tendsto (Ψ left (scalePath b a)) (𝓝[H] (t : ℂ))
        (𝓝 (((b⁻¹ : ℝ) : ℂ) * (x : ℂ))) := by
      have hin : Tendsto (fun w : ℂ => ((μ : ℂ))⁻¹ * w) (𝓝[H] (t : ℂ))
          (𝓝[H] ((Φ.symm x : ℝ) : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun w hw => ?_⟩
        · have hc : Continuous fun w : ℂ => ((μ : ℂ))⁻¹ * w := continuous_const.mul continuous_id
          have := (hc.tendsto (t : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
          convert this using 2
          rw [ht]; push_cast; field_simp
        · show 0 < (((μ : ℂ))⁻¹ * w).im
          rw [← ofReal_inv, im_ofReal_mul]; exact mul_pos (inv_pos.2 hμ) hw
      have h3 := (G1ZZ1.tendsto_of_reflGood hΦ hβh).comp hin
      rw [OrderIso.apply_symm_apply] at h3
      refine (h3.const_mul (((b⁻¹ : ℝ) : ℂ))).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (hΨ w hw).symm
    have := G1ZZ1.neBot_nhdsWithin_H t
    have hu := tendsto_nhds_unique h1 h2
    have hx' : Φ' t = x / b := by
      have : ((Φ' t : ℝ) : ℂ) = ((x / b : ℝ) : ℂ) := by rw [hu]; push_cast; ring
      exact ofReal_injective this
    rw [OrderIso.symm_apply_eq]; exact hx'.symm
  -- the computation
  have hwH : w + ((μ * Φ.symm x : ℝ) : ℂ) ∈ H := by
    show 0 < (w + ((μ * Φ.symm x : ℝ) : ℂ)).im
    have hw' : 0 < w.im := hw
    simpa using hw'
  simp only [G3Z2b2.g3locM]
  rw [hβ', hΨ _ hwH, hβ]
  push_cast
  field_simp

end G1Zm
end Thm18Asm
end QuantumZipper
