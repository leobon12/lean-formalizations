import QuantumZipper.Proofs.Thm11.FrozenLocalDynkin
import QuantumZipper.Proofs.Thm11.ForwardTamed
import QuantumZipper.Proofs.Thm11.ForwardClock
import QuantumZipper.Statements.CouplingFields
import QuantumZipper.Proofs.ItoLite.Increments
import QuantumZipper.Proofs.Thm11.LyapunovAlgebra

/-!
# Theorem 1.1, MF-1 and MF-2: martingales of the frozen field

Blueprint `blueprint/THM11_BLUEPRINT.md`, §1 (issue 1, option (d)) and §6.

Fix `0 < c ≤ δ` and a horizon `T`. For `a ∈ ℍ` with `Im a ≥ δ` let `Z̃_t(a)`, `Ã_t(a)` be the
`c`-tamed forward flow and argument process driven by `W = √κ B` (`tamedZ`, `tamedA`), let
`σ_a := hittingBtwn Z̃(a) {Im ≤ δ} 0 T` (the freezing time) and

* `𝔥^δ_t(a) := Φ(Z̃_{t∧σ_a}(a), Ã_{t∧σ_a}(a))`, `Φ(z,A) = h0fwd κ z − χ A` (`frozenField`);
* `K^δ_t(a,b) := G(Z̃_{t∧σ_a∧σ_b}(a), Z̃_{t∧σ_a∧σ_b}(b))`, `G = greenH` (`frozenKernel`).

Main results:

* `frozenField_martingale` (MF-1): `𝔥^δ(a)` is a martingale, bounded (`abs_frozenField_le`)
  with continuous paths (`continuous_frozenField`).
* `frozenPair_martingale` (MF-2): `𝔥^δ_t(a) 𝔥^δ_t(b) + K^δ_t(a,b)` is a martingale for `a ≠ b`.

Method: the one-point state `(Z̃, Ã) ∈ ℂ × ℝ` solves an SDE with additive noise
`(−√κ, 0) dB` and bounded Lipschitz drift (`fzU_eq`), so the local Dynkin formula
`martingale_localDynkin_stopped` applies to `Φ` (generator identity `dynkinGen_fzPhi`, computed
along lines). The two-point state lives in `(ℂ × ℝ)²`; before `ρ = σ_a ∧ σ_b` the points stay
`|a−b| e^{−2T/c²}`-separated (`norm_sub_tamedZ_ge`), the generator of `Φ_aΦ_b + G` vanishes
(`dynkinGen_fzPair`), and after `ρ` the glue lemma IL-5 handles the frozen factor.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace FrozenMart

open FwdHolo

/-! ## A. Generalities -/

/-- A continuous path that is in the closed set `S` at time `0` and at all times `< t` is in
`S` at time `t`. -/
theorem mem_of_forall_lt_of_isClosed {X : Type*} [TopologicalSpace X] {p : ℝ≥0 → X}
    (hp : Continuous p) {S : Set X} (hS : IsClosed S) {t : ℝ≥0} (h0 : p 0 ∈ S)
    (h : ∀ s < t, p s ∈ S) : p t ∈ S := by
  rcases eq_or_ne t 0 with rfl | ht
  · exact h0
  have hne : (Iio t).Nonempty := ⟨0, pos_iff_ne_zero.2 ht⟩
  have hcl : t ∈ closure (Iio t) := by rw [closure_Iio' hne]; exact Set.mem_Iic.2 le_rfl
  have hsub : p '' Iio t ⊆ S := by rintro _ ⟨s, hs, rfl⟩; exact h s hs
  exact hS.closure_subset_iff.2 hsub (image_closure_subset_closure_image hp ⟨t, hcl, rfl⟩)

/-- The hitting time of a union is the minimum of the hitting times. -/
theorem hittingBtwn_union {Ω β : Type*} (u : ℝ≥0 → Ω → β) (s₁ s₂ : Set β) (T : ℝ≥0) (ω : Ω) :
    hittingBtwn u (s₁ ∪ s₂) 0 T ω = min (hittingBtwn u s₁ 0 T ω) (hittingBtwn u s₂ 0 T ω) := by
  classical
  have hbdd : ∀ S : Set ℝ≥0, BddBelow S := fun S => ⟨0, fun _ _ => zero_le⟩
  have hsub : ∀ S : Set β, (∃ j ∈ Icc (0 : ℝ≥0) T, u j ω ∈ S) →
      sInf (Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ S}) ≤ T := fun S ⟨j, hj, h⟩ =>
    (csInf_le (hbdd (Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ S}))
      (show j ∈ Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ S} from ⟨hj, h⟩)).trans hj.2
  simp only [hittingBtwn]
  by_cases h1 : ∃ j ∈ Icc (0 : ℝ≥0) T, u j ω ∈ s₁ <;>
    by_cases h2 : ∃ j ∈ Icc (0 : ℝ≥0) T, u j ω ∈ s₂
  · have h12 : ∃ j ∈ Icc (0 : ℝ≥0) T, u j ω ∈ s₁ ∪ s₂ :=
      let ⟨j, hj, h⟩ := h1; ⟨j, hj, Or.inl h⟩
    rw [if_pos h12, if_pos h1, if_pos h2]
    have e : Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₁ ∪ s₂} =
        (Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₁}) ∪ (Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₂}) := by
      ext i; simp only [mem_inter_iff, mem_setOf_eq, mem_union]; tauto
    rw [e, csInf_union (hbdd _)
      (show (Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₁}).Nonempty from let ⟨j, hj, h⟩ := h1; ⟨j, hj, h⟩)
      (hbdd _)
      (show (Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₂}).Nonempty from let ⟨j, hj, h⟩ := h2; ⟨j, hj, h⟩)]
  · have h12 : ∃ j ∈ Icc (0 : ℝ≥0) T, u j ω ∈ s₁ ∪ s₂ :=
      let ⟨j, hj, h⟩ := h1; ⟨j, hj, Or.inl h⟩
    rw [if_pos h12, if_pos h1, if_neg h2]
    have e : Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₁ ∪ s₂} = Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₁} := by
      ext i
      simp only [mem_inter_iff, mem_setOf_eq, mem_union]
      exact ⟨fun ⟨hi, h⟩ => ⟨hi, h.resolve_right fun h' => h2 ⟨i, hi, h'⟩⟩,
        fun ⟨hi, h⟩ => ⟨hi, Or.inl h⟩⟩
    rw [e, min_eq_left (hsub s₁ h1)]
  · have h12 : ∃ j ∈ Icc (0 : ℝ≥0) T, u j ω ∈ s₁ ∪ s₂ :=
      let ⟨j, hj, h⟩ := h2; ⟨j, hj, Or.inr h⟩
    rw [if_pos h12, if_neg h1, if_pos h2]
    have e : Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₁ ∪ s₂} = Icc (0 : ℝ≥0) T ∩ {i | u i ω ∈ s₂} := by
      ext i
      simp only [mem_inter_iff, mem_setOf_eq, mem_union]
      exact ⟨fun ⟨hi, h⟩ => ⟨hi, h.resolve_left fun h' => h1 ⟨i, hi, h'⟩⟩,
        fun ⟨hi, h⟩ => ⟨hi, Or.inr h⟩⟩
    rw [e, min_eq_right (hsub s₂ h2)]
  · have h12 : ¬ ∃ j ∈ Icc (0 : ℝ≥0) T, u j ω ∈ s₁ ∪ s₂ := fun ⟨j, hj, h⟩ =>
      h.elim (fun h => h1 ⟨j, hj, h⟩) (fun h => h2 ⟨j, hj, h⟩)
    rw [if_neg h12, if_neg h1, if_neg h2, min_self]

/-! ## B. Facts on the tamed flow -/

section Tamed

variable {W : ℝ → ℝ}

theorem continuous_tamedZ_nnreal (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) :
    Continuous fun s : ℝ≥0 => tamedZ W c a s := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hW' : Continuous fun t : ℝ≥0 => W t := hW.comp NNReal.continuous_coe
  have hg : Continuous fun t : ℝ≥0 => |W t - W s| + 2 / c * |(t : ℝ) - s| := by fun_prop
  have h0 := hg.tendsto s
  simp only [sub_self, abs_zero, mul_zero, add_zero] at h0
  exact squeeze_zero (fun t => dist_nonneg) (fun t => dist_tamedZ_time_le hW hc a s.2 t.2) h0

theorem continuous_tamedA_nnreal (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) :
    Continuous fun s : ℝ≥0 => tamedA W c a s := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hg : Continuous fun t : ℝ≥0 => 2 / c ^ 2 * |(t : ℝ) - s| := by fun_prop
  have h0 := hg.tendsto s
  simp only [sub_self, abs_zero, mul_zero] at h0
  exact squeeze_zero (fun t => dist_nonneg)
    (fun t => by rw [Real.dist_eq]; exact abs_tamedA_time_le hW hc a s.2 t.2) h0

theorem abs_tamedA_le (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    |tamedA W c a t| ≤ 2 / c ^ 2 * t := by
  have h := abs_tamedA_time_le hW hc a le_rfl ht
  have h0 : tamedA W c a 0 = 0 := intervalIntegral.integral_same
  rwa [h0, sub_zero, sub_zero, abs_of_nonneg ht] at h

theorem im_tamedZ_zero (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) :
    (tamedZ W c a 0).im = a.im := by
  rw [tamedZ_eq hW hc a le_rfl]; simp

theorem im_tamedZ_le (hW : Continuous W) {c : ℝ} (hc : 0 < c) (a : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (tamedZ W c a t).im ≤ a.im := by
  rw [tamedZ_eq hW hc a ht]
  have hint : IntervalIntegrable (fun s => 2 / proj c (tamedZ W c a s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact (continuous_tamedZField hc).comp_continuousOn (continuousOn_tamedZ hW hc ht a)
  have him : (∫ s in (0 : ℝ)..t, 2 / proj c (tamedZ W c a s)).im =
      ∫ s in (0 : ℝ)..t, (2 / proj c (tamedZ W c a s)).im :=
    (Complex.imCLM.intervalIntegral_comp_comm hint).symm
  have hle : 0 ≤ ∫ s in (0 : ℝ)..t, -(2 / proj c (tamedZ W c a s)).im := by
    refine intervalIntegral.integral_nonneg ht fun s _ => ?_
    rw [FwdClock.im_two_div, neg_nonneg]
    have := proj_im_ge_tamed c (tamedZ W c a s)
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)
  rw [intervalIntegral.integral_neg] at hle
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_zero, him]
  linarith

/-- Separation of two tamed trajectories while both stay in `{Im ≥ c}`. -/
theorem norm_sub_tamedZ_ge (hW : Continuous W) {c : ℝ} (hc : 0 < c) {a b : ℂ} {t : ℝ}
    (ht : 0 ≤ t) (ha : ∀ s ∈ Icc (0 : ℝ) t, c ≤ (tamedZ W c a s).im)
    (hb : ∀ s ∈ Icc (0 : ℝ) t, c ≤ (tamedZ W c b s).im) :
    ‖a - b‖ * Real.exp (-(2 / c ^ 2 * t)) ≤ ‖tamedZ W c a t - tamedZ W c b t‖ := by
  have hsa := isForwardSol_tamedZ hW hc ht ha
  have hsb := isForwardSol_tamedZ hW hc ht hb
  have e := FwdHolo.sol_sub_eq hsb hsa t ⟨ht, le_rfl⟩
  rw [e, norm_mul, Complex.norm_exp]
  gcongr
  have hbd : ‖∫ s in (0 : ℝ)..t, 2 / (tamedZ W c a s * tamedZ W c b s)‖ ≤ 2 / c ^ 2 * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => by
      rw [uIoc_of_le ht] at hs
      have n1 : c ≤ ‖tamedZ W c a s‖ := (ha s ⟨hs.1.le, hs.2⟩).trans (Complex.im_le_norm _)
      have n2 : c ≤ ‖tamedZ W c b s‖ := (hb s ⟨hs.1.le, hs.2⟩).trans (Complex.im_le_norm _)
      rw [norm_div, norm_mul, Complex.norm_two]
      have hp : 0 < ‖tamedZ W c a s‖ * ‖tamedZ W c b s‖ := mul_pos (hc.trans_le n1) (hc.trans_le n2)
      rw [div_le_div_iff₀ hp (pow_pos hc 2)]
      nlinarith [mul_le_mul n1 n2 hc.le (hc.le.trans n1)]
  rw [sub_zero, abs_of_nonneg ht] at hbd
  rw [Complex.neg_re]
  have := Complex.re_le_norm (∫ s in (0 : ℝ)..t, 2 / (tamedZ W c a s * tamedZ W c b s))
  linarith

end Tamed

/-! ## C. The one-point state process and its SDE -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `Z̃_t(a)` driven by `W = √κ B(·,ω)`. -/
def fzZ (κ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  tamedZ (drive κ B ω) c a t

/-- `Ã_t(a)` driven by `W = √κ B(·,ω)`. -/
def fzA (κ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  tamedA (drive κ B ω) c a t

/-- The one-point state `(Z̃_t(a), Ã_t(a)) ∈ ℂ × ℝ`. -/
def fzU (κ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) (t : ℝ≥0) (ω : Ω) : ℂ × ℝ :=
  (fzZ κ c B a t ω, fzA κ c B a t ω)

/-- The drift of the one-point state. -/
def fzDrift (c : ℝ) (x : ℂ × ℝ) : ℂ × ℝ := (tamedZField c x.1, tamedAField c x.1)

/-- The noise direction of the one-point state: `dZ̃ = … − √κ dB`. -/
def fzNoise (κ : ℝ) : ℂ × ℝ := (-(Real.sqrt κ : ℂ), 0)

/-- `Φ(z, A) = h0fwd κ z − χ A = −(2/√κ) arg z − χ A`. -/
def fzPhi (κ : ℝ) (x : ℂ × ℝ) : ℝ := h0fwd κ x.1 - chiC κ * x.2

theorem continuous_drive_path {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω))
    (ω : Ω) : Continuous (drive κ B ω) :=
  continuous_const.mul ((hBc ω).comp continuous_real_toNNReal)

theorem lipschitzWith_fzDrift {c : ℝ} (hc : 0 < c) :
    LipschitzWith (Real.toNNReal (4 / c ^ 2 + 8 / c ^ 3)) (fzDrift c) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hc3 : 0 < c ^ 3 := pow_pos hc 3
  have h4 : 0 ≤ 4 / c ^ 2 := div_nonneg (by norm_num) hc2.le
  have h8 : 0 ≤ 8 / c ^ 3 := div_nonneg (by norm_num) hc3.le
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (add_nonneg h4 h8)]
  have hxy : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd0 : 0 ≤ dist x.1 y.1 := dist_nonneg
  have h1 : dist (tamedZField c x.1) (tamedZField c y.1) ≤ 4 / c ^ 2 * dist x.1 y.1 := by
    rw [dist_eq_norm]
    refine (norm_two_div_sub_le_tamed hc (norm_proj_ge_tamed c _)
      (norm_proj_ge_tamed c _)).trans ?_
    have hp := (proj_lipschitz c).dist_le_mul x.1 y.1
    rw [dist_eq_norm, dist_eq_norm] at hp
    rw [dist_eq_norm]
    have : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
    rw [this] at hp
    rw [div_le_iff₀ hc2]
    have : 4 / c ^ 2 * ‖x.1 - y.1‖ * c ^ 2 = 4 * ‖x.1 - y.1‖ := by field_simp
    rw [this]; linarith
  have h2 : dist (tamedAField c x.1) (tamedAField c y.1) ≤ 8 / c ^ 3 * dist x.1 y.1 := by
    rw [Real.dist_eq, dist_eq_norm]; exact abs_tamedAField_sub_le hc _ _
  rw [Prod.dist_eq]
  simp only [fzDrift]
  have hdd : 0 ≤ dist x y := dist_nonneg
  refine max_le (h1.trans ?_) (h2.trans ?_)
  · nlinarith [mul_le_mul_of_nonneg_left hxy h4, mul_nonneg h8 hdd]
  · nlinarith [mul_le_mul_of_nonneg_left hxy h8, mul_nonneg h4 hdd]

theorem norm_fzDrift_le {c : ℝ} (hc : 0 < c) (x : ℂ × ℝ) : ‖fzDrift c x‖ ≤ 2 / c + 2 / c ^ 2 := by
  rw [Prod.norm_def]
  simp only [fzDrift, Real.norm_eq_abs]
  have h1 := norm_tamedZField_le hc x.1
  have h2 := abs_tamedAField_le hc x.1
  have : 0 ≤ 2 / c := div_nonneg (by norm_num) hc.le
  have : 0 ≤ 2 / c ^ 2 := div_nonneg (by norm_num) (pow_pos hc 2).le
  exact max_le (by linarith) (by linarith)

/-- **The one-point SDE.** `U_t = (a,0) + ∫₀ᵗ b(U_r) dr + B_t e` with `b = fzDrift c`,
`e = fzNoise κ`. -/
theorem fzU_eq {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) {κ c : ℝ} (hc : 0 < c)
    (a : ℂ) (ω : Ω) (t : ℝ≥0) :
    fzU κ c B a t ω = (a, 0) + (∫ r in (0 : ℝ)..t, fzDrift c (fzU κ c B a r.toNNReal ω))
      + B t ω • fzNoise κ := by
  set W := drive κ B ω with hW_def
  have hW : Continuous W := continuous_drive_path hBc ω
  have h1 : Continuous fun r : ℝ => tamedZ W c a (r.toNNReal : ℝ) :=
    (continuous_tamedZ_nnreal hW hc a).comp continuous_real_toNNReal
  have hgc : Continuous fun r : ℝ => fzDrift c (fzU κ c B a r.toNNReal ω) :=
    ((continuous_tamedZField hc).comp h1).prodMk ((continuous_tamedAField hc).comp h1)
  have hint := hgc.intervalIntegrable (μ := volume) 0 t
  have hfst : (∫ r in (0 : ℝ)..t, fzDrift c (fzU κ c B a r.toNNReal ω)).1 =
      ∫ r in (0 : ℝ)..t, 2 / proj c (tamedZ W c a r) := by
    have := ((ContinuousLinearMap.fst ℝ ℂ ℝ).intervalIntegral_comp_comm hint).symm
    simp only [ContinuousLinearMap.coe_fst'] at this
    rw [this]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [fzDrift, fzU, fzZ, tamedZField, Real.coe_toNNReal r hr.1, W]
  have hsnd : (∫ r in (0 : ℝ)..t, fzDrift c (fzU κ c B a r.toNNReal ω)).2 =
      ∫ r in (0 : ℝ)..t, tamedAField c (tamedZ W c a r) := by
    have := ((ContinuousLinearMap.snd ℝ ℂ ℝ).intervalIntegral_comp_comm hint).symm
    simp only [ContinuousLinearMap.coe_snd'] at this
    rw [this]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [fzDrift, fzU, fzZ, Real.coe_toNNReal r hr.1, W]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, fzNoise, hfst]
    show tamedZ W c a t = _
    rw [tamedZ_eq hW hc a t.coe_nonneg]
    simp only [W, drive, Real.toNNReal_coe, Complex.real_smul]
    push_cast; ring
  · simp only [Prod.snd_add, Prod.smul_snd, fzNoise, smul_zero, add_zero, zero_add, hsnd]
    rfl

/-! ## D. The one-point generator -/

theorem contDiffAt_arg_real {z : ℂ} (hz : z ∈ Complex.slitPlane) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n Complex.arg z := by
  have h : Complex.arg = fun w => Complex.imCLM (Complex.log w) := by
    funext w; rw [Complex.imCLM_apply, Complex.log_im]
  rw [h]
  exact Complex.imCLM.contDiff.contDiffAt.comp z ((Complex.contDiffAt_log hz).restrict_scalars ℝ)

theorem mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inr hz.ne')

theorem isOpen_fzO : IsOpen {x : ℂ × ℝ | 0 < x.1.im} :=
  isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)

theorem contDiffAt_fzPhi (κ : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fzPhi κ) x := by
  unfold fzPhi h0fwd
  exact (contDiffAt_const.mul ((contDiffAt_arg_real (mem_slitPlane_of_im_pos hx)).comp x
    contDiffAt_fst)).sub (contDiffAt_const.mul contDiffAt_snd)

theorem contDiffOn_fzPhi (κ : ℝ) : ContDiffOn ℝ 3 (fzPhi κ) {x : ℂ × ℝ | 0 < x.1.im} :=
  fun _ hx => (contDiffAt_fzPhi κ hx).contDiffWithinAt

theorem hasDerivAt_arg_line (z w : ℂ) (r : ℝ) (h : z + r * w ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ => Complex.arg (z + s * w)) ((w / (z + r * w)).im) r := by
  have hf : HasDerivAt (fun s : ℝ => z + (s : ℂ) * w) w r := by
    simpa using (((hasDerivAt_id r).ofReal_comp).mul_const w).const_add z
  have hl := hf.clog_real h
  have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hl
  simpa [Function.comp_def, Complex.log_im] using this

theorem fzPhi_line (κ : ℝ) (x v : ℂ × ℝ) (s : ℝ) :
    fzPhi κ (x + s • v) = -(2 / Real.sqrt κ) * Complex.arg (x.1 + s * v.1)
      - chiC κ * (x.2 + s * v.2) := by
  simp [fzPhi, h0fwd, Complex.real_smul]

theorem hasDerivAt_fzPhi_line (κ : ℝ) (x v : ℂ × ℝ) (r : ℝ)
    (h : x.1 + r * v.1 ∈ Complex.slitPlane) :
    HasDerivAt (fun s : ℝ => fzPhi κ (x + s • v))
      (-(2 / Real.sqrt κ) * (v.1 / (x.1 + r * v.1)).im - chiC κ * v.2) r := by
  have e : (fun s : ℝ => fzPhi κ (x + s • v)) = fun s : ℝ =>
      -(2 / Real.sqrt κ) * Complex.arg (x.1 + s * v.1) - chiC κ * (x.2 + s * v.2) :=
    funext (fzPhi_line κ x v)
  rw [e]
  have hl : HasDerivAt (fun s : ℝ => x.2 + s * v.2) v.2 r := by
    simpa using ((hasDerivAt_id r).mul_const v.2).const_add x.2
  exact ((hasDerivAt_arg_line x.1 v.1 r h).const_mul _).sub (hl.const_mul _)

/-- The derivative of `r ↦ Φ(x + r e)` (noise direction). -/
def nd1 (κ : ℝ) (z : ℂ) (r : ℝ) : ℝ :=
  -(2 / Real.sqrt κ) * ((fzNoise κ).1 / (z + r * (fzNoise κ).1)).im - chiC κ * (fzNoise κ).2

theorem im_add_noise (κ : ℝ) (z : ℂ) (r : ℝ) : (z + r * (fzNoise κ).1).im = z.im := by
  simp [fzNoise]

theorem deriv_fzPhi_noise (κ : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) :
    deriv (fun r : ℝ => fzPhi κ (x + r • fzNoise κ)) = nd1 κ x.1 :=
  funext fun r => (hasDerivAt_fzPhi_line κ x (fzNoise κ) r
    (mem_slitPlane_of_im_pos (by rw [im_add_noise]; exact hx))).deriv

theorem hasDerivAt_nd1 {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (nd1 κ z) (Real.sqrt κ * (2 / z ^ 2).im) 0 := by
  have hne : ∀ r : ℝ, z + r * (fzNoise κ).1 ≠ 0 := fun r h => by
    have := congrArg Complex.im h
    rw [im_add_noise, Complex.zero_im] at this; linarith
  have hd : HasDerivAt (fun r : ℝ => z + (r : ℂ) * (fzNoise κ).1) (fzNoise κ).1 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (fzNoise κ).1).const_add z
  have hq := (hasDerivAt_const (0 : ℝ) (fzNoise κ).1).div hd (hne 0)
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  have h := (him.const_mul (-(2 / Real.sqrt κ))).sub_const (chiC κ * (fzNoise κ).2)
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  refine HasDerivAt.congr_deriv (f := nd1 κ z) h ?_
  simp only [Complex.imCLM_apply, fzNoise, Complex.ofReal_zero, zero_mul,
    add_zero, zero_sub]
  have e1 : -(-(Real.sqrt κ : ℂ) * -(Real.sqrt κ : ℂ)) / z ^ 2
      = ((-(Real.sqrt κ * Real.sqrt κ) : ℝ) : ℂ) * (z ^ 2)⁻¹ := by push_cast; ring
  have e2 : (2 : ℂ) / z ^ 2 = ((2 : ℝ) : ℂ) * (z ^ 2)⁻¹ := by push_cast; ring
  rw [e1, e2, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  field_simp

/-- The drift derivative of `Φ` at `x` (where the taming is inactive). -/
def driftPhi (κ : ℝ) (z : ℂ) : ℝ :=
  -(2 / Real.sqrt κ) * (2 / z ^ 2).im - chiC κ * (-2 / z ^ 2).im

theorem fzDrift_of_le {c : ℝ} {x : ℂ × ℝ} (hx : c ≤ x.1.im) :
    fzDrift c x = (2 / x.1, (-2 / x.1 ^ 2).im) := by
  simp [fzDrift, tamedZField, tamedAField, proj_of_le hx]

theorem hasDerivAt_fzPhi_drift (κ : ℝ) {c : ℝ} (hc : 0 < c) {x : ℂ × ℝ} (hx : c ≤ x.1.im) :
    HasDerivAt (fun s : ℝ => fzPhi κ (x + s • fzDrift c x)) (driftPhi κ x.1) 0 := by
  have hz : 0 < x.1.im := hc.trans_le hx
  have h := hasDerivAt_fzPhi_line κ x (fzDrift c x) 0
    (by simpa using mem_slitPlane_of_im_pos hz)
  convert h using 1
  rw [fzDrift_of_le hx]
  simp only [driftPhi, Complex.ofReal_zero, zero_mul, add_zero]
  congr 3
  ring

theorem onePoint_alg {κ : ℝ} (hκ : 0 < κ) (z : ℂ) :
    driftPhi κ z + 1 / 2 * (Real.sqrt κ * (2 / z ^ 2).im) = 0 := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  unfold driftPhi chiC
  rw [neg_div, Complex.neg_im]
  field_simp
  ring

/-- **One-point generator identity** `LΦ = 0` where the taming is inactive. -/
theorem dynkinGen_fzPhi {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) {x : ℂ × ℝ}
    (hx : c ≤ x.1.im) : dynkinGen (fzDrift c) (fzNoise κ) (fzPhi κ) x = 0 := by
  have hz : 0 < x.1.im := hc.trans_le hx
  have hcd : ContDiffAt ℝ 2 (fzPhi κ) x := contDiffAt_fzPhi κ hz
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hcd.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line hcd, (hasDerivAt_fzPhi_drift κ hc hx).deriv,
    deriv_fzPhi_noise κ hz, (hasDerivAt_nd1 hκ hz).deriv]
  exact onePoint_alg hκ x.1

/-! ## E. MF-1: the frozen one-point field -/

variable {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The freezing time `σ_a = inf{t ≤ T : Im Z̃_t(a) ≤ δ}` (equal to `T` if there is no such
time). -/
def frozenTime (κ c δ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) : Ω → ℝ≥0 :=
  hittingBtwn (fzZ κ c B a) {z : ℂ | z.im ≤ δ} 0 T

/-- The frozen one-point field `𝔥^δ_t(a) = Φ(Z̃_{t∧σ_a}(a), Ã_{t∧σ_a}(a))`. -/
def frozenField (κ c δ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  fzPhi κ (fzU κ c B a (min t (frozenTime κ c δ T B a ω)) ω)

/-- The region visited by the one-point state up to the freezing time. -/
def fzK (δ c : ℝ) (T : ℝ≥0) : Set (ℂ × ℝ) := {x | δ ≤ x.1.im ∧ |x.2| ≤ 2 / c ^ 2 * T}

/-- The bound of `Φ` on `fzK`. -/
def fzBound (κ c : ℝ) (T : ℝ≥0) : ℝ := 2 / Real.sqrt κ * Real.pi + |chiC κ| * (2 / c ^ 2 * T)

theorem hittingBtwn_fzU (κ c δ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (a : ℂ) :
    hittingBtwn (fzU κ c B a) {x : ℂ × ℝ | x.1.im ≤ δ} 0 T = frozenTime κ c δ T B a := rfl

theorem continuous_fzZ (hBc : ∀ ω, Continuous (B · ω)) {κ c : ℝ} (hc : 0 < c) (a : ℂ) (ω : Ω) :
    Continuous fun t => fzZ κ c B a t ω :=
  continuous_tamedZ_nnreal (continuous_drive_path hBc ω) hc a

theorem continuous_fzU (hBc : ∀ ω, Continuous (B · ω)) {κ c : ℝ} (hc : 0 < c) (a : ℂ) (ω : Ω) :
    Continuous fun t => fzU κ c B a t ω :=
  (continuous_fzZ hBc hc a ω).prodMk (continuous_tamedA_nnreal (continuous_drive_path hBc ω) hc a)

theorem isClosed_fzK (δ c : ℝ) (T : ℝ≥0) : IsClosed (fzK δ c T) :=
  (isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)).inter
    (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)

theorem isClosed_fzCl (δ : ℝ) : IsClosed {x : ℂ × ℝ | x.1.im ≤ δ} :=
  isClosed_le (Complex.continuous_im.comp continuous_fst) continuous_const

theorem fzU_mem_fzK (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) {a : ℂ}
    (hδa : δ ≤ a.im) {T : ℝ≥0} (ω : Ω) {t : ℝ≥0} (htT : t ≤ T)
    (h : ∀ s < t, fzU κ c B a s ω ∉ {x : ℂ × ℝ | x.1.im ≤ δ}) : fzU κ c B a t ω ∈ fzK δ c T := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  refine ⟨?_, ?_⟩
  · have h0 : fzZ κ c B a 0 ω ∈ {z : ℂ | δ ≤ z.im} := by
      show δ ≤ (tamedZ (drive κ B ω) c a ((0 : ℝ≥0) : ℝ)).im
      rw [NNReal.coe_zero, im_tamedZ_zero hW hc]; exact hδa
    exact mem_of_forall_lt_of_isClosed (p := fun s => fzZ κ c B a s ω)
      (continuous_fzZ hBc hc a ω) (isClosed_le continuous_const Complex.continuous_im) h0
      (fun s hs => by
        have := h s hs
        simp only [mem_setOf_eq, not_le] at this
        exact this.le)
  · show |tamedA (drive κ B ω) c a t| ≤ _
    exact (abs_tamedA_le hW hc a t.coe_nonneg).trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast htT) (div_nonneg (by norm_num) (pow_pos hc 2).le))

theorem abs_fzPhi_le_of_mem {κ c δ : ℝ} {T : ℝ≥0} {x : ℂ × ℝ} (hx : x ∈ fzK δ c T) :
    |fzPhi κ x| ≤ fzBound κ c T := by
  unfold fzPhi h0fwd fzBound
  have h1 : |Complex.arg x.1| ≤ Real.pi := Complex.abs_arg_le_pi _
  have hs : 0 ≤ 2 / Real.sqrt κ := div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc |-(2 / Real.sqrt κ) * Complex.arg x.1 - chiC κ * x.2|
      ≤ |-(2 / Real.sqrt κ) * Complex.arg x.1| + |chiC κ * x.2| := abs_sub _ _
    _ = 2 / Real.sqrt κ * |Complex.arg x.1| + |chiC κ| * |x.2| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hs]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left h1 hs)
        (mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _))

theorem fzU_frozen_mem (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) {a : ℂ}
    (hδa : δ ≤ a.im) {T : ℝ≥0} (t : ℝ≥0) (ω : Ω) :
    fzU κ c B a (min t (frozenTime κ c δ T B a ω)) ω ∈ fzK δ c T :=
  fzU_mem_fzK hBc hc hδa ω ((min_le_right _ _).trans (hittingBtwn_le ω))
    fun s hs => notMem_of_lt_hittingBtwn (hs.trans_le (min_le_right _ _)) zero_le

theorem abs_frozenField_le (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) {a : ℂ}
    (hδa : δ ≤ a.im) (T : ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    |frozenField κ c δ T B a t ω| ≤ fzBound κ c T :=
  abs_fzPhi_le_of_mem (fzU_frozen_mem hBc hc hδa t ω)

theorem continuous_frozenField (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c)
    (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) (ω : Ω) :
    Continuous fun t => frozenField κ c δ T B a t ω := by
  have hg : Continuous fun t => fzU κ c B a (min t (frozenTime κ c δ T B a ω)) ω :=
    (continuous_fzU hBc hc a ω).comp (continuous_id.min continuous_const)
  rw [continuous_iff_continuousAt]
  intro t
  have hpos : 0 < (fzU κ c B a (min t (frozenTime κ c δ T B a ω)) ω).1.im :=
    (hc.trans_le hcδ).trans_le (fzU_frozen_mem hBc hc hδa t ω).1
  exact ContinuousAt.comp (g := fzPhi κ) (contDiffAt_fzPhi κ hpos (n := 0)).continuousAt
    hg.continuousAt

/-- **MF-1.** The frozen one-point field `𝔥^δ(a)` is a martingale (for any filtration to which
`B` is adapted and which is contained in the past of `B`, e.g. `bmFiltration B`). It is bounded
by `fzBound κ c T` (`abs_frozenField_le`) and has continuous paths (`continuous_frozenField`). -/
theorem frozenField_martingale (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) :
    Martingale (frozenField κ c δ T B a) 𝓕 P := by
  have hKO : fzK δ c T ⊆ {x : ℂ × ℝ | 0 < x.1.im} := fun x hx =>
    (hc.trans_le hcδ).trans_le hx.1
  exact martingale_localDynkin_stopped hB hBc 𝓕 hBad hpast (lipschitzWith_fzDrift hc)
    (norm_fzDrift_le hc) (fzU_eq hBc hc a) isOpen_fzO (isClosed_fzCl δ) (isClosed_fzK δ c T) hKO
    (contDiffOn_fzPhi κ) (fun x hx _ => dynkinGen_fzPhi hκ hc (hcδ.trans hx.1)) T
    (fun ω t htT h => fzU_mem_fzK hBc hc hδa ω htT h) (fun x hx => abs_fzPhi_le_of_mem hx)

/-! ## F. The two-point generator -/

/-- The two-point state space `(ℂ × ℝ)²`. -/
abbrev E2 := (ℂ × ℝ) × (ℂ × ℝ)

/-- Two-point drift. -/
def fzDrift2 (c : ℝ) (x : E2) : E2 := (fzDrift c x.1, fzDrift c x.2)

/-- Two-point noise direction (common noise). -/
def fzNoise2 (κ : ℝ) : E2 := (fzNoise κ, fzNoise κ)

/-- `F₂ = Φ_a Φ_b + G(z_a, z_b)`. -/
def fzF2 (κ : ℝ) (x : E2) : ℝ := fzPhi κ x.1 * fzPhi κ x.2 + greenH x.1.1 x.2.1

/-- The open set where `F₂` is smooth. -/
def fzO2 : Set E2 := {x | 0 < x.1.1.im ∧ 0 < x.2.1.im ∧ x.1.1 ≠ x.2.1}

theorem isOpen_fzO2 : IsOpen fzO2 :=
  (isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_fst.comp continuous_fst))).inter
    ((isOpen_lt continuous_const
      (Complex.continuous_im.comp (continuous_fst.comp continuous_snd))).inter
      (isOpen_ne_fun (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd)))

theorem lipschitzWith_fzDrift2 {c : ℝ} (hc : 0 < c) :
    LipschitzWith (max (Real.toNNReal (4 / c ^ 2 + 8 / c ^ 3) * 1)
      (Real.toNNReal (4 / c ^ 2 + 8 / c ^ 3) * 1)) (fzDrift2 c) :=
  ((lipschitzWith_fzDrift hc).comp LipschitzWith.prod_fst).prodMk
    ((lipschitzWith_fzDrift hc).comp LipschitzWith.prod_snd)

theorem norm_fzDrift2_le {c : ℝ} (hc : 0 < c) (x : E2) : ‖fzDrift2 c x‖ ≤ 2 / c + 2 / c ^ 2 := by
  rw [Prod.norm_def]
  exact max_le (norm_fzDrift_le hc _) (norm_fzDrift_le hc _)

theorem ne_zero_sub_conj {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) : x - conj y ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this; linarith

theorem contDiffAt_greenH2 {x : E2} (hx : x ∈ fzO2) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun y : E2 => greenH y.1.1 y.2.1) x := by
  obtain ⟨ha, hb, hne⟩ := hx
  have hp1 : ContDiff ℝ n (fun y : E2 => y.1.1 - conj y.2.1) := by
    have e : (fun y : E2 => y.1.1 - conj y.2.1) =
        fun y : E2 => y.1.1 - Complex.conjCLE y.2.1 := by funext y; simp
    rw [e]
    exact (contDiff_fst.comp contDiff_fst).sub
      (Complex.conjCLE.contDiff.comp (contDiff_fst.comp contDiff_snd))
  have hp2 : ContDiff ℝ n (fun y : E2 => y.1.1 - y.2.1) :=
    (contDiff_fst.comp contDiff_fst).sub (contDiff_fst.comp contDiff_snd)
  have h1 : x.1.1 - conj x.2.1 ≠ 0 := ne_zero_sub_conj ha hb
  have h2 : x.1.1 - x.2.1 ≠ 0 := sub_ne_zero.2 hne
  unfold greenH
  exact ((hp1.contDiffAt.norm ℝ h1).log (norm_ne_zero_iff.2 h1)).sub
    ((hp2.contDiffAt.norm ℝ h2).log (norm_ne_zero_iff.2 h2))

theorem contDiffAt_fzF2 (κ : ℝ) {x : E2} (hx : x ∈ fzO2) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fzF2 κ) x := by
  unfold fzF2
  exact (((contDiffAt_fzPhi κ hx.1).comp x contDiffAt_fst).mul
    ((contDiffAt_fzPhi κ hx.2.1).comp x contDiffAt_snd)).add (contDiffAt_greenH2 hx)

theorem contDiffOn_fzF2 (κ : ℝ) : ContDiffOn ℝ 3 (fzF2 κ) fzO2 :=
  fun _ hx => (contDiffAt_fzF2 κ hx).contDiffWithinAt

theorem hasDerivAt_greenH_line (z1 z2 v1 v2 : ℂ) (h1 : z1 - conj z2 ≠ 0) (h2 : z1 - z2 ≠ 0) :
    HasDerivAt (fun s : ℝ => greenH (z1 + s * v1) (z2 + s * v2))
      (((v1 - conj v2) / (z1 - conj z2)).re - ((v1 - v2) / (z1 - z2)).re) 0 := by
  have hp : HasDerivAt (fun s : ℝ => z1 + s * v1 - conj (z2 + s * v2)) (v1 - conj v2) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (v1 - conj v2)).const_add
      (z1 - conj z2)
    have e : (fun s : ℝ => z1 + s * v1 - conj (z2 + s * v2)) =
        fun s : ℝ => (z1 - conj z2) + ((id s : ℝ) : ℂ) * (v1 - conj v2) := by
      funext s; simp only [map_add, map_mul, Complex.conj_ofReal, id]; ring
    rw [e]; exact this.congr_deriv (by simp)
  have hq : HasDerivAt (fun s : ℝ => z1 + s * v1 - (z2 + s * v2)) (v1 - v2) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (v1 - v2)).const_add (z1 - z2)
    have e : (fun s : ℝ => z1 + s * v1 - (z2 + s * v2)) =
        fun s : ℝ => (z1 - z2) + ((id s : ℝ) : ℂ) * (v1 - v2) := by
      funext s; simp only [id]; ring
    rw [e]; exact this.congr_deriv (by simp)
  have h3 := FwdClock.hasDerivWithinAt_log_norm (hp.hasDerivWithinAt (s := univ))
    (by simpa using h1)
  have h4 := FwdClock.hasDerivWithinAt_log_norm (hq.hasDerivWithinAt (s := univ))
    (by simpa using h2)
  have h5 := h3.sub h4
  rw [hasDerivWithinAt_univ] at h5
  refine h5.congr_deriv ?_
  simp

theorem greenH_noise (κ : ℝ) (z1 z2 : ℂ) (r : ℝ) :
    greenH (z1 + r * (fzNoise κ).1) (z2 + r * (fzNoise κ).1) = greenH z1 z2 := by
  have e : ∀ z : ℂ, z + r * (fzNoise κ).1 = z - ((r * Real.sqrt κ : ℝ) : ℂ) := fun z => by
    simp only [fzNoise]; push_cast; ring
  rw [e, e, FwdClock.greenH_sub_ofReal]

theorem fzF2_noise_line (κ : ℝ) (x : E2) (r : ℝ) :
    fzF2 κ (x + r • fzNoise2 κ) =
      fzPhi κ (x.1 + r • fzNoise κ) * fzPhi κ (x.2 + r • fzNoise κ) + greenH x.1.1 x.2.1 := by
  simp only [fzF2, fzNoise2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Complex.real_smul]
  rw [greenH_noise]

theorem fzF2_drift_line (κ c : ℝ) (x : E2) (s : ℝ) :
    fzF2 κ (x + s • fzDrift2 c x) =
      fzPhi κ (x.1 + s • fzDrift c x.1) * fzPhi κ (x.2 + s • fzDrift c x.2)
        + greenH (x.1.1 + s * (fzDrift c x.1).1) (x.2.1 + s * (fzDrift c x.2).1) := by
  simp only [fzF2, fzDrift2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Complex.real_smul]

theorem hasDerivAt_fzPhi_noise (κ : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) (r : ℝ) :
    HasDerivAt (fun s : ℝ => fzPhi κ (x + s • fzNoise κ)) (nd1 κ x.1 r) r :=
  hasDerivAt_fzPhi_line κ x (fzNoise κ) r
    (mem_slitPlane_of_im_pos (by rw [im_add_noise]; exact hx))

theorem nd1_zero {κ : ℝ} (hκ : 0 < κ) (z : ℂ) : nd1 κ z 0 = (2 / z).im := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  simp only [nd1, fzNoise, Complex.ofReal_zero, zero_mul, add_zero, mul_zero, sub_zero]
  have e1 : -(Real.sqrt κ : ℂ) / z = ((-Real.sqrt κ : ℝ) : ℂ) * z⁻¹ := by push_cast; ring
  have e2 : (2 : ℂ) / z = ((2 : ℝ) : ℂ) * z⁻¹ := by push_cast; ring
  rw [e1, e2, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
  field_simp

/-- **Two-point generator identity** `L[Φ_aΦ_b + G] = 0` where the taming is inactive. -/
theorem dynkinGen_fzF2 {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) {x : E2}
    (ha : c ≤ x.1.1.im) (hb : c ≤ x.2.1.im) (hne : x.1.1 ≠ x.2.1) :
    dynkinGen (fzDrift2 c) (fzNoise2 κ) (fzF2 κ) x = 0 := by
  have ha0 : 0 < x.1.1.im := hc.trans_le ha
  have hb0 : 0 < x.2.1.im := hc.trans_le hb
  have hO : x ∈ fzO2 := ⟨ha0, hb0, hne⟩
  have hcd : ContDiffAt ℝ 2 (fzF2 κ) x := contDiffAt_fzF2 κ hO
  -- drift part
  have hdrift : HasDerivAt (fun s : ℝ => fzF2 κ (x + s • fzDrift2 c x))
      (driftPhi κ x.1.1 * fzPhi κ x.2 + fzPhi κ x.1 * driftPhi κ x.2.1
        - (2 / x.1.1).im * (2 / x.2.1).im) 0 := by
    rw [funext (fzF2_drift_line κ c x)]
    have hg := hasDerivAt_greenH_line x.1.1 x.2.1 (fzDrift c x.1).1 (fzDrift c x.2).1
      (ne_zero_sub_conj ha0 hb0) (sub_ne_zero.2 hne)
    have h := ((hasDerivAt_fzPhi_drift κ hc ha).mul (hasDerivAt_fzPhi_drift κ hc hb)).add hg
    refine h.congr_deriv ?_
    rw [fzDrift_of_le ha, fzDrift_of_le hb]
    simp only [zero_smul, add_zero]
    rw [FwdClock.kernel_alg ha0 hb0 hne]
    ring
  -- noise part
  have hnoise_fun : deriv (fun r : ℝ => fzF2 κ (x + r • fzNoise2 κ)) = fun r =>
      nd1 κ x.1.1 r * fzPhi κ (x.2 + r • fzNoise κ)
        + fzPhi κ (x.1 + r • fzNoise κ) * nd1 κ x.2.1 r := by
    funext r
    rw [funext (fzF2_noise_line κ x)]
    exact (((hasDerivAt_fzPhi_noise κ ha0 r).mul (hasDerivAt_fzPhi_noise κ hb0 r)).add_const
      _).deriv
  have hnoise : HasDerivAt (fun r : ℝ => nd1 κ x.1.1 r * fzPhi κ (x.2 + r • fzNoise κ)
        + fzPhi κ (x.1 + r • fzNoise κ) * nd1 κ x.2.1 r)
      (Real.sqrt κ * (2 / x.1.1 ^ 2).im * fzPhi κ x.2
        + 2 * ((2 / x.1.1).im * (2 / x.2.1).im)
        + fzPhi κ x.1 * (Real.sqrt κ * (2 / x.2.1 ^ 2).im)) 0 := by
    have h := ((hasDerivAt_nd1 hκ ha0).mul (hasDerivAt_fzPhi_noise κ hb0 0)).add
      ((hasDerivAt_fzPhi_noise κ ha0 0).mul (hasDerivAt_nd1 hκ hb0))
    refine h.congr_deriv ?_
    simp only [zero_smul, add_zero, nd1_zero hκ]
    ring
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hcd.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line hcd, hdrift.deriv, hnoise_fun, hnoise.deriv]
  linear_combination fzPhi κ x.2 * onePoint_alg hκ x.1.1 + fzPhi κ x.1 * onePoint_alg hκ x.2.1

/-! ## G. MF-2: the two-point martingale -/

/-- The two-point state `(U_t(a), U_t(b))`. -/
def fzU2 (κ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (a b : ℂ) (t : ℝ≥0) (ω : Ω) : E2 :=
  (fzU κ c B a t ω, fzU κ c B b t ω)

/-- The frozen kernel `K^δ_t(a,b) = G(Z̃_{t∧σ_a∧σ_b}(a), Z̃_{t∧σ_a∧σ_b}(b))`. -/
def frozenKernel (κ c δ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (a b : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  greenH (fzZ κ c B a (min t (min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω))) ω)
    (fzZ κ c B b (min t (min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω))) ω)

/-- `N_t(a,b) = 𝔥^δ_t(a) 𝔥^δ_t(b) + K^δ_t(a,b)`. -/
def frozenPair (κ c δ : ℝ) (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ) (a b : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  frozenField κ c δ T B a t ω * frozenField κ c δ T B b t ω + frozenKernel κ c δ T B a b t ω

/-- The separation constant `|a − b| e^{−2T/c²}`. -/
def fzSep (c : ℝ) (T : ℝ≥0) (a b : ℂ) : ℝ := ‖a - b‖ * Real.exp (-(2 / c ^ 2 * T))

/-- The region visited by the two-point state before `σ_a ∧ σ_b`. -/
def fzK2 (δ c : ℝ) (T : ℝ≥0) (b : ℂ) (d0 : ℝ) : Set E2 :=
  {x | x.1 ∈ fzK δ c T ∧ x.2 ∈ fzK δ c T ∧ d0 ≤ ‖x.1.1 - x.2.1‖ ∧ x.2.1.im ≤ b.im}

/-- The freezing set of the two-point state. -/
def fzCl2 (δ : ℝ) : Set E2 := {x | x.1.1.im ≤ δ} ∪ {x | x.2.1.im ≤ δ}

theorem continuous_fzDrift_path (hBc : ∀ ω, Continuous (B · ω)) {κ c : ℝ} (hc : 0 < c)
    (a : ℂ) (ω : Ω) : Continuous fun r : ℝ => fzDrift c (fzU κ c B a r.toNNReal ω) := by
  have h1 : Continuous fun r : ℝ => tamedZ (drive κ B ω) c a (r.toNNReal : ℝ) :=
    (continuous_tamedZ_nnreal (continuous_drive_path hBc ω) hc a).comp continuous_real_toNNReal
  exact ((continuous_tamedZField hc).comp h1).prodMk ((continuous_tamedAField hc).comp h1)

/-- **The two-point SDE.** -/
theorem fzU2_eq (hBc : ∀ ω, Continuous (B · ω)) {κ c : ℝ} (hc : 0 < c) (a b : ℂ) (ω : Ω)
    (t : ℝ≥0) :
    fzU2 κ c B a b t ω = ((a, 0), (b, 0))
      + (∫ r in (0 : ℝ)..t, fzDrift2 c (fzU2 κ c B a b r.toNNReal ω)) + B t ω • fzNoise2 κ := by
  have hint : IntervalIntegrable (fun r : ℝ => fzDrift2 c (fzU2 κ c B a b r.toNNReal ω))
      volume 0 t :=
    ((continuous_fzDrift_path hBc hc a ω).prodMk
      (continuous_fzDrift_path hBc hc b ω)).intervalIntegrable 0 t
  have h1 := ((ContinuousLinearMap.fst ℝ (ℂ × ℝ) (ℂ × ℝ)).intervalIntegral_comp_comm hint).symm
  have h2 := ((ContinuousLinearMap.snd ℝ (ℂ × ℝ) (ℂ × ℝ)).intervalIntegral_comp_comm hint).symm
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', fzDrift2, fzU2]
    at h1 h2
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, fzNoise2, fzDrift2, fzU2, h1]
    exact fzU_eq hBc hc a ω t
  · simp only [Prod.snd_add, Prod.smul_snd, fzNoise2, fzDrift2, fzU2, h2]
    exact fzU_eq hBc hc b ω t

theorem isClosed_fzCl2 (δ : ℝ) : IsClosed (fzCl2 δ) :=
  (isClosed_le (Complex.continuous_im.comp (continuous_fst.comp continuous_fst))
    continuous_const).union
    (isClosed_le (Complex.continuous_im.comp (continuous_fst.comp continuous_snd))
      continuous_const)

theorem isClosed_fzK2 (δ c : ℝ) (T : ℝ≥0) (b : ℂ) (d0 : ℝ) : IsClosed (fzK2 δ c T b d0) :=
  ((isClosed_fzK δ c T).preimage continuous_fst).inter
    (((isClosed_fzK δ c T).preimage continuous_snd).inter
      ((isClosed_le continuous_const (continuous_norm.comp
        ((continuous_fst.comp continuous_fst).sub (continuous_fst.comp continuous_snd)))).inter
        (isClosed_le (Complex.continuous_im.comp (continuous_fst.comp continuous_snd))
          continuous_const)))

theorem fzU2_mem_fzK2 (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hc : 0 < c) (hcδ : c ≤ δ)
    {a b : ℂ} (hδa : δ ≤ a.im) (hδb : δ ≤ b.im) {T : ℝ≥0} (ω : Ω) {t : ℝ≥0} (htT : t ≤ T)
    (h : ∀ s < t, fzU2 κ c B a b s ω ∉ fzCl2 δ) :
    fzU2 κ c B a b t ω ∈ fzK2 δ c T b (fzSep c T a b) := by
  have hW := continuous_drive_path (κ := κ) hBc ω
  have ha' : ∀ s < t, fzU κ c B a s ω ∉ {x : ℂ × ℝ | x.1.im ≤ δ} := fun s hs h' =>
    h s hs (Or.inl h')
  have hb' : ∀ s < t, fzU κ c B b s ω ∉ {x : ℂ × ℝ | x.1.im ≤ δ} := fun s hs h' =>
    h s hs (Or.inr h')
  have hI : ∀ (a' : ℂ), δ ≤ a'.im → (∀ s < t, fzU κ c B a' s ω ∉ {x : ℂ × ℝ | x.1.im ≤ δ}) →
      ∀ s ∈ Icc (0 : ℝ) t, c ≤ (tamedZ (drive κ B ω) c a' s).im := by
    intro a' hδa' hh s hs
    have hsT : s.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2
    have hmem := (fzU_mem_fzK hBc hc hδa' ω (hsT.trans htT)
      (fun q hq => hh q (hq.trans_le hsT))).1
    have e : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1
    have : δ ≤ (tamedZ (drive κ B ω) c a' s).im := by
      have h' : δ ≤ (tamedZ (drive κ B ω) c a' (s.toNNReal : ℝ)).im := hmem
      rwa [e] at h'
    linarith
  refine ⟨fzU_mem_fzK hBc hc hδa ω htT ha', fzU_mem_fzK hBc hc hδb ω htT hb', ?_, ?_⟩
  · have hsep := norm_sub_tamedZ_ge hW hc t.coe_nonneg (hI a hδa ha') (hI b hδb hb')
    refine le_trans ?_ hsep
    unfold fzSep
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have : 2 / c ^ 2 * (t : ℝ) ≤ 2 / c ^ 2 * T :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast htT) (div_nonneg (by norm_num) (pow_pos hc 2).le)
    linarith
  · exact im_tamedZ_le hW hc b t.coe_nonneg

theorem abs_greenH_le {z1 z2 : ℂ} (h1 : 0 < z1.im) (h2 : 0 < z2.im) {d0 Y : ℝ} (hd0 : 0 < d0)
    (hd : d0 ≤ ‖z1 - z2‖) (hY : z2.im ≤ Y) : |greenH z1 z2| ≤ 2 * Y / d0 := by
  have hD : 0 < ‖z1 - z2‖ := hd0.trans_le hd
  have hne : z1 ≠ z2 := fun h => by rw [h, sub_self, norm_zero] at hD; exact lt_irrefl _ hD
  have hG0 : 0 ≤ greenH z1 z2 := greenH_nonneg (show 0 ≤ z1.im from h1.le)
    (show 0 ≤ z2.im from h2.le) hne
  have hA0 : 0 < ‖z1 - conj z2‖ := norm_pos_iff.2 (ne_zero_sub_conj h1 h2)
  have hA : ‖z1 - conj z2‖ ≤ ‖z1 - z2‖ + 2 * z2.im := by
    calc ‖z1 - conj z2‖ = ‖(z1 - z2) + (z2 - conj z2)‖ := by ring_nf
      _ ≤ ‖z1 - z2‖ + ‖z2 - conj z2‖ := norm_add_le _ _
      _ = ‖z1 - z2‖ + 2 * z2.im := by
          rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [abs_of_nonneg hG0]
  unfold greenH
  rw [← Real.log_div hA0.ne' hD.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hA0 hD)).trans ?_
  rw [div_sub_one hD.ne']
  calc (‖z1 - conj z2‖ - ‖z1 - z2‖) / ‖z1 - z2‖ ≤ 2 * z2.im / ‖z1 - z2‖ :=
        div_le_div_of_nonneg_right (by linarith) hD.le
    _ ≤ 2 * Y / d0 := div_le_div₀ (by linarith) (by linarith) hd0 hd

theorem abs_fzF2_le {κ c δ : ℝ} (hδ : 0 < δ) {T : ℝ≥0} {b : ℂ} {d0 : ℝ} (hd0 : 0 < d0)
    {x : E2} (hx : x ∈ fzK2 δ c T b d0) :
    |fzF2 κ x| ≤ fzBound κ c T * fzBound κ c T + 2 * b.im / d0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have ha := abs_fzPhi_le_of_mem (κ := κ) h1
  have hb := abs_fzPhi_le_of_mem (κ := κ) h2
  have hG := abs_greenH_le (hδ.trans_le h1.1) (hδ.trans_le h2.1) hd0 h3 h4
  unfold fzF2
  calc |fzPhi κ x.1 * fzPhi κ x.2 + greenH x.1.1 x.2.1|
      ≤ |fzPhi κ x.1 * fzPhi κ x.2| + |greenH x.1.1 x.2.1| := abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)) hG

/-- Pointwise algebra of the decomposition `N_t = N_{t∧ρ} + ξ_a(𝔥_t(b) − 𝔥_{t∧ρ}(b))
+ ξ_b(𝔥_t(a) − 𝔥_{t∧ρ}(a))`, `ρ = σ_a ∧ σ_b`. -/
theorem pair_decomp_alg (φa φb : ℝ≥0 → ℝ) (K ξa ξb : ℝ) (sa sb t : ℝ≥0)
    (h1 : sa ≤ sb → ξa = φa (min (min sa sb) sa) ∧ ξb = 0)
    (h2 : ¬ sa ≤ sb → ξa = 0 ∧ ξb = φb (min (min sa sb) sb)) :
    φa (min t sa) * φb (min t sb) + K =
      φa (min t (min sa sb)) * φb (min t (min sa sb)) + K
        + ξa * (φb (min t sb) - φb (min (min t (min sa sb)) sb))
        + ξb * (φa (min t sa) - φa (min (min t (min sa sb)) sa)) := by
  by_cases h : sa ≤ sb
  · obtain ⟨ha, hb⟩ := h1 h
    have e1 : min sa sb = sa := min_eq_left h
    have e2 : min (min t sa) sb = min t sa := min_eq_left ((min_le_right t sa).trans h)
    have e3 : min (min t sa) sa = min t sa := min_eq_left (min_le_right t sa)
    rw [ha, hb, e1, min_self, e2, e3]
    rcases le_total t sa with ht | ht
    · have e4 : min t sb = t := min_eq_left (ht.trans h)
      rw [min_eq_left ht, e4]; ring
    · rw [min_eq_right ht]; ring
  · obtain ⟨ha, hb⟩ := h2 h
    have h' : sb ≤ sa := (not_le.mp h).le
    have e1 : min sa sb = sb := min_eq_right h'
    have e2 : min (min t sb) sa = min t sb := min_eq_left ((min_le_right t sb).trans h')
    have e3 : min (min t sb) sb = min t sb := min_eq_left (min_le_right t sb)
    rw [ha, hb, e1, min_self, e2, e3]
    rcases le_total t sb with ht | ht
    · have e4 : min t sa = t := min_eq_left (ht.trans h')
      rw [min_eq_left ht, e4]; ring
    · rw [min_eq_right ht]; ring

/-- **MF-2.** For `a ≠ b` with `Im a, Im b ≥ δ`, the process
`N_t(a,b) = 𝔥^δ_t(a) 𝔥^δ_t(b) + K^δ_t(a,b)` is a martingale. -/
theorem frozenPair_martingale (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {κ c δ : ℝ} (hκ : 0 < κ) (hc : 0 < c) (hcδ : c ≤ δ) {a b : ℂ} (hδa : δ ≤ a.im)
    (hδb : δ ≤ b.im) (hab : a ≠ b) (T : ℝ≥0) :
    Martingale (frozenPair κ c δ T B a b) 𝓕 P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hδ : 0 < δ := hc.trans_le hcδ
  have hd0 : 0 < fzSep c T a b :=
    mul_pos (norm_pos_iff.2 (sub_ne_zero.2 hab)) (Real.exp_pos _)
  have hne_of : ∀ x ∈ fzK2 δ c T b (fzSep c T a b), x.1.1 ≠ x.2.1 := fun x hx h => by
    have := hx.2.2.1
    rw [h, sub_self, norm_zero] at this
    linarith
  have hK2O : fzK2 δ c T b (fzSep c T a b) ⊆ fzO2 := fun x hx =>
    ⟨hδ.trans_le hx.1.1, hδ.trans_le hx.2.1.1, hne_of x hx⟩
  -- local Dynkin on the two-point state, stopped at `σ_a ∧ σ_b`
  have hloc := martingale_localDynkin_stopped hB hBc 𝓕 hBad hpast (lipschitzWith_fzDrift2 hc)
    (norm_fzDrift2_le hc) (fzU2_eq hBc hc a b) isOpen_fzO2 (isClosed_fzCl2 δ)
    (isClosed_fzK2 δ c T b (fzSep c T a b)) hK2O (contDiffOn_fzF2 κ)
    (fun x hx _ => dynkinGen_fzF2 hκ hc (hcδ.trans hx.1.1) (hcδ.trans hx.2.1.1) (hne_of x hx)) T
    (fun ω t htT h => fzU2_mem_fzK2 hBc hc hcδ hδa hδb ω htT h)
    (fun x hx => abs_fzF2_le hδ hd0 hx)
  have hhit : ∀ ω, hittingBtwn (fzU2 κ c B a b) (fzCl2 δ) 0 T ω =
      min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω) := fun ω => by
    rw [fzCl2, hittingBtwn_union]; rfl
  simp only [hhit] at hloc
  -- the two freezing times
  have hZad : ∀ a' : ℂ, Adapted 𝓕 (fzZ κ c B a') := fun a' t =>
    measurable_fst.comp (Dynkin.measurable_of_integralEq 𝓕 hBad hBc (lipschitzWith_fzDrift hc)
      (norm_fzDrift_le hc) (fzU_eq hBc hc a') (fun ω => continuous_fzU hBc hc a' ω) t)
  have hσ : ∀ a' : ℂ, IsStoppingTime 𝓕
      (fun ω => ((frozenTime κ c δ T B a' ω : ℝ≥0) : WithTop ℝ≥0)) := fun a' =>
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed (hZad a') (continuous_fzZ hBc hc a')
      (isClosed_le Complex.continuous_im continuous_const) T
  have hρ := (hσ a).min (hσ b)
  -- MF-1 for both points
  have hMa := frozenField_martingale hB hBc 𝓕 hBad hpast hκ hc hcδ hδa T
  have hMb := frozenField_martingale hB hBc 𝓕 hBad hpast hκ hc hcδ hδb T
  have hca := continuous_frozenField (κ := κ) hBc hc hcδ hδa T
  have hcb := continuous_frozenField (κ := κ) hBc hc hcδ hδb T
  have hba := abs_frozenField_le (κ := κ) hBc hc hδa T
  have hbb := abs_frozenField_le (κ := κ) hBc hc hδb T
  have hBd0 : 0 ≤ fzBound κ c T := by unfold fzBound; positivity
  have hprog_a := hMa.stronglyAdapted.isStronglyProgressive_of_continuous hca
  have hprog_b := hMb.stronglyAdapted.isStronglyProgressive_of_continuous hcb
  -- the frozen factors
  set S : Set Ω := {ω | ((frozenTime κ c δ T B a ω : ℝ≥0) : WithTop ℝ≥0)
    ≤ ((frozenTime κ c δ T B b ω : ℝ≥0) : WithTop ℝ≥0)} with hS_def
  have hS : MeasurableSet[hρ.measurableSpace] S := IsStoppingTime.measurableSet_stopping_time_le_min (hσ a) (hσ b)
  set ρ' : Ω → WithTop ℝ≥0 := fun ω => min ((frozenTime κ c δ T B a ω : ℝ≥0) : WithTop ℝ≥0)
    ((frozenTime κ c δ T B b ω : ℝ≥0) : WithTop ℝ≥0) with hρ'_def
  set ξa : Ω → ℝ := S.indicator (stoppedValue (frozenField κ c δ T B a) ρ') with hξa_def
  set ξb : Ω → ℝ := Sᶜ.indicator (stoppedValue (frozenField κ c δ T B b) ρ') with hξb_def
  have hξa : Measurable[hρ.measurableSpace] ξa := (measurable_stoppedValue hprog_a hρ).indicator hS
  have hξb : Measurable[hρ.measurableSpace] ξb :=
    (measurable_stoppedValue hprog_b hρ).indicator hS.compl
  have hξab : ∀ ω, |ξa ω| ≤ fzBound κ c T := fun ω => by
    simp only [ξa, Set.indicator_apply]
    split_ifs
    · exact hba _ ω
    · simpa using hBd0
  have hξbb : ∀ ω, |ξb ω| ≤ fzBound κ c T := fun ω => by
    simp only [ξb, Set.indicator_apply]
    split_ifs
    · exact hbb _ ω
    · simpa using hBd0
  have hga := ItoLite.martingale_glue hMb hcb hbb hρ hξa hξab
  have hgb := ItoLite.martingale_glue hMa hca hba hρ hξb hξbb
  have hsum := (hloc.add hga).add hgb
  have hsp : ∀ (u : ℝ≥0 → Ω → ℝ) t ω, stoppedProcess u ρ' t ω =
      u (min t (min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω))) ω := by
    intro u t ω
    simp only [stoppedProcess, ρ', ← WithTop.coe_min]
    rfl
  have hsv : ∀ (u : ℝ≥0 → Ω → ℝ) ω, stoppedValue u ρ' ω =
      u (min (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω)) ω := by
    intro u ω
    simp only [stoppedValue, ρ', ← WithTop.coe_min]
    rfl
  convert hsum using 1
  funext t ω
  simp only [Pi.add_apply, hsp]
  have hmem : ω ∈ S ↔ frozenTime κ c δ T B a ω ≤ frozenTime κ c δ T B b ω := by
    simp only [S, mem_setOf_eq, WithTop.coe_le_coe]
  refine pair_decomp_alg (fun q => fzPhi κ (fzU κ c B a q ω)) (fun q => fzPhi κ (fzU κ c B b q ω))
    _ (ξa ω) (ξb ω) (frozenTime κ c δ T B a ω) (frozenTime κ c δ T B b ω) t (fun h => ?_)
    (fun h => ?_)
  · refine ⟨?_, ?_⟩
    · rw [hξa_def, Set.indicator_of_mem (hmem.2 h), hsv]; rfl
    · rw [hξb_def, Set.indicator_of_notMem (show ω ∉ Sᶜ from fun h' => h' (hmem.2 h))]
  · refine ⟨?_, ?_⟩
    · rw [hξa_def, Set.indicator_of_notMem (show ω ∉ S from fun h' => h (hmem.1 h'))]
    · rw [hξb_def, Set.indicator_of_mem (show ω ∈ Sᶜ from fun h' => h (hmem.1 h')), hsv]; rfl

/-! ## H. MF-4 (one-point part): pathwise increments of the frozen field -/

theorem le_bmOsc {ω : Ω} (hc : Continuous (B · ω)) {t s r : ℝ≥0} (hr : r ∈ Icc t (t + s)) :
    |B r ω - B t ω| ≤ bmOsc B t s ω := by
  rw [bmOsc_eq_iSup_subtype hc]
  have hbdd : BddAbove (Set.range fun x : Set.Icc t (t + s) => |B x ω - B t ω|) := by
    have hK : IsCompact (Set.Icc t (t + s)) := isCompact_Icc
    obtain ⟨C, hC⟩ := (hK.image (f := fun r => |B r ω - B t ω|) (by fun_prop)).bddAbove
    exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC ⟨x, x.2, rfl⟩⟩
  exact le_ciSup hbdd ⟨r, hr⟩

theorem bmOsc_nonneg' {ω : Ω} (hc : Continuous (B · ω)) (t s : ℝ≥0) : 0 ≤ bmOsc B t s ω := by
  have := le_bmOsc hc (t := t) (s := s) (r := t) ⟨le_rfl, le_self_add⟩
  rwa [sub_self, abs_zero] at this

/-- **MF-4, one-point increments.** For `t ≤ t'`,
`|𝔥^δ_{t'}(a) − 𝔥^δ_t(a)| ≤ (2/δ) osc_{[t,t']} B + K (t' − t)` with
`K = (2/√κ)(2/c)/δ + |χ| (2/c²)`. -/
theorem abs_frozenField_sub_le (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hκ : 0 < κ)
    (hc : 0 < c) (hcδ : c ≤ δ) {a : ℂ} (hδa : δ ≤ a.im) (T : ℝ≥0) (ω : Ω) {t t' : ℝ≥0}
    (htt : t ≤ t') :
    |frozenField κ c δ T B a t' ω - frozenField κ c δ T B a t ω| ≤
      2 / δ * bmOsc B t (t' - t) ω
        + (2 / Real.sqrt κ * (2 / c) / δ + |chiC κ| * (2 / c ^ 2)) * ((t' : ℝ) - t) := by
  have hδ : 0 < δ := hc.trans_le hcδ
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hW := continuous_drive_path (κ := κ) hBc ω
  have hosc := bmOsc_nonneg' (hBc ω) t (t' - t)
  have hdt : (0 : ℝ) ≤ (t' : ℝ) - t := sub_nonneg.2 (by exact_mod_cast htt)
  have hK0 : 0 ≤ 2 / Real.sqrt κ * (2 / c) / δ + |chiC κ| * (2 / c ^ 2) := by
    have : 0 < c ^ 2 := pow_pos hc 2
    positivity
  have hRHS : 0 ≤ 2 / δ * bmOsc B t (t' - t) ω
      + (2 / Real.sqrt κ * (2 / c) / δ + |chiC κ| * (2 / c ^ 2)) * ((t' : ℝ) - t) := by
    have : 0 ≤ 2 / δ := by positivity
    positivity
  set σ := frozenTime κ c δ T B a ω with hσ_def
  by_cases hσt : σ ≤ t
  · have e1 : min t σ = σ := min_eq_right hσt
    have e2 : min t' σ = σ := min_eq_right (hσt.trans htt)
    simp only [frozenField, ← hσ_def, e1, e2, sub_self, abs_zero]
    exact hRHS
  · have hlt : t < σ := not_le.mp hσt
    have e1 : min t σ = t := min_eq_left hlt.le
    set u := min t' σ with hu_def
    have htu : t ≤ u := le_min htt hlt.le
    have hut : u ≤ t' := min_le_left _ _
    have hmem := fzU_frozen_mem (κ := κ) hBc hc hδa (T := T) t ω
    have hmem' := fzU_frozen_mem (κ := κ) hBc hc hδa (T := T) t' ω
    rw [← hσ_def, e1] at hmem
    rw [← hσ_def] at hmem'
    have hdu : (u : ℝ) - t ≤ (t' : ℝ) - t := by
      have : (u : ℝ) ≤ t' := by exact_mod_cast hut
      linarith
    have hdu0 : (0 : ℝ) ≤ (u : ℝ) - t := sub_nonneg.2 (by exact_mod_cast htu)
    -- the increment of `Z̃`
    have hZ : ‖fzZ κ c B a u ω - fzZ κ c B a t ω‖ ≤
        Real.sqrt κ * bmOsc B t (t' - t) ω + 2 / c * ((t' : ℝ) - t) := by
      have h1 := dist_tamedZ_time_le hW hc a t.coe_nonneg u.coe_nonneg
      rw [dist_eq_norm] at h1
      have h2 : |drive κ B ω u - drive κ B ω t| ≤ Real.sqrt κ * bmOsc B t (t' - t) ω := by
        simp only [drive, Real.toNNReal_coe]
        rw [← mul_sub, abs_mul, abs_of_nonneg hs.le]
        refine mul_le_mul_of_nonneg_left (le_bmOsc (hBc ω) ⟨htu, ?_⟩) hs.le
        rw [add_tsub_cancel_of_le htt]; exact hut
      have h3 : 2 / c * |(u : ℝ) - t| ≤ 2 / c * ((t' : ℝ) - t) := by
        rw [abs_of_nonneg hdu0]
        exact mul_le_mul_of_nonneg_left hdu (div_nonneg (by norm_num) hc.le)
      exact h1.trans (add_le_add h2 h3)
    have hA : |fzA κ c B a u ω - fzA κ c B a t ω| ≤ 2 / c ^ 2 * ((t' : ℝ) - t) := by
      have h1 := abs_tamedA_time_le hW hc a t.coe_nonneg u.coe_nonneg
      rw [abs_of_nonneg hdu0] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hdu (div_nonneg (by norm_num) (pow_pos hc 2).le))
    have harg := Thm11Lyap.arg_lipschitz_of_im_ge hδ hmem'.1 hmem.1
    simp only [frozenField, ← hσ_def, e1, ← hu_def]
    unfold fzPhi h0fwd
    simp only [fzU]
    have hsplit : -(2 / Real.sqrt κ) * Complex.arg (fzZ κ c B a u ω) - chiC κ * fzA κ c B a u ω
        - (-(2 / Real.sqrt κ) * Complex.arg (fzZ κ c B a t ω) - chiC κ * fzA κ c B a t ω)
        = -(2 / Real.sqrt κ) * (Complex.arg (fzZ κ c B a u ω) - Complex.arg (fzZ κ c B a t ω))
          - chiC κ * (fzA κ c B a u ω - fzA κ c B a t ω) := by ring
    rw [hsplit]
    have h2s : 0 ≤ 2 / Real.sqrt κ := by positivity
    calc _ ≤ |-(2 / Real.sqrt κ) * (Complex.arg (fzZ κ c B a u ω)
            - Complex.arg (fzZ κ c B a t ω))| + |chiC κ * (fzA κ c B a u ω - fzA κ c B a t ω)| :=
          abs_sub _ _
      _ = 2 / Real.sqrt κ * |Complex.arg (fzZ κ c B a u ω) - Complex.arg (fzZ κ c B a t ω)|
            + |chiC κ| * |fzA κ c B a u ω - fzA κ c B a t ω| := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg h2s]
      _ ≤ 2 / Real.sqrt κ * ((Real.sqrt κ * bmOsc B t (t' - t) ω + 2 / c * ((t' : ℝ) - t)) / δ)
            + |chiC κ| * (2 / c ^ 2 * ((t' : ℝ) - t)) := by
          gcongr
          exact harg.trans (div_le_div_of_nonneg_right hZ hδ.le)
      _ = _ := by field_simp; ring

end FrozenMart
end QuantumZipper
