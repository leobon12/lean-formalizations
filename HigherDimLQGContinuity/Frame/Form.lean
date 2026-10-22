import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.LGF.Exists
import HigherDimLQGMetric.Field.StandardBorelDist

/-!
# Pairing frame I: a determining mean-zero family and Gram–Schmidt through the log form

Packet N3 (NA4 Details (a) A2, steps 1–2; blueprint Part C `c:lem-frame-dense`, `c:lem-frame-gs`).

* `frameGen d k = distGen ⊤ (unpair k)` enumerates HDLM's countable determining family of test functions, and
  `frameChi d k = φ_k - (∫ φ_k) θ` are mean-zero test functions. `eq_addConst_of_forall_chi`: two distributions
  with the same pairings against all `χ_k` differ by the constant `g'(θ) - g(θ)`.
* `frameForm φ ψ = logCovF φ ψ = ∫∫ φ(x) ψ(y) log|x - y|⁻¹` is a symmetric bilinear form on test functions
  (`frameFormL`), positive semidefinite on mean-zero test functions, and a null vector is orthogonal to every mean-zero
  test function (both through HDLM's Gram identity `inner_gramVec`; no linearity of `gramVec` is used).
* Gram–Schmidt through the form (`frameGS`): `ψ_k = n_k^{-1/2} ψ̃_k` if `n_k = ⟨ψ̃_k, ψ̃_k⟩₋ > 0` and `ψ_k = 0`
  otherwise, `ψ̃_k = χ_k - Σ_{j<k} ⟨χ_k, ψ_j⟩₋ ψ_j`. With `c_k = 1_{n_k > 0}` (`frameC`):
  `⟨ψ_i, ψ_j⟩₋ = δ_{ij} c_i` (`frameGS_orthonormal`); the coefficients `b_{kj} = ⟨χ_k, ψ_j⟩₋` (`frameGSCoef`) vanish for
  `j > k` (`frameGSCoef_eq_zero_of_lt`); the residual `r_k = χ_k - Σ_{j ≤ k} b_{kj} ψ_j` is null
  (`frameForm_frameRes_self`), so for every whole-space LGF `h(χ_k) = Σ_{j ≤ k} b_{kj} h(ψ_j)` a.s.
  (`ae_frameGS_relation`).

The index set `J = {k : n_k > 0}` of the blueprint is encoded by `frameC`; coordinates outside `J` carry `ψ_k = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The determining mean-zero family -/

/-- `φ_k = distGen ⊤ (unpair k)`: HDLM's countable family of test functions whose pairings determine a
distribution (`injective_distOn_pairings`), indexed by `ℕ`. -/
def frameGen (d : ℕ) (k : ℕ) : TestRd d := distGen ⊤ (Nat.unpair k)

/-- `χ_k = φ_k - (∫ φ_k) θ`: mean-zero test functions (Part C `c:lem-frame-dense`). -/
def frameChi (d : ℕ) (k : ℕ) : TestRd d := frameGen d k - (∫ x, frameGen d k x) • theta d

/-- Integration of test functions, as a linear map. -/
def frameMeanL (d : ℕ) : TestRd d →ₗ[ℝ] ℝ where
  toFun φ := ∫ x, φ x
  map_add' φ ψ := by
    simp only [add_apply]
    exact integral_add (integrable_testOn φ) (integrable_testOn ψ)
  map_smul' c φ := by
    simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem frameMeanL_apply (φ : TestRd d) : frameMeanL d φ = ∫ x, φ x := rfl

/-- `χ_k` is HDLM's `subTheta φ_k`, as a test function. -/
theorem coe_frameChi (k : ℕ) : ⇑(frameChi d k) = subTheta (frameGen d k) := by
  funext u
  simp only [frameChi, sub_apply, smul_apply, smul_eq_mul, subTheta]

theorem integral_frameChi (k : ℕ) : ∫ x, frameChi d k x = 0 := by
  rw [← frameMeanL_apply, frameChi, map_sub, map_smul, frameMeanL_apply, frameMeanL_apply (theta d),
    integral_theta, smul_eq_mul, mul_one, sub_self]

/-- **Determining family** (Part C `c:lem-frame-dense`): if `g(χ_k) = g'(χ_k)` for all `k`, then
`g' = g + c` with `c = g'(θ) - g(θ)`. -/
theorem eq_addConst_of_forall_chi {g g' : DistRd d}
    (h : ∀ k, g (frameChi d k) = g' (frameChi d k)) :
    g' = addConst g (g' (theta d) - g (theta d)) := by
  apply injective_distOn_pairings (⊤ : TopologicalSpace.Opens (Rd d))
  funext j
  set k := Nat.pair j.1 j.2 with hk
  have hj : frameGen d k = distGen ⊤ j := by
    simp only [frameGen, hk, Nat.unpair_pair]
  set a := ∫ x, distGen (⊤ : TopologicalSpace.Opens (Rd d)) j x with ha
  have hdec : distGen ⊤ j = frameChi d k + a • theta d := by
    rw [frameChi, hj, sub_add_cancel]
  have e1 : g' (distGen ⊤ j) = g' (frameChi d k) + a * g' (theta d) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, smul_eq_mul]
  have e2 : g (distGen ⊤ j) = g (frameChi d k) + a * g (theta d) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, smul_eq_mul]
  show g' (distGen ⊤ j) = addConst g (g' (theta d) - g (theta d)) (distGen ⊤ j)
  rw [addConst_apply, e1, e2, h k, ← ha]
  ring

/-! ## The logarithmic form on test functions -/

/-- `⟨φ, ψ⟩₋ = ∫∫ φ(x) ψ(y) log|x - y|⁻¹ dx dy` (HDLM's `logCovF`) on test functions. -/
def frameForm (φ ψ : TestRd d) : ℝ := logCovF ⇑φ ⇑ψ

theorem frameForm_comm (φ ψ : TestRd d) : frameForm φ ψ = frameForm ψ φ := logCovF_comm _ _

theorem frameForm_smul_left (c : ℝ) (φ ψ : TestRd d) :
    frameForm (c • φ) ψ = c * frameForm φ ψ := by
  unfold frameForm logCovF
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [smul_apply, smul_eq_mul]
  ring

theorem frameForm_smul_right (c : ℝ) (φ ψ : TestRd d) :
    frameForm φ (c • ψ) = c * frameForm φ ψ := by
  rw [frameForm_comm, frameForm_smul_left, frameForm_comm]

@[simp]
theorem frameForm_zero_left (ψ : TestRd d) : frameForm 0 ψ = 0 := by
  have h := frameForm_smul_left 0 (0 : TestRd d) ψ
  rwa [zero_smul, zero_mul] at h

@[simp]
theorem frameForm_zero_right (φ : TestRd d) : frameForm φ 0 = 0 := by
  rw [frameForm_comm, frameForm_zero_left]

section Form

variable [NeZero d]

theorem frameForm_add_left (φ₁ φ₂ ψ : TestRd d) :
    frameForm (φ₁ + φ₂) ψ = frameForm φ₁ ψ + frameForm φ₂ ψ := by
  obtain ⟨M₁, D₁, h₁⟩ := exists_isBddSupp_testOn φ₁
  obtain ⟨M₂, D₂, h₂⟩ := exists_isBddSupp_testOn φ₂
  obtain ⟨M, D, h⟩ := exists_isBddSupp_testOn ψ
  unfold frameForm logCovF
  rw [← integral_add (integrable_logKer h₁ h) (integrable_logKer h₂ h)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [add_apply]
  ring

theorem frameForm_add_right (φ ψ₁ ψ₂ : TestRd d) :
    frameForm φ (ψ₁ + ψ₂) = frameForm φ ψ₁ + frameForm φ ψ₂ := by
  rw [frameForm_comm, frameForm_add_left, frameForm_comm ψ₁, frameForm_comm ψ₂]

/-- The log form as a bilinear map. -/
def frameFormL (d : ℕ) [NeZero d] : TestRd d →ₗ[ℝ] TestRd d →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ frameForm frameForm_add_left
    (fun c φ ψ => by rw [frameForm_smul_left, smul_eq_mul]) frameForm_add_right
    (fun c φ ψ => by rw [frameForm_smul_right, smul_eq_mul])

theorem frameFormL_apply (φ ψ : TestRd d) : frameFormL d φ ψ = frameForm φ ψ := rfl

theorem frameForm_sub_left (φ₁ φ₂ ψ : TestRd d) :
    frameForm (φ₁ - φ₂) ψ = frameForm φ₁ ψ - frameForm φ₂ ψ := by
  rw [← frameFormL_apply, map_sub, LinearMap.sub_apply, frameFormL_apply, frameFormL_apply]

theorem frameForm_sub_right (φ ψ₁ ψ₂ : TestRd d) :
    frameForm φ (ψ₁ - ψ₂) = frameForm φ ψ₁ - frameForm φ ψ₂ := by
  rw [← frameFormL_apply, map_sub, frameFormL_apply, frameFormL_apply]

theorem frameForm_sum_smul_left {ι : Type*} (s : Finset ι) (a : ι → ℝ) (f : ι → TestRd d)
    (ψ : TestRd d) :
    frameForm (∑ i ∈ s, a i • f i) ψ = ∑ i ∈ s, a i * frameForm (f i) ψ := by
  rw [← frameFormL_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, frameFormL_apply, smul_eq_mul]

theorem frameForm_sum_smul_right {ι : Type*} (s : Finset ι) (a : ι → ℝ) (f : ι → TestRd d)
    (φ : TestRd d) :
    frameForm φ (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i * frameForm φ (f i) := by
  rw [frameForm_comm, frameForm_sum_smul_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frameForm_comm]

/-- The form is positive semidefinite on mean-zero test functions (Gram identity `inner_gramVec`). -/
theorem frameForm_self_nonneg {φ : TestRd d} (hφ : ∫ x, φ x = 0) : 0 ≤ frameForm φ φ := by
  obtain ⟨M, D, h⟩ := exists_isBddSupp_testOn φ
  have e := inner_gramVec h hφ h hφ
  unfold frameForm
  rw [← e]
  exact real_inner_self_nonneg

/-- A null mean-zero test function is orthogonal to every mean-zero test function. -/
theorem frameForm_eq_zero_of_self_eq_zero {u w : TestRd d} (hu : ∫ x, u x = 0)
    (hw : ∫ x, w x = 0) (h : frameForm u u = 0) : frameForm u w = 0 := by
  obtain ⟨M, D, hU⟩ := exists_isBddSupp_testOn u
  obtain ⟨M', D', hW⟩ := exists_isBddSupp_testOn w
  have h1 := inner_gramVec hU hu hU hu
  have h2 := inner_gramVec hU hu hW hw
  have h0 : gramVec (fun z => u z) = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ), h1]
    exact h
  unfold frameForm
  rw [← h2, h0, inner_zero_left]

end Form

/-! ## Gram–Schmidt through the form -/

/-- The Gram–Schmidt residual `ψ̃_k = χ_k - Σ_{j<k} ⟨χ_k, prev j⟩₋ prev j`. -/
def frameTilde (prev : ℕ → TestRd d) (k : ℕ) : TestRd d :=
  frameChi d k - ∑ j ∈ Finset.range k, frameForm (frameChi d k) (prev j) • prev j

/-- One Gram–Schmidt step: `n_k^{-1/2} ψ̃_k` if `n_k = ⟨ψ̃_k, ψ̃_k⟩₋ > 0`, else `0`. -/
def frameStep (prev : ℕ → TestRd d) (k : ℕ) : TestRd d :=
  if 0 < frameForm (frameTilde prev k) (frameTilde prev k) then
    (Real.sqrt (frameForm (frameTilde prev k) (frameTilde prev k)))⁻¹ • frameTilde prev k
  else 0

/-- The first `n` Gram–Schmidt vectors (auxiliary recursion). -/
def frameGSAux (d : ℕ) : ℕ → ℕ → TestRd d
  | 0 => fun _ => 0
  | n + 1 => fun k => if k < n then frameGSAux d n k else frameStep (frameGSAux d n) n

/-- The Gram–Schmidt vectors `ψ_k` (Part C `c:lem-frame-gs`). -/
def frameGS (d : ℕ) (k : ℕ) : TestRd d := frameGSAux d (k + 1) k

theorem frameGSAux_eq : ∀ (n k : ℕ), k < n → frameGSAux d n k = frameGS d k
  | 0, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, k, hk => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | rfl
    · simp only [frameGSAux, ite_eq_left hlt]
      exact frameGSAux_eq n k hlt
    · rfl

theorem frameTilde_congr {prev prev' : ℕ → TestRd d} (k : ℕ) (h : ∀ j < k, prev j = prev' j) :
    frameTilde prev k = frameTilde prev' k := by
  unfold frameTilde
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

theorem frameStep_congr {prev prev' : ℕ → TestRd d} (k : ℕ) (h : ∀ j < k, prev j = prev' j) :
    frameStep prev k = frameStep prev' k := by
  unfold frameStep
  rw [frameTilde_congr k h]

theorem frameGS_eq_step (k : ℕ) : frameGS d k = frameStep (frameGS d) k := by
  show frameGSAux d (k + 1) k = _
  simp only [frameGSAux, lt_irrefl, ite_false]
  exact frameStep_congr k fun j hj => frameGSAux_eq k j hj

/-- `n_k = ⟨ψ̃_k, ψ̃_k⟩₋`. -/
def frameNorm (d : ℕ) (k : ℕ) : ℝ :=
  frameForm (frameTilde (frameGS d) k) (frameTilde (frameGS d) k)

/-- `c_k = 1_{k ∈ J}`, `J = {k : n_k > 0}`. -/
def frameC (d : ℕ) (k : ℕ) : ℝ := if 0 < frameNorm d k then 1 else 0

theorem frameGS_of_pos {k : ℕ} (h : 0 < frameNorm d k) :
    frameGS d k = (Real.sqrt (frameNorm d k))⁻¹ • frameTilde (frameGS d) k := by
  rw [frameGS_eq_step, frameStep]
  exact ite_eq_left h

theorem frameGS_of_not_pos {k : ℕ} (h : ¬ 0 < frameNorm d k) : frameGS d k = 0 := by
  rw [frameGS_eq_step, frameStep]
  exact ite_eq_right h

theorem frameC_of_pos {k : ℕ} (h : 0 < frameNorm d k) : frameC d k = 1 := ite_eq_left h

theorem frameC_of_not_pos {k : ℕ} (h : ¬ 0 < frameNorm d k) : frameC d k = 0 := ite_eq_right h

theorem frameGS_eq_zero_of_frameC_eq_zero {k : ℕ} (h : frameC d k = 0) : frameGS d k = 0 := by
  by_cases hk : 0 < frameNorm d k
  · rw [frameC_of_pos hk] at h
    exact absurd h one_ne_zero
  · exact frameGS_of_not_pos hk

theorem frameC_mem (k : ℕ) : frameC d k = 0 ∨ frameC d k = 1 := by
  unfold frameC
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem frameC_mul_self (k : ℕ) : frameC d k * frameC d k = frameC d k := by
  rcases frameC_mem (d := d) k with h | h <;> rw [h] <;> norm_num

/-- The Gram–Schmidt coefficients `b_{kj} = ⟨χ_k, ψ_j⟩₋`. -/
def frameGSCoef (d : ℕ) (k j : ℕ) : ℝ := frameForm (frameChi d k) (frameGS d j)

/-- The residual `r_k = χ_k - Σ_{j ≤ k} b_{kj} ψ_j`. -/
def frameRes (d : ℕ) (k : ℕ) : TestRd d :=
  frameChi d k - ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j • frameGS d j

theorem frameTilde_frameGS (k : ℕ) :
    frameTilde (frameGS d) k = frameChi d k - ∑ j ∈ Finset.range k, frameGSCoef d k j • frameGS d j :=
  rfl

theorem integral_frameTilde {prev : ℕ → TestRd d} (k : ℕ) (h : ∀ j < k, ∫ x, prev j x = 0) :
    ∫ x, frameTilde prev k x = 0 := by
  rw [← frameMeanL_apply, frameTilde, map_sub, map_sum, frameMeanL_apply, integral_frameChi,
    zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [map_smul, frameMeanL_apply, h j (Finset.mem_range.1 hj), smul_zero]

theorem integral_frameGS (k : ℕ) : ∫ x, frameGS d k x = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [frameGS_eq_step, frameStep]
    split_ifs
    · rw [← frameMeanL_apply, map_smul, frameMeanL_apply, integral_frameTilde k ih, smul_zero]
    · rw [← frameMeanL_apply, map_zero]

theorem integral_frameTilde_frameGS (k : ℕ) : ∫ x, frameTilde (frameGS d) k x = 0 :=
  integral_frameTilde k fun j _ => integral_frameGS j

theorem integral_frameRes (k : ℕ) : ∫ x, frameRes d k x = 0 := by
  rw [← frameMeanL_apply, frameRes, map_sub, map_sum, frameMeanL_apply, integral_frameChi,
    zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, frameMeanL_apply, integral_frameGS, smul_zero]

section GS

variable [NeZero d]

/-- Under orthonormality below `k`, the residual `ψ̃_k` is orthogonal to `ψ_j`, `j < k`. -/
theorem frameForm_frameTilde_of_lt {k : ℕ}
    (ih : ∀ i j, i < k → j < k →
      frameForm (frameGS d i) (frameGS d j) = if i = j then frameC d i else 0)
    {j : ℕ} (hj : j < k) : frameForm (frameTilde (frameGS d) k) (frameGS d j) = 0 := by
  rw [frameTilde_frameGS, frameForm_sub_left, frameForm_sum_smul_left]
  have hs : ∑ i ∈ Finset.range k, frameGSCoef d k i * frameForm (frameGS d i) (frameGS d j) =
      frameGSCoef d k j * frameC d j := by
    rw [Finset.sum_eq_single j]
    · rw [ih j j hj hj, ite_eq_left rfl]
    · intro i hi hij
      rw [ih i j (Finset.mem_range.1 hi) hj, ite_eq_right hij, mul_zero]
    · intro hj'
      exact absurd (Finset.mem_range.2 hj) hj'
  rw [hs]
  by_cases hpos : 0 < frameNorm d j
  · rw [frameC_of_pos hpos, mul_one]
    exact sub_self _
  · have h0 : frameGS d j = 0 := frameGS_of_not_pos hpos
    simp only [frameGSCoef, h0, frameForm_zero_right, zero_mul, sub_zero]

/-- Orthonormality below `k` (strong form used by the induction). -/
theorem frameForm_frameGS_of_lt : ∀ (k : ℕ), ∀ i j, i < k → j < k →
    frameForm (frameGS d i) (frameGS d j) = if i = j then frameC d i else 0
  | 0 => fun i j hi _ => absurd hi (Nat.not_lt_zero i)
  | k + 1 => by
    have ih := frameForm_frameGS_of_lt k
    -- `ψ_k ⊥ ψ_j` for `j < k`
    have hkj : ∀ j, j < k → frameForm (frameGS d k) (frameGS d j) = 0 := by
      intro j hj
      by_cases hpos : 0 < frameNorm d k
      · rw [frameGS_of_pos hpos, frameForm_smul_left, frameForm_frameTilde_of_lt ih hj, mul_zero]
      · rw [frameGS_of_not_pos hpos, frameForm_zero_left]
    have hkk : frameForm (frameGS d k) (frameGS d k) = frameC d k := by
      by_cases hpos : 0 < frameNorm d k
      · rw [frameGS_of_pos hpos, frameForm_smul_left, frameForm_smul_right, frameC_of_pos hpos]
        change (Real.sqrt (frameNorm d k))⁻¹ * ((Real.sqrt (frameNorm d k))⁻¹ * frameNorm d k) = 1
        rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
      · rw [frameGS_of_not_pos hpos, frameForm_zero_left, frameC_of_not_pos hpos]
    intro i j hi hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · exact ih i j hi' hj'
      · rw [frameForm_comm, hkj i hi', ite_eq_right (Nat.ne_of_lt hi')]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · rw [hkj j hj', ite_eq_right (Nat.ne_of_gt hj')]
      · rw [hkk, ite_eq_left rfl]

/-- **Orthonormality** (Part C `c:lem-frame-gs`(a)): `⟨ψ_i, ψ_j⟩₋ = δ_{ij} c_i`. -/
theorem frameGS_orthonormal (i j : ℕ) :
    frameForm (frameGS d i) (frameGS d j) = if i = j then frameC d i else 0 :=
  frameForm_frameGS_of_lt (max i j + 1) i j (Nat.lt_succ_of_le (le_max_left i j))
    (Nat.lt_succ_of_le (le_max_right i j))

theorem frameForm_frameTilde_frameGS_of_lt {k j : ℕ} (hj : j < k) :
    frameForm (frameTilde (frameGS d) k) (frameGS d j) = 0 :=
  frameForm_frameTilde_of_lt (fun i j _ _ => frameGS_orthonormal i j) hj

/-- **The residual is null** (Part C `c:lem-frame-gs`(c)). -/
theorem frameForm_frameRes_self (k : ℕ) : frameForm (frameRes d k) (frameRes d k) = 0 := by
  have hres : frameRes d k = frameTilde (frameGS d) k - frameGSCoef d k k • frameGS d k := by
    rw [frameRes, frameTilde_frameGS, Finset.sum_range_succ, sub_add_eq_sub_sub]
  by_cases hpos : 0 < frameNorm d k
  · -- `b_kk = √n_k` and `r_k = 0`
    set t := frameTilde (frameGS d) k with ht
    have hchi : frameChi d k = t + ∑ j ∈ Finset.range k, frameGSCoef d k j • frameGS d j := by
      rw [ht, frameTilde_frameGS, sub_add_cancel]
    have hct : frameForm (frameChi d k) t = frameNorm d k := by
      rw [hchi, frameForm_add_left, frameForm_sum_smul_left]
      have : ∑ j ∈ Finset.range k, frameGSCoef d k j * frameForm (frameGS d j) t = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [frameForm_comm, frameForm_frameTilde_frameGS_of_lt (Finset.mem_range.1 hj), mul_zero]
      rw [this, add_zero]
      rfl
    have hbkk : frameGSCoef d k k = Real.sqrt (frameNorm d k) := by
      rw [frameGSCoef, frameGS_of_pos hpos, frameForm_smul_right, ← ht, hct]
      have hs := Real.sqrt_pos.2 hpos
      field_simp
      rw [Real.sq_sqrt hpos.le]
    have h0 : frameRes d k = 0 := by
      rw [hres, hbkk, frameGS_of_pos hpos, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne',
        one_smul, ← ht, sub_self]
    rw [h0, frameForm_zero_left]
  · have h0 : frameGS d k = 0 := frameGS_of_not_pos hpos
    rw [hres, h0, smul_zero, sub_zero]
    exact le_antisymm (not_lt.1 hpos) (frameForm_self_nonneg (integral_frameTilde_frameGS k))

/-- `b_{kj} = 0` for `j > k` (Part C `c:lem-frame-gs`(b)). -/
theorem frameGSCoef_eq_zero_of_lt {k j : ℕ} (h : k < j) : frameGSCoef d k j = 0 := by
  have hchi : frameChi d k =
      frameRes d k + ∑ i ∈ Finset.range (k + 1), frameGSCoef d k i • frameGS d i := by
    rw [frameRes, sub_add_cancel]
  rw [frameGSCoef, hchi, frameForm_add_left, frameForm_sum_smul_left,
    frameForm_eq_zero_of_self_eq_zero (integral_frameRes k) (integral_frameGS j)
      (frameForm_frameRes_self k), zero_add]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hij : i ≠ j := by
    have := Finset.mem_range.1 hi
    omega
  rw [frameGS_orthonormal, ite_eq_right hij, mul_zero]

end GS

theorem frameGSCoef_mul_frameC (k j : ℕ) : frameGSCoef d k j * frameC d j = frameGSCoef d k j := by
  by_cases hpos : 0 < frameNorm d j
  · rw [frameC_of_pos hpos, mul_one]
  · rw [frameC_of_not_pos hpos, mul_zero, frameGSCoef, frameGS_of_not_pos hpos, frameForm_zero_right]

/-! ## The relations under a whole-space LGF -/

/-- **The relations** (Part C `c:lem-frame-gs`(d)): for every whole-space LGF `h` and every `k`,
`h(χ_k) = Σ_{j ≤ k} b_{kj} h(ψ_j)` almost surely. -/
theorem ae_frameGS_relation [NeZero d] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P) (k : ℕ) :
    ∀ᵐ ω ∂P, h ω (frameChi d k) =
      ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * h ω (frameGS d j) := by
  have := hh.gaussian.isProbabilityMeasure
  let r : TestRd0 d := ⟨frameRes d k, integral_frameRes k⟩
  have hG : HasGaussianLaw (fun ω => h ω r.1) P := hh.gaussian.hasGaussianLaw_eval r
  have hL2 : MemLp (fun ω => h ω r.1) 2 P := hG.memLp_two
  have hvar : Var[fun ω => h ω r.1; P] = 0 := by
    rw [← covariance_self hG.aemeasurable, hh.covariance_eq r r]
    obtain ⟨M, D, hMD⟩ := exists_isBddSupp_testOn (frameRes d k)
    rw [logCovRd_eq_logCovF hMD hMD]
    exact frameForm_frameRes_self k
  have hmean : ∫ ω, h ω r.1 ∂P = 0 := hh.centered r
  filter_upwards [ae_eq_integral_of_variance_eq_zero hL2 hvar] with ω hω
  rw [hmean] at hω
  have e : h ω r.1 = h ω (frameChi d k) -
      ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * h ω (frameGS d j) := by
    show h ω (frameRes d k) = _
    rw [frameRes, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [e] at hω
  linarith

end HigherDimLQGContinuity
