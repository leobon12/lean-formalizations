import LQGDimension.Blueprint.Existence
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Gram representation of a PSD kernel on a countable set

We prove `Blueprint.Existence.CountableGramRep`: a kernel `K` on a countable type `T` which is
positive semidefinite on every finite subset is the Gram kernel of finitely supported real
sequences, `K s t = Σ_k v s k * v t k`.

Route:
1. `K` is positive semidefinite as an infinite matrix, so mathlib's reproducing kernel Hilbert
   space `RKHS.OfKernel` gives vectors `φ t` in a real inner product space `H` with
   `⟪φ s, φ t⟫ = K s t` (Moore's theorem).
2. Enumerate `T` by a surjection `e : ℕ → T` and apply Gram–Schmidt (`gramSchmidtNormed`) to
   `n ↦ φ (e n)`.  The output `g k` is orthonormal after removing zero vectors, and
   `φ (e n) ∈ span {g 0, …, g n}` while `⟪g k, φ (e n)⟫ = 0` for `k > n`.
3. `v t k := ⟪g k, φ t⟫`.

Main result: `LQGDimension.countableGramRep : Blueprint.Existence.CountableGramRep`.
-/

noncomputable section

open scoped RealInnerProductSpace
open InnerProductSpace

namespace LQGDimension

namespace CountableGram

/-! ### Expansion in an orthonormal-or-zero family -/

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A vector in the span of finitely many members of a family which is orthonormal after
removing zero vectors is the sum of its coefficients. -/
lemma cgram_eq_sum_of_mem_span (g : ℕ → E) (horth : ∀ i j, i ≠ j → ⟪g i, g j⟫ = 0)
    (hnorm : ∀ i, g i ≠ 0 → ⟪g i, g i⟫ = 1) (S : Finset ℕ) {x : E}
    (hx : x ∈ Submodule.span ℝ (g '' (S : Set ℕ))) :
    x = ∑ k ∈ S, ⟪g k, x⟫ • g k := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_coe.mp hj)]
    · by_cases h0 : g j = 0
      · simp [h0]
      · rw [hnorm j h0, one_smul]
    · intro k _ hkj
      rw [horth k j hkj, zero_smul]
  | zero => simp
  | add y z _ _ hy hz =>
    simp only [inner_add_right, add_smul, Finset.sum_add_distrib]
    rw [← hy, ← hz]
  | smul a y _ hy =>
    simp only [inner_smul_right, mul_smul]
    rw [← Finset.smul_sum, ← hy]

/-- Parseval's identity for a vector in the span of finitely many members of an
orthonormal-or-zero family. -/
lemma cgram_inner_eq_sum_of_mem_span (g : ℕ → E) (horth : ∀ i j, i ≠ j → ⟪g i, g j⟫ = 0)
    (hnorm : ∀ i, g i ≠ 0 → ⟪g i, g i⟫ = 1) (S : Finset ℕ) (y : E) {x : E}
    (hx : x ∈ Submodule.span ℝ (g '' (S : Set ℕ))) :
    ⟪y, x⟫ = ∑ k ∈ S, ⟪g k, y⟫ * ⟪g k, x⟫ := by
  conv_lhs => rw [cgram_eq_sum_of_mem_span g horth hnorm S hx]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, real_inner_comm (g k) y, mul_comm]

end Expansion

/-! ### Gram–Schmidt coefficients of a sequence -/

section GramSchmidt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma cgram_gsn_orth (u : ℕ → E) (i j : ℕ) (hij : i ≠ j) :
    ⟪gramSchmidtNormed ℝ u i, gramSchmidtNormed ℝ u j⟫ = 0 := by
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal ℝ u hij]

lemma cgram_gsn_norm (u : ℕ → E) (i : ℕ) (hi : gramSchmidtNormed ℝ u i ≠ 0) :
    ⟪gramSchmidtNormed ℝ u i, gramSchmidtNormed ℝ u i⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, gramSchmidtNormed_unit_length' hi, one_pow]

lemma cgram_gsn_inner_eq_zero (u : ℕ → E) {n k : ℕ} (hnk : n < k) :
    ⟪gramSchmidtNormed ℝ u k, u n⟫ = 0 := by
  simp [gramSchmidtNormed, inner_smul_left, gramSchmidt_inv_triangular ℝ u hnk]

lemma cgram_mem_span_gsn (u : ℕ → E) {n N : ℕ} (hnN : n ≤ N) :
    u n ∈ Submodule.span ℝ (gramSchmidtNormed ℝ u '' ((Finset.Iic N : Finset ℕ) : Set ℕ)) := by
  rw [Finset.coe_Iic, span_gramSchmidtNormed]
  exact mem_span_gramSchmidt ℝ u hnN

/-- Gram representation of a sequence of vectors by finitely supported coefficient sequences:
`⟪u m, u n⟫ = Σ_k ⟪g k, u m⟫ ⟪g k, u n⟫`, where only `k ≤ max m n` contribute. -/
lemma cgram_inner_eq_tsum (u : ℕ → E) (m n : ℕ) :
    ⟪u m, u n⟫ = ∑' k, ⟪gramSchmidtNormed ℝ u k, u m⟫ * ⟪gramSchmidtNormed ℝ u k, u n⟫ := by
  set N := max m n
  rw [tsum_eq_sum (s := Finset.Iic N)]
  · exact cgram_inner_eq_sum_of_mem_span _ (cgram_gsn_orth u) (cgram_gsn_norm u) _ _
      (cgram_mem_span_gsn u (le_max_right m n))
  · intro k hk
    have hk' : N < k := by simpa using hk
    rw [cgram_gsn_inner_eq_zero u ((le_max_left m n).trans_lt hk'), zero_mul]

end GramSchmidt

/-! ### From finite PSD to an infinite PSD matrix -/

section Kernel

universe u

variable {T : Type u} (K : T → T → ℝ)

lemma cgram_symm (hK : ∀ F : Finset T, PSDOn F K) (s t : T) : K s t = K t s := by
  classical
  have h := (hK {s, t}).isHermitian.apply (⟨s, by simp⟩ : ({s, t} : Finset T))
    (⟨t, by simp⟩ : ({s, t} : Finset T))
  simpa using h.symm

lemma cgram_sum_nonneg (hK : ∀ F : Finset T, PSDOn F K) (x : T →₀ ℝ) :
    0 ≤ x.sum fun i xi => x.sum fun j xj => xi * K i j * xj := by
  classical
  have h := (hK x.support).2 (x.subtypeDomain (· ∈ x.support))
  simp only [Matrix.of_apply, star_trivial] at h
  have hp : ∀ y ∈ x.support, y ∈ x.support := fun _ h => h
  calc (0 : ℝ) ≤ _ := h
    _ = (x.subtypeDomain (· ∈ x.support)).sum
          (fun i xi => x.sum fun j xj => xi * K i j * xj) := by
      refine Finsupp.sum_congr fun i _ => ?_
      exact Finsupp.sum_subtypeDomain_index
        (h := fun j xj => (x.subtypeDomain (· ∈ x.support)) i * K i j * xj) hp
    _ = x.sum fun i xi => x.sum fun j xj => xi * K i j * xj :=
      Finsupp.sum_subtypeDomain_index (h := fun i xi => x.sum fun j xj => xi * K i j * xj) hp

/-- The operator-valued (`ℝ →L[ℝ] ℝ`) version of the kernel, as used by `RKHS.OfKernel`. -/
def cgramOpKernel : Matrix T T (ℝ →L[ℝ] ℝ) := Matrix.of fun s t => K s t • (1 : ℝ →L[ℝ] ℝ)

lemma cgramOpKernel_posSemidef (hK : ∀ F : Finset T, PSDOn F K) :
    (cgramOpKernel K).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun vv => ?_⟩
  · ext1 i j
    simp [cgramOpKernel, Matrix.conjTranspose_apply, star_smul, cgram_symm K hK i j]
  · simp only [cgramOpKernel, Matrix.of_apply, smul_apply, one_apply_eq_self, smul_eq_mul, RCLike.inner_apply, conj_trivial,
      RCLike.re_to_real]
    refine le_of_le_of_eq (cgram_sum_nonneg K hK vv) ?_
    refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_
    rw [cgram_symm K hK j i]
    ring

/-- A kernel which is PSD on every finite subset of `T` has a feature map into a real inner
product space (the reproducing kernel Hilbert space `RKHS.OfKernel`). -/
lemma cgram_exists_feature (hK : ∀ F : Finset T, PSDOn F K) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (φ : T → H),
      ∀ s t, ⟪φ s, φ t⟫ = K s t := by
  have : Fact (cgramOpKernel K).PosSemidef := ⟨cgramOpKernel_posSemidef K hK⟩
  refine ⟨RKHS.OfKernel (cgramOpKernel K), inferInstance, inferInstance,
    fun t => RKHS.kerFun (RKHS.OfKernel (cgramOpKernel K)) t (1 : ℝ), fun s t => ?_⟩
  rw [← RKHS.kernel_inner, RKHS.OfKernel.kernel_ofKernel]
  simp only [cgramOpKernel, Matrix.of_apply, smul_apply, one_apply_eq_self, smul_eq_mul,
    RCLike.inner_apply, conj_trivial, mul_one, one_mul]
  exact cgram_symm K hK t s

end Kernel

end CountableGram

/-! ### The blueprint obligation -/

open CountableGram in
/-- **Countable Gram representation** (blueprint obligation `CountableGramRep`). -/
theorem countableGramRep : Blueprint.Existence.CountableGramRep := by
  intro T _ K hK
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨fun t => isEmptyElim t, fun t => isEmptyElim t, fun s => isEmptyElim s⟩
  obtain ⟨H, _, _, φ, hφ⟩ := cgram_exists_feature K hK
  obtain ⟨e, he⟩ := exists_surjective_nat T
  set u : ℕ → H := fun n => φ (e n) with hu
  set g : ℕ → H := gramSchmidtNormed ℝ u
  have hidx : ∀ t, u (Function.surjInv he t) = φ t := fun t => by
    simp only [hu, Function.surjInv_eq he t]
  refine ⟨fun t k => ⟪g k, φ t⟫, fun t => ⟨Function.surjInv he t + 1, fun k hk => ?_⟩,
    fun s t => ?_⟩
  · show ⟪g k, φ t⟫ = 0
    rw [← hidx t]
    exact cgram_gsn_inner_eq_zero u (Nat.lt_of_succ_le hk)
  · show ∑' k, ⟪g k, φ s⟫ * ⟪g k, φ t⟫ = K s t
    rw [← hφ s t, ← hidx s, ← hidx t]
    exact (cgram_inner_eq_tsum u _ _).symm

end LQGDimension
