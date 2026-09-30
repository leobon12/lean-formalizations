import QuantumZipper.Proofs.GFF.K3.MixedM7Local
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# K3-mixed M7-c, step 2: the joint Hilbert space of the coupling

Let `K̂ := closure span {v̂_μ − v̂_{bal μ} : μ local}` in `HkE` (the free local part) and let
`J : K̂ →ₗᵢ GradSpace D` be a linear isometry with `J (v̂_μ − v̂_{bal μ}) = v_μ − v_{bal μ}` and range
in the closed span of the mixed local generators (`exists_localIsometry`, given M7-a). On
`E := GradSpace D × HkE` (`L²` product) put

* `jointMixed μ := (v_μ, 0)` (the mixed field),
* `jointFree μ := (J (P̂ v̂_μ), v̂_μ − P̂ v̂_μ)` (the free field; `P̂` the projection onto `K̂`).

Results (all unconditional in `J`, except where the hypotheses on `J` are listed):

* `inner_jointMixed`: `⟪jointMixed μ, jointMixed ν⟫ = ⟪v_μ, v_ν⟫` (`= dualCov`);
* `inner_jointFree`: `⟪jointFree μ, jointFree ν⟫ = ⟪v̂_μ, v̂_ν⟫` (so the free Gram matrix,
  `kernelCov2 neumannH` on balanced pairs, is preserved);
* `inner_xi_jointFree`: a vector `(u, 0)` with `u` orthogonal to the mixed local part is
  orthogonal to every `jointFree ν` (this makes `Ξ` independent of `X`);
* `jointMixed_sub_jointFree_local`: for local `μ` and an admissible `ρ` of the same mass giving no
  mass to `ball t r`, `jointMixed μ − (jointFree μ − jointFree ρ) = (v_{bal μ}, −(v̂_{bal μ} − v̂_ρ))`
  — the Hilbert-level form of the coupling identity `Y μ − (X μ − X ρ) = (harmonic part)`.

Own construction (Hilbert-space form of the domain Markov property, Sheffield (2007) Thm 2.17).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace QuantumZipper.K3

open GFFExist

variable {t r r' : ℝ}

/-- The free local part `K̂ = closure span {v̂_μ − v̂_{bal μ}}`. -/
abbrev freeLocSpace (hr : 0 < r) (hr'r : r' < r) : Submodule ℝ HkE :=
  (Submodule.span ℝ (Set.range (freeLocVec (t := t) hr hr'r))).topologicalClosure

/-- The mixed field's vector in the joint space. -/
def jointMixed (D : Set ℂ) (c d : ℝ) (μ : Measure ℂ) : WithLp 2 (GradSpace D × HkE) :=
  WithLp.toLp 2 (rieszVec D (mixedSpace D (realSet (Set.Icc c d))) μ, 0)

/-- The free field's vector in the joint space. -/
def jointFree {D : Set ℂ} (hr : 0 < r) (hr'r : r' < r)
    (J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D) (x : HkE) :
    WithLp 2 (GradSpace D × HkE) :=
  WithLp.toLp 2 (J ((freeLocSpace (t := t) hr hr'r).orthogonalProjectionOnto x),
    x - (freeLocSpace (t := t) hr hr'r).starProjection x)

theorem inner_jointMixed (D : Set ℂ) (c d : ℝ) (μ ν : Measure ℂ) :
    ⟪jointMixed D c d μ, jointMixed D c d ν⟫ =
      ⟪rieszVec D (mixedSpace D (realSet (Set.Icc c d))) μ,
        rieszVec D (mixedSpace D (realSet (Set.Icc c d))) ν⟫ := by
  simp [jointMixed]

/-- The free Gram matrix is preserved. -/
theorem inner_jointFree {D : Set ℂ} (hr : 0 < r) (hr'r : r' < r)
    (J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D) (x y : HkE) :
    ⟪jointFree hr hr'r J x, jointFree hr hr'r J y⟫ = ⟪x, y⟫ := by
  rw [inner_eq_inner_proj_add_inner_sub_proj (freeLocSpace (t := t) hr hr'r) x y]
  simp only [jointFree, WithLp.prod_inner_apply, LinearIsometry.inner_map_map]

/-- `jointFree` is linear. -/
theorem jointFree_sub {D : Set ℂ} (hr : 0 < r) (hr'r : r' < r)
    (J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D) (x y : HkE) :
    jointFree hr hr'r J x - jointFree hr hr'r J y = jointFree hr hr'r J (x - y) := by
  simp only [jointFree, map_sub]
  rw [← WithLp.toLp_sub, Prod.mk_sub_mk]
  refine congrArg (WithLp.toLp 2) (Prod.ext rfl ?_)
  simp only
  abel

/-- Vectors `(u, 0)` with `u` orthogonal to the range of `J` are orthogonal to the free field. -/
theorem inner_xi_jointFree {D : Set ℂ} (hr : 0 < r) (hr'r : r' < r)
    (J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D) {u : GradSpace D}
    (hu : ∀ k, ⟪u, J k⟫ = 0) (x : HkE) :
    ⟪WithLp.toLp 2 (u, (0 : HkE)), jointFree hr hr'r J x⟫ = 0 := by
  simp [jointFree, hu]

/-- **Hilbert-level coupling identity.** For local `μ` and an admissible `ρ` with the same mass,
giving no mass to `ball t r`:
`jointMixed μ − (jointFree v̂_μ − jointFree v̂_ρ) = (v_{bal μ}, −(v̂_{bal μ} − v̂_ρ))`. -/
theorem jointMixed_sub_jointFree_local {D : Set ℂ} {c d : ℝ} (hr : 0 < r) (hr'r : r' < r)
    (J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D)
    (hJ : ∀ μ : LocIdx t r', J ⟨freeLocVec hr hr'r μ,
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)⟩ =
          mixedLocVec D c d t r μ.1)
    (μ : LocIdx t r') {ρ : Measure ℂ} (hρ : IsAdmissibleH ρ) (hρB : ρ (ball (t : ℂ) r) = 0)
    (hm : μ.1 Set.univ = ρ Set.univ) :
    jointMixed D c d μ.1 -
        (jointFree hr hr'r J (freeVec ⟨μ.1, μ.2.1⟩) - jointFree hr hr'r J (freeVec ⟨ρ, hρ⟩)) =
      WithLp.toLp 2 (rieszVec D (mixedSpace D (realSet (Set.Icc c d))) (bal t r μ.1),
        -(freeVec ⟨bal t r μ.1, μ.bal_adm hr hr'r⟩ - freeVec ⟨ρ, hρ⟩)) := by
  set K := freeLocSpace (t := t) hr hr'r with hK
  set xb := freeVec ⟨bal t r μ.1, μ.bal_adm hr hr'r⟩ - freeVec ⟨ρ, hρ⟩ with hxb
  have hmem : freeLocVec hr hr'r μ ∈ K :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)
  have hbal : bal t r μ.1 Set.univ = ρ Set.univ := by
    rw [bal_univ hr hr'r μ.2.2]; exact hm
  have horth : xb ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    exact inner_eq_zero_of_mem_closure_span_of_forall (fun ν =>
      inner_freeVec_sub_freeLocVec_eq_zero hr hr'r (μ.bal_adm hr hr'r) hρ hbal (bal_ball hr)
        hρB ν) hu
  have hsplit : freeVec ⟨μ.1, μ.2.1⟩ - freeVec ⟨ρ, hρ⟩ = freeLocVec hr hr'r μ + xb := by
    simp only [freeLocVec, hxb]; abel
  have hP : K.orthogonalProjectionOnto (freeVec ⟨μ.1, μ.2.1⟩ - freeVec ⟨ρ, hρ⟩) =
      ⟨freeLocVec hr hr'r μ, hmem⟩ := by
    rw [hsplit, map_add, Submodule.orthogonalProjectionOnto_eq_zero_iff.2 horth, add_zero]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := K) ⟨_, hmem⟩
  have hPs : K.starProjection (freeVec ⟨μ.1, μ.2.1⟩ - freeVec ⟨ρ, hρ⟩) = freeLocVec hr hr'r μ := by
    rw [Submodule.starProjection_apply, hP]
  rw [jointFree_sub, jointMixed, jointFree, hP, hPs, hJ μ, ← WithLp.toLp_sub]
  congr 1
  ext
  · simp [mixedLocVec]
  · simp [hsplit]
