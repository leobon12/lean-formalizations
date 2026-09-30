import QuantumZipper.Proofs.GFF.K3.MixedM7Nodes
import QuantumZipper.Proofs.GFF.K3.MixedM7Gram
import QuantumZipper.Proofs.GFF.K3.DualNorm
import QuantumZipper.Proofs.GFF.Existence
import QuantumZipper.Proofs.GFF.Admissible

/-!
# K3-mixed M7-c, step 1: the local parts of the mixed and free Hilbert spaces are isometric

For a half-disc `ball t r ∩ H ⊆ D` on the free arc and `0 < r' < r`, index the local measures by
`LocIdx t r'` (admissible, carried by `closedBall t r'`). The local generators are

* mixed: `mixedLocVec μ = v_μ − v_{bal μ}` in `GradSpace D` (`v = rieszVec D V`,
  `V = mixedSpace D (realSet (Icc c d))`);
* free: `freeLocVec μ = v̂_μ − v̂_{bal μ}` in `HkE` (`v̂ = GFFExist.freeVec`).

Results:

* `inner_freeLocVec`: the free Gram matrix is `kernelCov (halfDiscGreen t r)` (the kernel
  computation of L2, `covariance_markovZ`, at the Hilbert level);
* `inner_mixedLocVec`: under M7-a (`MixedHalfDiscMarkovCovStmt`), the mixed Gram matrix is the
  same;
* `exists_localIsometry`: hence (Gram isometry, `MixedM7Gram.lean`) a linear isometry from the
  closed span of the free generators into `GradSpace D` sending `freeLocVec μ ↦ mixedLocVec μ`.

This is the identification `J` of the local parts used in the M7-c assembly
(`MixedM7Nodes.lean`, proof plan). Own construction; the underlying fact is Sheffield (2007)
Thm 2.17 (the local part `H_U` of the Dirichlet space depends only on `U`).
-/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace QuantumZipper.K3

open GFFExist

/-- Local measures: admissible and carried by `closedBall t r'`. -/
abbrev LocIdx (t r' : ℝ) := {μ : Measure ℂ // IsAdmissibleH μ ∧ μ (closedBall (t : ℂ) r')ᶜ = 0}

/-- The balayage of a local measure is admissible. -/
theorem LocIdx.bal_adm {t r r' : ℝ} (hr : 0 < r) (hr'r : r' < r) (μ : LocIdx t r') :
    IsAdmissibleH (bal t r μ.1) := by
  have := μ.2.1.1
  exact isAdmissibleH_bal hr hr'r μ.2.2

/-- The free local generator `v̂_μ − v̂_{bal μ}`. -/
def freeLocVec {t r r' : ℝ} (hr : 0 < r) (hr'r : r' < r) (μ : LocIdx t r') : HkE :=
  freeVec ⟨μ.1, μ.2.1⟩ - freeVec ⟨bal t r μ.1, μ.bal_adm hr hr'r⟩

/-- The mixed local generator `v_μ − v_{bal μ}`. -/
def mixedLocVec (D : Set ℂ) (c d t r : ℝ) (μ : Measure ℂ) : GradSpace D :=
  rieszVec D (mixedSpace D (realSet (Set.Icc c d))) μ -
    rieszVec D (mixedSpace D (realSet (Set.Icc c d))) (bal t r μ)

/-- **Free local Gram matrix** = `kernelCov (halfDiscGreen t r)`. -/
theorem inner_freeLocVec {t r r' : ℝ} (hr : 0 < r) (hr'r : r' < r) (μ ν : LocIdx t r') :
    ⟪freeLocVec hr hr'r μ, freeLocVec hr hr'r ν⟫ = kernelCov (halfDiscGreen t r) μ.1 ν.1 := by
  have hμl : IsLocalH t r μ.1 := ⟨μ.2.1, r', hr'r, μ.2.2⟩
  have hνl : IsLocalH t r ν.1 := ⟨ν.2.1, r', hr'r, ν.2.2⟩
  have hc := freeVec_inner ⟨μ.1, μ.2.1⟩ ⟨bal t r μ.1, μ.bal_adm hr hr'r⟩ ⟨ν.1, ν.2.1⟩
    ⟨bal t r ν.1, ν.bal_adm hr hr'r⟩ (hμl.bal_spec hr).2 (hνl.bal_spec hr).2
  simp only [freeLocVec]
  rw [hc]
  obtain ⟨r₁, hr₁, hμr, R₁, hR₁, hμR⟩ := local_data hr hμl
  obtain ⟨r₂, hr₂, hνr, R₂, hR₂, hνR⟩ := local_data hr hνl
  set R := max R₁ R₂
  have hμR' := compl_ballH_null_mono (le_max_left R₁ R₂) hμR
  have hνR' := compl_ballH_null_mono (le_max_right R₁ R₂) hνR
  have hRt : |t| + r ≤ R := hR₁.trans (le_max_left _ _)
  have := μ.2.1.1
  have := ν.2.1.1
  have := isFiniteMeasure_bal hr hr₂ hνr
  obtain ⟨Cν, hCν, hνP⟩ := ν.2.1.2.2
  have e1 := kernelCov_bal_left (μ := μ.1) hr hr₁ hμr hRt (bal_ballH_compl (μ := ν.1) hr hRt)
    (ENNReal.mul_ne_top (measure_ne_top ν.1 _) (potC_ne_top r r₂)) (bal_pot_le hr hr₂ hνr)
    (bal_ball hr)
  have e2 := kernelCov_halfDiscGreen hr hr₁ hμr hRt hμR' hνR' hCν.ne hνP
  simp only [kernelCov2]
  rw [e1, e2]
  ring

/-- `kernelCov neumannH` is symmetric on admissible measures (as
`kernelCov_comm_of_admissible` in `CoordChangeKernel.lean`, not imported here). -/
theorem _root_.QuantumZipper.kernelCov_comm_of_admissible_k3 {μ ν : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) :
    kernelCov neumannH μ ν = kernelCov neumannH ν μ := by
  have := hμ.1; have := hν.1
  unfold kernelCov
  rw [integral_integral_swap (QuantumZipper.integrable_neumannH_prod hμ hν)]
  simp_rw [neumannH_symm]

/-- `dualCov` is symmetric. -/
theorem dualCov_comm_k3 (D : Set ℂ) (V : Set (ℂ → ℝ)) (μ ν : Measure ℂ) :
    dualCov D V μ ν = dualCov D V ν μ := by
  unfold dualCov
  rw [add_comm μ ν]
  ring

/-- **Mixed local Gram matrix** = `kernelCov (halfDiscGreen t r)`, given M7-a. -/
theorem inner_mixedLocVec {D : Set ℂ} {c d t r r' : ℝ}
    (hA : MixedHalfDiscMarkovCovStmt D c d t r r') (hgeom : Prop16Geometry D c d)
    (ht : t ∈ Set.Ioo c d) (hr' : 0 < r') (hr'r : r' < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D)
    (μ ν : LocIdx t r') :
    ⟪mixedLocVec D c d t r μ.1, mixedLocVec D c d t r ν.1⟫ =
      kernelCov (halfDiscGreen t r) μ.1 ν.1 := by
  have hr : 0 < r := hr'.trans hr'r
  set V := mixedSpace D (realSet (Set.Icc c d)) with hV
  have hDN : IsDNSpace D V := isDNSpace_mixedSpace D _
  obtain ⟨hμA, hμbA, hμo, hμc⟩ := (hA hgeom ht hr' hr'r hsub).2 μ.1 μ.2.1 μ.2.2
  obtain ⟨hνA, hνbA, hνo, -⟩ := (hA hgeom ht hr' hr'r hsub).2 ν.1 ν.2.1 ν.2.2
  simp only [mixedLocVec, inner_sub_left, inner_sub_right]
  rw [← dualCov_eq_inner_rieszVec hDN hμA hνA, ← dualCov_eq_inner_rieszVec hDN hμA hνbA,
    ← dualCov_eq_inner_rieszVec hDN hμbA hνA, ← dualCov_eq_inner_rieszVec hDN hμbA hνbA,
    hμo _ hνbA (bal_ball hr), dualCov_comm_k3 D V (bal t r μ.1) ν.1,
    hνo _ hμbA (bal_ball hr), dualCov_comm_k3 D V (bal t r ν.1) (bal t r μ.1),
    hμc ν.1 ν.2.1 ν.2.2]
  ring

/-- **Local isometry `J`** (given M7-a): a linear isometry from the closed span of the free local
generators into `GradSpace D` with `J (v̂_μ − v̂_{bal μ}) = v_μ − v_{bal μ}` for every local
`μ`. -/
theorem exists_localIsometry {D : Set ℂ} {c d t r r' : ℝ}
    (hA : MixedHalfDiscMarkovCovStmt D c d t r r') (hgeom : Prop16Geometry D c d)
    (ht : t ∈ Set.Ioo c d) (hr' : 0 < r') (hr'r : r' < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) :
    ∃ J : (Submodule.span ℝ (Set.range (freeLocVec (hr'.trans hr'r) hr'r :
        LocIdx t r' → HkE))).topologicalClosure →ₗᵢ[ℝ] GradSpace D,
      (∀ μ : LocIdx t r', J ⟨freeLocVec (hr'.trans hr'r) hr'r μ,
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)⟩ =
          mixedLocVec D c d t r μ.1) ∧
      ∀ x, J x ∈ (Submodule.span ℝ (Set.range fun μ : LocIdx t r' =>
        mixedLocVec D c d t r μ.1)).topologicalClosure :=
  exists_linearIsometry_closure_of_gram _ _ fun μ ν => by
    rw [inner_freeLocVec, inner_mixedLocVec hA hgeom ht hr' hr'r hsub]

/-- **Outside measures are orthogonal to the mixed local part** (given M7-a): for a `V`-admissible
`ρ` giving no mass to `ball t r` (e.g. `ρ = P_z`, `z ∈ closedBall t r' ∩ Hbar`),
`⟪v_ρ, v_ν − v_{bal ν}⟫ = 0` for every local `ν`. -/
theorem inner_rieszVec_mixedLocVec_eq_zero {D : Set ℂ} {c d t r r' : ℝ}
    (hA : MixedHalfDiscMarkovCovStmt D c d t r r') (hgeom : Prop16Geometry D c d)
    (ht : t ∈ Set.Ioo c d) (hr' : 0 < r') (hr'r : r' < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D)
    {ρ : Measure ℂ} (hρ : IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) ρ)
    (hρB : ρ (ball (t : ℂ) r) = 0) (ν : LocIdx t r') :
    ⟪rieszVec D (mixedSpace D (realSet (Set.Icc c d))) ρ, mixedLocVec D c d t r ν.1⟫ = 0 := by
  set V := mixedSpace D (realSet (Set.Icc c d)) with hV
  have hDN : IsDNSpace D V := isDNSpace_mixedSpace D _
  obtain ⟨hνA, hνbA, hνo, -⟩ := (hA hgeom ht hr' hr'r hsub).2 ν.1 ν.2.1 ν.2.2
  simp only [mixedLocVec, inner_sub_right]
  rw [← dualCov_eq_inner_rieszVec hDN hρ hνA, ← dualCov_eq_inner_rieszVec hDN hρ hνbA,
    dualCov_comm_k3 D V ρ ν.1, dualCov_comm_k3 D V ρ (bal t r ν.1), hνo ρ hρ hρB, sub_self]

/-- Balayage of a local `ν` does not change its `neumannH`-pairing with an admissible `ρ` giving no
mass to `ball t r` (from `kernelCov_bal_left` and symmetry). -/
theorem kernelCov_neumannH_bal_right {t r r' : ℝ} (hr : 0 < r) (hr'r : r' < r) (ν : LocIdx t r')
    {ρ : Measure ℂ} (hρ : IsAdmissibleH ρ) (hρB : ρ (ball (t : ℂ) r) = 0) :
    kernelCov neumannH ρ (bal t r ν.1) = kernelCov neumannH ρ ν.1 := by
  have := ν.2.1.1
  have := hρ.1
  obtain ⟨R₀, hR₀⟩ := exists_ballH_of_admissible hρ
  obtain ⟨C, hC, hρP⟩ := hρ.2.2
  rw [QuantumZipper.kernelCov_comm_of_admissible_k3 hρ (ν.bal_adm hr hr'r),
    kernelCov_bal_left (μ := ν.1) hr hr'r ν.2.2 (le_max_right R₀ (|t| + r))
      (compl_ballH_null_mono (le_max_left _ _) hR₀) hC.ne hρP hρB,
    QuantumZipper.kernelCov_comm_of_admissible_k3 ν.2.1 hρ]

/-- **Outside balanced pairs are orthogonal to the free local part**: for admissible `ρ, ρ'` of
equal mass giving no mass to `ball t r`, `⟪v̂_ρ − v̂_ρ', v̂_ν − v̂_{bal ν}⟫ = 0`. -/
theorem inner_freeVec_sub_freeLocVec_eq_zero {t r r' : ℝ} (hr : 0 < r) (hr'r : r' < r)
    {ρ ρ' : Measure ℂ} (hρ : IsAdmissibleH ρ) (hρ' : IsAdmissibleH ρ')
    (hm : ρ Set.univ = ρ' Set.univ) (hρB : ρ (ball (t : ℂ) r) = 0)
    (hρ'B : ρ' (ball (t : ℂ) r) = 0) (ν : LocIdx t r') :
    ⟪freeVec ⟨ρ, hρ⟩ - freeVec ⟨ρ', hρ'⟩, freeLocVec hr hr'r ν⟫ = 0 := by
  have hνl : IsLocalH t r ν.1 := ⟨ν.2.1, r', hr'r, ν.2.2⟩
  simp only [freeLocVec]
  rw [freeVec_inner ⟨ρ, hρ⟩ ⟨ρ', hρ'⟩ ⟨ν.1, ν.2.1⟩ ⟨bal t r ν.1, ν.bal_adm hr hr'r⟩ hm
    (hνl.bal_spec hr).2]
  simp only [kernelCov2]
  rw [kernelCov_neumannH_bal_right hr hr'r ν hρ hρB, kernelCov_neumannH_bal_right hr hr'r ν hρ' hρ'B]
  ring

/-- A vector orthogonal to every mixed local generator is orthogonal to the closed span of the
generators (hence to the range of the local isometry `J`). -/
theorem inner_eq_zero_of_mem_closure_span_mixedLocVec {D : Set ℂ} {c d t r r' : ℝ}
    {v : GradSpace D} (hv : ∀ ν : LocIdx t r', ⟪v, mixedLocVec D c d t r ν.1⟫ = 0)
    {u : GradSpace D} (hu : u ∈ (Submodule.span ℝ (Set.range fun μ : LocIdx t r' =>
        mixedLocVec D c d t r μ.1)).topologicalClosure) : ⟪v, u⟫ = 0 := by
  have hcl : IsClosed {u : GradSpace D | ⟪v, u⟫ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hspan : ∀ u ∈ Submodule.span ℝ (Set.range fun μ : LocIdx t r' =>
      mixedLocVec D c d t r μ.1), ⟪v, u⟫ = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨ν, rfl⟩ := hx; exact hv ν
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_right, hx, mul_zero]
  exact closure_minimal hspan hcl hu

end QuantumZipper.K3
