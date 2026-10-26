import HigherDimLFPPAS.Det.CompactLocality
import HigherDimLQGMetric.Coord.RecoverySubdivision
import HigherDimLQGMetric.Metric.WeylBasic

/-!
# Deterministic recovery of an internal path
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Det

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- A finite chain bounds the internal distance between its endpoints. -/
theorem internal_le_chain (D : ContMetric d) {U : Set (Rd d)}
    (q : ℕ → Rd d) (N : ℕ) (hq : ∀ i ≤ N, q i ∈ U) :
    D.internal U (q 0) (q N) ≤
      ∑ i ∈ Finset.range N, D.internal U (q i) (q (i + 1)) := by
  induction N with
  | zero => simp [D.internal_self (hq 0 le_rfl)]
  | succ N ih =>
    calc D.internal U (q 0) (q (N + 1)) ≤
          D.internal U (q 0) (q N) + D.internal U (q N) (q (N + 1)) :=
            D.internal_triangle U (q 0) (q N) (q (N + 1))
      _ ≤ (∑ i ∈ Finset.range N, D.internal U (q i) (q (i + 1))) +
            D.internal U (q N) (q (N + 1)) := by
          exact add_le_add (ih (fun i hi => hq i (le_trans hi (Nat.le_succ N)))) le_rfl
      _ = ∑ i ∈ Finset.range (N + 1), D.internal U (q i) (q (i + 1)) := by
          rw [Finset.sum_range_succ]

/-- Recover an internal path for a target metric from a nearly minimizing path of a source
length metric. The two metrics are compared on the compact carrier, and the target internal
metric agrees locally with its global distance. -/
theorem recover_internal_upper_bound
    (A B E : ContMetric d) (hA : A.IsLength)
    {F U : Set (Rd d)} (hF : IsCompact F) (hFU : F ⊆ U)
    {α δ e τ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (he : 0 ≤ e)
    (heα : e < α / 4) (hτ : 0 < τ)
    (hEeucl : ∀ x ∈ F, ∀ y ∈ F, E.1 (x,y) < α → dist x y < δ)
    (hEA : ∀ x ∈ F, ∀ y ∈ F, E.1 (x,y) ≤ A.1 (x,y) + e)
    (hBA : ∀ x ∈ F, ∀ y ∈ F, B.1 (x,y) ≤ A.1 (x,y) + e)
    (hBlocal : ∀ x ∈ F, ∀ y ∈ F, dist x y < δ →
      B.internal U x y = ENNReal.ofReal (B.1 (x,y)))
    {x y : Rd d} (hx : x ∈ F) (hy : y ∈ F) (hfin : A.internal F x y ≠ ∞) :
    B.internal U x y ≤ ENNReal.ofReal
      ((A.internal F x y).toReal + τ +
        (((A.internal F x y).toReal + τ) / (α / 4) + 1) * e) := by
  let v : ℝ := (A.internal F x y).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hval : A.internal F x y = ENNReal.ofReal v := (ENNReal.ofReal_toReal hfin).symm
  have hlt : A.internal F x y < ENNReal.ofReal (v + τ) := by
    rw [hval]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < v + τ)).2 (by linarith)
  rw [A.internal_eq_iInf_len] at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨P, hPc, hP0, hP1, hPF, hPL⟩ := hlt
  have hPglobal : ContinuousOn (A.pt ∘ P) (Icc (0 : ℝ) 1) :=
    A.continuous_pt.comp_continuousOn hPc
  obtain ⟨γ, hγlen, hγrange⟩ := exists_path_of_curve zero_le_one hPglobal
  have hγlen' : pathLength γ = A.len P 0 1 := by
    rw [A.len_def]
    exact hγlen
  have hγlt : pathLength γ < ENNReal.ofReal (v + τ) := by
    rw [hγlen']
    exact hPL
  have hγF : ∀ t, γ t ∈ A.pt '' F := by
    intro t
    obtain ⟨s, hs, hst⟩ := hγrange (mem_range_self t)
    exact ⟨P s, hPF hs, hst⟩
  have hγfin : pathLength γ ≠ ∞ := ne_top_of_lt hγlt
  obtain ⟨Q, hQc, hunit, hQ0, hQL, hQF⟩ := A.exists_unitSpeed_of_path γ hγF hγfin
  let L : ℝ := (pathLength γ).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hLv : L < v + τ := ENNReal.toReal_lt_of_lt_ofReal hγlt
  have hs : 0 < α / 4 := by positivity
  obtain ⟨N, hN, hcount, hsteps, hsum⟩ :=
    exists_uniform_recovery_grid hL0 hs
  let grid := IccPartition.uniform (a := 0) (b := L) hL0 N hN
  let q : ℕ → Rd d := fun i => Q (grid.t i)
  have hqF : ∀ i ≤ N, q i ∈ F := by
    intro i hi
    apply hQF
    exact grid.mem_Icc hi
  have hq0 : q 0 = x := by
    dsimp [q]
    rw [grid.zero, hQ0, hP0]
  have hqN : q N = y := by
    dsimp [q, L]
    change Q (grid.t grid.n) = y
    rw [grid.last, hQL, hP1]
  have hpiece : ∀ i < N,
      B.internal U (q i) (q (i + 1)) ≤
        ENNReal.ofReal (grid.t (i + 1) - grid.t i + e) := by
    intro i hi
    have hti := grid.mem_Icc (Nat.le_of_lt hi)
    have htj := grid.mem_Icc (Nat.succ_le_of_lt hi)
    have hstep : grid.t (i + 1) - grid.t i ≤ α / 4 := hsteps i hi
    have hstep0 : 0 ≤ grid.t (i + 1) - grid.t i :=
      sub_nonneg.mpr (grid.le_t (i := i) (j := i + 1) (Nat.le_succ i)
        (Nat.succ_le_of_lt hi))
    have hlenSeg : A.len Q (grid.t i) (grid.t (i + 1)) =
        ENNReal.ofReal (grid.t (i + 1) - grid.t i) := by
      rw [A.len_def, curveLength_of_hasUnitSpeedOn hunit hti htj]
    have hAdist : A.1 (q i, q (i + 1)) ≤ grid.t (i + 1) - grid.t i := by
      have hle := A.ofReal_le_len Q (grid.le_t (i := i) (j := i + 1) (Nat.le_succ i)
        (Nat.succ_le_of_lt hi))
      rw [hlenSeg] at hle
      have hle' : ENNReal.ofReal (A.1 (q i, q (i + 1))) ≤
          ENNReal.ofReal (grid.t (i + 1) - grid.t i) := by
        simpa [q] using hle
      exact (ENNReal.ofReal_le_ofReal_iff hstep0).mp hle'
    have hEdist : E.1 (q i, q (i + 1)) < α := by
      calc E.1 (q i, q (i + 1)) ≤ A.1 (q i, q (i + 1)) + e :=
            hEA (q i) (hqF i (Nat.le_of_lt hi)) (q (i + 1))
              (hqF (i + 1) (Nat.succ_le_of_lt hi))
        _ ≤ α / 4 + e := by linarith
        _ < α := by linarith
    have hEucl := hEeucl (q i) (hqF i (Nat.le_of_lt hi))
      (q (i + 1)) (hqF (i + 1) (Nat.succ_le_of_lt hi)) hEdist
    have hBlocal' := hBlocal (q i) (hqF i (Nat.le_of_lt hi))
      (q (i + 1)) (hqF (i + 1) (Nat.succ_le_of_lt hi)) hEucl
    rw [hBlocal']
    have hBdist : B.1 (q i, q (i + 1)) ≤ grid.t (i + 1) - grid.t i + e := by
      calc B.1 (q i, q (i + 1)) ≤ A.1 (q i, q (i + 1)) + e :=
            hBA (q i) (hqF i (Nat.le_of_lt hi)) (q (i + 1))
              (hqF (i + 1) (Nat.succ_le_of_lt hi))
        _ ≤ grid.t (i + 1) - grid.t i + e := by linarith
    exact ENNReal.ofReal_le_ofReal hBdist
  have hsumPieces : ∑ i ∈ Finset.range N, B.internal U (q i) (q (i + 1)) ≤
      ENNReal.ofReal (L + (N : ℝ) * e) := by
    calc
      _ ≤ ∑ i ∈ Finset.range N,
          ENNReal.ofReal (grid.t (i + 1) - grid.t i + e) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hpiece i (Finset.mem_range.1 hi)
      _ = ENNReal.ofReal (L + (N : ℝ) * e) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.range N) (fun i hi => add_nonneg
          (sub_nonneg.mpr ((grid.step (Finset.mem_range.1 hi)).2.1)) he)]
        congr 1
        calc
          (∑ i ∈ Finset.range N,
              (grid.t (i + 1) - grid.t i + e)) =
              (∑ i ∈ Finset.range N, (grid.t (i + 1) - grid.t i)) +
                ∑ i ∈ Finset.range N, e := by
                  exact Finset.sum_add_distrib
          _ = L + (N : ℝ) * e := by rw [hsum]; simp
  have hchain := internal_le_chain B q N (fun i hi => hFU (hqF i hi))
  have hresult : B.internal U x y ≤ ENNReal.ofReal (L + (N : ℝ) * e) := by
    simpa [hq0, hqN] using hchain.trans hsumPieces
  have hcount' : (N : ℝ) ≤ L / (α / 4) + 1 := hcount
  have hLt : L / (α / 4) ≤ (v + τ) / (α / 4) :=
    div_le_div_of_nonneg_right hLv.le hs.le
  have hreal : L + (N : ℝ) * e ≤
      v + τ + ((v + τ) / (α / 4) + 1) * e := by
    have hne : (N : ℝ) * e ≤ (L / (α / 4) + 1) * e :=
      mul_le_mul_of_nonneg_right hcount' he
    nlinarith
  exact hresult.trans (ENNReal.ofReal_le_ofReal hreal)

end HigherDimLFPPAS.Det

