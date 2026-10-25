import SupercriticalLQGUniqueness.B2.QPos.DGFFAlgebraicGreen

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
def totalRate (i : V) : ℝ := G.boundary i + ∑ j, G.edge i j

 
def killedTransition : Matrix V V ℝ := fun i j => G.edge i j / G.totalRate i

theorem precision_eq_totalRate_sub_edge (i j : V) :
    G.precision i j = (if i = j then G.totalRate i else 0) - G.edge i j := by
  by_cases h : i = j
  · subst j
    simp [precision, totalRate, G.edge_self]
  · simp [precision, h]

theorem precision_eq_rate_mul_transition (r : ℝ)
    (hr : ∀ i, G.totalRate i = r) :
    G.precision = r • (1 - G.killedTransition) := by
  ext i j
  rw [G.precision_eq_totalRate_sub_edge, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp [killedTransition, G.edge_self, hr]
  · simp [hij, killedTransition, hr]
    by_cases hr0 : r = 0
    · have he : G.edge i j = 0 := by
        have hb := G.boundary_nonneg i
        have he' := G.edge_nonneg i j
        have hs : G.edge i j ≤ ∑ k : V, G.edge i k :=
          Finset.single_le_sum (fun k _ => G.edge_nonneg i k) (Finset.mem_univ j)
        have hrate := hr i
        dsimp [totalRate] at hrate
        linarith
      simp [hr0, he]
    · field_simp

 

theorem algebraicKilledTransition_eq_killedTransition
    (hdegree : ∀ i, G.totalRate i = 2 / Real.pi) :
    G.algebraicKilledTransition = G.killedTransition := by
  rw [algebraicKilledTransition,
    G.precision_eq_rate_mul_transition (2 / Real.pi) hdegree]
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hc : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp
  rw [smul_smul, hc, one_smul, sub_sub_cancel]

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
