import SupercriticalLQGUniqueness.B2.QPos.DGFFBoxDegree

 


set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
def walkVisitsThrough (k : ℕ) : Matrix V V ℝ :=
  ∑ j ∈ Finset.range k, G.killedTransition ^ j

 

theorem walkVisitsThrough_add_tail (hK : G.precision.PosDef)
    (hdegree : ∀ i, G.totalRate i = 2 / Real.pi) (k : ℕ) :
    G.walkVisitsThrough k + G.killedTransition ^ k * G.algebraicGreen =
      G.algebraicGreen := by
  have hres : (1 - G.killedTransition) * G.algebraicGreen = 1 := by
    rw [← G.algebraicKilledTransition_eq_killedTransition hdegree]
    exact G.algebraicGreen_resolvent hK
  have hstep : G.algebraicGreen = 1 + G.killedTransition * G.algebraicGreen := by
    have hh := hres
    rw [sub_mul, one_mul] at hh
    exact (sub_eq_iff_eq_add).mp hh
  induction k with
  | zero => simp [walkVisitsThrough]
  | succ k ih =>
      rw [walkVisitsThrough, Finset.sum_range_succ]
      change G.walkVisitsThrough k + G.killedTransition ^ k +
          G.killedTransition ^ (k + 1) * G.algebraicGreen = G.algebraicGreen
      rw [pow_succ]
      calc
        G.walkVisitsThrough k + G.killedTransition ^ k +
            (G.killedTransition ^ k * G.killedTransition) * G.algebraicGreen =
          G.walkVisitsThrough k + G.killedTransition ^ k *
            (1 + G.killedTransition * G.algebraicGreen) := by
              simp [mul_add, mul_assoc, add_assoc]
        _ = G.walkVisitsThrough k + G.killedTransition ^ k * G.algebraicGreen :=
          by rw [← hstep]
        _ = G.algebraicGreen := ih

 


theorem walkVisitsThrough_tendsto_green (hK : G.precision.PosDef)
    (hdegree : ∀ i, G.totalRate i = 2 / Real.pi)
    (hvanish : Tendsto (fun k : ℕ => G.killedTransition ^ k)
      atTop (𝓝 0)) :
    Tendsto G.walkVisitsThrough atTop (𝓝 G.algebraicGreen) := by
  have htail : Tendsto
      (fun k : ℕ => G.killedTransition ^ k * G.algebraicGreen)
      atTop (𝓝 0) := by
    simpa using hvanish.mul_const G.algebraicGreen
  have hsum : Tendsto
      (fun k : ℕ => G.algebraicGreen -
        G.killedTransition ^ k * G.algebraicGreen)
      atTop (𝓝 G.algebraicGreen) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := G.algebraicGreen)).sub htail
  convert hsum using 1
  funext k
  have h := G.walkVisitsThrough_add_tail hK hdegree k
  exact eq_sub_of_add_eq h

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
