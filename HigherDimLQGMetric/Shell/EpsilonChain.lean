import HigherDimLQGMetric.Shell.Geom

/-!
# Finite epsilon chains in connected sets

The reflexive transitive closure below is a finite chain whose successive points lie in
the set and are less than `ε` apart. The proof uses Mathlib's connected-set induction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric Filter
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Any two points of a connected set can be joined by a finite `ε`-chain inside the set. -/
theorem connected_epsilon_chain {K : Set (Rd d)} (hK : IsConnected K)
    {ε : ℝ} (hε : 0 < ε) {x y : Rd d} (hx : x ∈ K) (hy : y ∈ K) :
    Relation.ReflTransGen (fun a b : Rd d => a ∈ K ∧ b ∈ K ∧ dist a b < ε) x y := by
  let R : Rd d → Rd d → Prop := fun a b => a ∈ K ∧ b ∈ K ∧ dist a b < ε
  change Relation.ReflTransGen R x y
  refine hK.isPreconnected.induction₂' (fun a b => Relation.ReflTransGen R a b)
    (fun a ha => ?_) (fun a b c _ _ _ hab hbc => hab.trans hbc) hx hy
  filter_upwards [inter_mem_nhdsWithin K (ball_mem_nhds a hε), self_mem_nhdsWithin]
    with b hb hbK
  have hba : dist b a < ε := mem_ball.mp hb.2
  constructor
  · exact Relation.ReflTransGen.single ⟨ha, hbK, by simpa only [dist_comm] using hba⟩
  · exact Relation.ReflTransGen.single ⟨hbK, ha, hba⟩

end HigherDimLQGMetric
