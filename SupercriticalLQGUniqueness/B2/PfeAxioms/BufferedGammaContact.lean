import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaJoin

 










set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem contact_chain_internal_bound {ι : Type*}
    (E : LSCMetric) (V : Set ℂ) (K : ι → Set V) (cost : ι → ℝ≥0∞)
    (hcost : ∀ i x y, x ∈ K i → y ∈ K i →
      E.internal V (x, y) ≤ cost i)
    (i : ι) (l : List ι) (j : ι)
    (hchain : (i :: l).IsChain fun u v => (K u ∩ K v).Nonempty)
    (hlast : (i :: l).getLast (List.cons_ne_nil i l) = j)
    {x y : V} (hx : x ∈ K i) (hy : y ∈ K j) :
    E.internal V (x, y) ≤ ((i :: l).map cost).sum := by
  induction l generalizing i x with
  | nil =>
      have hij : i = j := by simpa using hlast
      subst j
      simpa using hcost i x y hx hy
  | cons k tail ih =>
      have hik : (K i ∩ K k).Nonempty := (List.isChain_cons_cons.mp hchain).1
      obtain ⟨z, hzi, hzk⟩ := hik
      have htail : (k :: tail).IsChain fun u v => (K u ∩ K v).Nonempty :=
        (List.isChain_cons_cons.mp hchain).2
      have hlast' : (k :: tail).getLast (List.cons_ne_nil k tail) = j := by
        simpa using hlast
      calc
        E.internal V (x, y) ≤ E.internal V (x, z) + E.internal V (z, y) :=
          (E.isExtMetric_internal V).2.2.2 x z y
        _ ≤ cost i + ((k :: tail).map cost).sum :=
          add_le_add (hcost i x z hx hzi) (ih k htail hlast' hzk)
        _ = ((i :: k :: tail).map cost).sum := by
          simp only [List.map_cons, List.sum_cons]

end SupercriticalLQGUniqueness.B2.PfeAxioms
