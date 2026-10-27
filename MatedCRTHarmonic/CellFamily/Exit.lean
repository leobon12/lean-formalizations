import MatedCRTHarmonic.CellFamily.Interfaces
import MatedCRTHarmonic.GMS3.Walk

/-!
# Finite annular exit from the graph-connectivity interface

the waypoint construction uses that the mated-CRT graph is connected and infinite to show that the walk exits a finite annulus
almost surely. `GraphConnected` is the named interface; the vertex set here is `ℤ`, hence infinite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic

/-- In a connected graph on `ℤ`, simple random walk exits any finite vertex set almost surely. -/
theorem walkLaw_hitTime_compl_ne_top_of_connected {E : Type*} {G : LFMultigraph ℤ E} {U : Set ℤ}
    (hU : U.Finite) (hconn : G.adj.Connected) (x : ℤ) :
    G.walkLaw x {ω | Markov.hitTime Uᶜ (G.vertexPath ω) ≠ ⊤} = 1 := by
  exact GMS3.walkLaw_hitTime_compl_ne_top G hU (by
    intro v hv
    obtain ⟨y, hy⟩ := hU.exists_notMem
    exact ⟨y, hy, hconn.preconnected v y⟩) x

end MatedCRTHarmonic.CellFamily
