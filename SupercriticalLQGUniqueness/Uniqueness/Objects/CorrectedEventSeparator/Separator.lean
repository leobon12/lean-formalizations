import LQGMetric.Topo.Disconnect
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Normed.Module.Basic




 









set_option autoImplicit false

open Set Metric Bornology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventSeparator

 
theorem path_meets_frontier {V : Set ℂ} (hV : IsOpen V) {x y : ℂ} (γ : Path x y) (hx : x ∉ V)
    (hy : y ∈ V) : (range γ ∩ frontier V).Nonempty := by
  by_contra hem
  have hcov : range γ ⊆ V ∪ (closure V)ᶜ := by
    intro w hw
    by_cases hwV : w ∈ V
    · exact Or.inl hwV
    · refine Or.inr fun hwcl => hem ⟨w, hw, ?_⟩
      rw [hV.frontier_eq]; exact ⟨hwcl, hwV⟩
  have hdj : Disjoint V (closure V)ᶜ := Set.disjoint_left.2 fun w hw hwc => hwc (subset_closure hw)
  rcases (isPreconnected_range γ.continuous).subset_or_subset hV isClosed_closure.isOpen_compl hdj
      hcov with h | h
  · exact hx (h ⟨0, γ.source⟩)
  · exact h ⟨1, γ.target⟩ (subset_closure hy)

 
theorem frontier_component_subset {T : Set ℂ} (hT : IsClosed T) (x : ℂ) :
    frontier (connectedComponentIn Tᶜ x) ⊆ T := by
  intro p hp
  by_contra hpT
  have hopen : IsOpen (connectedComponentIn Tᶜ p) := hT.isOpen_compl.connectedComponentIn
  have hpmem : p ∈ connectedComponentIn Tᶜ p := mem_connectedComponentIn hpT
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 (frontier_subset_closure hp) _ hopen hpmem
  have hpx : p ∈ connectedComponentIn Tᶜ x := by
    rw [connectedComponentIn_eq hy2, ← connectedComponentIn_eq hy1]; exact hpmem
  rw [(hT.isOpen_compl.connectedComponentIn).frontier_eq] at hp
  exact hp.2 hpx

 
theorem path_meets_of_component {T : Set ℂ} (hT : IsClosed T) (c : ℂ) {x y : ℂ} (γ : Path x y)
    (hx : x ∉ connectedComponentIn Tᶜ c) (hy : y ∈ connectedComponentIn Tᶜ c) :
    (range γ ∩ T).Nonempty := by
  obtain ⟨w, hw, hwf⟩ := path_meets_frontier (hT.isOpen_compl.connectedComponentIn) γ hx hy
  exact ⟨w, hw, frontier_component_subset hT c hwf⟩

 


theorem ball_subset_component_subset_ball {T : Set ℂ} (hT : IsClosed T) {w : ℂ} {s : ℝ}
    (hs : 0 < s) (hTA : T ⊆ {z | s < dist z w ∧ dist z w < 2 * s})
    (hdis : LQGMetric.Disconnects T (sphere w s) (sphere w (2 * s))) :
    ball w s ⊆ connectedComponentIn Tᶜ w ∧ connectedComponentIn Tᶜ w ⊆ ball w (2 * s) := by
  have hwT : w ∉ T := fun hw => by
    have := (hTA hw).1; rw [dist_self] at this; linarith
  constructor
  · refine (convex_ball w s).isPreconnected.subset_connectedComponentIn (mem_ball_self hs) ?_
    intro z hz hzT
    have h1 := (hTA hzT).1
    rw [mem_ball] at hz
    linarith
  · intro y hy
    by_contra hyout
    have hopen : IsOpen (connectedComponentIn Tᶜ w) := hT.isOpen_compl.connectedComponentIn
    have hconn : IsConnected (connectedComponentIn Tᶜ w) :=
      isConnected_connectedComponentIn_iff.2 hwT
    have hpc : IsPathConnected (connectedComponentIn Tᶜ w) :=
      hopen.isConnected_iff_isPathConnected.1 hconn
    have hJ : JoinedIn (connectedComponentIn Tᶜ w) w y :=
      hpc.joinedIn w (mem_connectedComponentIn hwT) y hy
    obtain ⟨z, hz, hzT⟩ := (LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hdis) w y
      hJ.somePath (mem_closedBall_self hs.le) hyout
    obtain ⟨t, rfl⟩ := hz
    exact (connectedComponentIn_subset Tᶜ w (hJ.somePath_mem t)) hzT

 

theorem path_meets_union_of_cover {ι : Type*} (I : Finset ι) (T : ι → Set ℂ) (c : ι → ℂ)
    (hTc : ∀ i, IsClosed (T i)) {S : Set ℂ}
    (hcov : S ⊆ ⋃ i ∈ I, connectedComponentIn (T i)ᶜ (c i)) {x y : ℂ} (γ : Path x y)
    (hS : (range γ ∩ S).Nonempty) (hx : ∀ i ∈ I, x ∉ connectedComponentIn (T i)ᶜ (c i)) :
    (range γ ∩ ⋃ i ∈ I, T i).Nonempty := by
  obtain ⟨z, ⟨t, rfl⟩, hzS⟩ := hS
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 (hcov hzS)
  
  have h0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have hx' : γ.extend 0 ∉ connectedComponentIn (T i)ᶜ (c i) := by
    rw [Path.extend_zero]; exact hx i hi
  have hy' : γ.extend (t : ℝ) ∈ connectedComponentIn (T i)ᶜ (c i) := by
    rw [Path.extend_extends']; exact hzi
  obtain ⟨w, hw, hwT⟩ := path_meets_of_component (hTc i) (c i) (γ.truncateOfLE h0) hx' hy'
  refine ⟨w, ?_, mem_iUnion₂.2 ⟨i, hi, hwT⟩⟩
  have hsub : range (γ.truncateOfLE h0) ⊆ range γ := by
    intro v ⟨s, hs⟩
    exact γ.truncate_range ⟨s, by rw [← hs]; rfl⟩
  exact hsub hw

end SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEventSeparator

