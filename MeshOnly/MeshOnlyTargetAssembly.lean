import MeshOnly.MeshOnlyStatement
import BouRabeeGwynne.CoordinateHyperplane

/-! Recover the individual-function clause from the uniform-family clause. -/

open scoped Classical Topology

namespace BouRabeeGwynne

/-- The uniform-family conclusion includes every individual harmonic datum:
compactness supplies its finite C² bound on a smaller fixed neighborhood.
This lemma is an assembly step; it assumes, rather than proves, the new
uniform mesh-only convergence estimate. -/
theorem dirichletApproximation_of_uniformMeshOnly {d : ℕ} (hd : 1 ≤ d)
    (G : TilingSequence d) (U : Set (Euc d))
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain)
    (hmesh : G.MeshConverges) (huniform : UniformMeshOnlyDirichletTarget G U)
    (h : Euc d → ℝ) (hh : HarmonicNearClosure h U) :
    DirichletApproximationTarget G U h (fun n v => h ((G.tiling n).pos v)) := by
  obtain ⟨e, he⟩ : ∃ e : Euc d, e ≠ 0 := by
    cases d with
    | zero => omega
    | succ n =>
      exact ⟨coordinateAxis (0 : Fin (n + 1)), coordinateAxis_ne_zero 0⟩
  have hwell := G.eventually_uniqueDirichletExtension hd e he hmesh hU hUD
  refine ⟨?_, ?_⟩
  · filter_upwards [hwell] with n hn
    exact ⟨hn.1, hn.2 _⟩
  obtain ⟨Q, W, ρ, M, hρ, hM, hQc, hW, hhW, hUQ, hQW, hQD, hthick, huc, hH⟩ :=
    hh.exists_compact_collar hU hUD
  obtain ⟨H, hval⟩ := hQc.exists_bound_of_continuousOn
    (hhW.contDiffOn.continuousOn.mono hQW)
  have hfirst : ContinuousOn (fderiv ℝ h) Q :=
    (hhW.contDiffOn.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hQW
  obtain ⟨L, hderiv⟩ := hQc.exists_bound_of_continuousOn hfirst
  let C := max H 0 + max L 0 + max M 0
  have hHle : H ≤ C := by
    dsimp [C]
    linarith [le_max_left H 0, le_max_right L 0, le_max_right M 0]
  have hLle : L ≤ C := by
    dsimp [C]
    linarith [le_max_right H 0, le_max_left L 0, le_max_right M 0]
  have hMle : M ≤ C := by
    dsimp [C]
    linarith [le_max_right H 0, le_max_right L 0, le_max_left M 0]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsmallW : interior Q ⊆ W := interior_subset.trans hQW
  have hhsmall : IsHarmonicOn h (interior Q) :=
    ⟨hhW.contDiffOn.mono hsmallW, fun x hx => hhW.2 x (hsmallW hx)⟩
  have hbound : C2BoundOn h (interior Q) C := by
    intro x hx
    have hxQ : x ∈ Q := interior_subset hx
    refine ⟨?_, (hderiv x hxQ).trans hLle, (hH x hxQ).trans hMle⟩
    simpa only [Real.norm_eq_abs] using (hval x hxQ).trans hHle
  intro η hη
  filter_upwards [huniform (interior Q) isOpen_interior hUQ C hC η hη] with n hn
  exact hn h hhsmall hbound

end BouRabeeGwynne
