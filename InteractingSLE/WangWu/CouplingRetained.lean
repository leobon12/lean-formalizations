import InteractingSLE.WangWu.Defs

/-!
# Wang–Wu at `κ = 4`: deterministic properties of the retained domains and kernel (Lemma 3.4, parts)

Packet PROVE-WW-A. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, Lemma 3.4 (ruling R31).
The parts that need no kernel-convergence (Carathéodory) theory, for any driving path:

* **Lemma 3.4.2 (first claim)** `retainedDomain_antitone`: `U_t ⊆ U_s` for `s ≤ t`;
  `activeDomain_subset_retainedDomain`: `D_t ⊆ U_t`;
* **Lemma 3.4.3 (kernel facts)** `retainedGreen_comm` (symmetry), `retainedGreen_nonneg`,
  `retainedGreen_antitone` (the frozen kernel `G_{U_t}(a,b)` is nonincreasing in `t`: it is an infimum over the
  admissible times, which increase with `t`).

Not here (they need Carathéodory kernel convergence, `Foundations/Complex/Kernel.lean`): simple connectivity of the
components, `C(q)` equal or disjoint, boundedness of early components, "positive limiting radius ⇒ retained",
`G_{U_t} = G_C`, and the Hilbert-space form `Q_{U_t}(p,p) = ‖P_{H₀¹(U_t)} u_p‖²` behind Lemma 3.4.4 for signed `p`.
-/

set_option autoImplicit false

noncomputable section

open Set QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

/-- The hulls increase: `K_s ⊆ K_t` for `s ≤ t`. -/
theorem fwdHull_mono {W : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t) : fwdHull W s ⊆ fwdHull W t :=
  fun _ hz => ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal hst)⟩

theorem activeDomain_subset_retainedDomain (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (t : ℝ≥0) :
    H \ fwdHull (Ito.rpath w) t ⊆ retainedDomain w ζ t := subset_union_left

/-- **Lemma 3.4.2**: the retained domains decrease, `U_t ⊆ U_s` for `s ≤ t`. -/
theorem retainedDomain_antitone (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) {s t : ℝ≥0} (hst : s ≤ t) :
    retainedDomain w ζ t ⊆ retainedDomain w ζ s := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl ⟨hx.1, fun h => hx.2 (fwdHull_mono (by exact_mod_cast hst) h)⟩
  · simp only [mem_iUnion] at hx
    obtain ⟨q, hq, ⟨hqt, hqζ, hqr⟩, hxq⟩ := hx
    by_cases hqs : stopTime w ζ q ≤ s
    · right
      simp only [mem_iUnion]
      exact ⟨q, hq, ⟨hqs, hqζ, hqr⟩, hxq⟩
    · -- the component lies in the kernel domain, inside `D_s`
      push Not at hqs
      left
      have hC : retainedComponent w ζ q ⊆ kernelDomain w ζ q := by
        unfold retainedComponent
        split_ifs
        exact connectedComponentIn_subset _ _
      have hK : kernelDomain w ζ q ⊆ H \ fwdHull (Ito.rpath w) s := by
        unfold kernelDomain
        exact interior_subset.trans (iInter_subset (fun r : {r : ℝ≥0 // (r : ℝ≥0∞) < stopTime w ζ q} =>
          H \ fwdHull (Ito.rpath w) r) ⟨s, hqs⟩)
      exact hK (hC hxq)

/-- **Lemma 3.4.3**: the retained kernel is symmetric. -/
theorem retainedGreen_comm (w : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℂ) :
    retainedGreen w t a b = retainedGreen w t b a := by
  simp only [retainedGreen, K3.VT, K3.VTe_comm]

/-- **Lemma 3.4.3**: the retained kernel is nonnegative. -/
theorem retainedGreen_nonneg (w : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℂ) : 0 ≤ retainedGreen w t a b :=
  ENNReal.toReal_nonneg

/-- **Lemma 3.4.3**: the retained kernel is nonincreasing in time (an infimum over the admissible times
`{s ≤ t : s < s(a), s < s(b)}`, which increase with `t`), as long as it is finite at the earlier time. -/
theorem retainedGreen_antitone (w : ℝ≥0 → ℝ) {s t : ℝ≥0} (hst : s ≤ t) (a b : ℂ)
    (hfin : K3.VTe (Ito.rpath w) s a b ≠ ⊤) :
    retainedGreen w t a b ≤ retainedGreen w s a b := by
  unfold retainedGreen K3.VT
  refine ENNReal.toReal_mono hfin ?_
  unfold K3.VTe
  refine iInf₂_mono' fun r hr => ⟨r, ⟨hr.1, hr.2.1.trans (by exact_mod_cast hst), hr.2.2⟩, le_rfl⟩

end WangWu

end InteractingSLE
