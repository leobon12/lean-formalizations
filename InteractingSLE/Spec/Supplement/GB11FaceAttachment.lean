/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11FaceReal
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc

/-!
# GB11: a real-contact wall lift has a unique attachment gate

The existing cluster-set lemma applies to lifts in the CLOSED half-plane. Thus a
lifted incoming wall may have additional original-real contacts without losing its
unique limit at the attachment. No open-half-plane condition is needed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

/-- A continuous lifted incoming arc in `Hbar`, with continuous physical image,
has a unique real attachment gate when its endpoint leaves the active domain.
Both its boundedness and the gate limit follow from existing inverse-map results. -/
theorem exists_attachment_gate {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t a b : ℝ} (ht : 0 ≤ t) (hab : a < b) {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc a b)) (hβ : ContinuousOn β (Ico a b))
    (hβH : MapsTo β (Ico a b) Hbar)
    (hcomp : ∀ u ∈ Ico a b, trMap W 0 t (β u) = α u)
    (hend : α b ∉ H \ fwdHull W t) :
    ∃ q : ℝ, trMap W 0 t q = α b ∧ Tendsto β (𝓝[<] b) (𝓝 (q : ℂ)) := by
  have : (𝓝[<] b).NeBot := nhdsLT_neBot b
  obtain ⟨hFd, hFc, hFi, hFR⟩ :=
    YuanSimpleApprox.trMap_fiber_hyps hη hW hW0 (a := 0) le_rfl ht
  obtain ⟨M, hM⟩ := hη.exists_norm_extendFrom_sub_le hW hW0 ht
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  have hI : ∀ᶠ u in 𝓝[<] b, u ∈ Ico a b :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (fun _ hu => ⟨hu.1.le, hu.2⟩)
  have hbound : ∀ u ∈ Ico a b, ‖β u‖ ≤ B + M := by
    intro u hu
    have hdis := hM _ (hβH hu)
    rw [← YuanSimpleApprox.trMap_zero_left hW0 t, hcomp u hu] at hdis
    have hnorm := norm_le_norm_add_norm_sub' (β u) (α u)
    rw [norm_sub_rev] at hdis
    have hαB := hB u ⟨hu.1, hu.2.le⟩
    linarith
  have hconn : ∀ U ∈ 𝓝[<] b, ∃ S ∈ 𝓝[<] b, S ⊆ U ∧ IsPreconnected S ∧
      ContinuousOn β S := by
    intro U hU
    obtain ⟨c, hcb, hcU⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hU
    refine ⟨Ioo (max a c) b, Ioo_mem_nhdsLT (max_lt hab hcb), ?_,
      isPreconnected_Ioo, hβ.mono ?_⟩
    · exact fun u hu => hcU ⟨(le_max_right _ _).trans_lt hu.1, hu.2⟩
    · exact fun u hu => ⟨(le_max_left _ _).trans hu.1.le, hu.2⟩
  have hle : 𝓝[<] b ≤ 𝓝[Icc a b] b :=
    le_inf nhdsWithin_le_nhds (le_principal_iff.2
      (hI.mono fun _ hu => ⟨hu.1, hu.2.le⟩))
  have hFG : Tendsto (fun u => trMap W 0 t (β u)) (𝓝[<] b) (𝓝 (α b)) :=
    ((hα b ⟨hab.le, le_rfl⟩).tendsto.mono_left hle).congr'
      (hI.mono fun u hu => (hcomp u hu).symm)
  obtain ⟨ξ, hξH, hFξ, hlim⟩ :=
    YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter hFd hFc hFi hFR hconn
      (hI.mono fun _ hu => hβH hu) (hI.mono fun u hu => hbound u hu) hFG
  have hξim : ξ.im = 0 := by
    by_contra him
    have hξ : ξ ∈ H := lt_of_le_of_ne (show 0 ≤ ξ.im from hξH) (Ne.symm him)
    exact hend (hFξ ▸ Sec6.trMap_zero_mem_domain hW hW0 ht hξ)
  have hξre : (ξ.re : ℂ) = ξ := Complex.ext rfl (by simp only [Complex.ofReal_im, hξim])
  exact ⟨ξ.re, by rwa [hξre], by rwa [hξre]⟩

end InteractingSLE.Theorem14.GB11Chart
