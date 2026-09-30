import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopComp
import QuantumZipper.Proofs.Zipper.FieldLawler2Circ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-ARC (A1): the `D`-side arc of an image crosscut inside `Z_t(H_t ∩ C_ε)`

Task FL4-ARC (Track A round 4), towards `FieldLawler.FLImageSumBoundStmt`
(`FieldLawlerSubSum.lean`).

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015)
no. 10, arXiv:1407.3314, proof of Prop. 3.4 (p. 9): "`H_t ∩ C_ε = ⋃ⱼ ηⱼ`, the `ηⱼ` crosscuts of
`H_t`, and `Z_t ηⱼ` crosscuts of `ℍ`". Here the converse direction: a crosscut `η` of `ℍ` with
`η ⊆ Z_t(C_ε)` is `Z_t` of a whole maximal arc `{ε e^{iθ} : α < θ < β}` of `H_t ∩ C_ε`
(`fl4_arc_angles`). FL use it without comment; own elementary argument (1-dimensional invariance
of domain via `ContinuousOn.strictMonoOn_of_injOn_Ioo`, a clopen argument in the component of the
angle set `flO`, and the fact that the ends of `η` are real while `Z_t` maps `H_t` into `ℍ`).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- 1-dimensional invariance of domain: a continuous injective real function maps an open
interval onto an open set. -/
theorem fl4_isOpen_image_Ioo {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (hi : InjOn f (Ioo a b)) : IsOpen (f '' Ioo a b) := by
  rcases lt_or_ge a b with hab | hab
  swap
  · rw [Ioo_eq_empty (not_lt.2 hab), image_empty]; exact isOpen_empty
  have key : ∀ g : ℝ → ℝ, ContinuousOn g (Ioo a b) → StrictMonoOn g (Ioo a b) →
      IsOpen (g '' Ioo a b) := by
    intro g hg hm
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨s, hs, rfl⟩
    set s₁ := (a + s) / 2
    set s₂ := (s + b) / 2
    have h1 : a < s₁ := by simp only [s₁]; linarith [hs.1]
    have h2 : s₁ < s := by simp only [s₁]; linarith [hs.1]
    have h3 : s < s₂ := by simp only [s₂]; linarith [hs.2]
    have h4 : s₂ < b := by simp only [s₂]; linarith [hs.2]
    have hsub : Icc s₁ s₂ ⊆ Ioo a b := fun x hx => ⟨h1.trans_le hx.1, hx.2.trans_lt h4⟩
    have himg := ContinuousOn.image_Ioo_of_strictMonoOn (h2.trans h3).le (hg.mono hsub)
      (hm.mono hsub)
    refine Filter.mem_of_superset (Ioo_mem_nhds (hm ⟨h1, h2.trans hs.2⟩ hs h2)
      (hm hs ⟨hs.1.trans h3, h4⟩ h3)) ?_
    rw [← himg]
    exact image_mono fun x hx => ⟨h1.trans hx.1, hx.2.trans h4⟩
  rcases hf.strictMonoOn_of_injOn_Ioo hab hi with hm | hm
  · exact key f hf hm
  · have := key (fun x => -f x) hf.neg (fun x hx y hy hxy => neg_lt_neg (hm hx hy hxy))
    have e : f '' Ioo a b = (fun y : ℝ => -y) '' ((fun x => -f x) '' Ioo a b) := by
      rw [image_image]; simp
    rw [e]
    exact (Homeomorph.neg ℝ).isOpenMap _ this

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

lemma fl4_arg_flCirc {ε θ : ℝ} (hε : 0 < ε) (hθ : θ ∈ Ioo 0 π) : arg (flCirc ε θ) = θ := by
  unfold flCirc
  rw [arg_real_mul _ hε, exp_mul_I]
  exact arg_cos_add_sin_mul_I ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩

/-- **(A1)** The `D`-side of an image crosscut inside `Z_t(C_ε)` is a whole maximal arc of
`D ∩ C_ε`, `D = H_t = ℍ \ K_t`. -/
theorem fl4_arc_angles (hc : SideCtx W t F) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} {a b : ℝ}
    (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hsub : arcH η ⊆ {p | ‖fwdMapInv W t p‖ = ε}) :
    ∃ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ π ∧
      fwdMapInv W t '' arcH η = flCircArc ε α β ∧
      flCirc ε α ∉ H \ fwdHull W t ∧ flCirc ε β ∉ H \ fwdHull W t := by
  set D := H \ fwdHull W t with hD
  have hDo : IsOpen D := hc.isOpen_dom
  have hDH : D ⊆ H := sdiff_subset
  have hHb : H ⊆ Hbar := fun z hz => by show (0 : ℝ) ≤ z.im; exact le_of_lt hz
  obtain ⟨hηc, hηi, hηH, -, -⟩ := hη
  set g : ℝ → ℂ := fun s => F (η s) with hg
  have hgD : ∀ s ∈ Ioo (0 : ℝ) 1, g s ∈ D := fun s hs => hc.F_mem_dom (hηH hs)
  have hgn : ∀ s ∈ Ioo (0 : ℝ) 1, ‖g s‖ = ε := fun s hs => by
    have := hsub ⟨s, hs, rfl⟩
    simp only [mem_setOf_eq] at this
    simp only [hg, hc.Feq (hηH hs)]; exact this
  have hgc : ContinuousOn g (Ioo 0 1) :=
    hc.Fcont.comp hηc fun s hs => hHb (hηH hs)
  have hgi : InjOn g (Ioo 0 1) := fun s hs s' hs' h => by
    apply hηi hs hs'
    have := congrArg (fwdMap W t) h
    simpa only [hg, hc.fwdMap_F (hηH hs), hc.fwdMap_F (hηH hs')] using this
  set θ : ℝ → ℝ := fun s => arg (g s) with hθ
  have hgθ : ∀ s ∈ Ioo (0 : ℝ) 1, flCirc ε (θ s) = g s := fun s hs => by
    have := norm_mul_exp_arg_mul_I (g s)
    rw [hgn s hs] at this
    exact this
  have hθO : ∀ s ∈ Ioo (0 : ℝ) 1, θ s ∈ flO D ε := fun s hs => by
    have hH : g s ∈ H := hDH (hgD s hs)
    refine ⟨flCirc_mem_Ioo_of_H (ε := ε) ⟨arg_nonneg_iff.2 (le_of_lt hH), arg_le_pi _⟩ ?_, ?_⟩
    · rw [hgθ s hs]; exact hH
    · rw [hgθ s hs]; exact hgD s hs
  have hθc : ContinuousOn θ (Ioo 0 1) := fun s hs =>
    ((continuousAt_arg (Or.inr (ne_of_gt (hDH (hgD s hs))))).comp_continuousWithinAt
      (hgc s hs))
  have hθi : InjOn θ (Ioo 0 1) := fun s hs s' hs' h => hgi hs hs' (by
    rw [← hgθ s hs, ← hgθ s' hs']; exact congrArg (flCirc ε) h)
  set J := θ '' Ioo 0 1 with hJ
  have hJo : IsOpen J := fl4_isOpen_image_Ioo hθc hθi
  have hm : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set I := connectedComponentIn (flO D ε) (θ (1 / 2)) with hI
  obtain ⟨hIeq, h0α, hαβ, hβπ, hαD, hβD, hID⟩ := flComp_props hDo hDH (hθO _ hm)
  have hJI : J ⊆ I := (isPreconnected_Ioo.image θ hθc).subset_connectedComponentIn
    ⟨1 / 2, hm, rfl⟩ (image_subset_iff.2 hθO)
  -- closedness of `J` in `I`
  have hcl : closure J ∩ I ⊆ J := by
    rintro φ ⟨hφJ, hφI⟩
    have hφO : φ ∈ flO D ε := connectedComponentIn_subset _ _ hφI
    set q := flCirc ε φ
    have hqD : q ∈ D := hφO.2
    set w := fwdMap W t q with hw
    have hwH : w ∈ H := hc.mapsTo hqD
    set r := w.im / 2 with hr
    have hr0 : 0 < r := by simp only [hr]; exact half_pos hwH
    have hfar : ∀ x : ℝ, ∀ z : ℂ, dist z x < r → r ≤ dist z w := fun x z hz => by
      have h1 : w.im ≤ dist w x := by
        rw [dist_eq]
        have := abs_im_le_norm (w - x)
        simp only [sub_im, ofReal_im, sub_zero] at this
        exact (le_abs_self _).trans this
      have := dist_triangle w z x
      rw [dist_comm w z] at this
      simp only [hr] at hz ⊢; linarith
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ : ∃ δ₁ > 0, ∀ s ∈ Ioo (0 : ℝ) δ₁, dist (η s) a < r := by
      have := (ha.eventually (ball_mem_nhds _ hr0))
      obtain ⟨u, hu, hsub'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 this
      exact ⟨u, hu, fun s hs => hsub' hs⟩
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ : ∃ δ₂ < (1 : ℝ), ∀ s ∈ Ioo δ₂ 1, dist (η s) b < r := by
      have := (hb.eventually (ball_mem_nhds _ hr0))
      obtain ⟨u, hu, hsub'⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 this
      exact ⟨u, hu, fun s hs => hsub' hs⟩
    set c := min (δ₁ / 2) (1 / 4) with hcdef
    set d := max ((δ₂ + 1) / 2) (3 / 4) with hddef
    have hc0 : 0 < c := lt_min (half_pos hδ₁) (by norm_num)
    have hd1 : d < 1 := max_lt (by linarith) (by norm_num)
    have hcd : Icc c d ⊆ Ioo (0 : ℝ) 1 := fun s hs => ⟨hc0.trans_le hs.1, hs.2.trans_lt hd1⟩
    have hin : ∀ s ∈ Ioo (0 : ℝ) 1, dist (η s) w < r → s ∈ Icc c d := by
      intro s hs hsw
      refine ⟨le_of_not_gt fun h => ?_, le_of_not_gt fun h => ?_⟩
      · have h' : s < δ₁ := h.trans_le ((min_le_left _ _).trans (by linarith))
        have := hfar a _ (hδ₁' s ⟨hs.1, h'⟩); linarith
      · have h' : δ₂ < s := lt_of_le_of_lt (by
          have := le_max_left ((δ₂ + 1) / 2) (3 / 4); linarith) h
        have := hfar b _ (hδ₂' s ⟨h', hs.2⟩); linarith
    have hKc : IsCompact (η '' Icc c d) := isCompact_Icc.image_of_continuousOn (hηc.mono hcd)
    have hwK : w ∈ η '' Icc c d := by
      refine hKc.isClosed.closure_subset (Metric.mem_closure_iff.2 fun ρ hρ => ?_)
      have hcont : ContinuousAt (fun φ' : ℝ => fwdMap W t (flCirc ε φ')) φ := by
        have h1 : ContinuousAt (fwdMap W t) (flCirc ε φ) :=
          (hc.continuousOn_fwdMap).continuousAt (hDo.mem_nhds hqD)
        exact ContinuousAt.comp (x := φ) (f := flCirc ε) h1 (flCirc_continuous ε).continuousAt
      have hnb : (fun φ' : ℝ => fwdMap W t (flCirc ε φ')) ⁻¹' ball w (min ρ r) ∈ 𝓝 φ :=
        hcont.preimage_mem_nhds (ball_mem_nhds _ (lt_min hρ hr0))
      obtain ⟨_, hy, ⟨s, hs, rfl⟩⟩ := mem_closure_iff_nhds.1 hφJ _ hnb
      have hy' : dist (η s) w < min ρ r := by
        have : fwdMap W t (flCirc ε (θ s)) = η s := by
          rw [hgθ s hs]; exact hc.fwdMap_F (hηH hs)
        simpa [this] using hy
      refine ⟨η s, ⟨s, hin s hs (hy'.trans_le (min_le_right _ _)), rfl⟩, ?_⟩
      rw [dist_comm]; exact hy'.trans_le (min_le_left _ _)
    obtain ⟨s, hs, hsw⟩ := hwK
    refine ⟨s, hcd hs, ?_⟩
    have hgs : g s = q := by
      simp only [hg, hsw, hw]; exact hc.F_fwdMap hqD
    simp only [hθ, hgs]
    exact fl4_arg_flCirc hε hφO.1
  have hIJ : I ⊆ J := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hJo
    ⟨θ (1 / 2), mem_connectedComponentIn (hθO _ hm), ⟨1 / 2, hm, rfl⟩⟩
    (by rw [inter_comm]; exact inter_comm _ _ ▸ hcl)
  have hJeq : J = Ioo (sInf I) (sSup I) := (Subset.antisymm hJI hIJ).trans hIeq
  refine ⟨sInf I, sSup I, h0α, hαβ, hβπ, ?_, hαD, hβD⟩
  unfold flCircArc
  rw [← hJeq]
  ext p
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨θ s, ⟨s, hs, rfl⟩, ?_⟩
    show flCirc ε (θ s) = _
    rw [hgθ s hs, hg]; exact (hc.Feq (hηH hs))
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨η s, ⟨s, hs, rfl⟩, ?_⟩
    show _ = flCirc ε (θ s)
    rw [hgθ s hs, hg]; exact (hc.Feq (hηH hs)).symm

end FieldLawler
end QuantumZipper
