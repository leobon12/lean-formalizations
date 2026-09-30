import QuantumZipper.Proofs.Zipper.FieldLawlerCoverHarm
import QuantumZipper.Proofs.Thm18.LWHarmCross
import QuantumZipper.Proofs.Complex.CaraBdrySurj

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-UNIF (A): the Carathéodory data of `M(H_η)`, `M z = 1/(z + i)`

Task FL3-UNIF, setup for the uniformization of `H_η = hullComp η` (the unbounded component of
`ℍ \ η` for a crosscut `η` with distinct feet `a ≠ b`).

As in `FieldLawlerCoverHarm.lean`, `D' = M(H_η)` is a bounded domain whose frontier lies in the
compact set `E = M(η̄) ∪ {|w + i/2| = 1/2}` (a "theta graph": the circle and an arc joining two of
its points). We record:
* `fl3u_carHyp`: the standing hypotheses `Car.CarHyp` for a Riemann map `ℍ → D'`
  (Riemann mapping theorem, repo `RMT.riemann_mapping_of_hasHoloSqrt`), with `E` as above;
* `fl3u_E_ulc`: `E` is ULC;
* `fl3u_E_diff_preconnected`: `E \ {q}` is connected for every `q`, the hypothesis of the Jordan
  case of Carathéodory's theorem in the form `CA.Car.isClosedEmbedding_bdryMap`
  (Pommerenke, *Boundary Behaviour of Conformal Maps*, 1992, Thm 2.6, p. 24);
* Möbius transport of frontiers between `U` and `M(U)`.
Own elementary plane-topology arguments (a circle minus a point, a theta graph minus a point);
the construction of `CarHyp` repeats the one in `flHullHarmExists_holds`.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

/-- The circle `|w + i/2| = 1/2` is `M(ℝ) ∪ {0}`. -/
lemma fl3u_sphere_eq : sphere (-I / 2) (1 / 2) = insert 0 (range fun x : ℝ => flMob x) := by
  ext w
  constructor
  · intro hw
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    · right
      refine ⟨(flMobInv w).re, ?_⟩
      have : ((flMobInv w).re : ℂ) = flMobInv w :=
        Complex.ext (by simp) (by simp [flMobInv_im_of_sphere hw hw0])
      simp only [this, flMob_flMobInv]
  · rintro (rfl | ⟨x, rfl⟩)
    · rw [mem_sphere, dist_eq_norm]; simp
    · exact flMob_real_mem_sphere x

/-- A circle minus a point is connected (own elementary proof via the parametrization `M(ℝ)`). -/
lemma fl3u_sphere_diff_preconnected (q : ℂ) :
    IsPreconnected (sphere (-I / 2) (1 / 2) \ {q}) := by
  set f : ℝ → ℂ := fun x => flMob x with hf
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x =>
    (flMob_continuousAt (by simp)).comp continuous_ofReal.continuousAt
  have hlim : ∀ l : Filter ℝ, Tendsto (fun x : ℝ => |x|) l atTop → Tendsto f l (𝓝 0) :=
    fun l hl => flMob_tendsto_cobounded.comp
      (tendsto_norm_atTop_iff_cobounded.1 (by simpa [Complex.norm_real] using hl))
  have hf0 : ∀ x, f x ≠ 0 := fun x => flMob_ne_zero (by simp)
  have hfi : Function.Injective f := fun x y h => by
    have := congrArg flMobInv h
    simp only [hf, flMobInv_flMob] at this
    exact_mod_cast this
  have hcl : ∀ s : Set ℝ, IsPreconnected s → ∀ l : Filter ℝ, l.NeBot →
      Tendsto (fun x : ℝ => |x|) l atTop → s ∈ l → IsPreconnected (insert 0 (f '' s)) := by
    intro s hs l _ hl hsl
    refine (hs.image f hfc.continuousOn).subset_closure (subset_insert _ _)
      (insert_subset_iff.2 ⟨?_, subset_closure⟩)
    exact mem_closure_of_tendsto (hlim l hl)
      (mem_of_superset hsl fun x hx => mem_image_of_mem f hx)
  rw [fl3u_sphere_eq]
  by_cases hq : q ∈ range f
  · obtain ⟨x₀, rfl⟩ := hq
    have e : insert 0 (range f) \ {f x₀} = insert 0 (f '' Iio x₀) ∪ insert 0 (f '' Ioi x₀) := by
      ext w
      constructor
      · rintro ⟨hw | ⟨x, rfl⟩, hwq⟩
        · exact Or.inl (Or.inl hw)
        · rcases lt_or_gt_of_ne (fun h : x = x₀ => hwq (by rw [h]; rfl)) with h | h
          · exact Or.inl (Or.inr ⟨x, h, rfl⟩)
          · exact Or.inr (Or.inr ⟨x, h, rfl⟩)
      · rintro ((rfl | ⟨x, hx, rfl⟩) | (rfl | ⟨x, hx, rfl⟩))
        · exact ⟨Or.inl rfl, fun h => hf0 x₀ (Eq.symm h)⟩
        · exact ⟨Or.inr ⟨x, rfl⟩, fun h => (ne_of_lt hx) (hfi h)⟩
        · exact ⟨Or.inl rfl, fun h => hf0 x₀ (Eq.symm h)⟩
        · exact ⟨Or.inr ⟨x, rfl⟩, fun h => (ne_of_gt hx) (hfi h)⟩
    rw [e]
    exact IsPreconnected.union 0 (mem_insert _ _) (mem_insert _ _)
      (hcl _ isPreconnected_Iio atBot inferInstance tendsto_abs_atBot_atTop (Iio_mem_atBot x₀))
      (hcl _ isPreconnected_Ioi atTop inferInstance tendsto_abs_atTop_atTop (Ioi_mem_atTop x₀))
  · by_cases hq0 : q = 0
    · subst hq0
      rw [Set.insert_sdiff_of_mem _ (mem_singleton _),
        sdiff_singleton_eq_self (fun h => by obtain ⟨x, hx⟩ := h; exact hf0 x hx)]
      exact isPreconnected_range hfc
    · rw [sdiff_singleton_eq_self (fun h => h.elim hq0 hq)]
      have := hcl univ isPreconnected_univ atTop inferInstance tendsto_abs_atTop_atTop univ_mem
      rwa [image_univ] at this

/-- A theta graph (a set `S` whose punctures are connected, plus an arc joining two points of
`S`) minus a point is connected. Own elementary proof. -/
lemma fl3u_theta_diff_preconnected {S : Set ℂ} {γ : ℝ → ℂ}
    (hS : ∀ q, IsPreconnected (S \ {q})) (hγc : ContinuousOn γ (Icc 0 1))
    (hγi : InjOn γ (Icc 0 1)) (h0 : γ 0 ∈ S) (h1 : γ 1 ∈ S) (q : ℂ) :
    IsPreconnected ((γ '' Icc 0 1 ∪ S) \ {q}) := by
  have h01 : γ 0 ≠ γ 1 := fun h => by
    have := hγi (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) h
    norm_num at this
  obtain ⟨x, hxS, hxq⟩ : ∃ x ∈ S, x ≠ q := by
    by_cases h : γ 0 = q
    · exact ⟨γ 1, h1, fun h' => h01 (h.trans h'.symm)⟩
    · exact ⟨γ 0, h0, h⟩
  have hSq : S \ {q} ⊆ (γ '' Icc 0 1 ∪ S) \ {q} := sdiff_subset_sdiff_left subset_union_right
  refine isPreconnected_of_forall x fun y hy => ?_
  rcases hy with ⟨hyE | hyS, hyq⟩
  · obtain ⟨t, ht, rfl⟩ := hyE
    by_cases hlow : ∀ s ∈ Icc (0 : ℝ) t, γ s ≠ q
    · refine ⟨γ '' Icc 0 t ∪ S \ {q}, union_subset ?_ hSq, Or.inr ⟨hxS, hxq⟩,
        Or.inl ⟨t, right_mem_Icc.2 ht.1, rfl⟩, ?_⟩
      · rintro _ ⟨s, hs, rfl⟩
        exact ⟨Or.inl ⟨s, ⟨hs.1, hs.2.trans ht.2⟩, rfl⟩, hlow s hs⟩
      · exact IsPreconnected.union (γ 0) ⟨0, left_mem_Icc.2 ht.1, rfl⟩
          ⟨h0, hlow 0 (left_mem_Icc.2 ht.1)⟩
          (isPreconnected_Icc.image _ (hγc.mono (Icc_subset_Icc le_rfl ht.2))) (hS q)
    · push Not at hlow
      obtain ⟨s, hs, hsq⟩ := hlow
      have hup : ∀ s' ∈ Icc t 1, γ s' ≠ q := by
        intro s' hs' h'
        have hss := hγi ⟨hs.1, hs.2.trans ht.2⟩ ⟨ht.1.trans hs'.1, hs'.2⟩ (hsq.trans h'.symm)
        have hst : s = t := le_antisymm hs.2 (by rw [hss]; exact hs'.1)
        exact hyq (show γ t = q by rw [← hst, hsq])
      refine ⟨γ '' Icc t 1 ∪ S \ {q}, union_subset ?_ hSq, Or.inr ⟨hxS, hxq⟩,
        Or.inl ⟨t, left_mem_Icc.2 ht.2, rfl⟩, ?_⟩
      · rintro _ ⟨s', hs', rfl⟩
        exact ⟨Or.inl ⟨s', ⟨ht.1.trans hs'.1, hs'.2⟩, rfl⟩, hup s' hs'⟩
      · exact IsPreconnected.union (γ 1) ⟨1, right_mem_Icc.2 ht.2, rfl⟩
          ⟨h1, hup 1 (right_mem_Icc.2 ht.2)⟩
          (isPreconnected_Icc.image _ (hγc.mono (Icc_subset_Icc ht.1 le_rfl))) (hS q)
  · exact ⟨S \ {q}, hSq, ⟨hxS, hxq⟩, ⟨hyS, hyq⟩, hS q⟩

/-- The closed arc `lwArcExt η a b` is injective on `[0, 1]` when `a ≠ b`. -/
lemma fl3u_arcExt_injOn {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ} (hab : a ≠ b) :
    InjOn (lwArcExt η a b) (Icc 0 1) := by
  have key : ∀ s ∈ Icc (0 : ℝ) 1, (s = 0 ∧ lwArcExt η a b s = a) ∨
      (s = 1 ∧ lwArcExt η a b s = b) ∨
      (s ∈ Ioo (0 : ℝ) 1 ∧ lwArcExt η a b s = η s ∧ 0 < (η s).im) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · left; subst h0; simp [lwArcExt]
    rcases eq_or_lt_of_le hs.2 with h1 | h1
    · right; left; subst h1; simp [lwArcExt]
    · right; right; exact ⟨⟨h0, h1⟩, lwArcExt_mem hη ⟨h0, h1⟩⟩
  intro s hs t ht hst
  rcases key s hs with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ | ⟨hs', e1, i1⟩ <;>
    rcases key t ht with ⟨rfl, e2⟩ | ⟨rfl, e2⟩ | ⟨ht', e2, i2⟩ <;>
    first
    | rfl
    | (rw [e1, e2] at hst
       first
       | exact absurd (ofReal_injective hst) hab
       | exact absurd (ofReal_injective hst).symm hab
       | (have := congrArg Complex.im hst; simp at this; linarith)
       | exact hη.2.1 hs' ht' hst)

/-! ### Möbius transport between `U ⊆ ℍ` and `M(U)` -/

section Transport

variable {U : Set ℂ}

lemma fl3u_memD (hUH : U ⊆ H) (w : ℂ) : w ∈ flMob '' U ↔ w ≠ 0 ∧ flMobInv w ∈ U := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨flMob_ne_zero (hUH hz : (0 : ℝ) < z.im).le, by rw [flMobInv_flMob]; exact hz⟩
  · rintro ⟨-, h⟩
    exact ⟨_, h, flMob_flMobInv⟩

lemma fl3u_isOpenD (hUo : IsOpen U) (hUH : U ⊆ H) : IsOpen (flMob '' U) := by
  have : flMob '' U = {w : ℂ | w ≠ 0} ∩ flMobInv ⁻¹' U := by
    ext w; rw [fl3u_memD hUH]; rfl
  rw [this]
  exact ContinuousOn.isOpen_inter_preimage (fun w hw => (flMobInv_continuousAt hw).continuousWithinAt)
    isOpen_ne hUo

lemma fl3u_frontier_im (hUH : U ⊆ H) {z : ℂ} (hz : z ∈ frontier U) : 0 ≤ z.im :=
  flH_closure_H_im (closure_mono hUH (frontier_subset_closure hz))

lemma fl3u_frD_inv (hUo : IsOpen U) (hUH : U ⊆ H) {w : ℂ} (hw : w ∈ frontier (flMob '' U))
    (hw0 : w ≠ 0) : flMobInv w ∈ frontier U := by
  rw [(fl3u_isOpenD hUo hUH).frontier_eq] at hw
  rw [hUo.frontier_eq]
  refine ⟨closure_mono ?_ (mem_closure_image (flMobInv_continuousAt hw0) hw.1), fun hU => ?_⟩
  · rintro _ ⟨v, hv, rfl⟩; exact ((fl3u_memD hUH v).1 hv).2
  · exact hw.2 ((fl3u_memD hUH w).2 ⟨hw0, hU⟩)

lemma fl3u_fr_mob (hUo : IsOpen U) (hUH : U ⊆ H) {z : ℂ} (hz : z ∈ frontier U) :
    flMob z ∈ frontier (flMob '' U) := by
  have hzim := fl3u_frontier_im hUH hz
  rw [hUo.frontier_eq] at hz
  rw [(fl3u_isOpenD hUo hUH).frontier_eq]
  refine ⟨mem_closure_image (flMob_continuousAt hzim) hz.1, fun hD => ?_⟩
  have := ((fl3u_memD hUH _).1 hD).2
  rw [flMobInv_flMob] at this
  exact hz.2 this

lemma fl3u_zero_frD (hUo : IsOpen U) (hUH : U ⊆ H) (hUunb : ¬ Bornology.IsBounded U) :
    (0 : ℂ) ∈ frontier (flMob '' U) := by
  have hneb : (Bornology.cobounded ℂ ⊓ 𝓟 U).NeBot := by
    rw [inf_principal_neBot_iff]
    intro V hV
    by_contra hVU
    rw [not_nonempty_iff_eq_empty] at hVU
    have hVb : Bornology.IsBounded Vᶜ := Bornology.isBounded_compl_iff.2 hV
    exact hUunb (hVb.subset fun z hz hzV => (hVU ▸ ⟨hzV, hz⟩ : z ∈ (∅ : Set ℂ)))
  rw [(fl3u_isOpenD hUo hUH).frontier_eq]
  refine ⟨mem_closure_of_tendsto (flMob_tendsto_cobounded.mono_left inf_le_left)
    (eventually_inf_principal.2 (Eventually.of_forall fun z hz => ⟨z, hz, rfl⟩)), fun h => ?_⟩
  exact ((fl3u_memD hUH 0).1 h).1 rfl

end Transport

/-! ### The theta graph `E` and the Carathéodory hypotheses -/

/-- The theta graph `E = M(η̄) ∪ {|w + i/2| = 1/2}`. -/
def fl3uE (η : ℝ → ℂ) (a b : ℝ) : Set ℂ :=
  (flMob ∘ lwArcExt η a b) '' Icc 0 1 ∪ sphere (-I / 2) (1 / 2)

section Theta

variable {η : ℝ → ℂ} {a b : ℝ}

lemma fl3u_gamma_contOn (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) :
    ContinuousOn (flMob ∘ lwArcExt η a b) (Icc 0 1) :=
  ContinuousOn.comp (t := {z : ℂ | 0 ≤ z.im}) (fun _ hz => (flMob_continuousAt hz).continuousWithinAt)
    (lwArcExt_contOn hη ha hb) (fun t _ => flH_lwArcExt_im hη t)

lemma fl3u_E_isClosed (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) : IsClosed (fl3uE η a b) :=
  (isCompact_Icc.image_of_continuousOn (fl3u_gamma_contOn hη ha hb)).isClosed.union isClosed_sphere

lemma fl3u_E_ulc (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) : Topo.ULC (fl3uE η a b) :=
  Topo.ULC.union_of_isCompact_of_isClosed
    (isCompact_Icc.image_of_continuousOn (fl3u_gamma_contOn hη ha hb)) isClosed_sphere
    (Topo.ULC.image_Icc (fl3u_gamma_contOn hη ha hb)) (Topo.ULC.sphere _ _)

lemma fl3u_E_diff_preconnected (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) (hab : a ≠ b) (q : ℂ) :
    IsPreconnected (fl3uE η a b \ {q}) := by
  refine fl3u_theta_diff_preconnected fl3u_sphere_diff_preconnected
    (fl3u_gamma_contOn hη ha hb) (fun s hs t ht h => fl3u_arcExt_injOn hη hab hs ht ?_)
    (by simpa [lwArcExt] using flMob_real_mem_sphere a)
    (by norm_num [lwArcExt]; simpa using flMob_real_mem_sphere b) q
  have := congrArg flMobInv h
  simpa only [Function.comp_apply, flMobInv_flMob] using this

/-- **Carathéodory hypotheses for `M(H_η)`.** A Riemann map `ℍ → M(H_η)` exists (RMT) and
satisfies `Car.CarHyp` with the theta graph `E`. -/
theorem fl3u_carHyp (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ))) :
    ∃ G : ℂ → ℂ, Car.CarHyp G (flMob '' hullComp η) (fl3uE η a b) 1 := by
  set U := hullComp η with hUdef
  have hUo : IsOpen U := lwExc_hullComp_isOpen hη
  have hUH : U ⊆ H := lwExc_hullComp_subset_H η
  have hUim : ∀ z ∈ U, 0 ≤ z.im := fun z hz => (hUH hz : (0 : ℝ) < z.im).le
  obtain ⟨p₀, hp₀U, hUeq⟩ := flH_hullComp_eq hη
  have hUc : IsPreconnected U := by rw [hUdef, hUeq]; exact isPreconnected_connectedComponentIn
  have hUuniv : U ≠ univ := fun h => by
    have := hUH (h ▸ mem_univ (0 : ℂ)); simp [H] at this
  obtain ⟨φ₀, -, -, ψ₀, hψb, hψd, -⟩ := RMT.riemann_mapping_of_hasHoloSqrt hUo hUc ⟨p₀, hp₀U⟩
    hUuniv (RMT.hasHoloSqrt_of_unbounded_compl hUo hUc (flH_compl_unbounded hη ha hb))
  set D' := flMob '' U with hD'def
  have hD'o : IsOpen D' := fl3u_isOpenD hUo hUH
  have hEsub : frontier D' ⊆ fl3uE η a b := by
    intro w hw
    unfold fl3uE
    by_cases hw0 : w = 0
    · right; rw [hw0, mem_sphere, dist_eq_norm]; simp
    · have hz := fl3u_frD_inv hUo hUH hw hw0
      set z := flMobInv w
      have hwz : w = flMob z := flMob_flMobInv.symm
      have hzim : 0 ≤ z.im := fl3u_frontier_im hUH hz
      rw [hUo.frontier_eq] at hz
      rcases hzim.lt_or_eq with hpos | hzero
      · have harc : z ∈ arcH η := by
          by_contra hna
          exact hz.2 (lw3_mem_hull_of_closure hη ⟨hpos, hna⟩ hz.1)
        obtain ⟨s, hs, hzs⟩ := harc
        left
        refine ⟨s, Ioo_subset_Icc_self hs, ?_⟩
        simp only [Function.comp_apply, (lwArcExt_mem (a := a) (b := b) hη hs).1, hzs, hwz]
      · right
        have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
        rw [hwz, hzr]
        exact flMob_real_mem_sphere _
  have hEcompl : fl3uE η a b ⊆ D'ᶜ := by
    unfold fl3uE
    rintro w (⟨t, ht, rfl⟩ | hw) hD
    · have h2 := ((fl3u_memD hUH _).1 hD).2
      simp only [Function.comp_apply, flMobInv_flMob] at h2
      have hS := h2.1
      unfold lwArcExt at hS
      split_ifs at hS with h0 h1
      · exact (show ¬ (0 : ℝ) < ((a : ℂ)).im by simp) hS.1
      · exact (show ¬ (0 : ℝ) < ((b : ℂ)).im by simp) hS.1
      · exact hS.2 ⟨t, ⟨not_le.1 h0, not_le.1 h1⟩, rfl⟩
    · obtain ⟨hw0, hwU⟩ := (fl3u_memD hUH w).1 hD
      have := hUH hwU
      simp only [H, mem_ofPred_eq, flMobInv_im_of_sphere hw hw0] at this
      exact lt_irrefl _ this
  have hEbdd : fl3uE η a b ⊆ closedBall 0 1 := by
    unfold fl3uE
    rintro w (⟨t, -, rfl⟩ | hw)
    · rw [mem_closedBall, dist_zero_right]; exact flMob_norm_le (flH_lwArcExt_im hη t)
    · rw [mem_sphere, dist_eq_norm] at hw
      rw [mem_closedBall, dist_zero_right]
      have := norm_add_le (w - -I / 2) (-I / 2)
      rw [sub_add_cancel] at this
      have hI : ‖-I / 2‖ = 1 / 2 := by simp
      linarith
  refine ⟨flMob ∘ ψ₀ ∘ cayley, ?_⟩
  have hd1 : DifferentiableOn ℂ (ψ₀ ∘ cayley) H :=
    hψd.comp (differentiableOn_cayley_Hbar.mono H_subset_Hbar) bijOn_cayley_H.mapsTo
  have hb1 : BijOn (ψ₀ ∘ cayley) H U := hψb.comp bijOn_cayley_H
  have hinj : InjOn flMob U := fun z _ w _ he => by
    have := congrArg flMobInv he; rwa [flMobInv_flMob, flMobInv_flMob] at this
  refine ⟨?_, (hinj.bijOn_image).comp hb1, hD'o, ?_, fl3u_E_isClosed hη ha hb, hEsub, hEcompl,
    hEbdd⟩
  · refine DifferentiableOn.comp (t := U) (fun z hz => ?_) hd1 hb1.mapsTo
    exact (flMob_analyticAt (hUim z hz)).differentiableAt.differentiableWithinAt
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_ball, dist_zero_right]; exact flMob_norm_lt (hUH hz)

end Theta

end FieldLawler
end QuantumZipper
