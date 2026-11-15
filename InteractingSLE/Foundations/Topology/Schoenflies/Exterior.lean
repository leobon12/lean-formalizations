/- Provenance (PROVE-GEO-JORDAN, ruling R21): ported, through an intermediate copy, from an earlier mating-of-trees
formalization; only the module and namespace prefixes were changed (now `InteractingSLE.Foundations.Topology` and
`InteractingSLE.Foundations`), and declaration names are unchanged. -/
import InteractingSLE.Foundations.Topology.Schoenflies.Disc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # The Schoenflies theorem, part 2: the exterior

For a Jordan curve `Γ ⊆ ℂ` and `p` in the bounded component `U` of `Γᶜ`, the unbounded component
`V = Γᶜ ∖ U` together with `Γ` is the image of `{|z| ≥ 1}` under a map `E` continuous and injective
there, with `E '' {|z| > 1} = V`, `E '' ∂𝔻 = Γ` and `E z → ∞` as `z → ∞`
(`schoenflies_exterior`). Standard proof (e.g. Pommerenke, *Boundary Behaviour of Conformal
Maps*, 1992, §2.1, exterior maps): the inversion `z ↦ (z - p)⁻¹` maps `Γ` to a Jordan curve `Γ'`
and `V ∪ {∞}` onto the bounded component `W` of `Γ'ᶜ` containing `0`; apply the closed-disc
form (`schoenflies_disc`) to `Γ'` at `0` and invert back: `E z = p + g(z⁻¹)⁻¹`.
-/

noncomputable section

namespace InteractingSLE.Foundations.Schoenflies

open Metric Set Function Bornology Topology Filter
open LQGMetric.JordanMap

/-- The inversion `w ↦ p + w⁻¹` as an equivalence of `ℂ` (with Lean's `0⁻¹ = 0` it swaps `0`
and `p`); its inverse is `z ↦ (z - p)⁻¹`. -/
def invAt (p : ℂ) : ℂ ≃ ℂ where
  toFun w := p + w⁻¹
  invFun z := (z - p)⁻¹
  left_inv w := by simp
  right_inv z := by simp

@[simp] theorem invAt_apply (p w : ℂ) : invAt p w = p + w⁻¹ := rfl

@[simp] theorem invAt_symm_apply (p z : ℂ) : (invAt p).symm z = (z - p)⁻¹ := rfl

theorem continuousOn_invAt (p : ℂ) : ContinuousOn (invAt p) {0}ᶜ :=
  continuousOn_const.add continuousOn_inv₀

theorem isOpen_invAt_preimage {p : ℂ} {S : Set ℂ} (hS : IsOpen S) (hpS : p ∉ S) :
    IsOpen (invAt p ⁻¹' S) := by
  have h := (continuousOn_invAt p).isOpen_inter_preimage isOpen_compl_singleton hS
  convert h using 1
  ext w
  simp only [mem_preimage, mem_inter_iff, mem_compl_iff, mem_singleton_iff]
  refine ⟨fun hw => ⟨?_, hw⟩, fun h => h.2⟩
  rintro rfl
  simp only [invAt_apply, inv_zero, add_zero] at hw
  exact hpS hw

theorem continuousOn_inv_sub {p : ℂ} {S : Set ℂ} (hpS : p ∉ S) :
    ContinuousOn (fun z : ℂ => (z - p)⁻¹) S :=
  (continuousOn_id.sub continuousOn_const).inv₀ fun z hz h => by
    have h' : z = p := by simpa [sub_eq_zero] using h
    exact hpS (h' ▸ hz)

/-- **Schoenflies, exterior form (deliverable 2).** -/
theorem schoenflies_exterior {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    ∃ E : ℂ → ℂ, ContinuousOn E {z | 1 ≤ ‖z‖} ∧ InjOn E {z | 1 ≤ ‖z‖} ∧
      E '' {z | 1 < ‖z‖} = Γᶜ \ connectedComponentIn Γᶜ p ∧ E '' sphere 0 1 = Γ ∧
      Tendsto E (cobounded ℂ) (cobounded ℂ) := by
  set U := connectedComponentIn Γᶜ p with hU
  obtain ⟨-, V, hVo, hVc, -, hd, hun, -⟩ := jordan_split hΓ hp hb
  have hΓc : IsCompact Γ := isCompact_of_isJordanCurve hΓ
  have hUo : IsOpen U := hΓc.isClosed.isOpen_compl.connectedComponentIn
  have hpU : p ∈ U := mem_connectedComponentIn hp
  have hVΓ : V ⊆ Γᶜ := hun ▸ subset_union_right
  have hpV : p ∉ V := fun h => hd.ne_of_mem hpU h rfl
  have hpΓ : p ∉ Γ := hp
  have hVeq : Γᶜ \ U = V := by
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      rw [hun] at hz
      exact hz.resolve_left hzU
    · exact fun hz => ⟨hVΓ hz, fun hzU => hd.ne_of_mem hzU hz rfl⟩
  rw [hVeq]
  set K := invAt p with hKdef
  have himg : ∀ S, K.symm '' S = K ⁻¹' S := fun S => by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · exact fun h => ⟨K z, h, K.symm_apply_apply z⟩
  have hK0 : K 0 = p := by simp [K]
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUo p hpU
  obtain ⟨R, hR, hRU⟩ := (hb.union hΓc.isBounded).subset_closedBall_lt 0 p
  set ε := R⁻¹ with hεdef
  have hε : 0 < ε := inv_pos.mpr hR
  have hfar : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε → K w ∈ V := by
    intro w hw hwR
    have hgt : R < ‖K w - p‖ := by
      simp only [K, invAt_apply, add_sub_cancel_left, norm_inv]
      exact (lt_inv_comm₀ (norm_pos_iff.mpr hw) hR).mp hwR
    have hnot : K w ∉ U ∪ Γ := fun h => (not_le.mpr hgt) (by
      have := hRU h
      rwa [mem_closedBall, dist_eq_norm] at this)
    have : K w ∈ U ∪ V := by rw [← hun]; exact fun h => hnot (Or.inr h)
    exact this.resolve_left fun h => hnot (Or.inl h)
  set Γ' := K ⁻¹' Γ with hΓ'def
  have hJ' : IsJordanCurve Γ' := by
    rw [hΓ'def, ← himg]
    exact isJordanCurve_image hΓ (continuousOn_inv_sub hpΓ) K.symm.injective.injOn
  set W := K ⁻¹' V ∪ ball 0 ε with hWdef
  have hKV0 : (0 : ℂ) ∉ K ⁻¹' V := by
    rw [mem_preimage, hK0]; exact hpV
  have hWsub : W ⊆ K ⁻¹' V ∪ {0} := by
    rintro w (hw | hw)
    · exact Or.inl hw
    · by_cases h0 : w = 0
      · exact Or.inr h0
      · exact Or.inl (hfar w h0 (mem_ball_zero_iff.mp hw))
  have hWΓ' : W ⊆ Γ'ᶜ := by
    intro w hw
    rcases hWsub hw with hw | hw
    · exact hVΓ hw
    · rw [mem_singleton_iff.mp hw]
      show K 0 ∉ Γ
      rw [hK0]; exact hpΓ
  have hKVpre : IsPreconnected (K ⁻¹' V) := by
    rw [← himg]; exact hVc.image _ (continuousOn_inv_sub hpV)
  have hw0 : ((ε / 2 : ℝ) : ℂ) ∈ K ⁻¹' V ∩ ball 0 ε := by
    have hn : ‖((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    exact ⟨hfar _ hne (by rw [hn]; linarith), mem_ball_zero_iff.mpr (by rw [hn]; linarith)⟩
  have hWc : IsPreconnected W :=
    hKVpre.union _ hw0.1 hw0.2 (convex_ball (0 : ℂ) ε).isPreconnected
  have hWo : IsOpen W := (isOpen_invAt_preimage hVo hpV).union isOpen_ball
  have hvo : IsOpen (K ⁻¹' (U \ {p})) :=
    isOpen_invAt_preimage (hUo.sdiff isClosed_singleton) fun h => h.2 rfl
  have hdisj : Disjoint W (K ⁻¹' (U \ {p})) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    rcases hWsub hw with hw | hw
    · exact hd.ne_of_mem hw'.1 hw rfl
    · rw [mem_singleton_iff.mp hw] at hw'
      exact hw'.2 hK0
  have hcover : Γ'ᶜ ⊆ W ∪ K ⁻¹' (U \ {p}) := by
    intro w hw
    have : K w ∈ U ∪ V := by rw [← hun]; exact hw
    rcases this with hU' | hV'
    · by_cases hKp : K w = p
      · left; right
        have : w = 0 := by rw [← K.symm_apply_apply w, hKp, hKdef, invAt_symm_apply, sub_self, inv_zero]
        rw [this]; exact mem_ball_self hε
      · exact Or.inr ⟨hU', hKp⟩
    · exact Or.inl (Or.inl hV')
  have h0W : (0 : ℂ) ∈ W := Or.inr (mem_ball_self hε)
  have hccW : connectedComponentIn Γ'ᶜ 0 = W := by
    apply Subset.antisymm
    · exact IsPreconnected.subset_left_of_subset_union hWo hvo hdisj
        ((connectedComponentIn_subset _ _).trans hcover)
        ⟨0, mem_connectedComponentIn (hWΓ' h0W), h0W⟩ isPreconnected_connectedComponentIn
    · exact hWc.subset_connectedComponentIn h0W hWΓ'
  have hWb : IsBounded W := by
    refine IsBounded.union ((isBounded_closedBall (x := (0 : ℂ)) (r := r⁻¹)).subset ?_)
      isBounded_ball
    intro w hw
    have hw0 : w ≠ 0 := fun h => hKV0 (h ▸ hw)
    have hge : r ≤ ‖w‖⁻¹ := by
      by_contra hlt
      have hball : K w ∈ ball p r := by
        rw [mem_ball, dist_eq_norm]
        show ‖p + w⁻¹ - p‖ < r
        rw [add_sub_cancel_left, norm_inv]
        exact not_le.mp hlt
      exact hd.ne_of_mem (hrU hball) hw rfl
    rw [mem_closedBall_zero_iff]
    exact (le_inv_comm₀ hr (norm_pos_iff.mpr hw0)).mp hge
  obtain ⟨g, hgc, hgi, -, hg0, hgb, hgs⟩ := schoenflies_disc hJ' (hWΓ' h0W) (hccW ▸ hWb)
  rw [hccW] at hgb
  have hinvB : ∀ z : ℂ, 1 ≤ ‖z‖ → z⁻¹ ∈ closedBall (0 : ℂ) 1 ∧ z⁻¹ ≠ 0 := fun z hz => by
    refine ⟨?_, inv_ne_zero (norm_pos_iff.mp (zero_lt_one.trans_le hz))⟩
    rw [mem_closedBall_zero_iff, norm_inv]
    exact inv_le_one_of_one_le₀ hz
  have hgne : ∀ w ∈ closedBall (0 : ℂ) 1, w ≠ 0 → g w ≠ 0 := fun w hw hw0 h =>
    hw0 (hgi hw (mem_closedBall_self zero_le_one) (h.trans hg0.symm))
  have hinvimg : ∀ S : Set ℂ, (fun z : ℂ => z⁻¹) '' S = (fun z : ℂ => z⁻¹) ⁻¹' S := fun S =>
    congrFun (image_eq_preimage_of_inverse (f := fun z : ℂ => z⁻¹) (g := fun z : ℂ => z⁻¹)
      inv_inv inv_inv) S
  have hcomp : (fun z => K (g z⁻¹)) = K ∘ g ∘ fun z : ℂ => z⁻¹ := rfl
  refine ⟨fun z => K (g z⁻¹), ?_, ?_, ?_, ?_, ?_⟩
  · refine (continuousOn_invAt p).comp (hgc.comp (continuousOn_inv₀.mono fun z hz => ?_)
      fun z hz => (hinvB z hz).1) fun z hz => hgne _ (hinvB z hz).1 (hinvB z hz).2
    exact (hinvB z hz).2 ∘ fun h => by rw [h, inv_zero]
  · exact fun z hz w hw h => inv_injective (hgi (hinvB z hz).1 (hinvB w hw).1 (K.injective h))
  · rw [hcomp, image_comp, image_comp, hinvimg]
    have h1 : (fun z : ℂ => z⁻¹) ⁻¹' {z : ℂ | 1 < ‖z‖} = ball 0 1 \ {0} := by
      ext w
      by_cases hw : w = 0
      · simp [hw]
      · simp [hw, norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hw)]
    have h2 : g '' (ball 0 1 \ {0}) = W \ {0} := by
      rw [← hgb]
      ext y
      constructor
      · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩
        exact ⟨⟨w, hw, rfl⟩, hgne w (ball_subset_closedBall hw) hw0⟩
      · rintro ⟨⟨w, hw, rfl⟩, hy⟩
        exact ⟨w, ⟨hw, fun h => hy (by rw [mem_singleton_iff.mp h, hg0]; rfl)⟩, rfl⟩
    have h3 : W \ {0} = K ⁻¹' V := by
      ext w
      constructor
      · rintro ⟨hw, hw0⟩
        exact (hWsub hw).resolve_right hw0
      · exact fun hw => ⟨Or.inl hw, fun h => hKV0 (mem_singleton_iff.mp h ▸ hw)⟩
    rw [h1, h2, h3, K.image_preimage]
  · rw [hcomp, image_comp, image_comp, hinvimg]
    have h1 : (fun z : ℂ => z⁻¹) ⁻¹' sphere (0 : ℂ) 1 = sphere 0 1 := by
      ext w; simp [norm_inv]
    rw [h1, hgs, K.image_preimage]
  · have hev : ∀ᶠ z in cobounded ℂ, 1 ≤ ‖z‖ :=
      tendsto_norm_cobounded_atTop.eventually_ge_atTop 1
    have h1 : Tendsto (fun z : ℂ => z⁻¹) (cobounded ℂ) (𝓝[closedBall 0 1 \ {0}] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv₀_cobounded,
        hev.mono fun z hz => ⟨(hinvB z hz).1, (hinvB z hz).2⟩⟩
    have h2 : Tendsto g (𝓝[closedBall 0 1 \ {0}] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall
        fun w hw => hgne w hw.1 hw.2⟩
      have := (hgc 0 (mem_closedBall_self zero_le_one)).mono (sdiff_subset (t := {0}))
      rw [ContinuousWithinAt, hg0] at this
      exact this
    exact ((tendsto_const_add_cobounded p).comp tendsto_inv₀_nhdsNE_zero).comp (h2.comp h1)

end InteractingSLE.Foundations.Schoenflies
