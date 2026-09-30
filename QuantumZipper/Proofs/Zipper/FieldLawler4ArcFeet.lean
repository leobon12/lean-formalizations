import QuantumZipper.Proofs.Zipper.FieldLawler4Arc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-ARC (A1, feet): the feet of the image crosscut are the images of the arc's end points

Task FL4-ARC. With `(α, β)` from `fl4_arc_angles`, the Carathéodory extension `F` of `Z_t⁻¹`
(`SideCtx`) sends the feet `a, b` of `η` to the two end points `ε e^{iα}`, `ε e^{iβ}` (in some
order), so `a ≠ b` (`fl4_arc_feet`). Own elementary argument (FL, EJP 20 (2015), p. 9, use it
without comment): the angle of `Z_t⁻¹ ∘ η` is strictly monotone with image `(α, β)`, so its
one-sided limits are `α` and `β`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **(A1, feet)** The arc of `fl4_arc_angles` together with the images of the feet. -/
theorem fl4_arc_feet (hc : SideCtx W t F) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} {a b : ℝ}
    (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hsub : arcH η ⊆ {p | ‖fwdMapInv W t p‖ = ε}) :
    ∃ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ π ∧
      fwdMapInv W t '' arcH η = flCircArc ε α β ∧
      flCirc ε α ∉ H \ fwdHull W t ∧ flCirc ε β ∉ H \ fwdHull W t ∧
      ((F a = flCirc ε α ∧ F b = flCirc ε β) ∨ (F a = flCirc ε β ∧ F b = flCirc ε α)) := by
  obtain ⟨α, β, h0α, hαβ, hβπ, himg, hαD, hβD⟩ := fl4_arc_angles hc hε hη ha hb hsub
  refine ⟨α, β, h0α, hαβ, hβπ, himg, hαD, hβD, ?_⟩
  have hHb : H ⊆ Hbar := fun z hz => by show (0 : ℝ) ≤ z.im; exact le_of_lt hz
  obtain ⟨hηc, hηi, hηH, -, -⟩ := hη
  set g : ℝ → ℂ := fun s => F (η s) with hg
  have hgc : ContinuousOn g (Ioo 0 1) := hc.Fcont.comp hηc fun s hs => hHb (hηH hs)
  have hgi : InjOn g (Ioo 0 1) := fun s hs s' hs' h => by
    apply hηi hs hs'
    have := congrArg (fwdMap W t) h
    simpa only [hg, hc.fwdMap_F (hηH hs), hc.fwdMap_F (hηH hs')] using this
  -- every value of `g` is on the arc
  have hgarc : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ φ ∈ Ioo α β, flCirc ε φ = g s := fun s hs => by
    have : fwdMapInv W t (η s) ∈ flCircArc ε α β := himg ▸ ⟨η s, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨φ, hφ, hφe⟩ := this
    exact ⟨φ, hφ, by rw [hg]; simp only; rw [hc.Feq (hηH hs)]; exact hφe⟩
  have hsubπ : Ioo α β ⊆ Ioo 0 π := fun φ hφ => ⟨h0α.trans_lt hφ.1, hφ.2.trans_le hβπ⟩
  set θ : ℝ → ℝ := fun s => arg (g s) with hθ
  have hθmem : ∀ s ∈ Ioo (0 : ℝ) 1, θ s ∈ Ioo α β ∧ flCirc ε (θ s) = g s := fun s hs => by
    obtain ⟨φ, hφ, hφe⟩ := hgarc s hs
    have : θ s = φ := by simp only [hθ, ← hφe]; exact fl4_arg_flCirc hε (hsubπ hφ)
    rw [this]; exact ⟨hφ, hφe⟩
  have hθimg : θ '' Ioo 0 1 = Ioo α β := by
    refine Subset.antisymm (image_subset_iff.2 fun s hs => (hθmem s hs).1) fun φ hφ => ?_
    have : flCirc ε φ ∈ fwdMapInv W t '' arcH η := himg ▸ ⟨φ, hφ, rfl⟩
    obtain ⟨_, ⟨s, hs, rfl⟩, hse⟩ := this
    refine ⟨s, hs, ?_⟩
    have e : g s = flCirc ε φ := by rw [hg]; simp only; rw [hc.Feq (hηH hs)]; exact hse
    simp only [hθ, e]; exact fl4_arg_flCirc hε (hsubπ hφ)
  have hθc : ContinuousOn θ (Ioo 0 1) := fun s hs =>
    ((continuousAt_arg (x := g s) (Or.inr (ne_of_gt (hc.F_mem_dom (hηH hs)).1))).comp_continuousWithinAt (f := g)
      (hgc s hs))
  have hθi : InjOn θ (Ioo 0 1) := fun s hs s' hs' h => hgi hs hs' (by
    rw [← (hθmem s hs).2, ← (hθmem s' hs').2]; exact congrArg (flCirc ε) h)
  have hne : (Ioo (0 : ℝ) 1).Nonempty := ⟨1 / 2, by norm_num, by norm_num⟩
  have hbb : BddBelow (θ '' Ioo 0 1) := hθimg ▸ bddBelow_Ioo
  have hba : BddAbove (θ '' Ioo 0 1) := hθimg ▸ bddAbove_Ioo
  have hinf : sInf (θ '' Ioo 0 1) = α := by rw [hθimg]; exact csInf_Ioo hαβ
  have hsup : sSup (θ '' Ioo 0 1) = β := by rw [hθimg]; exact csSup_Ioo hαβ
  -- limits of `g` at the ends
  have hga : Tendsto g (𝓝[>] 0) (𝓝 (F a)) := by
    have h1 : Tendsto η (𝓝[>] 0) (𝓝[Hbar] (a : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨ha, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact hHb (hηH hs)
    exact (hc.Fcont _ (show (0 : ℝ) ≤ ((a : ℂ)).im by simp)).tendsto.comp h1
  have hgb : Tendsto g (𝓝[<] 1) (𝓝 (F b)) := by
    have h1 : Tendsto η (𝓝[<] 1) (𝓝[Hbar] (b : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hb, ?_⟩
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
      exact hHb (hηH hs)
    exact (hc.Fcont _ (show (0 : ℝ) ≤ ((b : ℂ)).im by simp)).tendsto.comp h1
  have hgθ' : ∀ l : Filter ℝ, l ≤ 𝓟 (Ioo 0 1) → ∀ φ : ℝ, Tendsto θ l (𝓝 φ) →
      Tendsto g l (𝓝 (flCirc ε φ)) := fun l hl φ h => by
    refine ((flCirc_continuous ε).tendsto φ |>.comp h).congr' ?_
    filter_upwards [le_principal_iff.1 hl] with s hs
    exact (hθmem s hs).2
  have hl0 : 𝓝[>] (0 : ℝ) ≤ 𝓟 (Ioo 0 1) := le_principal_iff.2 (Ioo_mem_nhdsGT (by norm_num))
  have hl1 : 𝓝[<] (1 : ℝ) ≤ 𝓟 (Ioo 0 1) := le_principal_iff.2 (Ioo_mem_nhdsLT (by norm_num))
  rcases hθc.strictMonoOn_of_injOn_Ioo (by norm_num) hθi with hm | hm
  · left
    have h0 := hm.monotoneOn.tendsto_nhdsWithin_Ioo_right hne hbb
    have h1 := hm.monotoneOn.tendsto_nhdsWithin_Ioo_left hne hba
    rw [hinf] at h0; rw [hsup] at h1
    exact ⟨tendsto_nhds_unique hga (hgθ' _ hl0 _ h0), tendsto_nhds_unique hgb (hgθ' _ hl1 _ h1)⟩
  · right
    have h0 := hm.antitoneOn.tendsto_nhdsWithin_Ioo_right hne hba
    have h1 := hm.antitoneOn.tendsto_nhdsWithin_Ioo_left hne hbb
    rw [hsup] at h0; rw [hinf] at h1
    exact ⟨tendsto_nhds_unique hga (hgθ' _ hl0 _ h0), tendsto_nhds_unique hgb (hgθ' _ hl1 _ h1)⟩

/-- The feet of `η` are distinct. -/
theorem fl4_feet_ne (hc : SideCtx W t F) {ε : ℝ} (hε : 0 < ε) {η : ℝ → ℂ} {a b : ℝ}
    (hη : IsCrosscutH η) (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hsub : arcH η ⊆ {p | ‖fwdMapInv W t p‖ = ε}) : a ≠ b := by
  obtain ⟨α, β, h0α, hαβ, hβπ, -, -, -, hfeet⟩ := fl4_arc_feet hc hε hη ha hb hsub
  intro hab
  subst hab
  have hne : flCirc ε α ≠ flCirc ε β := fun h =>
    hαβ.ne (flCirc_injOn hε ⟨h0α, hαβ.le.trans hβπ⟩ ⟨h0α.trans hαβ.le, hβπ⟩ h)
  rcases hfeet with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne (h1.symm.trans h2)
  · exact hne (h2.symm.trans h1)

end FieldLawler
end QuantumZipper
