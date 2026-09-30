import QuantumZipper.Proofs.Thm18.LWFarSideMain
import QuantumZipper.Proofs.Thm18.LWExcDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-IMAGETOP (partial): the context and the crosscut images of circle arcs

Task FL-IMAGETOP (helper of FL-THM, D75), towards `FieldLawler.FLImageTopStmt`
(`FieldLawlerSubSum.lean`).

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015)
no. 10, arXiv:1407.3314, proof of Prop. 3.4 (p. 9, first display): `D ∩ C_ε = ⋃ⱼ ηⱼ`, the
`ηⱼ` crosscuts of `D = H_t`, and `Z_t ηⱼ` crosscuts of `ℍ`.

Proved here:
* `flTop_ctx`: the Carathéodory context `SideCtx W t F` (continuous extension `F` of
  `Z_t⁻¹ = fwdMapInv W t` to `ℍ̄`, Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.1/2.6,
  via `CaraR.extExists`) from the hypotheses of `FLImageTopStmt`, which only concern `[0, t]`
  (the proof is that of `lwfSide_ctx`, with the hypotheses localised to `[0, t]`).
* `flArc`: the `Z_t`-image of the circle arc `{ε e^{iθ} : α < θ < β}`, parametrised on `(0,1)`;
  `flArc_props`: if the arc lies in `H_t`, its image is continuous, injective, in `ℍ`, and lies in
  the level set `{p | ‖fwdMapInv W t p‖ = ε}` (all conditions of `IsCrosscutH` except the endpoint
  limits); `flArc_disjoint`: images of disjoint arcs are disjoint.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ}

/-- The context `SideCtx` from the hypotheses of `FLImageTopStmt` (data on `[0, t]` only). -/
theorem flTop_ctx (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t)
    (htr0 : trace W 0 = 0) (htrc : ContinuousOn (trace W) (Icc 0 t))
    (hinj : InjOn (trace W) (Icc 0 t)) (htrH : ∀ s ∈ Ioc 0 t, trace W s ∈ H)
    (hhull : fwdHull W t = trace W '' Ioc 0 t) :
    ∃ F : ℂ → ℂ, SideCtx W t F ∧
      CaraR.RevExt (ArcDriver.trev W t) t (fun s => trace W (t * s)) F := by
  set γ : ℝ → ℂ := fun s => trace W (t * s) with hγdef
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, t * s ∈ Icc 0 t := fun s hs =>
    ⟨mul_nonneg ht.le hs.1, mul_le_of_le_one_right ht.le hs.2⟩
  have hγc : ContinuousOn γ (Icc 0 1) :=
    htrc.comp (continuousOn_const.mul continuousOn_id) hmem
  have hγi : InjOn γ (Icc 0 1) := fun a ha b hb h =>
    mul_left_cancel₀ ht.ne' (hinj (hmem a ha) (hmem b hb) h)
  have hγ0 : (γ 0).im = 0 := by simp [hγdef, htr0]
  have hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H := fun u hu =>
    htrH _ ⟨mul_pos ht hu.1, mul_le_of_le_one_right ht.le hu.2⟩
  have himg : γ '' Ioc 0 1 = trace W '' Ioc 0 t := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨t * s, ⟨mul_pos ht hs.1, mul_le_of_le_one_right ht.le hs.2⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r / t, ⟨div_pos hr.1 ht, (div_le_one ht).2 hr.2⟩, by
        simp only [hγdef, mul_div_cancel₀ _ ht.ne']⟩
  have hrev : revHull (ArcDriver.trev W t) t = γ '' Ioc 0 1 := by
    rw [ArcDriver.revHull_trev hW hW0 ht, hhull, himg]
  obtain ⟨F, hF⟩ := CaraR.extExists _ (ArcDriver.continuous_trev hW t) (ArcDriver.trev_zero W t)
    t ht γ hγc hγi hγ0 hγH hrev
  have hK : IsSimpleCurveHull (fwdHull W t) :=
    ⟨γ, hγc, hγi, hγ0, hγH, by rw [hhull, himg]⟩
  obtain ⟨C, hC⟩ := ArcDriver.exists_bound_revMap_trev hW hW0 ht CaraR.revMapCaratheodory hK
  have hFeq : EqOn F (fwdMapInv W t) H := fun u hu => by
    rw [hF.eqOn hu, UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht.le hu]
    rfl
  have hF0 : F 0 = trace W t := by
    have h1 : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[Hbar] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
          ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        show 0 ≤ ((y : ℂ) * I).im
        simpa using (le_of_lt (show (0 : ℝ) < y from hy))
    have h2 := (hF.cont 0 (show (0 : ℂ) ∈ Hbar by simp [Hbar])).tendsto.comp h1
    have hT : Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (F 0)) := by
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hFeq (show 0 < ((y : ℂ) * I).im by simpa using (show (0 : ℝ) < y from hy))
    exact (hT.limUnder_eq).symm
  have hγ1 : γ 1 = trace W t := by simp [hγdef]
  refine ⟨F, ⟨hW, hW0, ht, hF.cont, hFeq, fun x hx => ?_, hF0, ⟨C, fun u hu => ?_⟩,
    hhull, htrc, htr0⟩, hF⟩
  · have h0 : F ((0 : ℝ) : ℂ) = γ 1 := by rw [Complex.ofReal_zero, hF0, hγ1]
    exact hF.inj_tip x 0 (by rw [hx, hγ1]) h0
  · rw [hF.eqOn hu]; exact hC u hu

/-- The circle point `ε e^{iθ}`. -/
def flCirc (ε θ : ℝ) : ℂ := (ε : ℂ) * exp ((θ : ℂ) * I)

lemma flCirc_norm {ε : ℝ} (hε : 0 < ε) (θ : ℝ) : ‖flCirc ε θ‖ = ε := by
  simp [flCirc, norm_exp_ofReal_mul_I, abs_of_pos hε]

lemma flCirc_injOn {ε : ℝ} (hε : 0 < ε) : InjOn (flCirc ε) (Icc 0 π) := by
  intro a ha b hb h
  have h1 : (flCirc ε a).re = (flCirc ε b).re := by rw [h]
  have hre : ∀ θ : ℝ, (flCirc ε θ).re = ε * Real.cos θ := fun θ => by
    simp [flCirc, Complex.exp_ofReal_mul_I_re]
  rw [hre, hre] at h1
  exact Real.injOn_cos ha hb (mul_left_cancel₀ hε.ne' h1)

lemma flCirc_continuous (ε : ℝ) : Continuous (flCirc ε) := by
  unfold flCirc; fun_prop

/-- The affine angle parametrisation of `(α, β)` by `(0, 1)`. -/
def flAng (α β s : ℝ) : ℝ := α + s * (β - α)

lemma flAng_mem {α β s : ℝ} (hab : α < β) (hs : s ∈ Ioo (0 : ℝ) 1) : flAng α β s ∈ Ioo α β := by
  unfold flAng
  have h := sub_pos.2 hab
  constructor <;> nlinarith [hs.1, hs.2]

lemma flAng_injective {α β : ℝ} (hab : α < β) : Function.Injective (flAng α β) := by
  intro a b h
  unfold flAng at h
  have := sub_pos.2 hab
  have h' : a * (β - α) = b * (β - α) := by linarith
  exact mul_right_cancel₀ this.ne' h'

/-- The `Z_t`-image of the circle arc `{ε e^{iθ} : α < θ < β}`, parametrised by `(0, 1)`. -/
def flArc (W : ℝ → ℝ) (t ε α β : ℝ) (s : ℝ) : ℂ := fwdMap W t (flCirc ε (flAng α β s))

/-- **Image of an arc of `H_t ∩ C_ε`.** Continuity, injectivity, values in `ℍ`, and the level set
`‖Z_t⁻¹‖ = ε`: every condition of `IsCrosscutH` except the endpoint limits. -/
theorem flArc_props {t : ℝ} {F : ℂ → ℂ} (hc : SideCtx W t F) {ε α β : ℝ} (hε : 0 < ε)
    (hab : α < β) (h0α : 0 ≤ α) (hβπ : β ≤ π)
    (hD : ∀ θ ∈ Ioo α β, flCirc ε θ ∈ H \ fwdHull W t) :
    ContinuousOn (flArc W t ε α β) (Ioo 0 1) ∧ InjOn (flArc W t ε α β) (Ioo 0 1) ∧
      MapsTo (flArc W t ε α β) (Ioo 0 1) H ∧
      arcH (flArc W t ε α β) ⊆ {p | ‖fwdMapInv W t p‖ = ε} := by
  have hmem : ∀ s ∈ Ioo (0 : ℝ) 1, flCirc ε (flAng α β s) ∈ H \ fwdHull W t := fun s hs =>
    hD _ (flAng_mem hab hs)
  have hinv : ∀ s ∈ Ioo (0 : ℝ) 1, fwdMapInv W t (flArc W t ε α β s) = flCirc ε (flAng α β s) :=
    fun s hs => by
      show fwdMapInv W t (fwdMap W t (flCirc ε (flAng α β s))) = _
      rw [← hc.Feq (hc.mapsTo (hmem s hs))]
      exact hc.F_fwdMap (hmem s hs)
  refine ⟨?_, ?_, fun s hs => hc.mapsTo (hmem s hs), ?_⟩
  · refine hc.continuousOn_fwdMap.comp ?_ hmem
    exact ((flCirc_continuous ε).comp (by unfold flAng; fun_prop)).continuousOn
  · intro a ha b hb h
    have h2 := hinv a ha
    rw [h, hinv b hb] at h2
    have hIcc : ∀ s ∈ Ioo (0 : ℝ) 1, flAng α β s ∈ Icc 0 π := fun s hs =>
      ⟨h0α.trans (flAng_mem hab hs).1.le, (flAng_mem hab hs).2.le.trans hβπ⟩
    exact flAng_injective hab (flCirc_injOn hε (hIcc a ha) (hIcc b hb) h2.symm)
  · rintro p ⟨s, hs, rfl⟩
    show ‖fwdMapInv W t (flArc W t ε α β s)‖ = ε
    rw [hinv s hs, flCirc_norm hε]

/-- Images of disjoint arcs of `H_t ∩ C_ε` are disjoint. -/
theorem flArc_disjoint {t : ℝ} {F : ℂ → ℂ} (hc : SideCtx W t F) {ε α β α' β' : ℝ} (hε : 0 < ε)
    (hab : α < β) (h0α : 0 ≤ α) (hβπ : β ≤ π) (hab' : α' < β') (h0α' : 0 ≤ α') (hβπ' : β' ≤ π)
    (hD : ∀ θ ∈ Ioo α β, flCirc ε θ ∈ H \ fwdHull W t)
    (hD' : ∀ θ ∈ Ioo α' β', flCirc ε θ ∈ H \ fwdHull W t)
    (hdisj : Disjoint (Ioo α β) (Ioo α' β')) :
    Disjoint (arcH (flArc W t ε α β)) (arcH (flArc W t ε α' β')) := by
  rw [Set.disjoint_left]
  rintro p ⟨s, hs, rfl⟩ ⟨s', hs', he⟩
  have hm := hD _ (flAng_mem hab hs)
  have hm' := hD' _ (flAng_mem hab' hs')
  have h1 := hc.F_fwdMap hm
  have h2 := hc.F_fwdMap hm'
  unfold flArc at he
  rw [he] at h2
  rw [h1] at h2
  have hθ := flCirc_injOn hε ⟨h0α'.trans (flAng_mem hab' hs').1.le,
    (flAng_mem hab' hs').2.le.trans hβπ'⟩ ⟨h0α.trans (flAng_mem hab hs).1.le,
    (flAng_mem hab hs).2.le.trans hβπ⟩ h2.symm
  exact Set.disjoint_left.1 hdisj (flAng_mem hab hs) (hθ ▸ flAng_mem hab' hs')

end FieldLawler
end QuantumZipper
