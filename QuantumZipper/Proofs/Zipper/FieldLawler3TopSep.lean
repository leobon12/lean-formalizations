import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopSign
import QuantumZipper.Proofs.Thm18.LWExcDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-TOP: the outer side of a positive arc does not reach the left boundary

Task FL3-TOP (Track A, input of `FLImageSumBoundStmt`). Field–Lawler, *Escape probability and
transience for SLE*, EJP 20 (2015), proof of Prop. 3.4, p. 9, and (2.1): the comparison
`ℰ_ℍ(Z_t ηⱼ, ℝ₋) ≤ ℰ_{H_t}(ηⱼ, C_R)` uses that, in `H_t ∩ B(0, R)`, the region beyond a
positive arc `ηⱼ` only meets the boundary part `Z_t⁻¹(ℝ₊)` of `H_t` (the hull `K_t` separates
the half-disk, and the tip is its only point on `C_R`). FL use this without comment.

All statements are in image coordinates `u = Z_t z`, with `F` the continuous boundary
extension of `Z_t⁻¹` (`SideCtx`), `U = {u ∈ ℍ : ‖Z_t⁻¹ u‖ < R} = Z_t(H_t ∩ B(0, R))`.

* `fl3top_no_path`: no path in `ℍ̄` from `u₁ < 0` to `u₂ > 0` has `F`-image in `B(0, R)`
  (compactness reduces it to `fl_no_sep_path` with a radius `ρ < R`).
* `fl3top_no_cross`: an open connected `Ω ⊆ U` cannot have in its closure both a real `u₁ < 0`
  and a real `u₂ > 0` with `‖F uᵢ‖ < R`.
* `fl3top_pos_of_foot`: if moreover `Ω` is adjacent to an image crosscut `ζ = Z_t η` with a foot
  `a > 0` (`arcH ζ ⊆ closure Ω`, `‖Z_t⁻¹‖ = ε < R` on `ζ`), then every real `u₀ ∈ closure Ω` with
  `‖F u₀‖ < R` satisfies `0 < u₀`. For `Ω = Z_t W` (`W` the component of `(H_t ∩ B(0,R)) \ η`
  beyond `η`) this is the boundary fact needed for the maximum-principle comparison
  `G ∘ Z_t ≤ V` on `W`: frontier points of `W` inside `B(0, R)` correspond only to reals `> 0`.

Own elementary argument (the separation step is `fl_no_sep_path`, itself the winding-number
argument of `lwfSide_sign`); no published proof of this implicit step was found (FL p. 9).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- The set `{u ∈ ℍ̄ : ‖F u‖ < R}`. -/
def fl3topS (F : ℂ → ℂ) (R : ℝ) : Set ℂ := {z | z ∈ Hbar ∧ ‖F z‖ < R}

/-- **Separation.** No path in `ℍ̄` from `u₁ < 0` to `u₂ > 0` has `F`-image in `B(0, R)`. -/
theorem fl3top_no_path (hc : SideCtx W t F) {R : ℝ} (hH : trace W t ∈ H)
    (hnorm : ‖trace W t‖ = R) (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) {u₁ u₂ : ℝ} (hu₁ : u₁ < 0)
    (hu₂ : 0 < u₂) (h : JoinedIn (fl3topS F R) (u₁ : ℂ) (u₂ : ℂ)) : False := by
  obtain ⟨σ, hσ⟩ := h
  have hcF : Continuous fun s => ‖F (σ s)‖ :=
    continuous_norm.comp (hc.Fcont.comp_continuous σ.continuous fun s => (hσ s).1)
  obtain ⟨s₀, -, hs₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcF.continuousOn
  exact fl_no_sep_path hc (hσ s₀).2 hH hnorm hle hu₁ hu₂ σ (fun s => (hσ s).1)
    (fun s => hs₀ (mem_univ s))

/-- A real boundary point `u` of `Ω ⊆ ℍ` with `‖F u‖ < R` is joined to a point of `Ω`
inside `{‖F‖ < R} ∩ ℍ̄`. -/
theorem fl3top_joined_near (hc : SideCtx W t F) {R : ℝ} {Ω : Set ℂ} (hΩH : Ω ⊆ H) {u : ℝ}
    (hu : ‖F u‖ < R) (hcl : (u : ℂ) ∈ closure Ω) :
    ∃ p ∈ Ω, JoinedIn (fl3topS F R) (u : ℂ) p := by
  have huH : (u : ℂ) ∈ Hbar := by simp [Hbar]
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousWithinAt_iff.1 (hc.Fcont _ huH) (R - ‖F u‖)
    (by linarith)
  obtain ⟨p, hpΩ, hpd⟩ := Metric.mem_closure_iff.1 hcl δ hδ
  set B : Set ℂ := ball (u : ℂ) δ ∩ {z | (0 : ℝ) ≤ Complex.imLm z} with hB
  have hBc : Convex ℝ B := (convex_ball _ _).inter (convex_halfSpace_ge Complex.imLm.isLinear 0)
  have huB : (u : ℂ) ∈ B := ⟨mem_ball_self hδ, by simp⟩
  have hpB : p ∈ B := ⟨by rw [mem_ball, dist_comm]; exact hpd,
    by simpa using (le_of_lt (hΩH hpΩ : 0 < p.im))⟩
  refine ⟨p, hpΩ, ((hBc.isPathConnected ⟨_, huB⟩).joinedIn _ huB _ hpB).mono ?_⟩
  rintro z ⟨hzb, hzi⟩
  have hzH : z ∈ Hbar := by simpa [Hbar] using hzi
  refine ⟨hzH, ?_⟩
  have h1 := hδF hzH (by simpa using hzb)
  have h2 : ‖F z‖ ≤ ‖F u‖ + dist (F z) (F u) := by
    rw [dist_eq_norm]
    calc ‖F z‖ = ‖F u + (F z - F u)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  linarith

/-- **No crossing.** An open connected `Ω ⊆ {u ∈ ℍ : ‖Z_t⁻¹ u‖ < R}` cannot have in its
closure both a real `u₁ < 0` and a real `u₂ > 0` with `‖F uᵢ‖ < R`. -/
theorem fl3top_no_cross (hc : SideCtx W t F) {R : ℝ} (hH : trace W t ∈ H)
    (hnorm : ‖trace W t‖ = R) (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsConnected Ω) (hΩH : Ω ⊆ H) (hΩF : ∀ z ∈ Ω, ‖fwdMapInv W t z‖ < R) {u₁ u₂ : ℝ}
    (hu₁ : u₁ < 0) (hu₂ : 0 < u₂) (h₁ : (u₁ : ℂ) ∈ closure Ω) (h₂ : (u₂ : ℂ) ∈ closure Ω)
    (hF₁ : ‖F u₁‖ < R) (hF₂ : ‖F u₂‖ < R) : False := by
  obtain ⟨p₁, hp₁, hj₁⟩ := fl3top_joined_near hc hΩH hF₁ h₁
  obtain ⟨p₂, hp₂, hj₂⟩ := fl3top_joined_near hc hΩH hF₂ h₂
  have hΩS : Ω ⊆ fl3topS F R := fun z hz =>
    ⟨show (0:ℝ) ≤ z.im from le_of_lt (hΩH hz : 0 < z.im), by rw [hc.Feq (hΩH hz)]; exact hΩF z hz⟩
  have hj : JoinedIn (fl3topS F R) p₁ p₂ :=
    ((hΩo.isConnected_iff_isPathConnected.1 hΩc).joinedIn _ hp₁ _ hp₂).mono hΩS
  exact fl3top_no_path hc hH hnorm hle hu₁ hu₂ ((hj₁.trans hj).trans hj₂.symm)

/-- **The outer side of a positive arc meets the real line only on the right.** Let `ζ` be an
image crosscut (`ζ(0,1) ⊆ ℍ`, `ζ(s) → a > 0` as `s ↓ 0`) with `‖Z_t⁻¹‖ = ε < R` on `ζ(0,1)`,
and let `Ω ⊆ {u ∈ ℍ : ‖Z_t⁻¹ u‖ < R}` be open, connected, with `ζ(0,1) ⊆ closure Ω`. Then every
real `u₀ ∈ closure Ω` with `‖F u₀‖ < R` is `> 0`. -/
theorem fl3top_pos_of_foot (hc : SideCtx W t F) {R ε : ℝ} (hεR : ε < R) (hH : trace W t ∈ H)
    (hnorm : ‖trace W t‖ = R) (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) {Ω : Set ℂ} (hΩo : IsOpen Ω)
    (hΩc : IsConnected Ω) (hΩH : Ω ⊆ H) (hΩF : ∀ z ∈ Ω, ‖fwdMapInv W t z‖ < R)
    {ζ : ℝ → ℂ} {a : ℝ} (ha : 0 < a) (hζa : Tendsto ζ (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hζH : MapsTo ζ (Ioo 0 1) H) (hζε : arcH ζ ⊆ {p | ‖fwdMapInv W t p‖ = ε})
    (hζΩ : arcH ζ ⊆ closure Ω) {u₀ : ℝ} (hu₀ : (u₀ : ℂ) ∈ closure Ω) (hF₀ : ‖F u₀‖ < R) :
    0 < u₀ := by
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- the foot `a` is in the closure of `Ω`
  have haΩ : (a : ℂ) ∈ closure Ω := by
    rw [← closure_closure (s := Ω)]
    exact mem_closure_of_tendsto hζa (hev.mono fun s hs => hζΩ ⟨s, hs, rfl⟩)
  -- `‖F a‖ = ε`
  have haH : (a : ℂ) ∈ Hbar := by simp [Hbar]
  have hlim : Tendsto (fun s => ‖F (ζ s)‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖F a‖) := by
    refine (continuous_norm.tendsto _).comp ((hc.Fcont _ haH).tendsto.comp ?_)
    exact tendsto_nhdsWithin_iff.2 ⟨hζa, hev.mono fun s hs => show (0:ℝ) ≤ (ζ s).im from le_of_lt (hζH hs : 0 < (ζ s).im)⟩
  have hconst : Tendsto (fun s => ‖F (ζ s)‖) (𝓝[>] (0 : ℝ)) (𝓝 ε) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with s hs
    rw [hc.Feq (hζH hs)]
    exact (hζε ⟨s, hs, rfl⟩).symm
  have hFa : ‖F a‖ = ε := tendsto_nhds_unique hlim hconst
  -- `u₀ ≠ 0` and `u₀ ≮ 0`
  rcases lt_trichotomy u₀ 0 with h | h | h
  · exact (fl3top_no_cross hc hH hnorm hle hΩo hΩc hΩH hΩF h ha hu₀ haΩ hF₀
      (by rw [hFa]; exact hεR)).elim
  · subst h
    have : ‖F ((0 : ℝ) : ℂ)‖ = R := by rw [Complex.ofReal_zero, hc.F0, hnorm]
    linarith
  · exact h

end FieldLawler
end QuantumZipper
