import InteractingSLE.Foundations.PrimeEnd.Basic
import InteractingSLE.Foundations.Topology.Schoenflies.Disc

/-!
# Prime ends of Jordan domains

Design `planning/INFRA-GEO.md` §3 (packet GEO-PE). For a bounded domain `D` whose frontier is a
Jordan curve, the prime ends of `D` are the points of `frontier D`: every prime end has a Euclidean
realization, and realization is a homeomorphism `PrimeEnd D ≃ₜ frontier D`
(`PrimeEnd.exists_homeomorph_frontier_of_isJordanCurve`; Carathéodory–Osgood–Taylor, Pommerenke,
*Boundary Behaviour of Conformal Maps*, 1992, Thm 2.6; Specification p. 2: "automatic for Jordan
domains").

Proof. `D` is the bounded component of the complement of `Γ = frontier D`
(`connectedComponentIn_compl_frontier_eq`), so the closed-disc Schoenflies/Carathéodory theorem
(`Foundations.Schoenflies.schoenflies_disc`, from LQGMetric's `jm_jordan_closedDisc_extension'`)
gives `φ`, continuous and injective on the closed unit disc, holomorphic inside, with
`φ(𝔻) = D` and `φ(∂𝔻) = Γ`. The chart is `ψ₀ = cayleyInv ∘ φ⁻¹ : D → ℍ`, so `ψ₀⁻¹ = φ ∘ cayley`
on `ℍ`; the Cayley boundary correspondence `cayleyBdryHomeomorph : ℝ ∪ {∞} ≃ₜ ∂𝔻` and
`φ|∂𝔻 : ∂𝔻 ≃ₜ Γ` (a continuous bijection of compact Hausdorff spaces) give the homeomorphism,
and the realization is the limit of `φ ∘ cayley` along the approach filter
(`tendsto_cayley_approachH`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE

/-- The boundary correspondence of the Cayley transform `z ↦ (z - i)/(z + i)`:
`∞ ↦ 1` and `x ↦ (x - i)/(x + i)` on `ℝ ∪ {∞}`. -/
def cayleyBdry (p : OnePoint ℝ) : ℂ := p.elim 1 fun x => cayley x

@[simp] theorem cayleyBdry_infty : cayleyBdry OnePoint.infty = 1 := rfl

@[simp] theorem cayleyBdry_coe (x : ℝ) : cayleyBdry (x : OnePoint ℝ) = cayley x := rfl

private theorem ofReal_add_I_ne_zero (x : ℝ) : (x : ℂ) + I ≠ 0 :=
  QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (by simp)

private theorem norm_cayley_ofReal (x : ℝ) : ‖cayley x‖ = 1 := by
  have h : (x : ℂ) - I = (starRingEnd ℂ) ((x : ℂ) + I) := by simp [sub_eq_add_neg]
  rw [QuantumZipper.CA.cayley, norm_div, h, Complex.norm_conj,
    div_self (norm_ne_zero_iff.2 (ofReal_add_I_ne_zero x))]

theorem cayleyBdry_mem_sphere (p : OnePoint ℝ) : cayleyBdry p ∈ sphere (0 : ℂ) 1 := by
  cases p with
  | infty => simp
  | coe x => simp [norm_cayley_ofReal]

theorem continuous_cayleyBdry : Continuous cayleyBdry := by
  rw [OnePoint.continuous_iff]
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    refine QuantumZipper.CA.tendsto_cayley_cobounded.comp ?_
    rw [← tendsto_norm_atTop_iff_cobounded]
    have e : (fun x : ℝ => ‖(x : ℂ)‖) = norm := funext fun x => norm_real x
    rw [e]
    exact tendsto_norm_cobounded_atTop
  · exact QuantumZipper.CA.continuousOn_cayley.comp_continuous continuous_ofReal fun x => by
      show (x : ℂ) ≠ -I
      exact QuantumZipper.CA.ne_neg_I_iff.2 (ofReal_add_I_ne_zero x)

theorem cayleyBdry_injective : Injective cayleyBdry := by
  have hne : ∀ x : ℝ, cayley x ≠ 1 := fun x =>
    QuantumZipper.CA.cayley_ne_one (ofReal_add_I_ne_zero x)
  have hHbar : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => by show (0 : ℝ) ≤ (x : ℂ).im; simp
  intro p q hpq
  cases p with
  | infty =>
    cases q with
    | infty => rfl
    | coe y => exact absurd hpq.symm (hne y)
  | coe x =>
    cases q with
    | infty => exact absurd hpq (hne x)
    | coe y =>
      have := QuantumZipper.CA.bijOn_cayley_Hbar.injOn (hHbar x) (hHbar y) hpq
      exact congrArg _ (ofReal_injective this)

theorem exists_cayleyBdry_eq {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) : ∃ p, cayleyBdry p = w := by
  by_cases h1 : w = 1
  · exact ⟨OnePoint.infty, h1.symm⟩
  · have hnorm : ‖w‖ = 1 := by simpa using hw
    have him : (cayleyInv w).im = 0 := by
      rw [QuantumZipper.CA.im_cayleyInv, hnorm]; simp
    refine ⟨((cayleyInv w).re : OnePoint ℝ), ?_⟩
    rw [cayleyBdry_coe]
    have : ((cayleyInv w).re : ℂ) = cayleyInv w := Complex.ext (by simp) (by simp [him])
    rw [this, QuantumZipper.CA.cayley_cayleyInv h1]

/-- The Cayley boundary correspondence `ℝ ∪ {∞} ≃ₜ ∂𝔻`. -/
def cayleyBdryHomeomorph : OnePoint ℝ ≃ₜ sphere (0 : ℂ) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun p => ⟨cayleyBdry p, cayleyBdry_mem_sphere p⟩)
      ⟨fun p q h => cayleyBdry_injective (congrArg Subtype.val h), fun w => by
        obtain ⟨p, hp⟩ := exists_cayleyBdry_eq w.2
        exact ⟨p, Subtype.ext hp⟩⟩)
    (continuous_cayleyBdry.subtype_mk _)

@[simp] theorem cayleyBdryHomeomorph_apply (p : OnePoint ℝ) :
    (cayleyBdryHomeomorph p : ℂ) = cayleyBdry p := rfl

/-- Along the approach filter at `x`, the Cayley transform tends to `cayleyBdry x` from inside the
unit disc. -/
theorem tendsto_cayley_approachH (x : OnePoint ℝ) :
    Tendsto cayley (PrimeEnd.approachH x) (𝓝[ball 0 1] (cayleyBdry x)) := by
  have hball : ∀ᶠ z in PrimeEnd.approachH x, cayley z ∈ ball (0 : ℂ) 1 :=
    Filter.mem_of_superset (PrimeEnd.H_mem_approachH x) fun z hz =>
      QuantumZipper.CA.cayley_mem_ball hz
  refine tendsto_nhdsWithin_iff.2 ⟨?_, hball⟩
  cases x with
  | infty => exact QuantumZipper.CA.tendsto_cayley_cobounded.mono_left inf_le_left
  | coe r =>
    have hc : ContinuousAt cayley (r : ℂ) :=
      (QuantumZipper.CA.differentiableAt_cayley (ofReal_add_I_ne_zero r)).continuousAt
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The inverse Cayley transform is a bijection of the unit disc onto `ℍ` (as QuantumZipper's
`CA.Uniformizer.bijOn_cayleyInv_ball`, whose module has a much larger import closure). -/
private theorem bijOn_cayleyInv_ball : BijOn cayleyInv (ball (0 : ℂ) 1) H := by
  have hB1 : ∀ w ∈ ball (0 : ℂ) 1, w ≠ 1 := by
    intro w hw h; subst h; simp at hw
  refine ⟨fun w hw => QuantumZipper.CA.cayleyInv_mem_H hw, fun w hw w' hw' h => ?_,
    fun z hz => ?_⟩
  · rw [← QuantumZipper.CA.cayley_cayleyInv (hB1 w hw), h,
      QuantumZipper.CA.cayley_cayleyInv (hB1 w' hw')]
  · exact ⟨cayley z, QuantumZipper.CA.cayley_mem_ball hz,
      QuantumZipper.CA.cayleyInv_cayley
        (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hz))⟩

/-- An open connected set whose frontier `Γ` misses `p₀ ∈ D` is the component of `Γᶜ` through
`p₀`. -/
theorem connectedComponentIn_compl_frontier_eq {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsConnected D) {p₀ : ℂ} (hp₀ : p₀ ∈ D) :
    connectedComponentIn (frontier D)ᶜ p₀ = D := by
  have hDΓ : D ⊆ (frontier D)ᶜ := fun z hz hzf => by
    have := hDo.inter_frontier_eq
    exact (Set.eq_empty_iff_forall_notMem.1 this) z ⟨hz, hzf⟩
  refine Subset.antisymm ?_ (hDc.isPreconnected.subset_connectedComponentIn hp₀ hDΓ)
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hDo
    isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.2 subset_closure) ?_
    ⟨p₀, mem_connectedComponentIn (hDΓ hp₀), hp₀⟩
  intro z hz
  have hz' : z ∉ frontier D := connectedComponentIn_subset _ _ hz
  rw [frontier, hDo.interior_eq] at hz'
  by_cases hzc : z ∈ closure D
  · exact Or.inl (by_contra fun h => hz' ⟨hzc, h⟩)
  · exact Or.inr hzc

namespace PrimeEnd

/-- **Carathéodory–Osgood–Taylor** for Jordan domains: every prime end has a unique
realization, and realization is a homeomorphism onto `frontier D` (Specification p. 2:
"automatic for Jordan domains"). -/
theorem exists_homeomorph_frontier_of_isJordanCurve {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsConnected D) (hDb : Bornology.IsBounded D)
    (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier D)) :
    ∃ e : PrimeEnd D ≃ₜ frontier D, ∀ p : PrimeEnd D, p.IsRealizedAt (e p) := by
  obtain ⟨p₀, hp₀⟩ := hDc.nonempty
  have hDeq := connectedComponentIn_compl_frontier_eq hDo hDc hp₀
  have hp₀Γ : p₀ ∈ (frontier D)ᶜ := by
    rw [← hDeq] at hp₀; exact connectedComponentIn_subset _ _ hp₀
  obtain ⟨φ, hφc, hφi, hφd, -, hφball, hφsph⟩ :=
    Foundations.Schoenflies.schoenflies_disc hJ hp₀Γ (by rw [hDeq]; exact hDb)
  rw [hDeq] at hφball
  -- the chart `ψ₀ = cayleyInv ∘ φ⁻¹ : D → ℍ`
  have hφi' : InjOn φ (ball 0 1) := hφi.mono ball_subset_closedBall
  set e := QuantumZipper.CA.univalentOPH isOpen_ball hφd hφi'
  have hsymm_mem : ∀ z ∈ D, e.symm z ∈ ball (0 : ℂ) 1 := fun z hz => by
    have : z ∈ e.target := by
      rw [QuantumZipper.CA.univalentOPH_target, hφball]; exact hz
    exact e.map_target this
  have hφe : ∀ z ∈ D, φ (e.symm z) = z := fun z hz =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply isOpen_ball hφd hφi' (by rw [hφball]; exact hz)
  have heφ : ∀ w ∈ ball (0 : ℂ) 1, e.symm (φ w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball hφd hφi' hw
  have hB1 : ∀ w ∈ ball (0 : ℂ) 1, w ≠ 1 := by
    intro w hw h; subst h; simp at hw
  have hψd : DifferentiableOn ℂ (cayleyInv ∘ e.symm) D := by
    have hs := QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball hφd hφi'
    rw [hφball] at hs
    intro z hz
    have h1 : DifferentiableAt ℂ cayleyInv (e.symm z) :=
      QuantumZipper.CA.differentiableAt_cayleyInv (hB1 _ (hsymm_mem z hz))
    exact (h1.comp z ((hs z hz).differentiableAt (hDo.mem_nhds hz))).differentiableWithinAt
  have hsymm_bij : BijOn e.symm D (ball 0 1) := by
    refine ⟨fun z hz => hsymm_mem z hz, fun z hz z' hz' h => ?_, fun w hw => ?_⟩
    · rw [← hφe z hz, h, hφe z' hz']
    · refine ⟨φ w, ?_, heφ w hw⟩
      rw [← hφball]; exact mem_image_of_mem φ hw
  let ψ₀ : HChart D := ⟨cayleyInv ∘ e.symm, hψd, bijOn_cayleyInv_ball.comp hsymm_bij⟩
  have hinv : ∀ ζ ∈ H, invFunOn ψ₀.1 D ζ = φ (cayley ζ) := by
    intro ζ hζ
    have hc := QuantumZipper.CA.cayley_mem_ball hζ
    have hz : φ (cayley ζ) ∈ D := by rw [← hφball]; exact mem_image_of_mem φ hc
    have : ψ₀.1 (φ (cayley ζ)) = ζ := by
      show cayleyInv (e.symm (φ (cayley ζ))) = ζ
      rw [heφ _ hc, QuantumZipper.CA.cayleyInv_cayley
        (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt hζ))]
    rw [← this, ψ₀.invFunOn_apply hz, this]
  -- the boundary homeomorphism `∂𝔻 ≃ₜ frontier D`
  have hsph : ∀ w ∈ sphere (0 : ℂ) 1, φ w ∈ frontier D := fun w hw => by
    rw [← hφsph]; exact mem_image_of_mem φ hw
  have : CompactSpace (sphere (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  let F : sphere (0 : ℂ) 1 → frontier D := fun w => ⟨φ w, hsph w w.2⟩
  have hF : Bijective F := by
    refine ⟨fun w w' h => Subtype.ext (hφi (sphere_subset_closedBall w.2)
      (sphere_subset_closedBall w'.2) (congrArg Subtype.val h)), fun y => ?_⟩
    have hy : (y : ℂ) ∈ φ '' sphere 0 1 := by rw [hφsph]; exact y.2
    obtain ⟨w, hw, hwy⟩ := hy
    exact ⟨⟨w, hw⟩, Subtype.ext hwy⟩
  have hFc : Continuous F :=
    ((hφc.mono sphere_subset_closedBall).comp_continuous continuous_subtype_val
      (fun w => w.2)).subtype_mk _
  let Φ : sphere (0 : ℂ) 1 ≃ₜ frontier D :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hF) hFc
  refine ⟨(mkHomeomorph hDo ψ₀).symm.trans (cayleyBdryHomeomorph.trans Φ), fun p => ?_⟩
  set x := (mkHomeomorph hDo ψ₀).symm p
  have hx : mk ψ₀ x = p := (mkHomeomorph hDo ψ₀).apply_symm_apply p
  have hval : (((mkHomeomorph hDo ψ₀).symm.trans (cayleyBdryHomeomorph.trans Φ) p :
      frontier D) : ℂ) = φ (cayleyBdry x) := rfl
  refine ⟨ψ₀, x, hx, ?_⟩
  rw [hval]
  have hcw : ContinuousWithinAt φ (closedBall 0 1) (cayleyBdry x) :=
    hφc _ (sphere_subset_closedBall (cayleyBdry_mem_sphere x))
  have h1 := (tendsto_cayley_approachH x).mono_right (nhdsWithin_mono _ ball_subset_closedBall)
  refine (hcw.tendsto.comp h1).congr' ?_
  filter_upwards [H_mem_approachH x] with ζ hζ
  exact (hinv ζ hζ).symm

end PrimeEnd

end InteractingSLE
