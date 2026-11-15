/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7RetainedPath
import InteractingSLE.Spec.Supplement.G7ClockCluster
import InteractingSLE.Spec.Restart.ClockAssembly

/-!
# The geometry of a retained continuation (Lemma G7: seed, confinement, relative domains)

Packet PROVE-G7B. Lemma G7 (`source/spec/p481-528.md`, pp. 497–498). Retain the union `K = O ∪ η([0, a])` of the
prefix of a path `η` and another compact set `O` (the other retained prefix), with active domain
`D = ℍ \ fill K`, and continue `η` after its tip `p = η(a) ∈ ℍ`, `p ∉ O`, `p ∈ closure D`, until its first new
contact with `K`.

* **Charts of `D`** (`IsDomChart`): the forward map `φ : D → ℍ` and its inverse `ψ : ℍ → D` with the properties the
  clocks use; every retained chart is one (`IsRetChart.isDomChart`). For such charts: the forward image of the
  unbounded domain of a larger compact set avoids a chart path (`IsDomChart.fwd_image_subset`), the inverse image of
  the unbounded domain of a chart path lies in the unbounded domain of the enlarged set
  (`IsDomChart.inv_image_subset`), the hull identity and the **additivity of capacity**
  (`IsDomChart.hcapSet_fillH_eq_add`).
* **Seed** (`eventually_mem_of_seed`; G7's proof: "At the initial point, the other retained prefix has positive
  physical clearance. In the current path's own hydrodynamic chart, its additional retained filled hull is away from
  the driver"): the continuation enters `D` immediately. Map out the path's own prefix with its own first-contact
  chart `(φ₀, ψ₀)` at the tip; `ψ₀` is continuous at the tip's preimage `w₀` and `ψ₀(w₀) = p ∉ O`, so
  `V = ψ₀(B(w₀, ρ) ∩ ℍ)` is a connected set off `K`; it meets `D` because `φ₀(z) → w₀` as `z → p` in `D`; hence
  `V ⊆ D`. The continuation is in `V` just after `a` by the tip property of the trace.
* **Confinement** (`mem_closure_of_noContact`; G7's proof: "After that seed, connectedness and avoidance of `A` keep
  every interior point of the continued trace in `D`. An untouched original-real point has a trace-free upper
  half-neighborhood, which is wholly in `D` whenever it is approached from `D`"): the label dichotomy
  (`HalfPlaneSep.isFreeAt_or_isTrappedAt_of_isPreconnected`) along the connected continuation.
* **Relative domains** (`mem_relDomain_of_noContact`, Janiszewski): before the first new contact,
  `D ∩ (ℍ \ fill η([0, s])) ⊆ ℍ \ fill(O ∪ η([0, s]))`, since `K ∩ η([0, s]) = η([0, a])` is connected and attached
  to `ℝ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### Charts of an unbounded domain -/

/-- **A chart of the unbounded domain** `ℍ \ fill K`: a conformal bijection `φ` onto `ℍ` sending `∞` to `∞`, with
inverse `ψ` on `ℍ`, continuous on `ℍ̄`, mapping real points off the domain, with bounded displacement. -/
structure IsDomChart (K : Set ℂ) (φ ψ : ℂ → ℂ) : Prop where
  bijOn_fwd : BijOn φ (H \ fillH K) H
  differentiableOn_fwd : DifferentiableOn ℂ φ (H \ fillH K)
  cobounded : Tendsto φ (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH K)) (Bornology.cobounded ℂ)
  bijOn_inv : BijOn ψ H (H \ fillH K)
  fwd_inv : ∀ w ∈ H, φ (ψ w) = w
  inv_notMem : ∀ w ∉ H, ψ w ∉ H \ fillH K
  differentiableOn_inv : DifferentiableOn ℂ ψ H
  continuousOn_inv : ContinuousOn ψ Hbar
  bdd : ∃ M : ℝ, ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M

/-- **A first-contact chart is a chart of the active domain.** -/
theorem _root_.InteractingSLE.Restart.IsFirstContactChart.isDomChart {η₁ η₂ : ℝ≥0 → ℂ} {s₀ t₀ : ℝ≥0}
    {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ} (hC : IsFirstContactChart η₁ s₀ η₂ t₀ φ ψ lift)
    (hK : IsClosed (prefixSet η₁ s₀ η₂ t₀)) : IsDomChart (prefixSet η₁ s₀ η₂ t₀) φ ψ := by
  have hD := activeDomain_eq hK
  obtain ⟨⟨h1, h2, -, h4⟩, h5, h6, h7, -, -, h10, h11, -, h13, -⟩ := hC
  rw [hD] at h1 h2 h4 h5 h7
  exact ⟨h1, h2, h4, h5, h6, h7, h10, h11, h13⟩

/-- **A retained chart is a chart of the retained active domain.** -/
theorem IsRetChart.isDomChart {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
    (hC : IsRetChart α a β b φ ψ lift) (h0₂ : (β 0).im = 0) (hK : IsClosed (prefixSet α a β b)) :
    IsDomChart (prefixSet α a β b) φ ψ := by
  have hD := activeDomain_eq hK
  obtain ⟨h1, h2, -, h4⟩ := hC.isActiveChart h0₂
  have h5 := hC.bijOn h0₂
  have h7 := hC.inv_notMem h0₂
  rw [hD] at h1 h2 h4 h5 h7
  exact ⟨h1, h2, h4, h5, hC.fwd_inv, h7, hC.differentiableOn_inv, hC.continuousOn_inv,
    hC.2.2.2.2.2.2.2.2.2.1⟩

namespace IsDomChart

variable {K : Set ℂ} {φ ψ : ℂ → ℂ} (hD : IsDomChart K φ ψ)
include hD

theorem continuousOn_fwd : ContinuousOn φ (H \ fillH K) := hD.differentiableOn_fwd.continuousOn

theorem mapsTo_fwd : MapsTo φ (H \ fillH K) H := hD.bijOn_fwd.mapsTo

theorem inv_fwd {z : ℂ} (hz : z ∈ H \ fillH K) : ψ (φ z) = z := by
  obtain ⟨w, hw, rfl⟩ := hD.bijOn_inv.surjOn hz
  rw [hD.fwd_inv w hw]

theorem mem_H_of_inv_mem {w : ℂ} (hw : ψ w ∈ H \ fillH K) : w ∈ H := by
  by_contra h
  exact hD.inv_notMem w h hw

theorem injOn_inv : InjOn ψ H := hD.bijOn_inv.injOn

theorem inv_real_notMem_image (x : ℂ) (hx : x.im = 0) : ψ x ∉ ψ '' H := by
  rw [hD.bijOn_inv.image_eq]
  refine hD.inv_notMem x fun h => ?_
  have : (0 : ℝ) < x.im := h
  rw [hx] at this
  exact lt_irrefl _ this

/-- `ψ` maps `ℍ̄` into the closure of the domain. -/
theorem inv_mem_closure {w : ℂ} (hw : w ∈ Hbar) : ψ w ∈ closure (H \ fillH K) := by
  have hcw : ContinuousWithinAt ψ H w := (hD.continuousOn_inv w hw).mono QuantumZipper.H_subset_Hbar
  have hcl : w ∈ closure H := by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hw
  exact closure_mono hD.bijOn_inv.mapsTo.image_subset (hcw.mem_closure_image hcl)

/-- The forward image of an unbounded subset of the domain is unbounded. -/
theorem not_isBounded_image {X : Set ℂ} (hXD : X ⊆ H \ fillH K) (hX : ¬ Bornology.IsBounded X) :
    ¬ Bornology.IsBounded (φ '' X) := by
  intro hB
  have h0 : (φ '' X)ᶜ ∈ Bornology.cobounded ℂ := hB
  have h1 := hD.cobounded h0
  rw [mem_map, mem_inf_principal] at h1
  refine hX ((Bornology.isBounded_compl_iff.2 h1).subset fun z hz hz' => ?_)
  exact hz' (hXD hz) ⟨z, hz, rfl⟩

omit hD in
/-- `‖w‖ ≤ ‖ψ w‖ + M`. -/
theorem norm_le_of_inv {M : ℝ} (hM : ∀ w ∈ Hbar, ‖ψ w - w‖ ≤ M) {w : ℂ} (hw : w ∈ Hbar) :
    ‖w‖ ≤ ‖ψ w‖ + M := by
  have h1 := norm_sub_le (ψ w) (ψ w - w)
  rw [sub_sub_cancel] at h1
  linarith [hM w hw]

variable {Γ : ℝ≥0 → ℂ} {t : ℝ≥0} {P : Set ℂ}

/-- **The forward image of the unbounded domain of a larger compact set `P`** avoids a chart path whose
`ψ`-image lies in `P`: it lies in the unbounded domain of `Γ([0, t])`. -/
theorem fwd_image_subset (hP : IsCompact P) (hKP : fillH K ⊆ fillH P) (hΓc : ContinuousOn Γ (Icc 0 t))
    (hΓP : ∀ r ∈ Icc 0 t, ψ (Γ r) ∈ P) : φ '' (H \ fillH P) ⊆ H \ fillH (Γ '' Icc 0 t) := by
  have hsub : H \ fillH P ⊆ H \ fillH K := sdiff_subset_sdiff_right hKP
  have hX : IsPreconnected (φ '' (H \ fillH P)) :=
    (HalfPlaneSep.isPreconnected_H_diff_fillH hP.isClosed hP.isBounded).image _ (hD.continuousOn_fwd.mono hsub)
  have hXu : ¬ Bornology.IsBounded (φ '' (H \ fillH P)) :=
    hD.not_isBounded_image hsub (HalfPlaneSep.not_isBounded_H_diff_fillH hP.isClosed hP.isBounded)
  refine HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded
    (isCompact_Icc.image_of_continuousOn hΓc).isClosed hX hXu ?_
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨hD.mapsTo_fwd (hsub hz), ?_⟩
  rintro ⟨r, hr, hrz⟩
  have hzP : z ∈ P := by rw [← hD.inv_fwd (hsub hz), ← hrz]; exact hΓP r hr
  exact hz.2 (mem_fillH_of_mem_closure hz.1 (subset_closure hzP))

/-- **The inverse image of the unbounded domain of a chart path** lies in the unbounded domain of any compact set
`P` made of `K` and of points of the mapped path. -/
theorem inv_image_subset (hP : IsCompact P) (hPK : P ⊆ K ∪ ψ '' (Γ '' Icc 0 t))
    (hΓc : ContinuousOn Γ (Icc 0 t)) : ψ '' (H \ fillH (Γ '' Icc 0 t)) ⊆ H \ fillH P := by
  obtain ⟨M, hM⟩ := hD.bdd
  have hA : IsCompact (Γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hΓc
  have hHA : H \ fillH (Γ '' Icc 0 t) ⊆ H := sdiff_subset
  have hX : IsPreconnected (ψ '' (H \ fillH (Γ '' Icc 0 t))) :=
    (HalfPlaneSep.isPreconnected_H_diff_fillH hA.isClosed hA.isBounded).image _
      (hD.continuousOn_inv.mono (hHA.trans QuantumZipper.H_subset_Hbar))
  have hXu : ¬ Bornology.IsBounded (ψ '' (H \ fillH (Γ '' Icc 0 t))) := by
    intro hB
    obtain ⟨R, hR⟩ := hB.subset_closedBall 0
    refine HalfPlaneSep.not_isBounded_H_diff_fillH hA.isClosed hA.isBounded
      ((isBounded_closedBall (x := (0 : ℂ)) (r := R + M)).subset fun w hw => ?_)
    have h1 := hR ⟨w, hw, rfl⟩
    rw [mem_closedBall_zero_iff] at h1 ⊢
    linarith [norm_le_of_inv hM (QuantumZipper.H_subset_Hbar hw.1)]
  refine HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded hP.isClosed hX hXu ?_
  rintro _ ⟨w, hw, rfl⟩
  have hwD : ψ w ∈ H \ fillH K := hD.bijOn_inv.mapsTo hw.1
  refine ⟨hwD.1, fun hwP => ?_⟩
  rcases hPK hwP with hwK | ⟨_, ⟨r, hr, rfl⟩, hre⟩
  · exact hwD.2 (mem_fillH_of_mem_closure hwD.1 (subset_closure hwK))
  · have hΓrH : Γ r ∈ H := hD.mem_H_of_inv_mem (by rw [hre]; exact hwD)
    have hwr : w = Γ r := hD.injOn_inv hw.1 hΓrH hre.symm
    exact hw.2 (mem_fillH_of_mem_closure hw.1 (subset_closure ⟨r, hr, hwr.symm⟩))

/-- **The hull identity**: `φ(fill P \ fill K) = fill Γ([0, t])` when `P` is `K` plus the mapped chart path. -/
theorem fwd_image_fillH_diff_eq (hP : IsCompact P) (hKP : fillH K ⊆ fillH P)
    (hPK : P ⊆ K ∪ ψ '' (Γ '' Icc 0 t)) (hΓc : ContinuousOn Γ (Icc 0 t))
    (hΓP : ∀ r ∈ Icc 0 t, ψ (Γ r) ∈ P) : φ '' (fillH P \ fillH K) = fillH (Γ '' Icc 0 t) := by
  have hsub : H \ fillH P ⊆ H \ fillH K := sdiff_subset_sdiff_right hKP
  have himg : φ '' (H \ fillH P) = H \ fillH (Γ '' Icc 0 t) := by
    refine Subset.antisymm (hD.fwd_image_subset hP hKP hΓc hΓP) fun w hw => ?_
    exact ⟨ψ w, hD.inv_image_subset hP hPK hΓc ⟨w, hw, rfl⟩, hD.fwd_inv w hw.1⟩
  have hdiff : fillH P \ fillH K = (H \ fillH K) \ (H \ fillH P) := by
    ext z
    constructor
    · rintro ⟨hzP, hzK⟩
      exact ⟨⟨fillH_subset_H _ hzP, hzK⟩, fun h => h.2 hzP⟩
    · rintro ⟨⟨hzH, hzK⟩, hz⟩
      exact ⟨by_contra fun h => hz ⟨hzH, h⟩, hzK⟩
  rw [hdiff, image_sdiff_of_injOn hD.bijOn_fwd.injOn hsub, hD.bijOn_fwd.image_eq, himg]
  ext z
  exact ⟨fun h => by_contra fun h' => h.2 ⟨h.1, h'⟩, fun h => ⟨fillH_subset_H _ h, fun h' => h'.2 h⟩⟩

/-- **Additivity of capacity** (composition rule): for the hydrodynamic chart `φ = g − x₀`, `x₀` real,
`hcap(fill P) = hcap(fill Γ([0, t])) + hcap(fill K)`. -/
theorem hcapSet_fillH_eq_add {g : ℂ → ℂ} {x₀ : ℂ} (hg : IsMapOut (fillH K) g) (hφ : ∀ z, φ z = g z - x₀)
    (hx₀ : x₀.im = 0) (hKh : IsHPHull (fillH K)) (hPh : IsHPHull (fillH P)) (hP : IsCompact P)
    (hKP : fillH K ⊆ fillH P) (hPK : P ⊆ K ∪ ψ '' (Γ '' Icc 0 t)) (hΓc : ContinuousOn Γ (Icc 0 t))
    (hΓ0 : (Γ 0).im ≤ 0) (hΓP : ∀ r ∈ Icc 0 t, ψ (Γ r) ∈ P) :
    ConformalImage.hcapSet (fillH P) = ConformalImage.hcapSet (fillH (Γ '' Icc 0 t)) +
      ConformalImage.hcapSet (fillH K) := by
  have hΓ := isHPHull_fillH_image hΓc hΓ0
  have hadd := HPHull.hcap_eq_add (A := ⟨_, hKh⟩) (B := ⟨_, hPh⟩) hKP hg
  have himg : g '' (fillH P \ fillH K) = affHomeo 1 one_pos x₀.re '' fillH (Γ '' Icc 0 t) := by
    rw [← hD.fwd_image_fillH_diff_eq hP hKP hPK hΓc hΓP, image_image, coe_affHomeo]
    refine image_congr fun z _ => ?_
    have hx : (x₀.re : ℂ) = x₀ := Complex.ext (by simp) (by simp [hx₀])
    beta_reduce
    rw [hφ, ofReal_one, one_mul, hx, sub_add_cancel]
  have htr := HPHull.hcap_affHomeo (x := x₀.re) ⟨_, hΓ⟩ one_pos
  rw [ConformalImage.hcapSet_eq hPh, ConformalImage.hcapSet_eq hΓ, ConformalImage.hcapSet_eq hKh, hadd]
  congr 1
  exact (HPHull.hcap_congr (B := ⟨_, hΓ.image_affHomeo one_pos⟩) himg).trans (htr.trans (by ring))

end IsDomChart

/-! ### Good paths -/

namespace IsPathGood

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x)
include hp

/-- The tip property of a good path. -/
theorem mem_closure_tip {u s : ℝ≥0} (hus : u < s) (hsζ : (s : ℝ≥0∞) ≤ ζ) :
    η s ∈ closure (H \ fillH (η '' Icc 0 u)) := by
  obtain ⟨-, w, hw, hw0, hg⟩ := hp
  exact IsGeneratingTrace.mem_closure_of_lt_add hg hw hw0 hus hsζ

/-- Interior times are dense along a good path. -/
theorem exists_mem_H_between {a b : ℝ≥0} (hab : a < b) (hbζ : (b : ℝ≥0∞) ≤ ζ) : ∃ s ∈ Ioo a b, η s ∈ H := by
  obtain ⟨-, w, hw, hw0, hg⟩ := hp
  exact IsGeneratingTrace.exists_mem_H_add hg hw hw0 hab hbζ

theorem mem_Hbar_of_le {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ) : η s ∈ Hbar := by
  rcases (zero_le : (0 : ℝ≥0) ≤ s).lt_or_eq with h | h
  · have := mem_closure_tip hp h hs
    rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact closure_mono sdiff_subset this
  · rw [← h]
    show 0 ≤ (η 0).im
    rw [hp.seed]

theorem continuousOn_Icc_of_le {a : ℝ≥0} (ha : (a : ℝ≥0∞) ≤ ζ) : ContinuousOn η (Icc 0 a) :=
  hp.continuousOn.mono fun _ hs => (ENNReal.coe_le_coe.2 hs.2).trans ha

theorem mapsTo_Icc_of_le {a : ℝ≥0} (ha : (a : ℝ≥0∞) ≤ ζ) : MapsTo η (Icc 0 a) Hbar := fun _ hs =>
  mem_Hbar_of_le hp ((ENNReal.coe_le_coe.2 hs.2).trans ha)

theorem isCompact_image_Icc_of_le {a : ℝ≥0} (ha : (a : ℝ≥0∞) ≤ ζ) : IsCompact (η '' Icc 0 a) :=
  isCompact_Icc.image_of_continuousOn (continuousOn_Icc_of_le hp ha)

/-- A later point is not on an earlier prefix. -/
theorem notMem_image_Icc_of_lt {a t : ℝ≥0} (hat : a < t) (htζ : (t : ℝ≥0∞) ≤ ζ) : η t ∉ η '' Icc 0 a := by
  rintro ⟨s, hs, he⟩
  have := hp.1 ((ENNReal.coe_le_coe.2 (hs.2.trans hat.le)).trans htζ) htζ he
  exact absurd (this ▸ hs.2) (not_le.2 hat)

theorem continuousAt_of_lt {a : ℝ≥0} (haζ : (a : ℝ≥0∞) < ζ) : ContinuousAt η a :=
  hp.continuousOn.continuousAt (Filter.mem_of_superset
    ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds haζ)
      fun t (ht : (t : ℝ≥0∞) < ζ) => show (t : ℝ≥0∞) ≤ ζ from le_of_lt ht)

/-! ### The seed -/

/-- **The seed of a retained continuation** (Lemma G7's proof, p. 497): if the tip `η(a)` is interior, off the
closed set `O`, and adherent to `D = ℍ \ fill(O ∪ η([0, a]))`, then `η(t) ∈ D` for all `t > a` close to `a`. -/
theorem eventually_mem_of_seed {a : ℝ≥0} (haζ : (a : ℝ≥0∞) < ζ) {O : Set ℂ} (hO : IsClosed O)
    (hpH : η a ∈ H) (hpO : η a ∉ O) (hcl : η a ∈ closure (H \ fillH (O ∪ η '' Icc 0 a))) :
    ∀ᶠ t in 𝓝[>] a, η t ∈ H \ fillH (O ∪ η '' Icc 0 a) := by
  set K := O ∪ η '' Icc 0 a with hKdef
  have hca := continuousOn_Icc_of_le hp haζ.le
  have hHa := mapsTo_Icc_of_le hp haζ.le
  have hne : ∀ s < a, η s ≠ η a := fun s hs he =>
    hs.ne (hp.1 ((ENNReal.coe_le_coe.2 hs.le).trans haζ.le) haζ.le he)
  have hP : prefixSet η a η a = η '' Icc 0 a := union_self _
  have hKa : IsClosed (η '' Icc 0 a) := (isCompact_image_Icc_of_le hp haζ.le).isClosed
  have hU₀ : activeDomain η a η a = H \ fillH (η '' Icc 0 a) := by
    rw [activeDomain_eq (by rw [hP]; exact hKa), hP]
  have hDU : H \ fillH K ⊆ H \ fillH (η '' Icc 0 a) := sdiff_subset_sdiff_right (fillH_mono subset_union_right)
  have hcl₀ : η a ∈ closure (activeDomain η a η a) := by rw [hU₀]; exact closure_mono hDU hcl
  obtain ⟨φ₀, ψ₀, lift₀, hC₀⟩ := exists_isFirstContactChart hca hca hHa hHa hp.seed hp.seed rfl hne hne hcl₀
  have hreg : IsChartRegularPoint η a η a (η a) :=
    Or.inr (isUnboundedLinked_firstContact hca hca hp.seed hp.seed rfl hne hne)
  obtain ⟨w₀, hw₀, hlim, hψw₀, -⟩ := hC₀.2.2.2.2.2.2.2.2.2.2 (η a) hcl₀ hreg
  rw [hU₀] at hlim
  -- `ψ₀` stays off `O` near `w₀`
  have hψc : ContinuousWithinAt ψ₀ Hbar w₀ := hC₀.2.2.2.2.2.2.2.1 w₀ hw₀
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO.isOpen_compl (η a) hpO
  obtain ⟨ρ, hρ, hρε⟩ := Metric.continuousWithinAt_iff.1 hψc ε hε
  have hρO : ∀ w ∈ ball w₀ ρ ∩ H, ψ₀ w ∉ O := fun w hw => by
    have h1 := hρε (QuantumZipper.H_subset_Hbar hw.2) hw.1
    rw [hψw₀] at h1
    exact hεO h1
  set V := ψ₀ '' (ball w₀ ρ ∩ H) with hV
  have hVc : IsPreconnected V := (HalfPlaneSep.isPreconnected_ball_inter_H w₀ ρ).image _
    (hC₀.2.2.2.2.2.2.2.1.mono fun w hw => QuantumZipper.H_subset_Hbar hw.2)
  have hU₀sub : ∀ w ∈ H, ψ₀ w ∈ H \ fillH (η '' Icc 0 a) := fun w hw => by
    rw [← hU₀]; exact hC₀.2.1.mapsTo hw
  have hVK : V ⊆ H \ K := by
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hU₀sub w hw.2
    refine ⟨h1.1, ?_⟩
    rintro (hO' | hA)
    · exact hρO w hw hO'
    · exact h1.2 (mem_fillH_of_mem_closure h1.1 (subset_closure hA))
  have hKc : IsClosed K := hO.union hKa
  -- `V` meets `D`
  obtain ⟨z, hzD, hzV⟩ : ∃ z ∈ H \ fillH K, z ∈ V := by
    have hne' : (𝓝[H \ fillH K] (η a)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have h1 : Tendsto φ₀ (𝓝[H \ fillH K] (η a)) (𝓝 w₀) := hlim.mono_left (nhdsWithin_mono _ hDU)
    obtain ⟨z, hzb, hzD⟩ := ((h1.eventually (ball_mem_nhds w₀ hρ)).and self_mem_nhdsWithin).exists
    have hzU : z ∈ activeDomain η a η a := by rw [hU₀]; exact hDU hzD
    exact ⟨z, hzD, φ₀ z, ⟨hzb, hC₀.1.1.mapsTo hzU⟩, hC₀.inv_fwd hzU⟩
  have hVD : V ⊆ H \ fillH K := fun v hv =>
    HalfPlaneSep.connectedComponentIn_subset_H_diff_fillH hKc hzD (hVc.subset_connectedComponentIn hzV hVK hv)
  -- the continuation just after `a`
  have hηc := continuousAt_of_lt hp haζ
  have hζev : ∀ᶠ t : ℝ≥0 in 𝓝[>] a, (t : ℝ≥0∞) ≤ ζ := by
    have h1 : ∀ᶠ t : ℝ≥0 in 𝓝 a, (t : ℝ≥0∞) < ζ :=
      (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds haζ
    exact nhdsWithin_le_nhds (h1.mono fun t ht => ht.le)
  have hHev : ∀ᶠ t in 𝓝[>] a, η t ∈ H :=
    nhdsWithin_le_nhds (hηc.eventually (QuantumZipper.isOpen_H.mem_nhds hpH))
  have hevU : ∀ᶠ t in 𝓝[>] a, η t ∈ H \ fillH (η '' Icc 0 a) := by
    filter_upwards [hζev, hHev, self_mem_nhdsWithin] with t htζ htH hat
    exact mem_H_diff_fillH_of_mem_closure hKa htH (notMem_image_Icc_of_lt hp hat htζ) (mem_closure_tip hp hat htζ)
  have htend : Tendsto η (𝓝[>] a) (𝓝[H \ fillH (η '' Icc 0 a)] (η a)) :=
    tendsto_nhdsWithin_iff.2 ⟨hηc.tendsto.mono_left nhdsWithin_le_nhds, hevU⟩
  filter_upwards [hevU, (hlim.comp htend).eventually (ball_mem_nhds w₀ hρ)] with t htU htb
  have htU' : η t ∈ activeDomain η a η a := by rw [hU₀]; exact htU
  rw [← hC₀.inv_fwd htU']
  exact hVD ⟨φ₀ (η t), ⟨htb, hC₀.1.1.mapsTo htU'⟩, rfl⟩

/-! ### Confinement and relative domains -/

/-- **Confinement before the first new contact** (Lemma G7's proof, p. 497): every point of the continuation up to
and including its first new contact with `K = O ∪ η([0, a])` is adherent to `D = ℍ \ fill K`. -/
theorem mem_closure_of_noContact {a : ℝ≥0} (haζ : (a : ℝ≥0∞) < ζ) {O : Set ℂ} (hO : IsCompact O)
    (hpH : η a ∈ H) (hpO : η a ∉ O) (hcl : η a ∈ closure (H \ fillH (O ∪ η '' Icc 0 a))) {t : ℝ≥0}
    (hat : a < t) (htζ : (t : ℝ≥0∞) ≤ ζ) (hno : ∀ t' : ℝ≥0, a < t' → t' < t → η t' ∉ O ∪ η '' Icc 0 a) :
    η t ∈ closure (H \ fillH (O ∪ η '' Icc 0 a)) := by
  set K := O ∪ η '' Icc 0 a with hKdef
  have hKc : IsCompact K := hO.union (isCompact_image_Icc_of_le hp haζ.le)
  obtain ⟨t₁, ht₁D, ht₁⟩ : ∃ t₁, η t₁ ∈ H \ fillH K ∧ t₁ ∈ Ioo a t :=
    ((eventually_mem_of_seed hp haζ hO.isClosed hpH hpO hcl).and (Ioo_mem_nhdsGT hat)).exists
  have hct : ContinuousOn η (Icc a t) :=
    hp.continuousOn.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans htζ
  have hX : IsPreconnected (η '' Ioo a t) := isPreconnected_Ioo.image _ (hct.mono Ioo_subset_Icc_self)
  have hXF : η '' Ioo a t ⊆ {w | 0 ≤ w.im} \ K := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨mem_Hbar_of_le hp ((ENNReal.coe_le_coe.2 hs.2.le).trans htζ), hno s hs.1 hs.2⟩
  have hfree : ∀ s ∈ Ioo a t, η s ∈ closure (H \ fillH K) := by
    rcases HalfPlaneSep.isFreeAt_or_isTrappedAt_of_isPreconnected hKc.isClosed hX hXF with hall | hall
    · intro s hs
      have hf := hall _ ⟨s, hs, rfl⟩
      have hcl' : η s ∈ closure H := by
        rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
        exact mem_Hbar_of_le hp ((ENNReal.coe_le_coe.2 hs.2.le).trans htζ)
      exact closure_mono inter_subset_right (HalfPlaneSep.mem_closure_inter_of_isFreeAt hcl' subset_rfl hf)
    · exact absurd ht₁D (hall _ ⟨t₁, ht₁, rfl⟩).notMem
  have h := mem_closure_of_left (ζ := ζ) (X := closure (H \ fillH K)) hat htζ (hp.continuousOn t htζ)
    fun c hac hct' => by
      obtain ⟨s, hcs, hst⟩ := exists_between hct'
      exact ⟨s, ⟨hcs, hst⟩, hfree s ⟨hac.trans_lt hcs, hst⟩⟩
  rwa [closure_closure] at h

/-- **Relative domains before the first new contact** (Janiszewski, as in Aux. lemma 76): a continuation point
`η(t)` in `D = ℍ \ fill(O ∪ η([0, a]))`, with no contact with `O` on `(a, s]`, `s < t`, is in the unbounded domain
of `O ∪ η([0, s])`. -/
theorem mem_relDomain_of_noContact {a s t : ℝ≥0} (has : a ≤ s) (hst : s < t) (htζ : (t : ℝ≥0∞) ≤ ζ)
    {O : Set ℂ} (hO : IsCompact O) (hno : ∀ t' : ℝ≥0, a < t' → t' ≤ s → η t' ∉ O)
    (htD : η t ∈ H \ fillH (O ∪ η '' Icc 0 a)) : η t ∈ H \ fillH (O ∪ η '' Icc 0 s) := by
  have hsζ : (s : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hst.le).trans htζ
  have haζ : (a : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 has).trans hsζ
  have hF₂ := isCompact_image_Icc_of_le hp hsζ
  have hF₁ : IsCompact (O ∪ η '' Icc 0 a) := hO.union (isCompact_image_Icc_of_le hp haζ)
  have hts : η t ∈ H \ fillH (η '' Icc 0 s) :=
    mem_H_diff_fillH_of_mem_closure hF₂.isClosed htD.1 (notMem_image_Icc_of_lt hp hst htζ) (mem_closure_tip hp hst htζ)
  have hunion : O ∪ η '' Icc 0 s = (O ∪ η '' Icc 0 a) ∪ η '' Icc 0 s := by
    rw [union_assoc, union_eq_right.2 (image_mono (Icc_subset_Icc_right has))]
  rw [hunion]
  refine HalfPlaneSep.H_diff_fillH_inter_subset hF₁ hF₂ (fun w hw => ?_) ⟨htD, hts⟩
  have hwa : w ∈ η '' Icc 0 a := by
    obtain ⟨hw₁, ⟨t', ht', rfl⟩⟩ := hw
    by_cases hta : t' ≤ a
    · exact ⟨t', ⟨zero_le, hta⟩, rfl⟩
    · push Not at hta
      rcases hw₁ with hO' | ⟨t'', ht'', he⟩
      · exact absurd hO' (hno t' hta ht'.2)
      · have := hp.1 ((ENNReal.coe_le_coe.2 ht''.2).trans haζ) ((ENNReal.coe_le_coe.2 ht'.2).trans hsζ) he
        exact absurd (this ▸ ht''.2) (not_le.2 hta)
  exact ⟨η '' Icc 0 a, fun v hv => ⟨Or.inr hv, image_mono (Icc_subset_Icc_right has) hv⟩,
    isPreconnected_Icc.image _ (continuousOn_Icc_of_le hp haζ), hwa, η 0, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩, hp.seed⟩

end IsPathGood

end Supp7

end InteractingSLE
