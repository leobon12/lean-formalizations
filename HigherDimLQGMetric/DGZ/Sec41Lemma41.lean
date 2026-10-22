import HigherDimLQGMetric.DGZ.Sec41Defs
import HigherDimLQGMetric.DGZ.FreeSites
import HigherDimLQGMetric.DGZ.Discretize

/-!
# DGZ Lemma 4.1, corrected (packet L3c1; MA7 D-4.1)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 4.1 (TeX l. 1350–1358, p. 26), whose
proof uses an unproved d-dimensional "duality" (gap G1 of the planning audit
`planning/audits/MA7-ref2-sections-4-6.md`); the repair is MA7 Details (a) D-4.1, which works with
*free* sites (D-F1–D-FS, packet L3a1) and the discretization of continuous paths (D-DISC, L3a2).

Everything here is deterministic. For a configuration `O ⊆ ℤ^d` of open sites whose closed sites
lie in a box `[-R, R]^d` (`d ≥ 2`):

* `isOpenCluster_infCluster`, `infinite_infCluster`, `mem_infCluster_of_not_withinInf`,
  `eq_infCluster_of_isOpenCluster`, `eq_infCluster_of_infinite` (Lemma 4.1, first claim): the
  unbounded open cluster `𝒪 = infCluster O` is an infinite open cluster, it contains every site
  outside the box, and every unbounded (equivalently, infinite) open cluster equals it (no
  smallness of the closed clusters is needed);
* `infCluster_eq_freeSite` (MA7 D-4.1 (i)): if moreover `SmallClusters O D`, then `𝒪` is the set
  of free sites;
* `exists_path_near_of_mem_infCluster` (Lemma 4.1, second claim; MA7 D-4.1 (ii)): under
  `SmallClusters O D`, for every open connected `U ⊆ ℝ^d`, mesh `s > 0`, and `u, v ∈ 𝒪` with
  `s u, s v ∈ U`, there is a simple open L-path from `u` to `v` whose sites `x` satisfy
  `s x ∈ B_{(D+2)s}(U)` (`ℓ^∞` neighbourhood; MA7 states the radius `(D+3)s`).
* **`lemma41`**: the statement for DGZ's `m`-open configuration (`mOpen`, mesh `2^{-m}`, closed
  sites in `𝓛_m`, `D_m = m² - 101²` on `ℰ_{m,n}`), with the radius `(D_m + 2) 2^{-m}`, and
  `lemma41_dgzRadius` with DGZ's radius `m² 2^{1-m}` (`m ≥ 1`);
* `mem_eventF_iff`: on `ℰ_{m,n} ∩ ℰ_{m-1,n}`, the free-site form `eventF` of `ℱ_{m,n}` is DGZ's
  (4.7) literally (`y ∈ 𝒪_m ∩ 𝒪_{m-1}`).

Proof of (ii) (MA7 D-4.1, with the open variant of D-DISC). An open connected subset of `ℝ^d` is
path connected; extend a path from `s u` to `s v` inside `U` to `ℝ` (`Path.extend`, whose range is
the range of the path, so it stays in `U`); its range is compact, so it lies in a lattice box
`obox 0 (sN)`. The open variant of D-DISC (`exists_discretization`) gives a simple L-path of sites
`x`, each with `s x` within `ℓ^∞`-distance `< s` of a point of the path, whose first and last
sites `x₀, x₁` satisfy `s u ∈ obox (s x₀) s`, `s v ∈ obox (s x₁) s`; as `s u` and `s x₀` are both
lattice points, this forces `x₀ = u` and `x₁ = v` (no end corrections are needed). `u, v` are free
(`infCluster_eq_freeSite`), so free surgery (D-FS(i), `freeSurgery`) gives an open L-path from `u`
to `v` within lattice distance `D + 1` of the reference path; loop-erase it. A site `y` of the
result is within `(D + 1) s + s` (strictly less than `(D + 2) s`) of a point of the path in `U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Relation

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### Far sites -/

/-- The constant site `(R', …, R')` lies outside the box `[-R, R]^d` when `R < R'` (`d ≥ 1`). -/
lemma not_withinInf_const (hd : 1 ≤ d) {R R' : ℤ} (h : R < R') :
    ¬ WithinInf R (fun _ => R' : Zd d) 0 := by
  intro hw
  have := hw ⟨0, by omega⟩
  dsimp only at this
  rw [Pi.zero_apply, sub_zero, abs_le] at this
  omega

section Cluster

variable {O : Set (Zd d)} {R : ℤ}

/-- Two sites outside a box `[-R, R]^d` containing all closed sites are joined by an open L-path
(`d ≥ 2`; the complement of a box is L-connected). -/
lemma reflTransGen_of_not_withinInf (hd : 2 ≤ d) (hR : ∀ y, y ∉ O → WithinInf R y 0)
    {x y : Zd d} (hx : ¬ WithinInf R x 0) (hy : ¬ WithinInf R y 0) :
    ReflTransGen (StepIn O LAdj) x y := by
  have hC : ∀ c ∈ Oᶜ, WithinInf R c 0 := fun c hc => hR c hc
  have h1 : ReflTransGen (StepIn Oᶜᶜ LAdj) x (fun _ => R + 1) := mem_ext_of_not_withinInf hd hC hx
  have h2 : ReflTransGen (StepIn Oᶜᶜ LAdj) y (fun _ => R + 1) := mem_ext_of_not_withinInf hd hC hy
  rw [compl_compl] at h1 h2
  exact h1.trans (reflTransGen_lAdj_symm h2)

/-- Every site outside a box `[-R, R]^d` containing all closed sites lies in the unbounded open
cluster (`d ≥ 2`). -/
lemma mem_infCluster_of_not_withinInf (hd : 2 ≤ d) (hR : ∀ y, y ∉ O → WithinInf R y 0)
    {x : Zd d} (hx : ¬ WithinInf R x 0) : x ∈ infCluster O := by
  refine ⟨?_, fun R' => ?_⟩
  · by_contra h
    exact hx (hR x h)
  · refine ⟨fun _ => max R R' + 1, not_withinInf_const (by omega) (by omega), ?_⟩
    exact reflTransGen_of_not_withinInf hd hR hx (not_withinInf_const (by omega) (by omega))

lemma infCluster_subset (O : Set (Zd d)) : infCluster O ⊆ O := fun _ hx => hx.1

/-- `𝒪` is closed under open L-steps. -/
lemma mem_infCluster_of_lAdj {x y : Zd d} (hx : x ∈ infCluster O) (hy : y ∈ O) (hxy : LAdj x y) :
    y ∈ infCluster O := by
  refine ⟨hy, fun R' => ?_⟩
  obtain ⟨v, hv, hxv⟩ := hx.2 R'
  exact ⟨v, hv, (ReflTransGen.single ⟨hy, hx.1, hxy.symm⟩).trans hxv⟩

/-- `𝒪` is closed under open L-paths. -/
lemma mem_infCluster_of_reflTransGen {x y : Zd d} (hx : x ∈ infCluster O)
    (h : ReflTransGen (StepIn O LAdj) x y) : y ∈ infCluster O := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact mem_infCluster_of_lAdj ih hbc.2.1 hbc.2.2

/-- An open L-path from a site of `𝒪` stays in `𝒪`. -/
lemma reflTransGen_infCluster {x y : Zd d} (hx : x ∈ infCluster O)
    (h : ReflTransGen (StepIn O LAdj) x y) : ReflTransGen (StepIn (infCluster O) LAdj) x y := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail hab hbc ih =>
    have hb := mem_infCluster_of_reflTransGen hx hab
    exact ih.tail ⟨hb, mem_infCluster_of_lAdj hb hbc.2.1 hbc.2.2, hbc.2.2⟩

/-- An open cluster is closed under open L-paths. -/
lemma mem_of_reflTransGen_of_isOpenCluster {K : Set (Zd d)} (hK : IsOpenCluster O K)
    {x y : Zd d} (hx : x ∈ K) (h : ReflTransGen (StepIn O LAdj) x y) : y ∈ K := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact hK.2.2.2 _ ih _ hbc.2.1 hbc.2.2

/-- **DGZ Lemma 4.1, existence of `𝒪`**: the unbounded open cluster is an open cluster (`d ≥ 2`,
closed sites in a box). -/
theorem isOpenCluster_infCluster (hd : 2 ≤ d) (hR : ∀ y, y ∉ O → WithinInf R y 0) :
    IsOpenCluster O (infCluster O) := by
  refine ⟨⟨fun _ => R + 1, mem_infCluster_of_not_withinInf hd hR
    (not_withinInf_const (by omega) (by omega))⟩, infCluster_subset O, fun x hx y hy => ?_,
    fun x hx y hy hxy => mem_infCluster_of_lAdj hx hy hxy⟩
  obtain ⟨v, hv, hxv⟩ := hx.2 R
  obtain ⟨w, hw, hyw⟩ := hy.2 R
  exact reflTransGen_infCluster hx
    ((hxv.trans (reflTransGen_of_not_withinInf hd hR hv hw)).trans (reflTransGen_lAdj_symm hyw))

/-- **DGZ Lemma 4.1, uniqueness of `𝒪`**: every unbounded open cluster is `𝒪` (`d ≥ 2`, closed
sites in a box). -/
theorem eq_infCluster_of_isOpenCluster (hd : 2 ≤ d) (hR : ∀ y, y ∉ O → WithinInf R y 0)
    {K : Set (Zd d)} (hK : IsOpenCluster O K) (hunb : ∀ R' : ℤ, ∃ x ∈ K, ¬ WithinInf R' x 0) :
    K = infCluster O := by
  obtain ⟨x₀, hx₀K, hx₀⟩ := hunb R
  have hx₀O : x₀ ∈ infCluster O := mem_infCluster_of_not_withinInf hd hR hx₀
  ext y
  constructor
  · intro hy
    have h : ReflTransGen (StepIn O LAdj) y x₀ :=
      reflTransGen_stepIn_mono hK.2.1 (hK.2.2.1 y hy x₀ hx₀K)
    exact mem_infCluster_of_reflTransGen hx₀O (reflTransGen_lAdj_symm h)
  · intro hy
    obtain ⟨v, hv, hyv⟩ := hy.2 R
    have h : ReflTransGen (StepIn O LAdj) y x₀ :=
      hyv.trans (reflTransGen_of_not_withinInf hd hR hv hx₀)
    exact mem_of_reflTransGen_of_isOpenCluster hK hx₀K (reflTransGen_lAdj_symm h)

/-- **MA7 D-4.1 (i)**: under `SmallClusters O D`, the unbounded open cluster is the set of free
sites (`d ≥ 2`, closed sites in a box). -/
theorem infCluster_eq_freeSite (hd : 2 ≤ d) (hR : ∀ y, y ∉ O → WithinInf R y 0) {D : ℕ}
    (hsmall : SmallClusters O D) : infCluster O = {x | FreeSite O x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, hv, hxv⟩ := hx.2 R
    exact freeSite_of_reflTransGen hd hR hv hxv
  · intro hx
    refine ⟨hx.1, fun R' => ⟨fun _ => max R R' + 1, not_withinInf_const (by omega) (by omega),
      freeToInfinity d hd O D hsmall R hR x _ hx (not_withinInf_const (by omega) (by omega))⟩⟩

/-! #### Infinite = unbounded -/

/-- A set of sites in a box is finite. -/
lemma finite_of_forall_withinInf {K : Set (Zd d)} {R' : ℤ} (h : ∀ x ∈ K, WithinInf R' x 0) :
    K.Finite := by
  refine (boxF 0 R'.toNat).finite_toSet.subset fun x hx => ?_
  rw [Finset.mem_coe, mem_boxF]
  exact (h x hx).mono (Int.self_le_toNat R')

/-- A finite set of sites lies in a box. -/
lemma exists_forall_withinInf_of_finite {K : Set (Zd d)} (hK : K.Finite) :
    ∃ R' : ℤ, ∀ x ∈ K, WithinInf R' x 0 := by
  obtain ⟨B, hB⟩ := (hK.image fun x : Zd d => ∑ i, |x i|).bddAbove
  refine ⟨B, fun x hx i => ?_⟩
  rw [Pi.zero_apply, sub_zero]
  exact (Finset.single_le_sum (f := fun i => |x i|) (fun j _ => abs_nonneg (x j))
    (Finset.mem_univ i)).trans (hB ⟨x, hx, rfl⟩)

/-- **DGZ Lemma 4.1, first claim, literally**: the unbounded open cluster is infinite (`d ≥ 2`,
closed sites in a box). -/
theorem infinite_infCluster (hd : 2 ≤ d) (hR : ∀ y, y ∉ O → WithinInf R y 0) :
    (infCluster O).Infinite := by
  intro hfin
  obtain ⟨R', hR'⟩ := exists_forall_withinInf_of_finite hfin
  have hv := mem_infCluster_of_not_withinInf hd hR (x := fun _ => max R R' + 1)
    (not_withinInf_const (by omega) (by omega))
  exact not_withinInf_const (by omega) (show R' < max R R' + 1 by omega) (hR' _ hv)

/-- **DGZ Lemma 4.1, first claim, literally**: every infinite open cluster is `𝒪` (`d ≥ 2`,
closed sites in a box). -/
theorem eq_infCluster_of_infinite (hd : 2 ≤ d) (hR : ∀ y, y ∉ O → WithinInf R y 0)
    {K : Set (Zd d)} (hK : IsOpenCluster O K) (hinf : K.Infinite) : K = infCluster O := by
  refine eq_infCluster_of_isOpenCluster hd hR hK fun R' => ?_
  by_contra h
  push Not at h
  exact hinf (finite_of_forall_withinInf h)

end Cluster

/-! ### Paths near an open connected set -/

/-- Two lattice points `s u`, `s x` with `|s u - s x|_∞ < s` are equal. -/
lemma eq_of_latPt_mem_obox {s : ℝ} (hs : 0 < s) {u x : Zd d}
    (h : latPt s u ∈ obox (latPt s x) s) : u = x := by
  funext i
  have hi := h i
  rw [HigherDimLFPP.DGZ.latPt_apply, HigherDimLFPP.DGZ.latPt_apply, ← mul_sub, abs_mul,
    abs_of_pos hs] at hi
  have h1 : |((u i : ℤ) : ℝ) - ((x i : ℤ) : ℝ)| < 1 := by
    have := (mul_lt_iff_lt_one_right hs).1 hi
    exact this
  rw [← Int.cast_sub, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h1
  rw [abs_lt] at h1
  omega

/-- A site within lattice distance `D + 1` of a site `x` whose box `obox (s x) s` contains `z`
is within `(D + 2) s` of `z`. -/
lemma latPt_mem_obox_of_withinInf {s : ℝ} (hs : 0 < s) {D : ℕ} {x y : Zd d} {z : Rd d}
    (hxz : z ∈ obox (latPt s x) s) (hyx : WithinInf ((D : ℤ) + 1) y x) :
    latPt s y ∈ obox z (((D : ℝ) + 2) * s) := by
  intro i
  have h1 : |latPt s y i - latPt s x i| ≤ ((D : ℝ) + 1) * s := by
    rw [HigherDimLFPP.DGZ.latPt_apply, HigherDimLFPP.DGZ.latPt_apply, ← mul_sub, abs_mul,
      abs_of_pos hs, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hs.le
    have h := Int.cast_le (R := ℝ) |>.2 (hyx i)
    push_cast at h
    exact h
  have h2 : |z i - latPt s x i| < s := hxz i
  calc |latPt s y i - z i|
      = |(latPt s y i - latPt s x i) - (z i - latPt s x i)| := by ring_nf
    _ ≤ |latPt s y i - latPt s x i| + |z i - latPt s x i| := abs_sub _ _
    _ < ((D : ℝ) + 1) * s + s := by linarith
    _ = ((D : ℝ) + 2) * s := by ring

/-- **DGZ Lemma 4.1, second claim** (MA7 D-4.1 (ii)): under `SmallClusters O D` (closed sites in a
box, `d ≥ 2`), two sites `u, v` of the unbounded open cluster whose real points `s u, s v` lie in
an open connected set `U` are joined by a simple open L-path whose sites `x` satisfy
`s x ∈ B_{(D+2)s}(U)`. -/
theorem exists_path_near_of_mem_infCluster (hd : 2 ≤ d) {O : Set (Zd d)} {R : ℤ}
    (hR : ∀ y, y ∉ O → WithinInf R y 0) {D : ℕ} (hsmall : SmallClusters O D) {s : ℝ}
    (hs : 0 < s) {U : Set (Rd d)} (hUo : IsOpen U) (hUc : IsConnected U) {u v : Zd d}
    (hu : u ∈ infCluster O) (hv : v ∈ infCluster O) (huU : latPt s u ∈ U)
    (hvU : latPt s v ∈ U) :
    ∃ γ : List (Zd d), γ.Nodup ∧ γ.IsChain LAdj ∧ γ.head? = some u ∧ γ.getLast? = some v ∧
      ∀ x ∈ γ, x ∈ O ∧ ∃ z ∈ U, latPt s x ∈ obox z (((D : ℝ) + 2) * s) := by
  -- a continuous path in `U` from `s u` to `s v`
  have hUp : IsPathConnected U := (hUo.isConnected_iff_isPathConnected).1 hUc
  set γ₀ : Path (latPt s u) (latPt s v) := (hUp.joinedIn _ huU _ hvU).somePath with hγ₀
  have hγU : ∀ t, γ₀ t ∈ U := (hUp.joinedIn _ huU _ hvU).somePath_mem
  set P : ℝ → Rd d := fun t => γ₀.extend t with hP
  have hPc : Continuous P := γ₀.continuous_extend
  have hPU : ∀ t, P t ∈ U := by
    intro t
    have : P t ∈ range γ₀.extend := mem_range_self t
    rw [Path.extend_range] at this
    obtain ⟨t', ht'⟩ := this
    rw [← ht']
    exact hγU t'
  -- the path lies in a lattice box
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1
    (isCompact_range γ₀.continuous).isBounded
  set N : ℕ := ⌈M / s⌉₊ + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hMN : M < s * N := by
    have h1 : M / s < N := by
      rw [hN]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil _) (by linarith)
    rwa [div_lt_iff₀ hs, mul_comm] at h1
  have hPbox : MapsTo P (Icc 0 1) (obox (latPt s (0 : Zd d)) (s * N)) := by
    intro t _ i
    rw [HigherDimLFPP.DGZ.latPt_zero, PiLp.zero_apply, sub_zero]
    have hPr : P t ∈ range γ₀ := by rw [← Path.extend_range]; exact mem_range_self t
    obtain ⟨t', ht'⟩ := hPr
    have := hM (γ₀ t') (mem_range_self t')
    rw [ht'] at this
    exact lt_of_le_of_lt ((HigherDimLFPP.DGZ.abs_apply_le_norm _ i).trans this) hMN
  -- the reference L-path (open variant of D-DISC)
  obtain ⟨l, x₀, x₁, -, hlc, hl0, hl1, hP0, hP1, hlP⟩ :=
    exists_discretization hs (0 : Zd d) hN1 zero_le_one hPc.continuousOn hPbox
  have hx₀ : x₀ = u := by
    have : P 0 = latPt s u := γ₀.extend_zero
    rw [this] at hP0
    exact (eq_of_latPt_mem_obox hs hP0).symm
  have hx₁ : x₁ = v := by
    have : P 1 = latPt s v := γ₀.extend_one
    rw [this] at hP1
    exact (eq_of_latPt_mem_obox hs hP1).symm
  subst hx₀ hx₁
  -- free surgery and loop erasure
  have hfree := infCluster_eq_freeSite hd hR hsmall
  have hu' : FreeSite O x₀ := by
    have : x₀ ∈ infCluster O := hu
    rw [hfree] at this; exact this
  have hv' : FreeSite O x₁ := by
    have : x₁ ∈ infCluster O := hv
    rw [hfree] at this; exact this
  have hpath := freeSurgery d O D hsmall l x₀ x₁ hlc hl0 hl1 hu' hv'
  have hx₀S : x₀ ∈ {y | y ∈ O ∧ ∃ x ∈ l, WithinInf ((D : ℤ) + 1) y x} :=
    ⟨hu.1, x₀, List.mem_of_mem_head? hl0, withinInf_refl (by omega) x₀⟩
  obtain ⟨γ, hγn, hγc, hγ0, hγ1, hγS⟩ :=
    HigherDimLFPP.DGZ.exists_nodup_isChain_of_reflTransGen hx₀S hpath
  refine ⟨γ, hγn, hγc, hγ0, hγ1, fun y hy => ⟨(hγS y hy).1, ?_⟩⟩
  obtain ⟨x, hxl, hyx⟩ := (hγS y hy).2
  obtain ⟨-, -, t, -, hPt⟩ := hlP x hxl
  exact ⟨P t, hPU t, latPt_mem_obox_of_withinInf hs hPt hyx⟩

/-! ### Lemma 4.1 for the `m`-open configuration -/

/-- **DGZ Lemma 4.1, corrected** (MA7 D-4.1) for the `m`-open configuration `O_m` of a field `φ`
(DGZ (4.4); `φ = h_n`, `a = a^{(q)}_{n-m}`), mesh `2^{-m}`, `d ≥ 2`:

(i) (DGZ's first claim, which needs no smallness) the unbounded open cluster
`𝒪_m = infCluster O_m` is an infinite open cluster, every infinite open cluster equals it, and it
contains every site outside `𝓛_m`;

on `ℰ_{m,n}`, i.e. `SmallClusters O_m (m² - 101²)`:

(i′) `𝒪_m` is the set of free sites of `O_m` (MA7 D-4.1 (i));

(ii) (DGZ's second claim) for every open connected `U ⊆ ℝ^d` and `u, v ∈ 𝒪_m` with
`2^{-m} u, 2^{-m} v ∈ U`, there is a simple `m`-open L-path from `u` to `v` whose sites `x` satisfy
`2^{-m} x ∈ B_{(D_m + 2) 2^{-m}}(U)`, `D_m = m² - 101²` (`lemma41_dgzRadius`: DGZ's radius
`m² 2^{1-m}`, for `m ≥ 1`). -/
theorem lemma41 (hd : 2 ≤ d) (ξ Q η : ℝ) (φ : Rd d → ℝ) (m : ℕ) (a : ℝ) :
    IsOpenCluster (mOpen ξ Q η φ m a) (infCluster (mOpen ξ Q η φ m a)) ∧
    (infCluster (mOpen ξ Q η φ m a)).Infinite ∧
    (∀ K, IsOpenCluster (mOpen ξ Q η φ m a) K → K.Infinite →
      K = infCluster (mOpen ξ Q η φ m a)) ∧
    (∀ x, x ∉ latRegion m → x ∈ infCluster (mOpen ξ Q η φ m a)) ∧
    (SmallClusters (mOpen ξ Q η φ m a) (m ^ 2 - 101 ^ 2) →
      infCluster (mOpen ξ Q η φ m a) = {x | FreeSite (mOpen ξ Q η φ m a) x} ∧
      ∀ U : Set (Rd d), IsOpen U → IsConnected U → ∀ u v : Zd d,
        u ∈ infCluster (mOpen ξ Q η φ m a) → v ∈ infCluster (mOpen ξ Q η φ m a) →
        latPt ((2 : ℝ)⁻¹ ^ m) u ∈ U → latPt ((2 : ℝ)⁻¹ ^ m) v ∈ U →
        ∃ γ : List (Zd d), γ.Nodup ∧ γ.IsChain LAdj ∧ γ.head? = some u ∧ γ.getLast? = some v ∧
          ∀ x ∈ γ, x ∈ mOpen ξ Q η φ m a ∧ ∃ z ∈ U,
            latPt ((2 : ℝ)⁻¹ ^ m) x ∈
              obox z ((((m ^ 2 - 101 ^ 2 : ℕ) : ℝ) + 2) * (2 : ℝ)⁻¹ ^ m)) := by
  have hR : ∀ y, y ∉ mOpen ξ Q η φ m a → WithinInf (2 ^ (m + 1) - 1) y 0 :=
    fun y hy => withinInf_sub_one_of_mem_latRegion (mem_latRegion_of_not_mem_mOpen hy)
  refine ⟨isOpenCluster_infCluster hd hR, infinite_infCluster hd hR,
    fun K hK hinf => eq_infCluster_of_infinite hd hR hK hinf, fun x hx => ?_, fun hsmall => ⟨
    infCluster_eq_freeSite hd hR hsmall, fun U hUo hUc u v hu hv huU hvU =>
    exists_path_near_of_mem_infCluster hd hR hsmall (by positivity) hUo hUc hu hv huU hvU⟩⟩
  exact mem_infCluster_of_not_withinInf hd hR fun hw =>
    hx fun i => by have := hw i; rw [Pi.zero_apply, sub_zero] at this; omega

/-- `(D_m + 2) 2^{-m} ≤ m² 2^{1-m}` for `m ≥ 1`, `D_m = m² - 101²` (DGZ's radius in Lemma 4.1). -/
lemma radius_le_dgz {m : ℕ} (hm : 1 ≤ m) :
    (((m ^ 2 - 101 ^ 2 : ℕ) : ℝ) + 2) * (2 : ℝ)⁻¹ ^ m ≤ 2 * (m : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ m := by
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h : m ^ 2 - 101 ^ 2 + 2 ≤ 2 * m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · interval_cases m; norm_num
    · have : 4 ≤ m ^ 2 := by nlinarith
      omega
  exact_mod_cast h

/-- **DGZ Lemma 4.1, second claim, with DGZ's radius**: on `ℰ_{m,n}` (`m ≥ 1`), two sites of `𝒪_m`
whose real points lie in an open connected `U` are joined by a simple `m`-open L-path inside
`B_{m²/2^{m-1}}(U)`. -/
theorem lemma41_dgzRadius (hd : 2 ≤ d) (ξ Q η : ℝ) (φ : Rd d → ℝ) {m : ℕ} (hm : 1 ≤ m) (a : ℝ)
    (hE : SmallClusters (mOpen ξ Q η φ m a) (m ^ 2 - 101 ^ 2)) {U : Set (Rd d)} (hUo : IsOpen U)
    (hUc : IsConnected U) {u v : Zd d} (hu : u ∈ infCluster (mOpen ξ Q η φ m a))
    (hv : v ∈ infCluster (mOpen ξ Q η φ m a)) (huU : latPt ((2 : ℝ)⁻¹ ^ m) u ∈ U)
    (hvU : latPt ((2 : ℝ)⁻¹ ^ m) v ∈ U) :
    ∃ γ : List (Zd d), γ.Nodup ∧ γ.IsChain LAdj ∧ γ.head? = some u ∧ γ.getLast? = some v ∧
      ∀ x ∈ γ, x ∈ mOpen ξ Q η φ m a ∧ ∃ z ∈ U,
        latPt ((2 : ℝ)⁻¹ ^ m) x ∈ obox z (2 * (m : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ m) := by
  obtain ⟨γ, h1, h2, h3, h4, h5⟩ :=
    ((lemma41 hd ξ Q η φ m a).2.2.2.2 hE).2 U hUo hUc u v hu hv huU hvU
  refine ⟨γ, h1, h2, h3, h4, fun x hx => ?_⟩
  obtain ⟨hxO, z, hzU, hxz⟩ := h5 x hx
  exact ⟨hxO, z, hzU, fun i => (hxz i).trans_le (radius_le_dgz hm)⟩

/-! ### `ℱ_{m,n}` in DGZ's form -/

/-- **DGZ (4.7), literally** (`d ≥ 2`): on `ℰ_{m,n} ∩ ℰ_{m-1,n}` the free sites are the unbounded
open clusters (`lemma41` (i′)), so `ω ∈ ℱ_{m,n}` (free-site form, `eventF`) iff
`ω ∈ ℰ_{m,n} ∩ ℰ_{m-1,n}` and every `x ∈ 𝓛_m` is within `m² 2^{-m}` of a point
`y ∈ 𝒪_m ∩ 𝒪_{m-1}`, i.e. a coarse site `y` with `2y ∈ 𝒪_m` and `y ∈ 𝒪_{m-1}`. -/
theorem mem_eventF_iff (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (H : ℕ → Rd d → Ω → ℝ) (ξ Q η : ℝ) (q : ENNReal) (m n : ℕ) (ω : Ω) :
    ω ∈ eventF P H ξ Q η q m n ↔ ω ∈ eventE P H ξ Q η q m n ∧ ω ∈ eventE P H ξ Q η q (m - 1) n ∧
      ∀ x ∈ latRegion m, ∃ y : Zd d, WithinInf ((m : ℤ) ^ 2) x (2 • y) ∧
        2 • y ∈ infCluster (mOpen ξ Q η (fun z => H n z ω) m (aQ P H ξ (n - m) q)) ∧
        y ∈ infCluster
          (mOpen ξ Q η (fun z => H n z ω) (m - 1) (aQ P H ξ (n - (m - 1)) q)) := by
  have hR : ∀ (k : ℕ) (b : ℝ), ∀ y, y ∉ mOpen ξ Q η (fun z => H n z ω) k b →
      WithinInf (2 ^ (k + 1) - 1) y 0 :=
    fun k b y hy => withinInf_sub_one_of_mem_latRegion (mem_latRegion_of_not_mem_mOpen hy)
  constructor
  · rintro ⟨⟨hE₁, hE₂⟩, h3⟩
    refine ⟨hE₁, hE₂, ?_⟩
    rw [infCluster_eq_freeSite hd (hR _ _) hE₁, infCluster_eq_freeSite hd (hR _ _) hE₂]
    exact h3
  · rintro ⟨hE₁, hE₂, h3⟩
    rw [infCluster_eq_freeSite hd (hR _ _) hE₁, infCluster_eq_freeSite hd (hR _ _) hE₂] at h3
    exact ⟨⟨hE₁, hE₂⟩, h3⟩

end DGZ

end HigherDimLQGMetric
