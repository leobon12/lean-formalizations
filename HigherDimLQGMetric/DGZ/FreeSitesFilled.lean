import HigherDimLQGMetric.DGZ.FreeSitesDefs
import HigherDimLFPP.Perc.Clusters

/-!
# Filled clusters (packet L3a1, MA7 D-F0)

Source: planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-F0 (filled
clusters), repairing the "duality" steps of Ding–Gwynne–Zhuang (arXiv:2310.03996v5, §4; gaps
G1–G3).

For a set `C ⊆ ℤ^d` contained in some box `[-R, R]^d`, HigherDimLFPP's exterior `Ext R C` (the sites
joined to `(R + 1, …, R + 1)` by an L-path avoiding `C`) does not depend on `R` when `d ≥ 2`
(`ext_eq_ext`). We work with the box-free form

* `extAll C` — the sites in `Ext R C` for **every** `R` with `C ⊆ [-R, R]^d` (the form used by
  `FreeSite`; for bounded `C` and `d ≥ 2` it equals `Ext R C`, `mem_extAll_iff`);
* `filled C := (extAll C)ᶜ` — the filled cluster `F(C) = C ∪ Encl(C) = ℤ^d \ Ext(C)`;
* `encl C := filled C \ C` — the enclosed sites `Encl(C)`; `x ∈ encl C ↔ Encloses C x`
  (HigherDimLFPP's `Encloses`, `mem_encl_iff_encloses`);
* `bbox C` — the bounding box `∏ᵢ [min_C xᵢ, max_C xᵢ]`.

Main results (D-F0 (a)–(d)):

* `filled_subset_bbox` (a): `filled C ⊆ bbox C` (`d ≥ 2`); hence a filled cluster has the
  `ℓ^∞`-diameter of `C` (`withinInf_of_mem_filled`) and is finite (`finite_filled`);
* `closedCluster_subset_ext_or_encl` (b): for distinct closed clusters `C ≠ C'`, no site of `C'` is
  `*`-adjacent to a site of `C`, and `C' ⊆ extAll C` or `C' ⊆ encl C` (any `d`);
* `filled_subset_of_subset_encl` (c): `C' ⊆ encl C → filled C' ⊆ filled C` (`d ≥ 2`, `C` bounded);
* `filled_disjoint_nonadj` (d): if `C' ⊆ extAll C` and `C ⊆ extAll C'` (closed clusters, bounded,
  `d ≥ 2`), the filled clusters are disjoint and no site of one is `*`-adjacent to a site of the
  other.

Auxiliary facts: closed clusters sharing a site are equal (`isClosedCluster_eq_of_mem`), distinct
ones are not `*`-adjacent (`not_sAdj_of_isClosedCluster_ne`), a `*`-connected set of closed sites
lies in one closed cluster (`exists_isClosedCluster_superset`);
`FreeSite O x ↔ x ∈ O ∧ ∀ C, ¬ Encloses C x` (`freeSite_iff_not_encloses`).

Proofs follow D-F0 with two simplifications (written out in the handoff
`planning/handoffs/L3a1.md`): in (c) the "last site of the path in `C'`" is replaced by an
induction along the path (every site of an L-path from `y` to the base point avoiding `C` lies in
`Ext R C`, hence outside `C'`); in (d) the L-component `A` of `y` is replaced by the first hitting
time of `C` along the ray `y + j e₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open Relation

variable {d : ℕ}

/-! ### Closed clusters -/

/-- If two closed clusters share a site, the second is contained in the first (maximality). -/
lemma isClosedCluster_subset_of_mem {O C C' : Set (Zd d)} (hC : IsClosedCluster O C)
    (hC' : IsClosedCluster O C') {z : Zd d} (hzC : z ∈ C) (hzC' : z ∈ C') : C' ⊆ C := by
  intro y hy
  have hpath : ReflTransGen (StepIn C' SAdj) z y := hC'.2.2.1 z hzC' y hy
  clear hy
  induction hpath with
  | refl => exact hzC
  | tail _ hbc ih => exact hC.2.2.2 _ ih _ (hC'.2.1 hbc.2.1) hbc.2.2

/-- Two closed clusters sharing a site are equal. -/
lemma isClosedCluster_eq_of_mem {O C C' : Set (Zd d)} (hC : IsClosedCluster O C)
    (hC' : IsClosedCluster O C') {z : Zd d} (hzC : z ∈ C) (hzC' : z ∈ C') : C = C' :=
  Set.Subset.antisymm (isClosedCluster_subset_of_mem hC' hC hzC' hzC)
    (isClosedCluster_subset_of_mem hC hC' hzC hzC')

/-- Distinct closed clusters are disjoint. -/
lemma notMem_of_isClosedCluster_ne {O C C' : Set (Zd d)} (hC : IsClosedCluster O C)
    (hC' : IsClosedCluster O C') (hne : C ≠ C') {p : Zd d} (hp' : p ∈ C') : p ∉ C :=
  fun hp => hne (isClosedCluster_eq_of_mem hC hC' hp hp')

/-- No site of a closed cluster is `*`-adjacent to a site of a different closed cluster. -/
lemma not_sAdj_of_isClosedCluster_ne {O C C' : Set (Zd d)} (hC : IsClosedCluster O C)
    (hC' : IsClosedCluster O C') (hne : C ≠ C') {p p' : Zd d} (hp : p ∈ C) (hp' : p' ∈ C') :
    ¬ SAdj p p' :=
  fun h => hne (isClosedCluster_eq_of_mem hC hC' (hC.2.2.2 p hp p' (hC'.2.1 hp') h) hp')

/-- A closed cluster is the `*`-component `closedComp O c` of any of its sites. -/
lemma isClosedCluster_eq_closedComp {O C : Set (Zd d)} (hC : IsClosedCluster O C) {c : Zd d}
    (hc : c ∈ C) : C = closedComp O c :=
  isClosedCluster_eq_of_mem hC (isClosedCluster_closedComp (hC.2.1 hc)) hc (mem_closedComp_self O c)

/-- A `*`-connected set of closed sites meeting a closed cluster lies in it. -/
lemma subset_of_connIn_of_mem {O C S : Set (Zd d)} (hC : IsClosedCluster O C)
    (hS : ConnIn S SAdj) (hSO : S ⊆ Oᶜ) {c : Zd d} (hcS : c ∈ S) (hcC : c ∈ C) : S ⊆ C := by
  intro y hy
  have hpath : ReflTransGen (StepIn S SAdj) c y := hS c hcS y hy
  clear hy
  induction hpath with
  | refl => exact hcC
  | tail _ hbc ih => exact hC.2.2.2 _ ih _ (hSO hbc.2.1) hbc.2.2

/-- A nonempty `*`-connected set of closed sites lies in a closed cluster (the `*`-component of
any of its sites). -/
lemma exists_isClosedCluster_superset {O S : Set (Zd d)} (hS : ConnIn S SAdj) (hSO : S ⊆ Oᶜ)
    {c : Zd d} (hcS : c ∈ S) : ∃ C, IsClosedCluster O C ∧ S ⊆ C :=
  ⟨closedComp O c, isClosedCluster_closedComp (hSO hcS),
    subset_of_connIn_of_mem (isClosedCluster_closedComp (hSO hcS)) hS hSO hcS
      (mem_closedComp_self O c)⟩

/-! ### Unit cubes -/

/-- Two sites of the unit cube spanned by sites at `ℓ^∞`-distance `≤ 1` are at `ℓ^∞`-distance
`≤ 1`. -/
lemma withinInf_one_of_mem_cube {x y z z' : Zd d} (hxy : WithinInf 1 x y) (hz : z ∈ cube x y)
    (hz' : z' ∈ cube x y) : WithinInf 1 z z' := by
  intro k
  have hk := hxy k
  rcases hz k with h | h <;> rcases hz' k with h' | h' <;> rw [h, h']
  · simp
  · exact hk
  · rw [abs_sub_comm]; exact hk
  · simp

/-! ### The exterior does not depend on the box (`d ≥ 2`) -/

/-- The base point `(R + 1, …, R + 1)` of `Ext R F` lies in `Ext R' F` whenever `F` lies in both
boxes `[-R, R]^d` and `[-R', R']^d` (`d ≥ 2`): the ray from it in direction `e₀` keeps the
coordinate `R + 1` in direction `e₁`, so it avoids `F`. -/
lemma base_mem_ext (hd : 2 ≤ d) {R R' : ℤ} {F : Set (Zd d)} (hF : ∀ c ∈ F, WithinInf R c 0)
    (hF' : ∀ c ∈ F, WithinInf R' c 0) : (fun _ => R + 1 : Zd d) ∈ Ext R' F := by
  have h10 : (⟨1, by omega⟩ : Fin d) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  refine mem_ext_of_ray_add hd hF' _ ⟨0, by omega⟩ fun j hj => ?_
  have h := hF _ hj ⟨1, by omega⟩
  rw [add_single_apply_of_ne _ h10] at h
  simp only [Pi.zero_apply, sub_zero, abs_le] at h
  omega

/-- `Ext R F ⊆ Ext R' F` for two boxes containing `F` (`d ≥ 2`). -/
lemma ext_subset_ext (hd : 2 ≤ d) {R R' : ℤ} {F : Set (Zd d)} (hF : ∀ c ∈ F, WithinInf R c 0)
    (hF' : ∀ c ∈ F, WithinInf R' c 0) : Ext R F ⊆ Ext R' F := fun _ hy =>
  mem_ext_of_reflTransGen hy (base_mem_ext hd hF hF')

/-- **The exterior does not depend on the box** (`d ≥ 2`; MA7 D-F0): `Ext R F = Ext R' F` whenever
`F` lies in both boxes `[-R, R]^d` and `[-R', R']^d`. -/
lemma ext_eq_ext (hd : 2 ≤ d) {R R' : ℤ} {F : Set (Zd d)} (hF : ∀ c ∈ F, WithinInf R c 0)
    (hF' : ∀ c ∈ F, WithinInf R' c 0) : Ext R F = Ext R' F :=
  Set.Subset.antisymm (ext_subset_ext hd hF hF') (ext_subset_ext hd hF' hF)

/-- If no site of `C'` lies in `Ext R C`, then `Ext R C ⊆ Ext R C'` (the same box `R`): every site
of an L-path from `y` to the base point avoiding `C` lies in `Ext R C`, hence outside `C'`. -/
lemma ext_subset_ext_of_forall_notMem {R : ℤ} {C C' : Set (Zd d)}
    (h : ∀ p ∈ C', p ∉ Ext R C) : Ext R C ⊆ Ext R C' := by
  intro y hy
  change ReflTransGen (StepIn Cᶜ LAdj) y (fun _ => R + 1) at hy
  induction hy using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | head hyz hz ih =>
    exact mem_ext_of_lAdj (fun hy' => h _ hy' (ReflTransGen.head hyz hz)) (fun hz' => h _ hz' hz)
      hyz.2.2 ih

/-! ### Exterior, filled cluster, enclosed sites, bounding box -/

/-- The exterior of `F` with respect to **every** box containing it: the sites of `Ext R F` for
every `R` with `F ⊆ [-R, R]^d`. For bounded `F` and `d ≥ 2` this is `Ext R F` for any such `R`
(`mem_extAll_iff`); `FreeSite O x` is `x ∈ O ∧ ∀ C, IsClosedCluster O C → x ∈ extAll C`. -/
def extAll (F : Set (Zd d)) : Set (Zd d) :=
  {y | ∀ R : ℤ, (∀ c ∈ F, WithinInf R c 0) → y ∈ Ext R F}

/-- The **filled cluster** `F(C) = ℤ^d \ Ext(C)` (MA7 D-F0). -/
def filled (C : Set (Zd d)) : Set (Zd d) := (extAll C)ᶜ

/-- The **enclosed sites** `Encl(C) = ℤ^d \ (C ∪ Ext(C))` (MA7 D-F0). -/
def encl (C : Set (Zd d)) : Set (Zd d) := filled C \ C

/-- The **bounding box** `bbox(C) = ∏ᵢ [min_C xᵢ, max_C xᵢ]` (MA7 D-F0). -/
def bbox (C : Set (Zd d)) : Set (Zd d) :=
  {y | ∀ i, (∃ c ∈ C, c i ≤ y i) ∧ ∃ c ∈ C, y i ≤ c i}

/-- `FreeSite` in terms of `extAll` (definitional). -/
lemma freeSite_iff_extAll {O : Set (Zd d)} {x : Zd d} :
    FreeSite O x ↔ x ∈ O ∧ ∀ C, IsClosedCluster O C → x ∈ extAll C :=
  Iff.rfl

/-- `FreeSite` in terms of filled clusters. -/
lemma freeSite_iff_filled {O : Set (Zd d)} {x : Zd d} :
    FreeSite O x ↔ x ∈ O ∧ ∀ C, IsClosedCluster O C → x ∉ filled C := by
  simp only [freeSite_iff_extAll, filled, Set.mem_compl_iff, not_not]

lemma mem_filled_iff_exists {C : Set (Zd d)} {y : Zd d} :
    y ∈ filled C ↔ ∃ R : ℤ, (∀ c ∈ C, WithinInf R c 0) ∧ y ∉ Ext R C := by
  simp only [filled, extAll, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, exists_prop]

/-- For `C ⊆ [-R, R]^d` and `d ≥ 2`, `extAll C = Ext R C`. -/
lemma mem_extAll_iff (hd : 2 ≤ d) {R : ℤ} {C : Set (Zd d)} (hC : ∀ c ∈ C, WithinInf R c 0)
    {y : Zd d} : y ∈ extAll C ↔ y ∈ Ext R C :=
  ⟨fun h => h R hC, fun h _ hR' => ext_subset_ext hd hC hR' h⟩

/-- For `C ⊆ [-R, R]^d` and `d ≥ 2`, `filled C = ℤ^d \ Ext R C`. -/
lemma mem_filled_iff (hd : 2 ≤ d) {R : ℤ} {C : Set (Zd d)} (hC : ∀ c ∈ C, WithinInf R c 0)
    {y : Zd d} : y ∈ filled C ↔ y ∉ Ext R C := by
  rw [filled, Set.mem_compl_iff, mem_extAll_iff hd hC]

/-- `encl C` is the set of sites enclosed by `C` in the sense of HigherDimLFPP's `Encloses`. -/
lemma mem_encl_iff_encloses {C : Set (Zd d)} {x : Zd d} : x ∈ encl C ↔ Encloses C x := by
  simp only [encl, Set.mem_sdiff, mem_filled_iff_exists, Encloses]
  constructor
  · rintro ⟨⟨R, hR, hx⟩, hxC⟩
    exact ⟨R, hR, hxC, hx⟩
  · rintro ⟨R, hR, hxC, hx⟩
    exact ⟨⟨R, hR, hx⟩, hxC⟩

/-- **Free sites are the open sites enclosed by no closed cluster**: `FreeSite O x` iff `x` is open
and no closed cluster `Encloses` it (HigherDimLFPP's `Encloses`, whose probability is bounded by
`Perc.enclosureBound`). -/
lemma freeSite_iff_not_encloses {O : Set (Zd d)} {x : Zd d} :
    FreeSite O x ↔ x ∈ O ∧ ∀ C, IsClosedCluster O C → ¬ Encloses C x := by
  constructor
  · rintro ⟨hxO, hx⟩
    exact ⟨hxO, fun C hC ⟨R, hR, _, hxE⟩ => hxE (hx C hC R hR)⟩
  · rintro ⟨hxO, hx⟩
    refine ⟨hxO, fun C hC R hR => ?_⟩
    by_contra hxE
    exact hx C hC ⟨R, hR, fun hxC => hC.2.1 hxC hxO, hxE⟩

/-- A bounded set lies in its filled cluster (`d ≥ 1`). -/
lemma mem_filled_of_mem (hd : 1 ≤ d) {C : Set (Zd d)} (hCb : ∃ R : ℤ, ∀ c ∈ C, WithinInf R c 0)
    {y : Zd d} (hy : y ∈ C) : y ∈ filled C := by
  obtain ⟨R, hR⟩ := hCb
  exact fun h => notMem_of_mem_ext hR ⟨0, by omega⟩ (h R hR) hy

/-- A bounded set lies in its filled cluster (`d ≥ 1`). -/
lemma subset_filled (hd : 1 ≤ d) {C : Set (Zd d)} (hCb : ∃ R : ℤ, ∀ c ∈ C, WithinInf R c 0) :
    C ⊆ filled C :=
  fun _ hy => mem_filled_of_mem hd hCb hy

/-- A free site lies in no closed cluster. -/
lemma FreeSite.notMem_of_isClosedCluster {O C : Set (Zd d)} {x : Zd d} (hx : FreeSite O x)
    (hC : IsClosedCluster O C) : x ∉ C :=
  fun hxC => hC.2.1 hxC hx.1

/-! ### D-F0 (a): filled clusters lie in the bounding box -/

/-- **MA7 D-F0 (a)**: `F(C) ⊆ bbox(C)` (`d ≥ 2`). If `yᵢ > max_C xᵢ` the ray `y + t eᵢ` avoids `C`
and leaves the box, so `y ∈ Ext(C)` (`mem_ext_of_ray_add`); symmetrically if `yᵢ < min_C xᵢ`
(`mem_ext_of_ray_sub`). (For unbounded `C`, `filled C = ∅`.) -/
theorem filled_subset_bbox (hd : 2 ≤ d) (C : Set (Zd d)) : filled C ⊆ bbox C := by
  intro y hy i
  obtain ⟨R, hR, hyE⟩ := mem_filled_iff_exists.1 hy
  constructor
  · by_contra h
    push Not at h
    refine hyE (mem_ext_of_ray_sub hd hR y i fun j hj => ?_)
    have := h _ hj
    rw [add_single_apply_self] at this
    omega
  · by_contra h
    push Not at h
    refine hyE (mem_ext_of_ray_add hd hR y i fun j hj => ?_)
    have := h _ hj
    rw [add_single_apply_self] at this
    omega

/-- (a), distance form: if `C` has `ℓ^∞`-diameter `≤ D`, every site of `F(C)` is within `D` of
every site of `C`. -/
lemma withinInf_of_mem_filled_of_mem (hd : 2 ≤ d) {D : ℤ} {C : Set (Zd d)}
    (hD : ∀ c ∈ C, ∀ c' ∈ C, WithinInf D c c') {y c : Zd d} (hy : y ∈ filled C) (hc : c ∈ C) :
    WithinInf D y c := by
  intro i
  obtain ⟨⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩⟩ := filled_subset_bbox hd C hy i
  have e1 := hD c hc c₁ hc₁ i
  have e2 := hD c hc c₂ hc₂ i
  rw [abs_le] at e1 e2 ⊢
  constructor <;> omega

/-- (a), diameter form: `diam_∞ F(C) ≤ D` when `diam_∞ C ≤ D`. -/
lemma withinInf_of_mem_filled (hd : 2 ≤ d) {D : ℤ} {C : Set (Zd d)}
    (hD : ∀ c ∈ C, ∀ c' ∈ C, WithinInf D c c') {y y' : Zd d} (hy : y ∈ filled C)
    (hy' : y' ∈ filled C) : WithinInf D y y' := by
  intro i
  obtain ⟨⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩⟩ := filled_subset_bbox hd C hy i
  obtain ⟨⟨c₃, hc₃, h₃⟩, ⟨c₄, hc₄, h₄⟩⟩ := filled_subset_bbox hd C hy' i
  have e1 := hD c₂ hc₂ c₃ hc₃ i
  have e2 := hD c₄ hc₄ c₁ hc₁ i
  rw [abs_le] at e1 e2 ⊢
  constructor <;> omega

/-- A filled cluster of a set of finite diameter is finite (`d ≥ 2`). -/
lemma finite_filled (hd : 2 ≤ d) {D : ℕ} {C : Set (Zd d)}
    (hD : ∀ c ∈ C, ∀ c' ∈ C, WithinInf (D : ℤ) c c') : (filled C).Finite := by
  rcases C.eq_empty_or_nonempty with hC | ⟨c, hc⟩
  · refine Set.finite_empty.subset fun y hy => ?_
    obtain ⟨⟨c, hc, -⟩, -⟩ := filled_subset_bbox hd C hy ⟨0, by omega⟩
    rw [hC] at hc
    exact hc
  · exact (boxF c D).finite_toSet.subset fun y hy =>
      mem_boxF.2 (withinInf_of_mem_filled_of_mem hd hD hy hc)

/-! ### D-F0 (b): two closed clusters -/

/-- **MA7 D-F0 (b)**: for distinct closed clusters `C ≠ C'`, no site of `C'` is `*`-adjacent to a
site of `C`, and `C' ⊆ Ext(C)` or `C' ⊆ Encl(C)`. Two `*`-adjacent sites of `C'` are joined by the
coordinate path in their unit cube, which avoids `C` (a site of `C` in the cube would be
`*`-adjacent to a site of `C'`); so membership in the exterior of `C` is constant on the
`*`-connected set `C'`. No hypothesis on `d` is needed. -/
theorem closedCluster_subset_ext_or_encl {O C C' : Set (Zd d)} (hC : IsClosedCluster O C)
    (hC' : IsClosedCluster O C') (hne : C ≠ C') :
    (∀ p ∈ C, ∀ p' ∈ C', ¬ SAdj p p') ∧ (C' ⊆ extAll C ∨ C' ⊆ encl C) := by
  have hnadj : ∀ p ∈ C, ∀ p' ∈ C', ¬ SAdj p p' := fun p hp p' hp' =>
    not_sAdj_of_isClosedCluster_ne hC hC' hne hp hp'
  have hdisj : ∀ p ∈ C', p ∉ C := fun p hp' => notMem_of_isClosedCluster_ne hC hC' hne hp'
  refine ⟨hnadj, ?_⟩
  -- `*`-adjacent sites of `C'` are joined by an L-path avoiding `C`
  have hstep : ∀ p ∈ C', ∀ p' ∈ C', SAdj p p' → ReflTransGen (StepIn Cᶜ LAdj) p p' := by
    intro p hp p' _ hpp'
    have hsub : cube p p' ⊆ Cᶜ := by
      intro w hw hwC
      have hw1 : WithinInf 1 w p := (withinInf_of_mem_cube hpp'.withinInf hw).1
      have hwp : w ≠ p := fun h => hdisj p hp (h ▸ hwC)
      exact hnadj w hwC p hp (sAdj_of_withinInf hwp hw1)
    exact reflTransGen_stepIn_mono hsub (reflTransGen_cube hpp'.withinInf)
  -- membership in `extAll C` is constant along `C'`
  have hconst : ∀ p ∈ C', ∀ p' ∈ C', p ∈ extAll C → p' ∈ extAll C := by
    intro p hp p' hp' hpE
    have hpath : ReflTransGen (StepIn C' SAdj) p p' := hC'.2.2.1 p hp p' hp'
    clear hp'
    induction hpath with
    | refl => exact hpE
    | tail _ hbc ih =>
      exact fun R hR => mem_ext_of_reflTransGen
        (reflTransGen_lAdj_symm (hstep _ hbc.1 _ hbc.2.1 hbc.2.2)) (ih R hR)
  by_cases h : ∃ p ∈ C', p ∈ extAll C
  · obtain ⟨p, hp, hpE⟩ := h
    exact Or.inl fun p' hp' => hconst p hp p' hp' hpE
  · push Not at h
    exact Or.inr fun p hp => ⟨h p hp, hdisj p hp⟩

/-! ### D-F0 (c): nesting -/

/-- **MA7 D-F0 (c)**: if `C' ⊆ Encl(C)` then `F(C') ⊆ F(C)` (`d ≥ 2`, `C` bounded). In a common
box `R`, no site of `C'` is in `Ext R C`, so `Ext R C ⊆ Ext R C'`
(`ext_subset_ext_of_forall_notMem`). -/
theorem filled_subset_of_subset_encl (hd : 2 ≤ d) {C C' : Set (Zd d)}
    (hCb : ∃ R : ℤ, ∀ c ∈ C, WithinInf R c 0) (h : C' ⊆ encl C) : filled C' ⊆ filled C := by
  intro y hy
  rw [filled, Set.mem_compl_iff] at hy ⊢
  intro hyE
  apply hy
  intro R' hR'
  obtain ⟨R₀, hR₀⟩ := hCb
  have hCR : ∀ c ∈ C, WithinInf (max R₀ R') c 0 := fun c hc =>
    (hR₀ c hc).mono (le_max_left _ _)
  have hC'R : ∀ c ∈ C', WithinInf (max R₀ R') c 0 := fun c hc =>
    (hR' c hc).mono (le_max_right _ _)
  have hC'E : ∀ p ∈ C', p ∉ Ext (max R₀ R') C := fun p hp hpE =>
    (h hp).1 ((mem_extAll_iff hd hCR).2 hpE)
  exact ext_subset_ext hd hC'R hR' (ext_subset_ext_of_forall_notMem hC'E (hyE _ hCR))

/-! ### D-F0 (d): mutually exterior clusters -/

/-- **MA7 D-F0 (d)**: if `C' ⊆ Ext(C)` and `C ⊆ Ext(C')` (closed clusters, bounded, `d ≥ 2`), then
`F(C) ∩ F(C') = ∅` and no site of `F(C)` is `*`-adjacent to a site of `F(C')`.

*Disjointness.* For `y ∈ F(C)` the ray `y + j e₀` meets `C` (otherwise `y ∈ Ext(C)`); before its
first hit it stays in `F(C)`, hence avoids `C' ⊆ Ext(C)`, and the hit lies in `C ⊆ Ext(C')`; so
`y ∈ Ext(C')`. *Non-adjacency.* For `*`-adjacent `a ∈ F(C)`, `b ∈ F(C')`, the unit cube of `a, b`
meets `C` (otherwise `b ∈ F(C)` by the coordinate path) and `C'` (likewise); the two hits are
distinct and at `ℓ^∞`-distance `≤ 1`, contradicting (b). -/
theorem filled_disjoint_nonadj (hd : 2 ≤ d) {O C C' : Set (Zd d)} (hC : IsClosedCluster O C)
    (hC' : IsClosedCluster O C') (hCb : ∃ R : ℤ, ∀ c ∈ C, WithinInf R c 0)
    (hC'b : ∃ R : ℤ, ∀ c ∈ C', WithinInf R c 0) (h₁ : C' ⊆ extAll C) (h₂ : C ⊆ extAll C') :
    Disjoint (filled C) (filled C') ∧ ∀ a ∈ filled C, ∀ b ∈ filled C', ¬ SAdj a b := by
  obtain ⟨R₁, hR₁⟩ := hCb
  obtain ⟨R₂, hR₂⟩ := hC'b
  set R : ℤ := max R₁ R₂ with hRdef
  have hCR : ∀ c ∈ C, WithinInf R c 0 := fun c hc => (hR₁ c hc).mono (le_max_left _ _)
  have hC'R : ∀ c ∈ C', WithinInf R c 0 := fun c hc => (hR₂ c hc).mono (le_max_right _ _)
  have h₁' : ∀ p ∈ C', p ∈ Ext R C := fun p hp => h₁ hp R hCR
  have h₂' : ∀ p ∈ C, p ∈ Ext R C' := fun p hp => h₂ hp R hC'R
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  -- disjointness, in the form `y ∉ Ext R C → y ∈ Ext R C'`
  have hdisj : ∀ y, y ∉ Ext R C → y ∈ Ext R C' := by
    intro y hy
    classical
    have hhit : ∃ j : ℕ, y + Pi.single i₀ (j : ℤ) ∈ C := by
      by_contra hno
      push Not at hno
      exact hy (mem_ext_of_ray_add hd hCR y i₀ hno)
    have hj₀ : y + Pi.single i₀ ((Nat.find hhit : ℕ) : ℤ) ∈ C := Nat.find_spec hhit
    have hseg : ∀ s : ℕ, s ≤ Nat.find hhit → y + Pi.single i₀ (s : ℤ) ∈ C'ᶜ := by
      intro s hs
      rcases lt_or_eq_of_le hs with hs | hs
      · intro hsC'
        apply hy
        have hpath : ReflTransGen (StepIn Cᶜ LAdj) y (y + Pi.single i₀ (s : ℤ)) :=
          reflTransGen_add_single_nat y i₀ s fun t ht => Nat.find_min hhit (by omega)
        exact mem_ext_of_reflTransGen hpath (h₁' _ hsC')
      · rw [hs]
        exact notMem_of_mem_ext hC'R i₀ (h₂' _ hj₀)
    exact mem_ext_of_reflTransGen (reflTransGen_add_single_nat y i₀ _ hseg) (h₂' _ hj₀)
  have hF : ∀ y, y ∈ filled C ↔ y ∉ Ext R C := fun y => mem_filled_iff hd hCR
  have hF' : ∀ y, y ∈ filled C' ↔ y ∉ Ext R C' := fun y => mem_filled_iff hd hC'R
  refine ⟨Set.disjoint_left.2 fun y hyC hyC' => (hF' y).1 hyC' (hdisj y ((hF y).1 hyC)), ?_⟩
  intro a ha b hb hab
  -- the unit cube of `a, b` meets `C`
  have hw : ∃ w ∈ cube a b, w ∈ C := by
    by_contra hno
    push Not at hno
    have hsub : cube a b ⊆ Cᶜ := fun w hw => hno w hw
    have hpath : ReflTransGen (StepIn Cᶜ LAdj) a b :=
      reflTransGen_stepIn_mono hsub (reflTransGen_cube hab.withinInf)
    have hbE : b ∉ Ext R C := fun hbE => (hF a).1 ha (mem_ext_of_reflTransGen hpath hbE)
    exact (hF' b).1 hb (hdisj b hbE)
  -- and `C'`
  have hw' : ∃ w ∈ cube a b, w ∈ C' := by
    by_contra hno
    push Not at hno
    have hsub : cube a b ⊆ C'ᶜ := fun w hw => hno w hw
    have hpath : ReflTransGen (StepIn C'ᶜ LAdj) b a :=
      reflTransGen_lAdj_symm (reflTransGen_stepIn_mono hsub (reflTransGen_cube hab.withinInf))
    have haE : a ∉ Ext R C' := fun haE => (hF' b).1 hb (mem_ext_of_reflTransGen hpath haE)
    exact haE (hdisj a ((hF a).1 ha))
  obtain ⟨w, hwcube, hwC⟩ := hw
  obtain ⟨w', hw'cube, hw'C'⟩ := hw'
  have hne : C ≠ C' := by
    rintro rfl
    exact notMem_of_mem_ext hCR i₀ (h₁' w hwC) hwC
  have hww' : w ≠ w' := by
    rintro rfl
    exact notMem_of_mem_ext hCR i₀ (h₁' w hw'C') hwC
  exact (closedCluster_subset_ext_or_encl hC hC' hne).1 w hwC w' hw'C'
    (sAdj_of_withinInf hww' (withinInf_one_of_mem_cube hab.withinInf hwcube hw'cube))

end DGZ

end HigherDimLQGMetric
