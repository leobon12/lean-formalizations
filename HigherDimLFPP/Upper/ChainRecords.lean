import HigherDimLFPP.Upper.RecordCount
import HigherDimLFPP.Upper.PathTree

/-!
# The record assignment: a chain record for every leaf of every partition tree

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.3 (the paragraphs before (4.15) and the
last paragraph of the proof of Lemma 4.4: "the resulting family includes every field-dependent
path and every one of its chains"), as corrected by the planning audit HA3
(`planning/audits/HA3-section-4.md`), Details D6 ("Assignment"), with the fix F1; the
simultaneity paragraph of D7 uses exactly the conclusions proved here.

2D source: `LQGDimension/LFPP/Records.lean` (`nodeLoc`, `recOf`, `rec_mem`, `node_config`,
`recordAssignment`): the records along the ancestry of a leaf form a chain record whose families
contain the actual configurations.

Fix an admissible path `γ`, a well-formed partition tree `T` of `γ` at ratio `K = 2ⁿ` (`n ≥ 1`),
cutoff `ε > 0` and root radius `2√d`, a continuous field `φ`, and a leaf `v` with internal
ancestors `u_i = v.take i` (`i < |v|`).  The record of `u_i` is

* `(good, ⌊a_{u_i}/δ²⌋, ι, loc(u_i), loc(u_{i+1}))` if `a_{u_i} ≤ a₀` (`ι = v[i]` the followed
  child), with configuration `([x_{u_i}, y_{u_i}], Q_{u_i})`;
* `(bad, loc(u_i), p_j(x_w), p_j(y_w), loc(u_{i+1}))` otherwise, with `w` an adverse child
  (attaining `G_{u_i} = max_v (H_{u_i} - H_v)`; it depends on `φ`) and configuration
  `([x_{u_i}, y_{u_i}], [x_w, y_w])`.

`chainRecord_assignment` proves: these records lie in the finite record set `recSet d n δ ε`
and form a chain record (`IsChainRec`); the configuration of `u_i` lies in `Φ(ρ_i)` and its
variable is `δ^{-1/2} G_{u_i}`; good nodes have bin `k_i = ⌊a_{u_i}/δ²⌋ ≤ b_{u_i}`, bad nodes have
`b_{u_i} = a₀/δ²`; hence `cost(ρ_i) ≤ b_{u_i}` and
`Σ_{u ≺ v} (δ^{-1/2} G_u - b_u) ≤ Σ_i (Y_i(c_i) - cost(ρ_i))`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

open TreeJensen

/-! ## Facts about the partition tree of an admissible path -/

section TreeFacts

variable {d : ℕ} {n : ℕ} {ε : ℝ} {T : CutTree} {γ : ℝ → Rd d}

/-- The location `loc(u)` of the chord of node `u`. -/
def nodeLoc (δ : ℝ) (T : CutTree) (γ : ℝ → Rd d) (u : List ℕ) : Loc d :=
  locOf δ (T.x γ u) (T.y γ u)

theorem root_R_eq_one [NeZero d] (hγ : IsAdmissiblePath d γ) {K : ℕ} {ρ' : ℝ}
    (hT : T.WF γ K ε ρ') : T.R γ [] = 1 := by
  simp only [CutTree.R, CutTree.x, CutTree.y, hT.root_time.1, hT.root_time.2]
  exact norm_target_sub_source hγ

/-- The root location is `(0, p₀(0), p₀(e₁))`, with `p₀` the cube index at side `δ` (HA3 D6). -/
theorem rootLoc_eq [NeZero d] (δ : ℝ) :
    rootLoc d δ = (0, cubeIdx δ (0 : Rd d), cubeIdx δ (e₁ d)) := by
  have h1 : scaleIdx ‖e₁ d - 0‖ = 0 := by
    rw [sub_zero, norm_e₁]
    exact scaleIdx_eq (by norm_num) (by norm_num)
  simp only [rootLoc, locOf, h1, side, neg_zero, zpow_zero, mul_one]

theorem nodeLoc_root [NeZero d] (δ : ℝ) (hγ : IsAdmissiblePath d γ) {K : ℕ} {ρ' : ℝ}
    (hT : T.WF γ K ε ρ') : nodeLoc δ T γ [] = rootLoc d δ := by
  simp only [nodeLoc, CutTree.x, CutTree.y, hT.root_time.1, hT.root_time.2, hγ.source,
    hγ.target, rootLoc]

/-- Chord endpoints of nodes are points of the path, hence of `U = (-2, 2)^d`. -/
theorem x_mem_cube (hγ : IsAdmissiblePath d γ) {K : ℕ} {ρ' : ℝ} (hT : T.WF γ K ε ρ')
    {u : List ℕ} (hu : u ∈ T.nodes) : T.x γ u ∈ cube d := by
  obtain ⟨h0, h01, h1⟩ := times_mem hT hu
  exact hγ.mapsTo ⟨h0, h01.trans h1⟩

theorem y_mem_cube (hγ : IsAdmissiblePath d γ) {K : ℕ} {ρ' : ℝ} (hT : T.WF γ K ε ρ')
    {u : List ℕ} (hu : u ∈ T.nodes) : T.y γ u ∈ cube d := by
  obtain ⟨h0, h01, h1⟩ := times_mem hT hu
  exact hγ.mapsTo ⟨h0.trans h01, h1⟩

/-- For `K = 2ⁿ ≥ 2`, all chords of the tree have length at most `1`. -/
theorem R_le_one [NeZero d] (hn : 1 ≤ n) (hγ : IsAdmissiblePath d γ) {ρ' : ℝ}
    (hT : T.WF γ (2 ^ n) ε ρ') {u : List ℕ} (hu : u ∈ T.nodes) : T.R γ u ≤ 1 := by
  have h := (wf_R_bounds hT u.length u hu rfl).2
  rw [root_R_eq_one hγ hT, mul_one] at h
  refine h.trans (pow_le_one₀ (by positivity) ?_)
  have h2 : (2 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact_mod_cast this
  rw [div_le_one (by positivity)]
  linarith

theorem treeHyp_of [NeZero d] (hγ : IsAdmissiblePath d γ) {ρ' : ℝ}
    (hT : T.WF γ (2 ^ n) ε ρ') : TreeHyp T γ (2 ^ n) ε ρ' :=
  ⟨hT, root_R_eq_one hγ hT, by positivity⟩

theorem internal_R_gt {ρ' : ℝ} (hT : T.WF γ (2 ^ n) ε ρ') {u : List ℕ} (hu : u ∈ T.nodes)
    (hn0 : 0 < T.nch u) : ε < T.R γ u :=
  (hT.internal_iff u hu).1 hn0

/-- The chords of the children of an internal node are longer than `ε/(2K)`. -/
theorem child_R_gt {ρ' : ℝ} (hT : T.WF γ (2 ^ n) ε ρ') {u : List ℕ}
    (hu : u ∈ T.nodes) {i : ℕ} (hi : i < T.nch u) :
    ε / (2 * 2 ^ n) < T.R γ (u ++ [i]) := by
  have h1 := (hT.scale u hu i hi).1
  push_cast at h1
  have hR := internal_R_gt hT hu (by omega)
  calc ε / (2 * 2 ^ n) < T.R γ u / (2 * 2 ^ n) :=
        div_lt_div_of_pos_right hR (by positivity)
    _ ≤ T.R γ (u ++ [i]) := h1

/-- The location of a node chord longer than `ε/(2K)` lies in the ranges of the cutoff `ε`. -/
theorem nodeLoc_mem_locRange [NeZero d] (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : IsAdmissiblePath d γ) {ρ' : ℝ} (hT : T.WF γ (2 ^ n) ε ρ') {u : List ℕ}
    (hu : u ∈ T.nodes) (hR : ε / (2 * 2 ^ n) < T.R γ u) :
    nodeLoc δ T γ u ∈ locRange d (scaleMax n ε) (idxMax n δ ε) := by
  have hRpos : 0 < T.R γ u := R_pos (treeHyp_of hγ hT) hu
  have hj0 : 0 ≤ scaleIdx (T.R γ u) := scaleIdx_nonneg hRpos (R_le_one hn hγ hT hu)
  have hjJ : scaleIdx (T.R γ u) ≤ scaleMax n ε := scaleIdx_le_scaleMax hε hR
  rw [mem_locRange]
  exact ⟨⟨hj0, hjJ⟩, cubeIdx_mem_cubeRange hδ hjJ (x_mem_cube hγ hT hu),
    cubeIdx_mem_cubeRange hδ hjJ (y_mem_cube hγ hT hu)⟩

/-- The child times lie in the parent's time interval. -/
theorem child_times_mem {K : ℕ} {ρ' : ℝ} (hT : T.WF γ K ε ρ') {u : List ℕ} (hu : u ∈ T.nodes)
    {i : ℕ} (hi : i < T.nch u) :
    T.t₀ (u ++ [i]) ∈ Icc (T.t₀ u) (T.t₁ u) ∧ T.t₁ (u ++ [i]) ∈ Icc (T.t₀ u) (T.t₁ u) := by
  have hn0 : 0 < T.nch u := by omega
  have h0 : T.t₀ u = ctime T u 0 := (ctime_zero hT hu hn0).symm
  have h1 : T.t₁ u = ctime T u (T.nch u) := (ctime_nch u).symm
  rw [t₀_child hi, t₁_child hT hu hi, h0, h1]
  exact ⟨⟨ctime_mono hT hu (Nat.zero_le _) hi.le, ctime_mono hT hu hi.le le_rfl⟩,
    ⟨ctime_mono hT hu (Nat.zero_le _) (by omega), ctime_mono hT hu (by omega) le_rfl⟩⟩

/-- The endpoints of every child chord lie in `B̄(x_u, ρ₀ R_u)`, `ρ₀ = max(4, 2√d)` (HA3 D1 (iii)
for non-root nodes, (v) for the root; fix F7). -/
theorem child_near [NeZero d] (hγ : IsAdmissiblePath d γ) {K : ℕ}
    (hT : T.WF γ K ε (2 * Real.sqrt d)) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) :
    ‖T.x γ (u ++ [i]) - T.x γ u‖ ≤ rho0 d * T.R γ u ∧
      ‖T.y γ (u ++ [i]) - T.x γ u‖ ≤ rho0 d * T.R γ u := by
  obtain ⟨ht0, ht1⟩ := child_times_mem hT hu hi
  have key : ∀ t ∈ Icc (T.t₀ u) (T.t₁ u), ‖γ t - T.x γ u‖ ≤ rho0 d * T.R γ u := by
    intro t ht
    by_cases hroot : u = []
    · subst hroot
      have hR := root_R_eq_one hγ hT
      rw [hR, mul_one]
      have ht' : t ∈ Icc (0 : ℝ) 1 := by
        rw [hT.root_time.1, hT.root_time.2] at ht; exact ht
      have := hT.root_ball t ht'
      rw [CutTree.x, hT.root_time.1]
      exact this.trans (two_sqrt_le_rho0 d)
    · exact (hT.ball u hu hroot t ht).trans
        (mul_le_mul_of_nonneg_right (four_le_rho0 d) (norm_nonneg _))
  exact ⟨key _ ht0, key _ ht1⟩

/-- Every child chord satisfies the child-chord constraints relative to its parent chord. -/
theorem childChord_child [NeZero d] (hγ : IsAdmissiblePath d γ)
    (hT : T.WF γ (2 ^ n) ε (2 * Real.sqrt d)) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) :
    ChildChord n (T.x γ u) (T.y γ u) (T.x γ (u ++ [i])) (T.y γ (u ++ [i])) := by
  obtain ⟨h1, h2⟩ := hT.scale u hu i hi
  push_cast at h1 h2
  obtain ⟨h3, h4⟩ := child_near hγ hT hu hi
  exact ⟨h1, h2, h3, h4⟩

/-- The scale step between a node and a child, in the form of the record set. -/
theorem scaleStep_child (hε : 0 ≤ ε) {δ : ℝ} {ρ' : ℝ} (hT : T.WF γ (2 ^ n) ε ρ') {u : List ℕ}
    (hu : u ∈ T.nodes) {i : ℕ} (hi : i < T.nch u) :
    ScaleStep n (nodeLoc δ T γ u).1 (nodeLoc δ T γ (u ++ [i])).1 := by
  have h := scaleIdx_child hT hε hu hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  show (n : ℤ) - 1 ≤ scaleIdx (T.R γ (u ++ [i])) - scaleIdx (T.R γ u) ∧
    scaleIdx (T.R γ (u ++ [i])) - scaleIdx (T.R γ u) ≤ n + 1
  omega

theorem x_ne_y [NeZero d] (hγ : IsAdmissiblePath d γ) {ρ' : ℝ}
    (hT : T.WF γ (2 ^ n) ε ρ') {u : List ℕ} (hu : u ∈ T.nodes) : T.x γ u ≠ T.y γ u := by
  intro h
  have := R_pos (treeHyp_of hγ hT) hu
  rw [CutTree.R, h, sub_self, norm_zero] at this
  exact lt_irrefl _ this

/-- The length of the child polygon is `S_u`. -/
theorem polyLen_childPoly (hT' : T.WF γ (2 ^ n) ε (2 * Real.sqrt d)) {u : List ℕ}
    (hu : u ∈ T.nodes) : polyLen (T.childPoly γ u) = T.S γ u := by
  rw [childPoly_eq, polyLen_range_map]
  exact plen_ctime hT' hu

/-- The vertices of the child polygon: `z_i = γ(ctime u i)` for `i ≤ nch u`. -/
theorem childPoly_getD {u : List ℕ} {i : ℕ} (hi : i ≤ T.nch u) :
    (T.childPoly γ u).getD i 0 = γ (ctime T u i) := by
  rw [childPoly_eq, List.getD_eq_getElem _ _
    (by simp only [List.length_map, List.length_range]; omega), List.getElem_map,
    List.getElem_range]

end TreeFacts

/-! ## The record of one node -/

section NodeRecord

variable {d : ℕ} {n : ℕ} {δ ε : ℝ} {T : CutTree} {γ : ℝ → Rd d}

/-- **The record of an internal node** (HA3 D6, "Assignment"): for every internal node `u` and
followed child index `ι`, there are a record `ρ ∈ recSet d n δ ε` with `λ(ρ) = loc(u)`,
`λ'(ρ) = loc(u ι)`, and a configuration `c ∈ Φ(ρ)` whose variable is `δ^{-1/2} G_u`, with
`cost(ρ) ≤ b_u`; `ρ` is good with bin `⌊a_u/δ²⌋` if `a_u ≤ a₀`, and bad with `b_u = a₀/δ²`
otherwise. -/
theorem node_record [NeZero d] (hn : 1 ≤ n) (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : IsAdmissiblePath d γ) (hT : T.WF γ (2 ^ n) ε (2 * Real.sqrt d)) {φ : Rd d → ℝ}
    (hφ : Continuous φ) {u : List ℕ} (hu : u ∈ T.nodes) {ι : ℕ} (hι : ι < T.nch u) :
    ∃ ρ ∈ recSet d n δ ε, ∃ c : Config d,
      ρ.loc = nodeLoc δ T γ u ∧ ρ.nextLoc = nodeLoc δ T γ (u ++ [ι]) ∧
      c ∈ family n δ ρ ∧
      cfgVal δ φ c = δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ u ∧
      ρ.cost n δ ≤ T.bcost γ (a0 n) δ u ∧
      ((∃ g : GoodRec d, ρ = Sum.inl g ∧ T.A γ u ≤ a0 n ∧ g.bin = ⌊T.A γ u / δ ^ 2⌋₊ ∧
          g.idx = ι) ∨
        (∃ b : BadRec d, ρ = Sum.inr b ∧ ¬ T.A γ u ≤ a0 n ∧
          T.bcost γ (a0 n) δ u = a0 n / δ ^ 2)) := by
  have hn0 : 0 < T.nch u := by omega
  have hH := treeHyp_of hγ hT
  have hxy := x_ne_y hγ hT hu
  have hc_mem : u ++ [ι] ∈ T.nodes := hT.child_mem u hu ι hι
  have hxy' := x_ne_y hγ hT hc_mem
  have hK1 : (1 : ℝ) ≤ 2 * 2 ^ n := by
    have := one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := n); linarith
  have hloc_u := nodeLoc_mem_locRange hn hδ hε hγ hT hu
    ((div_le_self hε.le hK1).trans_lt (internal_R_gt hT hu hn0))
  have hloc_c := nodeLoc_mem_locRange hn hδ hε hγ hT hc_mem (child_R_gt hT hu hι)
  have hstep := scaleStep_child hε.le (δ := δ) hT hu hι
  have hδ2 : 0 < δ ^ 2 := by positivity
  by_cases hA : T.A γ u ≤ a0 n
  · -- good node
    obtain ⟨hK, hQ⟩ := goodNode_of_wf hT Nat.one_le_two_pow hε hu hn0 hA
    have hA0 : 0 ≤ T.A γ u := A_nonneg hH hu hn0
    set k := ⌊T.A γ u / δ ^ 2⌋₊ with hk
    have hk1 : (k : ℝ) ≤ T.A γ u / δ ^ 2 := Nat.floor_le (div_nonneg hA0 hδ2.le)
    have hk2 : T.A γ u / δ ^ 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlogA : Real.log (polyLen (T.childPoly γ u) / ‖T.y γ u - T.x γ u‖) = T.A γ u := by
      rw [polyLen_childPoly hT hu]; rfl
    set g : GoodRec d := ⟨k, ι, nodeLoc δ T γ u, nodeLoc δ T γ (u ++ [ι])⟩ with hg
    set c : Config d := ([T.x γ u, T.y γ u], T.childPoly γ u) with hc
    have hιK : ι < 2 ^ n := hK ▸ hι
    have hcfam : c ∈ goodFam n δ g := by
      refine ⟨T.x γ u, T.y γ u, rfl, hasLoc_locOf hδ hxy, hQ, ?_, ?_, hιK, ?_⟩
      · show (k : ℝ) * δ ^ 2 ≤ Real.log (polyLen (T.childPoly γ u) / ‖T.y γ u - T.x γ u‖)
        rw [hlogA]
        exact (le_div_iff₀ hδ2).1 hk1
      · show Real.log (polyLen (T.childPoly γ u) / ‖T.y γ u - T.x γ u‖) < ((k : ℝ) + 1) * δ ^ 2
        rw [hlogA]
        exact (div_lt_iff₀ hδ2).1 hk2
      · show HasLoc δ (nodeLoc δ T γ (u ++ [ι])) ((T.childPoly γ u).getD ι 0)
          ((T.childPoly γ u).getD (ι + 1) 0)
        rw [childPoly_getD hι.le, childPoly_getD (by omega), ← t₀_child hι, ← t₁_child hT hu hι]
        exact hasLoc_locOf hδ hxy'
    have hvalid : RecValid n δ (Sum.inl g : Record d) := ⟨⟨c, hcfam⟩, hιK, hstep⟩
    have hbin : g.bin ≤ binMax n δ := by
      show k ≤ ⌊a0 n / δ ^ 2⌋₊
      exact Nat.floor_le_floor (div_le_div_of_nonneg_right hA hδ2.le)
    refine ⟨Sum.inl g, good_mem_recSet hvalid hbin hιK hloc_u hloc_c, c, rfl, rfl, hcfam, ?_, ?_,
      Or.inl ⟨g, rfl, hA, rfl, rfl⟩⟩
    · rw [cfgVal, G_eq_of_good hT hφ hu hA]
      show δ ^ (-(1 / 2 : ℝ)) * ((∫ z, φ z ∂(polyMeasure [T.x γ u, T.y γ u])) -
        ∫ z, φ z ∂(polyMeasure (T.childPoly γ u))) = _
      rw [polyMeasure_pair hxy]
    · show (k : ℝ) ≤ min (T.A γ u) (a0 n) / δ ^ 2
      rw [min_eq_left hA]
      exact hk1
  · -- bad node
    obtain ⟨w, hw, hG⟩ := G_eq_of_bad hφ hn0 hA
    have hw_mem : u ++ [w] ∈ T.nodes := hT.child_mem u hu w hw
    have hxyw := x_ne_y hγ hT hw_mem
    set j := (nodeLoc δ T γ u).1 with hj
    set b : BadRec d := ⟨nodeLoc δ T γ u, cubeIdx (side δ j) (T.x γ (u ++ [w])),
      cubeIdx (side δ j) (T.y γ (u ++ [w])), nodeLoc δ T γ (u ++ [ι])⟩ with hb
    set c : Config d := ([T.x γ u, T.y γ u], [T.x γ (u ++ [w]), T.y γ (u ++ [w])]) with hc
    have hs := side_pos hδ j
    have hcfam : c ∈ badFam n δ b :=
      ⟨T.x γ u, T.y γ u, T.x γ (u ++ [w]), T.y γ (u ++ [w]), rfl, hasLoc_locOf hδ hxy,
        mem_latCube_cubeIdx hs _, mem_latCube_cubeIdx hs _, childChord_child hγ hT hu hw⟩
    have hvalid : RecValid n δ (Sum.inr b : Record d) :=
      ⟨⟨c, hcfam⟩, hstep, T.x γ u, T.y γ u, T.x γ (u ++ [w]), T.y γ (u ++ [w]),
        T.x γ (u ++ [ι]), T.y γ (u ++ [ι]), hcfam, hasLoc_locOf hδ hxy',
        childChord_child hγ hT hu hι⟩
    have hjJ : j ≤ scaleMax n ε := ((mem_locRange.1 hloc_u).1).2
    have hp : b.advP ∈ cubeRange d (idxMax n δ ε) :=
      cubeIdx_mem_cubeRange hδ hjJ (x_mem_cube hγ hT hw_mem)
    have hq : b.advQ ∈ cubeRange d (idxMax n δ ε) :=
      cubeIdx_mem_cubeRange hδ hjJ (y_mem_cube hγ hT hw_mem)
    have hbcost : T.bcost γ (a0 n) δ u = a0 n / δ ^ 2 := by
      rw [CutTree.bcost, min_eq_right (le_of_not_ge hA)]
    refine ⟨Sum.inr b, bad_mem_recSet hvalid hloc_u hp hq hloc_c, c, rfl, rfl, hcfam, ?_, ?_,
      Or.inr ⟨b, rfl, hA, hbcost⟩⟩
    · rw [cfgVal, hG]
      show δ ^ (-(1 / 2 : ℝ)) * ((∫ z, φ z ∂(polyMeasure [T.x γ u, T.y γ u])) -
        ∫ z, φ z ∂(polyMeasure [T.x γ (u ++ [w]), T.y γ (u ++ [w])])) = _
      rw [polyMeasure_pair hxy, polyMeasure_pair hxyw]
    · rw [hbcost]
      exact le_rfl

end NodeRecord

/-! ## The chain record of a leaf -/

section Assignment

variable {d : ℕ} {n : ℕ} {δ ε : ℝ} {T : CutTree} {γ : ℝ → Rd d}

/-- **The record assignment** along any node (HA3 D6 "Assignment", D7 "Simultaneity"); see
`chainRecord_assignment` for leaves. -/
theorem chainRecord_assignment_of_mem [NeZero d] (hn : 1 ≤ n) (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : IsAdmissiblePath d γ) (hT : T.WF γ (2 ^ n) ε (2 * Real.sqrt d)) {φ : Rd d → ℝ}
    (hφ : Continuous φ) {v : List ℕ} (hv : v ∈ T.nodes) :
    ∃ (ρ : Fin v.length → recSet d n δ ε) (c : Fin v.length → Config d),
      IsChainRec δ (fun i => (ρ i).1) ∧
      (∀ i : Fin v.length,
        c i ∈ family n δ (ρ i).1 ∧
        cfgVal δ φ (c i) = δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ (v.take i) ∧
        (ρ i).1.cost n δ ≤ T.bcost γ (a0 n) δ (v.take i) ∧
        ((∃ g : GoodRec d, (ρ i).1 = Sum.inl g ∧ T.A γ (v.take i) ≤ a0 n ∧
            g.bin = ⌊T.A γ (v.take i) / δ ^ 2⌋₊) ∨
          (∃ b : BadRec d, (ρ i).1 = Sum.inr b ∧ ¬ T.A γ (v.take i) ≤ a0 n ∧
            T.bcost γ (a0 n) δ (v.take i) = a0 n / δ ^ 2))) ∧
      ∑ j ∈ Finset.range v.length,
          (δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ (v.take j) - T.bcost γ (a0 n) δ (v.take j)) ≤
        ∑ i : Fin v.length, (cfgVal δ φ (c i) - (ρ i).1.cost n δ) := by
  have hnode : ∀ i : Fin v.length, ∃ (r : recSet d n δ ε) (c : Config d),
      r.1.loc = nodeLoc δ T γ (v.take i) ∧
      r.1.nextLoc = nodeLoc δ T γ (v.take (i + 1)) ∧
      c ∈ family n δ r.1 ∧
      cfgVal δ φ c = δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ (v.take i) ∧
      r.1.cost n δ ≤ T.bcost γ (a0 n) δ (v.take i) ∧
      ((∃ g : GoodRec d, r.1 = Sum.inl g ∧ T.A γ (v.take i) ≤ a0 n ∧
          g.bin = ⌊T.A γ (v.take i) / δ ^ 2⌋₊) ∨
        (∃ b : BadRec d, r.1 = Sum.inr b ∧ ¬ T.A γ (v.take i) ≤ a0 n ∧
          T.bcost γ (a0 n) δ (v.take i) = a0 n / δ ^ 2)) := by
    intro i
    have hi : (i : ℕ) < v.length := i.2
    have hpre := prefix_mem hT hv (w := v.take i) (i := v[(i : ℕ)])
      (by rw [List.take_append_getElem hi]; exact List.take_prefix _ _)
    obtain ⟨ρ, hρ, c, hloc, hnext, hfam, hval, hcost, hgb⟩ :=
      node_record hn hδ hε hγ hT hφ hpre.1 hpre.2
    refine ⟨⟨ρ, hρ⟩, c, hloc, ?_, hfam, hval, hcost, ?_⟩
    · rw [hnext, List.take_append_getElem hi]
    · rcases hgb with ⟨g, hg, hA, hbin, -⟩ | hbad
      · exact Or.inl ⟨g, hg, hA, hbin⟩
      · exact Or.inr hbad
  choose ρ c hρc using hnode
  refine ⟨ρ, c, ⟨fun h => ?_, fun i h => ?_⟩, fun i => ?_, ?_⟩
  · show (ρ ⟨0, h⟩).1.loc = rootLoc d δ
    rw [(hρc ⟨0, h⟩).1]
    simp only [List.take_zero]
    exact nodeLoc_root δ hγ hT
  · show (ρ ⟨i + 1, h⟩).1.loc = (ρ ⟨i, by omega⟩).1.nextLoc
    rw [(hρc ⟨i + 1, h⟩).1, (hρc ⟨i, by omega⟩).2.1]
  · obtain ⟨-, -, hfam, hval, hcost, hgb⟩ := hρc i
    exact ⟨hfam, hval, hcost, hgb⟩
  · rw [Finset.sum_range (fun j => δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ (v.take j) -
      T.bcost γ (a0 n) δ (v.take j))]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨-, -, -, hval, hcost, -⟩ := hρc i
    rw [hval]
    linarith

/-- **The record assignment** (HA3 D6 "Assignment", with the fix F1; used in D7
"Simultaneity").  Let `γ` be an admissible path, `T` a well-formed partition tree of `γ` at ratio
`K = 2ⁿ` (`n ≥ 1`), cutoff `ε > 0` and root radius `2√d`, `φ` a continuous field, `δ > 0`, and
`v` a leaf.  Then there are a chain record `ρ = (ρ_0, …, ρ_{|v|-1})` of records of the finite
record set `recSet d n δ ε` and configurations `c_i ∈ Φ(ρ_i)` such that, for the ancestors
`u_i = v.take i`:

* the variable of `c_i` is `δ^{-1/2} G_{u_i}`;
* `cost(ρ_i) ≤ b_{u_i}`; precisely, either `ρ_i` is good, `a_{u_i} ≤ a₀` and its bin is
  `k_i = ⌊a_{u_i}/δ²⌋` (so `k_i ≤ b_{u_i}`), or `ρ_i` is bad, `a_{u_i} > a₀` and
  `b_{u_i} = a₀/δ²`;
* consequently `Σ_{u ≺ v} (δ^{-1/2} G_u - b_u) ≤ Σ_i (Y(c_i) - cost(ρ_i))`.

The adverse children (hence the records of bad nodes) depend on `φ`; the families do not. -/
theorem chainRecord_assignment [NeZero d] (hn : 1 ≤ n) (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : IsAdmissiblePath d γ) (hT : T.WF γ (2 ^ n) ε (2 * Real.sqrt d)) {φ : Rd d → ℝ}
    (hφ : Continuous φ) {v : List ℕ} (hv : v ∈ T.leaves) :
    ∃ (ρ : Fin v.length → recSet d n δ ε) (c : Fin v.length → Config d),
      IsChainRec δ (fun i => (ρ i).1) ∧
      (∀ i : Fin v.length,
        c i ∈ family n δ (ρ i).1 ∧
        cfgVal δ φ (c i) = δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ (v.take i) ∧
        (ρ i).1.cost n δ ≤ T.bcost γ (a0 n) δ (v.take i) ∧
        ((∃ g : GoodRec d, (ρ i).1 = Sum.inl g ∧ T.A γ (v.take i) ≤ a0 n ∧
            g.bin = ⌊T.A γ (v.take i) / δ ^ 2⌋₊) ∨
          (∃ b : BadRec d, (ρ i).1 = Sum.inr b ∧ ¬ T.A γ (v.take i) ≤ a0 n ∧
            T.bcost γ (a0 n) δ (v.take i) = a0 n / δ ^ 2))) ∧
      ∑ j ∈ Finset.range v.length,
          (δ ^ (-(1 / 2 : ℝ)) * T.G γ (a0 n) φ (v.take j) - T.bcost γ (a0 n) δ (v.take j)) ≤
        ∑ i : Fin v.length, (cfgVal δ φ (c i) - (ρ i).1.cost n δ) :=
  chainRecord_assignment_of_mem hn hδ hε hγ hT hφ (Finset.mem_filter.1 hv).1

end Assignment

end HigherDimLFPP.Upper
