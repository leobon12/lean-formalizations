import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import QuantumZipper.Proofs.Complex.HoloLog
import QuantumZipper.Proofs.Complex.RMTStep3
import QuantumZipper.Proofs.Complex.TopoEilenberg
import SupercriticalConformalCovariance.Frozen.IsConformalBijection

/-!
# Planar simple connectivity

Design `planning/INFRA-GEO.md` §3 (packet GEO-SC). Mathlib's `IsSimplyConnected U` (the subtype `U`
is a simply connected space) is related to the planar notions the host library QuantumZipper works
with: "every component of `ℂ \ U` is unbounded" and "holomorphic square roots exist"
(`QuantumZipper.CA.RMT.HasHoloSqrt`).

## Main results

* `isSimplyConnected_iff_forall_not_isBounded`: a connected open `U ⊆ ℂ` is simply connected iff
  every component of `ℂ \ U` is unbounded: the homotopy definition (Mathlib) agrees with the
  complement definition (Ahlfors, *Complex Analysis*, 3rd ed. 1979, Ch. 4 §4.2, the citation
  pinned in QuantumZipper's `HoloLog`).
* `exists_differentiableOn_exp_eq_of_isSimplyConnected`: holomorphic logarithms of zero-free
  holomorphic functions on simply connected open sets;
* `hasHoloSqrt_of_isSimplyConnected`: hence holomorphic square roots (the input of QuantumZipper's
  Riemann mapping theorem);
* `isSimplyConnected_of_isConformalBijection`: simple connectivity is carried along conformal
  bijections.

## Proof routes

* (⇐) QuantumZipper's `hasHoloSqrt_of_unbounded_compl` and Riemann mapping theorem give a
  holomorphic bijection `𝔻 → U` with holomorphic inverse, and the disc is convex.
* (⇒) If `a ∉ U` has a bounded component `C` of `ℂ \ U`, a compact relatively clopen piece `K ⊇ C`
  of `ℂ \ U` is cut out by the clopen description of components in compact Hausdorff spaces
  (`connectedComponent_eq_iInter_isClopen`). The frontier `J` of a relatively compact open
  neighbourhood of `K` avoiding the rest of `ℂ \ U` is a compact subset of `U` that separates `a`
  from a far point `b`. A continuous logarithm of `z - a` on `U` (Mathlib,
  `Complex.exists_continuousOn_eqOn_exp_comp`) then contradicts Eilenberg's criterion
  (QuantumZipper `false_of_hasLogOn_of_isBounded`). The separation step follows the compact-frontier
  lemma of an earlier formalization, adapted.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE

/-! ### Holomorphic logarithms and square roots -/

/-- A continuous logarithm of a holomorphic function on an open set is holomorphic: near each point
it differs from a principal-branch logarithm by a constant. (Private: the public version of this
fact is GEO-DLOG's `InteractingSLE.differentiableOn_of_continuousOn_of_exp_eq` in
`Foundations/Complex/DerivLog.lean`, which this module does not import.) -/
private theorem differentiableOn_of_continuousOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U) {g f : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hf : ContinuousOn f U) (hfg : ∀ z ∈ U, exp (f z) = g z) :
    DifferentiableOn ℂ f U := by
  intro z hz
  set c := g z with hc
  have hc0 : c ≠ 0 := by rw [hc, ← hfg z hz]; exact exp_ne_zero _
  have hgz : DifferentiableAt ℂ g z := hg.differentiableAt (hU.mem_nhds hz)
  have h1 : g z / c ∈ slitPlane := by rw [← hc, div_self hc0]; exact one_mem_slitPlane
  -- the principal-branch candidate `f z + log (g y / c)`
  have hLd : DifferentiableAt ℂ (fun y => f z + log (g y / c)) z :=
    ((hgz.div_const c).clog h1).const_add _
  have hLc : ContinuousAt (fun y => log (g y / c)) z := ((hgz.div_const c).clog h1).continuousAt
  have hL0 : log (g z / c) = 0 := by rw [← hc, div_self hc0, log_one]
  have ev1 : ∀ᶠ y in 𝓝 z, y ∈ U := hU.mem_nhds hz
  have ev2 : ∀ᶠ y in 𝓝 z, ‖f y - f z‖ < 1 := by
    have := (hf.continuousAt (hU.mem_nhds hz)).eventually (Metric.ball_mem_nhds (f z) one_pos)
    filter_upwards [this] with y hy
    rwa [dist_eq_norm] at hy
  have ev3 : ∀ᶠ y in 𝓝 z, ‖log (g y / c)‖ < 1 := by
    have := hLc.eventually (Metric.ball_mem_nhds (log (g z / c)) one_pos)
    filter_upwards [this] with y hy
    rwa [dist_eq_norm, hL0, sub_zero] at hy
  have heq : (fun y => f z + log (g y / c)) =ᶠ[𝓝 z] f := by
    filter_upwards [ev1, ev2, ev3] with y hyU hy2 hy3
    have hgy : g y ≠ 0 := by rw [← hfg y hyU]; exact exp_ne_zero _
    have hexp : exp (f y - f z) = exp (log (g y / c)) := by
      rw [exp_log (div_ne_zero hgy hc0), exp_sub, hfg y hyU, hfg z hz]
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 hexp
    have hn0 : n = 0 := by
      by_contra hne
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
        exact_mod_cast this
      have hnorm : ‖(n : ℂ) * (2 * π * I)‖ = |(n : ℝ)| * (2 * π) := by
        rw [norm_mul, norm_mul, norm_mul, norm_I, mul_one, Complex.norm_intCast, Complex.norm_two,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have hle : ‖(n : ℂ) * (2 * π * I)‖ ≤ ‖f y - f z‖ + ‖log (g y / c)‖ := by
        have : (n : ℂ) * (2 * π * I) = (f y - f z) - log (g y / c) := by rw [hn]; ring
        rw [this]
        exact norm_sub_le _ _
      have hpi : (2 : ℝ) ≤ π := Real.two_le_pi
      nlinarith
    rw [hn0] at hn
    simp only [Int.cast_zero, zero_mul, add_zero] at hn
    rw [← hn]
    ring
  exact (hLd.congr_of_eventuallyEq heq.symm).differentiableWithinAt

/-- **Holomorphic logarithms on simply connected open sets.** A zero-free holomorphic function on
an open simply connected `U ⊆ ℂ` has a holomorphic logarithm on `U`. -/
theorem exists_differentiableOn_exp_eq_of_isSimplyConnected {U : Set ℂ} (hUo : IsOpen U)
    (hsc : IsSimplyConnected U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (h0 : ∀ z ∈ U, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ ∀ z ∈ U, exp (L z) = g z := by
  have hU0 : (0 : ℂ) ∉ g '' U := by
    rintro ⟨z, hz, hgz⟩
    exact h0 z hz hgz
  obtain ⟨L, hLc, hL⟩ := exists_continuousOn_eqOn_exp_comp hsc hUo hg.continuousOn hU0
  exact ⟨L, differentiableOn_of_continuousOn_of_exp_eq hUo hg hLc fun z hz => hL hz,
    fun z hz => hL hz⟩

/-- Simply connected open sets have the holomorphic square root property, the input of
QuantumZipper's Riemann mapping theorem `QuantumZipper.CA.RMT.riemann_mapping_of_hasHoloSqrt`. -/
theorem hasHoloSqrt_of_isSimplyConnected {U : Set ℂ} (hUo : IsOpen U)
    (hsc : IsSimplyConnected U) : QuantumZipper.CA.RMT.HasHoloSqrt U := by
  intro g hg h0
  obtain ⟨L, hL, hexp⟩ := exists_differentiableOn_exp_eq_of_isSimplyConnected hUo hsc hg h0
  refine ⟨fun z => exp (L z / 2), (hL.div_const 2).cexp, fun z hz => ?_⟩
  have h2 : ((2 : ℕ) : ℂ) * (L z / 2) = L z := by push_cast; ring
  rw [← Complex.exp_nat_mul, h2, hexp z hz]

/-! ### Transport along conformal bijections -/

/-- An open disc is simply connected (it is convex). -/
theorem isSimplyConnected_ball (c : ℂ) {r : ℝ} (hr : 0 < r) : IsSimplyConnected (ball c r) := by
  have := (convex_ball c r).contractibleSpace (nonempty_ball.2 hr)
  exact SimplyConnectedSpace.ofContractible _

/-- The plane is simply connected. -/
theorem isSimplyConnected_univ : IsSimplyConnected (univ : Set ℂ) := by
  have := convex_univ.contractibleSpace (E := ℂ) univ_nonempty
  exact SimplyConnectedSpace.ofContractible _

/-- **Simple connectivity is carried along conformal bijections**: a holomorphic bijection of an
open simply connected `U` onto `V` is a homeomorphism `U ≃ₜ V` (open mapping theorem). -/
theorem isSimplyConnected_of_isConformalBijection {φ : ℂ → ℂ} {U V : Set ℂ} (hUo : IsOpen U)
    (hφ : IsConformalBijection φ U V) (hU : IsSimplyConnected U) : IsSimplyConnected V := by
  rw [← hφ.2.image_eq]
  have : SimplyConnectedSpace U := hU
  exact (QuantumZipper.CA.univalentHomeomorph hUo hφ.1 hφ.2.injOn).symm.toHomotopyEquiv
    |>.simplyConnectedSpace

/-! ### Bounded complementary components -/

/-- A bounded component of a closed planar set `F` lies in a compact piece `K ⊆ F` whose
complement `F \ K` in `F` is closed (components of compact Hausdorff spaces are intersections of
clopen sets). -/
theorem exists_isCompact_isClosed_diff_of_isBounded_connectedComponentIn {F : Set ℂ}
    (hF : IsClosed F) {a : ℂ} (ha : a ∈ F)
    (hC : Bornology.IsBounded (connectedComponentIn F a)) :
    ∃ K ⊆ F, IsCompact K ∧ a ∈ K ∧ IsClosed (F \ K) := by
  classical
  obtain ⟨R, hR⟩ := hC.subset_ball (0 : ℂ)
  set B : Set ℂ := F ∩ closedBall 0 (R + 1) with hBdef
  have hBc : IsCompact B := (isCompact_closedBall _ _).inter_left hF
  have : CompactSpace B := isCompact_iff_compactSpace.mp hBc
  have haR : ‖a‖ < R := mem_ball_zero_iff.1 (hR (mem_connectedComponentIn ha))
  have haB : a ∈ B := ⟨ha, mem_closedBall_zero_iff.2 (by linarith)⟩
  set x : B := ⟨a, haB⟩ with hx
  -- the component of `x` in `B` stays inside `C ⊆ ball 0 R`
  have hcomp : ∀ y ∈ connectedComponent x, ‖(y : ℂ)‖ < R := by
    intro y hy
    have hpre : IsPreconnected (((↑) : B → ℂ) '' connectedComponent x) :=
      isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
    have hsub : ((↑) : B → ℂ) '' connectedComponent x ⊆ connectedComponentIn F a :=
      hpre.subset_connectedComponentIn ⟨x, mem_connectedComponent, rfl⟩
        (image_subset_iff.2 fun y _ => y.2.1)
    exact mem_ball_zero_iff.1 (hR (hsub ⟨y, hy, rfl⟩))
  set S : Set B := {y | R ≤ ‖(y : ℂ)‖} with hSdef
  have hS : IsClosed S := isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)
  have hdisj : Disjoint S (⋂ s : {s : Set B // IsClopen s ∧ x ∈ s}, s.1) := by
    rw [← connectedComponent_eq_iInter_isClopen, Set.disjoint_left]
    intro y hyS hyc
    exact absurd (hcomp y hyc) (not_lt.2 hyS)
  obtain ⟨t, ht⟩ := hS.isCompact.elim_finite_subfamily_closed
    (fun s : {s : Set B // IsClopen s ∧ x ∈ s} => s.1) (fun s => s.2.1.1) hdisj
  set Q : Set B := ⋂ s ∈ t, s.1 with hQdef
  have hQ : IsClopen Q := isClopen_biInter_finset fun s _ => s.2.1
  have hxQ : x ∈ Q := mem_iInter₂.2 fun s _ => s.2.2
  have hQR : ∀ y ∈ Q, ‖(y : ℂ)‖ < R := fun y hy =>
    not_le.1 fun hyS => Set.disjoint_left.1 ht hyS hy
  refine ⟨((↑) : B → ℂ) '' Q, image_subset_iff.2 fun y _ => y.2.1,
    hQ.isClosed.isCompact.image continuous_subtype_val, ⟨x, hxQ, rfl⟩, ?_⟩
  rw [← closure_subset_iff_isClosed]
  intro p hp
  have hpF : p ∈ F := closure_minimal sdiff_subset hF hp
  refine ⟨hpF, ?_⟩
  rintro ⟨q, hq, rfl⟩
  obtain ⟨O, hO, hOQ⟩ := isOpen_induced_iff.1 hQ.isOpen
  have hqO : (q : ℂ) ∈ O := by
    have : q ∈ ((↑) : B → ℂ) ⁻¹' O := by rw [hOQ]; exact hq
    exact this
  have hqR := hQR q hq
  have hnhd : O ∩ ball 0 (R + 1) ∈ 𝓝 (q : ℂ) :=
    inter_mem (hO.mem_nhds hqO) (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith)))
  obtain ⟨w, ⟨hwO, hwball⟩, hwF, hwK⟩ := mem_closure_iff_nhds.1 hp _ hnhd
  apply hwK
  refine ⟨⟨w, hwF, ball_subset_closedBall hwball⟩, ?_, rfl⟩
  have : (⟨w, hwF, ball_subset_closedBall hwball⟩ : B) ∈ ((↑) : B → ℂ) ⁻¹' O := hwO
  rwa [hOQ] at this

/-- The component of `Jᶜ` through a point of an open set `W` with frontier `J` lies in `W`. -/
theorem connectedComponentIn_compl_frontier_subset {W : Set ℂ} (hWo : IsOpen W) {a : ℂ}
    (haW : a ∈ W) : connectedComponentIn (frontier W)ᶜ a ⊆ W := by
  have haJ : a ∈ (frontier W)ᶜ := fun h => by
    rw [hWo.frontier_eq] at h
    exact h.2 haW
  have hJcompl : (frontier W)ᶜ = W ∪ (closure W)ᶜ := by
    ext z
    simp only [hWo.frontier_eq, mem_compl_iff, Set.mem_sdiff, not_and, not_not, mem_union]
    constructor
    · intro h
      by_cases hz : z ∈ closure W
      · exact Or.inl (h hz)
      · exact Or.inr hz
    · rintro (h | h) h'
      · exact h
      · exact absurd h' h
  have hCsub : connectedComponentIn (frontier W)ᶜ a ⊆ W ∪ (closure W)ᶜ := by
    rw [← hJcompl]
    exact connectedComponentIn_subset _ a
  have hdis : connectedComponentIn (frontier W)ᶜ a ∩ (W ∩ (closure W)ᶜ) = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
    intro hz
    exact hz.2.2 (subset_closure hz.2.1)
  rcases (isPreconnected_iff_subset_of_disjoint).1 isPreconnected_connectedComponentIn W
      (closure W)ᶜ hWo isClosed_closure.isOpen_compl hCsub hdis with h | h
  · exact h
  · exact absurd (subset_closure haW) (h (mem_connectedComponentIn haJ))

/-- **Simply connected planar domains have no bounded complementary component** (the hard
direction of `isSimplyConnected_iff_forall_not_isBounded`). -/
theorem not_isBounded_connectedComponentIn_compl_of_isSimplyConnected {U : Set ℂ}
    (hUo : IsOpen U) (hsc : IsSimplyConnected U) {a : ℂ} (ha : a ∉ U) :
    ¬ Bornology.IsBounded (connectedComponentIn Uᶜ a) := by
  intro hC
  obtain ⟨K, hKF, hK, haK, hFK⟩ :=
    exists_isCompact_isClosed_diff_of_isBounded_connectedComponentIn hUo.isClosed_compl ha hC
  obtain ⟨W, hWo, hKW, hWF, hWc⟩ := exists_open_between_and_isCompact_closure hK
    hFK.isOpen_compl (fun z hz hz' => hz'.2 hz)
  set J := frontier W with hJdef
  have hJU : J ⊆ U := by
    intro z hz
    by_contra hzU
    have hzW : z ∉ W := by
      rw [hJdef, hWo.frontier_eq] at hz
      exact hz.2
    exact hWF (frontier_subset_closure hz) ⟨hzU, fun hzK => hzW (hKW hzK)⟩
  have haW : a ∈ W := hKW haK
  have haJ : a ∉ J := fun h => by
    rw [hJdef, hWo.frontier_eq] at h
    exact h.2 haW
  have hCW : connectedComponentIn Jᶜ a ⊆ W := connectedComponentIn_compl_frontier_subset hWo haW
  obtain ⟨M, hM⟩ := hWc.isBounded.subset_ball (0 : ℂ)
  have hJM : ∀ z ∈ J, ‖z‖ < M := fun z hz =>
    mem_ball_zero_iff.1 (hM (frontier_subset_closure hz))
  have hM0 : 0 < M := lt_of_le_of_lt (norm_nonneg a)
    (mem_ball_zero_iff.1 (hM (subset_closure haW)))
  set b : ℂ := (M : ℂ) with hb
  have hbW : b ∉ closure W := fun h => by
    have := mem_ball_zero_iff.1 (hM h)
    rw [hb, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0] at this
    exact lt_irrefl _ this
  have hbJ : b ∉ J := fun h => hbW (frontier_subset_closure h)
  have hbC : b ∉ connectedComponentIn Jᶜ a := fun h => hbW (subset_closure (hCW h))
  -- a continuous logarithm of `z - a` on `U`
  have hU0 : (0 : ℂ) ∉ (fun z : ℂ => z - a) '' U := by
    rintro ⟨z, hz, hza⟩
    exact ha (sub_eq_zero.1 hza ▸ hz)
  obtain ⟨L, hLc, hL⟩ := exists_continuousOn_eqOn_exp_comp hsc hUo
    (continuousOn_id.sub continuousOn_const) hU0
  have hre : ∀ z ∈ J, 0 < (b - z).re := fun z hz => by
    have h1 := hJM z hz
    have h2 : z.re ≤ ‖z‖ := Complex.re_le_norm z
    simp only [hb, sub_re, ofReal_re]
    linarith
  have hlog : QuantumZipper.CA.Topo.HasLogOn (fun z => (z - a) / (z - b)) J := by
    refine ⟨fun z => L z - (log (b - z) + π * I), ?_, fun z hz => ?_⟩
    · refine (hLc.mono hJU).sub (ContinuousOn.add ?_ continuousOn_const)
      exact ContinuousOn.clog (continuousOn_const.sub continuousOn_id)
        fun z hz => Or.inl (hre z hz)
    · have hbz : b - z ≠ 0 := fun h => by
        have := hre z hz
        rw [h, zero_re] at this
        exact lt_irrefl _ this
      have hLz : exp (L z) = z - a := hL (hJU hz)
      rw [exp_sub, exp_add, exp_log hbz, exp_pi_mul_I, hLz]
      have hzb : z - b ≠ 0 := fun h => hbz (by rw [← neg_sub, h, neg_zero])
      field_simp
      ring
  exact QuantumZipper.CA.Topo.false_of_hasLogOn_of_isBounded isClosed_frontier haJ hbJ hbC
    (hWc.isBounded.subset (hCW.trans subset_closure)) hlog

/-- **Planar simple connectivity**: a connected open `U ⊆ ℂ` all of whose complementary
components are unbounded is simply connected (the easy direction of
`isSimplyConnected_iff_forall_not_isBounded`). -/
theorem isSimplyConnected_of_forall_not_isBounded {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsConnected U)
    (h : ∀ a ∉ U, ¬ Bornology.IsBounded (connectedComponentIn Uᶜ a)) : IsSimplyConnected U := by
  by_cases hU : U = univ
  · rw [hU]
    exact isSimplyConnected_univ
  have hsq := QuantumZipper.CA.RMT.hasHoloSqrt_of_unbounded_compl hUo hUc.isPreconnected h
  obtain ⟨-, -, -, ψ, hψbij, hψd, -⟩ :=
    QuantumZipper.CA.RMT.riemann_mapping_of_hasHoloSqrt hUo hUc.isPreconnected hUc.nonempty hU hsq
  exact isSimplyConnected_of_isConformalBijection isOpen_ball ⟨hψd, hψbij⟩
    (isSimplyConnected_ball 0 one_pos)

/-- **Planar simple connectivity** (Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4 §4.2): a
connected open `U ⊆ ℂ` is simply connected iff every component of `ℂ \ U` is unbounded. -/
theorem isSimplyConnected_iff_forall_not_isBounded {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsConnected U) :
    IsSimplyConnected U ↔ ∀ a ∉ U, ¬ Bornology.IsBounded (connectedComponentIn Uᶜ a) :=
  ⟨fun hsc _ ha => not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hUo hsc ha,
    isSimplyConnected_of_forall_not_isBounded hUo hUc⟩

end InteractingSLE
