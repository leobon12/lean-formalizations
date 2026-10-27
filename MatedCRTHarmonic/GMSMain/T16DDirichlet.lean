import MatedCRTHarmonic.GMS3.FirstVisit
import MatedCRTHarmonic.GMS3.Cells
import MatedCRTHarmonic.GMS3.Lemma38

/-!
# The discrete Dirichlet problem on `G^ε(D)`

Source: Gwynne–Miller–Sheffield, *Harmonic functions on mated-CRT maps* [18]
(`[18]:N` is line N): the sub-graph `G^ε(D)` of (1.5) ([18], vertex
set `V(G^ε(D)) = {x : H_x ∩ D ≠ ∅}`) and "the function `f_ε`" of (1.6): `f_ε : V(G^ε(D)) → ℝ` equals
the boundary data on `V(G^ε(∂D))` and is discrete harmonic on `V(G^ε(D)) \ V(G^ε(∂D))`. This file proves that the
definite article is justified (existence and uniqueness), the random-walk representation
`f_ε(x) = E_x[f_ε(X_τ)]` (`τ` the hitting time of `V(G^ε(∂D))`) and the maximum principle; in particular,
("interior vertices have all their neighbours in `V(D)`").

## Abstract layer (a locally finite multigraph `G`, finite vertex sets `S`, `B`)

* `IsDirichletSolution G S B g f`: `lap G f = 0` on `S \ B` and `f = g` on `S ∩ B` (`GMS3.lap`: the unnormalized
  Laplacian over edge ends, so multiple edges count with multiplicity; `lap G f x = 0` iff `f(x)` is the average of
  `f` over the edge ends at `x`, i.e. `f` is harmonic for simple random walk at `x`).
* `lap_sub`, `lap_neg`, `lap_sum_mul`: linearity of the Laplacian.
* `exists_mem_boundary_eq_max` (**maximum principle**, strong form): if every vertex of `S \ B` has all of its dart
  heads in `S`, `G` is connected and some vertex lies outside `S`, a function harmonic on `S \ B` attains its maximum
  over `S` at a vertex of `S ∩ B`; `le_of_harmonic`, `ge_of_harmonic`: the weak maximum and minimum principles.
* `eqOn_of_isDirichletSolution` (**uniqueness** on `S`).
* `dirichletSol G B g x = ∑_{b ∈ B} g(b) P_x(X_{τ_B} = b)` and `isDirichletSolution_dirichletSol` (**existence**;
  no connectivity is needed for it).
* `walkLaw_hitTime_eq_one` (the walk from `S` hits `B` almost surely), `ae_hitVertex_mem` (almost surely it first
  hits `B` inside `S ∩ B`), `integral_hitVertex` (`E_x[F(X_τ)] = ∑_{b ∈ B} F(b) P_x(X_τ = b)`) and
  `eq_integral_of_isDirichletSolution` (**walk representation** `f(x) = E_x[f(X_τ)]`).

## Cell layer (a cellular embedding `H` of a connected `G`, a bounded open `D ⊂ ℂ`)

* `vBd H D = V(∂D)` (the finset `GMS3.vFin H (frontier D)`; `coe_vBd`: it is the frozen
  `verticesMeeting H.cell (frontier D)`); `V(D)` is `GMS3.vFin H D` (finite: `GMS3.finite_verticesMeeting`; equal to
  `verticesMeeting H.cell D`: `GMS3.coe_vFin`).
* `dtgt_mem_vFin_of_interior`, `mem_vFin_of_adj_of_interior`: interior vertices have all their neighbours in `V(D)`;
  `exists_notMem_vFin`: some vertex lies outside `V(D)` (cellular embeddings have infinitely many vertices).
* `IsCellDirichletSolution H D g f` (= `IsDirichletSolution G V(D) V(∂D) g f`), and the cell theorems
  `existsUnique_cellDirichlet`, `cellDirichlet_walkLaw_hitTime_eq_one`, `cellDirichlet_eq_integral`,
  `cellDirichlet_le`, `cellDirichlet_ge`.
* `bdryVal H D f x = sup_{z ∈ H_x ∩ ∂D} f(z)` ((1.6)), attained for `f` continuous on `∂D` (`exists_bdryVal_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSMain.T16D

open LFMultigraph Harmonic HarmonicInfinity Markov GMS3

variable {V E : Type*} (G : LFMultigraph V E)

/-! ### Linearity of the Laplacian -/

theorem lap_sub (f h : V → ℝ) (x : V) : lap G (f - h) x = lap G f x - lap G h x := by
  unfold lap
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem lap_neg (f : V → ℝ) (x : V) : lap G (-f) x = -lap G f x := by
  unfold lap
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Pi.neg_apply]
  ring

theorem lap_sum_mul {ι : Type*} (T : Finset ι) (c : ι → ℝ) (φ : ι → V → ℝ) (x : V) :
    lap G (fun y => ∑ i ∈ T, c i * φ i y) x = ∑ i ∈ T, c i * lap G (φ i) x := by
  unfold lap
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### The Dirichlet problem on a finite vertex set -/

/-- **The discrete Dirichlet problem** on the finite vertex set `S` with boundary vertex set `B`: `f` is discrete
harmonic (`lap G f x = 0`) at every vertex of `S` outside `B` and equals `g` at every vertex of `S` in `B`. Only the
values of `f` on `S` and of `g` on `S ∩ B` matter. -/
def IsDirichletSolution (S B : Finset V) (g f : V → ℝ) : Prop :=
  (∀ x ∈ S, x ∉ B → lap G f x = 0) ∧ ∀ x ∈ S, x ∈ B → f x = g x

/-- At a vertex where `u` is harmonic and at least its values at all dart heads, `u` is constant on the dart heads. -/
theorem eq_of_lap_eq_zero_of_le {u : V → ℝ} {x : V} (hlap : lap G u x = 0)
    (hle : ∀ d ∈ G.outDarts x, u (G.dtgt d) ≤ u x) : ∀ d ∈ G.outDarts x, u (G.dtgt d) = u x := by
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun d hd => sub_nonneg.mpr (hle d hd))).mp hlap
  intro d hd
  linarith [h0 d hd]

/-- **Propagation of a maximum along a walk.** Let `u` be harmonic at the vertices of `S \ B`, all of whose dart heads
lie in `S`, and let `M` bound `u` on `S`. A walk that starts at `a ∈ S` with `u a = M` and ends outside `S` visits a
vertex `b ∈ S ∩ B` with `u b = M`. -/
theorem exists_mem_boundary_of_walk {S B : Finset V} {u : V → ℝ} {M : ℝ}
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S)
    (hharm : ∀ x ∈ S, x ∉ B → lap G u x = 0) (hM : ∀ x ∈ S, u x ≤ M) :
    ∀ {a c : V} (_ : G.adj.Walk a c), a ∈ S → u a = M → c ∉ S → ∃ b ∈ S, b ∈ B ∧ u b = M := by
  intro a c p
  induction p with
  | nil => intro ha _ hc; exact absurd ha hc
  | @cons a w c hadj q ih =>
    intro ha hua hc
    by_cases haB : a ∈ B
    · exact ⟨a, ha, haB, hua⟩
    · obtain ⟨d, hd1, hd2⟩ := exists_dart_of_adj G hadj
      have hdmem : d ∈ G.outDarts a := (mem_outDarts G).mpr hd1
      have hw : w ∈ S := hd2 ▸ hnb a ha haB d hdmem
      have heq := eq_of_lap_eq_zero_of_le G (hharm a ha haB)
        (fun d' hd' => hua ▸ hM _ (hnb a ha haB d' hd'))
      have huw : u w = M := by rw [← hd2, heq d hdmem, hua]
      exact ih hw huw hc

/-- **Maximum principle, strong form.** If every vertex of `S \ B` has all of its dart heads in `S`, `G` is connected
and some vertex lies outside `S`, then a function harmonic on `S \ B` attains its maximum over the (nonempty) set `S`
at a vertex of `S ∩ B`. -/
theorem exists_mem_boundary_eq_max {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) {u : V → ℝ}
    (hharm : ∀ x ∈ S, x ∉ B → lap G u x = 0) (hS : S.Nonempty) :
    ∃ b ∈ S, b ∈ B ∧ ∀ x ∈ S, u x ≤ u b := by
  obtain ⟨x₀, hx₀, hmax⟩ := S.exists_max_image u hS
  obtain ⟨w, hw⟩ := hout
  obtain ⟨p⟩ := hconn.preconnected x₀ w
  obtain ⟨b, hb, hbB, hub⟩ := exists_mem_boundary_of_walk G hnb hharm hmax p hx₀ rfl hw
  exact ⟨b, hb, hbB, fun x hx => hub ▸ hmax x hx⟩

/-- **Weak maximum principle**: a function harmonic on `S \ B` and at most `M` on `S ∩ B` is at most `M` on `S`. -/
theorem le_of_harmonic {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) {u : V → ℝ}
    (hharm : ∀ x ∈ S, x ∉ B → lap G u x = 0) {M : ℝ} (hbd : ∀ x ∈ S, x ∈ B → u x ≤ M) :
    ∀ x ∈ S, u x ≤ M := by
  intro x hx
  obtain ⟨b, hb, hbB, hmax⟩ := exists_mem_boundary_eq_max G hconn hout hnb hharm ⟨x, hx⟩
  exact (hmax x hx).trans (hbd b hb hbB)

/-- **Weak minimum principle**: a function harmonic on `S \ B` and at least `m` on `S ∩ B` is at least `m` on `S`. -/
theorem ge_of_harmonic {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) {u : V → ℝ}
    (hharm : ∀ x ∈ S, x ∉ B → lap G u x = 0) {m : ℝ} (hbd : ∀ x ∈ S, x ∈ B → m ≤ u x) :
    ∀ x ∈ S, m ≤ u x := by
  have h := le_of_harmonic G hconn hout hnb (u := -u) (M := -m)
    (fun x hx hxB => by rw [lap_neg, hharm x hx hxB, neg_zero])
    (fun x hx hxB => by simp only [Pi.neg_apply, neg_le_neg_iff]; exact hbd x hx hxB)
  intro x hx
  have := h x hx
  simp only [Pi.neg_apply, neg_le_neg_iff] at this
  exact this

/-- **Uniqueness**: two solutions of the Dirichlet problem with the same boundary data agree on `S`. -/
theorem eqOn_of_isDirichletSolution {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) {g f₁ f₂ : V → ℝ}
    (h₁ : IsDirichletSolution G S B g f₁) (h₂ : IsDirichletSolution G S B g f₂) :
    ∀ x ∈ S, f₁ x = f₂ x := by
  have hharm : ∀ x ∈ S, x ∉ B → lap G (f₁ - f₂) x = 0 := fun x hx hxB => by
    rw [lap_sub, h₁.1 x hx hxB, h₂.1 x hx hxB, sub_self]
  have hzero : ∀ x ∈ S, x ∈ B → (f₁ - f₂) x = 0 := fun x hx hxB => by
    rw [Pi.sub_apply, h₁.2 x hx hxB, h₂.2 x hx hxB, sub_self]
  have hle := le_of_harmonic G hconn hout hnb hharm (M := 0) fun x hx hxB => (hzero x hx hxB).le
  have hge := ge_of_harmonic G hconn hout hnb hharm (m := 0) fun x hx hxB => (hzero x hx hxB).ge
  intro x hx
  have h1 := hle x hx
  have h2 := hge x hx
  simp only [Pi.sub_apply] at h1 h2
  linarith

/-! ### Existence: the walk solution -/

/-- The walk solution `x ↦ E_x[g(X_{τ_B})] = ∑_{b ∈ B} g(b) P_x(X_{τ_B} = b)` (`τ_B` the hitting time of `B`). -/
def dirichletSol (B : Finset V) (g : V → ℝ) (x : V) : ℝ :=
  ∑ b ∈ B, g b * (hitDist G (B : Set V) x {b}).toReal

/-- The walk solution is discrete harmonic off `B`. -/
theorem lap_dirichletSol (B : Finset V) (g : V → ℝ) {x : V} (hx : x ∉ B) :
    lap G (dirichletSol G B g) x = 0 := by
  have h := lap_sum_mul G B g (fun b y => (hitDist G (B : Set V) y {b}).toReal) x
  have hfun : (fun y => ∑ b ∈ B, g b * (hitDist G (B : Set V) y {b}).toReal) = dirichletSol G B g := rfl
  rw [hfun] at h
  rw [h]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [lap_hitDist G (I := (B : Set V)) (by exact_mod_cast hx) {b}, mul_zero]

/-- The walk solution equals `g` on `B`. -/
theorem dirichletSol_of_mem (B : Finset V) (g : V → ℝ) {x : V} (hx : x ∈ B) :
    dirichletSol G B g x = g x := by
  unfold dirichletSol
  rw [Finset.sum_eq_single x]
  · rw [hitDist_of_mem G (I := (B : Set V)) (by exact_mod_cast hx),
      Set.indicator_of_mem (Set.mem_singleton x), Pi.one_apply, ENNReal.toReal_one, mul_one]
  · intro b _ hbx
    rw [hitDist_of_mem G (I := (B : Set V)) (by exact_mod_cast hx),
      Set.indicator_of_notMem (fun h => hbx (Set.mem_singleton_iff.mp h).symm), ENNReal.toReal_zero,
      mul_zero]
  · intro h
    exact absurd hx h

/-- **Existence**: the walk solution solves the Dirichlet problem (for any `S`; no connectivity is needed). -/
theorem isDirichletSolution_dirichletSol (S B : Finset V) (g : V → ℝ) :
    IsDirichletSolution G S B g (dirichletSol G B g) :=
  ⟨fun _ _ hxB => lap_dirichletSol G B g hxB, fun _ _ hxB => dirichletSol_of_mem G B g hxB⟩

/-- **Existence and uniqueness** of the solution of the Dirichlet problem on `S`. -/
theorem existsUnique_dirichlet {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) (g : V → ℝ) :
    ∃ f : V → ℝ, IsDirichletSolution G S B g f ∧
      ∀ f' : V → ℝ, IsDirichletSolution G S B g f' → ∀ x ∈ S, f' x = f x :=
  ⟨dirichletSol G B g, isDirichletSolution_dirichletSol G S B g,
    fun _ hf' => eqOn_of_isDirichletSolution G hconn hout hnb hf' (isDirichletSolution_dirichletSol G S B g)⟩

/-! ### The walk representation -/

/-- `X_{τ_B}`: the vertex of the walk at its first visit to `B` (a junk value if `B` is never visited; this happens
with probability zero in every use below). -/
def hitVertex (B : Set V) (ω : ℕ → G.State) : V :=
  G.vertexPath ω (hitTime B (G.vertexPath ω)).toNat

/-- Along a step path started in `S` that avoids `B` before time `m ≤ n`, every vertex up to time `m` lies in `S`. -/
theorem mem_of_isStepPath {S B : Finset V} (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S)
    {n : ℕ} {X : ℕ → V} (hX : IsStepPath G n X) (h0 : X 0 ∈ S) {m : ℕ} (hmn : m ≤ n)
    (havoid : ∀ j < m, X j ∉ B) : ∀ j ≤ m, X j ∈ S := by
  intro j hj
  induction j with
  | zero => exact h0
  | succ j ih =>
    have hjS := ih (by omega)
    have hjB := havoid j (by omega)
    rcases hX j (by omega) with h | h
    · rw [h]; exact hjS
    · obtain ⟨d, hd1, hd2⟩ := exists_dart_of_adj G h
      rw [← hd2]
      exact hnb _ hjS hjB d ((mem_outDarts G).mpr hd1)

/-- **The walk from `S` hits `B` almost surely.** -/
theorem walkLaw_hitTime_eq_one {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) {x : V} (hx : x ∈ S) :
    G.walkLaw x {ω | hitTime (B : Set V) (G.vertexPath ω) ≠ ⊤} = 1 := by
  refine walkLaw_hitTime_ne_top_of_exit G hconn (U := (S : Set V)) S.finite_toSet ?_ ?_
  · intro y _
    obtain ⟨w, hw⟩ := hout
    exact ⟨w, by exact_mod_cast hw, hconn.preconnected y w⟩
  · intro n X h0 hX hn
    by_contra hcon
    push Not at hcon
    have hmem := mem_of_isStepPath G hnb hX (h0 ▸ hx) le_rfl
      (fun j hj => by exact_mod_cast hcon j hj.le) n le_rfl
    exact hn (by exact_mod_cast hmem)

/-- **Almost surely the walk from `S` hits `B`, and its first visit to `B` lies in `S ∩ B`.** -/
theorem ae_hitVertex_mem {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) {x : V} (hx : x ∈ S) :
    ∀ᵐ ω ∂G.walkLaw x, hitTime (B : Set V) (G.vertexPath ω) ≠ ⊤ ∧
      hitVertex G B ω ∈ S ∧ hitVertex G B ω ∈ B := by
  have h1 : ∀ᵐ ω ∂G.walkLaw x, hitTime (B : Set V) (G.vertexPath ω) ≠ ⊤ := by
    rw [ae_iff_measure_eq (Harmonic.measurableSet_hitTime_ne_top G (B : Set V)).nullMeasurableSet,
      measure_univ]
    exact walkLaw_hitTime_eq_one G hconn hout hnb hx
  filter_upwards [h1, ae_isStepPath G hconn x] with ω hT ⟨h0, hstep⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hT
  have hmem := hitTime_eq_coe_iff.mp hn.symm
  have hX : hitVertex G B ω = G.vertexPath ω n := by
    unfold hitVertex
    rw [← hn]
    rfl
  refine ⟨hT, ?_, ?_⟩
  · rw [hX]
    refine mem_of_isStepPath G hnb (hstep n)
      (by change G.stateVertex (ω 0) ∈ S; rw [h0]; exact hx) le_rfl
      (fun j hj => by exact_mod_cast hmem.2 j hj) n le_rfl
  · rw [hX]
    exact_mod_cast hmem.1

/-- The event `{τ_B < ⊤, X_{τ_B} = b}`, whose probability is `hitDist G B x {b}`. -/
theorem measurableSet_hitVertex_eq (B : Set V) (b : V) :
    MeasurableSet {ω : ℕ → G.State | hitTime B (G.vertexPath ω) ≠ ⊤ ∧
      G.vertexPath ω (hitTime B (G.vertexPath ω)).toNat ∈ ({b} : Set V)} :=
  measurableSet_hitEvent (G.stateVertex ⁻¹' B) (G.stateVertex ⁻¹' {b})

/-- **Expectation of a function of the first visit**: for `x ∈ S`,
`E_x[F(X_{τ_B})] = ∑_{b ∈ B} F(b) P_x(X_{τ_B} = b)`. -/
theorem integral_hitVertex {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) {x : V} (hx : x ∈ S) (F : V → ℝ) :
    ∫ ω, F (hitVertex G B ω) ∂G.walkLaw x = ∑ b ∈ B, F b * (hitDist G (B : Set V) x {b}).toReal := by
  set Ev : V → Set (ℕ → G.State) := fun b => {ω | hitTime (B : Set V) (G.vertexPath ω) ≠ ⊤ ∧
      G.vertexPath ω (hitTime (B : Set V) (G.vertexPath ω)).toNat ∈ ({b} : Set V)} with hEv
  have hmeas : ∀ b, MeasurableSet (Ev b) := fun b => measurableSet_hitVertex_eq G (B : Set V) b
  have hae : (fun ω => F (hitVertex G B ω)) =ᵐ[G.walkLaw x]
      fun ω => ∑ b ∈ B, F b * (Ev b).indicator 1 ω := by
    filter_upwards [ae_hitVertex_mem G hconn hout hnb hx] with ω ⟨hT, _, hB⟩
    have hiff : ∀ b, ω ∈ Ev b ↔ hitVertex G B ω = b := fun b => by
      simp only [hEv, Set.mem_ofPred_eq, Set.mem_singleton_iff, hitVertex]
      exact ⟨fun h => h.2, fun h => ⟨hT, h⟩⟩
    rw [Finset.sum_eq_single (hitVertex G B ω)]
    · rw [Set.indicator_of_mem ((hiff _).mpr rfl), Pi.one_apply, mul_one]
    · intro b _ hb
      rw [Set.indicator_of_notMem (fun h => hb ((hiff b).mp h).symm), mul_zero]
    · intro h
      exact absurd hB h
  rw [integral_congr_ae hae, integral_finsetSum]
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_indicator_one (hmeas b), measureReal_def]
    rfl
  · intro b _
    exact ((integrable_const (1 : ℝ)).indicator (hmeas b)).const_mul (F b)

/-- The walk solution at `x ∈ S` is `E_x[g(X_{τ_B})]`. -/
theorem dirichletSol_eq_integral {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) (g : V → ℝ) {x : V} (hx : x ∈ S) :
    dirichletSol G B g x = ∫ ω, g (hitVertex G B ω) ∂G.walkLaw x :=
  (integral_hitVertex G hconn hout hnb hx g).symm

/-- **Walk representation** `f(x) = E_x[f(X_{τ_B})]` for every solution `f` and `x ∈ S`. -/
theorem eq_integral_of_isDirichletSolution {S B : Finset V} (hconn : G.adj.Connected) (hout : ∃ w, w ∉ S)
    (hnb : ∀ x ∈ S, x ∉ B → ∀ d ∈ G.outDarts x, G.dtgt d ∈ S) {g f : V → ℝ}
    (hf : IsDirichletSolution G S B g f) {x : V} (hx : x ∈ S) :
    f x = ∫ ω, f (hitVertex G B ω) ∂G.walkLaw x := by
  rw [eqOn_of_isDirichletSolution G hconn hout hnb hf (isDirichletSolution_dirichletSol G S B g) x hx,
    dirichletSol_eq_integral G hconn hout hnb g hx]
  refine integral_congr_ae ?_
  filter_upwards [ae_hitVertex_mem G hconn hout hnb hx] with ω ⟨_, hS, hB⟩
  exact (hf.2 _ hS hB).symm

/-! ### The cell layer: `G^ε(D)` -/

section Cells

variable {G} {o : V} (H : CellularEmbedding G o)

/-- `V(G(∂D))`: the vertices whose cells meet `∂D = frontier D`, as a finset (`GMS3.vFin`). -/
abbrev vBd (D : Set ℂ) : Finset V := vFin H (frontier D)

theorem isBounded_frontier {D : Set ℂ} (hD : Bornology.IsBounded D) : Bornology.IsBounded (frontier D) :=
  hD.closure.subset frontier_subset_closure

theorem mem_vBd {D : Set ℂ} (hD : Bornology.IsBounded D) {x : V} :
    x ∈ vBd H D ↔ (H.cell x ∩ frontier D).Nonempty :=
  mem_vFin H (isBounded_frontier hD)

/-- For bounded `D`, `V(G(∂D))` as a set is the frozen `verticesMeeting H.cell (frontier D)` (for `V(G(D))` itself
this is `GMS3.coe_vFin`). -/
theorem coe_vBd {D : Set ℂ} (hD : Bornology.IsBounded D) :
    (vBd H D : Set V) = verticesMeeting H.cell (frontier D) :=
  GMS3.coe_vFin (isBounded_frontier hD)

/-- **Interior vertices have all their neighbours in `V(G(D))`** ([18], DB1 §3.8): a cell meeting the open
set `D` but not `∂D` lies in `D`, and adjacent cells intersect. -/
theorem dtgt_mem_vFin_of_interior {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D) {x : V}
    (hx : x ∈ vFin H D) (hxB : x ∉ vBd H D) : ∀ d ∈ G.outDarts x, G.dtgt d ∈ vFin H D := by
  intro d hd
  have hfr : H.cell x ∩ frontier D = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    exact fun h => hxB ((mem_vBd H hDb).mpr h)
  exact dtgt_mem_vFin_of_subset H hDb
    (cell_subset_of_inter_frontier_eq_empty H hDo ((mem_vFin H hDb).mp hx) hfr) hx hd

/-- **Interior vertices have all their graph neighbours in `V(G(D))`** (adjacency form). -/
theorem mem_vFin_of_adj_of_interior {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D) {x y : V}
    (hx : x ∈ vFin H D) (hxB : x ∉ vBd H D) (hxy : G.adj.Adj x y) : y ∈ vFin H D := by
  have hfr : H.cell x ∩ frontier D = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    exact fun h => hxB ((mem_vBd H hDb).mpr h)
  exact mem_vFin_of_adj_of_subset H hDb
    (cell_subset_of_inter_frontier_eq_empty H hDo ((mem_vFin H hDb).mp hx) hfr) hxy

/-- Some vertex lies outside `V(G(D))` (a cellular embedding has infinitely many vertices). -/
theorem exists_notMem_vFin (D : Set ℂ) : ∃ w, w ∉ vFin H D := by
  have := infinite_vertex H
  obtain ⟨w, hw⟩ := (vFin H D).finite_toSet.infinite_compl.nonempty
  exact ⟨w, by simpa using hw⟩

/-- **[18] (1.6), the discrete Dirichlet problem on `G(D)`**: `f` is discrete harmonic on
`V(G(D)) \ V(G(∂D))` and equals `g` on `V(G(D)) ∩ V(G(∂D))`. -/
def IsCellDirichletSolution (D : Set ℂ) (g f : V → ℝ) : Prop :=
  IsDirichletSolution G (vFin H D) (vBd H D) g f

/-- **The function `f_ε` of [18] (1.6) exists and is unique** on `V(G(D))`, for every bounded open `D`, every
boundary data `g` and every cellular embedding of a connected locally finite multigraph. -/
theorem existsUnique_cellDirichlet (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) (g : V → ℝ) :
    ∃ f : V → ℝ, IsCellDirichletSolution H D g f ∧
      ∀ f' : V → ℝ, IsCellDirichletSolution H D g f' → ∀ x ∈ vFin H D, f' x = f x :=
  existsUnique_dirichlet G hconn (exists_notMem_vFin H D)
    (fun _ hx hxB => dtgt_mem_vFin_of_interior H hDo hDb hx hxB) g

/-- The walk solution solves the cell Dirichlet problem (for every `D`). -/
theorem isCellDirichletSolution_dirichletSol (D : Set ℂ) (g : V → ℝ) :
    IsCellDirichletSolution H D g (dirichletSol G (vBd H D) g) :=
  isDirichletSolution_dirichletSol G _ _ g

/-- Uniqueness on `V(G(D))`. -/
theorem cellDirichlet_eqOn (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {g f₁ f₂ : V → ℝ} (h₁ : IsCellDirichletSolution H D g f₁)
    (h₂ : IsCellDirichletSolution H D g f₂) : ∀ x ∈ vFin H D, f₁ x = f₂ x :=
  eqOn_of_isDirichletSolution G hconn (exists_notMem_vFin H D)
    (fun _ hx hxB => dtgt_mem_vFin_of_interior H hDo hDb hx hxB) h₁ h₂

/-- **The walk from `V(G(D))` hits `V(G(∂D))` almost surely.** -/
theorem cellDirichlet_walkLaw_hitTime_eq_one (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {x : V} (hx : x ∈ vFin H D) :
    G.walkLaw x {ω | hitTime (verticesMeeting H.cell (frontier D)) (G.vertexPath ω) ≠ ⊤} = 1 := by
  rw [← coe_vBd H hDb]
  exact walkLaw_hitTime_eq_one G hconn (exists_notMem_vFin H D)
    (fun _ hx hxB => dtgt_mem_vFin_of_interior H hDo hDb hx hxB) hx

/-- Almost surely the walk from `x ∈ V(G(D))` first hits `V(G(∂D))` inside `V(G(D)) ∩ V(G(∂D))`. -/
theorem cellDirichlet_ae_hitVertex_mem (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {x : V} (hx : x ∈ vFin H D) :
    ∀ᵐ ω ∂G.walkLaw x, hitTime (verticesMeeting H.cell (frontier D)) (G.vertexPath ω) ≠ ⊤ ∧
      hitVertex G (verticesMeeting H.cell (frontier D)) ω ∈ vFin H D ∧
      hitVertex G (verticesMeeting H.cell (frontier D)) ω ∈ vBd H D := by
  rw [← coe_vBd H hDb]
  exact ae_hitVertex_mem G hconn (exists_notMem_vFin H D)
    (fun _ hx hxB => dtgt_mem_vFin_of_interior H hDo hDb hx hxB) hx

/-- **Walk representation of `f_ε`** ([18] (1.6)): `f(x) = E_x[f(X_τ)]`, `τ` the hitting time of `V(G(∂D))`, for
every solution `f` and every `x ∈ V(G(D))`. -/
theorem cellDirichlet_eq_integral (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {g f : V → ℝ} (hf : IsCellDirichletSolution H D g f) {x : V}
    (hx : x ∈ vFin H D) :
    f x = ∫ ω, f (hitVertex G (verticesMeeting H.cell (frontier D)) ω) ∂G.walkLaw x := by
  rw [← coe_vBd H hDb]
  exact eq_integral_of_isDirichletSolution G hconn (exists_notMem_vFin H D)
    (fun _ hx hxB => dtgt_mem_vFin_of_interior H hDo hDb hx hxB) hf hx

/-- `f(x) = E_x[g(X_τ)]` for every solution `f` with boundary data `g` and every `x ∈ V(G(D))`. -/
theorem cellDirichlet_eq_integral_data (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {g f : V → ℝ} (hf : IsCellDirichletSolution H D g f) {x : V}
    (hx : x ∈ vFin H D) :
    f x = ∫ ω, g (hitVertex G (verticesMeeting H.cell (frontier D)) ω) ∂G.walkLaw x := by
  rw [cellDirichlet_eq_integral H hconn hDo hDb hf hx]
  refine integral_congr_ae ?_
  filter_upwards [cellDirichlet_ae_hitVertex_mem H hconn hDo hDb hx] with ω ⟨_, hS, hB⟩
  exact hf.2 _ hS hB

/-- **Maximum principle for `f_ε`**: if the boundary data are at most `M` on `V(G(D)) ∩ V(G(∂D))`, then `f ≤ M` on
`V(G(D))`. -/
theorem cellDirichlet_le (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {g f : V → ℝ} (hf : IsCellDirichletSolution H D g f) {M : ℝ}
    (hM : ∀ x ∈ vFin H D, x ∈ vBd H D → g x ≤ M) : ∀ x ∈ vFin H D, f x ≤ M :=
  le_of_harmonic G hconn (exists_notMem_vFin H D)
    (fun _ hx hxB => dtgt_mem_vFin_of_interior H hDo hDb hx hxB) hf.1
    (fun x hx hxB => (hf.2 x hx hxB).symm ▸ hM x hx hxB)

/-- **Minimum principle for `f_ε`**. -/
theorem cellDirichlet_ge (hconn : G.adj.Connected) {D : Set ℂ} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {g f : V → ℝ} (hf : IsCellDirichletSolution H D g f) {m : ℝ}
    (hm : ∀ x ∈ vFin H D, x ∈ vBd H D → m ≤ g x) : ∀ x ∈ vFin H D, m ≤ f x :=
  ge_of_harmonic G hconn (exists_notMem_vFin H D)
    (fun _ hx hxB => dtgt_mem_vFin_of_interior H hDo hDb hx hxB) hf.1
    (fun x hx hxB => (hf.2 x hx hxB).symm ▸ hm x hx hxB)

/-! ### The boundary values (1.6) -/

/-- **The boundary values of [18] (1.6)**: `sup_{z ∈ H_x ∩ ∂D} f(z)`. It is attained when `f` is
continuous on `∂D` and `H_x` meets `∂D` (`exists_bdryVal_eq`); its other values are never used. -/
def bdryVal (D : Set ℂ) (f : ℂ → ℝ) (x : V) : ℝ := sSup (f '' (H.cell x ∩ frontier D))

theorem isCompact_cell_inter_frontier (D : Set ℂ) (x : V) : IsCompact (H.cell x ∩ frontier D) :=
  (H.isCompact_cell x).inter_right isClosed_frontier

/-- For `f` continuous on `∂D` and `H_x ∩ ∂D ≠ ∅`, the supremum (1.6) is attained and bounds `f` on `H_x ∩ ∂D`. -/
theorem exists_bdryVal_eq {D : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f (frontier D)) {x : V}
    (hx : (H.cell x ∩ frontier D).Nonempty) :
    ∃ z ∈ H.cell x ∩ frontier D, bdryVal H D f x = f z ∧ ∀ w ∈ H.cell x ∩ frontier D, f w ≤ f z := by
  have hK := isCompact_cell_inter_frontier H D x
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hx (hf.mono Set.inter_subset_right)
  refine ⟨z, hz, ?_, fun w hw => hmax hw⟩
  have hgreat : IsGreatest (f '' (H.cell x ∩ frontier D)) (f z) :=
    ⟨Set.mem_image_of_mem f hz, by rintro _ ⟨w, hw, rfl⟩; exact hmax hw⟩
  exact hgreat.csSup_eq

end Cells

end MatedCRTHarmonic.GMSMain.T16D
