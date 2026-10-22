import HigherDimLQGContinuity.Labels.MeshScale
import HigherDimLQGMetric.Routing.Lemma41MeshFamily

/-!
# Fixed site data and its geometric pieces

The data are chosen before the tolerance `v`. The graph is a spanning tree of
the buffered annulus mesh. All edge centres, reserved boxes, ports and seed
shells are derived from it, with no independent geometric assumptions.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- Fixed seed reference and conversion constants of Part B, (F6). -/
structure SiteSeedData where
  H₀ : ℝ
  σ₀ : ℝ
  β₀ : ℝ
  m : ℝ
  M : ℝ
  Hsd : ℝ
  σsd : ℝ
  Kpin : ℝ
  Λ : ℝ
  HE : ℝ
  sE : ℝ
  A : ℝ
  α : ℝ
  β : ℝ
  ℓ₀ : ℝ
  ℓ₁ : ℝ
  d₀ : ℝ
  H₀_ge : 1 ≤ H₀
  σ₀_pos : 0 < σ₀
  σ₀_lt : σ₀ < 1
  β₀_gt : 1 < β₀
  m_pos : 0 < m
  m_lt_M : m < M
  Hsd_ge : 1 ≤ Hsd
  σsd_pos : 0 < σsd
  σsd_le : σsd ≤ 1
  Λ_ge : 1 ≤ Λ
  HE_ge : 1 ≤ HE
  sE_pos : 0 < sE
  sE_le : sE ≤ 1
  A_ge : 1 ≤ A
  α_pos : 0 < α
  α_le : α ≤ 1
  β_pos : 0 < β
  β_le : β ≤ 1
  ℓ₀_pos : 0 < ℓ₀
  ℓ₀_le_ℓ₁ : ℓ₀ ≤ ℓ₁
  d₀_pos : 0 < d₀

/-- Fixed site reference constants, a buffered dyadic mesh and tree, the
concentric trial count, and the seed conversion constants (F1)–(F6). -/
structure SiteData (d : ℕ) where
  Hup : ℝ
  s : ℝ
  Hlo : ℝ
  b : ℝ
  mc : ℝ
  A0 : ℝ
  Hup_ge : 1 ≤ Hup
  s_pos : 0 < s
  s_le : s ≤ 1
  Hlo_ge : 1 ≤ Hlo
  b_ge : 1 ≤ b
  mc_pos : 0 < mc
  A0_ge : Hlo⁻¹ ≤ A0
  mesh : SiteMeshData d Hup s (siteEps0 mc Hlo)
  Ntr : ℕ
  seed : SiteSeedData

/-- Construct the fixed site geometry for supplied reference and seed
constants. The seed constants themselves are supplied by the seed packet. -/
theorem exists_siteData {d : ℕ} (hd : 2 ≤ d)
    (Hup s Hlo b mc A0 : ℝ) (hHup : 1 ≤ Hup) (hs : 0 < s)
    (hs1 : s ≤ 1) (hHlo : 1 ≤ Hlo) (hb : 1 ≤ b) (hmc : 0 < mc)
    (hA0 : Hlo⁻¹ ≤ A0) (Ntr : ℕ) (seed : SiteSeedData) :
    ∃ S : SiteData d,
      S.Hup = Hup ∧ S.s = s ∧ S.Hlo = Hlo ∧ S.b = b ∧
      S.mc = mc ∧ S.A0 = A0 ∧ S.Ntr = Ntr ∧ S.seed = seed := by
  have hHloPos : 0 < Hlo := lt_of_lt_of_le (by norm_num) hHlo
  have hε : 0 < siteEps0 mc Hlo := by
    unfold siteEps0 siteBtrig siteAout
    have hinv : 0 < Hlo⁻¹ := inv_pos.mpr hHloPos
    positivity
  obtain ⟨mesh⟩ := exists_siteMeshData hd Hup s (siteEps0 mc Hlo) hs hε
  refine ⟨{
    Hup := Hup
    s := s
    Hlo := Hlo
    b := b
    mc := mc
    A0 := A0
    Hup_ge := hHup
    s_pos := hs
    s_le := hs1
    Hlo_ge := hHlo
    b_ge := hb
    mc_pos := hmc
    A0_ge := hA0
    mesh := mesh
    Ntr := Ntr
    seed := seed
  }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The site mesh vertices. -/
abbrev SiteData.Vertex {d : ℕ} (S : SiteData d) :=
  HigherDimLQGMetric.Topology.meshVertices S.mesh.δm (siteMeshRing d S.mesh.δm)

/-- The edges of the selected spanning tree. -/
abbrev SiteData.Edge {d : ℕ} (S : SiteData d) := S.mesh.tree.edgeSet

/-- The point in `ℝ^d` represented by a mesh vertex. -/
def SiteData.vertexPoint {d : ℕ} (S : SiteData d) (v : S.Vertex) : Rd d :=
  HigherDimLQGMetric.Topology.latticePoint S.mesh.δm v.1

/-- The two endpoints of an unoriented tree edge in the canonical `Sym2.out`
orientation. -/
def SiteData.edgeLeft {d : ℕ} (S : SiteData d) (e : S.Edge) : S.Vertex :=
  HigherDimLQGMetric.lemma41_meshLeft e

def SiteData.edgeRight {d : ℕ} (S : SiteData d) (e : S.Edge) : S.Vertex :=
  HigherDimLQGMetric.lemma41_meshRight e

/-- Midpoint of the associated lattice edge. -/
def SiteData.edgeCenter {d : ℕ} (S : SiteData d) (e : S.Edge) : Rd d :=
  midpoint ℝ (S.vertexPoint (S.edgeLeft e)) (S.vertexPoint (S.edgeRight e))

/-- Half-side of each reserved box. -/
def SiteData.boxHalfSide {d : ℕ} (S : SiteData d) : ℝ :=
  S.mesh.δm / (64 * d)

/-- Oriented unit direction of a tree edge. -/
def SiteData.edgeUnit {d : ℕ} (S : SiteData d) (e : S.Edge) : Rd d :=
  S.mesh.δm⁻¹ • (S.vertexPoint (S.edgeRight e) - S.vertexPoint (S.edgeLeft e))

/-- Closed coordinate box of half-side `L` around an edge midpoint. -/
def SiteData.box {d : ℕ} (S : SiteData d) (e : S.Edge) : Set (Rd d) :=
  {x | ∀ i, |x i - (S.edgeCenter e) i| ≤ S.boxHalfSide}

/-- The two ports on the box faces. -/
def SiteData.port {d : ℕ} (S : SiteData d) (e : S.Edge) (i : Fin 2) : Rd d :=
  if i = 0 then S.edgeCenter e - S.boxHalfSide • S.edgeUnit e
  else S.edgeCenter e + S.boxHalfSide • S.edgeUnit e

/-- The two retained outer segments of an edge after deleting its middle. -/
def SiteData.retained {d : ℕ} (S : SiteData d) (e : S.Edge) (i : Fin 2) : Set (Rd d) :=
  if i = 0 then segment ℝ (S.vertexPoint (S.edgeLeft e)) (S.port e 0)
  else segment ℝ (S.port e 1) (S.vertexPoint (S.edgeRight e))

/-- Trial radius for a one-based concentric seed index. -/
def SiteData.seedRadius {d : ℕ} (S : SiteData d) (j : Fin S.Ntr) : ℝ :=
  S.boxHalfSide / 4 * 8 ^ (-(j.val + 1 : ℝ))

/-- Smallest radius in the fixed trial family. -/
def SiteData.seedMin {d : ℕ} (S : SiteData d) : ℝ :=
  S.boxHalfSide / 4 * 8 ^ (-(S.Ntr : ℝ))

/-- Concentric inspection annulus of a trial. -/
def SiteData.seedA {d : ℕ} (S : SiteData d) (e : S.Edge)
    (j : Fin S.Ntr) : Set (Rd d) :=
  (fun x : Rd d => S.edgeCenter e + S.seedRadius j • x) '' siteA d

/-- Concentric compact seed shell of a trial. -/
def SiteData.seedK {d : ℕ} (S : SiteData d) (e : S.Edge)
    (j : Fin S.Ntr) : Set (Rd d) :=
  (fun x : Rd d => S.edgeCenter e + S.seedRadius j • x) '' annK d

end HigherDimLQGContinuity
