/-
Episode graph API for Phase 8.2 of `TODO.md`.

This file starts the production Lean formalization of the episode graph.
The current Mathlib checkout does not provide a directed `SimpleDigraph`
API suitable for this project, so the graph is represented by a local
directed edge relation, as recorded in `EPISODE_INVENTORY.md`.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-11.
-/

import Mathlib.Data.Finset.Basic
import CollatzShadowing.EpisodeInventory

namespace CollatzShadowing

/-!
## Episode nodes

The paper-level episode node has three natural-number coordinates:

* `k`: phantom/exponent level,
* `c`: class or component index,
* `b`: shadowing-depth/lift index.

The unbounded `EpisodeNode` is the mathematical node type. Finite
certificate work uses `TruncatedEpisodeNode K C B`, whose coordinates
are bounded by `Fin`.
-/

/-- Paper-level episode-graph node `(k, c, b)`. -/
structure EpisodeNode where
  k : ℕ
  c : ℕ
  b : ℕ
deriving DecidableEq, Repr

/-- Bounded episode nodes for a finite cutoff box. -/
abbrev TruncatedEpisodeNode (K C B : ℕ) :=
  Fin K × Fin C × Fin B

namespace EpisodeNode

/-- Embed a bounded node into the unbounded paper-level node type. -/
def ofTruncated {K C B : ℕ} (u : TruncatedEpisodeNode K C B) : EpisodeNode :=
  { k := u.1.val, c := u.2.1.val, b := u.2.2.val }

/-- The coordinate triple associated to an episode node. -/
def toTriple (u : EpisodeNode) : ℕ × ℕ × ℕ :=
  (u.k, u.c, u.b)

@[simp] theorem toTriple_mk (k c b : ℕ) :
    toTriple ({ k := k, c := c, b := b } : EpisodeNode) = (k, c, b) :=
  rfl

@[simp] theorem ofTruncated_k {K C B : ℕ} (u : TruncatedEpisodeNode K C B) :
    (ofTruncated u).k = u.1.val :=
  rfl

@[simp] theorem ofTruncated_c {K C B : ℕ} (u : TruncatedEpisodeNode K C B) :
    (ofTruncated u).c = u.2.1.val :=
  rfl

@[simp] theorem ofTruncated_b {K C B : ℕ} (u : TruncatedEpisodeNode K C B) :
    (ofTruncated u).b = u.2.2.val :=
  rfl

end EpisodeNode

instance (K C B : ℕ) : Fintype (TruncatedEpisodeNode K C B) := inferInstance
instance (K C B : ℕ) : DecidableEq (TruncatedEpisodeNode K C B) := inferInstance

/-!
## Directed graph relation

The episode graph is a directed relation on `EpisodeNode`. A finite
truncation is represented by an edge relation on bounded nodes. This is
deliberately simple: SCCs are mutual reachability, and later phases can
add concrete edge generation or certificate import without changing the
foundational graph notion.
-/

/-- A directed episode graph on the unbounded node type. -/
structure EpisodeGraph where
  edge : EpisodeRel EpisodeNode

namespace EpisodeGraph

/-- Reachability in an episode graph. -/
def reachable (G : EpisodeGraph) (u v : EpisodeNode) : Prop :=
  Reachable G.edge u v

/-- Strong-component relation in an episode graph. -/
def sameSCC (G : EpisodeGraph) (u v : EpisodeNode) : Prop :=
  SameSCC G.edge u v

/-- The empty episode graph. Useful as a typechecking baseline. -/
def empty : EpisodeGraph where
  edge := fun _ _ => False

example (u : EpisodeNode) : empty.reachable u u :=
  Relation.ReflTransGen.refl

end EpisodeGraph

/-- A finite directed episode graph inside a cutoff box. -/
structure TruncatedEpisodeGraph (K C B : ℕ) where
  edge : EpisodeRel (TruncatedEpisodeNode K C B)
  edge_decidable : DecidableRel edge

namespace TruncatedEpisodeGraph

instance {K C B : ℕ} (G : TruncatedEpisodeGraph K C B) :
    DecidableRel G.edge :=
  G.edge_decidable

/-- Reachability inside a finite cutoff graph. -/
def reachable {K C B : ℕ}
    (G : TruncatedEpisodeGraph K C B)
    (u v : TruncatedEpisodeNode K C B) : Prop :=
  Reachable G.edge u v

/-- Strong-component relation inside a finite cutoff graph. -/
def sameSCC {K C B : ℕ}
    (G : TruncatedEpisodeGraph K C B)
    (u v : TruncatedEpisodeNode K C B) : Prop :=
  SameSCC G.edge u v

/-- Enumerate directed edges in a finite cutoff graph. -/
def edgeFinset {K C B : ℕ} (G : TruncatedEpisodeGraph K C B) :
    Finset (TruncatedEpisodeNode K C B × TruncatedEpisodeNode K C B) :=
  Finset.univ.filter fun uv => G.edge uv.1 uv.2

/-- Empty finite cutoff graph. -/
def empty (K C B : ℕ) : TruncatedEpisodeGraph K C B where
  edge := fun _ _ => False
  edge_decidable := by
    intro _ _
    infer_instance

example {K C B : ℕ} (u : TruncatedEpisodeNode K C B) :
    (empty K C B).reachable u u :=
  Relation.ReflTransGen.refl

example : Fintype (TruncatedEpisodeNode 17 8 4) := inferInstance

example : (empty 17 8 4).edgeFinset = ∅ := by
  ext uv
  simp [edgeFinset, empty]

/-!
## Finite SCC certificates

The theorem-level notion of an SCC is mutual reachability. For finite
paper certificates, it is useful to package the component as a `Finset`
of bounded nodes plus the reachability facts needed by later operator
construction.
-/

/-- A certified strongly connected component inside a finite cutoff graph. -/
structure SCC {K C B : ℕ} (G : TruncatedEpisodeGraph K C B) where
  nodes : Finset (TruncatedEpisodeNode K C B)
  nonempty : nodes.Nonempty
  stronglyConnected :
    ∀ ⦃u⦄, u ∈ nodes → ∀ ⦃v⦄, v ∈ nodes → G.sameSCC u v

/-- Any singleton is a strongly connected component candidate by reflexivity. -/
def singletonSCC {K C B : ℕ}
    (G : TruncatedEpisodeGraph K C B)
    (u : TruncatedEpisodeNode K C B) : SCC G where
  nodes := {u}
  nonempty := by
    exact ⟨u, by simp⟩
  stronglyConnected := by
    intro x hx y hy
    have hx' : x = u := by simpa using hx
    have hy' : y = u := by simpa using hy
    subst x
    subst y
    exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- A finite directed walk, encoded as its successive vertices. -/
def Walk {K C B : ℕ}
    (G : TruncatedEpisodeGraph K C B)
    (u v : TruncatedEpisodeNode K C B) : List (TruncatedEpisodeNode K C B) → Prop
  | [] => u = v
  | x :: xs => G.edge u x ∧ Walk G x v xs

/-- Convert a checked finite walk into reachability. -/
theorem reachable_of_walk {K C B : ℕ}
    {G : TruncatedEpisodeGraph K C B}
    {u v : TruncatedEpisodeNode K C B} :
    ∀ {xs : List (TruncatedEpisodeNode K C B)}, Walk G u v xs → G.reachable u v
  | [], h => by
      subst h
      exact Relation.ReflTransGen.refl
  | x :: xs, h => by
      exact Relation.ReflTransGen.head h.1 (reachable_of_walk h.2)

/--
A hub-style SCC import certificate. For every node in `nodes`, the
certificate supplies a walk from the hub to the node and a walk back to
the hub. This is compact enough to generate from an external SCC run
and strong enough to imply mutual reachability for all listed nodes.
-/
structure HubSCCCertificate {K C B : ℕ} (G : TruncatedEpisodeGraph K C B) where
  hub : TruncatedEpisodeNode K C B
  nodes : Finset (TruncatedEpisodeNode K C B)
  hub_mem : hub ∈ nodes
  fromHub :
    ∀ ⦃u⦄, u ∈ nodes → ∃ walk : List (TruncatedEpisodeNode K C B), Walk G hub u walk
  toHub :
    ∀ ⦃u⦄, u ∈ nodes → ∃ walk : List (TruncatedEpisodeNode K C B), Walk G u hub walk

/-- A hub certificate yields an `SCC` certificate. -/
def HubSCCCertificate.toSCC {K C B : ℕ}
    {G : TruncatedEpisodeGraph K C B}
    (cert : HubSCCCertificate G) : SCC G where
  nodes := cert.nodes
  nonempty := ⟨cert.hub, cert.hub_mem⟩
  stronglyConnected := by
    intro u hu v hv
    obtain ⟨uToHub, huToHub⟩ := cert.toHub hu
    obtain ⟨hubToV, hhubToV⟩ := cert.fromHub hv
    obtain ⟨vToHub, hvToHub⟩ := cert.toHub hv
    obtain ⟨hubToU, hhubToU⟩ := cert.fromHub hu
    exact
      ⟨(reachable_of_walk huToHub).trans (reachable_of_walk hhubToV),
        (reachable_of_walk hvToHub).trans (reachable_of_walk hhubToU)⟩

/--
A placeholder shape for the paper's critical SCC certificate: a chosen
critical node, a certified finite SCC, and membership of the critical
node in that SCC.
-/
structure CriticalSCCCertificate {K C B : ℕ}
    (G : TruncatedEpisodeGraph K C B) where
  critical : TruncatedEpisodeNode K C B
  component : SCC G
  critical_mem : critical ∈ component.nodes

/-- Baseline critical-SCC certificate for a singleton component. -/
def singletonCriticalCertificate {K C B : ℕ}
    (G : TruncatedEpisodeGraph K C B)
    (u : TruncatedEpisodeNode K C B) : CriticalSCCCertificate G where
  critical := u
  component := singletonSCC G u
  critical_mem := by
    simp [singletonSCC]

end TruncatedEpisodeGraph

end CollatzShadowing
