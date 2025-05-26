import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Digraph.Condensation
import Mathlib.Combinatorics.Digraph.TopologicalSort

/-!
  src/Paralogic/DependencyGraphs.lean

  Directed dependency graphs, strongly connected components, condensation, and topological sort.
-/


namespace Paralogic.DependencyGraphs

variable {V : Type _}

/-- A directed graph on a vertex type V. -/
structure Graph where
  /-- adjacency relation -/
  adj : V → V → Prop

/-- Convert to Mathlib's Digraph. -/
def toDigraph (G : Graph) : Digraph V where
  Adj := G.adj

/-- Reachability as the reflexive-transitive closure of `adj`. -/
def reachable (G : Graph) : V → V → Prop :=
  Relation.ReflTransGen G.adj

/-- Two vertices are strongly connected if each is reachable from the other. -/
def stronglyConnected (G : Graph) (v w : V) : Prop :=
  reachable G v w ∧ reachable G w v

/-- Strong connectivity is an equivalence relation. -/
theorem stronglyConnected_equiv (G : Graph) : Equivalence (stronglyConnected G) :=
  by refine ⟨fun v => ⟨.refl, .refl⟩, fun _ _ h => h.symm, fun _ _ _ h1 h2 => ⟨Relation.ReflTransGen.trans h1.1 h2.1, Relation.ReflTransGen.trans h2.2 h1.2⟩⟩

/-- The type of strongly connected components (SCCs) of G. -/
def Scc (G : Graph) : Type _ := Quotient (stronglyConnected_equiv G)

namespace Scc

/-- Canonical map sending a vertex to its SCC. -/
def mk (G : Graph) (v : V) : Scc G := Quot.mk _ v

@[simp]
theorem mk_eq_mk {G : Graph} {v w : V} : mk G v = mk G w ↔ stronglyConnected G v w :=
  Quotient.eq _ _

end Scc

/-- The condensation graph of G, as a DAG of its SCCs. -/
def condGraph (G : Graph) : Digraph (Scc G) :=
  (toDigraph G).condensation

/-- The condensation graph is acyclic. -/
theorem condGraph_acyclic (G : Graph) : (condGraph G).isAcyclic :=
  (toDigraph G).condensation_acyclic

/-- A topological ordering of the SCCs of G. -/
def topoSort (G : Graph) : List (Scc G) :=
  (condGraph G).topologicalSort

/-- In the topological order, edges go forward. -/
theorem topoSort_ordered (G : Graph) :
  ∀ C D, ((condGraph G).Adj C D) → (topoSort G).indexOf? C < (topoSort G).indexOf? D :=
  (condGraph G).topologicalSort_spec

end Paralogic.DependencyGraphs