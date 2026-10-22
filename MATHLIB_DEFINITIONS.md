# Mathlib definitions used in Challenge.lean

Verbatim excerpts of the Mathlib definitions used by the statements in `Challenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib.

## SimpleGraph

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 95:

```lean
/-- A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
-/
@[ext, aesop safe constructors (rule_sets := [SimpleGraph]), wikidata Q141488]
structure SimpleGraph (V : Type u) where
  /-- The adjacency relation of a simple graph. -/
  Adj : V → V → Prop
  symm : Std.Symm Adj := by aesop_graph
  loopless : Std.Irrefl Adj := by aesop_graph
```

## SimpleGraph.edgeSetEmbedding

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 477:

```lean
def edgeSetEmbedding (V : Type*) : SimpleGraph V ↪o Set (Sym2 V) :=
  OrderEmbedding.ofMapLEIff (fun G => Sym2.fromRel G.symm) fun _ _ =>
    ⟨fun h a b => @h s(a, b), fun h e => Sym2.ind @h e⟩
```

## SimpleGraph.edgeSet

`Mathlib/Combinatorics/SimpleGraph/Basic.lean`, line 483:

```lean
/-- `G.edgeSet` is the edge set for `G`.
This is an abbreviation for `edgeSetEmbedding G` that permits dot notation. -/
abbrev edgeSet (G : SimpleGraph V) : Set (Sym2 V) := edgeSetEmbedding V G
```

## SimpleGraph.comap

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 126:

```lean
/-- Given a function, there is a contravariant induced map on graphs by pulling back the
adjacency relation.
This is one of the ways of creating induced graphs. See `SimpleGraph.induce` for a wrapper.

This is surjective when `f` is injective (see `SimpleGraph.comap_surjective`). -/
protected def comap (f : V → W) (G : SimpleGraph W) : SimpleGraph V where
  Adj u v := G.Adj (f u) (f v)
  symm.symm _ _ h := h.symm
```

## SimpleGraph.induce

`Mathlib/Combinatorics/SimpleGraph/Maps.lean`, line 227:

```lean
/-- Restrict a graph to the vertices in the set `s`, deleting all edges incident to vertices
outside the set. This is a wrapper around `SimpleGraph.comap`. -/
abbrev induce (s : Set V) (G : SimpleGraph V) : SimpleGraph s :=
  G.comap (Function.Embedding.subtype _)
```

## Function.Embedding.subtype

`Mathlib/Logic/Embedding/Basic.lean`, line 232:

```lean
/-- Embedding of a `Subtype`. -/
def subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨Subtype.val, fun _ _ => Subtype.ext⟩
```

## SimpleGraph.Reachable

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 52:

```lean
/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
```

## SimpleGraph.Preconnected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 228:

```lean
/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v
```

## SimpleGraph.Connected

`Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean`, line 314:

```lean
/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]
```

## SimpleGraph.Walk

`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`, line 54:

```lean
/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
```

## Set.encard

`Mathlib/Data/Set/Card.lean`, line 67:

```lean
/-- The cardinality of a set as a term in `ℕ∞` -/
noncomputable def encard (s : Set α) : ℕ∞ := ENat.card s
```

## Set.ncard

`Mathlib/Data/Set/Card.lean`, line 613:

```lean
/-- The cardinality of `s : Set α` . Has the junk value `0` if `s` is infinite -/
noncomputable def ncard (s : Set α) : ℕ := ENat.toNat s.encard
```

## Finset.card

`Mathlib/Data/Finset/Card.lean`, line 47:

```lean
/-- `s.card` is the number of elements of `s`, aka its cardinality.

The notation `#s` can be accessed in the `Finset` locale. -/
def card (s : Finset α) : ℕ :=
  Multiset.card s.1
```

## Fintype.card

`Mathlib/Data/Fintype/Card.lean`, line 40:

```lean
/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card
```
