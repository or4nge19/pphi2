# Formulation layer: open questions

Discussion of design questions raised by the formulation-layer interfaces in
`Common/QFT/Euclidean/`. Each section states the question, then proposes how
the current design should respond.

## 0. Separating spacetime from field content

### Question

The most fundamental issue with the current `Formulation` structure is that it
conflates spacetime and field content. A QFT is, at its core, about fields on a
spacetime: maps (or sections) from a spacetime manifold M to a target space X.
The spacetime M carries geometric structure (metric, symmetry group, causal
structure). The target X carries the field content (scalar, spinor, gauge,
valued in a Lie algebra, etc.). These are independent choices.

In the current design, `Formulation` has:

```lean
structure Formulation where
  SpaceTime : Type
  TestFunction : Type
  ComplexTestFunction : Type
  positiveTimeTestFunctions : Set TestFunction
```

Here `TestFunction` is a single opaque type that implicitly bundles together
the spacetime (what domain the test functions live on) and the field content
(what they are valued in). There is no way to express "the same field content
on a different spacetime" (e.g., a scalar field on a torus vs. on R^2) or "the
same spacetime with different field content" (e.g., a scalar vs. a spinor field
on R^2). Every combination requires a completely new `Formulation`.

The right mental model is:

- **Spacetime M**: a manifold, lattice, or other geometric object with a
  symmetry group. In the sigma model picture, this is the source.
- **Target X**: the space the fields are valued in. For a real scalar field,
  X = R. For N scalar fields, X = R^N. For a gauge field, X is a Lie-algebra-
  valued 1-form bundle. For a nonlinear sigma model, X is a Riemannian
  manifold. In the sigma model picture, this is the target.
- **Field configurations**: maps (or sections) M -> X, with appropriate
  regularity. The space of field configurations is Gamma(M, X) or Maps(M, X).
- **Test functions**: depend on both M and X. For a scalar field, a test
  function is f : M -> R (same as the field). For a spinor field, a test
  function is a spinor-valued function on M. The test function space is
  determined by the pairing with field configurations: the observable
  phi(f) = integral_M phi(x) f(x) dvol requires f to live in the dual of the
  field space.

This separation is essential for:

1. **Regularization.** The same field content (e.g., P(phi)_2 with a given
   polynomial) should be expressible on different spacetimes (lattice, torus,
   cylinder, plane) without redefining the theory. The formulation layer should
   let you change M while keeping X fixed.
2. **Comparison.** Two theories on the same spacetime with different field
   content (scalar vs. gauge) should share the spacetime infrastructure.
3. **Functoriality.** In the Atiyah-Segal framework, a QFT is a functor from
   a cobordism category (whose objects are (d-1)-manifolds and morphisms are
   d-cobordisms) to a linear category. This requires spacetime to be a
   variable, not baked into the formulation.
4. **Generality.** Nonlinear sigma models, gauge theories, and string theory
   worldsheet models are all "maps from M to X" theories. A formulation layer
   that cannot express this separation will need ad hoc workarounds for each.

### Response

The `Formulation` structure should be refactored to separate spacetime from
field content:

```lean
structure Formulation where
  SpaceTime : Type uSpace
  FieldTarget : Type uTarget      -- what the fields are valued in
  SymmetryGroup : Type uGroup
  instGroup : Group SymmetryGroup
  -- derived types (could be computed from M and X, but kept explicit
  -- since the construction depends on regularity choices):
  TestFunction : Type uTest
  ComplexTestFunction : Type uComplex
  FieldConfig : Type uConfig
  -- the evaluation pairing, connecting fields to test functions:
  pairing : FieldConfig → TestFunction → ℝ
```

Here `TestFunction`, `ComplexTestFunction`, and `FieldConfig` are derived from
the choices of `SpaceTime` and `FieldTarget` together with regularity
decisions (Schwartz vs. smooth vs. L^2, distributional vs. continuous, etc.),
but are kept as explicit fields because the derivation is theory-dependent.
The `FieldTarget` field makes the M-vs-X separation visible in the type.

For the current P(Phi)_2 theory:

```lean
def pphi2Formulation : Formulation where
  SpaceTime := EuclideanSpace ℝ (Fin 2)   -- M = R^2
  FieldTarget := ℝ                         -- X = R (real scalar field)
  SymmetryGroup := E2
  TestFunction := SchwartzMap SpaceTime2 ℝ
  ComplexTestFunction := SchwartzMap SpaceTime2 ℂ
  FieldConfig := Configuration (ContinuumTestFunction 2)  -- S'(R^2)
  pairing := distribPairing
```

For the same theory on a lattice:

```lean
def pphi2LatticeFormulation (N : ℕ) : Formulation where
  SpaceTime := ZMod N × ZMod N             -- M = Z^2_N
  FieldTarget := ℝ                         -- X = R (same field content)
  SymmetryGroup := ...                     -- discrete translations + reflections
  TestFunction := FinLatticeField 2 N
  ...
```

The shared `FieldTarget := ℝ` makes explicit that these are the same theory on
different spacetimes. A continuum limit theorem would then be a statement about
a family of formulations parametrized by the lattice spacing, with fixed
`FieldTarget`.

**Note:** The pairing `FieldConfig → TestFunction → ℝ` is moved into
`Formulation` from `PairingMeasureModel`. This is appropriate because the
pairing depends on the spacetime and field content, not on the choice of
measure. A given formulation may support multiple measures (free, interacting,
different couplings) that all use the same pairing.

## 1. General manifolds and lattices

### Question

Beyond the M-vs-X separation (section 0), the current `Formulation` has
`positiveTimeTestFunctions : Set TestFunction`, which implicitly assumes a
distinguished time direction. On compact manifolds (a torus, a sphere, a
lattice with periodic boundary conditions), there is no canonical positive-time
half-space: every time direction wraps around, and there is no global notion of
"future."

We want the formulation layer to cover not just flat R^d but also compact
Riemannian manifolds and finite lattices, since these are the intermediate
objects in any constructive approach (finite-volume regularization on a torus,
lattice regularization on Z^d_N, etc.). Beyond constructive QFT, many
applications in mathematics and string theory use curved manifolds, manifolds
with boundary, orbifolds, and other geometries where there is no global
flat-space structure.

A related gap: `Formulation` has `SpaceTime` as a bare `Type` with no
geometric structure. There is no symmetry group, no group action on test
functions, no metric. But Euclidean covariance (OS2) is a core axiom, and
different theories have different symmetry groups: E(d) for flat R^d, the
isometry group Isom(M,g) for a curved Riemannian manifold, Spin(d) (the double
cover of SO(d)) when fermions are present, the discrete symmetry group of a
lattice, or the super-Euclidean group for SUSY theories. The formulation layer
should have a place to record this.

### Response

There are two issues: the forced time direction and the missing symmetry group.

**Symmetry group.** `Formulation` should carry the spacetime symmetry group and
its action on test functions. A natural design:

```lean
structure Formulation where
  SpaceTime : Type uSpace
  TestFunction : Type uTest
  ComplexTestFunction : Type uComplex
  SymmetryGroup : Type uGroup
  instGroup : Group SymmetryGroup
  action : SymmetryGroup → TestFunction → TestFunction
  -- action is a group homomorphism into automorphisms of TestFunction
```

For flat R^2 this is `SymmetryGroup := E2` (the Euclidean group), for a lattice
`SymmetryGroup` is a finite group, for a torus it is the translation group
`R^d / L*Z^d` times the point group. OS2 (Euclidean covariance) then becomes
a statement about the generating functional being invariant under this action,
stated once in terms of the abstract `SymmetryGroup` rather than specialized
to each theory.

If the symmetry group acts on spacetime (not just on test functions), we should
also record the spacetime action and require compatibility:

```lean
  spaceTimeAction : SymmetryGroup → SpaceTime → SpaceTime
  action_compatible : ∀ g f x, (action g f) x = f (spaceTimeAction g⁻¹ x)
```

This is the standard pullback formula. For gauge symmetries that act on
internal indices but not on spacetime, `spaceTimeAction` would be trivial.

**Positive-time test functions.** The right fix is to make these optional or
conditional rather than a required field. Concretely:

**Option A: Make it a `Set TestFunction` that can be empty.** A compact torus
formulation sets `positiveTimeTestFunctions := ∅`. This is the minimal change
to the current code.  Downstream definitions like `OS3_ReflectionPositivity`
that quantify over positive-time test functions become vacuously true (or are
guarded by a nonemptiness hypothesis). This is honest: reflection positivity on
a compact torus is not the standard OS3 but a different property (it holds for
the full torus measure, but the passage to the Hilbert space is different).

**Option B: Factor out a `ReflectionStructure`.** Define a separate mixin:

```lean
structure ReflectionStructure (F : Formulation) where
  timeReflection : F.SpaceTime → F.SpaceTime
  timeReflection_involution : ∀ p, timeReflection (timeReflection p) = p
  positiveTimeTestFunctions : Set F.TestFunction
  -- pullback of timeReflection acts on test functions, etc.
```

and make `Formulation` carry only `SpaceTime`, `TestFunction`,
`ComplexTestFunction`. A theory on a compact manifold provides a `Formulation`
without a `ReflectionStructure`; a theory on R^d provides both.

Option B is cleaner but a larger refactor. Either way, the key principle is:
**`Formulation` should not force every theory to have a time direction.**

For lattices specifically, `SpaceTime` can be `Fin N × Fin N` (or `ZMod N`),
and `TestFunction` can be `FinLatticeField d N` or similar. Nothing in the
current definitions prevents this.  The lattice theories in `Pphi2` already use
these types internally; what is missing is only the adapter that packages them
as a `Formulation`.

## 2. Test functions, observables, and multiple fields

### Question

In the current design, `TestFunction` plays double duty: it is both the space
of Schwartz test functions on spacetime and (via the evaluation pairing
`ω(f)`) the space of linear observables. For a single real scalar field, these
coincide: smearing phi against f in S(R^d) gives a real-valued observable.

But for multiple fields, gauge fields, or fermions, the observable algebra is
richer. A gauge theory has gauge-invariant observables (Wilson loops, gauge-
invariant local operators) that are not smearings of a single field. A theory
with N scalar fields has observables that smear each field independently. A
fermionic theory has Grassmann-valued fields whose observables are fermionic
bilinears.

Is the formulation layer designed only for single scalar fields?

### Response

No, but it needs to be read correctly. The `TestFunction` in `Formulation` is
not "Schwartz test functions on spacetime." It is whatever type parametrizes the
linear observables of the theory. The `pairing` in `PairingMeasureModel` is
`FieldConfig → F.TestFunction → ℝ`, which means: a field configuration
assigns a real number to each "test function." The name `TestFunction` is
inherited from the scalar case, but structurally it is the **index type for
linear observables**.

For specific generalizations:

**N scalar fields.** `TestFunction` could be `Fin N → S(R^d)` (a tuple of
Schwartz functions, one per field), and the pairing evaluates
`⟨ω, (f_1, ..., f_N)⟩ = Σ_i ∫ φ_i(x) f_i(x) dx`. Or equivalently,
`TestFunction` could be `S(R^d, R^N)` — vector-valued Schwartz functions.

**Gauge fields.** The natural linear observables are smeared gauge-covariant
operators, not the gauge field A_μ itself (which is not gauge-invariant). For
the formulation layer, `TestFunction` would index the gauge-invariant
observables, and `FieldConfig` would be the gauge-orbit space (or a suitable
quotient). Alternatively, one works with a fixed gauge and treats the
gauge-invariant sector as a subspace.

**Fermions.** Fermionic fields are Grassmann-valued and do not fit into a
real-valued pairing. The natural observables are fermionic bilinears (which are
bosonic). After integrating out fermions, the effective theory has:
- bosonic observables (the original scalar field smearings),
- induced observables from fermionic bilinears (expectations of
  `ψ̄(x)Γψ(y)` become functions of the bosonic background).

The `PairingMeasureModel` layer can handle the bosonic sector of such a theory.
To handle the full graded structure natively, the formulation layer would need
a Z_2-graded extension: `TestFunction` split into even (bosonic) and odd
(fermionic) subspaces, and the pairing valued in a Grassmann algebra rather
than R. This is a genuine extension, not a minor tweak.

**Recommendation:** Rename or document `TestFunction` as "the observable index
type" rather than suggesting it must be a function space on spacetime. The
current structures are already general enough for multi-field bosonic theories.
For fermionic theories, a graded extension (`GradedFormulation`?) is needed and
should be designed when the first concrete fermionic example is formalized.

## 3. SchwingerFormulation vs GeneratingFunctionalModel

### Question

Is `SchwingerFormulation` really so different from `GeneratingFunctionalModel`?
The Schwinger functions S_n(f_1, ..., f_n) are the moments of the generating
functional Z[f]:

  S_n(f_1, ..., f_n) = (-i)^n (δ^n/δf_1 ... δf_n) Z[f] |_{f=0}

So a `TensorSchwingerModel` is just the Taylor coefficients of a
`GeneratingFunctionalModel`, and a `DistributionalSchwingerModel` is the same
data promoted to continuous multilinear functionals. Why have separate
structures?

### Response

The mathematical relationship is correct: moments determine and are determined
by the generating functional (under mild growth/regularity conditions). But the
Lean structures serve different purposes and should stay separate. Here is why:

**1. The moment-generating-functional correspondence is nontrivial
mathematics.** Recovering Z[f] from {S_n} requires summability of the moment
series. Recovering {S_n} from Z[f] requires sufficient differentiability. These
are genuine theorems, not definitional equalities. The formulation layer should
not hide them.

**2. The structures carry different data.** A `GeneratingFunctionalModel` is a
single function `TestFunction → ℂ`. A `TensorSchwingerModel` is a family of
functions indexed by arity n. A `DistributionalSchwingerModel` has n-point test
function spaces, linear maps, and continuity proofs. These are structurally
different Lean types even when they encode equivalent mathematical information.

**3. Some theories are more naturally presented at one level than another.**
A lattice gauge theory might have a well-defined generating functional (the
Wilson action gives Z[J] directly) but its Schwinger functions (gauge-invariant
correlation functions) require a nontrivial construction (gauge fixing, Faddeev-
Popov, or working with Wilson loops). Conversely, a conformal field theory
might be defined by its correlation functions (conformal blocks) without an
explicit generating functional.

**4. `SchwingerFormulation` is not a model structure.** It is a richer version
of `Formulation` that adds linear/topological infrastructure. The relationship
is:

```
Formulation                  -- bare types, no algebra
SchwingerFormulation         -- adds algebra + topology on test functions
GeneratingFunctionalModel F  -- data: a function Z : TestFunction → ℂ
TensorSchwingerModel F       -- data: a family S_n : (Fin n → TestFunction) → ℂ
DistributionalSchwingerModel F  -- data: continuous linear S_n on n-point spaces
```

`SchwingerFormulation` is infrastructure (what types and instances are
available); the models are data (what functions are defined on those types).
They are in different categories.

That said, the naming is confusing: `SchwingerFormulation` sounds like it should
contain Schwinger functions, but it does not — it just provides the topological
machinery needed to *define* distributional Schwinger functions. A renaming
to something like `TopologicalFormulation` or `AnalyticFormulation` might
reduce confusion.

## 4. Worked example: the 2D Wess-Zumino model

### Question

How would the N=1 Wess-Zumino model in 2D (a supersymmetric theory with a
scalar field and a Dirac fermion) look as a worked example? This is the
simplest physically interesting theory beyond scalar P(Phi)_2 and is a good
stress test for the formulation layer.

### Background

The 2D Wess-Zumino model has:

- **Fields:** A real scalar φ and a Dirac fermion ψ, coupled through a
  superpotential W(φ). For the simplest case W(φ) = ½mφ² + (g/3)φ³, the
  bosonic potential is the perfect square ½(W'(φ))² = ½(mφ + gφ²)².

- **Euclidean action:**
  S[φ,ψ] = ∫ [½(∂φ)² + ½(W'(φ))² + ψ̄(∂̸ + W''(φ))ψ] d²x

- **Functional integral:** After integrating out the fermion (Grassmann
  integration), the bosonic effective measure is
  dν(φ) ∝ exp(-½∫(W'(φ))²) · det(∂̸ + W''(φ)) · dμ_GFF(φ).
  The fermion determinant is real but not necessarily positive. This is a
  **signed measure**, not a probability measure.

- **Observables:** Bosonic smearings φ(f), fermionic bilinears like ψ̄ψ(g),
  and SUSY-invariant composites. After fermion integration, the purely bosonic
  Schwinger functions are well-defined. Mixed boson-fermion correlators involve
  the fermion propagator (∂̸ + W''(φ))^{-1} in the φ-background.

- **Rigorous status:** Partially constructed in finite volume on a cylinder by
  Jaffe-Lesniewski-Weitsman (1988). The infinite-volume limit is not fully
  rigorous.

### How it fits the formulation layer

**What works as-is:**

The bosonic sector after fermion integration can be described, with
modifications, using the existing structures:

```lean
def wzFormulation : Formulation where
  SpaceTime := EuclideanSpace ℝ (Fin 2)
  TestFunction := SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ  -- smears the scalar field
  ComplexTestFunction := SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ
  positiveTimeTestFunctions := positiveTimeSubmodule2.carrier
```

A `GeneratingFunctionalModel` can record the bosonic generating functional
Z_bos[J] = ∫ exp(⟨J,φ⟩) dν_eff(φ), and a `TensorSchwingerModel` can record
the bosonic Schwinger functions. These are well-defined even with a signed
measure — the generating functional is still a function TestFunction → ℂ, and
the Schwinger functions are still distributions.

**What breaks:**

1. **No `PairingMeasureModel`.** The effective bosonic measure is signed
   (because det(∂̸ + W''(φ)) can be negative), so `isProbability` fails.
   The theory lives at the `GeneratingFunctionalModel` /
   `TensorSchwingerModel` level, not the `MeasureModel` level.

   This is the key architectural validation: the formulation layer correctly
   distinguishes "has a positive measure" (P(Phi)_2) from "has Schwinger
   functions" (Wess-Zumino bosonic sector). The hierarchy exists precisely
   for cases like this.

2. **Fermionic observables are invisible.** The bosonic `TestFunction` smears
   only φ. The fermionic bilinears ψ̄Γψ are additional observables with their
   own test functions (spinor-valued Schwartz functions). To represent them,
   one would need either:
   - a second `TestFunction` type for fermionic observables, or
   - a Z_2-graded `TestFunction = TestFunction_bos ⊕ TestFunction_ferm`
     with graded pairing.

3. **Schwinger functions need Z_2-grading.** The full Schwinger functions
   include mixed boson-fermion correlators that are antisymmetric in their
   fermionic arguments. A `TensorSchwingerModel` with its single `schwinger`
   function on tuples of test functions cannot express this — it would need
   to be a graded family:
   - S_{n,m}(f_1,...,f_n; g_1,...,g_m) with n bosonic and m fermionic
     insertions, antisymmetric in the g_i.

4. **OS3 needs a graded Hilbert space.** The reconstructed Hilbert space is
   H = H_bos ⊕ H_ferm, and reflection positivity must be formulated on this
   Z_2-graded space. The current `OS3_ReflectionPositivity` works only in the
   ungraded (purely bosonic) setting.

5. **Euclidean covariance becomes Spin(2) covariance.** The fermion transforms
   under the double cover of SO(2). This is a minor extension of the symmetry
   group data.

**What the WZ example teaches about the formulation layer:**

| Layer | P(Phi)_2 | WZ bosonic sector | Full WZ |
|-------|----------|-------------------|---------|
| `Formulation` | yes | yes | needs graded TestFunction |
| `GeneratingFunctionalModel` | yes | yes | needs Grassmann sources |
| `TensorSchwingerModel` | yes | yes | needs graded S_{n,m} |
| `PairingMeasureModel` | yes | **no** (signed measure) | **no** |
| `MeasureModel` | yes | **no** | **no** |
| `DistributionalSchwingerModel` | future | future | needs graded n-point spaces |

The critical observation is that the WZ bosonic sector (after fermion
integration) fits naturally at the `GeneratingFunctionalModel` and
`TensorSchwingerModel` levels. This validates the design decision to have
these layers exist independently of `PairingMeasureModel`. The full WZ
theory with fermions requires a graded extension at every level.

### Concrete next steps if formalizing WZ

1. Instantiate `wzFormulation` and `wzGeneratingFunctionalModel` for the
   bosonic effective theory (scalar field with signed measure from the fermion
   determinant).
2. Define a `SignedMeasureModel` that parallels `PairingMeasureModel` but
   with a signed measure instead of a probability measure. The pairing and
   Schwinger functions still make sense.
3. Design `GradedFormulation` with `TestFunction_bos` and `TestFunction_ferm`
   for the full theory. The `TensorSchwingerModel` generalizes to a graded
   family `schwinger : (n m : ℕ) → (Fin n → TestFun_bos) →
   (Fin m → TestFun_ferm) → ℂ`.
4. Define graded reflection positivity. This requires the Z_2-graded Hilbert
   space formalism from Osterwalder-Schrader (1973, Helv. Phys. Acta).

### References

- Jaffe, Lesniewski, Weitsman, "The two-dimensional, N=2 Wess-Zumino model on
  a cylinder" (Commun. Math. Phys. 114, 1988). Closest to a rigorous
  construction.
- Nicolai, "On a new characterization of scalar supersymmetric theories"
  (Phys. Lett. B 89, 1980). The Nicolai map.
- Osterwalder, Schrader, "Euclidean Fermi fields and a Feynman-Kac formula"
  (Helv. Phys. Acta 46, 1973). OS axioms for fermions.

## 5. Complex and signed measures

### Question

Many Euclidean QFTs of physical interest have a complex Boltzmann weight
exp(-S) where the action S is not real-valued. Examples include:

- **Finite-density QCD.** At nonzero baryon chemical potential mu, the fermion
  determinant det(D + m + mu*gamma_0) is complex. This is the notorious "sign
  problem" that obstructs lattice Monte Carlo.
- **Theta-term theories.** Adding a topological term i*theta*Q (where Q is the
  topological charge) makes the action complex.
- **Chern-Simons theory.** The Euclidean action is purely imaginary.
- **Wess-Zumino after fermion integration.** The fermion determinant is real
  but can be negative, giving a signed (not positive) measure.

Does the formulation layer cover these theories?

### Response

The upper layers already handle them. The concrete measure layer does not,
but can be extended.

**What works as-is.** `GeneratingFunctionalModel`, `TensorSchwingerModel`, and
`DistributionalSchwingerModel` are all valued in C. They record the generating
functional and Schwinger functions without reference to how they were computed.
A theory with a complex action still has a well-defined generating functional
Z[f] (computed by integration against a complex weight) and well-defined
Schwinger functions S_n(f_1, ..., f_n). These structures can represent any of
the examples above.

**What breaks.** `PairingMeasureModel` requires `Measure FieldConfig` (a
positive measure from Mathlib's `MeasureTheory.Measure`) and
`IsProbabilityMeasure`. This excludes:
- signed measures (det(D + W''(phi)) < 0 for some configurations),
- complex measures (det(D + m + mu*gamma_0) not real).

`MeasureModel` inherits from `PairingMeasureModel` and has the same
restriction. The `MeasureToTensorBridge` uses `∫ ... ∂M.measure`, which is
Bochner integration against a positive measure.

**This is the correct default.** The sign problem is real: theories with
complex actions do not have a positive-measure formulation, and the formulation
layer correctly forces them to live at a weaker level
(`GeneratingFunctionalModel` or `TensorSchwingerModel`). The hierarchy exists
precisely so that "has a positive measure" is a provable property of specific
theories (like P(Phi)_2) rather than an implicit assumption on all QFTs.

**Extension for concrete signed/complex measure representations.** If we want
to also support measure-level descriptions for these theories (e.g., to state
and prove the signed/complex integral formulas, or to formalize the sign
problem itself), we would add:

```lean
-- Signed measure model (real but not necessarily positive)
structure SignedMeasureModel (F : Formulation) (FieldConfig : Type uConfig) where
  instMeasurableSpaceFieldConfig : MeasurableSpace FieldConfig
  signedMeasure : SignedMeasure FieldConfig
  pairing : FieldConfig → F.TestFunction → ℝ

-- Complex measure model (fully general)
structure ComplexMeasureModel (F : Formulation) (FieldConfig : Type uConfig) where
  instMeasurableSpaceFieldConfig : MeasurableSpace FieldConfig
  complexMeasure : ComplexMeasure FieldConfig
  pairing : FieldConfig → F.TestFunction → ℝ
```

Mathlib provides `MeasureTheory.SignedMeasure` and
`MeasureTheory.ComplexMeasure` with their own integration theories. The bridges
to `TensorSchwingerModel` would use these integration APIs.

The inheritance hierarchy for measure-level models would then be:

```
PairingMeasureModel   (positive probability measure)
        |
        | (totalVariation gives a positive measure;
        |  Radon-Nikodym gives a density)
        v
SignedMeasureModel    (real-valued signed measure)
        |
        | (real and imaginary parts)
        v
ComplexMeasureModel   (complex-valued measure)
```

Each level is strictly more general. A `PairingMeasureModel` can be embedded
into a `SignedMeasureModel` (the positive measure is a special case of a signed
measure), and a `SignedMeasureModel` into a `ComplexMeasureModel` (a real
signed measure is a special case of a complex measure). These embeddings should
be explicit coercions or bridge structures, not silent identifications.

**When to add this.** The extension is straightforward but should wait until
there is a concrete theory that needs it. The Wess-Zumino bosonic effective
theory (signed measure) is the most immediate candidate. Finite-density lattice
QCD (complex measure) is a more ambitious one. Adding the structures before
having a concrete use case risks designing the wrong API.
