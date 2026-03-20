# `Embedding.lean` — Informal Summary

> **Source**: [`Pphi2/ContinuumLimit/Embedding.lean`](../../Pphi2/ContinuumLimit/Embedding.lean)
>
> **Generated**: 2026-03-20

## Overview
Defines the lattice-to-continuum embedding $\iota_a : \text{FinLatticeField}(d,N) \to \mathcal{S}'(\mathbb{R}^d)$ that maps lattice field configurations to tempered distributions via a Riemann sum formula, and constructs the pushforward measures $\nu_a = (\iota_a)_* \mu_a$ on $\mathcal{S}'(\mathbb{R}^d)$. Also defines the marker predicate `IsPphi2Limit` characterizing $P(\varphi)_2$ continuum limit measures.

## Status
**Main result**: Fully proven (0 axioms, 0 sorries)
**Length**: 343 lines, 9 definitions + 6 theorems

---

### `ContinuumTestFunction (d : ℕ)`
```lean
abbrev ContinuumTestFunction := SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ
```
The Schwartz space $\mathcal{S}(\mathbb{R}^d)$ as the continuum test function space.

### `schwartzTranslate (v : EuclideanSpace ℝ (Fin d))`
```lean
noncomputable def schwartzTranslate (v : EuclideanSpace ℝ (Fin d)) :
    ContinuumTestFunction d →L[ℝ] ContinuumTestFunction d
```
Translation $(\tau_v f)(x) = f(x - v)$ as a CLM on $\mathcal{S}(\mathbb{R}^d)$.

### `physicalPosition (a : ℝ) (x : FinLatticeSites d N)`
```lean
def physicalPosition (a : ℝ) (x : FinLatticeSites d N) : EuclideanSpace ℝ (Fin d)
```
Physical position $a \cdot x \in \mathbb{R}^d$ of a lattice site $x \in (\mathbb{Z}/N\mathbb{Z})^d$.

### `evalAtSite (a : ℝ) (f : ContinuumTestFunction d) (x : FinLatticeSites d N)`
```lean
def evalAtSite (a : ℝ) (f : ContinuumTestFunction d) (x : FinLatticeSites d N) : ℝ
```
Evaluates $f(a \cdot x)$.

### `latticeEmbedEval (a : ℝ) (φ : FinLatticeField d N) (f : ContinuumTestFunction d)`
```lean
def latticeEmbedEval (a : ℝ) (φ : FinLatticeField d N) (f : ContinuumTestFunction d) : ℝ
```
The evaluation formula $(\iota_a \varphi)(f) = a^d \sum_{x \in \Lambda} \varphi(x) f(a \cdot x)$.

### `latticeEmbedEval_linear_phi`
The embedding is bilinear: $\iota_a(c_1\varphi_1 + c_2\varphi_2)(f) = c_1 \iota_a(\varphi_1)(f) + c_2 \iota_a(\varphi_2)(f)$. **Proved** by expanding the sum and factoring.

### `latticeEmbedEval_linear_f`
The embedding is linear in $f$: $\iota_a(\varphi)(c_1 f_1 + c_2 f_2) = c_1 \iota_a(\varphi)(f_1) + c_2 \iota_a(\varphi)(f_2)$. **Proved** by linearity of Schwartz evaluation.

### `latticeEmbed (a : ℝ) (ha : 0 < a) (φ : FinLatticeField d N)`
```lean
def latticeEmbed (a : ℝ) (ha : 0 < a) (φ : FinLatticeField d N) :
    Configuration (ContinuumTestFunction d)
```
Full embedding as a CLM from lattice fields to $\mathcal{S}'(\mathbb{R}^d)$, constructed via `SchwartzMap.mkCLMtoNormedSpace`.

### `latticeEmbed_eval`
Agreement: $(\texttt{latticeEmbed}\ \varphi)(f) = \texttt{latticeEmbedEval}\ \varphi\ f$. **Proved** by `rfl`.

### `latticeEmbed_measurable`
The embedding is measurable (each evaluation $\varphi \mapsto (\iota_a \varphi)(f)$ is continuous on the finite-dimensional space). **Proved**.

### `latticeEmbedLift (a : ℝ) (ha : 0 < a) (ω : Configuration (FinLatticeField d N))`
```lean
def latticeEmbedLift (a : ℝ) (ha : 0 < a)
    (ω : Configuration (FinLatticeField d N)) : Configuration (ContinuumTestFunction d)
```
Lifts the embedding to configuration space: extracts field values $\omega(\delta_x)$ and applies the lattice embedding.

### `latticeEmbedLift_measurable`
The lifted embedding is measurable. **Proved**.

### `continuumMeasure (P : InteractionPolynomial) (a mass : ℝ) ...`
```lean
def continuumMeasure (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : Measure (Configuration (ContinuumTestFunction d))
```
Pushforward measure $\nu_a = (\tilde{\iota}_a)_* \mu_a$ on $\mathcal{S}'(\mathbb{R}^d)$.

### `continuumMeasure_isProbability`
The pushforward is a probability measure. **Proved** from `interactingLatticeMeasure_isProbability`.

### `IsPphi2Limit`
```lean
def IsPphi2Limit {d : ℕ}
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    (_P : InteractionPolynomial) (_mass : ℝ) : Prop
```
Marker predicate: $\mu$ is a $P(\varphi)_2$ continuum limit if there exist lattice spacings $a_k \to 0$ and measures $\nu_k$ with convergent Schwinger functions, $\mathbb{Z}_2$ symmetry, characteristic functional convergence, and lattice translation invariance.

---
*This file has **9** definitions and **6** theorems/lemmas (0 with sorry).*
