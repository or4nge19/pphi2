# `OS2_WardIdentity.lean` -- Informal Summary

> **Source**: [`Pphi2/OSProofs/OS2_WardIdentity.lean`](../../Pphi2/OSProofs/OS2_WardIdentity.lean)
>
> **Generated**: 2026-03-20

## Overview
Proves OS2 (Euclidean invariance) for the continuum limit measure. Translation invariance follows from exact lattice symmetry + weak limits. Rotation invariance uses a Ward identity argument: the rotation anomaly $O_{\mathrm{break}}$ has scaling dimension 4 > $d=2$, so its coefficient is $O(a^2 |\log a|^p)$ and vanishes in the limit. Combines OS0 (analyticity) and OS1 (regularity) from exponential moment axioms.

## Status
**Main result**: 5 axioms (`anomaly_bound_from_superrenormalizability`, `rotation_invariance_continuum`, `continuum_exponential_moments`, `analyticOn_generatingFunctionalC`, `exponential_moment_schwartz_bound`, `continuum_exponential_clustering`)
**Length**: 1493 lines, 5 definitions + 18 theorems + 6 axioms

---

### Key definitions
- **`latticeTranslation`**: $(T_v\phi)(x) = \phi(x-v)$ on the lattice.
- **`latticeRotation90`**: 90-degree rotation on the 2D lattice.
- **`so2Generator`**: $SO(2)$ infinitesimal generator $Jf = x_1\partial_2 f - x_2\partial_1 f$.

### Key proved theorems
- **`latticeAction_translation_invariant`**: $S_a[T_v\phi] = S_a[\phi]$ (relabeling).
- **`latticeMeasure_translation_invariant`**: $\int F(T_v\omega)\,d\mu_a = \int F(\omega)\,d\mu_a$. Proved via density bridge + change of variables.
- **`translation_invariance_continuum`**: $Z[\tau_v f] = Z[f]$ for all $v \in \mathbb{R}^2$. From lattice translation invariance + `tendsto_nhds_unique_of_eventuallyEq`.
- **`anomaly_scaling_dimension`**: $\dim(O_{\mathrm{break}}) = 4$. Proved via Taylor expansion of $1 - \cos(ak)$.
- **`anomaly_vanishes`**: Rotation anomaly is $O(a^2|\log a|^p)$. Delegates to axiom.
- **`os0_for_continuum_limit`**: OS0 (analyticity) from exponential moments + Hartogs.
- **`os1_for_continuum_limit`**: OS1 (regularity) $\|Z[J]\| \le \exp(c(\|J\|_1 + \|J\|_2^2))$.
- **`os2_for_continuum_limit`**: OS2 from translation + rotation invariance, extended to complex test functions via `complex_gf_invariant_of_real_gf_invariant`.
- **`os4_for_continuum_limit`**: OS4 from exponential clustering.
- **`continuumLimit_satisfies_fullOS`**: Assembles all five OS axioms.
- **`pphi2_exists`**: $\exists \mu$ satisfying `SatisfiesFullOS`.

### Axioms
- **`continuum_exponential_moments`**: Fernique + Nelson uniform exponential moments.
- **`analyticOn_generatingFunctionalC`**: Analyticity of $Z_{\mathbb{C}}$ from moments + Hartogs.
- **`exponential_moment_schwartz_bound`**: $\int e^{|\omega(g)|}\,d\mu \le e^{c(\|g\|_1+\|g\|_2^2)}$.
- **`anomaly_bound_from_superrenormalizability`**: $O(a^2|\log a|^p)$ bound from Glimm-Jaffe 19.3.1.
- **`rotation_invariance_continuum`**: Full $O(2)$ invariance in the continuum limit.
- **`continuum_exponential_clustering`**: Exponential clustering from uniform spectral gap.

---
*This file has **5** definitions and **18** theorems (0 with sorry) + **6** axioms.*
