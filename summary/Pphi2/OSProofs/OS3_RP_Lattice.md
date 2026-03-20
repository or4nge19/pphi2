# `OS3_RP_Lattice.lean` -- Informal Summary

> **Source**: [`Pphi2/OSProofs/OS3_RP_Lattice.lean`](../../Pphi2/OSProofs/OS3_RP_Lattice.lean)
>
> **Generated**: 2026-03-20

## Overview
Proves reflection positivity (OS3) for the interacting lattice measure via the transfer matrix decomposition. The action splits as $S[\phi] = S^+[\phi^+,\phi^0] + S^-[\phi^-,\phi^0]$ with $S^- = S^+ \circ \Theta$. The RP inequality follows from: block-zero structure of the precision matrix $Q$, Fubini decomposition, change of variables under time reflection, and the perfect square argument.

## Status
**Main result**: 1 private axiom (`gaussian_rp_cov_perfect_square`)
**Length**: 1477 lines, 12 definitions + 20 theorems + 1 axiom

---

### Key definitions
- **`siteEquiv`**: $\mathrm{ZMod}\,N \times \mathrm{ZMod}\,N \simeq \mathrm{Fin}\,2 \to \mathrm{Fin}\,N$.
- **`timeReflection2D`**: $\Theta(t,x) = (-t, x)$.
- **`fieldReflection2D`**: $(\Theta\phi)(t,x) = \phi(-t,x)$.
- **`PositiveTimeSupported`**: $F$ depends only on $\phi(t,x)$ with $0 < t < N/2$.
- **`BoundarySupported`**: $w$ depends only on boundary sites.
- **`positiveTimeInteraction` / `boundaryTimeInteraction` / `negativeTimeInteraction`**: Time-decomposition of the Wick interaction $V = V_+ + V_0 + V_-$.
- **`evalField2D`**, **`pairing2D`**, **`Fcos`**, **`Fsin`**: Helper definitions for the trig expansion.

### Key proved theorems
- **`action_decomposition`**: $S[\phi] = S_+(\phi) + S_+(\Theta\phi)$ (lattice action is symmetric under $\Theta$).
- **`massOperator_cross_block_zero`**: $Q_{xy} = 0$ for $x \in S_+$, $y \in \Theta(S_+)$ (nearest-neighbor structure).
- **`massOperatorMatrix_timeNeg_invariant`**: $Q(-x,-y) = Q(x,y)$.
- **`gaussian_density_rp`**: $\int G(\phi) G(\Theta\phi) w(\phi) \rho(\phi)\,d\phi \ge 0$ for positive-time-supported $G$ and boundary-supported $w \ge 0$.
- **`lattice_rp`**: $\int F(\phi) F(\Theta\phi)\,d\mu_a \ge 0$ for positive-time-supported $F$.
- **`lattice_rp_matrix`**: $\sum_{ij} c_i c_j \int \cos(\langle\phi, f_i - \Theta f_j\rangle)\,d\mu_a \ge 0$ (matrix form of RP).
- **`rp_from_transfer_positivity`**: $\langle f, T^n f\rangle \ge 0$ (operator-theoretic RP from transfer matrix positivity).

### Axiom
- **`gaussian_rp_cov_perfect_square`** (private): The second Fubini + COV + perfect square step for Gaussian RP. Encapsulates the change of variables under time reflection and the resulting square integral $\ge 0$.

---
*This file has **12** definitions and **20** theorems (0 with sorry) + **1** private axiom.*
