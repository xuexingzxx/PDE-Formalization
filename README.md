# MyProject

A Lean 4 formalization of **Lawrence C. Evans' *Partial Differential Equations*** (2nd ed.),
covering the four fundamental linear PDEs of Chapter 2:

1. **Transport equation** — `u_t + b · Du = 0`
2. **Laplace's / Poisson's equation** — `−Δu = f`
3. **Heat equation** — `u_t − Δu = 0`
4. **Wave equation** — `u_tt − Δu = 0`

and the analytic foundations of **Sobolev spaces** (Chapter 5): weak derivatives and `W^{1,p}`.

Built with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Status

| Chapter | File | Status | Notes |
|---|---|---|---|
| §2.1 Transport | `Transport.lean` | ✅ **complete, zero `sorry`** | homogeneous IVP solved **and proved unique**; inhomogeneous Duhamel formula **provably solves the IVP** (Leibniz rule + spatial differentiation under the integral both proved) |
| §2.2 Laplace/Poisson | `Laplace.lean` | partial | fundamental solution, radial-power & `log` Laplacians, Green's identity (algebraic step) proved; mean-value, maximum principle and the Poisson representation are blocked by Mathlib gaps |
| §2.3 Heat | `Heat.lean` | ✅ **complete, zero `sorry`** | heat kernel is positive, has unit mass, and solves the heat equation; for **bounded continuous** `g`, the convolution `∫ Φ(x−y,t) g(y) dy` **provably solves the IVP** — both the time-derivative and the spatial-Laplacian are moved under the integral (n-dim Gaussian moments + nested differentiation under the integral) |
| §2.4 Wave | `Wave.lean` | ✅ **complete, zero `sorry`** | traveling waves, d'Alembert (existence + `C²` regularity + initial conditions), energy conservation, uniqueness, finite propagation speed |
| §5.2 Sobolev | `Sobolev.lean` | ✅ **foundations, zero `sorry`** | test functions `C_c^∞(U)`, weak directional derivatives, the classical⟹weak bridge (integration by parts), linearity, a.e. uniqueness (fundamental lemma of the calculus of variations), `W^{1,p}` membership, and `C_c^∞ ⊆ W^{1,p}` |

`Calculus.lean` provides shared spacetime calculus utilities (`spatialGradient`,
`timeDerivative`, `spatialLaplacian`, and a Leibniz-rule helper).

The project builds cleanly against Mathlib (`lake build`); the remaining `sorry`s are isolated
and documented at their use sites.

## Known blockers (missing Mathlib infrastructure)

The outstanding `sorry`s are all in **Laplace**, and are **not** gaps in the mathematics but
in available Mathlib lemmas:

- **Stokes' theorem on spherical domains** (Laplace `green_identity_annulus` Step 2,
  `green_boundary_tendsto_f`) — Mathlib's divergence theorem covers boxes only.
- **Sphere surface measure** `σ(∂B(0,ε)) = n ωₙ εⁿ⁻¹` (Laplace `fundamentalSolution_totalFlux`).
- **`n`-dimensional polar coordinates** (Laplace integrability of `‖Φ‖` near `0`); Mathlib has
  only the `ℝ²` case.

The **Heat** chapter's spatial-Laplacian-under-the-integral step required navigating a
genuine Mathlib instance gap — `ContinuousENorm` (hence `Integrable`/`integral_apply`) is
missing for iterated CLM spaces `ℝⁿ →L (ℝⁿ→Lℝ)` (a topology diamond) — by routing the proof
through single-CLM (`ℝⁿ→Lℝ`) integrals only, where the instances are available.

By contrast, the **Wave** chapter needs none of this — the 1D setting uses only ordinary
derivatives and the FTC.

## Layout

```
MyProject/
  Calculus.lean    -- shared spacetime calculus (Du, u_t, Δu)
  Transport.lean   -- §2.1 transport equation
  Laplace.lean     -- §2.2 Laplace / Poisson
  Heat.lean        -- §2.3 heat equation
  Wave.lean        -- §2.4 wave equation
  Sobolev.lean     -- §5.2 Sobolev spaces (weak derivatives, W^{1,p})
MyProject.lean     -- imports all of the above
pde_lean_project.tex  -- companion writeup with proof notes and status tables
```
