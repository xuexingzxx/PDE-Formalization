# MyProject

A Lean 4 formalization of **Lawrence C. Evans' *Partial Differential Equations*** (2nd ed.),
covering the four fundamental linear PDEs of Chapter 2:

1. **Transport equation** — `u_t + b · Du = 0`
2. **Laplace's / Poisson's equation** — `−Δu = f`
3. **Heat equation** — `u_t − Δu = 0`
4. **Wave equation** — `u_tt − Δu = 0`

and **Sobolev spaces** (Chapter 5): weak derivatives, `W^{1,p}` as a Banach space, and the
**Meyers–Serrin density theorem** (`H = W`) via mollification.

Built with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Status

| Chapter | File | Status | Notes |
|---|---|---|---|
| §2.1 Transport | `Transport.lean` | ✅ **complete, zero `sorry`** | homogeneous IVP solved **and proved unique**; inhomogeneous Duhamel formula **provably solves the IVP** (Leibniz rule + spatial differentiation under the integral both proved) |
| §2.2 Laplace/Poisson | `Laplace.lean` | partial | fundamental solution, radial-power & `log` Laplacians, Green's identity (algebraic step) proved; mean-value, maximum principle and the Poisson representation are blocked by Mathlib gaps |
| §2.3 Heat | `Heat.lean` | ✅ **complete, zero `sorry`** | heat kernel is positive, has unit mass, and solves the heat equation; for **bounded continuous** `g`, the convolution `∫ Φ(x−y,t) g(y) dy` **provably solves the IVP** — both the time-derivative and the spatial-Laplacian are moved under the integral (n-dim Gaussian moments + nested differentiation under the integral); plus the **weak maximum principle** on a parabolic cylinder and **uniqueness** on a bounded cylinder (§2.3.3–2.3.4) |
| §2.4 Wave | `Wave.lean` | ✅ **complete, zero `sorry`** | traveling waves, d'Alembert (existence + `C²` regularity + initial conditions), energy conservation, uniqueness, finite propagation speed |
| §5.2 Sobolev | `Sobolev.lean` | ✅ **foundations, zero `sorry`** | test functions `C_c^∞(U)`, weak directional derivatives, the classical⟹weak bridge (integration by parts), linearity, a.e.-invariance, the smooth product (Leibniz) rule, a.e. uniqueness (fundamental lemma of the calculus of variations), closedness under `L¹`-on-compacts **and `Lᵖ`** limits (via a Hölder bridge), the weak-derivative graph is **closed in `Lᵖ × Lᵖ`**, and hence **`W^{1,p}(ℝⁿ)` is a Banach space** — with the genuine Sobolev norm `(‖u‖ₚᵖ + Σᵢ‖∂ᵢu‖ₚᵖ)^{1/p}` (via `PiLp`) — and **`W^{1,p}(U)` is a Banach space for any measurable `U`** over the restricted measure `Lᵖ(U)`; bundled as a named type `W1p` with a `CompleteSpace` instance and the function-value and weak-partial-derivative maps `W^{1,p}(U) → Lᵖ(U)` as **bounded linear operators**; plus `W^{1,p}` membership, locality, and `C_c^∞ ⊆ W^{1,p}` |
| §5.3 Mollification / Meyers–Serrin | `Mollification.lean` | ✅ **complete, zero `sorry`** | the full `Lᵖ`-mollification layer (which Mathlib lacks): **continuity of translation in `Lᵖ`** (`‖u(·+t)−u‖_p → 0`), a weighted **Jensen inequality** in `ℝ≥0∞` from Hölder, the key estimate `‖η⋆u − u‖_p^p ≤ ∫ η(y)‖u(·−y)−u‖_p^p`, hence **`η_δ ⋆ u → u` in `Lᵖ`**; the regularization identity **`(∂ₑη)⋆u = η⋆v`** and **the mollification `η⋆u` has weak derivative `η⋆v`** (via Fubini), culminating in **Meyers–Serrin (`H = W`)**: a single smooth mollification simultaneously approximates `u` and **all** its weak partial derivatives in `Lᵖ` — i.e. **`C^∞` is dense in `W^{1,p}(ℝⁿ)`**; plus the **Gagliardo–Nirenberg–Sobolev embedding** `‖u‖_{p*} ≲ ‖Du‖_p` (and the full Sobolev range) for `C¹` compactly-supported functions, specializing Mathlib's GNS inequality, and **Poincaré's inequality** `‖u‖_p ≤ C‖Du‖_p` (`W₀^{1,p}` form, §5.6) as the `q=p` case |
| §5.7 Rellich–Kondrachov (in progress) | `Rellich.lean` | ⏳ **building blocks, zero `sorry`** | the **translation / `Lᵖ`-modulus-of-continuity estimate** `‖u(·+h) − u‖_p ≤ \|h\|·‖Du‖_p` (`eLpNorm_translate_sub_le_fderiv`) — the equicontinuity input to Fréchet–Kolmogorov — proved from the **segment FTC** `u(x+h)−u(x)=∫₀¹ Du(x+t·h)[h] dt` (`sub_eq_integral_fderiv_segment`) via weighted Jensen + Tonelli + translation-invariance (avoiding Minkowski's integral inequality, which Mathlib lacks). packaged as **uniform equicontinuity from a common gradient bound** (`eLpNorm_translate_sub_le_of_gradient_le`, with the modulus `‖h‖·M → 0` shown in `tendsto_enorm_mul_nhds_zero`) — exactly Fréchet–Kolmogorov's equicontinuity hypothesis. The full compactness theorem additionally needs the **Fréchet–Kolmogorov `Lᵖ`-precompactness criterion**, which Mathlib does not yet provide |
| §5.7 Fréchet–Kolmogorov (foundations) | `FrechetKolmogorov.lean` | ⏳ **foundations, zero `sorry`** | the measure-theoretic groundwork: **negation-invariance of `volume`** on `ℝⁿ` (`measurePreserving_neg_euclidean`, derived from `map_addHaar_smul` since Mathlib has no `IsNegInvariant` instance), **reflection invariance** `∫F(x−y)=∫F(y)` (`lintegral_comp_sub_left`), and **Young's inequality, `L∞` endpoint** `‖∫η(x−y)·u(y)‖ ≤ ‖η‖_Q·‖u‖_P` (`enorm_convolutionIntegral_le`) — the uniform-boundedness input to Arzelà–Ascoli. Remaining: equicontinuity of mollifications + Arzelà–Ascoli + total-boundedness assembly |
| §5.2/§5.6 Higher-order `W^{k,p}` | `SobolevHigher.lean` | ✅ **zero `sorry`** | iterated directional weak derivatives `IsWeakDerivList` (chains of single-direction weak derivatives) with the **classical⟹weak bridge** `isWeakDerivList_of_contDiff`, the predicate `MemWkp = W^{k,p}` (all iterated coordinate weak derivatives of order ≤ k in `Lᵖ`) with `C_c^∞ ⊆ W^{k,p}`, **homogeneity** of the iterated weak derivative, and `MemW1p ↔ MemWkp 1`; plus **`W^{k,p}(ℝⁿ)` realised as a Banach space** carrying its genuine Sobolev norm `(Σ_{|l|≤k}‖D^l u‖ₚᵖ)^{1/p}` — a closed submodule `wkpSpace k` of `PiLp p` over the (finite) index of derivative multi-indices, **complete** (`completeSpace_wkpSpace`) as a closed subspace, mirroring the `W^{1,p}` construction; and **symmetry of mixed weak partials** `isWeakDerivInDir_comm` (`∂₂∂₁u = ∂₁∂₂u` a.e., the Clairaut/Schwarz theorem for weak derivatives) via classical Clairaut on a test function plus the fundamental lemma; and the **Hilbert space `H^k = W^{k,2}`** (`p=2`: inner-product structure inherited from `PiLp 2`, complete by `completeSpace_wkpSpace`) with explicit inner-product `inner_wkpSpace` (`⟪u,v⟫ = Σ ∫ Dˡu·Dˡv`) and energy-norm `norm_sq_wkpSpace` (`‖u‖² = Σ ∫ |Dˡu|²`) formulas |

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
  Mollification.lean -- §5.3 mollification & Meyers–Serrin (H = W)
MyProject.lean     -- imports all of the above
pde_lean_project.tex  -- companion writeup with proof notes and status tables
```
