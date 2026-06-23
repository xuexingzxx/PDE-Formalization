# MyProject

A Lean 4 formalization of **Lawrence C. Evans' *Partial Differential Equations*** (2nd ed.),
covering the four fundamental linear PDEs of Chapter 2:

1. **Transport equation** — `u_t + b · Du = 0`
2. **Laplace's / Poisson's equation** — `−Δu = f`
3. **Heat equation** — `u_t − Δu = 0`
4. **Wave equation** — `u_tt − Δu = 0`

and **Sobolev spaces** (Chapter 5): weak derivatives, `W^{1,p}` as a Banach space, the
**Meyers–Serrin density theorem** (`H = W`) via mollification, and the **Rellich–Kondrachov
compactness theorem** (§5.7, sufficient direction) via a from-scratch Fréchet–Kolmogorov
`Lᵖ`-precompactness criterion.

Built with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Status

| Chapter | File | Status | Notes |
|---|---|---|---|
| §2.1 Transport | `Transport.lean` | ✅ **complete, zero `sorry`** | homogeneous IVP solved **and proved unique**; inhomogeneous Duhamel formula **provably solves the IVP** (Leibniz rule + spatial differentiation under the integral both proved) |
| §2.2 Laplace/Poisson | `Laplace.lean` | partial | fundamental solution, radial-power & `log` Laplacians, Green's identity (algebraic step) proved; mean-value, maximum principle and the Poisson representation are blocked by Mathlib gaps |
| §2.3 Heat | `Heat.lean` | ✅ **complete, zero `sorry`** | heat kernel is positive, has unit mass, and solves the heat equation; for **bounded continuous** `g`, the convolution `∫ Φ(x−y,t) g(y) dy` **provably solves the IVP** — both the time-derivative and the spatial-Laplacian are moved under the integral (n-dim Gaussian moments + nested differentiation under the integral); plus the **weak maximum principle** on a parabolic cylinder and **uniqueness** on a bounded cylinder (§2.3.3–2.3.4) |
| §2.4 Wave | `Wave.lean` | ✅ **complete, zero `sorry`** | traveling waves, d'Alembert (existence + `C²` regularity + initial conditions), energy conservation, uniqueness, finite propagation speed |
| §5.2 Sobolev | `Sobolev.lean` | ✅ **foundations, zero `sorry`** | test functions `C_c^∞(U)`, weak directional derivatives, the classical⟹weak bridge (integration by parts), linearity, a.e.-invariance, the smooth product (Leibniz) rule, a.e. uniqueness (fundamental lemma of the calculus of variations), closedness under `L¹`-on-compacts **and `Lᵖ`** limits (via a Hölder bridge), the weak-derivative graph is **closed in `Lᵖ × Lᵖ`**, and hence **`W^{1,p}(ℝⁿ)` is a Banach space** — with the genuine Sobolev norm `(‖u‖ₚᵖ + Σᵢ‖∂ᵢu‖ₚᵖ)^{1/p}` (via `PiLp`) — and **`W^{1,p}(U)` is a Banach space for any measurable `U`** over the restricted measure `Lᵖ(U)`; bundled as a named type `W1p` with a `CompleteSpace` instance and the function-value and weak-partial-derivative maps `W^{1,p}(U) → Lᵖ(U)` as **bounded linear operators**; plus `W^{1,p}` membership, locality, and `C_c^∞ ⊆ W^{1,p}` |
| §5.3 Mollification / Meyers–Serrin | `Mollification.lean` | ✅ **complete, zero `sorry`** | the full `Lᵖ`-mollification layer (which Mathlib lacks): **continuity of translation in `Lᵖ`** (`‖u(·+t)−u‖_p → 0`), a weighted **Jensen inequality** in `ℝ≥0∞` from Hölder, the key estimate `‖η⋆u − u‖_p^p ≤ ∫ η(y)‖u(·−y)−u‖_p^p`, hence **`η_δ ⋆ u → u` in `Lᵖ`**; the regularization identity **`(∂ₑη)⋆u = η⋆v`** and **the mollification `η⋆u` has weak derivative `η⋆v`** (via Fubini), culminating in **Meyers–Serrin (`H = W`)**: a single smooth mollification simultaneously approximates `u` and **all** its weak partial derivatives in `Lᵖ` — i.e. **`C^∞` is dense in `W^{1,p}(ℝⁿ)`**; plus the **Gagliardo–Nirenberg–Sobolev embedding** `‖u‖_{p*} ≲ ‖Du‖_p` (and the full Sobolev range) for `C¹` compactly-supported functions, specializing Mathlib's GNS inequality — **and its extension to all of `W^{1,p}` by passing to the limit** (`exists_eLpNorm_le_eLpNorm_fderiv_of_tendsto`: a `W^{1,p}`-limit of `C¹` compactly-supported functions inherits `‖u‖_{p*} ≤ C‖Du‖_p` with the uniform GNS constant, via convergence-in-measure + Fatou lower-semicontinuity) — and the **density of `C^∞_c` in `W^{1,p}(ℝⁿ)`** that supplies its approximating sequences (`exists_contDiff_hasCompactSupport_forall_isWeakDerivInDir`: truncate by a scaled cutoff with gradient `≤ M/R`, then mollify keeping compact support; the two `Lᵖ` truncation limits + weak Leibniz + `ε/2+ε/2`), giving the **embedding on all of `W^{1,p}(ℝⁿ)` with no hypotheses** (`exists_eLpNorm_le_eLpNorm_fderiv_of_forall_isWeakDerivInDir`: `u ∈ Lᵖ` with weak gradient `V ∈ Lᵖ` ⟹ `‖u‖_{p*} ≤ C‖V‖_p`, via the components bridge `‖L‖ ≤ ∑ᵢ‖L eᵢ‖` turning per-direction `Lᵖ`-convergence into `‖fderiv wₖ − V‖_p → 0`), and **Poincaré's inequality** `‖u‖_p ≤ C‖Du‖_p` (`W₀^{1,p}` form, §5.6) as the `q=p` case |
| §5.7 Rellich–Kondrachov | `Rellich.lean`, `FrechetKolmogorov.lean`, `RellichKondrachov.lean` | ✅ **complete, zero `sorry`** | the **sufficient direction of Rellich–Kondrachov**, proved end to end (the `Lᵖ`-compactness criterion that Mathlib lacks). **`rellich_kondrachov`** (`RellichKondrachov.lean`): a family of `C¹` functions with a **uniform `Lᵖ` gradient bound** `‖Du i‖_p ≤ M` (and a uniform `L^P` bound) is **totally bounded in `Lᵖ(K)`** on a compact `K` — the compactness behind `W^{1,p}(U) ↪↪ Lᵖ(U)`. Built from: (i) the **translation/gradient estimate** `‖u(·+h) − u‖_p ≤ \|h\|·‖Du‖_p` (`Rellich.lean`: `eLpNorm_translate_sub_le_fderiv` from the segment FTC `sub_eq_integral_fderiv_segment` via weighted Jensen + Tonelli + translation-invariance, packaged as `eLpNorm_translate_sub_le_of_gradient_le` with modulus `‖h‖·M → 0`, `tendsto_enorm_mul_nhds_zero`) supplying the **uniform equicontinuity**; (ii) the **Fréchet–Kolmogorov compactness machinery** (`FrechetKolmogorov.lean`): Young's `L∞` endpoint (`enorm_convolutionIntegral_le`), mollification continuity (`continuous_convolutionIntegral`), the **closed-embedding Arzelà–Ascoli** precompactness criterion `isCompact_closure_toLp_image_of_equicontinuous_of_bound` (range `{Continuous}` closed in the uniform-on-compacts topology, fed to Mathlib's relative-compactness AA), the `C(K)→Lᵖ` transfer via the continuous-linear `ContinuousMap.toLp`, the subtype-measure isometry transfer (`isCompact_closure_of_isometry` + `continuousMap_toLp_comap_eq_compMeasurePreserving`, identifying `toLp` across `Lᵖ(↥K,comap) ≅ Lᵖ(K,restrict)`), the dischargers (`equicontinuous_convolutionIntegral`, `norm_convolutionIntegral_le_of_bound`), the per-`δ` precompactness `isCompact_closure_toLp_restrict_convolution`, the **ε/3 glue** `totallyBounded_of_forall_approx`, and the **mollifiable-form FK criterion** `totallyBounded_toLp_restrict_of_mollifiable`; (iii) the **uniform mollification bound** (`Mollification.lean`: `eLpNorm_convolution_sub_le_of_modulus`, integral form via the convolution bridge `convolution_eq_integral_sub`). These assemble into the **self-contained criterion** `totallyBounded_toLp_restrict_of_equicontinuous` (discharging mollifiability with an explicit normalised `ContDiffBump`), whence `rellich_kondrachov`. The **necessary direction** (converse) is also proved in its equicontinuity form — `uniformEquicontinuous_translate_of_totallyBounded`: a family totally bounded in `Lᵖ(ℝⁿ)` is uniformly `Lᵖ`-equicontinuous (`sup_i ‖u i(·−y) − u i‖_p → 0`), the exact hypothesis the sufficient direction consumes (only the tightness-at-infinity half of the full whole-space equivalence is left) |
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
  Common/                  -- shared base + utilities (import-Mathlib base + Lᵖ helpers)
    Calculus.lean          -- shared spacetime calculus (Du, u_t, Δu) + shared Lᵖ/measure lemmas
    LpJensen.lean          -- weighted Jensen inequality in ℝ≥0∞
    Translation.lean       -- Lᵖ-continuity of translation (continuous compact support)
  PDE/                     -- Chapter 2: the four fundamental linear PDEs
    Transport.lean         -- §2.1 transport equation
    Laplace.lean           -- §2.2 Laplace / Poisson
    Heat.lean              -- §2.3 heat equation
    Wave.lean              -- §2.4 wave equation
  Sobolev/                 -- Chapter 5: Sobolev spaces
    Basic.lean             -- §5.2 Sobolev spaces (weak derivatives, W^{1,p})
    Higher.lean            -- §5.2/§5.6 higher-order W^{k,p}, H^k Hilbert, mixed symmetry
    Mollification.lean     -- §5.3 mollification & Meyers–Serrin (H = W)
    Rellich.lean           -- §5.7 translation/gradient equicontinuity estimates
    FrechetKolmogorov.lean -- §5.7 Fréchet–Kolmogorov compactness machinery + criterion
    RellichKondrachov.lean -- §5.7 self-contained FK criterion + named Rellich–Kondrachov theorem
MyProject.lean             -- imports all of the above
pde_lean_project.tex  -- companion writeup with proof notes and status tables
```
