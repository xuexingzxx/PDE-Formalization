# MyProject

A Lean 4 formalization of **Lawrence C. Evans' *Partial Differential Equations*** (2nd ed.),
covering the four fundamental linear PDEs of Chapter 2:

1. **Transport equation** — `u_t + b · Du = 0`
2. **Laplace's / Poisson's equation** — `−Δu = f`
3. **Heat equation** — `u_t − Δu = 0`
4. **Wave equation** — `u_tt − Δu = 0`

and **Sobolev spaces** (Chapter 5): weak derivatives, `W^{1,p}` as a Banach space, the
**Meyers–Serrin density theorem** (`H = W`) via mollification, the **Rellich–Kondrachov
compactness theorem** (§5.7 — the sufficient direction via a from-scratch Fréchet–Kolmogorov
`Lᵖ`-precompactness criterion, plus the full whole-space converse: equicontinuity **and**
tightness), **Morrey's inequality** (§5.6, the `p > n` embedding `W^{1,p} ↪ C^{0,1−n/p}`), and the
**Sobolev trace estimate + operator** (§5.5, `∫_{∂Ω} |u|^p ≤ C‖u‖^p_{W^{1,p}(Ω)}` for all `p ≥ 1`,
bundled into a bounded linear trace operator `traceCLM`), and the **Sobolev extension theorem for the
flat half-space** (§5.4, every `u ∈ W^{1,p}({xᵢ>0})` extends to `W^{1,p}(ℝⁿ)` — the local model of the
general extension operator, by even reflection + boundary density + `Lᵖ`-completeness).

It also builds the **surface-measure and Gauss–Green infrastructure** (Chapter 6 of the
companion writeup): the **area formula** for `C¹` images, surface measure on a `C¹`
hypersurface, and the **general divergence theorem** `∫_Ω div F = ∫_{∂Ω} ⟨F,ν⟩ dμ_H` on a
bounded `C¹` domain — a result Mathlib does not have (its divergence theorem covers only
rectangular boxes). This is the linchpin for the Sobolev trace/extension theorems and the
classical Laplacian representation formula.

Built with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## Status

| Chapter | File | Status | Notes |
|---|---|---|---|
| §2.1 Transport | `Transport.lean` | ✅ **complete, zero `sorry`** | homogeneous IVP solved **and proved unique**; inhomogeneous Duhamel formula **provably solves the IVP** (Leibniz rule + spatial differentiation under the integral both proved) |
| §2.2 Laplace/Poisson | `Laplace.lean` | ✅ **complete, zero `sorry`** | fundamental solution, radial-power & `log` Laplacians; **the entire mean-value + maximum-principle theory of §2.2.2–2.2.3** (`n ≥ 2`) — sphere & ball mean-value property, its converse, both maximum principles (ball version via the field `u(x+r·z)·z` + an ODE, *not* coarea; strong max via ball-mean rigidity + clopen/connectedness); **and the §2.2.4 Poisson representation formula `newtonianPotential_solves_poisson` (`n ≥ 2`): `u = ∫ Φ(x−y) f(y) dy` solves `−Δu = f`** — Part A (`Δu = ∫ Φ(x−y)·Δf`, moving `Δ` through the singular `Φ` onto `f` by a scalar diff-under-integral, `pot_hasFDerivAt`; the `precompR`/CLM convolution route diverges) + Part B (`∫ Φ(x−y)·Δf = −f(x)` via Green on the annulus for the singular `Φ`, using a `ContDiffBump` cutoff `mollified_fund`, then `ε→0` with `green_boundary_tendsto_f` + the vanishing near part). Surface integrals use the Riemannian `μHE` (the raw `(n−1)`-Hausdorff stubs were *false for `n ≥ 3`*: total flux `= −1` only holds for `μHE`, not `μH = μHE/c₀`); **and interior `C^∞` regularity `harmonic_smooth` (`n ≥ 2`)** — harmonic ⟹ C^∞, since `u` equals its own radial mollification locally (a radial C^∞ mollifier `moll` — Mathlib's `ContDiffBump` isn't guaranteed radial — with mean-value reproduction `moll_reproduce` proved by a layer-cake + Fubini; `u = (moll ⋆ ũ)/c` via a `ContDiffBump` cutoff `ũ` + `harmonic_ballMeanValue`). *(Restated to the C^∞ level `ContDiffOn ℝ (⊤ : ℕ∞)`: in current Mathlib `⊤ = ω = analytic` (Evans Thm 10, harder), not the cited C^∞ Thm 6.)* All off the `AreaFormula.lean` divergence theorem, no missing Mathlib |
| §2.3 Heat | `Heat.lean` | ✅ **complete, zero `sorry`** | heat kernel is positive, has unit mass, and solves the heat equation; for **bounded continuous** `g`, the convolution `∫ Φ(x−y,t) g(y) dy` **provably solves the IVP** — both the time-derivative and the spatial-Laplacian are moved under the integral (n-dim Gaussian moments + nested differentiation under the integral); plus the **weak maximum principle** on a parabolic cylinder and **uniqueness** on a bounded cylinder (§2.3.3–2.3.4) |
| §2.4 Wave | `Wave.lean` | ✅ **complete, zero `sorry`** | traveling waves, d'Alembert (existence + `C²` regularity + initial conditions), energy conservation, uniqueness, finite propagation speed |
| §5.2 Sobolev | `Sobolev/Basic.lean` | ✅ **foundations, zero `sorry`** | test functions `C_c^∞(U)`, weak directional derivatives, the classical⟹weak bridge (integration by parts), linearity, a.e.-invariance, the smooth product (Leibniz) rule, a.e. uniqueness (fundamental lemma of the calculus of variations), closedness under `L¹`-on-compacts **and `Lᵖ`** limits (via a Hölder bridge), the weak-derivative graph is **closed in `Lᵖ × Lᵖ`**, and hence **`W^{1,p}(ℝⁿ)` is a Banach space** — with the genuine Sobolev norm `(‖u‖ₚᵖ + Σᵢ‖∂ᵢu‖ₚᵖ)^{1/p}` (via `PiLp`) — and **`W^{1,p}(U)` is a Banach space for any measurable `U`** over the restricted measure `Lᵖ(U)`; bundled as a named type `W1p` with a `CompleteSpace` instance and the function-value and weak-partial-derivative maps `W^{1,p}(U) → Lᵖ(U)` as **bounded linear operators**; plus `W^{1,p}` membership, locality, and `C_c^∞ ⊆ W^{1,p}` |
| §5.3 Mollification / Meyers–Serrin | `Mollification.lean` | ✅ **complete, zero `sorry`** | the full `Lᵖ`-mollification layer (which Mathlib lacks): **continuity of translation in `Lᵖ`** (`‖u(·+t)−u‖_p → 0`), a weighted **Jensen inequality** in `ℝ≥0∞` from Hölder, the key estimate `‖η⋆u − u‖_p^p ≤ ∫ η(y)‖u(·−y)−u‖_p^p`, hence **`η_δ ⋆ u → u` in `Lᵖ`**; the regularization identity **`(∂ₑη)⋆u = η⋆v`** and **the mollification `η⋆u` has weak derivative `η⋆v`** (via Fubini), culminating in **Meyers–Serrin (`H = W`)**: a single smooth mollification simultaneously approximates `u` and **all** its weak partial derivatives in `Lᵖ` — i.e. **`C^∞` is dense in `W^{1,p}(ℝⁿ)`**; plus the **Gagliardo–Nirenberg–Sobolev embedding** `‖u‖_{p*} ≲ ‖Du‖_p` (and the full Sobolev range) for `C¹` compactly-supported functions, specializing Mathlib's GNS inequality — **and its extension to all of `W^{1,p}` by passing to the limit** (`exists_eLpNorm_le_eLpNorm_fderiv_of_tendsto`: a `W^{1,p}`-limit of `C¹` compactly-supported functions inherits `‖u‖_{p*} ≤ C‖Du‖_p` with the uniform GNS constant, via convergence-in-measure + Fatou lower-semicontinuity) — and the **density of `C^∞_c` in `W^{1,p}(ℝⁿ)`** that supplies its approximating sequences (`exists_contDiff_hasCompactSupport_forall_isWeakDerivInDir`: truncate by a scaled cutoff with gradient `≤ M/R`, then mollify keeping compact support; the two `Lᵖ` truncation limits + weak Leibniz + `ε/2+ε/2`), giving the **embedding on all of `W^{1,p}(ℝⁿ)` with no hypotheses** (`exists_eLpNorm_le_eLpNorm_fderiv_of_forall_isWeakDerivInDir`: `u ∈ Lᵖ` with weak gradient `V ∈ Lᵖ` ⟹ `‖u‖_{p*} ≤ C‖V‖_p`, via the components bridge `‖L‖ ≤ ∑ᵢ‖L eᵢ‖` turning per-direction `Lᵖ`-convergence into `‖fderiv wₖ − V‖_p → 0`), and **Poincaré's inequality** `‖u‖_p ≤ C‖Du‖_p` (`W₀^{1,p}` form, §5.6) as the `q=p` case |
| §5.7 Rellich–Kondrachov | `Rellich.lean`, `FrechetKolmogorov.lean`, `RellichKondrachov.lean` | ✅ **complete, zero `sorry`** | the **sufficient direction of Rellich–Kondrachov**, proved end to end (the `Lᵖ`-compactness criterion that Mathlib lacks). **`rellich_kondrachov`** (`RellichKondrachov.lean`): a family of `C¹` functions with a **uniform `Lᵖ` gradient bound** `‖Du i‖_p ≤ M` (and a uniform `L^P` bound) is **totally bounded in `Lᵖ(K)`** on a compact `K` — the compactness behind `W^{1,p}(U) ↪↪ Lᵖ(U)`. Built from: (i) the **translation/gradient estimate** `‖u(·+h) − u‖_p ≤ \|h\|·‖Du‖_p` (`Rellich.lean`: `eLpNorm_translate_sub_le_fderiv` from the segment FTC `sub_eq_integral_fderiv_segment` via weighted Jensen + Tonelli + translation-invariance, packaged as `eLpNorm_translate_sub_le_of_gradient_le` with modulus `‖h‖·M → 0`, `tendsto_enorm_mul_nhds_zero`) supplying the **uniform equicontinuity**; (ii) the **Fréchet–Kolmogorov compactness machinery** (`FrechetKolmogorov.lean`): Young's `L∞` endpoint (`enorm_convolutionIntegral_le`), mollification continuity (`continuous_convolutionIntegral`), the **closed-embedding Arzelà–Ascoli** precompactness criterion `isCompact_closure_toLp_image_of_equicontinuous_of_bound` (range `{Continuous}` closed in the uniform-on-compacts topology, fed to Mathlib's relative-compactness AA), the `C(K)→Lᵖ` transfer via the continuous-linear `ContinuousMap.toLp`, the subtype-measure isometry transfer (`isCompact_closure_of_isometry` + `continuousMap_toLp_comap_eq_compMeasurePreserving`, identifying `toLp` across `Lᵖ(↥K,comap) ≅ Lᵖ(K,restrict)`), the dischargers (`equicontinuous_convolutionIntegral`, `norm_convolutionIntegral_le_of_bound`), the per-`δ` precompactness `isCompact_closure_toLp_restrict_convolution`, the **ε/3 glue** `totallyBounded_of_forall_approx`, and the **mollifiable-form FK criterion** `totallyBounded_toLp_restrict_of_mollifiable`; (iii) the **uniform mollification bound** (`Mollification.lean`: `eLpNorm_convolution_sub_le_of_modulus`, integral form via the convolution bridge `convolution_eq_integral_sub`). These assemble into the **self-contained criterion** `totallyBounded_toLp_restrict_of_equicontinuous` (discharging mollifiability with an explicit normalised `ContDiffBump`), whence `rellich_kondrachov`. The **necessary direction** (converse) is proved in **full**: `uniformEquicontinuous_translate_of_totallyBounded` (a family totally bounded in `Lᵖ(ℝⁿ)` is uniformly `Lᵖ`-equicontinuous, `sup_i ‖u i(·−y) − u i‖_p → 0`, the exact hypothesis the sufficient direction consumes) **and** the **tightness half** `unifTight_of_totallyBounded` (for every `ε` a single finite-measure set `s` has `sup_i ‖𝟙_{sᶜ} u i‖_p ≤ ε`, an `ε/2`-net transfer off Mathlib's single-function tightness `MemLp.exists_eLpNorm_indicator_compl_lt`) — together the **complete whole-space Fréchet–Kolmogorov converse** |
| §5.6 Morrey | `Sobolev/Morrey.lean` | ✅ **complete, zero `sorry`** | **Morrey's inequality** — the `p > n` Sobolev embedding `W^{1,p}(ℝⁿ) ↪ C^{0,1−n/p}`, the exact complement of the `p < n` GNS embedding. `morrey_holder` (`n ≥ 2`, `p.HolderConjugate q`, `(n−1)q < n ⟺ p > n`): `|u x − u y| ≤ C·‖x−y‖^{1−n/p}·(∫‖Du‖^p)^{1/p}`. Four steps: (i) the **potential (Riesz) estimate** `∫_{B(0,r)}|u(x+z)−u(x)| ≤ (rⁿ/n)∫_{B(0,r)}‖Du(x+w)‖/‖w‖^{n−1}` — the hard core Mathlib lacked — proved by a **sphere-free** Cartesian-dilation + double-Tonelli route (no polar coordinates, hence no area-formula dependency); (ii) the **Hölder bound** `riesz_bound` (kernel `‖w‖^{−(n−1)} ∈ L^q` iff `p > n`, exponent identity `(n−(n−1)q)/q = 1−n/p`); (iii) **localisation** `lp_local_le_global` (`(∫_{B(0,r)}‖Du(x+·)‖^p)^{1/p} ≤ ‖Du‖_{Lᵖ(ℝⁿ)}`, translation measure-preserving); (iv) the **two-point lens** (midpoint ball `B(m,r/2) ⊆ B(x,r)∩B(y,r)`, average `|u x − u y| ≤ |u x − u z| + |u y − u z|`, the `rⁿ` cancels leaving the `r^{1−n/p}` modulus) |
| §5.5 Trace estimate | `Sobolev/Trace.lean` | ✅ **all `p ≥ 1` complete, zero `sorry`** | the **`Lᵖ` Sobolev trace estimate**, the analytic heart of the trace theorem, over the **entire** Sobolev range: for `u ∈ C¹` on a bounded `C¹` domain `Ω ⊆ ℝ^{m+2}` and every `p ≥ 1`, **`trace_estimate_lp`**: `∫_{∂Ω} \|u\|^p dμ_H ≤ C(∫_Ω \|u\|^p + ∫_Ω ‖Du‖^p)` with `\|u\|^p = (u²)^{p/2}` (non-smoothed special cases **`trace_estimate_pow`** for `p ≥ 2` and **`trace_estimate_sq`** at `p=2`). Built on the Chapter-6 **`divergence_theorem`** via two reusable lemmas: (i) **`exists_transverse_field`** — a global `C¹` field `F` with `⟪F,ν⟫ ≥ 1` on `∂Ω`, the geometric core: since the chart normal is **unit** (`norm_graphNormal`, transported through the isometries `e`, `flatten`), `ν` is a continuous unit field on the compact `∂Ω`; cut it to a compactly-supported field `= ν` near `∂Ω`, uniformly approximate within `½` by a `C^∞` field (`UniformContinuous.exists_contDiff_dist_le`), and double; (ii) **`divergenceE_smul_scalar`** — the divergence Leibniz rule `div(g•F) = g·div F + Dg(F)`. Gauss–Green on `(u²)^{p/2}•F`: `⟪·,ν⟫ ≥ (u²)^{p/2}` on `∂Ω`; `div((u²)^{p/2}•F) ≤ C((u²)^{p/2}+‖Du‖^p)` in `Ω` by Leibniz + Cauchy–Schwarz + a Young helper (**`trace_young`** for `p≥2`, **`trace_young_pos`** for the positive-base smoothing), `C` from sup bounds of `div F`, `‖F‖` over `Ω̄`. For `1 ≤ p < 2` (where `(u²)^{p/2}` fails to be `C¹` at `u=0`) the argument runs on the strictly-positive smoothing `(ε²+u²)^{p/2}` with `C` **independent of `ε`**, then `ε→0` along `1/(k+1)` by **dominated convergence**. **The trace operator** is built: the estimate is recast in operator form (**`trace_lp_bound`**: `‖u|_{∂Ω}‖_{Lᵖ(∂Ω)} ≤ K·max(‖u‖_{Lᵖ(Ω)}, ‖Du‖_{Lᵖ(Ω)})` uniformly over `C¹` `u`, via `MemLp.eLpNorm_eq_integral_rpow_norm`), the `C¹` functions embed into the graph space via `u ↦ (u,Du)` (**`traceEmbed`**) and restrict to the boundary via `u ↦ u|_{∂Ω}` (**`traceRestrict`**), and these bundle into the genuine bounded linear operator **`traceCLM : ↥(range traceEmbed) →L[ℝ] Lᵖ(∂Ω)`** (kernel inclusion `traceEmbed_ker_le` → `Submodule.liftQ`/`quotKerEquivRange`/`mkContinuous`). Making the `ContinuousLinearMap` compile required carrying the exponent as an **opaque `q : ℝ≥0∞`** (not `ENNReal.ofReal p`) to avoid a `whnf`/`isDefEq` blow-up. Extending `T` from `C¹` to all of `W^{1,p}(Ω)` by density still needs a Sobolev extension operator |
| §5.4 Extension | `Sobolev/Extension.lean` | ✅ **half-space operator complete, zero `sorry`** | the **`W^{1,p}` extension theorem for the flat half-space** — the local model of §5.4 — proved end to end, as a genuine **bounded** operator. **`exists_memW1p_extension_halfspace`**: every `u ∈ W^{1,p}({xᵢ>0})` (weak derivatives `v`) extends to a `U ∈ W^{1,p}(ℝⁿ)` (with explicit weak derivatives `V`) agreeing with `u` a.e. on `{xᵢ>0}` and satisfying the operator bounds `‖U‖_{Lᵖ(ℝⁿ)} ≤ 2‖u‖_{Lᵖ({xᵢ>0})}` **and** `‖Vⱼ‖_{Lᵖ(ℝⁿ)} ≤ 2‖vⱼ‖_{Lᵖ({xᵢ>0})}` for every `j` (the `≤2` per-approximant bounds pass to the `Lᵖ`-limit via `eLpNorm_le_two_of_tendsto`). Built from three layers: (i) the **even reflection** across the flattened boundary `{xᵢ=0}` — a linear operator landing in `W^{1,p}(ℝⁿ)`, bounded by `2` in each seminorm (`evenRefl`, `memW1p_evenRefl_restrict`, `eLpNorm_evenRefl_le_restrict`/`_grad_le_restrict`); its reflected weak gradient glues the classical derivative on the upper half with the reflection change-of-variables on the lower, the normal boundary term killed by a **direct dominated-convergence Lipschitz cancellation** (the `∂ᵢχ_m` blow-up compensated by `\|xᵢ\|≲1/(m+1)` — no Fubini); (ii) the **boundary density** `exists_seq_contDiff_tendsto_halfspace` — `C^∞` functions dense in `W^{1,p}({xᵢ>0})` *up to the boundary*, by mollifying an inward-translated copy `u_s=u(·+s·eᵢ)` with a mollifier of radius `<s` so every sample stays in the interior, using the **localized gradient identity** `convolution_deriv_eq_of_subset` (`(∂ₑη)⋆u = η⋆v` needing the weak-derivative relation only where the reflected bump is supported); (iii) the **`Lᵖ`-completeness passage** — reflect the approximants, show the reflected functions **and** their gradients Cauchy in `Lᵖ(ℝⁿ)` via the restricted `≤2` bounds, extract the `Lᵖ`-limits by Banach completeness (`exists_memLp_tendsto_of_dominated`, one call for the function + one per coordinate), and transfer the weak-derivative relation to the limit by the closedness cornerstone `isWeakDerivInDir_of_tendsto_Lp_restrict`. Sidesteps Mathlib's missing **convolution Young inequality** (`memLp_convolution` gets `ρ⋆u ∈ Lᵖ` by triangle inequality from the project's own convolution-error bound). The general bounded-`C¹`-domain operator (chart-flatten + partition-of-unity gluing) remains, gated on boundary-chart infrastructure not yet in the project |
| §5.2/§5.6 Higher-order `W^{k,p}` | `Sobolev/Higher.lean` | ✅ **zero `sorry`** | iterated directional weak derivatives `IsWeakDerivList` (chains of single-direction weak derivatives) with the **classical⟹weak bridge** `isWeakDerivList_of_contDiff`, the predicate `MemWkp = W^{k,p}` (all iterated coordinate weak derivatives of order ≤ k in `Lᵖ`) with `C_c^∞ ⊆ W^{k,p}`, **homogeneity** of the iterated weak derivative, and `MemW1p ↔ MemWkp 1`; plus **`W^{k,p}(ℝⁿ)` realised as a Banach space** carrying its genuine Sobolev norm `(Σ_{|l|≤k}‖D^l u‖ₚᵖ)^{1/p}` — a closed submodule `wkpSpace k` of `PiLp p` over the (finite) index of derivative multi-indices, **complete** (`completeSpace_wkpSpace`) as a closed subspace, mirroring the `W^{1,p}` construction; and **symmetry of mixed weak partials** `isWeakDerivInDir_comm` (`∂₂∂₁u = ∂₁∂₂u` a.e., the Clairaut/Schwarz theorem for weak derivatives) via classical Clairaut on a test function plus the fundamental lemma; and the **Hilbert space `H^k = W^{k,2}`** (`p=2`: inner-product structure inherited from `PiLp 2`, complete by `completeSpace_wkpSpace`) with explicit inner-product `inner_wkpSpace` (`⟪u,v⟫ = Σ ∫ Dˡu·Dˡv`) and energy-norm `norm_sq_wkpSpace` (`‖u‖² = Σ ∫ |Dˡu|²`) formulas |
| Ch.6 Surface measure & divergence theorem | `AreaFormula.lean` | ✅ **complete, zero `sorry`** | the surface-measure → Gauss–Green programme that Mathlib lacks, built end to end. The **area formula** `μ_H(φ''A) = ∫_A jac(Dφ)` for `C¹` immersions and its graph specialization `area_formula_graph` (`= ∫⁻ √(1+‖∇γ‖²)`), with vector-valued change of variables; the **flux identity** and the **graph Gauss–Green theorem** `divergence_theorem_graph` (the load-bearing local model, with a *signed* vertical integral so **no `γ ≥ 0` needed**); the volume/surface-measure-preserving isometry **`flatten`** carrying the plain product `ℝ^{m+1}×ℝ` to flat `ℝ^{m+2}` with the canonical trace-divergence `divergenceE`; the **bottomless subgraph theorem** for arbitrary `γ` (oriented `Iic`-additivity `integral_Iic_split`); **chart flux** via active rigid-motion transfer (`divergenceE_transport_affine`); the boundary-is-locally-a-graph topology (`chart_frontier_domain`); the single-chart `chart_term`; the bounded-`C¹`-domain and outward-normal structures (`IsBoundedC1Domain`, `IsOutwardNormal`) with a finite chart cover + smooth partition of unity; and **finiteness of the boundary surface measure** `μ_H(∂Ω) < ∞` (`surfaceMeasure_frontier_lt_top`) — assembling into the capstone **`divergence_theorem`**: for a bounded `C¹` domain `Ω ⊆ ℝ^{m+2}`, an outward normal `ν`, and `C¹` `F`, `∫_Ω divergenceE F = ∫_{∂Ω} ⟨F,ν⟩ dμ_H`, **unconditional** (no sign/compact-support/finiteness hypotheses) |

`Calculus.lean` provides shared spacetime calculus utilities (`spatialGradient`,
`timeDerivative`, `spatialLaplacian`, a Leibniz-rule helper, and the horizontal
integration-by-parts toolchain — compact-support FTC, `Fin.insertNth` coordinate-slice
lemmas, and `integral_horizontal_ibp` — that feeds the graph Gauss–Green theorem).

The project builds cleanly against Mathlib (`lake build`) and is now **entirely `sorry`-free** —
every chapter above is complete, with no outstanding proof obligations.

## Known blockers (missing Mathlib infrastructure)

**The Laplace chapter is now sorry-free** — **all three original blockers are resolved**, and both
the §2.2.4 representation formula and interior `C^∞` regularity they were blocking are **proved**.
None was a gap in the mathematics; each was reached from this project's own tools.

- ~~**Stokes' theorem on spherical domains**~~ (Laplace `green_identity_annulus`,
  `green_boundary_tendsto_f`) — **resolved**: the general `divergence_theorem` in
  `AreaFormula.lean` applies to any bounded `C¹` domain (a ball/annulus included), superseding
  Mathlib's box-only divergence theorem.
- ~~**Sphere surface measure** `σ(∂B(0,ε)) = n ωₙ εⁿ⁻¹`~~ — **resolved**: proved as
  `sphere_surfaceMeasure` (`σ(∂B) = n·vol(B)/r`), a corollary of `divergence_theorem` on
  `F = id`. It is the Riemannian `μHE` surface area — which is exactly Evans' `dσ`, and the
  reason the §2.2.4 lemmas had to be re-stated from raw `μH` to `μHE`.
- ~~**`n`-dimensional polar coordinates**~~ (Laplace integrability of `‖Φ‖` near `0`) —
  **resolved** via Mathlib's `integrable_fun_norm_addHaar`, packaged as
  `integrableOn_unitBall_radial` / `integrableOn_norm_rpow_unitBall`.

The §2.2.4 representation formula (`newtonianPotential_solves_poisson`) is complete: the
fundamental-solution flux (`= −1`, `μHE`), the annulus Green's identity, the `ε→0`
singular-integral limit (`green_boundary_tendsto_f`), moving `Δ` through the singular `Φ` onto `f`
(`laplacian_newtonianPotential`, a scalar diff-under-integral), and the annulus argument for the
singular `Φ` via a `ContDiffBump` cutoff (`mollified_fund` / `green_annulus_fund`) — all off the
`divergence_theorem`, no new Mathlib infrastructure. Interior `C^∞` regularity (`harmonic_smooth`)
is likewise proved, by radial mollification (`moll` / `moll_reproduce`), closing out the chapter.

The **Heat** chapter's spatial-Laplacian-under-the-integral step required navigating a
genuine Mathlib instance gap — `ContinuousENorm` (hence `Integrable`/`integral_apply`) is
missing for iterated CLM spaces `ℝⁿ →L (ℝⁿ→Lℝ)` (a topology diamond) — by routing the proof
through single-CLM (`ℝⁿ→Lℝ`) integrals only, where the instances are available.

By contrast, the **Wave** chapter needs none of this — the 1D setting uses only ordinary
derivatives and the FTC.

**~~Open gap — the trace *operator* bundling~~ (§5.5, `Sobolev/Trace.lean`) — RESOLVED.** The trace is
now a genuine bounded linear operator `traceCLM : ↥(range traceEmbed) →L[ℝ] Lᵖ(∂Ω)`, built by the
kernel inclusion `traceEmbed_ker_le` → `Submodule.liftQ` / `quotKerEquivRange` / `mkContinuous` and
bounded by `trace_lp_bound`. It had been blocked by a Lean elaboration-performance wall (`whnf`/
`isDefEq` blow-up on maps into `Lp (ENNReal.ofReal p)` across the function-space quotient — a >12-min
non-converging compile; `@[irreducible]` did not help). The fix was to carry the Sobolev exponent as
an **opaque `q : ℝ≥0∞`** (with `Fact (1 ≤ q)`, `q ≠ ⊤`, `q.toReal = p`) instead of `ENNReal.ofReal p`,
so the defeq checker never reduces the exponent — cutting the compile to ~4.6 min. The one remaining
piece of the *full* trace theorem is extending the operator from `C¹` to all of `W^{1,p}(Ω)` by
density, which for a general domain needs a Sobolev **extension operator**. The **half-space** case of
that operator is now proved (§5.4, `exists_memW1p_extension_halfspace` in `Sobolev/ExtensionOperator.lean`);
the general bounded-`C¹`-domain version remains, gated on the same `C¹`-boundary-chart infrastructure
(a flattening diffeomorphism + `W^{1,p}`-invariance under a nonlinear `C¹` change of variables).

## Layout

```
MyProject/
  Common/                  -- shared base + utilities (import-Mathlib base + Lᵖ helpers)
    Calculus.lean          -- shared spacetime calculus (Du, u_t, Δu) + shared Lᵖ/measure lemmas + horizontal IBP
    LpJensen.lean          -- weighted Jensen inequality in ℝ≥0∞
    Translation.lean       -- Lᵖ-continuity of translation (continuous compact support)
    AreaFormula.lean       -- Ch.6 area formula, surface measure, general divergence theorem (Gauss–Green)
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
    RellichKondrachov.lean -- §5.7 self-contained FK criterion + named Rellich–Kondrachov theorem + whole-space converse
    Morrey.lean            -- §5.6 Morrey inequality W^{1,p} ↪ C^{0,1−n/p} (p > n)
    Trace.lean             -- §5.5 trace estimate ∫_{∂Ω} |u|^p ≤ C‖u‖^p_{W^{1,p}} (all p≥1) (+ transverse field, div Leibniz)
    Extension.lean         -- §5.4 even-reflection foundations (refll, evenRefl weak gradient, Lᵖ/gradient bounds)
    ExtensionOperator.lean -- §5.4 half-space W^{1,p} extension operator (boundary density + Lᵖ completeness assembly)
MyProject.lean             -- imports all of the above
pde_lean_project.tex  -- companion writeup with proof notes and status tables
```
