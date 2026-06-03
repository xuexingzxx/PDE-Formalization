import Mathlib

open scoped Topology

/-!
# Wave Equation (Evans PDE, §2.4)

Formalizing the one-dimensional wave equation and d'Alembert's formula.

  (Wave)  u_tt − u_xx = 0   in ℝ × (0, ∞)
          u = g,  u_t = h    on ℝ × {t = 0}

We work on spacetime `ℝ × ℝ` with `x` the space variable and `t` the time variable,
using ordinary second derivatives `u_tt`, `u_xx`.

The key structural fact (Evans §2.4.1): the general solution is a superposition of a
right-moving wave `φ(x − t)` and a left-moving wave `ψ(x + t)`; each separately solves
the wave equation. d'Alembert's formula

  u(x, t) = ½(g(x + t) + g(x − t)) + ½ ∫_{x−t}^{x+t} h(s) ds

is exactly such a superposition (with the integral term being the difference of an
antiderivative of `h` evaluated at `x ± t`).

## References
* Evans, Lawrence C. *Partial Differential Equations*, 2nd ed., §2.4.
-/

/-! ### Second Derivatives -/

/-- The first time derivative `u_t(x, t)`. -/
noncomputable def timeDeriv (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun s => u (p.1, s)) p.2

/-- The first space derivative `u_x(x, t)`. -/
noncomputable def spaceDeriv (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun r => u (r, p.2)) p.1

/-- The second time derivative `u_tt(x, t)`. -/
noncomputable def timeDeriv2 (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun s => deriv (fun r => u (p.1, r)) s) p.2

/-- The second space derivative `u_xx(x, t)`. -/
noncomputable def spaceDeriv2 (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun s => deriv (fun r => u (r, p.2)) s) p.1

/-- `u` solves the (homogeneous, unit-speed) wave equation `u_tt = u_xx` everywhere. -/
def IsWaveSolution (u : ℝ × ℝ → ℝ) : Prop :=
  ∀ p : ℝ × ℝ, timeDeriv2 u p = spaceDeriv2 u p

/-! ### d'Alembert's Formula -/

/-- d'Alembert's solution `u(x,t) = ½(g(x+t)+g(x−t)) + ½∫_{x−t}^{x+t} h`. -/
noncomputable def dalembert (g h : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => (g (p.1 + p.2) + g (p.1 - p.2)) / 2 + (∫ s in (p.1 - p.2)..(p.1 + p.2), h s) / 2

/-! ### Derivative Helpers

The first derivative of `f` precomposed with the four affine shifts `a ± ·`, `· ± a`,
as a function. These let us compute the second derivatives of `φ(x ± t)` cleanly. -/

private lemma deriv_addL (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a : ℝ) :
    deriv (fun r => f (a + r)) = fun s => deriv f (a + s) := by
  funext s
  have h1 : HasDerivAt (fun r => a + r) 1 s := by simpa using (hasDerivAt_id s).const_add a
  simpa using (((hf (a + s)).hasDerivAt).comp s h1).deriv

private lemma deriv_addR (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a : ℝ) :
    deriv (fun r => f (r + a)) = fun s => deriv f (s + a) := by
  funext s
  have h1 : HasDerivAt (fun r => r + a) 1 s := by simpa using (hasDerivAt_id s).add_const a
  simpa using (((hf (s + a)).hasDerivAt).comp s h1).deriv

private lemma deriv_subL (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a : ℝ) :
    deriv (fun r => f (a - r)) = fun s => -deriv f (a - s) := by
  funext s
  have h1 : HasDerivAt (fun r => a - r) (-1) s := by simpa using (hasDerivAt_id s).const_sub a
  simpa using (((hf (a - s)).hasDerivAt).comp s h1).deriv

private lemma deriv_subR (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a : ℝ) :
    deriv (fun r => f (r - a)) = fun s => deriv f (s - a) := by
  funext s
  have h1 : HasDerivAt (fun r => r - a) 1 s := by simpa using (hasDerivAt_id s).sub_const a
  simpa using (((hf (s - a)).hasDerivAt).comp s h1).deriv

private lemma hasDerivAt_addL (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a s : ℝ) :
    HasDerivAt (fun r => f (a + r)) (deriv f (a + s)) s := by
  have h1 : HasDerivAt (fun r => a + r) 1 s := by simpa using (hasDerivAt_id s).const_add a
  simpa using ((hf (a + s)).hasDerivAt).comp s h1

private lemma hasDerivAt_subL (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a s : ℝ) :
    HasDerivAt (fun r => f (a - r)) (-deriv f (a - s)) s := by
  have h1 : HasDerivAt (fun r => a - r) (-1) s := by simpa using (hasDerivAt_id s).const_sub a
  simpa using ((hf (a - s)).hasDerivAt).comp s h1

private lemma hasDerivAt_addR (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a s : ℝ) :
    HasDerivAt (fun r => f (r + a)) (deriv f (s + a)) s := by
  have h1 : HasDerivAt (fun r => r + a) 1 s := by simpa using (hasDerivAt_id s).add_const a
  simpa using ((hf (s + a)).hasDerivAt).comp s h1

private lemma hasDerivAt_subR (f : ℝ → ℝ) (hf : Differentiable ℝ f) (a s : ℝ) :
    HasDerivAt (fun r => f (r - a)) (deriv f (s - a)) s := by
  have h1 : HasDerivAt (fun r => r - a) 1 s := by simpa using (hasDerivAt_id s).sub_const a
  simpa using ((hf (s - a)).hasDerivAt).comp s h1

/-! ### Traveling Waves Solve the Wave Equation -/

/-- **Left-moving wave**: if `φ ∈ C²`, then `u(x,t) = φ(x + t)` solves `u_tt = u_xx`.
    Both second derivatives equal `φ''(x + t)`. -/
theorem forwardWave_isWaveSolution (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) :
    IsWaveSolution (fun p => φ (p.1 + p.2)) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv φ) := by
    have h := hφ.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at h
  intro p
  obtain ⟨x, t⟩ := p
  have htime : timeDeriv2 (fun p => φ (p.1 + p.2)) (x, t) = deriv (deriv φ) (x + t) := by
    simp only [timeDeriv2]
    rw [show (fun s => deriv (fun r => φ (x + r)) s) = (fun s => deriv φ (x + s)) from
      deriv_addL φ hd x]
    exact congr_fun (deriv_addL (deriv φ) hd' x) t
  have hspace : spaceDeriv2 (fun p => φ (p.1 + p.2)) (x, t) = deriv (deriv φ) (x + t) := by
    simp only [spaceDeriv2]
    rw [show (fun s => deriv (fun r => φ (r + t)) s) = (fun s => deriv φ (s + t)) from
      deriv_addR φ hd t]
    exact congr_fun (deriv_addR (deriv φ) hd' t) x
  rw [htime, hspace]

/-- **Right-moving wave**: if `φ ∈ C²`, then `u(x,t) = φ(x − t)` solves `u_tt = u_xx`.
    Both second derivatives equal `φ''(x − t)`. -/
theorem backwardWave_isWaveSolution (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) :
    IsWaveSolution (fun p => φ (p.1 - p.2)) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv φ) := by
    have h := hφ.differentiable_iteratedDeriv 1 (by norm_num)
    rwa [iteratedDeriv_one] at h
  intro p
  obtain ⟨x, t⟩ := p
  have htime : timeDeriv2 (fun p => φ (p.1 - p.2)) (x, t) = deriv (deriv φ) (x - t) := by
    simp only [timeDeriv2]
    rw [show (fun s => deriv (fun r => φ (x - r)) s) = (fun s => -deriv φ (x - s)) from
      deriv_subL φ hd x]
    have hHD : HasDerivAt (fun s => -deriv φ (x - s)) (deriv (deriv φ) (x - t)) t := by
      have h1 : HasDerivAt (fun s => x - s) (-1) t := by simpa using (hasDerivAt_id t).const_sub x
      simpa using (((hd' (x - t)).hasDerivAt).comp t h1).neg
    exact hHD.deriv
  have hspace : spaceDeriv2 (fun p => φ (p.1 - p.2)) (x, t) = deriv (deriv φ) (x - t) := by
    simp only [spaceDeriv2]
    rw [show (fun s => deriv (fun r => φ (r - t)) s) = (fun s => deriv φ (s - t)) from
      deriv_subR φ hd t]
    exact congr_fun (deriv_subR (deriv φ) hd' t) x
  rw [htime, hspace]

/-- **Superposition of traveling waves**: if `Φ, Ψ ∈ C²`, then
    `u(x,t) = Φ(x + t) + Ψ(x − t)` solves `u_tt = u_xx`. Both second derivatives equal
    `Φ''(x + t) + Ψ''(x − t)`. This is exactly the form d'Alembert's solution takes. -/
theorem travelingWaves_isWaveSolution (Φ Ψ : ℝ → ℝ)
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ) :
    IsWaveSolution (fun p => Φ (p.1 + p.2) + Ψ (p.1 - p.2)) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hΦd' : Differentiable ℝ (deriv Φ) := by
    have h := hΦ.differentiable_iteratedDeriv 1 (by norm_num); rwa [iteratedDeriv_one] at h
  have hΨd' : Differentiable ℝ (deriv Ψ) := by
    have h := hΨ.differentiable_iteratedDeriv 1 (by norm_num); rwa [iteratedDeriv_one] at h
  intro p
  obtain ⟨x, t⟩ := p
  have htime : timeDeriv2 (fun p => Φ (p.1 + p.2) + Ψ (p.1 - p.2)) (x, t)
      = deriv (deriv Φ) (x + t) + deriv (deriv Ψ) (x - t) := by
    simp only [timeDeriv2]
    -- inner first derivative `s ↦ Φ'(x+s) − Ψ'(x−s)`
    have hin : (fun s => deriv (fun r => Φ (x + r) + Ψ (x - r)) s)
        = fun s => deriv Φ (x + s) - deriv Ψ (x - s) := by
      funext s
      simpa using ((hasDerivAt_addL Φ hΦd x s).add (hasDerivAt_subL Ψ hΨd x s)).deriv
    rw [hin]
    have hout := (hasDerivAt_addL (deriv Φ) hΦd' x t).sub (hasDerivAt_subL (deriv Ψ) hΨd' x t)
    simpa using hout.deriv
  have hspace : spaceDeriv2 (fun p => Φ (p.1 + p.2) + Ψ (p.1 - p.2)) (x, t)
      = deriv (deriv Φ) (x + t) + deriv (deriv Ψ) (x - t) := by
    simp only [spaceDeriv2]
    have hin : (fun s => deriv (fun r => Φ (r + t) + Ψ (r - t)) s)
        = fun s => deriv Φ (s + t) + deriv Ψ (s - t) := by
      funext s
      simpa using ((hasDerivAt_addR Φ hΦd t s).add (hasDerivAt_subR Ψ hΨd t s)).deriv
    rw [hin]
    have hout := (hasDerivAt_addR (deriv Φ) hΦd' t x).add (hasDerivAt_subR (deriv Ψ) hΨd' t x)
    simpa using hout.deriv
  rw [htime, hspace]

/-! ### d'Alembert: Initial Condition -/

/-- **Initial position**: `u(x, 0) = g(x)`. The integral term vanishes at `t = 0`. -/
theorem dalembert_initial_pos (g h : ℝ → ℝ) (x : ℝ) : dalembert g h (x, 0) = g x := by
  simp [dalembert, intervalIntegral.integral_same]

/-! ### d'Alembert Solves the Wave Equation -/

/-- **Decomposition into traveling waves**: for `g ∈ C²`, `h ∈ C¹`, d'Alembert's solution is
    a superposition `Φ(x+t) + Ψ(x−t)` of two `C²` profiles, `Φ = (g+H)/2`, `Ψ = (g−H)/2`,
    where `H(a) = ∫_0^a h`. The integral term splits as `∫_{x−t}^{x+t} h = H(x+t) − H(x−t)`,
    and `H ∈ C²` because `H' = h ∈ C¹`. This is the structural core of all the d'Alembert
    theorems below. -/
private lemma dalembert_decomp (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    ∃ Φ Ψ : ℝ → ℝ, ContDiff ℝ 2 Φ ∧ ContDiff ℝ 2 Ψ ∧
      dalembert g h = fun p => Φ (p.1 + p.2) + Ψ (p.1 - p.2) := by
  have hhc : Continuous h := hh.continuous
  set H : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, h s with hHdef
  have hHderiv : deriv H = h := by
    rw [hHdef]; funext u; exact Continuous.deriv_integral h hhc 0 u
  have hHdiff : Differentiable ℝ H := by
    rw [hHdef]; exact fun u => (hhc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have hHC2 : ContDiff ℝ 2 H := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    exact ⟨hHdiff, fun hω => absurd hω (by simp), by rw [hHderiv]; exact hh⟩
  refine ⟨fun a => (g a + H a) / 2, fun a => (g a - H a) / 2,
    (hg.add hHC2).div_const 2, (hg.sub hHC2).div_const 2, ?_⟩
  funext p
  obtain ⟨x, t⟩ := p
  simp only [dalembert]
  have hsplit : (∫ s in (x - t)..(x + t), h s) = H (x + t) - H (x - t) := by
    simp only [hHdef]
    rw [eq_sub_iff_add_eq, add_comm,
      intervalIntegral.integral_add_adjacent_intervals
        (hhc.intervalIntegrable 0 (x - t)) (hhc.intervalIntegrable (x - t) (x + t))]
  rw [hsplit]; ring

/-- **Evans §2.4.1, Theorem (existence)**: for `g ∈ C²` and `h ∈ C¹`, d'Alembert's formula
    solves the wave equation `u_tt = u_xx`. Immediate from the traveling-wave decomposition
    and `travelingWaves_isWaveSolution`. -/
theorem dalembert_solves_wave (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    IsWaveSolution (dalembert g h) := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, hrw⟩ := dalembert_decomp g h hg hh
  rw [hrw]; exact travelingWaves_isWaveSolution Φ Ψ hΦ hΨ

/-- **Evans §2.4.1, Theorem 1(i), regularity**: for `g ∈ C²` and `h ∈ C¹`, d'Alembert's
    solution is `C²` on `ℝ × ℝ`. Each traveling-wave profile is `C²` and the maps
    `(x,t) ↦ x ± t` are smooth, so the composition and their sum are `C²`. -/
theorem dalembert_contDiff (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 2 (dalembert g h) := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, hrw⟩ := dalembert_decomp g h hg hh
  rw [hrw]
  exact (hΦ.comp (contDiff_fst.add contDiff_snd)).add (hΨ.comp (contDiff_fst.sub contDiff_snd))

/-- **Initial velocity**: `u_t(x, 0) = h(x)`. The `g`-terms' time derivatives cancel at
    `t = 0`, while the integral term contributes `½(h(x) + h(x)) = h(x)` by the FTC. -/
theorem dalembert_initial_vel (g h : ℝ → ℝ) (hg : Differentiable ℝ g) (hh : Continuous h)
    (x : ℝ) : timeDeriv (dalembert g h) (x, 0) = h x := by
  set H : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, h s with hHdef
  have hHderiv : deriv H = h := by
    rw [hHdef]; funext u; exact Continuous.deriv_integral h hh 0 u
  have hHdiff : Differentiable ℝ H := by
    rw [hHdef]; exact fun u => (hh.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  -- The time-slice of d'Alembert, with the integral term split via the antiderivative.
  have hslice : (fun s => dalembert g h (x, s))
      = fun s => (g (x + s) + g (x - s)) / 2 + (H (x + s) - H (x - s)) / 2 := by
    funext s
    simp only [dalembert]
    have hsplit : (∫ u in (x - s)..(x + s), h u) = H (x + s) - H (x - s) := by
      simp only [hHdef]
      rw [eq_sub_iff_add_eq, add_comm,
        intervalIntegral.integral_add_adjacent_intervals
          (hh.intervalIntegrable 0 (x - s)) (hh.intervalIntegrable (x - s) (x + s))]
    rw [hsplit]
  simp only [timeDeriv, hslice]
  have hA : HasDerivAt (fun s => (g (x + s) + g (x - s)) / 2)
      ((deriv g (x + 0) + -deriv g (x - 0)) / 2) 0 :=
    ((hasDerivAt_addL g hg x 0).add (hasDerivAt_subL g hg x 0)).div_const 2
  have hB : HasDerivAt (fun s => (H (x + s) - H (x - s)) / 2)
      ((deriv H (x + 0) - -deriv H (x - 0)) / 2) 0 :=
    ((hasDerivAt_addL H hHdiff x 0).sub (hasDerivAt_subL H hHdiff x 0)).div_const 2
  have hAB : HasDerivAt (fun s => (g (x + s) + g (x - s)) / 2 + (H (x + s) - H (x - s)) / 2)
      ((deriv g (x + 0) + -deriv g (x - 0)) / 2 + (deriv H (x + 0) - -deriv H (x - 0)) / 2) 0 :=
    hA.add hB
  rw [hAB.deriv, hHderiv]
  simp only [add_zero, sub_zero]
  ring

/-! ### Energy Methods (Evans §2.4.3)

The energy density `e = ½(u_t² + u_x²)` and flux `p = u_t · u_x` satisfy the local
conservation law `∂_t e = ∂_x p` for any wave solution (this is `u_t(u_tt − u_xx) = 0`
together with the symmetry of mixed partials). Integrating over space gives conservation of
the total energy `∫ e`, the basis for uniqueness and finite propagation speed.

We prove the local law for the traveling-wave solution `Φ(x+t) + Ψ(x−t)`, where the mixed
partials are manifestly symmetric, so the law holds with no analytic side conditions. -/

/-- Energy density `e(x,t) = ½(u_t² + u_x²)`. -/
noncomputable def energyDensity (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ((timeDeriv u p) ^ 2 + (spaceDeriv u p) ^ 2) / 2

/-- Energy flux `p(x,t) = u_t · u_x`. -/
noncomputable def energyFlux (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  timeDeriv u p * spaceDeriv u p

/-- First time derivative of a traveling-wave superposition: `∂_t[A(x+t)+B(x−t)] = A'(x+t) − B'(x−t)`. -/
private lemma timeDeriv_super (A B : ℝ → ℝ) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (p : ℝ × ℝ) :
    timeDeriv (fun q => A (q.1 + q.2) + B (q.1 - q.2)) p
      = deriv A (p.1 + p.2) - deriv B (p.1 - p.2) := by
  simp only [timeDeriv]
  simpa using ((hasDerivAt_addL A hA p.1 p.2).add (hasDerivAt_subL B hB p.1 p.2)).deriv

/-- First space derivative of a traveling-wave superposition: `∂_x[A(x+t)+B(x−t)] = A'(x+t) + B'(x−t)`. -/
private lemma spaceDeriv_super (A B : ℝ → ℝ) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (p : ℝ × ℝ) :
    spaceDeriv (fun q => A (q.1 + q.2) + B (q.1 - q.2)) p
      = deriv A (p.1 + p.2) + deriv B (p.1 - p.2) := by
  simp only [spaceDeriv]
  simpa using ((hasDerivAt_addR A hA p.2 p.1).add (hasDerivAt_subR B hB p.2 p.1)).deriv

/-- **Evans §2.4.3, local energy conservation**: for `Φ, Ψ ∈ C²`, the wave solution
    `u = Φ(x+t) + Ψ(x−t)` satisfies `∂_t e = ∂_x p`, where `e = ½(u_t² + u_x²)` is the energy
    density and `p = u_t·u_x` the flux. Integrating over `x` yields conservation of total
    energy `d/dt ∫ e = ∫ ∂_x p = 0`, the basis of the uniqueness theorem. -/
theorem travelingWaves_energy_conservation (Φ Ψ : ℝ → ℝ)
    (hΦ : ContDiff ℝ 2 Φ) (hΨ : ContDiff ℝ 2 Ψ) (p : ℝ × ℝ) :
    timeDeriv (energyDensity (fun q => Φ (q.1 + q.2) + Ψ (q.1 - q.2))) p
      = spaceDeriv (energyFlux (fun q => Φ (q.1 + q.2) + Ψ (q.1 - q.2))) p := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hΦd' : Differentiable ℝ (deriv Φ) := hΦ.differentiable_deriv_two
  have hΨd' : Differentiable ℝ (deriv Ψ) := hΨ.differentiable_deriv_two
  -- Energy density and flux as traveling-wave superpositions in the profiles `Φ'²`, `Ψ'²`.
  have hE : energyDensity (fun q => Φ (q.1 + q.2) + Ψ (q.1 - q.2))
      = fun q => (deriv Φ (q.1 + q.2)) ^ 2 + (deriv Ψ (q.1 - q.2)) ^ 2 := by
    funext q
    simp only [energyDensity, timeDeriv_super Φ Ψ hΦd hΨd q, spaceDeriv_super Φ Ψ hΦd hΨd q]
    ring
  have hF : energyFlux (fun q => Φ (q.1 + q.2) + Ψ (q.1 - q.2))
      = fun q => (deriv Φ (q.1 + q.2)) ^ 2 + -(deriv Ψ (q.1 - q.2)) ^ 2 := by
    funext q
    simp only [energyFlux, timeDeriv_super Φ Ψ hΦd hΨd q, spaceDeriv_super Φ Ψ hΦd hΨd q]
    ring
  rw [hE, hF,
    timeDeriv_super (fun a => (deriv Φ a) ^ 2) (fun a => (deriv Ψ a) ^ 2)
      (hΦd'.pow 2) (hΨd'.pow 2) p,
    spaceDeriv_super (fun a => (deriv Φ a) ^ 2) (fun a => -(deriv Ψ a) ^ 2)
      (hΦd'.pow 2) (hΨd'.pow 2).neg p]
  -- the backward profile's derivative: ∂(−Ψ'²) = −∂(Ψ'²)
  have hneg : deriv (fun a => -(deriv Ψ a) ^ 2) (p.1 - p.2)
      = -deriv (fun a => (deriv Ψ a) ^ 2) (p.1 - p.2) :=
    (((hΨd'.pow 2) (p.1 - p.2)).hasDerivAt.neg).deriv
  rw [hneg]; ring

/-- The energy density is nonnegative (it is `½` times a sum of squares). Together with
    energy conservation, `E ≥ 0` is what drives the uniqueness argument. -/
lemma energyDensity_nonneg (u : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : 0 ≤ energyDensity u p := by
  unfold energyDensity; positivity

/-- **Energy conservation for d'Alembert's solution**: for `g ∈ C²`, `h ∈ C¹`, the local
    conservation law `∂_t e = ∂_x p` holds for `u = dalembert g h`. A corollary of
    `travelingWaves_energy_conservation` via the superposition decomposition. -/
theorem dalembert_energy_conservation (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h)
    (p : ℝ × ℝ) :
    timeDeriv (energyDensity (dalembert g h)) p = spaceDeriv (energyFlux (dalembert g h)) p := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, hrw⟩ := dalembert_decomp g h hg hh
  rw [hrw]; exact travelingWaves_energy_conservation Φ Ψ hΦ hΨ p

/-! ### Uniqueness (Evans §2.4.3)

For the 1D Cauchy problem the solution is unique. Energy uniqueness on a bounded domain
needs `∫`-energy conservation (the same diff-under-integral that blocks the Heat chapter);
in 1D, however, uniqueness follows from a clean pointwise argument via the Riemann invariants
`u_t ± u_x`. For a traveling-wave solution `A(x+t) + B(x−t)`, zero Cauchy data forces both
`A' + B'` and `A' − B'` to vanish, hence `A`, `B` are constant and cancel. -/

/-- **Zero Cauchy data ⟹ zero solution** (traveling-wave form): if `A, B` are differentiable
    with `A + B ≡ 0` (zero initial position) and `A' − B' ≡ 0` (zero initial velocity), then
    `A(x+t) + B(x−t) ≡ 0`. -/
theorem travelingWave_eq_zero_of_zero_data (A B : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (hpos : ∀ x, A x + B x = 0) (hvel : ∀ x, deriv A x - deriv B x = 0) (p : ℝ × ℝ) :
    A (p.1 + p.2) + B (p.1 - p.2) = 0 := by
  -- Differentiating `A + B ≡ 0` gives `A' + B' ≡ 0`.
  have hsum : ∀ x, deriv A x + deriv B x = 0 := by
    intro x
    have h0 : HasDerivAt (fun y => A y + B y) (deriv A x + deriv B x) x :=
      (hA x).hasDerivAt.add (hB x).hasDerivAt
    have hz : HasDerivAt (fun y => A y + B y) 0 x := by
      rw [show (fun y => A y + B y) = fun _ => (0 : ℝ) from funext hpos]
      exact hasDerivAt_const x 0
    exact h0.unique hz
  -- Both Riemann invariants vanish, so `A'` and `B'` vanish.
  have hA0 : ∀ x, deriv A x = 0 := fun x => by have := hsum x; have := hvel x; linarith
  have hB0 : ∀ x, deriv B x = 0 := fun x => by have := hsum x; have := hvel x; linarith
  -- Hence `A`, `B` are constant and cancel by the initial condition at `0`.
  rw [is_const_of_deriv_eq_zero hA hA0 (p.1 + p.2) 0,
      is_const_of_deriv_eq_zero hB hB0 (p.1 - p.2) 0]
  exact hpos 0

/-- **Uniqueness among traveling-wave solutions**: two solutions `Φᵢ(x+t)+Ψᵢ(x−t)` with the
    same initial position and velocity coincide. Since (by the general-solution theorem) every
    `C²` solution of the 1D wave equation has this form, this is uniqueness for the Cauchy
    problem; in particular `dalembert` is the unique such solution of its data. -/
theorem travelingWaves_unique (Φ₁ Ψ₁ Φ₂ Ψ₂ : ℝ → ℝ)
    (hΦ₁ : Differentiable ℝ Φ₁) (hΨ₁ : Differentiable ℝ Ψ₁)
    (hΦ₂ : Differentiable ℝ Φ₂) (hΨ₂ : Differentiable ℝ Ψ₂)
    (hpos : ∀ x, Φ₁ x + Ψ₁ x = Φ₂ x + Ψ₂ x)
    (hvel : ∀ x, deriv Φ₁ x - deriv Ψ₁ x = deriv Φ₂ x - deriv Ψ₂ x) (p : ℝ × ℝ) :
    Φ₁ (p.1 + p.2) + Ψ₁ (p.1 - p.2) = Φ₂ (p.1 + p.2) + Ψ₂ (p.1 - p.2) := by
  -- derivatives of the difference profiles
  have hdΦ : ∀ x, deriv (fun x => Φ₁ x - Φ₂ x) x = deriv Φ₁ x - deriv Φ₂ x :=
    fun x => ((hΦ₁ x).hasDerivAt.sub (hΦ₂ x).hasDerivAt).deriv
  have hdΨ : ∀ x, deriv (fun x => Ψ₁ x - Ψ₂ x) x = deriv Ψ₁ x - deriv Ψ₂ x :=
    fun x => ((hΨ₁ x).hasDerivAt.sub (hΨ₂ x).hasDerivAt).deriv
  have key := travelingWave_eq_zero_of_zero_data
    (fun x => Φ₁ x - Φ₂ x) (fun x => Ψ₁ x - Ψ₂ x) (hΦ₁.sub hΦ₂) (hΨ₁.sub hΨ₂)
    (fun x => by simp only; linarith [hpos x])
    (fun x => by rw [hdΦ x, hdΨ x]; linarith [hvel x]) p
  simp only at key
  linarith [key]

/-! ### Finite Propagation Speed (Evans §2.4.3) -/

/-- **Domain of dependence / finite propagation speed**: `dalembert g h (x₀, t₀)` depends only
    on the initial data in the interval `[x₀ − t₀, x₀ + t₀]`. If two pairs of initial data agree
    there, the solutions agree at `(x₀, t₀)`. Disturbances propagate at speed at most `1`. -/
theorem dalembert_domain_of_dependence (g₁ h₁ g₂ h₂ : ℝ → ℝ) (x₀ t₀ : ℝ) (ht₀ : 0 ≤ t₀)
    (hg : ∀ y ∈ Set.Icc (x₀ - t₀) (x₀ + t₀), g₁ y = g₂ y)
    (hh : ∀ y ∈ Set.Icc (x₀ - t₀) (x₀ + t₀), h₁ y = h₂ y) :
    dalembert g₁ h₁ (x₀, t₀) = dalembert g₂ h₂ (x₀, t₀) := by
  have hle : x₀ - t₀ ≤ x₀ + t₀ := by linarith
  simp only [dalembert]
  rw [hg _ ⟨by linarith, le_refl _⟩, hg _ ⟨le_refl _, by linarith⟩,
    intervalIntegral.integral_congr (g := h₂)
      (fun y hy => hh y (by rwa [Set.uIcc_of_le hle] at hy))]
