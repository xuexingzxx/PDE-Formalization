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

/-- **Evans §2.4.1, Theorem (existence)**: for `g ∈ C²` and `h ∈ C¹`, d'Alembert's formula
    solves the wave equation `u_tt = u_xx`.

    **Proof**: let `H(a) = ∫_0^a h` be an antiderivative of `h`. Splitting the integral,
    `∫_{x−t}^{x+t} h = H(x+t) − H(x−t)`, rewrites d'Alembert as the traveling-wave
    superposition `Φ(x+t) + Ψ(x−t)` with `Φ = (g+H)/2`, `Ψ = (g−H)/2`. Both are `C²`
    (`H ∈ C²` since `H' = h ∈ C¹`), so `travelingWaves_isWaveSolution` applies. -/
theorem dalembert_solves_wave (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    IsWaveSolution (dalembert g h) := by
  have hhc : Continuous h := hh.continuous
  -- Antiderivative of `h`.
  set H : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, h s with hHdef
  have hHderiv : deriv H = h := by
    rw [hHdef]; funext u; exact Continuous.deriv_integral h hhc 0 u
  have hHdiff : Differentiable ℝ H := by
    rw [hHdef]; exact fun u => (hhc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt
  have hHC2 : ContDiff ℝ 2 H := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨hHdiff, fun hω => absurd hω (by simp), ?_⟩
    rw [hHderiv]; exact hh
  -- The two traveling-wave profiles.
  have hΦ : ContDiff ℝ 2 (fun a => (g a + H a) / 2) := (hg.add hHC2).div_const 2
  have hΨ : ContDiff ℝ 2 (fun a => (g a - H a) / 2) := (hg.sub hHC2).div_const 2
  -- d'Alembert as a superposition of a forward and a backward wave.
  have hrewrite : dalembert g h
      = fun p => (fun a => (g a + H a) / 2) (p.1 + p.2)
          + (fun a => (g a - H a) / 2) (p.1 - p.2) := by
    funext p
    obtain ⟨x, t⟩ := p
    simp only [dalembert]
    have hsplit : (∫ s in (x - t)..(x + t), h s) = H (x + t) - H (x - t) := by
      simp only [hHdef]
      rw [eq_sub_iff_add_eq, add_comm,
        intervalIntegral.integral_add_adjacent_intervals
          (hhc.intervalIntegrable 0 (x - t)) (hhc.intervalIntegrable (x - t) (x + t))]
    rw [hsplit]; ring
  rw [hrewrite]
  exact travelingWaves_isWaveSolution _ _ hΦ hΨ

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
