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

/-! ### d'Alembert: Initial Condition -/

/-- **Initial position**: `u(x, 0) = g(x)`. The integral term vanishes at `t = 0`. -/
theorem dalembert_initial_pos (g h : ℝ → ℝ) (x : ℝ) : dalembert g h (x, 0) = g x := by
  simp [dalembert, intervalIntegral.integral_same]
