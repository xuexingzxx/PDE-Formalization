import MyProject.Calculus

open MeasureTheory InnerProductSpace

/-!
# Transport Equation (Evans PDE, §2.1)

Formalizing the initial value problem for the homogeneous transport equation:

  (IVP)  u_t + b · Du = 0   in ℝⁿ × (0, ∞)
         u = g               on ℝⁿ × {t = 0}

The key insight: along any characteristic line `z(s) = (x + sb, t + s)`,
  d/ds [u(z(s))] = b · Du + u_t = 0
so `u` is constant on characteristics. Tracing back to `t = 0` gives u(x, t) = g(x − tb).

## References
* Evans, Lawrence C. *Partial Differential Equations*, 2nd ed., §2.1.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ### The PDE -/

/-- `u` satisfies the homogeneous transport equation `u_t + b · Du = 0` at every
    spacetime point, where `u_t` is `timeDerivative` and `b · Du = ⟪Du, b⟫` uses
    `spatialGradient`. -/
def IsTransportSolution (b : ℝⁿ) (u : ℝⁿ × ℝ → ℝ) : Prop :=
  ∀ p : ℝⁿ × ℝ, timeDerivative u p + ⟪spatialGradient u p, b⟫_ℝ = 0

/-! ### Characteristics -/

/-- The characteristic flow: the linear map `(x, t) ↦ x − t · b`.
    Characteristics of the equation are lines parallel to `(b, 1)` in `ℝⁿ⁺¹`. -/
noncomputable def charFlow (b : ℝⁿ) : ℝⁿ × ℝ →L[ℝ] ℝⁿ :=
  ContinuousLinearMap.fst ℝ ℝⁿ ℝ -
  (ContinuousLinearMap.snd ℝ ℝⁿ ℝ).smulRight b

@[simp]
lemma charFlow_apply (b x : ℝⁿ) (t : ℝ) : charFlow b (x, t) = x - t • b := by
  simp [charFlow]

/-- The characteristic direction `(b, 1)` is in the kernel of `charFlow b`. -/
lemma charFlow_direction_zero (b : ℝⁿ) : charFlow b (b, (1 : ℝ)) = 0 := by simp

/-! ### Solution Formula -/

/-- Evans' solution: `u(x, t) = g(x − tb)`, i.e., `g` at the foot of the characteristic. -/
noncomputable def evansFormula (b : ℝⁿ) (g : ℝⁿ → ℝ) : ℝⁿ × ℝ → ℝ :=
  g ∘ charFlow b

@[simp]
lemma evansFormula_apply (b : ℝⁿ) (g : ℝⁿ → ℝ) (x : ℝⁿ) (t : ℝ) :
    evansFormula b g (x, t) = g (x - t • b) := by simp [evansFormula]

/-! ### Main Theorems -/

/-- **Initial condition**: `u(x, 0) = g(x)`. -/
theorem evansFormula_initial (b : ℝⁿ) (g : ℝⁿ → ℝ) (x : ℝⁿ) :
    evansFormula b g (x, 0) = g x := by simp

/-- Regularity: `evansFormula b g` is differentiable whenever `g` is. -/
theorem evansFormula_differentiable (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g) :
    Differentiable ℝ (evansFormula b g) :=
  hg.comp (charFlow b).differentiable

/-- The spatial gradient of `evansFormula b g` at `p` equals the gradient of `g`
    pulled back to the foot of the characteristic.
    Proof: `x ↦ x − t·b` is a translation with derivative `id`, so by the chain rule
    for gradients, `∇_x[g(x−tb)] = ∇g(x−tb)`. -/
lemma spatialGradient_evansFormula (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g)
    (p : ℝⁿ × ℝ) :
    spatialGradient (evansFormula b g) p = gradient g (charFlow b p) := by
  obtain ⟨x, t⟩ := p
  simp only [spatialGradient, evansFormula, Function.comp, charFlow_apply]
  -- Goal: gradient (fun x => g (x - t • b)) x = gradient g (x - t • b)
  -- Translation y ↦ y - t·b has derivative id, so chain rule gives fderiv g at the foot.
  have hφ : HasFDerivAt (fun y : ℝⁿ => y - t • b) (ContinuousLinearMap.id ℝ ℝⁿ) x :=
    hasFDerivAt_sub_const (t • b)
  have hchain : HasFDerivAt (fun y : ℝⁿ => g (y - t • b)) (fderiv ℝ g (x - t • b)) x := by
    have h := hg.differentiableAt.hasFDerivAt.comp x hφ
    simpa [ContinuousLinearMap.comp_id] using h
  -- gradient = (toDual ℝ ℝⁿ).symm ∘ fderiv; both sides reduce to the same thing.
  simp only [gradient, hchain.fderiv]

/-- The time derivative of `evansFormula b g` at `p` equals `−⟪∇g(x−tb), b⟫`.
    Proof: by the chain rule, `∂_t[g(x−tb)] = ∇g(x−tb) · (−b) = −⟪∇g(x−tb), b⟫`. -/
lemma timeDerivative_evansFormula (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g)
    (p : ℝⁿ × ℝ) :
    timeDerivative (evansFormula b g) p = -⟪gradient g (charFlow b p), b⟫_ℝ := by
  obtain ⟨x, t⟩ := p
  simp only [timeDerivative, evansFormula, Function.comp, charFlow_apply]
  have hψ : HasDerivAt (fun s : ℝ => x - s • b) (-b) t := by
    simpa using (hasDerivAt_const t x).sub ((hasDerivAt_id t).smul_const b)
  have hchain : HasDerivAt (fun s => g (x - s • b)) (fderiv ℝ g (x - t • b) (-b)) t :=
    hg.differentiableAt.hasFDerivAt.comp_hasDerivAt t hψ
  rw [hchain.deriv, map_neg]
  congr 1
  exact (inner_gradient_left hg.differentiableAt).symm

/-- **Evans §2.1.1, Theorem 1**: `u(x, t) = g(x − tb)` solves the transport equation.

    **Proof**: The spatial gradient pulls back to `∇g(x−tb)` and the time derivative
    equals `−⟪∇g(x−tb), b⟫`, so their sum vanishes. -/
theorem evansFormula_solves_transport (b : ℝⁿ) (g : ℝⁿ → ℝ) (hg : Differentiable ℝ g) :
    IsTransportSolution b (evansFormula b g) := by
  intro p
  rw [timeDerivative_evansFormula b g hg p, spatialGradient_evansFormula b g hg p]
  simp [real_inner_comm]

/-! ## §2.1.2 Inhomogeneous Transport Equation -/

/-- `u` satisfies the inhomogeneous transport equation `u_t + b · Du = f`. -/
def IsInhomTransportSolution (b : ℝⁿ) (f : ℝⁿ × ℝ → ℝ) (u : ℝⁿ × ℝ → ℝ) : Prop :=
  ∀ p : ℝⁿ × ℝ, timeDerivative u p + ⟪spatialGradient u p, b⟫_ℝ = f p

/-- Duhamel's formula: `u(x,t) = g(x−tb) + ∫₀ᵗ f(x−(t−s)b, s) ds`.
    The first term solves the homogeneous equation; the integral corrects for the source `f`. -/
noncomputable def duhamelFormula (b : ℝⁿ) (g : ℝⁿ → ℝ) (f : ℝⁿ × ℝ → ℝ) :
    ℝⁿ × ℝ → ℝ :=
  fun p => g (p.1 - p.2 • b) + ∫ s in (0 : ℝ)..p.2, f (p.1 - (p.2 - s) • b, s)

/-- **Initial condition**: `u(x, 0) = g(x)`. The Duhamel integral vanishes at `t = 0`. -/
theorem duhamelFormula_initial (b : ℝⁿ) (g : ℝⁿ → ℝ) (f : ℝⁿ × ℝ → ℝ) (x : ℝⁿ) :
    duhamelFormula b g f (x, 0) = g x := by
  simp [duhamelFormula, intervalIntegral.integral_same]

/-- **Evans §2.1.2, Theorem 2**: Duhamel's formula solves the inhomogeneous transport equation.


    **Proof sketch**: Split `u = v + w` where `v(x,t) = g(x−tb)` and
    `w(x,t) = ∫₀ᵗ f(x−(t−s)b, s) ds`. We know `v_t + b·Dv = 0`. For `w`, the
    Leibniz rule gives `w_t = f(x,t) + ∫₀ᵗ ∂_t[f(x−(t−s)b,s)] ds` (FTC boundary term)
    and `b·Dw = ∫₀ᵗ b·∇f(x−(t−s)b,s) ds`. Since `∂_t[f(x−(t−s)b,s)] = −b·∇f(x−(t−s)b,s)`,
    the two integrals cancel and `w_t + b·Dw = f(x,t)`. -/
theorem duhamelFormula_solves (b : ℝⁿ) (g : ℝⁿ → ℝ) (f : ℝⁿ × ℝ → ℝ)
    (hg : Differentiable ℝ g) (hf : ContDiff ℝ 1 f) :
    IsInhomTransportSolution b f (duhamelFormula b g f) := by
  intro ⟨x, t⟩
  simp only [duhamelFormula, timeDerivative, spatialGradient]
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hchain : ∀ s : ℝ, HasDerivAt (fun t => f (x - (t - s) • b, s))
      (-⟪gradient (fun y => f (y, s)) (x - (t - s) • b), b⟫_ℝ) t := by
    intro s
    have hpath : HasDerivAt (fun t => x - (t - s) • b) (-b) t := by
      have h1 : HasDerivAt (fun t => (t - s) • b) b t := by
        simpa using ((hasDerivAt_id t).sub_const s).smul_const b
      convert h1.neg.const_add x using 2
    have hfs : Differentiable ℝ (fun y : ℝⁿ => f (y, s)) :=
      fun y => hf1.differentiableAt.comp y (by fun_prop)
    have hcomp := hfs.differentiableAt.hasFDerivAt.comp_hasDerivAt t hpath
    convert hcomp using 1
    rw [map_neg, inner_gradient_left hfs.differentiableAt]
  have hleibniz : HasDerivAt
      (fun t => ∫ s in (0:ℝ)..t, f (x - (t - s) • b, s))
      (f (x, t) + ∫ s in (0:ℝ)..t,
        (-⟪gradient (fun y => f (y, s)) (x - (t - s) • b), b⟫_ℝ)) t := by
    sorry
  have hg_deriv : HasDerivAt (fun t => g (x - t • b))
      (-⟪gradient g (x - t • b), b⟫_ℝ) t := by
    have hpath : HasDerivAt (fun t => x - t • b) (-b) t := by
      have h1 : HasDerivAt (fun t => t • b) b t := by
        simpa using (hasDerivAt_id t).smul_const b
      convert h1.neg.const_add x using 2
    have hcomp := hg.differentiableAt.hasFDerivAt.comp_hasDerivAt t hpath
    convert hcomp using 1
    rw [map_neg, inner_gradient_left hg.differentiableAt]
  have htime : HasDerivAt
      (fun t => g (x - t • b) + ∫ s in (0:ℝ)..t, f (x - (t - s) • b, s))
      ((-⟪gradient g (x - t • b), b⟫_ℝ) + (f (x, t) +
        ∫ s in (0:ℝ)..t, (-⟪gradient (fun y => f (y, s)) (x - (t - s) • b), b⟫_ℝ))) t :=
    hg_deriv.add hleibniz
  have hgrad_cont : Continuous (fun s => gradient (fun y => f (y, s)) (x - (t - s) • b)) := by
    simp only [gradient]
    apply (toDual ℝ ℝⁿ).symm.continuous.comp
    sorry
  have hspace : gradient (fun x =>
        g (x - t • b) + ∫ s in (0:ℝ)..t, f (x - (t - s) • b, s)) x =
      gradient g (x - t • b) +
      ∫ s in (0:ℝ)..t, gradient (fun y => f (y, s)) (x - (t - s) • b) := by
    have hg_fderiv : HasFDerivAt (fun x => g (x - t • b))
        (fderiv ℝ g (x - t • b)) x := by
      have hφ : HasFDerivAt (fun y : ℝⁿ => y - t • b)
          (ContinuousLinearMap.id ℝ ℝⁿ) x := hasFDerivAt_sub_const (t • b)
      have := hg.differentiableAt.hasFDerivAt.comp x hφ
      simpa [ContinuousLinearMap.comp_id] using this
    have hint_fderiv : HasFDerivAt
        (fun x => ∫ s in (0:ℝ)..t, f (x - (t - s) • b, s))
        (∫ s in (0:ℝ)..t,
          fderiv ℝ (fun y => f (y, s)) (x - (t - s) • b) ∘L
          ContinuousLinearMap.id ℝ ℝⁿ) x := by
      refine (intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
        (μ := MeasureTheory.volume)
        (F := fun x s => f (x - (t - s) • b, s))
        (F' := fun s => fderiv ℝ (fun y => f (y, s)) (x - (t - s) • b) ∘L
          ContinuousLinearMap.id ℝ ℝⁿ)
        (bound := fun s => ‖fderiv ℝ f (x - (t - s) • b, s)‖ * ‖b‖)
        (x₀ := x) (a := 0) (b := t)
        (Metric.ball_mem_nhds x one_pos)
        ?_ ?_ ?_ ?_ ?_ ?_).2
      · apply Filter.Eventually.of_forall; intro x'
        exact (hf1.continuous.comp (by fun_prop)).aestronglyMeasurable
      · exact (hf1.continuous.comp (by fun_prop)).continuousOn.intervalIntegrable
      · sorry
      · sorry
      · sorry
      · filter_upwards with s _
        have hφ : HasFDerivAt (fun y : ℝⁿ => y - (t - s) • b)
            (ContinuousLinearMap.id ℝ ℝⁿ) x := hasFDerivAt_sub_const _
        have hfs : HasFDerivAt (fun y : ℝⁿ => f (y, s))
            (fderiv ℝ (fun y => f (y, s)) (x - (t - s) • b))
            (x - (t - s) • b) :=
          (hf1.differentiableAt.comp (x - (t - s) • b)
            (differentiableAt_id.prodMk (differentiableAt_const s))).hasFDerivAt
        exact hfs.comp x hφ
    have hsum : HasFDerivAt
        (fun x => g (x - t • b) + ∫ s in (0:ℝ)..t, f (x - (t - s) • b, s))
        (fderiv ℝ g (x - t • b) +
          ∫ s in (0:ℝ)..t,
            fderiv ℝ (fun y => f (y, s)) (x - (t - s) • b) ∘L
            ContinuousLinearMap.id ℝ ℝⁿ) x := by
      have := hg_fderiv.add hint_fderiv
      simp only [ContinuousLinearMap.comp_id] at this ⊢
      exact this
    simp only [gradient]
    rw [hsum.fderiv]
    simp only [map_add, ContinuousLinearMap.comp_id]
    congr 1
    have htoDual := ContinuousLinearMap.intervalIntegral_comp_comm
      (μ := MeasureTheory.volume)
      ((toDual ℝ ℝⁿ).symm.toContinuousLinearMap)
      (f := fun s => fderiv ℝ (fun y => f (y, s)) (x - (t - s) • b))
      (a := (0:ℝ)) (b := t)
      (by sorry)
    convert htoDual.symm using 1
  rw [htime.deriv, hspace]
  simp only [inner_add_left, intervalIntegral.integral_neg]
  have hinner_int : ⟪∫ s in (0:ℝ)..t,
        gradient (fun y => f (y, s)) (x - (t - s) • b), b⟫_ℝ =
      ∫ s in (0:ℝ)..t,
        ⟪gradient (fun y => f (y, s)) (x - (t - s) • b), b⟫_ℝ := by
    have key := ContinuousLinearMap.intervalIntegral_comp_comm
      (μ := MeasureTheory.volume)
      (innerSL ℝ b : ℝⁿ →L[ℝ] ℝ)
      (f := fun s => gradient (fun y => f (y, s)) (x - (t - s) • b))
      (a := (0:ℝ)) (b := t)
      (hgrad_cont.continuousOn.intervalIntegrable)
    simp only [innerSL_apply_apply] at key
    rw [real_inner_comm, ← key]
    congr 1; ext s
    exact real_inner_comm _ _
  linarith [hinner_int]


/-! ### Uniqueness via Characteristics (TODO)

The idea: if `u` is C¹, solves the IVP, and `v = evansFormula b g`, then
  `w := u − v` solves the transport equation with zero initial data.
  For any fixed `(x, t)`, define `z(s) = w(x + sb, t + s)`.
  Then `z'(s) = timeDerivative w (x+sb, t+s) + ⟪spatialGradient w (x+sb, t+s), b⟫ = 0`,
  so `z` is constant. `z(0) = w(x, t)` and `z(−t) = w(x − tb, 0) = 0`, giving `w ≡ 0`. -/

theorem evansFormula_unique (b : ℝⁿ) (g : ℝⁿ → ℝ)
    (u : ℝⁿ × ℝ → ℝ)
    (hu_pde : IsTransportSolution b u)
    (hu_init : ∀ x : ℝⁿ, u (x, 0) = g x)
    (hu_diff : Differentiable ℝ u) :
    u = evansFormula b g := by
  have const_of_deriv_zero : ∀ (f : ℝ → ℝ), (∀ s, HasDerivAt f 0 s) →
      ∀ a c, f a = f c := by
    intro f hf a c
    have hdiff : Differentiable ℝ f := fun x => (hf x).differentiableAt
    have h1 : ∀ x, deriv f x ≤ 0 := fun x => le_of_eq (hf x).deriv
    have h1' : ∀ x, deriv (fun x => -f x) x ≤ 0 := fun x => by simp [(hf x).deriv]
    suffices h : ∀ x y, x ≤ y → f x = f y by
      rcases le_total a c with hac | hac
      · exact h a c hac
      · exact (h c a hac).symm
    intro x y hxy
    have hle := image_sub_le_mul_sub_of_deriv_le hdiff h1 hxy
    have hge := image_sub_le_mul_sub_of_deriv_le hdiff.neg h1' hxy
    simp only [Pi.neg_apply] at hge
    linarith
  funext ⟨x, t⟩
  set z : ℝ → ℝ := fun s => u (x + s • b, t + s)
  have hz_deriv : ∀ s, HasDerivAt z 0 s := by
    intro s
    have h1 : HasDerivAt (fun s => x + s • b) b s := by
      simpa using ((hasDerivAt_id s).smul_const b).const_add x
    have h2 : HasDerivAt (fun s => t + s) (1 : ℝ) s := by
      simpa using (hasDerivAt_id s).const_add t
    have hγ : HasDerivAt (fun s => (x + s • b, t + s)) (b, (1 : ℝ)) s :=
      h1.prodMk h2
    have hchain := hu_diff.differentiableAt.hasFDerivAt.comp_hasDerivAt s hγ
    have hdir : fderiv ℝ u (x + s • b, t + s) (b, (1 : ℝ)) =
        ⟪spatialGradient u (x + s • b, t + s), b⟫_ℝ +
        timeDerivative u (x + s • b, t + s) := by
      have hu_at := hu_diff.differentiableAt (x := (x + s • b, t + s))
      simp only [spatialGradient, timeDerivative]
      have hx' : HasFDerivAt (fun y => u (y, t + s))
          (fderiv ℝ u (x + s • b, t + s) ∘L ContinuousLinearMap.inl ℝ ℝⁿ ℝ) (x + s • b) :=
        hu_at.hasFDerivAt.comp (x + s • b) (hasFDerivAt_prodMk_left (x + s • b) (t + s))
      have ht' : HasDerivAt (fun r => u (x + s • b, r))
          (fderiv ℝ u (x + s • b, t + s) (0, 1)) (t + s) := by
        have hprod : HasFDerivAt (fun r : ℝ => (x + s • b, r))
            (ContinuousLinearMap.inr ℝ ℝⁿ ℝ) (t + s) :=
          hasFDerivAt_prodMk_right (x + s • b) (t + s)
        have := hu_at.hasFDerivAt.comp_hasDerivAt (t + s) hprod.hasDerivAt
        simp only [ContinuousLinearMap.inr_apply] at this
        exact this
      have hsplit : fderiv ℝ u (x + s • b, t + s) (b, (1 : ℝ)) =
          fderiv ℝ u (x + s • b, t + s) (b, 0) +
          fderiv ℝ u (x + s • b, t + s) (0, 1) := by
        rw [← map_add]; congr 1; simp
      have hspace : fderiv ℝ u (x + s • b, t + s) (b, 0) =
          ⟪gradient (fun y => u (y, t + s)) (x + s • b), b⟫_ℝ := by
        rw [inner_gradient_left hx'.differentiableAt, hx'.fderiv]
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
      rw [hsplit, hspace, ht'.deriv.symm]
    rw [hdir] at hchain
    have hpde := hu_pde (x + s • b, t + s)
    convert hchain using 1
    linarith
  have hz_const : ∀ s, z s = z (-t) :=
    fun s => const_of_deriv_zero z hz_deriv s (-t)
  have hz_neg_t : z (-t) = g (x - t • b) := by
    change u (x + -t • b, t + -t) = g (x - t • b)
    have h1 : x + -t • b = x - t • b := by
      simp [neg_smul, sub_eq_add_neg]
    have h2 : t + -t = (0 : ℝ) := add_neg_cancel t
    rw [h1, h2, hu_init]
  have hz_zero : z 0 = u (x, t) := by simp [z]
  simp only [evansFormula, Function.comp, charFlow_apply]
  rw [← hz_zero, hz_const 0, hz_neg_t]
