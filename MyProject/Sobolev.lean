import MyProject.Calculus

open MeasureTheory InnerProductSpace Set Topology
open scoped ContDiff ENNReal

/-!
# Sobolev Spaces (Evans PDE, §5.2)

This file lays the analytic foundations for Sobolev spaces, following Evans §5.2:

* `IsTestFunction U φ` — `φ ∈ C_c^∞(U)`: smooth, compactly supported, with support inside `U`.
* `IsWeakDerivInDir U e u v` — `v` is the weak derivative of `u` in the direction `e` on `U`,
  characterised by the integration-by-parts identity `∫ u ∂_e φ = - ∫ v φ` against every test
  function `φ` (Evans §5.2.1, Definition).
* `MemW1p U p u` — `u ∈ W^{1,p}(U)`: `u ∈ Lᵖ` together with weak derivatives in every coordinate
  direction, each lying in `Lᵖ`.

Key results proved here:

* `isWeakDerivInDir_of_contDiff` — a `C¹` function is weakly differentiable, with weak derivative
  equal to the classical one (the bridge between classical and weak calculus). Uses Mathlib's
  integration-by-parts theorem `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.
* `IsWeakDerivInDir.add`, `IsWeakDerivInDir.const_smul` — linearity of the weak derivative.
* `isWeakDerivInDir_ae_unique` — the weak derivative is unique almost everywhere on `U`. Uses the
  fundamental lemma of the calculus of variations
  (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
* `memW1p_of_contDiff_hasCompactSupport` — every smooth, compactly supported function lies in
  `W^{1,p}(U)` for all `p`, the prototypical example of a Sobolev function.

## References
* Evans, Lawrence C. *Partial Differential Equations*, 2nd ed., §5.2.
-/

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Sobolev

/-! ### Test functions -/

/-- `φ` is a test function on `U`: smooth, compactly supported, with `tsupport φ ⊆ U`.
This is Evans' space `C_c^∞(U)`. -/
def IsTestFunction (U : Set ℝⁿ) (φ : ℝⁿ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

namespace IsTestFunction

lemma contDiff {U : Set ℝⁿ} {φ : ℝⁿ → ℝ} (hφ : IsTestFunction U φ) :
    ContDiff ℝ ∞ φ := hφ.1

lemma hasCompactSupport {U : Set ℝⁿ} {φ : ℝⁿ → ℝ} (hφ : IsTestFunction U φ) :
    HasCompactSupport φ := hφ.2.1

lemma tsupport_subset {U : Set ℝⁿ} {φ : ℝⁿ → ℝ} (hφ : IsTestFunction U φ) :
    tsupport φ ⊆ U := hφ.2.2

lemma continuous {U : Set ℝⁿ} {φ : ℝⁿ → ℝ} (hφ : IsTestFunction U φ) :
    Continuous φ := hφ.contDiff.continuous

lemma differentiable {U : Set ℝⁿ} {φ : ℝⁿ → ℝ} (hφ : IsTestFunction U φ) :
    Differentiable ℝ φ := hφ.contDiff.differentiable (by norm_num)

/-- The directional derivative `x ↦ ∂_e φ(x)` of a test function is continuous. -/
lemma continuous_dirDeriv {U : Set ℝⁿ} {φ : ℝⁿ → ℝ} (hφ : IsTestFunction U φ) (e : ℝⁿ) :
    Continuous (fun x => fderiv ℝ φ x e) :=
  (hφ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The directional derivative `x ↦ ∂_e φ(x)` of a test function has compact support. -/
lemma hasCompactSupport_dirDeriv {U : Set ℝⁿ} {φ : ℝⁿ → ℝ} (hφ : IsTestFunction U φ) (e : ℝⁿ) :
    HasCompactSupport (fun x => fderiv ℝ φ x e) :=
  hφ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) e

end IsTestFunction

/-- If `w` is locally integrable and `φ` is a test function, then `w · φ` is integrable. -/
lemma integrable_mul_testFunction {U : Set ℝⁿ} {w φ : ℝⁿ → ℝ}
    (hw : LocallyIntegrable w volume) (hφ : IsTestFunction U φ) :
    Integrable (fun x => w x * φ x) volume :=
  hw.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ.hasCompactSupport

/-- If `w` is locally integrable and `φ` is a test function, then `w · ∂_e φ` is integrable. -/
lemma integrable_mul_dirDeriv_testFunction {U : Set ℝⁿ} {w φ : ℝⁿ → ℝ} (e : ℝⁿ)
    (hw : LocallyIntegrable w volume) (hφ : IsTestFunction U φ) :
    Integrable (fun x => w x * fderiv ℝ φ x e) volume :=
  hw.integrable_smul_right_of_hasCompactSupport (hφ.continuous_dirDeriv e)
    (hφ.hasCompactSupport_dirDeriv e)

/-! ### Weak derivatives -/

/-- `v` is the **weak derivative of `u` in the direction `e`** on the open set `U`, defined (Evans
§5.2.1) by the integration-by-parts identity
`∫ u(x) ∂_e φ(x) dx = - ∫ v(x) φ(x) dx` for every test function `φ ∈ C_c^∞(U)`. -/
def IsWeakDerivInDir (U : Set ℝⁿ) (e : ℝⁿ) (u v : ℝⁿ → ℝ) : Prop :=
  ∀ φ : ℝⁿ → ℝ, IsTestFunction U φ →
    ∫ x, u x * fderiv ℝ φ x e = - ∫ x, v x * φ x

/-- **Classical ⟹ weak.** A `C¹` function `u` is weakly differentiable in every direction `e`, and
its weak derivative is its classical directional derivative `x ↦ ∂_e u(x) = fderiv ℝ u x e`.
This is the bridge between classical and weak calculus, proved by integration by parts
(`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`); the boundary term vanishes because `φ`
has compact support. -/
theorem isWeakDerivInDir_of_contDiff (U : Set ℝⁿ) (e : ℝⁿ) {u : ℝⁿ → ℝ}
    (hu : ContDiff ℝ 1 u) :
    IsWeakDerivInDir U e u (fun x => fderiv ℝ u x e) := by
  intro φ hφ
  have hu_diff : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hu_cont : Continuous u := hu.continuous
  have hdu_cont : Continuous (fun x => fderiv ℝ u x e) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- The three integrands are continuous and compactly supported (the test function `φ` or its
  -- derivative localises each product), hence integrable.
  have hf'g : Integrable (fun x => fderiv ℝ u x e * φ x) volume :=
    (hdu_cont.mul hφ.continuous).integrable_of_hasCompactSupport hφ.hasCompactSupport.mul_left
  have hfg' : Integrable (fun x => u x * fderiv ℝ φ x e) volume :=
    (hu_cont.mul (hφ.continuous_dirDeriv e)).integrable_of_hasCompactSupport
      (hφ.hasCompactSupport_dirDeriv e).mul_left
  have hfg : Integrable (fun x => u x * φ x) volume :=
    (hu_cont.mul hφ.continuous).integrable_of_hasCompactSupport hφ.hasCompactSupport.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun x _ => hu_diff x) (fun x _ => hφ.differentiable x)

/-! ### Linearity of the weak derivative -/

/-- The weak derivative is additive: if `v₁, v₂` are weak `e`-derivatives of `u₁, u₂`, then
`v₁ + v₂` is a weak `e`-derivative of `u₁ + u₂`. Requires local integrability to split integrals. -/
theorem IsWeakDerivInDir.add {U : Set ℝⁿ} {e : ℝⁿ} {u₁ u₂ v₁ v₂ : ℝⁿ → ℝ}
    (hu₁ : LocallyIntegrable u₁ volume) (hu₂ : LocallyIntegrable u₂ volume)
    (hv₁ : LocallyIntegrable v₁ volume) (hv₂ : LocallyIntegrable v₂ volume)
    (h₁ : IsWeakDerivInDir U e u₁ v₁) (h₂ : IsWeakDerivInDir U e u₂ v₂) :
    IsWeakDerivInDir U e (fun x => u₁ x + u₂ x) (fun x => v₁ x + v₂ x) := by
  intro φ hφ
  have e₁ := h₁ φ hφ
  have e₂ := h₂ φ hφ
  have hsplit_lhs : ∫ x, (u₁ x + u₂ x) * fderiv ℝ φ x e
      = (∫ x, u₁ x * fderiv ℝ φ x e) + ∫ x, u₂ x * fderiv ℝ φ x e := by
    simp_rw [add_mul]
    exact integral_add (integrable_mul_dirDeriv_testFunction e hu₁ hφ)
      (integrable_mul_dirDeriv_testFunction e hu₂ hφ)
  have hsplit_rhs : ∫ x, (v₁ x + v₂ x) * φ x
      = (∫ x, v₁ x * φ x) + ∫ x, v₂ x * φ x := by
    simp_rw [add_mul]
    exact integral_add (integrable_mul_testFunction hv₁ hφ)
      (integrable_mul_testFunction hv₂ hφ)
  rw [hsplit_lhs, hsplit_rhs, e₁, e₂, neg_add]

/-- The weak derivative is homogeneous: if `v` is a weak `e`-derivative of `u`, then `c • v` is a
weak `e`-derivative of `c • u`. -/
theorem IsWeakDerivInDir.const_smul {U : Set ℝⁿ} {e : ℝⁿ} {u v : ℝⁿ → ℝ} (c : ℝ)
    (h : IsWeakDerivInDir U e u v) :
    IsWeakDerivInDir U e (fun x => c * u x) (fun x => c * v x) := by
  intro φ hφ
  have he := h φ hφ
  have hl : ∫ x, (c * u x) * fderiv ℝ φ x e = c * ∫ x, u x * fderiv ℝ φ x e := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  have hr : ∫ x, (c * v x) * φ x = c * ∫ x, v x * φ x := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [hl, hr, he, mul_neg]

/-- The weak-derivative relation only depends on `u` and `v` up to almost-everywhere equality,
so it descends to `Lᵖ` equivalence classes. -/
theorem IsWeakDerivInDir.congr_ae {U : Set ℝⁿ} {e : ℝⁿ} {u u' v v' : ℝⁿ → ℝ}
    (hu : u =ᵐ[volume] u') (hv : v =ᵐ[volume] v')
    (h : IsWeakDerivInDir U e u v) : IsWeakDerivInDir U e u' v' := by
  intro φ hφ
  have hlhs : ∫ x, u' x * fderiv ℝ φ x e = ∫ x, u x * fderiv ℝ φ x e :=
    integral_congr_ae (hu.symm.mul (ae_eq_refl _))
  have hrhs : ∫ x, v' x * φ x = ∫ x, v x * φ x :=
    integral_congr_ae (hv.symm.mul (ae_eq_refl _))
  rw [hlhs, hrhs]; exact h φ hφ

/-- **Product rule with a smooth function** (Evans §5.2.3). If `v` is the weak `e`-derivative of `u`
and `ψ` is smooth, then `ψ · u` has weak `e`-derivative `ψ · v + (∂_e ψ) · u`. Proved by applying
the weak-derivative identity for `u` to the test function `ψ · φ` and expanding `∂_e(ψφ)` with the
Leibniz rule for `fderiv`. -/
theorem IsWeakDerivInDir.mul_smooth {U : Set ℝⁿ} {e : ℝⁿ} {u v ψ : ℝⁿ → ℝ}
    (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume)
    (hψ : ContDiff ℝ ∞ ψ) (h : IsWeakDerivInDir U e u v) :
    IsWeakDerivInDir U e (fun x => ψ x * u x)
      (fun x => ψ x * v x + fderiv ℝ ψ x e * u x) := by
  intro φ hφ
  have hψc : Continuous ψ := hψ.continuous
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hdψc : Continuous (fun x => fderiv ℝ ψ x e) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- `ψ · φ` is again a test function.
  have hψφ : IsTestFunction U (fun x => ψ x * φ x) :=
    ⟨hψ.mul hφ.contDiff, hφ.hasCompactSupport.mul_left,
      (tsupport_mul_subset_right (f := ψ) (g := φ)).trans hφ.tsupport_subset⟩
  -- Leibniz rule for the directional derivative of `ψ · φ`.
  have hLeibniz : ∀ x, fderiv ℝ (fun y => ψ y * φ y) x e
      = ψ x * fderiv ℝ φ x e + fderiv ℝ ψ x e * φ x := by
    intro x
    rw [fderiv_fun_mul (hψd x) (hφ.differentiable x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  -- The three integrable pieces (loc-integrable times continuous compact-support).
  have iA : Integrable (fun x => u x * (ψ x * fderiv ℝ φ x e)) volume :=
    hu.integrable_smul_right_of_hasCompactSupport (hψc.mul (hφ.continuous_dirDeriv e))
      (hφ.hasCompactSupport_dirDeriv e).mul_left
  have iB : Integrable (fun x => u x * (fderiv ℝ ψ x e * φ x)) volume :=
    hu.integrable_smul_right_of_hasCompactSupport (hdψc.mul hφ.continuous)
      hφ.hasCompactSupport.mul_left
  have iC : Integrable (fun x => v x * (ψ x * φ x)) volume :=
    hv.integrable_smul_right_of_hasCompactSupport (hψc.mul hφ.continuous)
      hφ.hasCompactSupport.mul_left
  -- Apply the weak-derivative identity for `u` to the test function `ψ · φ`, then split.
  have hkey := h (fun x => ψ x * φ x) hψφ
  have hsplit : (∫ x, u x * (ψ x * fderiv ℝ φ x e)) + ∫ x, u x * (fderiv ℝ ψ x e * φ x)
      = -∫ x, v x * (ψ x * φ x) := by
    rw [← integral_add iA iB, ← hkey]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hLeibniz]; ring)
  -- Re-assemble into the goal.
  have hgoalL : ∫ x, (ψ x * u x) * fderiv ℝ φ x e = ∫ x, u x * (ψ x * fderiv ℝ φ x e) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hgoalR : ∫ x, (ψ x * v x + fderiv ℝ ψ x e * u x) * φ x
      = (∫ x, v x * (ψ x * φ x)) + ∫ x, u x * (fderiv ℝ ψ x e * φ x) := by
    have hfun : (fun x => (ψ x * v x + fderiv ℝ ψ x e * u x) * φ x)
        = fun x => v x * (ψ x * φ x) + u x * (fderiv ℝ ψ x e * φ x) := by
      funext x; ring
    rw [hfun]; exact integral_add iC iB
  rw [hgoalL, hgoalR]
  linarith [hsplit]

/-! ### Uniqueness of the weak derivative -/

/-- **Uniqueness of the weak derivative (a.e.).** If `v₁` and `v₂` are both weak `e`-derivatives of
`u` on the open set `U`, then they agree almost everywhere on `U`. Proved via the fundamental lemma
of the calculus of variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) applied to the
difference `v₁ - v₂`. -/
theorem isWeakDerivInDir_ae_unique {U : Set ℝⁿ} (hU : IsOpen U) {e : ℝⁿ} {u v₁ v₂ : ℝⁿ → ℝ}
    (hv₁ : LocallyIntegrable v₁ volume) (hv₂ : LocallyIntegrable v₂ volume)
    (h₁ : IsWeakDerivInDir U e u v₁) (h₂ : IsWeakDerivInDir U e u v₂) :
    ∀ᵐ x ∂volume, x ∈ U → v₁ x = v₂ x := by
  have key : ∀ g : ℝⁿ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g x • (v₁ x - v₂ x) = 0 := by
    intro g hg hgc hgsub
    have ht : IsTestFunction U g := ⟨hg, hgc, hgsub⟩
    have e₁ := h₁ g ht
    have e₂ := h₂ g ht
    have hvv : ∫ x, v₁ x * g x = ∫ x, v₂ x * g x := by
      have h12 : -∫ x, v₁ x * g x = -∫ x, v₂ x * g x := by rw [← e₁, ← e₂]
      linarith
    have hint1 : Integrable (fun x => g x * v₁ x) volume :=
      hv₁.integrable_smul_left_of_hasCompactSupport ht.continuous ht.hasCompactSupport
    have hint2 : Integrable (fun x => g x * v₂ x) volume :=
      hv₂.integrable_smul_left_of_hasCompactSupport ht.continuous ht.hasCompactSupport
    calc ∫ x, g x • (v₁ x - v₂ x)
        = ∫ x, (g x * v₁ x - g x * v₂ x) := by simp_rw [smul_eq_mul, mul_sub]
      _ = (∫ x, g x * v₁ x) - ∫ x, g x * v₂ x := integral_sub hint1 hint2
      _ = (∫ x, v₁ x * g x) - ∫ x, v₂ x * g x := by simp_rw [mul_comm]
      _ = 0 := by rw [hvv]; ring
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => v₁ x - v₂ x) ((hv₁.sub hv₂).locallyIntegrableOn U) key
  filter_upwards [hae] with x hx
  intro hxU
  exact sub_eq_zero.mp (hx hxU)

/-! ### The Sobolev space `W^{1,p}` -/

/-- `u ∈ W^{1,p}(U)` (Evans §5.2.2): `u ∈ Lᵖ(U)` and in every coordinate direction there is a weak
derivative which also lies in `Lᵖ(U)`. The coordinate direction `i` is the standard basis vector
`EuclideanSpace.single i 1`. -/
structure MemW1p (U : Set ℝⁿ) (p : ℝ≥0∞) (u : ℝⁿ → ℝ) : Prop where
  /-- `u` itself is `p`-integrable on `U`. -/
  memLp : MemLp u p (volume.restrict U)
  /-- In each coordinate direction there is a weak derivative lying in `Lᵖ(U)`. -/
  exists_weakDeriv : ∀ i : Fin n, ∃ v : ℝⁿ → ℝ,
    IsWeakDerivInDir U (EuclideanSpace.single i (1 : ℝ)) u v ∧ MemLp v p (volume.restrict U)

/-- **A smooth, compactly supported function belongs to `W^{1,p}(U)` for every `p`.** This is the
basic example of a Sobolev function: its weak derivatives are its classical partial derivatives
(`isWeakDerivInDir_of_contDiff`), and a continuous compactly supported function is in `Lᵖ` for all
`p` (`Continuous.memLp_of_hasCompactSupport`). -/
theorem memW1p_of_contDiff_hasCompactSupport (U : Set ℝⁿ) (p : ℝ≥0∞) {u : ℝⁿ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hsupp : HasCompactSupport u) :
    MemW1p U p u where
  memLp := (hu.continuous.memLp_of_hasCompactSupport hsupp).restrict U
  exists_weakDeriv := fun i => by
    refine ⟨fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)), ?_, ?_⟩
    · exact isWeakDerivInDir_of_contDiff U _ (hu.of_le (by norm_num))
    · have hcont : Continuous (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) :=
        (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hcs : HasCompactSupport (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) :=
        hsupp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
      exact (hcont.memLp_of_hasCompactSupport hcs).restrict U

/-! ### Closedness of the weak derivative under limits (towards completeness) -/

open Filter

/-- If `wₖ → w` in `L¹` on the (compact) support of a continuous, compactly supported weight `g`,
then `∫ wₖ · g → ∫ w · g`. Integration against a fixed compactly supported weight is continuous for
`L¹`-on-compacts convergence; this is the analytic engine behind closedness of weak derivatives. -/
lemma tendsto_integral_mul_of_tendsto_setIntegral_abs
    {wₖ : ℕ → ℝⁿ → ℝ} {w g : ℝⁿ → ℝ}
    (hwkloc : ∀ k, LocallyIntegrable (wₖ k) volume) (hwloc : LocallyIntegrable w volume)
    (hg : Continuous g) (hgcs : HasCompactSupport g)
    (hconv : Tendsto (fun k => ∫ x in tsupport g, |wₖ k x - w x|) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x, wₖ k x * g x) atTop (nhds (∫ x, w x * g x)) := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgcs
  have hKmeas : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
  -- Products and differences are integrable.
  have iwk : ∀ k, Integrable (fun x => wₖ k x * g x) volume := fun k =>
    (hwkloc k).integrable_smul_right_of_hasCompactSupport hg hgcs
  have iw : Integrable (fun x => w x * g x) volume :=
    hwloc.integrable_smul_right_of_hasCompactSupport hg hgcs
  have ih : ∀ k, Integrable (fun x => (wₖ k x - w x) * g x) volume := fun k =>
    ((hwkloc k).sub hwloc).integrable_smul_right_of_hasCompactSupport hg hgcs
  have hdiff : ∀ k, (∫ x, wₖ k x * g x) - ∫ x, w x * g x = ∫ x, (wₖ k x - w x) * g x := by
    intro k; rw [← integral_sub (iwk k) iw]; congr 1; funext x; ring
  -- Pointwise/norm bound: `‖∫ (wₖ-w) g‖ ≤ C · ∫_{tsupp g} |wₖ-w|`.
  have hbound : ∀ k, ‖∫ x, (wₖ k x - w x) * g x‖ ≤ C * ∫ x in tsupport g, |wₖ k x - w x| := by
    intro k
    have hzero : ∀ x ∉ tsupport g, ‖(wₖ k x - w x) * g x‖ = 0 := by
      intro x hx; rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, norm_zero]
    have iRHS : IntegrableOn (fun x => C * |wₖ k x - w x|) (tsupport g) volume :=
      (((hwkloc k).sub hwloc).integrableOn_isCompact hgcs).abs.const_mul C
    have hpt : ∀ x ∈ tsupport g, ‖(wₖ k x - w x) * g x‖ ≤ C * |wₖ k x - w x| := by
      intro x _
      calc ‖(wₖ k x - w x) * g x‖ = |wₖ k x - w x| * |g x| := by
              rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |wₖ k x - w x| * C := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              rw [← Real.norm_eq_abs]; exact hC x
        _ = C * |wₖ k x - w x| := mul_comm _ _
    calc ‖∫ x, (wₖ k x - w x) * g x‖
        ≤ ∫ x, ‖(wₖ k x - w x) * g x‖ := norm_integral_le_integral_norm _
      _ = ∫ x in tsupport g, ‖(wₖ k x - w x) * g x‖ :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      _ ≤ ∫ x in tsupport g, C * |wₖ k x - w x| :=
            setIntegral_mono_on (ih k).norm.integrableOn iRHS hKmeas hpt
      _ = C * ∫ x in tsupport g, |wₖ k x - w x| := integral_const_mul C _
  -- Squeeze the difference to `0`, then add back the constant limit.
  have hsqnorm : Tendsto (fun k => ‖∫ x, (wₖ k x - w x) * g x‖) atTop (nhds 0) :=
    squeeze_zero (fun k => norm_nonneg _) hbound (by simpa using hconv.const_mul C)
  have hsq : Tendsto (fun k => ∫ x, (wₖ k x - w x) * g x) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hsqnorm
  have hsub : Tendsto (fun k => (∫ x, wₖ k x * g x) - ∫ x, w x * g x) atTop (nhds 0) := by
    simpa only [hdiff] using hsq
  simpa using hsub.add_const (∫ x, w x * g x)

/-- **Closedness of the weak derivative under `L¹`-on-compacts limits.** If each `vₖ` is a weak
`e`-derivative of `uₖ`, and `uₖ → u`, `vₖ → v` in `L¹` on every compact set, then `v` is a weak
`e`-derivative of `u`. This is the analytic cornerstone of completeness of `W^{1,p}`: it lets one
pass to the limit in the defining integration-by-parts identity. -/
theorem isWeakDerivInDir_of_tendsto_L1 {U : Set ℝⁿ} {e : ℝⁿ} {u v : ℝⁿ → ℝ}
    {uₖ vₖ : ℕ → ℝⁿ → ℝ}
    (hweak : ∀ k, IsWeakDerivInDir U e (uₖ k) (vₖ k))
    (hukloc : ∀ k, LocallyIntegrable (uₖ k) volume) (huloc : LocallyIntegrable u volume)
    (hvkloc : ∀ k, LocallyIntegrable (vₖ k) volume) (hvloc : LocallyIntegrable v volume)
    (hu : ∀ K : Set ℝⁿ, IsCompact K →
      Tendsto (fun k => ∫ x in K, |uₖ k x - u x|) atTop (nhds 0))
    (hv : ∀ K : Set ℝⁿ, IsCompact K →
      Tendsto (fun k => ∫ x in K, |vₖ k x - v x|) atTop (nhds 0)) :
    IsWeakDerivInDir U e u v := by
  intro φ hφ
  have hL : Tendsto (fun k => ∫ x, uₖ k x * fderiv ℝ φ x e) atTop
      (nhds (∫ x, u x * fderiv ℝ φ x e)) :=
    tendsto_integral_mul_of_tendsto_setIntegral_abs hukloc huloc
      (hφ.continuous_dirDeriv e) (hφ.hasCompactSupport_dirDeriv e)
      (hu _ (hφ.hasCompactSupport_dirDeriv e))
  have hR : Tendsto (fun k => ∫ x, vₖ k x * φ x) atTop (nhds (∫ x, v x * φ x)) :=
    tendsto_integral_mul_of_tendsto_setIntegral_abs hvkloc hvloc
      hφ.continuous hφ.hasCompactSupport (hv _ hφ.hasCompactSupport)
  have heq : ∀ k, ∫ x, uₖ k x * fderiv ℝ φ x e = -∫ x, vₖ k x * φ x := fun k => hweak k φ hφ
  have hRneg : Tendsto (fun k => ∫ x, uₖ k x * fderiv ℝ φ x e) atTop
      (nhds (-∫ x, v x * φ x)) := by
    simpa only [← heq] using hR.neg
  exact tendsto_nhds_unique hL hRneg

end Sobolev
