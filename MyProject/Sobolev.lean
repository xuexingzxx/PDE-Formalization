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

end Sobolev
