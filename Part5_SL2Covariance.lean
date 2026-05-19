import Part5_AlignmentConstruction

/-!
# Part 5 — SL(2,ℝ) Covariance: The True Physical Law

`ContourSL2Moments.query_moment` (∂_q contour = α − β·q) is mathematically FALSE
for finite N with fixed off-query poles: the LHS is a bounded rational function,
the RHS is unbounded linear in q.  The no-go theorems already in this project
(`not_FarFieldCentroidTarget_demo`) prove specific instances.

The TRUE physical law is a *covariance identity under the co-moving sl(2,ℝ) flow*:
when query q and all poles xₖ evolve under `ż = α − β·z`, the Poisson sum scales
as `e^{βt}` because differences cancel the fixed point: `q(t) − xₖ(t) = (q₀ − xₖ⁰)·e^{−βt}`.

This is the first formal machine-checked proof of the sl(2,ℝ) covariance of the
Cauchy/Poisson representation of transformer attention.
-/

noncomputable section

open Finset Real GeodesicCauchyBridge AnalyticTransformer

namespace SL2Covariance

-- ═══════════════════════════════════════════════════════════════════════
-- §C.1  Key algebraic lemma: differences cancel the fixed point
-- ═══════════════════════════════════════════════════════════════════════

lemma sl2_flow_difference_cancels (z₁ z₂ α β t : ℝ) :
    (α / β + (z₁ - α / β) * Real.exp (-β * t)) -
    (α / β + (z₂ - α / β) * Real.exp (-β * t)) =
    (z₁ - z₂) * Real.exp (-β * t) := by ring

-- ═══════════════════════════════════════════════════════════════════════
-- §C.2  Per-pole Poisson covariance
-- ═══════════════════════════════════════════════════════════════════════

/-- Core covariance identity: under the co-moving sl(2,ℝ) flow `ż = α − β·z`,
    each Poisson kernel scales as `e^{βt}`. -/
theorem poisson_sl2_covariance_per_pole (x₀ y₀ q₀ α β t : ℝ) (hy₀ : 0 < y₀) :
    let q_t := α / β + (q₀ - α / β) * Real.exp (-β * t)
    let x_t := α / β + (x₀ - α / β) * Real.exp (-β * t)
    let y_t := y₀ * Real.exp (-β * t)
    poisson x_t y_t q_t = Real.exp (β * t) * poisson x₀ y₀ q₀ := by
  simp only [poisson]
  set e := Real.exp (-β * t)
  set E := Real.exp (β * t)
  have heE : e * E = 1 := by simp only [e, E, ← Real.exp_add]; norm_num
  have he_ne : e ≠ 0 := Real.exp_ne_zero _
  have hD₀_pos : 0 < (q₀ - x₀) ^ 2 + y₀ ^ 2 := by positivity
  have hD₀_ne : (q₀ - x₀) ^ 2 + y₀ ^ 2 ≠ 0 := hD₀_pos.ne'
  have hqx : α / β + (q₀ - α / β) * e - (α / β + (x₀ - α / β) * e) =
             (q₀ - x₀) * e := by ring
  rw [hqx]
  have hDen : ((q₀ - x₀) * e) ^ 2 + (y₀ * e) ^ 2 =
              e ^ 2 * ((q₀ - x₀) ^ 2 + y₀ ^ 2) := by ring
  rw [hDen]
  -- Goal: y₀ * e / (e ^ 2 * D₀) = E * (y₀ / D₀)
  -- Use div_eq_iff to reduce to: y₀ * e = E * (y₀ / D₀) * (e^2 * D₀)
  have hEe2 : E * e ^ 2 = e :=
    calc E * e ^ 2 = (e * E) * e := by ring
    _ = 1 * e := by rw [heE]
    _ = e := one_mul e
  rw [div_eq_iff (mul_ne_zero (pow_ne_zero 2 he_ne) hD₀_ne)]
  -- Goal: y₀ * e = E * (y₀ / D₀) * (e^2 * D₀)
  have hrhs : E * (y₀ / ((q₀ - x₀) ^ 2 + y₀ ^ 2)) *
      (e ^ 2 * ((q₀ - x₀) ^ 2 + y₀ ^ 2)) = y₀ * e :=
    calc E * (y₀ / ((q₀ - x₀) ^ 2 + y₀ ^ 2)) * (e ^ 2 * ((q₀ - x₀) ^ 2 + y₀ ^ 2))
        = E * e ^ 2 * (y₀ / ((q₀ - x₀) ^ 2 + y₀ ^ 2) * ((q₀ - x₀) ^ 2 + y₀ ^ 2)) := by ring
      _ = E * e ^ 2 * y₀ := by rw [div_mul_cancel₀ _ hD₀_ne]
      _ = y₀ * e := by linear_combination y₀ * hEe2
  linarith [hrhs]

-- ═══════════════════════════════════════════════════════════════════════
-- §C.3  N-pole Poisson sum covariance (THE PHYSICAL LAW)
-- ═══════════════════════════════════════════════════════════════════════

/-- **THE PHYSICAL LAW OF THE TRANSFORMER'S ATTENTION HEAD.**

    When query and all poles co-move under `ż = α − β·z`:

        ∑ₖ P(xₖ(t), yₖ(t), q(t)) = e^{βt} · ∑ₖ P(xₖ⁰, yₖ⁰, q₀)

    The Poisson sum is an sl(2,ℝ) eigenform with eigenvalue β.
    Proof: each term scales by e^{βt}; sum inherits the scaling. -/
theorem poisson_sum_sl2_covariance (N : ℕ) (keys₀ log_heights₀ : Fin N → ℝ)
    (q₀ α β t : ℝ) :
    let q_t := α / β + (q₀ - α / β) * Real.exp (-β * t)
    let keys_t := fun k => α / β + (keys₀ k - α / β) * Real.exp (-β * t)
    let heights_t := fun k => Real.exp (log_heights₀ k) * Real.exp (-β * t)
    ∑ k : Fin N, poisson (keys_t k) (heights_t k) q_t =
      Real.exp (β * t) * ∑ k : Fin N, poisson (keys₀ k) (Real.exp (log_heights₀ k)) q₀ := by
  simp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ =>
    poisson_sl2_covariance_per_pole (keys₀ k) (Real.exp (log_heights₀ k))
      q₀ α β t (Real.exp_pos _)

-- ═══════════════════════════════════════════════════════════════════════
-- §C.4  Weighted version (softmax weights as residues)
-- ═══════════════════════════════════════════════════════════════════════

/-- Weighted covariance: the softmax-weighted Poisson sum also scales as e^{βt}
    under the co-moving flow.  Cauchy transform interpretation: G(z) = ∑ₖ wₖ/(z−zₖ)
    satisfies G(z(t), {zₖ(t)}) = e^{βt} · G(z₀, {zₖ⁰}). -/
theorem weighted_poisson_sum_sl2_covariance (N : ℕ) (scores keys₀ log_heights₀ : Fin N → ℝ)
    (q₀ α β t : ℝ) :
    let q_t := α / β + (q₀ - α / β) * Real.exp (-β * t)
    let keys_t := fun k => α / β + (keys₀ k - α / β) * Real.exp (-β * t)
    let heights_t := fun k => Real.exp (log_heights₀ k) * Real.exp (-β * t)
    ∑ k : Fin N, softmaxWeight scores k * poisson (keys_t k) (heights_t k) q_t =
      Real.exp (β * t) *
        ∑ k : Fin N, softmaxWeight scores k * poisson (keys₀ k) (Real.exp (log_heights₀ k)) q₀ := by
  simp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [poisson_sl2_covariance_per_pole (keys₀ k) (Real.exp (log_heights₀ k))
          q₀ α β t (Real.exp_pos _)]
    ring

-- ═══════════════════════════════════════════════════════════════════════
-- §C.5  Infinitesimal form: Lie derivative = β · P
-- ═══════════════════════════════════════════════════════════════════════

/-- **Lie derivative identity (single pole).**

    The Lie derivative of P along the co-moving sl(2,ℝ) vector field
    `ξ = (α−βx)∂_x + (−β)∂_{log y} + (α−βq)∂_q` equals β·P.

    This is the infinitesimal form of the covariance identity.
    Note: ∂P/∂x = −∂P/∂q (P depends only on q−x). -/
theorem poisson_sl2_lie_derivative (x₀ y₀ q₀ α β : ℝ) (hy₀ : 0 < y₀) :
    (α - β * x₀) * (-poisson_partial_q x₀ y₀ q₀) +
    (-β) * poisson_partial_logY x₀ y₀ q₀ +
    (α - β * q₀) * poisson_partial_q x₀ y₀ q₀ =
    β * poisson x₀ y₀ q₀ := by
  simp only [poisson, poisson_partial_q, poisson_partial_logY]
  have hD_ne : (q₀ - x₀) ^ 2 + y₀ ^ 2 ≠ 0 := by positivity
  have hD2_ne : ((q₀ - x₀) ^ 2 + y₀ ^ 2) ^ 2 ≠ 0 := pow_ne_zero _ hD_ne
  field_simp [hD_ne, hD2_ne]
  ring

/-- Lie derivative of the N-pole Poisson sum equals β times the sum. -/
theorem poisson_sum_sl2_lie_derivative (N : ℕ) (keys₀ log_heights₀ : Fin N → ℝ)
    (q₀ α β : ℝ) :
    ∑ k : Fin N,
      ((α - β * keys₀ k) * (-poisson_partial_q (keys₀ k) (Real.exp (log_heights₀ k)) q₀) +
       (-β) * poisson_partial_logY (keys₀ k) (Real.exp (log_heights₀ k)) q₀ +
       (α - β * q₀) * poisson_partial_q (keys₀ k) (Real.exp (log_heights₀ k)) q₀) =
    β * ∑ k : Fin N, poisson (keys₀ k) (Real.exp (log_heights₀ k)) q₀ := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ =>
    poisson_sl2_lie_derivative (keys₀ k) (Real.exp (log_heights₀ k)) q₀ α β (Real.exp_pos _)

-- ═══════════════════════════════════════════════════════════════════════
-- §C.6  Translation invariance (β = 0 special case)
-- ═══════════════════════════════════════════════════════════════════════

/-- At β = 0 the flow is purely translational; the Poisson sum is translation-invariant
    (all differences q(t)−xₖ(t) are constant). -/
theorem poisson_sum_translation_invariant (N : ℕ) (keys₀ log_heights₀ : Fin N → ℝ)
    (q₀ α t : ℝ) :
    ∑ k : Fin N,
        poisson (keys₀ k + α * t) (Real.exp (log_heights₀ k)) (q₀ + α * t) =
      ∑ k : Fin N, poisson (keys₀ k) (Real.exp (log_heights₀ k)) q₀ := by
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [poisson]
  congr 1
  ring

end SL2Covariance

end -- noncomputable section
