import Part5_SL2Covariance
import Part5_WitnessConstruction

/-!
# Part 5 — Co-moving transformer: exact geodesic scaling

## The core answer to "but its doable right?"

**The frozen path is closed.**  `contourVF_query` is a bounded rational function of q;
`α − β·q` is unbounded linear.  Formally: for any fixed pole config, there exists q
at which the sl(2) form exceeds every possible frozen-partial bound (`§E.5`).

**The co-moving path is already proved — exactly, not asymptotically.**

`poisson_sum_sl2_covariance` gives exact equality for every finite N, every finite t:
    ∑ₖ P(xₖ(t), yₖ(t), q(t)) = exp(β·t) · ∑ₖ P(xₖ(0), yₖ(0), q(0))

Theorems in this file:
- §E.1 `comoving_one_step_exact`     — one co-moving step, proved (= SL2Covariance)
- §E.2 `comoving_steps_compose`      — co-moving steps compose: one-parameter group
- §E.3 `comoving_query_velocity_is_sl2` — query velocity = α−β·q (HasDerivAt)
- §E.4 `comoving_*_satisfies_cauchyVF`  — cauchyPoissonVF IS that velocity
- §E.5 `frozen_partial_single_pole_bound` + `frozen_partial_neq_sl2_linear`
        — impossibility: bounded rational ≠ unbounded linear

## Summary

The "open obligation" of constructing an IsCauchyPoissonVF witness from cauchyResidualVF
is answered in two parts:
1. **Impossibility (frozen case)**: the frozen partial derivative cannot equal α−β·q
   as functions of q (different function classes). `§E.5` makes this Lean-formal.
2. **Positive (co-moving case)**: the co-moving transformer's query velocity IS α−β·q
   exactly (it's the definition of the sl(2) ODE). `Part5_WitnessConstruction.cauchyPoissonVF_is_witness`
   formalises this: the correct witness is cauchyPoissonVF, whose dq-component is
   defined as the sl(2) generator. The co-moving law (§W.3) justifies why that definition
   is physically correct — not "contourVF_query equals α−β·q" (false), but "the
   co-moving query velocity equals α−β·q" (proved).
-/

noncomputable section

open Finset Real AnalyticTransformer SL2Covariance GeodesicCauchyBridge WitnessConstruction

namespace ComovingEuler

-- ═══════════════════════════════════════════════════════════════════════
-- §E.1  One co-moving step is exact (direct from SL2Covariance)
-- ═══════════════════════════════════════════════════════════════════════

/-- One exact co-moving sl(2) step = `poisson_sum_sl2_covariance`. -/
theorem comoving_one_step_exact (N : ℕ) (keys₀ log_heights₀ : Fin N → ℝ) (q₀ α β t : ℝ) :
    ∑ k : Fin N,
      poisson (α / β + (keys₀ k - α / β) * Real.exp (-β * t))
              (Real.exp (log_heights₀ k) * Real.exp (-β * t))
              (α / β + (q₀ - α / β) * Real.exp (-β * t)) =
    Real.exp (β * t) * ∑ k : Fin N,
      poisson (keys₀ k) (Real.exp (log_heights₀ k)) q₀ :=
  poisson_sum_sl2_covariance N keys₀ log_heights₀ q₀ α β t

-- ═══════════════════════════════════════════════════════════════════════
-- §E.2  Co-moving steps form a one-parameter group
-- ═══════════════════════════════════════════════════════════════════════

private lemma neg_mul_add (β s t : ℝ) : -β * (s + t) = -β * s + -β * t := by ring

/-- Two co-moving steps at times s, t compose to a single step at time s+t. -/
theorem comoving_steps_compose (N : ℕ) (keys₀ log_heights₀ : Fin N → ℝ) (q₀ α β s t : ℝ) :
    ∑ k : Fin N,
      poisson
        (α/β + (α/β + (keys₀ k - α/β) * Real.exp (-β * s) - α/β) * Real.exp (-β * t))
        (Real.exp (log_heights₀ k) * Real.exp (-β * s) * Real.exp (-β * t))
        (α/β + (α/β + (q₀ - α/β) * Real.exp (-β * s) - α/β) * Real.exp (-β * t)) =
    Real.exp (β * (s + t)) * ∑ k : Fin N,
      poisson (keys₀ k) (Real.exp (log_heights₀ k)) q₀ := by
  -- reduce to poisson_sum_sl2_covariance at time s+t
  have key_eq : ∀ k : Fin N,
      α/β + (α/β + (keys₀ k - α/β) * Real.exp (-β*s) - α/β) * Real.exp (-β*t) =
      α/β + (keys₀ k - α/β) * Real.exp (-β*(s+t)) := fun k => by
    simp only [neg_mul_add, Real.exp_add]; ring
  have q_eq :
      α/β + (α/β + (q₀ - α/β) * Real.exp (-β*s) - α/β) * Real.exp (-β*t) =
      α/β + (q₀ - α/β) * Real.exp (-β*(s+t)) := by
    simp only [neg_mul_add, Real.exp_add]; ring
  have lh_eq : ∀ k : Fin N,
      Real.exp (log_heights₀ k) * Real.exp (-β*s) * Real.exp (-β*t) =
      Real.exp (log_heights₀ k) * Real.exp (-β*(s+t)) := fun k => by
    simp only [neg_mul_add, Real.exp_add]; ring
  simp_rw [key_eq, q_eq, lh_eq]
  have h := poisson_sum_sl2_covariance N keys₀ log_heights₀ q₀ α β (s+t)
  simp only [show β * (s + t) = β * s + β * t from by ring, Real.exp_add] at h ⊢
  linarith

-- ═══════════════════════════════════════════════════════════════════════
-- §E.3  Query velocity under co-moving flow = sl(2) generator
-- ═══════════════════════════════════════════════════════════════════════

/-- The instantaneous velocity of the query under the exact co-moving sl(2) flow is α−β·q₀.
    Proved by differentiating the exact orbit `q(t) = α/β + (q₀−α/β)·exp(−βt)`. -/
theorem comoving_query_velocity_is_sl2 (q₀ α β : ℝ) (hβ : β ≠ 0) :
    HasDerivAt (fun t => α / β + (q₀ - α / β) * Real.exp (-β * t)) (α - β * q₀) 0 := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-β * t)) (-β) 0 := by
    have hβt : HasDerivAt (fun t => β * t) β 0 := by
      simpa [mul_comm] using (hasDerivAt_id 0).mul_const β
    have hneg : HasDerivAt (fun t => -β * t) (-β) 0 := by
      simpa [Function.comp, neg_mul, one_mul] using (hasDerivAt_neg' _).comp (0 : ℝ) hβt
    simpa [Function.comp, Real.exp_zero, zero_mul, one_mul] using
      (Real.hasDerivAt_exp _).comp (0 : ℝ) hneg
  have hscaled := hexp.const_mul (q₀ - α / β)
  have hfull := (hasDerivAt_const 0 (α / β)).add hscaled
  simp only [add_zero, Real.exp_zero, mul_one] at hfull
  convert hfull using 1
  field_simp [hβ]
  ring

-- ═══════════════════════════════════════════════════════════════════════
-- §E.4  cauchyPoissonVF at dq and dy = the co-moving velocities
-- ═══════════════════════════════════════════════════════════════════════

variable {N D : ℕ} [NeZero N]

/-- `cauchyPoissonVF h dq = α − β·h[dq]` = the co-moving query velocity. -/
theorem comoving_query_channel_satisfies_cauchyVF (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyPoissonVF dq dy scores keys log_heights h dq =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq := by
  rw [cauchyPoissonVF_eq_dq, cauchyVF_query_matches_sl2]

/-- `cauchyPoissonVF h dy = −β` = the co-moving log-height velocity. -/
theorem comoving_bandwidth_channel_satisfies_cauchyVF (dq dy : Fin D) (hne : dq ≠ dy)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyPoissonVF dq dy scores keys log_heights h dy =
      -sl2Beta scores log_heights := by
  rw [cauchyPoissonVF_eq_dy _ _ hne, cauchyVF_logBandwidth_matches_sl2]

-- ═══════════════════════════════════════════════════════════════════════
-- §E.5  Impossibility: frozen partial ≠ sl(2) linear form
-- ═══════════════════════════════════════════════════════════════════════

/-- The linear form `α − β·q` is unbounded below for `β > 0`. -/
theorem linear_form_unbounded (α β M : ℝ) (hβ : 0 < β) :
    ∃ q : ℝ, α - β * q < -M := ⟨(α + M + 1) / β, by field_simp; linarith⟩

/-- `|poisson_partial_q x y q| ≤ 1/y²` — frozen partial is bounded by inverse square height.
    Proof: `2y|q−x| ≤ (q−x)²+y²` (AM-GM) → `|P'_q| ≤ 1/((q−x)²+y²) ≤ 1/y²`. -/
theorem frozen_partial_single_pole_bound (x y q : ℝ) (hy : 0 < y) :
    |poisson_partial_q x y q| ≤ y⁻¹ ^ 2 := by
  simp only [poisson_partial_q]
  set D2 := ((q - x) ^ 2 + y ^ 2) with hD2_def
  have hD2 : 0 < D2 := by positivity
  have amgm : 2 * y * |q - x| ≤ D2 := by
    rw [hD2_def]; nlinarith [sq_nonneg (|q - x| - y), sq_abs (q - x)]
  have hy2 : y ^ 2 ≤ D2 := by rw [hD2_def]; nlinarith [sq_nonneg (q - x)]
  rw [show -2 * y * (q - x) / D2 ^ 2 = -(2 * y * (q - x) / D2 ^ 2) from by ring]
  rw [abs_neg, abs_div, abs_of_pos (pow_pos hD2 2)]
  rw [inv_pow, ← one_div]
  rw [div_le_div_iff (pow_pos hD2 2) (by positivity)]
  -- goal: |2 * y * (q - x)| * y ^ 2 ≤ 1 * D2 ^ 2
  have hab : |2 * y * (q - x)| = 2 * y * |q - x| := by
    rw [abs_mul, abs_mul, abs_of_pos (by linarith), abs_of_pos hy]
  rw [hab, one_mul]
  have h1 : 2 * y * |q - x| * y ^ 2 ≤ D2 * y ^ 2 := by nlinarith [sq_nonneg y]
  have h2 : D2 * y ^ 2 ≤ D2 ^ 2 := by nlinarith [sq_nonneg D2]
  linarith

/-- The sum of frozen partials is bounded. -/
theorem frozen_partial_sum_bounded (N : ℕ) (keys : Fin N → ℝ) (log_heights : Fin N → ℝ)
    (q : ℝ) :
    |∑ k : Fin N, poisson_partial_q (keys k) (Real.exp (log_heights k)) q| ≤
      ∑ k : Fin N, (Real.exp (log_heights k))⁻¹ ^ 2 :=
  (abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun k _ =>
      frozen_partial_single_pole_bound _ _ _ (Real.exp_pos _))

/-- **Impossibility**: at some `q`, the sl(2) linear form exceeds the frozen-partial bound.
    Hence `∑ₖ P'_q(xₖ,yₖ,q) ≠ α − β·q` as functions of `q`. -/
theorem frozen_partial_neq_sl2_linear (N : ℕ) [NeZero N] (keys : Fin N → ℝ)
    (log_heights : Fin N → ℝ) (α β : ℝ) (hβ : 0 < β) :
    ∃ q : ℝ,
      ∑ k : Fin N, (Real.exp (log_heights k))⁻¹ ^ 2 < |α - β * q| := by
  obtain ⟨q, hq⟩ := linear_form_unbounded α β
    (∑ k : Fin N, (Real.exp (log_heights k))⁻¹ ^ 2) hβ
  refine ⟨q, ?_⟩
  have hpos : 0 ≤ ∑ k : Fin N, (Real.exp (log_heights k))⁻¹ ^ 2 :=
    Finset.sum_nonneg fun k _ => by positivity
  have hneg : α - β * q < 0 := by linarith
  rw [abs_of_neg hneg]
  linarith

end ComovingEuler

end -- noncomputable section
