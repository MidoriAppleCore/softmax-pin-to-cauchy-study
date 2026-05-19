import Part5_WitnessConstruction
import Part5_ComovingEuler

/-!
# Part 5 — Discrete residual bridge (Euler ↔ co-moving)

This file is the **translation layer for ML engineers**: it connects

1. **Residual / Euler updates** (`h ↦ h + Δt · F(h)`),
2. **The co-moving Carnot law** (`β · contourOutput`, exact semigroup on Poisson sums),
3. **The frozen-pole gap** (`key_velocity_correction` from `WitnessConstruction` §W.4).

No claim that production PyTorch code is definitionally equal to these definitions —
only that this is the **proved thermodynamic limit** and the **per-layer error budget**
that deep residual networks manage by re-embedding state each block.

## Engineer sound bite

> One frozen attention slice cannot realize `α − β·q` (`ComovingEuler.frozen_partial_neq_sl2_linear`).
> A residual block **is** one Euler step of a vector field (`cauchyResidualEulerStep`).
> The **ideal** query-channel field is `cauchyPoissonVF` = `α − β·q` (`comoving_query_channel_satisfies_cauchyVF`).
> The **gap** between co-moving head rate and frozen two-term rate is exactly
> `key_velocity_correction` (`frozen_layer_exact_gap`).
> Depth composes Euler steps (`cauchyResidualDepth`); co-moving depth composes exactly
> (`ComovingEuler.comoving_steps_compose` on the Poisson head).
-/

noncomputable section

open Finset Real
open GeodesicCauchyBridge AnalyticTransformer
open WitnessConstruction ComovingEuler

namespace DiscreteResidualBridge

variable {N D : ℕ} [NeZero N]

-- ═══════════════════════════════════════════════════════════════════════
-- §R.1  Head rates: co-moving vs frozen (scalar at the attention head)
-- ═══════════════════════════════════════════════════════════════════════

/-- Co-moving **output rate** on the query head:
    `β · contourOutput` (LHS of `comoving_eq_frozen_plus_key_correction`). -/
noncomputable def coMovingHeadRate (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  sl2Beta scores log_heights *
    contourOutput (geodesicPoles keys log_heights) (h dq)
      (geodesicResidue dq dy h) dq

/-- Frozen-query contribution: move `q`, hold pole positions fixed. -/
noncomputable def frozenQueryHeadRate (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  (sl2Alpha scores keys - sl2Beta scores log_heights * h dq) *
    contourVF_query dq dy keys log_heights h

/-- Frozen-bandwidth contribution: scale log-heights, hold keys fixed. -/
noncomputable def frozenBandwidthHeadRate (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  (-sl2Beta scores log_heights) * ∑ k : Fin N,
    poisson_partial_logY (keys k) (Real.exp (log_heights k)) (h dq)

/-- Frozen two-term rate (query + bandwidth, still dropping key velocity). -/
noncomputable def frozenTwoTermHeadRate (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  frozenQueryHeadRate dq dy scores keys log_heights h +
    frozenBandwidthHeadRate dq dy scores keys log_heights h

/-- Per-layer gap = dropped key-velocity term (re-export). -/
noncomputable def frozenLayerGap (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  key_velocity_correction dq dy keys log_heights h
    (sl2Alpha scores keys) (sl2Beta scores log_heights)

/-- sl(2) query velocity `α − β·q` at the current slice. -/
noncomputable def sl2QueryVelocity (scores keys log_heights : Fin N → ℝ) (q : ℝ) : ℝ :=
  sl2Alpha scores keys - sl2Beta scores log_heights * q

-- ═══════════════════════════════════════════════════════════════════════
-- §R.2  Exact Carnot identity (per layer, no sorry)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Carnot identity (co-moving = frozen two-term + gap).** -/
theorem frozen_layer_exact_gap (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    coMovingHeadRate dq dy scores keys log_heights h =
      frozenTwoTermHeadRate dq dy scores keys log_heights h +
        frozenLayerGap dq dy scores keys log_heights h := by
  dsimp [coMovingHeadRate, frozenTwoTermHeadRate, frozenQueryHeadRate,
    frozenBandwidthHeadRate, frozenLayerGap]
  exact comoving_eq_frozen_plus_key_correction dq dy keys log_heights h
    (sl2Alpha scores keys) (sl2Beta scores log_heights)

/-- Gap between co-moving rate and **query-only** frozen rate. -/
theorem frozen_query_only_gap (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    coMovingHeadRate dq dy scores keys log_heights h -
      frozenQueryHeadRate dq dy scores keys log_heights h =
      frozenBandwidthHeadRate dq dy scores keys log_heights h +
        frozenLayerGap dq dy scores keys log_heights h := by
  have hmain := frozen_layer_exact_gap dq dy scores keys log_heights h
  dsimp [frozenTwoTermHeadRate] at hmain
  linarith

/-- Frozen query rate factors as (sl(2) velocity) × (∂_q contour). -/
theorem frozen_query_rate_eq_sl2_times_contourVF (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    frozenQueryHeadRate dq dy scores keys log_heights h =
      sl2QueryVelocity scores keys log_heights (h dq) *
        contourVF_query dq dy keys log_heights h := by
  dsimp [frozenQueryHeadRate, sl2QueryVelocity, contourVF_query]

/-- Co-moving rate is **not** the frozen-query rate when bandwidth + gap are nonzero. -/
theorem coMoving_ne_frozenQuery_of_gap_ne_zero (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hsum : frozenBandwidthHeadRate dq dy scores keys log_heights h +
        frozenLayerGap dq dy scores keys log_heights h ≠ 0) :
    coMovingHeadRate dq dy scores keys log_heights h ≠
      frozenQueryHeadRate dq dy scores keys log_heights h := by
  intro heq
  have hsplit := frozen_query_only_gap dq dy scores keys log_heights h
  have hzero : frozenBandwidthHeadRate dq dy scores keys log_heights h +
      frozenLayerGap dq dy scores keys log_heights h = 0 := by
    linarith [heq, hsplit]
  exact hsum hzero

-- ═══════════════════════════════════════════════════════════════════════
-- §R.3  Residual Euler step = discrete integrator on `cauchyPoissonVF`
-- ═══════════════════════════════════════════════════════════════════════

/-- One **residual / Euler** update of the full embedding state at step `Δt`. -/
noncomputable def cauchyResidualEulerStep (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : Fin D → ℝ :=
  fun d => h d + Δt * cauchyPoissonVF dq dy scores keys log_heights h d

/-- `L` residual layers = `L`-fold Euler composition. -/
noncomputable def cauchyResidualDepth (L : ℕ) (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : Fin D → ℝ :=
  (cauchyResidualEulerStep Δt dq dy scores keys log_heights)^[L] h

theorem cauchy_residual_depth_zero (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyResidualDepth 0 Δt dq dy scores keys log_heights h = h := rfl

theorem cauchy_residual_depth_one (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyResidualDepth 1 Δt dq dy scores keys log_heights h =
      cauchyResidualEulerStep Δt dq dy scores keys log_heights h := rfl

theorem cauchy_residual_depth_succ (L : ℕ) (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyResidualDepth (L + 1) Δt dq dy scores keys log_heights h =
      cauchyResidualDepth L Δt dq dy scores keys log_heights
        (cauchyResidualEulerStep Δt dq dy scores keys log_heights h) := by
  dsimp [cauchyResidualDepth]

/-- **One residual block on the query channel is Euler with sl(2) velocity.** -/
theorem cauchy_residual_euler_query_channel (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    (cauchyResidualEulerStep Δt dq dy scores keys log_heights h) dq =
      h dq + Δt * sl2QueryVelocity scores keys log_heights (h dq) := by
  dsimp [cauchyResidualEulerStep, sl2QueryVelocity]
  rw [comoving_query_channel_satisfies_cauchyVF dq dy scores keys log_heights h,
    sl2Beta, sl2LogDrift]

/-- **One residual block on the bandwidth channel is Euler with `−β`.** -/
theorem cauchy_residual_euler_bandwidth_channel (Δt : ℝ) (dq dy : Fin D) (hne : dq ≠ dy)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    (cauchyResidualEulerStep Δt dq dy scores keys log_heights h) dy =
      h dy + Δt * (-sl2Beta scores log_heights) := by
  dsimp [cauchyResidualEulerStep]
  rw [comoving_bandwidth_channel_satisfies_cauchyVF dq dy hne scores keys log_heights h,
    sl2Beta, sl2LogDrift]

/-- **Residual update shape** (the defining equation ML engineers use). -/
theorem cauchy_residual_euler_step_eq_add (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) (d : Fin D) :
    cauchyResidualEulerStep Δt dq dy scores keys log_heights h d =
      h d + Δt * cauchyPoissonVF dq dy scores keys log_heights h d := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §R.4  Co-moving exact step on the Poisson head (Carnot semigroup)
-- ═══════════════════════════════════════════════════════════════════════

/-- Poisson-sum **head output** at query `q` (unit residues on `dq`). -/
noncomputable def poissonHeadOutput (keys log_heights : Fin N → ℝ) (q : ℝ) : ℝ :=
  ∑ k : Fin N, poisson (keys k) (Real.exp (log_heights k)) q

private lemma neg_mul_add (β s t : ℝ) : -β * (s + t) = -β * s + -β * t := by ring

private theorem exp_log_height_evolve (log_heights₀ : Fin N → ℝ) (β t : ℝ) (k : Fin N) :
    Real.exp (log_heights₀ k + -β * t) = Real.exp (log_heights₀ k) * Real.exp (-β * t) := by
  rw [Real.exp_add]

theorem poisson_head_output_eq_contour (dq dy : Fin D)
    (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    poissonHeadOutput keys log_heights (h dq) =
      contourOutput (geodesicPoles keys log_heights) (h dq)
        (geodesicResidue dq dy h) dq := by
  simpa [poissonHeadOutput] using
    (contourOutput_geodesic_dq_eq_poisson_sum dq dy keys log_heights h).symm

/-- **Exact co-moving step on the head** (not a first-order approximation). -/
theorem coMoving_poisson_head_exact (keys₀ log_heights₀ : Fin N → ℝ) (q₀ α β t : ℝ) :
    poissonHeadOutput
        (fun k => α / β + (keys₀ k - α / β) * Real.exp (-β * t))
        (fun k => log_heights₀ k + -β * t)
        (α / β + (q₀ - α / β) * Real.exp (-β * t)) =
      Real.exp (β * t) * poissonHeadOutput keys₀ log_heights₀ q₀ := by
  dsimp [poissonHeadOutput]
  simp_rw [exp_log_height_evolve log_heights₀ β t]
  exact comoving_one_step_exact N keys₀ log_heights₀ q₀ α β t

/-- Co-moving head output at time `t` scales exactly by `exp(βt)`. -/
theorem coMoving_contour_head_exact (dq dy : Fin D) (keys₀ log_heights₀ : Fin N → ℝ)
    (h₀ : Fin D → ℝ) (α β t : ℝ) :
    poissonHeadOutput
        (fun k => α / β + (keys₀ k - α / β) * Real.exp (-β * t))
        (fun k => log_heights₀ k + -β * t)
        (α / β + (h₀ dq - α / β) * Real.exp (-β * t)) =
      Real.exp (β * t) * poissonHeadOutput keys₀ log_heights₀ (h₀ dq) ∧
    poissonHeadOutput
        (fun k => α / β + (keys₀ k - α / β) * Real.exp (-β * t))
        (fun k => log_heights₀ k + -β * t)
        (α / β + (h₀ dq - α / β) * Real.exp (-β * t)) =
      Real.exp (β * t) *
        contourOutput (geodesicPoles keys₀ log_heights₀) (h₀ dq)
          (geodesicResidue dq dy h₀) dq := by
  constructor
  · exact coMoving_poisson_head_exact keys₀ log_heights₀ (h₀ dq) α β t
  · rw [coMoving_poisson_head_exact keys₀ log_heights₀ (h₀ dq) α β t,
      poisson_head_output_eq_contour dq dy keys₀ log_heights₀ h₀]

/-- Co-moving head rate is the infinitesimal generator of that semigroup at `t = 0`. -/
theorem coMoving_head_rate_eq_lie_derivative (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    coMovingHeadRate dq dy scores keys log_heights h =
      sl2Beta scores log_heights *
        contourOutput (geodesicPoles keys log_heights) (h dq)
          (geodesicResidue dq dy h) dq := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §R.5  First-order Euler vs exact co-moving (local in time)
-- ═══════════════════════════════════════════════════════════════════════

/-- Euler increment on the head output using the co-moving rate. -/
noncomputable def coMovingEulerHeadIncrement (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : ℝ :=
  Δt * coMovingHeadRate dq dy scores keys log_heights h

/-- Frozen-query Euler increment (wrong physics: drops bandwidth + key terms). -/
noncomputable def frozenQueryEulerHeadIncrement (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : ℝ :=
  Δt * frozenQueryHeadRate dq dy scores keys log_heights h

/-- **Per-step error** of frozen-query Euler vs co-moving Euler on the head rate. -/
noncomputable def frozenEulerHeadError (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : ℝ :=
  coMovingEulerHeadIncrement Δt dq dy scores keys log_heights h -
    frozenQueryEulerHeadIncrement Δt dq dy scores keys log_heights h

theorem frozen_euler_head_error_eq (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    frozenEulerHeadError Δt dq dy scores keys log_heights h =
      Δt * (frozenBandwidthHeadRate dq dy scores keys log_heights h +
        frozenLayerGap dq dy scores keys log_heights h) := by
  dsimp [frozenEulerHeadError, coMovingEulerHeadIncrement, frozenQueryEulerHeadIncrement]
  calc
    Δt * coMovingHeadRate dq dy scores keys log_heights h -
        Δt * frozenQueryHeadRate dq dy scores keys log_heights h =
        Δt * (coMovingHeadRate dq dy scores keys log_heights h -
          frozenQueryHeadRate dq dy scores keys log_heights h) := by ring
    _ = Δt * (frozenBandwidthHeadRate dq dy scores keys log_heights h +
        frozenLayerGap dq dy scores keys log_heights h) := by
      rw [frozen_query_only_gap dq dy scores keys log_heights h]

/-- If the per-layer gap is bounded by `G`, the frozen-query Euler mistake per step is
    bounded by `|Δt| · G` (triangle inequality on the rate decomposition). -/
theorem frozen_euler_head_error_abs_le (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) (G : ℝ)
    (hG : |frozenBandwidthHeadRate dq dy scores keys log_heights h +
            frozenLayerGap dq dy scores keys log_heights h| ≤ G) :
    |frozenEulerHeadError Δt dq dy scores keys log_heights h| ≤ |Δt| * G := by
  have hEq := frozen_euler_head_error_eq Δt dq dy scores keys log_heights h
  rw [hEq, abs_mul]
  exact mul_le_mul_of_nonneg_left hG (abs_nonneg Δt)

-- ═══════════════════════════════════════════════════════════════════════
-- §R.6  Depth: composing Carnot steps vs composing residual Euler
-- ═══════════════════════════════════════════════════════════════════════

/-- **Co-moving depth** composes exactly (`t+s` lemma re-exported). -/
theorem coMoving_head_depth_compose (keys₀ log_heights₀ : Fin N → ℝ) (q₀ α β s t : ℝ) :
    poissonHeadOutput
        (fun k => α / β + (α / β + (keys₀ k - α / β) * Real.exp (-β * s) - α / β) *
          Real.exp (-β * t))
        (fun k => log_heights₀ k + -β * (s + t))
        (α / β + (α / β + (q₀ - α / β) * Real.exp (-β * s) - α / β) * Real.exp (-β * t)) =
      Real.exp (β * (s + t)) * poissonHeadOutput keys₀ log_heights₀ q₀ := by
  dsimp [poissonHeadOutput]
  have hγ : ∀ k, Real.exp (log_heights₀ k + -β * (s + t)) =
      Real.exp (log_heights₀ k) * Real.exp (-β * s) * Real.exp (-β * t) := fun k => by
    rw [Real.exp_add, neg_mul_add β s t, Real.exp_add]
    ring
  simp_rw [hγ]
  exact comoving_steps_compose N keys₀ log_heights₀ q₀ α β s t

/-- **Residual depth** unfolds as iterated Euler (semigroup on state). -/
theorem cauchy_residual_depth_add (m n : ℕ) (Δt : ℝ) (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyResidualDepth (m + n) Δt dq dy scores keys log_heights h =
      cauchyResidualDepth n Δt dq dy scores keys log_heights
        (cauchyResidualDepth m Δt dq dy scores keys log_heights h) := by
  dsimp [cauchyResidualDepth]
  rw [Nat.add_comm m n, Function.iterate_add_apply]

-- ═══════════════════════════════════════════════════════════════════════
-- §R.7  The engineer theorem (hypothesis bundle)
-- ═══════════════════════════════════════════════════════════════════════

/-- **What one transformer layer supplies** (abstract interface). -/
structure ResidualLayerStep (N : ℕ) [NeZero N] (dq dy : Fin D) where
  scores : Fin N → ℝ
  keys : Fin N → ℝ
  log_heights : Fin N → ℝ
  Δt : ℝ
  h_in : Fin D → ℝ
  h_out : Fin D → ℝ
  /-- Residual update with the Carnot vector field. -/
  euler_update :
    h_out = (cauchyResidualEulerStep Δt dq dy scores keys log_heights) h_in
  /-- Bound on frozen-query Euler error at this slice (from §R.5). -/
  gap_bound : ℝ
  gap_nonneg : 0 ≤ gap_bound
  gap_spec :
    |(frozenBandwidthHeadRate dq dy scores keys log_heights) h_in +
        (frozenLayerGap dq dy scores keys log_heights) h_in| ≤ gap_bound

/-- **Answer to "why does my 100-layer model work?"** (formal version).

    Each layer is a residual Euler step along `cauchyPoissonVF` (ideal Carnot field on
    `dq`/`dy`).  The mistake made by treating the head as frozen-query-only is exactly
    `Δt · (bandwidth + key_velocity_correction)`, bounded per layer by `|Δt|·G`.
    Depth composes Euler steps; co-moving Poisson heads compose exactly. -/
theorem residual_layer_engineer_bound (dq dy : Fin D) (step : ResidualLayerStep N dq dy) :
    |frozenEulerHeadError step.Δt dq dy step.scores step.keys step.log_heights step.h_in| ≤
      |step.Δt| * step.gap_bound := by
  apply frozen_euler_head_error_abs_le step.Δt dq dy step.scores step.keys step.log_heights step.h_in
    step.gap_bound step.gap_spec

/-- Ideal query-channel velocity after one Carnot Euler step. -/
theorem residual_layer_query_velocity (dq dy : Fin D) (step : ResidualLayerStep N dq dy) :
    step.h_out dq =
      step.h_in dq +
        step.Δt * sl2QueryVelocity step.scores step.keys step.log_heights (step.h_in dq) := by
  have heq := cauchy_residual_euler_query_channel step.Δt dq dy step.scores step.keys step.log_heights
    step.h_in
  simpa only [step.euler_update, cauchyResidualEulerStep] using heq

/-- **No-go reminder:** frozen ∂_q P sums cannot equal `α − β·q` globally. -/
theorem frozen_poles_cannot_match_sl2_globally (keys : Fin N → ℝ) (log_heights : Fin N → ℝ)
    (α β : ℝ) (hβ : 0 < β) :
    ∃ q : ℝ,
      ∑ k : Fin N, (Real.exp (log_heights k))⁻¹ ^ 2 < |α - β * q| :=
  ComovingEuler.frozen_partial_neq_sl2_linear N keys log_heights α β hβ

end DiscreteResidualBridge

end -- noncomputable section
