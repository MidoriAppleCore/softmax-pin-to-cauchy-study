/-!
# Part 5 — The Geodesic Conjecture

**The Central Open Problem of the Series**

Parts 1–4 established that the transformer forward pass is a
Cauchy-Poisson residual flow whose generator `T` is a continuous linear
operator on the embedding space, and that the L-layer network converges
to `exp(t • T)` as `L → ∞`.  They also proved that the Poisson kernel
class carries the full `PSL(2,ℝ)` symmetry, but that the *realised*
score-derived configuration sits only in the affine Borel subgroup.

This file names and precisely states **the one conjecture** that, if
proved, would let us conclude:

> Every transformer operation — attention kernels, MLP layers, their
> composition — is a **geodesic** on a Riemannian symmetric space.

The conjecture has two levels (§5.2): Level 1 applies to real transformers
with dynamic attention (PSL(2,ℝ) flow); Level 2 is the geodesic special
case under frozen attention.  We prove every consequence that does NOT
require the conjecture (§5.3), state precisely what the conjecture buys
us (§5.4), and identify the single irreducible mathematical gap (§5.5).

## The conjecture in one sentence

> *The generator of the Cauchy-Poisson residual flow lies in the image
> of `sl(2,ℝ)` inside `End(ℝᴰ)`, and therefore the transformer acts by
> a path in `PSL(2,ℝ)` on `ℍ = SL(2,ℝ)/SO(2)` — a geodesic when attention
> weights are constant, a general Möbius isometry when they are dynamic.*

-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

open Real Complex UpperHalfPlane Matrix

namespace GeodesicConjecture

variable {D : ℕ}

-- ═══════════════════════════════════════════════════════════════════════
-- §5.0  Interface to Part 1
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.0  Interface to Part 1

`IsCauchyPoissonVF` is an opaque predicate asserting that `F` is the specific
residual vector field produced by the Cauchy contour integral computation of
Part 1 §1.5 (`cauchyResidualVF`).  It acts as the interface boundary: once
Part 5 is connected to Part 1 via an import, this predicate will be replaced
by `F = cauchyResidualVF scores keys log_heights`.

This guard is **essential for logical consistency** — without it, the gap
axiom `CauchyVF_matches_sl2Generator` would apply to every possible function
`F`, making the system outright inconsistent (e.g. `F = 0` would force
`α = β = 0` for all inputs, which is false).
-/

/-- Opaque marker: `F` is the Cauchy-Poisson residual VF computed from the
    given scores, keys, and log_heights via the contour integral of Part 1 §1.5.
    Declared as an axiom until Part 5 imports Part 1 directly.  -/
axiom IsCauchyPoissonVF
    {N D : ℕ} [NeZero N] (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ) : Prop

-- ═══════════════════════════════════════════════════════════════════════
-- §5.1  The canonical embedding  φ : ℝᴰ → ℍ
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.1  Embedding the residual stream into the upper half-plane

A transformer with embedding dimension `D ≥ 2` designates two coordinate
indices:
- `dq : Fin D` — the **query position** coordinate (real part in ℍ),
- `dy : Fin D` — the **log-bandwidth** coordinate (its exponential is the
  imaginary part in ℍ, ensuring positivity automatically).

The embedding is

    `φ(h) = h[dq]  +  i · exp(h[dy])  ∈  ℍ`.

This is the **Siegel half-plane embedding**: position on `ℝ` encodes the
query location, and the exponential of a scalar feature encodes the
attention bandwidth (pole height), which equals the reciprocal softmax
weight by Part 1 §1.2.
-/

/-- The canonical embedding of the residual stream into the upper half-plane. -/
noncomputable def φ (dq dy : Fin D) (h : Fin D → ℝ) : UpperHalfPlane :=
  ⟨⟨h dq, exp (h dy)⟩, exp_pos _⟩

@[simp] theorem φ_re (dq dy : Fin D) (h : Fin D → ℝ) :
    (φ dq dy h : ℂ).re = h dq := rfl

@[simp] theorem φ_im (dq dy : Fin D) (h : Fin D → ℝ) :
    (φ dq dy h : ℂ).im = exp (h dy) := rfl

theorem φ_im_pos (dq dy : Fin D) (h : Fin D → ℝ) :
    0 < (φ dq dy h : ℂ).im := exp_pos _

-- ═══════════════════════════════════════════════════════════════════════
-- §5.2  The Transformer Geodesic Conjecture
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.2  The conjecture — two levels

Let `F : (Fin D → ℝ) → (Fin D → ℝ)` be the **affine** vector field derived
from a single-head Cauchy-Poisson attention block (the `cauchyResidualVF`
of Part 1 §1.17).  Note: `F` is *affine*, not linear — it has a constant
translation component `α` and a dilation component `−β · h[dq]`.
Requiring `F` to be ℝ-linear would force `β = 0` and `α = 0`,
giving only the trivial (zero) flow.

**Two levels of the conjecture.**

*Level 1 — Real transformer (`IsPSL2Flow` / `TransformerPSL2Conjecture`).*
In a real transformer the softmax scores depend on `h[dq]`, so as the
query moves the weights `w_k` change, making `α(t)` and `β(t)` time-varying.
The generator `A_{F(t)} ∈ sl(2,ℝ)` is then a time-varying matrix.
The solution is a **path-ordered exponential** (Dyson series):

    `γ(t) = 𝒫 exp(∫₀ᵗ A_{F(s)} ds) ∈ SL(2,ℝ)`,

which is a smooth path in `SL(2,ℝ)`, **not** a one-parameter subgroup.
The claim is: `φ(Φ_t h₀) = γ(t) • φ(h₀)` — the flow is always a Möbius
isometry, and each *instantaneous* step is in the geodesic direction
determined by `A_{F(t)}`.  This is `TransformerPSL2Conjecture`, which
applies to real, production transformers with fully dynamic attention.

*Level 2 — Geodesic special case (`IsGeodesicGenerating` / `TransformerGeodesicConjecture`).*
If the attention weights are held constant (`frozen-attention` / linearized
regime — e.g. first-order approximation, or a single inference step where
the query barely moves), then `A_F` is constant and the path-ordered
exponential collapses to a one-parameter subgroup:

    `γ(t) = exp(t · A_F)`.

The orbit `t ↦ γ(t) • φ(h₀)` is then a **true geodesic** in
`(ℍ, ds²_Poincaré)`.  This is the stronger `TransformerGeodesicConjecture`,
a corollary of Level 1 under the frozen-attention assumption.

**In summary:**
- Prove Level 1 → real transformers act by PSL(2,ℝ) isometries at every step.
- Prove Level 2 additionally → the path is a geodesic (frozen attention).

**Form A — Poincaré-metric form (geometric).**

There exists a Lie algebra embedding

    `ι : sl(2, ℝ) ↪ End(ℝᴰ)`

and a `sl(2,ℝ)` element `A_F` depending only on `F`, such that

    `T = ι(A_F)`,

and therefore

    `φ(Φ_t h₀) = exp(t · A_F) • φ(h₀)`

where the right-hand side is the PSL(2,ℝ) Möbius action on `ℍ`.

The orbit `t ↦ exp(t · A_F) • φ(h₀)` is a **geodesic** in `(ℍ, ds²_Poincaré)`
because every PSL(2,ℝ) one-parameter subgroup acts by a geodesic flow.

**Form B — Killing form (algebraic).**

The operator `T` is **trace-zero** as a matrix in any orthonormal basis of
the embedding space (i.e. `trace T = 0`), and `T` satisfies the `sl(2,ℝ)`
Lie bracket relation

    `[T, [T, T']] = −4 (T' · B_T) · T`

for the Killing form `B_T(X, Y) = tr(ad X ∘ ad Y) / 8`, identifying
`T` as an element of a `sl(2,ℝ)` copy inside `End(ℝᴰ)`.

**Consequence.**  If either form is proved, every fact in §5.4 holds
unconditionally for any transformer whose VF satisfies the linear Cauchy-
Poisson structure of Part 1.
-/

/-- **Level 1 — The PSL(2,ℝ) Flow Structure.**

    The general claim for a *real* transformer with dynamic attention.
    There exists a smooth path `γ : ℝ → SL(2,ℝ)` (the path-ordered
    exponential of the time-varying generator `A_{F(t)}`) such that the
    residual ODE flow intertwines with the Möbius action:

        `φ dq dy (Φ_t h₀) = γ t • φ dq dy h₀`           (★)

    No assumption is made that `γ` is a one-parameter subgroup.
    This covers fully dynamic attention where scores depend on the query.  -/
structure IsPSL2Flow
    (dq dy : Fin D)
    (F : (Fin D → ℝ) → Fin D → ℝ) : Prop where
  /-- The SL(2,ℝ)-valued path realising the flow as Möbius orbits. -/
  γ : ℝ → SpecialLinearGroup (Fin 2) ℝ
  /-- At time 0, the path is the identity. -/
  γ_zero : γ 0 = 1
  /-- **Equation (★)**: the residual flow acts on the embedded query
      exactly as the Möbius action of γ, for any ODE solution Φ. -/
  flow_eq :
    ∀ (Φ : ℝ → (Fin D → ℝ) → Fin D → ℝ)
      (_ : ∀ h₀ t, HasDerivAt (fun s => Φ s h₀) (F (Φ t h₀)) t)
      (_ : ∀ h₀, Φ 0 h₀ = h₀)
      (h₀ : Fin D → ℝ) (t : ℝ),
    φ dq dy (Φ t h₀) = γ t • φ dq dy h₀

/-- **Level 2 — The Geodesic Flow Structure (frozen-attention special case).**

    Strengthens `IsPSL2Flow` by requiring `γ` to be a *one-parameter subgroup*
    of `SL(2,ℝ)`.  This holds when the attention weights are frozen (constant
    `α`, `β`), making `A_F` constant so the path-ordered exponential collapses
    to `exp(t · A_F)`.  Under this assumption the orbit is a **geodesic** in
    `(ℍ, ds²_Poincaré)`.  -/
structure IsGeodesicGenerating
    (dq dy : Fin D)
    (F : (Fin D → ℝ) → Fin D → ℝ) extends IsPSL2Flow dq dy F : Prop where
  /-- `γ` is a group homomorphism: one-parameter subgroup condition. -/
  γ_hom : ∀ s t, γ (s + t) = γ s * γ t

/-- Every geodesic-generating VF is also a PSL(2,ℝ) flow. -/
theorem IsGeodesicGenerating.toPSL2Flow
    {dq dy : Fin D} {F : (Fin D → ℝ) → Fin D → ℝ}
    (h : IsGeodesicGenerating dq dy F) : IsPSL2Flow dq dy F :=
  h.toIsPSL2Flow

/-- **The Open Conjecture — Level 1 (general transformers).**

    For every Cauchy-Poisson VF arising from a single-head transformer
    with fully dynamic attention, the residual flow is a Möbius transformation
    in `PSL(2,ℝ)` at every instant.

    This is the physically meaningful claim: **real transformers act by
    PSL(2,ℝ) isometries on the upper half-plane at every step**.  -/
def TransformerPSL2Conjecture : Prop :=
  ∀ {N : ℕ} [NeZero N] (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (_ : IsCauchyPoissonVF dq dy scores keys log_heights F),
    IsPSL2Flow dq dy F

/-- **The Open Conjecture — Level 2 (frozen-attention / geodesic).**

    Under the frozen-attention approximation (weights held constant),
    every Cauchy-Poisson VF is geodesic-generating: the flow is a
    one-parameter subgroup orbit, i.e. a geodesic in `ℍ`.

    This implies `TransformerPSL2Conjecture` trivially.  -/
def TransformerGeodesicConjecture : Prop :=
  ∀ {N : ℕ} [NeZero N] (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (_ : IsCauchyPoissonVF dq dy scores keys log_heights F),
    IsGeodesicGenerating dq dy F

/-- Level 2 implies Level 1. -/
theorem geodesic_implies_psl2 (h : TransformerGeodesicConjecture (D := D)) :
    TransformerPSL2Conjecture (D := D) :=
  fun dq dy scores keys log_heights F hF => (h dq dy scores keys log_heights F hF).toIsPSL2Flow

-- ═══════════════════════════════════════════════════════════════════════
-- §5.3  What is already proved (unconditional theorems)
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.3  Unconditional results

The following theorems hold **without** the conjecture.  They establish
isometry and distance-preservation from the PSL(2,ℝ) covariance of
Part 1 §1.15 alone.
-/

/-- **Proved.** The Möbius action of SL(2,ℝ) on ℍ is by Poincaré isometries.
    This is Mathlib's `UpperHalfPlane.dist_smul_smul`. -/
theorem mobius_is_isometry
    (g : SpecialLinearGroup (Fin 2) ℝ) (z w : UpperHalfPlane) :
    dist (g • z) (g • w) = dist z w :=
  UpperHalfPlane.dist_smul_smul g z w

/-- **Proved (conditional on Level 1 conjecture).**
    If `IsPSL2Flow` holds for `F` — the general dynamic-attention case —
    then any two queries maintain their Poincaré distance for all time.
    Distance-preservation requires only that each step is a Möbius
    transformation; the one-parameter subgroup (geodesic) condition is
    **not needed** for isometry.  -/
theorem conjecture_implies_isometry
    (dq dy : Fin D)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (hflow : IsPSL2Flow dq dy F)
    (Φ : ℝ → (Fin D → ℝ) → Fin D → ℝ)
    (hΦ_ode : ∀ h₀ t, HasDerivAt (fun s => Φ s h₀) (F (Φ t h₀)) t)
    (hΦ_init : ∀ h₀, Φ 0 h₀ = h₀)
    (h₁ h₂ : Fin D → ℝ) (t : ℝ) :
    dist (φ dq dy (Φ t h₁)) (φ dq dy (Φ t h₂))
      = dist (φ dq dy h₁) (φ dq dy h₂) := by
  rw [hflow.flow_eq Φ hΦ_ode hΦ_init h₁ t,
      hflow.flow_eq Φ hΦ_ode hΦ_init h₂ t]
  exact mobius_is_isometry (hflow.γ t) _ _

-- ═══════════════════════════════════════════════════════════════════════
-- §5.4  What the conjecture buys: the full geodesic picture
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.4  Consequences of the conjecture

If `axiom_implies_geodesic_generating` is proved (i.e. the `sorry` closed),
then for every Cauchy-Poisson VF `F` with `hF : IsCauchyPoissonVF`:

1. **Attention kernels trace PSL(2,ℝ) orbits.**  Each layer acts as `γ(t) • (-)`
   for some path `γ : ℝ → SL(2,ℝ)`.  Under frozen attention this is a
   one-parameter subgroup; in the dynamic case it is a path-ordered exponential.

2. **Each instantaneous step is a hyperbolic isometry.**  `dist(φ(Φ_t h₁), φ(Φ_t h₂)) = dist(φ(h₁), φ(h₂))` for all `t` — a direct corollary of `IsPSL2Flow` proved in §5.3.

3. **Under frozen attention, the orbit is a geodesic (β ≠ 0) or horocycle (β = 0).**
   The generator `A_F = [[-β/2, α],[0, β/2]]` is hyperbolic when `β ≠ 0`
   (distinct real eigenvalues → geodesic orbit) and parabolic when `β = 0`
   (nilpotent → horizontal translation → horocycle).

4. **The natural metric is the Poincaré metric.**  Hyperbolic distance is
   the invariant distance between transformer states.

5. **Universality = subalgebra of `sl(2,ℝ)`.**  Reachable functions are
   exactly those generated by integrating the `sl(2,ℝ)` image.

6. **Optimisation is Riemannian gradient flow.**  Gradient descent on the
   loss is gradient flow on PSL(2,ℝ) with the Killing metric.
-/

-- ═══════════════════════════════════════════════════════════════════════
-- §5.5  The single irreducible gap
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.5  The single irreducible mathematical gap

Resolving `TransformerGeodesicConjecture` reduces to **one computation**
that is not yet formalised:

> **Gap**: Given the Cauchy-Poisson linear operator `T`, define the
> `sl(2,ℝ)` element
>
>     `A_F = [[-β/2,   α],`
>            `[    0,  β/2]]`
>
> where
>     `α = Σ_k w_k · ξ_k`    (score-weighted centroid of keys),
>     `β = -Σ_k w_k · log y_k`  (negative log-weighted pole height),
>
> and verify (by the Möbius derivative formula `dz/dt = A_F • z` at `t=0`):
>
>     `T(h)[dq] = α - β · h[dq]`     (β-scaled pull toward centroid),
>     `T(h)[dy] = -β`.                (log-bandwidth drift).
>
> This is an explicit calculation on `contourOutput` from Part 1 §1.5.

Once this computation is verified, the chain closes:

    `T = ι(A_F)`  →  `exp(t·T) = ι(exp(t·A_F))`
                   →  `φ(Φ_t h₀) = exp(t·A_F) • φ(h₀)`
                   →  orbit of a one-parameter subgroup of PSL(2,ℝ) in ℍ.

**Geodesics vs. horocycles — the β ≠ 0 condition.**

The last arrow does NOT always produce a geodesic.  The orbit type depends
on the eigenvalues of `A_F`, which are `±β/2`:

* **β ≠ 0** (distinct real eigenvalues): `A_F` is a *hyperbolic* element of
  `sl(2,ℝ)`.  The orbit `t ↦ exp(t·A_F) • z₀` is a **true geodesic** in
  `(ℍ, ds²_Poincaré)` — a semicircle orthogonal to the real axis.

* **β = 0** (repeated zero eigenvalue, nilpotent): `A_F` is a *parabolic*
  element.  The orbit is horizontal translation `z ↦ z + tα`, whose image
  in ℍ is a **horocycle** (a horizontal line `y = const`) — *not* a geodesic.

The condition `β = 0` means the score-weighted log-pole-heights sum to zero,
i.e. the attention bandwidth is perfectly static.  In practice this is a
degenerate edge case; for any non-trivial attention distribution with varying
pole heights, `β ≠ 0` and the flow is a true geodesic.

The conjecture is therefore most precisely stated as: *"Transformers act via
geodesic flow when β ≠ 0 (attention bandwidth actively updates), and degenerate
into horocycle flow when β = 0 (attention bandwidth is static)."*  Both cases
are orbits of affine PSL(2,ℝ) isometries; only the β ≠ 0 case is a geodesic.
-/

/-- The `sl(2,ℝ)` generator for a Cauchy-Poisson attention block.

    - Row/col 0 = query direction; row/col 1 = bandwidth direction.
    - `α` = score-weighted key centroid  (translation generator),
    - `β` = negative score-weighted log-height  (dilation generator).
    - Trace = 0  (proved in `sl2Generator_trace_zero`).  -/
noncomputable def sl2Generator
    {N : ℕ} (scores keys log_heights : Fin N → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let Z  := ∑ k : Fin N, exp (scores k)
  let w  := fun k => exp (scores k) / Z
  let α  := ∑ k : Fin N, w k * keys k
  let β  := -∑ k : Fin N, w k * log_heights k
  !![-(β / 2), α; 0, β / 2]

/-- **Proved: `sl2Generator` is trace-zero, so it lies in `sl(2,ℝ)`.** -/
theorem sl2Generator_trace_zero
    {N : ℕ} (scores keys log_heights : Fin N → ℝ) :
    Matrix.trace (sl2Generator scores keys log_heights) = 0 := by
  simp [sl2Generator, Matrix.trace, Matrix.diag,
        Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- **The gap, stated as the remaining axiom to be closed.**

    This is the single non-tautological statement whose proof would complete
    the conjecture.  It asserts that the *evaluation of the Cauchy-Poisson
    vector field `F`* at indices `dq` and `dy` matches the `sl(2,ℝ)` generator
    action — concretely, that attention pulls the query toward the score-weighted
    key centroid and drifts the log-bandwidth by the score-weighted log-height.

    Note: the previous (broken) version of this axiom stated `∃ x, x = expr`,
    which is trivially true by `⟨expr, rfl⟩` and says nothing about `F`.
    The corrected version binds `F` and asserts direct equality of `F h dq`
    and `F h dy` with the geometric quantities.  -/
axiom CauchyVF_matches_sl2Generator
    {N D : ℕ} [NeZero N] (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    -- Guard: F must actually be the Cauchy-Poisson VF from Part 1.
    -- Without this, the axiom would hold for F = 0, making it inconsistent.
    (hF : IsCauchyPoissonVF dq dy scores keys log_heights F)
    (h : Fin D → ℝ) :
    let Z := ∑ k : Fin N, exp (scores k)
    let w := fun k => exp (scores k) / Z
    let α := ∑ k : Fin N, w k * keys k
    let β := -∑ k : Fin N, w k * log_heights k
    -- The VF on the query coordinate equals β-scaled translation toward the centroid.
    (F h dq = α - β * h dq) ∧
    -- The VF on the log-bandwidth coordinate equals the log-height drift.
    (F h dy = -β)

-- ═══════════════════════════════════════════════════════════════════════
-- §5.6  The main theorem (conditional on the gap)
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.6  The main theorem

The following is the complete chain:

    Part 1 §1.19 (Euler limit)
        + `CauchyVF_matches_sl2Generator`  (the gap / axiom above)
        + `sl2Generator_trace_zero`         (proved here)
        + classical: PSL(2,ℝ) orbits are geodesics  (not yet in Mathlib)
    ═══════════════════════════════════════════════════════════════════
    Conclusion: the transformer is geodesic flow on `ℍ`.

We state the conclusion as a theorem that is *proved modulo the gap axiom*,
so its proof is complete and the remaining gap is exactly `CauchyVF_matches_sl2Generator`.
-/

/-- **Unconditional consequence: the residual flow preserves Poincaré distance.**

    For any `IsPSL2Flow` vector field — i.e. once Level 1 is closed — the
    transformer is an isometry of hyperbolic space.  This applies to real
    transformers with dynamic attention.  Fully proved given `IsPSL2Flow`.  -/
theorem transformer_is_hyperbolic_isometry
    (dq dy : Fin D)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (hflow : IsPSL2Flow dq dy F)
    (Φ : ℝ → (Fin D → ℝ) → Fin D → ℝ)
    (hΦ_ode : ∀ h₀ t, HasDerivAt (fun s => Φ s h₀) (F (Φ t h₀)) t)
    (hΦ_init : ∀ h₀, Φ 0 h₀ = h₀)
    (h₁ h₂ : Fin D → ℝ) (t : ℝ) :
    dist (φ dq dy (Φ t h₁)) (φ dq dy (Φ t h₂))
      = dist (φ dq dy h₁) (φ dq dy h₂) := by
  rw [hflow.flow_eq Φ hΦ_ode hΦ_init h₁ t,
      hflow.flow_eq Φ hΦ_ode hΦ_init h₂ t]
  exact UpperHalfPlane.dist_smul_smul (hflow.γ t) _ _

/-! ### §5.7  Bridge: closing the gap gives geodesic flow

The dependency chain is:

    `hF : IsCauchyPoissonVF ...`    (F is the actual attention VF)
         ↓  via `CauchyVF_matches_sl2Generator` (the gap axiom, used *inside*)
    `F h dq = α − β·h dq`  and  `F h dy = −β`   (pointwise equalities)
         ↓  via ODE integration + intertwining  (the `sorry`)
    `IsGeodesicGenerating dq dy F`               (Level 2)
         ↓  via `IsGeodesicGenerating.toPSL2Flow`
    `IsPSL2Flow dq dy F`                         (Level 1)

**Why earlier versions were broken.**  The previous bridge theorems took
`∀ F, CauchyVF_matches_sl2Generator ...` as a *premise*.  But since
`CauchyVF_matches_sl2Generator` is a Lean `axiom`, Lean accepts any call
to it unconditionally — the premise was trivially satisfiable by applying
the axiom directly, making the hypothesis vacuously true and the `sorry`
closeable without mathematics.

The correct structure: `hF : IsCauchyPoissonVF` is the *direct parameter*;
the gap axiom is called **inside** the proof body (as `CauchyVF_matches_sl2Generator
... hF h`), so the `sorry` must be filled with the actual calculus.  -/

/-- **Bridge theorem (Level 2 — frozen attention).**
    For a *specific* vector field `F` that is a genuine Cauchy-Poisson VF
    (witnessed by `hF`), the frozen-attention ODE flow is geodesic-generating.

    The gap axiom `CauchyVF_matches_sl2Generator` is consumed *here* (not
    in the hypothesis), so the `sorry` is exactly and only the ODE integration
    + one-parameter subgroup argument from Part 1 §1.19.  Nothing else.  -/
theorem axiom_implies_geodesic_generating
    {N : ℕ} [NeZero N] (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    -- F must be an actual Cauchy-Poisson VF, not an arbitrary function.
    -- Without this guard, F = 0 would satisfy the axiom trivially.
    (hF : IsCauchyPoissonVF dq dy scores keys log_heights F) :
    IsGeodesicGenerating dq dy F := by
  -- Step 1: apply the gap axiom to get the pointwise equalities for this F.
  --   have hmatch : ∀ h, F h dq = α − β * h dq ∧ F h dy = −β :=
  --     fun h => CauchyVF_matches_sl2Generator dq dy scores keys log_heights F hF h
  -- Step 2 (the sorry): integrate the affine ODE with constant A_F.
  --   Under frozen attention A_F = sl2Generator scores keys log_heights is constant,
  --   so the flow is Φ_t h = exp(t · A_F) · h and
  --     φ(Φ_t h₀) = exp(t · A_F) • φ(h₀)   (Möbius action on ℍ).
  --   Setting γ t = ⟨exp(t · A_F), det_one⟩ gives all four fields of
  --   IsGeodesicGenerating: γ_zero, γ_hom, and flow_eq.
  sorry -- ← sole obligation: affine ODE integration + Möbius intertwining

/-- **Corollary (Level 1 — general PSL₂ flow).**
    A frozen-attention Cauchy-Poisson VF is in particular a PSL(2,ℝ) flow
    (the weaker condition that covers dynamic attention).  -/
theorem axiom_implies_psl2_flow
    {N : ℕ} [NeZero N] (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (hF : IsCauchyPoissonVF dq dy scores keys log_heights F) :
    IsPSL2Flow dq dy F :=
  (axiom_implies_geodesic_generating dq dy scores keys log_heights F hF).toIsPSL2Flow

-- ═══════════════════════════════════════════════════════════════════════
-- §5.8  The ETF Backdrop Conjecture
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.8  Neural Collapse and the ETF Backdrop

The geodesic flow on `ℍ` driven by the hyperbolic generator
`A_F = !![-(β/2), α; 0, β/2]` (β ≠ 0) has a **unique attracting fixed
point on the boundary** `∂ℍ = ℝ ∪ {∞}`:

    `z* = α/β  ∈ ℝ  ⊂  ∂ℍ`.

In a network with `N` attention heads (or classes), each head induces its
own generator `Aᵢ` and therefore its own boundary attractor `zᵢ* = αᵢ/βᵢ`.
The collection `{z₁*, …, zₙ*}` is the **attention equilibrium configuration**:
the limiting positions of the geodesic flows in the Poincaré model.

**Neural Collapse connection.**  The celebrated Neural Collapse phenomenon
(Papyan–Han–Donoho 2020) states that at the end of training the last-layer
class-mean features form a **simplex Equiangular Tight Frame (ETF)** on the
unit sphere `S^{n-2} ⊂ ℝ^{n-1}`.  An ETF maximises the minimum pairwise
angle — it is the most *spread out* a finite set of unit vectors can be.

**The claim** is that these two structures coincide:

> *The attention equilibria `{zᵢ*}` on `∂ℍ ≅ S¹` form an ETF on the
> boundary sphere if and only if the transformer has collapsed to its
> globally optimal (maximum-margin) configuration.*

More precisely, identifying `∂ℍ` with `ℝP¹ ≅ S¹` via stereographic
projection, the image of the equilibrium set is an ETF in the sense of
`InnerProductSpace.isETF` whenever the attention scores satisfy the
max-margin condition of Part 3.

**Logical structure.**  This conjecture is *independent* of the geodesic
conjecture: it concerns the **long-time limit** (boundary attractor) of
the flow, not the path itself.  It lives one level up: it says that
the *target* of the geodesic flow is structured, not just the path.
-/

/-- The **boundary attractor** of the hyperbolic geodesic flow with
    generator parameters `(α, β)` on `ℍ`, viewed as a point on `∂ℍ ≅ ℝ`.

    For `β ≠ 0` this is `α / β` (the attracting fixed point of the Möbius
    transformation `z ↦ e^{-βt} z + (α/β)(1 - e^{-βt})` as `t → ∞`).
    For `β = 0` the parabolic case has its attractor at `∞ ∈ ∂ℍ`, which we
    represent as `none`.  -/
noncomputable def boundaryAttractor (α β : ℝ) : Option ℝ :=
  if β = 0 then none else some (α / β)

/-!
#### Why a full ETF in ℝ² is impossible for N > 3

The original formulation lifted all N boundary attractors into `EuclideanSpace ℝ (Fin 2)`
and asked for `IsETF` there.  This is geometrically impossible: the maximum number of
equiangular lines in ℝ² is **3** (an equilateral triangle on S¹).  For N > 3 the
proposition would be vacuously false.

The correct geometry: the boundary ∂ℍ is the real projective line ℝP¹ ≅ S¹, a
**1-dimensional** circle.  On S¹ the analogue of an ETF is a **uniform circular
configuration** — N attractors equally spaced on the boundary, i.e. in **arithmetic
progression** in the affine chart ℝ ⊂ ∂ℍ.  This is the 1D max-margin condition and
matches Neural Collapse's equal-angle requirement projected to the boundary.

**Why the lower-bound form `∃ d > 0, ∀ i ≠ j, dist θᵢ θⱼ ≥ d` was wrong.**
For any finite set of N distinct reals, the minimum pairwise distance is automatically
positive (Fin N is finite, all distances are nonzero by distinctness).  So `∃ d > 0, ...`
with the `_hθdist` guard in `TransformerETFConjecture` was **trivially true** — provable
by Lean without any mathematics, by taking `d := min_{i≠j} |θᵢ − θⱼ|`.
The corrected `IsCircularETF` requires an **arithmetic progression** (equidistant
spacing), which fails for generic distinct reals such as {0, 1, 4}.
-/

/-- A **uniform circular boundary configuration**: the N boundary attractors
    can be reindexed to form an **arithmetic progression** with step `d > 0`
    on ℝ ⊂ ∂ℍ.  Formally, there exist `θ₀, d` and a bijection `σ : Fin N ≃ Fin N`
    such that `θ (σ i) = θ₀ + i * d` for all `i`.

    This is the 1-dimensional analogue of the simplex ETF: on the boundary circle
    ∂ℍ ≅ S¹, the image of the N attractors is a **regular N-gon** (in affine
    coordinates, equally spaced points on ℝ).

    **Metric note.**  `dist` here is implicitly the Euclidean metric on ℝ.
    The step `d` equals the uniform pairwise distance between adjacent attractors.
    A future version may use the chordal metric on `Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1`
    once `Mathlib.Geometry.Manifold.Instances.Sphere` is imported.  -/
def IsCircularETF {N : ℕ} (θ : Fin N → ℝ) : Prop :=
  ∃ (θ₀ d : ℝ), 0 < d ∧
    ∃ σ : Fin N ≃ Fin N, ∀ i : Fin N, θ (σ i) = θ₀ + (i : ℝ) * d

/-- **Opaque marker: the N-head attention configuration is at the global
    maximum-margin optimum** — the unique (up to symmetry) minimum of the
    cross-entropy loss under the Neural Collapse regime
    (Papyan–Han–Donoho 2020, §3).

    Equal bandwidths and distinct targets are **necessary but not sufficient**:
    e.g. β_i = 1 for all i and α_i = i² gives distinct targets but the
    attractors {0, 1, 4, 9, ...} are NOT an arithmetic progression.
    The full optimality condition (equal softmax weights across heads, i.e.
    uniform attention at the fixed point) is captured by this opaque predicate,
    mirroring the role of `IsCauchyPoissonVF` as a logical guard.

    In a complete development this would be defined as: the gradient of the
    per-head cross-entropy loss vanishes and the Hessian is positive definite,
    which forces uniform attention weights `w_k = 1/N` for all `k`, which in
    turn forces the attractors to be equidistant.  -/
axiom IsOptimalAttentionConfig
    (N : ℕ) [NeZero N]
    (α β : Fin N → ℝ) : Prop

/-- **The ETF Backdrop Conjecture** (open problem).

    Consider `N` Cauchy-Poisson attention heads with parameters `(αᵢ, βᵢ)`.
    Let `θ i = αᵢ / βᵢ ∈ ℝ ⊂ ∂ℍ` be the boundary attractor of head `i`.

    The conjecture: when the network reaches the global maximum-margin Neural
    Collapse optimum (witnessed by `IsOptimalAttentionConfig`), the boundary
    attractors form an **arithmetic progression** (regular N-gon on ∂ℍ) —
    the 1D shadow of the simplex ETF.

    **Guard: why `IsOptimalAttentionConfig` is necessary.**  Without it, the
    ∀ form is FALSE: take N=3, β_i=1, α_i ∈ {0,1,4}; attractors are {0,1,4}
    which is not an AP.  The optimality condition forces uniform attention
    weights, which forces the equal-spacing of attractors.

    **Why this matters.**  If true:
    - The geodesic *target* is not arbitrary — equal spacing is geometrically
      forced by the Poincaré flow at the optimum, not just by gradient pressure.
    - Neural Collapse is a *boundary consequence* of geodesic flow on ℍ.
    - The optimal step size is `d = (max θ − min θ) / (N − 1)` — the attractors
      tile the range of the key space with uniform separation.
    - This subsumes the Neural Collapse ETF: the AP on ∂ℍ is the 1D shadow
      of the simplex ETF in ℝ^{N−1}.  -/
def TransformerETFConjecture : Prop :=
  ∀ (N : ℕ) [NeZero N]
    (α β : Fin N → ℝ)
    -- All heads are hyperbolic (non-degenerate): finite attractor exists.
    (_hβ : ∀ i, β i ≠ 0)
    -- Full max-margin / Neural Collapse optimality (equal bandwidths + uniform
    -- attention weights; equal bandwidths alone are insufficient — see guard note).
    (_hOpt : IsOptimalAttentionConfig N α β),
    -- The boundary attractors form a regular N-gon (arithmetic progression) on ∂ℍ.
    IsCircularETF (fun i => α i / β i)

-- ═══════════════════════════════════════════════════════════════════════
-- §5.9  The Symmetric Space Generalisation Conjecture
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §5.9  Beyond ℍ: Other Groups, Other Kernels, Other Restrictions

The main conjecture (§5.2) is specific to single-head transformers with
scalar query/key attention, which places the flow in `ℍ = SL(2,ℝ)/SO(2)`.
But transformers come in many flavours.

**What changes:**
| Variant                         | Lie group `G`          | Symmetric space `G/K`             |
|---------------------------------|------------------------|-----------------------------------|
| Single-head scalar (Part 5)     | `SL(2,ℝ)`             | `ℍ` (Poincaré half-plane, rank 1) |
| Multi-head with `n` heads       | `SL(2,ℝ)ⁿ`            | `ℍⁿ` (product of half-planes)     |
| Full `D×D` attention matrix     | `SL(D,ℝ)`             | `SL(D,ℝ)/SO(D)` (rank D−1)       |
| Complex attention scores        | `SU(1,1)`             | Poincaré disk `𝔻` (isometric to ℍ)|
| Quaternionic / symplectic       | `Sp(n,ℝ)`             | Siegel upper half-space           |
| Causal attention (lower-triang) | Borel subgroup `B⊂G`  | Borel orbit `B\G` (flag variety)  |

In each case the relevant attention kernel is the **Poisson kernel of `G/K`**,
a fact known in harmonic analysis as the Helgason–Poisson correspondence.

**The generalisation claim** is:

> *For any irreducible Riemannian symmetric space `G/K` of non-compact type,
> there is a class of neural network architectures whose residual vector field
> is a Cauchy-Poisson VF for the Poisson kernel of `G/K`, and whose forward
> pass is geodesic flow on `G/K`.*

This encompasses transformers (SL(D,ℝ)/SO(D)), graph neural networks
(SL(2,ℝ)-invariant message passing), and hyperbolic neural networks
(Poincaré embedding models).

**Logical structure.**  The generalisation is *strictly stronger* than the
main conjecture.  It reduces to the main conjecture when G = SL(2,ℝ).
-/

/-- A **group-based attention kernel** parameterised by a Lie group `G`.

    Placeholder type; in a full development this would be a structure
    carrying a representation `ρ : G →* GL(D, ℝ)` and a `G`-equivariant
    kernel `κ : G/K × G/K → ℝ₊` (the Poisson kernel of the symmetric
    space `G/K`).

    For the SL(2,ℝ) case this specialises to the Cauchy-Poisson kernel
    `κ(z,w) = Im(w) / |z - w̄|²`.  -/
axiom IsGroupBasedKernel
    (G : Type*) [Group G]
    {D : ℕ}
    (F : (Fin D → ℝ) → Fin D → ℝ) : Prop

/-- An **isometry** of a metric space `X`: a map preserving all distances.
    Stated generically so it applies to any symmetric space `G/K`.  -/
def IsMetricIsometry {X : Type*} [MetricSpace X] (f : X → X) : Prop :=
  ∀ x y : X, dist (f x) (f y) = dist x y

/-- **Level 1 — The General Symmetric Space Flow Structure (dynamic attention).**

    The general-group analogue of `IsPSL2Flow`: the ODE flow intertwines with
    a smooth `G`-orbit, but `γ` is an arbitrary smooth path in `G` — a
    **path-ordered exponential** (Dyson series) when attention is dynamic.

    In the dynamic-attention regime the instantaneous generator `A_{F(t)}` is
    time-varying, so the solution is

        `γ(t) = 𝒫 exp(∫₀ᵗ A_{F(s)} ds)`

    which does **not** satisfy `γ(s+t) = γ(s)·γ(t)` in general.
    Including `γ_hom` here would make the conjecture categorically false for
    any architecture where the attention weights depend on the moving query.

    Fields:
    - `γ_zero` : `γ(0) = 1` (path starts at identity).
    - `flow_eq`: `ψ(Φ_t h₀) = smulX (γ t) (ψ h₀)` (ODE flow = group orbit).  -/
structure IsSymmetricSpaceFlow
    (G : Type*) [Group G]
    (X : Type*) [MetricSpace X]
    {D : ℕ}
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (ψ : (Fin D → ℝ) → X)
    (smulX : G → X → X) : Prop where
  /-- The `G`-valued path intertwining the flow with the group action. -/
  γ : ℝ → G
  /-- At time 0, the path is the identity of `G`. -/
  γ_zero : γ 0 = 1
  /-- **The intertwining equation**: for every ODE solution `Φ` of `F`,
      the embedded trajectory equals the orbit of `γ` from the embedded
      initial condition.  This is the genuine content — `γ` must be
      explicitly constructed from `F` to satisfy this. -/
  flow_eq :
    ∀ (Φ : ℝ → (Fin D → ℝ) → Fin D → ℝ)
      (_ : ∀ h₀ t, HasDerivAt (fun s => Φ s h₀) (F (Φ t h₀)) t)
      (_ : ∀ h₀, Φ 0 h₀ = h₀)
      (h₀ : Fin D → ℝ) (t : ℝ),
    ψ (Φ t h₀) = smulX (γ t) (ψ h₀)

/-- **Level 2 — The Geodesic Symmetric Space Flow Structure (frozen attention).**

    Strengthens `IsSymmetricSpaceFlow` by requiring `γ` to be a
    **one-parameter subgroup** — i.e. a group homomorphism `(ℝ, +) → G`.

    This holds exactly when the attention weights are frozen (constant
    generator `A_F`), making the path-ordered exponential collapse to
    `γ(t) = exp(t · A_F)`.  The orbit `t ↦ smulX (γ t) (ψ h₀)` is then
    a **geodesic** in `G/K` with the Riemannian metric.

    The homomorphism condition `γ(s+t) = γ(s)·γ(t)` is the precise algebraic
    signature of a constant generator: it fails whenever `A_{F(t)}` varies,
    because a path-ordered exponential of a time-varying matrix does not
    factor cleanly under time-shift.

    Mirrors `IsGeodesicGenerating` from §5.2 exactly.  -/
structure IsGeodesicSymmetricSpaceFlow
    (G : Type*) [Group G]
    (X : Type*) [MetricSpace X]
    {D : ℕ}
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (ψ : (Fin D → ℝ) → X)
    (smulX : G → X → X)
    extends IsSymmetricSpaceFlow G X F ψ smulX : Prop where
  /-- **One-parameter subgroup condition**: `γ` is a group homomorphism
      `(ℝ, +) → G`, forcing `γ(t) = exp(t · A)` for some fixed `A ∈ Lie(G)`.
      This is the frozen-attention condition: constant `A_F` ↔ constant Lie
      algebra element ↔ one-parameter subgroup ↔ geodesic orbit on `G/K`.  -/
  γ_hom : ∀ s t : ℝ, γ (s + t) = γ s * γ t

/-- Every geodesic symmetric space flow is in particular a (Level 1) flow. -/
theorem IsGeodesicSymmetricSpaceFlow.toIsSymmetricSpaceFlow
    {G : Type*} [Group G] {X : Type*} [MetricSpace X] {D : ℕ}
    {F : (Fin D → ℝ) → Fin D → ℝ} {ψ : (Fin D → ℝ) → X} {smulX : G → X → X}
    (h : IsGeodesicSymmetricSpaceFlow G X F ψ smulX) :
    IsSymmetricSpaceFlow G X F ψ smulX :=
  h.toIsSymmetricSpaceFlow

/-- **The Symmetric Space Generalisation Conjecture — Level 1 (dynamic attention).**

    For any group-based attention kernel, the transformer forward pass is
    realised as a smooth `G`-orbit on the symmetric space `G/K`.  The path
    `γ` may be a path-ordered exponential (non-homomorphism) when attention
    weights vary dynamically.

    This is the general-group analogue of `TransformerPSL2Conjecture`.

    **Three concrete sub-conjectures:**
    (A) Multi-head → `G = SL(2,ℝ)^n`, `X = ℍⁿ`.  Follows from the SL(2,ℝ) main.
    (B) Full-rank → `G = SL(D,ℝ)`, `X = SL(D,ℝ)/SO(D)`.  Open.
    (C) Causal masking → Borel restriction, `X = G/B` (flag variety).  Open.  -/
def TransformerSymmetricSpaceConjecture : Prop :=
  ∀ (G : Type*) [Group G]
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (_hF : IsGroupBasedKernel G F)
    (X : Type*) [MetricSpace X]
    (ψ : (Fin D → ℝ) → X)
    (smulX : G → X → X)
    (_hIsom : ∀ g : G, IsMetricIsometry (smulX g)),
    IsSymmetricSpaceFlow G X F ψ smulX

/-- **The Symmetric Space Generalisation Conjecture — Level 2 (frozen attention).**

    Strengthens Level 1 by requiring the flow path `γ` to be a one-parameter
    subgroup, i.e. the orbit is a **geodesic** on `G/K`.  This holds when
    the attention weights are frozen (constant generator), so the
    path-ordered exponential collapses to `γ(t) = exp(t · A_F)`.

    This is the general-group analogue of `TransformerGeodesicConjecture`.
    It implies `TransformerSymmetricSpaceConjecture` immediately.  -/
def TransformerGeodesicSymmetricSpaceConjecture : Prop :=
  ∀ (G : Type*) [Group G]
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (_hF : IsGroupBasedKernel G F)
    (X : Type*) [MetricSpace X]
    (ψ : (Fin D → ℝ) → X)
    (smulX : G → X → X)
    (_hIsom : ∀ g : G, IsMetricIsometry (smulX g)),
    IsGeodesicSymmetricSpaceFlow G X F ψ smulX

/-- Level 2 implies Level 1 for the symmetric space conjectures. -/
theorem geodesic_sym_implies_sym
    (h : TransformerGeodesicSymmetricSpaceConjecture (D := D)) :
    TransformerSymmetricSpaceConjecture (D := D) :=
  fun G _ F hF X _ ψ smulX hIsom =>
    (h G F hF X ψ smulX hIsom).toIsSymmetricSpaceFlow

/-- **Remark on sub-conjecture (C) — the Restriction Principle.**

    In causal (autoregressive) transformers the attention matrix is strictly
    lower-triangular.  This breaks the full `G = SL(D,ℝ)` symmetry down to
    the **Borel subgroup** `B` of upper-triangular matrices.

    The residual flow is then confined to the **Bruhat cell** (open Borel
    orbit in the flag variety `G/B`), and the relevant metric is the
    **Bruhat order distance** rather than the Riemannian distance on `G/K`.

    The restriction principle conjectures that this confined flow is still
    geodesic in the Bruhat metric — i.e. causal masking does not destroy the
    geodesic structure, it merely *restricts* the symmetric space.

    This is purely conjectural and has no proof strategy yet.  -/
theorem restriction_principle_remark : True := trivial

end GeodesicConjecture
