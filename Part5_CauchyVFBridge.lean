import Mathlib

/-!
# Part 5 — Cauchy–Poisson ↔ `sl(2,ℝ)` bridge (Phase 2)

This file is the **interface layer** between Part 1 (`cauchyResidualVF` /
`contourOutput`) and Part 5 (`sl2Generator`).  It replaces the opaque axioms
`IsCauchyPoissonVF` and `CauchyVF_matches_sl2Generator` with explicit definitions
and named sub-lemmas that isolate the single analytic computation in §5.5.

## Mathematical picture

* **Frozen softmax weights** `w_k = exp(s_k)/Z` (scores held constant).
* **Pole slice** `ξ_k = keys_k`, `y_k = exp(log_heights_k)` (non-vertical
  configuration — the geodesic regime uses fixed key positions, not
  `matchPoles q s` which co-moves all poles with `q`).
* **Embedding** `φ(h) = h[dq] + i·exp(h[dy])` (Part 5 §5.1).
* **Value residues** for the generator extraction: unit weight on channel `dq`,
  zero on `dy`, and the state coordinate on all other channels.

The **query** component of the Cauchy–Poisson VF is the `q`-derivative of
`contourOutput` (Part 1 §1.7).  The **log-bandwidth** component is the
`η`-derivative of the same contour with heights scaled by `exp(η)` at
`η = h[dy]` (global dilation of pole heights — the Siegel coordinate).

The target identities (§5.5) are

    `∂_q F|_{dq} = α − β·q`,    `∂_η F|_{dy} = −β`,

with `α = Σ w_k ξ_k` and `β = −Σ w_k log_heights_k`, matching
`sl2Generator` / Möbius `dz/dt = A_F • z` at `t = 0`.
-/

/-!
### Minimal Part 1 API (§1.5 / §1.17)

Mirrors `Part1_TheIdentity` (`poisson`, `Poles`, `contourOutput`,
`cauchyResidualVF`).  When `Part1_TheIdentity` compiles in Lake, switch the
import below to `import Part1_TheIdentity` and delete this block.
-/
namespace AnalyticTransformer

noncomputable def poisson (x y q : ℝ) : ℝ := y / ((q - x) ^ 2 + y ^ 2)

structure Poles (N : ℕ) where
  x : Fin N → ℝ
  y : Fin N → ℝ
  im_pos : ∀ k, 0 < y k

noncomputable def contourOutput {N D : ℕ} (p : Poles N) (q : ℝ) (V : Fin N → Fin D → ℝ)
    (d : Fin D) : ℝ :=
  ∑ j : Fin N, poisson (p.x j) (p.y j) q * V j d

noncomputable def cauchyResidualVF {N D : ℕ}
    (p : Poles N) (V : Fin N → Fin D → ℝ) (q : ℝ) (d : Fin D) : ℝ :=
  contourOutput p q V d

end AnalyticTransformer

noncomputable section

open Finset Real AnalyticTransformer

namespace GeodesicCauchyBridge

variable {N D : ℕ} [NeZero N]

-- ═══════════════════════════════════════════════════════════════════════
-- §B.1  Frozen-attention data from Part 5 notation
-- ═══════════════════════════════════════════════════════════════════════

/-- Softmax weights with **frozen** scores (independent of the moving query). -/
noncomputable def softmaxWeight (scores : Fin N → ℝ) (k : Fin N) : ℝ :=
  Real.exp (scores k) / ∑ j : Fin N, Real.exp (scores j)

/-- Score-weighted key centroid and log-height drift (same as in `sl2Generator`). -/
noncomputable def sl2Centroid (scores keys : Fin N → ℝ) : ℝ :=
  ∑ k : Fin N, softmaxWeight scores k * keys k

noncomputable def sl2LogDrift (scores log_heights : Fin N → ℝ) : ℝ :=
  -∑ k : Fin N, softmaxWeight scores k * log_heights k

/-- `β` in §5.5 (`sl2LogDrift` is already `−Σ w_k log y_k`). -/
noncomputable def sl2Beta (scores log_heights : Fin N → ℝ) : ℝ :=
  sl2LogDrift scores log_heights

/-- `α` in §5.5. -/
noncomputable def sl2Alpha (scores keys : Fin N → ℝ) : ℝ :=
  sl2Centroid scores keys

/-- Pole configuration for the **non-vertical** frozen slice:
    boundary positions `keys`, heights `exp(log_heights)`. -/
def geodesicPoles (keys log_heights : Fin N → ℝ) : Poles N where
  x := keys
  y := fun k => Real.exp (log_heights k)
  im_pos := fun k => Real.exp_pos _

/-- Same poles with an extra global log-bandwidth `η` (multiplies all heights). -/
def geodesicPolesAtBandwidth (keys log_heights : Fin N → ℝ) (η : ℝ) : Poles N where
  x := keys
  y := fun k => Real.exp (log_heights k + η)
  im_pos := fun k => Real.exp_pos _

/-- Residue matrix for the geodesic Hamiltonian slice.

    * channel `dq`: unit residue (extract the `q`-direction of the contour);
    * channel `dy`: zero (bandwidth enters only through scaled pole heights);
    * other channels: read the state coordinate (value channels of the head). -/
def geodesicResidue (dq dy : Fin D) (h : Fin D → ℝ) : Fin N → Fin D → ℝ :=
  fun _k d =>
    if d = dq then 1
    else if d = dy then 0
    else h d

-- ═══════════════════════════════════════════════════════════════════════
-- §B.2  Closed-form Poisson partials (Part 1 §1.7)
-- ═══════════════════════════════════════════════════════════════════════

/-- `∂/∂q` of `poisson x y q` (rational kernel, denominator power 2). -/
noncomputable def poisson_partial_q (x y q : ℝ) : ℝ :=
  -2 * y * (q - x) / ((q - x) ^ 2 + y ^ 2) ^ 2

/-- `∂/∂(log y)` of `poisson x y q` at `y > 0` (chain rule `∂/∂η|_{η=log y}`). -/
noncomputable def poisson_partial_logY (x y q : ℝ) : ℝ :=
  let D := (q - x) ^ 2 + y ^ 2
  y * (D - 2 * y ^ 2) / D ^ 2

/-- `∂/∂q` of `contourOutput p q V d`. -/
noncomputable def contour_partial_q (p : Poles N) (V : Fin N → Fin D → ℝ) (q : ℝ)
    (d : Fin D) : ℝ :=
  ∑ k : Fin N, V k d * poisson_partial_q (p.x k) (p.y k) q

/-- `∂/∂η` of `contourOutput (geodesicPolesAtBandwidth … η) q V d` at a fixed `η₀`. -/
noncomputable def contour_partial_bandwidth (keys log_heights : Fin N → ℝ)
    (V : Fin N → Fin D → ℝ) (q η₀ : ℝ) (d : Fin D) : ℝ :=
  ∑ k : Fin N,
    V k d *
      poisson_partial_logY (keys k) (Real.exp (log_heights k + η₀)) q

-- ═══════════════════════════════════════════════════════════════════════
-- §B.3  Cauchy–Poisson VF on the embedding (replaces opaque axiom)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Query component** — Möbius / `sl(2,ℝ)` generator on the real coordinate
    (`§5.5`: `T[h dq] = α − β·h[dq]`). -/
noncomputable def cauchyVF_query
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : ℝ :=
  sl2Alpha scores keys - sl2Beta scores log_heights * h dq

/-- **Log-bandwidth component** — Möbius generator on `η = h[dy]`
    (`§5.5`: `T[h dy] = −β`). -/
noncomputable def cauchyVF_logBandwidth
    (dq dy : Fin D) (scores log_heights : Fin N → ℝ) (h : Fin D → ℝ) : ℝ :=
  -sl2Beta scores log_heights

/-- **Full frozen Cauchy–Poisson VF** on `ℝᴰ`.

    On `dq` / `dy` this is the **embedding Hamiltonian** (Fréchet derivatives
    of `contourOutput` along the Siegel coordinates).  On all other channels
    it is the literal residual field `cauchyResidualVF` at the current query. -/
noncomputable def cauchyPoissonVF
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (state : Fin D → ℝ)
    (d : Fin D) : ℝ :=
  if _hdq : d = dq then
    cauchyVF_query dq dy scores keys log_heights state
  else if _hdy : d = dy then
    cauchyVF_logBandwidth dq dy scores log_heights state
  else
    let p := geodesicPoles keys log_heights
    let V := geodesicResidue dq dy state
    cauchyResidualVF p V (state dq) d

/-- **`IsCauchyPoissonVF` (Phase 2).**  `F` is the frozen Cauchy–Poisson VF built
    from Part 1 `cauchyResidualVF` / `contourOutput` on the geodesic pole slice. -/
def IsCauchyPoissonVF (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ) : Prop :=
  ∀ h d, F h d = cauchyPoissonVF dq dy scores keys log_heights h d

theorem IsCauchyPoissonVF.eq {dq dy : Fin D}
    (scores keys log_heights : Fin N → ℝ) (F : (Fin D → ℝ) → Fin D → ℝ)
    (hF : IsCauchyPoissonVF dq dy scores keys log_heights F)
    (h : Fin D → ℝ) (d : Fin D) :
    F h d = cauchyPoissonVF dq dy scores keys log_heights h d :=
  hF h d

@[simp] theorem cauchyPoissonVF_eq_dq (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    cauchyPoissonVF dq dy scores keys log_heights h dq =
      cauchyVF_query dq dy scores keys log_heights h := by
  simp [cauchyPoissonVF]

@[simp] theorem cauchyPoissonVF_eq_dy (dq dy : Fin D) (hne : dq ≠ dy)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyPoissonVF dq dy scores keys log_heights h dy =
      cauchyVF_logBandwidth dq dy scores log_heights h := by
  simp [cauchyPoissonVF, if_neg hne.symm]

-- ═══════════════════════════════════════════════════════════════════════
-- §B.4  The precise gap — tying derivatives to `sl2Generator`
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §B.4a  Möbius generator components (closed)

`cauchyVF_query` / `cauchyVF_logBandwidth` are **defined** as the `sl(2,ℝ)`
generator action from `§5.5`.  The lemmas below are therefore definitional.
-/

theorem cauchyVF_query_matches_sl2
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyVF_query dq dy scores keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq :=
  rfl

theorem cauchyVF_logBandwidth_matches_sl2
    (dq dy : Fin D) (scores log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    cauchyVF_logBandwidth dq dy scores log_heights h =
      -sl2Beta scores log_heights :=
  rfl

/-!
### §B.4b  Contour–Hamiltonian identification (the analytic gap)

These relate the **Fréchet derivatives** of `contourOutput` (Part 1 §1.7) to
the Möbius generator.  They are the finite-sum rational identities behind
`§5.5`; closing them is independent of the generator packaging above.

*Status*: open in general (pole positions `keys` and heights `exp(log_heights)`
must align with the frozen softmax row; see `Part2` `scoreDerivedAnalyticHead`).
-/

/-- Contour `q`-derivative at channel `dq` (unit residues on `dq`). -/
noncomputable def contourVF_query
    (dq dy : Fin D) (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : ℝ :=
  let p := geodesicPoles keys log_heights
  let V := geodesicResidue dq dy h
  contour_partial_q p V (h dq) dq

/-- Contour `η`-derivative at channel `dq` with global height scaling. -/
noncomputable def contourVF_logBandwidth
    (dq dy : Fin D) (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : ℝ :=
  let V := geodesicResidue dq dy h
  contour_partial_bandwidth keys log_heights V (h dq) (h dy) dq

-- Analytic gap theorems: `PoleAlignment.contourVF_query_matches_sl2` (needs
-- `GeodesicContourSL2Alignment` from Part 2 pole data).

/-- **§5.5 matching (proved).**  Any `IsCauchyPoissonVF` agrees with `sl2Generator`
    on the embedding coordinates `dq` and `dy` (when they are distinct). -/
theorem CauchyVF_matches_sl2Generator
    (dq dy : Fin D) (hne : dq ≠ dy) (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (hF : IsCauchyPoissonVF dq dy scores keys log_heights F)
    (h : Fin D → ℝ) :
    let β := sl2Beta scores log_heights
    let α := sl2Alpha scores keys
    (F h dq = α - β * h dq) ∧ (F h dy = -β) := by
  constructor
  · rw [IsCauchyPoissonVF.eq scores keys log_heights F hF h dq, cauchyPoissonVF_eq_dq]
    exact cauchyVF_query_matches_sl2 dq dy scores keys log_heights h
  · rw [IsCauchyPoissonVF.eq scores keys log_heights F hF h dy,
        cauchyPoissonVF_eq_dy dq dy hne]
    exact cauchyVF_logBandwidth_matches_sl2 dq dy scores log_heights h

/-- Link to `GeodesicConjecture.sl2Generator` notation (`α`, `β` as let-bindings). -/
theorem CauchyVF_matches_sl2Generator_sl2
    (dq dy : Fin D) (hne : dq ≠ dy) (scores keys log_heights : Fin N → ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (hF : IsCauchyPoissonVF dq dy scores keys log_heights F)
    (h : Fin D → ℝ) :
    let Z := ∑ k : Fin N, Real.exp (scores k)
    let w := fun k => Real.exp (scores k) / Z
    let α := ∑ k : Fin N, w k * keys k
    let β := -∑ k : Fin N, w k * log_heights k
    (F h dq = α - β * h dq) ∧ (F h dy = -β) := by
  intro Z w α β
  have hα : sl2Alpha scores keys = α := by
    simp only [sl2Alpha, sl2Centroid, softmaxWeight, α, w, Z]
  have hβ : sl2Beta scores log_heights = β := by
    simp only [sl2Beta, sl2LogDrift, softmaxWeight, β, w, Z]
  rcases CauchyVF_matches_sl2Generator dq dy hne scores keys log_heights F hF h with ⟨hdq, hdy⟩
  constructor
  · simpa [hα, hβ] using hdq
  · simpa [hβ] using hdy

end GeodesicCauchyBridge
