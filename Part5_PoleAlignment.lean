import Part5_CauchyVFBridge

/-!
# Part 5 — Pole alignment (Part 2 ⇒ contour–Hamiltonian bridge)

This file formalises **why** `contourVF_query_matches_sl2` and
`contourVF_logBandwidth_matches_sl2` cannot hold for arbitrary
`(scores, keys, log_heights)` (your numerical checks), and what **does**
hold on the Part 2 score-derived slice.

## The discovery (structural)

* **Vertical score-derived poles** (`keys k = q`, heights from softmax):
  `poisson(x, y, q)` is constant in `q` when `x = q`, so `∂_q contour = 0`
  while the Möbius generator `α − β·q` is generally **non-zero**.
  The sl(2) vector field lives on the **Siegel embedding**, not on raw
  `∂_q contourOutput` at a vertical slice.

* **General off-query keys** need the frozen-head linearisation identities
  from Part 2 (`softmax_pole_log_ratio`, `softmax_offquery_bandwidth_bound`).
  Those are the hypotheses in `GeodesicContourSL2Alignment`.

When `Part2_TheFullModel` compiles, replace the mirrored definitions below with
`import Part2_TheFullModel` and `scorePoles` / `scoreDerivedPoleHeight` from Part 1.
-/

noncomputable section

open Finset Real GeodesicCauchyBridge AnalyticTransformer

namespace PoleAlignment

variable {N D : ℕ} [NeZero N]

-- ═══════════════════════════════════════════════════════════════════════
-- §P.1  Part 2 score-derived pole data (mirrored until Part 1/2 import)
-- ═══════════════════════════════════════════════════════════════════════

/-- Softmax partition function `Z = Σ_j exp(s_j)`. -/
noncomputable def softmaxZ (scores : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, Real.exp (scores j)

theorem softmaxZ_pos (scores : Fin N → ℝ) : 0 < softmaxZ scores :=
  Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty

/-- Log-height from scores: `log y_k = log Z − s_k` (Part 1 `softmax_pole_log_ratio`). -/
noncomputable def scoreDerivedLogHeight (scores : Fin N → ℝ) (k : Fin N) : ℝ :=
  Real.log (softmaxZ scores) - scores k

/-- Pole height `y_k = Z / exp(s_k)` (Part 1 `scoreDerivedPoleHeight`). -/
noncomputable def scoreDerivedPoleHeight (scores : Fin N → ℝ) (k : Fin N) : ℝ :=
  softmaxZ scores / Real.exp (scores k)

theorem scoreDerivedPoleHeight_pos (scores : Fin N → ℝ) (k : Fin N) :
    0 < scoreDerivedPoleHeight scores k := by
  unfold scoreDerivedPoleHeight
  exact div_pos (softmaxZ_pos scores) (Real.exp_pos _)

theorem scoreDerivedPoleHeight_eq_exp_logHeight (scores : Fin N → ℝ) (k : Fin N) :
    scoreDerivedPoleHeight scores k =
      Real.exp (scoreDerivedLogHeight scores k) := by
  unfold scoreDerivedPoleHeight scoreDerivedLogHeight
  show softmaxZ scores / Real.exp (scores k) =
      Real.exp (Real.log (softmaxZ scores) - scores k)
  rw [Real.exp_sub, Real.exp_log (softmaxZ_pos scores)]

theorem scoreDerivedLogHeight_eq_log_y (scores : Fin N → ℝ) (k : Fin N) :
    scoreDerivedLogHeight scores k =
      Real.log (scoreDerivedPoleHeight scores k) := by
  calc
    scoreDerivedLogHeight scores k =
        Real.log (Real.exp (scoreDerivedLogHeight scores k)) :=
      (Real.log_exp _).symm
    _ = Real.log (scoreDerivedPoleHeight scores k) := by
      rw [scoreDerivedPoleHeight_eq_exp_logHeight]

theorem Poles.ext {p₁ p₂ : Poles N} (hx : p₁.x = p₂.x) (hy : p₁.y = p₂.y) : p₁ = p₂ := by
  rcases p₁ with ⟨_, _, _⟩
  rcases p₂ with ⟨_, _, _⟩
  subst hx
  subst hy
  rfl

/-- Part 2 `scorePoles scores q`: vertical slice above the query. -/
def scorePoles (scores : Fin N → ℝ) (q : ℝ) : Poles N where
  x := fun _ => q
  y := scoreDerivedPoleHeight scores
  im_pos := scoreDerivedPoleHeight_pos scores

/-- Heights match the Gibbs / score-derived law from Part 2. -/
def HasScoreDerivedHeights (scores log_heights : Fin N → ℝ) : Prop :=
  ∀ k : Fin N, log_heights k = scoreDerivedLogHeight scores k

/-- Every key sits on the query (vertical realised slice). -/
def OnQueryVerticalSlice (keys : Fin N → ℝ) (q : ℝ) : Prop :=
  ∀ k : Fin N, keys k = q

/-- **Frozen Part 2 row** at query `q`: score-derived heights and vertical keys. -/
structure FrozenScoreDerivedSlice (scores keys log_heights : Fin N → ℝ) (q : ℝ) where
  heights : HasScoreDerivedHeights scores log_heights
  vertical : OnQueryVerticalSlice keys q

/-- Keys are not all equal to the query (non-degenerate geodesic embedding). -/
def IsOffQuery (keys : Fin N → ℝ) (q : ℝ) : Prop :=
  ∃ k : Fin N, keys k ≠ q

-- ═══════════════════════════════════════════════════════════════════════
-- §P.2  Alignment links `geodesicPoles` to Part 2 `scorePoles`
-- ═══════════════════════════════════════════════════════════════════════

theorem geodesicPoles_eq_scorePoles {scores keys log_heights : Fin N → ℝ} {q : ℝ}
    (hslice : FrozenScoreDerivedSlice scores keys log_heights q) :
    geodesicPoles keys log_heights = scorePoles scores q := by
  apply Poles.ext
  · funext k
    simpa [geodesicPoles, scorePoles] using hslice.vertical k
  · funext k
    simp only [geodesicPoles, scorePoles]
    rw [hslice.heights k, scoreDerivedPoleHeight_eq_exp_logHeight]

theorem softmaxWeight_eq_inv_height (scores : Fin N → ℝ) (k : Fin N) :
    softmaxWeight scores k = (scoreDerivedPoleHeight scores k)⁻¹ := by
  unfold softmaxWeight scoreDerivedPoleHeight softmaxZ
  have hZ : (0 : ℝ) < ∑ j : Fin N, Real.exp (scores j) := softmaxZ_pos scores
  have hek : (0 : ℝ) < Real.exp (scores k) := Real.exp_pos _
  field_simp [hZ.ne', hek.ne']

theorem inv_scoreDerived_eq_softmaxWeight (scores : Fin N → ℝ) (k : Fin N) :
    (scoreDerivedPoleHeight scores k)⁻¹ = softmaxWeight scores k :=
  (softmaxWeight_eq_inv_height scores k).symm

-- ═══════════════════════════════════════════════════════════════════════
-- §P.3  Proved vertical-slice calculus (why the gap is not "generic")
-- ═══════════════════════════════════════════════════════════════════════

/-- On the vertical slice `x = q`, `∂/∂q` of the Poisson kernel vanishes. -/
theorem poisson_partial_q_on_query (q y : ℝ) :
    poisson_partial_q q y q = 0 := by
  unfold poisson_partial_q
  simp

/-- On the vertical slice, `∂/∂(log y)` kernel value at `x = q`. -/
theorem poisson_partial_logY_on_query {q y : ℝ} (hy : 0 < y) :
    poisson_partial_logY q y q = -1 / y := by
  unfold poisson_partial_logY
  have hD : (q - q) ^ 2 + y ^ 2 = y ^ 2 := by ring
  have hyne : y ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hy)
  rw [hD]
  field_simp [hy.ne']
  ring

/-- **Vertical obstruction:** contour `∂_q` is identically zero on a score-derived
    vertical slice, while the Möbius target `α − β·q` is generally non-zero. -/
theorem contourVF_query_eq_zero_of_vertical
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq)) :
    contourVF_query dq dy keys log_heights h = 0 := by
  unfold contourVF_query contour_partial_q geodesicResidue geodesicPoles
  have hterm :
      ∀ k : Fin N,
        poisson_partial_q (keys k) (Real.exp (log_heights k)) (h dq) = 0 := by
    intro k
    rw [hslice.vertical k]
    rw [show Real.exp (log_heights k) = scoreDerivedPoleHeight scores k from by
      rw [hslice.heights k, ← scoreDerivedPoleHeight_eq_exp_logHeight]]
    exact poisson_partial_q_on_query (h dq) _ 
  simp_rw [hterm, mul_zero, Finset.sum_const_zero]

/-- At the linearisation point `η = h dy = 0`, vertical score-derived poles give
    `∂_η contour|_{dq} = −Σ w_k`. -/
theorem contourVF_logBandwidth_eq_neg_sum_weights_of_vertical
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq))
    (hη : h dy = 0) :
    contourVF_logBandwidth dq dy keys log_heights h =
      -∑ k : Fin N, softmaxWeight scores k := by
  unfold contourVF_logBandwidth contour_partial_bandwidth geodesicResidue
  have hterm :
      ∀ k : Fin N,
        poisson_partial_logY (keys k) (Real.exp (log_heights k + h dy)) (h dq) =
          -softmaxWeight scores k := by
    intro k
    have hy : 0 < scoreDerivedPoleHeight scores k := scoreDerivedPoleHeight_pos scores k
    have hkeys : keys k = h dq := hslice.vertical k
    have hyexp : Real.exp (log_heights k + h dy) = scoreDerivedPoleHeight scores k := by
      rw [hη, add_zero, hslice.heights k, ← scoreDerivedPoleHeight_eq_exp_logHeight]
    calc
      poisson_partial_logY (keys k) (Real.exp (log_heights k + h dy)) (h dq)
          = poisson_partial_logY (h dq) (scoreDerivedPoleHeight scores k) (h dq) := by
            congr 1 <;> rw [hkeys, hyexp]
      _ = -1 / scoreDerivedPoleHeight scores k :=
            poisson_partial_logY_on_query hy
      _ = -softmaxWeight scores k := by
            rw [neg_div, one_div, inv_scoreDerived_eq_softmaxWeight]
  simp only [geodesicResidue, ↓reduceIte, one_mul]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  simpa using hterm k

-- ═══════════════════════════════════════════════════════════════════════
-- §P.4  The alignment hypothesis for closing the two sorries
-- ═══════════════════════════════════════════════════════════════════════

/-!
### `GeodesicContourSL2Alignment`

This is the **Part 2 ⇒ Part 5 bridge** in one record.  It packages exactly the
two Fréchet identities needed to identify `contourVF_*` with `sl2Generator`.

Constructing an instance is the frozen analytic lock:
* `heights` — Gibbs law (`softmax_pole_log_ratio` / `scoreDerivedLogHeight`);
* `off_query` — keys are genuine boundary positions, not the vertical degeneracy;
* `query_moment` / `bandwidth_moment` — the contour derivatives collapse to the
  Möbius generator (the open mathematics).

When `Part2_TheFullModel` is available, a `HeadParams` / `scoreDerivedAnalyticHead`
row at the linearisation point should induce this structure.
-/

/-- **Contour–Hamiltonian alignment** at frozen linearisation point `q = h dq`. -/
structure GeodesicContourSL2Alignment (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : Prop where
  /-- Part 2 height law: `log y_k = log Z − s_k`. -/
  heights : HasScoreDerivedHeights scores log_heights
  /-- Non-vertical keys (avoids `contourVF_query = 0` obstruction). -/
  off_query : IsOffQuery keys (h dq)
  /-- `∂_q contour|_{dq} = α − β·q`. -/
  query_moment :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq
  /-- `∂_η contour|_{dy} = −β`. -/
  bandwidth_moment :
    contourVF_logBandwidth dq dy keys log_heights h =
      -sl2Beta scores log_heights

/-- Score-derived heights + off-query keys (necessary, not sufficient). -/
structure FrozenHeadPoleHypothesis (scores keys log_heights : Fin N → ℝ) (q : ℝ) where
  heights : HasScoreDerivedHeights scores log_heights
  off_query : IsOffQuery keys q

-- ═══════════════════════════════════════════════════════════════════════
-- §P.5  Closing the bridge sorries under alignment
-- ═══════════════════════════════════════════════════════════════════════

theorem contourVF_query_matches_sl2_of_alignment
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (halign : GeodesicContourSL2Alignment dq dy scores keys log_heights h) :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq :=
  halign.query_moment

theorem contourVF_logBandwidth_matches_sl2_of_alignment
    (dq dy : Fin D) (scores log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (halign : GeodesicContourSL2Alignment dq dy scores keys log_heights h) :
    contourVF_logBandwidth dq dy keys log_heights h =
      -sl2Beta scores log_heights :=
  halign.bandwidth_moment

/-- **Target lemma (query):** reduce to alignment.  The `sorry` is now a single
    obligation: build `GeodesicContourSL2Alignment` from Part 2 head data. -/
theorem contourVF_query_matches_sl2
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (halign : GeodesicContourSL2Alignment dq dy scores keys log_heights h) :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq :=
  contourVF_query_matches_sl2_of_alignment dq dy scores keys log_heights h halign

/-- **Target lemma (bandwidth):** reduce to alignment. -/
theorem contourVF_logBandwidth_matches_sl2
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (halign : GeodesicContourSL2Alignment dq dy scores keys log_heights h) :
    contourVF_logBandwidth dq dy keys log_heights h =
      -sl2Beta scores log_heights :=
  contourVF_logBandwidth_matches_sl2_of_alignment dq dy scores log_heights h halign

/-- Vertical + score-derived ⇒ contour query derivative is zero (proved). -/
theorem vertical_obstructs_generic_contour_sl2
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq))
    (hsl2 : sl2Alpha scores keys - sl2Beta scores log_heights * h dq ≠ 0) :
    ¬ GeodesicContourSL2Alignment dq dy scores keys log_heights h := by
  intro halign
  have hz := contourVF_query_eq_zero_of_vertical dq dy scores keys log_heights h hslice
  have hzero : sl2Alpha scores keys - sl2Beta scores log_heights * h dq = 0 := by
    linarith [halign.query_moment, hz]
  exact hsl2 hzero

end PoleAlignment
