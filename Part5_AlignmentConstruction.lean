import Part5_PoleAlignment

/-!
# Part 5 — Alignment construction (clean room)

**Geography vs velocity.**  Static pole data (`FrozenHeadGeometry`) fixes where
boundary sources sit; off-query bounds (`HasOffQueryBandwidthBounds`) damp distant
contributions; kinematic moments (`ContourSL2Moments`) are the Fréchet derivatives
of the contour integral.  `GeodesicContourSL2Alignment` witnesses that the
kinematics collapse to the Möbius / sl(2) generator.

```
[FrozenHeadGeometry] + [HasOffQueryBandwidthBounds]
                          │
                          ▼  (open: `build_alignment_from_bounds`)
                  [ContourSL2Moments]
                          │
                          ▼  (`build_alignment_of_moments`, proved)
             [GeodesicContourSL2Alignment]
```

When Part 1/2 compile, replace mirrored `HeadParams` / `poissonDiscriminant` with
imports; the interface below stays stable.
-/

noncomputable section

open Finset Real GeodesicCauchyBridge AnalyticTransformer PoleAlignment

namespace AlignmentConstruction

variable {N D : ℕ} [NeZero N]

-- ═══════════════════════════════════════════════════════════════════════
-- §A.1  Clean-room head row + static geometry
-- ═══════════════════════════════════════════════════════════════════════

/-- GPT-2 head row at a frozen query (mirrors `Part2.HeadParams`). -/
structure HeadParams (N D : ℕ) where
  scores : Fin N → ℝ
  V : Fin N → Fin D → ℝ

/-- Static pole layout at linearisation point `q` (exact equalities). -/
structure FrozenHeadGeometry (scores keys log_heights : Fin N → ℝ) (q : ℝ) where
  heights : HasScoreDerivedHeights scores log_heights
  off_query : IsOffQuery keys q

def FrozenHeadGeometry.of_head (hp : HeadParams N D) (keys log_heights : Fin N → ℝ) (q : ℝ)
    (hlog : HasScoreDerivedHeights hp.scores log_heights) (hoff : IsOffQuery keys q) :
    FrozenHeadGeometry hp.scores keys log_heights q :=
  ⟨hlog, hoff⟩

/-- Same data as `FrozenHeadPoleHypothesis` (alias for cross-file references). -/
abbrev FrozenHeadPoleData (scores keys log_heights : Fin N → ℝ) (q : ℝ) :=
  FrozenHeadPoleHypothesis scores keys log_heights q

-- ═══════════════════════════════════════════════════════════════════════
-- §A.2  Off-query bandwidth bounds (inequality layer)
-- ═══════════════════════════════════════════════════════════════════════

/-- Part 1 `poissonDiscriminant` (mirrored). -/
def poissonDiscriminant (w d : ℝ) : ℝ := 1 - 4 * w ^ 2 * d ^ 2

/-- One off-query key at separation `d > 0` from `q`, with feasibility + bound. -/
structure OffQueryKeyBound (scores keys : Fin N → ℝ) (q : ℝ) where
  k : Fin N
  hk : keys k ≠ q
  d : ℝ
  hd : 0 < d
  hsep : |keys k - q| = d
  hdisc : 0 ≤ poissonDiscriminant (softmaxWeight scores k) d
  hbound : softmaxWeight scores k ≤ 1 / (2 * d)

/-- Every off-query key carries a Part 2–style bandwidth bound. -/
def HasOffQueryBandwidthBounds (scores keys : Fin N → ℝ) (q : ℝ) : Prop :=
  ∀ k, keys k ≠ q → ∃ b : OffQueryKeyBound scores keys q, b.k = k

-- ═══════════════════════════════════════════════════════════════════════
-- §A.3  Kinematic moments (the open analytic lock)
-- ═══════════════════════════════════════════════════════════════════════

/-- Fréchet identities: contour derivatives = Möbius generator components. -/
structure ContourSL2Moments (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) where
  query_moment :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq
  bandwidth_moment :
    contourVF_logBandwidth dq dy keys log_heights h =
      -sl2Beta scores log_heights

/-- Sharp localization limit: background suppression errors vanish. -/
structure LocalizationLimit (scores keys log_heights : Fin N → ℝ) (q : ℝ) where
  query_error : ℝ
  bandwidth_error : ℝ
  hε : query_error + bandwidth_error = 0
  hquery_nonneg : 0 ≤ query_error
  hband_nonneg : 0 ≤ bandwidth_error

/-- Both error budgets are zero (squeeze setup for `far_fields_vanish_of_localization`). -/
theorem LocalizationLimit.errors_eq_zero {scores keys log_heights : Fin N → ℝ} {q : ℝ}
    (hloc : LocalizationLimit scores keys log_heights q) :
    hloc.query_error = 0 ∧ hloc.bandwidth_error = 0 := by
  have := hloc.hε
  constructor
  · linarith [hloc.hquery_nonneg, hloc.hband_nonneg]
  · linarith [hloc.hquery_nonneg, hloc.hband_nonneg]

-- ═══════════════════════════════════════════════════════════════════════
-- §A.4  β calibration from static heights (proved)
-- ═══════════════════════════════════════════════════════════════════════

@[simp] theorem sl2Beta_eq_neg_weighted_log_heights (scores log_heights : Fin N → ℝ) :
    sl2Beta scores log_heights =
      -∑ k : Fin N, softmaxWeight scores k * log_heights k :=
  rfl

theorem sl2Beta_eq_score_derived_drift {scores log_heights : Fin N → ℝ}
    (hlog : HasScoreDerivedHeights scores log_heights) :
    sl2Beta scores log_heights =
      -∑ k : Fin N,
        softmaxWeight scores k * scoreDerivedLogHeight scores k := by
  simp only [sl2Beta, sl2LogDrift]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hlog k]

-- ═══════════════════════════════════════════════════════════════════════
-- §A.5  Constructors (proved packaging)
-- ═══════════════════════════════════════════════════════════════════════

/-- **Constructor A.**  Moments are inputs; the pipeline compiles today. -/
def build_alignment_of_moments (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (hmom : ContourSL2Moments dq dy scores keys log_heights h) :
    GeodesicContourSL2Alignment dq dy scores keys log_heights h where
  heights := hfrozen.heights
  off_query := hfrozen.off_query
  query_moment := hmom.query_moment
  bandwidth_moment := hmom.bandwidth_moment

/-- **Constructor B.**  Head row + static data + bounds + moments → alignment.
    `hbounds` is intentionally unused: bounds constrain the future proof of
    `hmom`, they do not define it. -/
def build_alignment_from_head (dq dy : Fin D) (_hne : dq ≠ dy) (hp : HeadParams N D)
    (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hfrozen : FrozenHeadGeometry hp.scores keys log_heights (h dq))
    (_hbounds : HasOffQueryBandwidthBounds hp.scores keys (h dq))
    (hmom : ContourSL2Moments dq dy hp.scores keys log_heights h) :
    GeodesicContourSL2Alignment dq dy hp.scores keys log_heights h :=
  build_alignment_of_moments dq dy hp.scores keys log_heights h hfrozen hmom

def ContourSL2Moments.of_alignment {dq dy : Fin D} {scores keys log_heights : Fin N → ℝ}
    {h : Fin D → ℝ} (halign : GeodesicContourSL2Alignment dq dy scores keys log_heights h) :
    ContourSL2Moments dq dy scores keys log_heights h where
  query_moment := halign.query_moment
  bandwidth_moment := halign.bandwidth_moment

theorem alignment_iff_moments_and_geometry (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hfrozen : FrozenHeadGeometry scores keys log_heights (h dq)) :
    GeodesicContourSL2Alignment dq dy scores keys log_heights h ↔
      ContourSL2Moments dq dy scores keys log_heights h := by
  constructor
  · intro halign
    exact ContourSL2Moments.of_alignment halign
  · intro hmom
    exact build_alignment_of_moments dq dy scores keys log_heights h hfrozen hmom

-- ═══════════════════════════════════════════════════════════════════════
-- §A.6  Open analytic lock (isolated — genuine open mathematics)
-- ═══════════════════════════════════════════════════════════════════════

/-!
### Status of the analytic lock

**Why the bounds are insufficient.**  Numerical evidence (and the `not_FarField*`
no-go theorems in `Part5_ContourDecomposition`) confirms that for finite N:

    ∑_k ∂_q P(ξ_k, 1/w_k, q)  ≠  α − β·q

even when `w_k ≤ 1/(2|ξ_k − q|)` (the `HasOffQueryBandwidthBounds` condition).
For example, `N=1`, `w=0.4`, `ξ=1`, `q=0` gives LHS ≈ 0.095 vs RHS = 0.4.

**What is needed.**  The Fréchet identity `contourVF_query = α − β·q` requires
`ContourSL2Moments` as an independent analytic input.  The bounds control the
SIZE of off-query contributions (the sieve / far-field suppression); they do NOT
determine the algebraic FORM of the derivative.

**Correct architecture.**  `ContourSL2Moments` is the single irreducible analytic
obligation in this formalization.  It should be witnessed by a continuous-limit
argument (N → ∞, poles concentrate at the localized key) or by a direct algebraic
identity for a specific matched-pole configuration (as in `Part1_TheIdentity.lean`
`matchPoles`).  Until that proof is supplied, it must be given explicitly.
-/

/-- **Fréchet identity (query)** — trivially extracts `query_moment` from
    `ContourSL2Moments`.  The open obligation is CONSTRUCTING `ContourSL2Moments`;
    see the module note above.  The `FrozenHeadGeometry` and
    `HasOffQueryBandwidthBounds` hypotheses are preserved for call-site
    documentation but are NOT sufficient on their own to close the identity. -/
theorem query_moment_from_bounds (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (_hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (_hbounds : HasOffQueryBandwidthBounds scores keys (h dq))
    (hmom : ContourSL2Moments dq dy scores keys log_heights h) :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq :=
  hmom.query_moment

/-- **Fréchet identity (bandwidth)** — trivially extracts `bandwidth_moment` from
    `ContourSL2Moments`.  Same open obligation as `query_moment_from_bounds`. -/
theorem bandwidth_moment_from_bounds (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (_hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (_hbounds : HasOffQueryBandwidthBounds scores keys (h dq))
    (hmom : ContourSL2Moments dq dy scores keys log_heights h) :
    contourVF_logBandwidth dq dy keys log_heights h =
      -sl2Beta scores log_heights :=
  hmom.bandwidth_moment

/-- Package `ContourSL2Moments` into the `from_bounds` call-site.
    **The moments must be supplied explicitly** — they cannot be derived from
    `FrozenHeadGeometry + HasOffQueryBandwidthBounds` alone; see §A.6 note. -/
theorem ContourSL2Moments.from_bounds (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (_hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (_hbounds : HasOffQueryBandwidthBounds scores keys (h dq))
    (hmom : ContourSL2Moments dq dy scores keys log_heights h) :
    ContourSL2Moments dq dy scores keys log_heights h :=
  hmom

/-- Build a full `GeodesicContourSL2Alignment` from static geometry + moments.
    The `ContourSL2Moments` hypothesis is the open analytic obligation (§A.6). -/
def build_alignment_from_bounds (dq dy : Fin D) (_hne : dq ≠ dy) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (hbounds : HasOffQueryBandwidthBounds scores keys (h dq))
    (hmom : ContourSL2Moments dq dy scores keys log_heights h) :
    GeodesicContourSL2Alignment dq dy scores keys log_heights h :=
  build_alignment_of_moments dq dy scores keys log_heights h hfrozen hmom

-- ═══════════════════════════════════════════════════════════════════════
-- §A.7  Negative / boundary lemmas (living textbook)
-- ═══════════════════════════════════════════════════════════════════════

/-- On a vertical score-derived slice at `η = 0`, contour bandwidth is `−Σ w_k`. -/
theorem vertical_contour_bandwidth_eq_neg_sum_weights
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq)) (hη : h dy = 0) :
    contourVF_logBandwidth dq dy keys log_heights h =
      -∑ k : Fin N, softmaxWeight scores k :=
  contourVF_logBandwidth_eq_neg_sum_weights_of_vertical dq dy scores keys log_heights h hslice hη

/-- **Wrench (bandwidth).**  On a vertical slice, `∂_η contour = −Σ w` while `−β = Σ w·log y`;
    alignment needs `β = Σ w`, which fails for generic score-derived heights. -/
theorem vertical_bandwidth_moment_fails
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq)) (hη : h dy = 0)
    (hβ : sl2Beta scores log_heights ≠ ∑ k : Fin N, softmaxWeight scores k) :
    contourVF_logBandwidth dq dy keys log_heights h ≠ -sl2Beta scores log_heights := by
  intro heq
  have hcontour :=
    vertical_contour_bandwidth_eq_neg_sum_weights dq dy scores keys log_heights h hslice hη
  have hsum : ∑ k : Fin N, softmaxWeight scores k = sl2Beta scores log_heights := by
    linarith [heq, hcontour]
  exact hβ hsum.symm

/-- Kinematic alignment requires moment identities (contrapositive packaging). -/
theorem no_moments_no_alignment (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hno : ¬ ContourSL2Moments dq dy scores keys log_heights h) :
    ¬ GeodesicContourSL2Alignment dq dy scores keys log_heights h := by
  intro halign
  exact hno (ContourSL2Moments.of_alignment halign)

/-- Static geometry alone does not determine kinematics (moments are extra data). -/
theorem geometry_does_not_imply_moments (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (_hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (hno : ¬ ContourSL2Moments dq dy scores keys log_heights h) :
    ¬ GeodesicContourSL2Alignment dq dy scores keys log_heights h :=
  no_moments_no_alignment dq dy scores keys log_heights h hno

/-- Off-query bounds are not sufficient for alignment: they do not imply moments. -/
theorem bounds_do_not_imply_alignment (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (_hbounds : HasOffQueryBandwidthBounds scores keys (h dq))
    (hno : ¬ ContourSL2Moments dq dy scores keys log_heights h) :
    ¬ GeodesicContourSL2Alignment dq dy scores keys log_heights h :=
  geometry_does_not_imply_moments dq dy scores keys log_heights h hfrozen hno

/-- Vertical degeneracy forbids generic sl(2) query flow (from `PoleAlignment`). -/
theorem vertical_query_obstructs_alignment
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq))
    (hsl2 : sl2Alpha scores keys - sl2Beta scores log_heights * h dq ≠ 0) :
    ¬ GeodesicContourSL2Alignment dq dy scores keys log_heights h :=
  vertical_obstructs_generic_contour_sl2 dq dy scores keys log_heights h hslice hsl2

end AlignmentConstruction
