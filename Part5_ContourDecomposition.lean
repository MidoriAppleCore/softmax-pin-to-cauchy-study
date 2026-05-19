import Part5_AlignmentConstruction

/-!
# Part 5 — Contour decomposition (near-field / far-field)

Multipole-style split of `contourVF_query` and `contourVF_logBandwidth` at the
linearisation point `q = h dq`:

```
contourVF_query = nearFieldQuerySum + farFieldQuerySum
                      (on-query)            (off-query remainder)
```

The far-field sum is packaged as `OffQueryQueryRemainder`.  Vanishing the
remainder (via `HasOffQueryBandwidthBounds` + a localization limit) is the
analytic sieve behind `query_moment_from_bounds` in `Part5_AlignmentConstruction`.
-/

noncomputable section

open Classical
open Finset Real GeodesicCauchyBridge AnalyticTransformer
open PoleAlignment AlignmentConstruction

namespace ContourDecomposition

variable {N D : ℕ} [NeZero N]

-- ═══════════════════════════════════════════════════════════════════════
-- §D.1  Key partition (near vs far)
-- ═══════════════════════════════════════════════════════════════════════

/-- Keys on the active query (`ξ_k = q`). -/
def onQueryKeys (keys : Fin N → ℝ) (q : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun k => keys k = q

/-- Keys in the background (`ξ_k ≠ q`). -/
def offQueryKeys (keys : Fin N → ℝ) (q : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun k => keys k ≠ q

theorem mem_onQueryKeys {keys : Fin N → ℝ} {q : ℝ} {k : Fin N} :
    k ∈ onQueryKeys keys q ↔ keys k = q := by
  simp [onQueryKeys, Finset.mem_filter]

theorem mem_offQueryKeys {keys : Fin N → ℝ} {q : ℝ} {k : Fin N} :
    k ∈ offQueryKeys keys q ↔ keys k ≠ q := by
  simp [offQueryKeys, Finset.mem_filter]

theorem onQueryKeys_disjoint_offQueryKeys (keys : Fin N → ℝ) (q : ℝ) :
    Disjoint (onQueryKeys keys q) (offQueryKeys keys q) := by
  simp [Finset.disjoint_filter, onQueryKeys, offQueryKeys]

theorem onQueryKeys_union_offQueryKeys (keys : Fin N → ℝ) (q : ℝ) :
    onQueryKeys keys q ∪ offQueryKeys keys q = Finset.univ := by
  ext k
  simp only [onQueryKeys, offQueryKeys, Finset.mem_union, Finset.mem_filter]
  rcases Classical.em (keys k = q) with h | h <;> simp [h]

-- ═══════════════════════════════════════════════════════════════════════
-- §D.2  Query-channel multipole terms
-- ═══════════════════════════════════════════════════════════════════════

/-- Single-pole contribution to `∂_q contour` at channel `dq` (residue `= 1`). -/
noncomputable def queryPoleContribution (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (k : Fin N) : ℝ :=
  poisson_partial_q (keys k) (Real.exp (log_heights k)) (h dq)

/-- Near-field (`ξ_k = q`) sum. -/
noncomputable def nearFieldQuerySum (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  ∑ k ∈ onQueryKeys keys (h dq), queryPoleContribution dq dy keys log_heights h k

/-- Far-field (`ξ_k ≠ q`) sum — the off-query remainder. -/
noncomputable def farFieldQuerySum (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  ∑ k ∈ offQueryKeys keys (h dq), queryPoleContribution dq dy keys log_heights h k

/-- Packaged far-field remainder at `q = h dq`. -/
structure OffQueryQueryRemainder (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) where
  value : ℝ
  hdef : value = farFieldQuerySum dq dy keys log_heights h

def offQueryQueryRemainder (dq dy : Fin D) (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    OffQueryQueryRemainder dq dy keys log_heights h :=
  ⟨farFieldQuerySum dq dy keys log_heights h, rfl⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §D.3  Query decomposition (proved)
-- ═══════════════════════════════════════════════════════════════════════

theorem Finset.sum_univ_partition {α : Type*} [Fintype α] (f : α → ℝ) (p : α → Prop)
    [DecidablePred p] :
    ∑ k, f k =
      ∑ k ∈ Finset.univ.filter p, f k +
        ∑ k ∈ Finset.univ.filter fun k => ¬ p k, f k := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := p)]

theorem contourVF_query_eq_sum_contributions (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    contourVF_query dq dy keys log_heights h =
      ∑ k : Fin N, queryPoleContribution dq dy keys log_heights h k := by
  unfold contourVF_query contour_partial_q geodesicPoles geodesicResidue queryPoleContribution
  simp only [geodesicResidue, ↓reduceIte, one_mul]

theorem contourVF_query_eq_near_plus_far (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    contourVF_query dq dy keys log_heights h =
      nearFieldQuerySum dq dy keys log_heights h +
        farFieldQuerySum dq dy keys log_heights h := by
  rw [contourVF_query_eq_sum_contributions]
  dsimp only [nearFieldQuerySum, farFieldQuerySum]
  rw [Finset.sum_univ_partition (f := queryPoleContribution dq dy keys log_heights h)
    (p := fun k => keys k = h dq)]
  simp only [onQueryKeys, offQueryKeys, add_assoc]

theorem offQueryQueryRemainder_value_eq_far (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    (offQueryQueryRemainder dq dy keys log_heights h).value =
      farFieldQuerySum dq dy keys log_heights h :=
  rfl

/-- On-query keys contribute zero to `∂_q P` at `q`. -/
theorem queryPoleContribution_eq_zero_on_query (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (k : Fin N) (hk : keys k = h dq) :
    queryPoleContribution dq dy keys log_heights h k = 0 := by
  unfold queryPoleContribution
  rw [hk]
  exact poisson_partial_q_on_query (h dq) _

/-- Vertical slice: the entire near-field sum vanishes. -/
theorem nearFieldQuerySum_eq_zero_of_vertical (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hvert : OnQueryVerticalSlice keys (h dq)) :
    nearFieldQuerySum dq dy keys log_heights h = 0 := by
  unfold nearFieldQuerySum
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [mem_onQueryKeys] at hk
  exact queryPoleContribution_eq_zero_on_query dq dy keys log_heights h k hk

/-- Vertical slice: all query kinematics sit in the far-field (which is also zero). -/
theorem contourVF_query_eq_far_of_vertical (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hvert : OnQueryVerticalSlice keys (h dq)) :
    contourVF_query dq dy keys log_heights h =
      farFieldQuerySum dq dy keys log_heights h := by
  rw [contourVF_query_eq_near_plus_far, nearFieldQuerySum_eq_zero_of_vertical dq dy scores keys
    log_heights h hvert]
  ring

-- ═══════════════════════════════════════════════════════════════════════
-- §D.4  Bandwidth-channel multipole terms (η = h dy)
-- ═══════════════════════════════════════════════════════════════════════

/-- Single-pole contribution to `∂_η contour` at channel `dq`. -/
noncomputable def bandwidthPoleContribution (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (k : Fin N) : ℝ :=
  poisson_partial_logY (keys k) (Real.exp (log_heights k + h dy)) (h dq)

noncomputable def nearFieldBandwidthSum (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  ∑ k ∈ onQueryKeys keys (h dq), bandwidthPoleContribution dq dy keys log_heights h k

noncomputable def farFieldBandwidthSum (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  ∑ k ∈ offQueryKeys keys (h dq), bandwidthPoleContribution dq dy keys log_heights h k

structure OffQueryBandwidthRemainder (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) where
  value : ℝ
  hdef : value = farFieldBandwidthSum dq dy keys log_heights h

def offQueryBandwidthRemainder (dq dy : Fin D) (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    OffQueryBandwidthRemainder dq dy keys log_heights h :=
  ⟨farFieldBandwidthSum dq dy keys log_heights h, rfl⟩

theorem contourVF_logBandwidth_eq_sum_contributions (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    contourVF_logBandwidth dq dy keys log_heights h =
      ∑ k : Fin N, bandwidthPoleContribution dq dy keys log_heights h k := by
  unfold contourVF_logBandwidth contour_partial_bandwidth geodesicResidue
    bandwidthPoleContribution
  simp only [geodesicResidue, ↓reduceIte, one_mul]

theorem contourVF_logBandwidth_eq_near_plus_far (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    contourVF_logBandwidth dq dy keys log_heights h =
      nearFieldBandwidthSum dq dy keys log_heights h +
        farFieldBandwidthSum dq dy keys log_heights h := by
  rw [contourVF_logBandwidth_eq_sum_contributions]
  dsimp only [nearFieldBandwidthSum, farFieldBandwidthSum]
  rw [Finset.sum_univ_partition (f := bandwidthPoleContribution dq dy keys log_heights h)
    (p := fun k => keys k = h dq)]
  simp only [onQueryKeys, offQueryKeys, add_assoc]

theorem farFieldBandwidthSum_eq_zero_of_vertical (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq)) :
    farFieldBandwidthSum dq dy keys log_heights h = 0 := by
  unfold farFieldBandwidthSum
  have hempty : offQueryKeys keys (h dq) = ∅ := by
    ext k
    simp [offQueryKeys, Finset.mem_filter, hslice.vertical k]
  rw [hempty]
  simp

theorem nearFieldBandwidthSum_eq_neg_sum_weights_of_vertical
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq)) (hη : h dy = 0) :
    nearFieldBandwidthSum dq dy keys log_heights h =
      -∑ k : Fin N, softmaxWeight scores k := by
  have htot :=
    contourVF_logBandwidth_eq_neg_sum_weights_of_vertical dq dy scores keys log_heights h hslice hη
  have hdec := contourVF_logBandwidth_eq_near_plus_far dq dy keys log_heights h
  have hfar := farFieldBandwidthSum_eq_zero_of_vertical dq dy scores keys log_heights h hslice
  linarith [htot, hdec, hfar]

theorem contourVF_logBandwidth_eq_near_plus_far_of_vertical
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq)) (hη : h dy = 0) :
    contourVF_logBandwidth dq dy keys log_heights h =
      -∑ k : Fin N, softmaxWeight scores k + farFieldBandwidthSum dq dy keys log_heights h := by
  rw [contourVF_logBandwidth_eq_near_plus_far,
    nearFieldBandwidthSum_eq_neg_sum_weights_of_vertical dq dy scores keys log_heights h hslice hη]

-- ═══════════════════════════════════════════════════════════════════════
-- §D.5  Far-field scale (micro-analysis: single-key bound)
-- ═══════════════════════════════════════════════════════════════════════

/-- Explicit query-channel far-field integrand: `w · ∂_q P(ξ, y, q)` at fixed `(ξ, y, q)`. -/
noncomputable def farFieldQueryIntegrand (ξ y w q : ℝ) : ℝ :=
  w * poisson_partial_q ξ y q

/-- **Weighted** far-field sum: `∑_{k off-query} w_k · ∂_q P(ξ_k, y_k, q)`.

    Score-weighted analogue of `farFieldQuerySum`.  Not equal to `contourVF_query`
    (unit residues); see `contourVF_query_eq_sum_contributions`. -/
noncomputable def weightedFarFieldQuerySum (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) : ℝ :=
  ∑ k ∈ offQueryKeys keys (h dq),
    farFieldQueryIntegrand (keys k) (Real.exp (log_heights k)) (softmaxWeight scores k) (h dq)

theorem weightedFarFieldQuerySum_eq_sum_weights (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) :
    weightedFarFieldQuerySum dq dy scores keys log_heights h =
      ∑ k ∈ offQueryKeys keys (h dq),
        softmaxWeight scores k * queryPoleContribution dq dy keys log_heights h k := by
  simp [weightedFarFieldQuerySum, farFieldQueryIntegrand, queryPoleContribution]

/-- Schematic scale `|∂_q P| ∼ 2 y d / (d² + y²)²` at displacement `d = |ξ − q|`. -/
noncomputable def poissonPartialQ_magnitude_bound (y d : ℝ) : ℝ :=
  2 * y * d / (d ^ 2 + y ^ 2) ^ 2

/-- Combined single-key scale `w · |∂_q P|` (before applying `w ≤ 1/(2d)`). -/
noncomputable def offQueryIntegrand_decay_scale (y w d : ℝ) : ℝ :=
  w * poissonPartialQ_magnitude_bound y d

theorem softmaxWeight_nonneg (scores : Fin N → ℝ) (k : Fin N) :
    0 ≤ softmaxWeight scores k := by
  unfold softmaxWeight
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (by
    apply Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty))

theorem poissonPartialQ_magnitude_bound_nonneg {y d : ℝ} (hy : 0 < y) (hd : 0 < d) :
    0 ≤ poissonPartialQ_magnitude_bound y d := by
  unfold poissonPartialQ_magnitude_bound
  positivity

/-- **Micro bound.**  At separation `|ξ − q| = d`, the kernel derivative is `O(y d / (d²+y²)²)`. -/
theorem abs_poisson_partial_q_le_magnitude_bound {x y q d : ℝ} (hd : 0 < d) (hy : 0 < y)
    (hsep : |x - q| = d) :
    |poisson_partial_q x y q| ≤ poissonPartialQ_magnitude_bound y d := by
  unfold poisson_partial_q poissonPartialQ_magnitude_bound
  have hqabs : |q - x| = d := by simpa [abs_sub_comm] using hsep
  have hD :
      (q - x) ^ 2 + y ^ 2 = d ^ 2 + y ^ 2 := by
    calc
      (q - x) ^ 2 + y ^ 2 = |q - x| ^ 2 + y ^ 2 := by rw [sq_abs (q - x)]
      _ = d ^ 2 + y ^ 2 := by rw [hqabs]
  have hDpos : 0 < d ^ 2 + y ^ 2 := by nlinarith
  have hden : ((q - x) ^ 2 + y ^ 2) ^ 2 = (d ^ 2 + y ^ 2) ^ 2 := by
    rw [hD]
  calc
    |poisson_partial_q x y q|
        = |(-2 : ℝ) * y * (q - x)| / |(q - x) ^ 2 + y ^ 2| ^ 2 := by
          simp [poisson_partial_q, abs_div, abs_mul, abs_neg, abs_of_pos hy]
    _ = (2 * y * |q - x|) / ((q - x) ^ 2 + y ^ 2) ^ 2 := by
          field_simp [abs_mul, abs_of_pos hy, hqabs]
    _ ≤ poissonPartialQ_magnitude_bound y d := by
          rw [hden, hqabs]
          rfl

/-- `w · |∂_q P| ≤ w · (2yd/(d²+y²)²)` for nonnegative mass. -/
theorem abs_farFieldQueryIntegrand_le_scale {ξ y w q d : ℝ} (hw : 0 ≤ w) (hd : 0 < d) (hy : 0 < y)
    (hsep : |ξ - q| = d) :
    |farFieldQueryIntegrand ξ y w q| ≤ offQueryIntegrand_decay_scale y w d := by
  dsimp [farFieldQueryIntegrand, offQueryIntegrand_decay_scale]
  rw [abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (abs_poisson_partial_q_le_magnitude_bound hd hy hsep) hw

/-- Under `w ≤ 1/(2d)`, the scale is `O(y / (d²+y²)²)` — i.e. `O(1/d⁴)` when `y = O(1)`. -/
theorem offQueryIntegrand_decay_scale_le_cap {y w d : ℝ} (hd : 0 < d) (hy : 0 < y) (hw : 0 ≤ w)
    (hw_le : w ≤ 1 / (2 * d)) :
    offQueryIntegrand_decay_scale y w d ≤
      poissonPartialQ_magnitude_bound y d * (1 / (2 * d)) := by
  dsimp [offQueryIntegrand_decay_scale]
  have hm := poissonPartialQ_magnitude_bound_nonneg hy hd
  rw [mul_comm (poissonPartialQ_magnitude_bound y d)]
  exact mul_le_mul_of_nonneg_right hw_le hm

/-- Per-key cap from an `OffQueryKeyBound` witness. -/
noncomputable def offQueryIntegrandCap (scores keys : Fin N → ℝ) (q : ℝ)
    (b : OffQueryKeyBound scores keys q) : ℝ :=
  poissonPartialQ_magnitude_bound (scoreDerivedPoleHeight scores b.k) b.d * (1 / (2 * b.d))

/-- Under `OffQueryKeyBound`, a single far integrand is dominated by magnitude × mass cap. -/
def OffQueryIntegrandBounded (scores keys : Fin N → ℝ) (q : ℝ) (b : OffQueryKeyBound scores keys q) :
    Prop :=
  |farFieldQueryIntegrand (keys b.k) (scoreDerivedPoleHeight scores b.k)
      (softmaxWeight scores b.k) q| ≤ offQueryIntegrandCap scores keys q b

theorem offQueryKey_bound_implies_integrand_bound (scores keys : Fin N → ℝ) (q : ℝ)
    (b : OffQueryKeyBound scores keys q) :
    OffQueryIntegrandBounded scores keys q b := by
  dsimp [OffQueryIntegrandBounded, offQueryIntegrandCap]
  let y := scoreDerivedPoleHeight scores b.k
  let w := softmaxWeight scores b.k
  have hy : 0 < y := scoreDerivedPoleHeight_pos scores b.k
  have hw : 0 ≤ w := softmaxWeight_nonneg scores b.k
  have hscale :=
    abs_farFieldQueryIntegrand_le_scale (ξ := keys b.k) (y := y) (w := w) (q := q) hw b.hd hy
      (by simpa [abs_sub_comm] using b.hsep)
  have hcap := offQueryIntegrand_decay_scale_le_cap b.hd hy hw b.hbound
  exact hscale.trans hcap

/-- Actual far summand `∂_q P` (residue `= 1`) is bounded by the kernel magnitude. -/
theorem abs_queryPoleContribution_le_magnitude_bound (dq dy : Fin D)
    (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) (k : Fin N) (y d : ℝ)
    (hd : 0 < d) (hy : 0 < y) (hsep : |keys k - h dq| = d)
    (hy_eq : Real.exp (log_heights k) = y) :
    |queryPoleContribution dq dy keys log_heights h k| ≤
      poissonPartialQ_magnitude_bound y d := by
  dsimp [queryPoleContribution]
  rw [hy_eq]
  exact abs_poisson_partial_q_le_magnitude_bound hd hy (by simpa [abs_sub_comm] using hsep)

theorem abs_weighted_query_integrand_le_cap (scores keys : Fin N → ℝ) (q : ℝ)
    (b : OffQueryKeyBound scores keys q) :
    |farFieldQueryIntegrand (keys b.k) (scoreDerivedPoleHeight scores b.k)
        (softmaxWeight scores b.k) q| ≤ offQueryIntegrandCap scores keys q b :=
  offQueryKey_bound_implies_integrand_bound scores keys q b

theorem offQueryIntegrandCap_nonneg (scores keys : Fin N → ℝ) (q : ℝ)
    (b : OffQueryKeyBound scores keys q) :
    0 ≤ offQueryIntegrandCap scores keys q b := by
  dsimp [offQueryIntegrandCap]
  have hy := scoreDerivedPoleHeight_pos scores b.k
  have hcap : 0 < 1 / (2 * b.d) := one_div_pos.mpr (mul_pos (by norm_num) b.hd)
  exact mul_nonneg (poissonPartialQ_magnitude_bound_nonneg hy b.hd) (le_of_lt hcap)

noncomputable def chosenOffQueryBound (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : keys k ≠ q) :
    OffQueryKeyBound scores keys q :=
  Classical.choose (hbounds k hk)

theorem chosenOffQueryBound_k_eq (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : keys k ≠ q) :
    (chosenOffQueryBound scores keys q k hbounds hk).k = k :=
  Classical.choose_spec (hbounds k hk)

/-- Off-query key in the far finset ⇒ choose a bandwidth witness. -/
theorem keys_ne_of_mem_offQueryKeys {keys : Fin N → ℝ} {q : ℝ} {k : Fin N}
    (hk : k ∈ offQueryKeys keys q) : keys k ≠ q := by
  simpa [offQueryKeys, Finset.mem_filter] using hk

/-- Per-key raw `∂_q P` magnitude cap from an off-query bandwidth witness. -/
noncomputable def farFieldMagnitudeCapAt (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : keys k ≠ q) : ℝ :=
  poissonPartialQ_magnitude_bound (scoreDerivedPoleHeight scores k)
    (chosenOffQueryBound scores keys q k hbounds hk).d

/-- Per-key cap, defined on all indices but zero on the query slice. -/
noncomputable def farFieldMagnitudeCapTerm (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) : ℝ :=
  if hne : keys k ≠ q then
    have hk : k ∈ offQueryKeys keys q := by
      simp [offQueryKeys, Finset.mem_filter, hne]
    farFieldMagnitudeCapAt scores keys q k hbounds (keys_ne_of_mem_offQueryKeys hk)
  else 0

/-- Sum of per-key magnitude caps over the far-field finset. -/
noncomputable def farFieldMagnitudeCapSum (scores keys : Fin N → ℝ) (q : ℝ)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) : ℝ :=
  ∑ k : Fin N, farFieldMagnitudeCapTerm scores keys q k hbounds

theorem farFieldMagnitudeCapTerm_eq_cap (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : k ∈ offQueryKeys keys q) :
    farFieldMagnitudeCapTerm scores keys q k hbounds =
      farFieldMagnitudeCapAt scores keys q k hbounds (keys_ne_of_mem_offQueryKeys hk) := by
  have hne : keys k ≠ q := keys_ne_of_mem_offQueryKeys hk
  dsimp [farFieldMagnitudeCapTerm]
  simp [hne]

theorem farFieldMagnitudeCapTerm_eq_zero_on_query (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : keys k = q) :
    farFieldMagnitudeCapTerm scores keys q k hbounds = 0 := by
  dsimp [farFieldMagnitudeCapTerm]
  simp [hk]

theorem farFieldMagnitudeCapSum_eq_sum (scores keys : Fin N → ℝ) (q : ℝ)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) :
    farFieldMagnitudeCapSum scores keys q hbounds =
      ∑ k ∈ offQueryKeys keys q, farFieldMagnitudeCapTerm scores keys q k hbounds := by
  dsimp [farFieldMagnitudeCapSum]
  rw [Finset.sum_univ_partition
    (f := fun k => farFieldMagnitudeCapTerm scores keys q k hbounds) (p := fun k => keys k = q)]
  have hon :
      ∑ k ∈ onQueryKeys keys q, farFieldMagnitudeCapTerm scores keys q k hbounds = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [mem_onQueryKeys] at hk
    exact farFieldMagnitudeCapTerm_eq_zero_on_query scores keys q k hbounds hk
  have hon' :
      ∑ k with keys k = q, farFieldMagnitudeCapTerm scores keys q k hbounds = 0 := by
    simpa [onQueryKeys] using hon
  simp [onQueryKeys, offQueryKeys, hon', zero_add]

/-- Each far summand is individually capped (proved from `offQueryKey_bound_implies_integrand_bound`). -/
theorem offQuery_summand_integrand_bounded (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : keys k ≠ q) :
    OffQueryIntegrandBounded scores keys q (chosenOffQueryBound scores keys q k hbounds hk) :=
  offQueryKey_bound_implies_integrand_bound scores keys q _

/-- Raw far summand `|∂_q P_k|` bounded by the per-key magnitude cap. -/
theorem abs_queryPoleContribution_le_magnitude_cap_at (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hlog : HasScoreDerivedHeights scores log_heights)
    (hbounds : HasOffQueryBandwidthBounds scores keys (h dq)) (k : Fin N) (hk : keys k ≠ h dq) :
    |queryPoleContribution dq dy keys log_heights h k| ≤
      farFieldMagnitudeCapAt scores keys (h dq) k hbounds hk := by
  dsimp [farFieldMagnitudeCapAt]
  let b := chosenOffQueryBound scores keys (h dq) k hbounds hk
  let y := scoreDerivedPoleHeight scores k
  have hy : 0 < y := scoreDerivedPoleHeight_pos scores k
  have hbk : b.k = k := chosenOffQueryBound_k_eq scores keys (h dq) k hbounds hk
  have hsep : |keys k - h dq| = b.d := by simpa [hbk] using b.hsep
  have hy_eq : Real.exp (log_heights k) = y := by
    dsimp [y]
    calc
      Real.exp (log_heights k) = Real.exp (scoreDerivedLogHeight scores k) := by rw [hlog k]
      _ = scoreDerivedPoleHeight scores k :=
        (scoreDerivedPoleHeight_eq_exp_logHeight scores k).symm
  exact abs_queryPoleContribution_le_magnitude_bound dq dy keys log_heights h k y b.d b.hd hy hsep hy_eq

theorem farFieldMagnitudeCapAt_nonneg (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : keys k ≠ q) :
    0 ≤ farFieldMagnitudeCapAt scores keys q k hbounds hk := by
  dsimp [farFieldMagnitudeCapAt]
  exact poissonPartialQ_magnitude_bound_nonneg (scoreDerivedPoleHeight_pos scores k)
    (chosenOffQueryBound scores keys q k hbounds hk).hd

theorem farFieldMagnitudeCapSum_nonneg (scores keys : Fin N → ℝ) (q : ℝ)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) :
    0 ≤ farFieldMagnitudeCapSum scores keys q hbounds := by
  dsimp [farFieldMagnitudeCapSum, farFieldMagnitudeCapTerm]
  apply Finset.sum_nonneg
  intro k _
  by_cases hneq : keys k ≠ q
  · simpa [farFieldMagnitudeCapTerm, hneq] using
      farFieldMagnitudeCapAt_nonneg scores keys q k hbounds
        (keys_ne_of_mem_offQueryKeys (mem_offQueryKeys.mpr hneq))
  · have hk : keys k = q := not_ne_iff.mp hneq
    simpa [farFieldMagnitudeCapTerm, hk] using
      farFieldMagnitudeCapTerm_eq_zero_on_query scores keys q k hbounds hk

/-- **Macro sieve.**  Triangle inequality + per-key caps on the far finset. -/
theorem abs_farFieldQuerySum_le_sum_magnitude_caps (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hlog : HasScoreDerivedHeights scores log_heights)
    (hbounds : HasOffQueryBandwidthBounds scores keys (h dq)) :
    |farFieldQuerySum dq dy keys log_heights h| ≤
      farFieldMagnitudeCapSum scores keys (h dq) hbounds := by
  dsimp [farFieldQuerySum]
  let s := offQueryKeys keys (h dq)
  let q := h dq
  have hle_sum :
      ∑ k ∈ s, |queryPoleContribution dq dy keys log_heights h k| ≤
        ∑ k ∈ s, farFieldMagnitudeCapTerm scores keys q k hbounds := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [farFieldMagnitudeCapTerm_eq_cap scores keys q k hbounds hk]
    exact abs_queryPoleContribution_le_magnitude_cap_at dq dy scores keys log_heights h hlog hbounds k
      (keys_ne_of_mem_offQueryKeys hk)
  have hle :=
    (Finset.abs_sum_le_sum_abs (fun k => queryPoleContribution dq dy keys log_heights h k) s).trans
      hle_sum
  have hcap : ∑ k ∈ s, farFieldMagnitudeCapTerm scores keys q k hbounds =
      farFieldMagnitudeCapSum scores keys q hbounds := by
    dsimp only [s]
    exact (farFieldMagnitudeCapSum_eq_sum scores keys q hbounds).symm
  calc
    |farFieldQuerySum dq dy keys log_heights h|
        = |∑ k ∈ s, queryPoleContribution dq dy keys log_heights h k| := rfl
    _ ≤ ∑ k ∈ s, farFieldMagnitudeCapTerm scores keys q k hbounds := hle
    _ = farFieldMagnitudeCapSum scores keys q hbounds := hcap

/-- **Macro sieve (existential form).**  Bounded far sum with an explicit nonnegative cap. -/
theorem abs_farFieldQuerySum_le_sum_caps
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hlog : HasScoreDerivedHeights scores log_heights)
    (hbounds : HasOffQueryBandwidthBounds scores keys (h dq)) :
    ∃ B : ℝ, 0 ≤ B ∧ |farFieldQuerySum dq dy keys log_heights h| ≤ B :=
  ⟨farFieldMagnitudeCapSum scores keys (h dq) hbounds,
    farFieldMagnitudeCapSum_nonneg scores keys (h dq) hbounds,
    abs_farFieldQuerySum_le_sum_magnitude_caps dq dy scores keys log_heights h hlog hbounds⟩

/-- Per-key integrand cap at an off-query index. -/
noncomputable def offQueryIntegrandCapAt (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : keys k ≠ q) : ℝ :=
  offQueryIntegrandCap scores keys q (chosenOffQueryBound scores keys q k hbounds hk)

/-- Per-key integrand cap term (zero on the query slice). -/
noncomputable def offQueryIntegrandCapTerm (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) : ℝ :=
  if hne : keys k ≠ q then
    offQueryIntegrandCapAt scores keys q k hbounds
      (keys_ne_of_mem_offQueryKeys (mem_offQueryKeys.mpr hne))
  else 0

/-- Sum of per-key integrand caps over the far-field finset. -/
noncomputable def offQueryIntegrandCapSum (scores keys : Fin N → ℝ) (q : ℝ)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) : ℝ :=
  ∑ k : Fin N, offQueryIntegrandCapTerm scores keys q k hbounds

theorem offQueryIntegrandCapTerm_eq_cap (scores keys : Fin N → ℝ) (q : ℝ) (k : Fin N)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : k ∈ offQueryKeys keys q) :
    offQueryIntegrandCapTerm scores keys q k hbounds =
      offQueryIntegrandCapAt scores keys q k hbounds (keys_ne_of_mem_offQueryKeys hk) := by
  have hne : keys k ≠ q := keys_ne_of_mem_offQueryKeys hk
  dsimp [offQueryIntegrandCapTerm]
  simp [hne]

/-- Per-key weighted integrand bound at an off-query index (score-derived heights). -/
theorem abs_weighted_far_integrand_le_cap_at (scores keys log_heights : Fin N → ℝ) (q : ℝ)
    (k : Fin N) (hlog : HasScoreDerivedHeights scores log_heights)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) (hk : k ∈ offQueryKeys keys q) :
    |farFieldQueryIntegrand (keys k) (Real.exp (log_heights k)) (softmaxWeight scores k) q| ≤
      offQueryIntegrandCapAt scores keys q k hbounds (keys_ne_of_mem_offQueryKeys hk) := by
  dsimp [offQueryIntegrandCapAt]
  let b := chosenOffQueryBound scores keys q k hbounds (keys_ne_of_mem_offQueryKeys hk)
  have hbk : b.k = k :=
    chosenOffQueryBound_k_eq scores keys q k hbounds (keys_ne_of_mem_offQueryKeys hk)
  have hy_eq : Real.exp (log_heights k) = scoreDerivedPoleHeight scores b.k := by
    calc
      Real.exp (log_heights k) = Real.exp (scoreDerivedLogHeight scores k) := by rw [hlog k]
      _ = scoreDerivedPoleHeight scores k :=
        (scoreDerivedPoleHeight_eq_exp_logHeight scores k).symm
      _ = scoreDerivedPoleHeight scores b.k := by rw [hbk]
  have heq : farFieldQueryIntegrand (keys k) (Real.exp (log_heights k)) (softmaxWeight scores k) q =
      farFieldQueryIntegrand (keys b.k) (scoreDerivedPoleHeight scores b.k) (softmaxWeight scores b.k) q := by
    simp [farFieldQueryIntegrand, hbk, hy_eq]
  rw [heq]
  exact abs_weighted_query_integrand_le_cap scores keys q b

theorem offQueryIntegrandCapSum_eq_sum (scores keys : Fin N → ℝ) (q : ℝ)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) :
    offQueryIntegrandCapSum scores keys q hbounds =
      ∑ k ∈ offQueryKeys keys q, offQueryIntegrandCapTerm scores keys q k hbounds := by
  dsimp [offQueryIntegrandCapSum]
  rw [Finset.sum_univ_partition
    (f := fun k => offQueryIntegrandCapTerm scores keys q k hbounds) (p := fun k => keys k = q)]
  have hon :
      ∑ k ∈ onQueryKeys keys q, offQueryIntegrandCapTerm scores keys q k hbounds = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [mem_onQueryKeys] at hk
    dsimp [offQueryIntegrandCapTerm]
    simp [hk]
  have hon' :
      ∑ k with keys k = q, offQueryIntegrandCapTerm scores keys q k hbounds = 0 := by
    simpa [onQueryKeys] using hon
  simp [onQueryKeys, offQueryKeys, hon', zero_add]

theorem offQueryIntegrandCapSum_nonneg (scores keys : Fin N → ℝ) (q : ℝ)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) :
    0 ≤ offQueryIntegrandCapSum scores keys q hbounds := by
  dsimp [offQueryIntegrandCapSum, offQueryIntegrandCapTerm]
  apply Finset.sum_nonneg
  intro k _
  by_cases hneq : keys k ≠ q
  · simpa [offQueryIntegrandCapTerm, hneq] using
      offQueryIntegrandCap_nonneg scores keys q
        (chosenOffQueryBound scores keys q k hbounds
          (keys_ne_of_mem_offQueryKeys (mem_offQueryKeys.mpr hneq)))
  · simp [offQueryIntegrandCapTerm, not_ne_iff.mp hneq]

/-- **Weighted macro sieve.**  `|∑ w_k ∂_q P| ≤ ∑` integrand caps (tighter than raw `|∂_q P|`). -/
theorem abs_weightedFarFieldQuerySum_le_sum_integrand_caps (dq dy : Fin D)
    (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hlog : HasScoreDerivedHeights scores log_heights)
    (hbounds : HasOffQueryBandwidthBounds scores keys (h dq)) :
    |weightedFarFieldQuerySum dq dy scores keys log_heights h| ≤
      offQueryIntegrandCapSum scores keys (h dq) hbounds := by
  dsimp [weightedFarFieldQuerySum]
  let s := offQueryKeys keys (h dq)
  let q := h dq
  have hle_sum :
      ∑ k ∈ s,
          |farFieldQueryIntegrand (keys k) (Real.exp (log_heights k)) (softmaxWeight scores k) q| ≤
        ∑ k ∈ s, offQueryIntegrandCapTerm scores keys q k hbounds := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [offQueryIntegrandCapTerm_eq_cap scores keys q k hbounds hk]
    exact abs_weighted_far_integrand_le_cap_at scores keys log_heights q k hlog hbounds hk
  have hcap :
      ∑ k ∈ s, offQueryIntegrandCapTerm scores keys q k hbounds =
        offQueryIntegrandCapSum scores keys q hbounds := by
    dsimp only [s]
    exact (offQueryIntegrandCapSum_eq_sum scores keys q hbounds).symm
  have hle :=
    (Finset.abs_sum_le_sum_abs
        (fun k => farFieldQueryIntegrand (keys k) (Real.exp (log_heights k))
          (softmaxWeight scores k) q) s).trans hle_sum
  calc
    |weightedFarFieldQuerySum dq dy scores keys log_heights h|
        = |∑ k ∈ s,
            farFieldQueryIntegrand (keys k) (Real.exp (log_heights k)) (softmaxWeight scores k) q| := rfl
    _ ≤ ∑ k ∈ s, offQueryIntegrandCapTerm scores keys q k hbounds := hle
    _ = offQueryIntegrandCapSum scores keys q hbounds := hcap

theorem abs_weightedFarFieldQuerySum_le_sum_caps
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hlog : HasScoreDerivedHeights scores log_heights)
    (hbounds : HasOffQueryBandwidthBounds scores keys (h dq)) :
    ∃ B : ℝ, 0 ≤ B ∧ |weightedFarFieldQuerySum dq dy scores keys log_heights h| ≤ B :=
  ⟨offQueryIntegrandCapSum scores keys (h dq) hbounds,
    offQueryIntegrandCapSum_nonneg scores keys (h dq) hbounds,
    abs_weightedFarFieldQuerySum_le_sum_integrand_caps dq dy scores keys log_heights h hlog hbounds⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §D.6  Frozen-head centroid target + reduced moment obligations
-- ═══════════════════════════════════════════════════════════════════════

/-!
### Near vs far on the query channel

On the slice `ξ_k = q`, `poisson_partial_q q y q = 0` (`poisson_partial_q_on_query`), so
**on-query poles contribute nothing** to `queryPoleContribution`.

**Contour derivative (proved).**  `contourVF_query = ∑_k ∂_q P(ξ_k, y_k, q)` with unit
residue on `dq` — *unweighted* in softmax (`contourVF_query_eq_sum_contributions`).

**Möbius generator (defined).**  `cauchyVF_query = α − β·q` with `α = ∑ w_k ξ_k`,
`β = −∑ w_k log y_k` (`Part5_CauchyVFBridge`).

The open identification is `contourVF_query = cauchyVF_query`.  Neither the raw far sum
`farFieldQuerySum` nor the weighted sum `weightedFarFieldQuerySum` is *a priori* equal to
`α − β·q` for finite off-query poles; see `not_FarFieldCentroidTarget_demo` and
`not_FarFieldWeightedCentroidTarget_demo` in §D.6c.
-/

/-- On-query keys contribute zero to the near-field query sum (proved kernel fact). -/
theorem nearFieldQuerySum_eq_zero (dq dy : Fin D) (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) :
    nearFieldQuerySum dq dy keys log_heights h = 0 := by
  dsimp [nearFieldQuerySum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [mem_onQueryKeys] at hk
  exact queryPoleContribution_eq_zero_on_query dq dy keys log_heights h k hk

/-- **Unweighted far-field = Möbius** (conjectural; refuted at `demo` — see §D.6c). -/
def FarFieldQueryCentroid (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (q : ℝ) : Prop :=
  ∀ (h : Fin D → ℝ), h dq = q →
    farFieldQuerySum dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * q

/-- **Weighted far-field = Möbius** (conjectural; also refuted at `demo`). -/
def FarFieldWeightedQueryCentroid (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ)
    (q : ℝ) : Prop :=
  ∀ (h : Fin D → ℝ), h dq = q →
    weightedFarFieldQuerySum dq dy scores keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * q

/-- Legacy name: the near-field centroid target (provable only when `α − β·q = 0`). -/
def FrozenHeadQueryCentroid (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (q : ℝ) : Prop :=
  FarFieldQueryCentroid dq dy scores keys log_heights q

/-- If the near-field centroid held with a nonzero Möbius target, we'd have `0 = α − β·q`. -/
theorem near_field_centroid_forces_sl2_zero
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (q : ℝ) (h : Fin D → ℝ)
    (hq : h dq = q)
    (hcentroid : ∀ (h' : Fin D → ℝ), h' dq = q →
      nearFieldQuerySum dq dy keys log_heights h' = sl2Alpha scores keys - sl2Beta scores log_heights * q)
    (hsl2 : sl2Alpha scores keys - sl2Beta scores log_heights * q ≠ 0) :
    False := by
  have hz := hcentroid h hq
  have hnear := nearFieldQuerySum_eq_zero dq dy keys log_heights h
  have hzero : sl2Alpha scores keys - sl2Beta scores log_heights * q = 0 := by
    linarith [hnear, hz]
  exact hsl2 hzero

/-- Far-field vanishing at the linearisation point (localization / trained limit). -/
def FarFieldQueryVanishes (dq dy : Fin D) (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : Prop :=
  farFieldQuerySum dq dy keys log_heights h = 0

/-- **Reduced query moment.**  Far-field centroid + proved `nearField = 0` ⇒ full alignment. -/
theorem query_moment_of_far_centroid_and_near_zero
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hcentroid : FarFieldQueryCentroid dq dy scores keys log_heights (h dq)) :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq := by
  rw [contourVF_query_eq_near_plus_far, nearFieldQuerySum_eq_zero dq dy keys log_heights h]
  simp only [zero_add]
  exact hcentroid h (Eq.refl (h dq))

/-- Alias (old name): centroid on the far-field, not on near-field summands. -/
theorem query_moment_of_near_centroid_and_vanishing_far
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hcentroid : FarFieldQueryCentroid dq dy scores keys log_heights (h dq)) :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq :=
  query_moment_of_far_centroid_and_near_zero dq dy scores keys log_heights h hcentroid

/-- Far-field bandwidth vanishing at `η = 0` (second analytic lock). -/
def FarFieldBandwidthVanishes (dq dy : Fin D) (keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) : Prop :=
  farFieldBandwidthSum dq dy keys log_heights h = 0

/-- Near-field bandwidth matches `−Σ w` on a vertical slice (proved base case). -/
theorem nearField_bandwidth_matches_neg_weights_of_vertical
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq)) (hη : h dy = 0) :
    nearFieldBandwidthSum dq dy keys log_heights h =
      -∑ k : Fin N, softmaxWeight scores k :=
  nearFieldBandwidthSum_eq_neg_sum_weights_of_vertical dq dy scores keys log_heights h hslice hη

/-- **Reduced bandwidth moment** at `η = 0` when far-field vanishes. -/
theorem bandwidth_moment_at_zero_of_vanishing_far
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ) (hη : h dy = 0)
    (hslice : FrozenScoreDerivedSlice scores keys log_heights (h dq))
    (hvanish : FarFieldBandwidthVanishes dq dy keys log_heights h)
    (hβ : sl2Beta scores log_heights = ∑ k : Fin N, softmaxWeight scores k) :
    contourVF_logBandwidth dq dy keys log_heights h =
      -sl2Beta scores log_heights := by
  rw [contourVF_logBandwidth_eq_near_plus_far_of_vertical dq dy scores keys log_heights h
      hslice hη, hvanish, add_zero]
  have hsum := nearField_bandwidth_matches_neg_weights_of_vertical dq dy scores keys log_heights h
    hslice hη
  linarith [hβ, hsum]

-- ═══════════════════════════════════════════════════════════════════════
-- §D.7  Bridge to `AlignmentConstruction` (named reduction)
-- ═══════════════════════════════════════════════════════════════════════

/-- Cap-aware localization: links the ε-budget to macro-sieve ceilings. -/
structure LocalizationLimitWithCaps {D : ℕ} (scores keys log_heights : Fin N → ℝ) (q : ℝ)
    (hbounds : HasOffQueryBandwidthBounds scores keys q) where
  limit : LocalizationLimit scores keys log_heights q
  hquery_cap : farFieldMagnitudeCapSum scores keys q hbounds ≤ limit.query_error
  hband_abs : ∀ (dq dy : Fin D) (h : Fin D → ℝ), h dq = q →
    |farFieldBandwidthSum dq dy keys log_heights h| ≤ limit.bandwidth_error

theorem abs_nonneg_le_zero_iff_eq_zero {x : ℝ} (hnonneg : 0 ≤ x) (hle : x ≤ 0) : x = 0 :=
  le_antisymm hle hnonneg

theorem farFieldQuerySum_eq_zero_of_abs_le_zero (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hle : |farFieldQuerySum dq dy keys log_heights h| ≤ 0) :
    farFieldQuerySum dq dy keys log_heights h = 0 :=
  abs_nonpos_iff.mp hle

theorem farFieldBandwidthSum_eq_zero_of_abs_le_zero (dq dy : Fin D) (keys log_heights : Fin N → ℝ)
    (h : Fin D → ℝ) (hle : |farFieldBandwidthSum dq dy keys log_heights h| ≤ 0) :
    farFieldBandwidthSum dq dy keys log_heights h = 0 :=
  abs_nonpos_iff.mp hle

/-- Reduce `query_moment_from_bounds` to the far-field centroid (bounds prove the cap, not the identity). -/
theorem query_moment_from_bounds_via_decomposition
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (_hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (_hbounds : HasOffQueryBandwidthBounds scores keys (h dq))
    (hcentroid : FarFieldQueryCentroid dq dy scores keys log_heights (h dq)) :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq :=
  query_moment_of_far_centroid_and_near_zero dq dy scores keys log_heights h hcentroid

/-- Localization limit ⇒ vanishing far fields (squeeze: macro sieve + ε-budget → 0). -/
theorem far_fields_vanish_of_localization
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (hfrozen : FrozenHeadGeometry scores keys log_heights (h dq))
    (hbounds : HasOffQueryBandwidthBounds scores keys (h dq))
    (hloc : LocalizationLimitWithCaps (D := D) scores keys log_heights (h dq) hbounds) :
    FarFieldQueryVanishes dq dy keys log_heights h ∧
      FarFieldBandwidthVanishes dq dy keys log_heights h := by
  rcases LocalizationLimit.errors_eq_zero hloc.limit with ⟨hq0, hb0⟩
  have hcap0 : farFieldMagnitudeCapSum scores keys (h dq) hbounds ≤ 0 := by
    simpa [hq0] using hloc.hquery_cap
  have hcap_eq_zero : farFieldMagnitudeCapSum scores keys (h dq) hbounds = 0 :=
    le_antisymm hcap0 (farFieldMagnitudeCapSum_nonneg scores keys (h dq) hbounds)
  have habs_query :
      |farFieldQuerySum dq dy keys log_heights h| ≤ 0 := by
    calc
      |farFieldQuerySum dq dy keys log_heights h| ≤
          farFieldMagnitudeCapSum scores keys (h dq) hbounds :=
        abs_farFieldQuerySum_le_sum_magnitude_caps dq dy scores keys log_heights h hfrozen.heights hbounds
      _ = 0 := by rw [hcap_eq_zero]
  have habs_band :
      |farFieldBandwidthSum dq dy keys log_heights h| ≤ 0 :=
    by simpa [hb0] using hloc.hband_abs dq dy h rfl
  exact ⟨
    farFieldQuerySum_eq_zero_of_abs_le_zero dq dy keys log_heights h habs_query,
    farFieldBandwidthSum_eq_zero_of_abs_le_zero dq dy keys log_heights h habs_band⟩

/-- Localization + vanishing far ⇒ the Möbius target collapses to zero. -/
theorem sl2_query_component_eq_zero_of_vanishing_far
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (q : ℝ)
    (hcentroid : FarFieldQueryCentroid dq dy scores keys log_heights q)
    (hvanish : ∀ (h : Fin D → ℝ), h dq = q → FarFieldQueryVanishes dq dy keys log_heights h) :
    sl2Alpha scores keys - sl2Beta scores log_heights * q = 0 := by
  rcases hvanish (fun i => if i = dq then q else 0) (by simp) with hsum
  exact (hcentroid _ (by simp)).symm.trans hsum

/-!
### §D.6a  `N = 2` toy: vertical on-query row (centroid check)

Both keys at `ξ_k = q` ⇒ `farFieldQuerySum = 0`.  The Möbius component `α − β·q` is
`q · (1 + ∑ w_k log y_k)` in general, so the **far-field centroid identity holds only
when that expression is zero** (the trained limit via `sl2_query_component_eq_zero_of_vanishing_far`).
-/

namespace TwoHeadOnQuery

/-- Two-head row with both poles on the query (`ξ_0 = ξ_1 = q`). -/
def OnQueryRowFin2 (keys : Fin 2 → ℝ) (q : ℝ) : Prop :=
  keys 0 = q ∧ keys 1 = q

theorem farFieldQuerySum_eq_zero_fin2 (dq dy : Fin D) (keys log_heights : Fin 2 → ℝ) (q : ℝ)
    (h : Fin D → ℝ) (hrow : OnQueryRowFin2 keys q) (hq : h dq = q) :
    farFieldQuerySum (N := 2) dq dy keys log_heights h = 0 := by
  dsimp [farFieldQuerySum, offQueryKeys]
  have hkeys : ∀ k : Fin 2, keys k = h dq := by
    intro k
    fin_cases k
    · simpa [hq] using hrow.1
    · simpa [hq] using hrow.2
  refine Finset.sum_eq_zero fun k hk => ?_
  simp [mem_offQueryKeys] at hk
  exact absurd (hkeys k) hk

end TwoHeadOnQuery

/-!
### §D.6b  Symmetric `N = 2` off-query witness (`ξ₀ = q − d`, `ξ₁ = q + d`)

Closed forms for the far-field sum (the algebraic final boss at toy scale):

`∂_q P(q−d, y₀, q) = −2 y₀ d / (d² + y₀²)²`,
`∂_q P(q+d, y₁, q) =  2 y₁ d / (d² + y₁²)²`,

so

`farFieldQuerySum = 2d · ( y₁/(d²+y₁²)² − y₀/(d²+y₀²)² )`.

The Möbius target is `α − β·q = ∑ w_k ξ_k + q ∑ w_k log y_k` with `ξ₀+ξ₁ = 2q`.
Equal heights `y₀ = y₁` kill the far sum (symmetric derivative cancellation) while
`α − β·q` need not vanish — the trained centroid identity is **not** the degenerate
`S = 0` case, but a balance of softmax weights against the rational denominators.
-/

namespace SymmetricOffQueryFin2

/-- Symmetric off-query placement at separation `d > 0`. -/
structure SymmetricWitness where
  q : ℝ
  d : ℝ
  hd : 0 < d
  y : Fin 2 → ℝ
  hy : ∀ k, 0 < y k
  scores : Fin 2 → ℝ

/-- Keys `ξ₀ = q − d`, `ξ₁ = q + d`. -/
noncomputable def keys (W : SymmetricWitness) : Fin 2 → ℝ :=
  fun k => if k = 0 then W.q - W.d else W.q + W.d

noncomputable def logHeights (W : SymmetricWitness) : Fin 2 → ℝ := fun k => Real.log (W.y k)

@[simp] lemma keys_zero (W : SymmetricWitness) : keys W 0 = W.q - W.d := by simp [keys]

@[simp] lemma keys_one (W : SymmetricWitness) : keys W 1 = W.q + W.d := by simp [keys]

@[simp] lemma exp_logHeights (W : SymmetricWitness) (k : Fin 2) :
    Real.exp (logHeights W k) = W.y k :=
  Real.exp_log (W.hy k)

lemma keys_ne_query (W : SymmetricWitness) (k : Fin 2) : keys W k ≠ W.q := by
  fin_cases k <;> simp [keys_zero, keys_one, W.hd.ne']

/-- `∂_q P` at the left pole `ξ = q − d`. -/
noncomputable def partialQLeft (W : SymmetricWitness) : ℝ :=
  poisson_partial_q (W.q - W.d) (W.y 0) W.q

/-- `∂_q P` at the right pole `ξ = q + d`. -/
noncomputable def partialQRight (W : SymmetricWitness) : ℝ :=
  poisson_partial_q (W.q + W.d) (W.y 1) W.q

theorem partialQLeft_eq (W : SymmetricWitness) :
    partialQLeft W = -2 * W.y 0 * W.d / (W.d ^ 2 + W.y 0 ^ 2) ^ 2 := by
  dsimp [partialQLeft, poisson_partial_q]
  have hdpos : 0 < W.d ^ 2 + W.y 0 ^ 2 := by nlinarith [sq_pos_of_ne_zero W.hd.ne', sq_nonneg (W.y 0)]
  field_simp [hdpos.ne', pow_two]

theorem partialQRight_eq (W : SymmetricWitness) :
    partialQRight W = 2 * W.y 1 * W.d / (W.d ^ 2 + W.y 1 ^ 2) ^ 2 := by
  dsimp [partialQRight, poisson_partial_q]
  have hdpos : 0 < W.d ^ 2 + W.y 1 ^ 2 := by nlinarith [sq_pos_of_ne_zero W.hd.ne', sq_nonneg (W.y 1)]
  field_simp [hdpos.ne', pow_two]

/-- Closed-form far-field sum for the symmetric two-pole row. -/
noncomputable def farFieldSum (W : SymmetricWitness) : ℝ :=
  partialQLeft W + partialQRight W

/-- Score-weighted far-field sum on `Fin 2` (both keys off-query when `d > 0`). -/
noncomputable def weightedFarFieldSum (W : SymmetricWitness) : ℝ :=
  softmaxWeight W.scores 0 * partialQLeft W + softmaxWeight W.scores 1 * partialQRight W

theorem farFieldSum_eq_closed_form (W : SymmetricWitness) :
    farFieldSum W =
      2 * W.d *
        (W.y 1 / (W.d ^ 2 + W.y 1 ^ 2) ^ 2 - W.y 0 / (W.d ^ 2 + W.y 0 ^ 2) ^ 2) := by
  dsimp [farFieldSum]
  rw [partialQLeft_eq W, partialQRight_eq W]
  field_simp
  ring

/-- Equal pole heights ⇒ symmetric `∂_q P` contributions cancel. -/
theorem farFieldSum_eq_zero_of_eq_heights (W : SymmetricWitness) {y : ℝ} (_hy : 0 < y)
    (h : W.y 0 = y ∧ W.y 1 = y) :
    farFieldSum W = 0 := by
  rw [farFieldSum_eq_closed_form W]
  rcases h with ⟨h0, h1⟩
  simp [h0, h1, sub_self, mul_zero]

/-- Möbius query component `α − β·q` for this witness (arbitrary softmax scores). -/
noncomputable def sl2MobiusComponent (W : SymmetricWitness) : ℝ :=
  sl2Alpha (N := 2) W.scores (keys W) - sl2Beta (N := 2) W.scores (logHeights W) * W.q

/-- **Unweighted toy centroid** (conjectural; refuted at `demo`). -/
def FarFieldCentroidTarget (W : SymmetricWitness) : Prop :=
  farFieldSum W = sl2MobiusComponent W

/-- **Weighted toy centroid** on `Fin 2` (conjectural; refuted at `demo`). -/
def FarFieldWeightedCentroidTarget (W : SymmetricWitness) : Prop :=
  weightedFarFieldSum W = sl2MobiusComponent W

/-- Both off-query keys exhaust `Fin 2` when `d > 0`. -/
theorem offQueryKeys_univ (W : SymmetricWitness) :
    offQueryKeys (N := 2) (keys W) W.q = Finset.univ := by
  ext k
  fin_cases k <;> simp [offQueryKeys, Finset.mem_filter, keys_zero, keys_one, W.hd.ne']

/-- Link the witness to `farFieldQuerySum` on `Fin 2`. -/
theorem farFieldQuerySum_eq_witness_farFieldSum (dq dy : Fin D) (W : SymmetricWitness)
    (h : Fin D → ℝ) (hq : h dq = W.q) :
    farFieldQuerySum (N := 2) dq dy (keys W) (logHeights W) h = farFieldSum W := by
  dsimp [farFieldQuerySum, queryPoleContribution, farFieldSum]
  have hoff : offQueryKeys (N := 2) (keys W) (h dq) = ({0, 1} : Finset (Fin 2)) := by
    ext k
    fin_cases k <;> simp [offQueryKeys, Finset.mem_insert, Finset.mem_singleton, keys_zero, keys_one,
      hq, W.hd.ne']
  rw [hoff, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
  simp [keys_zero, keys_one, hq, exp_logHeights, partialQLeft, partialQRight]

/-- Packaging: toy centroid ⇒ `FarFieldQueryCentroid` at `q = h dq`. -/
theorem farFieldQueryCentroid_of_witness (dq dy : Fin D) (W : SymmetricWitness)
    (hcentroid : FarFieldCentroidTarget W) :
    FarFieldQueryCentroid (N := 2) dq dy W.scores (keys W) (logHeights W) W.q := by
  intro h hq
  dsimp [FarFieldQueryCentroid]
  rw [farFieldQuerySum_eq_witness_farFieldSum dq dy W h hq, hcentroid]
  rfl

end SymmetricOffQueryFin2

/-!
### §D.6c  Asymmetric-score witness (`s₁ > s₀`, heights from Gibbs law)

`HasScoreDerivedHeights` forces `y_k = Z / exp(s_k) = 1 / w_k` (not independent knobs).
Equal scores would force equal heights and `farFieldSum = 0`; an attention gradient is required.
-/

namespace AsymmetricScoreWitness

lemma softmaxZ_fin_two (scores : Fin 2 → ℝ) :
    softmaxZ scores = Real.exp (scores 0) + Real.exp (scores 1) := by
  simp [softmaxZ, Fin.sum_univ_two]

/-- Symmetric geometry + strictly increasing scores (`w₁ > w₀`, `y₀ ≠ y₁`). -/
structure Witness where
  q : ℝ
  d : ℝ
  hd : 0 < d
  scores : Fin 2 → ℝ
  hs1 : scores 1 > scores 0

namespace Witness

/-- Score-derived log-heights (Gibbs gauge). -/
noncomputable def scoreLogHeights (A : Witness) : Fin 2 → ℝ :=
  fun k => scoreDerivedLogHeight A.scores k

theorem hasScoreDerivedHeights (A : Witness) :
    HasScoreDerivedHeights A.scores (scoreLogHeights A) := by
  intro k
  rfl

/-- Heights `y_k = Z / exp(s_k)` from scores. -/
noncomputable def poleHeight (A : Witness) : Fin 2 → ℝ :=
  fun k => scoreDerivedPoleHeight A.scores k

theorem poleHeight_pos (A : Witness) (k : Fin 2) : 0 < poleHeight A k :=
  scoreDerivedPoleHeight_pos A.scores k

theorem poleHeight_eq_inv_weight (A : Witness) (k : Fin 2) :
    poleHeight A k = (softmaxWeight A.scores k)⁻¹ := by
  rw [← inv_inj, inv_inv]
  exact (softmaxWeight_eq_inv_height A.scores k).symm

theorem softmaxWeight_pos (A : Witness) (k : Fin 2) : 0 < softmaxWeight A.scores k := by
  dsimp [softmaxWeight, softmaxZ]
  exact div_pos (Real.exp_pos _) (softmaxZ_pos A.scores)

theorem logHeight_eq_neg_log_weight (A : Witness) (k : Fin 2) :
    scoreLogHeights A k = -Real.log (softmaxWeight A.scores k) := by
  change scoreDerivedLogHeight A.scores k = -Real.log (softmaxWeight A.scores k)
  have hw : (softmaxWeight A.scores k)⁻¹ = scoreDerivedPoleHeight A.scores k := by
    rw [← inv_scoreDerived_eq_softmaxWeight, inv_inv]
  rw [scoreDerivedLogHeight_eq_log_y, ← Real.log_inv, hw]

/-- Embed into the symmetric-geometry `SymmetricWitness` (heights from scores only). -/
noncomputable def toSymmetric (A : Witness) : SymmetricOffQueryFin2.SymmetricWitness where
  q := A.q
  d := A.d
  hd := A.hd
  scores := A.scores
  y := poleHeight A
  hy := poleHeight_pos A

@[simp] theorem toSymmetric_y (A : Witness) (k : Fin 2) : (toSymmetric A).y k = poleHeight A k := rfl

theorem softmaxWeight_lt (A : Witness) : softmaxWeight A.scores 0 < softmaxWeight A.scores 1 := by
  have hexp : Real.exp (A.scores 0) < Real.exp (A.scores 1) := (Real.exp_lt_exp).mpr A.hs1
  have hsum := softmaxZ_fin_two A.scores
  have hZpos : 0 < Real.exp (A.scores 0) + Real.exp (A.scores 1) := by
    linarith [Real.exp_pos (A.scores 0), Real.exp_pos (A.scores 1)]
  calc
    softmaxWeight A.scores 0 = Real.exp (A.scores 0) / softmaxZ A.scores := rfl
    _ = Real.exp (A.scores 0) / (Real.exp (A.scores 0) + Real.exp (A.scores 1)) := by rw [hsum]
    _ < Real.exp (A.scores 1) / (Real.exp (A.scores 0) + Real.exp (A.scores 1)) :=
      div_lt_div_of_pos_right hexp hZpos
    _ = Real.exp (A.scores 1) / softmaxZ A.scores := by rw [hsum]
    _ = softmaxWeight A.scores 1 := rfl

theorem poleHeight_ne (A : Witness) : poleHeight A 0 ≠ poleHeight A 1 := by
  intro heq
  have hinv :
      (softmaxWeight A.scores 0)⁻¹ = (softmaxWeight A.scores 1)⁻¹ := by
    simpa [poleHeight_eq_inv_weight, poleHeight_eq_inv_weight] using heq
  exact ne_of_lt (softmaxWeight_lt A) (inv_injective hinv)

/-- Closed-form Möbius component with score-derived heights. -/
noncomputable def sl2MobiusComponent (A : Witness) : ℝ :=
  sl2Alpha (N := 2) A.scores (SymmetricOffQueryFin2.keys (toSymmetric A)) -
    sl2Beta (N := 2) A.scores (scoreLogHeights A) * A.q

theorem sl2MobiusComponent_eq_affine (A : Witness) :
    sl2MobiusComponent A =
      (softmaxWeight A.scores 0 * (A.q - A.d) + softmaxWeight A.scores 1 * (A.q + A.d)) +
        A.q *
          (softmaxWeight A.scores 0 * Real.log (poleHeight A 0) +
            softmaxWeight A.scores 1 * Real.log (poleHeight A 1)) := by
  dsimp [sl2MobiusComponent, sl2Alpha, sl2Beta, sl2Centroid, sl2LogDrift,
    SymmetricOffQueryFin2.keys, scoreLogHeights, toSymmetric, poleHeight]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [SymmetricOffQueryFin2.keys, Fin.isValue, if_true,
    if_neg (by decide : (1 : Fin 2) ≠ 0), scoreDerivedLogHeight_eq_log_y]
  ring

/-- **Unweighted toy centroid** with locked `y_k = 1 / w_k` (refuted at `demo`). -/
def FarFieldCentroidTarget (A : Witness) : Prop :=
  SymmetricOffQueryFin2.farFieldSum (toSymmetric A) = sl2MobiusComponent A

/-- **Weighted toy centroid** with locked `y_k = 1 / w_k` (refuted at `demo`). -/
def FarFieldWeightedCentroidTarget (A : Witness) : Prop :=
  SymmetricOffQueryFin2.FarFieldWeightedCentroidTarget (toSymmetric A)

/-- Concrete non-degenerate certificate (`s₀ = 0`, `s₁ = 2`, `q = 0`, `d = 1`). -/
noncomputable def demo : Witness where
  q := 0
  d := 1
  hd := by norm_num
  scores := ![0, 2]
  hs1 := by simp

/-- **Numeric guard:** unweighted symmetric far sum ≠ `α − β·q` at `demo`.

    Key argument: `farFieldSum < 1/2 < sl2MobiusComponent` at `demo`.
    * Upper bound: farFieldSum < 2·(1+v)·v³/(2v²+2v+1)² < 1/2
      (polynomial: 4·(1+v)·v³ < (2v²+2v+1)² ↔ 0 < 4v³+8v²+4v+1)
    * Lower bound: sl2Mob = (v−1)/(v+1) > 1/2 since v = exp 2 ≥ 4 > 3. -/
theorem not_FarFieldCentroidTarget_demo : ¬ FarFieldCentroidTarget demo := by
  intro h
  dsimp [FarFieldCentroidTarget] at h
  -- h : farFieldSum (toSymmetric demo) = sl2MobiusComponent demo
  set v := Real.exp 2 with hv_def
  have hv_pos : (0 : ℝ) < v := Real.exp_pos 2
  have hv_ge4 : (4 : ℝ) ≤ v := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hv_eq : v = Real.exp 1 * Real.exp 1 := by
      rw [hv_def, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have h1v_pos : (0 : ℝ) < 1 + v := by linarith
  -- sl2MobiusComponent demo = (v−1)/(1+v)
  have hRHS : sl2MobiusComponent demo = (v - 1) / (1 + v) := by
    rw [sl2MobiusComponent_eq_affine]
    simp only [demo, Fin.sum_univ_two, softmaxWeight, softmaxZ_fin_two,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Real.exp_zero, one_mul, mul_zero, zero_mul, add_zero]
    rw [← hv_def]
    field_simp [h1v_pos.ne']
    ring
  -- sl2Mob > 1/2 since v ≥ 4 > 3: (v-1)/(v+1) - 1/2 = (v-3)/(2(v+1)) > 0
  have hRHS_gt : (1 / 2 : ℝ) < sl2MobiusComponent demo := by
    rw [hRHS]
    have hpos : (0 : ℝ) < (v - 1) / (1 + v) - 1 / 2 := by
      have heq : (v - 1) / (1 + v) - 1 / 2 = (v - 3) / (2 * (1 + v)) := by
        field_simp [h1v_pos.ne']; ring
      rw [heq]; apply div_pos <;> linarith
    linarith
  -- farFieldSum < 1/2: farFieldSum = A − B where A < 1/2 and B > 0
  have hLHS_lt : SymmetricOffQueryFin2.farFieldSum (toSymmetric demo) < 1 / 2 := by
    rw [SymmetricOffQueryFin2.farFieldSum_eq_closed_form]
    simp only [toSymmetric, toSymmetric_y, demo, poleHeight, scoreDerivedPoleHeight,
               softmaxZ_fin_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Real.exp_zero, one_mul, div_one, mul_one, one_pow]
    rw [← hv_def]
    have hD1 : (0 : ℝ) < (2 * v ^ 2 + 2 * v + 1) ^ 2 := by positivity
    have hD2 : (0 : ℝ) < (v ^ 2 + 2 * v + 2) ^ 2 := by positivity
    -- A = 2*(1+v)*v³/(2v²+2v+1)² < 1/2 by 4*(1+v)*v³ < (2v²+2v+1)² ↔ 0 < 4v³+8v²+4v+1
    have hA : 2 * (1 + v) * v ^ 3 / (2 * v ^ 2 + 2 * v + 1) ^ 2 < 1 / 2 := by
      rw [div_lt_div_iff hD1 (by norm_num : (0 : ℝ) < 2)]
      nlinarith [pow_pos hv_pos 3]
    -- B = 2*(1+v)/(v²+2v+2)² > 0
    have hB : (0 : ℝ) < 2 * (1 + v) / (v ^ 2 + 2 * v + 2) ^ 2 := by positivity
    -- goal_expr = A - B by field arithmetic
    have hgoal : 2 * (1 + v) * v ^ 3 / (2 * v ^ 2 + 2 * v + 1) ^ 2 -
        2 * (1 + v) / (v ^ 2 + 2 * v + 2) ^ 2 < 1 / 2 := by linarith
    -- convert goal to A - B using field_simp + ring, then apply hgoal
    have hconv : ∀ (x : ℝ), x =
        2 * (1 + v) * v ^ 3 / (2 * v ^ 2 + 2 * v + 1) ^ 2 -
        2 * (1 + v) / (v ^ 2 + 2 * v + 2) ^ 2 →
        x < 1 / 2 := fun _ hx => hx ▸ hgoal
    apply hconv
    field_simp [hv_pos.ne']
    ring
  -- Contradiction: farFieldSum < 1/2 < sl2Mob = farFieldSum
  exact absurd h (ne_of_lt (lt_trans hLHS_lt hRHS_gt))

/-- Symmetric and witness Möbius components agree on `toSymmetric`. -/
theorem sl2MobiusComponent_toSymmetric (A : Witness) :
    SymmetricOffQueryFin2.sl2MobiusComponent (toSymmetric A) = sl2MobiusComponent A := by
  dsimp [SymmetricOffQueryFin2.sl2MobiusComponent, sl2MobiusComponent, toSymmetric, poleHeight,
    SymmetricOffQueryFin2.keys, SymmetricOffQueryFin2.logHeights, scoreLogHeights,
    sl2Alpha, sl2Beta, sl2Centroid, sl2LogDrift]
  simp only [scoreDerivedLogHeight_eq_log_y, SymmetricOffQueryFin2.exp_logHeights,
    Fin.sum_univ_two, SymmetricOffQueryFin2.keys_zero, SymmetricOffQueryFin2.keys_one]

/-- **Numeric guard:** weighted far sum ≠ `α − β·q` at `demo` (`q = 0`).

    Key argument: `weightedFarFieldSum < 1/2 < sl2MobiusComponent` at `demo`.
    * Upper bound: weighted ≤ 2·v⁴/(2v²+2v+1)² < 1/2
      (polynomial: 4·v⁴ < (2v²+2v+1)² ↔ 0 < 8v³+8v²+4v+1)
    * Lower bound: same as unweighted (v = exp 2 ≥ 4 > 3). -/
theorem not_FarFieldWeightedCentroidTarget_demo : ¬ FarFieldWeightedCentroidTarget demo := by
  intro h
  dsimp [FarFieldWeightedCentroidTarget, SymmetricOffQueryFin2.FarFieldWeightedCentroidTarget] at h
  -- h : weightedFarFieldSum (toSymmetric demo) = sl2MobiusComponent (toSymmetric demo)
  set v := Real.exp 2 with hv_def
  have hv_pos : (0 : ℝ) < v := Real.exp_pos 2
  have hv_ge4 : (4 : ℝ) ≤ v := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hv_eq : v = Real.exp 1 * Real.exp 1 := by
      rw [hv_def, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have h1v_pos : (0 : ℝ) < 1 + v := by linarith
  -- sl2MobiusComponent (toSymmetric demo) = (v−1)/(1+v)
  have hRHS : SymmetricOffQueryFin2.sl2MobiusComponent (toSymmetric demo) = (v - 1) / (1 + v) := by
    rw [sl2MobiusComponent_toSymmetric, sl2MobiusComponent_eq_affine]
    simp only [demo, Fin.sum_univ_two, softmaxWeight, softmaxZ_fin_two,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Real.exp_zero, one_mul, mul_zero, zero_mul, add_zero]
    rw [← hv_def]
    field_simp [h1v_pos.ne']
    ring
  -- sl2Mob > 1/2: same argument as unweighted
  have hRHS_gt : (1 / 2 : ℝ) <
      SymmetricOffQueryFin2.sl2MobiusComponent (toSymmetric demo) := by
    rw [hRHS]
    have hpos : (0 : ℝ) < (v - 1) / (1 + v) - 1 / 2 := by
      have heq : (v - 1) / (1 + v) - 1 / 2 = (v - 3) / (2 * (1 + v)) := by
        field_simp [h1v_pos.ne']; ring
      rw [heq]; apply div_pos <;> linarith
    linarith
  -- weightedFarFieldSum < 1/2: weighted = A − B where A < 1/2 and B > 0
  have hLHS_lt : SymmetricOffQueryFin2.weightedFarFieldSum (toSymmetric demo) < 1 / 2 := by
    simp only [SymmetricOffQueryFin2.weightedFarFieldSum]
    rw [SymmetricOffQueryFin2.partialQLeft_eq, SymmetricOffQueryFin2.partialQRight_eq]
    simp only [toSymmetric, toSymmetric_y, demo, poleHeight, scoreDerivedPoleHeight, softmaxWeight,
               softmaxZ_fin_two, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Real.exp_zero, one_mul, div_one, mul_one, one_pow]
    rw [← hv_def]
    have hD1 : (0 : ℝ) < (2 * v ^ 2 + 2 * v + 1) ^ 2 := by positivity
    have hD2 : (0 : ℝ) < (v ^ 2 + 2 * v + 2) ^ 2 := by positivity
    -- A = 2*v⁴/(2v²+2v+1)² < 1/2 by 4*v⁴ < (2v²+2v+1)² ↔ 0 < 8v³+8v²+4v+1
    have hA : 2 * v ^ 4 / (2 * v ^ 2 + 2 * v + 1) ^ 2 < 1 / 2 := by
      rw [div_lt_div_iff hD1 (by norm_num : (0 : ℝ) < 2)]
      nlinarith [pow_pos hv_pos 3]
    -- B = 2/(v²+2v+2)² > 0
    have hB : (0 : ℝ) < 2 / (v ^ 2 + 2 * v + 2) ^ 2 := by positivity
    have hgoal : 2 * v ^ 4 / (2 * v ^ 2 + 2 * v + 1) ^ 2 -
        2 / (v ^ 2 + 2 * v + 2) ^ 2 < 1 / 2 := by linarith
    have hconv : ∀ (x : ℝ), x =
        2 * v ^ 4 / (2 * v ^ 2 + 2 * v + 1) ^ 2 -
        2 / (v ^ 2 + 2 * v + 2) ^ 2 →
        x < 1 / 2 := fun _ hx => hx ▸ hgoal
    apply hconv
    field_simp [hv_pos.ne', h1v_pos.ne']
    ring
  exact absurd h (ne_of_lt (lt_trans hLHS_lt hRHS_gt))

end Witness

end AsymmetricScoreWitness

/-- **Contour = Möbius under alignment.**

    `GeodesicContourSL2Alignment` is the minimal hypothesis: it packages exactly the
    Fréchet identity needed (`query_moment` field).  The unconditional statement is FALSE
    (LHS does not mention `scores`; see `not_FarFieldCentroidTarget_demo` for a concrete
    refutation of the unguarded discrete form).

    The open question is *constructing* `GeodesicContourSL2Alignment` from Part 2 head
    data; that lives in `Part5_AlignmentConstruction.query_moment_from_bounds`. -/
theorem contourVF_query_matches_sl2
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (halign : PoleAlignment.GeodesicContourSL2Alignment dq dy scores keys log_heights h) :
    contourVF_query dq dy keys log_heights h =
      sl2Alpha scores keys - sl2Beta scores log_heights * h dq :=
  halign.query_moment

/-- **Bounds + moments ⇒ FarFieldQueryCentroid.**

    The centroid identity `farFieldQuerySum = α − β·q` is NOT an automatic consequence
    of bandwidth bounds alone (refuted by `not_FarFieldCentroidTarget_demo`).  It requires
    the full Fréchet moment identity (`ContourSL2Moments.query_moment`).

    Given `ContourSL2Moments`, the proof is:
      contourVF = nearField + farField  (split)
      nearField = 0                      (on-query kernel vanishes, proved)
      contourVF = α − β·q               (from ContourSL2Moments at h)
      farFieldQuerySum depends on h' only through h' dq  (kernel is rational in q-ξ)
    ⟹  farFieldQuerySum h' = α − β·q  for any h' with h' dq = h dq. -/
theorem frozen_head_query_centroid_from_bounds
    (dq dy : Fin D) (scores keys log_heights : Fin N → ℝ) (h : Fin D → ℝ)
    (_hfrozen : AlignmentConstruction.FrozenHeadGeometry scores keys log_heights (h dq))
    (_hbounds : AlignmentConstruction.HasOffQueryBandwidthBounds scores keys (h dq))
    (hmom : AlignmentConstruction.ContourSL2Moments dq dy scores keys log_heights h) :
    FarFieldQueryCentroid dq dy scores keys log_heights (h dq) := by
  intro h' hq'
  -- farFieldQuerySum depends on h' only through (h' dq): both the offQueryKeys filter
  -- and the poisson_partial_q kernel are functions of q = h dq alone.
  have hff_eq : farFieldQuerySum dq dy keys log_heights h' =
      farFieldQuerySum dq dy keys log_heights h := by
    simp only [farFieldQuerySum, offQueryKeys, queryPoleContribution,
               Finset.sum_congr, Finset.filter_congr_decidable]
    congr 1
    · rw [hq']
    · funext k; simp only [queryPoleContribution, hq']
  -- contourVF_query h = 0 + farFieldQuerySum h (nearField vanishes, proved)
  have hcontour_eq : contourVF_query dq dy keys log_heights h =
      farFieldQuerySum dq dy keys log_heights h := by
    rw [contourVF_query_eq_near_plus_far, nearFieldQuerySum_eq_zero]
    simp
  -- assemble
  rw [hff_eq, ← hcontour_eq]
  exact hmom.query_moment

end ContourDecomposition

