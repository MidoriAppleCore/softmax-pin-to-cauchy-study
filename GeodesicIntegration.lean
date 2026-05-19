import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Geodesic Integration — Closing the `sorry` in Part 5 §5.7

This file fills `axiom_implies_geodesic_generating` from `Part5_GeodesicConjecture.lean`
using the Picard-Lindelöf jujitsu strategy:

1. Write down the explicit closed-form matrix path `γ_explicit`.
2. Verify `γ_zero` and `γ_hom` by ring arithmetic.
3. Define the candidate flow `Ψ t h₀ = unembed(γ_explicit(t) • φ(h₀))`.
4. Show `Ψ` satisfies the ODE (chain rule + `CauchyVF_matches_sl2Generator`).
5. Invoke Picard-Lindelöf uniqueness: any ODE solution = `Ψ`.
6. Conclude `φ(Φ_t h₀) = γ_explicit(t) • φ(h₀)` = equation (★).

**Two cases** depending on β:
- `β ≠ 0`: hyperbolic element — exponential approach to fixed point, geodesic orbit.
- `β = 0`: parabolic element — horizontal drift, horocycle orbit.

-/

open Real Complex UpperHalfPlane Matrix MeasureTheory

namespace GeodesicIntegration

-- ═══════════════════════════════════════════════════════════════════════
-- §I.1  The explicit matrix exponential  γ_explicit : ℝ → SL(2,ℝ)
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §I.1  Explicit closed-form path

For the upper-triangular generator
    A = [[-β/2, α], [0, β/2]]
the matrix exponential has a closed form that we define directly,
avoiding any need to invoke `Matrix.exp` (which is hard to unfold).

Case β ≠ 0:
    γ(t) = [[e^{-βt/2},  (α/β)(e^{βt/2} - e^{-βt/2})],
             [0,           e^{βt/2}]]

Case β = 0:
    γ(t) = [[1,  αt], [0, 1]]

Both are verified to have determinant 1 (so they land in SL(2,ℝ)).
-/

/-- The explicit matrix path for the β ≠ 0 (hyperbolic) case. -/
noncomputable def γ_hyperbolic (α β : ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp (-β * t / 2),  (α / β) * (Real.exp (β * t / 2) - Real.exp (-β * t / 2));
     0,                       Real.exp (β * t / 2)]

/-- The explicit matrix path for the β = 0 (parabolic) case. -/
noncomputable def γ_parabolic (α : ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,  α * t;
     0,  1]

/-- `γ_hyperbolic` has determinant 1. -/
theorem γ_hyperbolic_det (α β : ℝ) (t : ℝ) :
    (γ_hyperbolic α β t).det = 1 := by
  simp [γ_hyperbolic, Matrix.det_fin_two]
  ring_nf
  rw [← Real.exp_add]
  norm_num

/-- `γ_parabolic` has determinant 1. -/
theorem γ_parabolic_det (α : ℝ) (t : ℝ) :
    (γ_parabolic α t).det = 1 := by
  simp [γ_parabolic, Matrix.det_fin_two]

/-- Bundle `γ_hyperbolic` into `SL(2,ℝ)`. -/
noncomputable def γ_hyp_SL (α β : ℝ) (t : ℝ) : SpecialLinearGroup (Fin 2) ℝ :=
  ⟨γ_hyperbolic α β t, γ_hyperbolic_det α β t⟩

/-- Bundle `γ_parabolic` into `SL(2,ℝ)`. -/
noncomputable def γ_par_SL (α : ℝ) (t : ℝ) : SpecialLinearGroup (Fin 2) ℝ :=
  ⟨γ_parabolic α t, γ_parabolic_det α t⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §I.2  One-parameter subgroup verification
-- ═══════════════════════════════════════════════════════════════════════

/-- `γ_hyp_SL` satisfies γ(0) = 1. -/
theorem γ_hyp_zero (α β : ℝ) : γ_hyp_SL α β 0 = 1 := by
  ext i j
  simp only [γ_hyp_SL, γ_hyperbolic, SpecialLinearGroup.coe_mk,
             SpecialLinearGroup.coe_one, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `γ_par_SL` satisfies γ(0) = 1. -/
theorem γ_par_zero (α : ℝ) : γ_par_SL α 0 = 1 := by
  ext i j
  simp only [γ_par_SL, γ_parabolic, SpecialLinearGroup.coe_mk,
             SpecialLinearGroup.coe_one, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `γ_hyp_SL` is a group homomorphism (one-parameter subgroup). -/
theorem γ_hyp_hom (α β : ℝ) (s t : ℝ) :
    γ_hyp_SL α β (s + t) = γ_hyp_SL α β s * γ_hyp_SL α β t := by
  ext i j
  simp only [γ_hyp_SL, γ_hyperbolic, SpecialLinearGroup.coe_mk,
             SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Fin.sum_univ_two] <;>
    ring_nf <;>
    simp only [Real.exp_add] <;>
    ring

/-- `γ_par_SL` is a group homomorphism (one-parameter subgroup). -/
theorem γ_par_hom (α : ℝ) (s t : ℝ) :
    γ_par_SL α (s + t) = γ_par_SL α s * γ_par_SL α t := by
  ext i j
  simp only [γ_par_SL, γ_parabolic, SpecialLinearGroup.coe_mk,
             SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Fin.sum_univ_two] <;>
    ring

-- ═══════════════════════════════════════════════════════════════════════
-- §I.3  ODE for the two coordinates
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §I.3  Solving the affine ODE explicitly

The Cauchy-Poisson VF gives:
    ẋ = α - β·x      (query coordinate)
    ẏ = -β·y         (bandwidth coordinate, after unembedding y = exp(h_dy))

For β ≠ 0, the query ODE has solution:
    x(t) = (x₀ - α/β) · e^{-βt} + α/β

For β = 0:
    x(t) = x₀ + α·t

The bandwidth ODE ẏ = -β·y has solution y(t) = y₀ · e^{-βt} in both cases.
-/

/-- The query coordinate solves the affine ODE for β ≠ 0. -/
lemma query_ode_solution_hyp (α β x₀ : ℝ) (hβ : β ≠ 0)
    (x : ℝ → ℝ)
    (h_ode  : ∀ t, HasDerivAt x (α - β * x t) t)
    (h_init : x 0 = x₀) :
    ∀ t, x t = (x₀ - α / β) * Real.exp (-β * t) + α / β := by
  intro t
  -- Integrating factor: f(s) = (x(s) - α/β) * Real.exp(β*s) satisfies f' = 0.
  let f := fun s => (x s - α / β) * Real.exp (β * s)
  -- HasDerivAt (fun s => Real.exp (β*s)) (Real.exp (β*s) * β) s
  have hexp_deriv : ∀ s, HasDerivAt (fun s => Real.exp (β * s)) (Real.exp (β * s) * β) s :=
    fun s => by
      have hmul : HasDerivAt (fun s : ℝ => s * β) β s := by
        simpa using (hasDerivAt_id s).mul_const β
      have hcomm : (fun s : ℝ => s * β) = (fun s => β * s) := funext fun s => mul_comm s β
      rw [hcomm] at hmul
      have h := (Real.hasDerivAt_exp _).comp s hmul
      simpa [mul_comm] using h
  have hf_deriv : ∀ s, HasDerivAt f 0 s := fun s => by
    simp only [f]
    have hx   := h_ode s
    have hsub : HasDerivAt (fun s => x s - α / β) (α - β * x s) s := hx.sub_const (α / β)
    have hprod := hsub.mul (hexp_deriv s)
    convert hprod using 1
    have hcancel : α / β * β = α := div_mul_cancel₀ α hβ
    have : (α - β * x s) * Real.exp (β * s) + (x s - α / β) * (Real.exp (β * s) * β) =
           Real.exp (β * s) * (α - α / β * β) := by ring
    rw [this, hcancel, sub_self, mul_zero]
  -- f is constant by FTC.
  have hf_const : f t = f 0 := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun s _ => hf_deriv s) (intervalIntegrable_const (c := (0 : ℝ)))
    simp at heq; linarith
  simp only [f, h_init, Real.exp_zero, mul_one, mul_zero] at hf_const
  have hne : Real.exp (β * t) ≠ 0 := Real.exp_ne_zero _
  suffices h : x t - α / β = (x₀ - α / β) * Real.exp (-β * t) by linarith
  apply mul_right_cancel₀ hne
  rw [mul_assoc,
      show Real.exp (-β * t) * Real.exp (β * t) = 1 from by rw [← Real.exp_add]; norm_num,
      mul_one]
  exact hf_const

/-- The query coordinate solves the translation ODE for β = 0. -/
lemma query_ode_solution_par (α x₀ : ℝ)
    (x : ℝ → ℝ)
    (h_ode  : ∀ t, HasDerivAt x α t)
    (h_init : x 0 = x₀) :
    ∀ t, x t = x₀ + α * t := by
  intro t
  -- f(s) = x(s) - x₀ - α*s satisfies f' = 0 and f(0) = 0.
  let f := fun s => x s - x₀ - α * s
  have hf_deriv : ∀ s, HasDerivAt f 0 s := fun s => by
    simp only [f]
    have hx  := h_ode s
    have hc  : HasDerivAt (fun _ => x₀) (0 : ℝ) s := hasDerivAt_const s x₀
    have hls : HasDerivAt (fun s : ℝ => α * s) α s := by
      have hmul : HasDerivAt (fun s : ℝ => s * α) α s := by
        simpa using (hasDerivAt_id s).mul_const α
      have hcomm : (fun s : ℝ => s * α) = (fun s => α * s) := funext fun s => mul_comm s α
      rwa [hcomm] at hmul
    have hsum := hc.add hls
    simp only [zero_add] at hsum
    have hdiff := hx.sub hsum
    simp only [sub_self] at hdiff
    have heq : (fun s => x s - x₀ - α * s) = (fun s => x s - (x₀ + α * s)) :=
      funext (fun s => by ring)
    rw [heq]; exact hdiff
  have hf_const : f t = f 0 := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun s _ => hf_deriv s) (intervalIntegrable_const (c := (0 : ℝ)))
    simp at heq; linarith
  simp only [f, h_init, mul_zero, sub_zero, sub_self] at hf_const
  linarith

/-- The log-bandwidth coordinate solves ẏ = -β·y (exponential decay/growth). -/
lemma bandwidth_ode_solution (β y₀ : ℝ)
    (y : ℝ → ℝ)
    (h_ode  : ∀ t, HasDerivAt y (-β * y t) t)
    (h_init : y 0 = y₀) :
    ∀ t, y t = y₀ * Real.exp (-β * t) := by
  intro t
  -- Integrating factor: g(s) = y(s) * Real.exp(β*s) satisfies g' = 0.
  let g := fun s => y s * Real.exp (β * s)
  have hexp_deriv : ∀ s, HasDerivAt (fun s => Real.exp (β * s)) (Real.exp (β * s) * β) s :=
    fun s => by
      have hmul : HasDerivAt (fun s : ℝ => s * β) β s := by
        simpa using (hasDerivAt_id s).mul_const β
      have hcomm : (fun s : ℝ => s * β) = (fun s => β * s) := funext fun s => mul_comm s β
      rw [hcomm] at hmul
      have h := (Real.hasDerivAt_exp _).comp s hmul
      simpa [mul_comm] using h
  have hg_deriv : ∀ s, HasDerivAt g 0 s := fun s => by
    simp only [g]
    have hy    := h_ode s
    have hprod := hy.mul (hexp_deriv s)
    convert hprod using 1; ring
  have hg_const : g t = g 0 := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun s _ => hg_deriv s) (intervalIntegrable_const (c := (0 : ℝ)))
    simp at heq; linarith
  simp only [g, h_init, Real.exp_zero, mul_one, mul_zero] at hg_const
  have hne : Real.exp (β * t) ≠ 0 := Real.exp_ne_zero _
  apply mul_right_cancel₀ hne
  rw [mul_assoc,
      show Real.exp (-β * t) * Real.exp (β * t) = 1 from by rw [← Real.exp_add]; norm_num,
      mul_one]
  exact hg_const

-- ═══════════════════════════════════════════════════════════════════════
-- §I.4  The intertwining identity  φ(Φ_t h₀) = γ(t) • φ(h₀)
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §I.4  Intertwining

Given the coordinate solutions from §I.3, we verify that the Möbius action
of `γ(t)` on `φ(h₀)` gives exactly `φ(Φ_t h₀)`.

The Möbius action of [[a,b],[0,d]] on z = x + iy is:
    [[a,b],[0,d]] • z  =  (a·z + b) / (0·z + d)  =  a/d · z + b/d

For γ_hyperbolic(t) acting on z₀ = x₀ + i·exp(h₀[dy]):
    re: e^{-βt/2} / e^{βt/2} · x₀  +  (α/β)(e^{βt/2} - e^{-βt/2}) / e^{βt/2}
      = e^{-βt} · x₀  +  (α/β)(1 - e^{-βt})
      = (x₀ - α/β)·e^{-βt} + α/β    ✓  matches query ODE solution
    im: exp(h₀[dy]) / e^{βt}         = exp(h₀[dy]) · e^{-βt}
      = exp(h₀[dy] - β·t)            ✓  matches bandwidth ODE solution
-/

/-- Real part of (↑r·z + ↑s) / ↑d, for r s d : ℝ, d ≠ 0.
    Avoids normSq/ofReal_exp confusion by working with abstract real scalars. -/
private lemma div_ofReal_re (z : ℂ) (r s d : ℝ) (hd : d ≠ 0) :
    ((↑r * z + ↑s) / ↑d).re = (r * z.re + s) / d := by
  simp [Complex.div_re, Complex.normSq_ofReal]; field_simp [hd]; ring

/-- Imaginary part of (↑r·z + ↑s) / ↑d, for r s d : ℝ, d ≠ 0. -/
private lemma div_ofReal_im (z : ℂ) (r s d : ℝ) (hd : d ≠ 0) :
    ((↑r * z + ↑s) / ↑d).im = r * z.im / d := by
  simp [Complex.div_im, Complex.normSq_ofReal]; field_simp [hd]; ring

/-- The Möbius action of an upper-triangular SL(2,ℝ) element [[a,b],[0,d]] on z ∈ ℍ
    equals (a·z + b) / d.
    This is the key algebraic identity used in the intertwining check.  -/
lemma upper_triangular_smul (a b d : ℝ) (hdet : a * d = 1) (hd : 0 < d) (z : UpperHalfPlane) :
    let g : SpecialLinearGroup (Fin 2) ℝ :=
          ⟨!![a, b; 0, d], by simp [Matrix.det_fin_two, hdet]⟩
    (g • z : UpperHalfPlane) = ⟨⟨a / d * (z : ℂ).re + b / d,
                                   a / d * (z : ℂ).im⟩, by
      have ha : 0 < a := by
        have : a = 1 / d := by field_simp; linarith [hdet]
        rw [this]; exact div_pos one_pos hd
      exact mul_pos (div_pos ha hd) z.2⟩ := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [SpecialLinearGroup.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.head_cons, Algebra.id.map_eq_id, RingHom.id_apply,
             Complex.ofReal_zero, zero_mul, zero_add]
  apply Complex.ext
  · simp only [Complex.div_re, Complex.normSq_ofReal, Complex.add_re, Complex.mul_re,
               Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero, sub_zero]
    field_simp [hd.ne']; ring
  · simp only [Complex.div_im, Complex.normSq_ofReal, Complex.add_im, Complex.mul_im,
               Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
    field_simp [hd.ne']; ring

/-- **The intertwining identity for the hyperbolic (β ≠ 0) case.**
    For any initial state h₀ and ODE solution Φ:
        φ(Φ_t h₀) = γ_hyp(t) • φ(h₀)  -/
theorem intertwining_hyp
    {D : ℕ} (dq dy : Fin D) (α β : ℝ) (hβ : β ≠ 0)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (hF_dq : ∀ h, F h dq = α - β * h dq)
    (hF_dy : ∀ h, F h dy = -β)
    (Φ : ℝ → (Fin D → ℝ) → Fin D → ℝ)
    (hΦ_ode  : ∀ h₀ t, HasDerivAt (fun s => Φ s h₀) (F (Φ t h₀)) t)
    (hΦ_init : ∀ h₀, Φ 0 h₀ = h₀)
    (h₀ : Fin D → ℝ) (t : ℝ) :
    let φ : (Fin D → ℝ) → UpperHalfPlane := fun h => ⟨⟨h dq, Real.exp (h dy)⟩, Real.exp_pos _⟩
    φ (Φ t h₀) = γ_hyp_SL α β t • φ h₀ := by
  let φ : (Fin D → ℝ) → UpperHalfPlane := fun h => ⟨⟨h dq, Real.exp (h dy)⟩, Real.exp_pos _⟩
  have hΦ_coord : ∀ (i : Fin D) t, HasDerivAt (fun s => Φ s h₀ i) (F (Φ t h₀) i) t :=
    fun i t => hasDerivAt_pi.mp (hΦ_ode h₀ t) i
  have hq : ∀ t, Φ t h₀ dq = (h₀ dq - α / β) * Real.exp (-β * t) + α / β :=
    query_ode_solution_hyp α β (h₀ dq) hβ (fun t => Φ t h₀ dq)
      (fun t => by rw [← hF_dq (Φ t h₀)]; exact hΦ_coord dq t)
      (congr_fun (hΦ_init h₀) dq)
  have hdy : ∀ t, Φ t h₀ dy = h₀ dy + (-β) * t :=
    query_ode_solution_par (-β) (h₀ dy) (fun t => Φ t h₀ dy)
      (fun t => by rw [← hF_dy (Φ t h₀)]; exact hΦ_coord dy t)
      (congr_fun (hΦ_init h₀) dy)
  set a := Real.exp (-β * t / 2)
  set b := (α / β) * (Real.exp (β * t / 2) - Real.exp (-β * t / 2))
  set d := Real.exp (β * t / 2)
  have hdet : a * d = 1 := by
    dsimp [a, d]
    rw [← Real.exp_add, show -β * t / 2 + β * t / 2 = 0 by ring, Real.exp_zero]
  have hd : 0 < d := by dsimp [d]; exact Real.exp_pos _
  have hγ : γ_hyp_SL α β t = ⟨!![a, b; 0, d], by simp [Matrix.det_fin_two, hdet]⟩ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [γ_hyp_SL, γ_hyperbolic, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    all_goals dsimp [a, b, d] <;> ring_nf
  have hμ := upper_triangular_smul a b d hdet hd (φ h₀)
  show φ (Φ t h₀) = γ_hyp_SL α β t • φ h₀
  apply UpperHalfPlane.ext
  set w := γ_hyp_SL α β t • φ h₀
  show (φ (Φ t h₀) : ℂ) = (w : ℂ)
  have hμC : (w : ℂ) =
      { re := a / d * (φ h₀ : ℂ).re + b / d, im := a / d * (φ h₀ : ℂ).im } := by
    simpa [hγ, UpperHalfPlane.coe_mk] using congr_arg (fun z : ℍ => (z : ℂ)) hμ
  rw [hμC]
  simp only [φ]
  apply Complex.ext
  · dsimp [a, b, d]
    have had : a / d = Real.exp (-β * t) := by
      dsimp [a, d]; field_simp; rw [← Real.exp_add]; ring
    have hbd : b / d = (α / β) * (1 - Real.exp (-β * t)) := by
      have hsplit :
          (Real.exp (β * t / 2) - Real.exp (-(β * t) / 2)) / Real.exp (β * t / 2) =
            1 - Real.exp (-β * t) := by
        have hnum : Real.exp (β * t / 2) - Real.exp (-(β * t) / 2) =
            Real.exp (β * t / 2) * (1 - Real.exp (-β * t)) := by
          have h2 : Real.exp (-(β * t) / 2) = Real.exp (β * t / 2) * Real.exp (-β * t) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [h2]; ring
        rw [hnum]
        field_simp [Real.exp_ne_zero (β * t / 2)]
      have hstep : b / d =
          (α / β) * ((Real.exp (β * t / 2) - Real.exp (-(β * t) / 2)) / Real.exp (β * t / 2)) := by
        dsimp [b, d]
        field_simp [hβ]
      calc
        b / d = (α / β) * ((Real.exp (β * t / 2) - Real.exp (-(β * t) / 2)) / Real.exp (β * t / 2)) := hstep
        _ = (α / β) * (1 - Real.exp (-β * t)) := by rw [hsplit]
    rw [hq t, had, hbd]; field_simp [hβ]; ring
  · dsimp [a, b, d]
    have had : a / d = Real.exp (-β * t) := by
      dsimp [a, d]; field_simp; rw [← Real.exp_add]; ring
    rw [had, ← Real.exp_add]
    congr 1
    linarith [hdy t]

/-- **The intertwining identity for the parabolic (β = 0) case.**  -/
theorem intertwining_par
    {D : ℕ} (dq dy : Fin D) (α : ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (hF_dq : ∀ h, F h dq = α)
    (hF_dy : ∀ h, F h dy = (0 : ℝ))
    (Φ : ℝ → (Fin D → ℝ) → Fin D → ℝ)
    (hΦ_ode  : ∀ h₀ t, HasDerivAt (fun s => Φ s h₀) (F (Φ t h₀)) t)
    (hΦ_init : ∀ h₀, Φ 0 h₀ = h₀)
    (h₀ : Fin D → ℝ) (t : ℝ) :
    let φ : (Fin D → ℝ) → UpperHalfPlane := fun h => ⟨⟨h dq, Real.exp (h dy)⟩, Real.exp_pos _⟩
    φ (Φ t h₀) = γ_par_SL α t • φ h₀ := by
  let φ : (Fin D → ℝ) → UpperHalfPlane := fun h => ⟨⟨h dq, Real.exp (h dy)⟩, Real.exp_pos _⟩
  have hΦ_coord : ∀ (i : Fin D) t, HasDerivAt (fun s => Φ s h₀ i) (F (Φ t h₀) i) t :=
    fun i t => hasDerivAt_pi.mp (hΦ_ode h₀ t) i
  have hq : ∀ t, Φ t h₀ dq = h₀ dq + α * t :=
    query_ode_solution_par α (h₀ dq) (fun t => Φ t h₀ dq)
      (fun t => by rw [← hF_dq (Φ t h₀)]; exact hΦ_coord dq t)
      (congr_fun (hΦ_init h₀) dq)
  have hdy : ∀ t, Φ t h₀ dy = h₀ dy :=
    fun t => by
      have := query_ode_solution_par 0 (h₀ dy) (fun t => Φ t h₀ dy)
        (fun t => by have hc := hΦ_coord dy t; rwa [hF_dy] at hc)
        (congr_fun (hΦ_init h₀) dy) t
      linarith
  have hγ : γ_par_SL α t = ⟨!![1, α * t; 0, 1], by simp [Matrix.det_fin_two]⟩ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [γ_par_SL, γ_parabolic, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have hμ := upper_triangular_smul 1 (α * t) 1 (by ring) (by norm_num) (φ h₀)
  set w := γ_par_SL α t • φ h₀
  have hμC : (w : ℂ) =
      { re := (φ h₀ : ℂ).re + α * t, im := (φ h₀ : ℂ).im } := by
    simpa [hγ, UpperHalfPlane.coe_mk] using congr_arg (fun z : ℍ => (z : ℂ)) hμ
  show φ (Φ t h₀) = γ_par_SL α t • φ h₀
  apply UpperHalfPlane.ext
  show (φ (Φ t h₀) : ℂ) = (w : ℂ)
  rw [hμC]
  simp only [φ, one_div, one_mul, div_one]
  apply Complex.ext
  · simp [φ, one_div, one_mul, div_one]; linarith [hq t]
  · simp [φ, hdy t]

-- ═══════════════════════════════════════════════════════════════════════
-- §I.5  Assembling IsGeodesicGenerating
-- ═══════════════════════════════════════════════════════════════════════

/-!
### §I.5  Assembly

With the two intertwining theorems proved, `IsGeodesicGenerating` assembles
by case-splitting on β = 0 vs β ≠ 0.  The `γ`, `γ_zero`, `γ_hom`, and
`flow_eq` fields are supplied by the explicit path + the theorems above.
-/

-- Re-import the structures from Part 5.
-- (In practice: `import TransformersAreCauchyPoisson.Part5_GeodesicConjecture`)
-- For now we inline the definitions to keep this file self-contained.

-- The key result: once all sorries above are closed, this goes through
-- by `exact` + the two intertwining theorems.

/-- **Assembly lemma.**  Given pointwise equalities for the VF (from the gap axiom),
    construct `IsGeodesicGenerating`.  The only remaining work is in the `sorry`s
    in §I.3 and §I.4 above.  -/
lemma assemble_geodesic_generating
    {D : ℕ} (dq dy : Fin D) (α β : ℝ)
    (F : (Fin D → ℝ) → Fin D → ℝ)
    (hF_dq : ∀ h, F h dq = α - β * h dq)
    (hF_dy : ∀ h, F h dy = -β) :
    -- What we need to build: γ satisfying the three conditions.
    ∃ (γ : ℝ → SpecialLinearGroup (Fin 2) ℝ),
      γ 0 = 1 ∧
      (∀ s t, γ (s + t) = γ s * γ t) ∧
      ∀ (Φ : ℝ → (Fin D → ℝ) → Fin D → ℝ)
        (_ : ∀ h₀ t, HasDerivAt (fun s => Φ s h₀) (F (Φ t h₀)) t)
        (_ : ∀ h₀, Φ 0 h₀ = h₀)
        (h₀ : Fin D → ℝ) (t : ℝ),
        let z₀ : UpperHalfPlane := ⟨⟨h₀ dq, Real.exp (h₀ dy)⟩, Real.exp_pos _⟩
        let z₁ : UpperHalfPlane := ⟨⟨Φ t h₀ dq, Real.exp (Φ t h₀ dy)⟩, Real.exp_pos _⟩
        z₁ = γ t • z₀ := by
  by_cases hβ : β = 0
  · -- Parabolic case: use γ_par_SL α
    subst hβ
    refine ⟨γ_par_SL α, γ_par_zero α, γ_par_hom α, ?_⟩
    intro Φ hΦ_ode hΦ_init h₀ t
    have hF_dq' : ∀ h, F h dq = α := by simpa using hF_dq
    have hF_dy' : ∀ h, F h dy = 0 := by simpa using hF_dy
    exact intertwining_par dq dy α F hF_dq' hF_dy' Φ hΦ_ode hΦ_init h₀ t
  · -- Hyperbolic case: use γ_hyp_SL α β
    refine ⟨γ_hyp_SL α β, γ_hyp_zero α β, γ_hyp_hom α β, ?_⟩
    intro Φ hΦ_ode hΦ_init h₀ t
    exact intertwining_hyp dq dy α β hβ F hF_dq hF_dy Φ hΦ_ode hΦ_init h₀ t

end GeodesicIntegration
