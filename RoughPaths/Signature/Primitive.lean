/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Signature.Piecewise
import RoughPaths.Signature.Log
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.GeomSum

/-!
# Primitivity of the truncated log-signature

A series `b` is *primitive* for the shuffle coproduct when `b([]) = 0` and
`Σ_{x ∈ u ⧢ v} b(x) = 0` for all nonempty `u, v` (the boundary sums
against `[]` are automatic, so this is `Δ_⧢ b = b ⊗ 1 + 1 ⊗ b` in
coefficient form). **Main theorem**: the truncated logarithm of a
group-like series is primitive up to the truncation degree — the
first-order shadow of "the log-signature lies in the free Lie algebra".

Proof: shuffle sums of `(a-1)^{⊗k}` expand via the
shuffle–deconcatenation compatibility `Word.shuffle_splits_perm` as
`Σ_{i,j} N(k,i,j)·(a-1)^{⊗i}(u)·(a-1)^{⊗j}(v)`, where `N(k,i,j)` is the
coefficient of `xⁱyʲ` in `(x+y+xy)^k`, realised in `ℤ[y][x]`. The
required vanishing `Σ_k (-1)^k/(k+1)·N(k+1,i,j) = 0` for `i,j ≥ 1` is the
coefficient identity of `log((1+x)(1+y)) = log(1+x) + log(1+y)`: after
`d/dx` the sum becomes geometric, `(1+x+y+xy)·W = (1-(-x-y-xy)^n)(1+y)`
pins down the low-degree coefficients of `W` by a bidegree recursion.
-/

namespace RoughPaths

open HopfAlgebras

universe u v

variable {α : Type u} {R : Type v}

namespace Word

/-! ### Primitive series -/

/-- A series is **primitive** for the shuffle coproduct: the empty
coefficient vanishes and all mixed shuffle sums over nonempty word pairs
vanish. -/
def IsPrimitive [Semiring R] (b : (List α → R)) : Prop :=
  coeff b [] = 0 ∧
    ∀ u v : List α, u ≠ [] → v ≠ [] → shuffleCoeff b u v = 0

/-- Primitivity up to a degree: mixed shuffle sums vanish whenever the
total length is at most `n`. -/
def IsPrimitiveUpToDegree [Semiring R] (b : (List α → R)) (n : ℕ) :
    Prop :=
  coeff b [] = 0 ∧
    ∀ u v : List α, u ≠ [] → v ≠ [] → u.length + v.length ≤ n →
      shuffleCoeff b u v = 0

theorem isPrimitive_iff_forall_isPrimitiveUpToDegree [Semiring R]
    (b : (List α → R)) :
    IsPrimitive b ↔ ∀ n, IsPrimitiveUpToDegree b n := by
  constructor
  · exact fun h n => ⟨h.1, fun u v hu hv _ => h.2 u v hu hv⟩
  · exact fun h => ⟨(h 0).1, fun u v hu hv =>
      (h (u.length + v.length)).2 u v hu hv le_rfl⟩

private theorem list_sum_map_add {β : Type*} [AddCommMonoid R]
    (l : List β) (f g : β → R) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      exact add_add_add_comm _ _ _ _

private theorem list_sum_map_sub {β : Type*} [Ring R]
    (l : List β) (f g : β → R) :
    (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      abel

theorem zero_isPrimitive [Semiring R] :
    IsPrimitive (zero α R) := by
  refine ⟨rfl, fun u v _ _ => ?_⟩
  exact List.sum_eq_zero fun x hx => by
    rcases List.mem_map.1 hx with ⟨w, _, rfl⟩
    rfl

theorem IsPrimitive.add [Semiring R] {b c : (List α → R)}
    (hb : IsPrimitive b) (hc : IsPrimitive c) :
    IsPrimitive (b + c) := by
  constructor
  · show coeff b [] + coeff c [] = 0
    rw [hb.1, hc.1, add_zero]
  · intro u v hu hv
    have h : shuffleCoeff (b + c) u v =
        shuffleCoeff b u v + shuffleCoeff c u v :=
      list_sum_map_add (Word.shuffle u v) b c
    rw [h, hb.2 u v hu hv, hc.2 u v hu hv, add_zero]

theorem IsPrimitive.smul [Semiring R] (r : R) {b : (List α → R)}
    (hb : IsPrimitive b) :
    IsPrimitive (r • b) := by
  constructor
  · show r * coeff b [] = 0
    rw [hb.1, mul_zero]
  · intro u v hu hv
    have h : shuffleCoeff (r • b) u v = r * shuffleCoeff b u v :=
      List.sum_map_mul_left (Word.shuffle u v) b r
    rw [h, hb.2 u v hu hv, mul_zero]

/-! ### The bilinear pairing form of shuffle–deconcatenation
compatibility -/

/-- **Shuffle sums of a tensor product** expand over the splittings of
both words — the pairing form of `Word.shuffle_splits_perm`. -/
theorem shuffleCoeff_tensorProduct [CommSemiring R]
    (f g : (List α → R)) (u v : List α) :
    shuffleCoeff (tensorProduct f g) u v =
      ((Word.splits u).map fun p =>
        ((Word.splits v).map fun q =>
          shuffleCoeff f p.1 q.1 * shuffleCoeff g p.2 q.2).sum).sum := by
  have hL : shuffleCoeff (tensorProduct f g) u v =
      (((Word.shuffle u v).flatMap Word.splits).map
        fun r => coeff f r.1 * coeff g r.2).sum := by
    rw [shuffleCoeff, sum_map_flatMap]
    rfl
  rw [hL, ((Word.shuffle_splits_perm u v).map
    fun r => coeff f r.1 * coeff g r.2).sum_eq]
  rw [Word.splitShufflePairs_def, sum_map_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [sum_map_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  rw [sum_map_flatMap, shuffleCoeff, shuffleCoeff, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  rw [List.map_map, ← List.sum_map_mul_left]
  rfl

/-! ### List-sum utilities -/

private theorem list_sum_list_sum_swap {β : Type*} {γ : Type*} [AddCommMonoid R]
    (l : List β) (l' : List γ) (F : β → γ → R) :
    (l.map fun x => ((l'.map fun y => F x y).sum)).sum =
      (l'.map fun y => ((l.map fun x => F x y).sum)).sum := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact (List.sum_eq_zero fun x hx => by
        rcases List.mem_map.1 hx with ⟨w, _, rfl⟩
        rfl).symm
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [← list_sum_map_add]

private theorem list_sum_finset_sum_swap {β : Type*} {ι : Type*}
    [AddCommMonoid R] (l : List β) (s : Finset ι) (F : β → ι → R) :
    (l.map fun x => ∑ i ∈ s, F x i).sum =
      ∑ i ∈ s, (l.map fun x => F x i).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private theorem list_range_map_sum [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]
      simp

/-! ### Splitting sums against the unit, and short-word vanishing -/

/-- Summing over splits with the unit weighting the prefix collapses to
the full word. -/
private theorem sum_splits_unit_left [Semiring R]
    (g : List α → R) (w : List α) :
    ((Word.splits w).map fun p => unit α R p.1 * g p.2).sum = g w := by
  cases w with
  | nil =>
      rw [Word.splits_nil]
      show unit α R [] * g [] + 0 = g []
      rw [add_zero]
      show (1 : R) * g [] = g []
      rw [one_mul]
  | cons x w =>
      rw [Word.splits_cons, List.map_cons, List.sum_cons, List.map_map]
      have hzero : (((Word.splits w).map
          ((fun p => unit α R p.1 * g p.2) ∘
            fun p => (x :: p.1, p.2))).sum) = 0 := by
        apply List.sum_eq_zero
        intro y hy
        rcases List.mem_map.1 hy with ⟨p, _, rfl⟩
        show unit α R (x :: p.1) * g p.2 = 0
        show (0 : R) * g p.2 = 0
        rw [zero_mul]
      rw [hzero, add_zero]
      show (1 : R) * g (x :: w) = g (x :: w)
      rw [one_mul]

/-- Tensor powers of a series vanishing on `[]` vanish on short words. -/
private theorem tensorPower_eq_zero_of_short [Semiring R]
    {c : (List α → R)} (hc : c [] = 0) :
    ∀ (k : ℕ) (w : List α), w.length < k → tensorPower c k w = 0 := by
  intro k
  induction k with
  | zero => exact fun w hw => absurd hw (Nat.not_lt_zero _)
  | succ k ih =>
      intro w hw
      show ((Word.splits w).map fun p =>
        coeff c p.1 * coeff (tensorPower c k) p.2).sum = 0
      apply List.sum_eq_zero
      intro x hx
      rcases List.mem_map.1 hx with ⟨p, hp, rfl⟩
      have happ := Word.mem_splits_append hp
      rcases p with ⟨p1, p2⟩
      cases p1 with
      | nil =>
          show c [] * coeff (tensorPower c k) p2 = 0
          rw [hc, zero_mul]
      | cons y l =>
          have hlen : p2.length < k := by
            have := congrArg List.length happ
            simp only [List.length_append, List.length_cons] at this
            omega
          show c (y :: l) * tensorPower c k p2 = 0
          rw [ih p2 hlen, mul_zero]

/-! ### Bidegree coefficients of `(x + y + xy)^k` in `ℤ[y][x]` -/

section PolyAux

open Polynomial

/-- The polynomial `x + y + xy` in `ℤ[y][x]`. -/
private noncomputable def xyP : Polynomial (Polynomial ℤ) :=
  X + C X + X * C X

/-- Bidegree coefficient extraction from `ℤ[y][x]`. -/
private noncomputable def coeff₂ (P : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    ℤ :=
  (P.coeff i).coeff j

private theorem coeff₂_add (P Q : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    coeff₂ (P + Q) i j = coeff₂ P i j + coeff₂ Q i j := by
  rw [coeff₂, coeff₂, coeff₂, Polynomial.coeff_add, Polynomial.coeff_add]

private theorem coeff₂_sub (P Q : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    coeff₂ (P - Q) i j = coeff₂ P i j - coeff₂ Q i j := by
  rw [coeff₂, coeff₂, coeff₂, Polynomial.coeff_sub, Polynomial.coeff_sub]

private theorem coeff₂_neg (P : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    coeff₂ (-P) i j = -coeff₂ P i j := by
  rw [coeff₂, coeff₂, Polynomial.coeff_neg, Polynomial.coeff_neg]

private theorem coeff₂_sum {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (Polynomial ℤ)) (i j : ℕ) :
    coeff₂ (∑ k ∈ s, P k) i j = ∑ k ∈ s, coeff₂ (P k) i j := by
  rw [coeff₂, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  rfl

private theorem coeff₂_neg_one_pow_mul (k : ℕ) :
    ∀ (P : Polynomial (Polynomial ℤ)) (i j : ℕ),
      coeff₂ ((-1) ^ k * P) i j = (-1) ^ k * coeff₂ P i j := by
  induction k with
  | zero => intro P i j; rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ k ih =>
      intro P i j
      have h1 : ((-1 : Polynomial (Polynomial ℤ))) ^ (k + 1) * P =
          (-1) ^ k * (-P) := by ring
      rw [h1, ih (-P) i j, coeff₂_neg, pow_succ]
      ring

private theorem coeff₂_one_zero_zero : coeff₂ 1 0 0 = 1 := by
  rw [coeff₂, Polynomial.coeff_one]
  simp

private theorem coeff₂_one_succ_left (i j : ℕ) : coeff₂ 1 (i + 1) j = 0 := by
  rw [coeff₂, Polynomial.coeff_one]
  simp

private theorem coeff₂_one_zero_succ (j : ℕ) : coeff₂ 1 0 (j + 1) = 0 := by
  rw [coeff₂, Polynomial.coeff_one]
  simp [Polynomial.coeff_one]

private theorem coeff₂_mul_X_succ (P : Polynomial (Polynomial ℤ))
    (i j : ℕ) :
    coeff₂ (P * X) (i + 1) j = coeff₂ P i j := by
  rw [coeff₂, coeff₂, Polynomial.coeff_mul_X]

private theorem coeff₂_mul_X_zero (P : Polynomial (Polynomial ℤ)) (j : ℕ) :
    coeff₂ (P * X) 0 j = 0 := by
  rw [coeff₂, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, mul_zero]
  rfl

private theorem coeff₂_mul_CX_succ (P : Polynomial (Polynomial ℤ))
    (i j : ℕ) :
    coeff₂ (P * C X) i (j + 1) = coeff₂ P i j := by
  rw [coeff₂, coeff₂, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X]

private theorem coeff₂_mul_CX_zero (P : Polynomial (Polynomial ℤ)) (i : ℕ) :
    coeff₂ (P * C X) i 0 = 0 := by
  rw [coeff₂, Polynomial.coeff_mul_C, Polynomial.mul_coeff_zero,
    Polynomial.coeff_X_zero, mul_zero]

/-- The four-case product rule against `x + y + xy`. -/
private theorem coeff₂_mul_xyP_zero_zero (P : Polynomial (Polynomial ℤ)) :
    coeff₂ (P * xyP) 0 0 = 0 := by
  rw [xyP, mul_add, mul_add, coeff₂_add, coeff₂_add, coeff₂_mul_X_zero,
    coeff₂_mul_CX_zero, ← mul_assoc, coeff₂_mul_CX_zero]
  ring

private theorem coeff₂_mul_xyP_succ_zero (P : Polynomial (Polynomial ℤ))
    (i : ℕ) :
    coeff₂ (P * xyP) (i + 1) 0 = coeff₂ P i 0 := by
  rw [xyP, mul_add, mul_add, coeff₂_add, coeff₂_add, coeff₂_mul_X_succ,
    coeff₂_mul_CX_zero, ← mul_assoc, coeff₂_mul_CX_zero]
  ring

private theorem coeff₂_mul_xyP_zero_succ (P : Polynomial (Polynomial ℤ))
    (j : ℕ) :
    coeff₂ (P * xyP) 0 (j + 1) = coeff₂ P 0 j := by
  rw [xyP, mul_add, mul_add, coeff₂_add, coeff₂_add, coeff₂_mul_X_zero,
    coeff₂_mul_CX_succ, ← mul_assoc, coeff₂_mul_CX_succ, coeff₂_mul_X_zero]
  ring

private theorem coeff₂_mul_xyP_succ_succ (P : Polynomial (Polynomial ℤ))
    (i j : ℕ) :
    coeff₂ (P * xyP) (i + 1) (j + 1) =
      coeff₂ P i (j + 1) + coeff₂ P (i + 1) j + coeff₂ P i j := by
  rw [xyP, mul_add, mul_add, coeff₂_add, coeff₂_add, coeff₂_mul_X_succ,
    coeff₂_mul_CX_succ, ← mul_assoc, coeff₂_mul_CX_succ, coeff₂_mul_X_succ]

/-- Powers of `x + y + xy` have no coefficients below total degree `k`. -/
private theorem coeff₂_xyP_pow_eq_zero :
    ∀ (k i j : ℕ), i + j < k → coeff₂ (xyP ^ k) i j = 0 := by
  intro k
  induction k with
  | zero => exact fun i j h => absurd h (Nat.not_lt_zero _)
  | succ k ih =>
      intro i j hij
      rw [pow_succ]
      match i, j with
      | 0, 0 => exact coeff₂_mul_xyP_zero_zero _
      | i + 1, 0 =>
          rw [coeff₂_mul_xyP_succ_zero]
          exact ih i 0 (by omega)
      | 0, j + 1 =>
          rw [coeff₂_mul_xyP_zero_succ]
          exact ih 0 j (by omega)
      | i + 1, j + 1 =>
          rw [coeff₂_mul_xyP_succ_succ, ih i (j + 1) (by omega),
            ih (i + 1) j (by omega), ih i j (by omega)]
          ring

/-- The geometric partial sum `W = (Σ_{k<n} (-(x+y+xy))^k)·(1+y)` — the
`x`-derivative of the truncated `log(1 + x + y + xy)`. -/
private noncomputable def geomW (n : ℕ) : Polynomial (Polynomial ℤ) :=
  (∑ k ∈ Finset.range n, (-xyP) ^ k) * (1 + C X)

private theorem one_add_xyP_mul_geomW (n : ℕ) :
    (1 + xyP) * geomW n = (1 - (-xyP) ^ n) * (1 + C X) := by
  have hg := geom_sum_mul (-xyP) n
  have h1 : (∑ k ∈ Finset.range n, (-xyP) ^ k) * (1 + xyP) =
      1 - (-xyP) ^ n := by linear_combination -hg
  rw [geomW, show (1 + xyP) * ((∑ k ∈ Finset.range n, (-xyP) ^ k) *
    (1 + C X)) = ((∑ k ∈ Finset.range n, (-xyP) ^ k) * (1 + xyP)) *
    (1 + C X) by ring, h1]

private theorem coeff₂_one_add_CX_zero_zero : coeff₂ (1 + C X) 0 0 = 1 := by
  rw [coeff₂_add, coeff₂_one_zero_zero, coeff₂, Polynomial.coeff_C]
  simp

private theorem coeff₂_one_add_CX_zero_one : coeff₂ (1 + C X) 0 1 = 1 := by
  rw [coeff₂_add, coeff₂_one_zero_succ, coeff₂, Polynomial.coeff_C]
  simp

private theorem coeff₂_one_add_CX_succ_left (i j : ℕ) :
    coeff₂ (1 + C X) (i + 1) j = 0 := by
  rw [coeff₂_add, coeff₂_one_succ_left, coeff₂, Polynomial.coeff_C]
  simp

private theorem coeff₂_one_add_CX_zero_ge_two (j : ℕ) :
    coeff₂ (1 + C X) 0 (j + 2) = 0 := by
  rw [coeff₂_add, coeff₂_one_zero_succ, coeff₂, Polynomial.coeff_C]
  simp [Polynomial.coeff_X]

private theorem neg_xyP_pow (k : ℕ) :
    (-xyP) ^ k = (-1) ^ k * xyP ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, pow_succ, ih]
      ring

private theorem coeff₂_neg_xyP_pow (n i j : ℕ) (h : i + j < n) :
    coeff₂ ((-xyP) ^ n) i j = 0 := by
  rw [neg_xyP_pow, coeff₂_neg_one_pow_mul, coeff₂_xyP_pow_eq_zero n i j h,
    mul_zero]

/-- The geometric identity's right side agrees with `1 + y` in low total
degree. -/
private theorem coeff₂_geom_rhs (n i j : ℕ) (hij : i + j < n) :
    coeff₂ ((1 - (-xyP) ^ n) * (1 + C X)) i j = coeff₂ (1 + C X) i j := by
  rw [sub_mul, one_mul, coeff₂_sub]
  have hz : coeff₂ ((-xyP) ^ n * (1 + C X)) i j = 0 := by
    rw [mul_add, mul_one, coeff₂_add, coeff₂_neg_xyP_pow n i j hij]
    match j with
    | 0 => rw [coeff₂_mul_CX_zero, add_zero]
    | j + 1 => rw [coeff₂_mul_CX_succ, coeff₂_neg_xyP_pow n i j (by omega),
        add_zero]
  rw [hz, sub_zero]

/-- The coefficient equation extracted from
`(1 + xyP)·W = (1 - (-xyP)^n)(1 + y)` at a fixed bidegree. -/
private theorem geomW_key (n i j : ℕ) (hij : i + j < n) :
    coeff₂ (geomW n) i j + coeff₂ (geomW n * xyP) i j =
      coeff₂ (1 + C X) i j := by
  have hkey := congrArg (fun P => coeff₂ P i j) (one_add_xyP_mul_geomW n)
  rw [add_mul, one_mul, coeff₂_add, mul_comm xyP (geomW n),
    coeff₂_geom_rhs n i j hij] at hkey
  exact hkey

/-- Low bidegree coefficients of the geometric sum: `1/(1+x)` along
`j = 0`, and nothing for `j ≥ 1`. -/
private theorem coeff₂_geomW_aux (n : ℕ) :
    ∀ d : ℕ,
      (∀ i, i = d → i < n → coeff₂ (geomW n) i 0 = (-1) ^ i) ∧
      (∀ i j, i + j = d → 1 ≤ j → i + j < n →
        coeff₂ (geomW n) i j = 0) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      constructor
      · intro i hd hn
        subst hd
        match i with
        | 0 =>
            have hkey := geomW_key n 0 0 hn
            rw [coeff₂_mul_xyP_zero_zero, add_zero,
              coeff₂_one_add_CX_zero_zero] at hkey
            rw [hkey, pow_zero]
        | i + 1 =>
            have hkey := geomW_key n (i + 1) 0 hn
            rw [coeff₂_mul_xyP_succ_zero,
              (ih i (by omega)).1 i rfl (by omega),
              coeff₂_one_add_CX_succ_left] at hkey
            have hps : ((-1 : ℤ)) ^ (i + 1) = -(-1) ^ i := by
              rw [pow_succ]; ring
            rw [hps]
            linarith [hkey]
      · intro i j hd hj hn
        subst hd
        match i, j with
        | i, 0 => omega
        | 0, 1 =>
            have hkey := geomW_key n 0 1 hn
            rw [coeff₂_mul_xyP_zero_succ,
              (ih 0 (by omega)).1 0 rfl (by omega),
              coeff₂_one_add_CX_zero_one, pow_zero] at hkey
            linarith [hkey]
        | 0, j + 2 =>
            have hkey := geomW_key n 0 (j + 2) hn
            rw [coeff₂_mul_xyP_zero_succ,
              (ih (0 + (j + 1)) (by omega)).2 0 (j + 1) rfl (by omega)
                (by omega),
              coeff₂_one_add_CX_zero_ge_two] at hkey
            linarith [hkey]
        | i + 1, j + 1 =>
            have hkey := geomW_key n (i + 1) (j + 1) hn
            rw [coeff₂_mul_xyP_succ_succ,
              (ih (i + (j + 1)) (by omega)).2 i (j + 1) rfl (by omega)
                (by omega),
              coeff₂_one_add_CX_succ_left] at hkey
            match j with
            | 0 =>
                rw [(ih (i + 1 + 0) (by omega)).1 (i + 1) rfl (by omega),
                  (ih (i + 0) (by omega)).1 i rfl (by omega)] at hkey
                have h3 : ((-1 : ℤ)) ^ (i + 1) + (-1) ^ i = 0 := by
                  rw [pow_succ]; ring
                linarith [hkey, h3]
            | j + 1 =>
                rw [(ih ((i + 1) + (j + 1)) (by omega)).2 (i + 1) (j + 1)
                    rfl (by omega) (by omega),
                  (ih (i + (j + 1)) (by omega)).2 i (j + 1) rfl (by omega)
                    (by omega)] at hkey
                linarith [hkey]

/-- The `j ≥ 1` coefficients of the geometric sum vanish. -/
private theorem coeff₂_geomW_pos (n i j : ℕ) (hj : 1 ≤ j)
    (hn : i + j < n) :
    coeff₂ (geomW n) i j = 0 :=
  (coeff₂_geomW_aux n (i + j)).2 i j rfl hj hn

/-- Derivative bridge:
`(i+1)·N(k+1, i+1, j) = (k+1)·coeff₂(xyP^k·(1+y), i, j)`. -/
private theorem coeff₂_pow_succ_mul_index (k i j : ℕ) :
    ((i : ℤ) + 1) * coeff₂ (xyP ^ (k + 1)) (i + 1) j =
      ((k : ℤ) + 1) * coeff₂ (xyP ^ k * (1 + C X)) i j := by
  have hder : derivative xyP = 1 + C X := by
    rw [xyP]
    simp [derivative_add, derivative_mul]
  have hpow : derivative (xyP ^ (k + 1)) =
      C ((k : Polynomial ℤ) + 1) * (xyP ^ k * (1 + C X)) := by
    rw [derivative_pow, hder, Nat.add_sub_cancel]
    push_cast
    ring
  have hcoeff := congrArg (fun P => (P.coeff i).coeff j) hpow
  rw [Polynomial.coeff_derivative] at hcoeff
  rw [Polynomial.coeff_C_mul] at hcoeff
  have hL : ((xyP ^ (k + 1)).coeff (i + 1) * ((i : Polynomial ℤ) + 1)).coeff j
      = coeff₂ (xyP ^ (k + 1)) (i + 1) j * ((i : ℤ) + 1) := by
    have hC : ((i : Polynomial ℤ) + 1) = C ((i : ℤ) + 1) := by
      rw [map_add, map_one, map_natCast]
    rw [hC, Polynomial.coeff_mul_C]
    rfl
  have hR : (((k : Polynomial ℤ) + 1) * (xyP ^ k * (1 + C X)).coeff i).coeff j
      = ((k : ℤ) + 1) * coeff₂ (xyP ^ k * (1 + C X)) i j := by
    have hC : ((k : Polynomial ℤ) + 1) = C ((k : ℤ) + 1) := by
      rw [map_add, map_one, map_natCast]
    rw [hC, Polynomial.coeff_C_mul]
    rfl
  rw [hL, hR] at hcoeff
  linarith [hcoeff]

/-- **The log coefficient identity**: for `i, j ≥ 1` and `i + j ≤ n`,
`Σ_{k<n} (-1)^k/(k+1) · N(k+1, i, j) = 0` — the `x^i y^j` coefficient of
`log((1+x)(1+y)) - log(1+x) - log(1+y)`. -/
private theorem log_coeff_vanish [Field R] [CharZero R] {i j n : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j ≤ n) :
    ∑ k ∈ Finset.range n,
      (-1 : R) ^ k * ((k + 1 : ℕ) : R)⁻¹ *
        (coeff₂ (xyP ^ (k + 1)) i j : R) = 0 := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hi1 : ((i : R) + 1) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := R)).2 (Nat.succ_ne_zero i)
  -- multiply through by `i + 1`; the derivative bridge then cancels the
  -- `1/(k+1)` weight and the sum becomes the geometric sum's coefficient
  suffices h : ((i : R) + 1) * (∑ k ∈ Finset.range n,
      (-1 : R) ^ k * ((k + 1 : ℕ) : R)⁻¹ *
        (coeff₂ (xyP ^ (k + 1)) (i + 1) j : R)) = 0 by
    rcases mul_eq_zero.1 h with h1 | h2
    · exact absurd h1 hi1
    · exact h2
  rw [Finset.mul_sum]
  have hstep : ∀ k : ℕ,
      ((i : R) + 1) * ((-1 : R) ^ k * ((k + 1 : ℕ) : R)⁻¹ *
          (coeff₂ (xyP ^ (k + 1)) (i + 1) j : R)) =
        (-1 : R) ^ k * (coeff₂ (xyP ^ k * (1 + C X)) i j : R) := by
    intro k
    have hZ := coeff₂_pow_succ_mul_index k i j
    have hZR : ((i : R) + 1) * (coeff₂ (xyP ^ (k + 1)) (i + 1) j : R) =
        ((k : R) + 1) * (coeff₂ (xyP ^ k * (1 + C X)) i j : R) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : R)) hZ
    have hk1 : ((k : R) + 1) ≠ 0 := by
      exact_mod_cast (Nat.cast_ne_zero (R := R)).2 (Nat.succ_ne_zero k)
    have hcast_k : ((k + 1 : ℕ) : R) = (k : R) + 1 := by push_cast; ring
    calc ((i : R) + 1) * ((-1 : R) ^ k * ((k + 1 : ℕ) : R)⁻¹ *
            (coeff₂ (xyP ^ (k + 1)) (i + 1) j : R))
        = (-1 : R) ^ k * ((k : R) + 1)⁻¹ *
            (((i : R) + 1) * (coeff₂ (xyP ^ (k + 1)) (i + 1) j : R)) := by
          rw [hcast_k]; ring
      _ = (-1 : R) ^ k * ((k : R) + 1)⁻¹ *
            (((k : R) + 1) * (coeff₂ (xyP ^ k * (1 + C X)) i j : R)) := by
          rw [hZR]
      _ = (((k : R) + 1)⁻¹ * ((k : R) + 1)) *
            ((-1 : R) ^ k * (coeff₂ (xyP ^ k * (1 + C X)) i j : R)) := by
          ring
      _ = (-1 : R) ^ k * (coeff₂ (xyP ^ k * (1 + C X)) i j : R) := by
          rw [inv_mul_cancel₀ hk1, one_mul]
  rw [Finset.sum_congr rfl fun k _ => hstep k]
  have hsum : ∑ k ∈ Finset.range n,
      ((-1 : R) ^ k * (coeff₂ (xyP ^ k * (1 + C X)) i j : R)) =
      ((coeff₂ (geomW n) i j : ℤ) : R) := by
    have hgw : coeff₂ (geomW n) i j =
        ∑ k ∈ Finset.range n,
          (-1 : ℤ) ^ k * coeff₂ (xyP ^ k * (1 + C X)) i j := by
      rw [geomW, Finset.sum_mul, coeff₂_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hterm : (-xyP) ^ k * (1 + C X) =
          (-1) ^ k * (xyP ^ k * (1 + C X)) := by
        rw [neg_xyP_pow]
        ring
      rw [hterm, coeff₂_neg_one_pow_mul]
    rw [hgw]
    push_cast
    rfl
  rw [hsum, coeff₂_geomW_pos n i j hj (by omega)]
  simp

end PolyAux

/-! ### The shuffle expansion of tensor powers of the augmentation part -/

section Expansion

variable [CommRing R]

/-- The three-term shuffle formula for the augmentation part of a
group-like series. -/
private theorem shuffleCoeff_augmentationPart
    {a : (List α → R)} (ha : IsGroupLike a) (u v : List α) :
    shuffleCoeff (augmentationPart a) u v =
      augmentationPart a u * unit α R v +
        unit α R u * augmentationPart a v +
        augmentationPart a u * augmentationPart a v := by
  have h1 : shuffleCoeff (augmentationPart a) u v =
      shuffleCoeff a u v - shuffleCoeff (unit α R) u v :=
    list_sum_map_sub (Word.shuffle u v) a (unit α R)
  rw [h1, ← ha.2, shuffleCoeff_unit]
  simp only [coeff_apply]
  have hm : ∀ w : List α, augmentationPart a w = a w - unit α R w :=
    fun w => rfl
  rw [hm u, hm v]
  ring

private theorem aux_rearrange (x y z : R) : (x * y) * z = y * (x * z) := by
  ring

/-- The blockwise reassembly of the double sum under the trinomial
recurrence — pure `Finset.range` algebra. -/
private theorem double_sum_assembly (L M : ℕ) (c c' : ℕ → ℕ → R)
    (P Q : ℕ → R)
    (hc00 : c' 0 0 = 0)
    (hcL : ∀ i, c' (i + 1) 0 = c i 0)
    (hcM : ∀ j, c' 0 (j + 1) = c 0 j)
    (hcS : ∀ i j, c' (i + 1) (j + 1) =
      c i (j + 1) + c (i + 1) j + c i j)
    (hP : P (L + 1) = 0) (hQ : Q (M + 1) = 0) :
    ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
        c' i j * (P i * Q j) =
      (∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
        c i j * (P (i + 1) * Q j)) +
      (∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
        c i j * (P i * Q (j + 1))) +
      (∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
        c i j * (P (i + 1) * Q (j + 1))) := by
  -- Left side: peel the first index of each range and apply the
  -- recurrence for `c'`.
  have hLHS : ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
      c' i j * (P i * Q j) =
      (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range M,
        (c i (j + 1) + c (i + 1) j + c i j) *
          (P (i + 1) * Q (j + 1))) +
      (∑ i ∈ Finset.range L, c i 0 * (P (i + 1) * Q 0)) +
      (∑ j ∈ Finset.range M, c 0 j * (P 0 * Q (j + 1))) := by
    rw [Finset.sum_range_succ']
    have hfirst : ∀ i, ∑ j ∈ Finset.range (M + 1),
        c' (i + 1) j * (P (i + 1) * Q j) =
        (∑ j ∈ Finset.range M,
          (c i (j + 1) + c (i + 1) j + c i j) *
            (P (i + 1) * Q (j + 1))) +
        c i 0 * (P (i + 1) * Q 0) := by
      intro i
      rw [Finset.sum_range_succ']
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by rw [hcS]
      · rw [hcL]
    have hzero : ∑ j ∈ Finset.range (M + 1), c' 0 j * (P 0 * Q j) =
        ∑ j ∈ Finset.range M, c 0 j * (P 0 * Q (j + 1)) := by
      rw [Finset.sum_range_succ']
      rw [hc00, zero_mul, add_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [hcM]
    rw [Finset.sum_congr rfl fun i _ => hfirst i, hzero,
      Finset.sum_add_distrib]
  -- Right side, first block: kill the top row with `hP`, then peel the
  -- second index.
  have hS1 : ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
      c i j * (P (i + 1) * Q j) =
      (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range M,
        c i (j + 1) * (P (i + 1) * Q (j + 1))) +
      (∑ i ∈ Finset.range L, c i 0 * (P (i + 1) * Q 0)) := by
    rw [Finset.sum_range_succ]
    have htop : ∑ j ∈ Finset.range (M + 1), c L j * (P (L + 1) * Q j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hP, zero_mul, mul_zero]
    rw [htop, add_zero]
    have hpeel : ∀ i, ∑ j ∈ Finset.range (M + 1),
        c i j * (P (i + 1) * Q j) =
        (∑ j ∈ Finset.range M, c i (j + 1) * (P (i + 1) * Q (j + 1))) +
        c i 0 * (P (i + 1) * Q 0) := fun i => Finset.sum_range_succ' _ M
    rw [Finset.sum_congr rfl fun i _ => hpeel i, Finset.sum_add_distrib]
  -- Second block: kill the top column with `hQ`, then peel the first
  -- index.
  have hS2 : ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
      c i j * (P i * Q (j + 1)) =
      (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range M,
        c (i + 1) j * (P (i + 1) * Q (j + 1))) +
      (∑ j ∈ Finset.range M, c 0 j * (P 0 * Q (j + 1))) := by
    have hkill : ∀ i, ∑ j ∈ Finset.range (M + 1),
        c i j * (P i * Q (j + 1)) =
        ∑ j ∈ Finset.range M, c i j * (P i * Q (j + 1)) := by
      intro i
      rw [Finset.sum_range_succ, hQ, mul_zero, mul_zero, add_zero]
    rw [Finset.sum_congr rfl fun i _ => hkill i, Finset.sum_range_succ']
  -- Third block: kill both tops.
  have hS3 : ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
      c i j * (P (i + 1) * Q (j + 1)) =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range M,
        c i j * (P (i + 1) * Q (j + 1)) := by
    have hkill : ∀ i, ∑ j ∈ Finset.range (M + 1),
        c i j * (P (i + 1) * Q (j + 1)) =
        ∑ j ∈ Finset.range M, c i j * (P (i + 1) * Q (j + 1)) := by
      intro i
      rw [Finset.sum_range_succ, hQ, mul_zero, mul_zero, add_zero]
    rw [Finset.sum_congr rfl fun i _ => hkill i, Finset.sum_range_succ]
    have htop : ∑ j ∈ Finset.range M, c L j * (P (L + 1) * Q (j + 1)) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hP, zero_mul, mul_zero]
    rw [htop, add_zero]
  rw [hLHS, hS1, hS2, hS3]
  have hsplit : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range M,
      (c i (j + 1) + c (i + 1) j + c i j) * (P (i + 1) * Q (j + 1)) =
      (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range M,
        c i (j + 1) * (P (i + 1) * Q (j + 1))) +
      (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range M,
        c (i + 1) j * (P (i + 1) * Q (j + 1))) +
      (∑ i ∈ Finset.range L, ∑ j ∈ Finset.range M,
        c i j * (P (i + 1) * Q (j + 1))) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsplit]
  ring

private theorem length_snd_le_of_mem_splits {p : List α × List α}
    {w : List α} (hp : p ∈ Word.splits w) : p.2.length ≤ w.length := by
  have := congrArg List.length (Word.mem_splits_append hp)
  rw [List.length_append] at this
  omega

private theorem sum_splits_mul_tensorPower
    (m : (List α → R)) (i : ℕ) (u : List α) :
    ((Word.splits u).map fun p =>
      m p.1 * tensorPower m i p.2).sum = tensorPower m (i + 1) u := by
  rw [tensorPower_succ]
  rfl

open Polynomial in
/-- **The shuffle expansion of tensor powers**: for group-like `a` with
`m := a - 1`,
`Σ_{x ∈ u ⧢ v} m^{⊗k}(x) = Σ_{i,j} N(k,i,j)·m^{⊗i}(u)·m^{⊗j}(v)` where
`N(k,i,j)` is the `xⁱyʲ` coefficient of `(x+y+xy)^k`. -/
private theorem shuffleCoeff_tensorPower_expand
    {a : (List α → R)} (ha : IsGroupLike a) (L M : ℕ) :
    ∀ (k : ℕ) (u v : List α), u.length ≤ L → v.length ≤ M →
      shuffleCoeff (tensorPower (augmentationPart a) k) u v =
        ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
          (coeff₂ (xyP ^ k) i j : R) *
            (tensorPower (augmentationPart a) i u *
              tensorPower (augmentationPart a) j v) := by
  have hm0 : augmentationPart a [] = 0 := by
    show coeff a [] - coeff (unit α R) [] = 0
    rw [ha.coeff_nil]
    show (1 : R) - 1 = 0
    ring
  intro k
  induction k with
  | zero =>
      intro u v hu hv
      -- Left side: the shuffle sum of the unit.
      have hL : shuffleCoeff (tensorPower (augmentationPart a) 0) u v =
          unit α R u * unit α R v := shuffleCoeff_unit u v
      -- Right side: only the `(0,0)` term survives.
      rw [hL, pow_zero, Finset.sum_range_succ']
      have hz1 : ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range (M + 1),
          (coeff₂ 1 (i + 1) j : R) *
            (tensorPower (augmentationPart a) (i + 1) u *
              tensorPower (augmentationPart a) j v) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [coeff₂_one_succ_left]
        norm_num
      rw [hz1, zero_add, Finset.sum_range_succ']
      have hz2 : ∑ j ∈ Finset.range M,
          (coeff₂ 1 0 (j + 1) : R) *
            (tensorPower (augmentationPart a) 0 u *
              tensorPower (augmentationPart a) (j + 1) v) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [coeff₂_one_zero_succ]
        norm_num
      rw [hz2, zero_add, coeff₂_one_zero_zero]
      norm_num
  | succ k ih =>
      intro u v hu hv
      -- Pairing lemma at `m ⊗ m^{⊗k}`.
      have h1 : shuffleCoeff
          (tensorPower (augmentationPart a) (k + 1)) u v =
          ((Word.splits u).map fun p =>
            ((Word.splits v).map fun q =>
              shuffleCoeff (augmentationPart a) p.1 q.1 *
                shuffleCoeff (tensorPower (augmentationPart a) k)
                  p.2 q.2).sum).sum := by
        rw [tensorPower_succ]
        exact shuffleCoeff_tensorProduct _ _ u v
      -- Substitute the three-term formula and distribute.
      have h3 := fun (x y : List α) => shuffleCoeff_augmentationPart ha x y
      have h2 : shuffleCoeff
          (tensorPower (augmentationPart a) (k + 1)) u v =
          (((Word.splits u).map fun p => ((Word.splits v).map fun q =>
            (augmentationPart a p.1 * unit α R q.1) *
              shuffleCoeff (tensorPower (augmentationPart a) k)
                p.2 q.2).sum).sum) +
          (((Word.splits u).map fun p => ((Word.splits v).map fun q =>
            (unit α R p.1 * augmentationPart a q.1) *
              shuffleCoeff (tensorPower (augmentationPart a) k)
                p.2 q.2).sum).sum) +
          (((Word.splits u).map fun p => ((Word.splits v).map fun q =>
            (augmentationPart a p.1 * augmentationPart a q.1) *
              shuffleCoeff (tensorPower (augmentationPart a) k)
                p.2 q.2).sum).sum) := by
        rw [h1]
        simp only [h3, add_mul, list_sum_map_add]
      rw [h2]
      -- Notation for the three blocks.
      set m := augmentationPart a with hm
      -- Block 1: the unit kills the `v`-split.
      have hB1 : ((Word.splits u).map fun p =>
          ((Word.splits v).map fun q =>
            (m p.1 * unit α R q.1) * shuffleCoeff (tensorPower m k) p.2 q.2).sum).sum =
          ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
            (coeff₂ (xyP ^ k) i j : R) *
              (tensorPower m (i + 1) u * tensorPower m j v) := by
        have hinner : ∀ p : List α × List α, p ∈ Word.splits u →
            ((Word.splits v).map fun q =>
              (m p.1 * unit α R q.1) * shuffleCoeff (tensorPower m k) p.2 q.2).sum =
            m p.1 * shuffleCoeff (tensorPower m k) p.2 v := by
          intro p _
          have hre : ∀ q : List α × List α,
              (m p.1 * unit α R q.1) * shuffleCoeff (tensorPower m k) p.2 q.2 =
                unit α R q.1 * (m p.1 * shuffleCoeff (tensorPower m k) p.2 q.2) := fun q =>
            aux_rearrange _ _ _
          rw [List.map_congr_left fun q _ => hre q]
          exact sum_splits_unit_left (fun v2 => m p.1 * shuffleCoeff (tensorPower m k) p.2 v2) v
        rw [List.map_congr_left hinner]
        have hlen : ∀ p : List α × List α, p ∈ Word.splits u →
            p.2.length ≤ L := fun p hp =>
          le_trans (length_snd_le_of_mem_splits hp) hu
        have hIH : ∀ p : List α × List α, p ∈ Word.splits u →
            m p.1 * shuffleCoeff (tensorPower m k) p.2 v =
            ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
              (coeff₂ (xyP ^ k) i j : R) *
                (m p.1 * (tensorPower m i p.2 * tensorPower m j v)) := by
          intro p hp
          rw [ih p.2 v (hlen p hp) hv, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [List.map_congr_left hIH]
        refine Eq.trans (list_sum_finset_sum_swap (Word.splits u)
          (Finset.range (L + 1)) (fun p i =>
            ∑ j ∈ Finset.range (M + 1), (coeff₂ (xyP ^ k) i j : R) *
              (m p.1 * (tensorPower m i p.2 * tensorPower m j v)))) ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Eq.trans (list_sum_finset_sum_swap (Word.splits u)
          (Finset.range (M + 1)) (fun p j =>
            (coeff₂ (xyP ^ k) i j : R) *
              (m p.1 * (tensorPower m i p.2 * tensorPower m j v)))) ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        have hre2 : ∀ p : List α × List α,
            (coeff₂ (xyP ^ k) i j : R) *
              (m p.1 * (tensorPower m i p.2 * tensorPower m j v)) =
            (coeff₂ (xyP ^ k) i j : R) *
              ((m p.1 * tensorPower m i p.2) * tensorPower m j v) := by
          intro p; ring
        rw [List.map_congr_left fun p _ => hre2 p,
          List.sum_map_mul_left, List.sum_map_mul_right]
        rw [sum_splits_mul_tensorPower m i u]
      -- Block 2: the unit kills the `u`-split.
      have hB2 : ((Word.splits u).map fun p =>
          ((Word.splits v).map fun q =>
            (unit α R p.1 * m q.1) * shuffleCoeff (tensorPower m k) p.2 q.2).sum).sum =
          ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
            (coeff₂ (xyP ^ k) i j : R) *
              (tensorPower m i u * tensorPower m (j + 1) v) := by
        have hout : ∀ p : List α × List α, p ∈ Word.splits u →
            ((Word.splits v).map fun q =>
              (unit α R p.1 * m q.1) * shuffleCoeff (tensorPower m k) p.2 q.2).sum =
            unit α R p.1 * ((Word.splits v).map fun q =>
              m q.1 * shuffleCoeff (tensorPower m k) p.2 q.2).sum := by
          intro p _
          rw [← List.sum_map_mul_left]
          apply congrArg List.sum
          apply List.map_congr_left
          intro q _
          ring
        rw [List.map_congr_left hout,
          sum_splits_unit_left (fun u2 => ((Word.splits v).map fun q =>
            m q.1 * shuffleCoeff (tensorPower m k) u2 q.2).sum) u]
        have hlen : ∀ q : List α × List α, q ∈ Word.splits v →
            q.2.length ≤ M := fun q hq =>
          le_trans (length_snd_le_of_mem_splits hq) hv
        have hIH : ∀ q : List α × List α, q ∈ Word.splits v →
            m q.1 * shuffleCoeff (tensorPower m k) u q.2 =
            ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
              (coeff₂ (xyP ^ k) i j : R) *
                (m q.1 * (tensorPower m i u * tensorPower m j q.2)) := by
          intro q hq
          rw [ih u q.2 hu (hlen q hq), Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [List.map_congr_left hIH]
        refine Eq.trans (list_sum_finset_sum_swap (Word.splits v)
          (Finset.range (L + 1)) (fun q i =>
            ∑ j ∈ Finset.range (M + 1), (coeff₂ (xyP ^ k) i j : R) *
              (m q.1 * (tensorPower m i u * tensorPower m j q.2)))) ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Eq.trans (list_sum_finset_sum_swap (Word.splits v)
          (Finset.range (M + 1)) (fun q j =>
            (coeff₂ (xyP ^ k) i j : R) *
              (m q.1 * (tensorPower m i u * tensorPower m j q.2)))) ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        have hre2 : ∀ q : List α × List α,
            (coeff₂ (xyP ^ k) i j : R) *
              (m q.1 * (tensorPower m i u * tensorPower m j q.2)) =
            (coeff₂ (xyP ^ k) i j : R) * tensorPower m i u *
              (m q.1 * tensorPower m j q.2) := by
          intro q; ring
        rw [List.map_congr_left fun q _ => hre2 q, List.sum_map_mul_left]
        rw [sum_splits_mul_tensorPower m j v]
        ring
      -- Block 3: both splits carry `m`.
      have hB3 : ((Word.splits u).map fun p =>
          ((Word.splits v).map fun q =>
            (m p.1 * m q.1) * shuffleCoeff (tensorPower m k) p.2 q.2).sum).sum =
          ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
            (coeff₂ (xyP ^ k) i j : R) *
              (tensorPower m (i + 1) u * tensorPower m (j + 1) v) := by
        have hlenu : ∀ p : List α × List α, p ∈ Word.splits u →
            p.2.length ≤ L := fun p hp =>
          le_trans (length_snd_le_of_mem_splits hp) hu
        have hlenv : ∀ q : List α × List α, q ∈ Word.splits v →
            q.2.length ≤ M := fun q hq =>
          le_trans (length_snd_le_of_mem_splits hq) hv
        have hIH : ∀ p : List α × List α, p ∈ Word.splits u →
            ((Word.splits v).map fun q =>
              (m p.1 * m q.1) * shuffleCoeff (tensorPower m k) p.2 q.2).sum =
            ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
              (coeff₂ (xyP ^ k) i j : R) *
                ((m p.1 * tensorPower m i p.2) *
                  ((Word.splits v).map fun q =>
                    m q.1 * tensorPower m j q.2).sum) := by
          intro p hp
          have hq : ∀ q : List α × List α, q ∈ Word.splits v →
              (m p.1 * m q.1) * shuffleCoeff (tensorPower m k) p.2 q.2 =
              ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (M + 1),
                (coeff₂ (xyP ^ k) i j : R) *
                  ((m p.1 * tensorPower m i p.2) *
                    (m q.1 * tensorPower m j q.2)) := by
            intro q hq
            rw [ih p.2 q.2 (hlenu p hp) (hlenv q hq), Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          rw [List.map_congr_left hq]
          refine Eq.trans (list_sum_finset_sum_swap (Word.splits v)
            (Finset.range (L + 1)) (fun q i =>
              ∑ j ∈ Finset.range (M + 1), (coeff₂ (xyP ^ k) i j : R) *
                ((m p.1 * tensorPower m i p.2) *
                  (m q.1 * tensorPower m j q.2)))) ?_
          refine Finset.sum_congr rfl fun i _ => ?_
          refine Eq.trans (list_sum_finset_sum_swap (Word.splits v)
            (Finset.range (M + 1)) (fun q j =>
              (coeff₂ (xyP ^ k) i j : R) *
                ((m p.1 * tensorPower m i p.2) *
                  (m q.1 * tensorPower m j q.2)))) ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
        rw [List.map_congr_left hIH]
        refine Eq.trans (list_sum_finset_sum_swap (Word.splits u)
          (Finset.range (L + 1)) (fun p i =>
            ∑ j ∈ Finset.range (M + 1), (coeff₂ (xyP ^ k) i j : R) *
              ((m p.1 * tensorPower m i p.2) *
                ((Word.splits v).map fun q =>
                  m q.1 * tensorPower m j q.2).sum))) ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Eq.trans (list_sum_finset_sum_swap (Word.splits u)
          (Finset.range (M + 1)) (fun p j =>
            (coeff₂ (xyP ^ k) i j : R) *
              ((m p.1 * tensorPower m i p.2) *
                ((Word.splits v).map fun q =>
                  m q.1 * tensorPower m j q.2).sum))) ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        have hre2 : ∀ p : List α × List α,
            (coeff₂ (xyP ^ k) i j : R) *
              ((m p.1 * tensorPower m i p.2) *
                ((Word.splits v).map fun q =>
                  m q.1 * tensorPower m j q.2).sum) =
            (m p.1 * tensorPower m i p.2) *
              ((coeff₂ (xyP ^ k) i j : R) *
                ((Word.splits v).map fun q =>
                  m q.1 * tensorPower m j q.2).sum) := by
          intro p; ring
        rw [List.map_congr_left fun p _ => hre2 p, List.sum_map_mul_right]
        rw [sum_splits_mul_tensorPower m i u,
          sum_splits_mul_tensorPower m j v]
        ring
      rw [hB1, hB2, hB3]
      -- Assemble via the trinomial recurrence.
      have hP : tensorPower m (L + 1) u = 0 :=
        tensorPower_eq_zero_of_short hm0 (L + 1) u (by omega)
      have hQ : tensorPower m (M + 1) v = 0 :=
        tensorPower_eq_zero_of_short hm0 (M + 1) v (by omega)
      refine (double_sum_assembly L M
        (fun i j => (coeff₂ (xyP ^ k) i j : R))
        (fun i j => (coeff₂ (xyP ^ (k + 1)) i j : R))
        (fun i => tensorPower m i u) (fun j => tensorPower m j v)
        ?_ ?_ ?_ ?_ hP hQ).symm
      · rw [pow_succ, coeff₂_mul_xyP_zero_zero]
        norm_num
      · intro i
        rw [pow_succ, coeff₂_mul_xyP_succ_zero]
      · intro j
        rw [pow_succ, coeff₂_mul_xyP_zero_succ]
      · intro i j
        rw [pow_succ, coeff₂_mul_xyP_succ_succ]
        push_cast
        ring

end Expansion

/-! ### The main theorem -/

/-- **The truncated log-signature of a group-like series is primitive up
to the truncation degree.** This is the coefficient-level statement that
the logarithm of a shuffle character is an infinitesimal character —
the first-order form of "log-signatures are Lie elements". -/
theorem isPrimitiveUpToDegree_logSignatureTruncated [Field R] [CharZero R]
    {a : (List α → R)} (ha : IsGroupLike a) (n : ℕ) :
    IsPrimitiveUpToDegree (logSignatureTruncated a n) n := by
  have hm0 : augmentationPart a [] = 0 := by
    show coeff a [] - coeff (unit α R) [] = 0
    rw [ha.coeff_nil]
    show (1 : R) - 1 = 0
    ring
  constructor
  · -- the empty coefficient: every tensor power `k ≥ 1` vanishes at `[]`
    show ((List.range n).map fun i =>
      ((-1 : R)) ^ (i + 1 + 1) * ((i + 1 : ℕ) : R)⁻¹ *
        coeff (tensorPower (augmentationPart a) (i + 1)) []).sum = 0
    apply List.sum_eq_zero
    intro x hx
    rcases List.mem_map.1 hx with ⟨i, _, rfl⟩
    rw [tensorPower_coeff_nil]
    show ((-1 : R)) ^ (i + 1 + 1) * ((i + 1 : ℕ) : R)⁻¹ *
      (augmentationPart a [] ^ (i + 1)) = 0
    rw [hm0, zero_pow (Nat.succ_ne_zero i), mul_zero]
  · intro u v hu hv huv
    -- swap the shuffle sum with the truncation sum
    have hswap : shuffleCoeff (logSignatureTruncated a n) u v =
        ((List.range n).map fun i =>
          ((Word.shuffle u v).map fun w =>
            ((-1 : R)) ^ (i + 1 + 1) * ((i + 1 : ℕ) : R)⁻¹ *
              tensorPower (augmentationPart a) (i + 1) w).sum).sum :=
      list_sum_list_sum_swap (Word.shuffle u v) (List.range n) _
    rw [hswap]
    have hpull : ∀ i : ℕ,
        ((Word.shuffle u v).map fun w =>
          ((-1 : R)) ^ (i + 1 + 1) * ((i + 1 : ℕ) : R)⁻¹ *
            tensorPower (augmentationPart a) (i + 1) w).sum =
        ((-1 : R)) ^ (i + 1 + 1) * ((i + 1 : ℕ) : R)⁻¹ *
          shuffleCoeff (tensorPower (augmentationPart a) (i + 1)) u v :=
      fun i => List.sum_map_mul_left _ _ _
    rw [List.map_congr_left fun i _ => hpull i, list_range_map_sum]
    -- expand each tensor power
    have hexp := shuffleCoeff_tensorPower_expand ha u.length v.length
    rw [Finset.sum_congr rfl fun k _ => by
      rw [hexp (k + 1) u v le_rfl le_rfl]]
    -- push the truncation sum inside the double sum
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    -- factor the word-dependent part out of the truncation sum
    have hfactor : ∀ k : ℕ,
        ((-1 : R)) ^ (k + 1 + 1) * ((k + 1 : ℕ) : R)⁻¹ *
          ((coeff₂ (xyP ^ (k + 1)) i j : R) *
            (tensorPower (augmentationPart a) i u *
              tensorPower (augmentationPart a) j v)) =
        ((-1 : R)) ^ k * ((k + 1 : ℕ) : R)⁻¹ *
          (coeff₂ (xyP ^ (k + 1)) i j : R) *
            (tensorPower (augmentationPart a) i u *
              tensorPower (augmentationPart a) j v) := by
      intro k
      have hsign : ((-1 : R)) ^ (k + 1 + 1) = (-1 : R) ^ k := by
        rw [pow_succ, pow_succ]
        ring
      rw [hsign]
      ring
    rw [Finset.sum_congr rfl fun k _ => hfactor k, ← Finset.sum_mul]
    -- now kill each `(i,j)`
    match i, j with
    | 0, j =>
        have h0 : tensorPower (augmentationPart a) 0 u = 0 := by
          obtain ⟨x, u', rfl⟩ := List.exists_cons_of_ne_nil hu
          rfl
        rw [h0, zero_mul, mul_zero]
    | i + 1, 0 =>
        have h0 : tensorPower (augmentationPart a) 0 v = 0 := by
          obtain ⟨y, v', rfl⟩ := List.exists_cons_of_ne_nil hv
          rfl
        rw [h0, mul_zero, mul_zero]
    | i + 1, j + 1 =>
        have hlei : i + 1 ≤ u.length := by
          have := Finset.mem_range.1 hi
          omega
        have hlej : j + 1 ≤ v.length := by
          have := Finset.mem_range.1 hj
          omega
        rw [log_coeff_vanish (Nat.succ_le_succ (Nat.zero_le i))
          (Nat.succ_le_succ (Nat.zero_le j)) (by omega), zero_mul]

/-- The truncated log-signature of a bundled group-like signature is
primitive up to the truncation degree. -/
theorem Signature.isPrimitiveUpToDegree_logTruncated [Field R] [CharZero R]
    (σ : Signature α R) (n : ℕ) :
    IsPrimitiveUpToDegree (Signature.logTruncated σ n) n :=
  isPrimitiveUpToDegree_logSignatureTruncated σ.2 n

end Word

end RoughPaths
