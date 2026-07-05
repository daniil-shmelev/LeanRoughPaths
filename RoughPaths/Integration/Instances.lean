/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import RoughPaths.Signature.Linear
import RoughPaths.Integration.ControlledPath

/-!
# Concrete rough paths

The first genuine instances connecting the algebraic and analytic halves
of the library:

* `AlgebraicRoughPath.ofLinear` — the canonical (signature) lift of the
  linear path `t ↦ t·v`, a weakly geometric rough path over any field;
* `AlgebraicRoughPath.ofLinearClamped` — its clamp to the time window
  `[0, T₀]`, which satisfies the **global** level-2 Hölder bounds
  `IsLevel2RoughPath` with `α = 1/2` against the linear control
  `Control.ofReal (M²·T₀)` — so the entire rough integration and RDE
  theory applies to it;
* `AlgebraicRoughPath.bracketPath` — the Itô-type *bracket path*
  `exp((t-s)·(e₀⊗e₀))`: zero first level, symmetric second level `t-s`.
  Chen's identity holds (the binomial law for the tensor exponential) but
  the shuffle identity fails, so it is a genuinely **non-geometric**
  rough path; it is nevertheless level-2 with `α = 1/2`.
-/

namespace RoughPaths

open HopfAlgebras

open scoped ENNReal

universe u v

variable {α : Type u} {R : Type v}

/-- Clamp a real time to the window `[0, T₀]`. -/
noncomputable def clampTo (T₀ r : ℝ) : ℝ :=
  min (max r 0) T₀

theorem clampTo_mono (T₀ : ℝ) : Monotone (clampTo T₀) :=
  fun _ _ h => min_le_min (max_le_max h le_rfl) le_rfl

theorem clampTo_nonneg {T₀ : ℝ} (hT₀ : 0 ≤ T₀) (r : ℝ) :
    0 ≤ clampTo T₀ r :=
  le_min (le_max_right r 0) hT₀

theorem clampTo_le (T₀ r : ℝ) : clampTo T₀ r ≤ T₀ :=
  min_le_right _ _

/-- The clamp is 1-Lipschitz from the left. -/
theorem clampTo_le_add (T₀ : ℝ) {s t : ℝ} (h : s ≤ t) :
    clampTo T₀ t ≤ clampTo T₀ s + (t - s) := by
  have hmax : max t 0 ≤ max s 0 + (t - s) := by
    rcases le_total t 0 with h3 | h3 <;> rcases le_total s 0 with h4 | h4
    · rw [max_eq_right h3, max_eq_right h4]; linarith
    · rw [max_eq_right h3, max_eq_left h4]; linarith
    · rw [max_eq_left h3, max_eq_right h4]; linarith
    · rw [max_eq_left h3, max_eq_left h4]; linarith
  calc clampTo T₀ t ≤ min (max s 0 + (t - s)) T₀ :=
        min_le_min hmax le_rfl
    _ ≤ min (max s 0 + (t - s)) (T₀ + (t - s)) :=
        min_le_min le_rfl (by linarith)
    _ = clampTo T₀ s + (t - s) := min_add_add_right _ _ _

namespace AlgebraicRoughPath

/-- The canonical rough-path lift of the linear path `t ↦ t·v`: increments
are the linear signatures of the scaled segment. Chen's identity is the
semigroup law `tensorProduct_linearSignature_smul`. -/
def ofLinear [Field R] [CharZero R] (v : α → R) :
    AlgebraicRoughPath R α R where
  increment s t := Word.linearSignature ((t - s) • v)
  identity t := by
    rw [sub_self, zero_smul, Word.linearSignature_zero]
  chen s t u := by
    rw [show u - s = (t - s) + (u - t) from by ring]
    exact (Word.tensorProduct_linearSignature_smul v _ _).symm
  unitEmpty s t := Word.linearSignature_nil _

@[simp]
theorem ofLinear_increment [Field R] [CharZero R] (v : α → R) (s t : R) :
    (ofLinear v).increment s t =
      Word.linearSignature ((t - s) • v) :=
  rfl

/-- The signature lift of a linear path is weakly geometric. -/
theorem ofLinear_isWeaklyGeometric [Field R] [CharZero R] (v : α → R) :
    (ofLinear v).IsWeaklyGeometric :=
  fun _ _ => Word.isGroupLike_linearSignature _

/-- The linear path clamped to the window `[0, T₀]`: constant before `0`,
linear on `[0, T₀]`, constant after. Unlike the unclamped lift it carries
**global** level-2 bounds. -/
noncomputable def ofLinearClamped {d : ℕ} (v : Fin d → ℝ) (T₀ : ℝ) :
    AlgebraicRoughPath ℝ (Fin d) ℝ :=
  (ofLinear v).comapTime (clampTo T₀)

theorem ofLinearClamped_isWeaklyGeometric {d : ℕ} (v : Fin d → ℝ)
    (T₀ : ℝ) : (ofLinearClamped v T₀).IsWeaklyGeometric :=
  (ofLinear_isWeaklyGeometric v).comapTime _

theorem ofLinearClamped_coeff_single {d : ℕ} (v : Fin d → ℝ) (T₀ s t : ℝ)
    (i : Fin d) :
    (ofLinearClamped v T₀).coeff s t [i] =
      (clampTo T₀ t - clampTo T₀ s) * v i := by
  show Word.linearSignature
    ((clampTo T₀ t - clampTo T₀ s) • v) [i] = _
  rw [Word.linearSignature_singleton, Pi.smul_apply, smul_eq_mul]

theorem ofLinearClamped_coeff_pair {d : ℕ} (v : Fin d → ℝ) (T₀ s t : ℝ)
    (i j : Fin d) :
    (ofLinearClamped v T₀).coeff s t [i, j] =
      ((clampTo T₀ t - clampTo T₀ s) * v i) *
        ((clampTo T₀ t - clampTo T₀ s) * v j) / 2 := by
  show Word.linearSignature
    ((clampTo T₀ t - clampTo T₀ s) • v) [i, j] = _
  rw [Word.linearSignature_pair, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul]

private theorem clamp_diff_facts {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {s t : ℝ}
    (hst : s ≤ t) :
    0 ≤ clampTo T₀ t - clampTo T₀ s ∧
      clampTo T₀ t - clampTo T₀ s ≤ t - s ∧
      clampTo T₀ t - clampTo T₀ s ≤ T₀ := by
  refine ⟨sub_nonneg.2 (clampTo_mono T₀ hst), ?_, ?_⟩
  · have := clampTo_le_add T₀ hst; linarith
  · have h1 := clampTo_le T₀ t
    have h2 := clampTo_nonneg hT₀ s
    linarith

/-- **The clamped linear path is a global level-2 rough path** with
`α = 1/2` against the linear control `ω = (M²T₀)·(t-s)`: the first
end-to-end analytic instance of the theory. -/
theorem ofLinearClamped_isLevel2 {d : ℕ} (v : Fin d → ℝ) {M T₀ : ℝ}
    (hT₀ : 0 ≤ T₀) (hM : 0 ≤ M) (hv : ∀ i, |v i| ≤ M) :
    IsLevel2RoughPath (ofLinearClamped v T₀)
      (Control.ofReal (ENNReal.ofReal (M ^ 2 * T₀))) (1 / 2) := by
  have hMT : (0 : ℝ) ≤ M ^ 2 * T₀ := by positivity
  have key : ∀ ⦃s t : ℝ⦄, s ≤ t → ∀ i j : Fin d,
      |((clampTo T₀ t - clampTo T₀ s) * v i) *
        ((clampTo T₀ t - clampTo T₀ s) * v j)| ≤
        M ^ 2 * T₀ * (t - s) := by
    intro s t hst i j
    obtain ⟨hc0, hc1, hcT⟩ := clamp_diff_facts hT₀ hst
    have h3 : (clampTo T₀ t - clampTo T₀ s) * (clampTo T₀ t - clampTo T₀ s)
        ≤ (t - s) * T₀ := mul_le_mul hc1 hcT hc0 (by linarith)
    have h4 : |v i| * |v j| ≤ M * M :=
      mul_le_mul (hv i) (hv j) (abs_nonneg _) hM
    calc |((clampTo T₀ t - clampTo T₀ s) * v i) *
          ((clampTo T₀ t - clampTo T₀ s) * v j)|
        = ((clampTo T₀ t - clampTo T₀ s) * (clampTo T₀ t - clampTo T₀ s)) *
            (|v i| * |v j|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc0]; ring
      _ ≤ ((t - s) * T₀) * (M * M) :=
          mul_le_mul h3 h4 (by positivity) (mul_nonneg (by linarith) hT₀)
      _ = M ^ 2 * T₀ * (t - s) := by ring
  refine ⟨by norm_num, le_rfl, ?_, ?_⟩
  · intro s t hst i
    have h5 : ((clampTo T₀ t - clampTo T₀ s) * v i) ^ 2 ≤
        M ^ 2 * T₀ * (t - s) := by
      rw [pow_two]
      exact (le_abs_self _).trans (key hst i i)
    rw [ofLinearClamped_coeff_single, Control.ofReal_apply,
      ← ENNReal.ofReal_mul hMT,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hMT (by linarith))
        (by norm_num), ← ofReal_norm, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.sqrt_eq_rpow]
    calc |(clampTo T₀ t - clampTo T₀ s) * v i|
        = Real.sqrt (((clampTo T₀ t - clampTo T₀ s) * v i) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (M ^ 2 * T₀ * (t - s)) := Real.sqrt_le_sqrt h5
  · intro s t hst i j
    rw [ofLinearClamped_coeff_pair, Control.ofReal_apply,
      ← ENNReal.ofReal_mul hMT,
      show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one,
      ← ofReal_norm, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_div, abs_two]
    have h6 := key hst i j
    have habs : (0 : ℝ) ≤ |((clampTo T₀ t - clampTo T₀ s) * v i) *
        ((clampTo T₀ t - clampTo T₀ s) * v j)| := abs_nonneg _
    linarith

/-! ### The bracket path: a non-geometric rough path -/

/-- The coefficient profile of the bracket path: `aᵐ/m!` on words of
length `2m`, zero on odd lengths. -/
noncomputable def bracketCoeff (a : ℝ) (k : ℕ) : ℝ :=
  if 2 ∣ k then a ^ (k / 2) / ((k / 2).factorial : ℝ) else 0

theorem bracketCoeff_even (a : ℝ) (m : ℕ) :
    bracketCoeff a (2 * m) = a ^ m / (m.factorial : ℝ) := by
  rw [bracketCoeff, if_pos ⟨m, rfl⟩,
    show 2 * m / 2 = m from by omega]

theorem bracketCoeff_odd (a : ℝ) {k : ℕ} (h : ¬ 2 ∣ k) :
    bracketCoeff a k = 0 := by
  rw [bracketCoeff, if_neg h]

theorem bracketCoeff_zero_left (k : ℕ) (hk : k ≠ 0) :
    bracketCoeff 0 k = 0 := by
  rw [bracketCoeff]
  split_ifs with h
  · rw [zero_pow (by omega), zero_div]
  · rfl

/-- A `range (2m+1)` sum supported on even indices is a `range (m+1)`
sum over the doubled index. -/
private theorem sum_range_even {M : Type*} [AddCommMonoid M] (m : ℕ)
    (h : ℕ → M) (h0 : ∀ k, ¬ 2 ∣ k → h k = 0) :
    ∑ k ∈ Finset.range (2 * m + 1), h k =
      ∑ j ∈ Finset.range (m + 1), h (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ (fun j => h (2 * j)) (m + 1),
        h0 (2 * m + 1) (by omega), add_zero,
        show 2 * m + 1 + 1 = 2 * (m + 1) from by ring]

/-- Chen's identity for the bracket profile: the binomial law. -/
private theorem bracketCoeff_chen (a b : ℝ) (w : List (Fin 1)) :
    ((Word.splits w).map fun p =>
      bracketCoeff a p.1.length * bracketCoeff b p.2.length).sum =
      bracketCoeff (a + b) w.length := by
  have hterm : ∀ p ∈ Word.splits w,
      bracketCoeff a p.1.length * bracketCoeff b p.2.length =
        bracketCoeff a p.1.length *
          bracketCoeff b (w.length - p.1.length) := by
    intro p hp
    have hlen : p.1.length + p.2.length = w.length := by
      rw [← Word.mem_splits_append hp, List.length_append]
    rw [show w.length - p.1.length = p.2.length from by omega]
  refine Eq.trans (congrArg List.sum (List.map_congr_left hterm)) ?_
  refine Eq.trans (Word.sum_splits_length_fst w fun k =>
    bracketCoeff a k * bracketCoeff b (w.length - k)) ?_
  by_cases hn : 2 ∣ w.length
  · obtain ⟨m, hm⟩ := hn
    rw [hm, bracketCoeff_even]
    have hper : ∀ j ∈ Finset.range (m + 1),
        bracketCoeff a (2 * j) * bracketCoeff b (2 * m - 2 * j) =
          a ^ j * b ^ (m - j) *
            ((m.choose j : ℝ) / (m.factorial : ℝ)) := by
      intro j hj
      have hjm : j ≤ m := by
        have := Finset.mem_range.mp hj; omega
      rw [show 2 * m - 2 * j = 2 * (m - j) from by omega,
        bracketCoeff_even, bracketCoeff_even,
        div_factorial_mul_div_factorial (n := m) (k := j) hjm]
    calc ∑ k ∈ Finset.range (2 * m + 1),
          bracketCoeff a k * bracketCoeff b (2 * m - k)
        = ∑ j ∈ Finset.range (m + 1),
            bracketCoeff a (2 * j) * bracketCoeff b (2 * m - 2 * j) :=
          sum_range_even m _ fun k hk => by
            rw [bracketCoeff_odd a hk, zero_mul]
      _ = ∑ j ∈ Finset.range (m + 1), a ^ j * b ^ (m - j) *
            ((m.choose j : ℝ) / (m.factorial : ℝ)) :=
          Finset.sum_congr rfl hper
      _ = (a + b) ^ m / (m.factorial : ℝ) := sum_pow_div_factorial a b m
  · rw [bracketCoeff_odd _ hn]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkn : k ≤ w.length := by
      have := Finset.mem_range.mp hk; omega
    by_cases h2 : 2 ∣ k
    · rw [bracketCoeff_odd b (k := w.length - k) (by omega), mul_zero]
    · rw [bracketCoeff_odd a h2, zero_mul]

/-- **The bracket path**: the Itô-type lift of a constant path — zero
first level, symmetric second level `X²(s,t) = t-s`. It is the tensor
exponential `exp((t-s)·(e₀⊗e₀))`, so Chen's identity is the binomial law;
the shuffle identity fails at level one (see
`bracketPath_not_isWeaklyGeometric`). -/
noncomputable def bracketPath : AlgebraicRoughPath ℝ (Fin 1) ℝ where
  increment s t w := bracketCoeff (t - s) w.length
  identity t := by
    funext w
    rw [sub_self]
    cases w with
    | nil =>
        show bracketCoeff 0 0 = 1
        rw [show (0 : ℕ) = 2 * 0 from rfl, bracketCoeff_even]
        norm_num
    | cons x w' =>
        show bracketCoeff 0 (x :: w').length = 0
        exact bracketCoeff_zero_left _ (by simp)
  chen s t u := by
    funext w
    refine Eq.trans ?_ (bracketCoeff_chen (t - s) (u - t) w).symm
    rw [show u - s = (t - s) + (u - t) from by ring]
  unitEmpty s t := by
    show bracketCoeff (t - s) 0 = 1
    rw [show (0 : ℕ) = 2 * 0 from rfl, bracketCoeff_even]
    norm_num

@[simp]
theorem bracketPath_coeff (s t : ℝ) (w : List (Fin 1)) :
    bracketPath.coeff s t w = bracketCoeff (t - s) w.length :=
  rfl

/-- **The bracket path is not weakly geometric**: the shuffle identity
fails at the first level, `2·X²₀₀ = 2·(t-s) ≠ 0 = X¹₀·X¹₀`. Together with
`bracketPath` (Chen holds) this exhibits a genuinely non-geometric rough
path, as promised by the non-geometric base of the theory. -/
theorem bracketPath_not_isWeaklyGeometric :
    ¬ bracketPath.IsWeaklyGeometric := by
  intro h
  have h2 := (h 0 1).shuffle [0] [0]
  rw [Word.shuffleCoeff] at h2
  simp only [Word.shuffle, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil] at h2
  rw [show (Word.coeff (bracketPath.increment 0 1) [0] : ℝ) =
      bracketCoeff (1 - 0) 1 from rfl] at h2
  rw [show (bracketPath.increment 0 1 [0, 0] : ℝ) =
      bracketCoeff (1 - 0) 2 from rfl] at h2
  rw [bracketCoeff_odd (1 - 0 : ℝ) (k := 1) (by omega),
    show (2 : ℕ) = 2 * 1 from rfl, bracketCoeff_even] at h2
  norm_num [Nat.factorial] at h2

/-- The bracket path is level-2 with `α = 1/2` against `ω = t-s`: a
complete non-geometric instance of the analytic theory. -/
theorem bracketPath_isLevel2 :
    IsLevel2RoughPath bracketPath (Control.ofReal 1) (1 / 2) := by
  refine ⟨by norm_num, le_rfl, ?_, ?_⟩
  · intro s t hst i
    rw [show bracketPath.coeff s t [i] = bracketCoeff (t - s) 1 from rfl,
      bracketCoeff_odd (t - s) (k := 1) (by omega)]
    simp
  · intro s t hst i j
    rw [bracketPath_coeff,
      show ([i, j] : List (Fin 1)).length = 2 * 1 from rfl,
      bracketCoeff_even,
      Control.ofReal_apply, one_mul,
      show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one,
      ← ofReal_norm, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    exact le_of_eq (abs_of_nonneg (by linarith))

end AlgebraicRoughPath

end RoughPaths
