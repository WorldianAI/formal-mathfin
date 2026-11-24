/-
Copyright (c) 2026 WorldianAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WorldianAI
-/
module

public import MathFin.Markets.DeFi.ConstantProductAMM
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The constant-mean (Balancer) AMM: invariant and spot price

`Markets/DeFi/ConstantProductAMM.lean` covers the two-token constant-product pool `x·y = k`.
A Balancer pool holds `n` tokens with reserves `B_i > 0` and weights `w_i > 0`, and trades keep
the **constant-mean** (weighted geometric) invariant

  `V = ∏ᵢ B_i^{w_i}`

fixed. The constant-product pool is the two-token pool with equal weights `1/2`: there
`V² = x·y`.

The **spot price** of token `i` in terms of token `j` is the ratio of the marginal values of the
two reserves on the invariant surface, `p_{ij} = (∂V/∂B_i) / (∂V/∂B_j)`. The partial derivative is
`∂V/∂B_i = w_i·V/B_i`, so

  `p_{ij} = (B_j / w_j) / (B_i / w_i)`,

which is `y / x`, the internal price of the constant-product pool, when `n = 2` and the weights are
equal.

## Main definitions

* `constantMeanInvariant`: the invariant `V = ∏ᵢ B_i^{w_i}`.
* `constantMeanSpotPrice`: the spot price `(B_j / w_j) / (B_i / w_i)`.

## Main results

* `constantMeanInvariant_pos`: `V > 0` for positive reserves.
* `constantMeanInvariant_smul`: `V` is homogeneous of degree one when the weights sum to one.
* `hasDerivAt_constantMeanInvariant_update`: `∂V/∂B_i = w_i·V/B_i`.
* `constantMeanSpotPrice_eq_deriv_ratio`: the spot price is the ratio of the partial derivatives
  of the invariant.
* `constantMeanInvariant_sq_two`, `constantMeanSpotPrice_two`: for `n = 2` and weights `1/2`,
  `V² = x·y` and `p = y / x = internalPrice x y`.

## References

* [F. Martinelli, N. Mushegian, *A non-custodial portfolio manager, liquidity provider, and price
  sensor* (Balancer whitepaper, 2019)][MartinelliMushegian2019]

## Tags

automated market maker, Balancer, constant mean market maker, weighted geometric mean,
spot price, decentralized exchange, MSC 91G80, JEL G23
-/

@[expose] public section

namespace MathFin.DeFi

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **constant-mean invariant** of a Balancer pool with reserves `B` and weights `w`:
the weighted geometric mean `V = ∏ᵢ B_i^{w_i}`, which every trade keeps fixed. -/
noncomputable def constantMeanInvariant (w B : ι → ℝ) : ℝ :=
  ∏ i, B i ^ w i

omit [DecidableEq ι] in
/-- The invariant is positive when all reserves are. -/
lemma constantMeanInvariant_pos {w B : ι → ℝ} (hB : ∀ i, 0 < B i) :
    0 < constantMeanInvariant w B :=
  Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (hB i) _

omit [DecidableEq ι] in
/-- The invariant is homogeneous of degree one when the weights sum to one:
scaling every reserve by `c > 0` scales `V` by `c`. -/
lemma constantMeanInvariant_smul {w B : ι → ℝ} (hB : ∀ i, 0 < B i) (hw : ∑ i, w i = 1)
    {c : ℝ} (hc : 0 < c) :
    constantMeanInvariant w (fun i ↦ c * B i) = c * constantMeanInvariant w B := by
  unfold constantMeanInvariant
  have h : ∀ i, (c * B i) ^ w i = c ^ w i * B i ^ w i := fun i ↦
    Real.mul_rpow hc.le (hB i).le
  simp_rw [h]
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hc, hw, Real.rpow_one]

/-- The **spot price** of token `i` in terms of token `j` in a constant-mean pool:
`p_{ij} = (B_j / w_j) / (B_i / w_i)`. -/
noncomputable def constantMeanSpotPrice (w B : ι → ℝ) (i j : ι) : ℝ :=
  (B j / w j) / (B i / w i)

/-- Splitting the invariant at coordinate `i`: replacing `B_i` by `t` gives
`t^{w_i} · ∏_{k ≠ i} B_k^{w_k}`. -/
lemma constantMeanInvariant_update (w B : ι → ℝ) (i : ι) (t : ℝ) :
    constantMeanInvariant w (Function.update B i t)
      = t ^ w i * ∏ k ∈ univ.erase i, B k ^ w k := by
  unfold constantMeanInvariant
  rw [← Finset.mul_prod_erase univ _ (mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- **The partial derivative of the invariant**: `∂V/∂B_i = w_i·V/B_i`. -/
theorem hasDerivAt_constantMeanInvariant_update {w B : ι → ℝ} (hB : ∀ i, 0 < B i) (i : ι) :
    HasDerivAt (fun t ↦ constantMeanInvariant w (Function.update B i t))
      (w i * constantMeanInvariant w B / B i) (B i) := by
  set C := ∏ k ∈ univ.erase i, B k ^ w k with hC
  have hfun : (fun t ↦ constantMeanInvariant w (Function.update B i t))
      = fun t ↦ t ^ w i * C := funext fun t ↦ constantMeanInvariant_update w B i t
  have hV : constantMeanInvariant w B = B i ^ w i * C := by
    have := constantMeanInvariant_update w B i (B i)
    rwa [Function.update_eq_self] at this
  rw [hfun]
  refine ((Real.hasDerivAt_rpow_const (Or.inl (hB i).ne')).mul_const C).congr_deriv ?_
  rw [hV, Real.rpow_sub_one (hB i).ne']
  field_simp

/-- **The spot price from the constant-mean surface**: the price of token `i` in terms of token `j`
is the ratio `(∂V/∂B_i) / (∂V/∂B_j)` of the partial derivatives of the invariant, and equals
`(B_j / w_j) / (B_i / w_i)`. -/
theorem constantMeanSpotPrice_eq_deriv_ratio {w B : ι → ℝ} (hB : ∀ i, 0 < B i)
    (hw : ∀ i, 0 < w i) (i j : ι) :
    deriv (fun t ↦ constantMeanInvariant w (Function.update B i t)) (B i)
        / deriv (fun t ↦ constantMeanInvariant w (Function.update B j t)) (B j)
      = constantMeanSpotPrice w B i j := by
  rw [(hasDerivAt_constantMeanInvariant_update hB i).deriv,
    (hasDerivAt_constantMeanInvariant_update hB j).deriv, constantMeanSpotPrice]
  have hV := (constantMeanInvariant_pos (w := w) hB).ne'
  have := hB i; have := hB j; have := hw i; have := hw j
  field_simp

/-- **Reduction to the constant-product pool, invariant**: for two tokens with weights `1/2`,
`V² = x·y`. -/
theorem constantMeanInvariant_sq_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    constantMeanInvariant (fun _ : Fin 2 ↦ (1 / 2 : ℝ)) ![x, y] ^ 2 = x * y := by
  unfold constantMeanInvariant
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hx.le, Real.sq_sqrt hy.le]

/-- **Reduction to the constant-product pool, price**: for two tokens with equal weights the spot
price of token `0` in terms of token `1` is `y / x = internalPrice x y`. -/
theorem constantMeanSpotPrice_two {x y : ℝ} (hx : 0 < x) :
    constantMeanSpotPrice (fun _ : Fin 2 ↦ (1 / 2 : ℝ)) ![x, y] 0 1 = internalPrice x y := by
  unfold constantMeanSpotPrice internalPrice
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

end MathFin.DeFi
