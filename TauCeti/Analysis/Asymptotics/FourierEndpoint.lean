/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.Calculus.IteratedDeriv.Within

/-!
# Endpoint expansions of Fourier integrals

For a function `q` that is smooth up to the endpoints of `[a, b]`, repeated integration by parts
expands the Fourier integral `∫ t in a..b, e^{ixt} q(t)` as `x → +∞` in powers of `i / x`, with
coefficients read off from the derivatives of `q` at the two endpoints (DLMF 2.3.4):

`∫_a^b e^{ixt} q(t) dt ∼ e^{iax} ∑ q^{(s)}(a) (i/x)^{s+1} - e^{ibx} ∑ q^{(s)}(b) (i/x)^{s+1}`.

The coefficients oscillate with `x`, so this is a generalized expansion and is written out as a
family of `O` bounds. The remainder after `n` terms is at most `x⁻ⁿ ∫_a^b |q^{(n)}|` (DLMF 2.3.6).

On a half-line, suppose that each `∫ e^{ixt} q^{(s)}(t) dt` converges at `∞` uniformly for all
sufficiently large `x`. Then the improper integral exists for large `x`, the derivatives of `q`
vanish at infinity, and only the endpoint `a` contributes (DLMF 2.3.5): `e^{-iax}` times the
integral has the expansion `∑ q^{(s)}(a) (i/x)^{s+1}`.

## Main results

* `Asymptotics.intervalIntegral_cexp_smul_eq_sum_add`: the exact formula after `n` integrations
  by parts.
* `Asymptotics.norm_intervalIntegral_cexp_smul_sub_sum_le`: the remainder bound on `[a, b]`.
* `Asymptotics.isBigO_intervalIntegral_cexp_smul_sub_sum`: the expansion on `[a, b]`.
* `Asymptotics.tendsto_zero_of_tendsto_cexp_smul`: a function whose modulations at two distinct
  frequencies both converge at infinity tends to `0`.
* `Asymptotics.tendsto_iteratedDerivWithin_atTop_of_uniform`: under the uniform convergence
  hypothesis, every derivative of `q` tends to `0` at infinity.
* `Asymptotics.hasAsymptoticExpansion_fourier_Ici`,
  `Asymptotics.exists_tendsto_and_hasAsymptoticExpansion_fourier_Ici`: the expansion of the improper
  integral on `[a, ∞)`, and its existence.
* `Asymptotics.norm_sub_sum_le_of_tendsto_intervalIntegral`: the remainder bound on `[a, ∞)`.
* `Asymptotics.exists_forall_norm_intervalIntegral_cexp_smul_le`,
  `Asymptotics.exists_forall_norm_intervalIntegral_cexp_smul_iteratedDerivWithin_le`: decay at
  infinity and integrability of the next derivative give the uniform convergence for `x ≥ 1`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.3(i).
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set intervalIntegral
open scoped ContDiff Interval Topology

namespace Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- One integration by parts in a Fourier integral. -/
theorem intervalIntegral_cexp_smul_eq_add [CompleteSpace E] {g g' : ℝ → E} {a b x : ℝ}
    (hx : x ≠ 0) (hg : ContinuousOn g [[a, b]])
    (hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt g (g' t) t)
    (hg' : IntervalIntegrable g' volume a b) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g t =
      (I / x) • (cexp (((x * a : ℝ) : ℂ) * I) • g a - cexp (((x * b : ℝ) : ℂ) * I) • g b) +
        (I / x) • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g' t := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  have hE : Continuous fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I) := by fun_prop
  have hU (t : ℝ) : HasDerivAt (fun t : ℝ => -(I / x) * cexp (((x * t : ℝ) : ℂ) * I))
      (cexp (((x * t : ℝ) : ℂ) * I)) t := by
    have h₁ : HasDerivAt (fun t : ℝ => ((x * t : ℝ) : ℂ) * I) (x * I) t := by
      simpa using ((hasDerivAt_id t).const_mul x).ofReal_comp.mul_const I
    convert h₁.cexp.const_mul (-(I / x)) using 1
    field_simp
    simp
  have key := integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t : ℝ => -(I / x) * cexp (((x * t : ℝ) : ℂ) * I))
    (u' := fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I)) (v := g) (v' := g')
    (by fun_prop) hg (fun t _ => hU t) hd (hE.intervalIntegrable _ _) hg'
  simp only [mul_smul, intervalIntegral.integral_smul] at key
  linear_combination (norm := module) key

/-- The exact formula after `n` integrations by parts in a Fourier integral, for a tower `g` of
successive derivatives. -/
theorem intervalIntegral_cexp_smul_eq_sum_add [CompleteSpace E] {g : ℕ → ℝ → E} {a b x : ℝ}
    (hx : x ≠ 0) {n : ℕ} (hc : ∀ s ≤ n, ContinuousOn (g s) [[a, b]])
    (hd : ∀ s < n, ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt (g s) (g (s + 1) t) t) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g 0 t =
      ∑ s ∈ Finset.range n, (I / x) ^ (s + 1) •
        (cexp (((x * a : ℝ) : ℂ) * I) • g s a - cexp (((x * b : ℝ) : ℂ) * I) • g s b) +
      (I / x) ^ n • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g n t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih (fun s hs => hc s (by omega)) (fun s hs => hd s (by omega)),
      intervalIntegral_cexp_smul_eq_add hx (hc n (by omega)) (hd n (by omega))
        ((hc (n + 1) le_rfl).intervalIntegrable),
      Finset.sum_range_succ, smul_add, smul_smul, smul_smul, ← pow_succ, add_assoc]

private theorem norm_I_div_pow {x : ℝ} (hx : 0 < x) (n : ℕ) : ‖(I / (x : ℂ)) ^ n‖ = (x ^ n)⁻¹ := by
  simp [norm_pow, abs_of_pos hx]

private theorem norm_cexp_smul (u : ℝ) (v : E) : ‖cexp ((u : ℂ) * I) • v‖ = ‖v‖ := by
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

private theorem norm_intervalIntegral_cexp_smul_le {r : ℝ → E} {x T T' : ℝ} (hT : T ≤ T') :
    ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ∫ t in T..T', ‖r t‖ := by
  simpa only [norm_cexp_smul] using
    norm_integral_le_integral_norm (f := fun t => cexp (((x * t : ℝ) : ℂ) * I) • r t) hT

/-- The formula of `intervalIntegral_cexp_smul_eq_sum_add` for the iterated derivatives of `q`
within a set containing `[a, b]`, of which the points of `(a, b)` are interior. -/
private theorem intervalIntegral_cexp_smul_eq_sum_add_iteratedDerivWithin [CompleteSpace E]
    {q : ℝ → E} {S : Set ℝ} {m : ℕ∞ω} {a b x : ℝ} {n : ℕ} (hS : UniqueDiffOn ℝ S)
    (hq : ContDiffOn ℝ m q S) (hab : a ≤ b) (hsub : Icc a b ⊆ S) (hnhds : ∀ t ∈ Ioo a b, S ∈ 𝓝 t)
    (hx : x ≠ 0) (hn : (n : ℕ∞ω) ≤ m) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t =
      ∑ s ∈ Finset.range n, (I / x) ^ (s + 1) •
        (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q S a -
          cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q S b) +
      (I / x) ^ n • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin n q S t := by
  have h := intervalIntegral_cexp_smul_eq_sum_add (g := fun s => iteratedDerivWithin s q S)
    (a := a) (b := b) hx (n := n)
    (fun s hs => (hq.continuousOn_iteratedDerivWithin
      ((Nat.cast_le.2 hs).trans hn) hS).mono (by rwa [uIcc_of_le hab]))
    (fun s hs t ht => hq.hasDerivAt_iteratedDerivWithin
      ((Nat.cast_lt.2 hs).trans_le hn)
      (hnhds t (by rwa [min_eq_left hab, max_eq_right hab] at ht)))
  simpa only [iteratedDerivWithin_zero] using h

/-- **Remainder bound for the endpoint expansion** (DLMF 2.3.6): for `q` of class `C^n` on
`[a, b]`, the remainder after `n` terms of the expansion of `∫ t in a..b, e^{ixt} q(t)` is at most
`x⁻ⁿ ∫_a^b |q^{(n)}|`. -/
theorem norm_intervalIntegral_cexp_smul_sub_sum_le [CompleteSpace E] {q : ℝ → E} {a b x : ℝ}
    {n : ℕ} (hab : a ≤ b) (hx : 0 < x) (hq : ContDiffOn ℝ n q (Icc a b)) :
    ‖(∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t) -
        ∑ s ∈ Finset.range n, (I / x) ^ (s + 1) •
          (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) a -
            cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) b)‖ ≤
      (x ^ n)⁻¹ * ∫ t in a..b, ‖iteratedDerivWithin n q (Icc a b) t‖ := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  rw [intervalIntegral_cexp_smul_eq_sum_add_iteratedDerivWithin (uniqueDiffOn_Icc hab) hq hab.le
    subset_rfl (fun t ht => Icc_mem_nhds ht.1 ht.2) hx.ne' le_rfl, add_sub_cancel_left, norm_smul,
    norm_I_div_pow hx]
  exact mul_le_mul_of_nonneg_left (norm_intervalIntegral_cexp_smul_le hab.le) (by positivity)

/-- **Endpoint expansion of a Fourier integral** (DLMF 2.3.4): for `q` of class `C^{N+1}` on
`[a, b]`, as `x → +∞`, the remainder after `N` terms of
`e^{iax} ∑ q^{(s)}(a) (i/x)^{s+1} - e^{ibx} ∑ q^{(s)}(b) (i/x)^{s+1}` is `O(x^{-(N+1)})`. -/
theorem isBigO_intervalIntegral_cexp_smul_sub_sum [CompleteSpace E] {q : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) {N : ℕ} (hq : ContDiffOn ℝ (N + 1 : ℕ) q (Icc a b)) :
    (fun x : ℝ => (∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t) -
        ∑ s ∈ Finset.range N, (I / x) ^ (s + 1) •
          (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) a -
            cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) b))
      =O[atTop] fun x : ℝ => (x ^ (N + 1))⁻¹ := by
  refine IsBigO.of_bound (‖iteratedDerivWithin N q (Icc a b) a‖ +
    ‖iteratedDerivWithin N q (Icc a b) b‖ +
    ∫ t in a..b, ‖iteratedDerivWithin (N + 1) q (Icc a b) t‖) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hpos : 0 < (x ^ (N + 1))⁻¹ := by positivity
  have h := norm_intervalIntegral_cexp_smul_sub_sum_le (n := N + 1) hab hx hq
  rw [Finset.sum_range_succ, ← sub_sub] at h
  have hterm : ‖(I / (x : ℂ)) ^ (N + 1) •
      (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin N q (Icc a b) a -
        cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin N q (Icc a b) b)‖ ≤
      (x ^ (N + 1))⁻¹ * (‖iteratedDerivWithin N q (Icc a b) a‖ +
        ‖iteratedDerivWithin N q (Icc a b) b‖) := by
    rw [norm_smul, norm_I_div_pow hx]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans_eq ?_) hpos.le
    rw [norm_cexp_smul, norm_cexp_smul]
  rw [Real.norm_of_nonneg hpos.le]
  calc _ ≤ _ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add h hterm
    _ = _ := by ring

/-- A function whose modulations by `e^{ix₁T}` and `e^{ix₂T}`, at two distinct frequencies, both
converge as `T → ∞` tends to `0`. -/
theorem tendsto_zero_of_tendsto_cexp_smul {f : ℝ → E} {x₁ x₂ : ℝ} {L₁ L₂ : E} (hx : x₁ ≠ x₂)
    (h₁ : Tendsto (fun T : ℝ => cexp (((x₁ * T : ℝ) : ℂ) * I) • f T) atTop (𝓝 L₁))
    (h₂ : Tendsto (fun T : ℝ => cexp (((x₂ * T : ℝ) : ℂ) * I) • f T) atTop (𝓝 L₂)) :
    Tendsto f atTop (𝓝 0) := by
  -- With `δ = x₂ - x₁` and `τ = π / δ`, the shift by `τ` flips the sign of `e^{iδT}`, so
  -- `B (T + τ) + B T = e^{iδT} • (A T - A (T + τ))` for the two modulations `A` and `B`.
  have hδ : x₂ - x₁ ≠ 0 := sub_ne_zero.2 hx.symm
  set τ : ℝ := Real.pi / (x₂ - x₁) with hτ
  have hsplit (u : ℝ) : cexp (((x₂ * u : ℝ) : ℂ) * I) =
      cexp ((((x₂ - x₁) * u : ℝ) : ℂ) * I) * cexp (((x₁ * u : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hflip (T : ℝ) : cexp (((((x₂ - x₁) * (T + τ) : ℝ) : ℂ)) * I) =
      -cexp ((((x₂ - x₁) * T : ℝ) : ℂ) * I) := by
    have : (((x₂ - x₁) * (T + τ) : ℝ) : ℂ) * I =
        (((x₂ - x₁) * T : ℝ) : ℂ) * I + Real.pi * I := by
      rw [hτ, mul_add, mul_div_cancel₀ _ hδ]
      push_cast
      ring
    rw [this, Complex.exp_add, exp_pi_mul_I, mul_neg_one]
  have hshift : Tendsto (fun T : ℝ => T + τ) atTop atTop := tendsto_atTop_add_const_right _ _
    tendsto_id
  have hdiff : Tendsto (fun T : ℝ => cexp (((x₁ * T : ℝ) : ℂ) * I) • f T -
      cexp (((x₁ * (T + τ) : ℝ) : ℂ) * I) • f (T + τ)) atTop (𝓝 0) := by
    simpa using h₁.sub (h₁.comp hshift)
  have hsum : Tendsto (fun T : ℝ => cexp (((x₂ * (T + τ) : ℝ) : ℂ) * I) • f (T + τ) +
      cexp (((x₂ * T : ℝ) : ℂ) * I) • f T) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hdiff ⊢
    refine hdiff.congr fun T => ?_
    rw [hsplit (T + τ), hsplit T, hflip T, ← norm_cexp_smul ((x₂ - x₁) * T)
      (cexp (((x₁ * T : ℝ) : ℂ) * I) • f T - cexp (((x₁ * (T + τ) : ℝ) : ℂ) * I) • f (T + τ))]
    congr 1
    simp only [smul_sub, neg_mul, neg_smul, mul_smul]
    abel
  have hL₂ : L₂ + L₂ = 0 := tendsto_nhds_unique ((h₂.comp hshift).add h₂) hsum
  have hL₂' : L₂ = 0 := by
    have h2 : (2 : ℂ) • L₂ = 0 := by rw [two_smul, hL₂]
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  rw [hL₂', tendsto_zero_iff_norm_tendsto_zero] at h₂
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact h₂.congr fun T => norm_cexp_smul _ _

private theorem intervalIntegrable_cexp_smul {r : ℝ → E} {a T x : ℝ}
    (hr : ContinuousOn r (Ici a)) (hT : a ≤ T) :
    IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) • r t) volume a T := by
  refine ContinuousOn.intervalIntegrable (ContinuousOn.smul (by fun_prop) (hr.mono ?_))
  rw [uIcc_of_le hT]
  exact Icc_subset_Ici_self

/-- Under the uniform Cauchy condition at a frequency `x`, the improper integral exists. -/
private theorem exists_tendsto_intervalIntegral_cexp_smul [CompleteSpace E] {r : ℝ → E} {a x₀ x : ℝ}
    (hr : ContinuousOn r (Ici a))
    (hu : ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ε) (hx : x₀ ≤ x) :
    ∃ L, Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • r t) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
  obtain ⟨c, hc⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨max c a, fun T hT => ?_⟩
  have hT' : max c a ≤ T := hT
  rw [dist_eq_norm, integral_interval_sub_left
    (intervalIntegrable_cexp_smul hr ((le_max_right c a).trans hT'))
    (intervalIntegrable_cexp_smul hr (le_max_right c a))]
  exact (hc x hx _ (le_max_left c a) T hT').trans_lt (half_lt_self hε)

/-- If `r` has a derivative `r'` on `(a, ∞)` and the Fourier integrals of `r` and `r'` at a nonzero
frequency `x` both converge, then `e^{ixT} r(T)` converges as `T → ∞`. -/
private theorem exists_tendsto_cexp_smul_of_tendsto [CompleteSpace E] {r r' : ℝ → E} {a x : ℝ}
    {L L' : E} (hx : x ≠ 0) (hr : ContinuousOn r (Ici a)) (hr' : ContinuousOn r' (Ici a))
    (hd : ∀ t ∈ Ioi a, HasDerivAt r (r' t) t)
    (hL : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • r t) atTop (𝓝 L))
    (hL' : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • r' t) atTop (𝓝 L')) :
    ∃ M, Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) • r T) atTop (𝓝 M) := by
  have hc : I / (x : ℂ) ≠ 0 := div_ne_zero I_ne_zero (ofReal_ne_zero.2 hx)
  refine ⟨cexp (((x * a : ℝ) : ℂ) * I) • r a + L' - (I / (x : ℂ))⁻¹ • L,
    (((tendsto_const_nhds.add hL').sub (hL.const_smul _))).congr' ?_⟩
  filter_upwards [eventually_ge_atTop a] with T hT
  have h := intervalIntegral_cexp_smul_eq_add (g := r) (g' := r') (a := a) (b := T) hx
    (hr.mono (by rw [uIcc_of_le hT]; exact Icc_subset_Ici_self))
    (fun t ht => hd t (by
      rw [min_eq_left hT] at ht
      exact ht.1))
    (hr'.mono (by rw [uIcc_of_le hT]; exact Icc_subset_Ici_self)).intervalIntegrable
  rw [h, smul_add, smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul, inv_mul_cancel₀ hc,
    one_smul]
  abel

/-- If each of `∫ e^{ixt} q^{(s)}(t) dt` and `∫ e^{ixt} q^{(s+1)}(t) dt` converges at `∞` uniformly
for all sufficiently large `x`, then `q^{(s)}(t) → 0` as `t → ∞`. -/
theorem tendsto_iteratedDerivWithin_atTop_of_uniform [CompleteSpace E] {q : ℝ → E} {a : ℝ}
    {s : ℕ} (hq : ContDiffOn ℝ (s + 1 : ℕ) q (Ici a))
    (hs : ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (hs' : ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin (s + 1) q (Ici a) t‖ ≤ ε) :
    Tendsto (iteratedDerivWithin s q (Ici a)) atTop (𝓝 0) := by
  obtain ⟨x₀, hx₀⟩ := hs
  obtain ⟨x₀', hx₀'⟩ := hs'
  have hU : UniqueDiffOn ℝ (Ici a) := uniqueDiffOn_Ici a
  have hcont {k : ℕ} (hk : k ≤ s + 1) : ContinuousOn (iteratedDerivWithin k q (Ici a)) (Ici a) :=
    hq.continuousOn_iteratedDerivWithin (by exact_mod_cast hk) hU
  have hder : ∀ t ∈ Ioi a, HasDerivAt (iteratedDerivWithin s q (Ici a))
      (iteratedDerivWithin (s + 1) q (Ici a) t) t := fun t ht =>
    hq.hasDerivAt_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self s) (Ici_mem_nhds ht)
  have hmod {x : ℝ} (hx : max (max x₀ x₀') 1 ≤ x) :
      ∃ M, Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) •
        iteratedDerivWithin s q (Ici a) T) atTop (𝓝 M) := by
    have h1 : x₀ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
    have h2 : x₀' ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
    have h3 : (1 : ℝ) ≤ x := (le_max_right _ _).trans hx
    obtain ⟨L, hL⟩ := exists_tendsto_intervalIntegral_cexp_smul (hcont s.le_succ) hx₀ h1
    obtain ⟨L', hL'⟩ := exists_tendsto_intervalIntegral_cexp_smul (hcont le_rfl) hx₀' h2
    exact exists_tendsto_cexp_smul_of_tendsto (by linarith) (hcont s.le_succ) (hcont le_rfl) hder
      hL hL'
  obtain ⟨M₁, hM₁⟩ := hmod (x := max (max x₀ x₀') 1) le_rfl
  obtain ⟨M₂, hM₂⟩ := hmod (x := max (max x₀ x₀') 1 + 1) (by linarith)
  exact tendsto_zero_of_tendsto_cexp_smul (by linarith [show (0 : ℝ) < 1 from one_pos] :
    max (max x₀ x₀') 1 ≠ max (max x₀ x₀') 1 + 1) hM₁ hM₂

/-- Letting `T → ∞` in the formula after `n` integrations by parts, when the first `n` derivatives
of `q` vanish at infinity. -/
private theorem tendsto_pow_smul_intervalIntegral_cexp_smul [CompleteSpace E] {q : ℝ → E}
    {a x : ℝ} {n : ℕ} {F : E} (hq : ContDiffOn ℝ n q (Ici a)) (hx : x ≠ 0)
    (h0 : ∀ s < n, Tendsto (iteratedDerivWithin s q (Ici a)) atTop (𝓝 0))
    (hF : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 F)) :
    Tendsto (fun T : ℝ => (I / (x : ℂ)) ^ n •
        ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin n q (Ici a) t) atTop
      (𝓝 (F - ∑ s ∈ Finset.range n, (I / (x : ℂ)) ^ (s + 1) •
        cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a)) := by
  have hb : ∀ s ∈ Finset.range n, Tendsto (fun T : ℝ => (I / (x : ℂ)) ^ (s + 1) •
      (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a -
        cexp (((x * T : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) T)) atTop
      (𝓝 ((I / (x : ℂ)) ^ (s + 1) •
        cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a)) := fun s hs => by
    have hz : Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) •
        iteratedDerivWithin s q (Ici a) T) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simpa only [norm_cexp_smul, norm_zero] using (h0 s (Finset.mem_range.1 hs)).norm
    simpa using (tendsto_const_nhds.sub hz).const_smul ((I / (x : ℂ)) ^ (s + 1))
  refine (hF.sub (tendsto_finsetSum _ hb)).congr' ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  rw [intervalIntegral_cexp_smul_eq_sum_add_iteratedDerivWithin (uniqueDiffOn_Ici a) hq hT
    Icc_subset_Ici_self (fun t ht => Ici_mem_nhds ht.1) hx le_rfl, add_sub_cancel_left]

/-- **Remainder bound on a half-line** (DLMF 2.3.6, `b = ∞`): if the Fourier integrals of the
derivatives of `q` up to order `n` converge at `∞` uniformly for large `x`, `F` is the improper
integral at `x > 0` and `q^{(n)}` is integrable, then the remainder after `n` terms is at most
`x⁻ⁿ ∫_a^∞ |q^{(n)}|`. -/
theorem norm_sub_sum_le_of_tendsto_intervalIntegral [CompleteSpace E] {q : ℝ → E} {a x : ℝ}
    {n : ℕ} {F : E} (hq : ContDiffOn ℝ n q (Ici a))
    (hunif : ∀ s ≤ n, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (hx : 0 < x)
    (hF : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 F))
    (hn : IntegrableOn (iteratedDerivWithin n q (Ici a)) (Ioi a)) :
    ‖F - ∑ s ∈ Finset.range n, (I / (x : ℂ)) ^ (s + 1) •
        cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a‖ ≤
      (x ^ n)⁻¹ * ∫ t in Ioi a, ‖iteratedDerivWithin n q (Ici a) t‖ := by
  have hlim := tendsto_pow_smul_intervalIntegral_cexp_smul hq hx.ne'
    (fun s hs => tendsto_iteratedDerivWithin_atTop_of_uniform
      (hq.of_le (by exact_mod_cast hs)) (hunif s hs.le) (hunif _ hs)) hF
  refine le_of_tendsto hlim.norm ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  rw [norm_smul, norm_I_div_pow hx]
  refine mul_le_mul_of_nonneg_left ((norm_intervalIntegral_cexp_smul_le hT).trans ?_)
    (by positivity)
  rw [intervalIntegral.integral_of_le hT]
  exact setIntegral_mono_set hn.norm (ae_of_all _ fun _ => norm_nonneg _)
    (ae_of_all _ fun _ ht => Ioc_subset_Ioi_self ht)

/-- The powers `(i / x) ^ (s + 1)` form an asymptotic scale as `x → +∞`. -/
theorem isAsymptoticScale_I_div_pow_succ :
    IsAsymptoticScale atTop (fun s (x : ℝ) => (I / (x : ℂ)) ^ (s + 1)) := by
  have hw : Tendsto (fun x : ℝ => I / (x : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_inv_atTop_zero (𝕜 := ℝ)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [abs_of_pos hx]
  exact .of_isLittleO fun n => (isAsymptoticScale_pow hw).isLittleO (n + 1)

/-- Under the uniform convergence hypothesis, the remainder after `N` terms of the improper integral
is at most a constant times `x⁻ᴺ`, for all large `x`. -/
private theorem exists_norm_sub_sum_le_of_uniform [CompleteSpace E] {q : ℝ → E} {a : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a))
    (hunif : ∀ s : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (N : ℕ) :
    ∃ C x₀ : ℝ, ∀ x ≥ x₀, 0 < x → ∀ F : E,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 F) →
      ‖F - ∑ s ∈ Finset.range N, (I / (x : ℂ)) ^ (s + 1) •
        cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a‖ ≤ (x ^ N)⁻¹ * C := by
  obtain ⟨x₀, hx₀⟩ := hunif N
  obtain ⟨c, hc⟩ := hx₀ 1 one_pos
  have hac' : a ≤ max c a := le_max_right _ _
  have hcont : ContinuousOn (iteratedDerivWithin N q (Ici a)) (Ici a) :=
    hq.continuousOn_iteratedDerivWithin (by exact_mod_cast le_top) (uniqueDiffOn_Ici a)
  refine ⟨(∫ t in a..max c a, ‖iteratedDerivWithin N q (Ici a) t‖) + 1, x₀,
    fun x hxx₀ hx F hF => le_of_tendsto (tendsto_pow_smul_intervalIntegral_cexp_smul
      (hq.of_le (by exact_mod_cast le_top)) hx.ne' (fun s _ =>
        tendsto_iteratedDerivWithin_atTop_of_uniform (hq.of_le (by exact_mod_cast le_top))
          (hunif s) (hunif (s + 1))) hF).norm ?_⟩
  filter_upwards [eventually_ge_atTop (max c a)] with T hT
  rw [norm_smul, norm_I_div_pow hx,
    ← integral_add_adjacent_intervals (b := max c a)
      (intervalIntegrable_cexp_smul hcont hac')
      ((intervalIntegrable_cexp_smul hcont hac').symm.trans
        (intervalIntegrable_cexp_smul hcont (hac'.trans hT)))]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add
    (norm_intervalIntegral_cexp_smul_le hac') (hc x hxx₀ _ (le_max_left _ _) T hT)))
    (by positivity)

/-- **Endpoint expansion on a half-line** (DLMF 2.3.5): if each `∫ e^{ixt} q^{(s)}(t) dt` converges
at `∞` uniformly for all sufficiently large `x` and `F x` is the improper integral for large `x`,
then `e^{-iax} F(x) ∼ ∑ q^{(s)}(a) (i/x)^{s+1}` as `x → +∞`. -/
theorem hasAsymptoticExpansion_fourier_Ici [CompleteSpace E] {q : ℝ → E} {a : ℝ} {F : ℝ → E}
    (hq : ContDiffOn ℝ ∞ q (Ici a))
    (hunif : ∀ s : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (hF : ∀ᶠ x : ℝ in atTop,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 (F x))) :
    HasAsymptoticExpansion atTop (fun s (x : ℝ) => (I / (x : ℂ)) ^ (s + 1))
      (fun s => iteratedDerivWithin s q (Ici a) a)
      (fun x => cexp (-(((x * a : ℝ) : ℂ) * I)) • F x) := by
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  obtain ⟨C, x₀, hC⟩ := exists_norm_sub_sum_le_of_uniform hq hunif (N + 1)
  refine IsBigO.of_bound (C + ‖iteratedDerivWithin N q (Ici a) a‖) ?_
  filter_upwards [hF, eventually_gt_atTop 0, eventually_ge_atTop x₀] with x hFx hx hxx₀
  have hee (v : E) : cexp (-(((x * a : ℝ) : ℂ) * I)) • cexp (((x * a : ℝ) : ℂ) * I) • v = v := by
    rw [smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  have hrew : cexp (-(((x * a : ℝ) : ℂ) * I)) • F x -
      ∑ s ∈ Finset.range N, (I / (x : ℂ)) ^ (s + 1) • iteratedDerivWithin s q (Ici a) a =
      cexp (-(((x * a : ℝ) : ℂ) * I)) • (F x - ∑ s ∈ Finset.range (N + 1),
        (I / (x : ℂ)) ^ (s + 1) • cexp (((x * a : ℝ) : ℂ) * I) •
          iteratedDerivWithin s q (Ici a) a) +
        (I / (x : ℂ)) ^ (N + 1) • iteratedDerivWithin N q (Ici a) a := by
    rw [smul_sub, Finset.sum_range_succ, smul_add, Finset.smul_sum]
    simp only [smul_comm (cexp (-(((x * a : ℝ) : ℂ) * I))) ((I / (x : ℂ)) ^ _), hee]
    abel
  rw [hrew, norm_I_div_pow hx, add_mul, mul_comm C]
  refine (norm_add_le _ _).trans (add_le_add ?_ (by rw [norm_smul, norm_I_div_pow hx, mul_comm]))
  rw [← neg_mul, ← ofReal_neg, norm_cexp_smul]
  exact hC x hxx₀ hx _ hFx

/-- Existence of the improper integral and its endpoint expansion on a half-line (DLMF 2.3.5). -/
theorem exists_tendsto_and_hasAsymptoticExpansion_fourier_Ici [CompleteSpace E] {q : ℝ → E} {a : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a))
    (hunif : ∀ s : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε) :
    ∃ F : ℝ → E,
      (∀ᶠ x : ℝ in atTop,
        Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 (F x))) ∧
      HasAsymptoticExpansion atTop (fun s (x : ℝ) => (I / (x : ℂ)) ^ (s + 1))
        (fun s => iteratedDerivWithin s q (Ici a) a)
        (fun x => cexp (-(((x * a : ℝ) : ℂ) * I)) • F x) := by
  obtain ⟨x₀, hx₀⟩ := hunif 0
  simp only [iteratedDerivWithin_zero] at hx₀
  have hF : ∀ᶠ x : ℝ in atTop,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop
        (𝓝 (limUnder atTop fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t)) := by
    filter_upwards [eventually_ge_atTop x₀] with x hx
    exact tendsto_nhds_limUnder (exists_tendsto_intervalIntegral_cexp_smul
      (hq.continuousOn.mono subset_rfl) hx₀ hx)
  exact ⟨_, hF, hasAsymptoticExpansion_fourier_Ici hq hunif hF⟩

/-- If `r → 0` at infinity and `r′` is integrable on `(a, ∞)`, then `∫ e^{ixt} r(t) dt` converges at
`∞` uniformly for `x ≥ 1`. -/
theorem exists_forall_norm_intervalIntegral_cexp_smul_le [CompleteSpace E] {r r' : ℝ → E} {a ε : ℝ}
    (hr : ContinuousOn r (Ici a)) (hd : ∀ t ∈ Ioi a, HasDerivAt r (r' t) t)
    (h0 : Tendsto r atTop (𝓝 0)) (hi : IntegrableOn r' (Ioi a)) (hε : 0 < ε) :
    ∃ c : ℝ, ∀ x ≥ (1 : ℝ), ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ε := by
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.1 ((tendsto_zero_iff_norm_tendsto_zero.1 h0).eventually
    (ge_mem_nhds hε3))
  have hG := intervalIntegral_tendsto_integral_Ioi a hi.norm tendsto_id
  obtain ⟨c₂, hc₂⟩ := Metric.cauchySeq_iff.1 hG.cauchySeq _ hε3
  refine ⟨max (max c₁ c₂) (a + 1), fun x hx T hT T' hT' => ?_⟩
  have hTc₁ : c₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hTc₂ : c₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hTa : a < T := by linarith [(le_max_right (max c₁ c₂) (a + 1)).trans hT]
  have hsub : Ioc T T' ⊆ Ioi a := fun t ht => hTa.trans ht.1
  have hrint : IntervalIntegrable r' volume T T' :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT').2 (hi.mono_set hsub)
  have hstep := intervalIntegral_cexp_smul_eq_add (g := r) (g' := r') (a := T) (b := T')
    (by linarith : x ≠ 0)
    (hr.mono (by
      rw [uIcc_of_le hT']
      exact fun t ht => hTa.le.trans ht.1))
    (fun t ht => hd t (by
      rw [min_eq_left hT'] at ht
      exact hTa.trans ht.1)) hrint
  have hxpos : 0 < x := by linarith
  have hcoef : ‖I / (x : ℂ)‖ ≤ 1 := by
    simpa [abs_of_pos hxpos] using inv_le_one_of_one_le₀ hx
  have htail : ∫ t in T..T', ‖r' t‖ ≤ ε / 3 := by
    have hint (u : ℝ) (hu : a ≤ u) : IntervalIntegrable (fun t => ‖r' t‖) volume a u :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).2
        (IntegrableOn.mono_set hi.norm Ioc_subset_Ioi_self)
    have h := hc₂ T' (hTc₂.trans hT') T hTc₂
    simp only [id_eq] at h
    rw [Real.dist_eq, integral_interval_sub_left (hint _ (hTa.le.trans hT')) (hint _ hTa.le)] at h
    exact (le_abs_self _).trans h.le
  rw [hstep]
  calc _ ≤ ‖(I / (x : ℂ)) • (cexp (((x * T : ℝ) : ℂ) * I) • r T -
          cexp (((x * T' : ℝ) : ℂ) * I) • r T')‖ +
        ‖(I / (x : ℂ)) • ∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r' t‖ := norm_add_le _ _
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := by
      refine add_le_add ?_ ?_
      · rw [norm_smul]
        refine (mul_le_of_le_one_left (norm_nonneg _) hcoef).trans ((norm_sub_le _ _).trans ?_)
        rw [norm_cexp_smul, norm_cexp_smul]
        exact add_le_add (hc₁ T hTc₁) (hc₁ T' (hTc₁.trans hT'))
      · rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) hcoef).trans
          ((norm_intervalIntegral_cexp_smul_le hT').trans htail)
    _ = ε := by ring

/-- If `q^{(s)}(t) → 0` as `t → ∞` and `q^{(s+1)}` is integrable on `(a, ∞)`, then
`∫ e^{ixt} q^{(s)}(t) dt` converges at `∞` uniformly for `x ≥ 1`. Holding for every `s`, this is the
hypothesis of `hasAsymptoticExpansion_fourier_Ici`. -/
theorem exists_forall_norm_intervalIntegral_cexp_smul_iteratedDerivWithin_le [CompleteSpace E]
    {q : ℝ → E} {a : ℝ} {s : ℕ} (hq : ContDiffOn ℝ (s + 1 : ℕ) q (Ici a))
    (h0 : Tendsto (iteratedDerivWithin s q (Ici a)) atTop (𝓝 0))
    (hi : IntegrableOn (iteratedDerivWithin (s + 1) q (Ici a)) (Ioi a)) :
    ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε :=
  ⟨1, fun _ hε => exists_forall_norm_intervalIntegral_cexp_smul_le
    (hq.continuousOn_iteratedDerivWithin (by exact_mod_cast s.le_succ) (uniqueDiffOn_Ici a))
    (fun _ ht => hq.hasDerivAt_iteratedDerivWithin (by exact_mod_cast s.lt_succ_self)
      (Ici_mem_nhds ht)) h0 hi hε⟩

end Asymptotics
