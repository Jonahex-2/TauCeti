/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.Calculus.IteratedDeriv.Within
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.Polynomial

/-!
# Endpoint expansions of Fourier integrals

For a smooth function `q`, repeated integration by parts expands the Fourier integral
`∫ e^{ixt} q(t) dt` as `x → +∞` in the values of the derivatives of `q` at the endpoints. On a
compact interval (DLMF 2.3.4),

  `∫_a^b e^{ixt} q(t) dt ∼ e^{iax} ∑ q^{(s)}(a) (i/x)^{s+1} - e^{ibx} ∑ q^{(s)}(b) (i/x)^{s+1}`,

and on a half-line (DLMF 2.3.5), when each `∫ e^{ixt} q^{(s)}(t) dt` converges at infinity
uniformly for all sufficiently large `x`, the improper integral exists for large `x` and

  `∫_a^∞ e^{ixt} q(t) dt ∼ e^{iax} ∑ q^{(s)}(a) (i/x)^{s+1}`.

In both cases the remainder after `n` terms is at most `x⁻ⁿ ∫_a^b |q^{(n)}|` (DLMF 2.3.6). These
expansions are the regular-endpoint contributions in the method of stationary phase.

## Main results

* `Asymptotics.integral_cexp_smul_eq_sum_add`: the exact `n`-fold integration by parts on `[a, b]`.
* `Asymptotics.norm_integral_cexp_smul_sub_sum_le`: the remainder bound on `[a, b]`.
* `Asymptotics.isBigO_integral_cexp_smul_sub_sum`: the two-endpoint expansion on `[a, b]`.
* `Asymptotics.exists_tendsto_integral_cexp_smul_atTop`: existence of the improper integral.
* `Asymptotics.hasAsymptoticExpansion_integral_cexp_smul_atTop`: the expansion on `[a, ∞)`.
* `Asymptotics.norm_limit_integral_cexp_smul_sub_sum_le`: the remainder bound on `[a, ∞)`.
* `Asymptotics.exists_forall_norm_integral_cexp_smul_le`: decay of `r` with integrable `r'` gives
  convergence at infinity uniformly in the frequency, and
  `Asymptotics.exists_forall_norm_integral_cexp_smul_iteratedDerivWithin_le` applies this to the
  derivatives of `q`.
* `Asymptotics.exists_forall_norm_integral_cexp_smul_iteratedDerivWithin_sin_div_le` and
  `Asymptotics.not_integrableOn_iteratedDerivWithin_one_sin_div`: `sin t / t` on `[1, ∞)` has the
  uniform convergence for `x ≥ 2` although its derivative is not integrable, so that condition
  is not necessary.

## References

* NIST *Digital Library of Mathematical Functions*, §2.3(ii), formulas 2.3.4–2.3.6.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 3.
-/

public section

noncomputable section

open Complex Filter Finset MeasureTheory Set intervalIntegral
open scoped ContDiff Interval Topology

namespace Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma hasDerivAt_cexp_mul_I (x t : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I))
      (((x : ℂ) * I) * cexp (((x * t : ℝ) : ℂ) * I)) t := by
  have h : HasDerivAt (fun t : ℝ => ((x * t : ℝ) : ℂ) * I) ((x : ℂ) * I) t := by
    have h₁ : HasDerivAt (fun t : ℝ => x * t) x t := by
      simpa using (hasDerivAt_id t).const_mul x
    simpa using h₁.ofReal_comp.mul_const I
  simpa [mul_comm] using h.cexp

private lemma continuous_cexp_mul_I (x : ℝ) :
    Continuous fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I) := by
  fun_prop

private lemma norm_cexp_mul_I (x t : ℝ) : ‖cexp (((x * t : ℝ) : ℂ) * I)‖ = 1 :=
  norm_exp_ofReal_mul_I _

/-- One integration by parts in a Fourier integral. -/
theorem integral_cexp_smul_eq_of_hasDerivAt [CompleteSpace E] {g g' : ℝ → E} {a b x : ℝ}
    (hx : x ≠ 0) (hg : ContinuousOn g [[a, b]])
    (hd : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt g (g' t) t)
    (hint : IntervalIntegrable g' volume a b) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g t =
      ((I : ℂ) / x) • (cexp (((x * a : ℝ) : ℂ) * I) • g a - cexp (((x * b : ℝ) : ℂ) * I) • g b) +
        ((I : ℂ) / x) • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g' t := by
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (-((I : ℂ) / x)) * cexp (((x * t : ℝ) : ℂ) * I))
      (cexp (((x * t : ℝ) : ℂ) * I)) t := fun t => by
    convert (hasDerivAt_cexp_mul_I x t).const_mul (-((I : ℂ) / x)) using 1
    field_simp
    simp
  have key := integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t : ℝ => (-((I : ℂ) / x)) * cexp (((x * t : ℝ) : ℂ) * I))
    (u' := fun t : ℝ => cexp (((x * t : ℝ) : ℂ) * I)) (v := g) (v' := g') (a := a) (b := b)
    (by have := continuous_cexp_mul_I x; fun_prop) hg (fun t _ => hu t) hd
    ((continuous_cexp_mul_I x).intervalIntegrable _ _) hint
  have hpull : ∫ t in a..b, ((-((I : ℂ) / x)) * cexp (((x * t : ℝ) : ℂ) * I)) • g' t =
      (-((I : ℂ) / x)) • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g' t := by
    simp_rw [mul_smul]
    exact intervalIntegral.integral_smul _ _
  rw [hpull] at key
  have hsolve : ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g t =
      ((-((I : ℂ) / x)) * cexp (((x * b : ℝ) : ℂ) * I)) • g b -
        ((-((I : ℂ) / x)) * cexp (((x * a : ℝ) : ℂ) * I)) • g a -
        (-((I : ℂ) / x)) • ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • g' t := by
    rw [key]
    abel
  rw [hsolve, smul_sub, mul_smul, mul_smul, neg_smul, neg_smul, neg_smul]
  abel

/-- The `n`-fold integration by parts, for derivatives taken within any set with unique
derivatives that contains `[a, b]` and is a neighbourhood of each point of `(a, b)`. -/
private lemma integral_cexp_smul_eq_sum_add_aux [CompleteSpace E] {q : ℝ → E} {S : Set ℝ}
    {a b x : ℝ} (hx : x ≠ 0) (hab : a ≤ b) (hS : UniqueDiffOn ℝ S) (hIcc : Icc a b ⊆ S)
    (hIoo : ∀ t ∈ Ioo a b, S ∈ 𝓝 t) (n : ℕ) (hq : ContDiffOn ℝ n q S) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t =
      ∑ s ∈ range n, ((I : ℂ) / x) ^ (s + 1) •
        (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q S a -
          cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q S b) +
      ((I : ℂ) / x) ^ n •
        ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin n q S t := by
  induction n with
  | zero => simp [iteratedDerivWithin_zero]
  | succ n ih =>
    have hq' : ContDiffOn ℝ n q S := hq.of_le (by exact_mod_cast Nat.le_succ n)
    have hcont : ∀ m : ℕ, m ≤ n + 1 → ContinuousOn (iteratedDerivWithin m q S) [[a, b]] := by
      intro m hm
      rw [uIcc_of_le hab]
      exact (hq.continuousOn_iteratedDerivWithin (by exact_mod_cast hm) hS).mono hIcc
    have hstep := integral_cexp_smul_eq_of_hasDerivAt (g := iteratedDerivWithin n q S)
      (g' := iteratedDerivWithin (n + 1) q S) (a := a) (b := b) hx (hcont n (Nat.le_succ n))
      (fun t ht => by
        rw [min_eq_left hab, max_eq_right hab] at ht
        exact hq.hasDerivAt_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n) (hIoo t ht))
      ((hcont (n + 1) le_rfl).intervalIntegrable)
    rw [ih hq', hstep, sum_range_succ, smul_add, smul_smul, smul_smul, ← pow_succ, add_assoc]

/-- **Exact integration by parts** in a Fourier integral on `[a, b]`: the partial sum of the
endpoint expansion plus the remainder `(i/x)ⁿ ∫_a^b e^{ixt} q^{(n)}(t) dt`. -/
theorem integral_cexp_smul_eq_sum_add [CompleteSpace E] {q : ℝ → E} {a b x : ℝ} (hx : x ≠ 0)
    (hab : a ≤ b) (n : ℕ) (hq : ContDiffOn ℝ n q (Icc a b)) :
    ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t =
      ∑ s ∈ range n, ((I : ℂ) / x) ^ (s + 1) •
        (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) a -
          cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) b) +
      ((I : ℂ) / x) ^ n •
        ∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin n q (Icc a b) t := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · exact integral_cexp_smul_eq_sum_add_aux hx hab (uniqueDiffOn_Icc hlt) subset_rfl
      (fun t ht => Icc_mem_nhds ht.1 ht.2) n hq

private lemma norm_integral_cexp_smul_le_integral_norm {r : ℝ → E} {a b : ℝ} (x : ℝ)
    (hab : a ≤ b) :
    ‖∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ∫ t in a..b, ‖r t‖ := by
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans_eq ?_
  simp only [norm_smul, norm_cexp_mul_I, one_mul]

/-- **Remainder bound** for the endpoint expansion on `[a, b]` (DLMF 2.3.6). -/
theorem norm_integral_cexp_smul_sub_sum_le [CompleteSpace E] {q : ℝ → E} {a b x : ℝ} (hx : x ≠ 0)
    (hab : a ≤ b) (n : ℕ) (hq : ContDiffOn ℝ n q (Icc a b)) :
    ‖(∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t) -
        ∑ s ∈ range n, ((I : ℂ) / x) ^ (s + 1) •
          (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) a -
            cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) b)‖ ≤
      (|x| ^ n)⁻¹ * ∫ t in a..b, ‖iteratedDerivWithin n q (Icc a b) t‖ := by
  rw [integral_cexp_smul_eq_sum_add hx hab n hq, add_sub_cancel_left, norm_smul, norm_pow,
    norm_div, norm_I, Complex.norm_real, Real.norm_eq_abs, one_div, inv_pow]
  exact mul_le_mul_of_nonneg_left (norm_integral_cexp_smul_le_integral_norm x hab) (by positivity)

/-- **Endpoint expansion on a compact interval** (DLMF 2.3.4). For `q` of class `C^{N+1}` on
`[a, b]`, the first `N` terms of
`e^{iax} ∑ q^{(s)}(a) (i/x)^{s+1} - e^{ibx} ∑ q^{(s)}(b) (i/x)^{s+1}` approximate
`∫_a^b e^{ixt} q(t) dt` to within `O(x^{-(N+1)})` as `x → +∞`. -/
theorem isBigO_integral_cexp_smul_sub_sum [CompleteSpace E] {q : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (hq : ContDiffOn ℝ (N + 1 : ℕ) q (Icc a b)) :
    (fun x : ℝ => (∫ t in a..b, cexp (((x * t : ℝ) : ℂ) * I) • q t) -
      ∑ s ∈ range N, ((I : ℂ) / x) ^ (s + 1) •
        (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) a -
          cexp (((x * b : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Icc a b) b))
      =O[atTop] fun x : ℝ => ((x : ℂ) ^ (N + 1))⁻¹ := by
  refine IsBigO.of_bound (‖iteratedDerivWithin N q (Icc a b) a‖ +
    ‖iteratedDerivWithin N q (Icc a b) b‖ +
      ∫ t in a..b, ‖iteratedDerivWithin (N + 1) q (Icc a b) t‖) ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hnorm : ‖((I : ℂ) / x) ^ (N + 1)‖ = ‖((x : ℂ) ^ (N + 1))⁻¹‖ := by
    simp [div_eq_inv_mul]
  rw [integral_cexp_smul_eq_sum_add hx.ne' hab (N + 1) hq, sum_range_succ, add_assoc,
    add_sub_cancel_left, ← smul_add, norm_smul, hnorm, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans_eq ?_)
    (norm_integral_cexp_smul_le_integral_norm x hab))
  simp only [norm_smul, norm_cexp_mul_I, one_mul]

/-! ### The half-line -/

private lemma intervalIntegrable_cexp_smul {r : ℝ → E} {a T T' : ℝ} (x : ℝ)
    (hr : ContinuousOn r (Ici a)) (hT : a ≤ T) (hT' : a ≤ T') :
    IntervalIntegrable (fun t => cexp (((x * t : ℝ) : ℂ) * I) • r t) volume T T' := by
  refine ContinuousOn.intervalIntegrable ?_
  refine (continuous_cexp_mul_I x).continuousOn.smul (hr.mono fun t ht => ?_)
  exact le_trans (le_min hT hT') ht.1

/-- If the Fourier integrals of `r` over `[T, T']` become small as `T → ∞`, the improper integral
`lim_{T→∞} ∫_a^T e^{ixt} r(t) dt` exists. -/
theorem exists_tendsto_integral_cexp_smul_atTop [CompleteSpace E] {r : ℝ → E} {a x : ℝ}
    (hr : ContinuousOn r (Ici a))
    (hC : ∀ ε > 0, ∃ c : ℝ, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ε) :
    ∃ L, Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • r t) atTop (𝓝 L) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
  obtain ⟨c, hc⟩ := hC (ε / 2) (half_pos hε)
  refine ⟨max c a, fun T hT => ?_⟩
  have hN : a ≤ max c a := le_max_right _ _
  have hTa : a ≤ T := hN.trans hT
  rw [dist_eq_norm, integral_interval_sub_left (intervalIntegrable_cexp_smul x hr le_rfl hTa)
    (intervalIntegrable_cexp_smul x hr le_rfl hN)]
  exact (hc _ (le_max_left _ _) T hT).trans_lt (half_lt_self hε)

/-- A limit of Fourier integrals is bounded independently of the frequency. -/
private lemma norm_le_of_tendsto_integral {r : ℝ → E} {a x c : ℝ} {L : E}
    (hr : ContinuousOn r (Ici a))
    (hL : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • r t) atTop (𝓝 L))
    (hc : ∀ T ≥ c, ∀ T' ≥ T, ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ 1) :
    ‖L‖ ≤ (∫ t in a..max c a, ‖r t‖) + 1 := by
  have hN : a ≤ max c a := le_max_right _ _
  refine le_of_tendsto hL.norm ?_
  filter_upwards [eventually_ge_atTop (max c a)] with T hT
  rw [← integral_add_adjacent_intervals (intervalIntegrable_cexp_smul x hr le_rfl hN)
    (intervalIntegrable_cexp_smul x hr hN (hN.trans hT))]
  exact (norm_add_le _ _).trans (add_le_add (norm_integral_cexp_smul_le_integral_norm x hN)
    (hc _ (le_max_left _ _) T hT))

/-- If `r` and `r'` have convergent Fourier integrals at frequency `y`, the boundary term
`e^{iyT} r(T)` converges as `T → ∞`. -/
private lemma exists_tendsto_cexp_smul_atTop [CompleteSpace E] {r r' : ℝ → E} {a y : ℝ}
    (hr : ContinuousOn r (Ici a)) (hr' : ContinuousOn r' (Ici a))
    (hd : ∀ t ∈ Ioi a, HasDerivAt r (r' t) t)
    (h0 : ∀ ε > 0, ∃ c : ℝ, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((y * t : ℝ) : ℂ) * I) • r t‖ ≤ ε)
    (h1 : ∀ ε > 0, ∃ c : ℝ, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((y * t : ℝ) : ℂ) * I) • r' t‖ ≤ ε) :
    ∃ L, Tendsto (fun T : ℝ => cexp (((y * T : ℝ) : ℂ) * I) • r T) atTop (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_integral_cexp_smul_atTop (a := a) hr h0
  obtain ⟨L₁, hL₁⟩ := exists_tendsto_integral_cexp_smul_atTop (a := a) hr' h1
  refine ⟨cexp (((y * a : ℝ) : ℂ) * I) • r a + ((y : ℂ) * I) • L₀ + L₁,
    ((tendsto_const_nhds.add (hL₀.const_smul _)).add hL₁).congr' ?_⟩
  filter_upwards [eventually_ge_atTop a] with T hT
  have hsub : [[a, T]] ⊆ Ici a := by
    rw [uIcc_of_le hT]
    exact Icc_subset_Ici_self
  have hibp := integral_deriv_smul_eq_sub_of_hasDeriv_right
    (u := fun t : ℝ => cexp (((y * t : ℝ) : ℂ) * I))
    (u' := fun t : ℝ => ((y : ℂ) * I) * cexp (((y * t : ℝ) : ℂ) * I)) (v := r) (v' := r')
    (a := a) (b := T) (continuous_cexp_mul_I y).continuousOn (hr.mono hsub)
    (fun t _ => (hasDerivAt_cexp_mul_I y t).hasDerivWithinAt)
    (fun t ht => by
      rw [min_eq_left hT, max_eq_right hT] at ht
      exact (hd t ht.1).hasDerivWithinAt)
    ((continuous_const.mul (continuous_cexp_mul_I y)).intervalIntegrable _ _)
    ((hr'.mono hsub).intervalIntegrable)
  have hA : IntervalIntegrable (fun t : ℝ => (((y : ℂ) * I) * cexp (((y * t : ℝ) : ℂ) * I)) • r t)
      volume a T :=
    ((continuous_const.mul (continuous_cexp_mul_I y)).continuousOn.smul
      (hr.mono hsub)).intervalIntegrable
  have hadd := intervalIntegral.integral_add hA (intervalIntegrable_cexp_smul y hr' le_rfl hT)
  have hpull : ∫ t in a..T, (((y : ℂ) * I) * cexp (((y * t : ℝ) : ℂ) * I)) • r t =
      ((y : ℂ) * I) • ∫ t in a..T, cexp (((y * t : ℝ) : ℂ) * I) • r t := by
    simp_rw [mul_smul, intervalIntegral.integral_smul]
  rw [hibp, hpull] at hadd
  rw [add_assoc, ← hadd]
  abel

/-- A vector whose signed sequence `(-1)ᵏ L` converges is zero. -/
private lemma eq_zero_of_tendsto_neg_one_pow_smul {L L' : E}
    (hsign : Tendsto (fun k : ℕ => (-1 : ℂ) ^ k • L) atTop (𝓝 L')) : L = 0 := by
  have heven : L' = L := by
    have h2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
      tendsto_id.const_mul_atTop' (by norm_num)
    refine tendsto_nhds_unique (hsign.comp h2) ?_
    simp [Function.comp_def, pow_mul]
  have hodd : L' = -L := by
    have h2 : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
      tendsto_atTop_mono (fun m => by simp only [id]; omega) tendsto_id
    refine tendsto_nhds_unique (hsign.comp h2) ?_
    simp [Function.comp_def, pow_succ, pow_mul]
  have h : (2 : ℂ) • L = 0 := by
    rw [two_smul]
    nth_rw 1 [← heven]
    rw [hodd]
    simp
  simpa using h

/-- If `r` and `r'` have convergent Fourier integrals at every frequency `y ≥ x₀`, the boundary
term `e^{ixT} r(T)` tends to `0`: it converges at each frequency, and two frequencies differing
by `π` force the limit to equal its negative along the integers. -/
private lemma tendsto_cexp_smul_atTop_nhds_zero [CompleteSpace E] {r r' : ℝ → E} {a x₀ x : ℝ}
    (hr : ContinuousOn r (Ici a)) (hr' : ContinuousOn r' (Ici a))
    (hd : ∀ t ∈ Ioi a, HasDerivAt r (r' t) t)
    (h0 : ∀ y ≥ x₀, ∀ ε > 0, ∃ c : ℝ, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((y * t : ℝ) : ℂ) * I) • r t‖ ≤ ε)
    (h1 : ∀ y ≥ x₀, ∀ ε > 0, ∃ c : ℝ, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((y * t : ℝ) : ℂ) * I) • r' t‖ ≤ ε)
    (hx : x₀ ≤ x) :
    Tendsto (fun T : ℝ => cexp (((x * T : ℝ) : ℂ) * I) • r T) atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := exists_tendsto_cexp_smul_atTop hr hr' hd (h0 x hx) (h1 x hx)
  have hx' : x₀ ≤ x + Real.pi := by linarith [Real.pi_pos]
  obtain ⟨L', hL'⟩ := exists_tendsto_cexp_smul_atTop hr hr' hd (h0 _ hx') (h1 _ hx')
  have hk : ∀ k : ℕ, cexp (((((x + Real.pi) * (k : ℝ)) : ℝ) : ℂ) * I) =
      (-1 : ℂ) ^ k * cexp (((x * (k : ℝ) : ℝ) : ℂ) * I) := fun k => by
    rw [← Complex.exp_pi_mul_I, ← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hLk : Tendsto (fun k : ℕ => cexp (((x * (k : ℝ) : ℝ) : ℂ) * I) • r k) atTop (𝓝 L) :=
    hL.comp tendsto_natCast_atTop_atTop
  have hLk' : Tendsto (fun k : ℕ => (-1 : ℂ) ^ k • (cexp (((x * (k : ℝ) : ℝ) : ℂ) * I) • r k))
      atTop (𝓝 L') := by
    refine (hL'.comp tendsto_natCast_atTop_atTop).congr fun k => ?_
    simp only [Function.comp_apply, hk, mul_smul]
  have hdiff : Tendsto (fun k : ℕ => (-1 : ℂ) ^ k •
      (cexp (((x * (k : ℝ) : ℝ) : ℂ) * I) • r k - L)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k : ℕ => ‖cexp (((x * (k : ℝ) : ℝ) : ℂ) * I) • r k - L‖)
      (fun k => by simp [norm_smul]) ?_
    simpa using (hLk.sub_const L).norm
  have hsign : Tendsto (fun k : ℕ => (-1 : ℂ) ^ k • L) atTop (𝓝 L') := by
    have := hLk'.sub hdiff
    simpa [smul_sub] using this
  simpa [eq_zero_of_tendsto_neg_one_pow_smul hsign] using hL

/-- Passing to the limit `T → ∞` in the exact integration by parts on `[a, T]`. -/
private lemma limit_eq_sum_add [CompleteSpace E] {q : ℝ → E} {a x₀ x : ℝ} {L G : E} (hx0 : x ≠ 0)
    (hq : ContDiffOn ℝ ∞ q (Ici a)) (n : ℕ)
    (hunif : ∀ s ≤ n, ∀ y ≥ x₀, ∀ ε > 0, ∃ c : ℝ, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((y * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (hx : x₀ ≤ x)
    (hL : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 L))
    (hG : Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) •
      iteratedDerivWithin n q (Ici a) t) atTop (𝓝 G)) :
    L = ∑ s ∈ range n, ((I : ℂ) / x) ^ (s + 1) •
        (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a) +
      ((I : ℂ) / x) ^ n • G := by
  have hS : UniqueDiffOn ℝ (Ici a) := uniqueDiffOn_Ici a
  have hcd : ∀ m : ℕ, ContDiffOn ℝ m q (Ici a) := fun m =>
    hq.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
  have hcont : ∀ m : ℕ, ContinuousOn (iteratedDerivWithin m q (Ici a)) (Ici a) := fun m =>
    (hcd m).continuousOn_iteratedDerivWithin le_rfl hS
  have hbdry : ∀ s ∈ range n, Tendsto (fun T : ℝ => ((I : ℂ) / x) ^ (s + 1) •
      (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a -
        cexp (((x * T : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) T)) atTop
      (𝓝 (((I : ℂ) / x) ^ (s + 1) •
        (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a))) := by
    intro s hs
    have hsn : s < n := mem_range.1 hs
    have h0 := tendsto_cexp_smul_atTop_nhds_zero (hcont s) (hcont (s + 1))
      (fun t ht => (hcd (s + 1)).hasDerivAt_iteratedDerivWithin
        (by exact_mod_cast Nat.lt_succ_self s) (Ici_mem_nhds ht))
      (hunif s hsn.le) (hunif (s + 1) hsn) hx
    simpa using (tendsto_const_nhds.sub h0).const_smul (((I : ℂ) / x) ^ (s + 1))
  refine tendsto_nhds_unique hL (((tendsto_finsetSum _ hbdry).add
    (hG.const_smul _)).congr' ?_)
  filter_upwards [eventually_ge_atTop a] with T hT
  exact (integral_cexp_smul_eq_sum_add_aux hx0 hT hS Icc_subset_Ici_self
    (fun t ht => Ici_mem_nhds ht.1) n (hcd n)).symm

/-- Finitely many uniform-convergence thresholds have a common value. -/
private lemma exists_common_threshold {g : ℕ → ℝ → E}
    (hunif : ∀ s : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • g s t‖ ≤ ε) (n : ℕ) :
    ∃ X : ℝ, ∀ s ≤ n, ∀ y ≥ X, ∀ ε > 0, ∃ c : ℝ, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((y * t : ℝ) : ℂ) * I) • g s t‖ ≤ ε := by
  choose x₀ hx₀ using hunif
  refine ⟨(range (n + 1)).sup' nonempty_range_add_one x₀, fun s hs y hy ε hε => ?_⟩
  obtain ⟨c, hc⟩ := hx₀ s ε hε
  exact ⟨c, hc y ((le_sup' x₀ (mem_range.2 (Nat.lt_succ_of_le hs))).trans hy)⟩

/-- Removing the phase `e^{iθ}` from the `N + 1`-term identity leaves the `N`-term remainder of the
normalized expansion in the form `x^{-(N+1)} i^{N+1} (d_N + e^{-iθ} G)`. -/
private lemma cexp_neg_smul_sub_sum_eq {d : ℕ → E} {F G : E} {x : ℝ} {θ : ℂ} (N : ℕ)
    (hid : F = ∑ s ∈ range (N + 1), ((I : ℂ) / x) ^ (s + 1) • (cexp θ • d s) +
      ((I : ℂ) / x) ^ (N + 1) • G) :
    cexp (-θ) • F - ∑ n ∈ range N, ((x : ℂ) ^ (n + 1))⁻¹ • (I : ℂ) ^ (n + 1) • d n =
      ((x : ℂ) ^ (N + 1))⁻¹ • (I : ℂ) ^ (N + 1) • (d N + cexp (-θ) • G) := by
  have he : cexp (-θ) * cexp θ = 1 := by
    rw [← Complex.exp_add]
    simp
  have hterm : ∀ s : ℕ, cexp (-θ) • (((I : ℂ) / x) ^ (s + 1) • (cexp θ • d s)) =
      ((x : ℂ) ^ (s + 1))⁻¹ • (I : ℂ) ^ (s + 1) • d s := by
    intro s
    have hcancel : cexp (-θ) • cexp θ • d s = d s := by
      rw [smul_smul, he, one_smul]
    rw [smul_comm, hcancel, smul_smul, div_pow, div_eq_inv_mul]
  have hGterm : cexp (-θ) • (((I : ℂ) / x) ^ (N + 1) • G) =
      ((x : ℂ) ^ (N + 1))⁻¹ • (I : ℂ) ^ (N + 1) • cexp (-θ) • G := by
    rw [div_pow, div_eq_inv_mul, mul_smul, smul_comm _ ((x : ℂ) ^ (N + 1))⁻¹,
      smul_comm _ ((I : ℂ) ^ (N + 1))]
  rw [hid, smul_add, smul_sum, sum_range_succ, Finset.sum_congr rfl fun s _ => hterm s, hterm N,
    hGterm, smul_add, smul_add]
  abel

/-- **Endpoint expansion on a half-line** (DLMF 2.3.5). If `q` is smooth on `[a, ∞)` and each
`∫ e^{ixt} q^{(s)}(t) dt` converges at infinity uniformly for all sufficiently large `x`, then
the improper integral `F x = lim_{T→∞} ∫_a^T e^{ixt} q(t) dt` satisfies
`e^{-iax} F(x) ∼ ∑ q^{(s)}(a) (i/x)^{s+1}` as `x → +∞`. -/
theorem hasAsymptoticExpansion_integral_cexp_smul_atTop [CompleteSpace E] {q F : ℝ → E} {a : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a))
    (hunif : ∀ s : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (hF : ∀ᶠ x : ℝ in atTop,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 (F x))) :
    HasAsymptoticExpansion atTop (fun s (x : ℝ) => ((x : ℂ) ^ (s + 1))⁻¹)
      (fun s => (I : ℂ) ^ (s + 1) • iteratedDerivWithin s q (Ici a) a)
      fun x => cexp (-(((x * a : ℝ) : ℂ) * I)) • F x := by
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  have hS : UniqueDiffOn ℝ (Ici a) := uniqueDiffOn_Ici a
  have hcont : ContinuousOn (iteratedDerivWithin (N + 1) q (Ici a)) (Ici a) :=
    (hq.of_le (by exact_mod_cast (le_top : ((N + 1 : ℕ) : ℕ∞) ≤ ⊤))
      : ContDiffOn ℝ (N + 1 : ℕ) q (Ici a)).continuousOn_iteratedDerivWithin le_rfl hS
  obtain ⟨X, hX⟩ := exists_common_threshold hunif (N + 1)
  obtain ⟨x₁, hx₁⟩ := hunif (N + 1)
  obtain ⟨c, hc⟩ := hx₁ 1 one_pos
  refine Asymptotics.IsBigO.of_bound
    (‖iteratedDerivWithin N q (Ici a) a‖ +
      ((∫ t in a..max c a, ‖iteratedDerivWithin (N + 1) q (Ici a) t‖) + 1)) ?_
  filter_upwards [hF, eventually_ge_atTop X, eventually_ge_atTop x₁, eventually_gt_atTop 0]
    with x hFx hxX hxx₁ hxpos
  obtain ⟨G, hG⟩ := exists_tendsto_integral_cexp_smul_atTop (a := a) hcont
    (hX (N + 1) le_rfl x hxX)
  have hid := limit_eq_sum_add hxpos.ne' hq (N + 1) hX hxX hFx hG
  have hGle := norm_le_of_tendsto_integral hcont hG (hc x hxx₁)
  have hne : ‖cexp (-(((x * a : ℝ) : ℂ) * I))‖ = 1 := by
    have h : -(((x * a : ℝ) : ℂ) * I) = ((-(x * a) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h]
    exact norm_exp_ofReal_mul_I _
  have hrem := cexp_neg_smul_sub_sum_eq (d := fun s => iteratedDerivWithin s q (Ici a) a) N hid
  rw [hrem, norm_smul, norm_smul, norm_pow, norm_I, one_pow, one_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rwa [norm_smul, hne, one_mul]

/-- **Remainder bound on a half-line** (DLMF 2.3.6): if `q^{(n)}` is integrable on `(a, ∞)`, then
for all large `x` the improper integral differs from the first `n` terms of its endpoint expansion
by at most `x⁻ⁿ ∫_a^∞ |q^{(n)}|`. -/
theorem norm_limit_integral_cexp_smul_sub_sum_le [CompleteSpace E] {q : ℝ → E} {a : ℝ}
    (hq : ContDiffOn ℝ ∞ q (Ici a))
    (hunif : ∀ s : ℕ, ∃ x₀ : ℝ, ∀ ε > 0, ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε)
    (n : ℕ) (hn : IntegrableOn (iteratedDerivWithin n q (Ici a)) (Ioi a)) :
    ∀ᶠ x : ℝ in atTop, ∀ L,
      Tendsto (fun T : ℝ => ∫ t in a..T, cexp (((x * t : ℝ) : ℂ) * I) • q t) atTop (𝓝 L) →
      ‖L - ∑ s ∈ range n, ((I : ℂ) / x) ^ (s + 1) •
          (cexp (((x * a : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) a)‖ ≤
        (x ^ n)⁻¹ * ∫ t in Ioi a, ‖iteratedDerivWithin n q (Ici a) t‖ := by
  have hcont : ContinuousOn (iteratedDerivWithin n q (Ici a)) (Ici a) :=
    (hq.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
      : ContDiffOn ℝ n q (Ici a)).continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici a)
  obtain ⟨X, hX⟩ := exists_common_threshold hunif n
  filter_upwards [eventually_ge_atTop X, eventually_gt_atTop 0] with x hxX hxpos L hL
  obtain ⟨G, hG⟩ := exists_tendsto_integral_cexp_smul_atTop (a := a) hcont (hX n le_rfl x hxX)
  rw [limit_eq_sum_add hxpos.ne' hq n hX hxX hL hG, add_sub_cancel_left, norm_smul, norm_pow,
    norm_div, norm_I, Complex.norm_real, Real.norm_of_nonneg hxpos.le, one_div, inv_pow]
  refine mul_le_mul_of_nonneg_left (le_of_tendsto hG.norm ?_) (by positivity)
  filter_upwards [eventually_ge_atTop a] with T hT
  refine (norm_integral_cexp_smul_le_integral_norm x hT).trans ?_
  rw [intervalIntegral.integral_of_le hT]
  exact setIntegral_mono_set hn.norm (ae_of_all _ fun _ => norm_nonneg _)
    (ae_of_all _ fun _ h => Set.Ioc_subset_Ioi_self h)

/-! ### A sufficient condition for uniform convergence -/

/-- One integration by parts bounds a Fourier integral by the endpoint values of `r` and the
total variation `∫ ‖r'‖`, with a factor `|x|⁻¹`. -/
theorem norm_integral_cexp_smul_le_of_hasDerivAt [CompleteSpace E] {r r' : ℝ → E} {T T' x : ℝ}
    (hx : x ≠ 0) (hTT' : T ≤ T') (hr : ContinuousOn r (Icc T T'))
    (hd : ∀ t ∈ Ioo T T', HasDerivAt r (r' t) t) (hint : IntervalIntegrable r' volume T T') :
    ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤
      |x|⁻¹ * (‖r T‖ + ‖r T'‖ + ∫ t in T..T', ‖r' t‖) := by
  rw [integral_cexp_smul_eq_of_hasDerivAt hx (by rwa [uIcc_of_le hTT'])
    (by rwa [min_eq_left hTT', max_eq_right hTT']) hint, ← smul_add, norm_smul, norm_div, norm_I,
    Complex.norm_real, Real.norm_eq_abs, one_div]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans_eq ?_) (norm_integral_cexp_smul_le_integral_norm x hTT')))
    (by positivity)
  simp only [norm_smul, norm_cexp_mul_I, one_mul]

/-- If `r → 0` at infinity and `r'` is integrable, then `∫ e^{ixt} r(t) dt` converges at infinity
uniformly for `x ≥ x₀`, for every `x₀ > 0`. -/
theorem exists_forall_norm_integral_cexp_smul_le [CompleteSpace E] {r r' : ℝ → E} {a x₀ ε : ℝ}
    (hx₀ : 0 < x₀) (hε : 0 < ε) (hr : ContinuousOn r (Ici a))
    (hd : ∀ t ∈ Ioi a, HasDerivAt r (r' t) t) (hr0 : Tendsto r atTop (𝓝 0))
    (hr' : IntegrableOn r' (Ioi a)) :
    ∃ c : ℝ, ∀ x ≥ x₀, ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖ ≤ ε := by
  set δ : ℝ := ε * x₀ / 3 with hδdef
  have hδ : 0 < δ := by positivity
  have hint : ∀ {u v : ℝ}, a ≤ u → u ≤ v → IntervalIntegrable r' volume u v := fun hu huv =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).2
      (hr'.mono_set fun t ht => lt_of_le_of_lt hu ht.1)
  have htail := intervalIntegral_tendsto_integral_Ioi a hr'.norm tendsto_id
  obtain ⟨c₁, hc₁⟩ := Metric.tendsto_atTop.1 hr0 δ hδ
  obtain ⟨c₂, hc₂⟩ := Metric.tendsto_atTop.1 htail δ hδ
  refine ⟨max (max c₁ c₂) a, fun x hx T hT T' hT' => ?_⟩
  have hTa : a ≤ T := (le_max_right _ _).trans hT
  have hT₁ : c₁ ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
  have hT₂ : c₂ ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
  have hxpos : 0 < x := hx₀.trans_le hx
  have hbound := norm_integral_cexp_smul_le_of_hasDerivAt hxpos.ne' hT'
    (hr.mono fun t ht => hTa.trans ht.1) (fun t ht => hd t (lt_of_le_of_lt hTa ht.1))
    (hint hTa hT')
  have hrT : ∀ u ≥ T, ‖r u‖ < δ := fun u hu => by
    simpa [dist_zero_right] using hc₁ u (hT₁.trans hu)
  have hvar : ∫ t in T..T', ‖r' t‖ ≤ δ := by
    have hnorm : ∀ {u v : ℝ}, a ≤ u → u ≤ v → IntervalIntegrable (fun t => ‖r' t‖) volume u v :=
      fun hu huv => (hint hu huv).norm
    have hsplit : (∫ t in T..T', ‖r' t‖) =
        (∫ t in a..T', ‖r' t‖) - ∫ t in a..T, ‖r' t‖ :=
      (integral_interval_sub_left (hnorm le_rfl (hTa.trans hT')) (hnorm le_rfl hTa)).symm
    have hle : ∫ t in a..T', ‖r' t‖ ≤ ∫ t in Ioi a, ‖r' t‖ := by
      rw [intervalIntegral.integral_of_le (hTa.trans hT')]
      exact setIntegral_mono_set hr'.norm (ae_of_all _ fun _ => norm_nonneg _)
        (ae_of_all _ fun _ h => Set.Ioc_subset_Ioi_self h)
    have hclose := (abs_lt.1 (by simpa [Real.dist_eq] using hc₂ T hT₂)).1
    linarith
  have hsum : ‖r T‖ + ‖r T'‖ + ∫ t in T..T', ‖r' t‖ ≤ 3 * δ := by
    linarith [hrT T le_rfl, hrT T' hT']
  calc ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • r t‖
      ≤ |x|⁻¹ * (‖r T‖ + ‖r T'‖ + ∫ t in T..T', ‖r' t‖) := hbound
    _ ≤ x₀⁻¹ * (3 * δ) := by
        rw [abs_of_pos hxpos]
        exact mul_le_mul (inv_anti₀ hx₀ hx) hsum
          (add_nonneg (by positivity)
            (intervalIntegral.integral_nonneg hT' fun _ _ => norm_nonneg _))
          (by positivity)
    _ = ε := by
        rw [hδdef]
        field_simp

/-- If every `q^{(s)}` tends to `0` at infinity and every `q^{(s+1)}` is integrable on `(a, ∞)`,
then each `∫ e^{ixt} q^{(s)}(t) dt` converges at infinity uniformly for `x ≥ 1`. -/
theorem exists_forall_norm_integral_cexp_smul_iteratedDerivWithin_le [CompleteSpace E] {q : ℝ → E}
    {a : ℝ} (hq : ContDiffOn ℝ ∞ q (Ici a))
    (h0 : ∀ s : ℕ, Tendsto (iteratedDerivWithin s q (Ici a)) atTop (𝓝 0))
    (h1 : ∀ s : ℕ, IntegrableOn (iteratedDerivWithin (s + 1) q (Ici a)) (Ioi a))
    (s : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, ∀ x ≥ (1 : ℝ), ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • iteratedDerivWithin s q (Ici a) t‖ ≤ ε := by
  have hcd : ContDiffOn ℝ (s + 1 : ℕ) q (Ici a) :=
    hq.of_le (by exact_mod_cast (le_top : ((s + 1 : ℕ) : ℕ∞) ≤ ⊤))
  exact exists_forall_norm_integral_cexp_smul_le one_pos hε
    ((hcd.of_le (by exact_mod_cast Nat.le_succ s)).continuousOn_iteratedDerivWithin le_rfl
      (uniqueDiffOn_Ici a))
    (fun t ht => hcd.hasDerivAt_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self s)
      (Ici_mem_nhds ht))
    (h0 s) (h1 s)

/-! ### The example `sin t / t`

The function `q(t) = sin t / t` on `[1, ∞)` shows that the sufficient condition above is not
necessary. Each derivative of `q` is `e^{it} A(1/t) / t + e^{-it} B(1/t) / t` for polynomials `A`
and `B`, so its Fourier integral at `x ≥ 2` is a sum of two integrals at the frequencies
`x ± 1 ≥ 1` against functions to which the sufficient condition applies. -/

open Polynomial in
/-- The function `t⁻¹ P(t⁻¹)`. -/
private def invSymbol (P : ℂ[X]) (t : ℝ) : ℂ := (t : ℂ)⁻¹ * P.eval (t : ℂ)⁻¹

open Polynomial in
/-- The polynomial whose `invSymbol` is the derivative of `invSymbol P`. -/
private def invSymbolDeriv (P : ℂ[X]) : ℂ[X] := -(X * (P + X * derivative P))

open Polynomial in
private lemma hasDerivAt_invSymbol (P : ℂ[X]) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (invSymbol P) (invSymbol (invSymbolDeriv P) t) t := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hu : HasDerivAt (fun y : ℝ => (y : ℂ)⁻¹) (-((t : ℂ) ^ 2)⁻¹) t :=
    (hasDerivAt_inv htc).comp_ofReal
  have hP : HasDerivAt (fun y : ℝ => P.eval (y : ℂ)⁻¹)
      (P.derivative.eval (t : ℂ)⁻¹ * (-((t : ℂ) ^ 2)⁻¹)) t :=
    (P.hasDerivAt _).comp t hu
  refine HasDerivAt.congr_deriv (f := invSymbol P) (hu.mul hP) ?_
  simp only [invSymbol, invSymbolDeriv, eval_neg, eval_mul, eval_add, eval_X]
  field_simp
  ring

open Polynomial in
private lemma continuousOn_invSymbol (P : ℂ[X]) : ContinuousOn (invSymbol P) (Ici 1) :=
  fun _ ht => (hasDerivAt_invSymbol P
    (one_pos.trans_le ht).ne').continuousAt.continuousWithinAt

open Polynomial in
private lemma tendsto_invSymbol (P : ℂ[X]) : Tendsto (invSymbol P) atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => (t : ℂ)⁻¹) atTop (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using h
  have h := hu.mul (((Polynomial.continuous P).tendsto 0).comp hu)
  rw [zero_mul] at h
  exact h.congr fun t => rfl

open Polynomial in
private lemma integrableOn_invSymbol_invSymbolDeriv (P : ℂ[X]) :
    IntegrableOn (invSymbol (invSymbolDeriv P)) (Ioi 1) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun z => (P + X * derivative P).eval z) (Polynomial.continuous _).continuousOn
  have hg : IntegrableOn (fun t : ℝ => |M| * t ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (ContinuousOn.aestronglyMeasurable (fun t ht => (hasDerivAt_invSymbol _
      (one_pos.trans ht).ne').continuousAt.continuousWithinAt) measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := one_pos.trans ht
    have hinv : ‖(t : ℂ)⁻¹‖ = t⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    have hmem : (t : ℂ)⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, hinv]
      exact inv_le_one_of_one_le₀ (le_of_lt ht)
    have hbound := (hM _ hmem).trans (le_abs_self M)
    have hrpow : t ^ (-2 : ℝ) = t⁻¹ * t⁻¹ := by
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      field_simp
    simp only [invSymbol, invSymbolDeriv, eval_neg, eval_mul, eval_X, norm_mul, norm_neg, hinv]
    rw [hrpow]
    calc t⁻¹ * (t⁻¹ * ‖eval (t : ℂ)⁻¹ (P + X * derivative P)‖)
        ≤ t⁻¹ * (t⁻¹ * |M|) := by gcongr
      _ = |M| * (t⁻¹ * t⁻¹) := by ring

/-- `e^{iεt} t⁻¹ P(t⁻¹)`. -/
private def phaseSymbol (ε : ℝ) (P : Polynomial ℂ) (t : ℝ) : ℂ :=
  cexp (((ε * t : ℝ) : ℂ) * I) * invSymbol P t

/-- The polynomials in the decomposition of the derivatives of `sin t / t`. -/
private def sinDivPoly (ε : ℝ) : ℕ → Polynomial ℂ
  | 0 => Polynomial.C ((ε : ℂ) / (2 * I))
  | s + 1 => Polynomial.C ((ε : ℂ) * I) * sinDivPoly ε s + invSymbolDeriv (sinDivPoly ε s)

private lemma hasDerivAt_phaseSymbol (ε : ℝ) (P : Polynomial ℂ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (phaseSymbol ε P)
      (phaseSymbol ε (Polynomial.C ((ε : ℂ) * I) * P + invSymbolDeriv P) t) t := by
  refine HasDerivAt.congr_deriv (f := phaseSymbol ε P)
    ((hasDerivAt_cexp_mul_I ε t).mul (hasDerivAt_invSymbol P ht)) ?_
  simp only [phaseSymbol, invSymbol, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  ring

private lemma iteratedDerivWithin_sin_div_eqOn (s : ℕ) :
    EqOn (iteratedDerivWithin s (fun t : ℝ => ((Real.sin t / t : ℝ) : ℂ)) (Ici 1))
      (fun t => phaseSymbol 1 (sinDivPoly 1 s) t + phaseSymbol (-1) (sinDivPoly (-1) s) t)
      (Ici 1) := by
  induction s with
  | zero =>
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (one_pos.trans_le ht).ne'
    simp only [iteratedDerivWithin_zero, phaseSymbol, invSymbol, sinDivPoly, Polynomial.eval_C]
    push_cast
    rw [Complex.sin]
    simp only [one_mul, neg_mul]
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  | succ s ih =>
    intro t ht
    have ht0 : t ≠ 0 := (one_pos.trans_le ht).ne'
    rw [iteratedDerivWithin_succ, derivWithin_congr ih (ih ht)]
    exact ((hasDerivAt_phaseSymbol 1 _ ht0).add
      (hasDerivAt_phaseSymbol (-1) _ ht0)).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ici 1 t ht)

private lemma exists_forall_norm_integral_cexp_smul_phaseSymbol_le (ε : ℝ) (P : Polynomial ℂ)
    (hε : 1 ≤ 2 + ε) {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, ∀ x ≥ (2 : ℝ), ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • phaseSymbol ε P t‖ ≤ η := by
  obtain ⟨c, hc⟩ := exists_forall_norm_integral_cexp_smul_le (a := 1) one_pos hη
    (continuousOn_invSymbol P) (fun t ht => hasDerivAt_invSymbol P (one_pos.trans ht).ne')
    (tendsto_invSymbol P) (integrableOn_invSymbol_invSymbolDeriv P)
  refine ⟨c, fun x hx T hT T' hT' => ?_⟩
  have heq : ∀ t : ℝ, cexp (((x * t : ℝ) : ℂ) * I) • phaseSymbol ε P t =
      cexp ((((x + ε) * t : ℝ) : ℂ) * I) • invSymbol P t := fun t => by
    have hphase : ((x * t : ℝ) : ℂ) * I + ((ε * t : ℝ) : ℂ) * I = (((x + ε) * t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [phaseSymbol, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add, hphase]
  simp_rw [heq]
  exact hc (x + ε) (by linarith) T hT T' hT'

/-- **Check for DLMF 2.3.5.** The function `q(t) = sin t / t` satisfies the uniform convergence
hypothesis on `[1, ∞)` for `x ≥ 2`. -/
theorem exists_forall_norm_integral_cexp_smul_iteratedDerivWithin_sin_div_le (s : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : ℝ, ∀ x ≥ (2 : ℝ), ∀ T ≥ c, ∀ T' ≥ T,
      ‖∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) •
        iteratedDerivWithin s (fun t : ℝ => ((Real.sin t / t : ℝ) : ℂ)) (Ici 1) t‖ ≤ ε := by
  obtain ⟨c₁, hc₁⟩ := exists_forall_norm_integral_cexp_smul_phaseSymbol_le 1 (sinDivPoly 1 s)
    (by norm_num) (half_pos hε)
  obtain ⟨c₂, hc₂⟩ := exists_forall_norm_integral_cexp_smul_phaseSymbol_le (-1)
    (sinDivPoly (-1) s) (by norm_num) (half_pos hε)
  refine ⟨max (max c₁ c₂) 1, fun x hx T hT T' hT' => ?_⟩
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hsub : [[T, T']] ⊆ Ici 1 := by
    rw [uIcc_of_le hT']
    exact fun t ht => hT1.trans ht.1
  have hcont : ∀ (ε' : ℝ) (P : Polynomial ℂ), IntervalIntegrable
      (fun t => cexp (((x * t : ℝ) : ℂ) * I) • phaseSymbol ε' P t) volume T T' := fun ε' P =>
    ContinuousOn.intervalIntegrable ((continuous_cexp_mul_I x).continuousOn.smul
      ((continuous_cexp_mul_I ε').continuousOn.mul ((continuousOn_invSymbol P).mono hsub)))
  have hcongr : ∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) •
        iteratedDerivWithin s (fun t : ℝ => ((Real.sin t / t : ℝ) : ℂ)) (Ici 1) t =
      (∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • phaseSymbol 1 (sinDivPoly 1 s) t) +
        ∫ t in T..T', cexp (((x * t : ℝ) : ℂ) * I) • phaseSymbol (-1) (sinDivPoly (-1) s) t := by
    rw [← intervalIntegral.integral_add (hcont _ _) (hcont _ _)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    simp only [iteratedDerivWithin_sin_div_eqOn s (hsub ht), smul_add]
  rw [hcongr]
  have h₁ := hc₁ x hx T (((le_max_left _ _).trans (le_max_left _ _)).trans hT) T' hT'
  have h₂ := hc₂ x hx T (((le_max_right _ _).trans (le_max_left _ _)).trans hT) T' hT'
  exact (norm_add_le _ _).trans (by linarith)

private lemma integrableOn_sin_div_sq : IntegrableOn (fun t : ℝ => Real.sin t / t ^ 2) (Ioi 1) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos) ?_ ?_
  · exact (ContinuousOn.aestronglyMeasurable (fun t ht => ContinuousAt.continuousWithinAt
      (Real.continuous_sin.continuousAt.div (by fun_prop)
        (pow_ne_zero 2 (one_pos.trans ht).ne'))) measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := one_pos.trans ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos ht0 2), Real.rpow_neg ht0.le,
      Real.rpow_two, div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one t)

/-- `cos t / t` is not integrable on `(1, ∞)`: translating by `π / 2` would make `sin t / t`
integrable too, and `|cos t| + |sin t| ≥ 1` would then make `1 / t` integrable. -/
private lemma not_integrableOn_cos_div : ¬ IntegrableOn (fun t : ℝ => Real.cos t / t) (Ioi 1) := by
  intro hcos
  have hshift : IntegrableOn (fun t : ℝ => ‖Real.cos (t - Real.pi / 2) / (t - Real.pi / 2)‖)
      (Ioi (1 + Real.pi / 2)) := by
    have h := (measurePreserving_sub_right volume (Real.pi / 2)).integrableOn_comp_preimage
      (measurableEmbedding_subRight _) |>.2 hcos.norm
    simpa [Function.comp_def, Set.preimage_sub_const_Ioi] using h
  have hcosn : IntegrableOn (fun t : ℝ => ‖Real.cos t / t‖) (Ioi 1) := hcos.norm
  have hpos : (0 : ℝ) < 1 + Real.pi / 2 := by positivity
  refine not_integrableOn_Ioi_inv (a := 1 + Real.pi / 2) (Integrable.mono'
    ((hcosn.mono_set (Ioi_subset_Ioi (by linarith [Real.pi_pos]))).add hshift)
    (ContinuousOn.aestronglyMeasurable (fun t ht => ContinuousAt.continuousWithinAt
      (continuousAt_inv₀ (hpos.trans ht).ne')) measurableSet_Ioi) ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hpi := Real.pi_pos
  have ht' : 1 + Real.pi / 2 < t := ht
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - Real.pi / 2 := by linarith
  have hle : 1 ≤ |Real.cos t| + |Real.sin t| := by
    have h1 := Real.sin_sq_add_cos_sq t
    nlinarith [abs_nonneg (Real.cos t), abs_nonneg (Real.sin t), sq_abs (Real.cos t),
      sq_abs (Real.sin t), Real.abs_cos_le_one t, Real.abs_sin_le_one t]
  simp only [Pi.add_apply, Real.cos_sub_pi_div_two, norm_div, Real.norm_eq_abs,
    abs_of_pos ht0, abs_of_pos ht1, norm_inv]
  have hinv : t⁻¹ ≤ (t - Real.pi / 2)⁻¹ := inv_anti₀ ht1 (by linarith)
  calc t⁻¹ ≤ (|Real.cos t| + |Real.sin t|) * t⁻¹ := le_mul_of_one_le_left (by positivity) hle
    _ = |Real.cos t| / t + |Real.sin t| * t⁻¹ := by ring
    _ ≤ |Real.cos t| / t + |Real.sin t| / (t - Real.pi / 2) := by
        rw [div_eq_mul_inv |Real.sin t|]
        gcongr

/-- **Check for DLMF 2.3.5.** The first derivative of `q(t) = sin t / t` is not integrable on
`[1, ∞)`, so the sufficient condition `exists_forall_norm_integral_cexp_smul_iteratedDerivWithin_le`
is not necessary for the uniform convergence hypothesis. -/
theorem not_integrableOn_iteratedDerivWithin_one_sin_div :
    ¬ IntegrableOn (iteratedDerivWithin 1 (fun t : ℝ => ((Real.sin t / t : ℝ) : ℂ)) (Ici 1))
      (Ioi 1) := by
  intro hI
  have hderiv : ∀ t ∈ Ioi (1 : ℝ),
      (iteratedDerivWithin 1 (fun t : ℝ => ((Real.sin t / t : ℝ) : ℂ)) (Ici 1) t).re =
        Real.cos t / t - Real.sin t / t ^ 2 := by
    intro t ht
    have ht0 : t ≠ 0 := (one_pos.trans ht).ne'
    have h : HasDerivAt (fun t : ℝ => Real.sin t / t)
        ((Real.cos t * t - Real.sin t * 1) / t ^ 2) t :=
      (Real.hasDerivAt_sin t).div (hasDerivAt_id t) ht0
    rw [iteratedDerivWithin_one, derivWithin_of_mem_nhds (Ici_mem_nhds ht), h.ofReal_comp.deriv,
      Complex.ofReal_re]
    field_simp
  refine not_integrableOn_cos_div ((hI.re.add integrableOn_sin_div_sq).congr ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Pi.add_apply, RCLike.re_to_complex, hderiv t ht]
  ring

end Asymptotics
