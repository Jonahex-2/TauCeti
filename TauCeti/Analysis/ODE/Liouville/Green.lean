/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Asymptotics.Volterra
import TauCeti.Analysis.ODE.Gronwall.Integrable
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Liouville–Green approximation

Let `f` be positive and `C²` on `(a, ∞)`, let `g` be continuous there, and put
`ξ x = ∫ t in c..x, √(f t)`. The Liouville–Green (or WKB) approximation to a solution of
`w'' = (f + g) w` that is recessive at `+∞` is `f^{-1/4} exp (-ξ)`. Its quality is controlled by

`Φ = f^{-1/4} (f^{-1/4})'' - g f^{-1/2}`,

and by the error-control function `V x = ∫ t in Ici x, |Φ t|`. If `V` is finite, this file
constructs a `C²` solution `w = f^{-1/4} exp (-ξ) (1 + ε)` with

`|ε x| ≤ exp (V x / 2) - 1` and `|ε' x| / (2 √(f x)) ≤ exp (V x / 2) - 1`

(`TauCeti.liouvilleGreen_recessive`). Since `V` is the tail of a convergent integral, it tends to
`0` at `+∞`, and with it the bound on `ε`.

The error `ε` solves the Volterra integral equation

`ε x = ∫ v in Ioi x, ½ (exp (2 (ξ x - ξ v)) - 1) (Φ v + Φ v ε v)`,

whose kernel is bounded by `½` because `ξ` is increasing, so
`TauCeti.exists_volterra_solution` provides it. The sharp bound `exp (V / 2) - 1` comes from the
backward integral Grönwall inequality
`TauCeti.le_mul_exp_integral_of_le_add_integral_mul_rev`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §2.
* NIST Digital Library of Mathematical Functions, §2.7(iii), equations (2.7.20)–(2.7.25),
  <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- The tail integral of a continuous function with integrable tails has derivative `-H`. -/
private theorem hasDerivAt_tail {a : ℝ} {H : ℝ → ℝ} (hHc : ContinuousOn H (Ioi a))
    (hHi : ∀ x ∈ Ioi a, IntegrableOn H (Ioi x)) {x : ℝ} (hx : x ∈ Ioi a) :
    HasDerivAt (fun u ↦ ∫ v in Ioi u, H v) (-H x) x := by
  obtain ⟨b, hab, hbx⟩ := exists_between hx.out
  exact (hHi b hab).hasDerivAt_integral_Ioi (hHc.continuousAt (Ioi_mem_nhds hx)) hbx

/-- The backward Grönwall step on `[x, T]` for the tail `1 + ½ ∫ₜ^∞ q (1 + m)`. -/
private theorem one_add_tail_le_mul_exp {a : ℝ} {q m : ℝ → ℝ}
    (hq : ContinuousOn q (Ioi a)) (hq0 : ∀ x ∈ Ioi a, 0 ≤ q x) (hm : ContinuousOn m (Ioi a))
    (hqm : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ q v * (1 + m v)) (Ioi x))
    (hle : ∀ x ∈ Ioi a, m x ≤ (∫ v in Ioi x, q v * (1 + m v)) / 2) {x T : ℝ} (hx : x ∈ Ioi a)
    (hxT : x ≤ T) :
    1 + (∫ v in Ioi x, q v * (1 + m v)) / 2 ≤
      (1 + (∫ v in Ioi T, q v * (1 + m v)) / 2) * Real.exp (∫ s in x..T, q s / 2) := by
  set G : ℝ → ℝ := fun v ↦ q v * (1 + m v) with hG
  have hGc : ContinuousOn G (Ioi a) := hq.mul (continuousOn_const.add hm)
  set u : ℝ → ℝ := fun t ↦ 1 + (∫ v in Ioi t, G v) / 2 with hu
  have huc : ContinuousOn u (Ioi a) := fun t ht ↦
    (((hasDerivAt_tail hGc hqm ht).continuousAt.div_const 2).const_add 1).continuousWithinAt
  have hsub : ∀ {y S : ℝ}, y ∈ Ioi a → Icc y S ⊆ Ioi a := fun hy z hz ↦ lt_of_lt_of_le hy hz.1
  have hβ : ContinuousOn (fun s ↦ q s / 2) (Icc x T) := (hq.mono (hsub hx)).div_const 2
  have hβu : ContinuousOn (fun s ↦ q s / 2 * u s) (Icc x T) := hβ.mul (huc.mono (hsub hx))
  refine le_mul_exp_integral_of_le_add_integral_mul_rev (hβ.integrableOn_compact isCompact_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2
      (ae_of_all _ fun s hs ↦ div_nonneg (hq0 s (hsub hx hs)) zero_le_two))
    (hβu.integrableOn_compact isCompact_Icc) (fun t ht ↦ ?_) x (left_mem_Icc.2 hxT)
  have htmem : t ∈ Ioi a := hsub hx ht
  have hsplit : (∫ v in Ioi t, G v) - ∫ v in Ioi T, G v = ∫ v in t..T, G v :=
    intervalIntegral.integral_Ioi_sub_Ioi' (hqm t htmem) (hqm T (hsub hx (right_mem_Icc.2 hxT)))
  have huIcc : uIcc t T ⊆ Ioi a := by rw [uIcc_of_le ht.2]; exact hsub htmem
  have hmono : ∫ v in t..T, G v / 2 ≤ ∫ v in t..T, q v / 2 * u v := by
    refine intervalIntegral.integral_mono_on ht.2
      ((hGc.mono huIcc).div_const 2).intervalIntegrable
      (((hq.mono huIcc).div_const 2).mul (huc.mono huIcc)).intervalIntegrable fun v hv ↦ ?_
    have hv' := hsub htmem hv
    have := mul_le_mul_of_nonneg_left (hle v hv') (hq0 v hv')
    simp only [hG, hu]
    nlinarith
  have hdiv : ∫ v in t..T, G v / 2 = (∫ v in t..T, G v) / 2 := intervalIntegral.integral_div _ _
  simp only [hu]
  linarith

/-- The tail estimate behind the sharp Liouville–Green bound. If `m x ≤ ½ ∫ₓ^∞ q (1 + m)` for a
nonnegative integrable weight `q`, then `½ ∫ₓ^∞ q (1 + m) ≤ exp (½ ∫ₓ^∞ q) - 1`. -/
private theorem integral_mul_one_add_div_two_le {a : ℝ} {q m : ℝ → ℝ}
    (hq : ContinuousOn q (Ioi a)) (hq0 : ∀ x ∈ Ioi a, 0 ≤ q x) (hm : ContinuousOn m (Ioi a))
    (hqi : ∀ x ∈ Ioi a, IntegrableOn q (Ioi x))
    (hqm : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ q v * (1 + m v)) (Ioi x))
    (hle : ∀ x ∈ Ioi a, m x ≤ (∫ v in Ioi x, q v * (1 + m v)) / 2) {x : ℝ} (hx : x ∈ Ioi a) :
    (∫ v in Ioi x, q v * (1 + m v)) / 2 ≤ Real.exp ((∫ v in Ioi x, q v) / 2) - 1 := by
  have hYtend : Tendsto (fun T ↦ ∫ v in Ioi T, q v * (1 + m v)) atTop (𝓝 0) := by
    have hlim := intervalIntegral_tendsto_integral_Ioi x (hqm x hx) tendsto_id
    have hcongr : (fun T ↦ (∫ v in Ioi x, q v * (1 + m v)) - ∫ v in x..id T, q v * (1 + m v))
        =ᶠ[atTop] fun T ↦ ∫ v in Ioi T, q v * (1 + m v) := by
      filter_upwards [eventually_ge_atTop x] with T hT
      rw [id, ← intervalIntegral.integral_Ioi_sub_Ioi' (hqm x hx)
        (hqm T (lt_of_lt_of_le hx hT)), sub_sub_cancel]
    simpa using (tendsto_const_nhds.sub hlim).congr' hcongr
  have hVtend : Tendsto (fun T ↦ ∫ s in x..T, q s / 2) atTop (𝓝 ((∫ v in Ioi x, q v) / 2)) := by
    simpa [integral_div] using
      intervalIntegral_tendsto_integral_Ioi x ((hqi x hx).div_const 2) tendsto_id
  have hlim : Tendsto (fun T ↦ (1 + (∫ v in Ioi T, q v * (1 + m v)) / 2) *
      Real.exp (∫ s in x..T, q s / 2)) atTop (𝓝 ((1 + 0 / 2) *
        Real.exp ((∫ v in Ioi x, q v) / 2))) :=
    ((hYtend.div_const 2).const_add 1).mul (Real.continuous_exp.continuousAt.tendsto.comp hVtend)
  have hfinal := ge_of_tendsto hlim ((eventually_ge_atTop x).mono fun T hT ↦
    one_add_tail_le_mul_exp hq hq0 hm hqm hle hx hT)
  norm_num at hfinal
  linarith

/-- The kernel of the Volterra equation for the Liouville–Green error. -/
private noncomputable def errorKernel (ξ : ℝ → ℝ) (x v : ℝ) : ℝ :=
  (Real.exp (2 * (ξ x - ξ v)) - 1) / 2

/-- For increasing `ξ`, the error kernel is bounded by `½`. -/
private theorem abs_errorKernel_le {a x v : ℝ} {ξ : ℝ → ℝ} (hξ : MonotoneOn ξ (Ioi a))
    (hx : a < x) (hxv : x ≤ v) : |errorKernel ξ x v| ≤ 1 / 2 := by
  have h := hξ (show x ∈ Ioi a from hx) (show v ∈ Ioi a from hx.trans_le hxv) hxv
  have h1 : Real.exp (2 * (ξ x - ξ v)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := Real.exp_pos (2 * (ξ x - ξ v))
  rw [abs_le]
  constructor <;> simp only [errorKernel] <;> linarith

/-- A function bounded by the Volterra bound with kernel constant `½` is bounded on each tail. -/
private theorem exists_forall_abs_le_of_volterra_bound {a x : ℝ} {Φ ε : ℝ → ℝ}
    (hV : ∀ x ∈ Ioi a, IntegrableOn (fun t ↦ ‖Φ t‖) (Ioi x))
    (hε : ∀ x ∈ Ioi a, ‖ε x‖ ≤ (1 / 2 * ∫ v in Ioi x, (1 : ℝ) * ‖Φ v‖) *
      Real.exp (∫ v in Ioi x, (1 / 2 : ℝ) * 1 * ‖Φ v‖)) (hx : x ∈ Ioi a) :
    ∃ C, ∀ v ∈ Ioi x, |ε v| ≤ C := by
  have hW := antitoneOn_integral_Ioi (f := fun v ↦ (1 : ℝ) * ‖Φ v‖)
    (fun v _ ↦ by positivity) (fun y hy ↦ by simpa using hV y hy)
  have hZ := antitoneOn_integral_Ioi (f := fun v ↦ (1 / 2 : ℝ) * 1 * ‖Φ v‖)
    (fun v _ ↦ by positivity)
    (fun y hy ↦ by simpa [mul_assoc, IntegrableOn] using (hV y hy).const_mul (1 / 2 : ℝ))
  have hW0 : 0 ≤ ∫ v in Ioi x, (1 : ℝ) * ‖Φ v‖ := setIntegral_nonneg measurableSet_Ioi
    fun _ _ ↦ by positivity
  refine ⟨(1 / 2 * ∫ v in Ioi x, (1 : ℝ) * ‖Φ v‖) *
    Real.exp (∫ v in Ioi x, (1 / 2 : ℝ) * 1 * ‖Φ v‖), fun v hv ↦ ?_⟩
  have hv' : v ∈ Ioi a := hx.out.trans hv
  have h1 : (∫ u in Ioi v, (1 : ℝ) * ‖Φ u‖) ≤ ∫ u in Ioi x, (1 : ℝ) * ‖Φ u‖ :=
    hW hx hv' (le_of_lt hv)
  have h2 : (∫ u in Ioi v, (1 / 2 : ℝ) * 1 * ‖Φ u‖) ≤ ∫ u in Ioi x, (1 / 2 : ℝ) * 1 * ‖Φ u‖ :=
    hZ hx hv' (le_of_lt hv)
  calc |ε v| = ‖ε v‖ := (Real.norm_eq_abs _).symm
    _ ≤ _ := hε v hv'
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) (Real.exp_le_exp.2 h2)
      (Real.exp_pos _).le (mul_nonneg (by norm_num) hW0)

/-- The Volterra equation for the Liouville–Green error has a continuous solution for which
`|Φ| (1 + |ε|)` is integrable on every tail. -/
private theorem exists_error_volterra {a : ℝ} {ξ Φ : ℝ → ℝ} (hξc : ContinuousOn ξ (Ioi a))
    (hξ : MonotoneOn ξ (Ioi a)) (hΦ : ContinuousOn Φ (Ioi a))
    (hV : ∀ x ∈ Ioi a, IntegrableOn (fun t ↦ |Φ t|) (Ioi x)) :
    ∃ ε : ℝ → ℝ, ContinuousOn ε (Ioi a) ∧
      (∀ x ∈ Ioi a, ε x = ∫ v in Ioi x, errorKernel ξ x v * (Φ v * (1 + ε v))) ∧
      ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ |Φ v| * (1 + |ε v|)) (Ioi x) := by
  have hKc : ContinuousOn (Function.uncurry (errorKernel ξ))
      {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2} := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ ↦ ξ p.1) {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2} :=
      hξc.comp continuousOn_fst fun p hp ↦ hp.1
    have h2 : ContinuousOn (fun p : ℝ × ℝ ↦ ξ p.2) {p : ℝ × ℝ | a < p.1 ∧ p.1 ≤ p.2} :=
      hξc.comp continuousOn_snd fun p hp ↦ lt_of_lt_of_le hp.1 hp.2
    exact ((((continuousOn_const.mul (h1.sub h2)).rexp).sub continuousOn_const).div_const 2)
  have hVn : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ ‖Φ v‖) (Ioi x) := fun x hx ↦ by
    simpa [Real.norm_eq_abs] using hV x hx
  obtain ⟨ε, hεc, hεeq, hεb⟩ := exists_volterra_solution (𝕜 := ℝ) (E := ℝ) (a := a)
    (K := errorKernel ξ) (J := Φ) (ψ := Φ) (P := fun _ ↦ 1 / 2) (Q := fun _ ↦ 1) hKc hΦ hΦ
    continuousOn_const continuousOn_const (fun _ _ ↦ by norm_num) (fun _ _ ↦ zero_le_one)
    (fun x v hx hxv ↦ by simpa [Real.norm_eq_abs] using abs_errorKernel_le hξ hx hxv)
    (fun x hx ↦ by simpa using hVn x hx)
    (fun x hx ↦ by simpa [mul_assoc, IntegrableOn] using (hVn x hx).const_mul (1 / 2 : ℝ))
  refine ⟨ε, hεc, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hεeq x hx]
    exact integral_congr_ae (ae_of_all _ fun v ↦ by simp only [smul_eq_mul]; ring)
  · obtain ⟨C, hC⟩ := exists_forall_abs_le_of_volterra_bound hVn hεb hx
    have hsub := Ioi_subset_Ioi hx.out.le
    refine Integrable.mono' ((hV x hx).mul_const (1 + C))
      (((hΦ.mono hsub).abs.mul (continuousOn_const.add (hεc.mono hsub).abs)).aestronglyMeasurable
        measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun v hv ↦ ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
    exact hC v hv

/-- The flux `exp (2 ξ x) ∫ₓ^∞ exp (-2 ξ) G` of the Liouville–Green error. -/
private noncomputable def errorFlux (ξ G : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (2 * ξ x) * ∫ v in Ioi x, Real.exp (-(2 * ξ v)) * G v

/-- For increasing `ξ`, the weight `exp (-2 ξ)` preserves integrability on tails. -/
private theorem integrableOn_exp_mul {a : ℝ} {ξ G : ℝ → ℝ} (hξc : ContinuousOn ξ (Ioi a))
    (hξ : MonotoneOn ξ (Ioi a)) (hGc : ContinuousOn G (Ioi a))
    (hGi : ∀ x ∈ Ioi a, IntegrableOn G (Ioi x)) {x : ℝ} (hx : x ∈ Ioi a) :
    IntegrableOn (fun v ↦ Real.exp (-(2 * ξ v)) * G v) (Ioi x) := by
  have hc : ContinuousOn (fun v ↦ Real.exp (-(2 * ξ v)) * G v) (Ioi a) :=
    ((continuousOn_const.mul hξc).neg.rexp).mul hGc
  refine Integrable.mono' ((hGi x hx).norm.const_mul (Real.exp (-(2 * ξ x))))
    ((hc.mono (Ioi_subset_Ioi hx.out.le)).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun v hv ↦ ?_))
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  gcongr
  exact hξ hx (hx.out.trans hv : v ∈ Ioi a) (le_of_lt hv)

/-- The flux solves `D' = 2 s D - G`, where `s = ξ'`. -/
private theorem hasDerivAt_errorFlux {a : ℝ} {ξ s G : ℝ → ℝ} (hξc : ContinuousOn ξ (Ioi a))
    (hξm : MonotoneOn ξ (Ioi a)) (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (s x) x)
    (hGc : ContinuousOn G (Ioi a)) (hGi : ∀ x ∈ Ioi a, IntegrableOn G (Ioi x)) {x : ℝ}
    (hx : x ∈ Ioi a) : HasDerivAt (errorFlux ξ G) (2 * s x * errorFlux ξ G x - G x) x := by
  have hEc : ContinuousOn (fun v ↦ Real.exp (-(2 * ξ v)) * G v) (Ioi a) :=
    ((continuousOn_const.mul hξc).neg.rexp).mul hGc
  have h := (((hξ x hx).const_mul 2).exp).fun_mul
    (hasDerivAt_tail hEc (fun y hy ↦ integrableOn_exp_mul hξc hξm hGc hGi hy) hx)
  refine h.congr_deriv ?_
  have hcancel : Real.exp (2 * ξ x) * Real.exp (-(2 * ξ x)) = 1 := by
    rw [← Real.exp_add]; simp
  simp only [errorFlux]
  linear_combination (-G x) * hcancel

/-- The solution of the error equation is half the flux minus half the tail of `G`. -/
private theorem error_eq_errorFlux {a x : ℝ} {ξ G ε : ℝ → ℝ} (hξc : ContinuousOn ξ (Ioi a))
    (hξm : MonotoneOn ξ (Ioi a)) (hGc : ContinuousOn G (Ioi a))
    (hGi : ∀ x ∈ Ioi a, IntegrableOn G (Ioi x)) (hx : x ∈ Ioi a)
    (hε : ε x = ∫ v in Ioi x, errorKernel ξ x v * G v) :
    ε x = errorFlux ξ G x / 2 - (∫ v in Ioi x, G v) / 2 := by
  have hint : ∀ v, errorKernel ξ x v * G v =
      Real.exp (2 * ξ x) / 2 * (Real.exp (-(2 * ξ v)) * G v) - G v / 2 := fun v ↦ by
    have hexp : Real.exp (2 * (ξ x - ξ v)) = Real.exp (2 * ξ x) * Real.exp (-(2 * ξ v)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [errorKernel, hexp]
    ring
  rw [hε]
  simp only [hint]
  rw [integral_sub ((integrableOn_exp_mul hξc hξm hGc hGi hx).const_mul _)
    ((hGi x hx).div_const 2), integral_const_mul, integral_div]
  simp only [errorFlux]
  ring

/-- The flux is bounded by the tail integral of any majorant of `|G|`. -/
private theorem abs_errorFlux_le {a x : ℝ} {ξ G B : ℝ → ℝ} (hξ : MonotoneOn ξ (Ioi a))
    (hx : x ∈ Ioi a) (hB : IntegrableOn B (Ioi x)) (hGB : ∀ v, |G v| ≤ B v) :
    |errorFlux ξ G x| ≤ ∫ v in Ioi x, B v := by
  simp only [errorFlux]
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hB
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun v hv ↦ ?_))
  have hexp : Real.exp (2 * ξ x) * (Real.exp (-(2 * ξ v)) * G v) =
      Real.exp (2 * (ξ x - ξ v)) * G v := by
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have hle : Real.exp (2 * (ξ x - ξ v)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have := hξ hx (hx.out.trans hv : v ∈ Ioi a) (le_of_lt hv)
    linarith)
  rw [hexp, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  calc Real.exp (2 * (ξ x - ξ v)) * |G v| ≤ 1 * |G v| := by gcongr
    _ ≤ B v := by simpa using hGB v

/-- The error equation of the Liouville–Green approximation. For an increasing `ξ` with
derivative `s > 0` and a continuous `Φ` with integrable tails, the system `ε' = s D`,
`D' = 2 s D - Φ (1 + ε)` has a solution with `|ε|, |D| / 2 ≤ exp (½ ∫ₓ^∞ |Φ|) - 1`. -/
private theorem exists_liouvilleGreen_error {a : ℝ} {ξ s Φ : ℝ → ℝ}
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (s x) x) (hs : ∀ x ∈ Ioi a, 0 < s x)
    (hΦ : ContinuousOn Φ (Ioi a)) (hV : ∀ x ∈ Ioi a, IntegrableOn (fun t ↦ |Φ t|) (Ioi x)) :
    ∃ ε D : ℝ → ℝ,
      (∀ x ∈ Ioi a, HasDerivAt ε (s x * D x) x) ∧
      (∀ x ∈ Ioi a, HasDerivAt D (2 * s x * D x - Φ x * (1 + ε x)) x) ∧
      ∀ x ∈ Ioi a, |ε x| ≤ Real.exp ((∫ t in Ioi x, |Φ t|) / 2) - 1 ∧
        |D x| / 2 ≤ Real.exp ((∫ t in Ioi x, |Φ t|) / 2) - 1 := by
  have hξc : ContinuousOn ξ (Ioi a) := fun x hx ↦ (hξ x hx).continuousAt.continuousWithinAt
  have hξm : MonotoneOn ξ (Ioi a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi a) hξc (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · rw [interior_Ioi] at hx
      exact (hξ x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi] at hx
      rw [(hξ x hx).deriv]
      exact (hs x hx).le
  obtain ⟨ε, hεc, hεeq, hqm⟩ := exists_error_volterra hξc hξm hΦ hV
  set G : ℝ → ℝ := fun v ↦ Φ v * (1 + ε v) with hG
  have hGc : ContinuousOn G (Ioi a) := hΦ.mul (continuousOn_const.add hεc)
  have hGle : ∀ v, |G v| ≤ |Φ v| * (1 + |ε v|) := fun v ↦ by
    simp only [hG, abs_mul]
    gcongr
    exact (abs_add_le _ _).trans (by simp)
  have hGi : ∀ x ∈ Ioi a, IntegrableOn G (Ioi x) := fun x hx ↦
    Integrable.mono' (hqm x hx) ((hGc.mono (Ioi_subset_Ioi hx.out.le)).aestronglyMeasurable
      measurableSet_Ioi) (ae_of_all _ hGle)
  have hDd := fun x (hx : x ∈ Ioi a) ↦ hasDerivAt_errorFlux hξc hξm hξ hGc hGi hx
  have hεd : ∀ x ∈ Ioi a, HasDerivAt ε (s x * errorFlux ξ G x) x := fun x hx ↦ by
    have h := ((hDd x hx).div_const 2).sub ((hasDerivAt_tail hGc hGi hx).div_const 2)
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
      using error_eq_errorFlux hξc hξm hGc hGi hy (hεeq y hy)
  have hεY : ∀ x ∈ Ioi a, |ε x| ≤ (∫ v in Ioi x, |Φ v| * (1 + |ε v|)) / 2 := fun x hx ↦ by
    rw [← integral_div, hεeq x hx, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hqm x hx).div_const 2)
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun v hv ↦ ?_))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |errorKernel ξ x v| * |G v| ≤ 1 / 2 * (|Φ v| * (1 + |ε v|)) :=
          mul_le_mul (abs_errorKernel_le hξm hx.out (le_of_lt hv)) (hGle v) (abs_nonneg _)
            (by norm_num)
      _ = |Φ v| * (1 + |ε v|) / 2 := by ring
  refine ⟨ε, errorFlux ξ G, hεd, hDd, fun x hx ↦ ?_⟩
  have hkey := integral_mul_one_add_div_two_le (q := fun t ↦ |Φ t|) (m := fun t ↦ |ε t|)
    hΦ.abs (fun _ _ ↦ abs_nonneg _) hεc.abs hV hqm hεY hx
  exact ⟨(hεY x hx).trans hkey, (div_le_div_of_nonneg_right
    (abs_errorFlux_le hξm hx (hqm x hx) hGle) zero_le_two).trans hkey⟩

/-- The two derivatives of `w = F exp (-ξ) (1 + ε)` at a point, given the error equation. Here
`F > 0`, `ξ' = s`, and `F² s = 1`, so `f = s²`. The second derivative is `(f + g) w`. -/
private theorem hasDerivAt_liouvilleGreen {F F₁ ξ ε D W₁ : ℝ → ℝ} {x s f g F₂ : ℝ}
    (hF0 : F x ≠ 0) (hs : F x ^ 2 * s = 1) (hfs : f = s ^ 2) (hF : HasDerivAt F (F₁ x) x)
    (hF₁ : HasDerivAt F₁ F₂ x) (hξ : HasDerivAt ξ s x) (hε : HasDerivAt ε (s * D x) x)
    (hD : HasDerivAt D (2 * s * D x - (F x * F₂ - g / s) * (1 + ε x)) x)
    (hW₁ : W₁ = fun y ↦ Real.exp (-ξ y) *
      (F₁ y * (1 + ε y) - (F y)⁻¹ * (1 + ε y) + (F y)⁻¹ * D y)) :
    HasDerivAt (fun y ↦ F y * Real.exp (-ξ y) * (1 + ε y)) (W₁ x) x ∧
      HasDerivAt W₁ ((f + g) * (F x * Real.exp (-ξ x) * (1 + ε x))) x := by
  have hsx : s = (F x ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hs
  have hy := hε.const_add 1
  have hE := hξ.fun_neg.exp
  constructor
  · refine ((hF.fun_mul hE).fun_mul hy).congr_deriv ?_
    subst hW₁
    simp only [hsx]
    field_simp
    ring
  · have hinv := hF.fun_inv hF0
    subst hW₁
    refine (hE.fun_mul (((hF₁.fun_mul hy).fun_sub (hinv.fun_mul hy)).fun_add
      (hinv.fun_mul hD))).congr_deriv ?_
    subst hfs
    simp only [hsx]
    field_simp
    ring

/-- The Liouville–Green construction for an abstract amplitude `F` with `F² √f = 1`. -/
private theorem liouvilleGreen_aux {f g F : ℝ → ℝ} {a c : ℝ} (hc : a < c)
    (hf : ContinuousOn f (Ioi a)) (hfpos : ∀ x ∈ Ioi a, 0 < f x) (hg : ContinuousOn g (Ioi a))
    (hFC : ContDiffOn ℝ 2 F (Ioi a)) (hFpos : ∀ x ∈ Ioi a, 0 < F x)
    (hFs : ∀ x ∈ Ioi a, F x ^ 2 * √(f x) = 1)
    (hV : ∀ x ∈ Ioi a,
      IntegrableOn (fun t ↦ |F t * iteratedDeriv 2 F t - g t / √(f t)|) (Ioi x)) :
    ∃ w ε : ℝ → ℝ, ContDiffOn ℝ 2 w (Ioi a) ∧
      (∀ x ∈ Ioi a, iteratedDeriv 2 w x = (f x + g x) * w x) ∧
      ∀ x ∈ Ioi a,
        w x = F x * Real.exp (-∫ t in c..x, √(f t)) * (1 + ε x) ∧
        |ε x| ≤ Real.exp ((∫ t in Ioi x, |F t * iteratedDeriv 2 F t - g t / √(f t)|) / 2) - 1 ∧
        |deriv ε x| / (2 * √(f x)) ≤
          Real.exp ((∫ t in Ioi x, |F t * iteratedDeriv 2 F t - g t / √(f t)|) / 2) - 1 := by
  have hsqrtc : ContinuousOn (fun x ↦ √(f x)) (Ioi a) := hf.sqrt
  have hspos : ∀ x ∈ Ioi a, 0 < √(f x) := fun x hx ↦ Real.sqrt_pos.2 (hfpos x hx)
  have hF1C : ContDiffOn ℝ 1 (deriv F) (Ioi a) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioi).1
      (by simpa [one_add_one_eq_two] using hFC)).2.2
  have hiter : iteratedDeriv 2 F = deriv (deriv F) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hF1 : ∀ x ∈ Ioi a, HasDerivAt F (deriv F x) x := fun x hx ↦
    ((hFC.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hF2 : ∀ x ∈ Ioi a, HasDerivAt (deriv F) (iteratedDeriv 2 F x) x := fun x hx ↦ by
    rw [hiter]
    exact ((hF1C.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hF2c : ContinuousOn (iteratedDeriv 2 F) (Ioi a) := by
    rw [hiter]
    exact hF1C.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have hΦc : ContinuousOn (fun t ↦ F t * iteratedDeriv 2 F t - g t / √(f t)) (Ioi a) :=
    (hFC.continuousOn.mul hF2c).sub (hg.div hsqrtc fun x hx ↦ (hspos x hx).ne')
  have hξ : ∀ x ∈ Ioi a, HasDerivAt (fun x ↦ ∫ t in c..x, √(f t)) (√(f x)) x := fun x hx ↦ by
    have hsub : uIcc c x ⊆ Ioi a := fun z hz ↦ lt_of_lt_of_le (lt_min hc hx) hz.1
    exact intervalIntegral.integral_hasDerivAt_right ((hsqrtc.mono hsub).intervalIntegrable)
      (hsqrtc.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hsqrtc.continuousAt (Ioi_mem_nhds hx))
  obtain ⟨ε, D, hεd, hDd, hbd⟩ := exists_liouvilleGreen_error hξ hspos hΦc hV
  have hder := fun x (hx : x ∈ Ioi a) ↦ hasDerivAt_liouvilleGreen (F₂ := iteratedDeriv 2 F x)
    (f := f x) (g := g x) (hFpos x hx).ne' (hFs x hx) (Real.sq_sqrt (hfpos x hx).le).symm
    (hF1 x hx) (hF2 x hx) (hξ x hx) (hεd x hx) (hDd x hx) rfl
  refine ⟨_, ε, ?_, fun x hx ↦ ?_, fun x hx ↦ ⟨rfl, (hbd x hx).1, ?_⟩⟩
  · have hwc : ContinuousOn (fun y ↦ F y * Real.exp (-∫ t in c..y, √(f t)) * (1 + ε y)) (Ioi a) :=
      fun x hx ↦ (hder x hx).1.continuousAt.continuousWithinAt
    have hW₁ : ContDiffOn ℝ 1 (fun y ↦ Real.exp (-∫ t in c..y, √(f t)) *
        (deriv F y * (1 + ε y) - (F y)⁻¹ * (1 + ε y) + (F y)⁻¹ * D y)) (Ioi a) := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun x hx ↦ (hder x hx).2.differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact contDiffOn_zero.2 (((hf.add hg).mul hwc).congr fun x hx ↦ (hder x hx).2.deriv)
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨fun x hx ↦ (hder x hx).1.differentiableAt.differentiableWithinAt, by simp,
      hW₁.congr fun x hx ↦ (hder x hx).1.deriv⟩
  · have hderiv := (eventually_of_mem (Ioi_mem_nhds hx) fun y hy ↦ (hder y hy).1.deriv)
    rw [iteratedDeriv_succ, iteratedDeriv_one, Filter.EventuallyEq.deriv_eq hderiv,
      (hder x hx).2.deriv]
  · rw [(hεd x hx).deriv, abs_mul, abs_of_pos (hspos x hx)]
    have hs0 := (hspos x hx).ne'
    calc √(f x) * |D x| / (2 * √(f x)) = |D x| / 2 := by field_simp
      _ ≤ _ := (hbd x hx).2

/-- **The Liouville–Green theorem** for the solution recessive at `+∞` (DLMF 2.7.20–2.7.25; Olver,
Chapter 6, §2). Let `f` be positive and `C²` on `(a, ∞)`, let `g` be continuous there,
let `c > a`, and suppose that `Φ = f^{-1/4} (f^{-1/4})'' - g f^{-1/2}` is integrable on `[x, ∞)`
for every `x > a`. Then `w'' = (f + g) w` has a `C²` solution on `(a, ∞)` of the form
`w = f^{-1/4} exp (-∫ t in c..x, √(f t)) (1 + ε)`, where, with `V x = ∫ t in Ici x, |Φ t|`,
`|ε x| ≤ exp (V x / 2) - 1` and `|ε' x| / (2 √(f x)) ≤ exp (V x / 2) - 1`. -/
theorem liouvilleGreen_recessive {f g : ℝ → ℝ} {a c : ℝ} (hc : a < c)
    (hf : ContDiffOn ℝ 2 f (Ioi a)) (hfpos : ∀ x ∈ Ioi a, 0 < f x)
    (hg : ContinuousOn g (Ioi a))
    (hV : ∀ x ∈ Ioi a, IntegrableOn (fun t ↦ |f t ^ (-(1 / 4 : ℝ)) *
      iteratedDeriv 2 (fun s ↦ f s ^ (-(1 / 4 : ℝ))) t - g t / √(f t)|) (Ici x)) :
    ∃ w ε : ℝ → ℝ, ContDiffOn ℝ 2 w (Ioi a) ∧
      (∀ x ∈ Ioi a, iteratedDeriv 2 w x = (f x + g x) * w x) ∧
      ∀ x ∈ Ioi a,
        w x = f x ^ (-(1 / 4 : ℝ)) * Real.exp (-∫ t in c..x, √(f t)) * (1 + ε x) ∧
        |ε x| ≤ Real.exp ((∫ t in Ici x, |f t ^ (-(1 / 4 : ℝ)) *
          iteratedDeriv 2 (fun s ↦ f s ^ (-(1 / 4 : ℝ))) t - g t / √(f t)|) / 2) - 1 ∧
        |deriv ε x| / (2 * √(f x)) ≤ Real.exp ((∫ t in Ici x, |f t ^ (-(1 / 4 : ℝ)) *
          iteratedDeriv 2 (fun s ↦ f s ^ (-(1 / 4 : ℝ))) t - g t / √(f t)|) / 2) - 1 := by
  have hFs : ∀ x ∈ Ioi a, (f x ^ (-(1 / 4 : ℝ))) ^ 2 * √(f x) = 1 := fun x hx ↦ by
    have hx0 := hfpos x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    norm_num
  simp only [integral_Ici_eq_integral_Ioi]
  exact liouvilleGreen_aux hc hf.continuousOn hfpos hg
    (hf.rpow_const_of_ne fun x hx ↦ (hfpos x hx).ne')
    (fun x hx ↦ Real.rpow_pos_of_pos (hfpos x hx) _) hFs
    fun x hx ↦ (hV x hx).mono_set Ioi_subset_Ici_self

/-- The check `f = 1`, `g = 0`: here `Φ = 0`, so the error vanishes and the recessive solution is
exactly `exp (-(x - c))`. -/
example {a c : ℝ} (hc : a < c) :
    ∃ w : ℝ → ℝ, ContDiffOn ℝ 2 w (Ioi a) ∧ (∀ x ∈ Ioi a, iteratedDeriv 2 w x = w x) ∧
      ∀ x ∈ Ioi a, w x = Real.exp (-(x - c)) := by
  have hΦ : ∀ t : ℝ, |(1 : ℝ) ^ (-(1 / 4 : ℝ)) *
      iteratedDeriv 2 (fun _ : ℝ ↦ (1 : ℝ) ^ (-(1 / 4 : ℝ))) t - 0 / √1| = 0 := fun t ↦ by
    simp [iteratedDeriv_succ]
  obtain ⟨w, ε, hw, heq, hbd⟩ := liouvilleGreen_recessive (f := fun _ ↦ 1) (g := fun _ ↦ 0) hc
    contDiffOn_const (fun _ _ ↦ one_pos) continuousOn_const
    (fun x _ ↦ by simp only [hΦ]; exact integrableOn_zero)
  refine ⟨w, hw, fun x hx ↦ by simpa using heq x hx, fun x hx ↦ ?_⟩
  obtain ⟨hwx, hε, -⟩ := hbd x hx
  have hε0 : ε x = 0 := by simpa [iteratedDeriv_succ] using hε
  simpa [hε0] using hwx

end TauCeti
