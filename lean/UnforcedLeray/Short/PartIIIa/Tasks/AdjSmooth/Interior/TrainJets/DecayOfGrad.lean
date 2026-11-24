import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- From `P |v| ≤ A` with `P > 0`: `|v| ≤ A P⁻¹`. -/
theorem dec_abs_of_weight {P A v : ℝ} (hP : 0 < P) (h : P * |v| ≤ A) :
    |v| ≤ A * P⁻¹ := by
  have hP' : P ≠ 0 := hP.ne'
  calc |v| = (P * |v|) * P⁻¹ := by field_simp
    _ ≤ A * P⁻¹ := mul_le_mul_of_nonneg_right h (inv_nonneg.2 hP.le)

/-- The tail of the weight `(1 + s²)^{-β/2}` on `[η, ∞)`, `η ≥ 0`. -/
theorem dec_tail (β : ℝ) (hβ : 1 < β) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ η R : ℝ, 0 ≤ η → η ≤ R →
      ∫ s in η..R, (1 + s ^ 2) ^ (-(β / 2)) ≤ K₀ * (1 + η ^ 2) ^ (-((β - 1) / 2)) := by
  have hβ1 : 0 < β - 1 := by linarith
  refine ⟨(2:ℝ) ^ (β / 2) / (β - 1), div_nonneg (by positivity) hβ1.le, ?_⟩
  intro η R hη hR
  have hpt : ∀ s ∈ Icc η R, (1 + s ^ 2) ^ (-(β / 2)) ≤ (2:ℝ) ^ (β / 2) * (1 + s) ^ (-β) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans hη hs.1
    have h1s : 0 < 1 + s := by linarith
    have hx : 0 < (1 + s) ^ 2 / 2 := div_pos (pow_pos h1s 2) two_pos
    have hxy : (1 + s) ^ 2 / 2 ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
    have h1 := Real.rpow_le_rpow_of_nonpos hx hxy (show -(β / 2) ≤ 0 by linarith)
    have e1 : (1 + s) ^ 2 = (1 + s) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
    have e2 : ((1 + s) ^ ((2 : ℕ) : ℝ)) ^ (-(β / 2)) = (1 + s) ^ (-β) := by
      rw [← Real.rpow_mul h1s.le]
      congr 1
      push_cast
      ring
    have h2 : ((1 + s) ^ 2 / 2) ^ (-(β / 2)) = (2:ℝ) ^ (β / 2) * (1 + s) ^ (-β) := by
      rw [Real.div_rpow (sq_nonneg _) (by norm_num), e1, e2,
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
    linarith
  have hsub : uIcc η R = Icc η R := Set.uIcc_of_le hR
  have hcontg : Continuous (fun s : ℝ => (1 + s ^ 2) ^ (-(β / 2))) :=
    (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).rpow_const
      (fun s => Or.inl (by positivity))
  have hIg : IntervalIntegrable (fun s : ℝ => (1 + s ^ 2) ^ (-(β / 2))) volume η R :=
    hcontg.intervalIntegrable η R
  have hconth : ContinuousOn (fun s : ℝ => (2:ℝ) ^ (β / 2) * (1 + s) ^ (-β)) (uIcc η R) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rpow_const (by fun_prop)
    intro s hs
    left
    rw [hsub] at hs
    have : 0 ≤ s := le_trans hη hs.1
    exact (show (0:ℝ) < 1 + s by linarith).ne'
  have hIh : IntervalIntegrable (fun s : ℝ => (2:ℝ) ^ (β / 2) * (1 + s) ^ (-β)) volume η R :=
    hconth.intervalIntegrable
  have hJ : ∫ s in η..R, (1 + s) ^ (-β) ≤ (1 + η) ^ (-β + 1) / (β - 1) := by
    have hshift := intervalIntegral.integral_comp_add_left (a := η) (b := R)
      (fun u : ℝ => u ^ (-β)) 1
    have h0 : (0 : ℝ) ∉ uIcc (1 + η) (1 + R) := by
      intro h0
      rw [Set.uIcc_of_le (by linarith)] at h0
      linarith [h0.1]
    have hr : -β ≠ -1 := by intro h; linarith
    rw [hshift, integral_rpow (Or.inr ⟨hr, h0⟩)]
    have e3 : ((1 + R) ^ (-β + 1) - (1 + η) ^ (-β + 1)) / (-β + 1) =
        ((1 + η) ^ (-β + 1) - (1 + R) ^ (-β + 1)) / (β - 1) := by
      rw [show -β + 1 = -(β - 1) by ring, div_neg, ← neg_div, neg_sub]
    have hX : 0 ≤ (1 + R) ^ (-β + 1) := Real.rpow_nonneg (by linarith) _
    rw [e3]
    exact div_le_div_of_nonneg_right (by linarith) hβ1.le
  have hcomp : (1 + η) ^ (-β + 1) ≤ (1 + η ^ 2) ^ (-((β - 1) / 2)) := by
    have e4 : ((1 + η) ^ 2) ^ (-((β - 1) / 2)) = (1 + η) ^ (-β + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      congr 1
      push_cast
      ring
    rw [← e4]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [hη]) (by linarith)
  have hIntLe : ∫ s in η..R, (1 + s ^ 2) ^ (-(β / 2)) ≤
      ∫ s in η..R, (2:ℝ) ^ (β / 2) * (1 + s) ^ (-β) :=
    intervalIntegral.integral_mono_on hR hIg hIh hpt
  calc ∫ s in η..R, (1 + s ^ 2) ^ (-(β / 2))
      ≤ ∫ s in η..R, (2:ℝ) ^ (β / 2) * (1 + s) ^ (-β) := hIntLe
    _ = (2:ℝ) ^ (β / 2) * ∫ s in η..R, (1 + s) ^ (-β) :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (2:ℝ) ^ (β / 2) * ((1 + η) ^ (-β + 1) / (β - 1)) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (2:ℝ) ^ (β / 2) / (β - 1) * (1 + η) ^ (-β + 1) := by ring
    _ ≤ (2:ℝ) ^ (β / 2) / (β - 1) * (1 + η ^ 2) ^ (-((β - 1) / 2)) :=
        mul_le_mul_of_nonneg_left hcomp (div_nonneg (by positivity) hβ1.le)

/-- The core one-sided estimate: the horizontal mean `Ē(η) = ∫ E(q, η) dq` of a `C¹` field
with the weighted `η`-derivative bound and bounded strip integrals satisfies, for `η₀ ≥ 0`,
`Ē(η₀) ≤ 2c A K₀ (1 + η₀²)^{-(β-1)/2}`. -/
theorem dec_core (β c : ℝ) (hβ : 1 < β) (hc : 0 < c) (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
    (hK : ∀ η R : ℝ, 0 ≤ η → η ≤ R →
      ∫ s in η..R, (1 + s ^ 2) ^ (-(β / 2)) ≤ K₀ * (1 + η ^ 2) ^ (-((β - 1) / 2)))
    (E : ℝ × ℝ → ℝ) (A B : ℝ) (hE : ContDiff ℝ 1 E)
    (hη : ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialEta E x| ≤ A)
    (hstrip : ∀ a b : ℝ, |∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), E (q, η)| ≤ B) :
    ∀ η₀ : ℝ, 0 ≤ η₀ → ∫ q in (-(c / 2))..(c / 2), E (q, η₀) ≤
      2 * c * (A * (K₀ * (1 + η₀ ^ 2) ^ (-((β - 1) / 2)))) := by
  intro η₀ hη₀
  have hdiffE : Differentiable ℝ E := hE.differentiable (by norm_num)
  have hcont : Continuous E := hE.continuous
  have hcontg : Continuous (fun s : ℝ => (1 + s ^ 2) ^ (-(β / 2))) :=
    (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).rpow_const
      (fun s => Or.inl (by positivity))
  have hcq : ∀ R : ℝ, Continuous (fun q : ℝ => E (q, R)) := fun R =>
    hcont.comp (continuous_id.prodMk continuous_const)
  have hsl : ∀ q s : ℝ, HasDerivAt (fun t : ℝ => E (q, t))
      (UnforcedLeray.Cyl.partialEta E (q, s)) s := by
    intro q s
    have h1 : DifferentiableAt ℝ (fun t : ℝ => E (q, t)) s :=
      DifferentiableAt.comp s (hdiffE (q, s))
        ((differentiableAt_const q).prodMk differentiableAt_id)
    exact h1.hasDerivAt
  have hpE_cont : ∀ q : ℝ, Continuous (fun s : ℝ => UnforcedLeray.Cyl.partialEta E (q, s)) := by
    intro q
    have hfd : Continuous (fun s : ℝ => fderiv ℝ E (q, s) (0, 1)) := by
      have h1 : Continuous (fun s : ℝ => fderiv ℝ E (q, s)) :=
        (hE.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)
      exact h1.clm_apply continuous_const
    convert hfd using 1
    funext s
    have h3 : HasDerivAt (fun t : ℝ => ((q, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) s :=
      (hasDerivAt_const s q).prodMk (hasDerivAt_id s)
    have h4 := (hdiffE (q, s)).hasFDerivAt.comp_hasDerivAt s h3
    exact h4.deriv
  -- the `η`-increment of `E` on each line is controlled by the weight
  have hC1 : ∀ q R : ℝ, η₀ ≤ R →
      |E (q, R) - E (q, η₀)| ≤ A * ∫ s in η₀..R, (1 + s ^ 2) ^ (-(β / 2)) := by
    intro q R hR
    have hFTC : E (q, R) - E (q, η₀) =
        ∫ s in η₀..R, UnforcedLeray.Cyl.partialEta E (q, s) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hsl q s)
        ((hpE_cont q).intervalIntegrable _ _)]
    rw [hFTC, ← Real.norm_eq_abs]
    have hg : IntervalIntegrable (fun s : ℝ => A * (1 + s ^ 2) ^ (-(β / 2))) volume η₀ R :=
      (continuous_const.mul hcontg).intervalIntegrable _ _
    have hpt : ∀ t : ℝ, ‖UnforcedLeray.Cyl.partialEta E (q, t)‖ ≤
        A * (1 + t ^ 2) ^ (-(β / 2)) := by
      intro t
      have hP : 0 < (1 + t ^ 2) ^ (β / 2) := Real.rpow_pos_of_pos (by positivity) _
      rw [Real.norm_eq_abs, Real.rpow_neg (show (0:ℝ) ≤ 1 + t ^ 2 by positivity)]
      exact dec_abs_of_weight hP (hη (q, t))
    calc ‖∫ s in η₀..R, UnforcedLeray.Cyl.partialEta E (q, s)‖
        ≤ ∫ s in η₀..R, A * (1 + s ^ 2) ^ (-(β / 2)) :=
          intervalIntegral.norm_integral_le_of_norm_le hR
            (Filter.Eventually.of_forall fun t _ => hpt t) hg
      _ = A * ∫ s in η₀..R, (1 + s ^ 2) ^ (-(β / 2)) :=
          intervalIntegral.integral_const_mul _ _
  obtain ⟨Eb, hEb⟩ : ∃ Eb : ℝ → ℝ, ∀ t, Eb t = ∫ q in (-(c / 2))..(c / 2), E (q, t) :=
    ⟨fun t => ∫ q in (-(c / 2))..(c / 2), E (q, t), fun t => rfl⟩
  have hstrip' : ∀ a b : ℝ, |∫ t in a..b, Eb t| ≤ B := by
    intro a b
    simpa only [hEb] using hstrip a b
  have contEb : Continuous Eb := by
    have hfun : Eb = fun t => ∫ q in (-(c / 2))..(c / 2), E (q, t) := funext hEb
    rw [hfun]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t q => E (q, t)) (hcont.comp (continuous_snd.prodMk continuous_fst)) _ _
  have hA : 0 ≤ A := le_trans (by positivity) (hη (0, 0))
  have hB : 0 ≤ B := by
    have h := hstrip' 0 0
    rw [intervalIntegral.integral_same, abs_zero] at h
    exact h
  -- the horizontal means move by at most the tail
  have hbarR : ∀ R : ℝ, η₀ ≤ R →
      |Eb R - Eb η₀| ≤ c * (A * ∫ s in η₀..R, (1 + s ^ 2) ^ (-(β / 2))) := by
    intro R hR
    rw [hEb, hEb, ← intervalIntegral.integral_sub ((hcq R).intervalIntegrable _ _)
      ((hcq η₀).intervalIntegrable _ _), ← Real.norm_eq_abs]
    have hlen : |c / 2 - -(c / 2)| = c := by
      rw [show c / 2 - -(c / 2) = c by ring, abs_of_pos hc]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(c / 2)) (b := c / 2)
      (C := A * ∫ s in η₀..R, (1 + s ^ 2) ^ (-(β / 2)))
      (f := fun q => E (q, R) - E (q, η₀))
      (fun q _ => by rw [Real.norm_eq_abs]; exact hC1 q R hR)
    rw [hlen] at hb
    exact le_trans hb (le_of_eq (by ring))
  have hD : ∀ R : ℝ, η₀ ≤ R →
      |Eb R - Eb η₀| ≤ c * (A * (K₀ * (1 + η₀ ^ 2) ^ (-((β - 1) / 2)))) := fun R hR =>
    le_trans (hbarR R hR)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK η₀ R hη₀ hR) hA) hc.le)
  rw [← hEb]
  by_contra hcon
  push_neg at hcon
  -- `D` is the admissible increment; `δ = Ē(η₀) - D > D ≥ 0` is a lower bound for `Ē`
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = c * (A * (K₀ * (1 + η₀ ^ 2) ^ (-((β - 1) / 2)))) :=
    ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    have : 0 ≤ (1 + η₀ ^ 2) ^ (-((β - 1) / 2)) := Real.rpow_nonneg (by positivity) _
    positivity
  have hcon' : 2 * D < Eb η₀ := by
    rw [hDdef]
    have e : 2 * (c * (A * (K₀ * (1 + η₀ ^ 2) ^ (-((β - 1) / 2))))) =
        2 * c * (A * (K₀ * (1 + η₀ ^ 2) ^ (-((β - 1) / 2)))) := by ring
    rw [e]
    exact hcon
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = Eb η₀ - D := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hlow : ∀ R : ℝ, η₀ ≤ R → δ ≤ Eb R := by
    intro R hR
    have h := hD R hR
    rw [abs_le] at h
    rw [hδdef]
    linarith [h.1]
  have hint : ∀ R : ℝ, η₀ ≤ R → δ * (R - η₀) ≤ B := by
    intro R hR
    have h1 : ∫ t in η₀..R, δ ≤ ∫ t in η₀..R, Eb t :=
      intervalIntegral.integral_mono_on hR intervalIntegrable_const (contEb.intervalIntegrable _ _)
        (fun t ht => hlow t ht.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have h2 := (le_abs_self _).trans (hstrip' η₀ R)
    nlinarith [h1, h2]
  have hRpos : η₀ ≤ η₀ + (B + 1) / δ := by
    have : 0 ≤ (B + 1) / δ := div_nonneg (by linarith) hδpos.le
    linarith
  have hfin := hint (η₀ + (B + 1) / δ) hRpos
  have e5 : δ * (η₀ + (B + 1) / δ - η₀) = B + 1 := by
    rw [show η₀ + (B + 1) / δ - η₀ = (B + 1) / δ by ring]
    field_simp
  linarith [hfin, e5]

/-- The pointwise oscillation of `E` in the cell: `c |E(q, η)| ≤ |Ē(η)| + A w c²`. -/
theorem dec_pointwise (β c A : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (E : ℝ × ℝ → ℝ)
    (hE : ContDiff ℝ 1 E) (hper : ∀ x : ℝ × ℝ, E (x.1 + c, x.2) = E x)
    (hQ : ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialQ E x| ≤ A)
    (η q : ℝ) :
    c * |E (q, η)| ≤ |∫ s in (-(c / 2))..(c / 2), E (s, η)| +
      A * (1 + η ^ 2) ^ (-(β / 2)) * c ^ 2 := by
  have hdiffE : Differentiable ℝ E := hE.differentiable (by norm_num)
  have hw0 : 0 ≤ (1 + η ^ 2) ^ (-(β / 2)) := Real.rpow_nonneg (by positivity) _
  have hd : ∀ t : ℝ, ‖deriv (fun s : ℝ => E (s, η)) t‖ ≤ A * (1 + η ^ 2) ^ (-(β / 2)) := by
    intro t
    have hP : 0 < (1 + η ^ 2) ^ (β / 2) := Real.rpow_pos_of_pos (by positivity) _
    rw [Real.norm_eq_abs, Real.rpow_neg (show (0:ℝ) ≤ 1 + η ^ 2 by positivity)]
    exact dec_abs_of_weight hP (hQ (t, η))
  have hlip : ∀ u v : ℝ, ‖E (u, η) - E (v, η)‖ ≤ A * (1 + η ^ 2) ^ (-(β / 2)) * ‖u - v‖ := by
    intro u v
    have hf : ∀ s ∈ (univ : Set ℝ), DifferentiableAt ℝ (fun s : ℝ => E (s, η)) s := fun s _ =>
      DifferentiableAt.comp s (hdiffE (s, η))
        (differentiableAt_id.prodMk (differentiableAt_const η))
    exact Convex.norm_image_sub_le_of_norm_deriv_le hf (fun s _ => hd s) convex_univ
      (mem_univ v) (mem_univ u)
  have hperiod : Function.Periodic (fun s : ℝ => E (s, η)) c := fun s => hper (s, η)
  -- reduce `q` to the cell `[-c/2, c/2)`
  obtain ⟨q', hq'mem, k, rfl⟩ : ∃ q' ∈ Ico (-(c / 2)) (-(c / 2) + c), ∃ k : ℤ,
      q = q' + k * c := by
    refine ⟨toIcoMod hc (-(c / 2)) q, toIcoMod_mem_Ico hc _ _, toIcoDiv hc (-(c / 2)) q, ?_⟩
    have := toIcoMod_add_toIcoDiv_zsmul hc (-(c / 2)) q
    rw [zsmul_eq_mul] at this
    linarith
  have hE' : E (q' + k * c, η) = E (q', η) := (hperiod.int_mul k) q'
  rw [hE']
  -- the oscillation of `E(q', ·)` over the cell
  have hI : ‖∫ s in (-(c / 2))..(c / 2), (E (q', η) - E (s, η))‖ ≤
      A * (1 + η ^ 2) ^ (-(β / 2)) * c * c := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(c / 2)) (b := c / 2) (C := A * (1 + η ^ 2) ^ (-(β / 2)) * c)
      (f := fun s => E (q', η) - E (s, η)) (fun s hs => by
        rw [uIoc_of_le (by linarith)] at hs
        have hdist : ‖q' - s‖ ≤ c := by
          rw [Real.norm_eq_abs, abs_le]
          constructor
          · linarith [hq'mem.1, hs.2]
          · linarith [hq'mem.2, hs.1]
        calc ‖E (q', η) - E (s, η)‖ ≤ A * (1 + η ^ 2) ^ (-(β / 2)) * ‖q' - s‖ := by
              rw [← norm_neg (E (q', η) - E (s, η)), neg_sub, ← norm_neg (q' - s), neg_sub]
              exact hlip s q'
          _ ≤ A * (1 + η ^ 2) ^ (-(β / 2)) * c :=
              mul_le_mul_of_nonneg_left hdist (mul_nonneg hA hw0))
    have hlen : |c / 2 - -(c / 2)| = c := by
      rw [show c / 2 - -(c / 2) = c by ring, abs_of_pos hc]
    rw [hlen] at hb
    exact hb
  have hcη : Continuous (fun s : ℝ => E (s, η)) :=
    hE.continuous.comp (continuous_id.prodMk continuous_const)
  have hsplit : ∫ s in (-(c / 2))..(c / 2), (E (q', η) - E (s, η)) =
      c * E (q', η) - ∫ s in (-(c / 2))..(c / 2), E (s, η) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_const (c := E (q', η)))
      (hcη.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [hsplit] at hI
  have h2 : |c * E (q', η)| ≤ |∫ s in (-(c / 2))..(c / 2), E (s, η)| +
      |c * E (q', η) - ∫ s in (-(c / 2))..(c / 2), E (s, η)| := by
    have := abs_sub_abs_le_abs_sub (c * E (q', η)) (∫ s in (-(c / 2))..(c / 2), E (s, η))
    linarith
  rw [abs_mul, abs_of_pos hc, Real.norm_eq_abs] at *
  have h3 : |c * E (q', η) - ∫ s in (-(c / 2))..(c / 2), E (s, η)| ≤
      A * (1 + η ^ 2) ^ (-(β / 2)) * c * c := by
    simpa [Real.norm_eq_abs] using hI
  nlinarith [h2, h3]

/-- The horizontal mean bound on `t ≥ 0`, from `dec_core` for `E` and for `-E`. -/
theorem dec_abs_nonneg (β c A B K₀ : ℝ) (hβ : 1 < β) (hc : 0 < c) (hK₀ : 0 ≤ K₀)
    (hK : ∀ η R : ℝ, 0 ≤ η → η ≤ R →
      ∫ s in η..R, (1 + s ^ 2) ^ (-(β / 2)) ≤ K₀ * (1 + η ^ 2) ^ (-((β - 1) / 2)))
    (E : ℝ × ℝ → ℝ) (hE : ContDiff ℝ 1 E)
    (hη : ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialEta E x| ≤ A)
    (hstrip : ∀ a b : ℝ, |∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), E (q, η)| ≤ B)
    (t : ℝ) (ht : 0 ≤ t) :
    |∫ q in (-(c / 2))..(c / 2), E (q, t)| ≤
      2 * c * (A * (K₀ * (1 + t ^ 2) ^ (-((β - 1) / 2)))) := by
  have hup := dec_core β c hβ hc K₀ hK₀ hK E A B hE hη hstrip t ht
  have hη' : ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) *
      |UnforcedLeray.Cyl.partialEta (fun y : ℝ × ℝ => -E y) x| ≤ A := by
    intro x
    have e : UnforcedLeray.Cyl.partialEta (fun y : ℝ × ℝ => -E y) x =
        -UnforcedLeray.Cyl.partialEta E x := by
      show deriv (fun η : ℝ => -E (x.1, η)) x.2 = -deriv (fun η : ℝ => E (x.1, η)) x.2
      exact deriv.neg (f := fun η : ℝ => E (x.1, η))
    rw [e, abs_neg]
    exact hη x
  have hstrip' : ∀ a b : ℝ, |∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), (fun y : ℝ × ℝ => -E y) (q, η)| ≤ B := by
    intro a b
    have e : (∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), (fun y : ℝ × ℝ => -E y) (q, η)) =
        -∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), E (q, η) := by
      simp only [intervalIntegral.integral_neg]
    rw [e, abs_neg]
    exact hstrip a b
  have hlow := dec_core β c hβ hc K₀ hK₀ hK (fun y : ℝ × ℝ => -E y) A B hE.neg hη' hstrip' t ht
  have e2 : (∫ q in (-(c / 2))..(c / 2), (fun y : ℝ × ℝ => -E y) (q, t)) =
      -∫ q in (-(c / 2))..(c / 2), E (q, t) := by
    simp only [intervalIntegral.integral_neg]
  rw [e2] at hlow
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The reflected field `(q, η) ↦ E(q, -η)` and the bound on `t ≤ 0`. -/
theorem dec_abs_nonpos (β c A B K₀ : ℝ) (hβ : 1 < β) (hc : 0 < c) (hK₀ : 0 ≤ K₀)
    (hK : ∀ η R : ℝ, 0 ≤ η → η ≤ R →
      ∫ s in η..R, (1 + s ^ 2) ^ (-(β / 2)) ≤ K₀ * (1 + η ^ 2) ^ (-((β - 1) / 2)))
    (E : ℝ × ℝ → ℝ) (hE : ContDiff ℝ 1 E)
    (hη : ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialEta E x| ≤ A)
    (hstrip : ∀ a b : ℝ, |∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), E (q, η)| ≤ B)
    (t : ℝ) (ht : t ≤ 0) :
    |∫ q in (-(c / 2))..(c / 2), E (q, t)| ≤
      2 * c * (A * (K₀ * (1 + t ^ 2) ^ (-((β - 1) / 2)))) := by
  have hEr : ContDiff ℝ 1 (fun x : ℝ × ℝ => E (x.1, -x.2)) :=
    hE.comp (contDiff_fst.prodMk contDiff_snd.neg)
  have hηr : ∀ x : ℝ × ℝ, (1 + x.2 ^ 2) ^ (β / 2) *
      |UnforcedLeray.Cyl.partialEta (fun y : ℝ × ℝ => E (y.1, -y.2)) x| ≤ A := by
    intro x
    have e : UnforcedLeray.Cyl.partialEta (fun y : ℝ × ℝ => E (y.1, -y.2)) x =
        -UnforcedLeray.Cyl.partialEta E (x.1, -x.2) := by
      show deriv (fun η : ℝ => E (x.1, -η)) x.2 = -deriv (fun η : ℝ => E (x.1, η)) (-x.2)
      exact deriv_comp_neg (f := fun η : ℝ => E (x.1, η)) (x := x.2)
    rw [e, abs_neg]
    have h : (1 + (-x.2) ^ 2) ^ (β / 2) * |UnforcedLeray.Cyl.partialEta E (x.1, -x.2)| ≤ A :=
      hη (x.1, -x.2)
    rw [neg_sq] at h
    exact h
  have hstrip_r : ∀ a b : ℝ, |∫ η in a..b, ∫ q in (-(c / 2))..(c / 2),
      (fun y : ℝ × ℝ => E (y.1, -y.2)) (q, η)| ≤ B := by
    intro a b
    have e : (∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), E (q, -η)) =
        ∫ η in -b..-a, ∫ q in (-(c / 2))..(c / 2), E (q, η) :=
      intervalIntegral.integral_comp_neg (f := fun η : ℝ => ∫ q in (-(c / 2))..(c / 2), E (q, η))
    show |∫ η in a..b, ∫ q in (-(c / 2))..(c / 2), E (q, -η)| ≤ B
    rw [e]
    exact hstrip (-b) (-a)
  have hr := dec_abs_nonneg β c A B K₀ hβ hc hK₀ hK (fun y : ℝ × ℝ => E (y.1, -y.2)) hEr hηr
    hstrip_r (-t) (by linarith)
  simp only [neg_neg, neg_sq] at hr
  exact hr

theorem tjDecayOfGrad : TjDecayOfGrad := by
  intro β c hβ hc
  obtain ⟨K₀, hK₀, hK⟩ := dec_tail β hβ
  refine ⟨2 * K₀ + c, by linarith, ?_⟩
  intro E A B hE hper hQ hη hstrip x
  have hA : 0 ≤ A := le_trans (by positivity) (hη (0, 0))
  have hbar : ∀ t : ℝ, |∫ q in (-(c / 2))..(c / 2), E (q, t)| ≤
      2 * c * (A * (K₀ * (1 + t ^ 2) ^ (-((β - 1) / 2)))) := by
    intro t
    rcases le_total 0 t with ht | ht
    · exact dec_abs_nonneg β c A B K₀ hβ hc hK₀ hK E hE hη hstrip t ht
    · exact dec_abs_nonpos β c A B K₀ hβ hc hK₀ hK E hE hη hstrip t ht
  have hpt := dec_pointwise β c A hc hA E hE hper hQ x.2 x.1
  rw [Prod.mk.eta] at hpt
  have hb := hbar x.2
  have hx1 : (0:ℝ) ≤ 1 + x.2 ^ 2 := by positivity
  have hWw : (1 + x.2 ^ 2) ^ (-(β / 2)) ≤ (1 + x.2 ^ 2) ^ (-((β - 1) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x.2]) (by linarith)
  have hP : 0 < (1 + x.2 ^ 2) ^ ((β - 1) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hPW : (1 + x.2 ^ 2) ^ ((β - 1) / 2) * (1 + x.2 ^ 2) ^ (-((β - 1) / 2)) = 1 := by
    rw [Real.rpow_neg hx1, mul_inv_cancel₀ hP.ne']
  have hW0 : 0 ≤ (1 + x.2 ^ 2) ^ (-((β - 1) / 2)) := Real.rpow_nonneg hx1 _
  have hw' : A * (1 + x.2 ^ 2) ^ (-(β / 2)) * c ^ 2 ≤
      A * (1 + x.2 ^ 2) ^ (-((β - 1) / 2)) * c ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWw hA) (sq_nonneg c)
  have h1 : c * |E x| ≤ c * ((2 * K₀ + c) * A * (1 + x.2 ^ 2) ^ (-((β - 1) / 2))) := by
    have e : c * ((2 * K₀ + c) * A * (1 + x.2 ^ 2) ^ (-((β - 1) / 2))) =
        2 * c * (A * (K₀ * (1 + x.2 ^ 2) ^ (-((β - 1) / 2)))) +
          A * (1 + x.2 ^ 2) ^ (-((β - 1) / 2)) * c ^ 2 := by ring
    rw [e]
    linarith [hpt, hb, hw']
  have h2 : |E x| ≤ (2 * K₀ + c) * A * (1 + x.2 ^ 2) ^ (-((β - 1) / 2)) :=
    le_of_mul_le_mul_left h1 hc
  calc (1 + x.2 ^ 2) ^ ((β - 1) / 2) * |E x|
      ≤ (1 + x.2 ^ 2) ^ ((β - 1) / 2) * ((2 * K₀ + c) * A * (1 + x.2 ^ 2) ^ (-((β - 1) / 2))) :=
        mul_le_mul_of_nonneg_left h2 hP.le
    _ = (2 * K₀ + c) * A * ((1 + x.2 ^ 2) ^ ((β - 1) / 2) * (1 + x.2 ^ 2) ^ (-((β - 1) / 2))) := by
        ring
    _ = (2 * K₀ + c) * A := by rw [hPW, mul_one]

end UnforcedLeray.Short.IIIa
