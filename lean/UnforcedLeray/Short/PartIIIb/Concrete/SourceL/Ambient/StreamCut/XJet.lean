import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Data.Nat.Choose.Sum

/-!
# Part III-b, task `PartIII-b:C/srcL/9/5/4` (`SCXJet`): the stream-cutoff jet bound

`scXJet_of_parts` : from `SCPsiSmooth`, `SCPsiBound`, `SCChiJet χy` we get `SCXJet χy`.

Write `X = 𝒞_y Z = φ(y) Z(y) + (g(y) Ψ_Z(y)) e_z` with `φ(y) = χ_y(ν/r²)`,
`g(y) = (∂_r χ_y)(r)/r`, `r = cylR y`, `Ψ_Z = streamPsi Z`.
On the open set `{|y|² > 11ν/12, r > 0}` the three factors are `C^7`; the Leibniz bounds give
`‖∂^m X(y)‖ ≤ 2^m (|C₂| + |C₂||C₁|) B r^{-4-m} ≤ 128 (|C₂| + |C₂||C₁|) B r^{-4-m}`.
Where `r² < ν`, `X` vanishes on the open set `{w₀² + w₁² < ν}` (`χ_y` vanishes for `t² < ν`).

Source: `the November 2 reference manuscript` lines 4161-4166, 4178-4186, 4917-4937.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The open region `{|w|² > 11ν/12, r > 0}`. -/
def xjWReg (ν : ℝ) : Set Vec3 := {y | ν * (11 / 12) < eucSq y ∧ 0 < cylR y}

/-- `χ_y(ν/r²)` as a function of `y`. -/
def xjPhi (ν : ℝ) (χy : ℝ → ℝ) (w : Vec3) : ℝ := chiYr ν 1 χy (cylR w)

/-- `(χ_y'(r))/r` as a function of `y`. -/
def xjG (ν : ℝ) (χy : ℝ → ℝ) (w : Vec3) : ℝ := deriv (chiYr ν 1 χy) (cylR w) / cylR w

/-- The unit vector `e_z`. -/
def xjEz : Vec3 := ![0, 0, 1]

/-- The open set `{w₀² + w₁² < ν}`. -/
def xjOut (ν : ℝ) : Set Vec3 := {w | w 0 ^ 2 + w 1 ^ 2 < ν}

theorem xjWReg_isOpen (ν : ℝ) : IsOpen (xjWReg ν) := by
  have h1 : Continuous fun y : Vec3 => eucSq y := by
    unfold eucSq; fun_prop
  have h2 : Continuous fun y : Vec3 => cylR y := by
    unfold cylR; fun_prop
  exact (isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2)

theorem xjOut_isOpen (ν : ℝ) : IsOpen (xjOut ν) :=
  isOpen_lt (f := fun w : Vec3 => w 0 ^ 2 + w 1 ^ 2) (g := fun _ : Vec3 => ν) (by fun_prop)
    continuous_const

theorem xj_cylR_nonneg (y : Vec3) : 0 ≤ cylR y := Real.sqrt_nonneg _

theorem xj_cylR_sq (y : Vec3) : cylR y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  unfold cylR
  exact Real.sq_sqrt (by positivity)

theorem xj_sq_le_eucSq (y : Vec3) : cylR y ^ 2 ≤ eucSq y := by
  rw [xj_cylR_sq]
  unfold eucSq
  rw [Fin.sum_univ_three]
  nlinarith [sq_nonneg (y 2)]

theorem xj_cylR_le_sqrt (y : Vec3) : cylR y ≤ Real.sqrt (eucSq y) := by
  unfold cylR
  apply Real.sqrt_le_sqrt
  unfold eucSq
  rw [Fin.sum_univ_three]
  nlinarith [sq_nonneg (y 2)]

/-- `χ_y(ν/r²)` vanishes where `t² < ν` (with `ε = 1`). -/
theorem xj_chiYr_zero {ν : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) {t : ℝ}
    (ht : t ^ 2 < ν) : chiYr ν 1 χy t = 0 := by
  unfold chiYr
  split_ifs with h0
  · rfl
  · have h1 : (1 * t) ^ 2 = t ^ 2 := by ring
    have hpos : 0 < (1 * t) ^ 2 := by
      rw [h1]
      exact lt_of_le_of_ne (sq_nonneg t) (Ne.symm (pow_ne_zero 2 h0))
    apply hχ.zero
    rw [le_div_iff₀ hpos, h1]
    linarith

/-- The derivative of `chiYr` vanishes where `t² < ν`. -/
theorem xj_chiYr_deriv_zero {ν : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) {t : ℝ}
    (ht : t ^ 2 < ν) : deriv (chiYr ν 1 χy) t = 0 := by
  have hopen : IsOpen {s : ℝ | s ^ 2 < ν} :=
    isOpen_lt (f := fun s : ℝ => s ^ 2) (g := fun _ : ℝ => ν) (by fun_prop) continuous_const
  have hev : chiYr ν 1 χy =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds (show t ∈ {s : ℝ | s ^ 2 < ν} from ht)] with s hs
    exact xj_chiYr_zero hχ hs
  rw [hev.deriv_eq, deriv_const]

theorem xj_stream_zero_on_out {ν : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : Vec3 → Vec3) {w : Vec3} (hw : w ∈ xjOut ν) : streamCut ν 1 χy Z w = 0 := by
  have hw' : cylR w ^ 2 < ν := by
    rw [xj_cylR_sq]
    exact hw
  unfold streamCut
  rw [xj_chiYr_zero hχ hw', xj_chiYr_deriv_zero hχ hw']
  simp

/-- Derivative bound for `Z` at `y` (from `SCZHyp`-type bounds, `r ≤ |y|`). -/
theorem xj_zJet {ν B : ℝ} (hB : 0 ≤ B) {Z : Vec3 → Vec3}
    (hZb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤ B * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m))
    {y : Vec3} (hy : ν * (11 / 12) < eucSq y) (hr : 0 < cylR y) (j : ℕ) (hj : j ≤ 7) :
    ‖iteratedFDeriv ℝ j Z y‖ ≤ B * cylR y ^ (-(4 : ℝ) - j) := by
  have h := hZb j hj y hy
  have hpow : (Real.sqrt (eucSq y)) ^ (-(4 : ℝ) - j) ≤ cylR y ^ (-(4 : ℝ) - j) := by
    apply Real.rpow_le_rpow_of_nonpos hr (xj_cylR_le_sqrt y)
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  exact h.trans (mul_le_mul_of_nonneg_left hpow hB)

theorem xj_le_abs_mul_rpow {x C r a : ℝ} (hr : 0 ≤ r) (h : x ≤ C * r ^ a) :
    x ≤ |C| * r ^ a :=
  h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hr a))

theorem xj_le_abs_mul_mul_rpow {x C B r a : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r)
    (h : x ≤ C * B * r ^ a) : x ≤ |C| * B * r ^ a :=
  h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hB)
    (Real.rpow_nonneg hr a))

theorem xj_iterWithin_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set Vec3}
    (hs : IsOpen s) {y : Vec3} (hy : y ∈ s) (f : Vec3 → E) (n : ℕ) :
    iteratedFDerivWithin ℝ n f s y = iteratedFDeriv ℝ n f y :=
  iteratedFDerivWithin_of_isOpen n hs hy

theorem xj_sum_choose_mul (m : ℕ) (c : ℝ) :
    ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * c = 2 ^ m * c := by
  rw [← Finset.sum_mul]
  congr 1
  exact_mod_cast Nat.sum_range_choose m

theorem xj_norm_xjEz_le : ‖xjEz‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (x := xjEz) (r := 1) zero_le_one).2 (fun i => ?_)
  fin_cases i <;> simp [xjEz]

/-- The stream cutoff splits on `xjWReg ν`. -/
theorem xj_stream_eq (ν : ℝ) (χy : ℝ → ℝ) (Z : Vec3 → Vec3) :
    streamCut ν 1 χy Z = (fun w => xjPhi ν χy w • Z w) +
      (fun w => (xjG ν χy w * streamPsi Z w) • xjEz) := by
  funext w
  rfl

theorem scXJet_of_parts (χy : ℝ → ℝ) (h1 : SCPsiSmooth) (h2 : SCPsiBound) (h3 : SCChiJet χy) :
    SCXJet χy := by
  obtain ⟨C1, hC1⟩ := h2
  obtain ⟨C2, hC2⟩ := h3
  unfold SCXJet
  refine ⟨128 * (|C2| + |C2| * |C1|), ?_⟩
  intro ν B hν hB Z hZ hχ y hy
  have hC4 : 0 ≤ 128 * (|C2| + |C2| * |C1|) := by positivity
  have hR : ∀ k : ℕ, 0 ≤ 128 * (|C2| + |C2| * |C1|) * B * cylR y ^ (-(4 : ℝ) - k) :=
    fun k => mul_nonneg (mul_nonneg hC4 hB) (Real.rpow_nonneg (xj_cylR_nonneg y) _)
  rcases lt_or_ge (cylR y ^ 2) ν with hlt | hge
  · -- region `r² < ν`: the field vanishes near `y`
    have hyO : y ∈ xjOut ν := by
      show y 0 ^ 2 + y 1 ^ 2 < ν
      rw [← xj_cylR_sq]
      exact hlt
    have hev : streamCut ν 1 χy Z =ᶠ[𝓝 y] fun _ => (0 : Vec3) := by
      filter_upwards [(xjOut_isOpen ν).mem_nhds hyO] with w hw
      exact xj_stream_zero_on_out hχ Z hw
    refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, ?_⟩
    intro m _
    rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
    by_cases h0 : m = 0
    · subst h0
      simpa using hR 0
    · simp only [iteratedFDeriv_const_of_ne h0, Pi.zero_apply, norm_zero]
      exact hR m
  · -- region `ν ≤ r²`: Leibniz on the smooth factors
    have hyW : y ∈ xjWReg ν :=
      ⟨lt_of_lt_of_le (by linarith) (le_trans hge (xj_sq_le_eucSq y)), hy⟩
    obtain ⟨hZc, hZb⟩ := id hZ
    have hopen := xjWReg_isOpen ν
    have huniq : UniqueDiffOn ℝ (xjWReg ν) := hopen.uniqueDiffOn
    have hφW : ContDiffOn ℝ 7 (xjPhi ν χy) (xjWReg ν) := fun w hw =>
      ((hC2 ν hν hχ w hw.2).1).contDiffWithinAt
    have hgW : ContDiffOn ℝ 7 (xjG ν χy) (xjWReg ν) := fun w hw =>
      ((hC2 ν hν hχ w hw.2).2.1).contDiffWithinAt
    have hZW : ContDiffOn ℝ 7 Z (xjWReg ν) := hZc.mono (fun w hw => hw.1)
    have hΨW : ContDiffOn ℝ 7 (streamPsi Z) (xjWReg ν) := h1 ν B Z hν hB hZ
    have hFW : ContDiffOn ℝ 7 (streamCut ν 1 χy Z) (xjWReg ν) := by
      rw [xj_stream_eq]
      exact (hφW.smul hZW).add ((hgW.mul hΨW).smul contDiffOn_const)
    refine ⟨hFW.contDiffAt (hopen.mem_nhds hyW), ?_⟩
    intro m hm
    -- pointwise facts at `y`
    have hφY : ContDiffWithinAt ℝ 7 (xjPhi ν χy) (xjWReg ν) y := hφW y hyW
    have hZY : ContDiffWithinAt ℝ 7 Z (xjWReg ν) y := hZW y hyW
    have hgY : ContDiffWithinAt ℝ 7 (xjG ν χy) (xjWReg ν) y := hgW y hyW
    have hΨY : ContDiffWithinAt ℝ 7 (streamPsi Z) (xjWReg ν) y := hΨW y hyW
    have hA0 : ContDiffWithinAt ℝ 7 (fun w => xjPhi ν χy w • Z w) (xjWReg ν) y :=
      hφY.smul hZY
    have hgΨY : ContDiffWithinAt ℝ 7 (fun w => xjG ν χy w * streamPsi Z w) (xjWReg ν) y :=
      hgY.mul hΨY
    have hB0 : ContDiffWithinAt ℝ 7 (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
        (xjWReg ν) y :=
      hgΨY.smul (contDiffWithinAt_const (c := xjEz))
    have hm7 : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
    have hA1 : ContDiffWithinAt ℝ (m : WithTop ℕ∞) (fun w => xjPhi ν χy w • Z w)
        (xjWReg ν) y := hA0.of_le hm7
    have hB1 : ContDiffWithinAt ℝ (m : WithTop ℕ∞) (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
        (xjWReg ν) y := hB0.of_le hm7
    -- term bounds for the first Leibniz sum
    have termA : ∀ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (xjPhi ν χy) (xjWReg ν) y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) Z (xjWReg ν) y‖ ≤
          (m.choose i : ℝ) * (|C2| * B * cylR y ^ (-(4 : ℝ) - m)) := by
      intro i hi
      have hi' : i ≤ m := by
        rw [Finset.mem_range] at hi
        omega
      rw [xj_iterWithin_eq hopen hyW, xj_iterWithin_eq hopen hyW]
      have hφb : ‖iteratedFDeriv ℝ i (xjPhi ν χy) y‖ ≤ |C2| * cylR y ^ (-(i : ℝ)) :=
        xj_le_abs_mul_rpow (xj_cylR_nonneg y) ((hC2 ν hν hχ y hy).2.2 i (by omega)).1
      have hZb' : ‖iteratedFDeriv ℝ (m - i) Z y‖ ≤ B * cylR y ^ (-(4 : ℝ) - ((m - i : ℕ) : ℝ)) :=
        xj_zJet hB hZb hyW.1 hyW.2 (m - i) (by omega)
      have hexp : cylR y ^ (-(i : ℝ)) * cylR y ^ (-(4 : ℝ) - ((m - i : ℕ) : ℝ)) =
          cylR y ^ (-(4 : ℝ) - (m : ℝ)) := by
        rw [← Real.rpow_add hyW.2]
        congr 1
        rw [Nat.cast_sub hi']
        ring
      have hprod : ‖iteratedFDeriv ℝ i (xjPhi ν χy) y‖ * ‖iteratedFDeriv ℝ (m - i) Z y‖ ≤
          (|C2| * B) * cylR y ^ (-(4 : ℝ) - (m : ℝ)) := by
        have h1' := mul_le_mul hφb hZb' (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (xj_cylR_nonneg y) _))
        calc _ ≤ _ := h1'
          _ = (|C2| * B) * (cylR y ^ (-(i : ℝ)) * cylR y ^ (-(4 : ℝ) - ((m - i : ℕ) : ℝ))) := by
            ring
          _ = _ := by rw [hexp]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    -- term bounds for the second Leibniz sum (`g · Ψ_Z`)
    have termB : ∀ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (xjG ν χy) (xjWReg ν) y‖ *
            ‖iteratedFDerivWithin ℝ (m - i) (streamPsi Z) (xjWReg ν) y‖ ≤
          (m.choose i : ℝ) * ((|C2| * |C1|) * B * cylR y ^ (-(4 : ℝ) - (m : ℝ))) := by
      intro i hi
      have hi' : i ≤ m := by
        rw [Finset.mem_range] at hi
        omega
      rw [xj_iterWithin_eq hopen hyW, xj_iterWithin_eq hopen hyW]
      have hgb : ‖iteratedFDeriv ℝ i (xjG ν χy) y‖ ≤ |C2| * cylR y ^ (-(2 : ℝ) - (i : ℝ)) :=
        xj_le_abs_mul_rpow (xj_cylR_nonneg y) ((hC2 ν hν hχ y hy).2.2 i (by omega)).2
      have hψb : ‖iteratedFDeriv ℝ (m - i) (streamPsi Z) y‖ ≤
          |C1| * B * cylR y ^ (-(2 : ℝ) - ((m - i : ℕ) : ℝ)) :=
        xj_le_abs_mul_mul_rpow hB (xj_cylR_nonneg y)
          (hC1 ν B Z hν hB hZ (m - i) (by omega) y hge)
      have hexp : cylR y ^ (-(2 : ℝ) - (i : ℝ)) * cylR y ^ (-(2 : ℝ) - ((m - i : ℕ) : ℝ)) =
          cylR y ^ (-(4 : ℝ) - (m : ℝ)) := by
        rw [← Real.rpow_add hyW.2]
        congr 1
        rw [Nat.cast_sub hi']
        ring
      have hprod : ‖iteratedFDeriv ℝ i (xjG ν χy) y‖ * ‖iteratedFDeriv ℝ (m - i) (streamPsi Z) y‖ ≤
          ((|C2| * |C1|) * B) * cylR y ^ (-(4 : ℝ) - (m : ℝ)) := by
        have h1' := mul_le_mul hgb hψb (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (xj_cylR_nonneg y) _))
        calc _ ≤ _ := h1'
          _ = ((|C2| * |C1|) * B) *
              (cylR y ^ (-(2 : ℝ) - (i : ℝ)) * cylR y ^ (-(2 : ℝ) - ((m - i : ℕ) : ℝ))) := by
            ring
          _ = _ := by rw [hexp]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    -- the two Leibniz bounds
    have hXb : ‖iteratedFDerivWithin ℝ m (fun w => xjPhi ν χy w • Z w) (xjWReg ν) y‖ ≤
        2 ^ m * (|C2| * B * cylR y ^ (-(4 : ℝ) - (m : ℝ))) := by
      have hL := norm_iteratedFDerivWithin_smul_le hφW hZW huniq hyW (n := m)
        (by exact_mod_cast hm)
      exact (hL.trans (Finset.sum_le_sum termA)).trans
        (le_of_eq (xj_sum_choose_mul m _))
    have hYb : ‖iteratedFDerivWithin ℝ m (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
        (xjWReg ν) y‖ ≤
        2 ^ m * ((|C2| * |C1|) * B * cylR y ^ (-(4 : ℝ) - (m : ℝ))) := by
      have hcomp : (fun w => (xjG ν χy w * streamPsi Z w) • xjEz) =
          (ContinuousLinearMap.toSpanSingleton ℝ xjEz) ∘
            (fun w => xjG ν χy w * streamPsi Z w) := by
        funext w
        simp [ContinuousLinearMap.toSpanSingleton_apply]
      have hcomp' := ContinuousLinearMap.norm_iteratedFDerivWithin_comp_left
        (ContinuousLinearMap.toSpanSingleton ℝ xjEz) hgΨY huniq hyW (n := m)
        (by exact_mod_cast hm)
      rw [ContinuousLinearMap.norm_toSpanSingleton] at hcomp'
      have hG1 : ‖iteratedFDerivWithin ℝ m (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
          (xjWReg ν) y‖ ≤ ‖iteratedFDerivWithin ℝ m (fun w => xjG ν χy w * streamPsi Z w)
          (xjWReg ν) y‖ := by
        rw [hcomp]
        exact hcomp'.trans (mul_le_of_le_one_left (norm_nonneg _) xj_norm_xjEz_le)
      have hL := norm_iteratedFDerivWithin_mul_le hgW hΨW huniq hyW (n := m)
        (by exact_mod_cast hm)
      exact hG1.trans ((hL.trans (Finset.sum_le_sum termB)).trans
        (le_of_eq (xj_sum_choose_mul m _)))
    -- assemble
    have hD : iteratedFDeriv ℝ m (streamCut ν 1 χy Z) y =
        iteratedFDerivWithin ℝ m (streamCut ν 1 χy Z) (xjWReg ν) y :=
      (xj_iterWithin_eq hopen hyW (streamCut ν 1 χy Z) m).symm
    rw [hD, xj_stream_eq, iteratedFDerivWithin_add_apply hA1 hB1 huniq hyW]
    have h2m : (2 : ℝ) ^ m ≤ 128 := by
      calc (2 : ℝ) ^ m ≤ 2 ^ 7 := pow_le_pow_right₀ (by norm_num) hm
        _ = 128 := by norm_num
    have hKnn : 0 ≤ (|C2| + |C2| * |C1|) * B * cylR y ^ (-(4 : ℝ) - (m : ℝ)) :=
      mul_nonneg (mul_nonneg (by positivity) hB) (Real.rpow_nonneg (xj_cylR_nonneg y) _)
    calc ‖iteratedFDerivWithin ℝ m (fun w => xjPhi ν χy w • Z w) (xjWReg ν) y +
          iteratedFDerivWithin ℝ m (fun w => (xjG ν χy w * streamPsi Z w) • xjEz) (xjWReg ν) y‖
        ≤ ‖iteratedFDerivWithin ℝ m (fun w => xjPhi ν χy w • Z w) (xjWReg ν) y‖ +
          ‖iteratedFDerivWithin ℝ m (fun w => (xjG ν χy w * streamPsi Z w) • xjEz)
            (xjWReg ν) y‖ := norm_add_le _ _
      _ ≤ 2 ^ m * (|C2| * B * cylR y ^ (-(4 : ℝ) - (m : ℝ))) +
          2 ^ m * ((|C2| * |C1|) * B * cylR y ^ (-(4 : ℝ) - (m : ℝ))) :=
          add_le_add hXb hYb
      _ = 2 ^ m * ((|C2| + |C2| * |C1|) * B * cylR y ^ (-(4 : ℝ) - (m : ℝ))) := by ring
      _ ≤ 128 * ((|C2| + |C2| * |C1|) * B * cylR y ^ (-(4 : ℝ) - (m : ℝ))) :=
          mul_le_mul_of_nonneg_right h2m hKnn
      _ = 128 * (|C2| + |C2| * |C1|) * B * cylR y ^ (-(4 : ℝ) - (m : ℝ)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
