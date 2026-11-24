import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.KopEq

/-!
# `PartIII-b:C/inst/11/3/3`: `HAcPieceKop` from the lattice `L²` bound

Source `the November 2 reference manuscript`:
lattice sums 4973-4975, the operator `𝒦 = η∂_η + 2s∂_s` 4979-4980, size 5009-5016, 5063-5079.

Proved here: the closed form of `KopC` as a lattice sum (x-derivative `psipAC_fderiv`, s-derivative
`psipAC_hasDerivAt`), the pointwise bound `|KopC| ≤ 50 (|C| + |D|) · latG`, measurability of `KopC`
and of the lattice majorant `latG`, and `hAcPieceKop_of (h : LatticeL2) : HAcPieceKop`.
The single remaining analytic input is `LatticeL2`, the uniform `L²(avgμ)` bound of the Gaussian
lattice sum `latG` (stated as a `Prop`); it is reduced below (`latticeL2_of`) to four elementary lemmas.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The Gaussian lattice majorant `Σ_n (1+|x_n|)^4 e^{-|x_n|²/(4a)}`, `a = 1+νs`. -/
def latG (ν s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' n : ℤ, (1 + ‖xj ν n x‖) ^ 4 * Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))

/-- Source 5063-5079: the lattice majorant is bounded in `L²(avgμ)` uniformly for
`a = 1+νs ∈ [1, 2.1]`, `c = ν⁻² ≥ 1` (Cauchy-Schwarz over `n` with Gaussian weights, one Gaussian
integral, the cell integral unfolds to the plane for `c ≥ 1`). -/
def LatticeL2 : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ ν s : ℝ, 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν →
    ∫⁻ x, ENNReal.ofReal (latG ν s x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤ ENNReal.ofReal K

theorem latG_term_summable (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (x : ℝ × ℝ) :
    Summable (fun n : ℤ => (1 + ‖xj ν n x‖) ^ 4 * Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hα : 0 < 1 / (4 * ageA ν s) := div_pos one_pos (by linarith)
  have hc : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hu := (sp_poly4_summable x.1 (1 / (4 * ageA ν s)) (cOf ν) hα hc).mul_left (1 * (1 + |x.2|) ^ 4)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hu
  have := sp_major ν s (ageA ν s) 1 1 x n ha1 le_rfl (by norm_num) le_rfl (by norm_num)
  simpa [mul_assoc] using this

theorem latG_nonneg (ν s : ℝ) (x : ℝ × ℝ) : 0 ≤ latG ν s x :=
  tsum_nonneg fun n => by positivity

theorem measurable_tsum_int {α : Type*} [MeasurableSpace α] (f : ℤ → α → ℝ)
    (hf : ∀ n, Measurable (f n)) (hs : ∀ x, Summable (fun n => f n x)) :
    Measurable (fun x => ∑' n, f n x) := by
  have e : ∀ x, ∑' n, f n x = ∑' m : ℕ, f (Equiv.intEquivNat.symm m) x := fun x =>
    (Equiv.tsum_eq Equiv.intEquivNat.symm (fun n => f n x)).symm
  simp_rw [e]
  refine measurable_of_tendsto_metrizable (f := fun (N : ℕ) x =>
    ∑ m ∈ Finset.range N, f (Equiv.intEquivNat.symm m) x)
    (fun N => Finset.measurable_sum _ fun m _ => hf _) ?_
  rw [tendsto_pi_nhds]
  intro x
  have : Summable (fun m : ℕ => f (Equiv.intEquivNat.symm m) x) :=
    (Equiv.summable_iff Equiv.intEquivNat.symm).2 (hs x)
  exact this.hasSum.tendsto_sum_nat


theorem latG_measurable (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) : Measurable (latG ν s) := by
  unfold latG
  refine measurable_tsum_int _ (fun n => ?_) (fun x => latG_term_summable ν s hν hs x)
  unfold xj sq2
  fun_prop

/-- The `x`-derivative of the lattice sum `ψ^p` is the sum of the term derivatives. -/
theorem psipAC_hasFDerivAt (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (M : Mat3) (x : ℝ × ℝ) :
    HasFDerivAt (psipAC ν s M)
      (∑' n : ℤ, fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x) x := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hu := ubd_summable ν s ha1 x M hν
  have hval : ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 → ∀ v : ℝ × ℝ,
      ‖psiPhiD ν s M (xj ν j z) v‖ ≤ ubd ν s x M j * ‖v‖ := by
    intro j z hz v
    have h1 := psiPhiD_bound ν s ha1 M (xj ν j z) v
    have h2 := ball_geom ν s ha1 x z hz j
    have hn := norm_nonneg v
    have h6 : 0 ≤ 6 * Kmat M := by have := Kmat_nonneg M; linarith
    have h3 : 6 * Kmat M * ‖v‖ * ((1 + ‖xj ν j z‖) ^ 3 *
        Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)))
        ≤ 6 * Kmat M * ‖v‖ * (64 * (1 + |x.2|) ^ 3 * Real.exp (1 / (4 * ageA ν s)) *
          ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
            Real.exp (-(1 / (8 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2))) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg h6 hn)
    refine h1.trans (h3.trans (le_of_eq ?_))
    unfold ubd
    ring
  have hfb : ∀ (j : ℤ) (z : ℝ × ℝ), ‖z - x‖ < 1 →
      ‖fderiv ℝ (fun w => psiPhi ν s M (xj ν j w)) z‖ ≤ ubd ν s x M j := by
    intro j z hz
    apply ContinuousLinearMap.opNorm_le_bound _ (ubd_nonneg ν s x M j)
    intro v
    rw [fderiv_term]
    exact hval j z hz v
  have hf0 : Summable (fun n : ℤ => psiPhi ν s M (xj ν n x)) := psiPhi_summable ν s M x hν hs
  have hF : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      HasFDerivAt (fun w => psiPhi ν s M (xj ν n w))
        (fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z) z :=
    fun n z _ => (term_diff ν s M n z).hasFDerivAt
  have hbound : ∀ (n : ℤ) (z : ℝ × ℝ), z ∈ Metric.ball x 1 →
      ‖fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z‖ ≤ ubd ν s x M n :=
    fun n z hz => hfb n z (mem_ball_iff_norm.mp hz)
  have key := hasFDerivAt_tsum_of_isPreconnected
    (f := fun n (w : ℝ × ℝ) => psiPhi ν s M (xj ν n w))
    (f' := fun n z => fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) z)
    (u := ubd ν s x M) hu Metric.isOpen_ball (convex_ball x 1).isPreconnected hF hbound
    (Metric.mem_ball_self one_pos) hf0 (Metric.mem_ball_self one_pos)
  have e : psipAC ν s M = fun w => ∑' n : ℤ, psiPhi ν s M (xj ν n w) :=
    funext fun w => psipAC_eq_sum ν s M w
  rw [e]
  exact key

theorem psipAC_fderiv_ei1 (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (M : Mat3) (x : ℝ × ℝ) :
    fderiv ℝ (psipAC ν s M) x (ei 1) = ∑' n : ℤ, psiPhiD ν s M (xj ν n x) (ei 1) := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hu := ubd_summable ν s ha1 x M hν
  rw [(psipAC_hasFDerivAt ν s hν hs M x).fderiv]
  have hsum : Summable (fun n : ℤ => fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x) := by
    refine Summable.of_norm_bounded hu (fun n => ?_)
    apply ContinuousLinearMap.opNorm_le_bound _ (ubd_nonneg ν s x M n)
    intro v
    rw [fderiv_term]
    have h1 := psiPhiD_bound ν s ha1 M (xj ν n x) v
    have h2 := ball_geom ν s ha1 x x (by simp) n
    have hn := norm_nonneg v
    have h6 : 0 ≤ 6 * Kmat M := by have := Kmat_nonneg M; linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg h6 hn)
    refine h1.trans (h3.trans (le_of_eq ?_))
    unfold ubd
    ring
  have hh := (ContinuousLinearMap.apply ℝ ℝ (ei 1)).hasSum hsum.hasSum
  have h2 : (∑' n : ℤ, fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x) (ei 1)
      = ∑' n : ℤ, fderiv ℝ (fun w => psiPhi ν s M (xj ν n w)) x (ei 1) := hh.tsum_eq.symm
  rw [h2]
  exact tsum_congr fun n => by rw [fderiv_term]


theorem abs_entry_le_frob (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem Kmat_le_frob (M : Mat3) : Kmat M ≤ 4 * frob M := by
  unfold Kmat
  linarith [abs_entry_le_frob M 0 0, abs_entry_le_frob M 0 2, abs_entry_le_frob M 2 0,
    abs_entry_le_frob M 2 2]

theorem abs_tsum_le_of_le (f g : ℤ → ℝ) (B : ℝ) (hg : Summable g) (h : ∀ n, |f n| ≤ B * g n) :
    |∑' n, f n| ≤ B * ∑' n, g n := by
  have hs : Summable (fun n => |f n|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) h (hg.mul_left B)
  calc |∑' n, f n| = ‖∑' n, f n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs)
    _ = ∑' n, |f n| := by simp [Real.norm_eq_abs]
    _ ≤ ∑' n, B * g n := hs.tsum_le_tsum h (hg.mul_left B)
    _ = B * ∑' n, g n := tsum_mul_left

theorem KopC_formula (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (C D : Mat3) (x : ℝ × ℝ) :
    KopC ν s C D x = x.2 * (∑' n : ℤ, psiPhiD ν s C (xj ν n x) (ei 1)) +
      2 * (s * (∑' n : ℤ, sV ν (xj ν n x) C 0 s) + ∑' n : ℤ, psiPhi ν s D (xj ν n x)) := by
  unfold KopC
  rw [psipAC_fderiv_ei1 ν s hν hs C x, (psipAC_hasDerivAt ν s hν hs C x).deriv,
    psipAC_eq_sum ν s D x]

/-- Pointwise bound: `|𝒦ψ^p| ≤ 50 (|C| + |D|) Σ_n (1+|x_n|)^4 e^{-|x_n|²/(4a)}` for `νs ≤ 1.1`. -/
theorem KopC_abs_le (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (hνs : s ≤ (11 / 10) / ν)
    (C D : Mat3) (x : ℝ × ℝ) :
    |KopC ν s C D x| ≤ 50 * (frob C + frob D) * latG ν s x := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hνs' : ν * s ≤ 11 / 10 := by
    have := (le_div_iff₀ hν).1 hνs
    linarith
  have hfC : 0 ≤ frob C := Real.sqrt_nonneg _
  have hfD : 0 ≤ frob D := Real.sqrt_nonneg _
  have hg : Summable (fun n : ℤ => (1 + ‖xj ν n x‖) ^ 4 *
      Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := latG_term_summable ν s hν hs x
  have hR : ∀ n : ℤ, (0:ℝ) ≤ 1 + ‖xj ν n x‖ := fun n => by linarith [norm_nonneg (xj ν n x)]
  have hE : ∀ n : ℤ, 0 ≤ Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)) := fun n =>
    (Real.exp_pos _).le
  have hR34 : ∀ n : ℤ, (1 + ‖xj ν n x‖) ^ 3 ≤ (1 + ‖xj ν n x‖) ^ 4 := fun n =>
    pow_le_pow_right₀ (by linarith [norm_nonneg (xj ν n x)]) (by norm_num)
  have hei : ‖ei 1‖ = 1 := by simp [ei, Prod.norm_def]
  -- term 1
  have b1 : |x.2 * ∑' n : ℤ, psiPhiD ν s C (xj ν n x) (ei 1)| ≤
      (6 * Kmat C) * latG ν s x := by
    have hsum : Summable (fun n : ℤ => psiPhiD ν s C (xj ν n x) (ei 1)) := by
      refine Summable.of_norm_bounded (hg.mul_left (6 * Kmat C)) (fun n => ?_)
      have h1 := psiPhiD_bound ν s ha1 C (xj ν n x) (ei 1)
      rw [hei] at h1
      refine h1.trans ?_
      have := mul_le_mul_of_nonneg_right (hR34 n) (hE n)
      have hK := Kmat_nonneg C
      nlinarith [mul_nonneg hK (hE n), mul_nonneg hK (mul_nonneg (pow_nonneg (hR n) 3) (hE n))]
    rw [← tsum_mul_left]
    unfold latG
    refine abs_tsum_le_of_le _ _ _ hg (fun n => ?_)
    rw [abs_mul]
    have h1 := psiPhiD_bound ν s ha1 C (xj ν n x) (ei 1)
    rw [hei, Real.norm_eq_abs] at h1
    have h2 : |x.2| ≤ 1 + ‖xj ν n x‖ := by
      have := abs_snd_le' (xj ν n x)
      have e : (xj ν n x).2 = x.2 := rfl
      rw [e] at this
      linarith
    have hK := Kmat_nonneg C
    calc |x.2| * |psiPhiD ν s C (xj ν n x) (ei 1)|
        ≤ (1 + ‖xj ν n x‖) * (6 * Kmat C * 1 * ((1 + ‖xj ν n x‖) ^ 3 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)))) :=
          mul_le_mul h2 h1 (abs_nonneg _) (hR n)
      _ = 6 * Kmat C * ((1 + ‖xj ν n x‖) ^ 4 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := by ring
  -- term 2
  have b2 : |s * ∑' n : ℤ, sV ν (xj ν n x) C 0 s| ≤ (11 / 10 * frob C * 10) * latG ν s x := by
    rw [← tsum_mul_left]
    unfold latG
    refine abs_tsum_le_of_le _ _ _ hg (fun n => ?_)
    rw [abs_mul, abs_of_pos hs]
    have h1 := sV_bound ν hν (xj ν n x) (frob C) 0 C 0 s hs
      (fun i j => abs_entry_le_frob C i j) (fun i j => by simp)
    calc s * |sV ν (xj ν n x) C 0 s|
        ≤ s * ((10 * ν * frob C + 8 * 0) * (1 + ‖xj ν n x‖) ^ 4 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) :=
          mul_le_mul_of_nonneg_left h1 hs.le
      _ = (10 * (ν * s) * frob C) * ((1 + ‖xj ν n x‖) ^ 4 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := by ring
      _ ≤ (11 / 10 * frob C * 10) * ((1 + ‖xj ν n x‖) ^ 4 *
            Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hνs' hfC]
  -- term 3
  have b3 : |∑' n : ℤ, psiPhi ν s D (xj ν n x)| ≤ (2 * Kmat D) * latG ν s x := by
    unfold latG
    refine abs_tsum_le_of_le _ _ _ hg (fun n => ?_)
    have h1 := psiPhi_abs_le ν s ha1 D (xj ν n x)
    refine h1.trans ?_
    have hK := Kmat_nonneg D
    have := mul_le_mul_of_nonneg_right (hR34 n) (hE n)
    nlinarith [mul_nonneg hK (hE n)]
  have hlat := latG_nonneg ν s x
  have hKD := Kmat_le_frob D
  have hKC := Kmat_le_frob C
  have hs1 : |KopC ν s C D x| ≤ |x.2 * ∑' n : ℤ, psiPhiD ν s C (xj ν n x) (ei 1)| +
      2 * |s * ∑' n : ℤ, sV ν (xj ν n x) C 0 s| + 2 * |∑' n : ℤ, psiPhi ν s D (xj ν n x)| := by
    rw [KopC_formula ν s hν hs C D x]
    have := abs_add_le (x.2 * ∑' n : ℤ, psiPhiD ν s C (xj ν n x) (ei 1))
      (2 * (s * (∑' n : ℤ, sV ν (xj ν n x) C 0 s) + ∑' n : ℤ, psiPhi ν s D (xj ν n x)))
    have h2 := abs_add_le (s * (∑' n : ℤ, sV ν (xj ν n x) C 0 s)) (∑' n : ℤ, psiPhi ν s D (xj ν n x))
    have h3 : |2 * (s * (∑' n : ℤ, sV ν (xj ν n x) C 0 s) + ∑' n : ℤ, psiPhi ν s D (xj ν n x))|
        = 2 * |s * (∑' n : ℤ, sV ν (xj ν n x) C 0 s) + ∑' n : ℤ, psiPhi ν s D (xj ν n x)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith
  have hKCnn := Kmat_nonneg C
  have hKDnn := Kmat_nonneg D
  nlinarith [mul_le_mul_of_nonneg_right hKC hlat, mul_le_mul_of_nonneg_right hKD hlat,
    mul_nonneg hfC hlat, mul_nonneg hfD hlat]

theorem psiPhiD_ei_summable (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (C : Mat3) (x : ℝ × ℝ) :
    Summable (fun n : ℤ => psiPhiD ν s C (xj ν n x) (ei 1)) := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hei : ‖ei 1‖ = 1 := by simp [ei, Prod.norm_def]
  have hg := latG_term_summable ν s hν hs x
  refine Summable.of_norm_bounded (hg.mul_left (6 * Kmat C)) (fun n => ?_)
  have h1 := psiPhiD_bound ν s ha1 C (xj ν n x) (ei 1)
  rw [hei] at h1
  refine h1.trans ?_
  have hE := (Real.exp_pos (-(sq2 (xj ν n x)) / (4 * ageA ν s))).le
  have hR34 : (1 + ‖xj ν n x‖) ^ 3 ≤ (1 + ‖xj ν n x‖) ^ 4 :=
    pow_le_pow_right₀ (by linarith [norm_nonneg (xj ν n x)]) (by norm_num)
  have hK := Kmat_nonneg C
  have := mul_le_mul_of_nonneg_right hR34 hE
  nlinarith [mul_nonneg hK hE, mul_le_mul_of_nonneg_left this hK]

theorem sV_summable (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (C : Mat3) (x : ℝ × ℝ) :
    Summable (fun n : ℤ => sV ν (xj ν n x) C 0 s) := by
  have hg := latG_term_summable ν s hν hs x
  refine Summable.of_norm_bounded (hg.mul_left (10 * ν * frob C)) (fun n => ?_)
  have h1 := sV_bound ν hν (xj ν n x) (frob C) 0 C 0 s hs
    (fun i j => abs_entry_le_frob C i j) (fun i j => by simp)
  rw [Real.norm_eq_abs]
  refine h1.trans (le_of_eq ?_)
  ring

theorem KopC_measurable (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (C D : Mat3) :
    Measurable (KopC ν s C D) := by
  have e : KopC ν s C D = fun x => x.2 * (∑' n : ℤ, psiPhiD ν s C (xj ν n x) (ei 1)) +
      2 * (s * (∑' n : ℤ, sV ν (xj ν n x) C 0 s) + ∑' n : ℤ, psiPhi ν s D (xj ν n x)) :=
    funext fun x => KopC_formula ν s hν hs C D x
  rw [e]
  have m1 : Measurable (fun x : ℝ × ℝ => ∑' n : ℤ, psiPhiD ν s C (xj ν n x) (ei 1)) := by
    refine measurable_tsum_int _ (fun n => ?_) (fun x => psiPhiD_ei_summable ν s hν hs C x)
    unfold psiPhiD xj sq2 merApply merTrace ei
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    fun_prop
  have m2 : Measurable (fun x : ℝ × ℝ => ∑' n : ℤ, sV ν (xj ν n x) C 0 s) := by
    refine measurable_tsum_int _ (fun n => ?_) (fun x => sV_summable ν s hν hs C x)
    unfold sV xj sq2
    fun_prop
  have m3 : Measurable (fun x : ℝ × ℝ => ∑' n : ℤ, psiPhi ν s D (xj ν n x)) := by
    refine measurable_tsum_int _ (fun n => ?_) (fun x => psiPhi_summable ν s D x hν hs)
    unfold psiPhi xj sq2 merApply merTrace
    fun_prop
  exact (measurable_snd.mul m1).add (((m2.const_mul s).add m3).const_mul 2)

/-- `HAcPieceKop` from the lattice `L²` bound `LatticeL2` (source 5063-5079). -/
theorem hAcPieceKop_of (h : LatticeL2) : HAcPieceKop := by
  obtain ⟨K, hK0, hK⟩ := h
  refine ⟨50 * Real.sqrt K, by positivity, fun ν s hν hν1 hs hsν C D => ?_⟩
  refine ⟨KopC_measurable ν s hν hs C D, ?_⟩
  have hpt : ∀ x, ENNReal.ofReal (‖KopC ν s C D x‖ ^ 2) ≤
      ENNReal.ofReal ((50 * (frob C + frob D)) ^ 2) * ENNReal.ofReal (latG ν s x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (sq_nonneg _), Real.norm_eq_abs]
    apply ENNReal.ofReal_le_ofReal
    have := KopC_abs_le ν s hν hs hsν C D x
    rw [← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ∫⁻ x, ENNReal.ofReal (‖KopC ν s C D x‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν))
      ≤ ∫⁻ x, ENNReal.ofReal ((50 * (frob C + frob D)) ^ 2) * ENNReal.ofReal (latG ν s x ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := lintegral_mono hpt
    _ = ENNReal.ofReal ((50 * (frob C + frob D)) ^ 2) *
          ∫⁻ x, ENNReal.ofReal (latG ν s x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((50 * (frob C + frob D)) ^ 2) * ENNReal.ofReal K :=
        by gcongr; exact hK ν s hν hν1 hs hsν
    _ = ENNReal.ofReal ((50 * Real.sqrt K) ^ 2 * (frob C + frob D) ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        rw [mul_pow, mul_pow, Real.sq_sqrt hK0]
        ring


/-! ## Reduction of `LatticeL2` to four elementary lemmas -/

/-- Lemma 1 (unfolding of the cell integral; source 5063-5079, tiling of the plane by the cells
`cell c + (n c, 0)`): the lattice sum of translates integrates over one cell to the plane integral. -/
def LatUnfold : Prop :=
  ∀ c : ℝ, 0 < c → ∀ F : ℝ × ℝ → ℝ≥0∞, Measurable F →
    ∫⁻ x in UnforcedLeray.Cyl.cell c, ∑' n : ℤ, F (x.1 - (n : ℝ) * c, x.2) = ∫⁻ y, F y

/-- Lemma 2 (uniform Gaussian weight sum over a lattice of spacing `c ≥ 1`, `a ∈ [1, 2.1]`; source
5063-5079, the weights of the Cauchy-Schwarz step). -/
def LatWeight : Prop :=
  ∃ H : ℝ, 0 ≤ H ∧ ∀ c a t : ℝ, 1 ≤ c → 1 ≤ a → a ≤ 21 / 10 →
    Summable (fun n : ℤ => Real.exp (-(t - (n : ℝ) * c) ^ 2 / (8 * a))) ∧
      ∑' n : ℤ, Real.exp (-(t - (n : ℝ) * c) ^ 2 / (8 * a)) ≤ H

/-- Lemma 3 (one Gaussian integral, uniform for `a ∈ [1, 2.1]`; source 5063-5079). -/
def GaussInt8 : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ, 1 ≤ a → a ≤ 21 / 10 →
    ∫⁻ y : ℝ × ℝ, ENNReal.ofReal ((1 + ‖y‖) ^ 8 * Real.exp (-(3 / 8) * sq2 y / a))
      ≤ ENNReal.ofReal K

/-- Lemma 4 (Cauchy-Schwarz for `ℤ`-indexed sums in `[0, ∞]`). -/
def TsumCS : Prop :=
  ∀ g h : ℤ → ℝ, (∀ n, 0 ≤ g n) → (∀ n, 0 < h n) →
    (∑' n, ENNReal.ofReal (g n)) ^ 2 ≤
      (∑' n, ENNReal.ofReal (h n)) * ∑' n, ENNReal.ofReal (g n ^ 2 / h n)

theorem latticeL2_of (h1 : LatUnfold) (h2 : LatWeight) (h3 : GaussInt8) (h4 : TsumCS) :
    LatticeL2 := by
  obtain ⟨H, hH0, hH⟩ := h2
  obtain ⟨K, hK0, hK⟩ := h3
  refine ⟨H * K, mul_nonneg hH0 hK0, fun ν s hν hν1 hs hsν => ?_⟩
  have hνs' : ν * s ≤ 11 / 10 := by
    have := (le_div_iff₀ hν).1 hsν
    linarith
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by unfold ageA; linarith
  have ha0 : 0 < ageA ν s := by linarith
  have hc0 : 0 < cOf ν := by unfold cOf; exact inv_pos.mpr (pow_pos hν 2)
  have hc1 : 1 ≤ cOf ν := by
    unfold cOf
    exact one_le_inv₀ (pow_pos hν 2) |>.2 (pow_le_one₀ hν.le hν1)
  set a := ageA ν s with ha
  set c := cOf ν with hc
  let F : ℝ × ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal
    (((1 + ‖y‖) ^ 4 * Real.exp (-(sq2 y) / (4 * a))) ^ 2 / Real.exp (-(y.1) ^ 2 / (8 * a)))
  have hFm : Measurable F := by
    show Measurable (fun y : ℝ × ℝ => ENNReal.ofReal
      (((1 + ‖y‖) ^ 4 * Real.exp (-(sq2 y) / (4 * a))) ^ 2 / Real.exp (-(y.1) ^ 2 / (8 * a))))
    unfold sq2
    fun_prop
  have hFle : ∀ y : ℝ × ℝ, F y ≤
      ENNReal.ofReal ((1 + ‖y‖) ^ 8 * Real.exp (-(3 / 8) * sq2 y / a)) := by
    intro y
    apply ENNReal.ofReal_le_ofReal
    have e1 : (Real.exp (-(sq2 y) / (4 * a))) ^ 2 = Real.exp (-(sq2 y) / (2 * a)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      field_simp
      ring
    have hex : -(sq2 y) / (2 * a) - (-(y.1) ^ 2 / (8 * a)) ≤ -(3 / 8) * sq2 y / a := by
      have h0 : -(3 / 8) * sq2 y / a - (-(sq2 y) / (2 * a) - (-(y.1) ^ 2 / (8 * a)))
          = (y.2 ^ 2 / 8) / a := by
        unfold sq2
        field_simp
        ring
      have h2 : 0 ≤ (y.2 ^ 2 / 8) / a := by positivity
      linarith
    calc ((1 + ‖y‖) ^ 4 * Real.exp (-(sq2 y) / (4 * a))) ^ 2 / Real.exp (-(y.1) ^ 2 / (8 * a))
        = (1 + ‖y‖) ^ 8 * ((Real.exp (-(sq2 y) / (4 * a))) ^ 2 / Real.exp (-(y.1) ^ 2 / (8 * a))) := by
          ring
      _ = (1 + ‖y‖) ^ 8 * Real.exp (-(sq2 y) / (2 * a) - (-(y.1) ^ 2 / (8 * a))) := by
          rw [e1, Real.exp_sub]
      _ ≤ (1 + ‖y‖) ^ 8 * Real.exp (-(3 / 8) * sq2 y / a) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hex) (by positivity)
  have hpt : ∀ x : ℝ × ℝ, ENNReal.ofReal (latG ν s x ^ 2) ≤
      ENNReal.ofReal H * ∑' n : ℤ, F (x.1 - (n : ℝ) * c, x.2) := by
    intro x
    obtain ⟨hWs, hWH⟩ := hH c a x.1 hc1 ha1 ha2
    have hgs := latG_term_summable ν s hν hs x
    have hg0 : ∀ n : ℤ, 0 ≤ (1 + ‖xj ν n x‖) ^ 4 *
        Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)) := fun n => by positivity
    have e1 : ENNReal.ofReal (latG ν s x ^ 2) = (∑' n : ℤ, ENNReal.ofReal
        ((1 + ‖xj ν n x‖) ^ 4 * Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)))) ^ 2 := by
      rw [ENNReal.ofReal_pow (latG_nonneg ν s x), latG, ENNReal.ofReal_tsum_of_nonneg hg0 hgs]
    have hcs := h4 (fun n : ℤ => (1 + ‖xj ν n x‖) ^ 4 *
        Real.exp (-(sq2 (xj ν n x)) / (4 * ageA ν s)))
      (fun n : ℤ => Real.exp (-(x.1 - (n : ℝ) * c) ^ 2 / (8 * a))) hg0
      (fun n => Real.exp_pos _)
    rw [e1]
    refine hcs.trans (mul_le_mul' ?_ le_rfl)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hWs]
    exact ENNReal.ofReal_le_ofReal hWH
  have hint : ∫⁻ y, F y ≤ ENNReal.ofReal K :=
    (lintegral_mono hFle).trans (hK a ha1 ha2)
  rw [UnforcedLeray.Cyl.lintegral_avgμ]
  calc ENNReal.ofReal c⁻¹ * ∫⁻ x in UnforcedLeray.Cyl.cell c, ENNReal.ofReal (latG ν s x ^ 2)
      ≤ ENNReal.ofReal c⁻¹ * ∫⁻ x in UnforcedLeray.Cyl.cell c,
          ENNReal.ofReal H * ∑' n : ℤ, F (x.1 - (n : ℝ) * c, x.2) :=
        mul_le_mul' le_rfl (lintegral_mono hpt)
    _ = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal H *
          ∫⁻ x in UnforcedLeray.Cyl.cell c, ∑' n : ℤ, F (x.1 - (n : ℝ) * c, x.2)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal H * ∫⁻ y, F y) := by
        rw [h1 c hc0 F hFm]
    _ ≤ ENNReal.ofReal 1 * (ENNReal.ofReal H * ENNReal.ofReal K) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ hc1))
          (mul_le_mul' le_rfl hint)
    _ = ENNReal.ofReal (H * K) := by
        rw [ENNReal.ofReal_one, one_mul, ENNReal.ofReal_mul hH0]

/-- `HAcPieceKop` from the four elementary lattice lemmas (source 4979-4980, 5063-5079). -/
theorem hAcPieceKop_of_lemmas (h1 : LatUnfold) (h2 : LatWeight) (h3 : GaussInt8)
    (h4 : TsumCS) : HAcPieceKop :=
  hAcPieceKop_of (latticeL2_of h1 h2 h3 h4)

end UnforcedLeray.Short.PartIIIb.Concrete
