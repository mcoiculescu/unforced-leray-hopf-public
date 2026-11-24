import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Units.B0238
import UnforcedLeray.Units.B0277
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Part III-a, `PartIII-a:T21/2/6/10`: the error part of the rescaled vorticity

Source of record: `the November 2 reference manuscript`, lines 2866-2873 (interpolate
the Gaussian-small unweighted norm with a larger weighted norm, absorb fixed powers), 290-303.

With `c = ν⁻²`, `a = clockA ν r`, `x = ν⁻¹`, `z₀ = (√a y₁, √a y₂)`, `F = ‖D^{j+1}(v - V_c^p)(r)(z₀)‖`:
* `F ≤ C x e^{-b c²/a}` (sup part of `PartI.TrainComparison`, pointwise);
* `(1+z₀₂²)^{2k} F ≤ Q x^{M}` (the polynomial weighted bounds of the train and of `V_c^p`);
* `⟨y⟩^{2k}‖D^j curl(v - V_c^p)(z₀)‖ ≤ 2 ⟨y⟩^{2k} F` (`CurlJetBound`), and `⟨y⟩² ≤ (1+c²)(1+z₀₂²)`.
Squaring and using `c² = x⁴`, `e^{-b c²/a} ≤ e^{-bx}`, `ExpPolyAbsorb` gives the bound by
`C a^{-(2+j/2)}`.  The four orders `j = 0,…,3` are combined by a sum of constants and a minimum of
the threshold `ν`s.

Statement: `vortErrMoving_of`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The train period exponent `ν^{-2}` as a named function (definitionally `ν ^ (-2 : ℝ)`). -/
noncomputable def vortC (ν : ℝ) : ℝ := ν ^ (-2 : ℝ)

theorem vort_c_eq {ν : ℝ} (hν : 0 < ν) : vortC ν = (ν⁻¹) ^ 2 := by
  unfold vortC
  rw [Real.rpow_neg hν.le, Real.rpow_two, inv_pow]

/-- Clock facts on the region `θ(r) ≥ 1`, `ν ≤ 1`: `1 ≤ a ≤ ν⁻¹`, `1 + r ≤ 2ν⁻²`. -/
theorem vort_clock {ν r : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hr : 0 ≤ r)
    (hθ : 1 ≤ clockTheta ν r) :
    1 ≤ clockA ν r ∧ clockA ν r ≤ ν⁻¹ ∧ 1 + r ≤ 2 * (ν⁻¹) ^ 2 ∧ 1 ≤ ν⁻¹ := by
  have hνne : ν ≠ 0 := hν.ne'
  have ha1 : 1 ≤ clockA ν r := by unfold clockA; nlinarith [mul_nonneg hν.le hr]
  have hapos : 0 < ν * clockA ν r := by nlinarith
  have hνa : ν * clockA ν r ≤ 1 := by
    unfold clockTheta at hθ
    exact (one_le_inv₀ hapos).mp hθ
  have hx1 : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).mpr hν1
  have hx0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have ha2 : clockA ν r ≤ ν⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hνa hx0
    have e : ν * clockA ν r * ν⁻¹ = clockA ν r := by field_simp
    linarith
  have hr2 : r ≤ (ν⁻¹) ^ 2 := by
    have h1 : ν * r ≤ ν⁻¹ := by unfold clockA at ha2; nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 hx0
    have e2 : ν * r * ν⁻¹ = r := by field_simp
    calc r = ν * r * ν⁻¹ := e2.symm
      _ ≤ ν⁻¹ * ν⁻¹ := h2
      _ = (ν⁻¹) ^ 2 := (sq _).symm
  have hx2 : 1 ≤ (ν⁻¹) ^ 2 := one_le_pow₀ hx1
  exact ⟨ha1, ha2, by linarith, hx1⟩

/-- The cell relation `y₁² ≤ c²` and the weight comparison `⟨y⟩² ≤ (1+c²)(1+z₂²)`. -/
theorem vort_hjb {c a y1 y2 z2 : ℝ} (ha1 : 1 ≤ a) (hz2 : z2 = Real.sqrt a * y2)
    (hcell : -(c / Real.sqrt a / 2) ≤ y1 ∧ y1 < c / Real.sqrt a / 2) :
    1 + y1 ^ 2 + y2 ^ 2 ≤ (1 + c ^ 2) * (1 + z2 ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hsq : (c / Real.sqrt a) ^ 2 = c ^ 2 / a := by rw [div_pow, Real.sq_sqrt ha0.le]
  have hz : z2 ^ 2 = a * y2 ^ 2 := by rw [hz2, mul_pow, Real.sq_sqrt ha0.le]
  have hprod : 0 ≤ (c / Real.sqrt a / 2 - y1) * (c / Real.sqrt a / 2 + y1) :=
    mul_nonneg (by linarith [hcell.2]) (by linarith [hcell.1])
  have h1 : y1 ^ 2 ≤ (c / Real.sqrt a) ^ 2 / 4 := by nlinarith [hprod]
  have h3 : 0 ≤ c ^ 2 / a := div_nonneg (sq_nonneg c) ha0.le
  have h2 : c ^ 2 / a ≤ c ^ 2 := div_le_self (sq_nonneg c) ha1
  have h4 : y1 ^ 2 ≤ c ^ 2 := by rw [hsq] at h1; linarith
  have h5 : y2 ^ 2 ≤ z2 ^ 2 := by
    rw [hz]; nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sq_nonneg y2)]
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg z2)]

/-- The Gaussian factor of the sup bound: `Cm x a^{-(5+m)/2} e^{-b c²/a} ≤ |Cm| x e^{-bx}`. -/
theorem vort_E {x a c bm Cm : ℝ} (m : ℕ) (hx1 : 1 ≤ x) (ha1 : 1 ≤ a) (ha2 : a ≤ x)
    (hc : c = x ^ 2) (hbm : 0 < bm) :
    Cm * x * a ^ (-((5 + (m : ℝ)) / 2)) * Real.exp (-(bm * c ^ 2 / a)) ≤
      |Cm| * x * Real.exp (-(bm * x)) := by
  have hx0 : 0 ≤ x := by linarith
  have ha0 : 0 < a := by linarith
  have h1 : a ^ (-((5 + (m : ℝ)) / 2)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos ha1
    apply neg_nonpos.mpr
    positivity
  have hc2 : c ^ 2 = x ^ 4 := by rw [hc]; ring
  have hxa : x * a ≤ c ^ 2 := by
    rw [hc2]
    calc x * a ≤ x * x := mul_le_mul_of_nonneg_left ha2 hx0
      _ = x ^ 2 := by ring
      _ ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  have hbx : bm * x ≤ bm * c ^ 2 / a := by
    rw [le_div_iff₀ ha0]
    calc bm * x * a = bm * (x * a) := by ring
      _ ≤ bm * c ^ 2 := mul_le_mul_of_nonneg_left hxa hbm.le
  have h2 : Real.exp (-(bm * c ^ 2 / a)) ≤ Real.exp (-(bm * x)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hCm' : Cm ≤ |Cm| := le_abs_self Cm
  calc Cm * x * a ^ (-((5 + (m : ℝ)) / 2)) * Real.exp (-(bm * c ^ 2 / a))
      = Cm * (x * a ^ (-((5 + (m : ℝ)) / 2)) * Real.exp (-(bm * c ^ 2 / a))) := by ring
    _ ≤ |Cm| * (x * a ^ (-((5 + (m : ℝ)) / 2)) * Real.exp (-(bm * c ^ 2 / a))) :=
        mul_le_mul_of_nonneg_right hCm' (mul_nonneg (mul_nonneg hx0
          (Real.rpow_nonneg ha0.le _)) (Real.exp_nonneg _))
    _ ≤ |Cm| * (x * 1 * Real.exp (-(bm * x))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left h1 hx0) h2 (Real.exp_nonneg _)
            (mul_nonneg hx0 zero_le_one))
          (abs_nonneg _)
    _ = |Cm| * x * Real.exp (-(bm * x)) := by ring

/-- The first weighted piece: `A ≤ Cp x^N (1+r)^N ≤ |Cp| 2^N x^M` for `M ≥ 3N`. -/
theorem vort_T1 {x r A Cp : ℝ} {k Np Mx : ℕ} (hx1 : 1 ≤ x) (hr : 0 ≤ r)
    (hr2 : 1 + r ≤ 2 * x ^ 2) (hMx : Mx = 3 * Np + 2 * k) (hA : A ≤ Cp * x ^ Np * (1 + r) ^ Np) :
    A ≤ |Cp| * 2 ^ Np * x ^ Mx := by
  have hx0 : 0 ≤ x := by linarith
  have hr_nonneg : 0 ≤ 1 + r := by linarith
  have hxN : 0 ≤ x ^ Np := pow_nonneg hx0 Np
  have hpow : (1 + r) ^ Np ≤ (2 * x ^ 2) ^ Np := pow_le_pow_left₀ hr_nonneg hr2 Np
  have h2 : Cp * x ^ Np * (1 + r) ^ Np ≤ |Cp| * 2 ^ Np * x ^ Mx := by
    calc Cp * x ^ Np * (1 + r) ^ Np = Cp * (x ^ Np * (1 + r) ^ Np) := by ring
      _ ≤ |Cp| * (x ^ Np * (1 + r) ^ Np) :=
          mul_le_mul_of_nonneg_right (le_abs_self Cp) (mul_nonneg hxN (pow_nonneg hr_nonneg Np))
      _ ≤ |Cp| * (x ^ Np * (2 * x ^ 2) ^ Np) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hxN) (abs_nonneg _)
      _ = |Cp| * 2 ^ Np * x ^ (3 * Np) := by ring
      _ ≤ |Cp| * 2 ^ Np * x ^ Mx := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply pow_le_pow_right₀ hx1
          rw [hMx]; omega
  linarith

/-- The second weighted piece: `(1+w)^{2k} F₂ ≤ |G| x^M` from the interpolated bound. -/
theorem vort_T2 {x a G q w F2 : ℝ} {k Mx : ℕ} (hx1 : 1 ≤ x) (ha1 : 1 ≤ a) (ha2 : a ≤ x)
    (hMx : 2 * k ≤ Mx) (hw : 0 ≤ w) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hF2 : 0 ≤ F2)
    (hG : (1 + w / a) ^ (2 * k) * F2 ≤ G * q) :
    (1 + w) ^ (2 * k) * F2 ≤ |G| * x ^ Mx := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hsub : 1 + w ≤ a * (1 + w / a) := by
    have e : a * (1 + w / a) = a + w := by field_simp
    linarith
  have hpw : (1 + w) ^ (2 * k) ≤ a ^ (2 * k) * (1 + w / a) ^ (2 * k) := by
    calc (1 + w) ^ (2 * k) ≤ (a * (1 + w / a)) ^ (2 * k) :=
          pow_le_pow_left₀ (by linarith) hsub _
      _ = a ^ (2 * k) * (1 + w / a) ^ (2 * k) := mul_pow _ _ _
  have hak : a ^ (2 * k) ≤ x ^ Mx := by
    calc a ^ (2 * k) ≤ x ^ (2 * k) := pow_le_pow_left₀ ha0.le ha2 _
      _ ≤ x ^ Mx := pow_le_pow_right₀ hx1 hMx
  have hGq : G * q ≤ |G| := by
    calc G * q ≤ |G| * q := mul_le_mul_of_nonneg_right (le_abs_self G) hq0
      _ ≤ |G| * 1 := mul_le_mul_of_nonneg_left hq1 (abs_nonneg G)
      _ = |G| := mul_one _
  calc (1 + w) ^ (2 * k) * F2 ≤ (a ^ (2 * k) * (1 + w / a) ^ (2 * k)) * F2 :=
        mul_le_mul_of_nonneg_right hpw hF2
    _ = a ^ (2 * k) * ((1 + w / a) ^ (2 * k) * F2) := by ring
    _ ≤ a ^ (2 * k) * (G * q) := mul_le_mul_of_nonneg_left hG (pow_nonneg ha0.le _)
    _ ≤ a ^ (2 * k) * |G| := mul_le_mul_of_nonneg_left hGq (pow_nonneg ha0.le _)
    _ ≤ x ^ Mx * |G| := mul_le_mul_of_nonneg_right hak (abs_nonneg G)
    _ = |G| * x ^ Mx := by ring

/-- The final absorption: `⟨y⟩^{2k} D ≤ (1 + K Ne!/bm^Ne) t⁻¹` from the squared bounds. -/
theorem vort_alg (hexp : ExpPolyAbsorb) (k j Mx Ne : ℕ)
    (hNe : Ne = 8 * k + Mx + 1 + (4 + 2 * j))
    {x c w jbv D F Q C bm t : ℝ} (hx1 : 1 ≤ x) (hc : c = x ^ 2)
    (hjb0 : 0 ≤ jbv) (hD0 : 0 ≤ D) (hF0 : 0 ≤ F) (hjb : jbv ≤ (1 + c ^ 2) * (1 + w))
    (hw : 0 ≤ w) (hD : D ≤ 2 * F) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hbm : 0 < bm)
    (hW : (1 + w) ^ (2 * k) * F ≤ Q * x ^ Mx) (hF : F ≤ C * x * Real.exp (-(bm * x)))
    (ht0 : 0 < t) (ht : t ≤ x ^ (2 + j)) :
    jbv ^ k * D ≤ (1 + 4 * 2 ^ (2 * k) * Q * C * (Ne.factorial : ℝ) / bm ^ Ne) * t⁻¹ := by
  have hx0 : 0 ≤ x := by linarith
  have hc2 : c ^ 2 = x ^ 4 := by rw [hc]; ring
  have hc1 : 1 ≤ c ^ 2 := by rw [hc2]; exact one_le_pow₀ hx1
  have hXle : jbv ^ k * D ≤ ((1 + c ^ 2) ^ k * (1 + w) ^ k) * (2 * F) := by
    have h1 : jbv ^ k ≤ ((1 + c ^ 2) * (1 + w)) ^ k := pow_le_pow_left₀ hjb0 hjb k
    rw [mul_pow] at h1
    exact mul_le_mul h1 hD hD0 (mul_nonneg (pow_nonneg (by linarith) _)
      (pow_nonneg (by linarith) _))
  have hX0 : 0 ≤ jbv ^ k * D := mul_nonneg (pow_nonneg hjb0 _) hD0
  have hbr0 : 0 ≤ 4 * ((1 + w) ^ (2 * k) * F) * F :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (by linarith) _) hF0)) hF0
  have hX2 : (jbv ^ k * D) ^ 2 ≤ (1 + c ^ 2) ^ (2 * k) * (4 * ((1 + w) ^ (2 * k) * F) * F) := by
    have h1 := pow_le_pow_left₀ hX0 hXle 2
    calc (jbv ^ k * D) ^ 2 ≤ (((1 + c ^ 2) ^ k * (1 + w) ^ k) * (2 * F)) ^ 2 := h1
      _ = (1 + c ^ 2) ^ (2 * k) * (4 * ((1 + w) ^ (2 * k) * F) * F) := by ring
  have hc2k : (1 + c ^ 2) ^ (2 * k) ≤ 2 ^ (2 * k) * x ^ (8 * k) := by
    calc (1 + c ^ 2) ^ (2 * k) ≤ (2 * c ^ 2) ^ (2 * k) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = 2 ^ (2 * k) * x ^ (8 * k) := by rw [mul_pow, hc2]; ring
  have hA : 4 * ((1 + w) ^ (2 * k) * F) ≤ 4 * (Q * x ^ Mx) := by linarith [hW]
  have hbr : 4 * ((1 + w) ^ (2 * k) * F) * F ≤
      4 * (Q * x ^ Mx) * (C * x * Real.exp (-(bm * x))) :=
    mul_le_mul hA hF hF0 (mul_nonneg (by norm_num) (mul_nonneg hQ (pow_nonneg hx0 _)))
  have hX2' : (jbv ^ k * D) ^ 2 ≤
      2 ^ (2 * k) * x ^ (8 * k) * (4 * (Q * x ^ Mx) * (C * x * Real.exp (-(bm * x)))) :=
    le_trans hX2 (mul_le_mul hc2k hbr hbr0
      (mul_nonneg (by positivity) (pow_nonneg hx0 _)))
  have hK0 : 0 ≤ 4 * 2 ^ (2 * k) * Q * C :=
    mul_nonneg (mul_nonneg (by positivity) hQ) hC
  have hY2 : ((jbv ^ k * D) * x ^ (2 + j)) ^ 2 ≤
      (4 * 2 ^ (2 * k) * Q * C) * (x ^ Ne * Real.exp (-(bm * x))) := by
    calc ((jbv ^ k * D) * x ^ (2 + j)) ^ 2 = (jbv ^ k * D) ^ 2 * x ^ (4 + 2 * j) := by ring
      _ ≤ 2 ^ (2 * k) * x ^ (8 * k) * (4 * (Q * x ^ Mx) * (C * x * Real.exp (-(bm * x)))) *
            x ^ (4 + 2 * j) := mul_le_mul_of_nonneg_right hX2' (pow_nonneg hx0 _)
      _ = (4 * 2 ^ (2 * k) * Q * C) * (x ^ Ne * Real.exp (-(bm * x))) := by
          rw [hNe]; ring
  have hexpNe := hexp Ne bm x hbm hx0
  have hY2' : ((jbv ^ k * D) * x ^ (2 + j)) ^ 2 ≤
      (4 * 2 ^ (2 * k) * Q * C) * (Ne.factorial : ℝ) / bm ^ Ne := by
    calc ((jbv ^ k * D) * x ^ (2 + j)) ^ 2
        ≤ (4 * 2 ^ (2 * k) * Q * C) * (x ^ Ne * Real.exp (-(bm * x))) := hY2
      _ ≤ (4 * 2 ^ (2 * k) * Q * C) * ((Ne.factorial : ℝ) / bm ^ Ne) :=
          mul_le_mul_of_nonneg_left hexpNe hK0
      _ = (4 * 2 ^ (2 * k) * Q * C) * (Ne.factorial : ℝ) / bm ^ Ne := by ring
  have hKf0 : 0 ≤ (4 * 2 ^ (2 * k) * Q * C) * (Ne.factorial : ℝ) / bm ^ Ne :=
    div_nonneg (mul_nonneg hK0 (Nat.cast_nonneg _)) (pow_nonneg hbm.le _)
  have gen : ∀ Y K : ℝ, 0 ≤ Y → 0 ≤ K → Y ^ 2 ≤ K → Y ≤ 1 + K := by
    intro Y K hY hK h
    nlinarith [sq_nonneg (Y - 1)]
  have hYle : (jbv ^ k * D) * x ^ (2 + j) ≤
      1 + (4 * 2 ^ (2 * k) * Q * C) * (Ne.factorial : ℝ) / bm ^ Ne :=
    gen _ _ (mul_nonneg hX0 (pow_nonneg hx0 _)) hKf0 hY2'
  have hT : (jbv ^ k * D) * t ≤ (jbv ^ k * D) * x ^ (2 + j) := mul_le_mul_of_nonneg_left ht hX0
  rw [← div_eq_mul_inv, le_div_iff₀ ht0]
  exact le_trans hT hYle

/-- The order-`j` error bound on the moving cell, for fixed `k`. -/
theorem vortErr_order (hcmp : UnforcedLeray.Short.PartI.TrainComparison)
    (hpoly : TrainWeightedJetPoly) (hVc : VcWeightedJet) (hcurl : CurlJetBound)
    (hexp : ExpPolyAbsorb) (k j : ℕ) :
    ∃ C ν₀ : ℝ, 0 ≤ C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r →
        ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
          B0579.jb y ^ k *
              ‖iteratedFDeriv ℝ j
                (UnforcedLeray.Cyl.curl
                  (fun x => tr.v r x - UnforcedLeray.Train.Vc ν (ν ^ (-2 : ℝ)) r x))
                (Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2)‖ ≤
            C * (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ := by
  obtain ⟨Cm, bm, νm, hCm, hbm, hνm, hcm⟩ := hcmp 2 (by norm_num) (j + 1)
  obtain ⟨Cp, Np, νp, hνp, hpl⟩ := hpoly (2 * k) (j + 1)
  obtain ⟨G, hG⟩ := hVc (2 * k) (j + 1)
  obtain ⟨Qw, hQw⟩ : ∃ Q : ℝ, Q = |Cp| * 2 ^ Np + |G| := ⟨_, rfl⟩
  obtain ⟨Mx, hMx⟩ : ∃ M : ℕ, M = 3 * Np + 2 * k := ⟨_, rfl⟩
  obtain ⟨Kx, hKx⟩ : ∃ K : ℝ, K = 4 * 2 ^ (2 * k) * Qw * |Cm| := ⟨_, rfl⟩
  obtain ⟨Ne, hNe⟩ : ∃ N : ℕ, N = 8 * k + Mx + 1 + (4 + 2 * j) := ⟨_, rfl⟩
  have hQw0 : 0 ≤ Qw := by rw [hQw]; positivity
  have hKf0 : 0 ≤ Kx * (Ne.factorial : ℝ) / bm ^ Ne := by
    rw [hKx]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hQw0) (abs_nonneg _))
      (Nat.cast_nonneg _)) (pow_nonneg hbm.le _)
  refine ⟨1 + Kx * (Ne.factorial : ℝ) / bm ^ Ne, min (min νm νp) 1, by linarith,
    lt_min (lt_min hνm hνp) one_pos, min_le_right _ _, ?_⟩
  intro ν hν tr hbuc r hr hθ y hy
  have hν0 : 0 < ν := hν.1
  have hνm' : ν ≤ νm := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hνp' : ν ≤ νp := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hν1 : ν ≤ 1 := le_trans hν.2 (min_le_right _ _)
  obtain ⟨ha1, ha2, hr2, hx1⟩ := vort_clock hν0 hν1 hr hθ
  have hcx : vortC ν = (ν⁻¹) ^ 2 := vort_c_eq hν0
  set x := ν⁻¹ with hxdef
  set a := clockA ν r with hadef
  have hx0 : 0 ≤ x := by linarith
  have ha0 : 0 < a := by linarith
  have hcpos : 0 < vortC ν := by rw [hcx]; positivity
  have hc2 : (vortC ν) ^ 2 = x ^ 4 := by rw [hcx]; ring
  have hxle : x ^ 1 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
  rw [pow_one] at hxle
  have hac : a ≤ (vortC ν) ^ 2 := by rw [hc2]; exact le_trans ha2 hxle
  have hsa0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsa1 : 1 ≤ Real.sqrt a := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt ha1
  have hsa_le : Real.sqrt a ≤ a :=
    calc Real.sqrt a ≤ Real.sqrt a * Real.sqrt a := le_mul_of_one_le_left hsa0 hsa1
      _ = a := Real.mul_self_sqrt ha0.le
  have hwpos : 0 < UnforcedLeray.Train.width ν r := by
    unfold UnforcedLeray.Train.width
    have := mul_nonneg hν0.le hr
    linarith
  have hf_smooth : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr
  have hg_smooth : ContDiff ℝ ∞ (UnforcedLeray.Train.Vc ν (vortC ν) r) :=
    UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hcpos hwpos
  have hsmooth : ContDiff ℝ ∞ (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (vortC ν) r z) :=
    hf_smooth.sub hg_smooth
  -- pointwise order `j+1` bound from the sup part of the comparison
  have hpt : ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ (j + 1) (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (vortC ν) r z) z‖ ≤
        Cm * x * a ^ (-((5 + ((j + 1 : ℕ) : ℝ)) / 2)) * Real.exp (-(bm * (vortC ν) ^ 2 / a)) := by
    intro z
    have key := (hcm ν hν0 hνm' tr hbuc r hr hac).2
    exact UnforcedLeray.B0277.norm_le_of_supNormD_le
      (mul_nonneg (mul_nonneg (mul_nonneg hCm.le hx0) (Real.rpow_nonneg ha0.le _))
        (Real.exp_nonneg _)) key z
  set z0 : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2) with hz0
  have hz2 : z0.2 = Real.sqrt a * y.2 := rfl
  have hF_bound := le_trans (hpt z0) (vort_E (c := vortC ν) (j + 1) hx1 ha1 ha2 hcx hbm)
  have hsplit : ‖iteratedFDeriv ℝ (j + 1) (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (vortC ν) r z) z0‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) (tr.v r) z0‖ +
        ‖iteratedFDeriv ℝ (j + 1) (UnforcedLeray.Train.Vc ν (vortC ν) r) z0‖ := by
    have hA' : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (tr.v r) :=
      hf_smooth.of_le (by exact_mod_cast le_top)
    have hB' : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (UnforcedLeray.Train.Vc ν (vortC ν) r) :=
      hg_smooth.of_le (by exact_mod_cast le_top)
    have hfn : iteratedFDeriv ℝ (j + 1) (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (vortC ν) r z) z0 =
        iteratedFDeriv ℝ (j + 1) (tr.v r) z0 -
          iteratedFDeriv ℝ (j + 1) (UnforcedLeray.Train.Vc ν (vortC ν) r) z0 :=
      iteratedFDeriv_sub_apply hA'.contDiffAt hB'.contDiffAt
    rw [hfn]
    exact norm_sub_le _ _
  have hT1 := vort_T1 (k := k) (Np := Np) (Mx := Mx) hx1 hr hr2 hMx
    (hpl ν ⟨hν0, hνp'⟩ tr hbuc r hr z0)
  have hq0 : 0 ≤ (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ (j + 1))⁻¹ :=
    inv_nonneg.2 (mul_nonneg (Real.rpow_nonneg ha0.le _) (pow_nonneg hsa0 _))
  have hq1 : (a ^ (3 / 2 : ℝ) * Real.sqrt a ^ (j + 1))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow ha1 (by norm_num))
      (one_le_pow₀ hsa1)
  have hT2 := vort_T2 (k := k) (Mx := Mx) hx1 ha1 ha2 (by rw [hMx]; omega)
    (w := z0.2 ^ 2) (sq_nonneg _) hq0 hq1 (norm_nonneg _)
    (hG ν (vortC ν) r hν0 hcpos hr hac z0)
  have hFW : (1 + z0.2 ^ 2) ^ (2 * k) *
      ‖iteratedFDeriv ℝ (j + 1) (fun z => tr.v r z - UnforcedLeray.Train.Vc ν (vortC ν) r z) z0‖
        ≤ Qw * x ^ Mx := by
    have hmul := mul_le_mul_of_nonneg_left hsplit
      (by positivity : (0 : ℝ) ≤ (1 + z0.2 ^ 2) ^ (2 * k))
    have hsum : (1 + z0.2 ^ 2) ^ (2 * k) * (‖iteratedFDeriv ℝ (j + 1) (tr.v r) z0‖ +
        ‖iteratedFDeriv ℝ (j + 1) (UnforcedLeray.Train.Vc ν (vortC ν) r) z0‖) =
        (1 + z0.2 ^ 2) ^ (2 * k) * ‖iteratedFDeriv ℝ (j + 1) (tr.v r) z0‖ +
        (1 + z0.2 ^ 2) ^ (2 * k) * ‖iteratedFDeriv ℝ (j + 1) (UnforcedLeray.Train.Vc ν (vortC ν) r) z0‖ := by
      ring
    have hQ' : Qw * x ^ Mx = |Cp| * 2 ^ Np * x ^ Mx + |G| * x ^ Mx := by
      rw [hQw]; ring
    rw [hQ']
    linarith [hmul, hsum, hT1, hT2]
  -- the curl and the weight
  have hD := hcurl _ hsmooth j z0
  have hjb := vort_hjb (c := vortC ν) (z2 := z0.2) ha1 hz2
    (Set.mem_Ico.mp (Set.mem_prod.mp hy).1)
  have hjb0 : 0 ≤ B0579.jb y := (B0579.jb_pos y).le
  have hsa_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have ht0 : 0 < a ^ 2 * Real.sqrt a ^ j := mul_pos (pow_pos ha0 2) (pow_pos hsa_pos j)
  have ht : a ^ 2 * Real.sqrt a ^ j ≤ x ^ (2 + j) := by
    have h1 : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ha0.le ha2 2
    have h2 : Real.sqrt a ^ j ≤ x ^ j := pow_le_pow_left₀ hsa0 (le_trans hsa_le ha2) j
    calc a ^ 2 * Real.sqrt a ^ j ≤ x ^ 2 * x ^ j :=
          mul_le_mul h1 h2 (pow_nonneg hsa0 _) (pow_nonneg hx0 _)
      _ = x ^ (2 + j) := by ring
  have hfinal := vort_alg hexp k j Mx Ne hNe hx1 hcx hjb0 (norm_nonneg _) (norm_nonneg _)
    hjb (sq_nonneg _) hD hQw0 (abs_nonneg Cm) hbm hFW hF_bound ht0 ht
  rw [hKx]
  exact hfinal

theorem vortErrMoving_of (hcmp : UnforcedLeray.Short.PartI.TrainComparison)
    (hpoly : TrainWeightedJetPoly) (hVc : VcWeightedJet) (hcurl : CurlJetBound)
    (hexp : ExpPolyAbsorb) : VortErrMoving := by
  intro k
  refine ⟨1, fun b hb => ?_⟩
  obtain ⟨C0, ν0, hC0, hν0, _, h0⟩ := vortErr_order hcmp hpoly hVc hcurl hexp k 0
  obtain ⟨C1, ν1, hC1, hν1, _, h1⟩ := vortErr_order hcmp hpoly hVc hcurl hexp k 1
  obtain ⟨C2, ν2, hC2, hν2, _, h2⟩ := vortErr_order hcmp hpoly hVc hcurl hexp k 2
  obtain ⟨C3, ν3, hC3, hν3, _, h3⟩ := vortErr_order hcmp hpoly hVc hcurl hexp k 3
  refine ⟨C0 + C1 + C2 + C3, min (min ν0 ν1) (min ν2 ν3),
    lt_min (lt_min hν0 hν1) (lt_min hν2 hν3), fun ν hν tr hbuc r hr hθ j hj y hy => ?_⟩
  have hb1 : 1 ≤ clockTheta ν r := le_trans hb hθ
  have hνa0 : ν ≤ ν0 := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hνa1 : ν ≤ ν1 := le_trans hν.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hνa2 : ν ≤ ν2 := le_trans hν.2 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hνa3 : ν ≤ ν3 := le_trans hν.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hT0 : 0 ≤ (clockA ν r ^ 2 * Real.sqrt (clockA ν r) ^ j)⁻¹ :=
    inv_nonneg.2 (mul_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))
  interval_cases j
  · exact le_trans (h0 ν ⟨hν.1, hνa0⟩ tr hbuc r hr hb1 y hy)
      (mul_le_mul_of_nonneg_right (by linarith) hT0)
  · exact le_trans (h1 ν ⟨hν.1, hνa1⟩ tr hbuc r hr hb1 y hy)
      (mul_le_mul_of_nonneg_right (by linarith) hT0)
  · exact le_trans (h2 ν ⟨hν.1, hνa2⟩ tr hbuc r hr hb1 y hy)
      (mul_le_mul_of_nonneg_right (by linarith) hT0)
  · exact le_trans (h3 ν ⟨hν.1, hνa3⟩ tr hbuc r hr hb1 y hy)
      (mul_le_mul_of_nonneg_right (by linarith) hT0)

end UnforcedLeray.Short.IIIa
