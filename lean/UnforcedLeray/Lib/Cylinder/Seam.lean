import UnforcedLeray.Lib.Cylinder.IBP
import UnforcedLeray.Lib.Cylinder.Weight
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The weighted diffusion energy with the seam term, and transport antisymmetry (INF13, CY05)


§4 "Not recommended (a)" and §5 CY05 (`re_weighted_laplacian_le_seam`,
`re_weighted_laplacian_le_smooth`, `transport_antisymm`); decision D12 of `scoping/README.md`.

`paper/main.tex` lines 4171-4184 (unit B0242): the centred weight `(1+q²+η²)^m` "is continuous
across the seam. Its normal derivative has a negative jump there ... integration by parts
separately on the two sides, give[s] the usual weighted diffusion energy with this favorable
seam term."  Lines 6494-6518 (unit B0343) use the exact `Δp/p` of the centred weight and
"its outward derivative leaves a nonpositive diffusion boundary term".

* `weighted_laplacian_identity`: for a real `C²`, `c`-periodic `w` and a real `C²` weight `p`
  with equal values on the two seams, the exact identity
  `2∫_cell Δw w p = -2∫_cell |∇w|² p + ∫_cell w² Δp - ∫ w(c/2,η)² [∂_q p]_{-c/2}^{c/2} dη`
  (one-sided integration by parts on `[-c/2, c/2]`, the scoping note's recommended proof),
  under explicit integrability hypotheses.
* `weighted_laplacian_le_seam_core`: when the outward derivative of `p` jumps the right way
  (`∂_q p(-c/2) ≤ ∂_q p(c/2)`) the boundary term is `≤ 0`.
* `weighted_laplacian_le_seam` (CY05 `re_weighted_laplacian_le_seam`, real form): the centred
  weight `p = ρc^m`, `m ≥ 0`, for `w` with compact support in `η`.  The general case follows by
  density (scoping CY06), which is not part of this target.
* `laplacian_rpow_ρc`, `laplacian_rpow_ρc_le`: `Δ(ρc^m) = 4mρc^{m-1} + 4m(m-1)|y|²ρc^{m-2}
  ≤ 4m·max(1,m)·ρc^m` (B0343's `Δp/p`), and the B0242 form `weighted_laplacian_le_seam_const`.
* `weighted_laplacian_le_smooth`: the smooth periodic weight `ρw^m`, where no seam term appears.
* `transport_antisymm` (CY05): `∫ (v·∇w) w ρ = -½ ∫ w² v·∇ρ` for divergence-free periodic `v`
  and any weight with equal seam values.

Fields are real-valued (the vorticity of the manuscript is real).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real
open scoped Topology ContDiff

namespace UnforcedLeray.Cyl

/-! ### The exact identity -/

section Identity

variable {c : ℝ} {w p : Plane → ℝ}

/-- **Weighted Green identity on the centred cell** with the seam term. -/
theorem weighted_laplacian_identity (hc : 0 < c) (hw : C2 w) (hp : C2 p)
    (hper : IsPeriodic c w) (hpseam : ∀ η, p (-c / 2, η) = p (c / 2, η))
    (i1 : IntegrableOn (fun z => p z * w z * partialQ (partialQ w) z) (cell c))
    (i2 : IntegrableOn (fun z => p z * w z * partialEta (partialEta w) z) (cell c))
    (i3 : IntegrableOn (fun z => p z * partialQ w z ^ 2) (cell c))
    (i4 : IntegrableOn (fun z => p z * partialEta w z ^ 2) (cell c))
    (i5 : IntegrableOn (fun z => w z ^ 2 * partialQ (partialQ p) z) (cell c))
    (i6 : IntegrableOn (fun z => w z ^ 2 * partialEta (partialEta p) z) (cell c))
    (i7 : IntegrableOn
      (fun z => p z * (2 * w z * partialEta w z) - w z ^ 2 * partialEta p z) (cell c)) :
    2 * (∫ z in cell c, laplacian w z * w z * p z) =
      -2 * (∫ z in cell c, (partialQ w z ^ 2 + partialEta w z ^ 2) * p z)
        + (∫ z in cell c, w z ^ 2 * laplacian p z)
        - ∫ η, w (c / 2, η) ^ 2 * (partialQ p (c / 2, η) - partialQ p (-c / 2, η)) := by
  -- the `q`-flux and its derivative
  obtain ⟨Pq, hPq⟩ : ∃ Pq : Plane → ℝ,
      Pq = fun z => p z * (2 * w z * partialQ w z) - w z ^ 2 * partialQ p z := ⟨_, rfl⟩
  obtain ⟨Dq, hDq⟩ : ∃ Dq : Plane → ℝ, Dq = fun z => 2 * (p z * w z * partialQ (partialQ w) z) +
      2 * (p z * partialQ w z ^ 2) - w z ^ 2 * partialQ (partialQ p) z := ⟨_, rfl⟩
  have hdq : ∀ q η, HasDerivAt (fun q' => Pq (q', η)) (Dq (q, η)) q := by
    intro q η
    have hw1 := hasDerivAt_sliceQ hw.diff q η
    have hw2 := hasDerivAt_sliceQ hw.diffQ q η
    have hp1 := hasDerivAt_sliceQ hp.diff q η
    have hp2 := hasDerivAt_sliceQ hp.diffQ q η
    have := (hp1.mul ((hw1.const_mul 2).mul hw2)).sub ((hw1.pow 2).mul hp2)
    simp only [hPq, hDq]
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    norm_num
    ring
  -- the `η`-flux and its derivative
  obtain ⟨Pη, hPη⟩ : ∃ Pη : Plane → ℝ,
      Pη = fun z => p z * (2 * w z * partialEta w z) - w z ^ 2 * partialEta p z := ⟨_, rfl⟩
  obtain ⟨Dη, hDη⟩ : ∃ Dη : Plane → ℝ, Dη = fun z =>
      2 * (p z * w z * partialEta (partialEta w) z) +
      2 * (p z * partialEta w z ^ 2) - w z ^ 2 * partialEta (partialEta p) z := ⟨_, rfl⟩
  have hdη : ∀ q η, HasDerivAt (fun η' => Pη (q, η')) (Dη (q, η)) η := by
    intro q η
    have hw1 := hasDerivAt_sliceEta hw.diff q η
    have hw2 := hasDerivAt_sliceEta hw.diffEta q η
    have hp1 := hasDerivAt_sliceEta hp.diff q η
    have hp2 := hasDerivAt_sliceEta hp.diffEta q η
    have := (hp1.mul ((hw1.const_mul 2).mul hw2)).sub ((hw1.pow 2).mul hp2)
    simp only [hPη, hDη]
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    norm_num
    ring
  have iDq : IntegrableOn Dq (cell c) := by
    rw [hDq]; exact ((i1.const_mul 2).add (i3.const_mul 2)).sub i5
  have iDη : IntegrableOn Dη (cell c) := by
    rw [hDη]; exact ((i2.const_mul 2).add (i4.const_mul 2)).sub i6
  have iPη : IntegrableOn Pη (cell c) := by rw [hPη]; exact i7
  -- the two fundamental theorems
  have hQ := integral_cell_deriv_q hc hdq iDq
  have hH := integral_cell_deriv_eta hdη iPη iDη
  have hbd : (fun η => Pq (c / 2, η) - Pq (-c / 2, η)) =
      fun η => -(w (c / 2, η) ^ 2 * (partialQ p (c / 2, η) - partialQ p (-c / 2, η))) := by
    funext η
    rw [hPq]
    simp only
    rw [hper.neg_half, hper.partialQ.neg_half, hpseam]
    ring
  rw [hbd, integral_neg] at hQ
  -- split the integrals
  have eQ : ∫ z in cell c, Dq z = 2 * (∫ z in cell c, p z * w z * partialQ (partialQ w) z) +
      2 * (∫ z in cell c, p z * partialQ w z ^ 2) -
      ∫ z in cell c, w z ^ 2 * partialQ (partialQ p) z := by
    have j1 : IntegrableOn (fun z => 2 * (p z * w z * partialQ (partialQ w) z) +
        2 * (p z * partialQ w z ^ 2)) (cell c) := (i1.const_mul 2).add (i3.const_mul 2)
    have j2 : IntegrableOn (fun z => 2 * (p z * w z * partialQ (partialQ w) z)) (cell c) :=
      i1.const_mul 2
    have j3 : IntegrableOn (fun z => 2 * (p z * partialQ w z ^ 2)) (cell c) := i3.const_mul 2
    simp only [hDq]
    rw [integral_sub j1 i5, integral_add j2 j3, integral_const_mul, integral_const_mul]
  have eH : ∫ z in cell c, Dη z = 2 * (∫ z in cell c, p z * w z * partialEta (partialEta w) z) +
      2 * (∫ z in cell c, p z * partialEta w z ^ 2) -
      ∫ z in cell c, w z ^ 2 * partialEta (partialEta p) z := by
    have j1 : IntegrableOn (fun z => 2 * (p z * w z * partialEta (partialEta w) z) +
        2 * (p z * partialEta w z ^ 2)) (cell c) := (i2.const_mul 2).add (i4.const_mul 2)
    have j2 : IntegrableOn (fun z => 2 * (p z * w z * partialEta (partialEta w) z)) (cell c) :=
      i2.const_mul 2
    have j3 : IntegrableOn (fun z => 2 * (p z * partialEta w z ^ 2)) (cell c) := i4.const_mul 2
    simp only [hDη]
    rw [integral_sub j1 i6, integral_add j2 j3, integral_const_mul, integral_const_mul]
  have eL : ∫ z in cell c, laplacian w z * w z * p z =
      (∫ z in cell c, p z * w z * partialQ (partialQ w) z) +
        ∫ z in cell c, p z * w z * partialEta (partialEta w) z := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [laplacian]; ring
  have eG : ∫ z in cell c, (partialQ w z ^ 2 + partialEta w z ^ 2) * p z =
      (∫ z in cell c, p z * partialQ w z ^ 2) + ∫ z in cell c, p z * partialEta w z ^ 2 := by
    rw [← integral_add i3 i4]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only; ring
  have eP : ∫ z in cell c, w z ^ 2 * laplacian p z =
      (∫ z in cell c, w z ^ 2 * partialQ (partialQ p) z) +
        ∫ z in cell c, w z ^ 2 * partialEta (partialEta p) z := by
    rw [← integral_add i5 i6]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [laplacian]; ring
  rw [eL, eG, eP]
  linarith

/-- **Seam inequality, general weight.**  If the outward `q`-derivative of the weight does not
decrease across the seam (`∂_q p(-c/2,η) ≤ ∂_q p(c/2,η)`), the seam term is nonpositive. -/
theorem weighted_laplacian_le_seam_core (hc : 0 < c) (hw : C2 w) (hp : C2 p)
    (hper : IsPeriodic c w) (hpseam : ∀ η, p (-c / 2, η) = p (c / 2, η))
    (hjump : ∀ η, partialQ p (-c / 2, η) ≤ partialQ p (c / 2, η))
    (i1 : IntegrableOn (fun z => p z * w z * partialQ (partialQ w) z) (cell c))
    (i2 : IntegrableOn (fun z => p z * w z * partialEta (partialEta w) z) (cell c))
    (i3 : IntegrableOn (fun z => p z * partialQ w z ^ 2) (cell c))
    (i4 : IntegrableOn (fun z => p z * partialEta w z ^ 2) (cell c))
    (i5 : IntegrableOn (fun z => w z ^ 2 * partialQ (partialQ p) z) (cell c))
    (i6 : IntegrableOn (fun z => w z ^ 2 * partialEta (partialEta p) z) (cell c))
    (i7 : IntegrableOn
      (fun z => p z * (2 * w z * partialEta w z) - w z ^ 2 * partialEta p z) (cell c)) :
    2 * (∫ z in cell c, laplacian w z * w z * p z) ≤
      -2 * (∫ z in cell c, (partialQ w z ^ 2 + partialEta w z ^ 2) * p z)
        + ∫ z in cell c, w z ^ 2 * laplacian p z := by
  rw [weighted_laplacian_identity hc hw hp hper hpseam i1 i2 i3 i4 i5 i6 i7]
  have : 0 ≤ ∫ η, w (c / 2, η) ^ 2 * (partialQ p (c / 2, η) - partialQ p (-c / 2, η)) :=
    integral_nonneg fun η => mul_nonneg (sq_nonneg _) (sub_nonneg.2 (hjump η))
  linarith

end Identity

/-! ### Derivatives of the centred weight -/

section CentredWeight

theorem hasDerivAt_ρc_q (q η : ℝ) : HasDerivAt (fun q' => ρc (q', η)) (2 * q) q := by
  have h : HasDerivAt (fun q' : ℝ => 1 + q' ^ 2 + η ^ 2) (2 * q) q := by
    simpa using ((hasDerivAt_pow 2 q).const_add 1).add_const (η ^ 2)
  exact h

theorem hasDerivAt_ρc_eta (q η : ℝ) : HasDerivAt (fun η' => ρc (q, η')) (2 * η) η := by
  have h : HasDerivAt (fun η' : ℝ => 1 + q ^ 2 + η' ^ 2) (2 * η) η := by
    simpa using (hasDerivAt_pow 2 η).const_add (1 + q ^ 2)
  exact h

theorem partialQ_rpow_ρc (m : ℝ) (z : Plane) :
    partialQ (fun z => ρc z ^ m) z = 2 * z.1 * m * ρc z ^ (m - 1) :=
  ((hasDerivAt_ρc_q z.1 z.2).rpow_const (Or.inl (ρc_pos _).ne')).deriv

theorem partialEta_rpow_ρc (m : ℝ) (z : Plane) :
    partialEta (fun z => ρc z ^ m) z = 2 * z.2 * m * ρc z ^ (m - 1) :=
  ((hasDerivAt_ρc_eta z.1 z.2).rpow_const (Or.inl (ρc_pos _).ne')).deriv

theorem partialQ_partialQ_rpow_ρc (m : ℝ) (z : Plane) :
    partialQ (partialQ fun z => ρc z ^ m) z =
      2 * m * ρc z ^ (m - 1) + 4 * m * (m - 1) * z.1 ^ 2 * ρc z ^ (m - 2) := by
  have hfun : partialQ (fun z => ρc z ^ m) = fun z => 2 * z.1 * m * ρc z ^ (m - 1) :=
    funext (partialQ_rpow_ρc m)
  rw [hfun]
  have h1 := (hasDerivAt_ρc_q z.1 z.2).rpow_const (p := m - 1) (Or.inl (ρc_pos _).ne')
  have h2 := (((hasDerivAt_id' z.1).const_mul 2).mul_const m).mul h1
  show deriv (fun q : ℝ => 2 * q * m * ρc (q, z.2) ^ (m - 1)) z.1 = _
  rw [show (fun q : ℝ => 2 * q * m * ρc (q, z.2) ^ (m - 1)) =
    ((fun y => 2 * y * m) * fun y => ρc (y, z.2) ^ (m - 1)) from rfl, h2.deriv,
    show m - 1 - 1 = m - 2 by ring, Prod.mk.eta]
  ring

theorem partialEta_partialEta_rpow_ρc (m : ℝ) (z : Plane) :
    partialEta (partialEta fun z => ρc z ^ m) z =
      2 * m * ρc z ^ (m - 1) + 4 * m * (m - 1) * z.2 ^ 2 * ρc z ^ (m - 2) := by
  have hfun : partialEta (fun z => ρc z ^ m) = fun z => 2 * z.2 * m * ρc z ^ (m - 1) :=
    funext (partialEta_rpow_ρc m)
  rw [hfun]
  have h1 := (hasDerivAt_ρc_eta z.1 z.2).rpow_const (p := m - 1) (Or.inl (ρc_pos _).ne')
  have h2 := (((hasDerivAt_id' z.2).const_mul 2).mul_const m).mul h1
  show deriv (fun η : ℝ => 2 * η * m * ρc (z.1, η) ^ (m - 1)) z.2 = _
  rw [show (fun η : ℝ => 2 * η * m * ρc (z.1, η) ^ (m - 1)) =
    ((fun y => 2 * y * m) * fun y => ρc (z.1, y) ^ (m - 1)) from rfl, h2.deriv,
    show m - 1 - 1 = m - 2 by ring, Prod.mk.eta]
  ring

/-- `Δ(ρc^m) = 4m ρc^{m-1} + 4m(m-1)(q²+η²) ρc^{m-2}` (tex 6494-6518, B0343). -/
theorem laplacian_rpow_ρc (m : ℝ) (z : Plane) :
    laplacian (fun z => ρc z ^ m) z =
      4 * m * ρc z ^ (m - 1) + 4 * m * (m - 1) * (z.1 ^ 2 + z.2 ^ 2) * ρc z ^ (m - 2) := by
  rw [laplacian, partialQ_partialQ_rpow_ρc, partialEta_partialEta_rpow_ρc]
  ring

/-- `Δ(ρc^m) ≤ 4m·max(1,m)·ρc^m` for `m ≥ 0` (the constant `C_m` of B0242, tex 4171-4184). -/
theorem laplacian_rpow_ρc_le {m : ℝ} (hm : 0 ≤ m) (z : Plane) :
    laplacian (fun z => ρc z ^ m) z ≤ 4 * m * max 1 m * ρc z ^ m := by
  rw [laplacian_rpow_ρc]
  have hρ := ρc_pos z
  have hρ1 := one_le_ρc z
  have e1 : ρc z ^ (m - 1) = ρc z ^ m / ρc z := by
    rw [Real.rpow_sub hρ, Real.rpow_one]
  have e2 : ρc z ^ (m - 2) = ρc z ^ m / ρc z ^ 2 := by
    rw [Real.rpow_sub hρ, Real.rpow_two]
  rw [e1, e2]
  have hpm : 0 < ρc z ^ m := Real.rpow_pos_of_pos hρ m
  have hy : z.1 ^ 2 + z.2 ^ 2 ≤ ρc z := by unfold ρc; linarith
  have hy0 : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
  -- first term
  have t1 : 4 * m * (ρc z ^ m / ρc z) ≤ 4 * m * ρc z ^ m := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact div_le_self hpm.le hρ1
  -- second term
  have t2 : 4 * m * (m - 1) * (z.1 ^ 2 + z.2 ^ 2) * (ρc z ^ m / ρc z ^ 2) ≤
      4 * m * max 0 (m - 1) * ρc z ^ m := by
    have hq : (z.1 ^ 2 + z.2 ^ 2) / ρc z ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have hq0 : 0 ≤ (z.1 ^ 2 + z.2 ^ 2) / ρc z ^ 2 := by positivity
    have : 4 * m * (m - 1) * (z.1 ^ 2 + z.2 ^ 2) * (ρc z ^ m / ρc z ^ 2) =
        4 * m * ρc z ^ m * ((m - 1) * ((z.1 ^ 2 + z.2 ^ 2) / ρc z ^ 2)) := by
      field_simp
    rw [this]
    have h4 : (m - 1) * ((z.1 ^ 2 + z.2 ^ 2) / ρc z ^ 2) ≤ max 0 (m - 1) := by
      rcases le_total (m - 1) 0 with h | h
      · exact (mul_nonpos_of_nonpos_of_nonneg h hq0).trans (le_max_left _ _)
      · calc (m - 1) * ((z.1 ^ 2 + z.2 ^ 2) / ρc z ^ 2) ≤ (m - 1) * 1 :=
              mul_le_mul_of_nonneg_left hq h
          _ ≤ max 0 (m - 1) := by rw [mul_one]; exact le_max_right _ _
    calc 4 * m * ρc z ^ m * ((m - 1) * ((z.1 ^ 2 + z.2 ^ 2) / ρc z ^ 2))
        ≤ 4 * m * ρc z ^ m * max 0 (m - 1) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 4 * m * max 0 (m - 1) * ρc z ^ m := by ring
  have hmax : 1 + max 0 (m - 1) = max 1 m := by
    rcases le_total m 1 with h | h
    · rw [max_eq_left (by linarith), max_eq_left h]; ring
    · rw [max_eq_right (by linarith), max_eq_right h]; ring
  calc _ ≤ 4 * m * ρc z ^ m + 4 * m * max 0 (m - 1) * ρc z ^ m := add_le_add t1 t2
    _ = 4 * m * (1 + max 0 (m - 1)) * ρc z ^ m := by ring
    _ = 4 * m * max 1 m * ρc z ^ m := by rw [hmax]

theorem contDiff_rpow_ρc (m : ℝ) : ContDiff ℝ 2 fun z => ρc z ^ m :=
  ContDiff.rpow_const_of_ne (by unfold ρc; fun_prop) fun z => (ρc_pos z).ne'

theorem contDiff_rpow_ρw (ℓ m : ℝ) : ContDiff ℝ 2 fun z => ρw ℓ z ^ m :=
  ContDiff.rpow_const_of_ne (by unfold ρw; fun_prop) fun z => (ρw_pos ℓ z).ne'

end CentredWeight

/-! ### The seam inequality for the centred weight -/

section Seam

variable {c m R : ℝ} {w : Plane → ℝ}

theorem integrable_pieces (hw : C2 w) {p : Plane → ℝ} (hp : C2 p) (hR : VanishesOutside R w) :
    IntegrableOn (fun z => p z * w z * partialQ (partialQ w) z) (cell c) ∧
    IntegrableOn (fun z => p z * w z * partialEta (partialEta w) z) (cell c) ∧
    IntegrableOn (fun z => p z * partialQ w z ^ 2) (cell c) ∧
    IntegrableOn (fun z => p z * partialEta w z ^ 2) (cell c) ∧
    IntegrableOn (fun z => w z ^ 2 * partialQ (partialQ p) z) (cell c) ∧
    IntegrableOn (fun z => w z ^ 2 * partialEta (partialEta p) z) (cell c) ∧
    IntegrableOn
      (fun z => p z * (2 * w z * partialEta w z) - w z ^ 2 * partialEta p z) (cell c) := by
  have c0 := hw.cont; have c1 := hw.contQ; have c2 := hw.contEta
  have c3 := hw.contQQ; have c4 := hw.contEtaEta
  have d0 := hp.cont; have d2 := hp.contEta; have d3 := hp.contQQ; have d4 := hp.contEtaEta
  have hRq := hR.partialQ; have hRη := hR.partialEta
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  · exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  · exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hRq z hz]) (by fun_prop) c
  · exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hRη z hz]) (by fun_prop) c
  · exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  · exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  · exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c

/-- **The seam inequality** (CY05 `re_weighted_laplacian_le_seam`, real form; B0242,
tex 4171-4184; B0343, tex 6494-6518).  For `m ≥ 0`, a real `C²`, `c`-periodic `w` with compact
support in `η`, and the centred weight `ρc^m` on the cell `[-c/2, c/2) × ℝ`,
`2∫_cell Δw w ρc^m ≤ -2∫_cell |∇w|² ρc^m + ∫_cell w² Δ(ρc^m)`. -/
theorem weighted_laplacian_le_seam (hc : 0 < c) (hm : 0 ≤ m) (hw : ContDiff ℝ 2 w)
    (hper : IsPeriodic c w) (hR : VanishesOutside R w) :
    2 * (∫ z in cell c, laplacian w z * w z * ρc z ^ m) ≤
      -2 * (∫ z in cell c, (partialQ w z ^ 2 + partialEta w z ^ 2) * ρc z ^ m)
        + ∫ z in cell c, w z ^ 2 * laplacian (fun z => ρc z ^ m) z := by
  have hw2 := C2.of_contDiff hw
  have hp2 : C2 (fun z => ρc z ^ m) := C2.of_contDiff (contDiff_rpow_ρc m)
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := integrable_pieces (c := c) hw2 hp2 hR
  refine weighted_laplacian_le_seam_core hc hw2 hp2 hper
    (fun η => by simp only [ρc_neg_half]) (fun η => ?_) i1 i2 i3 i4 i5 i6 i7
  rw [partialQ_rpow_ρc, partialQ_rpow_ρc, ρc_neg_half]
  have : 0 ≤ c * m * ρc (c / 2, η) ^ (m - 1) :=
    mul_nonneg (mul_nonneg hc.le hm) (Real.rpow_nonneg (ρc_pos _).le _)
  simp only
  nlinarith

/-- The seam inequality with the constant `C_m = 4m·max(1,m)` (B0242, tex 4171-4184:
`2⟨Δw, w⟩_X ≤ -2∫|∇w|² weight + C_m ‖w‖²_X`). -/
theorem weighted_laplacian_le_seam_const (hc : 0 < c) (hm : 0 ≤ m) (hw : ContDiff ℝ 2 w)
    (hper : IsPeriodic c w) (hR : VanishesOutside R w) :
    2 * (∫ z in cell c, laplacian w z * w z * ρc z ^ m) ≤
      -2 * (∫ z in cell c, (partialQ w z ^ 2 + partialEta w z ^ 2) * ρc z ^ m)
        + 4 * m * max 1 m * ∫ z in cell c, w z ^ 2 * ρc z ^ m := by
  refine (weighted_laplacian_le_seam hc hm hw hper hR).trans ?_
  have hw2 := C2.of_contDiff hw
  have hp2 : C2 (fun z => ρc z ^ m) := C2.of_contDiff (contDiff_rpow_ρc m)
  have c0 := hw2.cont
  have d0 := hp2.cont; have d3 := hp2.contQQ; have d4 := hp2.contEtaEta
  have iA : IntegrableOn (fun z => w z ^ 2 * laplacian (fun z => ρc z ^ m) z) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz])
      (by simp only [laplacian]; fun_prop) c
  have iB : IntegrableOn (fun z => 4 * m * max 1 m * (w z ^ 2 * ρc z ^ m)) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  have e : ∫ z in cell c, 4 * m * max 1 m * (w z ^ 2 * ρc z ^ m) =
      4 * m * max 1 m * ∫ z in cell c, w z ^ 2 * ρc z ^ m := integral_const_mul _ _
  have : ∫ z in cell c, w z ^ 2 * laplacian (fun z => ρc z ^ m) z ≤
      ∫ z in cell c, 4 * m * max 1 m * (w z ^ 2 * ρc z ^ m) :=
    setIntegral_mono iA iB fun z => by
      have := laplacian_rpow_ρc_le hm z
      have h2 := sq_nonneg (w z)
      nlinarith
  linarith

end Seam

/-! ### The smooth periodic weight: no seam term -/

/-- The weighted diffusion identity for the smooth periodic weight `ρw c^m` (CY05
`re_weighted_laplacian_le_smooth`, B0271, tex 4569-4578): the seam term vanishes, and
`2∫_cell Δw w ρw^m = -2∫_cell |∇w|² ρw^m + ∫_cell w² Δ(ρw^m)`. -/
theorem weighted_laplacian_smooth {c m R : ℝ} (hc : 0 < c) {w : Plane → ℝ}
    (hw : ContDiff ℝ 2 w) (hper : IsPeriodic c w) (hR : VanishesOutside R w) :
    2 * (∫ z in cell c, laplacian w z * w z * ρw c z ^ m) =
      -2 * (∫ z in cell c, (partialQ w z ^ 2 + partialEta w z ^ 2) * ρw c z ^ m)
        + ∫ z in cell c, w z ^ 2 * laplacian (fun z => ρw c z ^ m) z := by
  have hw2 := C2.of_contDiff hw
  have hp2 : C2 (fun z => ρw c z ^ m) := C2.of_contDiff (contDiff_rpow_ρw c m)
  have hpper : IsPeriodic c (fun z => ρw c z ^ m) :=
    (isPeriodic_ρw hc.ne').fun_comp fun x => x ^ m
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := integrable_pieces (c := c) hw2 hp2 hR
  rw [weighted_laplacian_identity hc hw2 hp2 hper (fun η => hpper.neg_half η)
    i1 i2 i3 i4 i5 i6 i7]
  have : ∀ η, partialQ (fun z => ρw c z ^ m) (c / 2, η) -
      partialQ (fun z => ρw c z ^ m) (-c / 2, η) = 0 := fun η => by
    rw [hpper.partialQ.neg_half, sub_self]
  simp only [this, mul_zero, integral_zero, sub_zero]

/-! ### Transport antisymmetry -/

/-- **Transport antisymmetry** (CY05 `transport_antisymm`; B0343, tex 6494-6518).  For a
divergence-free, `c`-periodic `C¹` meridional field `v`, a real `C¹`, `c`-periodic `w` with
compact support in `η`, and a `C¹` weight `ρ` with equal values on the two seams (the centred
weight `ρc^m` or the periodic weight `ρw^m`),
`∫_cell (v·∇w) w ρ = -½ ∫_cell w² (v·∇ρ)`. -/
theorem transport_antisymm {c R : ℝ} (hc : 0 < c) {v : Plane → Vec2} {w ρ : Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) (hρ : ContDiff ℝ 1 ρ)
    (hvp : IsPeriodic c v) (hwp : IsPeriodic c w)
    (hρseam : ∀ η, ρ (-c / 2, η) = ρ (c / 2, η))
    (hdiv : ∀ z, divergence v z = 0) (hR : VanishesOutside R w) :
    ∫ z in cell c, (v z 0 * partialQ w z + v z 1 * partialEta w z) * w z * ρ z =
      -(1 / 2) * ∫ z in cell c, w z ^ 2 * (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z) := by
  have hvd := hv.differentiable one_ne_zero
  have hwd := hw.differentiable one_ne_zero
  have hρd := hρ.differentiable one_ne_zero
  have hv0 : ContDiff ℝ 1 fun z => v z 0 :=
    (EuclideanSpace.proj (0 : Fin 2) : Vec2 →L[ℝ] ℝ).contDiff.comp hv
  have hv1 : ContDiff ℝ 1 fun z => v z 1 :=
    (EuclideanSpace.proj (1 : Fin 2) : Vec2 →L[ℝ] ℝ).contDiff.comp hv
  obtain ⟨cv0q, -⟩ := C1_partial_of_contDiff hv0
  obtain ⟨-, cv1η⟩ := C1_partial_of_contDiff hv1
  obtain ⟨cwq, cwη⟩ := C1_partial_of_contDiff hw
  obtain ⟨cρq, cρη⟩ := C1_partial_of_contDiff hρ
  have cv0 := hv0.continuous; have cv1 := hv1.continuous
  have cw := hw.continuous; have cρ := hρ.continuous
  have hRq := hR.partialQ; have hRη := hR.partialEta
  -- fluxes
  obtain ⟨P, hP⟩ : ∃ P : Plane → ℝ, P = fun z => v z 0 * w z ^ 2 * ρ z := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Plane → ℝ, Q = fun z => v z 1 * w z ^ 2 * ρ z := ⟨_, rfl⟩
  obtain ⟨DP, hDP⟩ : ∃ DP : Plane → ℝ, DP = fun z =>
      partialQ (fun z => v z 0) z * w z ^ 2 * ρ z +
      v z 0 * (2 * w z * partialQ w z) * ρ z + v z 0 * w z ^ 2 * partialQ ρ z := ⟨_, rfl⟩
  obtain ⟨DQ, hDQ⟩ : ∃ DQ : Plane → ℝ, DQ = fun z =>
      partialEta (fun z => v z 1) z * w z ^ 2 * ρ z +
      v z 1 * (2 * w z * partialEta w z) * ρ z + v z 1 * w z ^ 2 * partialEta ρ z := ⟨_, rfl⟩
  have hdP : ∀ q η, HasDerivAt (fun q' => P (q', η)) (DP (q, η)) q := by
    intro q η
    have h1 := hasDerivAt_sliceQ (differentiable_component hvd 0) q η
    have h2 := hasDerivAt_sliceQ hwd q η
    have h3 := hasDerivAt_sliceQ hρd q η
    have := (h1.mul (h2.pow 2)).mul h3
    simp only [hP, hDP]
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    norm_num
    ring
  have hdQ : ∀ q η, HasDerivAt (fun η' => Q (q, η')) (DQ (q, η)) η := by
    intro q η
    have h1 := hasDerivAt_sliceEta (differentiable_component hvd 1) q η
    have h2 := hasDerivAt_sliceEta hwd q η
    have h3 := hasDerivAt_sliceEta hρd q η
    have := (h1.mul (h2.pow 2)).mul h3
    simp only [hQ, hDQ]
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    norm_num
    ring
  have iDP : IntegrableOn DP (cell c) := by
    rw [hDP]
    exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz, hRq z hz])
      (by fun_prop) c
  have iDQ : IntegrableOn DQ (cell c) := by
    rw [hDQ]
    exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz, hRη z hz])
      (by fun_prop) c
  have iQ : IntegrableOn Q (cell c) := by
    rw [hQ]
    exact VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz])
      (by fun_prop) c
  have hPper : ∀ η, P (c / 2, η) - P (-c / 2, η) = 0 := fun η => by
    rw [hP]
    simp only
    rw [(hvp.fun_comp fun x => x 0).neg_half, hwp.neg_half, hρseam, sub_self]
  have h1 : ∫ z in cell c, DP z = 0 := by
    rw [integral_cell_deriv_q hc hdP iDP]
    simp [hPper]
  have h2 : ∫ z in cell c, DQ z = 0 := integral_cell_deriv_eta hdQ iQ iDQ
  -- pointwise: DP + DQ = 2 (v·∇w) w ρ + w² v·∇ρ
  have hsum : ∀ z, DP z + DQ z =
      2 * ((v z 0 * partialQ w z + v z 1 * partialEta w z) * w z * ρ z) +
        w z ^ 2 * (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z) := by
    intro z
    have hd := hdiv z
    simp only [divergence] at hd
    simp only [hDP, hDQ]
    linear_combination (w z ^ 2 * ρ z) * hd
  have iT : IntegrableOn (fun z => (v z 0 * partialQ w z + v z 1 * partialEta w z) *
      w z * ρ z) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  have iS : IntegrableOn (fun z => w z ^ 2 *
      (v z 0 * partialQ ρ z + v z 1 * partialEta ρ z)) (cell c) :=
    VanishesOutside.integrableOn_cell (R := R) (fun z hz => by simp [hR z hz]) (by fun_prop) c
  have htot : ∫ z in cell c, (DP z + DQ z) = 0 := by
    rw [integral_add iDP iDQ, h1, h2, add_zero]
  rw [integral_congr_ae (ae_of_all _ hsum), integral_add (iT.const_mul 2) iS,
    integral_const_mul] at htot
  linarith

end UnforcedLeray.Cyl
