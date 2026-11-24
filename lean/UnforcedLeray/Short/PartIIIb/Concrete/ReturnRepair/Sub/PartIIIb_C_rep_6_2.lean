import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6_1.SigmaW

/-!
# `N0wLeN1`: the cut old moment is bounded by the first moment (`PartIII-b:C/rep/6/2`)

Source: `the November 2 reference manuscript` lines 4924-4927 and 5400.

`oldN0w c ν χ_o M = ∫_{u>6/(5ν)} u^{-3/2} χ_o(νu) ∫|M(u,·)| d(dq dη/c)` is bounded by the
age-weighted first moment `IIIa.firstMoment c 0 (χ_o(ν·) M)`:

* Cauchy-Schwarz in `q` with the probability measure `dq/c` (`w2_cs`, proved by the
  inequality `2tB ≤ A + t²` for all `t > 0`, so no measurability is needed);
* Tonelli `∫_cell ≤ ∫dη ∫dq` (`lintegral_prod_le`, valid without measurability);
* `frob(χ•M) = χ frob M` for `χ ≥ 0`, and `1 ≤ 1 + |η|/√s`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `frobSq X = frob X ^ 2`. -/
theorem w2_frob_sq (X : Mat3) :
    UnforcedLeray.Short.IIIa.frobSq (X : Matrix (Fin 3) (Fin 3) ℝ) = frob X ^ 2 := by
  unfold frob UnforcedLeray.Short.IIIa.frobSq
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]

/-- Scalar multiples of the Frobenius norm. -/
theorem w2_frob_smul (a : ℝ) (ha : 0 ≤ a) (X : Mat3) : frob (a • X) = a * frob X := by
  rw [rj6_frob_smul, abs_of_nonneg ha]

/-- Abstract form of the Cauchy-Schwarz step: `B² ≤ A` from `2tB ≤ A + t²` for all `t > 0`. -/
theorem w2_cs_aux (A B : ℝ≥0∞)
    (key : ∀ t : ℝ, 0 < t → ENNReal.ofReal (2 * t) * B ≤ A + ENNReal.ofReal (t ^ 2)) :
    B ^ 2 ≤ A := by
  rcases eq_or_ne A ⊤ with hAt | hAt
  · rw [hAt]; exact le_top
  rcases eq_or_ne B ⊤ with hBt | hBt
  · exfalso
    have h1 := key 1 one_pos
    rw [hBt, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by norm_num)).ne'] at h1
    exact absurd h1 (not_le.2 (ENNReal.add_lt_top.2 ⟨hAt.lt_top, ENNReal.ofReal_lt_top⟩))
  rcases eq_or_ne B 0 with hB0 | hB0
  · rw [hB0]; simp
  obtain ⟨t, ht_eq⟩ : ∃ t : ℝ, t = B.toReal := ⟨_, rfl⟩
  have ht : 0 < t := by rw [ht_eq]; exact ENNReal.toReal_pos hB0 hBt
  have hBt' : B = ENNReal.ofReal t := by rw [ht_eq, ENNReal.ofReal_toReal hBt]
  have h1 := key t ht
  have h2 : ENNReal.ofReal (2 * t) * B = ENNReal.ofReal (t ^ 2) + ENNReal.ofReal (t ^ 2) := by
    rw [hBt', ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * t),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [h2] at h1
  have h3 : ENNReal.ofReal (t ^ 2) ≤ A := ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h1
  calc B ^ 2 = ENNReal.ofReal (t ^ 2) := by rw [hBt', ENNReal.ofReal_pow ht.le]
    _ ≤ A := h3

/-- Cauchy-Schwarz for the probability measure `dq/c` on `[-c/2, c/2)`:
`(∫ dq/c |F|)² ≤ ∫ dq/c F²`, in `ℝ≥0∞`, with no measurability hypothesis. -/
theorem w2_cs {c : ℝ} (hc : 0 < c) (F : ℝ → ℝ) :
    (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q)) ^ 2 ≤
      ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q ^ 2) := by
  apply w2_cs_aux
  intro t ht
  have hw1 : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  have hvol : volume (Ico (-(c / 2)) (c / 2)) = ENNReal.ofReal c := by
    rw [Real.volume_Ico]; congr 1; ring
  have hpt : ∀ q : ℝ, ENNReal.ofReal (2 * t) * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q)) ≤
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q ^ 2) +
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (t ^ 2) := by
    intro q
    calc ENNReal.ofReal (2 * t) * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q))
        = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (2 * t * F q) := by
          rw [ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * t)]; ring
      _ ≤ ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q ^ 2 + t ^ 2) :=
          mul_le_mul_of_nonneg_left
            (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (F q - t)])) zero_le
      _ = ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q ^ 2) +
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal (t ^ 2) := by
          rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), mul_add]
  calc ENNReal.ofReal (2 * t) *
        ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q)
      = ∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal (2 * t) * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q)) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ q in Ico (-(c / 2)) (c / 2),
          (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q ^ 2) +
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal (t ^ 2)) :=
        lintegral_mono hpt
    _ = (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * ENNReal.ofReal (F q ^ 2)) +
          ENNReal.ofReal (t ^ 2) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, hvol]
        congr 1
        calc ENNReal.ofReal c⁻¹ * ENNReal.ofReal (t ^ 2) * ENNReal.ofReal c
            = ENNReal.ofReal (t ^ 2) * (ENNReal.ofReal c⁻¹ * ENNReal.ofReal c) := by ring
          _ = ENNReal.ofReal (t ^ 2) := by rw [hw1, mul_one]

/-- From `B² ≤ A` to `B ≤ A^{1/2}`. -/
theorem w2_root (A B : ℝ≥0∞) (h : B ^ 2 ≤ A) : B ≤ A ^ (1 / 2 : ℝ) := by
  calc B = (B ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ A ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)

/-- The per-age bound: the cut Bochner integral at age `s` is bounded by the `η`-integral in
the first moment (source 4924-4927, 5400). -/
theorem w2_pt {c ν : ℝ} (hc : 0 < c) (χo : ℝ → ℝ) (hχ : IsOutwardCutoff χo) (M : Chart → Mat3)
    (s : ℝ) :
    ENNReal.ofReal (χo (ν * s) * ∫ x, frob (M (s, x)) ∂(Cyl.avgμ c)) ≤
      ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) *
        (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq
            ((fun p : Chart => χo (ν * p.1) • M p : Chart → Matrix (Fin 3) (Fin 3) ℝ)
              (s, (q, η))))) ^ (1 / 2 : ℝ) := by
  have hχ0 : 0 ≤ χo (ν * s) := (hχ.range _).1
  by_cases hI : Integrable (fun x => frob (M (s, x))) (Cyl.avgμ c)
  swap
  · rw [integral_undef hI, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  have hG : ENNReal.ofReal (∫ x, frob (M (s, x)) ∂(Cyl.avgμ c)) ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ η, ∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal (frob (M (s, (q, η)))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun x => frob_nonneg' _),
      Cyl.lintegral_avgμ, Cyl.volume_restrict_cell, show (-c / 2 : ℝ) = -(c / 2) by ring]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc ∫⁻ z, ENNReal.ofReal (frob (M (s, z)))
          ∂((volume.restrict (Ico (-(c / 2)) (c / 2))).prod volume)
        = ∫⁻ z, ENNReal.ofReal (frob (M (s, z.swap)))
            ∂(volume.prod (volume.restrict (Ico (-(c / 2)) (c / 2)))) :=
          (lintegral_prod_swap (fun z : ℝ × ℝ => ENNReal.ofReal (frob (M (s, z))))).symm
      _ ≤ ∫⁻ η, ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal (frob (M (s, (q, η)))) :=
          lintegral_prod_le (fun z : ℝ × ℝ => ENNReal.ofReal (frob (M (s, z.swap))))
  have hpt : ∀ η q : ℝ, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frob (χo (ν * s) • M (s, (q, η))))
      = ENNReal.ofReal (χo (ν * s)) *
          (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frob (M (s, (q, η))))) := by
    intro η q
    rw [w2_frob_smul _ hχ0, ENNReal.ofReal_mul hχ0]; ring
  have he : ∫⁻ η, ∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frob (χo (ν * s) • M (s, (q, η)))) =
      ENNReal.ofReal (χo (ν * s)) * (ENNReal.ofReal c⁻¹ * ∫⁻ η, ∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal (frob (M (s, (q, η))))) := by
    simp only [hpt, lintegral_const_mul', ENNReal.ofReal_ne_top, ne_eq, not_false_eq_true]
  have hstep : ENNReal.ofReal (χo (ν * s) * ∫ x, frob (M (s, x)) ∂(Cyl.avgμ c)) ≤
      ∫⁻ η, ∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frob (χo (ν * s) • M (s, (q, η)))) := by
    rw [ENNReal.ofReal_mul hχ0, he]
    exact mul_le_mul_of_nonneg_left hG zero_le
  have hη : ∀ η : ℝ,
      (∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frob (χo (ν * s) • M (s, (q, η))))) ≤
      ENNReal.ofReal (1 + |η| / Real.sqrt s) *
        (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq
            ((fun p : Chart => χo (ν * p.1) • M p : Chart → Matrix (Fin 3) (Fin 3) ℝ)
              (s, (q, η))))) ^ (1 / 2 : ℝ) := by
    intro η
    have hA : (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq
            ((fun p : Chart => χo (ν * p.1) • M p : Chart → Matrix (Fin 3) (Fin 3) ℝ)
              (s, (q, η))))) =
        ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ *
          ENNReal.ofReal (frob (χo (ν * s) • M (s, (q, η))) ^ 2) :=
      lintegral_congr fun q => by rw [w2_frob_sq]
    rw [hA]
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + |η| / Real.sqrt s) :=
      ENNReal.one_le_ofReal.2 (le_add_of_nonneg_right (div_nonneg (abs_nonneg η) (Real.sqrt_nonneg s)))
    exact le_trans (w2_root _ _ (w2_cs hc (fun q => frob (χo (ν * s) • M (s, (q, η))))))
      (le_mul_of_one_le_left zero_le h1)
  calc ENNReal.ofReal (χo (ν * s) * ∫ x, frob (M (s, x)) ∂(Cyl.avgμ c))
      ≤ ∫⁻ η, ∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frob (χo (ν * s) • M (s, (q, η)))) := hstep
    _ ≤ _ := lintegral_mono hη

/-- **`N0wLeN1`** (`PartIII-b:C/rep/6/2`): `N₀^χ(M) ≤ 𝒩₁(χ_o M)`. -/
theorem n0wLeN1 : UnforcedLeray.Short.PartIIIb.Concrete.N0wLeN1 := by
  intro c ν χo hc hν hχ M hM
  have hI := w_int hν hχ M hM
  have ha : (0 : ℝ) < 6 / 5 / ν := div_pos (by norm_num) hν
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (6 / 5 / ν))] fun u : ℝ =>
      u ^ (-(3 / 2 : ℝ)) * (χo (ν * u) * ∫ x, frob (M (u, x)) ∂(Cyl.avgμ c)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg (ha.trans (Set.mem_Ioi.1 hu)).le _)
      (mul_nonneg (hχ.range _).1 (integral_nonneg fun x => frob_nonneg' _))
  have hexp : (-3 / 2 : ℝ) = -(3 / 2 : ℝ) := by norm_num
  unfold oldN0w UnforcedLeray.Short.IIIa.firstMoment
  rw [ofReal_integral_eq_lintegral_ofReal hI hnn, hexp]
  refine le_trans (lintegral_mono_ae ?_) (lintegral_mono_set (Set.Ioi_subset_Ioi ha.le))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := ha.trans (Set.mem_Ioi.1 hs)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le _)]
  exact mul_le_mul_of_nonneg_left (w2_pt (c := c) (ν := ν) hc χo hχ M s) zero_le

end UnforcedLeray.Short.PartIIIb.Concrete
