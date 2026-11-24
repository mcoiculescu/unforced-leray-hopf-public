import UnforcedLeray.Lib.Axisymmetric.Cylindrical

/-!
# Exponent bookkeeping for the far product rule (helper for `ProdHom`)

Source `the November 2 reference manuscript`
lines 2542-2549, 2563-2569. Each product of a raw factor `ϱ^{-(1+a)} s^M` and an inlet factor
`ϱ^{-(1+b)} s^{-(M+2)}` with `a + b = 2` is `≤ c ϱ^{-4} s^{-2} ≤ c ϱ^{-3} s^{-2}` for `ϱ ≥ 1`,
where `s = 1 + |y₃|/ϱ ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.ProdHom

/-- A product of two far-field bounds of total derivative order `2` (homogeneity `ϱ^{-4}`,
transverse weight `s^{-2}`), dominated by the `ϱ^{-3}s^{-2}` envelope for `ϱ ≥ 1`. -/
theorem prod_bound (X Y c1 c2 ρ s : ℝ) (M a b : ℕ) (hab : a + b = 2) (hρ : 1 ≤ ρ) (hs : 1 ≤ s)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hY0 : 0 ≤ Y)
    (hX : X ≤ c1 * (ρ ^ (-(1 + (a : ℝ))) * s ^ M))
    (hY : Y ≤ c2 * (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) :
    X * Y ≤ (c1 * c2) * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  have hs0 : 0 < s := by linarith
  have hab' : (a : ℝ) + (b : ℝ) = 2 := by exact_mod_cast hab
  have hAB : ρ ^ (-(1 + (a : ℝ))) * s ^ M * (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))
      = ρ ^ (-4 : ℝ) * s ^ (-2 : ℝ) := by
    have h1 : ρ ^ (-(1 + (a : ℝ))) * ρ ^ (-(1 + (b : ℝ))) = ρ ^ (-4 : ℝ) := by
      rw [← Real.rpow_add hρ0]
      congr 1
      linarith
    have h2 : s ^ M * s ^ (-((M + 2 : ℕ) : ℝ)) = s ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast s M, ← Real.rpow_add hs0]
      congr 1
      push_cast
      ring
    calc ρ ^ (-(1 + (a : ℝ))) * s ^ M * (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))
        = (ρ ^ (-(1 + (a : ℝ))) * ρ ^ (-(1 + (b : ℝ)))) *
            (s ^ M * s ^ (-((M + 2 : ℕ) : ℝ))) := by ring
      _ = ρ ^ (-4 : ℝ) * s ^ (-2 : ℝ) := by rw [h1, h2]
  have hA : 0 ≤ ρ ^ (-(1 + (a : ℝ))) * s ^ M := by positivity
  have hρ4 : ρ ^ (-4 : ℝ) ≤ ρ ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
  have hs2 : 0 ≤ s ^ (-2 : ℝ) := by positivity
  calc X * Y ≤ (c1 * (ρ ^ (-(1 + (a : ℝ))) * s ^ M)) *
        (c2 * (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) :=
          mul_le_mul hX hY hY0 (mul_nonneg hc1 hA)
    _ = (c1 * c2) * (ρ ^ (-(1 + (a : ℝ))) * s ^ M *
        (ρ ^ (-(1 + (b : ℝ))) * s ^ (-((M + 2 : ℕ) : ℝ)))) := by ring
    _ = (c1 * c2) * (ρ ^ (-4 : ℝ) * s ^ (-2 : ℝ)) := by rw [hAB]
    _ ≤ (c1 * c2) * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ4 hs2) (mul_nonneg hc1 hc2)

/-- A single inlet factor of total order `3` (`ϱ^{-4}`, transverse weight `s^{-N}`, `N ≥ 2`),
dominated by the `ϱ^{-3}s^{-2}` envelope for `ϱ ≥ 1`. -/
theorem single_bound (Y c ρ s : ℝ) (N : ℕ) (hN : 2 ≤ N) (hρ : 1 ≤ ρ) (hs : 1 ≤ s)
    (hc : 0 ≤ c)
    (hY : Y ≤ c * (ρ ^ (-(1 + ((3 : ℕ) : ℝ))) * s ^ (-((N : ℕ) : ℝ)))) :
    Y ≤ c * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) := by
  have hρ0 : 0 < ρ := by linarith
  have hs0 : 0 < s := by linarith
  have hr : ρ ^ (-(1 + ((3 : ℕ) : ℝ))) = ρ ^ (-4 : ℝ) := by norm_num
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsN : s ^ (-((N : ℕ) : ℝ)) ≤ s ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have hρ4 : ρ ^ (-4 : ℝ) ≤ ρ ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hρ (by norm_num)
  have hρ4' : 0 ≤ ρ ^ (-4 : ℝ) := by positivity
  have hs2 : 0 ≤ s ^ (-2 : ℝ) := by positivity
  calc Y ≤ c * (ρ ^ (-(1 + ((3 : ℕ) : ℝ))) * s ^ (-((N : ℕ) : ℝ))) := hY
    _ = c * (ρ ^ (-4 : ℝ) * s ^ (-((N : ℕ) : ℝ))) := by rw [hr]
    _ ≤ c * (ρ ^ (-4 : ℝ) * s ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsN hρ4') hc
    _ ≤ c * (ρ ^ (-3 : ℝ) * s ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ4 hs2) hc

end UnforcedLeray.Short.PartIIIb.Concrete.ProdHom
