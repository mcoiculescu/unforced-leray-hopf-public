import UnforcedLeray.Short.PartIIa.Calc.JetClass

/-!
# Part II-a, jet-class calculus: size monotonicity and the factor `ν` (`WAlgMisc`)

Target: `UnforcedLeray.Short.PartIIa.Jet.wAlgMisc : WAlgMisc` (`Calc/JetClass.lean`).

Source of record: `the November 2 reference manuscript`, lines 1269-1272
(weighted sizes `s^{-a}` for `s ≥ 1`).

* `s^{-a} ≤ s^{-a'}` for `s ≥ 1` and `a' ≤ a` (`Real.rpow_le_rpow_of_exponent_le`), with the
  constant nonnegative (`WtdBound.nonneg`, `ExpBound` route for `WE`);
* for `0 < ν ≤ min ν₀ 1` we have `|ν X| ≤ |X|`, so the same constants serve `ν F`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.Jet

/-- Size monotonicity: a larger size index gives a smaller bound (`s ≥ 1`). -/
theorem wam_anti (a a' : ℝ) (F : Fam) (hle : a' ≤ a) (hF : WW a F) : WW a' F := by
  intro ρ m hρ
  obtain ⟨C, d, ν₀, hν₀, H⟩ := hF ρ m hρ
  refine ⟨C, d, ν₀, hν₀, fun ν hν hνle tr htr => ?_⟩
  have hB : 0 ≤ polyConst C d ν (ν ^ (-ρ)) := WtdBound.nonneg (H ν hν hνle tr htr)
  intro x hx
  have h := H ν hν hνle tr htr x hx
  have hs : x.2.2 ^ (-a) ≤ x.2.2 ^ (-a') :=
    Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hle)
  exact h.trans (mul_le_mul_of_nonneg_left hs hB)

/-- The factor `ν` (with `ν ≤ 1`) does not increase a weighted size. -/
theorem wam_nu (a : ℝ) (F : Fam) (hF : WW a F) : WW a (famNu F) := by
  intro ρ m hρ
  obtain ⟨C, d, ν₀, hν₀, H⟩ := hF ρ m hρ
  refine ⟨C, d, min ν₀ 1, lt_min hν₀ one_pos, fun ν hν hνle tr htr => ?_⟩
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hνν : ν ≤ ν₀ := hνle.trans (min_le_left _ _)
  have h := H ν hν hνν tr htr
  intro x hx
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |ν * F ν (ν ^ (-ρ)) tr x| ≤ _
  rw [abs_mul, abs_of_pos hν]
  have hw : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m := weight_nonneg m hx
  have hY : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| :=
    mul_nonneg hw (abs_nonneg _)
  have key : (1 + x.2.1 ^ 2 / x.2.2) ^ m * (ν * |F ν (ν ^ (-ρ)) tr x|) ≤
      (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| := by
    nlinarith [mul_nonneg (sub_nonneg.2 hν1) hY]
  exact key.trans (h x hx)

/-- The factor `ν` does not increase an exponentially small bound. -/
theorem wam_nuE (F : Fam) (hF : WE F) : WE (famNu F) := by
  intro ρ m hρ
  obtain ⟨C, d, κ, ν₀, hκ, hν₀, H⟩ := hF ρ m hρ
  refine ⟨C, d, κ, min ν₀ 1, hκ, lt_min hν₀ one_pos, fun ν hν hνle tr htr => ?_⟩
  have hν1 : ν ≤ 1 := hνle.trans (min_le_right _ _)
  have hνν : ν ≤ ν₀ := hνle.trans (min_le_left _ _)
  have h := H ν hν hνν tr htr
  intro x hx
  show (1 + x.2.1 ^ 2 / x.2.2) ^ m * |ν * F ν (ν ^ (-ρ)) tr x| ≤ _
  rw [abs_mul, abs_of_pos hν]
  have hw : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m := weight_nonneg m hx
  have hY : 0 ≤ (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| :=
    mul_nonneg hw (abs_nonneg _)
  have key : (1 + x.2.1 ^ 2 / x.2.2) ^ m * (ν * |F ν (ν ^ (-ρ)) tr x|) ≤
      (1 + x.2.1 ^ 2 / x.2.2) ^ m * |F ν (ν ^ (-ρ)) tr x| := by
    nlinarith [mul_nonneg (sub_nonneg.2 hν1) hY]
  exact key.trans (h x hx)

/-- **Size monotonicity and the factor `ν`** (`WAlgMisc`). -/
theorem wAlgMisc : WAlgMisc := by
  unfold WAlgMisc
  exact ⟨fun a a' F h hF => wam_anti a a' F h hF, fun a F hF => wam_nu a F hF,
    fun F hF => wam_nuE F hF⟩

end UnforcedLeray.Short.PartIIa.Jet
