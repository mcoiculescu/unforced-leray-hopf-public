import UnforcedLeray.Short.PartIIb.Sub.T22_4

/-!
# Part II-b, task `PartII-b:T22/4/5`: removing the cut-off (`DbLimitStmt`)

Source of record: `the November 2 reference manuscript`, lines 2092-2104.
Given the integrability leaves `DbInt1`, `DbInt2`, the cut-off identity `DbCutId` and a family of
cut-offs `DbCutoff`, prove `DbIdentity` by letting `n → ∞`:

* the three bulk integrands are dominated by integrable functions and `χ_n(η)² → 1` pointwise
  (dominated convergence, `dbl_cut_tendsto`);
* the transport-type term `∫ 2 χ_n χ_n' h` with `h = g w ∂_η g` is bounded by
  `(2|K|/(n+1)) ∫ |h|` (`dbl_E_tendsto`), and `h` is integrable because
  `|g ∂_η g w| ≤ (g² w + w(∂_q g² + ∂_η g²))/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- Dominated convergence for the cut-off family: `∫ χ_n(η)² F → ∫ F` for integrable `F` on the
cell, since `χ_n = 1` on `[-n, n]` and `0 ≤ χ_n² ≤ 1`. -/
theorem dbl_cut_tendsto (c : ℝ) (χ : ℕ → ℝ → ℝ) (hχc : ∀ n, Continuous (χ n))
    (hχ01 : ∀ n t, 0 ≤ χ n t ∧ χ n t ≤ 1) (hχ1 : ∀ n : ℕ, ∀ t ∈ Icc (-(n : ℝ)) n, χ n t = 1)
    (F : B0579.Plane → ℝ) (hF : IntegrableOn F (B0579.cell c)) :
    Tendsto (fun n : ℕ => ∫ x in B0579.cell c, χ n x.2 ^ 2 * F x) atTop
      (𝓝 (∫ x in B0579.cell c, F x)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖) ?_ ?_
    (Integrable.norm hF) ?_
  · exact Eventually.of_forall fun n =>
      (((hχc n).comp continuous_snd).pow 2).aestronglyMeasurable.mul
        (Integrable.aestronglyMeasurable hF)
  · refine Eventually.of_forall fun n => ae_of_all _ fun x => ?_
    have h0 := hχ01 n x.2
    have hsq : χ n x.2 ^ 2 ≤ 1 := by nlinarith [h0.1, h0.2]
    have hsq0 : 0 ≤ χ n x.2 ^ 2 := sq_nonneg _
    rw [norm_mul, Real.norm_of_nonneg hsq0]
    exact mul_le_of_le_one_left (norm_nonneg _) hsq
  · refine ae_of_all _ fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|x.2|⌉₊] with n hn
    have hmem : x.2 ∈ Icc (-(n : ℝ)) n := by
      have h1 : |x.2| ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      exact abs_le.1 h1
    rw [hχ1 n x.2 hmem]
    simp

/-- The cut-off term `∫ 2 χ_n χ_n' h` tends to `0` when `h` is integrable on the cell and
`|χ_n'| ≤ K/(n+1)`. -/
theorem dbl_E_tendsto (c : ℝ) (χ : ℕ → ℝ → ℝ) (K : ℝ)
    (hχ01 : ∀ n t, 0 ≤ χ n t ∧ χ n t ≤ 1)
    (hK : ∀ (n : ℕ) (t : ℝ), |deriv (χ n) t| ≤ K / ((n : ℝ) + 1))
    (h : B0579.Plane → ℝ) (hh : IntegrableOn h (B0579.cell c)) :
    Tendsto (fun n : ℕ => ∫ x in B0579.cell c, 2 * χ n x.2 * deriv (χ n) x.2 * h x) atTop
      (𝓝 0) := by
  have hbound : ∀ n : ℕ,
      ‖∫ x in B0579.cell c, 2 * χ n x.2 * deriv (χ n) x.2 * h x‖
        ≤ (2 * |K| * (∫ x in B0579.cell c, ‖h x‖)) * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpt : ∀ x : B0579.Plane,
        ‖2 * χ n x.2 * deriv (χ n) x.2 * h x‖ ≤ (2 * |K| / ((n : ℝ) + 1)) * ‖h x‖ := by
      intro x
      have ha : |χ n x.2| ≤ 1 :=
        abs_le.2 ⟨by linarith [(hχ01 n x.2).1], (hχ01 n x.2).2⟩
      have hb : |deriv (χ n) x.2| ≤ |K| / ((n : ℝ) + 1) :=
        (hK n x.2).trans (by gcongr; exact le_abs_self K)
      simp only [Real.norm_eq_abs, abs_mul, abs_two]
      calc 2 * |χ n x.2| * |deriv (χ n) x.2| * |h x|
          ≤ 2 * 1 * (|K| / ((n : ℝ) + 1)) * |h x| := by gcongr
        _ = (2 * |K| / ((n : ℝ) + 1)) * |h x| := by ring
    have h1 := norm_integral_le_of_norm_le
      ((Integrable.norm hh).const_mul (2 * |K| / ((n : ℝ) + 1))) (ae_of_all _ hpt)
    rw [integral_const_mul] at h1
    calc _ ≤ _ := h1
      _ = (2 * |K| * (∫ x in B0579.cell c, ‖h x‖)) * (1 / ((n : ℝ) + 1)) := by ring
  have hlim : Tendsto (fun n : ℕ => (2 * |K| * (∫ x in B0579.cell c, ‖h x‖)) * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (2 * |K| * (∫ x in B0579.cell c, ‖h x‖))
  exact squeeze_zero_norm hbound hlim

/-- **Leaf 5 of `PartII-b:T22/4` (SP 2103-2104): removing the cut-off.** -/
theorem dbLimit : UnforcedLeray.Short.IIb.DbLimitStmt := by
  intro h1 h2 h3 h4 m hm c hc g hg
  obtain ⟨χ, hχc, hχs, hχ01, hχ1, K, hK⟩ := h4
  obtain ⟨i1, i2⟩ := h1 m hm c hc g hg
  obtain ⟨j1, j2⟩ := h2 m hm c hc g hg
  have hgc : Continuous g := hg.smooth.continuous
  have hp1 : Continuous (B0579.pd 1 g) :=
    (hg.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdens : Continuous (fun x => (B0579.density m x : ℝ)) :=
    NNReal.continuous_coe.comp (B0579.continuous_density m)
  have hhc : Continuous (fun x => g x * (B0579.density m x : ℝ) * B0579.pd 1 g x) :=
    (hgc.mul hdens).mul hp1
  have hh : IntegrableOn (fun x => g x * (B0579.density m x : ℝ) * B0579.pd 1 g x)
      (B0579.cell c) := by
    have hb : Integrable (fun x => (1 / 2 : ℝ) * (g x ^ 2 * (B0579.density m x : ℝ)) +
        (1 / 2 : ℝ) * ((B0579.density m x : ℝ) * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)))
        (volume.restrict (B0579.cell c)) :=
      (Integrable.const_mul i1 (1 / 2 : ℝ)).add (Integrable.const_mul j1 (1 / 2 : ℝ))
    refine Integrable.mono' hb hhc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have hd : (0 : ℝ) ≤ (B0579.density m x : ℝ) := NNReal.coe_nonneg _
    have hA : |g x * B0579.pd 1 g x| ≤ (g x ^ 2 + B0579.pd 1 g x ^ 2) / 2 :=
      abs_le.2 ⟨by nlinarith [sq_nonneg (g x + B0579.pd 1 g x)],
        by nlinarith [sq_nonneg (g x - B0579.pd 1 g x)]⟩
    have e : g x * (B0579.density m x : ℝ) * B0579.pd 1 g x
        = (g x * B0579.pd 1 g x) * (B0579.density m x : ℝ) := by ring
    rw [Real.norm_eq_abs, e, abs_mul, abs_of_nonneg hd]
    nlinarith [mul_le_mul_of_nonneg_right hA hd, mul_nonneg hd (sq_nonneg (B0579.pd 0 g x))]
  have L1 : Tendsto (fun n : ℕ => ∫ x in B0579.cell c,
      χ n x.2 ^ 2 * (g x * lapP g x * (B0579.density m x : ℝ))) atTop
      (𝓝 (∫ x in B0579.cell c, g x * lapP g x * (B0579.density m x : ℝ))) :=
    dbl_cut_tendsto c χ (fun n => (hχc n).continuous) hχ01 hχ1 _ i2
  have L2 : Tendsto (fun n : ℕ => ∫ x in B0579.cell c,
      χ n x.2 ^ 2 * ((B0579.density m x : ℝ) * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2))) atTop
      (𝓝 (∫ x in B0579.cell c,
        (B0579.density m x : ℝ) * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2))) :=
    dbl_cut_tendsto c χ (fun n => (hχc n).continuous) hχ01 hχ1 _ j1
  have L3 : Tendsto (fun n : ℕ => ∫ x in B0579.cell c,
      χ n x.2 ^ 2 * (g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
        B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x))) atTop
      (𝓝 (∫ x in B0579.cell c, g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
        B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x))) :=
    dbl_cut_tendsto c χ (fun n => (hχc n).continuous) hχ01 hχ1 _ j2
  have L4 : Tendsto (fun n : ℕ => ∫ x in B0579.cell c,
      2 * χ n x.2 * deriv (χ n) x.2 * (g x * (B0579.density m x : ℝ) * B0579.pd 1 g x)) atTop
      (𝓝 0) :=
    dbl_E_tendsto c χ K hχ01 hK _ hh
  have hid : ∀ n : ℕ, (∫ x in B0579.cell c,
        χ n x.2 ^ 2 * (g x * lapP g x * (B0579.density m x : ℝ)))
      = -(∫ x in B0579.cell c,
          χ n x.2 ^ 2 * ((B0579.density m x : ℝ) * (B0579.pd 0 g x ^ 2 + B0579.pd 1 g x ^ 2)))
        - (∫ x in B0579.cell c,
          χ n x.2 ^ 2 * (g x * (B0579.pd 0 (fun y => B0579.jb y ^ m) x * B0579.pd 0 g x +
            B0579.pd 1 (fun y => B0579.jb y ^ m) x * B0579.pd 1 g x)))
        - (∫ x in B0579.cell c,
          2 * χ n x.2 * deriv (χ n) x.2 * (g x * (B0579.density m x : ℝ) * B0579.pd 1 g x)) :=
    fun n => h3 m hm c hc g hg (χ n) (hχc n) (hχs n)
  have hR := ((L2.neg).sub L3).sub L4
  have hlim := Tendsto.congr (fun n => (hid n).symm) hR
  have key := tendsto_nhds_unique L1 hlim
  linarith

end UnforcedLeray.Short.IIb
