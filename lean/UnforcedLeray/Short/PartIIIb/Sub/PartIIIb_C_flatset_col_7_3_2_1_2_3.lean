import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivOf

/-!
# `T0adjFormulaDom` reduced to three source facts
(task `PartIII-b:C/flatset/col/7/3/2/1/2/3`)

Source `the November 2 reference manuscript` 1650-1656:
`T₀(t)*f(s) = e^{-t/2} e^{νs(eᵗ-1)Δ} f(seᵗ)`.  For `u = A₀*ζ` in the band `[s₀,s₁] × |η| ≤ L`,
`|u| ≤ M`, and near `t` the formula is nonzero only for ages `s ∈ [a,b]`, with heat age
`θ ≤ Θ`; the planar heat moment bound gives `(1+η²)|e^{θΔ}v| ≤ M(1+2L²+8θ)`, so the formula is
dominated by `C 1_{[a,b]}(s)(1+η²)⁻¹ ∈ L²(H)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIa (IsMeridTest pdS pdQ pdEta)

/-- **Planar heat moment bound** (source 1650-1656; second Gaussian moment
`∫ G_θ‖y‖² = 4θ` on `ℝ²`): a function `v` of `(q,η)` bounded by `M` and vanishing for
`|η| > L` satisfies `(1+η²)‖e^{θΔ}v(q,η)‖ ≤ M(1+2L²+8θ)`, because where `v(x-ιy) ≠ 0` one has
`|x₁ - y₁| ≤ L`, so `1 + x₁² ≤ 1 + 2L² + 2‖y‖²`. -/
def PlaneHeatMoment : Prop :=
  ∀ (θ L M : ℝ), 0 < θ → ∀ v : ℝ × ℝ → MeridC, (∀ z, ‖v z‖ ≤ M) →
    (∀ z : ℝ × ℝ, L < |z.2| → v z = 0) → ∀ x : ℝ × ℝ,
      (1 + x.2 ^ 2) * ‖UnforcedLeray.B0224.planeHeat θ v x‖ ≤ M * (1 + 2 * L ^ 2 + 8 * θ)

/-- **The `L²(H)` majorant** (source 1650-1656; `measureH c = (volume|cell).withDensity s^{-3/2}`):
`C·1_{[a,b]}(s)(1+η²)⁻¹ ∈ L²(measureH c)` for `0 < a`. -/
def MemLpMajorant : Prop :=
  ∀ (c a b C : ℝ), 0 < c → 0 < a →
    MemLp (fun p : Profile => C * (Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * (1 + p.2.2 ^ 2)⁻¹)
      2 (measureH c)

/-- **Smooth band tests are bounded** (source 1650-1656): `ζ` is continuous, `c`-periodic in `q`
and vanishes off `s ∈ [s₀,s₁]`, `|η| ≤ L`, hence is bounded (max on the compact
`[s₀,s₁] × [0,c] × [-L,L]` and periodic reduction `periodic_reduceIoc_eq`). -/
def MeridTestBounded : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ f : Profile → MeridC, IsMeridTest c f → ∃ M : ℝ, ∀ p, ‖f p‖ ≤ M

/-- **Reduction of `T0adjFormulaDom`** to the heat moment bound, the `L²` majorant and the
boundedness of smooth band tests (source 1650-1656). -/
theorem t0adj_formula_dom_of (h1 : PlaneHeatMoment) (h2 : MemLpMajorant)
    (h3 : MeridTestBounded) : T0adjFormulaDom := by
  intro c ν hc hν ζ hζ t ht
  have hu : IsMeridTest c (A0adj ν ζ) := isMeridTest_A0adj ν hζ
  obtain ⟨s0, s1, L, hs0, hb⟩ := hu.band
  obtain ⟨M, hM⟩ := h3 c hc _ hu
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set ε : ℝ := t / 2 with hε
  have hε0 : 0 < ε := by positivity
  set a : ℝ := s0 * Real.exp (-(t + ε)) with ha
  set b : ℝ := s1 * Real.exp (-(t - ε)) with hbdef
  set Θ : ℝ := ν * b * (Real.exp (t + ε) - 1) with hΘ
  set C : ℝ := M * (1 + 2 * L ^ 2 + 8 * Θ) with hC
  have ha0 : 0 < a := mul_pos hs0 (Real.exp_pos _)
  refine ⟨ε, hε0, _, h2 c a b C hc ha0, ?_⟩
  filter_upwards [ae_measureH_age_pos c] with p hp1 r hr
  have hr0 : 0 < r := by linarith [hr.1]
  have hexp1 : 1 < Real.exp r := Real.one_lt_exp_iff.mpr hr0
  have hinv : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add]; simp
  have hper : ∀ z : ℝ × ℝ, UnforcedLeray.B0220.periodize c (A0adj ν ζ) (Real.exp r * p.1, z) =
      A0adj ν ζ (Real.exp r * p.1, z) := fun z => by
    rw [UnforcedLeray.B0220.periodize_of_periodic _ hu.periodic]
  have hform : t0adjFormula c ν r (A0adj ν ζ) p =
      Real.exp (-r / 2) • UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp r - 1))
        (fun z => A0adj ν ζ (Real.exp r * p.1, z)) p.2 := by
    unfold t0adjFormula
    simp only [hper]
  have hexple : ‖Real.exp (-r / 2)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hnorm : ‖t0adjFormula c ν r (A0adj ν ζ) p‖ ≤
      ‖UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp r - 1))
        (fun z => A0adj ν ζ (Real.exp r * p.1, z)) p.2‖ := by
    rw [hform, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) hexple
  by_cases hab : p.1 ∈ Icc a b
  · have hθ : 0 < ν * p.1 * (Real.exp r - 1) :=
      mul_pos (mul_pos hν hp1) (by linarith)
    have hb0 : 0 < b := lt_of_lt_of_le hp1 hab.2
    have hθΘ : ν * p.1 * (Real.exp r - 1) ≤ Θ := by
      rw [hΘ]
      refine mul_le_mul (mul_le_mul_of_nonneg_left hab.2 hν.le)
        (sub_le_sub_right (Real.exp_le_exp.2 hr.2.le) _) (by linarith) (by positivity)
    have hmom := h1 _ L M hθ (fun z => A0adj ν ζ (Real.exp r * p.1, z)) (fun z => hM _) (fun z hz => by
      by_contra hne
      have := (hb _ hne).2
      simp only at hz this
      linarith) p.2
    have hpos : 0 < 1 + p.2.2 ^ 2 := by positivity
    have hCle : M * (1 + 2 * L ^ 2 + 8 * (ν * p.1 * (Real.exp r - 1))) ≤ C := by
      rw [hC]
      exact mul_le_mul_of_nonneg_left (by linarith) hM0
    have hPn : ‖UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp r - 1))
        (fun z => A0adj ν ζ (Real.exp r * p.1, z)) p.2‖ ≤ C * (1 + p.2.2 ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      nlinarith [hmom, hCle]
    refine hnorm.trans (hPn.trans (le_of_eq ?_))
    simp [Set.indicator_of_mem hab]
  · have hv0 : ∀ z : ℝ × ℝ, A0adj ν ζ (Real.exp r * p.1, z) = 0 := by
      intro z
      by_contra hne
      apply hab
      have h1' := (hb _ hne).1
      simp only at h1'
      have hep : 0 ≤ Real.exp r * p.1 := by positivity
      have e1 : p.1 = Real.exp (-r) * (Real.exp r * p.1) := by
        rw [← mul_assoc, hinv, one_mul]
      constructor
      · calc a = s0 * Real.exp (-(t + ε)) := rfl
          _ ≤ (Real.exp r * p.1) * Real.exp (-(t + ε)) :=
              mul_le_mul_of_nonneg_right h1'.1 (Real.exp_pos _).le
          _ ≤ (Real.exp r * p.1) * Real.exp (-r) :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [hr.2])) hep
          _ = p.1 := by rw [mul_comm]; exact e1.symm
      · calc p.1 = Real.exp (-r) * (Real.exp r * p.1) := e1
          _ ≤ Real.exp (-(t - ε)) * (Real.exp r * p.1) :=
              mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith [hr.1])) hep
          _ ≤ Real.exp (-(t - ε)) * s1 :=
              mul_le_mul_of_nonneg_left h1'.2 (Real.exp_pos _).le
          _ = b := by rw [hbdef, mul_comm]
    have hz : UnforcedLeray.B0224.planeHeat (ν * p.1 * (Real.exp r - 1))
        (fun z => A0adj ν ζ (Real.exp r * p.1, z)) p.2 = 0 := by
      have hfun : (fun z : ℝ × ℝ => A0adj ν ζ (Real.exp r * p.1, z)) = fun _ => 0 :=
        funext hv0
      rw [hfun]
      by_cases hθ : 0 < ν * p.1 * (Real.exp r - 1)
      · rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]; simp
      · rw [UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 hθ)]
    rw [hz, norm_zero] at hnorm
    have : (Icc a b).indicator (fun _ => (1 : ℝ)) p.1 = 0 := Set.indicator_of_notMem hab _
    simp only [this, mul_zero, zero_mul]
    exact hnorm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
