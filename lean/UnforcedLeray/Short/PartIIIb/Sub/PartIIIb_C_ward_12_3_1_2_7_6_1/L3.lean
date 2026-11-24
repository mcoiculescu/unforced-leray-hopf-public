import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Main

/-!
# `NvSecondPt`: second-derivative pointwise bound of the ring lift

Source `the November 2 reference manuscript`
lines 2385-2387, 2562-2564, 2347-2369.  From `nv_jets` (order `2`: `‖D²Nv‖ ≲ Cm ϱ⁻³ W²`),
`age^{3/2} = R³ ϱ⁻³`, and locality (`nv_eventually_zero`) on the axis and on `{age > T}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Axi

theorem nvSecondPt : NvSecondPt := by
  intro R hR
  obtain ⟨K, hK, hjet⟩ := nv_jets hR
  refine ⟨K / R ^ 3, by positivity, ?_⟩
  intro c T C κ b hyp j k τ y
  obtain ⟨hbs, -, hvan, hjets⟩ := hyp
  have hC0 : 0 ≤ C := by
    have h := hjets 0 (by norm_num) (0, (0, 0))
    have h0 : 0 ≤ ‖iteratedFDeriv ℝ 0 b (0, (0, 0))‖ := norm_nonneg _
    have he := Real.exp_pos (-(κ * |((0, (0, 0)) : ℝ × (ℝ × ℝ)).2.2| / c))
    by_contra hneg
    push Not at hneg
    nlinarith
  have hNvs : ContDiff ℝ ∞ (fun p : ℝ × Space => Axi.Nv R b p.1 p.2) :=
    IIb.NicePT.contDiff_Nv hR hbs (s1 := T) (fun x hx => hvan x hx.le)
  have hΦ : ContDiff ℝ ∞ (fun x : ℝ × Space =>
      UnforcedLeray.B0412.realC (Axi.Nv R b x.1 x.2)) := IIb.NicePT.contDiff_realC.comp hNvs
  by_cases hz : y ∈ Axi.axis ∨ T < Axi.age R y
  · have hev : ∀ᶠ q in 𝓝 (τ, y), UnforcedLeray.B0412.realC (Axi.Nv R b q.1 q.2) = 0 := by
      have h1 := nv_eventually_zero hR (fun m hm => hvan m hm) hz
      have h2 := (continuous_snd.tendsto (τ, y)).eventually h1
      filter_upwards [h2] with q hq
      rw [hq q.1]
      simp [UnforcedLeray.B0412.realC]
    rw [dydy_eq_zero hev j k]
    simp only [norm_zero]
    split_ifs
    · have : 0 ≤ Axi.age R y := by rw [age_eq_sq]; positivity
      positivity
    · exact le_rfl
  · push Not at hz
    obtain ⟨hy, hage⟩ := hz
    rw [if_pos hage]
    have hage0 : 0 ≤ Axi.age R y := by rw [age_eq_sq]; positivity
    have hsl : ContDiff ℝ ∞ (Axi.Nv R b τ) := by
      have hg : ContDiff ℝ ∞ (fun z : Space => ((τ, z) : ℝ × Space)) :=
        contDiff_const.prodMk contDiff_id
      have h2 : Axi.Nv R b τ = (fun p : ℝ × Space => Axi.Nv R b p.1 p.2) ∘
          (fun z : Space => ((τ, z) : ℝ × Space)) := by funext z; rfl
      rw [h2]
      exact hNvs.comp hg
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = Real.exp (-(κ * |Axi.trans R y| / c)) := ⟨_, rfl⟩
    have he0 : 0 < e := by rw [he]; exact Real.exp_pos _
    have hη : (Axi.chart R τ y).2.2 = Axi.trans R y := rfl
    have hCm : ∀ i ≤ 2, ‖iteratedFDeriv ℝ i b (Axi.chart R τ y)‖ ≤ C * e := by
      intro i hi
      have := hjets i hi (Axi.chart R τ y)
      rw [hη, ← he] at this
      exact this
    rw [← he]
    obtain ⟨-, h2⟩ := hjet τ b hbs y hy (C * e) hCm
    have hL : ‖dy j (dy k (fun x : ℝ × Space => UnforcedLeray.B0412.realC (Axi.Nv R b x.1 x.2)))
        (τ, y)‖ ≤ ‖iteratedFDeriv ℝ 2 (Axi.Nv R b τ) y‖ :=
      (dy_dy_le hΦ j k τ y).trans (iter_realC_le hsl 2 y)
    refine hL.trans (h2.trans ?_)
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := by rw [ht]; exact inv_nonneg.2 (Axi.ϱ_nonneg y)
    have hs : Axi.age R y = R ^ 2 * t ^ 2 := by rw [age_eq_sq, ht]
    have h32 : Axi.age R y ^ (3 / 2 : ℝ) = R ^ 3 * t ^ 3 := by
      rw [age_rpow_three_halves hR, ht]
    rw [← ht, h32]
    obtain ⟨V, hV⟩ : ∃ V : ℝ, V = 1 + T + |Axi.trans R y| := ⟨_, rfl⟩
    have hV1 : 1 ≤ V := by
      rw [hV]; linarith [abs_nonneg (Axi.trans R y), hage0.trans hage]
    have hW0 : 0 ≤ 1 + Axi.age R y + |Axi.trans R y| := by
      linarith [abs_nonneg (Axi.trans R y)]
    have hW : (1 + Axi.age R y + |Axi.trans R y|) ^ 2 ≤ V ^ 2 := by
      have : 1 + Axi.age R y + |Axi.trans R y| ≤ V := by rw [hV]; linarith
      exact pow_le_pow_left₀ hW0 this 2
    rw [← hV]
    have hX : 0 ≤ K * (C * e) * t ^ 3 := by positivity
    calc K * (C * e) * t ^ 3 * (1 + Axi.age R y + |Axi.trans R y|) ^ 2
        ≤ K * (C * e) * t ^ 3 * V ^ 2 := mul_le_mul_of_nonneg_left hW hX
      _ = K / R ^ 3 * C * (R ^ 3 * t ^ 3) * V ^ 2 * e := by
          field_simp

end UnforcedLeray.Short.PartIIIb.Concrete
