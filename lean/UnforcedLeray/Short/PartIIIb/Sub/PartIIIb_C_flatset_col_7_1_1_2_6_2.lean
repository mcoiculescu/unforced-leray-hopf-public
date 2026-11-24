import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_of

/-!
# `SFCDivCont`: continuity of the slice divergence pairing on `s > 0`

Leaf of `PartIII-b:C/flatset/col/7/1/1/2/6` (source `shorter-proof-2026-11-02.tex` 1650-1656).
For a smooth representative `b` (jointly continuous on `s > 0`) and a cylinder test `ψ`, the map
`s ↦ ∫_cell b(s,x)·∇ψ(x) dx` is continuous on `s > 0`: on a compact neighbourhood
`[s₀/2, 2 s₀]` the field is bounded on the box that carries the support of `∇ψ` on the cell, and
dominated convergence applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcDivCont : SFCDivCont := by
  intro c b hb ψ hψ
  obtain ⟨-, hcd, -, -, -⟩ := hb
  have hbc : ∀ i : Fin 2, ContinuousOn (fun p : Chart => b p i) (Ioi (0 : ℝ) ×ˢ univ) :=
    fun i => (hcd i).continuousOn
  -- a common radius beyond which both derivatives of ψ vanish
  obtain ⟨R0, hR0⟩ := (hψ.pd 0).band
  obtain ⟨R1, hR1⟩ := (hψ.pd 1).band
  obtain ⟨R, hR0R, hR1R⟩ : ∃ R : ℝ, R0 ≤ R ∧ R1 ≤ R :=
    ⟨max R0 R1, le_max_left _ _, le_max_right _ _⟩
  have hout : ∀ x ∈ B0579.cell c, x ∉ B0579.box c R → R < |x.2| := by
    intro x hx hxb
    by_contra hle
    exact hxb (B0579.mem_box_of_mem_cell hx (not_lt.mp hle))
  have hp0 : ∀ x ∈ B0579.cell c, x ∉ B0579.box c R → B0579.pd 0 ψ x = 0 :=
    fun x hx hxb => hR0 x (lt_of_le_of_lt hR0R (hout x hx hxb))
  have hp1 : ∀ x ∈ B0579.cell c, x ∉ B0579.box c R → B0579.pd 1 ψ x = 0 :=
    fun x hx hxb => hR1 x (lt_of_le_of_lt hR1R (hout x hx hxb))
  have hpc0 : Continuous fun x : ℝ × ℝ => ((B0579.pd 0 ψ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hψ.pd 0).continuous
  have hpc1 : Continuous fun x : ℝ × ℝ => ((B0579.pd 1 ψ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hψ.pd 1).continuous
  have hh : Continuous fun x : ℝ × ℝ => ‖B0579.pd 0 ψ x‖ + ‖B0579.pd 1 ψ x‖ :=
    ((hψ.pd 0).continuous.norm).add (hψ.pd 1).continuous.norm
  -- the dominating function is integrable on the cell
  have hint : IntegrableOn (fun x : ℝ × ℝ => ‖B0579.pd 0 ψ x‖ + ‖B0579.pd 1 ψ x‖)
      (B0579.cell c) :=
    (hh.continuousOn.integrableOn_compact (B0579.isCompact_box c R)).of_forall_sdiff_eq_zero
      (B0579.measurableSet_cell c)
      (fun x hx => by rw [hp0 x hx.1 hx.2, hp1 x hx.1 hx.2]; simp)
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  -- continuity in `s` of the field at each fixed `x`
  have hcs : ∀ (s0 : ℝ), 0 < s0 → ∀ (x : ℝ × ℝ) (i : Fin 2),
      ContinuousAt (fun s : ℝ => b (s, x) i) s0 := by
    intro s0 hs0 x i
    have hc : ContinuousAt (fun p : Chart => b p i) (s0, x) :=
      (hbc i).continuousAt (hopen.mem_nhds (Set.mk_mem_prod hs0 (mem_univ x)))
    exact hc.comp (f := fun s : ℝ => ((s, x) : Chart))
      (continuous_id.prodMk continuous_const).continuousAt
  -- continuity in `x` of the field at each fixed `s > 0`
  have hslice : ∀ s : ℝ, 0 < s → ∀ i : Fin 2, Continuous fun x : ℝ × ℝ => b (s, x) i := by
    intro s hs i
    have hf : Continuous fun x : ℝ × ℝ => ((s, x) : Chart) := continuous_const.prodMk continuous_id
    have h1 : ContinuousOn (fun x : ℝ × ℝ => b (s, x) i) univ :=
      (hbc i).comp hf.continuousOn (fun x _ => Set.mk_mem_prod hs (mem_univ x))
    exact continuousOn_univ.mp h1
  have hcont : ∀ s0 ∈ Ioi (0 : ℝ), ContinuousAt (fun s : ℝ => ∫ x in B0579.cell c,
      (b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ))) s0 := by
    intro s0 hs0
    have hs0' : (0 : ℝ) < s0 := hs0
    have hh2 : (0 : ℝ) < s0 / 2 := half_pos hs0'
    set K : Set Chart := Icc (s0 / 2) (2 * s0) ×ˢ B0579.box c R with hKdef
    have hKc : IsCompact K := isCompact_Icc.prod (B0579.isCompact_box c R)
    have hKsub : K ⊆ Ioi (0 : ℝ) ×ˢ univ := fun p hp =>
      Set.mk_mem_prod (lt_of_lt_of_le hh2 hp.1.1) (mem_univ _)
    obtain ⟨M, hMnn, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, ‖b p 0‖ ≤ M ∧ ‖b p 1‖ ≤ M := by
      obtain ⟨M0, hM0⟩ := hKc.exists_bound_of_continuousOn ((hbc 0).mono hKsub)
      obtain ⟨M1, hM1⟩ := hKc.exists_bound_of_continuousOn ((hbc 1).mono hKsub)
      refine ⟨|M0| + |M1|, by positivity, fun p hp => ⟨?_, ?_⟩⟩
      · exact le_trans (hM0 p hp) (by linarith [abs_nonneg M1, le_abs_self M0])
      · exact le_trans (hM1 p hp) (by linarith [abs_nonneg M0, le_abs_self M1])
    have hIcc : Icc (s0 / 2) (2 * s0) ∈ 𝓝 s0 := Icc_mem_nhds (by linarith) (by linarith)
    refine continuousAt_of_dominated
      (F := fun s x => b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ))
      (bound := fun x => M * (‖B0579.pd 0 ψ x‖ + ‖B0579.pd 1 ψ x‖)) ?_ ?_ ?_ ?_
    · filter_upwards [hIcc] with s hs
      have hs' : 0 < s := lt_of_lt_of_le hh2 hs.1
      exact (((hslice s hs' 0).mul hpc0).add ((hslice s hs' 1).mul hpc1)).aestronglyMeasurable
    · filter_upwards [hIcc] with s hs
      have hs' : 0 < s := lt_of_lt_of_le hh2 hs.1
      refine ae_restrict_of_forall_mem (B0579.measurableSet_cell c) (fun x hx => ?_)
      by_cases hxb : x ∈ B0579.box c R
      · have hsK : (s, x) ∈ K := Set.mk_mem_prod hs hxb
        obtain ⟨h0, h1⟩ := hMb (s, x) hsK
        calc ‖b (s, x) 0 * (B0579.pd 0 ψ x : ℂ) + b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)‖
            ≤ ‖b (s, x) 0 * (B0579.pd 0 ψ x : ℂ)‖ + ‖b (s, x) 1 * (B0579.pd 1 ψ x : ℂ)‖ :=
              norm_add_le _ _
          _ = ‖b (s, x) 0‖ * ‖B0579.pd 0 ψ x‖ + ‖b (s, x) 1‖ * ‖B0579.pd 1 ψ x‖ := by
              rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
          _ ≤ M * ‖B0579.pd 0 ψ x‖ + M * ‖B0579.pd 1 ψ x‖ := by gcongr
          _ = M * (‖B0579.pd 0 ψ x‖ + ‖B0579.pd 1 ψ x‖) := by ring
      · have hz0 := hp0 x hx hxb
        have hz1 := hp1 x hx hxb
        simp [hz0, hz1]
    · exact Integrable.const_mul hint M
    · exact Filter.Eventually.of_forall fun x =>
        ((hcs s0 hs0' x 0).mul continuousAt_const).add ((hcs s0 hs0' x 1).mul continuousAt_const)
  exact fun s0 hs0 => (hcont s0 hs0).continuousWithinAt

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
