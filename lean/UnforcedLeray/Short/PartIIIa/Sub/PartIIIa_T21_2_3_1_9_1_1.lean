import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1

/-!
# `PartIII-a:T21/2/3/1/9/1/1` (`LadTestDensity`), decomposition

Source: `the November 2 reference manuscript` (SP) lines 3230-3240
(`eq:ct-embeddings`) and 3052-3058: density of real cylinder tests in `X_{m,c}`, with the circulation
repaired afterwards.

`LadTestDensity m` follows from
* `LadDensApprox` : (no circulation condition) every `w ∈ L²(cellMeasure c m)` is within `ε` in
  `xNorm` of `a + i b`, `a, b` real cylinder tests (truncate by `ladCut R`, then mollify the
  `c`-periodic extension and cut off again);
* `LadDensCircFix` : for zero-circulation `w`, a test approximant is repaired to have zero cell
  integral by subtracting `(∫ (a+ib-w)) χ`, `χ` a fixed cylinder bump with `∫_cell χ = 1`; the cost
  is `≤ C_c xNorm (a+ib-w)` because `|∫_cell f| ≤ (∫_cell ⟨x⟩^{-2m})^{1/2} ‖f‖_{X_m}` (`m > 1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- **Leaf A** (SP 3230-3240): `L²(cellMeasure c m)` functions are `xNorm`-approximable by
`a + i b` with `a, b` real cylinder tests (no circulation condition). -/
def LadDensApprox (m : ℝ) : Prop :=
  ∀ (c : ℝ) (w : ℝ × ℝ → ℂ), 1 ≤ c → MemLp w 2 (B0579.cellMeasure c m) →
    ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ × ℝ → ℝ, B0579.IsCylTest c a ∧ B0579.IsCylTest c b ∧
      xNorm c m (fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ) - w x) <
        ENNReal.ofReal ε

/-- **Leaf B** (SP 3052-3058, circulation repair): for `c ≥ 1` there is `C` such that every real
cylinder-test approximant `a + i b` of a zero-circulation `w ∈ X_{m,c}` is replaced by an
approximant `a' + i b'` with zero cell integrals, at cost `C` times the error. -/
def LadDensCircFix (m : ℝ) : Prop :=
  ∀ c : ℝ, 1 ≤ c → ∃ C : ℝ, ∀ (w : ℝ × ℝ → ℂ), MemLp w 2 (B0579.cellMeasure c m) →
    HasZeroCirculation c w → ∀ a b : ℝ × ℝ → ℝ, B0579.IsCylTest c a → B0579.IsCylTest c b →
    ∃ a' b' : ℝ × ℝ → ℝ, B0579.IsCylTest c a' ∧ B0579.IsCylTest c b' ∧
      IntegrableOn a' (B0579.cell c) ∧ IntegrableOn b' (B0579.cell c) ∧
      ∫ x in B0579.cell c, a' x = 0 ∧ ∫ x in B0579.cell c, b' x = 0 ∧
      xNorm c m (fun x => ((a' x : ℝ) : ℂ) + Complex.I * ((b' x : ℝ) : ℂ) - w x) ≤
        ENNReal.ofReal C * xNorm c m
          (fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ) - w x)

/-- Assembly of `LadTestDensity` from the two leaves. -/
theorem ladTestDensity_of (m : ℝ) (hA : LadDensApprox m) (hB : LadDensCircFix m) :
    LadTestDensity m := by
  intro c w hc hw hz
  obtain ⟨C, hC⟩ := hB c hc
  have hex : ∀ n : ℕ, ∃ a b : ℝ × ℝ → ℝ, B0579.IsCylTest c a ∧ B0579.IsCylTest c b ∧
      xNorm c m (fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ) - w x) <
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    hA c w hc hw _ (by positivity)
  choose a b ha hb hlt using hex
  have hlim0 : Tendsto (fun n : ℕ => xNorm c m
      (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun _ => bot_le) (fun n => (hlt n).le)
  have hfix : ∀ n, ∃ a' b' : ℝ × ℝ → ℝ, B0579.IsCylTest c a' ∧ B0579.IsCylTest c b' ∧
      IntegrableOn a' (B0579.cell c) ∧ IntegrableOn b' (B0579.cell c) ∧
      ∫ x in B0579.cell c, a' x = 0 ∧ ∫ x in B0579.cell c, b' x = 0 ∧
      xNorm c m (fun x => ((a' x : ℝ) : ℂ) + Complex.I * ((b' x : ℝ) : ℂ) - w x) ≤
        ENNReal.ofReal C * xNorm c m
          (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x) :=
    fun n => hC w hw hz (a n) (b n) (ha n) (hb n)
  choose a' b' ha' hb' hia hib hza hzb hle using hfix
  refine ⟨a', b', fun n => ⟨ha' n, hb' n, hia n, hib n, hza n, hzb n⟩, ?_⟩
  have hlim : Tendsto (fun n => ENNReal.ofReal C * xNorm c m
      (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hlim0
      (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hle

end UnforcedLeray.Short.IIIa
