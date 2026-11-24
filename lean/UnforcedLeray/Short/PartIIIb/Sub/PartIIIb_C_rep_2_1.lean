import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs

/-!
# `PartIII-b:C/rep/2/1` : `SepDomPhaseSup` from Minkowski, scaled Young, periodic dilation sum

Source `the November 2 reference manuscript` 3624-3647 (`sep:young`: Young in `y`,
dilation, Minkowski in `λ`, phase translation) and 3838-3845, 5219-5221 (normalised phase estimate
over `P ≤ 1`).  Three analytic Props; the assembly (`sepDomPhaseSup_of`) is proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(M) Minkowski in `λ`** (SP 3636-3640): for `q ≥ 1`, jointly measurable `g`, at every phase,
`‖∫_0^1 λ^a F_λ dλ‖_{L^q_y} ≤ ∫_0^1 λ^a ‖F_λ‖_{L^q_y} dλ`, with
`F_λ(y) = ∫ 1_{|y-λz|≥D}|y-λz|^{-4-j} g(τ+2logλ,z) dz`, i.e. `IIIa.sepDom` unfolded. -/
def SepDomMinkowski : Prop :=
  ∀ (a : ℝ) (j : ℕ) (D q : ℝ), 1 ≤ q → ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
    ∀ τ : ℝ, lqNorm q (IIIa.sepDom a j D g τ) ≤
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
        lqNorm q (fun y => ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z)

/-- **(Y) Young with dilation** (SP 3624-3645): `‖1_{|x|≥D}|x|^{-4-j}‖_{L^b} = C D^{-4-j+3/b}`
(`(4+j)b > 3`), substitute `z' = λz` (Jacobian `λ^{-3}`), Young in `y`, and
`‖g'(·/λ)‖_p = λ^{3/p}‖g'‖_p`: for `0<λ<1` and measurable `g'`,
`‖∫ sepKd(·-λz) g'(z) dz‖_{L^q} ≤ C D^{-4-j+3/b} λ^{-3+3/p} ‖g'‖_{L^p}`. -/
def SepKdYoungScaled : Prop :=
  ∀ (j : ℕ) (p q b : ℝ), 1 ≤ p → 1 ≤ b → 1 ≤ q → 1 + 1 / q = 1 / p + 1 / b →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℝ, 0 < D → ∀ l : ℝ, 0 < l → l < 1 → ∀ g' : Space → ℝ≥0∞,
      Measurable g' →
        lqNorm q (fun y => ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g' z) ≤
          ENNReal.ofReal (C * D ^ (-4 - (j : ℝ) + 3 / b)) *
            (ENNReal.ofReal (l ^ (-3 + 3 / p)) * lqNorm p g')

/-- **(S) Periodic dilation sum** (SP 3838-3845, 5219-5221): for a `P`-periodic measurable
`G ≥ 0`, `0 < P ≤ 1`, `c ≥ δ - 1`: with `λ = e^{-h/2}`,
`∫_0^1 λ^c G(τ+2logλ)dλ = ½∫_0^∞ e^{-κh}G(τ-h)dh`, `κ = (c+1)/2 ≥ δ/2`; cut `h` into periods,
periodicity and Cauchy-Schwarz on each period give
`≤ ½ (1-e^{-κP})⁻¹ P ‖G‖_{L²(0,P) normalised} ≤ ½(2/δ+1)‖G‖`, since `P/(1-e^{-κP}) ≤ 1/κ+P`. -/
def PeriodicDilationSum : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, δ - 1 ≤ c → ∀ P : ℝ, 0 < P → P ≤ 1 →
    ∀ G : ℝ → ℝ≥0∞, Measurable G → (∀ s, G (s + P) = G s) → ∀ τ : ℝ,
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l) ≤
        ENNReal.ofReal C * IIIa.ltauAt P G

theorem ltauAt_lqNorm_eq (P p : ℝ) (g : ℝ → Space → ℝ≥0∞) :
    IIIa.ltauAt P (fun s => lqNorm p (g s)) = IIIa.ltauLq P p g := by
  have key : ∀ s, (lqNorm p (g s)) ^ (2 : ℝ) = (∫⁻ y, g s y ^ p) ^ (2 / p) := by
    intro s
    unfold lqNorm
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  unfold IIIa.ltauAt IIIa.ltauLq
  simp_rw [key]

theorem sepDomPhaseSup_of (hM : SepDomMinkowski) (hY : SepKdYoungScaled)
    (hS : PeriodicDilationSum) : SepDomPhaseSup := by
  intro j p q b δ hp hb hq hrel hδ
  obtain ⟨C1, hC1, hY'⟩ := hY j p q b hp hb hq hrel
  obtain ⟨C2, hC2, hS'⟩ := hS δ hδ
  refine ⟨C1 * C2, mul_nonneg hC1 hC2, ?_⟩
  intro a ha hδa D P hD hP hP1 g hgm hper τ
  set G : ℝ → ℝ≥0∞ := fun s => lqNorm p (g s) with hG
  have hp0 : 0 < p := by linarith
  have hGm : Measurable G := by
    simp only [hG]
    unfold lqNorm
    have : Measurable fun s => ∫⁻ y, g s y ^ p := by
      have h1 : Measurable (fun x : ℝ × Space => g x.1 x.2 ^ p) := hgm.pow_const p
      exact h1.lintegral_prod_right'
    exact this.pow_const _
  have hGper : ∀ s, G (s + P) = G s := by
    intro s; have h := funext (hper s); simp only [hG, h]
  have hgτ : ∀ l : ℝ, Measurable (g (τ + 2 * Real.log l)) := fun l =>
    hgm.comp (measurable_const.prodMk measurable_id)
  calc lqNorm q (IIIa.sepDom a j D g τ)
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
          lqNorm q (fun y => ∫⁻ z : Space, IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z) :=
        hM a j D q hq g hgm τ
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (C1 * D ^ (-4 - (j : ℝ) + 3 / b)) *
          (ENNReal.ofReal (l ^ (a - 3 + 3 / p)) * G (τ + 2 * Real.log l)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        have h1 := hY' D hD l hl.1 hl.2 _ (hgτ l)
        calc ENNReal.ofReal (l ^ a) * lqNorm q (fun y => ∫⁻ z : Space,
              IIIa.sepKd j D (y - l • z) * g (τ + 2 * Real.log l) z)
            ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal (C1 * D ^ (-4 - (j : ℝ) + 3 / b)) *
              (ENNReal.ofReal (l ^ (-3 + 3 / p)) * G (τ + 2 * Real.log l))) :=
              mul_le_mul' le_rfl h1
          _ = ENNReal.ofReal (C1 * D ^ (-4 - (j : ℝ) + 3 / b)) *
              (ENNReal.ofReal (l ^ (a - 3 + 3 / p)) * G (τ + 2 * Real.log l)) := by
              have : l ^ (a - 3 + 3 / p) = l ^ a * l ^ (-3 + 3 / p) := by
                rw [← Real.rpow_add hl.1]; ring_nf
              rw [this, ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
              ring
    _ = ENNReal.ofReal (C1 * D ^ (-4 - (j : ℝ) + 3 / b)) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 + 3 / p)) * G (τ + 2 * Real.log l) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C1 * D ^ (-4 - (j : ℝ) + 3 / b)) *
          (ENNReal.ofReal C2 * IIIa.ltauAt P G) := by
        refine mul_le_mul' le_rfl ?_
        exact hS' _ (by linarith) P hP hP1 G hGm hGper τ
    _ = ENNReal.ofReal (C1 * C2 * D ^ (-4 - (j : ℝ) + 3 / b)) * IIIa.ltauLq P p g := by
        rw [← ltauAt_lqNorm_eq P p g, ← mul_assoc, ← ENNReal.ofReal_mul
          (mul_nonneg hC1 (Real.rpow_nonneg hD.le _))]
        congr 2
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
end
