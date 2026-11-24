import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2

/-!
# `PartIII-a:T21/2/7/2/2/1/2/3`: decomposition of `AdjCutE0Lower`

Source: `the November 2 reference manuscript`
(SP) lines 3060-3067 (energy identity for the cutoff energy), 3044-3049 (`|∇ jb^{-m}| ≤ 2|m| jb^{-m}`),
3052-3058 (`χ` bounded in `X_{-m}`).

Route.  Fix `ρ ∈ (t, s)`, `Φ = φ ρ`, `χ = ladChi`, `w = χ_R² jb^{-m}`.  Since `ladChi = ∂_ρφ + νΔΦ + v·∇Φ`,
`D_R = 2(I₁ - ν I₂ - I₃)` with `I₁ = ∫ w Re(Φ̄ χ)`, `I₂ = ∫ w Re(Φ̄ ΔΦ)`, `I₃ = ∫ w Re(Φ̄ v·∇Φ)`.
(i) integrability of the three integrands; (ii) `|I₁| ≤ K` (Cauchy-Schwarz, `‖χ‖_{X_{-m}} ≤ M_χ`,
`E_0 ≤ M`); (iii) one integration by parts (seam terms cancel by periodicity):
`I₂ = -∑_k G_k - J`, `J = ∫ Φ̄ ∇w·∇Φ`; (iv) `|J| ≤ ¼ ∑ G_k + K` (`|∇w| ≤ K₂ χ_R jb^{-m}`,
Cauchy-Schwarz, Young); (v) `|I₃| ≤ (ν/4) ∑ G_k + K` (`|v| ≤ C`, Cauchy-Schwarz, Young).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The hypotheses of `AdjCutE0Lower`. -/
def LowCtx (m : ℝ) (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ)
    (G : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ) (M : ℝ) : Prop :=
  AdjIntCtx m ν tr t s G φ ∧ 8 < m ∧
    ∀ ρ ∈ Icc t s,
      ∫⁻ x, ‖φ ρ x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤ ENNReal.ofReal M

/-- Integrand of `I₁`: `χ_R² jb^{-m} Re(Φ̄ χ)`. -/
def lowF1 {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m R : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) (x : ℝ × ℝ) : ℝ :=
  ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (φ ρ x) * ladChi tr φ ρ x).re)

/-- Integrand of `I₂`: `χ_R² jb^{-m} Re(Φ̄ ΔΦ)`. -/
def lowF2 (m R : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) (x : ℝ × ℝ) : ℝ :=
  ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (φ ρ x) * ladLapCx (φ ρ) x).re)

/-- Integrand of `I₃`: `χ_R² jb^{-m} Re(Φ̄ v·∇Φ)`. -/
def lowF3 {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m R : ℝ)
    (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) (x : ℝ × ℝ) : ℝ :=
  ladCut R x ^ 2 *
    (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (φ ρ x) * ladTransport tr ρ (φ ρ) x).re)

/-- The weight `w = χ_R² jb^{-m}` as a function on `ℝ²`. -/
def lowW (m R : ℝ) (x : ℝ × ℝ) : ℝ := ladCut R x ^ 2 * B0579.jb x ^ (-m)

/-- Integrand of `J`: `Re(Φ̄ ∇w·∇Φ)`. -/
def lowFJ (m R : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (ρ : ℝ) (x : ℝ × ℝ) : ℝ :=
  ((starRingEnd ℂ) (φ ρ x) *
    (((B0579.pd 0 (lowW m R) x : ℝ) : ℂ) * pdCx 0 (φ ρ) x +
      ((B0579.pd 1 (lowW m R) x : ℝ) : ℂ) * pdCx 1 (φ ρ) x)).re

/-- **(i) Integrability** of the three integrands over the cell, `ρ ∈ (t, s)` (continuous, with
support in the compact band `|η| ≤ √2 R`). -/
def CutLowerInt (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (M : ℝ), LowCtx m ν tr t s G φ M → ∀ R : ℝ, 0 < R →
    ∀ ρ ∈ Ioo t s,
      IntegrableOn (lowF1 tr m R φ ρ) (B0579.cell (ν ^ (-2 : ℝ))) ∧
      IntegrableOn (lowF2 m R φ ρ) (B0579.cell (ν ^ (-2 : ℝ))) ∧
      IntegrableOn (lowF3 tr m R φ ρ) (B0579.cell (ν ^ (-2 : ℝ)))

/-- **(ii) The `χ`-term** (SP 3052-3058, `adjWeakChiBound` for `8 < m`, `c = ν^{-2} ≥ 1`; Cauchy-Schwarz
`|∫ w Re(Φ̄ χ)| ≤ (∫ jb^{-m}|Φ|²)^{1/2} (∫ jb^{-m}|χ|²)^{1/2} ≤ √M M_χ`, `0 ≤ w ≤ jb^{-m}`):
`|I₁| ≤ K`, `K` independent of `R ≥ 1`, `ρ`. -/
def CutLowerChi (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (M : ℝ), LowCtx m ν tr t s G φ M →
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t s,
      |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R φ ρ x| ≤ K

/-- **(iii) One integration by parts in `x`** (SP 3060-3067; seam terms cancel by periodicity of
`Φ` and evenness of `jb`, `ladCut`; no boundary terms in `η` by the compact support of `χ_R`):
`I₂ = -∑_k G_k^R - J`. -/
def CutLowerIBP (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (M : ℝ), LowCtx m ν tr t s G φ M → ∀ R : ℝ, 0 < R →
    ∀ ρ ∈ Ioo t s,
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF2 m R φ ρ x =
        -(∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ) -
          ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowFJ m R φ ρ x

/-- **(iv) The weight-gradient term** (`|∇w| ≤ K₂ χ_R jb^{-m}` by `adjWeightGrad`, `ladCutProps`,
`R ≥ 1`; Cauchy-Schwarz against `∫ jb^{-m}|Φ|² ≤ M` and `∑ G_k`; Young):
`|J| ≤ ¼ ∑_k G_k^R + K`. -/
def CutLowerGradYoung (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (M : ℝ), LowCtx m ν tr t s G φ M →
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t s,
      |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowFJ m R φ ρ x| ≤
        (1 / 4) * (∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ) + K

/-- **(v) The transport term** (`|v| ≤ C` on `[0, s]` by `LadTrainBdd`; Cauchy-Schwarz and Young
with `E_0 ≤ M`): `|I₃| ≤ (ν/4) ∑_k G_k^R + K`. -/
def CutLowerTransport (m : ℝ) : Prop :=
  ∀ (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t s : ℝ) (G : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ) (M : ℝ), LowCtx m ν tr t s G φ M →
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ ρ ∈ Ioo t s,
      |∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF3 tr m R φ ρ x| ≤
        (ν / 4) * (∑ k : Fin 2, cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ) + K

/-- `AdjCutE0Lower` from the leaves (i)-(v). -/
theorem adjCutE0Lower_of (m : ℝ) (h1 : CutLowerInt m) (h2 : CutLowerChi m) (h3 : CutLowerIBP m)
    (h4 : CutLowerGradYoung m) (h5 : CutLowerTransport m) : AdjCutE0Lower m := by
  intro ν tr t s G φ hctx M hm hM
  have hL : LowCtx m ν tr t s G φ M := ⟨hctx, hm, hM⟩
  have hν : 0 < ν := hctx.1
  obtain ⟨K1, hK1⟩ := h2 ν tr t s G φ M hL
  obtain ⟨K4, hK4⟩ := h4 ν tr t s G φ M hL
  obtain ⟨K5, hK5⟩ := h5 ν tr t s G φ M hL
  refine ⟨2 * K1 + 2 * ν * K4 + 2 * K5, fun R hR ρ hρ => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  obtain ⟨i1, i2, i3⟩ := h1 ν tr t s G φ M hL R hR0 ρ hρ
  have hI := h3 ν tr t s G φ M hL R hR0 ρ hρ
  have hpt : ∀ x : ℝ × ℝ,
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ((starRingEnd ℂ) (φ ρ x) * ladDt φ ρ x).re) =
        lowF1 tr m R φ ρ x - ν * lowF2 m R φ ρ x - lowF3 tr m R φ ρ x := by
    intro x
    have hd : ladDt φ ρ x = ladChi tr φ ρ x - (ν : ℂ) * ladLapCx (φ ρ) x -
        ladTransport tr ρ (φ ρ) x := by
      unfold ladChi; ring
    simp only [lowF1, lowF2, lowF3, hd, mul_sub, Complex.sub_re]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hrate : cutE0Rate (ν ^ (-2 : ℝ)) m R φ ρ =
      2 * ((∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF1 tr m R φ ρ x) -
        ν * (∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF2 m R φ ρ x) -
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), lowF3 tr m R φ ρ x) := by
    unfold cutE0Rate
    simp_rw [hpt]
    have j2 : IntegrableOn (fun x => ν * lowF2 m R φ ρ x) (B0579.cell (ν ^ (-2 : ℝ))) :=
      i2.const_mul ν
    have j12 : IntegrableOn (fun x => lowF1 tr m R φ ρ x - ν * lowF2 m R φ ρ x)
        (B0579.cell (ν ^ (-2 : ℝ))) := i1.sub j2
    rw [integral_sub j12 i3, integral_sub i1 j2, integral_const_mul]
  have a1 := abs_le.1 (hK1 R hR ρ hρ)
  have a4 := abs_le.1 (hK4 R hR ρ hρ)
  have a5 := abs_le.1 (hK5 R hR ρ hρ)
  rw [hrate, hI]
  nlinarith [mul_le_mul_of_nonneg_left a4.1 hν.le, a1.1, a5.2, a4.2, mul_le_mul_of_nonneg_left a4.2 hν.le]

end UnforcedLeray.Short.IIIa
