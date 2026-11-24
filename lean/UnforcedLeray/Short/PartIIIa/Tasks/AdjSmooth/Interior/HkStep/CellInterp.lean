import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellInterpSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollTendsto
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollWeakDeriv

/-!
# `PartIII-a:T21/2/7/2/1/1/5/16`: the interpolation inequality for periodic weak derivatives

Source of record: `the November 2 reference manuscript` (SP), lines 3044-3050
(the diffusion-weight error `|∂_j ⟨x⟩^{-2m}| <= 2|m| ⟨x⟩^{-2m}`), 3060-3061 (the limit of the
mollifications), with `CellInterpSmooth` for the smooth periodic fields `ρ_n ⋆ f`.

Proof. Let `F_n = cellMoll n f`. By `CellMollWeakDeriv`, `∂_j F_n = cellMoll n g` and
`∂_j (∂_j F_n) = cellMoll n h`, so `CellInterpSmooth` gives
`‖cellMoll n g‖² <= ‖cellMoll n f‖ (2|m| ‖cellMoll n g‖ + ‖cellMoll n h‖)`.
Each `‖cellMoll n u‖_{X_{-m,c}}` converges to `‖u‖_{X_{-m,c}}` (`CellMollTendsto` and the
triangle inequality, squeezed between `‖u‖ - d_n` and `‖u‖ + d_n`), and the limit passes through
the inequality since all norms are finite.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The mollified `X_{-m,c}` norms converge to the norm: `‖ρ_n ⋆ u‖ -> ‖u‖`. -/
theorem ci_xNorm_tendsto {c m : ℝ} (hc : 0 < c) {u : ℝ × ℝ → ℂ}
    (hper : ∀ x : ℝ × ℝ, u (x.1 + c, x.2) = u x) (hmem : MemLp u 2 (B0579.cellMeasure c (-m))) :
    Tendsto (fun n : ℕ => xNorm c (-m) (cellMoll n u)) atTop (𝓝 (xNorm c (-m) u)) := by
  have hd := cellMollTendsto c m u hc hper hmem
  have hfin : xNorm c (-m) u ≠ ⊤ := hmem.eLpNorm_lt_top.ne
  have hA : ∀ n : ℕ, AEStronglyMeasurable (cellMoll n u) (B0579.cellMeasure c (-m)) := fun n =>
    ((cellMollSmooth c m n u hc hper hmem).1.continuous).aestronglyMeasurable
  have hU : AEStronglyMeasurable u (B0579.cellMeasure c (-m)) := hmem.aestronglyMeasurable
  have hup : ∀ n : ℕ, xNorm c (-m) (cellMoll n u) ≤
      xNorm c (-m) u + xNorm c (-m) (cellMoll n u - u) := by
    intro n
    have h := eLpNorm_add_le ((hA n).sub hU) hU one_le_two
    rw [sub_add_cancel] at h
    exact h.trans_eq (add_comm _ _)
  have hlo : ∀ n : ℕ, xNorm c (-m) u ≤
      xNorm c (-m) (cellMoll n u) + xNorm c (-m) (cellMoll n u - u) := by
    intro n
    have h := eLpNorm_sub_le (hA n) ((hA n).sub hU) one_le_two
    rw [sub_sub_cancel] at h
    exact h
  have hc0 : Tendsto (fun _ : ℕ => xNorm c (-m) u) atTop (𝓝 (xNorm c (-m) u)) :=
    tendsto_const_nhds
  have hlow : Tendsto (fun n : ℕ => xNorm c (-m) u - xNorm c (-m) (cellMoll n u - u)) atTop
      (𝓝 (xNorm c (-m) u)) := by
    have h := ENNReal.Tendsto.sub hc0 hd (Or.inl hfin)
    rw [tsub_zero] at h
    exact h
  have hhigh : Tendsto (fun n : ℕ => xNorm c (-m) u + xNorm c (-m) (cellMoll n u - u)) atTop
      (𝓝 (xNorm c (-m) u)) := by
    have h := hc0.add hd
    rw [add_zero] at h
    exact h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh
    (fun n => tsub_le_iff_right.2 (hlo n)) hup

/-- **The interpolation inequality for periodic weak derivatives** (SP 3044-3050): if `g = ∂_j f`
and `h = ∂_j g` weakly on the cylinder, all periodic and in `X_{-m,c}`, then
`‖g‖² <= ‖f‖ (2|m| ‖g‖ + ‖h‖)` in `X_{-m,c}`. -/
theorem cellInterp : UnforcedLeray.Short.IIIa.CellInterp := by
  unfold UnforcedLeray.Short.IIIa.CellInterp
  intro c m j f g h hc hf hg hh hmf hmg hmh hfg hgh
  have hS := fun n : ℕ => cellMollSmooth c m n f hc hf hmf
  have hn1 : ∀ n : ℕ, pdCx j (cellMoll n f) = cellMoll n g :=
    fun n => cellMollWeakDeriv c m j f g hc hf hg hmf hmg hfg n
  have hn2 : ∀ n : ℕ, pdCx j (pdCx j (cellMoll n f)) = cellMoll n h := fun n => by
    rw [hn1 n]
    exact cellMollWeakDeriv c m j g h hc hg hh hmg hmh hgh n
  have hineq : ∀ n : ℕ, xNorm c (-m) (cellMoll n g) ^ 2 ≤
      xNorm c (-m) (cellMoll n f) * (ENNReal.ofReal (2 * |m|) * xNorm c (-m) (cellMoll n g) +
        xNorm c (-m) (cellMoll n h)) := by
    intro n
    have h1 := cellInterpSmooth c m j (cellMoll n f) hc (hS n).1 (hS n).2.1 (hS n).2.2
    rw [hn2 n, hn1 n] at h1
    exact h1
  have hf_lim := ci_xNorm_tendsto hc hf hmf
  have hg_lim := ci_xNorm_tendsto hc hg hmg
  have hh_lim := ci_xNorm_tendsto hc hh hmh
  have hF : xNorm c (-m) f ≠ ⊤ := hmf.eLpNorm_lt_top.ne
  have hG : xNorm c (-m) g ≠ ⊤ := hmg.eLpNorm_lt_top.ne
  have hH : xNorm c (-m) h ≠ ⊤ := hmh.eLpNorm_lt_top.ne
  have hcst : ENNReal.ofReal (2 * |m|) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hL : Tendsto (fun n : ℕ => xNorm c (-m) (cellMoll n g) ^ 2) atTop
      (𝓝 (xNorm c (-m) g ^ 2)) := by
    simp only [sq]
    exact ENNReal.Tendsto.mul hg_lim (Or.inr hG) hg_lim (Or.inr hG)
  have hinner : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * |m|) * xNorm c (-m) (cellMoll n g) +
      xNorm c (-m) (cellMoll n h)) atTop
      (𝓝 (ENNReal.ofReal (2 * |m|) * xNorm c (-m) g + xNorm c (-m) h)) :=
    (ENNReal.Tendsto.const_mul hg_lim (Or.inr hcst)).add hh_lim
  have hinner_top : ENNReal.ofReal (2 * |m|) * xNorm c (-m) g + xNorm c (-m) h ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hcst hG, hH⟩
  have hR : Tendsto (fun n : ℕ => xNorm c (-m) (cellMoll n f) *
      (ENNReal.ofReal (2 * |m|) * xNorm c (-m) (cellMoll n g) + xNorm c (-m) (cellMoll n h)))
      atTop (𝓝 (xNorm c (-m) f *
        (ENNReal.ofReal (2 * |m|) * xNorm c (-m) g + xNorm c (-m) h))) :=
    ENNReal.Tendsto.mul hf_lim (Or.inr hinner_top) hinner (Or.inr hF)
  exact le_of_tendsto_of_tendsto' hL hR hineq

end UnforcedLeray.Short.IIIa
