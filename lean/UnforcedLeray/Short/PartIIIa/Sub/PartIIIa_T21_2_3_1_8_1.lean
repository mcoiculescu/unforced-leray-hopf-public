import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

/-!
# Part III-a, task `PartIII-a:T21/2/3/1/8/1` (`adjWeakChiBound`): decomposition

Source of record: `the November 2 reference manuscript` lines 3052-3058 ("The adjoint
localized interaction maps `X_{-m,d}` to `H^1_{-m,d}` uniformly: its localized source has uniformly
bounded `L^1` and `L^2` norms by weighted Cauchy-Schwarz").

Three leaves: the weighted field bound (`AdjWFieldBound`), the uniform `X_{-m}` bound of the weak
solution (`AdjWXNormBdd`), the identification of `ladChi` with the kernel adjoint (`AdjWChiIdentify`).
Proved here: `adjWeakChiBound_of` (assembly with `KernelAdjointBound`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- **Leaf `.../1`** (SP 3052-3058, weighted Cauchy-Schwarz): for a jointly smooth weak solution the
sources `F_j = φ(ρ) ∂_jE(ρ)` are in `L¹ ∩ L²` of the cell with
`‖F_j‖_{L¹} + ‖F_j‖_{L²} ≤ C' ‖φ(ρ)‖_{X_{-m}}`, `C'` uniform in `ρ ∈ (t, s)`. Proof: `LadTrainBdd tr m s C`
gives `|∂_jE| ≤ C jb^{-(m+2)/2}` on the cell; `jb^{-1} ∈ L²` (`m > 1`) and Hölder. -/
def AdjWFieldBound (m : ℝ) : Prop :=
  8 < m → ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), 1 ≤ c → AdjWCtx m ν c tr t s g φ →
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ ρ ∈ Ioo t s, ∀ j : Fin 2,
      IntegrableOn (fun x => φ ρ x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ))
        (B0579.cell c) ∧
      MemLp (fun x => φ ρ x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) 2
        (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => φ ρ x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) 1
          (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => φ ρ x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) 2
          (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal C' * xNorm c (-m) (φ ρ)

/-- **Leaf `.../2`** (SP 3052-3058; `IsAdjointWeak.memX`, `strongCont`, `tendsto_toReal_eLpNorm`):
`ρ ↦ ‖φ(ρ)‖_{X_{-m}}` is continuous on the compact `[t, s]`, hence bounded on `(t, s)`. -/
def AdjWXNormBdd (m : ℝ) : Prop :=
  8 < m → ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), 1 ≤ c → AdjWCtx m ν c tr t s g φ →
    ∃ M : ℝ, ∀ r ∈ Ioo t s, xNorm c (-m) (φ r) ≤ ENNReal.ofReal M

/-- **Leaf `.../3`** (SP 3052-3060; `adjWeakPointwise`, `kernelBSExists`, `weakFieldBandInt`,
`cellUnique`): if `χ'` (finite `H^1_{-m}` norm with weak gradient) has the pairings
`∫ χ' ψ = ∫ Σ_j F_j (K_cψ)_j` of the kernel adjoint, then `ladChi tr φ ρ = χ'` a.e. on the cell.
`ladChi - χ'` has the same pairings with every test (`AdjWeakPointwise`, every test has a kernel
velocity), is band integrable (`ladChi` continuous, `χ'` by `weakFieldBandInt`), so vanishes. -/
def AdjWChiIdentify (m : ℝ) : Prop :=
  8 < m → ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), 1 ≤ c → AdjWCtx m ν c tr t s g φ →
    ∀ ρ ∈ Ioo t s, ∀ (χ' : ℝ × ℝ → ℂ) (gχ : Fin 2 → ℝ × ℝ → ℂ),
      (∀ j, HasWeakCellDerivC c j χ' (gχ j)) → h1Norm c m χ' gχ ≠ ⊤ →
      (∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest c ψ →
        IsKernelBiotSavart c ψ uψ →
        ∫ y in B0579.cell c, χ' y * (ψ y : ℂ) =
          ∫ y in B0579.cell c, ∑ j : Fin 2,
            (φ ρ y * ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) y : ℝ) : ℂ)) *
              ((uψ y j : ℝ) : ℂ)) →
      ladChi tr φ ρ =ᵐ[volume.restrict (B0579.cell c)] χ'

theorem xNorm_le_h1Norm (c m : ℝ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) :
    xNorm c (-m) φ ≤ h1Norm c m φ g := by
  unfold h1Norm
  calc xNorm c (-m) φ = (xNorm c (-m) φ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow le_self_add (by norm_num)

theorem adjWeakChiBound_of (m : ℝ) (hK : KernelAdjointBound m) (hA : AdjWFieldBound m)
    (hB : AdjWXNormBdd m) (hC : AdjWChiIdentify m) (hm : 8 < m) : AdjWeakChiBound m := by
  intro ν c tr t s g φ hc hctx
  obtain ⟨CK, hCK0, hCK⟩ := hK (by linarith)
  obtain ⟨C', hC'0, hF⟩ := hA hm ν c tr t s g φ hc hctx
  obtain ⟨M, hM⟩ := hB hm ν c tr t s g φ hc hctx
  have hc0 : 0 < c := hctx.2.1
  refine ⟨CK * (2 * C') * M, fun ρ hρ => ?_⟩
  obtain ⟨χ', gχ, hder, hbd, hdual⟩ := hCK c hc
    (fun j x => φ ρ x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ))
    (fun j => ⟨(hF ρ hρ j).1, (hF ρ hρ j).2.1⟩)
  have hsum : ∑ j : Fin 2, (eLpNorm (fun x => φ ρ x *
        ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell c)) +
      eLpNorm (fun x => φ ρ x * ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℝ) : ℂ)) 2
        (volume.restrict (B0579.cell c))) ≤
      ENNReal.ofReal (2 * C' * M) := by
    calc _ ≤ ∑ _j : Fin 2, ENNReal.ofReal C' * ENNReal.ofReal M :=
          Finset.sum_le_sum fun j _ => (hF ρ hρ j).2.2.trans
            (mul_le_mul' le_rfl (hM ρ hρ))
      _ = ENNReal.ofReal (2 * C') * ENNReal.ofReal M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_mul
            (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, nsmul_eq_mul]
          push_cast; ring
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have hbound : h1Norm c m χ' gχ ≤ ENNReal.ofReal (CK * (2 * C') * M) := by
    refine hbd.trans ?_
    calc _ ≤ ENNReal.ofReal CK * ENNReal.ofReal (2 * C' * M) := mul_le_mul' le_rfl hsum
      _ = _ := by rw [← ENNReal.ofReal_mul hCK0]; congr 1; ring
  have hfin : h1Norm c m χ' gχ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hid := hC hm ν c tr t s g φ hc hctx ρ hρ χ' gχ hder hfin
    (fun ψ uψ hψ hu => by
      have := hdual ψ uψ hψ hu
      simpa using this)
  have hid' : ladChi tr φ ρ =ᵐ[B0579.cellMeasure c (-m)] χ' :=
    (B0579.cellMeasure_ac c (-m)) hid
  have hx : xNorm c (-m) (ladChi tr φ ρ) ≤ ENNReal.ofReal (CK * (2 * C') * M) := by
    unfold xNorm
    rw [eLpNorm_congr_ae hid']
    exact (xNorm_le_h1Norm c m χ' gχ).trans hbound
  have hcont : Continuous (ladChi tr φ ρ) :=
    continuous_ladChi tr hctx.2.2.1 hctx.2.2.2.2.2.2 hρ
  refine ⟨⟨hcont.aestronglyMeasurable, lt_of_le_of_lt hx ENNReal.ofReal_lt_top⟩, hx⟩

end UnforcedLeray.Short.IIIa
