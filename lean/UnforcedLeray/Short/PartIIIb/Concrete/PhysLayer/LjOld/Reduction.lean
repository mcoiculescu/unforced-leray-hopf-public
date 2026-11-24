import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.OldMeasureAC

/-!
# `𝓛` depends only on old data: reduction of `IsLjOld` to the `𝓛` pin (source 4762-4796, 5800)

Source of record: `the November 2 reference manuscript` (73 pages).

The map `𝓛` of `source-class:L` (source 4792-4796) sees an old thin tensor `M` only through its
normalized phase mean `E_ij(u) = χ_o(u)/c ∫_cell M_ij(u,q,η) dq dη` (source 4766-4770), i.e. only
through `χ_o M`.  For a stress `T` with `χ_oT = 0` (`chiOStr`, source 4163-4166) the thin
component of `T` therefore enters `𝓛` as the zero tensor:

* `oldCut ν χo M` : `M` with the points where `χ_o(νu) = 0` set to zero; it has the same phase mean
  as `M` (`phaseMean_oldCut`), hence the same `X^mt` and the same `𝓛M`
  (`Xmt_congr_phaseMean`, `Lpt_congr_Xmt`);
* `oldCut_thinRep_ae_zero` : `χ_oT = 0` gives `oldCut (thinRep T) = 0` a.e. for the gain measure of
  `Z_1`, hence a.e. on the old region (`oldMeasureAC`, source 2666-2700);
* `XmtCongr` (source 4766-4770; task `PartIII-b:C/srcL/5`) then gives `X^mt` of it equal to
  `X^mt` of the zero tensor, and `Lpt_zero` : the `𝓛` formula of the zero tensor is `0`;
* `isLjOld_of_xmtCongr` : with the `𝓛` pin `IsSourceLPinned` (`ι(𝓛T) = LjFun T`) and the
  injectivity of the inclusion `ι : 𝒜 → (ℝ → Mat3)`, `χ_oT = 0 → 𝓛T = 0` (source 5800-5803:
  `HT = M(Y + h - ĥ_{𝓛T})` depends only on `χ_oT`).

The conclusion is the body of `PhysLayer.IsLjOld B hχo` (`∀ T, chiOStr … T = 0 → B.Lj T = 0`),
written out: `Concrete/PhysLayer.lean` and `Concrete/SourceL.lean` both declare
`Concrete.streamCut` and cannot yet be imported together, so this file imports only `SourceL`.
A term of this type is accepted where `IsLjOld B hχo` is expected (definitional unfolding).
The unconditional `isLjOld_of` (`Concrete/PhysLayer/LjOld.lean`) is `isLjOld_of_xmtCongr` applied
to `xmtCongr`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. `𝓛` sees `M` only through `χ_o M` (source 4766-4796) -/

/-- `M` with the points `(u, q, η)` where the outward cutoff `χ_o(u) = χ̂_o(νu)` vanishes set to
zero. -/
def oldCut (ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) : Chart → Mat3 :=
  fun p => if χo (ν * p.1) = 0 then 0 else M p

/-- The phase mean `E(u) = χ_o(u)/c ∫_cell M(u,·)` (source 4766-4770) does not see the points where
`χ_o` vanishes. -/
theorem phaseMean_oldCut (c ν : ℝ) (χo : ℝ → ℝ) (M : Chart → Mat3) :
    phaseMean c ν χo (oldCut ν χo M) = phaseMean c ν χo M := by
  funext u i j
  unfold phaseMean
  split_ifs with h
  · rfl
  · by_cases h0 : χo (ν * u) = 0
    · rw [h0, zero_mul, zero_mul]
    · simp only [oldCut, h0, ite_false]

/-- `X^mt_{μ,M}` depends on `M` only through its phase mean `E` (source 4766-4791). -/
theorem Xmt_congr_phaseMean {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} {M M' : Chart → Mat3}
    (h : phaseMean c ν χo M = phaseMean c ν χo M') :
    Xmt c ν ε μ χo χy M = Xmt c ν ε μ χo χy M' := by
  have hσ : sigmaM c ν χo M = sigmaM c ν χo M' := by
    unfold sigmaM
    rw [h]
  have hV : ∀ μ' : ℝ, newtonV c ν μ' χo M = newtonV c ν μ' χo M' := fun μ' => by
    unfold newtonV
    rw [hσ]
  unfold Xmt youngW
  rw [hV μ, hV (μ + 1)]

/-- `𝓛M` depends on `M` only through `X^mt_{μ,M}` (source 4792-4796). -/
theorem Lpt_congr_Xmt {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} {M M' : Chart → Mat3}
    (h : Xmt c ν ε μ χo χy M = Xmt c ν ε μ χo χy M') :
    Lpt c ν ε μ χo χy M = Lpt c ν ε μ χo χy M' := by
  unfold Lpt
  rw [h]

/-! ## 2. The `𝓛` formula of the zero tensor (source 4764-4796) -/

theorem phaseMean_zero (c ν : ℝ) (χo : ℝ → ℝ) : phaseMean c ν χo 0 = 0 := by
  funext u i j
  simp [phaseMean]

theorem sigmaM_zero (c ν : ℝ) (χo : ℝ → ℝ) : sigmaM c ν χo 0 = 0 := by
  funext x' a b
  simp [sigmaM, phaseMean_zero]

theorem newtonV_zero (c ν μ : ℝ) (χo : ℝ → ℝ) : newtonV c ν μ χo 0 = 0 := by
  funext x i
  simp [newtonV, sigmaM_zero]

theorem youngW_zero (c ν ε μ : ℝ) (χo : ℝ → ℝ) : youngW c ν ε μ χo 0 = 0 := by
  funext y
  simp [youngW, newtonV_zero]

theorem streamCut_zero (ν ε : ℝ) (χy : ℝ → ℝ) : streamCut ν ε χy 0 = 0 := by
  funext y
  simp [streamCut, streamPsi]

/-- `X^mt` of the zero old tensor vanishes. -/
theorem Xmt_zero (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Xmt c ν ε μ χo χy 0 = 0 := by
  unfold Xmt
  rw [youngW_zero, youngW_zero, sub_zero, streamCut_zero]

/-- The `𝓛` formula of the zero old tensor vanishes. -/
theorem Lpt_zero (c ν ε μ : ℝ) (χo χy : ℝ → ℝ) : Lpt c ν ε μ χo χy 0 = 0 := by
  funext s
  unfold Lpt
  rw [Xmt_zero]
  split_ifs
  · funext i j
    simp
  · rfl

/-! ## 3. `χ_oT = 0` kills the thin component where `χ_o ≠ 0` -/

/-- The thin component of `χ_oT` is `χ̂_o(νs)` times the thin component of `T`. -/
theorem chiOStr_fst_ae {c mZ ρb γ ν : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (T : StrG c mZ ρb γ ν) :
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
      cutFun χo ν • ((T.fst : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)) : Chart → Ten3) :=
  NearInst.mulBdd_apply_ae (cutFun χo ν) (cutFun_measurable hχo ν) 1 (cutFun_bound hχo ν) T.fst

/-- If `χ_oT = 0`, the thin representative of `T` vanishes a.e. (gain measure of `Z_1`) wherever
`χ_o ≠ 0`. -/
theorem oldCut_thinRep_ae_zero {c mZ ρb γ ν : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (T : StrG c mZ ρb γ ν) (hT : chiOStr c mZ ρb γ ν hχo T = 0) :
    oldCut ν χo (thinRep T) =ᵐ[gainZ1Measure c mZ γ ν] 0 := by
  have h1 : ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] 0 := by
    rw [hT, WithLp.zero_fst]; exact Lp.coeFn_zero _ _ _
  filter_upwards [h1, chiOStr_fst_ae hχo T] with p hp1 hp2
  rw [hp1] at hp2
  unfold oldCut
  split_ifs with h
  · rfl
  · have h0 : (T.fst : Chart → Ten3) p = 0 := by
      have h3 : cutFun χo ν p • (T.fst : Chart → Ten3) p = 0 := by
        have h5 := hp2.symm
        simpa only [Pi.smul_apply', Pi.zero_apply] using h5
      exact (smul_eq_zero.1 h3).resolve_left h
    show Ten3.toMatrix ((WithLp.ofLp T).1 p) = 0
    have h4 : (WithLp.ofLp T).1 p = 0 := h0
    rw [h4]
    funext a b
    rfl

/-! ## 4. The reduction -/

/-- **`𝓛` depends only on old data** (source 4762-4796, 5800-5803): for a `ReturnBase` whose `Lj`
is the source map `𝓛` (`IsSourceLPinned`, read through the injective inclusion `ι` of `𝒜`),
`χ_oT = 0 → 𝓛T = 0` (the body of `PhysLayer.IsLjOld B hχo`), given `XmtCongr` (`X^mt` depends
only on the a.e. class of `M` on the old region, source 4766-4770). -/
theorem isLjOld_of_xmtCongr {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff]
    [NormedSpace ℝ Aff] [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)
    {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {S : ConcreteYF.FlatSetting} {lam κ ell : ℂ} {J : ℂ → ℂ}
    {ε μ : ℝ} {χo χy χf : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hι : Function.Injective ι)
    (hν : 0 < ν) (hL : IsSourceLPinned B ι S lam κ ell J ε μ χo χy χf) (hC : XmtCongr) :
    ∀ T : StrG c mZ ρb γ ν, chiOStr c mZ ρb γ ν hχo T = 0 → B.Lj T = 0 := by
  intro T hT
  apply hι
  rw [map_zero, hL.1 T]
  unfold LjFun
  have hae : oldCut ν χo (thinRep T) =ᵐ[oldMeasure c ν] 0 :=
    (oldMeasureAC c mZ γ ν hν).ae_le (oldCut_thinRep_ae_zero hχo T hT)
  have hX : Xmt c ν ε μ χo χy (thinRep T) = Xmt c ν ε μ χo χy 0 := by
    rw [← Xmt_congr_phaseMean (ε := ε) (μ := μ) (χy := χy) (phaseMean_oldCut c ν χo (thinRep T))]
    exact hC c ν ε μ χo χy hχo hν _ _ hae
  rw [Lpt_congr_Xmt hX, Lpt_zero]

end UnforcedLeray.Short.PartIIIb.Concrete
