import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.WeightedWeakDerivOfPairing
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.CellMollTendsto
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.IbpPdCxWeak
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.WeightedCS

/-!
# `PartIII-a:T21/2/7/2/1/1/5/14`: the periodic weak derivative from bounded mollified derivatives

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
(the mollified derivatives are bounded uniformly in `n`), 3060-3061 (the limit `n -> infinity`).

Proof. Let `f_n = cellMoll n f`. For a cylinder test `ψ`, `IbpPdCxWeak` gives
`∫ f_n ∂_jψ = -∫ ∂_j f_n ψ`, and `weightedCS` gives
`‖∫ ∂_j f_n ψ‖ₑ ≤ ‖∂_j f_n‖_{X_{-m}} ‖ψ‖_{X_m} ≤ M ‖ψ‖_{X_m}`. Since
`‖∫ f ∂_jψ - ∫ f_n ∂_jψ‖ₑ ≤ ‖f_n - f‖_{X_{-m}} ‖∂_jψ‖_{X_m} → 0` (`CellMollTendsto`), the same
bound passes to `f`. Then `WeightedWeakDerivOfPairing` gives a weak derivative `g` in
`X_{-m,c}` with `‖g‖ ≤ 2M`, and the periodic representative `perRep c g` has the same cell
integrals, hence is the required `G`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The enorm of a real number cast into `ℂ`. -/
theorem cdw_enorm_ofReal (r : ℝ) : ‖(r : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  congr 1
  apply NNReal.eq
  simp [Complex.norm_real]

/-- Enorm of a pairing: `‖∫_cell f B‖ₑ ≤ ‖f‖_{X_{-m}} ‖B‖_{X_m}` for a real `B`. -/
theorem cdw_enorm_pair_le {c m : ℝ} {f : ℝ × ℝ → ℂ} {B : ℝ × ℝ → ℝ}
    (hf : AEStronglyMeasurable f (B0579.cellMeasure c (-m)))
    (hB : AEStronglyMeasurable B (B0579.cellMeasure c m)) :
    ‖∫ x in B0579.cell c, f x * (B x : ℂ)‖ₑ ≤
      xNorm c (-m) f * eLpNorm B 2 (B0579.cellMeasure c m) := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have h : ∫⁻ x in B0579.cell c, ‖f x * (B x : ℂ)‖ₑ =
      ∫⁻ x in B0579.cell c, ‖f x‖ₑ * ‖B x‖ₑ := by
    refine lintegral_congr fun x => ?_
    rw [enorm_mul, cdw_enorm_ofReal]
  rw [h]
  exact weightedCS c m f B hf hB

/-- A product `f * B` with `f ∈ X_{-m,c}` and `B ∈ X_m` (real) is integrable on the cell. -/
theorem cdw_integrableOn {c m : ℝ} {f : ℝ × ℝ → ℂ} {B : ℝ × ℝ → ℝ}
    (hf : MemLp f 2 (B0579.cellMeasure c (-m))) (hB : MemLp B 2 (B0579.cellMeasure c m)) :
    IntegrableOn (fun x => f x * (B x : ℂ)) (B0579.cell c) := by
  have hfm : AEStronglyMeasurable f (volume.restrict (B0579.cell c)) :=
    hf.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m))
  have hBm : AEStronglyMeasurable (fun x => (B x : ℂ)) (volume.restrict (B0579.cell c)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hB.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c m))
  refine ⟨hfm.mul hBm, ?_⟩
  have h1 := weightedCS c m f B hf.aestronglyMeasurable hB.aestronglyMeasurable
  have h2 : xNorm c (-m) f * eLpNorm B 2 (B0579.cellMeasure c m) < ⊤ :=
    ENNReal.mul_lt_top hf.eLpNorm_lt_top hB.eLpNorm_lt_top
  have h3 : ∫⁻ x in B0579.cell c, ‖f x * (B x : ℂ)‖ₑ =
      ∫⁻ x in B0579.cell c, ‖f x‖ₑ * ‖B x‖ₑ := by
    refine lintegral_congr fun x => ?_
    rw [enorm_mul, cdw_enorm_ofReal]
  show ∫⁻ x in B0579.cell c, ‖f x * (B x : ℂ)‖ₑ < ⊤
  rw [h3]
  exact lt_of_le_of_lt h1 h2

/-- The bounded pairing of the mollified fields passes to the limit: for a cylinder test `ψ`,
`‖∫_cell f ∂_jψ‖ₑ ≤ M ‖ψ‖_{X_m}` (the hypothesis of `WeightedWeakDerivOfPairing`). -/
theorem cdw_pairing {c m : ℝ} (hc : 0 < c) {f : ℝ × ℝ → ℂ} {j : Fin 2} {M : ℝ}
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x)
    (hmem : MemLp f 2 (B0579.cellMeasure c (-m)))
    (hD : ∀ n : ℕ, xNorm c (-m) (pdCx j (cellMoll n f)) ≤ ENNReal.ofReal M)
    (ψ : ℝ × ℝ → ℝ) (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun x => f x * (B0579.pd j ψ x : ℂ)) (B0579.cell c) ∧
      ‖∫ x in B0579.cell c, f x * (B0579.pd j ψ x : ℂ)‖ₑ ≤
        ENNReal.ofReal M * eLpNorm ψ 2 (B0579.cellMeasure c m) := by
  have hS := fun n : ℕ => cellMollSmooth c m n f hc hper hmem
  have hcd : ∀ n : ℕ, ContDiff ℝ ∞ (cellMoll n f) := fun n => (hS n).1
  have hperN : ∀ n : ℕ, ∀ x : ℝ × ℝ, cellMoll n f (x.1 + c, x.2) = cellMoll n f x :=
    fun n => (hS n).2.1
  have hMemN : ∀ n : ℕ, MemLp (cellMoll n f) 2 (B0579.cellMeasure c (-m)) := by
    intro n
    have h := (hS n).2.2 []
    simpa [adjSpatial] using h
  have hpsi : MemLp (B0579.pd j ψ) 2 (B0579.cellMeasure c m) := (hψ.pd j).memLp m
  have hint : ∀ n : ℕ, IntegrableOn (fun x => cellMoll n f x * (B0579.pd j ψ x : ℂ))
      (B0579.cell c) :=
    fun n => cdw_integrableOn (hMemN n) hpsi
  have hintf : IntegrableOn (fun x => f x * (B0579.pd j ψ x : ℂ)) (B0579.cell c) :=
    cdw_integrableOn hmem hpsi
  -- the bound on the mollified pairings, from the integration by parts and weighted Cauchy-Schwarz
  have hbd : ∀ n : ℕ, ‖∫ x in B0579.cell c, cellMoll n f x * (B0579.pd j ψ x : ℂ)‖ₑ ≤
      ENNReal.ofReal M * eLpNorm ψ 2 (B0579.cellMeasure c m) := by
    intro n
    have hibp : HasWeakCellDerivC c j (cellMoll n f) (pdCx j (cellMoll n f)) :=
      ibpPdCxWeak c j (cellMoll n f) hc (hcd n) (hperN n)
    rw [hibp.2 ψ hψ, enorm_neg]
    have hpc : AEStronglyMeasurable (pdCx j (cellMoll n f)) (B0579.cellMeasure c (-m)) :=
      ((contDiff_pdCx (hcd n) j).continuous).aestronglyMeasurable
    calc ‖∫ x in B0579.cell c, pdCx j (cellMoll n f) x * (ψ x : ℂ)‖ₑ
        ≤ xNorm c (-m) (pdCx j (cellMoll n f)) * eLpNorm ψ 2 (B0579.cellMeasure c m) :=
          cdw_enorm_pair_le hpc hψ.continuous.aestronglyMeasurable
      _ ≤ ENNReal.ofReal M * eLpNorm ψ 2 (B0579.cellMeasure c m) :=
          mul_le_mul' (hD n) le_rfl
  -- the difference from the limit is controlled by the mollification error
  have hdiff : ∀ n : ℕ,
      ‖(∫ x in B0579.cell c, cellMoll n f x * (B0579.pd j ψ x : ℂ)) -
          ∫ x in B0579.cell c, f x * (B0579.pd j ψ x : ℂ)‖ₑ ≤
        xNorm c (-m) (cellMoll n f - f) * eLpNorm (B0579.pd j ψ) 2 (B0579.cellMeasure c m) := by
    intro n
    have hsub : (∫ x in B0579.cell c, cellMoll n f x * (B0579.pd j ψ x : ℂ)) -
        ∫ x in B0579.cell c, f x * (B0579.pd j ψ x : ℂ) =
        ∫ x in B0579.cell c, (cellMoll n f - f) x * (B0579.pd j ψ x : ℂ) := by
      rw [← integral_sub (hint n) hintf]
      congr 1
      funext x
      simp only [Pi.sub_apply, sub_mul]
    rw [hsub]
    exact cdw_enorm_pair_le ((hMemN n).sub hmem).aestronglyMeasurable hpsi.aestronglyMeasurable
  have hlim : Tendsto (fun n : ℕ => xNorm c (-m) (cellMoll n f - f) *
      eLpNorm (B0579.pd j ψ) 2 (B0579.cellMeasure c m)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const (cellMollTendsto c m f hc hper hmem)
      (Or.inr hpsi.eLpNorm_lt_top.ne)
    rw [zero_mul] at h
    exact h
  refine ⟨hintf, ?_⟩
  have key : ∀ a b : ℂ, ‖a‖ₑ ≤ ‖b‖ₑ + ‖b - a‖ₑ := by
    intro a b
    calc ‖a‖ₑ = ‖b - (b - a)‖ₑ := by rw [sub_sub_cancel]
      _ ≤ ‖b‖ₑ + ‖b - a‖ₑ := enorm_sub_le
  have hle : ∀ n : ℕ, ‖∫ x in B0579.cell c, f x * (B0579.pd j ψ x : ℂ)‖ₑ ≤
      ENNReal.ofReal M * eLpNorm ψ 2 (B0579.cellMeasure c m) +
        xNorm c (-m) (cellMoll n f - f) * eLpNorm (B0579.pd j ψ) 2 (B0579.cellMeasure c m) :=
    fun n => (key _ _).trans (add_le_add (hbd n) (hdiff n))
  have hT : Tendsto (fun n : ℕ => ENNReal.ofReal M * eLpNorm ψ 2 (B0579.cellMeasure c m) +
      xNorm c (-m) (cellMoll n f - f) * eLpNorm (B0579.pd j ψ) 2 (B0579.cellMeasure c m))
      atTop (𝓝 (ENNReal.ofReal M * eLpNorm ψ 2 (B0579.cellMeasure c m) + 0)) :=
    tendsto_const_nhds.add hlim
  rw [add_zero] at hT
  exact ge_of_tendsto' hT hle

/-- **Weak derivative from uniformly bounded mollified derivatives** (SP 3060-3071: the
mollified derivatives `∂_j (ρ_n ⋆ f)` are bounded in `X_{-m,c}` uniformly in `n`; the Riesz
representation gives the periodic weak derivative `G` with `‖G‖ ≤ 2M`). -/
theorem cellWeakDerivOfMollBound : UnforcedLeray.Short.IIIa.CellWeakDerivOfMollBound := by
  unfold UnforcedLeray.Short.IIIa.CellWeakDerivOfMollBound
  intro c m j f M hc hper hmem hD
  obtain ⟨g, hg, hgm, hgn⟩ := weightedWeakDerivOfPairing c m hc f j (ENNReal.ofReal M)
    ENNReal.ofReal_ne_top (fun ψ hψ => cdw_pairing hc hper hmem hD ψ hψ)
  have hae : perRep c g =ᵐ[volume.restrict (B0579.cell c)] g := perRep_ae_cell hc g
  obtain ⟨h1, h2⟩ := hg
  refine ⟨perRep c g, perRep_periodic hc g, ?_, ?_, ?_⟩
  · exact hgm.ae_eq (perRep_ae_cellMeasure hc (-m) g).symm
  · unfold HasWeakCellDerivC
    refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
    · have hae' : (fun x => g x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
          (fun x => perRep c g x * (ψ x : ℂ)) :=
        hae.mono fun x hx => by simp only [hx]
      exact ⟨(h1 ψ hψ).1, (h1 ψ hψ).2.congr_fun_ae hae'⟩
    · have hae' : (fun x => g x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
          (fun x => perRep c g x * (ψ x : ℂ)) :=
        hae.mono fun x hx => by simp only [hx]
      rw [h2 ψ hψ, integral_congr_ae hae']
  · have hG : xNorm c (-m) (perRep c g) = xNorm c (-m) g :=
      eLpNorm_congr_ae (perRep_ae_cellMeasure hc (-m) g)
    calc xNorm c (-m) (perRep c g) = xNorm c (-m) g := hG
      _ ≤ 2 * ENNReal.ofReal M := hgn
      _ = ENNReal.ofReal (2 * M) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

end UnforcedLeray.Short.IIIa
