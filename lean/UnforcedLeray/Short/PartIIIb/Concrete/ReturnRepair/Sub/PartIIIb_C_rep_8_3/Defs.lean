import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Lib.Train.PeriodizedVortex

/-!
# `PartIII-b:C/rep/8/3/2`: the objects of the Gaussian replacement (source 5484-5498)

Source of record: `the November 2 reference manuscript` (73 pages).

`GRBound` (`Sub/PartIII-b_C_rep_8_3.lean`) bounds `‖ringAff - E_{A_T}‖_{L²(π s^{-3/2}dς)}`, where
`ringAff` is the chart coefficient of `s^{3/2}{2B_Tv + 2νA_T:D²_flat v - (A_T+A_Tᵀ)∇_flat p_cyl}`
with the *actual* train `(v, p_cyl)` (source 5466-5483) and `E_{A_T} = EAcoef` is the same
expression summed over the Gaussian profiles `V_j, p_j` (`eA`, source 4963-4985).  Both sides use
the same matrices `A_T = 𝓛T₁` and `B_T`; neither contains the exact background pressure or the
repair `r_b`.  So the difference is exactly "replacing the actual train and its decaying pressure
by the summed Gaussian profiles" (source 5484-5486), which costs `P_ν ε³ δ_base N`:

* the train-minus-Gaussian profiles `trainDV = v - Σ_jV_j`, `trainDP = p_cyl - Σ_jp_j`
  (`gaussV`, `gaussP` the lattice sums);
* `ringAff - EAcoef` is the chart coefficient of `ringAffGen` applied to `(trainDV, trainDP)`
  (`GaussSumEA`: `e_A` is `ringAffGen` of the summed profiles; `RingAffGenSub`: linearity);
* pointwise `|ringAffGen(w, q)| ≤ 12(|B||w| + ν|A^y||D²w| + |A^y||∇q|)` (`RingAffGenPt`);
* the young-train comparison (source 5486-5492, Part I `sct:fixed-band`, source 468-478, with
  `Σ = 1.1`, `c = ν⁻²`): on `0 < s ≤ 1.1/ν` the cell norm of `|w| + |D²w| + |∇q|` is
  `≤ P_ν δ_base`, `δ_base = e^{C_Σ/ν - b_Σc²}` (`TrainGaussCell`, from `PartI.TrainFixedBand` and
  the pointwise conversion `TrainGaussPt`);
* `|A^y| ≤ s^{5/2}M(A_T)`, `|B| ≤ (1+μ)s^{3/2}M(A_T)` (`ayBound`, `bmatBound`), and
  `M(A_T) ≤ P_ν ε³ N` (`AffMJet`, from `repair:actual-jet` 5400-5413);
* the body conversion `ChartL2Conv` (source 5055-5060, 5063-5079).

The exact-pressure / repair-coefficient error `P_ν ε^{85/22} e^{m₀/ν} N` of source 5272-5289,
5494-5498 does not enter `ringAff - EAcoef`; it arises between the Ward residual on the exact
background (`meanE`: `L.U`, `L.pres`) and `ringAff`.  In `GRBound` that term is a harmless
nonnegative surplus.

The source's `P_ν` is `C ν^{-k}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The summed Gaussian profiles and the train-minus-Gaussian profiles -/

/-- The summed Gaussian velocity profile `Σ_j V_j(s, q, η)` (source 4963-4968, 5484-5486). -/
def gaussV (ν s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := ∑' j : ℤ, Vj ν s j x

/-- The summed Gaussian pressure `Σ_j p_j(s, q, η)` (source 4963-4968, 5484-5486). -/
def gaussP (ν s : ℝ) (x : ℝ × ℝ) : ℝ := ∑' j : ℤ, pj ν s j x

/-- `v - Σ_jV_j`: the actual train minus the summed Gaussians (source 5484-5486). -/
def trainDV (L : ReturnLevel) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := trainV L s x - gaussV L.ν s x

/-- `p_cyl - Σ_jp_j`: the decaying train pressure minus the summed Gaussian pressures
(source 5484-5486). -/
def trainDP (L : ReturnLevel) (s : ℝ) (x : ℝ × ℝ) : ℝ := trainP L s x - gaussP L.ν s x

/-- The size `Σ_{a,b} |∂_a∂_b V|` of the flat Hessian, in the form used by `hessContr`. -/
def flatHessNorm (V : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2, ‖fderiv ℝ (fun y => fderiv ℝ V y (ei b)) x (ei a)‖

/-- The jet `|v - ΣV_j| + |D²_flat(v - ΣV_j)| + |∇_flat(p_cyl - Σp_j)|` entering the affine
expression (source 5466-5486). -/
def trainGaussJet (L : ReturnLevel) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ‖trainDV L s x‖ + flatHessNorm (trainDV L s) x + ‖mgrad (trainDP L s) x‖

/-! ## 2. The leaves -/

/-- **`e_A` is the affine expression of the summed Gaussians** (source 4963-4985: `V_j, p_j` and
their derivatives decay like Gaussians in `j`, so the lattice sums converge with all derivatives
and may be differentiated termwise).  For `ν > 0`, `s > 0`: the profiles `Σ_jV_j`, `Σ_jp_j` are
`C²`, resp. differentiable, in `(q, η)`, and `e_A = ringAffGen(Σ_jV_j, Σ_jp_j)`. -/
def GaussSumEA : Prop :=
  ∀ ν s : ℝ, 0 < ν → 0 < s →
    ContDiff ℝ 2 (gaussV ν s) ∧ Differentiable ℝ (gaussP ν s) ∧
      ∀ (μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (x : ℝ × ℝ),
        eA ν μ χf A s x = ringAffGen ν μ χf A (gaussV ν) (gaussP ν) s x

/-- **The train slices are smooth** (source 2141-2161, `B0140.IsTrain.smooth_v`, `smooth_p`):
for `s ≥ 0` the flat profiles `v(s, ·)`, `p_cyl(s, ·)` are `C²`, resp. differentiable. -/
def TrainSliceSmooth : Prop :=
  ∀ (L : ReturnLevel) (s : ℝ), 0 ≤ s →
    ContDiff ℝ 2 (trainV L s) ∧ Differentiable ℝ (trainP L s)

/-- **Linearity of the affine expression in the profile** (calculus): for `C²` velocity slices
and differentiable pressure slices at age `s`, `ringAffGen` of the differences is the difference
of `ringAffGen`. -/
def RingAffGenSub : Prop :=
  ∀ (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (v₁ v₂ : ℝ → ℝ × ℝ → ℝ × ℝ)
    (p₁ p₂ : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ),
    ContDiff ℝ 2 (v₁ s) → ContDiff ℝ 2 (v₂ s) → Differentiable ℝ (p₁ s) →
      Differentiable ℝ (p₂ s) →
      ringAffGen ν μ χf A v₁ p₁ s x - ringAffGen ν μ χf A v₂ p₂ s x =
        ringAffGen ν μ χf A (fun s' y => v₁ s' y - v₂ s' y) (fun s' y => p₁ s' y - p₂ s' y) s x

/-- **Pointwise size of the affine expression** (algebra; source 5466-5483):
`|(2Bw + 2νA^y:D²w - (A^y+(A^y)ᵀ)∇q)_{(r,z)}| ≤ 12(|B||w| + ν|A^y||D²w| + |A^y||∇q|)`
(Frobenius norms of the matrices). -/
def RingAffGenPt : Prop :=
  ∀ (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (w : ℝ → ℝ × ℝ → ℝ × ℝ) (q : ℝ → ℝ × ℝ → ℝ)
    (s : ℝ) (x : ℝ × ℝ), 0 ≤ ν →
    ‖merOf (ringAffGen ν μ χf A w q s x)‖ ≤
      12 * (frob (Bmat ν μ χf A s) * ‖w s x‖ +
        ν * frob (Ay ν χf A s) * flatHessNorm (w s) x +
        frob (Ay ν χf A s) * ‖mgrad (q s) x‖)

/-- **Pointwise conversion to the Part I fields** (source 468-478, 2196-2216): `Σ_jV_j` is the
periodized heat vortex `V_c^p = Train.Vc ν c s` and `Σ_jp_j` the summed radial pressures
`p_c^p = Train.pc ν c s` (`c = ν⁻²`), read in `ℝ × ℝ`; the flat jet of the differences is
bounded by the Part I jets `|v - V_c^p|`, `|D²(v - V_c^p)|`, `|∇(p - p_c^p)|`. -/
def TrainGaussPt : Prop :=
  ∀ (L : ReturnLevel) (s : ℝ), 0 < s → ∀ x : ℝ × ℝ,
    trainGaussJet L s x ≤
      4 * (‖L.train.v s x - UnforcedLeray.Train.Vc L.ν (cOf L.ν) s x‖ +
        ‖iteratedFDeriv ℝ 2
            (fun z => L.train.v s z - UnforcedLeray.Train.Vc L.ν (cOf L.ν) s z) x‖ +
        ‖UnforcedLeray.Train.gradS
            (fun w => L.train.p s w - UnforcedLeray.Train.pc L.ν (cOf L.ν) s w) x‖)

/-- **The young-train comparison** (source 5484-5492: "the young-train comparison supplies the
quantitative envelope `δ_base ≤ P_ν exp(C_G/ν - b_G/ν⁴)` for the fixed derivative and
transverse-weight budget on `0 ≤ s ≤ 1.1/ν`"; Part I `sct:fixed-band`, 468-478): for the BUC train
of a level with `ν ≤ ν₀`, on `0 < s ≤ 1.1/ν`, the normalized cell `L²` norm of the jet
`|v - ΣV_j| + |D²(v - ΣV_j)| + |∇(p_cyl - Σp_j)|` is `≤ C ν^{-k} δ_base`,
`δ_base = e^{C_Σ/ν - b_Σc²}` (`deltaBase`, `c = ν⁻²`). -/
def TrainGaussCell : Prop :=
  ∃ (C : ℝ) (k : ℕ) (Csig bsig ν₀ : ℝ), 0 < C ∧ 0 < bsig ∧ 0 < ν₀ ∧
    ∀ L : ReturnLevel, UnforcedLeray.Short.PartI.IsBUCTrain L.train → L.ν ≤ ν₀ →
      ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / L.ν →
        ∫⁻ x, ENNReal.ofReal (trainGaussJet L s x ^ 2) ∂(UnforcedLeray.Cyl.avgμ (cOf L.ν)) ≤
          ENNReal.ofReal ((C * L.ν⁻¹ ^ k * deltaBase Csig bsig L.ν) ^ 2)

end UnforcedLeray.Short.PartIIIb.Concrete
