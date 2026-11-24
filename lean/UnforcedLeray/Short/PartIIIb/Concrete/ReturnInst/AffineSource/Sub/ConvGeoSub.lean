import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoDefs

/-!
# Sub-statements for `ConvChartEq` and `ConvGL2` (`PartIII-b:C/asrc/ra/9/2/2`)

Source of record: `the November 2 reference manuscript` (73 pages), lines 5034-5044
(chart rules, solenoidal completion), 2075-2077 (`U_raw`, `H`), 4963-4980 (lattice sums,
`ĥ_A`), 4371 (`δ_base`, train band), 2055-2060 (train bounds).  Proved here:
`convGL2_of` (pointwise lattice envelope + `GradLatticeL2` give `ConvGL2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-! ## 1. The bound for `sG` -/

/-- **Train band** (source 4371, 2055-2077: "the fixed-band train comparison", finite spatial and
conormal derivative budget): on `0 < s ≤ 1.1/ν`, for the BUC train of the regime, the planar
velocity `v`, its `x`-derivative and `𝒦v`, and `H = (1-𝒦)ψ`, its `x`-derivative and `𝒦H` are
bounded by `C ν^{-k}(1+|η|)^N` (`N` a fixed power, from `PartII-b` `RawJetBound`). -/
def TrainBand : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k N : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
    ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν → ∀ x : ℝ × ℝ,
      ‖trPl p s x‖ ≤ C * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N ∧
      ‖fderiv ℝ (trPl p s) x‖ ≤ C * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N ∧
      ‖cK (trPl p) s x‖ ≤ C * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N ∧
      |trH p s x| ≤ C * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N ∧
      ‖fderiv ℝ (trH p s) x‖ ≤ C * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N ∧
      |Kop (trH p) s x| ≤ C * p.ν⁻¹ ^ k * (1 + |x.2|) ^ N

/-- **Lattice envelope of `h^p_A` and `k = (1-𝒦)ψ^p_A`** (source 4963-4980, 5036-5039): for
`ν ≤ 1`, `0 < s ≤ 1.1/ν` (so `a = 1+νs ∈ [1, 2.1]`), `h^p_A`, `D_x h^p_A`, `𝒦h^p_A`, `k`, `D_x k`,
`𝒦k` are bounded by `C M(A) s^{5/2} Σ_j W(x - jc)` (Gaussian rate `α`, polynomial degree `N`
independent of the data; `M(A)` includes the cutoff derivative). -/
def HpPsiEnv (as : ℝ) : Prop :=
  ∃ (C α : ℝ) (N : ℕ), 0 ≤ C ∧ 0 < α ∧ ∀ (χf : ℝ → ℝ), IsSourceCutoffC χf →
    ∀ (ν : ℝ), 0 < ν → ν ≤ 1 → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / ν → ∀ x : ℝ × ℝ,
      ‖hpA ν χf A s x‖ ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * latticeS α N (cOf ν) x ∧
      ‖fderiv ℝ (hpA ν χf A s) x‖ ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * latticeS α N (cOf ν) x ∧
      ‖cK (hpA ν χf A) s x‖ ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * latticeS α N (cOf ν) x ∧
      |kOf ν χf A s x| ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * latticeS α N (cOf ν) x ∧
      ‖fderiv ℝ (kOf ν χf A s) x‖ ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * latticeS α N (cOf ν) x ∧
      |Kop (kOf ν χf A) s x| ≤ C * affM ν χf A * s ^ (5 / 2 : ℝ) * latticeS α N (cOf ν) x

/-- **Pointwise lattice envelope of `sG`** (source 5040-5044): follows from `TrainBand` and
`HpPsiEnv` by expanding `convG` (finite sum of products, `ε ≤ 1`, `(1+|η|)^{N₀} W_j ≤ W_j` of degree
`N+N₀`). -/
def ConvGEnvelope (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C α : ℝ) (N k : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < α ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν → ∀ x : ℝ × ℝ,
        ‖s • toMer (convG p χf A s x)‖ ≤
          C * p.ν⁻¹ ^ k * affM p.ν χf A * s ^ (7 / 2 : ℝ) * latticeS α N (cOf p.ν) x

theorem convGL2_of (as : ℝ) (χf : ℝ → ℝ) (h1 : ConvGEnvelope as χf) (h2 : GradLatticeL2) :
    ConvGL2 as χf := by
  intro hχ dm dp hdm
  obtain ⟨C, α, N, k, ν₁, hC, hα, hν₁, H⟩ := h1 hχ dm dp hdm
  obtain ⟨K0, hK0, hL⟩ := h2 α hα N
  refine ⟨C * Real.sqrt K0, k, min ν₁ 1, lt_min hν₁ one_pos, fun p d hreg hν A hA s hs hsT => ?_⟩
  have hν1 : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hc : p.c = cOf p.ν := hreg.c_eq
  have hc1 : 1 ≤ p.c := by
    rw [hc]
    unfold cOf
    rw [one_le_inv₀ (by positivity)]
    nlinarith
  have hM : 0 ≤ affM p.ν χf A := affM_nonneg p.ν χf A
  have h72 : 0 ≤ s ^ (7 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  have h52 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  set B : ℝ := C * p.ν⁻¹ ^ k * affM p.ν χf A * s ^ (7 / 2 : ℝ) with hB
  have hB0 : 0 ≤ B := by positivity
  calc ∫⁻ x, ENNReal.ofReal (‖s • toMer (convG p χf A s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
      ≤ ∫⁻ x, ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (latticeS α N p.c x ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c) := by
        refine lintegral_mono (fun x => ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h := H p d hreg hν1 A hA s hs hsT x
        rw [hc] at *
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ENNReal.ofReal (B ^ 2) *
          ∫⁻ x, ENNReal.ofReal (latticeS α N p.c x ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (B ^ 2) * ENNReal.ofReal K0 := by gcongr; exact hL p.c hc1
    _ = ENNReal.ofReal (B ^ 2 * K0) := by rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (((C * Real.sqrt K0) * p.ν⁻¹ ^ k * affM p.ν χf A *
              (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsq : B ^ 2 * K0 = (C * Real.sqrt K0 * p.ν⁻¹ ^ k * affM p.ν χf A * s ^ (7 / 2 : ℝ)) ^ 2 := by
          rw [hB]
          have := Real.sq_sqrt hK0
          calc (C * p.ν⁻¹ ^ k * affM p.ν χf A * s ^ (7 / 2 : ℝ)) ^ 2 * K0
              = (C * p.ν⁻¹ ^ k * affM p.ν χf A * s ^ (7 / 2 : ℝ)) ^ 2 * (Real.sqrt K0) ^ 2 := by
                rw [this]
            _ = _ := by ring
        rw [hsq]
        have hcoef : 0 ≤ C * Real.sqrt K0 * p.ν⁻¹ ^ k * affM p.ν χf A := by positivity
        have : C * Real.sqrt K0 * p.ν⁻¹ ^ k * affM p.ν χf A * s ^ (7 / 2 : ℝ) ≤
            C * Real.sqrt K0 * p.ν⁻¹ ^ k * affM p.ν χf A * (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hcoef
        exact pow_le_pow_left₀ (by positivity) this 2

/-! ## 2. Sub-statements of the chart identity -/

/-- **Chart rule for the symmetrized convection of two lifts** (source 5034-5044; `radial_chain`,
`axial_chain`, `∂_φ e_r = e_φ`): for profiles `α, β` differentiable at the chart point `q`, `s>0`,
`coefOf R (div(Nv α ⊗ Nv β + Nv β ⊗ Nv α)) q = s·cBil R⁻¹ α β`. -/
def ConvChartRuleGen : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (α β : Chart → Merid) (q : Chart), 0 < q.1 →
    DifferentiableAt ℝ α q → DifferentiableAt ℝ β q →
    coefOf R (fun τ y => physDivSym (fun y' => Nv R α τ y') (fun y' => Nv R β τ y') y) q =
      q.1 • toMer (cBil R⁻¹ (plOf α) (plOf β) q.1 q.2)

/-- `perExt` is the identity on the lattice sums (`c = ν⁻²`-periodicity in `q`, source 4963-4975). -/
def ConvPerExtHat (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → 0 < ε → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
      perExt (cOf ν) (hAcoef ν ε χf A) (s, x) = hAcoef ν ε χf A (s, x)

/-- `hAcoef` is differentiable on `s > 0` (source 4978: sums converge with their derivatives). -/
def ConvDiffHat (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → 0 < ε → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ, DifferentiableAt ℝ (hAcoef ν ε χf A) (s, x)

/-- The raw profile is differentiable on `s > 0` (the train and its stream are smooth there). -/
def ConvDiffRaw : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (p : Params) (d : ℝ),
    UnforcedLeray.Short.IIb.BgRegime p d dm dp → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
      DifferentiableAt ℝ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) (s, x)

/-- Differentiability in `x` of the four planar pieces `v`, `He`, `h^p_A`, `ke` (source 2075-2077,
4978). -/
def ConvDiffParts (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ dm dp : ℝ, 0 < dm → ∀ (p : Params) (d : ℝ),
    UnforcedLeray.Short.IIb.BgRegime p d dm dp → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
      DifferentiableAt ℝ (trPl p s) x ∧ DifferentiableAt ℝ (trHe p s) x ∧
      DifferentiableAt ℝ (hpPl p χf A s) x ∧ DifferentiableAt ℝ (kEz p χf A s) x

/-- The raw lift equals the ring lift of `rawProfile` near every off-axis point (`axisExt`). -/
def ConvRawEv : Prop :=
  ∀ (p : Params) (τ : ℝ) (y : Space), y ∉ axis →
    ∀ᶠ y' in nhds y, p.raw τ y' = Nv p.ε⁻¹ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) τ y'

/-- The profile identities `rawPl = v + εHe` and `hatPl = h^p + εke` for `s > 0`
(`eq:m3-ring-lift`, source 2075-2077; `ĥ_A` source 4980). -/
def ConvProfileEqs (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (p : Params) (A : ℝ → Mat3) (s : ℝ), 0 < s → ∀ x : ℝ × ℝ,
    rawPl p s x = trPl p s x + p.ε • trHe p s x ∧
    hatPl p χf A s x = hpPl p χf A s x + p.ε • kEz p χf A s x

/-- The planar train is solenoidal (`IsTrain.solenoidal`) and `h^p_A = J∇ψ^p_A` is solenoidal
(source 4993: `A^y_mer J = J[(tr A^y_mer)I - (A^y_mer)ᵀ]`, termwise). -/
def ConvDivZero (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (p : Params) (A : ℝ → Mat3), IsAffElem as A →
    ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
      cDiv (trPl p) s x = 0 ∧ cDiv (hpPl p χf A) s x = 0

/-- The bilinear expansion of `cB0` (pure algebra; `fderiv` is linear). -/
def ConvB0Expand : Prop :=
  ∀ (F E G K : ℝ → ℝ × ℝ → ℝ × ℝ) (ε s : ℝ) (x : ℝ × ℝ),
    DifferentiableAt ℝ (F s) x → DifferentiableAt ℝ (E s) x →
    DifferentiableAt ℝ (G s) x → DifferentiableAt ℝ (K s) x →
    cB0 (fun s' y => F s' y + ε • E s' y) (fun s' y => G s' y + ε • K s' y) s x =
      cB0 F G s x + ε • (cB0 E G s x + cB0 F K s x) + ε ^ 2 • cB0 E K s x

end UnforcedLeray.Short.PartIIIb.Concrete
